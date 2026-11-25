"""Cache orchestration tests use a fake compiler; they do not verify Lean proofs."""
import json
from pathlib import Path
import tempfile
import unittest

from build_cached import build, make_plan


class BuildCacheTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.ed = self.root / "EulerLean/ED"
        self.ed.mkdir(parents=True)
        (self.root / "lean-toolchain").write_text("leanprover/lean4:v4.32.0\n")
        (self.root / "lakefile.toml").write_text('name="fixture"\n')
        (self.root / "lake-manifest.json").write_text('{"packages":[]}\n')
        self.write("Base", "import Mathlib\ndef x := 1\n")
        self.write("Middle", "import Base\ndef y := x\n")
        self.write("Leaf", "import Middle\ndef z := y\n")
        self.write("Unrelated", "import Mathlib\ndef unused := 0\n")
        self.calls = []

    def write(self, name, text):
        (self.ed / f"{name}.lean").write_text(text)

    def compiler(self, name, work, environment, project):
        self.calls.append(name)
        self.assertTrue(environment["LEAN_PATH"].startswith(str(work)))
        (work / f"{name}.olean").write_bytes((name + "-fixture").encode())
        (work / f"{name}.olean.private").write_bytes(b"private fixture")
        (work / f"{name}.out").write_text(f"'{name}' does not depend on any axioms\n")
        return 0

    def run_build(self, compiler=None):
        return build(make_plan(self.root, "Leaf"), self.root / "cache", self.root / "work",
                     compiler or self.compiler, base_env={})

    def keys(self):
        return {m["module"]: m["key"] for m in make_plan(self.root, "Leaf")["modules"]}

    def test_build_then_hits_preserve_target_axiom_output(self):
        self.assertTrue(self.run_build()["ok"])
        self.assertEqual(self.calls, ["Base", "Middle", "Leaf"])
        self.calls.clear()
        result = self.run_build()
        self.assertEqual(self.calls, [])
        self.assertTrue(all(m["cache_hit"] for m in result["modules"]))
        self.assertIn("'Leaf'", Path(result["target_log"]).read_text())

    def test_leaf_change_reuses_both_dependencies(self):
        self.run_build(); self.calls.clear()
        self.write("Leaf", "import Middle\ndef z := y + 1\n")
        self.run_build()
        self.assertEqual(self.calls, ["Leaf"])

    def test_upstream_change_rebuilds_descendants(self):
        self.run_build(); self.calls.clear()
        self.write("Base", "import Mathlib\ndef x := 2\n")
        self.run_build()
        self.assertEqual(self.calls, ["Base", "Middle", "Leaf"])

    def test_each_pin_file_invalidates_all_modules(self):
        for filename in ["lean-toolchain", "lakefile.toml", "lake-manifest.json"]:
            before = self.keys()
            with (self.root / filename).open("a") as f: f.write("\n")
            after = self.keys()
            self.assertTrue(all(before[n] != after[n] for n in before))

    def test_unrelated_source_and_ledger_do_not_invalidate(self):
        before = self.keys()
        self.write("Unrelated", "import Mathlib\ndef unused := 99\n")
        (self.ed / "LEMMA_LEDGER.md").write_text("documentation only")
        self.assertEqual(before, self.keys())

    def test_comments_do_not_create_dependencies(self):
        self.write("Leaf", "/- import Missing\n/- nested -/\nimport Other -/\nimport Middle -- note\n")
        self.assertEqual([m["module"] for m in make_plan(self.root, "Leaf")["modules"]],
                         ["Base", "Middle", "Leaf"])

    def test_cycle_and_missing_module_are_rejected(self):
        self.write("Base", "import Leaf\n")
        with self.assertRaisesRegex(ValueError, "cyclic"): self.keys()
        self.write("Base", "import DoesNotExist\n")
        with self.assertRaisesRegex(ValueError, "unresolved"): self.keys()

    def test_corrupt_cached_artifact_is_rebuilt(self):
        self.run_build(); self.calls.clear()
        path = self.root / "cache/Middle" / self.keys()["Middle"] / "Middle.olean"
        path.write_bytes(b"corrupted")
        self.run_build()
        self.assertEqual(self.calls, ["Middle"])

    def test_failed_compilation_never_creates_valid_cache(self):
        def failing(name, work, environment, project):
            self.compiler(name, work, environment, project)
            return 1 if name == "Middle" else 0
        result = self.run_build(failing)
        self.assertFalse(result["ok"])
        self.assertEqual(result["failed_module"], "Middle")
        self.calls.clear()
        self.assertTrue(self.run_build()["ok"])
        self.assertEqual(self.calls, ["Middle", "Leaf"])


if __name__ == "__main__": unittest.main()

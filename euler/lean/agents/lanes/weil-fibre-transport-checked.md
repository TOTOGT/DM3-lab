# Checked Weil-fibre transport handoff

Date: 2026-11-25. Owner: Weil-fibre lane. Branch: codex/weil-fibre-pushforward.

Base/source main: 59af1de199f6eafd908c7be737478a68b3c3c3e8, rechecked remotely after compilation.
Tested proof commit: 1ccdfc8a20b6b69419572e45509ca0464a3d4580.
No remote CI run was dispatched. Local compiler and exact axiom gate both exited 0.
No publication was attempted; the integration lane owns publication, workflows and ledger.

Pinned compiler: Lean 4.32.0, commit 8c9756b28d64dab099da31a4c09229a9e6a2ef35.
Mathlib: 81a5d257c8e410db227a6665ed08f64fea08e997 (validated against manifest).
All other git dependency pins were validated by build_cached.py. Shared packages
were used read-only; the target and EDc6 were compiled in the lane work directory.
StageA4o was restored from a source/dependency/compiler-keyed cache.

Exact runner command (exit 0):
```sh
PATH=/workspace/scratch/e5767af651ef/runtime/lean-4.32.0-linux/bin:$PATH python3 /workspace/scratch/e5767af651ef/integration/euler/lean/agents/build_cached.py --project /workspace/scratch/a44247de7249/fibre-worktree/euler/lean --target FibrePushforward
```
The runner's leaf invocation was `lake env lean -R <work> -o
<work>/FibrePushforward.olean <work>/FibrePushforward.lean`, with the validated
import directory prepended to LEAN_PATH. Work is
`euler/lean/.ci-module-work/FibrePushforward` in the lane checkout.
Leaf cache key: 6f485ac0892c6b96186c4626daf0c9268f5a59ed5b3579d8fbf8ba44655cd296.

## Meaning and remaining obligations

The linear map sends a complex vertex function to its sum on each fibre.
Reindexing by a finite bijection and relabelling by an equivalence preserve the
kernel. The main theorem uses EDc6 to identify this kernel with simultaneous
orthogonality to oneY and chiE. A separate compiled corollary swaps Bool labels.

Full assumptions are printed below: p prime, 2 nonzero, a splitting xs²+ys²=-1,
the existing finite quotient instances, any finite V, an actual equivalence
e:Yp≃V, w:V→Bool and the pointwise fibre compatibility hw. There is no spectral
assumption and no conclusion hidden in hw: hw identifies the vertex labels only.
The hypotheses are satisfiable (V=Yp, identity equivalence, chi=1 indicator).

Not provided: the geometric vertex equivalence over F̄₂, the pairing-label
identity for actual geometric vertices, the operator/edge-count identification,
or the published spectral theorem in Lean. RPEigen stays explicit and open.
There is no new axiom declaration and all six theorem reports use exactly
propext, Classical.choice, Quot.sound. No sorryAx. Do not label this CI-tested.

The source review is a new lane note, not a replacement for an inaccessible
newer specialist package. No shared ledger/workflow was changed.

## Compiler output: all full theorem statements and axiom reports

```text
'EulerWeilFibre.fibre_sum_reindex' depends on axioms: [propext, Classical.choice, Quot.sound]
'EulerWeilFibre.fibrePush_relabel' depends on axioms: [propext, Classical.choice, Quot.sound]
'EulerWeilFibre.ker_fibrePush_relabel' depends on axioms: [propext, Classical.choice, Quot.sound]
'EulerWeilFibre.orth_iff_mem_ker_fibrePush' depends on axioms: [propext, Classical.choice, Quot.sound]
'EulerWeilFibre.orth_iff_mem_ker_fibrePush_swap' depends on axioms: [propext, Classical.choice, Quot.sound]
'EulerWeilFibre.mem_ker_fibrePush' depends on axioms: [propext, Classical.choice, Quot.sound]
EulerWeilFibre.mem_ker_fibrePush.{u_1, u_2} {V : Type u_1} {I : Type u_2} [Fintype V] [DecidableEq I] (w : V → I)
  (f : V → ℂ) : f ∈ (EulerWeilFibre.fibrePush w).ker ↔ ∀ (i : I), ∑ v with w v = i, f v = 0
EulerWeilFibre.fibre_sum_reindex.{u_1, u_2, u_3} {Y : Type u_1} {V : Type u_2} {I : Type u_3} [Fintype Y] [Fintype V]
  [DecidableEq I] (e : Y ≃ V) (w : V → I) (i : I) (f : Y → ℂ) :
  ∑ v with w v = i, f (e.symm v) = ∑ y with w (e y) = i, f y
EulerWeilFibre.fibrePush_relabel.{u_1, u_2, u_3} {V : Type u_1} {I : Type u_2} {J : Type u_3} [Fintype V]
  [DecidableEq I] [DecidableEq J] (s : I ≃ J) (w : V → I) (f : V → ℂ) :
  (EulerWeilFibre.fibrePush (⇑s ∘ w)) f = (EulerWeilFibre.fibrePush w) f ∘ ⇑s.symm
EulerWeilFibre.ker_fibrePush_relabel.{u_1, u_2, u_3} {V : Type u_1} {I : Type u_2} {J : Type u_3} [Fintype V]
  [DecidableEq I] [DecidableEq J] (s : I ≃ J) (w : V → I) :
  (EulerWeilFibre.fibrePush (⇑s ∘ w)).ker = (EulerWeilFibre.fibrePush w).ker
EulerWeilFibre.orth_iff_mem_ker_fibrePush.{u_1} (p : ℕ) [Fact (Nat.Prime p)] (h2 : 2 ≠ 0) (xs ys : ZMod p)
  (hxy : xs ^ 2 + ys ^ 2 = -1) [Fintype (SectionA2.PGL2 p)] [Fintype (SectionA2.PGL2 p ⧸ SectionA3b.Gam p h2 xs ys hxy)]
  [Fintype ↥(SectionA3b.Gam p h2 xs ys hxy)] {V : Type u_1} [Fintype V] (e : SectionA3b.Yp p h2 xs ys hxy ≃ V)
  (w : V → Bool) (hw : ∀ (y : SectionA3b.Yp p h2 xs ys hxy), w (e y) = true ↔ SectionA4k.chiY p h2 xs ys hxy y = 1)
  (f : SectionA4m2.EY p h2 xs ys hxy) :
  inner ℂ (SectionA4m2.oneY p h2 xs ys hxy) f = 0 ∧ inner ℂ (SectionA4m2.chiE p h2 xs ys hxy) f = 0 ↔
    (fun v => f.ofLp (e.symm v)) ∈ (EulerWeilFibre.fibrePush w).ker
EulerWeilFibre.orth_iff_mem_ker_fibrePush_swap.{u_1} (p : ℕ) [Fact (Nat.Prime p)] (h2 : 2 ≠ 0) (xs ys : ZMod p)
  (hxy : xs ^ 2 + ys ^ 2 = -1) [Fintype (SectionA2.PGL2 p)] [Fintype (SectionA2.PGL2 p ⧸ SectionA3b.Gam p h2 xs ys hxy)]
  [Fintype ↥(SectionA3b.Gam p h2 xs ys hxy)] {V : Type u_1} [Fintype V] (e : SectionA3b.Yp p h2 xs ys hxy ≃ V)
  (w : V → Bool) (hw : ∀ (y : SectionA3b.Yp p h2 xs ys hxy), w (e y) = true ↔ SectionA4k.chiY p h2 xs ys hxy y = 1)
  (f : SectionA4m2.EY p h2 xs ys hxy) :
  inner ℂ (SectionA4m2.oneY p h2 xs ys hxy) f = 0 ∧ inner ℂ (SectionA4m2.chiE p h2 xs ys hxy) f = 0 ↔
    (fun v => f.ofLp (e.symm v)) ∈ (EulerWeilFibre.fibrePush (⇑Equiv.boolNot ∘ w)).ker
```

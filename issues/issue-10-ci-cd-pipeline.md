## CI/CD pipeline: GitHub Actions for automated Lean 4 lake build + Python simulation tests

**Labels:** `ci-cd`, `devops`, `github-actions`, `lean`, `testing`

---

### Summary

There is currently no automated CI/CD pipeline in this repository. Every pull request must be manually verified. This issue adds a GitHub Actions workflow that:

1. Runs `lake build` to check all Lean 4 proofs
2. Runs Python simulation smoke tests

---

### Motivation

The repository's core assets are:
- `lean/Main.lean` — formal proofs that must compile without `sorry`
- `simulations/*.py` — Python scripts that must run without errors

Without CI, any contributor can accidentally break either. The `lean/Main.lean` header says *"ZERO sorry. ZERO axioms."* — CI enforces this automatically on every push.

---

### Scope of this issue

**Workflow file:** `.github/workflows/ci.yml`

**Job 1 — Lean 4 build:**
```yaml
- name: Install elan
  run: curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
- name: lake update
  run: ~/.elan/bin/lake update
- name: lake build
  run: ~/.elan/bin/lake build
```

**Job 2 — Python smoke tests:**
```yaml
- name: Set up Python 3.11
  uses: actions/setup-python@v5
  with: { python-version: '3.11' }
- name: Install dependencies
  run: pip install networkx numpy matplotlib scipy
- name: Run connectome loader test
  run: python -c "
    import sys; sys.path.insert(0, 'simulations')
    from connectome_loader import load_connectome, connectome_stats
    G = load_connectome('synthetic')
    s = connectome_stats(G)
    assert s['n_neurons'] > 0
    assert s['n_synapses'] > 0
    print('Smoke test passed:', s['n_neurons'], 'neurons')
  "
```

**Checks:**
- [ ] Workflow triggers on `push` and `pull_request` to `main`
- [ ] Lean job checks for `sorry` occurrences (fail if any found via `grep`)
- [ ] Python job runs synthetic connectome and verifies `tau > 0` from `dm3_metric`
- [ ] Badge added to `README.md`: `![CI](https://github.com/TOTOGT/PabloNogueira-dm3-lab/actions/workflows/ci.yml/badge.svg)`

---

### Acceptance criteria

1. `.github/workflows/ci.yml` exists and is valid YAML.
2. Both jobs pass on the current `main` branch.
3. A CI badge appears in `README.md`.
4. A PR that introduces a `sorry` in `Main.lean` causes the Lean job to fail.

---

### References

- `lean/Main.lean` — Lean proof file to build
- `simulations/connectome_loader.py`, `simple_to_operator.py` — Python files to test
- `lakefile.toml` — Lean project configuration
- GitHub Actions docs: https://docs.github.com/en/actions
- elan (Lean version manager): https://github.com/leanprover/elan

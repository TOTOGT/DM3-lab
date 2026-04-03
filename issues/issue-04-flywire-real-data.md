## FlyWire real connectome integration — replace synthetic fallback with live data pipeline

**Labels:** `simulation`, `data`, `enhancement`, `good-first-issue`

---

### Summary

`simulations/connectome_loader.py` currently falls back to a **synthetic Barabási–Albert graph** (200 nodes, 800 edges) when no real data is present. The AXLE framework is meant to run on the actual *Drosophila melanogaster* FlyWire connectome (~130,000 neurons, ~50 million synapses). This issue adds a documented, reproducible pipeline for downloading and using the real data.

---

### Background

FlyWire publishes the full fly connectome via:
- **API:** `https://codex.flywire.ai/api/download`
- **License:** CC BY 4.0 (cite FlyWire Consortium, 2023)
- **Format:** CSV with columns `pre_root_id`, `post_root_id`, `syn_count`

The loader already has a `_load_flywire()` function that reads this CSV — it just needs the data file present at `data/flywire_connections.csv`. The pipeline should make this step easy, documented, and testable.

---

### Scope of this issue

- [ ] Add `simulations/download_flywire.py`: a script that fetches the FlyWire CSV using `requests` and saves it to `simulations/data/flywire_connections.csv`
- [ ] Update `simulations/connectome_loader.py` to:
  - Accept `source="flywire"` and call the download script automatically if the CSV is absent
  - Print a clear citation line when loading real data
- [ ] Add `simulations/data/.gitignore` to exclude large CSV files from the repo
- [ ] Update `docs/index.md` "How to Run the Simulations" section with a FlyWire data setup step
- [ ] Add a smoke test: `load_connectome("synthetic")` returns a graph with `n_neurons > 0` and `n_synapses > 0`

---

### Expected output

When running with real data:
```
[AXLE] FlyWire connectome loaded: 130,000 neurons, 50,000,000 synapses
[AXLE] Citation: FlyWire Consortium (2023). https://codex.flywire.ai
```

---

### Acceptance criteria

1. `python simulations/connectome_loader.py` runs without errors using synthetic data (no network required).
2. The download script is documented and includes the proper citation.
3. The data CSV is listed in `.gitignore` (large file, not committed).
4. `docs/index.md` is updated with the new setup step.

---

### References

- `simulations/connectome_loader.py` — loader to extend
- `docs/index.md` — documentation to update
- FlyWire: https://codex.flywire.ai/api/download
- FlyWire citation: Dorkenwald et al., *Nature* 2023; Schlegel et al., *Nature* 2023

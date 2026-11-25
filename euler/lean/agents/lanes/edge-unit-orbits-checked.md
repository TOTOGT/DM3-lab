# Checked edge unit-orbit equivalence

Date 2026-11-25. Lane edge normalization and orientation.
Base main 01c4210aed1c422eae8530dc8b8c2e8e48bec378.
Tested proof commit 64bcbe6a44083b08338522e48791a26c466ac284.
Branch lane/edge-review-01c4210. No tracked AGENTS.md was present.
No shared ledger or workflow was edited. Publication belongs to integration.

## Result

UnitEndpointOrbits.lean imports the current EDc11.
residual_iff proves that the restricted unit-orbit relation on NEnd is
exactly existence of a unit u with rho u=1 and qv(u)*a=b.
orbitEquiv gives an equivalence between this residual orbit type and the
Hurwitz-unit orbit type on NCos.

Full assumptions are p prime; 2 nonzero in ZMod p; any xs,ys with
xs²+ys²=-1; any natural norm l with p not dividing l; and arbitrary
g,h in PGL2. Surjectivity normalizes a coset endpoint using the existing
uOf lift. Injectivity follows from inclusion; residual_iff identifies
the restricted relation with the kernel action by group cancellation.
No assumption contains the asserted equivalence or a spectral conclusion.
The source imposes no distinct-endpoint condition, so loops are included.

The two orbit relations are Setoids on finite endpoint subtypes,
induced by left Hurwitz-unit multiplication. residualSetoid is defined
by restriction; residual_iff proves its actual kernel interpretation.
Neither quotient needs Gamma to be normal.

Existing EDc11 supplies the count NCos=12*NEnd and the coefficient
12*NEnd/24=NEnd/2. The new theorem adds the explicit orbit correspondence.
Geometric identification with target automorphism orbits remains external.
RPEigen remains explicit and open.

## Compiler and gate evidence

Lean 4.32.0, compiler commit 8c9756b28d64dab099da31a4c09229a9e6a2ef35.
Mathlib 81a5d257c8e410db227a6665ed08f64fea08e997.
All git package HEADs were checked against the manifest; all tracked pins
are unchanged. The runtime was restored from the official Lean release.
Mathlib cache download first encountered HTTP 429; the retry with two
parallel transfers completed successfully for all 8639 files.
Dependency worktrees are lane-specific. Other lanes' packages were not modified.

Exact successful command, compiler runner exit 0:

    PATH=/workspace/scratch/e96a610cd621/runtime/lean-4.32.0-linux/bin:$PATH python3 /workspace/scratch/e5767af651ef/current/euler/lean/agents/build_cached.py --project edge/euler/lean --target UnitEndpointOrbits

Executed from /workspace/scratch/e96a610cd621.
The runner compiles the transitive closure with lake env lean -R <work>
-o <work>/<module>.olean <work>/<module>.lean, using the validated Lean path.
StageA4o and EDc11 were freshly compiled exit 0 during this run, then
restored by their content/dependency keys for the target repair attempts.
The successful target was freshly compiled.
Leaf key 0ee7da0cf998d644de66f4b1e264a2daba7988de31530697edc1561239c09445.

A preliminary build failed in StageA4o on a missing Mathlib object,
before reaching the target. Once downloads completed, target diagnostics
identified omitted theorem section-variable hpl binders and a quotient
relation inference problem. Both were repaired without weakening statements.
An intermediate syntax error from a doc comment preceding include was
also repaired. Successful final output has no errors or sorryAx.

The declaration-specific axiom gate exited 0 for residual_iff,
orbitMap_injective, orbitMap_surjective and orbitEquiv. Each printed exactly
[propext, Classical.choice, Quot.sound].
CI has not run this new module. It is locally kernel-checked, pending CI.

## Integration

Take the two proof commits and this note from the lane bundle, or copy
the final new source and note. Existing main EDc11 is unchanged.
Compile order is StageA4o, EDc11, UnitEndpointOrbits.
Gate exactly these four EdgeUnitOrbits declarations; import names are flat.
Raw compiler and gate output are in the handoff.

## Complete target output

```text
'EdgeUnitOrbits.residual_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'EdgeUnitOrbits.orbitMap_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'EdgeUnitOrbits.orbitMap_surjective' depends on axioms: [propext, Classical.choice, Quot.sound]
'EdgeUnitOrbits.orbitEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
EdgeUnitOrbits.residual_iff (p : ℕ) [Fact (Nat.Prime p)] (h2 : 2 ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)
  (l : ℕ) (hpl : ¬p ∣ l) (g h : SectionA2.PGL2 p) (a b : EdgeCount.NEnd p xs ys l g h) :
  (EdgeUnitOrbits.residualSetoid p xs ys l g h) a b ↔
    ∃ u, (SectionA3a2.rho p h2 xs ys hxy) u = 1 ∧ SectionA3a3.qv u * ↑a = ↑b
EdgeUnitOrbits.orbitEquiv (p : ℕ) [Fact (Nat.Prime p)] (h2 : 2 ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)
  (l : ℕ) (hpl : ¬p ∣ l) (g h : SectionA2.PGL2 p) :
  Quotient (EdgeUnitOrbits.residualSetoid p xs ys l g h) ≃ Quotient (EdgeUnitOrbits.cosetSetoid p h2 xs ys hxy l g h)
EdgeUnitOrbits.orbitMap_injective (p : ℕ) [Fact (Nat.Prime p)] (h2 : 2 ≠ 0) (xs ys : ZMod p)
  (hxy : xs ^ 2 + ys ^ 2 = -1) (l : ℕ) (g h : SectionA2.PGL2 p) :
  Function.Injective (EdgeUnitOrbits.orbitMap p h2 xs ys hxy l g h)
EdgeUnitOrbits.orbitMap_surjective (p : ℕ) [Fact (Nat.Prime p)] (h2 : 2 ≠ 0) (xs ys : ZMod p)
  (hxy : xs ^ 2 + ys ^ 2 = -1) (l : ℕ) (hpl : ¬p ∣ l) (g h : SectionA2.PGL2 p) :
  Function.Surjective (EdgeUnitOrbits.orbitMap p h2 xs ys hxy l g h)
```

Source SHA256 f0546bd69843eb70f1d5c044a74730264292bb16f10eade0855f6eca70ebb82a

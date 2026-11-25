# Vertex lane recheck on current main

2026-11-25. Base main 01c4210aed1c422eae8530dc8b8c2e8e48bec378.
Branch lane/vertex-review-01c4210. Recovered proof commit 0134012,
byte-identical to historical proof 7c575747bcaa71a4bca3f0c9c4ac056b18e39d53.
No AGENTS.md was tracked. Full source and current StageA4o definitions were read.

All requested finite content already exists in VertexDoubleOrbit.lean.
Its doubleOrbitRel_iff identifies the pulled-back relation with actual left
unit multiplication and right scalar multiplication. doubleOrbitEquiv is an
equivalence of quotient types; no normality assumption on Gamma occurs.
stabilizer_eq_kernel is equality of sets for every projective g, and
stabilizer_card gives cardinality two using the existing checked kernel.
EDc10.unit_stabilizer_iff supplies the explicit {1, negOne} characterization.
The source was reused without adding duplicate declarations.

The hypotheses are p prime, 2 nonzero in ZMod p, and xs²+ys²=-1.
There is no p>3 assumption, no elliptic-curve hypothesis and no spectral
assumption. The external geometric inputs are the Hurwitz endomorphism-order
identification over the algebraic closure of F2 and compatibility of rho
with the torsion action. RPEigen remains open.

A fresh local build of EDc10 and VertexDoubleOrbit completed exit 0.
StageA4o was restored from the matching content/dependency-keyed artifact
produced in the edge lane. Dependencies were used read-only.
Lean 4.32.0, commit 8c9756b28d64dab099da31a4c09229a9e6a2ef35.
Mathlib 81a5d257c8e410db227a6665ed08f64fea08e997.
The runner verified all git package revisions and clean tracked dependency
sources before building; the tracked project pins were unchanged.

Actual command, exit 0, from /workspace/scratch/9141b61410c9:

    PATH=/workspace/scratch/e96a610cd621/runtime/lean-4.32.0-linux/bin:$PATH python3 /workspace/scratch/e5767af651ef/current/euler/lean/agents/build_cached.py --project vertex/euler/lean --target VertexDoubleOrbit

Target key be529268eb9392442149b2a0091daf716f168b7e64c77e03fb1374897960e3b4.
All five exact axiom reports passed the declaration-specific gate, exit 0.
Each contains exactly propext, Classical.choice, Quot.sound. No sorryAx.
No new CI run or publication occurred. Status remains locally checked,
pending CI for this module. Shared files were not edited.

The integration branch already carries the original proof and evidence;
only this recheck note needs adding if those commits are present.

## Full compiler output

```text
'EulerVertexOrbit.doubleOrbitRel_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'EulerVertexOrbit.doubleOrbitEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'EulerVertexOrbit.doubleOrbitEquiv_mk' depends on axioms: [propext, Classical.choice, Quot.sound]
'EulerVertexOrbit.stabilizer_eq_kernel' depends on axioms: [propext, Classical.choice, Quot.sound]
'EulerVertexOrbit.stabilizer_card' depends on axioms: [propext, Classical.choice, Quot.sound]
EulerVertexOrbit.doubleOrbitRel_iff (p : ℕ) [Fact (Nat.Prime p)] (h2 : 2 ≠ 0) (xs ys : ZMod p)
  (hxy : xs ^ 2 + ys ^ 2 = -1) (a b : EulerVertexDraft.MatrixUnits p) :
  (EulerVertexOrbit.doubleOrbitSetoid p h2 xs ys hxy) a b ↔
    ∃ u c, b = EulerVertexDraft.unitRed p h2 xs ys hxy u * a * (Matrix.GeneralLinearGroup.scalar (Fin 2)) c
EulerVertexOrbit.doubleOrbitEquiv (p : ℕ) [Fact (Nat.Prime p)] (h2 : 2 ≠ 0) (xs ys : ZMod p)
  (hxy : xs ^ 2 + ys ^ 2 = -1) :
  Quotient (EulerVertexOrbit.doubleOrbitSetoid p h2 xs ys hxy) ≃ SectionA3b.Yp p h2 xs ys hxy
EulerVertexOrbit.stabilizer_eq_kernel (p : ℕ) [Fact (Nat.Prime p)] (h2 : 2 ≠ 0) (xs ys : ZMod p)
  (hxy : xs ^ 2 + ys ^ 2 = -1) (g : SectionA2.PGL2 p) :
  {u | (SectionA3a2.rho p h2 xs ys hxy) u * g = g} = ↑(SectionA3a2.rho p h2 xs ys hxy).ker
EulerVertexOrbit.stabilizer_card (p : ℕ) [Fact (Nat.Prime p)] (h2 : 2 ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)
  (g : SectionA2.PGL2 p) : Nat.card { u // (SectionA3a2.rho p h2 xs ys hxy) u * g = g } = 2
```

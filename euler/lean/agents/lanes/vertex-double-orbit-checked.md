# Vertex quotient and stabilizers: checked lane handoff

Date: 2026-11-25. Branch: codex/vertex-orbit-equivalence.
Base main, fetched before work and independently rechecked after compilation:
59af1de199f6eafd908c7be737478a68b3c3c3e8.
Tested proof source commit: 7c575747bcaa71a4bca3f0c9c4ac056b18e39d53.
No tracked AGENTS.md was present at this base. Source read: current EDc10,
StageA4o's SectionA2, SectionA3a2, SectionA3b, and the pinned Mathlib matrix
center/scalar classification. No prior declarations were copied under new names.

## Results and full assumptions

Namespace EulerVertexOrbit; new file ED/VertexDoubleOrbit.lean.
All results take p:ℕ with Fact p.Prime, h2:(2:ZMod p)≠0, xs ys:ZMod p,
and hxy:xs²+ys²=-1. No p>3 restriction, Fintype instances, geometric facts,
or spectral assumptions are required.

1. doubleOrbitRel_iff: for a,b in GL₂(F_p), the pulled-back Gamma orbit
relation holds iff there exist a Hurwitz unit u and c in F_pˣ with
b=unitRed(u)*a*scalar(c). Scalars are literal GL₂ scalar units, not an
unproved identification of the whole center with scalars: the proof uses
Mathlib's Matrix.GeneralLinearGroup.center_eq_range_scalar.
2. doubleOrbitEquiv: Quotient doubleOrbitSetoid ≃ Yp, mapping [a] to
[projectivize(a)]. This is an equivalence of orbit TYPES. Gamma is not assumed
normal, and no quotient-group structure is introduced on either orbit type.
3. doubleOrbitEquiv_mk proves that exact representative formula.
4. stabilizer_eq_kernel: for every projective g, the set of Hurwitz units u
with rho(u)*g=g equals the set underlying ker rho. This uses free_left.
5. stabilizer_card: Nat.card {u // rho(u)*g=g}=2, from the checked card_ker.
The exact identities ±1 are already proved in rho_eq_one_iff and
EDc10.unit_stabilizer_iff; they are reused rather than duplicated.

Assumptions do not contain the conclusions. The double-orbit relation is
defined by pullback, and the independent explicit relation theorem supplies
the substantive unit/scalar content. No RPEigen assumption is used.

## Actual local verification

Lean 4.32.0, compiler commit 8c9756b28d64dab099da31a4c09229a9e6a2ef35.
Mathlib pin 81a5d257c8e410db227a6665ed08f64fea08e997.
Runner validates all git dependency revisions and clean tracked package sources.
Command, exit 0:

```sh
PATH=/workspace/scratch/e5767af651ef/runtime/lean-4.32.0-linux/bin:$PATH python3 /workspace/scratch/e5767af651ef/integration/euler/lean/agents/build_cached.py --project /workspace/scratch/9141b61410c9/vertex/euler/lean --target VertexDoubleOrbit
```

The leaf was compiled (cache_hit=false); StageA4o reused a validated source-keyed
cache. EDc10 was freshly compiled successfully in this lane on the first build,
then restored unchanged on the final build. Shared dependency packages were
read-only and no lake update was run.
Leaf compiler command: lake env lean -R <work> -o <work>/VertexDoubleOrbit.olean
<work>/VertexDoubleOrbit.lean, where work is the lane's
euler/lean/.ci-module-work/VertexDoubleOrbit and validated LEAN_PATH includes it.
Leaf key: be529268eb9392442149b2a0091daf716f168b7e64c77e03fb1374897960e3b4.
Declaration-specific check_axioms.py also exited 0 on the five exact reports.
There is no sorryAx or new hidden axiom. This is local kernel verification,
not a new GitHub Actions run. Compiler diagnostics were fixed only in this file.

## Boundaries and integration

External prerequisites remain End(E over F̄₂) ≅ the Hurwitz order and compatibility
of its action on geometric p-torsion with the matrix representation. This file
asserts no elliptic-curve equivalence or geometric automorphism count. It does
not substitute F₂-rational automorphisms for geometric ones. Operator edge
counts and spectral applicability are separate lanes; RPEigen remains open.
No splitting conjugacy was reimplemented. No shared ledger/workflow was changed.
Publication belongs to the integration lane; no push was attempted.

## Exact compiler reports and statements

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

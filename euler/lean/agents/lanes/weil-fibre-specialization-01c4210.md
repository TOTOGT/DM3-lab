# Scalar level in characteristic two

Reviewed 2026-11-25 against fetched main 01c4210aed1c422eae8530dc8b8c2e8e48bec378.
Owner is the Weil-fibre lane. No tracked AGENTS.md was present. The current specialist
package was absent from the repository and an exact-title Library search did not
resolve it. This supplementary note leaves that package intact.

## Source and precise scope

Codogni–Lido, Journal of Number Theory 286 (2026), 131–184,
https://doi.org/10.1016/j.jnt.2026.02.006 .
Published PDF was downloaded directly from the authors' institutional repository,
https://art.torvergata.it/retrieve/6dee5b82-553f-4677-88e4-12c3fa705637/G.%20Codogni%20and%20G.Lido%20Spectral%20theory%20of%20isogeny%20graphs.pdf .
SHA256 c55a4e08f21972ac2f581991309e35645d94db563bb919b638cf848cc93cd4af.

Definition 1.3 (p.134) allows distinct characteristic and isogeny-degree primes
coprime to N, with any H. Vertices and their automorphisms are geometric.
Edges are taken modulo target automorphisms, and A_ij counts j→i.
Proposition 2.2.2 (pp.147–148) gives the adjoint using automorphism weights.
Remark 2.3.6 (pp.150–151) describes the kernel by separate fibre sums.
Proposition 2.3.7 (p.151) gives the quotient's exceptional spectrum.
Theorem 2.3.8 (p.151), proved as 4.18 (p.165), bounds kernel eigenvalues
strictly by 2√ℓ. These statements were read in the published PDF.

## Specialization and deductions to review

Use q for the paper's characteristic p. Set q=2, N=our prime p>3,
H={aI:a∈F_p×}, and ℓ a prime unequal to 2,p. These satisfy Definition 1.3.
In particular, Proposition 2.2.2's additional sufficient condition q≡1 mod12
for ordinary matrix symmetry is unnecessary for self-adjointness here:
ℓI∈H makes its diamond operator the identity.

For scalar H, det(aI)=a². After choosing a primitive p-th root of unity,
the Weil invariant set identifies with F_p×/(F_p×)². This choice identifies
its two points with signs; changing the root can exchange the signs.
A degree-ℓ edge multiplies the Weil exponent by ℓ. Consequently:

| Legendre symbol (ℓ/p) | Action on Weil labels | Base cycles | Exceptional quotient eigenvalues |
| --- | --- | --- | --- |
| +1 | fixes both | two cycles of length 1 | ℓ+1 on each cycle |
| −1 | exchanges them | one cycle of length 2 | ℓ+1 and −(ℓ+1) |

The total pushforward kernel is the direct sum of the cycle kernels.
Thus the componentwise published bound supplies the global bound: a
nonzero global eigenvector has a nonzero component, carrying the same
eigenvalue. Neither residue case needs a new exceptional-mode assumption.

To identify the paper's weighted inner product with twice the counting
inner product, still supply the geometric stabilizer calculation
Aut(E,φ)=±1 for scalar level p>3. The algebraic unit-kernel calculation
requires compatibility with End(E/F̄₂) and its torsion action.
This compatibility is an external geometric obligation.

The pairing-label identity required by FibrePushforward follows on paper
from e_p(φ_g(e₁),φ_g(e₂))=e_p(φ₀(e₁),φ₀(e₂))^(det g).
It still needs an actual geometric vertex equivalence e, including the
chosen endomorphism-order and torsion identifications.

Finally provide the exact matrix conjugacy in that equivalence. Transposition
between the paper's column convention and functions on outgoing neighbours
must be accounted for. Uniform weights together with self-adjointness then
give ordinary symmetry; checking the constant eigenvalue alone does not
supply matrix conjugacy.

## Lean evidence retained

FibrePushforward.lean is byte-identical to locally tested proof
1ccdfc8a20b6b69419572e45509ca0464a3d4580. All transitive cache keys for
StageA4o, EDc6 and FibrePushforward match the historical exit-zero build
after reconciliation with current main. This run repeated the exact
six-declaration axiom gate, exit 0; each report is exactly
[propext, Classical.choice, Quot.sound].
Full assumptions and original compiler command are preserved in
weil-fibre-transport-checked.md.

No Lean invocation occurred in this review run. The former private compiler
and dependency cache are absent here. The local proof evidence is historical;
CI for FibrePushforward remains pending. No Lean source, shared ledger or
workflow was edited. RPEigen remains open.

The integration branch already contains both original fibre commits under
its own cherry-pick hashes. Integrators should take only this new note when
those sources are already present.

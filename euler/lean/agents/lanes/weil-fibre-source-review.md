# Weil-fibre source review — 2026-11-25

Lane: Weil-fibre transport and spectral-source review. Base checked: main
59af1de199f6eafd908c7be737478a68b3c3c3e8. No tracked AGENTS.md or specialist
package was found in that tree. This note does not replace the project package.

Primary source: Giulio Codogni and Guido Maria Lido, *Spectral theory of isogeny
graphs*, Journal of Number Theory 286 (2026), 131–184,
https://doi.org/10.1016/j.jnt.2026.02.006 . Published PDF inspected directly:
https://art.torvergata.it/retrieve/6dee5b82-553f-4677-88e4-12c3fa705637/G.%20Codogni%20and%20G.Lido%20Spectral%20theory%20of%20isogeny%20graphs.pdf

## Published statements checked

- Definition 1.3, p.134: geometric vertices and outgoing degree-ℓ isogenies modulo target automorphisms; A_ij counts edges j→i.
- Proposition 2.2.2, pp.147–148: the automorphism-weighted Hermitian form gives A* = ⟨ℓ⁻¹⟩A. Scalar H makes A self-adjoint.
- Remark 2.3.6, pp.150–151: pushforward kernels consist of coefficient sums zero separately on every Weil fibre.
- Proposition 2.3.7, p.151: separates the exceptional quotient spectrum.
- Theorem 2.3.8, p.151, proved as Theorem 4.18, p.165: eigenvalues on each component's pushforward kernel have modulus strictly below 2√ℓ.

## Candidate application — inferences, still external

Set characteristic q=2, N=p odd, H=F_p×I, ℓ≠2,p. Scalar determinants are squares: the Weil labels should be the two determinant classes. Their ℓ-action fixes or swaps them; the global kernel splits over the resulting components. All automorphisms and isogenies must be geometric, over F̄₂. Counting only F₂-rational automorphisms would change the quotient.

Needed bridges: a geometric vertex equivalence; pairing-label compatibility; exact operator identification including weights/transposition; and application of the external spectral theorem. These are not supplied by the finite Lean transport. Uniform stabilizers would identify weighted and counting inner products. RPEigen remains open.

# `HPrime`: exact statement, and the classical bridge (verification commit, 21 Nov 2026)

Status words: KERNEL-CHECKED (declaration inspected, axiom report read), CLASSICAL (established mathematics; citation NOT opened in this session unless said), UNCHECKED (recalled or taken from `INTERFACE-Lemma-3.2.md`, not verified here).
`HPrime` is an explicit hypothesis, `def HPrime : Prop` in `EDb8.lean`. It is not an axiom and is not folded into any other hypothesis. Nothing in this commit changes it.

## 1. The Lean statement (verbatim, EDb8.lean)
```lean
def HPrime : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (_hp3 : p % 4 = 3) (_hp4 : 3 < p) (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)
    (l : ℕ), l.Prime → Adm p l → ∀ f : EY p h2 xs ys hxy,
      inner ℂ (oneY p h2 xs ys hxy) f = 0 → inner ℂ (chiE p h2 xs ys hxy) f = 0 →
      ‖Tl p h2 xs ys hxy l f‖ ≤ 2 * Real.sqrt l * ‖f‖
```

## 2. What each piece is (read from the Lean definitions in StageA4o.lean; KERNEL-CHECKED as definitions, their intended meaning below is my reading)
| Piece | Definition | Note |
|---|---|---|
| Primes | p prime, p ≡ 3 mod 4, p > 3; l prime | the bound is only claimed for prime l |
| `Adm p l` | `Odd l ∧ ¬ p ∣ l` | so l is odd and l ≠ p |
| Space `EY` | `EuclideanSpace ℂ (Yp)`, counting inner product | functions on the finite set Y_p = right cosets of Γ_p in PGL₂(F_p) (`SectionA3b.Yp`) |
| Γ_p | image of the Hurwitz unit group in PGL₂(F_p), order 12 | via an isomorphism O/pO ≅ M₂(F_p) fixed by (xs, ys) with xs²+ys² = −1 (`SectionA3b.Gam`, A3a–A3b) |
| `Tl p … l` | linear map `f ↦ SectionA4g.Tn … l f` (and 0 if `Adm` fails) | Hecke relations proved in Lean (A4e–A4i): T_m self-adjoint; odd T_m commute; T_l T_{l^k} = T_{l^{k+1}} + l T_{l^{k−1}}; T_m 1 = σ(m)·1; T_m χ = (m/p) σ(m) χ |
| Normalization | **unnormalized** Hecke operator: eigenvalue on constants is σ(l) = l + 1 | not divided by √l; this is why the bound reads 2√l |
| Subspace | f orthogonal to `oneY` (constants) and `chiE` (the quadratic character of det) | removes the two one-dimensional pieces whose eigenvalues are σ(l) and (l/p)σ(l) |
| Bound | ‖T_l f‖ ≤ 2·√l·‖f‖ | operator norm of T_l on {1, χ}^⊥; for a self-adjoint T_l this is |eigenvalue| ≤ 2√l |

Weight and level, in classical terms: this is the weight-2 Ramanujan–Petersson bound |a_l| ≤ 2·l^{(2−1)/2} for the Hecke eigenvalues a_l on the part of L²(Y_p) orthogonal to {1, χ}. The functions on Y_p are automorphic forms of weight 2 on the definite quaternion algebra of discriminant 2 (the Hurwitz order is a maximal order of it) with a full level-p structure. The exact level and nebentypus of the modular-form space they correspond to under the Eichler/Jacquet–Langlands dictionary are UNCHECKED and are not needed to state `HPrime`; see `INTERFACE-Lemma-3.2.md` §2.

## 3. The classical bridge (CLASSICAL, citations not opened here)
1. **Weil.** The Riemann Hypothesis for curves over finite fields (Weil, 1940s; Frobenius eigenvalues have absolute value √q). UNCHECKED reference details.
2. **Eichler–Shimura.** For a weight-2 newform on Γ₀(N) and a prime l not dividing N, T_l acts on the Jacobian of X₀(N) mod l as Frobenius + Verschiebung (T_l = F + lF⁻¹ type relation). Hence a_l = α + ᾱ with |α| = √l, so |a_l| ≤ 2√l. UNCHECKED: exact form of the congruence relation and its hypotheses.
3. **Igusa.** Removes the finitely many exceptional primes in step 2 (per Livne, as recorded in `INTERFACE-Lemma-3.2.md`; my recollection, not opened). UNCHECKED.
4. **Quaternionic transfer.** The eigenvalues of T_l on {1, χ}^⊥ ⊂ L²(Y_p) are eigenvalues of weight-2 Hecke operators on cusp forms of some level dividing a power of 2·p with l ∤ level (Eichler's basis problem / Jacquet–Langlands). UNCHECKED: which levels, and whether oldforms need separate treatment. Lean has none of this.
5. **From eigenvalues to the norm.** T_l is self-adjoint (KERNEL-CHECKED, StageA4b), so on {1, χ}^⊥ (T_l-invariant because 1 and χ are eigenvectors, KERNEL-CHECKED StageA4j/k) ‖T_l f‖ ≤ max|eigenvalue|·‖f‖. This step is elementary and is the part already in the Lean development.
6. **Prime powers and general m** follow from the Chebyshev-type relation T_l T_{l^k} = T_{l^{k+1}} + l T_{l^{k−1}} and multiplicativity (KERNEL-CHECKED), giving ‖T_m‖ ≤ τ(m)√m for the odd m used.

Missing from Mathlib today: modular curves and their Jacobians, the Eichler–Shimura relation, the Weil bound for curves, the Jacquet–Langlands/Eichler transfer. The AxiomMath/Weil formalization is the candidate source of step 1; its status is not yet checked.

## 4. What this commit establishes
Only the removal of `native_decide` from the finite range n < 64⁴ (EDcert*.lean, EDb9k.lean). The mathematical content of `HPrime`, its Lean statement and the proof chain from `HPrime` to Euler 1747 are unchanged.

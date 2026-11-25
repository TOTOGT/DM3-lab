import EDc4
import EDc2

/-!
UNTESTED until CI (isolated task, branch rpeigen-h31-x1-isolated).  Finite algebra / linear algebra / bookkeeping only.
RPEigen is NOT proved here; it is an explicit hypothesis of the final theorem, never an axiom.

`RPEigenH31` closes the arrow that was missing from the Lean chain: RPEigen -> Section83.H31gt3.
  * `Amaj_one_eq_tau`        : EDc0.Amaj 1 n = tau n  (n != 0).
  * `hprime_two_of_rpeigen`  : EDc4.RPEigen -> operator-norm bound with the sharp constant 2 (EDc4 proves it and
                               then weakens it to 51/25; here the weakening is omitted).  Same proof as EDc4.
  * `H31gt3_of_hprime_two`   : the proof of EDc2.H31gt3A_of_hprime204 specialised to X = 1 (every 51/50 replaced by 1,
                               hX : 1 <= X by le_refl), followed by the tail of EDb8.H31gt3_of_hprime.
  * `H31gt3_of_rpeigen`      : composition.
`HPrimeRestricted2` is an abbreviation for the conclusion of `hprime_two_of_rpeigen`; it is never assumed on its own
in the final composition.  No existing declaration is modified.
-/

namespace RPEigenH31

open SectionA4l SectionA4m SectionA4m2 SectionA4n SectionA4o

/-- `EDc0.Amaj 1 n = tau n` for `n != 0` (uses `EDc0.w_one`: `w 1 k = k + 1`). -/
theorem Amaj_one_eq_tau (n : ℕ) (hn : n ≠ 0) :
    EDc0.Amaj 1 n = ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) := by
  have hτ : ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ)
      = ∏ q ∈ n.primeFactors, ((n.factorization q : ℝ) + 1) := by
    rw [ArithmeticFunction.sigma_zero_apply, Nat.card_divisors hn, Nat.cast_prod]
    push_cast
    try rfl
  rw [hτ]
  unfold EDc0.Amaj
  exact Finset.prod_congr rfl (fun q _ => (EDc0.w_one _).1)

open Classical in
/-- `HPrime204Restricted` with the sharp constant `2` in place of `51/25`.  Prime `l = 3 mod 4` only.
Proved from `EDc4.RPEigen` by `hprime_two_of_rpeigen`; not an assumption of the final theorem. -/
def HPrimeRestricted2 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (_hp3 : p % 4 = 3) (_hp4 : 3 < p) (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p)
    (hxy : xs ^ 2 + ys ^ 2 = -1)
    (l : ℕ), l.Prime → l % 4 = 3 → Adm p l → ∀ f : EY p h2 xs ys hxy,
      inner ℂ (oneY p h2 xs ys hxy) f = 0 → inner ℂ (chiE p h2 xs ys hxy) f = 0 →
      ‖Tl p h2 xs ys hxy l f‖ ≤ 2 * Real.sqrt l * ‖f‖

open Classical in
/-- `RPEigen` gives the operator-norm bound with the sharp constant `2` (EDc4's proof, without the final weakening). -/
theorem hprime_two_of_rpeigen (hR : EDc4.RPEigen) : HPrimeRestricted2 := by
  intro p _ hp3 hp4 h2 xs ys hxy l hl hl4 hAdm f h1 hchi
  have hsymm : (Tl p h2 xs ys hxy l).IsSymmetric := Tl_symm p h2 xs ys hxy l hAdm
  obtain ⟨a, ha⟩ := Tl_one_eig p h2 xs ys hxy l hAdm
  obtain ⟨b, hb⟩ := Tl_chi_eig p h2 xs ys hxy l hAdm
  let W : Submodule ℂ (EY p h2 xs ys hxy) :=
    (Submodule.span ℂ {oneY p h2 xs ys hxy})ᗮ ⊓ (Submodule.span ℂ {chiE p h2 xs ys hxy})ᗮ
  have hmem : ∀ v, v ∈ W ↔
      (inner ℂ (oneY p h2 xs ys hxy) v = 0 ∧ inner ℂ (chiE p h2 xs ys hxy) v = 0) := by
    intro v
    simp only [W, Submodule.mem_inf, Submodule.mem_orthogonal_singleton_iff_inner_right]
  have hinv : ∀ v ∈ W, Tl p h2 xs ys hxy l v ∈ W := by
    intro v hv
    rw [hmem] at hv ⊢
    obtain ⟨hv1, hv2⟩ := hv
    constructor
    · have e := hsymm (oneY p h2 xs ys hxy) v
      rw [ha, inner_smul_left, hv1, mul_zero] at e
      exact e.symm
    · have e := hsymm (chiE p h2 xs ys hxy) v
      rw [hb, inner_smul_left, hv2, mul_zero] at e
      exact e.symm
  have hT' := hsymm.restrict_invariant hinv
  have hfW : f ∈ W := (hmem f).2 ⟨h1, hchi⟩
  have hB : (0 : ℝ) ≤ 2 * Real.sqrt l := by positivity
  have hev : ∀ (μ : ℝ) (v : W), v ≠ 0 →
      (Tl p h2 xs ys hxy l).restrict hinv v = (μ : ℂ) • v → |μ| ≤ 2 * Real.sqrt l := by
    intro μ v hv0 hv
    refine hR p hp3 hp4 h2 xs ys hxy l hl hl4 hAdm μ (v : EY p h2 xs ys hxy) ?_ ?_ ?_ ?_
    · intro h
      exact hv0 (Subtype.ext h)
    · exact ((hmem v).1 v.2).1
    · exact ((hmem v).1 v.2).2
    · have h' := congrArg Subtype.val hv
      simpa using h'
  have key := EDc4.norm_le_of_eigen_bound (E := W) ((Tl p h2 xs ys hxy l).restrict hinv) hT' (2 * Real.sqrt l) hB hev
    (⟨f, hfW⟩ : W)
  have e1 : ‖(Tl p h2 xs ys hxy l).restrict hinv ⟨f, hfW⟩‖ = ‖Tl p h2 xs ys hxy l f‖ := by
    first
    | (rw [← Submodule.coe_norm]; rfl)
    | simp [Submodule.coe_norm]
  have e2 : ‖(⟨f, hfW⟩ : W)‖ = ‖f‖ := by
    first
    | rfl
    | simp
  rw [e1, e2] at key
  exact key


open Classical in
/-- EDc2's proof at `X = 1`: the restricted prime-case bound with constant `2` gives `Section83.H31gt3`. -/
theorem H31gt3_of_hprime_two (hP : HPrimeRestricted2) : Section83.H31gt3 := by
  intro m hm2 hmq h64 p hp hp3 hpm hpP hp4
  haveI : Fact p.Prime := ⟨hp⟩
  have hm0 : 0 < m := by omega
  have hp2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff 2 p).1 h')
    omega
  obtain ⟨xs, ys, hxy⟩ := ZMod.sq_add_sq p (-1)
  have hAdm : Adm p m := ⟨Nat.odd_iff.2 hm2, hpm⟩
  have hprime0 := hP p hp3 hp4 hp2 xs ys hxy
  have hprime : ∀ l : ℕ, l.Prime → l % 4 = 3 → Adm p l → ∀ f : EY p hp2 xs ys hxy,
      inner ℂ (oneY p hp2 xs ys hxy) f = 0 → inner ℂ (chiE p hp2 xs ys hxy) f = 0 →
      ‖Tl p hp2 xs ys hxy l f‖ ≤ 2 * 1 * Real.sqrt l * ‖f‖ := by
    intro l hl hl4 hAl f h1f h2f
    rw [mul_one]
    exact hprime0 l hl hl4 hAl f h1f h2f
  -- the chain  b_p(2m) ≤ #S ≤ 8 TR ≤ 8 (σ ρ + τ √m (1-ρ))
  have h1 : (Section42.bp p (2 * m) : ℝ) ≤ ((((Section77a.Hn_finite m).toFinset).filter
        (fun x => SectionA4e.rhoT p xs ys x ∈ Kp p xs ys)).card : ℝ) := by
    exact_mod_cast EDb7.bp_le_S p hp2 xs ys hxy hpm
  have h2' := EDb4.card_S_le_eight_TR p hp2 xs ys hxy hpm
  have h3 := EDc1.pointwise_Kp_cheb p hp2 xs ys hxy 1 (le_refl _) hprime m hAdm hmq
  -- sizes
  set a : ℝ := ((OK p hp2 xs ys hxy (Kp p xs ys)).card : ℝ) with ha
  set Y : ℝ := (Fintype.card (SectionA3b.Yp p hp2 xs ys hxy) : ℝ) with hY
  have ha0 : 0 ≤ a := by positivity
  have hcardY : 12 * Fintype.card (SectionA3b.Yp p hp2 xs ys hxy) = p * (p ^ 2 - 1) := by
    have h := SectionA3b.card_PGL_eq_card_Yp_mul p hp2 xs ys hxy
    rw [EDa1.card_PGL2_eq p, Nat.card_eq_fintype_card (α := SectionA3b.Yp p hp2 xs ys hxy)] at h
    omega
  have hp1 : (1 : ℕ) ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
  have hYr : 12 * Y = (p : ℝ) * ((p : ℝ) ^ 2 - 1) := by
    have := congrArg (fun n : ℕ => (n : ℝ)) hcardY
    simp only [Nat.cast_mul, Nat.cast_sub hp1, Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat] at this
    rw [hY]; exact this
  have hpR : (3 : ℝ) < p := by exact_mod_cast hp4
  have hp0 : (0 : ℝ) < p := by linarith
  have hYpos : 0 < Y := by
    have : 0 < (p : ℝ) * ((p : ℝ) ^ 2 - 1) := by
      apply mul_pos hp0; nlinarith
    linarith
  have haO : 2 * a ≤ (p : ℝ) + 1 := by
    have := EDa9.card_OK_Kp_le p hp2 xs ys hxy
    rw [ha]; exact_mod_cast this
  have hq : (0 : ℝ) < (p : ℝ) * ((p : ℝ) - 1) := by nlinarith
  have hrho : a / Y ≤ 6 / ((p : ℝ) * ((p : ℝ) - 1)) := by
    rw [div_le_iff₀ hYpos]
    have e : 6 / ((p : ℝ) * ((p : ℝ) - 1)) * Y = 6 * Y / ((p : ℝ) * ((p : ℝ) - 1)) := by ring
    rw [e, le_div_iff₀ hq]
    have h5 := mul_le_mul_of_nonneg_right haO hq.le
    nlinarith [h5, hYr]
  have hrho0 : 0 ≤ a / Y := div_nonneg ha0 hYpos.le
  have hsig := EDb8.sig_pos hm0
  rw [Amaj_one_eq_tau m hm0.ne'] at h3
  have hSg : (Section79a.sg m : ℝ) = (Section51.sig m : ℝ) := rfl
  have hTau : ((ArithmeticFunction.sigma 0 m : ℕ) : ℝ) = (Section51.tau m : ℝ) := rfl
  rw [hSg, hTau] at h3
  set τ : ℝ := (Section51.tau m : ℝ) with hτ
  set σ : ℝ := (Section51.sig m : ℝ) with hσ
  have hτ0 : 0 ≤ τ * Real.sqrt m := by positivity
  have hkey : (Section42.bp p (2 * m) : ℝ) ≤ 8 * (σ * (6 / ((p : ℝ) * ((p : ℝ) - 1))) + τ * Real.sqrt m) := by
    have e1 : σ * (a / Y) ≤ σ * (6 / ((p : ℝ) * ((p : ℝ) - 1))) := mul_le_mul_of_nonneg_left hrho hsig.le
    have e2 : τ * Real.sqrt m * (1 - a / Y) ≤ τ * Real.sqrt m := by nlinarith
    linarith
  rw [div_le_iff₀ (by linarith [hsig])]
  have : (2 / ((p : ℝ) * ((p : ℝ) - 1)) + τ * Real.sqrt m / (3 * σ)) * (24 * σ)
      = 8 * (σ * (6 / ((p : ℝ) * ((p : ℝ) - 1))) + τ * Real.sqrt m) := by
    field_simp; ring
  rw [this]; exact hkey


end RPEigenH31

/-- The missing arrow: `RPEigen` (explicit hypothesis) implies `Section83.H31gt3`. -/
theorem RPEigenH31.H31gt3_of_rpeigen (hR : EDc4.RPEigen) : Section83.H31gt3 :=
  RPEigenH31.H31gt3_of_hprime_two (RPEigenH31.hprime_two_of_rpeigen hR)

#print axioms RPEigenH31.Amaj_one_eq_tau
#print axioms RPEigenH31.hprime_two_of_rpeigen
#print axioms RPEigenH31.H31gt3_of_hprime_two
#print axioms RPEigenH31.H31gt3_of_rpeigen

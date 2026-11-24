import EDc1
import EDb8

/-!
# EDc2.lean   (PRODUCTION-FACING; UNTESTED until compiled by CI)

Phase 8B.  The A-shaped consumer.  Imports `EDc1` (Chebyshev one-vector chain) and `EDb8` (production `HPrime`, `sig_pos`).
No `EDcert*`.

* `hprime204_of_hprime` : `EDb8.HPrime → EDcDefs.HPrime204Restricted`.  Trivial: `2 √l ‖f‖ ≤ (51/25) √l ‖f‖` and the primes are restricted.
* `H31gt3A_of_hprime204` : `EDcDefs.HPrime204Restricted → EDcDefs.H31gt3A`.  The proof of `EDb8.H31gt3_of_hprime` with exactly:
  `pointwise_Kp` ⟶ `EDc1.pointwise_Kp_cheb` at `X = 51/50` (so `2 X = 51/25`), the divisor term `τ(m)` ⟶ `EDc0.Amaj (51/50) m`,
  and the divisibility hypothesis `hmq` passed through.  Nothing else changes.

`HPrime204Restricted` stays an OPEN hypothesis.  Nothing here proves it; `H31gt3A_of_hprime204` is an implication.
-/

namespace EDc2

open SectionA4l SectionA4m SectionA4m2 SectionA4n SectionA4o

open Classical in
/-- `HPrime` (bound `2 √l ‖f‖`, all primes `l`) implies the relaxed restricted hypothesis (bound `(51/25) √l ‖f‖`, primes `l ≡ 3 mod 4`). -/
theorem hprime204_of_hprime (hP : EDb8.HPrime) : EDcDefs.HPrime204Restricted := by
  intro p _ hp3 hp4 h2 xs ys hxy l hl hl4 hAdm f h1 hchi
  have h := hP p hp3 hp4 h2 xs ys hxy l hl hAdm f h1 hchi
  have hn : 0 ≤ Real.sqrt l * ‖f‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith [h, hn]

open Classical in
/-- A-shaped E-D1c: `H31gt3A` follows from the relaxed restricted prime-case hypothesis `HPrime204Restricted`. -/
theorem H31gt3A_of_hprime204 (hP : EDcDefs.HPrime204Restricted) : EDcDefs.H31gt3A := by
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
  have e204 : (2 : ℝ) * (51 / 50) = 51 / 25 := by norm_num
  have hprime : ∀ l : ℕ, l.Prime → l % 4 = 3 → Adm p l → ∀ f : EY p hp2 xs ys hxy,
      inner ℂ (oneY p hp2 xs ys hxy) f = 0 → inner ℂ (chiE p hp2 xs ys hxy) f = 0 →
      ‖Tl p hp2 xs ys hxy l f‖ ≤ 2 * (51 / 50) * Real.sqrt l * ‖f‖ := by
    intro l hl hl4 hAl f h1f h2f
    rw [e204]
    exact hprime0 l hl hl4 hAl f h1f h2f
  -- the chain  b_p(2m) ≤ #S ≤ 8 TR ≤ 8 (σ ρ + τ √m (1-ρ))
  have h1 : (Section42.bp p (2 * m) : ℝ) ≤ ((((Section77a.Hn_finite m).toFinset).filter
        (fun x => SectionA4e.rhoT p xs ys x ∈ Kp p xs ys)).card : ℝ) := by
    exact_mod_cast EDb7.bp_le_S p hp2 xs ys hxy hpm
  have h2' := EDb4.card_S_le_eight_TR p hp2 xs ys hxy hpm
  have h3 := EDc1.pointwise_Kp_cheb p hp2 xs ys hxy (51 / 50) (by norm_num) hprime m hAdm hmq
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
  have hsig := sig_pos hm0
  have hA0 : 0 ≤ EDc0.Amaj (51 / 50) m := EDc0.Amaj_nonneg (by norm_num) m
  have hSg : (Section79a.sg m : ℝ) = (Section51.sig m : ℝ) := rfl
  rw [hSg] at h3
  set τ : ℝ := EDc0.Amaj (51 / 50) m with hτ
  set σ : ℝ := (Section51.sig m : ℝ) with hσ
  have hτ0 : 0 ≤ τ * Real.sqrt m := mul_nonneg hA0 (Real.sqrt_nonneg _)
  have hkey : (Section42.bp p (2 * m) : ℝ) ≤ 8 * (σ * (6 / ((p : ℝ) * ((p : ℝ) - 1))) + τ * Real.sqrt m) := by
    have e1 : σ * (a / Y) ≤ σ * (6 / ((p : ℝ) * ((p : ℝ) - 1))) := mul_le_mul_of_nonneg_left hrho hsig.le
    have e2 : τ * Real.sqrt m * (1 - a / Y) ≤ τ * Real.sqrt m := by nlinarith
    linarith
  rw [div_le_iff₀ (by linarith [hsig])]
  have : (2 / ((p : ℝ) * ((p : ℝ) - 1)) + τ * Real.sqrt m / (3 * σ)) * (24 * σ)
      = 8 * (σ * (6 / ((p : ℝ) * ((p : ℝ) - 1))) + τ * Real.sqrt m) := by
    field_simp; ring
  rw [this]; exact hkey


end EDc2
#print axioms EDc2.hprime204_of_hprime
#print axioms EDc2.H31gt3A_of_hprime204

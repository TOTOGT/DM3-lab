import Stage83cut
import EDa1
import EDa9
import EDb4
import EDb7

namespace EDb8
open SectionA4l SectionA4m SectionA4m2 SectionA4n SectionA4o

open Classical in
/-- The prime-case bound, as a hypothesis, uniformly in the data (p, xs, ys). -/
def HPrime : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (_hp3 : p % 4 = 3) (_hp4 : 3 < p) (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)
    (l : ℕ), l.Prime → Adm p l → ∀ f : EY p h2 xs ys hxy,
      inner ℂ (oneY p h2 xs ys hxy) f = 0 → inner ℂ (chiE p h2 xs ys hxy) f = 0 →
      ‖Tl p h2 xs ys hxy l f‖ ≤ 2 * Real.sqrt l * ‖f‖

theorem sig_pos {m : ℕ} (hm : 0 < m) : (0 : ℝ) < (Section51.sig m : ℝ) := by
  have : m ≤ Section51.sig m := by
    unfold Section51.sig
    rw [ArithmeticFunction.sigma_one_apply]
    exact Finset.single_le_sum (f := fun d => d) (fun _ _ => Nat.zero_le _) (Nat.mem_divisors_self m hm.ne')
  have : (0 : ℕ) < Section51.sig m := lt_of_lt_of_le hm this
  exact_mod_cast this

open Classical in
/-- E-D1c: H31gt3 follows from the prime-case Ramanujan-type bound. -/
theorem H31gt3_of_hprime (hP : HPrime) : Section83.H31gt3 := by
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
  have hprime := hP p hp3 hp4 hp2 xs ys hxy
  -- the chain  b_p(2m) ≤ #S ≤ 8 TR ≤ 8 (σ ρ + τ √m (1-ρ))
  have h1 : (Section42.bp p (2 * m) : ℝ) ≤ ((((Section77a.Hn_finite m).toFinset).filter
        (fun x => SectionA4e.rhoT p xs ys x ∈ Kp p xs ys)).card : ℝ) := by
    exact_mod_cast EDb7.bp_le_S p hp2 xs ys hxy hpm
  have h2' := EDb4.card_S_le_eight_TR p hp2 xs ys hxy hpm
  have h3 := pointwise_Kp p hp2 xs ys hxy hprime m hAdm
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

end EDb8
#print axioms EDb8.H31gt3_of_hprime

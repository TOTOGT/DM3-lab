import Stage83cut
import EDb8

/-!
EDweak -- DRAFT. Compiled only by the manual workflow euler-weak.yml (not part of any gated chain).
The final-theorem wrapper (EDcert.euler_1747_of_H31gt3_k) is deliberately omitted until H31gt3_of_weak compiles.

Purpose: replace the spectral hypothesis `EDb8.HPrime` (a norm bound for every admissible prime l on every f orthogonal
to 1 and chi) by the one-vector, one-sided quadratic-form bound that `EulerBridge.pointwise_of_quadform` actually
consumes (StageA4o.lean:4516, hypothesis `hquad`), for the single vector u_p = 1_{O_p} - mu_p.

Everything below is copied from, or assembled out of, declarations READ in StageA4o.lean / EDb8.lean (line numbers in
comments).  No new Mathlib lemma is invoked.  No sorry / admit / axiom.  Every line is UNTESTED.

UNTESTED RISKS (all of them):
  R1  `open Classical` / Fintype-instance agreement between my `def`s and the instances `pointwise_Yp` elaborated with;
  R2  defeq unfolding of `uP`, `indO`, `muO` when `hW'` is passed to a goal stated with `(fun z => f z - μ)`;
  R3  name resolution of `Tn_adj`, `sum_chi`, `const_OK`, `OK`, `mkY`, `Kp`, `TR` through the `open` line;
  R4  the transcribed proof bodies (copied by hand from the printed source) may have whitespace/bullet errors;
  R5  `weak_of_hprime` glue (sums) is assembled from the pattern in `pointwise_Yp`, not copied.
-/

namespace EDweak
open SectionA4l SectionA4m SectionA4m2 SectionA4n SectionA4o

variable (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)

open Classical in
/-- the indicator of O_p = image of K_p in Y_p (as in EDb8 / pointwise_Kp) -/
noncomputable def indO : SectionA3b.Yp p h2 xs ys hxy → ℝ :=
  fun y => if y ∈ OK p h2 xs ys hxy (Kp p xs ys) then (1 : ℝ) else 0

open Classical in
/-- mu_p = |O_p| / |Y_p| -/
noncomputable def muO : ℝ :=
  ((OK p h2 xs ys hxy (Kp p xs ys)).card : ℝ) / (Fintype.card (SectionA3b.Yp p h2 xs ys hxy) : ℝ)

/-- u_p = 1_{O_p} - mu_p -/
noncomputable def uP : SectionA3b.Yp p h2 xs ys hxy → ℝ :=
  fun y => indO p h2 xs ys hxy y - muO p h2 xs ys hxy

open Classical in
/-- WEAK at (p, xs, ys):  <u_p, T_m u_p> <= tau(m) sqrt(m) ||u_p||^2  (real, ONE-SIDED), only for the m that
H31gt3 quantifies over (odd, all prime factors = 3 mod 4, 64^4 <= 2m, p not dividing m, p <= Pn(2m)). -/
def WeakAt : Prop :=
  ∀ m : ℕ, m % 2 = 1 → (∀ q : ℕ, q.Prime → q ∣ m → q % 4 = 3) → 64 ^ 4 ≤ 2 * m →
    ∀ hpm : ¬ p ∣ m, p ≤ Section63b.Pn (2 * m) →
      ∑ y, uP p h2 xs ys hxy y * TR p h2 xs ys hxy m hpm (uP p h2 xs ys hxy) y
        ≤ ((ArithmeticFunction.sigma 0 m : ℕ) : ℝ) * Real.sqrt m * ∑ y, (uP p h2 xs ys hxy y) ^ 2

open Classical in
/-- the replacement hypothesis, uniform in the same data as HPrime (no l, no f, no inner products with 1, chi) -/
def HWeak : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (_ : p % 4 = 3) (_ : 3 < p) (h2 : (2 : ZMod p) ≠ 0)
    (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1), WeakAt p h2 xs ys hxy

open Classical in
/-- `SectionA4n.pointwise_Yp` (StageA4o:4766) with `hprime` and `hchiO` replaced by `hquad`.
Body copied from the printed source; only the final bullet differs (`exact hquad`). -/
theorem pointwise_Yp_of_quad
    (m : ℕ) (hm : Adm p m) (O : Finset (SectionA3b.Yp p h2 xs ys hxy)) (y₀ : SectionA3b.Yp p h2 xs ys hxy)
    (hy₀ : y₀ ∈ O)
    (hconst : ∀ y ∈ O, TR p h2 xs ys hxy m hm.2 (fun z => if z ∈ O then (1 : ℝ) else 0) y
        = TR p h2 xs ys hxy m hm.2 (fun z => if z ∈ O then (1 : ℝ) else 0) y₀)
    (hquad : ∑ y, ((if y ∈ O then (1 : ℝ) else 0) - (O.card : ℝ) / (Fintype.card (SectionA3b.Yp p h2 xs ys hxy) : ℝ))
          * TR p h2 xs ys hxy m hm.2
              (fun z => (if z ∈ O then (1 : ℝ) else 0) - (O.card : ℝ) / (Fintype.card (SectionA3b.Yp p h2 xs ys hxy) : ℝ)) y
        ≤ ((ArithmeticFunction.sigma 0 m : ℕ) : ℝ) * Real.sqrt m
          * ∑ y, ((if y ∈ O then (1 : ℝ) else 0) - (O.card : ℝ) / (Fintype.card (SectionA3b.Yp p h2 xs ys hxy) : ℝ)) ^ 2) :
    TR p h2 xs ys hxy m hm.2 (fun z => if z ∈ O then (1 : ℝ) else 0) y₀
      ≤ (Section79a.sg m : ℝ) * ((O.card : ℝ) / (Fintype.card (SectionA3b.Yp p h2 xs ys hxy) : ℝ))
        + ((ArithmeticFunction.sigma 0 m : ℕ) : ℝ) * Real.sqrt m
          * (1 - (O.card : ℝ) / (Fintype.card (SectionA3b.Yp p h2 xs ys hxy) : ℝ)) := by
  have hcard : (0 : ℝ) < (Fintype.card (SectionA3b.Yp p h2 xs ys hxy) : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.2 ⟨y₀⟩
  set μ : ℝ := (O.card : ℝ) / (Fintype.card (SectionA3b.Yp p h2 xs ys hxy) : ℝ) with hμdef
  have hμ : μ * (Fintype.card (SectionA3b.Yp p h2 xs ys hxy) : ℝ) = (O.card : ℝ) := by
    rw [hμdef]; field_simp
  have hmo : m % 2 = 1 := Nat.odd_iff.1 hm.1
  refine EulerBridge.pointwise_of_quadform (TR p h2 xs ys hxy m hm.2) (Section79a.sg m : ℝ)
    (((ArithmeticFunction.sigma 0 m : ℕ) : ℝ) * Real.sqrt m) μ O y₀ hy₀ _ (fun _ => rfl) ?_ ?_ hconst hμ ?_
  · funext y
    simp only [TR, LinearMap.coe_mk, AddHom.coe_mk]
    have : (fun z : SectionA3b.Yp p h2 xs ys hxy => (((1 : ℝ)) : ℂ)) = fun _ => (1 : ℂ) := by funext z; simp
    rw [this, SectionA4j.Tn_const p h2 xs ys hxy m hmo hm.2 y]
    simp
  · intro u v
    have e := Tn_adj p h2 xs ys hxy m hm.2 (fun z => (u z : ℂ)) (fun z => (v z : ℂ))
    have e2 := congrArg Complex.re e
    have L : ∀ y, (SectionA4g.Tn p h2 xs ys hxy m hm.2 (fun z => (u z : ℂ)) y * (starRingEnd ℂ) (v y : ℂ)).re
        = (SectionA4g.Tn p h2 xs ys hxy m hm.2 (fun z => (u z : ℂ)) y).re * v y := by
      intro y; simp [Complex.conj_ofReal]
    have R : ∀ y, ((u y : ℂ) * (starRingEnd ℂ) (SectionA4g.Tn p h2 xs ys hxy m hm.2 (fun z => (v z : ℂ)) y)).re
        = u y * (SectionA4g.Tn p h2 xs ys hxy m hm.2 (fun z => (v z : ℂ)) y).re := by
      intro y; simp
    simp only [Complex.re_sum, L, R] at e2
    exact e2.symm
  · exact hquad   -- <== the only changed line (original: `apply quad_bound p h2 xs ys hxy hprime m hm` + two bullets)

open Classical in
/-- The consumed step `h3` of EDb8.H31gt3_of_hprime, from WEAK.  `const_OK`, `mem_OK`, `Kp` as in `pointwise_Kp`
(StageA4o:5179).  NOTE: `Kp_has_nonsquare` / `sum_chi_OK` are NOT needed here. -/
theorem pointwise_Kp_of_weak (hW : WeakAt p h2 xs ys hxy)
    (m : ℕ) (hm : Adm p m) (hmq : ∀ q : ℕ, q.Prime → q ∣ m → q % 4 = 3) (h64 : 64 ^ 4 ≤ 2 * m)
    (hpP : p ≤ Section63b.Pn (2 * m)) :
    TR p h2 xs ys hxy m hm.2 (fun z => if z ∈ OK p h2 xs ys hxy (Kp p xs ys) then (1 : ℝ) else 0)
        (mkY p h2 xs ys hxy 1)
      ≤ (Section79a.sg m : ℝ) * (((OK p h2 xs ys hxy (Kp p xs ys)).card : ℝ)
            / (Fintype.card (SectionA3b.Yp p h2 xs ys hxy) : ℝ))
        + ((ArithmeticFunction.sigma 0 m : ℕ) : ℝ) * Real.sqrt m
          * (1 - ((OK p h2 xs ys hxy (Kp p xs ys)).card : ℝ)
            / (Fintype.card (SectionA3b.Yp p h2 xs ys hxy) : ℝ)) :=
  pointwise_Yp_of_quad p h2 xs ys hxy m hm (OK p h2 xs ys hxy (Kp p xs ys)) (mkY p h2 xs ys hxy 1)
    ((mem_OK p h2 xs ys hxy (Kp p xs ys) _).2 ⟨1, (Kp p xs ys).one_mem, rfl⟩)
    (fun y hy => const_OK p h2 xs ys hxy (Kp p xs ys) m hm.2 y hy)
    (hW m (Nat.odd_iff.1 hm.1) hmq h64 hm.2 hpP)

open Classical in
/-- Same conclusion as `EDb8.H31gt3_of_hprime` (EDb8:28).  Body copied from EDb8:29-91; the TWO changed lines are
marked `-- CHANGED`.  Everything else, including `EDa9.card_OK_Kp_le` and `EDb4`/`EDb7`, is unchanged. -/
theorem H31gt3_of_weak (hW : HWeak) : Section83.H31gt3 := by
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
  have hweak := hW p hp3 hp4 hp2 xs ys hxy                                   -- CHANGED (was: hprime := hP p ...)
  have h1 : (Section42.bp p (2 * m) : ℝ) ≤ ((((Section77a.Hn_finite m).toFinset).filter
        (fun x => SectionA4e.rhoT p xs ys x ∈ Kp p xs ys)).card : ℝ) := by
    exact_mod_cast EDb7.bp_le_S p hp2 xs ys hxy hpm
  have h2' := EDb4.card_S_le_eight_TR p hp2 xs ys hxy hpm
  have h3 := pointwise_Kp_of_weak p hp2 xs ys hxy (hweak) m hAdm hmq h64 hpP  -- CHANGED (was: pointwise_Kp ... hprime m hAdm)
  -- ===== from here: EDb8.lean lines 46-91, transcribed from the printed source (R4: re-diff against the file) =====
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

open Classical in
/-- VALIDATION ONLY (not used by the two theorems above): `HPrime → HWeak`.  Shows HWeak is implied by HPrime using the
SAME ingredients `pointwise_Yp` used (`quad_bound`, `Kp_has_nonsquare`, `sum_chi_OK`, `sum_chi`).  The two sum goals are
assembled from the pattern in StageA4o:4960-4975, not copied (R5). -/
theorem weak_of_hprime (hP : EDb8.HPrime) : HWeak := by
  intro p _ hp3 hp4 h2 xs ys hxy m hm2 hmq h64 hpm hpP
  have hprime := hP p hp3 hp4 h2 xs ys hxy
  have hAdm : Adm p m := ⟨Nat.odd_iff.2 hm2, hpm⟩
  obtain ⟨k₀, hk₀, hchi⟩ := Kp_has_nonsquare p h2 xs ys hxy
  have hchiO := sum_chi_OK p h2 xs ys hxy (Kp p xs ys) k₀ hk₀ hchi
  have hcard : (0 : ℝ) < (Fintype.card (SectionA3b.Yp p h2 xs ys hxy) : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.2 ⟨mkY p h2 xs ys hxy 1⟩
  have hμ : muO p h2 xs ys hxy * (Fintype.card (SectionA3b.Yp p h2 xs ys hxy) : ℝ)
      = ((OK p h2 xs ys hxy (Kp p xs ys)).card : ℝ) := by
    unfold muO; field_simp
  have hsumO : ∑ y, indO p h2 xs ys hxy y = ((OK p h2 xs ys hxy (Kp p xs ys)).card : ℝ) := by
    unfold indO; rw [Finset.sum_ite_mem, Finset.univ_inter]; simp
  exact quad_bound p h2 xs ys hxy hprime m hAdm (uP p h2 xs ys hxy)
    (by unfold uP
        simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [hsumO]; linarith [hμ])
    (by -- chi-sum of u_p: the last bullet of pointwise_Yp (StageA4o:4968-4975) with O := OK(Kp), mu := muO
      have hchiA : ∑ y, SectionA4k.chiY p h2 xs ys hxy y * ((indO p h2 xs ys hxy y : ℝ) : ℂ)
          = ∑ y ∈ OK p h2 xs ys hxy (Kp p xs ys), SectionA4k.chiY p h2 xs ys hxy y := by
        calc _ = ∑ y, if y ∈ OK p h2 xs ys hxy (Kp p xs ys) then SectionA4k.chiY p h2 xs ys hxy y else 0 :=
              Finset.sum_congr rfl (fun y _ => by unfold indO; split_ifs <;> simp)
          _ = _ := by rw [Finset.sum_ite_mem, Finset.univ_inter]
      have e : ∀ y, SectionA4k.chiY p h2 xs ys hxy y * ((uP p h2 xs ys hxy y : ℝ) : ℂ)
          = SectionA4k.chiY p h2 xs ys hxy y * ((indO p h2 xs ys hxy y : ℝ) : ℂ)
            - ((muO p h2 xs ys hxy : ℝ) : ℂ) * SectionA4k.chiY p h2 xs ys hxy y := by
        intro y; unfold uP; push_cast; ring
      simp only [e, Finset.sum_sub_distrib, ← Finset.mul_sum, hchiA, hchiO, sum_chi p h2 xs ys hxy]
      simp)

end EDweak

import StageA4o
import EDa6
import EDb3

namespace EDb4
open EDa4 SectionA4o

variable (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)

open Classical in
include h2 hxy in
/-- P4: 24 · (T_m 1_{O_K})(base) = #{α ∈ Q_m : Γ ρ(α) ∈ O_K} -/
theorem TR_ind_base (K : Subgroup (SectionA2.PGL2 p)) {m : ℕ} (hm : ¬ p ∣ m) :
    SectionA4n.TR p h2 xs ys hxy m hm (fun z => if z ∈ OK p h2 xs ys hxy K then (1 : ℝ) else 0)
        (mkY p h2 xs ys hxy 1)
      = ((((Section77a.Hn_finite m).toFinset).filter
          (fun x => mkY p h2 xs ys hxy (SectionA4e.rhoT p xs ys x) ∈ OK p h2 xs ys hxy K)).card : ℝ) / 24 := by
  unfold SectionA4n.TR
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  unfold SectionA4g.Tn
  have hU := SectionA4e.U_mk p h2 xs ys hxy m hm
    (fun z => ((if z ∈ OK p h2 xs ys hxy K then (1 : ℝ) else 0 : ℝ) : ℂ)) 1
  change (SectionA4e.U p h2 xs ys hxy m hm _ (Quotient.mk _ 1) / 24).re = _
  rw [hU]
  simp only [mul_one]
  have hsum : (∑ x ∈ (Section77a.Hn_finite m).toFinset,
      ((if (Quotient.mk (QuotientGroup.rightRel (SectionA3b.Gam p h2 xs ys hxy))
          (SectionA4e.rhoT p xs ys x) : SectionA3b.Yp p h2 xs ys hxy) ∈ OK p h2 xs ys hxy K
        then (1 : ℝ) else 0 : ℝ) : ℂ))
      = ((((Section77a.Hn_finite m).toFinset.filter
          (fun x => mkY p h2 xs ys hxy (SectionA4e.rhoT p xs ys x) ∈ OK p h2 xs ys hxy K)).card : ℕ) : ℂ) := by
    rw [← Complex.ofReal_sum, Finset.sum_boole]
    simp
  rw [hsum]
  have : ((((Section77a.Hn_finite m).toFinset.filter
          (fun x => mkY p h2 xs ys hxy (SectionA4e.rhoT p xs ys x) ∈ OK p h2 xs ys hxy K)).card : ℕ) : ℂ) / 24
      = ((((((Section77a.Hn_finite m).toFinset.filter
          (fun x => mkY p h2 xs ys hxy (SectionA4e.rhoT p xs ys x) ∈ OK p h2 xs ys hxy K)).card : ℝ) / 24 : ℝ)) : ℂ) := by
    push_cast; ring
  rw [this, Complex.ofReal_re]

open Classical in
include h2 hxy in
/-- #{α ∈ Q_m : ρ(α) ∈ K_p} ≤ 8 · (T_m 1_{O_p})(base)  — the counting heart of (3.6) -/
theorem card_S_le_eight_TR {m : ℕ} (hm : ¬ p ∣ m) :
    ((((Section77a.Hn_finite m).toFinset).filter
        (fun x => SectionA4e.rhoT p xs ys x ∈ Kp p xs ys)).card : ℝ)
      ≤ 8 * SectionA4n.TR p h2 xs ys hxy m hm
          (fun z => if z ∈ OK p h2 xs ys hxy (Kp p xs ys) then (1 : ℝ) else 0) (mkY p h2 xs ys hxy 1) := by
  rw [TR_ind_base p h2 xs ys hxy (Kp p xs ys) hm]
  have h3 := EDb3.three_mul_le p h2 xs ys hxy hm
  have h3' : (3 : ℝ) * ((((Section77a.Hn_finite m).toFinset).filter
        (fun x => SectionA4e.rhoT p xs ys x ∈ Kp p xs ys)).card : ℝ) ≤ ((((Section77a.Hn_finite m).toFinset).filter
          (fun x => mkY p h2 xs ys hxy (SectionA4e.rhoT p xs ys x) ∈ OK p h2 xs ys hxy (Kp p xs ys))).card : ℝ) := by
    exact_mod_cast h3
  linarith

end EDb4
#print axioms EDb4.TR_ind_base
#print axioms EDb4.card_S_le_eight_TR

import StageA4o
import EDa6
import EDa8
import EDb1

namespace EDb2
open EDa4 SectionA4o

open Classical in
/-- the eight integral units ±1, ±i, ±j, ±k -/
noncomputable def Int8 : Finset (Quaternion ℚ) :=
  ([⟨1,0,0,0⟩, ⟨-1,0,0,0⟩, ⟨0,1,0,0⟩, ⟨0,-1,0,0⟩, ⟨0,0,1,0⟩, ⟨0,0,-1,0⟩, ⟨0,0,0,1⟩, ⟨0,0,0,-1⟩] : List (Quaternion ℚ)).toFinset

theorem Int8_card : Int8.card ≤ 8 := by
  classical
  unfold Int8
  exact List.toFinset_card_le _

set_option maxHeartbeats 800000 in
/-- an integral quaternion of norm 1 is one of the eight -/
theorem int_unit_mem (x : Quaternion ℚ) (a b c d : ℤ)
    (ha : x.re = a) (hb : x.imI = b) (hc : x.imJ = c) (hd : x.imK = d)
    (hn : Quaternion.normSq x = 1) : x ∈ Int8 := by
  have hn' : x.re ^ 2 + x.imI ^ 2 + x.imJ ^ 2 + x.imK ^ 2 = 1 := by
    rw [Quaternion.normSq_def'] at hn; exact hn
  rw [ha, hb, hc, hd] at hn'
  have e : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = (1 : ℤ) := by exact_mod_cast hn'
  have ha1 : a ^ 2 ≤ 1 := by nlinarith [sq_nonneg b, sq_nonneg c, sq_nonneg d]
  have hb1 : b ^ 2 ≤ 1 := by nlinarith [sq_nonneg a, sq_nonneg c, sq_nonneg d]
  have hc1 : c ^ 2 ≤ 1 := by nlinarith [sq_nonneg b, sq_nonneg a, sq_nonneg d]
  have hd1 : d ^ 2 ≤ 1 := by nlinarith [sq_nonneg b, sq_nonneg c, sq_nonneg a]
  have ha2 : -1 ≤ a ∧ a ≤ 1 := by constructor <;> nlinarith
  have hb2 : -1 ≤ b ∧ b ≤ 1 := by constructor <;> nlinarith
  have hc2 : -1 ≤ c ∧ c ≤ 1 := by constructor <;> nlinarith
  have hd2 : -1 ≤ d ∧ d ≤ 1 := by constructor <;> nlinarith
  have hx : x = ⟨(a : ℚ), (b : ℚ), (c : ℚ), (d : ℚ)⟩ := by
    ext <;> simp [ha, hb, hc, hd]
  rw [hx]
  obtain ⟨a1, a2⟩ := ha2
  obtain ⟨b1, b2⟩ := hb2
  obtain ⟨c1, c2⟩ := hc2
  obtain ⟨d1, d2⟩ := hd2
  clear hx hn hn' ha hb hc hd
  interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d <;>
    first | (unfold Int8; simp; done) | (exfalso; norm_num at e)

variable (p : ℕ) [Fact p.Prime]

theorem unit_in_K (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)
    (w : Quaternion ℚ) (hQ : Section71d.QH w) (hn : Quaternion.normSq w = 1)
    (hK : SectionA4e.rhoT p xs ys w ∈ Kp p xs ys) : w ∈ Int8 := by
  have hu : IsUnit (Section74b.red p xs ys w) :=
    SectionA1.red_isUnit p h2 xs ys hxy hQ 1 (by simpa using hn) (SectionA3a.not_dvd_one_p p)
  rcases hQ with ⟨a, b, c, d, ha, hb, hc, hd⟩ | ⟨a, b, c, d, ha, hb, hc, hd⟩
  · exact int_unit_mem w a b c d ha hb hc hd hn
  · exact absurd hK (EDb1.half_unit_not_in_K p h2 xs ys hxy w a b c d ha hb hc hd hn hu)

end EDb2
#print axioms EDb2.unit_in_K

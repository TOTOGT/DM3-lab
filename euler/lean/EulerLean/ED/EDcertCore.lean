import Stage83cut
import EDcertDefs

/-! # EDcertCore: soundness of the kernel-checked finite certificate for Euler 1747 (n = 2 mod 4, n < 64^4)

Replaces `Euler1747.allOk_true` (proved there by `native_decide`, axiom `Lean.ofReduceBool`).  Statement preserved: every n = 2 mod 4 with
n < 64^4 is a sum of two `EulerGood` numbers with the smaller summand <= 313.
  * `good_of_sq_add_sq`: gcd(x,y)=1 and x^2+y^2 odd  =>  EulerGood (x^2+y^2)  (from `ZMod.exists_sq_eq_neg_one_iff`).
  * For each chunk of 2^16 consecutive n the kernel computes, with GMP bit operations, the bitmask G of all odd primitive sums x^2+y^2 in the
    window, ORs its shifts by the 43 candidate small summands, and checks that every n = 2 mod 4 of the chunk is covered (`chunkOk c`).
  * `chunk_sound`: a covered bit yields an explicit primitive representation, hence EulerGood (n - a).  Soundness does not depend on how the
    pairs (x,y) are enumerated; the enumeration only affects whether the check succeeds.
  * 256 theorems `chunk_c : chunkOk c = true := by decide +kernel` (files EDcertC0..C7), c < 256, cover n < 2^24 = 64^4.
No `native_decide`, no new axioms. -/

namespace EDcert
open Euler1747

/-! ### Soundness of the certificate -/

theorem good_of_sq_add_sq {x y : ℕ} (hg : Nat.gcd x y = 1) (hodd : (x * x + y * y) % 2 = 1) :
    EulerGood (x * x + y * y) := by
  refine ⟨by omega, fun p hp hpd => ?_⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    obtain ⟨k, hk⟩ := hpd
    omega
  haveI := Fact.mk hp
  have h0 : ((x * x + y * y : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hpd
  have hz : (y : ZMod p) * y = -((x : ZMod p) * x) := by
    push_cast at h0
    linear_combination h0
  have hmod : p % 4 ≠ 3 := by
    by_cases hx : (x : ZMod p) = 0
    · exfalso
      have hy : (y : ZMod p) = 0 := by
        rw [hx] at hz
        simpa using hz
      have h1 : p ∣ x := (ZMod.natCast_eq_zero_iff _ _).1 hx
      have h2 : p ∣ y := (ZMod.natCast_eq_zero_iff _ _).1 hy
      have h3 : p ∣ Nat.gcd x y := Nat.dvd_gcd h1 h2
      rw [hg] at h3
      exact hp.one_lt.ne' (Nat.dvd_one.1 h3)
    · apply ZMod.exists_sq_eq_neg_one_iff.1
      have hxinv : (x : ZMod p) * (x : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ hx
      refine ⟨(y : ZMod p) * (x : ZMod p)⁻¹, ?_⟩
      linear_combination (-((x : ZMod p)⁻¹ ^ 2)) * hz + ((x : ZMod p) * (x : ZMod p)⁻¹ + 1) * hxinv
  have hodd' : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  omega

theorem tb_one_shift (k j : ℕ) : (1 <<< k).testBit j = true ↔ j = k := by
  rw [Nat.testBit_shiftLeft]
  simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.testBit_one_eq_true_iff_self_eq_zero]
  omega

theorem foldY_sound (x a L : ℕ) (l : List ℕ) (m j : ℕ) :
    (l.foldl (stepY x a L) m).testBit j = true →
    m.testBit j = true ∨ ∃ y ∈ l, Nat.gcd x y = 1 ∧ (x + y) % 2 = 1 ∧ a ≤ x * x + y * y ∧
      x * x + y * y < a + L ∧ x * x + y * y - a = j := by
  induction l generalizing m with
  | nil => intro h; exact Or.inl h
  | cons y t ih =>
    intro h
    simp only [List.foldl_cons] at h
    rcases ih _ h with h1 | ⟨y', hy', hr⟩
    · unfold stepY at h1
      split_ifs at h1 with hc
      · rw [Nat.testBit_lor, Bool.or_eq_true] at h1
        rcases h1 with h2 | h2
        · exact Or.inl h2
        · right
          refine ⟨y, List.mem_cons_self .., hc.1, hc.2.1, hc.2.2.1, hc.2.2.2, ?_⟩
          exact ((tb_one_shift _ _).1 h2).symm
      · exact Or.inl h1
    · exact Or.inr ⟨y', List.mem_cons_of_mem _ hy', hr⟩

theorem rowMask_sound (a L x j : ℕ) (h : (rowMask a L x).testBit j = true) :
    ∃ y, Nat.gcd x y = 1 ∧ (x + y) % 2 = 1 ∧ a ≤ x * x + y * y ∧ x * x + y * y < a + L ∧
      x * x + y * y - a = j := by
  unfold rowMask at h
  by_cases h1 : a + L ≤ x * x
  · rw [if_pos h1] at h
    simp at h
  · rw [if_neg h1] at h
    dsimp only at h
    rcases foldY_sound x a L _ 0 j h with h2 | ⟨y, -, hy⟩
    · simp at h2
    · exact ⟨y, hy⟩

theorem foldOr_sound {α : Type} (f : α → ℕ) (l : List α) (m j : ℕ) :
    (l.foldl (fun m x => m ||| f x) m).testBit j = true →
    m.testBit j = true ∨ ∃ x ∈ l, (f x).testBit j = true := by
  induction l generalizing m with
  | nil => intro h; exact Or.inl h
  | cons y t ih =>
    intro h
    simp only [List.foldl_cons] at h
    rcases ih _ h with h1 | ⟨x, hx, hr⟩
    · rw [Nat.testBit_lor, Bool.or_eq_true] at h1
      rcases h1 with h2 | h2
      · exact Or.inl h2
      · exact Or.inr ⟨y, List.mem_cons_self .., h2⟩
    · exact Or.inr ⟨x, List.mem_cons_of_mem _ hx, hr⟩

theorem foldOr1_mono (f : ℕ → ℕ) (l : List ℕ) (m j : ℕ) (h : m.testBit j = true) :
    (l.foldl (fun m i => m ||| (1 <<< f i)) m).testBit j = true := by
  induction l generalizing m with
  | nil => exact h
  | cons y t ih =>
    simp only [List.foldl_cons]
    apply ih
    rw [Nat.testBit_lor, Bool.or_eq_true]
    exact Or.inl h

theorem foldOr1_mem (f : ℕ → ℕ) (l : List ℕ) (m i : ℕ) (hi : i ∈ l) :
    (l.foldl (fun m i => m ||| (1 <<< f i)) m).testBit (f i) = true := by
  induction l generalizing m with
  | nil => simp at hi
  | cons y t ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 hi with rfl | ht
    · apply foldOr1_mono
      rw [Nat.testBit_lor, Bool.or_eq_true]
      exact Or.inr ((tb_one_shift _ _).2 rfl)
    · exact ih _ ht

theorem candsL_good : ∀ a ∈ candsL, EulerGood a ∧ a ≤ 313 := by
  have hc : candCert.all (fun p => Nat.gcd p.1 p.2 == 1 && (p.1 * p.1 + p.2 * p.2) % 2 == 1 &&
      decide (p.1 * p.1 + p.2 * p.2 ≤ 313)) = true := by decide
  intro a ha
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
  have := List.all_eq_true.1 hc p hp
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  exact ⟨good_of_sq_add_sq this.1.1 this.1.2, this.2⟩

theorem chunk_sound (c : ℕ) (h : chunkOk c = true) (n : ℕ) (h1 : c * W ≤ n) (h2 : n < c * W + W)
    (hn : n % 4 = 2) : ∃ a, a < n ∧ a ≤ 313 ∧ EulerGood a ∧ EulerGood (n - a) := by
  have hg0 : g0 c ≤ c * W := by unfold g0; split_ifs <;> omega
  have hg0' : c ≠ 0 → c * W - g0 c = 320 := by intro hc; unfold g0; rw [if_neg hc]; unfold W; omega
  have heq : cover c &&& tgt c = tgt c := by simpa [chunkOk] using h
  obtain ⟨i, hi, hpos⟩ : ∃ i, i < W / 4 ∧ n - g0 c = c * W - g0 c + 2 + 4 * i := by
    refine ⟨(n - c * W) / 4, ?_, ?_⟩ <;> unfold W at * <;> omega
  have hT : (tgt c).testBit (n - g0 c) = true := by
    rw [hpos]
    exact foldOr1_mem (fun i => c * W - g0 c + 2 + 4 * i) (List.range (W / 4)) 0 i (List.mem_range.2 hi)
  have hC : (cover c).testBit (n - g0 c) = true := by
    have := congrArg (fun z => z.testBit (n - g0 c)) heq
    simp only [Nat.testBit_land, hT, Bool.and_true] at this
    simpa using this
  unfold cover at hC
  rcases foldOr_sound (fun a => Gm c <<< a) candsL 0 _ hC with h0 | ⟨a, ha, hga⟩
  · simp at h0
  · rw [Nat.testBit_shiftLeft] at hga
    simp only [Bool.and_eq_true, decide_eq_true_eq, ge_iff_le] at hga
    obtain ⟨hap, hG⟩ := hga
    unfold Gm at hG
    rcases foldOr_sound (fun x => rowMask (g0 c) (Lg c) x) (xsL (g0 c) (Lg c)) 0 _ hG with h0 | ⟨x, -, hx⟩
    · simp at h0
    · obtain ⟨y, hgcd, hpar, hlo, hhi, hj⟩ := rowMask_sound _ _ _ _ hx
      have hb : x * x + y * y = n - a := by omega
      have hodd : (x * x + y * y) % 2 = 1 := by
        have hx2 := Nat.mod_two_eq_zero_or_one x
        have hy2 := Nat.mod_two_eq_zero_or_one y
        rcases hx2 with hx2 | hx2 <;> rcases hy2 with hy2 | hy2 <;>
          simp [Nat.add_mod, Nat.mul_mod, hx2, hy2] at hpar ⊢
      have hgood := good_of_sq_add_sq hgcd hodd
      rw [hb] at hgood
      have ⟨hag, ha313⟩ := candsL_good a ha
      refine ⟨a, ?_, ha313, hag, hgood⟩
      have := hgood.1
      omega


end EDcert
#print axioms EDcert.chunk_sound

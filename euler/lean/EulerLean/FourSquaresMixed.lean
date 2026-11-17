/-
  FourSquaresMixed.lean   (draft written 2026-11-16 by Claude; UNTESTED. 2026-11-16 first compile gave 2 errors, patched, not re-run)

  Source: equation (2.2) of Howe-Huffman-Kohlmeyer-Kruer, hexagon:2611.00370v1.

  WHAT THIS FILE PROVES, if it compiles:
    For n with n % 4 = 2, let R n be the set of signed, ordered representations
    (x0,x1,x2,x3) in Z^4 with x0^2+x1^2+x2^2+x3^2 = n, and let Rmix be those in which
    x0+x1 is odd and x2+x3 is odd.  Then   3 * |Rmix| = 2 * |R|,   i.e. |Rmix| = (2/3)|R|.

  WHAT THIS FILE DOES NOT PROVE:
    It does NOT prove Jacobi's four-square formula |R n| = 24 sigma(m), and it does NOT say
    anything about |R n| itself; it only relates two counts.  Jacobi's count is not in Mathlib
    (checked in the geometry checkout, Mathlib dated 2026-07-13) and is a separate, larger job.

  Proof idea (the paper's): n = 2 mod 4 forces exactly two coordinates to be odd.  Look at the
  three ways to split the coordinates into two pairs: {01|23}, {02|13}, {03|12}.  An x counts as
  "mixed" for a split when its two odd coordinates lie in different pairs.  Each x is mixed for
  EXACTLY TWO of the three splits, and swapping coordinates shows the three splits have the same
  count.  So 3 * |Rmix| = 2 * |R|.

  Run:  cd ~/Desktop/DM3-lab/euler/lean
        lake env lean EulerLean/FourSquaresMixed.lean
-/
import Mathlib

namespace FourSq

/-- Signed ordered representations of `n` as a sum of four squares, as a finite set. -/
noncomputable def R (n : ℕ) : Finset (Fin 4 → ℤ) :=
  (Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(n : ℤ)) n).filter
    (fun x => ∑ i, x i ^ 2 = (n : ℤ))

/-- Split {01|23}: both pairs have opposite parity. -/
def S1 (x : Fin 4 → ℤ) : Prop := (x 0 + x 1) % 2 = 1 ∧ (x 2 + x 3) % 2 = 1
/-- Split {02|13}. -/
def S2 (x : Fin 4 → ℤ) : Prop := (x 0 + x 2) % 2 = 1 ∧ (x 1 + x 3) % 2 = 1
/-- Split {03|12}. -/
def S3 (x : Fin 4 → ℤ) : Prop := (x 0 + x 3) % 2 = 1 ∧ (x 1 + x 2) % 2 = 1

instance : DecidablePred S1 := fun x => by unfold S1; infer_instance
instance : DecidablePred S2 := fun x => by unfold S2; infer_instance
instance : DecidablePred S3 := fun x => by unfold S3; infer_instance

theorem sq_mod_four (x : ℤ) : x ^ 2 % 4 = x % 2 := by
  obtain ⟨k, hk | hk⟩ : ∃ k, x = 2 * k ∨ x = 2 * k + 1 := ⟨x / 2, by omega⟩
  · subst hk
    have : (2 * k) ^ 2 = 4 * (k ^ 2) := by ring
    rw [this]; omega
  · subst hk
    have : (2 * k + 1) ^ 2 = 4 * (k ^ 2 + k) + 1 := by ring
    rw [this]; omega

/-- Each representation is mixed for exactly two of the three splits. -/
theorem pointwise (n : ℕ) (hn : n % 4 = 2) (x : Fin 4 → ℤ) (hx : x ∈ R n) :
    ((if S1 x then 1 else 0) + (if S2 x then 1 else 0) + (if S3 x then 1 else 0) : ℕ) = 2 := by
  have hs : ∑ i, x i ^ 2 = (n : ℤ) := (Finset.mem_filter.1 hx).2
  rw [Fin.sum_univ_four] at hs
  have h0 := sq_mod_four (x 0)
  have h1 := sq_mod_four (x 1)
  have h2 := sq_mod_four (x 2)
  have h3 := sq_mod_four (x 3)
  unfold S1 S2 S3
  split_ifs <;> omega

/-- Permuting coordinates keeps us inside `R n`. -/
theorem comp_mem_R (σ : Equiv.Perm (Fin 4)) {n : ℕ} {x : Fin 4 → ℤ} (hx : x ∈ R n) :
    (x ∘ σ) ∈ R n := by
  simp only [R, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc] at hx ⊢
  obtain ⟨hb, hs⟩ := hx
  refine ⟨fun i => hb (σ i), ?_⟩
  have := Equiv.sum_comp σ (fun i => x i ^ 2)
  simpa [Function.comp] using this.trans hs

theorem comp_involution (σ : Equiv.Perm (Fin 4)) (h2 : ∀ i, σ (σ i) = i) (x : Fin 4 → ℤ) :
    (x ∘ σ) ∘ σ = x := by
  funext i; simp [Function.comp, h2]

/-- If swapping coordinates by an involution `σ` carries `p` to `q`, the two counts agree. -/
theorem card_filter_eq (σ : Equiv.Perm (Fin 4)) (h2 : ∀ i, σ (σ i) = i) (n : ℕ)
    (p q : (Fin 4 → ℤ) → Prop) [DecidablePred p] [DecidablePred q]
    (hpq : ∀ x, q (x ∘ σ) ↔ p x) :
    ((R n).filter p).card = ((R n).filter q).card := by
  have hqp : ∀ x, p (x ∘ σ) ↔ q x := fun x => by
    rw [← hpq (x ∘ σ), comp_involution σ h2 x]
  refine Finset.card_bij' (fun x _ => x ∘ σ) (fun x _ => x ∘ σ) ?_ ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨comp_mem_R σ hx.1, (hpq x).2 hx.2⟩
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨comp_mem_R σ hx.1, (hqp x).2 hx.2⟩
  · intro x _; exact comp_involution σ h2 x
  · intro x _; exact comp_involution σ h2 x

/-- Equation (2.2) of the paper:  |Rmix| = (2/3) |R|  for n = 2 mod 4. -/
theorem mixed_count (n : ℕ) (hn : n % 4 = 2) :
    3 * ((R n).filter S1).card = 2 * (R n).card := by
  -- swap coordinates 1 and 2:  S2 (x ∘ σ) ↔ S1 x
  have a0 : Equiv.swap (1 : Fin 4) 2 0 = 0 := by decide
  have a1 : Equiv.swap (1 : Fin 4) 2 1 = 2 := by decide
  have a2 : Equiv.swap (1 : Fin 4) 2 2 = 1 := by decide
  have a3 : Equiv.swap (1 : Fin 4) 2 3 = 3 := by decide
  have e12 : ((R n).filter S1).card = ((R n).filter S2).card :=
    card_filter_eq (Equiv.swap 1 2) (fun i => Equiv.swap_apply_self _ _ i) n S1 S2
      (fun x => by simp [S1, S2, Function.comp, a0, a1, a2, a3])
  -- swap coordinates 1 and 3:  S3 (x ∘ σ) ↔ S1 x
  have b0 : Equiv.swap (1 : Fin 4) 3 0 = 0 := by decide
  have b1 : Equiv.swap (1 : Fin 4) 3 1 = 3 := by decide
  have b2 : Equiv.swap (1 : Fin 4) 3 2 = 2 := by decide
  have b3 : Equiv.swap (1 : Fin 4) 3 3 = 1 := by decide
  have e13 : ((R n).filter S1).card = ((R n).filter S3).card :=
    card_filter_eq (Equiv.swap 1 3) (fun i => Equiv.swap_apply_self _ _ i) n S1 S3
      (fun x => by simp only [S1, S3, Function.comp_apply, b0, b1, b2, b3]; omega)
  have hsum : ((R n).filter S1).card + ((R n).filter S2).card + ((R n).filter S3).card
      = 2 * (R n).card := by
    simp only [Finset.card_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (fun x hx => pointwise n hn x hx)]
    simp [Finset.sum_const, mul_comm]
  omega

/-! Numerical sanity check (NOT in Lean: `R` is noncomputable). Python brute force gave
    3*|Rmix| = 2*|R| for n = 2,6,10,14,18,22; for n = 6 the pair is (|R|, |Rmix|) = (96, 64). -/

end FourSq

#print axioms FourSq.mixed_count

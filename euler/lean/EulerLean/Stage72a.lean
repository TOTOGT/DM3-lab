import Mathlib

/-! # Stage72a: exactly 24 Hurwitz quadruples of norm 1 (UNTESTED when written; no compiler run yet)

WHAT THIS FILE PROVES, if it compiles.  The set of rational quadruples x = (x0,x1,x2,x3) that are Hurwitz (all four
integers, or all four in Z + 1/2) with  x0^2 + x1^2 + x2^2 + x3^2 = 1  has exactly 24 elements.

Hand derivation.  Put u = 2x.  Then u has integer entries, all even or all odd, with sum of squares 4.  Each |u_i| <= 2
because u_i^2 <= 4.  All even: one entry +-2 and the rest 0, so 4 positions x 2 signs = 8 (integral quaternions +-1, +-i, +-j, +-k).
All odd: every entry is +-1 (an odd entry has square 1 or 9, and 9 > 4), so 2^4 = 16 (the quaternions (+-1 +-i +-j +-k)/2).
Total 24.  The Lean below does not do this case split: it bounds the entries, then counts the finite set of numerators by
`decide +kernel`, then transports the count through the injective map u -> u/2.

DOES NOT PROVE: that these 24 elements are the units of the Hurwitz order (inverse = conjugate; that needs the ring structure),
nor anything about elements of other norms.  It is the finite fact "number of elements of norm 1 is 24" used by the Jacobi
count (JACOBI_PLAN.md step 1, in the form: units = Hurwitz quadruples of norm 1). -/

namespace Section72a

/-- all four coordinates integers, or all four in Z + 1/2 (same definition as Section71.IsHur) -/
def IsHur (q : Fin 4 → ℚ) : Prop :=
  (∀ i, ∃ z : ℤ, q i = z) ∨ (∀ i, ∃ z : ℤ, q i = z + 1 / 2)

/-- numerators u = 2x: entries all even or all odd, sum of squares 4; entries bounded by 2 so this is a finite set -/
def U : Finset (Fin 4 → ℤ) :=
  (Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-2 : ℤ) 2).filter
    (fun u => ((∀ i, u i % 2 = 0) ∨ (∀ i, u i % 2 = 1)) ∧ ∑ i, u i ^ 2 = 4)

theorem U_card : U.card = 24 := by
  first
  | decide +kernel
  | rfl

theorem memU (u : Fin 4 → ℤ) :
    u ∈ U ↔ ((∀ i, u i % 2 = 0) ∨ (∀ i, u i % 2 = 1)) ∧ ∑ i, u i ^ 2 = 4 := by
  constructor
  · intro h
    exact (Finset.mem_filter.1 h).2
  · intro h
    have hb : ∀ i, -2 ≤ u i ∧ u i ≤ 2 := by
      intro i
      have hle : u i ^ 2 ≤ ∑ j, u j ^ 2 :=
        Finset.single_le_sum (f := fun j => u j ^ 2) (fun j _ => sq_nonneg (u j)) (Finset.mem_univ i)
      have h4 : u i ^ 2 ≤ 4 := by rw [h.2] at hle; exact hle
      constructor
      · by_contra hc
        push Not at hc
        nlinarith
      · by_contra hc
        push Not at hc
        nlinarith
    exact Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 (fun i => Finset.mem_Icc.2 (hb i)), h⟩

/-- halving map from numerators to rational quadruples -/
def f (u : Fin 4 → ℤ) : Fin 4 → ℚ := fun i => (u i : ℚ) / 2

theorem f_inj : Function.Injective f := by
  intro u v h
  funext i
  have h' : (u i : ℚ) / 2 = (v i : ℚ) / 2 := congrFun h i
  have h'' : (u i : ℚ) = (v i : ℚ) := by linarith
  exact_mod_cast h''

theorem hur_num (x : Fin 4 → ℚ) (hx : IsHur x) (hs : ∑ i, x i ^ 2 = 1) :
    ∃ u : Fin 4 → ℤ, u ∈ U ∧ f u = x := by
  rcases hx with h | h
  · choose z hz using h
    have e : ∑ i, (((2 * z i : ℤ) : ℚ)) ^ 2 = 4 * ∑ i, x i ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hz i]
      push_cast
      ring
    have e2 : ((∑ i, (2 * z i) ^ 2 : ℤ) : ℚ) = 4 := by
      push_cast
      push_cast at e
      rw [e, hs]
      norm_num
    have e3 : ∑ i, (2 * z i) ^ 2 = 4 := by exact_mod_cast e2
    refine ⟨fun i => 2 * z i, (memU _).2 ⟨Or.inl (fun i => by omega), e3⟩, ?_⟩
    funext i
    show ((2 * z i : ℤ) : ℚ) / 2 = x i
    rw [hz i]
    push_cast
    ring
  · choose z hz using h
    have e : ∑ i, (((2 * z i + 1 : ℤ) : ℚ)) ^ 2 = 4 * ∑ i, x i ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hz i]
      push_cast
      ring
    have e2 : ((∑ i, (2 * z i + 1) ^ 2 : ℤ) : ℚ) = 4 := by
      push_cast
      push_cast at e
      rw [e, hs]
      norm_num
    have e3 : ∑ i, (2 * z i + 1) ^ 2 = 4 := by exact_mod_cast e2
    refine ⟨fun i => 2 * z i + 1, (memU _).2 ⟨Or.inr (fun i => by omega), e3⟩, ?_⟩
    funext i
    show ((2 * z i + 1 : ℤ) : ℚ) / 2 = x i
    rw [hz i]
    push_cast
    ring

theorem f_mem (u : Fin 4 → ℤ) (hu : u ∈ U) : IsHur (f u) ∧ ∑ i, (f u i) ^ 2 = 1 := by
  have h := (memU u).1 hu
  constructor
  · rcases h.1 with h1 | h1
    · left
      intro i
      refine ⟨u i / 2, ?_⟩
      have hk : u i = 2 * (u i / 2) := by have := h1 i; omega
      show (u i : ℚ) / 2 = ((u i / 2 : ℤ) : ℚ)
      have hk' : (u i : ℚ) = 2 * ((u i / 2 : ℤ) : ℚ) := by exact_mod_cast hk
      rw [hk']
      ring
    · right
      intro i
      refine ⟨u i / 2, ?_⟩
      have hk : u i = 2 * (u i / 2) + 1 := by have := h1 i; omega
      show (u i : ℚ) / 2 = ((u i / 2 : ℤ) : ℚ) + 1 / 2
      have hk' : (u i : ℚ) = 2 * ((u i / 2 : ℤ) : ℚ) + 1 := by exact_mod_cast hk
      rw [hk']
      ring
  · have hq : (∑ i, (u i : ℚ) ^ 2) = 4 := by
      have := congrArg (fun t : ℤ => (t : ℚ)) h.2
      simpa using this
    have hs : ∑ i, ((u i : ℚ) / 2) ^ 2 = (∑ i, (u i : ℚ) ^ 2) / 4 := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    show ∑ i, ((u i : ℚ) / 2) ^ 2 = 1
    rw [hs, hq]
    norm_num

theorem units_set :
    {x : Fin 4 → ℚ | IsHur x ∧ ∑ i, x i ^ 2 = 1} = f '' (U : Set (Fin 4 → ℤ)) := by
  ext x
  constructor
  · rintro ⟨hx, hs⟩
    obtain ⟨u, hu, rfl⟩ := hur_num x hx hs
    exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact f_mem u hu

/-- there are exactly 24 Hurwitz quadruples of norm 1 -/
theorem units_count :
    {x : Fin 4 → ℚ | IsHur x ∧ ∑ i, x i ^ 2 = 1}.ncard = 24 := by
  rw [units_set, Set.ncard_image_of_injective _ f_inj]
  first
  | (rw [Set.ncard_coe_finset]; exact U_card)
  | (rw [Set.ncard_eq_toFinset_card' (U : Set (Fin 4 → ℤ))]; simpa using U_card)

end Section72a

#print axioms Section72a.units_count

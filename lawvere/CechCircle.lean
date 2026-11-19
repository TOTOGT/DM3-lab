/-
  CechCircle.lean — the smallest honest local-to-global example, machine-checked.
  For Principia Orthogona, Book VIII ch13 (holology), "Holology, computed".

  STATUS: UNTESTED until the Actions run says otherwise. Core Lean 4 only.

  SETUP (by hand, not formalised here). Cover the circle S¹ by two open arcs U, V
  whose intersection U ∩ V has two components (call them 1 and 2). U and V are
  contractible, so a locally constant sheaf of rank 1 is trivial on each. Mayer–Vietoris:
      0 → H⁰(S¹) → H⁰(U) ⊕ H⁰(V) --d--> H⁰(U∩V) → H¹(S¹) → H¹(U) ⊕ H¹(V) = 0
  so  H⁰(S¹) = ker d  and  H¹(S¹) = coker d,  with d : Z² → Z².

    constant sheaf Z   : d(a,b) = (b - a, b - a)
    twisted sheaf  Z~  : d(a,b) = (b - a, b + a)   (a sign flip across component 2,
                                                    i.e. the Möbius gluing)

  WHAT THIS FILE PROVES (and only this): the two linear-algebra facts about d.
    constant: ker d = {(a,a)} (rank 1) and im d = {(x,x)}, so coker d ≅ Z via (x,y) ↦ y - x.
    twisted : ker d = 0, and im d = {(x,y) | x + y even}, so coker d ≅ Z/2.
  It does NOT formalise sheaves, Čech cohomology, or Mayer–Vietoris; those steps are
  the hand argument above. The reading — "locally consistent data that fails to glue
  globally is measured by H¹" — is an illustration, not a theorem about holology.
-/

namespace CechCircle

/-- Constant sheaf: the coboundary on a pair of local sections. -/
def dConst (a b : Int) : Int × Int := (b - a, b - a)

/-- Twisted (Möbius) sheaf: sign flip across the second component. -/
def dTwist (a b : Int) : Int × Int := (b - a, b + a)

/-- H⁰ for the constant sheaf: kernel = pairs that agree (global sections). -/
theorem const_ker (a b : Int) : dConst a b = (0, 0) ↔ a = b := by
  unfold dConst
  constructor
  · intro h
    have h1 : b - a = 0 := congrArg Prod.fst h
    omega
  · intro h
    subst h
    simp

/-- Image for the constant sheaf: exactly the diagonal. -/
theorem const_im (x y : Int) : (∃ a b : Int, dConst a b = (x, y)) ↔ x = y := by
  unfold dConst
  constructor
  · rintro ⟨a, b, h⟩
    have h1 : b - a = x := congrArg Prod.fst h
    have h2 : b - a = y := congrArg Prod.snd h
    omega
  · intro h
    subst h
    exact ⟨0, x, by simp⟩

/-- H¹ for the constant sheaf is Z: `(x,y) ↦ y - x` is onto and kills exactly the image. -/
theorem const_coker_onto (n : Int) : ∃ x y : Int, y - x = n := ⟨0, n, by omega⟩

/-- H⁰ for the twisted sheaf is 0: only the zero section is global. -/
theorem twist_ker (a b : Int) : dTwist a b = (0, 0) ↔ a = 0 ∧ b = 0 := by
  unfold dTwist
  constructor
  · intro h
    have h1 : b - a = 0 := congrArg Prod.fst h
    have h2 : b + a = 0 := congrArg Prod.snd h
    omega
  · rintro ⟨rfl, rfl⟩
    simp

/-- Image for the twisted sheaf: exactly the pairs with even sum (index 2). -/
theorem twist_im (x y : Int) : (∃ a b : Int, dTwist a b = (x, y)) ↔ (x + y) % 2 = 0 := by
  unfold dTwist
  constructor
  · rintro ⟨a, b, h⟩
    have h1 : b - a = x := congrArg Prod.fst h
    have h2 : b + a = y := congrArg Prod.snd h
    omega
  · intro h
    refine ⟨(y - x) / 2, (x + y) / 2, ?_⟩
    have e1 : (x + y) / 2 - (y - x) / 2 = x := by omega
    have e2 : (x + y) / 2 + (y - x) / 2 = y := by omega
    rw [e1, e2]

/-- H¹ for the twisted sheaf is not trivial: (1,0) is not in the image. -/
theorem twist_not_onto : ¬ ∃ a b : Int, dTwist a b = (1, 0) := by
  intro h
  have := (twist_im 1 0).1 h
  omega

/-- ...and (2,0) is, so the quotient has exactly two classes: Z/2. -/
theorem twist_two_in_image : ∃ a b : Int, dTwist a b = (2, 0) :=
  (twist_im 2 0).2 (by omega)

end CechCircle

#print axioms CechCircle.const_ker
#print axioms CechCircle.const_im
#print axioms CechCircle.twist_ker
#print axioms CechCircle.twist_im
#print axioms CechCircle.twist_not_onto

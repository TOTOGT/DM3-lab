/-
  Lawvere.lean — Lawvere's fixed-point theorem and Cantor's theorem as a corollary.
  For Principia Orthogona, Book VIII ch13 (holology) — self-reference, machine-checked.

  STATUS: UNTESTED. Written without a local Lean toolchain. Core Lean 4 only
  (no Mathlib, no imports). Run it against a real kernel and fix against the
  actual compiler output.

  WHAT IS ACTUALLY PROVED (read this, not just the names):
  * `lawvere`:  if φ : A → (A → B) is point-surjective (every g : A → B equals φ a
    for some a), then EVERY f : B → B has a fixed point.
  * `no_surj_of_fixed_point_free`: contrapositive. A fixed-point-free f : B → B
    rules out any point-surjection A → (A → B).
  * `cantor_prop`: no surjection A → (A → Prop)   (f = Not).
  * `cantor_bool`: no surjection A → (A → Bool)   (f = not).
  * `no_surj_nat`: no surjection A → (A → Nat)    (f = succ) — uses a third f, not Not.
  * `lawvere_nonvacuous`: the hypothesis CAN hold (B = Unit), so `lawvere` is not
    vacuous.
  NOT proved here: Gödel/Tarski/Turing (same diagonal shape, but they need a
  syntax/coding layer that is not formalised in this file).
-/

namespace Lawvere

/-- Point-surjectivity: every `g : A → B` is `φ a` for some `a`. -/
def PointSurj {A B : Type} (φ : A → (A → B)) : Prop :=
  ∀ g : A → B, ∃ a : A, φ a = g

/-- Lawvere's fixed-point theorem. -/
theorem lawvere {A B : Type} (φ : A → (A → B)) (hφ : PointSurj φ)
    (f : B → B) : ∃ b : B, f b = b := by
  -- diagonal map g a := f (φ a a)
  obtain ⟨a₀, h⟩ := hφ (fun a => f (φ a a))
  -- h : φ a₀ = fun a => f (φ a a);  evaluate at a₀
  have h₀ : φ a₀ a₀ = f (φ a₀ a₀) := congrFun h a₀
  exact ⟨φ a₀ a₀, h₀.symm⟩

/-- Contrapositive: a fixed-point-free endomap forbids point-surjections. -/
theorem no_surj_of_fixed_point_free {A B : Type} (f : B → B)
    (hf : ∀ b : B, f b ≠ b) (φ : A → (A → B)) : ¬ PointSurj φ := by
  intro hφ
  obtain ⟨b, hb⟩ := lawvere φ hφ f
  exact hf b hb

/-- Cantor, propositional form: no `A → (A → Prop)` is surjective. -/
theorem cantor_prop (A : Type) (φ : A → (A → Prop)) : ¬ PointSurj φ := by
  apply no_surj_of_fixed_point_free (fun p : Prop => ¬ p)
  intro p hp
  have hi : (¬ p) ↔ p := Iff.of_eq hp
  have np : ¬ p := fun x => hi.2 x x
  exact np (hi.1 np)

/-- Cantor, Boolean form. -/
theorem cantor_bool (A : Type) (φ : A → (A → Bool)) : ¬ PointSurj φ := by
  apply no_surj_of_fixed_point_free not
  intro b hb
  cases b <;> simp at hb

/-- Same shape with `succ` on `Nat`: no `A → (A → Nat)` is point-surjective. -/
theorem no_surj_nat (A : Type) (φ : A → (A → Nat)) : ¬ PointSurj φ := by
  apply no_surj_of_fixed_point_free Nat.succ
  intro n hn
  exact Nat.succ_ne_self n hn

/-- Cantor in its usual form: no surjection `A → Set A` (sets as predicates).
    Surjectivity is spelled out, since core Lean has no `Function.Surjective`. -/
theorem cantor_set (A : Type) (φ : A → (A → Prop)) :
    ¬ (∀ S : A → Prop, ∃ a : A, φ a = S) :=
  cantor_prop A φ

/-- Non-vacuity: for `B = Unit` a point-surjection exists, so `lawvere`'s
    hypothesis is satisfiable (and, consistently, `Unit` has fixed points). -/
theorem lawvere_nonvacuous : ∃ φ : Unit → (Unit → Unit), PointSurj φ := by
  refine ⟨fun _ => fun _ => (), ?_⟩
  intro g
  exact ⟨(), funext fun u => Subsingleton.elim _ _⟩

end Lawvere

#print axioms Lawvere.lawvere
#print axioms Lawvere.cantor_prop
#print axioms Lawvere.cantor_bool
#print axioms Lawvere.no_surj_nat
#print axioms Lawvere.cantor_set
#print axioms Lawvere.lawvere_nonvacuous

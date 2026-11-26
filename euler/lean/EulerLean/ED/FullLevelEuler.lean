import ScalarDescent
import EDc8
import RPEigenEuler

/-!
UNTESTED until CI (isolated task, branch fulllevel-euler-composition-isolated).
Conditional composition.  `FullLevelBound` is an EXPLICIT hypothesis of the theorem; it is a Prop-valued
definition in ScalarDescent.lean, it is not postulated globally and it is not proved here.

  EulerScalarDescent.rpeigenAt_of_fullLevel : FullLevelBound p h2 xs ys hxy -> EDcSplitTransport.RPEigenAt p h2 xs ys hxy
  EDcSplitTransport.rpeigen_of_one_splitting : (one splitting per prime p, p % 4 = 3, 3 < p, with RPEigenAt) -> EDc4.RPEigen
  RPEigenEuler.euler_1747_of_rpeigen : EDc4.RPEigen -> Euler's statement for n % 4 = 2

The conclusion is exactly the conclusion of `RPEigenEuler.euler_1747_of_rpeigen`.
No earlier module is modified.  This is a conditional implication, not an unconditional proof.
-/

namespace FullLevelEuler

theorem euler_1747_of_fullLevelBound
    (hB : ∀ (p : ℕ) [Fact p.Prime], p % 4 = 3 → 3 < p → ∀ (h2 : (2 : ZMod p) ≠ 0),
      ∃ (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1),
        EulerScalarDescent.FullLevelBound p h2 xs ys hxy)
    (n : ℕ) (hn4 : n % 4 = 2) :
    ∃ a b : ℕ, Euler1747.EulerGood a ∧ Euler1747.EulerGood b ∧ a + b = n := by
  refine RPEigenEuler.euler_1747_of_rpeigen ?_ n hn4
  refine EDcSplitTransport.rpeigen_of_one_splitting ?_
  intro p hp hp3 hp4 h2
  obtain ⟨xs, ys, hxy, h⟩ := hB p hp3 hp4 h2
  exact ⟨xs, ys, hxy, EulerScalarDescent.rpeigenAt_of_fullLevel p h2 xs ys hxy h⟩

/-- Type pin: the theorem has exactly this statement, with the spectral hypothesis explicit. -/
example :
    (∀ (p : ℕ) [Fact p.Prime], p % 4 = 3 → 3 < p → ∀ (h2 : (2 : ZMod p) ≠ 0),
      ∃ (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1),
        EulerScalarDescent.FullLevelBound p h2 xs ys hxy) →
    ∀ (n : ℕ), n % 4 = 2 →
      ∃ a b : ℕ, Euler1747.EulerGood a ∧ Euler1747.EulerGood b ∧ a + b = n :=
  euler_1747_of_fullLevelBound

end FullLevelEuler

#check @FullLevelEuler.euler_1747_of_fullLevelBound
#print axioms EDcSplitTransport.rpeigen_of_one_splitting
#print axioms EulerScalarDescent.rpeigenAt_of_fullLevel
#print axioms RPEigenEuler.euler_1747_of_rpeigen
#print axioms FullLevelEuler.euler_1747_of_fullLevelBound

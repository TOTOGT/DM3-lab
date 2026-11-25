import RPEigenH31
import EDcert

/-!
UNTESTED until CI (isolated task, branch rpeigen-h31-x1-isolated).
Final composition.  `RPEigen` is an EXPLICIT hypothesis of the theorem; it is not an axiom and is not proved here.

  RPEigenH31.H31gt3_of_rpeigen : EDc4.RPEigen -> Section83.H31gt3        (first isolated task, CI-green)
  EDcert.euler_1747_of_H31gt3_k : Section83.H31gt3 -> Euler's statement  (kernel-checked finite range; no native_decide)

The conclusion is exactly the conclusion of `EDcert.euler_1747_of_H31gt3_k`:
for every n with n % 4 = 2, n = a + b with `Euler1747.EulerGood a` and `Euler1747.EulerGood b`.
No `EDcert*` module and no earlier declaration is modified.
-/

namespace RPEigenEuler

theorem euler_1747_of_rpeigen (hR : EDc4.RPEigen) (n : ℕ) (hn4 : n % 4 = 2) :
    ∃ a b : ℕ, Euler1747.EulerGood a ∧ Euler1747.EulerGood b ∧ a + b = n :=
  EDcert.euler_1747_of_H31gt3_k (RPEigenH31.H31gt3_of_rpeigen hR) n hn4

end RPEigenEuler

#print axioms RPEigenEuler.euler_1747_of_rpeigen
#print axioms RPEigenH31.Amaj_one_eq_tau
#print axioms RPEigenH31.hprime_two_of_rpeigen
#print axioms RPEigenH31.H31gt3_of_hprime_two
#print axioms RPEigenH31.H31gt3_of_rpeigen

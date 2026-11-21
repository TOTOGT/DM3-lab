import Stage83cut
import EDb8
import EDcert

namespace EDb9k

/-- Euler's 1747 conjecture for n = 2 mod 4, conditional ONLY on `EDb8.HPrime`, with the finite range n < 64^4 checked in the kernel
(`EDcert`), so the axiom list contains no `Lean.ofReduceBool`.  `HPrime` is an explicit hypothesis (a `def ... : Prop` in `EDb8`),
not an axiom, and is not hidden in any other hypothesis. -/
theorem euler_1747_of_hprime_k (hP : EDb8.HPrime) (n : ℕ) (hn4 : n % 4 = 2) :
    ∃ a b : ℕ, Euler1747.EulerGood a ∧ Euler1747.EulerGood b ∧ a + b = n :=
  EDcert.euler_1747_of_H31gt3_k (EDb8.H31gt3_of_hprime hP) n hn4

end EDb9k
#print axioms EDb9k.euler_1747_of_hprime_k

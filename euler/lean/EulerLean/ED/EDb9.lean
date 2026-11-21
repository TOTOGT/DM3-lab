import Stage83cut
import EDb8

namespace EDb9

/-- Euler's 1747 conjecture for n ≡ 2 (mod 4), conditional ONLY on the prime-case bound `HPrime`
(‖T_ℓ f‖ ≤ 2√ℓ ‖f‖ on {1, χ}⊥ for primes ℓ admissible at p), plus the finite `native_decide` check
Euler1747.allOk_true that is already inside `Section83.euler_1747_of_H31gt3`. -/
theorem euler_1747_of_hprime (hP : EDb8.HPrime) (n : ℕ) (hn4 : n % 4 = 2) :
    ∃ a b : ℕ, Euler1747.EulerGood a ∧ Euler1747.EulerGood b ∧ a + b = n :=
  Section83.euler_1747_of_H31gt3 (EDb8.H31gt3_of_hprime hP) n hn4

end EDb9
#print axioms EDb9.euler_1747_of_hprime

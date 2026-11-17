import Mathlib

/-!
# Exact rational arithmetic behind Lemma 5.1 and Proposition 6.1
(Howe-Huffman-Kohlmeyer-Kruer, hexagon:2611.00370v1)

STATUS: UNTESTED in Lean (no local toolchain in the session that wrote it).
Every number below was first reproduced with exact `fractions.Fraction`
arithmetic in Python (COMPUTED); the Lean statements are the same equalities
and inequalities over `ℚ`, closed by `norm_num`.

WHAT THIS FILE DOES NOT PROVE (read before treating it as settled):
* It does not prove Lemma 5.1. It checks the finite numerical certificate
  (the product of local factors over the primes < 32, and the fifth-power
  bounds). The maximisation over the exponent e at each prime, the fact that
  primes >= 32 contribute a factor <= 1, and the link from fifth powers to
  real fifth roots are separate lemmas, not done here.
* It does not prove Prop 6.1. It checks only the final rational inequality
  (6.1)+(6.2) < 2/3 once the paper's intermediate bounds are granted.
-/

namespace Section6Arithmetic

/-! ### Lemma 5.1: fifth powers of the constants -/

/-- C1^5: product of the fifth powers of the local factors at p = 3, 7, 11, 19, 23
(p = 31 has local factor < 1, so it contributes 1). -/
theorem c1_pow5 :
    (9375 / 1024 : ℚ) * (83349 / 32768) * (14641 / 7776) * (130321 / 100000)
      * (279841 / 248832) = 183143120027364343 / 2849934139195392 := by
  norm_num

theorem c1_pow5_lt : (183143120027364343 / 2849934139195392 : ℚ) < (23 / 10) ^ 5 := by
  norm_num

/-- the p = 31 factor is < 1 -/
theorem local31_lt_one : (923521 / 1048576 : ℚ) < 1 := by norm_num

/-- C2^5 -/
theorem c2_pow5 :
    (243 / 25 : ℚ) * (32 / 13) * (32 / 17) * (32 / 29) = 7962624 / 160225 := by
  norm_num

theorem c2_pow5_lt : (7962624 / 160225 : ℚ) < (11 / 5) ^ 5 := by norm_num

/-- primes q >= 37 contribute at most 32/37 < 1 -/
theorem tail_factor_lt_one : (32 / 37 : ℚ) < 1 := by norm_num

/-- P3 primes >= 32 contribute at most 3418801/5153632 < 1 -/
theorem p3_tail_factor_lt_one : (3418801 / 5153632 : ℚ) < 1 := by norm_num

/-! ### Prop 6.1: side bounds at X = 64 (stated as fifth / tenth power facts) -/

theorem side_inv64 : (1 / 64 : ℚ) ≤ (4 / 9) ^ 5 := by norm_num
theorem side_pow : (2 : ℚ) ^ 3 < (5 / 4) ^ 10 := by norm_num
theorem side_64 : ((9 / 4 : ℚ)) ^ 5 ≤ 64 := by norm_num

/-! ### Prop 6.1: the final sum (6.1) + (6.2) < 2/3 -/

theorem final_sum_eq :
    (21 / 50 : ℚ)
      + (23 / 30) * (5 / 4) * (4 / 9) * (4 / 15 + 1 / 64)
      + (44 / 15) * (4 / 9) * (1 / 15 + 19 / (30 * 64) + 1 / 64 ^ 3)
      = 21235493 / 33177600 := by
  norm_num

theorem final_sum_lt : (21235493 / 33177600 : ℚ) < 2 / 3 := by norm_num

/-! ### (5.4): the partial sum behind 2 * sum 1/(p(p-1)) < 21/50

The finite part is the sum over p in {3,7,11,19,23,31,43,47,59}; the tail term (120/59)(2/(15*60) + 2/60^2) is the
paper's own remainder estimate in its proof of (5.4): p/(p-1) <= 60/59 for p > 60, with (5.3) at P = 60. I originally
described this shape as my own; reading the paper's proof again, it matches. What this theorem checks is the
arithmetic of that final inequality only. The tail estimate itself is (5.3), proved separately in Lemma52.lean
(untested when this comment was written). Not a formalization of (5.4) as a statement about primes. -/

theorem partial_sum_5_4 :
    (2 / (3 * 2) + 2 / (7 * 6) + 2 / (11 * 10) + 2 / (19 * 18) + 2 / (23 * 22)
      + 2 / (31 * 30) + 2 / (43 * 42) + 2 / (47 * 46) + 2 / (59 * 58) : ℚ)
      + (120 / 59) * (2 / (15 * 60) + 2 / (60 * 60)) < 21 / 50 := by
  norm_num

end Section6Arithmetic

#print axioms Section6Arithmetic.c1_pow5
#print axioms Section6Arithmetic.final_sum_eq
#print axioms Section6Arithmetic.final_sum_lt

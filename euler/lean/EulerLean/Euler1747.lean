/-
  Euler1747.lean   (draft written 2026-11-16 by Claude; UNTESTED: no Lean toolchain was available
  when this was written. Expect small repairs against your Mathlib version; fix against what
  the compiler actually says.)

  Source: Howe, Huffman, Kohlmeyer, Kruer, "Euler's 1747 conjecture on sums of integers with
  restricted prime factors", hexagon:2611.00370v1 (credits OpenAI Codex).  This file is NOT their
  formalization; it is an independent attempt at part of it.

  WHAT THIS FILE PROVES (if it compiles):
    1. EulerGood is closed under multiplication, and EulerGood a -> a % 4 = 1.
    2. FINITE PART (the paper's Proposition 7.2): every n with n % 4 = 2 and n < 64^4 is a sum of
       two EulerGood numbers with the smaller summand at most 313.  Proved by an exhaustive
       computation checked with `native_decide`, which trusts the Lean compiler (Lean.ofReduceBool),
       not only the kernel.
    3. A CONDITIONAL theorem: Euler's conjecture follows from `AnalyticRange`.

  WHAT THIS FILE DOES NOT PROVE:
    `AnalyticRange` is the statement of the paper's Proposition 6.1 (n = 2m >= 64^4, m odd, all prime
    factors of m are 3 mod 4).  It is a HYPOTHESIS here, not a theorem.  Proving it needs the
    Ramanujan-Petersson bound through Jacquet-Langlands and the paper's sections 2-5, which are not
    in Mathlib and which I have not audited.  So `euler_1747_of_analytic_range` is NOT the full
    Euler conjecture; it is the reduction of it to Proposition 6.1.

  Run:  put this file in a project that depends on Mathlib (for example inside your geometry repo)
        and run `lake env lean Euler1747.lean`.  The `native_decide` step factors about 4 million
        numbers; expect minutes, not seconds.
-/
import Mathlib

namespace Euler1747

/-- The set A of the paper: positive integers all of whose prime factors are 1 mod 4 (1 allowed). -/
def EulerGood (a : ℕ) : Prop :=
  0 < a ∧ ∀ p : ℕ, p.Prime → p ∣ a → p % 4 = 1

/-- Computable test for `EulerGood`. -/
def goodB (a : ℕ) : Bool :=
  decide (0 < a) && a.primeFactorsList.all (fun p => p % 4 == 1)

theorem goodB_iff (a : ℕ) : goodB a = true ↔ EulerGood a := by
  unfold goodB EulerGood
  constructor
  · intro h
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at h
    obtain ⟨ha, hall⟩ := h
    refine ⟨ha, fun p hp hpd => hall p ?_⟩
    exact Nat.mem_primeFactorsList'.2 ⟨hp, hpd, ha.ne'⟩
  · rintro ⟨ha, h⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq]
    refine ⟨ha, fun p hp => ?_⟩
    obtain ⟨hpp, hpd, -⟩ := Nat.mem_primeFactorsList'.1 hp
    exact h p hpp hpd

/-! ### Adjacent facts used by the paper -/

theorem good_mul {a b : ℕ} (ha : EulerGood a) (hb : EulerGood b) : EulerGood (a * b) := by
  refine ⟨Nat.mul_pos ha.1 hb.1, fun p hp hpd => ?_⟩
  rcases (Nat.Prime.dvd_mul hp).1 hpd with h | h
  · exact ha.2 p hp h
  · exact hb.2 p hp h

theorem good_of_mul_left {a b : ℕ} (h : EulerGood (a * b)) : EulerGood a := by
  have hpos : 0 < a := Nat.pos_of_ne_zero (fun h0 => by simp [h0, EulerGood] at h)
  exact ⟨hpos, fun p hp hpd => h.2 p hp (Dvd.dvd.mul_right hpd b)⟩

theorem good_of_mul_right {a b : ℕ} (h : EulerGood (a * b)) : EulerGood b := by
  rw [mul_comm] at h
  exact good_of_mul_left h

/-- Elements of A are 1 mod 4 (the parity fact behind the paper's Lemma 7.1). -/
theorem good_mod_four (a : ℕ) (h : EulerGood a) : a % 4 = 1 := by
  induction a using Nat.recOnMul with
  | zero => exact absurd h.1 (lt_irrefl 0)
  | one => rfl
  | prime p hp => exact h.2 p hp (dvd_refl p)
  | mul a b iha ihb =>
    have ha := iha (good_of_mul_left h)
    have hb := ihb (good_of_mul_right h)
    rw [Nat.mul_mod, ha, hb]

/-! ### The finite part (Proposition 7.2) -/

/-- Possible smaller summands: the numbers 4i+1 with i <= 78 that are in A.  The paper lists 43 of them,
    ending at 313. -/
def cands : List ℕ := ((List.range 79).map (fun i => 4 * i + 1)).filter goodB

/- Sanity checks against the paper's list J (run with `lake env lean`; these are cheap). -/
#eval cands.length          -- the paper says 43
#eval cands.getLast?        -- the paper says 313

def checkOne (n : ℕ) : Bool :=
  cands.any (fun a => decide (a < n) && goodB (n - a))

/-- n = 4k+2 for every k < 2^22 = 4194304, i.e. every n = 2 mod 4 below 64^4 = 16777216. -/
def allOk : Bool := (List.range 4194304).all (fun k => checkOne (4 * k + 2))

/-- The computation. TRUSTS THE COMPILER via native_decide. -/
theorem allOk_true : allOk = true := by native_decide

theorem euler_finite (n : ℕ) (hn : n % 4 = 2) (hlt : n < 64 ^ 4) :
    ∃ a b : ℕ, EulerGood a ∧ EulerGood b ∧ a + b = n ∧ min a b ≤ 313 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k + 2 := ⟨n / 4, by omega⟩
  have h64 : (64 : ℕ) ^ 4 = 16777216 := by norm_num
  rw [h64] at hlt
  have hk : k < 4194304 := by omega
  have h := allOk_true
  unfold allOk at h
  have h2 := (List.all_eq_true.1 h) k (List.mem_range.2 hk)
  unfold checkOne at h2
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h2
  obtain ⟨a, ha, hlt', hb⟩ := h2
  obtain ⟨hmap, hga⟩ := List.mem_filter.1 ha
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hmap
  have hi' := List.mem_range.1 hi
  refine ⟨4 * i + 1, 4 * k + 2 - (4 * i + 1), (goodB_iff _).1 hga, (goodB_iff _).1 hb,
    by omega, ?_⟩
  exact le_trans (min_le_left _ _) (by omega)

/-! ### Conditional reduction of the full conjecture to Proposition 6.1 -/

/-- Statement of the paper's Proposition 6.1.  A HYPOTHESIS in this file, not a theorem. -/
def AnalyticRange : Prop :=
  ∀ m : ℕ, m % 2 = 1 → (∀ p : ℕ, p.Prime → p ∣ m → p % 4 = 3) → 64 ^ 4 ≤ 2 * m →
    ∃ a b : ℕ, EulerGood a ∧ EulerGood b ∧ a + b = 2 * m

/-- Euler's 1747 conjecture, CONDITIONAL on `AnalyticRange` (Proposition 6.1 of the paper).
    This reproduces the paper's Lemma 2.1 and the finite-range case by strong induction. -/
theorem euler_1747_of_analytic_range (H : AnalyticRange) (n : ℕ) (hn : n % 4 = 2) :
    ∃ a b : ℕ, EulerGood a ∧ EulerGood b ∧ a + b = n := by
  obtain ⟨m, rfl, hm⟩ : ∃ m, n = 2 * m ∧ m % 2 = 1 := ⟨n / 2, by omega, by omega⟩
  clear hn
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases hex : ∃ p : ℕ, p.Prime ∧ p ∣ m ∧ p % 4 = 1
    · obtain ⟨p, hp, hpd, hp1⟩ := hex
      obtain ⟨m', rfl⟩ := hpd
      have hm' : m' % 2 = 1 :=
        Nat.odd_iff.1 (Nat.odd_mul.1 (Nat.odd_iff.2 hm)).2
      have hp2 := hp.two_le
      have hm'pos : 0 < m' := by omega
      have hlt : m' < p * m' := by nlinarith
      obtain ⟨a, b, ha, hb, hab⟩ := ih m' hlt hm'
      have hpg : EulerGood p :=
        ⟨hp.pos, fun q hq hqd => by rw [(Nat.prime_dvd_prime_iff_eq hq hp).1 hqd]; exact hp1⟩
      exact ⟨p * a, p * b, good_mul hpg ha, good_mul hpg hb, by rw [← mul_add, hab]; ring⟩
    · have h3 : ∀ p : ℕ, p.Prime → p ∣ m → p % 4 = 3 := by
        intro p hp hpd
        rcases hp.eq_two_or_odd with h2 | h2
        · subst h2; omega
        · have : p % 4 ≠ 1 := fun h1 => hex ⟨p, hp, hpd, h1⟩
          omega
      by_cases hbig : 64 ^ 4 ≤ 2 * m
      · exact H m hm h3 hbig
      · obtain ⟨a, b, ha, hb, hab, -⟩ := euler_finite (2 * m) (by omega) (not_le.1 hbig)
        exact ⟨a, b, ha, hb, hab⟩

end Euler1747

#print axioms Euler1747.euler_finite
#print axioms Euler1747.euler_1747_of_analytic_range

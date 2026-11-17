import Mathlib

/-!
# (2.3), sufficiency step, of Howe-Huffman-Kohlmeyer-Kruer (hexagon:2611.00370v1)

Paper: for n = 2m, let Rmix(n) be the integer solutions of x0²+x1²+x2²+x3² = n in which each of
(x0,x1) and (x2,x3) has opposite parity (x0+x1 odd, x2+x3 odd). For a prime p ≡ 3 (mod 4), let
b_p(n) count the elements of Rmix(n) with (p | x0 and p | x1) or (p | x2 and p | x3).
Then
      Σ_p b_p(n) < |Rmix(n)|   implies   n = a + b with a, b in A,
where A = positive integers all of whose prime factors are ≡ 1 mod 4.

STATUS: UNTESTED in Lean (no local toolchain in the session that wrote this).

What this proves: ONLY the implication above (the pigeonhole / "-1 is a nonresidue" step).
It does NOT prove |Rmix(n)| = (2/3)·R(n), nor R(n) = 24σ(m), nor any bound on Σ b_p; those are
(2.2) (FourSquaresMixed.lean), Jacobi's formula (open), and Prop 3.1/Lemma 4.2/Prop 6.1.
The sum here runs over primes p ≡ 3 mod 4 with p ≤ n, which suffices because every prime
factor of x0²+x1² ≤ n is at most n.
-/

namespace Sufficiency

/-- the paper's set A: positive integers all of whose prime factors are 1 mod 4 (1 allowed);
    same definition as `Euler1747.EulerGood` -/
def Good (a : ℕ) : Prop := 0 < a ∧ ∀ p : ℕ, p.Prime → p ∣ a → p % 4 = 1

/-- a prime ≡ 3 mod 4 dividing a sum of two squares divides both -/
lemma dvd_of_sq_add {q : ℕ} (hq : q.Prime) (h3 : q % 4 = 3) (x y : ℤ)
    (h : (q : ℤ) ∣ x ^ 2 + y ^ 2) : (q : ℤ) ∣ x ∧ (q : ℤ) ∣ y := by
  haveI : Fact q.Prime := ⟨hq⟩
  have h0 : ((x : ZMod q)) ^ 2 + (y : ZMod q) ^ 2 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (x ^ 2 + y ^ 2) q).2 h
    push_cast at this
    exact this
  by_cases hy : (y : ZMod q) = 0
  · have hx2 : (x : ZMod q) ^ 2 = 0 := by rw [hy] at h0; simpa using h0
    have hx : (x : ZMod q) = 0 := pow_eq_zero_iff (by norm_num) |>.1 hx2
    exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd x q).1 hx,
           (ZMod.intCast_zmod_eq_zero_iff_dvd y q).1 hy⟩
  · exfalso
    have hxy : (x : ZMod q) ^ 2 = -(y : ZMod q) ^ 2 := by linear_combination h0
    exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq' hy hxy h3

def Rmix (n : ℕ) : Finset (Fin 4 → ℤ) :=
  (Fintype.piFinset fun _ => Finset.Icc (-(n : ℤ)) n).filter
    (fun x => (x 0 + x 1) % 2 = 1 ∧ (x 2 + x 3) % 2 = 1 ∧
      x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 = (n : ℤ))

def Eset (p n : ℕ) : Finset (Fin 4 → ℤ) :=
  (Rmix n).filter (fun x => ((p : ℤ) ∣ x 0 ∧ (p : ℤ) ∣ x 1) ∨ ((p : ℤ) ∣ x 2 ∧ (p : ℤ) ∣ x 3))

/-- b_p(n) -/
def bp (p n : ℕ) : ℕ := (Eset p n).card

/-- a pair of opposite parity, with no prime ≡ 3 mod 4 dividing both coordinates, gives a good number -/
lemma good_of_pair {x y : ℤ} {n : ℕ} (hodd : (x + y) % 2 = 1) (hle : x ^ 2 + y ^ 2 ≤ (n : ℤ))
    (hno : ∀ q : ℕ, q.Prime → q % 4 = 3 → q ≤ n → ¬ ((q : ℤ) ∣ x ∧ (q : ℤ) ∣ y)) :
    Good (x ^ 2 + y ^ 2).toNat := by
  have hpos : 0 < x ^ 2 + y ^ 2 := by
    by_contra hc
    have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    subst hx; subst hy
    omega
  have hcast : (((x ^ 2 + y ^ 2).toNat : ℕ) : ℤ) = x ^ 2 + y ^ 2 := Int.toNat_of_nonneg hpos.le
  refine ⟨by omega, ?_⟩
  intro q hq hqd
  have hqdz : (q : ℤ) ∣ x ^ 2 + y ^ 2 := by
    rw [← hcast]; exact Int.natCast_dvd_natCast.2 hqd
  -- the number is odd
  have hodd2 : (x ^ 2 + y ^ 2) % 2 = 1 := by
    have : x % 2 = 0 ∧ y % 2 = 1 ∨ x % 2 = 1 ∧ y % 2 = 0 := by omega
    rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      simp [pow_two, Int.add_emod, Int.mul_emod, h1, h2]
  have hq2 : q ≠ 2 := by
    rintro rfl
    have : (2 : ℤ) ∣ x ^ 2 + y ^ 2 := hqdz
    omega
  have hqle : q ≤ n := by
    have : (q : ℤ) ≤ x ^ 2 + y ^ 2 := Int.le_of_dvd hpos hqdz
    have : (q : ℤ) ≤ n := le_trans this hle
    exact_mod_cast this
  have hq4 : q % 4 = 1 ∨ q % 4 = 3 := by
    have h2 : q % 2 = 1 := by
      rcases hq.eq_two_or_odd with h | h
      · exact absurd h hq2
      · exact h
    omega
  rcases hq4 with h | h
  · exact h
  · exact absurd (dvd_of_sq_add hq h x y hqdz) (hno q hq h hqle)

theorem sufficiency (n : ℕ)
    (h : ∑ p ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p % 4 = 3), bp p n
          < (Rmix n).card) :
    ∃ a b : ℕ, Good a ∧ Good b ∧ a + b = n := by
  by_contra hne
  have hcov : Rmix n ⊆
      ((Finset.range (n + 1)).filter (fun p => p.Prime ∧ p % 4 = 3)).biUnion (fun p => Eset p n) := by
    intro x hx
    by_contra hnot
    apply hne
    rw [Finset.mem_biUnion] at hnot
    push_neg at hnot
    have hx' := (Finset.mem_filter.1 hx).2
    obtain ⟨ho1, ho2, hsum⟩ := hx'
    have hno1 : ∀ q : ℕ, q.Prime → q % 4 = 3 → q ≤ n → ¬ ((q : ℤ) ∣ x 0 ∧ (q : ℤ) ∣ x 1) := by
      intro q hq h3 hqn hdiv
      apply hnot q (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hq, h3⟩)
      exact Finset.mem_filter.2 ⟨hx, Or.inl hdiv⟩
    have hno2 : ∀ q : ℕ, q.Prime → q % 4 = 3 → q ≤ n → ¬ ((q : ℤ) ∣ x 2 ∧ (q : ℤ) ∣ x 3) := by
      intro q hq h3 hqn hdiv
      apply hnot q (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hq, h3⟩)
      exact Finset.mem_filter.2 ⟨hx, Or.inr hdiv⟩
    have hle1 : x 0 ^ 2 + x 1 ^ 2 ≤ (n : ℤ) := by nlinarith [sq_nonneg (x 2), sq_nonneg (x 3)]
    have hle2 : x 2 ^ 2 + x 3 ^ 2 ≤ (n : ℤ) := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
    have hg1 := good_of_pair ho1 hle1 hno1
    have hg2 := good_of_pair ho2 hle2 hno2
    refine ⟨(x 0 ^ 2 + x 1 ^ 2).toNat, (x 2 ^ 2 + x 3 ^ 2).toNat, hg1, hg2, ?_⟩
    have p1 : 0 ≤ x 0 ^ 2 + x 1 ^ 2 := by positivity
    have p2 : 0 ≤ x 2 ^ 2 + x 3 ^ 2 := by positivity
    omega
  have hcard := Finset.card_le_card hcov
  have hbu := Finset.card_biUnion_le (s := (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p % 4 = 3))
    (t := fun p => Eset p n)
  unfold bp at h
  omega

end Sufficiency

#print axioms Sufficiency.sufficiency

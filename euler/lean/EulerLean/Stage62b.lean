import Mathlib

/-!
# Lemma 4.1 of Howe-Huffman-Kohlmeyer-Kruer (hexagon:2611.00370v1)

  For every t ≥ 0:  N_mix(t) ≤ 2(t+1),
  where N_mix(t) = #{(x,y) ∈ ℤ² : x+y odd, x²+y² ≤ t}.

STATUS: UNTESTED in Lean (no local toolchain in the session that wrote this).
Expect compile errors; fix them against what the compiler says.

What is formalized: the paper's own argument, in two pieces.
  (a) `Nmix_eq`   : N_mix(t) = 4 * #A(t), where A(t) is the quadrant x>0, y≥0
                    (quarter-turn r(x,y) = (-y,x) permutes the four quadrants).
  (b) `quarter_card` : 2 * #A(t) ≤ t+1, via the paper's label
                    L = u²+u+v+1 with x+y = 2u+1, x−y = 2v+1,
                    which is injective on A(t) and lands in [1, (t+1)/2].
Combined: `Nmix_le`.

Scope notes (so the statement is not read as more than it is):
* t is a natural number here. For real t, N_mix(t) = N_mix(⌊t⌋), so the integer
  case is the whole content; that reduction is not formalized.
* The bound is only an upper bound. Numerically, max N_mix(t)/(2(t+1)) = 1.0 for
  integer t in [0,4000] (script audit_lemma4.py), so the constant 2 is attained.
-/

namespace Section4
open Classical

/-- parity + norm condition defining the "mixed" pairs -/
def P (t : ℕ) (p : ℤ × ℤ) : Prop := (p.1 + p.2) % 2 = 1 ∧ p.1 ^ 2 + p.2 ^ 2 ≤ (t : ℤ)

noncomputable def inBox (t : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(t : ℤ)) t ×ˢ Finset.Icc (-(t : ℤ)) t

/-- the set counted by N_mix(t) (cut to a finite box, which loses nothing: see `mem_Nset`) -/
noncomputable def Nset (t : ℕ) : Finset (ℤ × ℤ) := (inBox t).filter (P t)

noncomputable def Nmix (t : ℕ) : ℕ := (Nset t).card

lemma bound_of_sq {x : ℤ} {t : ℕ} (h : x ^ 2 ≤ (t : ℤ)) : -(t : ℤ) ≤ x ∧ x ≤ (t : ℤ) := by
  have ht : (0 : ℤ) ≤ t := Nat.cast_nonneg t
  constructor
  · by_contra hc
    have hc := not_le.1 hc
    have h1 : (t : ℤ) + 1 ≤ -x := by omega
    have h2 := mul_self_le_mul_self (by omega : (0 : ℤ) ≤ (t : ℤ) + 1) h1
    nlinarith
  · by_contra hc
    have hc := not_le.1 hc
    have h1 : (t : ℤ) + 1 ≤ x := by omega
    have h2 := mul_self_le_mul_self (by omega : (0 : ℤ) ≤ (t : ℤ) + 1) h1
    nlinarith

lemma mem_Nset {t : ℕ} {p : ℤ × ℤ} : p ∈ Nset t ↔ P t p := by
  constructor
  · intro h
    exact (Finset.mem_filter.1 h).2
  · intro h
    refine Finset.mem_filter.2 ⟨?_, h⟩
    obtain ⟨x, y⟩ := p
    obtain ⟨_, hn⟩ := h
    have hx : x ^ 2 ≤ (t : ℤ) := by nlinarith [sq_nonneg y]
    have hy : y ^ 2 ≤ (t : ℤ) := by nlinarith [sq_nonneg x]
    have bx := bound_of_sq hx
    have bY := bound_of_sq hy
    simp only [inBox, Finset.mem_product, Finset.mem_Icc]
    exact ⟨bx, bY⟩

/-! ### Part (b): the label injection on the quadrant x>0, y≥0 -/

/-- the paper's label L = u²+u+v+1 with u = (x+y−1)/2, v = (x−y−1)/2 (exact division for x+y odd) -/
def Lf (x y : ℤ) : ℤ :=
  ((x + y - 1) / 2) ^ 2 + (x + y - 1) / 2 + (x - y - 1) / 2 + 1

lemma Lf_bounds {x y : ℤ} {t : ℕ} (hx : 0 < x) (hy : 0 ≤ y) (ho : (x + y) % 2 = 1)
    (hn : x ^ 2 + y ^ 2 ≤ (t : ℤ)) : 1 ≤ Lf x y ∧ 2 * Lf x y ≤ (t : ℤ) + 1 := by
  unfold Lf
  obtain ⟨u, hu⟩ : ∃ u, u = (x + y - 1) / 2 := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = (x - y - 1) / 2 := ⟨_, rfl⟩
  rw [← hu, ← hv]
  have hb : 0 ≤ u ∧ -u ≤ v ∧ v ≤ u := by omega
  have hx' : x = u + v + 1 := by omega
  have hy' : y = u - v := by omega
  rw [hx', hy'] at hn
  constructor
  · nlinarith [sq_nonneg u, hb.1, hb.2.1]
  · nlinarith [sq_nonneg v]

lemma Lf_inj {x1 y1 x2 y2 : ℤ} (hx1 : 0 < x1) (hy1 : 0 ≤ y1) (ho1 : (x1 + y1) % 2 = 1)
    (hx2 : 0 < x2) (hy2 : 0 ≤ y2) (ho2 : (x2 + y2) % 2 = 1)
    (h : Lf x1 y1 = Lf x2 y2) : x1 = x2 ∧ y1 = y2 := by
  unfold Lf at h
  obtain ⟨u1, hu1⟩ : ∃ u, u = (x1 + y1 - 1) / 2 := ⟨_, rfl⟩
  obtain ⟨v1, hv1⟩ : ∃ v, v = (x1 - y1 - 1) / 2 := ⟨_, rfl⟩
  obtain ⟨u2, hu2⟩ : ∃ u, u = (x2 + y2 - 1) / 2 := ⟨_, rfl⟩
  obtain ⟨v2, hv2⟩ : ∃ v, v = (x2 - y2 - 1) / 2 := ⟨_, rfl⟩
  rw [← hu1, ← hv1, ← hu2, ← hv2] at h
  have hb1 : 0 ≤ u1 ∧ -u1 ≤ v1 ∧ v1 ≤ u1 := by omega
  have hb2 : 0 ≤ u2 ∧ -u2 ≤ v2 ∧ v2 ≤ u2 := by omega
  rcases lt_trichotomy u1 u2 with hlt | heq | hgt
  · exfalso
    have h1 : u1 + 1 ≤ u2 := by omega
    have h2 := mul_self_le_mul_self (by omega : (0 : ℤ) ≤ u1 + 1) h1
    nlinarith [hb1.2.2, hb2.2.1]
  · subst heq
    have hv : v1 = v2 := by linarith
    omega
  · exfalso
    have h1 : u2 + 1 ≤ u1 := by omega
    have h2 := mul_self_le_mul_self (by omega : (0 : ℤ) ≤ u2 + 1) h1
    nlinarith [hb2.2.2, hb1.2.1]

def qA (p : ℤ × ℤ) : Prop := 0 < p.1 ∧ 0 ≤ p.2

noncomputable def Aset (t : ℕ) : Finset (ℤ × ℤ) := (Nset t).filter qA

lemma quarter_card (t : ℕ) : 2 * (Aset t).card ≤ t + 1 := by
  have key : (Aset t).card ≤ (Finset.Icc 1 ((t + 1) / 2)).card := by
    refine Finset.card_le_card_of_injOn (fun p => (Lf p.1 p.2).toNat) ?_ ?_
    · intro p hp
      simp only [Aset, Finset.mem_coe, Finset.mem_filter, mem_Nset, P, qA] at hp
      obtain ⟨⟨ho, hn⟩, hx, hy⟩ := hp
      obtain ⟨b1, b2⟩ := Lf_bounds hx hy ho hn
      simp only [Finset.mem_coe, Finset.mem_Icc]
      omega
    · intro p hp q hq hpq
      simp only [Aset, Finset.mem_coe, Finset.mem_filter, mem_Nset, P, qA] at hp hq
      obtain ⟨⟨ho1, hn1⟩, hx1, hy1⟩ := hp
      obtain ⟨⟨ho2, hn2⟩, hx2, hy2⟩ := hq
      obtain ⟨b1, _⟩ := Lf_bounds hx1 hy1 ho1 hn1
      obtain ⟨b2, _⟩ := Lf_bounds hx2 hy2 ho2 hn2
      have hL : Lf p.1 p.2 = Lf q.1 q.2 := by
        simp only at hpq
        omega
      obtain ⟨e1, e2⟩ := Lf_inj hx1 hy1 ho1 hx2 hy2 ho2 hL
      exact Prod.ext e1 e2
  rw [Nat.card_Icc] at key
  omega

/-! ### Part (a): the quarter-turn gives N_mix = 4 * #A -/

def quad (p : ℤ × ℤ) : ℕ :=
  if 0 < p.1 ∧ 0 ≤ p.2 then 0
  else if p.1 ≤ 0 ∧ 0 < p.2 then 1
  else if p.1 < 0 ∧ p.2 ≤ 0 then 2
  else 3

lemma quad_lt (p : ℤ × ℤ) : quad p < 4 := by
  unfold quad
  split_ifs <;> omega

lemma quad_zero (p : ℤ × ℤ) : quad p = 0 ↔ qA p := by
  unfold quad qA
  split_ifs <;> simp_all

lemma quad_rot (x y : ℤ) (hp : (x + y) % 2 = 1) :
    quad (-y, x) = (quad (x, y) + 1) % 4 ∧ quad (y, -x) = (quad (x, y) + 3) % 4 := by
  unfold quad
  dsimp only
  split_ifs <;> omega

/-- quarter-turn and its inverse -/
def rot (p : ℤ × ℤ) : ℤ × ℤ := (-p.2, p.1)
def rotInv (p : ℤ × ℤ) : ℤ × ℤ := (p.2, -p.1)

lemma P_rot {t : ℕ} {p : ℤ × ℤ} (h : P t p) : P t (rot p) := by
  obtain ⟨x, y⟩ := p
  obtain ⟨ho, hn⟩ := h
  refine ⟨?_, ?_⟩
  · simp only [rot]; omega
  · simp only [rot] at *
    rw [neg_sq]; linarith

lemma P_rotInv {t : ℕ} {p : ℤ × ℤ} (h : P t p) : P t (rotInv p) := by
  obtain ⟨x, y⟩ := p
  obtain ⟨ho, hn⟩ := h
  refine ⟨?_, ?_⟩
  · simp only [rotInv]; omega
  · simp only [rotInv] at *
    rw [neg_sq]; linarith

noncomputable def fib (t i : ℕ) : Finset (ℤ × ℤ) := (Nset t).filter (fun p => quad p = i)

lemma fib_step (t i : ℕ) (hi : i < 4) : (fib t i).card = (fib t ((i + 1) % 4)).card := by
  refine Finset.card_nbij' rot rotInv ?_ ?_ ?_ ?_
  · intro p hp
    simp only [fib, Finset.mem_coe, Finset.mem_filter, mem_Nset] at hp ⊢
    obtain ⟨hP, hq⟩ := hp
    refine ⟨P_rot hP, ?_⟩
    obtain ⟨x, y⟩ := p
    have := (quad_rot x y hP.1).1
    simp only [rot]
    omega
  · intro p hp
    simp only [fib, Finset.mem_coe, Finset.mem_filter, mem_Nset] at hp ⊢
    obtain ⟨hP, hq⟩ := hp
    refine ⟨P_rotInv hP, ?_⟩
    obtain ⟨x, y⟩ := p
    have := (quad_rot x y hP.1).2
    simp only [rotInv]
    omega
  · intro p _
    obtain ⟨x, y⟩ := p
    simp [rot, rotInv]
  · intro p _
    obtain ⟨x, y⟩ := p
    simp [rot, rotInv]

lemma Nmix_eq (t : ℕ) : Nmix t = 4 * (Aset t).card := by
  have hsum : (Nset t).card = ∑ i ∈ Finset.range 4, (fib t i).card := by
    unfold fib
    exact Finset.card_eq_sum_card_fiberwise (fun p _ => Finset.mem_range.2 (quad_lt p))
  have h01 := fib_step t 0 (by norm_num)
  have h12 := fib_step t 1 (by norm_num)
  have h23 := fib_step t 2 (by norm_num)
  have hA : (fib t 0) = Aset t := by
    unfold fib Aset
    exact Finset.filter_congr (fun p _ => quad_zero p)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hsum
  norm_num at h01 h12 h23
  unfold Nmix
  rw [hsum, ← hA]
  omega

/-- Lemma 4.1 (for integer t). -/
theorem Nmix_le (t : ℕ) : Nmix t ≤ 2 * (t + 1) := by
  have h1 := Nmix_eq t
  have h2 := quarter_card t
  omega

/-! ### Real cutoffs: N_mix(t) = N_mix(⌊t⌋) for t ≥ 0

Lemma 4.2 applies Lemma 4.1 at the real cutoff t = n/p², so the integer version alone is not
enough. UNTESTED in Lean when written. -/

/-- the real-cutoff condition: x+y odd and x²+y² ≤ t, with t a real number -/
def PR (t : ℝ) (p : ℤ × ℤ) : Prop := (p.1 + p.2) % 2 = 1 ∧ ((p.1 ^ 2 + p.2 ^ 2 : ℤ) : ℝ) ≤ t

lemma PR_iff {t : ℝ} (ht : 0 ≤ t) (p : ℤ × ℤ) : PR t p ↔ P ⌊t⌋₊ p := by
  obtain ⟨x, y⟩ := p
  unfold PR P
  dsimp only
  constructor
  · rintro ⟨ho, hn⟩
    refine ⟨ho, ?_⟩
    have h0 : (0 : ℤ) ≤ x ^ 2 + y ^ 2 := by positivity
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le h0
    rw [hk] at hn ⊢
    have hk' : k ≤ ⌊t⌋₊ := Nat.le_floor (by exact_mod_cast hn)
    exact_mod_cast hk'
  · rintro ⟨ho, hn⟩
    refine ⟨ho, ?_⟩
    have h1 : ((x ^ 2 + y ^ 2 : ℤ) : ℝ) ≤ ((⌊t⌋₊ : ℤ) : ℝ) := by exact_mod_cast hn
    have h2 : ((⌊t⌋₊ : ℤ) : ℝ) = (⌊t⌋₊ : ℝ) := by simp
    linarith [Nat.floor_le ht]

theorem NmixR_floor (t : ℝ) (ht : 0 ≤ t) : {p : ℤ × ℤ | PR t p}.ncard = Nmix ⌊t⌋₊ := by
  have hset : {p : ℤ × ℤ | PR t p} = (↑(Nset ⌊t⌋₊) : Set (ℤ × ℤ)) := by
    ext p
    simp only [Set.mem_setOf_eq, Finset.mem_coe, mem_Nset]
    exact PR_iff ht p
  rw [hset, Set.ncard_coe_finset]
  rfl

/-- Lemma 4.1 for real t ≥ 0 -/
theorem NmixR_le (t : ℝ) (ht : 0 ≤ t) : (({p : ℤ × ℤ | PR t p}.ncard : ℕ) : ℝ) ≤ 2 * (t + 1) := by
  rw [NmixR_floor t ht]
  have h : (Nmix ⌊t⌋₊ : ℝ) ≤ 2 * ((⌊t⌋₊ : ℝ) + 1) := by exact_mod_cast Nmix_le ⌊t⌋₊
  linarith [Nat.floor_le ht]

end Section4


/-!
# Lemma 4.2 of Howe-Huffman-Kohlmeyer-Kruer (hexagon:2611.00370v1), CONDITIONAL

STATUS: UNTESTED in Lean when written (no local toolchain). The first part of this file is
Lemma41.lean verbatim (Lemma 4.1, kernel-checked in earlier GitHub runs); the part below is new.

WHAT IS PROVED (once it compiles): for p odd and n, with the explicit hypothesis `hr2`,
      b_p(n) <= 16 * M * (n/(p*p) + 1)          (natural-number division)
      b_p(n) = 0 when n < p*p
and the summed estimate (4.1), with R a real number satisfying 12 n <= R.

HYPOTHESES THAT ARE NOT PROVED HERE (they appear in the theorem statements, not hidden):
* `hr2`: for every integer u with 1 <= u <= n, the number of (a,b) in the box [-n,n]^2 with
  a^2 + b^2 = u is at most 4 * M. In the paper M = M(n) and this is the two-square formula
  r2(u) <= 4 M(n). It is NOT proved here and Mathlib at the project pin has no r2 formula.
* `hR`: 12 n <= R. In the paper R = R(n) = 24 sigma(m) >= 12 n (Jacobi). Not proved here.
Also: the sum on the right of (4.1) is over primes p with p*p <= n only. That is the sum in the
paper restricted to the primes that can occur (the terms with p*p > n vanish, proved below),
so it is no larger than the paper's sum over all p > P. `Rmix`, `bp` are re-declared here
with the same definitions as Sufficiency23.lean (separate file, same text).
-/

namespace Section42
open Section4

noncomputable def Rmix (n : ℕ) : Finset (Fin 4 → ℤ) :=
  (Fintype.piFinset fun _ => Finset.Icc (-(n : ℤ)) n).filter
    (fun x => (x 0 + x 1) % 2 = 1 ∧ (x 2 + x 3) % 2 = 1 ∧
      x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 = (n : ℤ))

noncomputable def E1 (p n : ℕ) : Finset (Fin 4 → ℤ) :=
  (Rmix n).filter (fun x => (p : ℤ) ∣ x 0 ∧ (p : ℤ) ∣ x 1)

noncomputable def E2 (p n : ℕ) : Finset (Fin 4 → ℤ) :=
  (Rmix n).filter (fun x => (p : ℤ) ∣ x 2 ∧ (p : ℤ) ∣ x 3)

/-- b_p(n): same as `Sufficiency.bp` -/
noncomputable def bp (p n : ℕ) : ℕ :=
  ((Rmix n).filter (fun x => ((p : ℤ) ∣ x 0 ∧ (p : ℤ) ∣ x 1) ∨
    ((p : ℤ) ∣ x 2 ∧ (p : ℤ) ∣ x 3))).card

/-- integer points (a,b) of the box [-n,n]^2 with a^2 + b^2 = u -/
noncomputable def R2 (n : ℕ) (u : ℤ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-(n : ℤ)) n) ×ˢ (Finset.Icc (-(n : ℤ)) n)).filter
    (fun q => q.1 ^ 2 + q.2 ^ 2 = u)

lemma bp_le (p n : ℕ) : bp p n ≤ (E1 p n).card + (E2 p n).card := by
  unfold bp E1 E2
  rw [Finset.filter_or]
  exact Finset.card_union_le _ _

lemma mem_Rmix {n : ℕ} {x : Fin 4 → ℤ} :
    x ∈ Rmix n ↔ (∀ i, x i ∈ Finset.Icc (-(n : ℤ)) n) ∧ (x 0 + x 1) % 2 = 1 ∧
      (x 2 + x 3) % 2 = 1 ∧ x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 = (n : ℤ) := by
  unfold Rmix
  rw [Finset.mem_filter, Fintype.mem_piFinset]

def swap (x : Fin 4 → ℤ) : Fin 4 → ℤ := ![x 2, x 3, x 0, x 1]

lemma swap_swap (x : Fin 4 → ℤ) : swap (swap x) = x := by
  funext i
  fin_cases i <;> rfl

lemma swap_mem {n : ℕ} {x : Fin 4 → ℤ} (hx : x ∈ Rmix n) : swap x ∈ Rmix n := by
  rw [mem_Rmix] at hx ⊢
  obtain ⟨hb, h1, h2, h3⟩ := hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hb 2
    · exact hb 3
    · exact hb 0
    · exact hb 1
  · simpa [swap] using h2
  · simpa [swap] using h1
  · simp only [swap]
    simp
    linarith

lemma E2_card_le_E1 (p n : ℕ) : (E2 p n).card ≤ (E1 p n).card := by
  refine Finset.card_le_card_of_injOn swap ?_ ?_
  · intro x hx
    have hx' : x ∈ E2 p n := by exact_mod_cast hx
    unfold E2 at hx'
    rw [Finset.mem_filter] at hx'
    change swap x ∈ E1 p n
    unfold E1
    rw [Finset.mem_filter]
    exact ⟨swap_mem hx'.1, by simpa [swap] using hx'.2⟩
  · intro x _ x' _ h
    calc x = swap (swap x) := (swap_swap x).symm
      _ = swap (swap x') := by rw [h]
      _ = x' := swap_swap x'

/-- the pair obtained by dividing the first coordinate pair by p lies in the mixed-parity disk
    of radius^2 n/(p*p) -/
lemma E1_map {p n : ℕ} (hodd : p % 2 = 1) (hp : 0 < p) {x : Fin 4 → ℤ} (hx : x ∈ E1 p n) :
    (x 0 / (p : ℤ), x 1 / (p : ℤ)) ∈ Nset (n / (p * p)) := by
  have hx' := hx
  unfold E1 at hx'
  rw [Finset.mem_filter, mem_Rmix] at hx'
  obtain ⟨⟨hb, h1, h2, h3⟩, d0, d1⟩ := hx'
  have e0 : x 0 = (p : ℤ) * (x 0 / (p : ℤ)) := (Int.mul_ediv_cancel' d0).symm
  have e1 : x 1 = (p : ℤ) * (x 1 / (p : ℤ)) := (Int.mul_ediv_cancel' d1).symm
  generalize x 0 / (p : ℤ) = a0 at e0 ⊢
  generalize x 1 / (p : ℤ) = a1 at e1 ⊢
  have hpz : (p : ℤ) % 2 = 1 := by omega
  rw [mem_Nset]
  unfold P
  dsimp only
  refine ⟨?_, ?_⟩
  · by_contra hne
    have h0 : (a0 + a1) % 2 = 0 := by omega
    obtain ⟨c, hc⟩ : ∃ c, a0 + a1 = 2 * c := ⟨(a0 + a1) / 2, by omega⟩
    have h4 : (p : ℤ) * a0 + (p : ℤ) * a1 = 2 * ((p : ℤ) * c) := by
      rw [← mul_add, hc]; ring
    rw [e0, e1] at h1
    omega
  · have h0 : 0 ≤ a0 ^ 2 + a1 ^ 2 := by positivity
    obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le h0
    rw [ha]
    have hkey : (a : ℤ) * ((p : ℤ) * p) = ((p : ℤ) * a0) ^ 2 + ((p : ℤ) * a1) ^ 2 := by
      rw [← ha]; ring
    rw [e0, e1] at h3
    have hle : (a : ℤ) * ((p : ℤ) * p) ≤ (n : ℤ) := by
      nlinarith [sq_nonneg (x 2), sq_nonneg (x 3)]
    have hmul : a * (p * p) ≤ n := by exact_mod_cast hle
    exact_mod_cast (Nat.le_div_iff_mul_le (Nat.mul_pos hp hp)).2 hmul

lemma fib_data {p n : ℕ} {x : Fin 4 → ℤ} {y : ℤ × ℤ} (hx : x ∈ E1 p n)
    (hxy : (x 0 / (p : ℤ), x 1 / (p : ℤ)) = y) : x 0 = p * y.1 ∧ x 1 = p * y.2 := by
  have hx' := hx
  unfold E1 at hx'
  rw [Finset.mem_filter] at hx'
  obtain ⟨_, d0, d1⟩ := hx'
  have e0 : x 0 / (p : ℤ) = y.1 := congrArg Prod.fst hxy
  have e1 : x 1 / (p : ℤ) = y.2 := congrArg Prod.snd hxy
  constructor
  · rw [← e0]; exact (Int.mul_ediv_cancel' d0).symm
  · rw [← e1]; exact (Int.mul_ediv_cancel' d1).symm

/-- the first-pair-divisible-by-p count, using Lemma 4.1 for the divided pair and `hr2` for the
    other pair -/
theorem E1_card_le {p n M : ℕ} (hodd : p % 2 = 1) (hp : 0 < p)
    (hr2 : ∀ u : ℤ, 1 ≤ u → u ≤ n → (R2 n u).card ≤ 4 * M) :
    (E1 p n).card ≤ 2 * (n / (p * p) + 1) * (4 * M) := by
  have hmap : ∀ x ∈ E1 p n, (x 0 / (p : ℤ), x 1 / (p : ℤ)) ∈ Nset (n / (p * p)) :=
    fun x hx => E1_map hodd hp hx
  have hsum := Finset.card_eq_sum_card_fiberwise
    (f := fun x : Fin 4 → ℤ => (x 0 / (p : ℤ), x 1 / (p : ℤ)))
    (s := E1 p n) (t := Nset (n / (p * p))) hmap
  have hfib : ∀ y ∈ Nset (n / (p * p)),
      ((E1 p n).filter (fun x => (x 0 / (p : ℤ), x 1 / (p : ℤ)) = y)).card ≤ 4 * M := by
    intro y _
    rcases Finset.eq_empty_or_nonempty
      ((E1 p n).filter (fun x => (x 0 / (p : ℤ), x 1 / (p : ℤ)) = y)) with hemp | ⟨x₀, hx₀⟩
    · rw [hemp]; simp
    · have key : ∀ x ∈ (E1 p n).filter (fun x => (x 0 / (p : ℤ), x 1 / (p : ℤ)) = y),
          x 2 ^ 2 + x 3 ^ 2 = (n : ℤ) - (p : ℤ) ^ 2 * (y.1 ^ 2 + y.2 ^ 2) ∧
          (x 2 + x 3) % 2 = 1 ∧ (∀ i, x i ∈ Finset.Icc (-(n : ℤ)) n) := by
        intro x hx
        rw [Finset.mem_filter] at hx
        obtain ⟨hxE, hxy⟩ := hx
        obtain ⟨f0, f1⟩ := fib_data hxE hxy
        have hxE' := hxE
        unfold E1 at hxE'
        rw [Finset.mem_filter, mem_Rmix] at hxE'
        obtain ⟨⟨hb, h1, h2, h3⟩, d0, d1⟩ := hxE'
        refine ⟨?_, h2, hb⟩
        rw [f0, f1] at h3
        nlinarith [h3]
      obtain ⟨hu_eq, hpar, _⟩ := key x₀ hx₀
      have hu1 : 1 ≤ (n : ℤ) - (p : ℤ) ^ 2 * (y.1 ^ 2 + y.2 ^ 2) := by
        rw [← hu_eq]
        by_contra hlt
        have s2 : x₀ 2 ^ 2 = 0 := by
          nlinarith [sq_nonneg (x₀ 2), sq_nonneg (x₀ 3), not_le.1 hlt]
        have s3 : x₀ 3 ^ 2 = 0 := by
          nlinarith [sq_nonneg (x₀ 2), sq_nonneg (x₀ 3), not_le.1 hlt]
        have hx2 : x₀ 2 = 0 := pow_eq_zero_iff (by norm_num) |>.1 s2
        have hx3 : x₀ 3 = 0 := pow_eq_zero_iff (by norm_num) |>.1 s3
        rw [hx2, hx3] at hpar
        omega
      have hu2 : (n : ℤ) - (p : ℤ) ^ 2 * (y.1 ^ 2 + y.2 ^ 2) ≤ n := by
        have : 0 ≤ (p : ℤ) ^ 2 * (y.1 ^ 2 + y.2 ^ 2) := by positivity
        linarith
      refine le_trans (Finset.card_le_card_of_injOn (fun x => (x 2, x 3)) ?_ ?_)
        (hr2 _ hu1 hu2)
      · intro x hx
        have hx' : x ∈ (E1 p n).filter (fun x => (x 0 / (p : ℤ), x 1 / (p : ℤ)) = y) := by
          exact_mod_cast hx
        obtain ⟨h1, _, hb⟩ := key x hx'
        change (x 2, x 3) ∈ R2 n _
        unfold R2
        rw [Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hb 2, hb 3⟩, h1⟩
      · intro x hx x' hx' hxx
        have hxm : x ∈ (E1 p n).filter (fun x => (x 0 / (p : ℤ), x 1 / (p : ℤ)) = y) := by
          exact_mod_cast hx
        have hxm' : x' ∈ (E1 p n).filter (fun x => (x 0 / (p : ℤ), x 1 / (p : ℤ)) = y) := by
          exact_mod_cast hx'
        rw [Finset.mem_filter] at hxm hxm'
        obtain ⟨a0, a1⟩ := fib_data hxm.1 hxm.2
        obtain ⟨b0, b1⟩ := fib_data hxm'.1 hxm'.2
        have e2 : x 2 = x' 2 := congrArg Prod.fst hxx
        have e3 : x 3 = x' 3 := congrArg Prod.snd hxx
        funext i
        fin_cases i
        · exact a0.trans b0.symm
        · exact a1.trans b1.symm
        · exact e2
        · exact e3
  calc (E1 p n).card
      = ∑ y ∈ Nset (n / (p * p)),
          ((E1 p n).filter (fun x => (x 0 / (p : ℤ), x 1 / (p : ℤ)) = y)).card := hsum
    _ ≤ ∑ y ∈ Nset (n / (p * p)), 4 * M := Finset.sum_le_sum hfib
    _ = (Nset (n / (p * p))).card * (4 * M) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (2 * (n / (p * p) + 1)) * (4 * M) :=
        Nat.mul_le_mul_right _ (Nmix_le (n / (p * p)))

lemma E1_empty {p n : ℕ} (hodd : p % 2 = 1) (hp : 0 < p) (hlt : n < p * p) :
    E1 p n = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro x hx
  have hm := E1_map hodd hp hx
  rw [mem_Nset] at hm
  unfold P at hm
  rw [Nat.div_eq_of_lt hlt] at hm
  obtain ⟨hpar, hb⟩ := hm
  dsimp only at hpar hb
  generalize x 0 / (p : ℤ) = a at hpar hb
  generalize x 1 / (p : ℤ) = b at hpar hb
  have hb0 : a ^ 2 + b ^ 2 ≤ 0 := by exact_mod_cast hb
  have s1 : a ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
  have s2 : b ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
  have ha : a = 0 := pow_eq_zero_iff (by norm_num) |>.1 s1
  have hb' : b = 0 := pow_eq_zero_iff (by norm_num) |>.1 s2
  rw [ha, hb'] at hpar
  omega

theorem bp_le_16 {p n M : ℕ} (hodd : p % 2 = 1) (hp : 0 < p)
    (hr2 : ∀ u : ℤ, 1 ≤ u → u ≤ n → (R2 n u).card ≤ 4 * M) :
    bp p n ≤ 16 * M * (n / (p * p) + 1) := by
  have h1 := bp_le p n
  have h2 := E2_card_le_E1 p n
  have h3 := E1_card_le hodd hp hr2
  linarith

theorem bp_zero {p n : ℕ} (hodd : p % 2 = 1) (hp : 0 < p) (hlt : n < p * p) : bp p n = 0 := by
  have h1 := bp_le p n
  have hE1 : (E1 p n).card = 0 := by rw [E1_empty hodd hp hlt]; simp
  have hE2 : (E2 p n).card = 0 := by
    have := E2_card_le_E1 p n
    omega
  omega

/-- (4.1), conditional on `hr2` (two-square count) and `hR` (R >= 12 n). -/
theorem lemma42 (n M P : ℕ) (R : ℝ) (hn : 0 < n)
    (hr2 : ∀ u : ℤ, 1 ≤ u → u ≤ n → (R2 n u).card ≤ 4 * M)
    (hR : 12 * (n : ℝ) ≤ R) :
    (1 / R) * ∑ p ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p % 4 = 3 ∧ P < p),
        (bp p n : ℝ)
      ≤ (4 / 3) * M * (∑ p ∈ ((Finset.range (n + 1)).filter
              (fun p => p.Prime ∧ p % 4 = 3 ∧ P < p)).filter (fun p => p * p ≤ n),
              1 / (p : ℝ) ^ 2
          + (((Finset.range (n + 1)).filter
              (fun p => p.Prime ∧ p % 4 = 3 ∧ P < p)).filter (fun p => p * p ≤ n)).card
            / (n : ℝ)) := by
  set Q := (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p % 4 = 3 ∧ P < p) with hQ
  set T := Q.filter (fun p => p * p ≤ n) with hT
  have hTQ : T ⊆ Q := Finset.filter_subset _ _
  have hsum : ∑ p ∈ Q, (bp p n : ℝ) = ∑ p ∈ T, (bp p n : ℝ) := by
    symm
    apply Finset.sum_subset hTQ
    intro p hpQ hpT
    have hp := (Finset.mem_filter.1 hpQ).2
    have h4 := hp.2.1
    have hlt : n < p * p := by
      by_contra h
      exact hpT (Finset.mem_filter.2 ⟨hpQ, not_lt.1 h⟩)
    have hodd : p % 2 = 1 := by omega
    have : bp p n = 0 := bp_zero hodd hp.1.pos hlt
    simp [this]
  have hpt : ∀ p ∈ T, (bp p n : ℝ) ≤ 16 * M * ((n : ℝ) * (1 / (p : ℝ) ^ 2) + 1) := by
    intro p hpT
    have hpQ := (Finset.mem_filter.1 hpT).1
    have hp := (Finset.mem_filter.1 hpQ).2
    have h4 := hp.2.1
    have hodd : p % 2 = 1 := by omega
    have hb := bp_le_16 hodd hp.1.pos hr2
    have hcast : (bp p n : ℝ) ≤ 16 * M * (((n / (p * p) : ℕ) : ℝ) + 1) := by
      exact_mod_cast hb
    have hdiv : ((n / (p * p) : ℕ) : ℝ) ≤ (n : ℝ) / (p : ℝ) ^ 2 := by
      have := Nat.cast_div_le (α := ℝ) (m := n) (n := p * p)
      simpa [pow_two] using this
    have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    have hxx : (n : ℝ) / (p : ℝ) ^ 2 = (n : ℝ) * (1 / (p : ℝ) ^ 2) := by ring
    have hmono : 16 * (M : ℝ) * (((n / (p * p) : ℕ) : ℝ) + 1)
        ≤ 16 * (M : ℝ) * ((n : ℝ) * (1 / (p : ℝ) ^ 2) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    exact le_trans hcast hmono
  have hB : ∑ p ∈ T, (bp p n : ℝ)
      ≤ 16 * M * ((n : ℝ) * ∑ p ∈ T, 1 / (p : ℝ) ^ 2 + (T.card : ℝ)) := by
    calc ∑ p ∈ T, (bp p n : ℝ)
        ≤ ∑ p ∈ T, 16 * (M : ℝ) * ((n : ℝ) * (1 / (p : ℝ) ^ 2) + 1) :=
          Finset.sum_le_sum hpt
      _ = 16 * M * ((n : ℝ) * ∑ p ∈ T, 1 / (p : ℝ) ^ 2 + (T.card : ℝ)) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
          simp
  have hS : 0 ≤ ∑ p ∈ T, (bp p n : ℝ) := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := hn'.ne'
  rw [hsum]
  have h1 : 1 / R ≤ 1 / (12 * (n : ℝ)) := one_div_le_one_div_of_le (by positivity) hR
  calc 1 / R * ∑ p ∈ T, (bp p n : ℝ)
      ≤ 1 / (12 * (n : ℝ)) * ∑ p ∈ T, (bp p n : ℝ) := mul_le_mul_of_nonneg_right h1 hS
    _ ≤ 1 / (12 * (n : ℝ)) *
          (16 * M * ((n : ℝ) * ∑ p ∈ T, 1 / (p : ℝ) ^ 2 + (T.card : ℝ))) :=
        mul_le_mul_of_nonneg_left hB (by positivity)
    _ = (4 / 3) * M * (∑ p ∈ T, 1 / (p : ℝ) ^ 2 + (T.card : ℝ) / (n : ℝ)) := by
        field_simp
        ring

end Section42

#print axioms Section4.Nmix_le
#print axioms Section42.E1_card_le
#print axioms Section42.bp_le_16
#print axioms Section42.bp_zero
#print axioms Section42.lemma42


/-!
# Lemma 5.2, estimate (5.2), of Howe-Huffman-Kohlmeyer-Kruer (hexagon:2611.00370v1)

  #{ p prime : p ≡ 3 (mod 4), 3 < p ≤ t }  ≤  2t/15 + 1   for every t ≥ 0.

Stated here as   15 * #{...} ≤ 2 * t + 15   (no division).

STATUS: UNTESTED in Lean (no local toolchain in the session that wrote this).
Expect possible compile errors; fix them against what the compiler says.

Method (the paper's mod-60 argument): such a prime is coprime to 60, hence lies in one of the
8 residue classes {7,11,19,23,31,43,47,59} mod 60. Counting integers in those classes up to t
gives the bound; the count is periodic with period 60 and 8 hits per period.

Previously only COMPUTED (checked up to 3,000,000 by script). This file is the proof.
(5.3), the tail sum, is added at the end of this file (also untested when written). (5.4) is added after it (also untested when written).
-/

namespace Section5

/-- the 8 residue classes mod 60 that are 3 mod 4 and coprime to 60 -/
def S : Finset ℕ := {7, 11, 19, 23, 31, 43, 47, 59}

def Pm (n : ℕ) : Prop := n % 60 ∈ S

instance : DecidablePred Pm := fun n => by unfold Pm; infer_instance

lemma count_sixty : Nat.count Pm 60 = 8 := by decide

lemma count_base : ∀ N, N < 60 → 15 * Nat.count Pm N ≤ 2 * N + 13 := by decide

lemma count_shift (M : ℕ) : Nat.count (fun k => Pm (60 + k)) M = Nat.count Pm M := by
  induction M with
  | zero => simp
  | succ n ih =>
    rw [Nat.count_succ, Nat.count_succ, ih]
    simp [Pm, Nat.add_mod_left]

lemma count_bound (N : ℕ) : 15 * Nat.count Pm N ≤ 2 * N + 13 := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    by_cases hN : N < 60
    · exact count_base N hN
    · obtain ⟨M, rfl⟩ : ∃ M, N = 60 + M := ⟨N - 60, by omega⟩
      have hadd := Nat.count_add (p := Pm) 60 M
      rw [count_shift M, count_sixty] at hadd
      have := ih M (by omega)
      omega

lemma residue_key : ∀ r, r < 60 → r % 4 = 3 → r % 3 ≠ 0 → r % 5 ≠ 0 → r ∈ S := by decide

/-- (5.2): primes p ≡ 3 mod 4 with 3 < p ≤ t number at most 2t/15 + 1. -/
theorem prime_count_bound (t : ℕ) :
    15 * ((Finset.range (t + 1)).filter (fun p => p.Prime ∧ p % 4 = 3 ∧ 3 < p)).card
      ≤ 2 * t + 15 := by
  have hsub : (Finset.range (t + 1)).filter (fun p => p.Prime ∧ p % 4 = 3 ∧ 3 < p)
      ⊆ (Finset.range (t + 1)).filter Pm := by
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    obtain ⟨hr, hpr, h4, h3⟩ := hp
    refine ⟨hr, ?_⟩
    have h3d : ¬ 3 ∣ p := by
      intro hd
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hpr).1 hd
      omega
    have h5d : ¬ 5 ∣ p := by
      intro hd
      have := (Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 5) hpr).1 hd
      omega
    show p % 60 ∈ S
    exact residue_key (p % 60) (Nat.mod_lt _ (by norm_num)) (by omega) (by omega) (by omega)
  have h1 := Finset.card_le_card hsub
  have h2 : ((Finset.range (t + 1)).filter Pm).card = Nat.count Pm (t + 1) :=
    (Nat.count_eq_card_filter_range Pm (t + 1)).symm
  have h3 := count_bound (t + 1)
  omega

/-! ### (5.3): tail sum of 1/p² over primes p ≡ 3 mod 4, p > P

  Σ_{p>P, p≡3 (4)} 1/p²  ≤  2/(15P) + 2/P²     for integers P ≥ 3.

UNTESTED when written. Proof: a purely discrete version of the paper's partial summation.
Let a_k = 1 if k mod 60 ∈ S and 0 otherwise, A(K) = #{1 ≤ k ≤ K : a_k = 1}, and
B_K = A(K) − A(P) − (2/15)(K − P). The count bounds from (5.2) and its lower companion give
B_K ≤ 29/15 ≤ 2, and an induction on K proves
  Σ_{P<k≤K} a_k/k²  ≤  (2/15)(1/P − 1/K) + 2/P² − (2 − B_K)/K².
-/

lemma count_lower (N : ℕ) : 2 * N ≤ 15 * Nat.count Pm N + 16 := by
  have base : ∀ N, N < 60 → 2 * N ≤ 15 * Nat.count Pm N + 16 := by decide
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    by_cases hN : N < 60
    · exact base N hN
    · obtain ⟨M, rfl⟩ : ∃ M, N = 60 + M := ⟨N - 60, by omega⟩
      have hadd := Nat.count_add (p := Pm) 60 M
      rw [count_shift M, count_sixty] at hadd
      have := ih M (by omega)
      omega

/-- A(K) = number of k in [0, K] with k mod 60 ∈ S (0 is never in S, so this counts 1..K) -/
def Acnt (K : ℕ) : ℕ := Nat.count Pm (K + 1)

lemma Acnt_succ (K : ℕ) : Acnt (K + 1) = Acnt K + (if Pm (K + 1) then 1 else 0) := by
  unfold Acnt
  rw [Nat.count_succ]

lemma A_upper (K : ℕ) : (15 : ℝ) * (Acnt K : ℝ) ≤ 2 * K + 15 := by
  have h := count_bound (K + 1)
  unfold Acnt
  have : (15 : ℝ) * (Nat.count Pm (K + 1) : ℝ) ≤ 2 * ((K + 1 : ℕ) : ℝ) + 13 := by exact_mod_cast h
  push_cast at this
  linarith

lemma A_lower (K : ℕ) : 2 * (K : ℝ) ≤ 15 * (Acnt K : ℝ) + 14 := by
  have h := count_lower (K + 1)
  unfold Acnt
  have : 2 * ((K + 1 : ℕ) : ℝ) ≤ 15 * (Nat.count Pm (K + 1) : ℝ) + 16 := by exact_mod_cast h
  push_cast at this
  linarith

noncomputable def Bf (P K : ℕ) : ℝ := (Acnt K : ℝ) - (Acnt P : ℝ) - (2 / 15) * ((K : ℝ) - P)

lemma Bf_le (P K : ℕ) : Bf P K ≤ 2 := by
  unfold Bf
  have h1 := A_upper K
  have h2 := A_lower P
  linarith

lemma Bf_self (P : ℕ) : Bf P P = 0 := by simp [Bf]

lemma Bf_succ (P K : ℕ) :
    Bf P (K + 1) = Bf P K + (if Pm (K + 1) then (1 : ℝ) else 0) - 2 / 15 := by
  by_cases h : Pm (K + 1)
  · simp [Bf, Acnt_succ, h]; ring
  · simp [Bf, Acnt_succ, h]; ring

noncomputable def Ssum (P K : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ioc P K, (if Pm k then (1 : ℝ) else 0) / (k : ℝ) ^ 2

theorem tail_bound (P : ℕ) (hP : 1 ≤ P) :
    ∀ K, P ≤ K → Ssum P K ≤
      (2 / 15) * (1 / (P : ℝ) - 1 / (K : ℝ)) + 2 / (P : ℝ) ^ 2 - (2 - Bf P K) / (K : ℝ) ^ 2 := by
  intro K hK
  induction K, hK using Nat.le_induction with
  | base =>
    have hB := Bf_self P
    simp [Ssum, hB]
  | succ K hK ih =>
    have hK0 : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
    have hsum : Ssum P (K + 1) = Ssum P K + (if Pm (K + 1) then (1 : ℝ) else 0) / ((K : ℝ) + 1) ^ 2 := by
      unfold Ssum
      rw [Finset.sum_Ioc_succ_top hK]
      push_cast
      ring
    have hB := Bf_succ P K
    have hb2 := Bf_le P K
    have h1 : 1 / ((K : ℝ) + 1) - 1 / (K : ℝ) + 1 / ((K : ℝ) + 1) ^ 2 ≤ 0 := by
      have e : 1 / ((K : ℝ) + 1) - 1 / (K : ℝ) + 1 / ((K : ℝ) + 1) ^ 2
          = -1 / ((K : ℝ) * ((K : ℝ) + 1) ^ 2) := by
        field_simp
        ring
      rw [e]
      have hpos : 0 < (K : ℝ) * ((K : ℝ) + 1) ^ 2 := by positivity
      exact div_nonpos_of_nonpos_of_nonneg (by norm_num) hpos.le
    have h2 : 1 / ((K : ℝ) + 1) ^ 2 ≤ 1 / (K : ℝ) ^ 2 :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith)
    have h3 : 0 ≤ (2 - Bf P K) * (1 / (K : ℝ) ^ 2 - 1 / ((K : ℝ) + 1) ^ 2) :=
      mul_nonneg (by linarith) (by linarith)
    rw [hsum, hB]
    push_cast
    -- linarith treats `z / x^2` as one atom, so turn quotients into products with inverse atoms
    have e1 : ∀ z : ℝ, z / ((K : ℝ) + 1) ^ 2 = z * (((K : ℝ) + 1) ^ 2)⁻¹ := fun z => by ring
    have e0 : ∀ z : ℝ, z / (K : ℝ) ^ 2 = z * ((K : ℝ) ^ 2)⁻¹ := fun z => by ring
    simp only [one_div, e1, e0] at ih h1 h3 ⊢
    nlinarith [ih, h1, h3]

lemma prime_in_Pm {p : ℕ} (hp : p.Prime) (h4 : p % 4 = 3) (h3 : 3 < p) : Pm p := by
  have h3d : ¬ 3 ∣ p := by
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 hd
    omega
  have h5d : ¬ 5 ∣ p := by
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 5) hp).1 hd
    omega
  show p % 60 ∈ S
  exact residue_key (p % 60) (Nat.mod_lt _ (by norm_num)) (by omega) (by omega) (by omega)

/-- (5.3) -/
theorem prime_tail (P : ℕ) (hP : 3 ≤ P) (K : ℕ) :
    ∑ p ∈ (Finset.Ioc P K).filter (fun p => p.Prime ∧ p % 4 = 3), 1 / (p : ℝ) ^ 2
      ≤ 2 / (15 * (P : ℝ)) + 2 / (P : ℝ) ^ 2 := by
  have hPpos : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hrhs : 0 ≤ 2 / (15 * (P : ℝ)) + 2 / (P : ℝ) ^ 2 := by positivity
  by_cases hK : P ≤ K
  · have hsub : (Finset.Ioc P K).filter (fun p => p.Prime ∧ p % 4 = 3)
        ⊆ (Finset.Ioc P K).filter Pm := by
      intro p hp
      rw [Finset.mem_filter] at hp ⊢
      obtain ⟨hI, hpr, h4⟩ := hp
      exact ⟨hI, prime_in_Pm hpr h4 (by have := (Finset.mem_Ioc.1 hI).1; omega)⟩
    have h1 : ∑ p ∈ (Finset.Ioc P K).filter (fun p => p.Prime ∧ p % 4 = 3), 1 / (p : ℝ) ^ 2
        ≤ ∑ p ∈ (Finset.Ioc P K).filter Pm, 1 / (p : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    have h2 : ∑ p ∈ (Finset.Ioc P K).filter Pm, 1 / (p : ℝ) ^ 2 = Ssum P K := by
      unfold Ssum
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      split_ifs <;> simp
    have h3 := tail_bound P (by omega) K hK
    have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
    have h4 : 0 ≤ (2 - Bf P K) / (K : ℝ) ^ 2 :=
      div_nonneg (by linarith [Bf_le P K]) (by positivity)
    have h5 : 0 < 1 / (K : ℝ) := by positivity
    have h6 : 2 / (15 * (P : ℝ)) = (2 / 15) * (1 / (P : ℝ)) := by field_simp
    rw [h2] at h1
    rw [h6]
    nlinarith [h1, h3, h4, h5]
  · have : (Finset.Ioc P K) = ∅ := by
      ext x; simp only [Finset.mem_Ioc, Finset.notMem_empty, iff_false]; omega
    rw [this]
    simpa using hrhs

/-! ### (5.4): 2 Σ_{p ≡ 3 (4)} 1/(p(p−1)) < 21/50

UNTESTED when written, and it depends on `prime_tail` (5.3) compiling first.
Split at 60: the nine primes ≤ 60 are summed exactly; for p > 60, 1/(p(p−1)) ≤ (60/59)/p²,
and (5.3) at P = 60 bounds the rest. This is the paper's own split. -/

def PT (K : ℕ) : Finset ℕ := (Finset.range (K + 1)).filter (fun p => p.Prime ∧ p % 4 = 3)

lemma small_primes : ∀ p, p ≤ 60 → p.Prime → p % 4 = 3 →
    p ∈ ({3, 7, 11, 19, 23, 31, 43, 47, 59} : Finset ℕ) := by decide

lemma small_sum :
    ∑ p ∈ ({3, 7, 11, 19, 23, 31, 43, 47, 59} : Finset ℕ), 1 / ((p : ℝ) * ((p : ℝ) - 1))
      < 21 / 100 - (60 / 59) * (2 / (15 * 60) + 2 / 60 ^ 2) := by
  norm_num [Finset.sum_insert]

theorem five_four (K : ℕ) :
    2 * ∑ p ∈ PT K, 1 / ((p : ℝ) * ((p : ℝ) - 1)) < 21 / 50 := by
  have hsplit := Finset.sum_filter_add_sum_filter_not (PT K) (fun p => p ≤ 60)
    (fun p => 1 / ((p : ℝ) * ((p : ℝ) - 1)))
  -- primes up to 60
  have hsmall : ∑ p ∈ (PT K).filter (fun p => p ≤ 60), 1 / ((p : ℝ) * ((p : ℝ) - 1))
      ≤ ∑ p ∈ ({3, 7, 11, 19, 23, 31, 43, 47, 59} : Finset ℕ), 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      simp only [PT, Finset.mem_filter] at hp
      obtain ⟨⟨_, hpr, h4⟩, hle⟩ := hp
      exact small_primes p hle hpr h4
    · intro p hp _
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  -- primes above 60
  have hlarge : ∑ p ∈ (PT K).filter (fun p => ¬ p ≤ 60), 1 / ((p : ℝ) * ((p : ℝ) - 1))
      ≤ (60 / 59) * (2 / (15 * 60) + 2 / 60 ^ 2) := by
    have hsub : (PT K).filter (fun p => ¬ p ≤ 60)
        ⊆ (Finset.Ioc 60 K).filter (fun p => p.Prime ∧ p % 4 = 3) := by
      intro p hp
      simp only [PT, Finset.mem_filter, Finset.mem_range] at hp
      obtain ⟨⟨hr, hpr, h4⟩, hle⟩ := hp
      exact Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨by omega, by omega⟩, hpr, h4⟩
    have hterm : ∀ p ∈ (PT K).filter (fun p => ¬ p ≤ 60),
        1 / ((p : ℝ) * ((p : ℝ) - 1)) ≤ (60 / 59) * (1 / (p : ℝ) ^ 2) := by
      intro p hp
      simp only [PT, Finset.mem_filter] at hp
      have hp61 : (61 : ℝ) ≤ p := by exact_mod_cast (show 61 ≤ p by omega)
      have hpos : 0 < (p : ℝ) * ((p : ℝ) - 1) := by nlinarith
      rw [div_le_iff₀ hpos]
      have hp2 : (0 : ℝ) < (p : ℝ) ^ 2 := by positivity
      have : (60 / 59 : ℝ) * (1 / (p : ℝ) ^ 2) * ((p : ℝ) * ((p : ℝ) - 1))
          = (60 / 59) * (((p : ℝ) - 1) / p) := by
        field_simp
      rw [this]
      have hq : (59 / 60 : ℝ) ≤ ((p : ℝ) - 1) / p := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith
      nlinarith
    have h1 := Finset.sum_le_sum hterm
    rw [← Finset.mul_sum] at h1
    have h2 : ∑ p ∈ (PT K).filter (fun p => ¬ p ≤ 60), 1 / (p : ℝ) ^ 2
        ≤ ∑ p ∈ (Finset.Ioc 60 K).filter (fun p => p.Prime ∧ p % 4 = 3), 1 / (p : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    have h3 := prime_tail 60 (by norm_num) K
    push_cast at h3
    have h4 : (60 / 59 : ℝ) * ∑ p ∈ (PT K).filter (fun p => ¬ p ≤ 60), 1 / (p : ℝ) ^ 2
        ≤ (60 / 59) * (2 / (15 * 60) + 2 / 60 ^ 2) :=
      mul_le_mul_of_nonneg_left (le_trans h2 h3) (by norm_num)
    linarith
  have := small_sum
  linarith

end Section5

#print axioms Section5.prime_count_bound
#print axioms Section5.prime_tail
#print axioms Section5.five_four

/-! ### Prop 6.1, stage 2b: the large-prime bound, shape of (6.2)
UNTESTED, not compiled anywhere. Lemma42.lean verbatim, then Lemma52.lean verbatim (its `import` line
dropped), then the new material below.

Combines Section42.lemma42 (conditional on hr2, hR) with (5.3) = Section5.prime_tail and
(5.2) = Section5.prime_count_bound. Hypotheses carried, NOT proved here:
  hr2 : r2(u) <= 4 M for 1 <= u <= n      (two-square formula, not in Mathlib)
  hR  : 12 n <= R                           (Jacobi: R = 24 sigma(m) >= 12 n)
  hM  : M <= (11/5) n^(1/5)                 (Section62.Mn_le gives this for M = Mn n; kept abstract here)
Conclusion has the paper's shape  (4/3) * M-bound * (2/(15P) + 2/P^2 + (2 sqrt n/15 + 1)/n). -/

namespace Section62b

open Section42 Section5

def Qs (n P : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p % 4 = 3 ∧ P < p)

def Ts (n P : ℕ) : Finset ℕ := (Qs n P).filter (fun p => p * p ≤ n)

theorem large_primes (n P M : ℕ) (R : ℝ) (hn : 0 < n) (hP : 3 ≤ P)
    (hr2 : ∀ u : ℤ, 1 ≤ u → u ≤ n → (R2 n u).card ≤ 4 * M)
    (hR : 12 * (n : ℝ) ≤ R)
    (hM : (M : ℝ) ≤ (11 / 5) * (n : ℝ) ^ ((1 : ℝ) / 5)) :
    (1 / R) * ∑ p ∈ Qs n P, (bp p n : ℝ)
      ≤ (4 / 3) * ((11 / 5) * (n : ℝ) ^ ((1 : ℝ) / 5)) *
          (2 / (15 * (P : ℝ)) + 2 / (P : ℝ) ^ 2 + (2 * Real.sqrt n / 15 + 1) / (n : ℝ)) := by
  have h42 : (1 / R) * ∑ p ∈ Qs n P, (bp p n : ℝ)
      ≤ (4 / 3) * M * (∑ p ∈ Ts n P, 1 / (p : ℝ) ^ 2 + ((Ts n P).card : ℝ) / (n : ℝ)) :=
    Section42.lemma42 n M P R hn hr2 hR
  -- (5.3) on T
  have hsub : Ts n P ⊆ (Finset.Ioc P n).filter (fun p => p.Prime ∧ p % 4 = 3) := by
    intro p hp
    simp only [Ts, Qs, Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc] at hp ⊢
    obtain ⟨⟨hlt, hpr, h4, hPp⟩, _⟩ := hp
    exact ⟨⟨hPp, by omega⟩, hpr, h4⟩
  have hS : ∑ p ∈ Ts n P, 1 / (p : ℝ) ^ 2 ≤ 2 / (15 * (P : ℝ)) + 2 / (P : ℝ) ^ 2 :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity))
      (prime_tail P hP n)
  -- (5.2) on T, at t = Nat.sqrt n
  have hsubc : Ts n P ⊆
      (Finset.range (Nat.sqrt n + 1)).filter (fun p => p.Prime ∧ p % 4 = 3 ∧ 3 < p) := by
    intro p hp
    simp only [Ts, Qs, Finset.mem_filter, Finset.mem_range] at hp ⊢
    obtain ⟨⟨hlt, hpr, h4, hPp⟩, hpp⟩ := hp
    have hsq := Nat.le_sqrt.2 hpp
    exact ⟨by omega, hpr, h4, by omega⟩
  have hc15 : 15 * (Ts n P).card ≤ 2 * Nat.sqrt n + 15 :=
    le_trans (Nat.mul_le_mul_left 15 (Finset.card_le_card hsubc)) (prime_count_bound (Nat.sqrt n))
  have hcR : ((Ts n P).card : ℝ) ≤ 2 * Real.sqrt n / 15 + 1 := by
    have h1 : (15 : ℝ) * ((Ts n P).card : ℝ) ≤ 2 * (Nat.sqrt n : ℝ) + 15 := by
      exact_mod_cast hc15
    have h2 : (Nat.sqrt n : ℝ) ≤ Real.sqrt n := Real.nat_sqrt_le_real_sqrt
    linarith
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hdiv : ((Ts n P).card : ℝ) / (n : ℝ) ≤ (2 * Real.sqrt n / 15 + 1) / (n : ℝ) :=
    div_le_div_of_nonneg_right hcR hnR.le
  have hUV : ∑ p ∈ Ts n P, 1 / (p : ℝ) ^ 2 + ((Ts n P).card : ℝ) / (n : ℝ)
      ≤ 2 / (15 * (P : ℝ)) + 2 / (P : ℝ) ^ 2 + (2 * Real.sqrt n / 15 + 1) / (n : ℝ) := by
    linarith
  have hU0 : 0 ≤ ∑ p ∈ Ts n P, 1 / (p : ℝ) ^ 2 + ((Ts n P).card : ℝ) / (n : ℝ) := by positivity
  have hMb : 0 ≤ (11 / 5 : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 5) := by positivity
  calc (1 / R) * ∑ p ∈ Qs n P, (bp p n : ℝ)
      ≤ (4 / 3) * M * (∑ p ∈ Ts n P, 1 / (p : ℝ) ^ 2 + ((Ts n P).card : ℝ) / (n : ℝ)) := h42
    _ ≤ (4 / 3) * ((11 / 5) * (n : ℝ) ^ ((1 : ℝ) / 5)) *
          (2 / (15 * (P : ℝ)) + 2 / (P : ℝ) ^ 2 + (2 * Real.sqrt n / 15 + 1) / (n : ℝ)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hM (by norm_num)) hUV hU0
          (mul_nonneg (by norm_num) hMb)

end Section62b

#print axioms Section62b.large_primes

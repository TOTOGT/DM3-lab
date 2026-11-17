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

#print axioms Section4.Nmix_le
#print axioms Section4.NmixR_le

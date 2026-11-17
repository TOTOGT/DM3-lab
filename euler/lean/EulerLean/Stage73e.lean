import Mathlib

/-! # Stage71b: Hurwitz division with remainder over the rational quaternions (UNTESTED when written; no compiler run yet)

WHAT THIS FILE PROVES, if it compiles.  For rational quaternions a and b, b not zero, there is a quaternion q whose
four coordinates form a Hurwitz point (all integers, or all in Z + 1/2) with  N(a - q b) < N(b),  N = Quaternion.normSq.

Hand derivation.  x = a b^-1 satisfies x b = a, so a - q b = (x - q) b.  The norm is multiplicative, so
N(a - q b) = N(x - q) N(b).  By the covering lemma (Stage71a, copied below) choose q Hurwitz with N(x - q) < 1.  N(b) > 0
since b is not zero.  Hence N(a - q b) < N(b).

DOES NOT PROVE: that the set of Hurwitz points is closed under addition and multiplication (it is a ring: that is a
separate lemma), so this is NOT yet "the Hurwitz order is Euclidean"; it is the approximation statement that Euclidean
division needs.  It does not prove unique factorization or Jacobi's count and does not discharge HJac.  The covering lemma
is copied from Stage71a (compiled clean in euler-stage66 run #9) with `push_neg` replaced by `push Not`. -/

open Finset

namespace Section71

/-- the Hurwitz lattice inside Q^4: all coordinates integers, or all in Z + 1/2 -/
def IsHur (q : Fin 4 → ℚ) : Prop :=
  (∀ i, ∃ z : ℤ, q i = z) ∨ (∀ i, ∃ z : ℤ, q i = z + 1 / 2)

theorem cover (x : Fin 4 → ℚ) : ∃ q : Fin 4 → ℚ, IsHur q ∧ ∑ i, (x i - q i) ^ 2 < 1 := by
  by_cases hall : ∀ i, |x i - round (x i)| = 1 / 2
  · refine ⟨x, Or.inr ?_, by simp⟩
    intro i
    have h := hall i
    rcases abs_eq (by norm_num : (0 : ℚ) ≤ 1 / 2) |>.1 h with h1 | h1
    · exact ⟨round (x i), by linarith⟩
    · exact ⟨round (x i) - 1, by push_cast; linarith⟩
  · push Not at hall
    obtain ⟨i0, hi0⟩ := hall
    have hle : ∀ i, (x i - round (x i)) ^ 2 ≤ 1 / 4 := by
      intro i
      have := abs_le.1 (abs_sub_round (x i))
      nlinarith [this.1, this.2]
    have hlt : (x i0 - round (x i0)) ^ 2 < 1 / 4 := by
      have h1 := abs_sub_round (x i0)
      have h2 : |x i0 - round (x i0)| < 1 / 2 := lt_of_le_of_ne h1 hi0
      have := abs_lt.1 h2
      nlinarith [this.1, this.2]
    refine ⟨fun i => ((round (x i) : ℤ) : ℚ), Or.inl (fun i => ⟨round (x i), rfl⟩), ?_⟩
    calc ∑ i, (x i - ((round (x i) : ℤ) : ℚ)) ^ 2
        < ∑ _i : Fin 4, (1 / 4 : ℚ) :=
          Finset.sum_lt_sum (fun i _ => hle i) ⟨i0, Finset.mem_univ _, hlt⟩
      _ = 1 := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; norm_num

end Section71


namespace Section71b

theorem hur_div_approx (a b : Quaternion ℚ) (hb : b ≠ 0) :
    ∃ q : Quaternion ℚ, Section71.IsHur ![q.re, q.imI, q.imJ, q.imK] ∧
      Quaternion.normSq (a - q * b) < Quaternion.normSq b := by
  obtain ⟨c, hc, hlt⟩ := Section71.cover ![(a * b⁻¹).re, (a * b⁻¹).imI, (a * b⁻¹).imJ, (a * b⁻¹).imK]
  have hcv : (![c 0, c 1, c 2, c 3] : Fin 4 → ℚ) = c := by
    funext i; fin_cases i <;> rfl
  obtain ⟨q, h0, h1, h2, h3⟩ : ∃ q : Quaternion ℚ,
      q.re = c 0 ∧ q.imI = c 1 ∧ q.imJ = c 2 ∧ q.imK = c 3 :=
    ⟨⟨c 0, c 1, c 2, c 3⟩, rfl, rfl, rfl, rfl⟩
  have hxb : a * b⁻¹ * b = a := by rw [mul_assoc, inv_mul_cancel₀ hb, mul_one]
  refine ⟨q, ?_, ?_⟩
  · rw [h0, h1, h2, h3, hcv]; exact hc
  · have e1 : a - q * b = (a * b⁻¹ - q) * b := by rw [sub_mul, hxb]
    have hnb : 0 < Quaternion.normSq b :=
      lt_of_le_of_ne Quaternion.normSq_nonneg (fun h => hb (Quaternion.normSq_eq_zero.1 h.symm))
    have e2 : Quaternion.normSq (a * b⁻¹ - q) < 1 := by
      rw [Quaternion.normSq_def']
      have r0 : (a * b⁻¹ - q).re = (a * b⁻¹).re - c 0 := by rw [← h0]; rfl
      have r1 : (a * b⁻¹ - q).imI = (a * b⁻¹).imI - c 1 := by rw [← h1]; rfl
      have r2 : (a * b⁻¹ - q).imJ = (a * b⁻¹).imJ - c 2 := by rw [← h2]; rfl
      have r3 : (a * b⁻¹ - q).imK = (a * b⁻¹).imK - c 3 := by rw [← h3]; rfl
      rw [r0, r1, r2, r3]
      simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three] at hlt
      nlinarith [hlt]
    rw [e1, map_mul]
    nlinarith [e2, hnb]

end Section71b



/-! # Stage71c: the Hurwitz lattice is closed under quaternion multiplication (UNTESTED when written; no compiler run yet)

WHAT THIS FILE PROVES, if it compiles.  Write a quaternion over Q as four rationals (a,b,c,d).  Call the quadruple
Hurwitz (`H a b c d`) if all four are integers, or all four lie in Z + 1/2.  Then, for the Hamilton product
  (a,b,c,d)(e,f,g,h) = (ae-bf-cg-dh,  af+be+ch-dg,  ag-bh+ce+df,  ah+bg-cf+de),
the product of two Hurwitz quadruples is Hurwitz (`H_mul`).  Also: `H_add`, `H_neg`, `H_one`.

Hand derivation (done before the Lean).  Integer x integer is trivial.  Mixed case: x integer (p,q,r,s), y = (u,v,w,t)+1/2.
Each product component is an integer plus (+-p +-q +-r +-s)/2, and +-p +-q +-r +-s has the parity of S = p+q+r+s whatever
the signs, so all four components share the class of S/2: all integers if S is even, all in Z+1/2 if S is odd.
Half x half: the products (p+1/2)(u+1/2) contribute integer + (p+u)/2 + 1/4, the four signed 1/4's sum to -1/2 (real part)
or +1/2 (the three imaginary parts), and the signed halves have the parity of T = p+q+r+s+u+v+w+t; again all four
components land in the same class.

NOT PROVED HERE: (1) that these four formulas are the multiplication of Mathlib's `Quaternion Q` (they are the Hamilton
product written out; the identification is not proved in this file), (2) the Hurwitz order as a bundled Subring,
(3) Euclidean division inside the ring, (4) unique factorization, (5) Jacobi's count, so HJac is NOT discharged. -/

namespace Section71c

/-- all four coordinates integers, or all four in Z + 1/2 -/
def H (a b c d : ℚ) : Prop :=
  (∃ p q r s : ℤ, a = p ∧ b = q ∧ c = r ∧ d = s) ∨
  (∃ p q r s : ℤ, a = p + 1 / 2 ∧ b = q + 1 / 2 ∧ c = r + 1 / 2 ∧ d = s + 1 / 2)

theorem H_one : H 1 0 0 0 := by
  left
  exact ⟨1, 0, 0, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem H_neg {a b c d : ℚ} (h : H a b c d) : H (-a) (-b) (-c) (-d) := by
  rcases h with ⟨p, q, r, s, rfl, rfl, rfl, rfl⟩ | ⟨p, q, r, s, rfl, rfl, rfl, rfl⟩
  · left
    refine ⟨-p, -q, -r, -s, ?_, ?_, ?_, ?_⟩ <;> push_cast <;> ring
  · right
    refine ⟨-p - 1, -q - 1, -r - 1, -s - 1, ?_, ?_, ?_, ?_⟩ <;> push_cast <;> ring

theorem H_add {a b c d e f g h : ℚ} (hx : H a b c d) (hy : H e f g h) :
    H (a + e) (b + f) (c + g) (d + h) := by
  rcases hx with ⟨p, q, r, s, rfl, rfl, rfl, rfl⟩ | ⟨p, q, r, s, rfl, rfl, rfl, rfl⟩ <;>
  rcases hy with ⟨u, v, w, t, rfl, rfl, rfl, rfl⟩ | ⟨u, v, w, t, rfl, rfl, rfl, rfl⟩
  · left
    refine ⟨p + u, q + v, r + w, s + t, ?_, ?_, ?_, ?_⟩ <;> push_cast <;> ring
  · right
    refine ⟨p + u, q + v, r + w, s + t, ?_, ?_, ?_, ?_⟩ <;> push_cast <;> ring
  · right
    refine ⟨p + u, q + v, r + w, s + t, ?_, ?_, ?_, ?_⟩ <;> push_cast <;> ring
  · left
    refine ⟨p + u + 1, q + v + 1, r + w + 1, s + t + 1, ?_, ?_, ?_, ?_⟩ <;> push_cast <;> ring

theorem H_mul {a b c d e f g h : ℚ} (hx : H a b c d) (hy : H e f g h) :
    H (a * e - b * f - c * g - d * h) (a * f + b * e + c * h - d * g)
      (a * g - b * h + c * e + d * f) (a * h + b * g - c * f + d * e) := by
  rcases hx with ⟨p, q, r, s, rfl, rfl, rfl, rfl⟩ | ⟨p, q, r, s, rfl, rfl, rfl, rfl⟩ <;>
  rcases hy with ⟨u, v, w, t, rfl, rfl, rfl, rfl⟩ | ⟨u, v, w, t, rfl, rfl, rfl, rfl⟩
  · -- integer x integer
    left
    refine ⟨p * u - q * v - r * w - s * t, p * v + q * u + r * t - s * w,
      p * w - q * t + r * u + s * v, p * t + q * w - r * v + s * u, ?_, ?_, ?_, ?_⟩ <;>
      push_cast <;> ring
  · -- integer x half : parity of S = p+q+r+s
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' (p + q + r + s)
    · have hS : (p : ℚ) + q + r + s = 2 * m := by exact_mod_cast hm
      left
      refine ⟨p * u - q * v - r * w - s * t + m - (q + r + s),
        p * v + q * u + r * t - s * w + m - s,
        p * w - q * t + r * u + s * v + m - q,
        p * t + q * w - r * v + s * u + m - r, ?_, ?_, ?_, ?_⟩ <;>
        push_cast <;> linear_combination (1 / 2 : ℚ) * hS
    · have hS : (p : ℚ) + q + r + s = 2 * m + 1 := by exact_mod_cast hm
      right
      refine ⟨p * u - q * v - r * w - s * t + m - (q + r + s),
        p * v + q * u + r * t - s * w + m - s,
        p * w - q * t + r * u + s * v + m - q,
        p * t + q * w - r * v + s * u + m - r, ?_, ?_, ?_, ?_⟩ <;>
        push_cast <;> linear_combination (1 / 2 : ℚ) * hS
  · -- half x integer : parity of S' = u+v+w+t
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' (u + v + w + t)
    · have hS : (u : ℚ) + v + w + t = 2 * m := by exact_mod_cast hm
      left
      refine ⟨p * u - q * v - r * w - s * t + m - (v + w + t),
        p * v + q * u + r * t - s * w + m - w,
        p * w - q * t + r * u + s * v + m - t,
        p * t + q * w - r * v + s * u + m - v, ?_, ?_, ?_, ?_⟩ <;>
        push_cast <;> linear_combination (1 / 2 : ℚ) * hS
    · have hS : (u : ℚ) + v + w + t = 2 * m + 1 := by exact_mod_cast hm
      right
      refine ⟨p * u - q * v - r * w - s * t + m - (v + w + t),
        p * v + q * u + r * t - s * w + m - w,
        p * w - q * t + r * u + s * v + m - t,
        p * t + q * w - r * v + s * u + m - v, ?_, ?_, ?_, ?_⟩ <;>
        push_cast <;> linear_combination (1 / 2 : ℚ) * hS
  · -- half x half : parity of T = p+q+r+s+u+v+w+t
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' (p + q + r + s + u + v + w + t)
    · have hT : (p : ℚ) + q + r + s + u + v + w + t = 2 * m := by exact_mod_cast hm
      right
      refine ⟨p * u - q * v - r * w - s * t + m - (q + v + r + w + s + t) - 1,
        p * v + q * u + r * t - s * w + m - (s + w),
        p * w - q * t + r * u + s * v + m - (q + t),
        p * t + q * w - r * v + s * u + m - (r + v), ?_, ?_, ?_, ?_⟩ <;>
        push_cast <;> linear_combination (1 / 2 : ℚ) * hT
    · have hT : (p : ℚ) + q + r + s + u + v + w + t = 2 * m + 1 := by exact_mod_cast hm
      left
      refine ⟨p * u - q * v - r * w - s * t + m - (q + v + r + w + s + t),
        p * v + q * u + r * t - s * w + m + 1 - (s + w),
        p * w - q * t + r * u + s * v + m + 1 - (q + t),
        p * t + q * w - r * v + s * u + m + 1 - (r + v), ?_, ?_, ?_, ?_⟩ <;>
        push_cast <;> linear_combination (1 / 2 : ℚ) * hT

end Section71c


/-! # Stage71d: Euclidean division in the Hurwitz order (UNTESTED when written; no compiler run yet)

This file is Stage71b + Stage71c concatenated (both compiled clean: runs #12, #13) followed by Section71d, which is new.

WHAT SECTION71D PROVES, if it compiles.  With `QH x` meaning the four coordinates of a rational quaternion x are a Hurwitz
quadruple (Section71c.H): for QH a, QH b, b not zero, there is q with QH q, QH (a - q b) and N(a - q b) < N(b).
Proof: Stage71b gives q Hurwitz with N(a - q b) < N(b); the product q b is Hurwitz by Stage71c (H_mul, identified with Mathlib's
product through Quaternion.mul_re etc.), a is Hurwitz, so a - q b = a + (-(q b)) is Hurwitz by H_add, H_neg.

NOT PROVED: a bundled Subring/EuclideanDomain instance, unique factorization of primitive elements, Jacobi's count, HJac.
Hurwitz order is non-commutative: this is LEFT-quotient division (a = q b + r, r small), which is what the factorization step uses. -/

namespace Section71d

def QH (x : Quaternion ℚ) : Prop := Section71c.H x.re x.imI x.imJ x.imK

theorem isHur_to_QH (x : Quaternion ℚ) (h : Section71.IsHur ![x.re, x.imI, x.imJ, x.imK]) : QH x := by
  rcases h with h | h
  · obtain ⟨p, hp⟩ := h 0
    obtain ⟨q, hq⟩ := h 1
    obtain ⟨r, hr⟩ := h 2
    obtain ⟨s, hs⟩ := h 3
    left
    exact ⟨p, q, r, s, by simpa using hp, by simpa using hq, by simpa using hr, by simpa using hs⟩
  · obtain ⟨p, hp⟩ := h 0
    obtain ⟨q, hq⟩ := h 1
    obtain ⟨r, hr⟩ := h 2
    obtain ⟨s, hs⟩ := h 3
    right
    exact ⟨p, q, r, s, by simpa using hp, by simpa using hq, by simpa using hr, by simpa using hs⟩

theorem QH_mul {x y : Quaternion ℚ} (hx : QH x) (hy : QH y) : QH (x * y) := by
  have h := Section71c.H_mul hx hy
  unfold QH
  have e0 : (x * y).re = x.re * y.re - x.imI * y.imI - x.imJ * y.imJ - x.imK * y.imK := by
    first
    | exact Quaternion.mul_re x y
    | (simp <;> ring)
    | (simp [QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul] <;> ring)
    | (simp [QuaternionAlgebra.mul_re, QuaternionAlgebra.mul_imI, QuaternionAlgebra.mul_imJ, QuaternionAlgebra.mul_imK] <;> ring)
    | (show _ = _; simp [HMul.hMul, Mul.mul] <;> ring)
  have e1 : (x * y).imI = x.re * y.imI + x.imI * y.re + x.imJ * y.imK - x.imK * y.imJ := by
    first
    | exact Quaternion.mul_imI x y
    | (simp <;> ring)
    | (simp [QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul] <;> ring)
    | (simp [QuaternionAlgebra.mul_re, QuaternionAlgebra.mul_imI, QuaternionAlgebra.mul_imJ, QuaternionAlgebra.mul_imK] <;> ring)
    | (show _ = _; simp [HMul.hMul, Mul.mul] <;> ring)
  have e2 : (x * y).imJ = x.re * y.imJ - x.imI * y.imK + x.imJ * y.re + x.imK * y.imI := by
    first
    | exact Quaternion.mul_imJ x y
    | (simp <;> ring)
    | (simp [QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul] <;> ring)
    | (simp [QuaternionAlgebra.mul_re, QuaternionAlgebra.mul_imI, QuaternionAlgebra.mul_imJ, QuaternionAlgebra.mul_imK] <;> ring)
    | (show _ = _; simp [HMul.hMul, Mul.mul] <;> ring)
  have e3 : (x * y).imK = x.re * y.imK + x.imI * y.imJ - x.imJ * y.imI + x.imK * y.re := by
    first
    | exact Quaternion.mul_imK x y
    | (simp <;> ring)
    | (simp [QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul] <;> ring)
    | (simp [QuaternionAlgebra.mul_re, QuaternionAlgebra.mul_imI, QuaternionAlgebra.mul_imJ, QuaternionAlgebra.mul_imK] <;> ring)
    | (show _ = _; simp [HMul.hMul, Mul.mul] <;> ring)
  rw [e0, e1, e2, e3]
  exact h

theorem QH_sub {x y : Quaternion ℚ} (hx : QH x) (hy : QH y) : QH (x - y) := by
  have h := Section71c.H_add hx (Section71c.H_neg hy)
  simp only [← sub_eq_add_neg] at h
  exact h

theorem hurwitz_euclid (a b : Quaternion ℚ) (ha : QH a) (hb : QH b) (hb0 : b ≠ 0) :
    ∃ q : Quaternion ℚ, QH q ∧ QH (a - q * b) ∧ Quaternion.normSq (a - q * b) < Quaternion.normSq b := by
  obtain ⟨q, hq, hlt⟩ := Section71b.hur_div_approx a b hb0
  have hqH : QH q := isHur_to_QH q hq
  exact ⟨q, hqH, QH_sub ha (QH_mul hqH hb), hlt⟩

end Section71d


/-! # Stage73a: RIGHT-sided Euclidean division in the Hurwitz order (UNTESTED when written; no compiler run yet)

The text above this block is Stage71d (which contains Stage71b and Stage71c); all of it compiled clean (runs #15, #17).
Section73a is new.

WHAT SECTION73A PROVES, if it compiles.  Conjugation `star` is an anti-automorphism of the quaternions that preserves the norm and
the Hurwitz coordinates.  Applying Stage71d to the conjugates gives:  for QH a, QH b, b not zero, there is q with QH q, QH (a - b q)
and N(a - b q) < N(b).  This is the form needed to show that right ideals q H + n H are principal.

Hand derivation of the divisor lemma this feeds (NOT in Lean yet).  Let p be prime and q in H primitive (not in p H) with p | N(q).
Let g generate the right ideal q H + p H.  Then N(g) divides N(p) = p^2.
 - N(g) = p^2 is impossible: p = g c gives N(c) = 1, c a unit, so g H = p H and q is in p H, contradicting primitivity.
 - N(g) = 1 is impossible: 1 = q a + p b, multiply by the conjugate q-bar on the left: q-bar = N(q) a + p q-bar b, and p | N(q), so q-bar is in p H, hence q is in p H, contradiction.
 - So N(g) = p and q = g q2 with N(q2) = N(q)/p.
 Uniqueness: if q = g' q2' with N(g') = p, then p = g' g'-bar, so g' left-divides both q and p; hence g H = q H + p H is contained in g' H;
 equal norms force g = g' c with c a unit.  So the left factor of norm p is unique up to a unit on the right.
 This holds at p = 2 as well; it is only the COUNT of such factors that differs at the ramified prime (JACOBI note, 2026-11-17).

NOT PROVED HERE: the divisor lemma itself, principal right ideals as a statement about a bundled ring, the count 24(p+1). -/

open Section71d

namespace Section73a

theorem QH_star {x : Quaternion ℚ} (hx : QH x) : QH (star x) := by
  have s0 : (star x).re = x.re := by first | rfl | simp
  have s1 : (star x).imI = -x.imI := by first | rfl | simp
  have s2 : (star x).imJ = -x.imJ := by first | rfl | simp
  have s3 : (star x).imK = -x.imK := by first | rfl | simp
  unfold QH at hx ⊢
  rw [s0, s1, s2, s3]
  rcases hx with ⟨p, q, r, s, h0, h1, h2, h3⟩ | ⟨p, q, r, s, h0, h1, h2, h3⟩
  · left
    refine ⟨p, -q, -r, -s, ?_, ?_, ?_, ?_⟩
    · rw [h0]
    · rw [h1]; push_cast; ring
    · rw [h2]; push_cast; ring
    · rw [h3]; push_cast; ring
  · right
    refine ⟨p, -q - 1, -r - 1, -s - 1, ?_, ?_, ?_, ?_⟩
    · rw [h0]
    · rw [h1]; push_cast; ring
    · rw [h2]; push_cast; ring
    · rw [h3]; push_cast; ring

theorem normSq_star' (x : Quaternion ℚ) : Quaternion.normSq (star x) = Quaternion.normSq x := by
  have s0 : (star x).re = x.re := by first | rfl | simp
  have s1 : (star x).imI = -x.imI := by first | rfl | simp
  have s2 : (star x).imJ = -x.imJ := by first | rfl | simp
  have s3 : (star x).imK = -x.imK := by first | rfl | simp
  rw [Quaternion.normSq_def', Quaternion.normSq_def', s0, s1, s2, s3]
  ring

theorem hurwitz_euclid_right (a b : Quaternion ℚ) (ha : QH a) (hb : QH b) (hb0 : b ≠ 0) :
    ∃ q : Quaternion ℚ, QH q ∧ QH (a - b * q) ∧ Quaternion.normSq (a - b * q) < Quaternion.normSq b := by
  have hb0' : star b ≠ 0 := fun h => hb0 (star_eq_zero.1 h)
  obtain ⟨q', hq', hqq, hlt⟩ :=
    Section71d.hurwitz_euclid (star a) (star b) (QH_star ha) (QH_star hb) hb0'
  have e : a - b * star q' = star (star a - q' * star b) := by
    simp only [star_sub, star_mul, star_star]
  refine ⟨star q', QH_star hq', ?_, ?_⟩
  · rw [e]
    exact QH_star hqq
  · rw [e, normSq_star']
    calc Quaternion.normSq (star a - q' * star b) < Quaternion.normSq (star b) := hlt
      _ = Quaternion.normSq b := normSq_star' b

end Section73a


/-! # Stage73b: units and the integrality of 4N (UNTESTED when written; no compiler run yet)

The text above is Stage73a (which contains Stage71b, 71c, 71d); all compiled clean (run #19).  Section73b is new.

WHAT SECTION73B PROVES, if it compiles.
 (1) `QH_one`: 1 has Hurwitz coordinates.
 (2) `unit_inv`: if QH u and N(u) = 1 then star u has Hurwitz coordinates and u * star u = 1 = star u * u.  So an element of norm 1 is a
     unit of the order, with inverse its conjugate (the fact Stage72a left open: it counted the 24 norm-one quadruples but did not show
     they are invertible in the order).
 (3) `four_normSq_nat`: for QH x, 4 N(x) is a natural number.  This is the measure that makes the Euclidean algorithm (right gcd)
     terminate by induction on a natural number.

Hand derivation of (3).  Integer case: 4N = 4(p^2+q^2+r^2+s^2).  Half case, x_i = p_i + 1/2: 4 sum (p_i + 1/2)^2 = 4 sum (p_i^2 + p_i) + 4.
Both are integers, and 4N >= 0, so 4N is a natural number.
Hand derivation of (2).  u star(u) has real part u0^2 + u1^2 + u2^2 + u3^2 = N(u) = 1 and each imaginary part cancels in pairs
(for example the i-part is u0(-u1) + u1 u0 + u2(-u3) - u3(-u2) = 0); same for star(u) u.

NOT PROVED: that the 24 quadruples of Stage72a are exactly the elements of QH of norm 1 as quaternions (Stage72a is about Fin 4 -> Q),
the right gcd lemma, the divisor lemma, any count. -/

namespace Section73b

theorem mul_comp (x y : Quaternion ℚ) :
    (x * y).re = x.re * y.re - x.imI * y.imI - x.imJ * y.imJ - x.imK * y.imK ∧
    (x * y).imI = x.re * y.imI + x.imI * y.re + x.imJ * y.imK - x.imK * y.imJ ∧
    (x * y).imJ = x.re * y.imJ - x.imI * y.imK + x.imJ * y.re + x.imK * y.imI ∧
    (x * y).imK = x.re * y.imK + x.imI * y.imJ - x.imJ * y.imI + x.imK * y.re := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals first | (simp <;> ring) | (simp [QuaternionAlgebra.re_mul] <;> ring) | (show _ = _; simp [HMul.hMul, Mul.mul] <;> ring)

theorem star_comp (x : Quaternion ℚ) :
    (star x).re = x.re ∧ (star x).imI = -x.imI ∧ (star x).imJ = -x.imJ ∧ (star x).imK = -x.imK := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals first | rfl | simp

theorem QH_one : QH (1 : Quaternion ℚ) := by
  have o0 : (1 : Quaternion ℚ).re = 1 := by first | rfl | simp
  have o1 : (1 : Quaternion ℚ).imI = 0 := by first | rfl | simp
  have o2 : (1 : Quaternion ℚ).imJ = 0 := by first | rfl | simp
  have o3 : (1 : Quaternion ℚ).imK = 0 := by first | rfl | simp
  unfold QH
  rw [o0, o1, o2, o3]
  exact Section71c.H_one

theorem unit_inv (u : Quaternion ℚ) (hu : QH u) (hn : Quaternion.normSq u = 1) :
    ∃ v : Quaternion ℚ, QH v ∧ u * v = 1 ∧ v * u = 1 := by
  have hq : u.re ^ 2 + u.imI ^ 2 + u.imJ ^ 2 + u.imK ^ 2 = 1 := by
    rw [← Quaternion.normSq_def']; exact hn
  obtain ⟨a0, a1, a2, a3⟩ := mul_comp u (star u)
  obtain ⟨b0, b1, b2, b3⟩ := mul_comp (star u) u
  obtain ⟨s0, s1, s2, s3⟩ := star_comp u
  have o0 : (1 : Quaternion ℚ).re = 1 := by first | rfl | simp
  have o1 : (1 : Quaternion ℚ).imI = 0 := by first | rfl | simp
  have o2 : (1 : Quaternion ℚ).imJ = 0 := by first | rfl | simp
  have o3 : (1 : Quaternion ℚ).imK = 0 := by first | rfl | simp
  refine ⟨star u, Section73a.QH_star hu, ?_, ?_⟩
  · first | refine Quaternion.ext _ _ ?_ ?_ ?_ ?_ | refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_
    · rw [a0, s0, s1, s2, s3, o0]; nlinarith [hq]
    · rw [a1, s0, s1, s2, s3, o1]; ring
    · rw [a2, s0, s1, s2, s3, o2]; ring
    · rw [a3, s0, s1, s2, s3, o3]; ring
  · first | refine Quaternion.ext _ _ ?_ ?_ ?_ ?_ | refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_
    · rw [b0, s0, s1, s2, s3, o0]; nlinarith [hq]
    · rw [b1, s0, s1, s2, s3, o1]; ring
    · rw [b2, s0, s1, s2, s3, o2]; ring
    · rw [b3, s0, s1, s2, s3, o3]; ring

theorem four_normSq_nat {x : Quaternion ℚ} (hx : QH x) :
    ∃ n : ℕ, 4 * Quaternion.normSq x = (n : ℚ) := by
  rw [Quaternion.normSq_def']
  unfold QH at hx
  obtain ⟨k, hk⟩ : ∃ k : ℤ, 4 * (x.re ^ 2 + x.imI ^ 2 + x.imJ ^ 2 + x.imK ^ 2) = (k : ℚ) := by
    rcases hx with ⟨p, q, r, s, h0, h1, h2, h3⟩ | ⟨p, q, r, s, h0, h1, h2, h3⟩
    · exact ⟨4 * (p ^ 2 + q ^ 2 + r ^ 2 + s ^ 2), by rw [h0, h1, h2, h3]; push_cast; ring⟩
    · exact ⟨4 * (p ^ 2 + p + q ^ 2 + q + r ^ 2 + r + s ^ 2 + s) + 4,
        by rw [h0, h1, h2, h3]; push_cast; ring⟩
  have hnn : (0 : ℚ) ≤ (k : ℚ) := by rw [← hk]; positivity
  have hk0 : 0 ≤ k := by exact_mod_cast hnn
  refine ⟨k.toNat, ?_⟩
  rw [hk]
  have := Int.toNat_of_nonneg hk0
  exact_mod_cast this.symm

end Section73b

namespace Section73c
open Section71d

theorem normSq_nat {x : Quaternion ℚ} (hx : QH x) :
    ∃ n : ℕ, Quaternion.normSq x = (n : ℚ) := by
  rw [Quaternion.normSq_def']
  unfold QH at hx
  obtain ⟨k, hk⟩ : ∃ k : ℤ, x.re ^ 2 + x.imI ^ 2 + x.imJ ^ 2 + x.imK ^ 2 = (k : ℚ) := by
    rcases hx with ⟨p, q, r, s, h0, h1, h2, h3⟩ | ⟨p, q, r, s, h0, h1, h2, h3⟩
    · exact ⟨p ^ 2 + q ^ 2 + r ^ 2 + s ^ 2, by rw [h0, h1, h2, h3]; push_cast; ring⟩
    · exact ⟨(p ^ 2 + p + q ^ 2 + q + r ^ 2 + r + s ^ 2 + s) + 1,
        by rw [h0, h1, h2, h3]; push_cast; ring⟩
  have hnn : (0 : ℚ) ≤ (k : ℚ) := by rw [← hk]; positivity
  have hk0 : 0 ≤ k := by exact_mod_cast hnn
  refine ⟨k.toNat, ?_⟩
  rw [hk]
  have := Int.toNat_of_nonneg hk0
  exact_mod_cast this.symm

end Section73c

namespace Section73d
open Section71d

/-- A right ideal of the Hurwitz order, as a predicate on rational quaternions. -/
structure RIdeal (I : Set (Quaternion ℚ)) : Prop where
  all_H : ∀ x ∈ I, QH x
  sub_mem : ∀ x ∈ I, ∀ y ∈ I, x - y ∈ I
  mul_mem : ∀ x ∈ I, ∀ y, QH y → x * y ∈ I

/-- Every nonzero right ideal is principal, generated by an element of minimal norm. -/
theorem min_gen (I : Set (Quaternion ℚ)) (hI : RIdeal I) (hne : ∃ x ∈ I, x ≠ 0) :
    ∃ g ∈ I, g ≠ 0 ∧ ∀ x ∈ I, ∃ y, QH y ∧ x = g * y := by
  classical
  have hex : ∃ n : ℕ, ∃ x ∈ I, x ≠ 0 ∧ Quaternion.normSq x = (n : ℚ) := by
    obtain ⟨x, hx, hx0⟩ := hne
    obtain ⟨n, hn⟩ := Section73c.normSq_nat (hI.all_H x hx)
    exact ⟨n, x, hx, hx0, hn⟩
  obtain ⟨g, hg, hg0, hgn⟩ := Nat.find_spec hex
  refine ⟨g, hg, hg0, ?_⟩
  intro x hx
  obtain ⟨q, hq, hr, hlt⟩ :=
    Section73a.hurwitz_euclid_right x g (hI.all_H x hx) (hI.all_H g hg) hg0
  have hmem : x - g * q ∈ I := hI.sub_mem x hx (g * q) (hI.mul_mem g hg q hq)
  by_contra hcon
  have hne0 : x - g * q ≠ 0 := by
    intro h
    apply hcon
    exact ⟨q, hq, by rw [sub_eq_zero] at h; exact h⟩
  obtain ⟨m, hm⟩ := Section73c.normSq_nat hr
  have hmle : Nat.find hex ≤ m := Nat.find_min' hex ⟨x - g * q, hmem, hne0, hm⟩
  rw [hm, hgn] at hlt
  have hlt' : m < Nat.find hex := by exact_mod_cast hlt
  omega

/-- Two generators of the same right ideal differ by a right unit. -/
theorem gens_unit (g g' a b : Quaternion ℚ) (hg : g ≠ 0) (ha : QH a) (hb : QH b)
    (h1 : g' = g * a) (h2 : g = g' * b) : QH a ∧ Quaternion.normSq a = 1 := by
  have hab : a * b = 1 := by
    apply mul_left_cancel₀ hg
    rw [mul_one, ← mul_assoc, ← h1, ← h2]
  have h3 := congrArg Quaternion.normSq hab
  rw [map_mul, map_one] at h3
  obtain ⟨n, hn⟩ := Section73c.normSq_nat ha
  obtain ⟨m, hm⟩ := Section73c.normSq_nat hb
  rw [hn, hm] at h3
  have h4 : n * m = 1 := by exact_mod_cast h3
  have hn1 : n = 1 := Nat.dvd_one.mp (Dvd.intro m h4)
  exact ⟨ha, by rw [hn, hn1]; simp⟩

/-- Conversely g*u for a unit u generates the same right ideal. -/
theorem unit_gen_mem (g u : Quaternion ℚ) (hu : QH u) (hn : Quaternion.normSq u = 1) :
    ∃ v, QH v ∧ g = (g * u) * v := by
  obtain ⟨v, hv, h1, _⟩ := Section73b.unit_inv u hu hn
  exact ⟨v, hv, by rw [mul_assoc, h1, mul_one]⟩

end Section73d



/-! # Stage72a: exactly 24 Hurwitz quadruples of norm 1 (UNTESTED when written; no compiler run yet)

WHAT THIS FILE PROVES, if it compiles.  The set of rational quadruples x = (x0,x1,x2,x3) that are Hurwitz (all four
integers, or all four in Z + 1/2) with  x0^2 + x1^2 + x2^2 + x3^2 = 1  has exactly 24 elements.

Hand derivation.  Put u = 2x.  Then u has integer entries, all even or all odd, with sum of squares 4.  Each |u_i| <= 2
because u_i^2 <= 4.  All even: one entry +-2 and the rest 0, so 4 positions x 2 signs = 8 (integral quaternions +-1, +-i, +-j, +-k).
All odd: every entry is +-1 (an odd entry has square 1 or 9, and 9 > 4), so 2^4 = 16 (the quaternions (+-1 +-i +-j +-k)/2).
Total 24.  The Lean below does not do this case split: it bounds the entries, then counts the finite set of numerators by
`decide +kernel`, then transports the count through the injective map u -> u/2.

DOES NOT PROVE: that these 24 elements are the units of the Hurwitz order (inverse = conjugate; that needs the ring structure),
nor anything about elements of other norms.  It is the finite fact "number of elements of norm 1 is 24" used by the Jacobi
count (JACOBI_PLAN.md step 1, in the form: units = Hurwitz quadruples of norm 1). -/

namespace Section72a

/-- all four coordinates integers, or all four in Z + 1/2 (same definition as Section71.IsHur) -/
def IsHur (q : Fin 4 → ℚ) : Prop :=
  (∀ i, ∃ z : ℤ, q i = z) ∨ (∀ i, ∃ z : ℤ, q i = z + 1 / 2)

/-- numerators u = 2x: entries all even or all odd, sum of squares 4; entries bounded by 2 so this is a finite set -/
noncomputable def U : Finset (Fin 4 → ℤ) :=
  (Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-2 : ℤ) 2).filter
    (fun u => ((∀ i, u i % 2 = 0) ∨ (∀ i, u i % 2 = 1)) ∧ ∑ i, u i ^ 2 = 4)

theorem U_card : U.card = 24 := by
  first
  | decide +kernel
  | rfl

theorem memU (u : Fin 4 → ℤ) :
    u ∈ U ↔ ((∀ i, u i % 2 = 0) ∨ (∀ i, u i % 2 = 1)) ∧ ∑ i, u i ^ 2 = 4 := by
  constructor
  · intro h
    exact (Finset.mem_filter.1 h).2
  · intro h
    have hb : ∀ i, -2 ≤ u i ∧ u i ≤ 2 := by
      intro i
      have hle : u i ^ 2 ≤ ∑ j, u j ^ 2 :=
        Finset.single_le_sum (f := fun j => u j ^ 2) (fun j _ => sq_nonneg (u j)) (Finset.mem_univ i)
      have h4 : u i ^ 2 ≤ 4 := by rw [h.2] at hle; exact hle
      constructor
      · by_contra hc
        push Not at hc
        nlinarith
      · by_contra hc
        push Not at hc
        nlinarith
    exact Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 (fun i => Finset.mem_Icc.2 (hb i)), h⟩

/-- halving map from numerators to rational quadruples -/
def f (u : Fin 4 → ℤ) : Fin 4 → ℚ := fun i => (u i : ℚ) / 2

theorem f_inj : Function.Injective f := by
  intro u v h
  funext i
  have h' : (u i : ℚ) / 2 = (v i : ℚ) / 2 := congrFun h i
  have h'' : (u i : ℚ) = (v i : ℚ) := by linarith
  exact_mod_cast h''

theorem hur_num (x : Fin 4 → ℚ) (hx : IsHur x) (hs : ∑ i, x i ^ 2 = 1) :
    ∃ u : Fin 4 → ℤ, u ∈ U ∧ f u = x := by
  rcases hx with h | h
  · choose z hz using h
    have e : ∑ i, (((2 * z i : ℤ) : ℚ)) ^ 2 = 4 * ∑ i, x i ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hz i]
      push_cast
      ring
    have e2 : ((∑ i, (2 * z i) ^ 2 : ℤ) : ℚ) = 4 := by
      push_cast
      push_cast at e
      rw [e, hs]
      norm_num
    have e3 : ∑ i, (2 * z i) ^ 2 = 4 := by exact_mod_cast e2
    refine ⟨fun i => 2 * z i, (memU _).2 ⟨Or.inl (fun i => by omega), e3⟩, ?_⟩
    funext i
    show ((2 * z i : ℤ) : ℚ) / 2 = x i
    rw [hz i]
    push_cast
    ring
  · choose z hz using h
    have e : ∑ i, (((2 * z i + 1 : ℤ) : ℚ)) ^ 2 = 4 * ∑ i, x i ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hz i]
      push_cast
      ring
    have e2 : ((∑ i, (2 * z i + 1) ^ 2 : ℤ) : ℚ) = 4 := by
      push_cast
      push_cast at e
      rw [e, hs]
      norm_num
    have e3 : ∑ i, (2 * z i + 1) ^ 2 = 4 := by exact_mod_cast e2
    refine ⟨fun i => 2 * z i + 1, (memU _).2 ⟨Or.inr (fun i => by omega), e3⟩, ?_⟩
    funext i
    show ((2 * z i + 1 : ℤ) : ℚ) / 2 = x i
    rw [hz i]
    push_cast
    ring

theorem f_mem (u : Fin 4 → ℤ) (hu : u ∈ U) : IsHur (f u) ∧ ∑ i, (f u i) ^ 2 = 1 := by
  have h := (memU u).1 hu
  constructor
  · rcases h.1 with h1 | h1
    · left
      intro i
      refine ⟨u i / 2, ?_⟩
      have hk : u i = 2 * (u i / 2) := by have := h1 i; omega
      show (u i : ℚ) / 2 = ((u i / 2 : ℤ) : ℚ)
      have hk' : (u i : ℚ) = 2 * ((u i / 2 : ℤ) : ℚ) := by exact_mod_cast hk
      rw [hk']
      ring
    · right
      intro i
      refine ⟨u i / 2, ?_⟩
      have hk : u i = 2 * (u i / 2) + 1 := by have := h1 i; omega
      show (u i : ℚ) / 2 = ((u i / 2 : ℤ) : ℚ) + 1 / 2
      have hk' : (u i : ℚ) = 2 * ((u i / 2 : ℤ) : ℚ) + 1 := by exact_mod_cast hk
      rw [hk']
      ring
  · have hq : (∑ i, (u i : ℚ) ^ 2) = 4 := by
      have := congrArg (fun t : ℤ => (t : ℚ)) h.2
      simpa using this
    have hs : ∑ i, ((u i : ℚ) / 2) ^ 2 = (∑ i, (u i : ℚ) ^ 2) / 4 := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    show ∑ i, ((u i : ℚ) / 2) ^ 2 = 1
    rw [hs, hq]
    norm_num

theorem units_set :
    {x : Fin 4 → ℚ | IsHur x ∧ ∑ i, x i ^ 2 = 1} = f '' (U : Set (Fin 4 → ℤ)) := by
  ext x
  constructor
  · rintro ⟨hx, hs⟩
    obtain ⟨u, hu, rfl⟩ := hur_num x hx hs
    exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact f_mem u hu

/-- there are exactly 24 Hurwitz quadruples of norm 1 -/
theorem units_count :
    {x : Fin 4 → ℚ | IsHur x ∧ ∑ i, x i ^ 2 = 1}.ncard = 24 := by
  rw [units_set, Set.ncard_image_of_injective _ f_inj]
  first
  | (rw [Set.ncard_coe_finset]; exact U_card)
  | (rw [Set.ncard_eq_toFinset_card' (U : Set (Fin 4 → ℤ))]; simpa using U_card)

end Section72a

namespace Section73e
open Section71d

def f (u : Quaternion ℚ) : Fin 4 → ℚ := ![u.re, u.imI, u.imJ, u.imK]

theorem f_inj : Function.Injective f := by
  intro u v h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  simp [f] at h0 h1 h2 h3
  first
  | (refine Quaternion.ext _ _ ?_ ?_ ?_ ?_ <;> assumption)
  | (refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_ <;> assumption)

theorem units_QH_count :
    {u : Quaternion ℚ | QH u ∧ Quaternion.normSq u = 1}.ncard = 24 := by
  have himg : f '' {u : Quaternion ℚ | QH u ∧ Quaternion.normSq u = 1} =
      {x : Fin 4 → ℚ | Section72a.IsHur x ∧ ∑ i, x i ^ 2 = 1} := by
    ext x
    constructor
    · rintro ⟨u, ⟨hu, hn⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · unfold QH Section71c.H at hu
        unfold Section72a.IsHur
        rcases hu with ⟨p, q, r, s, h0, h1, h2, h3⟩ | ⟨p, q, r, s, h0, h1, h2, h3⟩
        · left
          intro i
          fin_cases i
          · exact ⟨p, by simp [f, h0]⟩
          · exact ⟨q, by simp [f, h1]⟩
          · exact ⟨r, by simp [f, h2]⟩
          · exact ⟨s, by simp [f, h3]⟩
        · right
          intro i
          fin_cases i
          · exact ⟨p, by simp [f, h0]⟩
          · exact ⟨q, by simp [f, h1]⟩
          · exact ⟨r, by simp [f, h2]⟩
          · exact ⟨s, by simp [f, h3]⟩
      · have hs : ∑ i, f u i ^ 2 = u.re ^ 2 + u.imI ^ 2 + u.imJ ^ 2 + u.imK ^ 2 := by
          simp [f, Fin.sum_univ_four]
        rw [hs, ← Quaternion.normSq_def']
        exact hn
    · rintro ⟨hx, hs⟩
      let u : Quaternion ℚ := (⟨x 0, x 1, x 2, x 3⟩ : QuaternionAlgebra ℚ (-1) (-1))
      have e0 : u.re = x 0 := rfl
      have e1 : u.imI = x 1 := rfl
      have e2 : u.imJ = x 2 := rfl
      have e3 : u.imK = x 3 := rfl
      refine ⟨u, ⟨?_, ?_⟩, ?_⟩
      · unfold QH Section71c.H
        unfold Section72a.IsHur at hx
        rcases hx with hx | hx
        · obtain ⟨a, ha⟩ := hx 0
          obtain ⟨b, hb⟩ := hx 1
          obtain ⟨c, hc⟩ := hx 2
          obtain ⟨d, hd⟩ := hx 3
          left
          exact ⟨a, b, c, d, by rw [e0, ha], by rw [e1, hb], by rw [e2, hc], by rw [e3, hd]⟩
        · obtain ⟨a, ha⟩ := hx 0
          obtain ⟨b, hb⟩ := hx 1
          obtain ⟨c, hc⟩ := hx 2
          obtain ⟨d, hd⟩ := hx 3
          right
          exact ⟨a, b, c, d, by rw [e0, ha], by rw [e1, hb], by rw [e2, hc], by rw [e3, hd]⟩
      · rw [Quaternion.normSq_def', e0, e1, e2, e3, ← Fin.sum_univ_four (fun i => x i ^ 2)]
        exact hs
      · funext i
        fin_cases i <;> rfl
  rw [← Set.ncard_image_of_injective _ f_inj, himg]
  exact Section72a.units_count

/-- the generators of the right ideal gH -/
def Gens (g : Quaternion ℚ) : Set (Quaternion ℚ) :=
  {g' | ∃ a, QH a ∧ g' = g * a ∧ ∃ b, QH b ∧ g = g' * b}

theorem gens_count (g : Quaternion ℚ) (hg : g ≠ 0) : (Gens g).ncard = 24 := by
  have himg : (fun u => g * u) '' {u : Quaternion ℚ | QH u ∧ Quaternion.normSq u = 1} = Gens g := by
    ext g'
    constructor
    · rintro ⟨u, ⟨hu, hn⟩, rfl⟩
      obtain ⟨v, hv, h⟩ := Section73d.unit_gen_mem g u hu hn
      exact ⟨u, hu, rfl, v, hv, h⟩
    · rintro ⟨a, ha, h1, b, hb, h2⟩
      obtain ⟨_, hn⟩ := Section73d.gens_unit g g' a b hg ha hb h1 h2
      exact ⟨a, ⟨ha, hn⟩, h1.symm⟩
  rw [← himg, Set.ncard_image_of_injective _ (mul_right_injective₀ hg)]
  exact units_QH_count

end Section73e

#print axioms Section73e.units_QH_count
#print axioms Section73e.gens_count

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



/-! # Stage74a: the matrix model of the quaternion algebra over a field with x^2 + y^2 = -1 (UNTESTED when written)

WHAT THIS FILE PROVES, if it compiles.  Let K be a commutative ring and x, y in K with x^2 + y^2 = -1.  The map
psi(a,b,c,d) = a + b I + c J + d IJ, with I = [[0,-1],[1,0]] and J = [[x,y],[y,-x]], into 2x2 matrices over K satisfies:
 * psi is multiplicative for the Hamilton product of coefficient quadruples (psi_mul);
 * det psi(a,b,c,d) = a^2 + b^2 + c^2 + d^2 (psi_det);
 * psi(1,0,0,0) = 1 (psi_one);
 * over a field with 2 != 0, psi(a,b,c,d) = 0 forces a = b = c = d = 0 (psi_eq_zero).
Hand derivation: the four entries of psi(q1) psi(q2) - psi(q1 q2) are (c1c2+d1d2)(x^2+y^2+1), (c1d2-c2d1)(x^2+y^2+1),
(c2d1-c1d2)(x^2+y^2+1), (c1c2+d1d2)(x^2+y^2+1) (checked symbolically), so each vanishes when x^2+y^2 = -1.

DOES NOT PROVE: anything about the Hurwitz order, reduction modulo p, kernels or surjectivity.  Those are the next stage. -/

namespace Section74a

variable {K : Type*} [CommRing K]

def psi (x y a b c d : K) : Matrix (Fin 2) (Fin 2) K :=
  !![a + c * x - d * y, -b + c * y + d * x; b + c * y + d * x, a - c * x + d * y]

theorem psi_one (x y : K) : psi x y 1 0 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [psi]

theorem psi_mul (x y : K) (h : x ^ 2 + y ^ 2 = -1) (a1 b1 c1 d1 a2 b2 c2 d2 : K) :
    psi x y a1 b1 c1 d1 * psi x y a2 b2 c2 d2 =
      psi x y (a1 * a2 - b1 * b2 - c1 * c2 - d1 * d2) (a1 * b2 + b1 * a2 + c1 * d2 - d1 * c2)
        (a1 * c2 - b1 * d2 + c1 * a2 + d1 * b2) (a1 * d2 + b1 * c2 - c1 * b2 + d1 * a2) := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [psi, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (c1 * c2 + d1 * d2) * h
  · simp [psi, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (c1 * d2 - c2 * d1) * h
  · simp [psi, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (-c1 * d2 + c2 * d1) * h
  · simp [psi, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (c1 * c2 + d1 * d2) * h

theorem psi_det (x y : K) (h : x ^ 2 + y ^ 2 = -1) (a b c d : K) :
    (psi x y a b c d).det = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
  rw [Matrix.det_fin_two]
  simp [psi]
  linear_combination (-(c ^ 2 + d ^ 2)) * h

theorem psi_eq_zero {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (x y : F) (h : x ^ 2 + y ^ 2 = -1)
    (a b c d : F) (hz : psi x y a b c d = 0) : a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have e00 : a + c * x - d * y = 0 := by
    have := congrFun (congrFun hz 0) 0
    simpa [psi] using this
  have e01 : -b + c * y + d * x = 0 := by
    have := congrFun (congrFun hz 0) 1
    simpa [psi] using this
  have e10 : b + c * y + d * x = 0 := by
    have := congrFun (congrFun hz 1) 0
    simpa [psi] using this
  have e11 : a - c * x + d * y = 0 := by
    have := congrFun (congrFun hz 1) 1
    simpa [psi] using this
  have ha : a = 0 := by
    have : (2 : F) * a = 0 := by linear_combination e00 + e11
    exact (mul_eq_zero.mp this).resolve_left h2
  have hb : b = 0 := by
    have : (2 : F) * b = 0 := by linear_combination e10 - e01
    exact (mul_eq_zero.mp this).resolve_left h2
  have hu : c * x - d * y = 0 := by
    have : (2 : F) * (c * x - d * y) = 0 := by linear_combination e00 - e11
    exact (mul_eq_zero.mp this).resolve_left h2
  have hv : c * y + d * x = 0 := by
    have : (2 : F) * (c * y + d * x) = 0 := by linear_combination e01 + e10
    exact (mul_eq_zero.mp this).resolve_left h2
  have hc : c = 0 := by linear_combination (-1 : F) * (x * hu + y * hv) + c * h
  have hd : d = 0 := by linear_combination (-1 : F) * (x * hv - y * hu) + d * h
  exact ⟨ha, hb, hc, hd⟩

end Section74a

namespace Section74b
open Section71d

theorem coord_int {x : Quaternion ℚ} (hx : QH x) :
    ∃ a0 a1 a2 a3 : ℤ, 2 * x.re = a0 ∧ 2 * x.imI = a1 ∧ 2 * x.imJ = a2 ∧ 2 * x.imK = a3 := by
  unfold QH Section71c.H at hx
  rcases hx with ⟨n0, n1, n2, n3, h0, h1, h2, h3⟩ | ⟨n0, n1, n2, n3, h0, h1, h2, h3⟩
  · exact ⟨2 * n0, 2 * n1, 2 * n2, 2 * n3, by rw [h0]; push_cast; ring, by rw [h1]; push_cast; ring,
      by rw [h2]; push_cast; ring, by rw [h3]; push_cast; ring⟩
  · exact ⟨2 * n0 + 1, 2 * n1 + 1, 2 * n2 + 1, 2 * n3 + 1, by rw [h0]; push_cast; ring,
      by rw [h1]; push_cast; ring, by rw [h2]; push_cast; ring, by rw [h3]; push_cast; ring⟩

theorem exists_quat (a b c d : ℚ) :
    ∃ u : Quaternion ℚ, u.re = a ∧ u.imI = b ∧ u.imJ = c ∧ u.imK = d := by
  first
  | exact ⟨⟨a, b, c, d⟩, rfl, rfl, rfl, rfl⟩
  | exact ⟨QuaternionAlgebra.mk a b c d, rfl, rfl, rfl, rfl⟩

theorem scale_eq {F : Type*} [Field F] (c W i : F) (hi : 2 * i = 1) (h : 2 * c = W) :
    c * i = W * (i * i) := by
  linear_combination (-c * i) * hi + i ^ 2 * h

theorem int_case (P : ℤ) (hP : Prime P) (h2 : ¬ P ∣ 2) (n a : ℤ) (ha : a = 2 * n) (hd : P ∣ a) :
    ∃ m : ℤ, n = P * m := by
  rw [ha] at hd
  obtain ⟨m, hm⟩ := (hP.dvd_or_dvd hd).resolve_left h2
  exact ⟨m, hm⟩

theorem half_case (P : ℤ) (n a : ℤ) (ha : a = 2 * n + 1) (hd : P ∣ a) :
    ∃ m : ℤ, 2 * n + 1 = P * (2 * m + 1) := by
  obtain ⟨v, hv⟩ := hd
  rcases Int.even_or_odd' v with ⟨m, hm | hm⟩
  · exfalso
    rw [hm] at hv
    have h' : P * (2 * m) = 2 * (P * m) := by ring
    rw [h'] at hv
    generalize P * m = t at hv
    omega
  · exact ⟨m, by rw [← ha, hv, hm]⟩

variable (p : ℕ) [Fact p.Prime]

noncomputable def cz (q : ℚ) : ZMod p := ((⌊2 * q⌋ : ℤ) : ZMod p) * (2 : ZMod p)⁻¹

theorem cz_eq (q : ℚ) (z : ℤ) (h : 2 * q = (z : ℚ)) : cz p q = (z : ZMod p) * (2 : ZMod p)⁻¹ := by
  unfold cz
  rw [h, Int.floor_intCast]

noncomputable def red (xs ys : ZMod p) (x : Quaternion ℚ) : Matrix (Fin 2) (Fin 2) (ZMod p) :=
  Section74a.psi xs ys (cz p x.re) (cz p x.imI) (cz p x.imJ) (cz p x.imK)

theorem red_one (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) : red p xs ys 1 = 1 := by
  unfold red
  have e0 : (1 : Quaternion ℚ).re = 1 := by first | rfl | simp
  have e1 : (1 : Quaternion ℚ).imI = 0 := by first | rfl | simp
  have e2 : (1 : Quaternion ℚ).imJ = 0 := by first | rfl | simp
  have e3 : (1 : Quaternion ℚ).imK = 0 := by first | rfl | simp
  have c1 : cz p 1 = 1 := by
    rw [cz_eq p 1 2 (by norm_num)]
    push_cast
    exact mul_inv_cancel₀ h2
  have c0 : cz p 0 = 0 := by
    rw [cz_eq p 0 0 (by norm_num)]
    simp
  rw [e0, e1, e2, e3, c1, c0]
  exact Section74a.psi_one xs ys

theorem red_mul (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)
    {x y : Quaternion ℚ} (hx : QH x) (hy : QH y) :
    red p xs ys (x * y) = red p xs ys x * red p xs ys y := by
  obtain ⟨a0, a1, a2, a3, ha0, ha1, ha2, ha3⟩ := coord_int hx
  obtain ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3⟩ := coord_int hy
  obtain ⟨c0, c1, c2, c3, hc0, hc1, hc2, hc3⟩ := coord_int (QH_mul hx hy)
  obtain ⟨m0, m1, m2, m3⟩ := Section73b.mul_comp x y
  have k0 : (2 : ℤ) * c0 = a0 * b0 - a1 * b1 - a2 * b2 - a3 * b3 := by
    have : (2 : ℚ) * c0 = a0 * b0 - a1 * b1 - a2 * b2 - a3 * b3 := by
      rw [← hc0, ← ha0, ← ha1, ← ha2, ← ha3, ← hb0, ← hb1, ← hb2, ← hb3, m0]; ring
    exact_mod_cast this
  have k1 : (2 : ℤ) * c1 = a0 * b1 + a1 * b0 + a2 * b3 - a3 * b2 := by
    have : (2 : ℚ) * c1 = a0 * b1 + a1 * b0 + a2 * b3 - a3 * b2 := by
      rw [← hc1, ← ha0, ← ha1, ← ha2, ← ha3, ← hb0, ← hb1, ← hb2, ← hb3, m1]; ring
    exact_mod_cast this
  have k2 : (2 : ℤ) * c2 = a0 * b2 - a1 * b3 + a2 * b0 + a3 * b1 := by
    have : (2 : ℚ) * c2 = a0 * b2 - a1 * b3 + a2 * b0 + a3 * b1 := by
      rw [← hc2, ← ha0, ← ha1, ← ha2, ← ha3, ← hb0, ← hb1, ← hb2, ← hb3, m2]; ring
    exact_mod_cast this
  have k3 : (2 : ℤ) * c3 = a0 * b3 + a1 * b2 - a2 * b1 + a3 * b0 := by
    have : (2 : ℚ) * c3 = a0 * b3 + a1 * b2 - a2 * b1 + a3 * b0 := by
      rw [← hc3, ← ha0, ← ha1, ← ha2, ← ha3, ← hb0, ← hb1, ← hb2, ← hb3, m3]; ring
    exact_mod_cast this
  have hi : 2 * (2 : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ h2
  have z0 : (2 : ZMod p) * (c0 : ZMod p) = a0 * b0 - a1 * b1 - a2 * b2 - a3 * b3 := by
    have := congrArg (Int.cast : ℤ → ZMod p) k0
    push_cast at this
    exact this
  have z1 : (2 : ZMod p) * (c1 : ZMod p) = a0 * b1 + a1 * b0 + a2 * b3 - a3 * b2 := by
    have := congrArg (Int.cast : ℤ → ZMod p) k1
    push_cast at this
    exact this
  have z2 : (2 : ZMod p) * (c2 : ZMod p) = a0 * b2 - a1 * b3 + a2 * b0 + a3 * b1 := by
    have := congrArg (Int.cast : ℤ → ZMod p) k2
    push_cast at this
    exact this
  have z3 : (2 : ZMod p) * (c3 : ZMod p) = a0 * b3 + a1 * b2 - a2 * b1 + a3 * b0 := by
    have := congrArg (Int.cast : ℤ → ZMod p) k3
    push_cast at this
    exact this
  have e0 : (c0 : ZMod p) * (2 : ZMod p)⁻¹ =
      ((a0 : ZMod p) * (2 : ZMod p)⁻¹) * ((b0 : ZMod p) * (2 : ZMod p)⁻¹)
      - ((a1 : ZMod p) * (2 : ZMod p)⁻¹) * ((b1 : ZMod p) * (2 : ZMod p)⁻¹)
      - ((a2 : ZMod p) * (2 : ZMod p)⁻¹) * ((b2 : ZMod p) * (2 : ZMod p)⁻¹)
      - ((a3 : ZMod p) * (2 : ZMod p)⁻¹) * ((b3 : ZMod p) * (2 : ZMod p)⁻¹) := by
    rw [scale_eq _ _ _ hi z0]; ring
  have e1 : (c1 : ZMod p) * (2 : ZMod p)⁻¹ =
      ((a0 : ZMod p) * (2 : ZMod p)⁻¹) * ((b1 : ZMod p) * (2 : ZMod p)⁻¹)
      + ((a1 : ZMod p) * (2 : ZMod p)⁻¹) * ((b0 : ZMod p) * (2 : ZMod p)⁻¹)
      + ((a2 : ZMod p) * (2 : ZMod p)⁻¹) * ((b3 : ZMod p) * (2 : ZMod p)⁻¹)
      - ((a3 : ZMod p) * (2 : ZMod p)⁻¹) * ((b2 : ZMod p) * (2 : ZMod p)⁻¹) := by
    rw [scale_eq _ _ _ hi z1]; ring
  have e2 : (c2 : ZMod p) * (2 : ZMod p)⁻¹ =
      ((a0 : ZMod p) * (2 : ZMod p)⁻¹) * ((b2 : ZMod p) * (2 : ZMod p)⁻¹)
      - ((a1 : ZMod p) * (2 : ZMod p)⁻¹) * ((b3 : ZMod p) * (2 : ZMod p)⁻¹)
      + ((a2 : ZMod p) * (2 : ZMod p)⁻¹) * ((b0 : ZMod p) * (2 : ZMod p)⁻¹)
      + ((a3 : ZMod p) * (2 : ZMod p)⁻¹) * ((b1 : ZMod p) * (2 : ZMod p)⁻¹) := by
    rw [scale_eq _ _ _ hi z2]; ring
  have e3 : (c3 : ZMod p) * (2 : ZMod p)⁻¹ =
      ((a0 : ZMod p) * (2 : ZMod p)⁻¹) * ((b3 : ZMod p) * (2 : ZMod p)⁻¹)
      + ((a1 : ZMod p) * (2 : ZMod p)⁻¹) * ((b2 : ZMod p) * (2 : ZMod p)⁻¹)
      - ((a2 : ZMod p) * (2 : ZMod p)⁻¹) * ((b1 : ZMod p) * (2 : ZMod p)⁻¹)
      + ((a3 : ZMod p) * (2 : ZMod p)⁻¹) * ((b0 : ZMod p) * (2 : ZMod p)⁻¹) := by
    rw [scale_eq _ _ _ hi z3]; ring
  unfold red
  rw [cz_eq p _ c0 hc0, cz_eq p _ c1 hc1, cz_eq p _ c2 hc2, cz_eq p _ c3 hc3,
    cz_eq p _ a0 ha0, cz_eq p _ a1 ha1, cz_eq p _ a2 ha2, cz_eq p _ a3 ha3,
    cz_eq p _ b0 hb0, cz_eq p _ b1 hb1, cz_eq p _ b2 hb2, cz_eq p _ b3 hb3]
  rw [Section74a.psi_mul xs ys hxy, e0, e1, e2, e3]

theorem red_ker (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)
    {x : Quaternion ℚ} (hx : QH x) (hz : red p xs ys x = 0) :
    ∃ y : Quaternion ℚ, QH y ∧ x = (p : ℚ) • y := by
  obtain ⟨a0, a1, a2, a3, ha0, ha1, ha2, ha3⟩ := coord_int hx
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out)
  have hnd2 : ¬ (p : ℤ) ∣ 2 := by
    intro hd
    apply h2
    have := (CharP.intCast_eq_zero_iff (ZMod p) p (2 : ℤ)).mpr hd
    simpa using this
  have hdiv : (p : ℤ) ∣ a0 ∧ (p : ℤ) ∣ a1 ∧ (p : ℤ) ∣ a2 ∧ (p : ℤ) ∣ a3 := by
    unfold red at hz
    rw [cz_eq p _ a0 ha0, cz_eq p _ a1 ha1, cz_eq p _ a2 ha2, cz_eq p _ a3 ha3] at hz
    obtain ⟨z0, z1, z2, z3⟩ := Section74a.psi_eq_zero h2 xs ys hxy _ _ _ _ hz
    have hi : (2 : ZMod p)⁻¹ ≠ 0 := inv_ne_zero h2
    have w0 := (mul_eq_zero.mp z0).resolve_right hi
    have w1 := (mul_eq_zero.mp z1).resolve_right hi
    have w2 := (mul_eq_zero.mp z2).resolve_right hi
    have w3 := (mul_eq_zero.mp z3).resolve_right hi
    exact ⟨(CharP.intCast_eq_zero_iff (ZMod p) p a0).mp w0, (CharP.intCast_eq_zero_iff (ZMod p) p a1).mp w1,
      (CharP.intCast_eq_zero_iff (ZMod p) p a2).mp w2, (CharP.intCast_eq_zero_iff (ZMod p) p a3).mp w3⟩
  obtain ⟨d0, d1, d2, d3⟩ := hdiv
  unfold QH Section71c.H at hx
  rcases hx with ⟨n0, n1, n2, n3, h0, h1, h2', h3⟩ | ⟨n0, n1, n2, n3, h0, h1, h2', h3⟩
  · have g0 : a0 = 2 * n0 := by
      have : (a0 : ℚ) = 2 * n0 := by rw [← ha0, h0]
      exact_mod_cast this
    have g1 : a1 = 2 * n1 := by
      have : (a1 : ℚ) = 2 * n1 := by rw [← ha1, h1]
      exact_mod_cast this
    have g2 : a2 = 2 * n2 := by
      have : (a2 : ℚ) = 2 * n2 := by rw [← ha2, h2']
      exact_mod_cast this
    have g3 : a3 = 2 * n3 := by
      have : (a3 : ℚ) = 2 * n3 := by rw [← ha3, h3]
      exact_mod_cast this
    obtain ⟨m0, hm0⟩ := int_case (p : ℤ) hpZ hnd2 n0 a0 g0 d0
    obtain ⟨m1, hm1⟩ := int_case (p : ℤ) hpZ hnd2 n1 a1 g1 d1
    obtain ⟨m2, hm2⟩ := int_case (p : ℤ) hpZ hnd2 n2 a2 g2 d2
    obtain ⟨m3, hm3⟩ := int_case (p : ℤ) hpZ hnd2 n3 a3 g3 d3
    obtain ⟨y, y0, y1, y2, y3⟩ := exists_quat (m0 : ℚ) (m1 : ℚ) (m2 : ℚ) (m3 : ℚ)
    refine ⟨y, ?_, ?_⟩
    · unfold QH Section71c.H
      left
      exact ⟨m0, m1, m2, m3, y0, y1, y2, y3⟩
    · first
      | refine Quaternion.ext _ _ ?_ ?_ ?_ ?_
      | refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_
      · simp [y0, h0, hm0]
      · simp [y1, h1, hm1]
      · simp [y2, h2', hm2]
      · simp [y3, h3, hm3]
  · have g0 : a0 = 2 * n0 + 1 := by
      have : (a0 : ℚ) = 2 * n0 + 1 := by rw [← ha0, h0]; ring
      exact_mod_cast this
    have g1 : a1 = 2 * n1 + 1 := by
      have : (a1 : ℚ) = 2 * n1 + 1 := by rw [← ha1, h1]; ring
      exact_mod_cast this
    have g2 : a2 = 2 * n2 + 1 := by
      have : (a2 : ℚ) = 2 * n2 + 1 := by rw [← ha2, h2']; ring
      exact_mod_cast this
    have g3 : a3 = 2 * n3 + 1 := by
      have : (a3 : ℚ) = 2 * n3 + 1 := by rw [← ha3, h3]; ring
      exact_mod_cast this
    obtain ⟨m0, hm0⟩ := half_case (p : ℤ) n0 a0 g0 d0
    obtain ⟨m1, hm1⟩ := half_case (p : ℤ) n1 a1 g1 d1
    obtain ⟨m2, hm2⟩ := half_case (p : ℤ) n2 a2 g2 d2
    obtain ⟨m3, hm3⟩ := half_case (p : ℤ) n3 a3 g3 d3
    have q0 : (2 * (n0 : ℚ) + 1) = (p : ℚ) * (2 * m0 + 1) := by exact_mod_cast hm0
    have q1 : (2 * (n1 : ℚ) + 1) = (p : ℚ) * (2 * m1 + 1) := by exact_mod_cast hm1
    have q2 : (2 * (n2 : ℚ) + 1) = (p : ℚ) * (2 * m2 + 1) := by exact_mod_cast hm2
    have q3 : (2 * (n3 : ℚ) + 1) = (p : ℚ) * (2 * m3 + 1) := by exact_mod_cast hm3
    obtain ⟨y, y0, y1, y2, y3⟩ := exists_quat ((m0 : ℚ) + 1 / 2) ((m1 : ℚ) + 1 / 2)
      ((m2 : ℚ) + 1 / 2) ((m3 : ℚ) + 1 / 2)
    refine ⟨y, ?_, ?_⟩
    · unfold QH Section71c.H
      right
      exact ⟨m0, m1, m2, m3, y0, y1, y2, y3⟩
    · first
      | refine Quaternion.ext _ _ ?_ ?_ ?_ ?_
      | refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_
      · simp [y0, h0]; linear_combination (1 / 2 : ℚ) * q0
      · simp [y1, h1]; linear_combination (1 / 2 : ℚ) * q1
      · simp [y2, h2']; linear_combination (1 / 2 : ℚ) * q2
      · simp [y3, h3]; linear_combination (1 / 2 : ℚ) * q3

end Section74b

namespace Section74c
open Section71d

theorem psi_surj {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (x y : F) (h : x ^ 2 + y ^ 2 = -1)
    (M : Matrix (Fin 2) (Fin 2) F) : ∃ a b c d : F, Section74a.psi x y a b c d = M := by
  have hi : 2 * (2 : F)⁻¹ = 1 := mul_inv_cancel₀ h2
  refine ⟨(M 0 0 + M 1 1) * 2⁻¹, (M 1 0 - M 0 1) * 2⁻¹,
    -(x * ((M 0 0 - M 1 1) * 2⁻¹) + y * ((M 0 1 + M 1 0) * 2⁻¹)),
    -(x * ((M 0 1 + M 1 0) * 2⁻¹) - y * ((M 0 0 - M 1 1) * 2⁻¹)), ?_⟩
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Section74a.psi]
    linear_combination (-(2 : F)⁻¹ * (M 0 0 - M 1 1)) * h + M 0 0 * hi
  · simp [Section74a.psi]
    linear_combination (-(2 : F)⁻¹ * (M 0 1 + M 1 0)) * h + M 0 1 * hi
  · simp [Section74a.psi]
    linear_combination (-(2 : F)⁻¹ * (M 0 1 + M 1 0)) * h + M 1 0 * hi
  · simp [Section74a.psi]
    linear_combination ((2 : F)⁻¹ * (M 0 0 - M 1 1)) * h + M 1 1 * hi

variable (p : ℕ) [Fact p.Prime]

/-- every 2x2 matrix over F_p is the reduction of a Hurwitz element -/
theorem red_surj (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)
    (M : Matrix (Fin 2) (Fin 2) (ZMod p)) : ∃ x : Quaternion ℚ, QH x ∧ Section74b.red p xs ys x = M := by
  obtain ⟨a, b, c, d, habcd⟩ := psi_surj h2 xs ys hxy M
  obtain ⟨n0, hn0⟩ := ZMod.intCast_surjective a
  obtain ⟨n1, hn1⟩ := ZMod.intCast_surjective b
  obtain ⟨n2, hn2⟩ := ZMod.intCast_surjective c
  obtain ⟨n3, hn3⟩ := ZMod.intCast_surjective d
  obtain ⟨x, x0, x1, x2, x3⟩ := Section74b.exists_quat (n0 : ℚ) (n1 : ℚ) (n2 : ℚ) (n3 : ℚ)
  have cz_int : ∀ n : ℤ, Section74b.cz p (n : ℚ) = (n : ZMod p) := by
    intro n
    rw [Section74b.cz_eq p (n : ℚ) (2 * n) (by push_cast; ring)]
    push_cast
    field_simp
  refine ⟨x, ?_, ?_⟩
  · unfold QH Section71c.H
    left
    exact ⟨n0, n1, n2, n3, x0, x1, x2, x3⟩
  · unfold Section74b.red
    rw [x0, x1, x2, x3, cz_int, cz_int, cz_int, cz_int, hn0, hn1, hn2, hn3]
    exact habcd

/-- norm-determinant bridge: if N(x) = n then det (red x) = n in F_p -/
theorem det_red (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)
    {x : Quaternion ℚ} (hx : QH x) (n : ℕ) (hn : Quaternion.normSq x = (n : ℚ)) :
    (Section74b.red p xs ys x).det = (n : ZMod p) := by
  obtain ⟨a0, a1, a2, a3, ha0, ha1, ha2, ha3⟩ := Section74b.coord_int hx
  have hs : (a0 : ℚ) ^ 2 + a1 ^ 2 + a2 ^ 2 + a3 ^ 2 = 4 * n := by
    rw [← ha0, ← ha1, ← ha2, ← ha3, ← hn, Quaternion.normSq_def']
    ring
  have hs' : a0 ^ 2 + a1 ^ 2 + a2 ^ 2 + a3 ^ 2 = 4 * (n : ℤ) := by exact_mod_cast hs
  have hz : (a0 : ZMod p) ^ 2 + (a1 : ZMod p) ^ 2 + (a2 : ZMod p) ^ 2 + (a3 : ZMod p) ^ 2
      = 4 * (n : ZMod p) := by
    have := congrArg (Int.cast : ℤ → ZMod p) hs'
    push_cast at this
    exact this
  have hi : 2 * (2 : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ h2
  unfold Section74b.red
  rw [Section74b.cz_eq p _ a0 ha0, Section74b.cz_eq p _ a1 ha1, Section74b.cz_eq p _ a2 ha2,
    Section74b.cz_eq p _ a3 ha3, Section74a.psi_det xs ys hxy]
  linear_combination ((2 : ZMod p)⁻¹) ^ 2 * hz + ((n : ZMod p) * (2 * (2 : ZMod p)⁻¹ + 1)) * hi

end Section74c

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

namespace Section75b
open Section71d

theorem psi_sub {K : Type*} [CommRing K] (x y a b c d a' b' c' d' : K) :
    Section74a.psi x y (a - a') (b - b') (c - c') (d - d') =
      Section74a.psi x y a b c d - Section74a.psi x y a' b' c' d' := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Section74a.psi] <;> ring

theorem psi_zero {K : Type*} [CommRing K] (x y : K) : Section74a.psi x y 0 0 0 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Section74a.psi]

variable (p : ℕ) [Fact p.Prime]

theorem cz_sub (q1 q2 : ℚ) (z1 z2 : ℤ) (h1 : 2 * q1 = (z1 : ℚ)) (h2 : 2 * q2 = (z2 : ℚ)) :
    Section74b.cz p (q1 - q2) = Section74b.cz p q1 - Section74b.cz p q2 := by
  rw [Section74b.cz_eq p (q1 - q2) (z1 - z2) (by push_cast; rw [mul_sub, h1, h2]),
    Section74b.cz_eq p q1 z1 h1, Section74b.cz_eq p q2 z2 h2]
  push_cast
  ring

theorem red_sub (xs ys : ZMod p) {x y : Quaternion ℚ} (hx : QH x) (hy : QH y) :
    Section74b.red p xs ys (x - y) = Section74b.red p xs ys x - Section74b.red p xs ys y := by
  obtain ⟨a0, a1, a2, a3, ha0, ha1, ha2, ha3⟩ := Section74b.coord_int hx
  obtain ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3⟩ := Section74b.coord_int hy
  have e0 : (x - y).re = x.re - y.re := by first | rfl | simp
  have e1 : (x - y).imI = x.imI - y.imI := by first | rfl | simp
  have e2 : (x - y).imJ = x.imJ - y.imJ := by first | rfl | simp
  have e3 : (x - y).imK = x.imK - y.imK := by first | rfl | simp
  unfold Section74b.red
  rw [e0, e1, e2, e3, cz_sub p _ _ a0 b0 ha0 hb0, cz_sub p _ _ a1 b1 ha1 hb1,
    cz_sub p _ _ a2 b2 ha2 hb2, cz_sub p _ _ a3 b3 ha3 hb3]
  exact psi_sub xs ys _ _ _ _ _ _ _ _

theorem red_smul_p (xs ys : ZMod p) {z : Quaternion ℚ} (hz : QH z) :
    Section74b.red p xs ys ((p : ℚ) • z) = 0 := by
  obtain ⟨a0, a1, a2, a3, ha0, ha1, ha2, ha3⟩ := Section74b.coord_int hz
  have cz0 : ∀ (q : ℚ) (a : ℤ), 2 * q = (a : ℚ) → Section74b.cz p ((p : ℚ) * q) = 0 := by
    intro q a h
    rw [Section74b.cz_eq p ((p : ℚ) * q) ((p : ℤ) * a) (by push_cast; rw [← h]; ring)]
    push_cast
    simp
  have e0 : ((p : ℚ) • z).re = (p : ℚ) * z.re := by simp
  have e1 : ((p : ℚ) • z).imI = (p : ℚ) * z.imI := by simp
  have e2 : ((p : ℚ) • z).imJ = (p : ℚ) * z.imJ := by simp
  have e3 : ((p : ℚ) • z).imK = (p : ℚ) * z.imK := by simp
  unfold Section74b.red
  rw [e0, e1, e2, e3, cz0 _ a0 ha0, cz0 _ a1 ha1, cz0 _ a2 ha2, cz0 _ a3 ha3]
  exact psi_zero xs ys

/-- representatives of the p+1 lines: (1,t) and (0,1) -/
def kv : Option (ZMod p) → ZMod p × ZMod p
  | some t => (1, t)
  | none => (0, 1)

/-- the right ideal of Hurwitz elements whose reduction has both columns multiples of the key vector -/
def Ik (xs ys : ZMod p) (k : Option (ZMod p)) : Set (Quaternion ℚ) :=
  {x | QH x ∧ ∃ r s : ZMod p,
    Section74b.red p xs ys x 0 0 = r * (kv p k).1 ∧ Section74b.red p xs ys x 1 0 = r * (kv p k).2 ∧
    Section74b.red p xs ys x 0 1 = s * (kv p k).1 ∧ Section74b.red p xs ys x 1 1 = s * (kv p k).2}

theorem Ik_ideal (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)
    (k : Option (ZMod p)) : Section73d.RIdeal (Ik p xs ys k) where
  all_H := fun x hx => hx.1
  sub_mem := by
    rintro x ⟨hx, r, s, h00, h10, h01, h11⟩ y ⟨hy, r', s', g00, g10, g01, g11⟩
    refine ⟨QH_sub hx hy, r - r', s - s', ?_, ?_, ?_, ?_⟩
    · rw [red_sub p xs ys hx hy, Matrix.sub_apply, h00, g00]; ring
    · rw [red_sub p xs ys hx hy, Matrix.sub_apply, h10, g10]; ring
    · rw [red_sub p xs ys hx hy, Matrix.sub_apply, h01, g01]; ring
    · rw [red_sub p xs ys hx hy, Matrix.sub_apply, h11, g11]; ring
  mul_mem := by
    rintro x ⟨hx, r, s, h00, h10, h01, h11⟩ y hy
    refine ⟨QH_mul hx hy, r * Section74b.red p xs ys y 0 0 + s * Section74b.red p xs ys y 1 0,
      r * Section74b.red p xs ys y 0 1 + s * Section74b.red p xs ys y 1 1, ?_, ?_, ?_, ?_⟩
    · rw [Section74b.red_mul p h2 xs ys hxy hx hy, Matrix.mul_apply, Fin.sum_univ_two, h00, h01]; ring
    · rw [Section74b.red_mul p h2 xs ys hxy hx hy, Matrix.mul_apply, Fin.sum_univ_two, h10, h11]; ring
    · rw [Section74b.red_mul p h2 xs ys hxy hx hy, Matrix.mul_apply, Fin.sum_univ_two, h00, h01]; ring
    · rw [Section74b.red_mul p h2 xs ys hxy hx hy, Matrix.mul_apply, Fin.sum_univ_two, h10, h11]; ring

theorem one_not_mem (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (k : Option (ZMod p)) :
    (1 : Quaternion ℚ) ∉ Ik p xs ys k := by
  rintro ⟨_, r, s, h00, h10, h01, h11⟩
  rw [Section74b.red_one p h2 xs ys] at h00 h10 h01 h11
  have o00 : (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 = 1 := by simp
  have o10 : (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 = 0 := by simp
  have o01 : (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1 = 0 := by simp
  have o11 : (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 1 = 1 := by simp
  rw [o00] at h00
  rw [o10] at h10
  rw [o01] at h01
  rw [o11] at h11
  cases k with
  | some t =>
    dsimp [kv] at h00 h10 h01 h11
    have : (1 : ZMod p) = 0 := by linear_combination h11 - t * h01
    exact one_ne_zero this
  | none =>
    dsimp [kv] at h00 h10 h01 h11
    have : (1 : ZMod p) = 0 := by linear_combination h00
    exact one_ne_zero this

theorem Ik_not_pH (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)
    (k : Option (ZMod p)) :
    ∃ y : Quaternion ℚ, y ∈ Ik p xs ys k ∧ ∀ w : Quaternion ℚ, QH w → y ≠ (p : ℚ) • w := by
  obtain ⟨y, hy, hred⟩ := Section74c.red_surj p h2 xs ys hxy
    !![(kv p k).1, 0; (kv p k).2, 0]
  refine ⟨y, ⟨hy, 1, 0, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hred]; simp
  · rw [hred]; simp
  · rw [hred]; simp
  · rw [hred]; simp
  · intro w hw hyw
    have := red_smul_p p xs ys hw
    rw [← hyw, hred] at this
    cases k with
    | some t =>
      have e := congrFun (congrFun this 0) 0
      simp [kv] at e
    | none =>
      have e := congrFun (congrFun this 1) 0
      simp [kv] at e

theorem gen_exists (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)
    (k : Option (ZMod p)) :
    ∃ g : Quaternion ℚ, g ∈ Ik p xs ys k ∧ Quaternion.normSq g = (p : ℚ) ∧
      ∀ x ∈ Ik p xs ys k, ∃ y, QH y ∧ x = g * y := by
  have hI := Ik_ideal p h2 xs ys hxy k
  obtain ⟨y0, hy0, hy0n⟩ := Ik_not_pH p h2 xs ys hxy k
  have hq0 : QH (0 : Quaternion ℚ) := by
    have := QH_sub Section73b.QH_one Section73b.QH_one
    rwa [sub_self] at this
  have hne : ∃ x ∈ Ik p xs ys k, x ≠ 0 := by
    refine ⟨y0, hy0, ?_⟩
    intro h0
    exact hy0n 0 hq0 (by rw [h0, smul_zero])
  obtain ⟨g, hg, hg0, hgen⟩ := Section73d.min_gen _ hI hne
  have hu1 : QH ((p : ℚ) • (1 : Quaternion ℚ)) := by
    unfold QH Section71c.H
    left
    exact ⟨(p : ℤ), 0, 0, 0, by simp, by simp, by simp, by simp⟩
  have hu_mem : (p : ℚ) • (1 : Quaternion ℚ) ∈ Ik p xs ys k := by
    refine ⟨hu1, 0, 0, ?_, ?_, ?_, ?_⟩ <;>
    · rw [red_smul_p p xs ys Section73b.QH_one]; simp
  obtain ⟨c, hc, hgc⟩ := hgen _ hu_mem
  have hu_n : Quaternion.normSq ((p : ℚ) • (1 : Quaternion ℚ)) = (p : ℚ) ^ 2 := by
    rw [Quaternion.normSq_def']
    simp
  have hN : Quaternion.normSq g * Quaternion.normSq c = (p : ℚ) ^ 2 := by
    have := congrArg Quaternion.normSq hgc
    rw [map_mul, hu_n] at this
    exact this.symm
  obtain ⟨a, ha⟩ := Section73c.normSq_nat (hI.all_H g hg)
  obtain ⟨b, hb⟩ := Section73c.normSq_nat hc
  rw [ha, hb] at hN
  have hab : a * b = p ^ 2 := by exact_mod_cast hN
  have hdvd : a ∣ p ^ 2 := Dvd.intro b hab
  obtain ⟨m, hm, ham⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).1 hdvd
  interval_cases m
  · exfalso
    have hn1 : Quaternion.normSq g = 1 := by rw [ha, ham]; simp
    obtain ⟨v, hv, hgv, _⟩ := Section73b.unit_inv g (hI.all_H g hg) hn1
    have := hI.mul_mem g hg v hv
    rw [hgv] at this
    exact one_not_mem p h2 xs ys k this
  · refine ⟨g, hg, ?_, hgen⟩
    rw [ha, ham]
    simp
  · exfalso
    have hpp : 0 < p ^ 2 := pow_pos (Fact.out : p.Prime).pos 2
    have hb1 : b = 1 := by
      rw [ham] at hab
      exact Nat.eq_of_mul_eq_mul_left hpp (by rw [hab, mul_one])
    have hcn : Quaternion.normSq c = 1 := by rw [hb, hb1]; simp
    obtain ⟨v, hv, hcv, _⟩ := Section73b.unit_inv c hc hcn
    have hg' : g = (p : ℚ) • v := by
      calc g = g * (c * v) := by rw [hcv, mul_one]
        _ = (g * c) * v := by rw [mul_assoc]
        _ = ((p : ℚ) • (1 : Quaternion ℚ)) * v := by rw [← hgc]
        _ = (p : ℚ) • v := by rw [smul_mul_assoc, one_mul]
    obtain ⟨z, hz, hy0z⟩ := hgen y0 hy0
    exact hy0n (v * z) (QH_mul hv hz) (by rw [hy0z, hg', smul_mul_assoc])

end Section75b

namespace Section76a

variable {F : Type*} [Field F]

def kvF : Option F → F × F
  | some t => (1, t)
  | none => (0, 1)

def InKey (v : F × F) (M : Matrix (Fin 2) (Fin 2) F) : Prop :=
  ∃ r s : F, M 0 0 = r * v.1 ∧ M 1 0 = r * v.2 ∧ M 0 1 = s * v.1 ∧ M 1 1 = s * v.2

theorem indep (k k' : Option F) (h : k ≠ k') :
    (kvF k).1 * (kvF k').2 - (kvF k).2 * (kvF k').1 ≠ 0 := by
  cases k with
  | none =>
    cases k' with
    | none => exact absurd rfl h
    | some t' => simp [kvF]
  | some t =>
    cases k' with
    | none => simp [kvF]
    | some t' =>
      simp only [kvF]
      intro h0
      apply h
      congr 1
      linear_combination -h0

theorem key_unique (v w : F × F) (hind : v.1 * w.2 - v.2 * w.1 ≠ 0) (M : Matrix (Fin 2) (Fin 2) F)
    (hv : InKey v M) (hw : InKey w M) : M = 0 := by
  obtain ⟨r, s, a, b, c, d⟩ := hv
  obtain ⟨r', s', a', b', c', d'⟩ := hw
  have e1 : r * v.1 = r' * w.1 := a.symm.trans a'
  have e2 : r * v.2 = r' * w.2 := b.symm.trans b'
  have e3 : s * v.1 = s' * w.1 := c.symm.trans c'
  have e4 : s * v.2 = s' * w.2 := d.symm.trans d'
  have hr : r = 0 := by
    have : r * (v.1 * w.2 - v.2 * w.1) = 0 := by linear_combination w.2 * e1 - w.1 * e2
    exact (mul_eq_zero.mp this).resolve_right hind
  have hs : s = 0 := by
    have : s * (v.1 * w.2 - v.2 * w.1) = 0 := by linear_combination w.2 * e3 - w.1 * e4
    exact (mul_eq_zero.mp this).resolve_right hind
  ext i j
  fin_cases i <;> fin_cases j
  · simp [a, hr]
  · simp [c, hs]
  · simp [b, hr]
  · simp [d, hs]

theorem key_exists (M : Matrix (Fin 2) (Fin 2) F) (hdet : M.det = 0) (hM : M ≠ 0) :
    ∃ k : Option F, InKey (kvF k) M := by
  rw [Matrix.det_fin_two] at hdet
  by_cases h00 : M 0 0 = 0
  · by_cases h10 : M 1 0 = 0
    · by_cases h01 : M 0 1 = 0
      · have h11 : M 1 1 ≠ 0 := by
          intro h11
          apply hM
          ext i j
          fin_cases i <;> fin_cases j <;> simp [h00, h10, h01, h11]
        refine ⟨none, 0, M 1 1, ?_, ?_, ?_, ?_⟩ <;> simp [kvF, h00, h10, h01]
      · refine ⟨some (M 1 1 / M 0 1), 0, M 0 1, ?_, ?_, ?_, ?_⟩
        · simp [kvF, h00]
        · simp [kvF, h10]
        · simp [kvF]
        · simp [kvF]
          field_simp
    · have h01 : M 0 1 = 0 := by
        have : M 0 1 * M 1 0 = 0 := by rw [h00] at hdet; linear_combination -hdet
        exact (mul_eq_zero.mp this).resolve_right h10
      refine ⟨none, M 1 0, M 1 1, ?_, ?_, ?_, ?_⟩ <;> simp [kvF, h00, h01]
  · refine ⟨some (M 1 0 / M 0 0), M 0 0, M 0 1, ?_, ?_, ?_, ?_⟩
    · simp [kvF]
    · simp [kvF]
      field_simp
    · simp [kvF]
    · simp [kvF]
      field_simp
      linear_combination hdet

end Section76a

namespace Section76b
open Section71d

/-! Stage76b (UNTESTED when written).  Connects Stage75b's right ideals Ik (defined by reduced columns) to Stage76a's
2x2 key lemmas.  PROVES, if it compiles: (1) a Hurwitz x lying in two different Ik has red x = 0; (2) red x = 0 puts x in
every Ik; (3) if p divides N(x) and red x is not 0, x lies in exactly one Ik.  DOES NOT PROVE any count of elements;
the counting identity is the next stage. -/

variable (p : ℕ) [Fact p.Prime]

theorem kv_eq (k : Option (ZMod p)) : Section75b.kv p k = Section76a.kvF k := by
  cases k <;> rfl

theorem mem_Ik_iff (xs ys : ZMod p) (x : Quaternion ℚ) (k : Option (ZMod p)) :
    x ∈ Section75b.Ik p xs ys k ↔ QH x ∧ Section76a.InKey (Section76a.kvF k) (Section74b.red p xs ys x) := by
  constructor <;> intro h <;> simpa [Section75b.Ik, Section76a.InKey, kv_eq] using h

theorem Ik_unique (xs ys : ZMod p) {x : Quaternion ℚ} {k k' : Option (ZMod p)} (hk : k ≠ k')
    (h : x ∈ Section75b.Ik p xs ys k) (h' : x ∈ Section75b.Ik p xs ys k') :
    Section74b.red p xs ys x = 0 := by
  rw [mem_Ik_iff] at h h'
  exact Section76a.key_unique _ _ (Section76a.indep k k' hk) _ h.2 h'.2

theorem Ik_zero (xs ys : ZMod p) {x : Quaternion ℚ} (hx : QH x) (hz : Section74b.red p xs ys x = 0)
    (k : Option (ZMod p)) : x ∈ Section75b.Ik p xs ys k := by
  rw [mem_Ik_iff]
  refine ⟨hx, 0, 0, ?_, ?_, ?_, ?_⟩ <;> simp [hz]

theorem Ik_exists (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)
    {x : Quaternion ℚ} (hx : QH x) (n : ℕ) (hn : Quaternion.normSq x = (n : ℚ))
    (hdiv : (n : ZMod p) = 0) (hne : Section74b.red p xs ys x ≠ 0) :
    ∃ k : Option (ZMod p), x ∈ Section75b.Ik p xs ys k := by
  have hd := Section74c.det_red p h2 xs ys hxy hx n hn
  obtain ⟨k, hk⟩ := Section76a.key_exists (Section74b.red p xs ys x) (by rw [hd, hdiv]) hne
  exact ⟨k, (mem_Ik_iff p xs ys x k).2 ⟨hx, hk⟩⟩

theorem Ik_existsUnique (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)
    {x : Quaternion ℚ} (hx : QH x) (n : ℕ) (hn : Quaternion.normSq x = (n : ℚ))
    (hdiv : (n : ZMod p) = 0) (hne : Section74b.red p xs ys x ≠ 0) :
    ∃! k : Option (ZMod p), x ∈ Section75b.Ik p xs ys k := by
  obtain ⟨k, hk⟩ := Ik_exists p h2 xs ys hxy hx n hn hdiv hne
  refine ⟨k, hk, fun k' hk' => ?_⟩
  by_contra hne'
  exact hne (Ik_unique p xs ys (Ne.symm hne') hk hk')

end Section76b

namespace Section75a
open Section71d

def Hn (n : ℕ) : Set (Quaternion ℚ) := {x | QH x ∧ Quaternion.normSq x = (n : ℚ)}

theorem exq (a b c d : ℚ) : ∃ u : Quaternion ℚ, u.re = a ∧ u.imI = b ∧ u.imJ = c ∧ u.imK = d := by
  first
  | exact ⟨⟨a, b, c, d⟩, rfl, rfl, rfl, rfl⟩
  | exact ⟨QuaternionAlgebra.mk a b c d, rfl, rfl, rfl, rfl⟩

theorem ev_sq (n : ℤ) : ∃ k : ℤ, n ^ 2 + n = 2 * k := by
  rcases Int.even_or_odd' n with ⟨s, h | h⟩
  · exact ⟨2 * s ^ 2 + s, by rw [h]; ring⟩
  · exact ⟨2 * s ^ 2 + 3 * s + 1, by rw [h]; ring⟩

/-- an element of even norm 2m has integer coordinates -/
theorem int_coords (y : Quaternion ℚ) (hy : QH y) (m : ℕ)
    (hn : Quaternion.normSq y = 2 * (m : ℚ)) :
    ∃ a b c d : ℤ, y.re = a ∧ y.imI = b ∧ y.imJ = c ∧ y.imK = d := by
  unfold QH Section71c.H at hy
  rcases hy with ⟨a, b, c, d, h0, h1, h2, h3⟩ | ⟨n0, n1, n2, n3, h0, h1, h2, h3⟩
  · exact ⟨a, b, c, d, h0, h1, h2, h3⟩
  · exfalso
    have hq : (n0 : ℚ) ^ 2 + n0 + n1 ^ 2 + n1 + n2 ^ 2 + n2 + n3 ^ 2 + n3 + 1 = 2 * m := by
      rw [← hn, Quaternion.normSq_def', h0, h1, h2, h3]
      ring
    have hz : n0 ^ 2 + n0 + n1 ^ 2 + n1 + n2 ^ 2 + n2 + n3 ^ 2 + n3 + 1 = 2 * (m : ℤ) := by
      exact_mod_cast hq
    obtain ⟨k0, e0⟩ := ev_sq n0
    obtain ⟨k1, e1⟩ := ev_sq n1
    obtain ⟨k2, e2⟩ := ev_sq n2
    obtain ⟨k3, e3⟩ := ev_sq n3
    omega

/-- multiplication on the right by w = 1 + i is a bijection from norm m to norm 2m -/
theorem double_card (w : Quaternion ℚ) (hw0 : w.re = 1) (hw1 : w.imI = 1) (hw2 : w.imJ = 0)
    (hw3 : w.imK = 0) (m : ℕ) : (Hn (2 * m)).ncard = (Hn m).ncard := by
  have hwQH : QH w := by
    unfold QH Section71c.H
    left
    exact ⟨1, 1, 0, 0, by simp [hw0], by simp [hw1], by simp [hw2], by simp [hw3]⟩
  have hwN : Quaternion.normSq w = 2 := by
    rw [Quaternion.normSq_def', hw0, hw1, hw2, hw3]
    norm_num
  have hw0' : w ≠ 0 := by
    intro h
    rw [h] at hwN
    simp at hwN
  have inj : Function.Injective (fun z : Quaternion ℚ => z * w) :=
    fun a b h => mul_right_cancel₀ hw0' h
  have himg : (fun z : Quaternion ℚ => z * w) '' Hn m = Hn (2 * m) := by
    ext y
    constructor
    · rintro ⟨z, ⟨hz, hzn⟩, rfl⟩
      refine ⟨QH_mul hz hwQH, ?_⟩
      show Quaternion.normSq (z * w) = ((2 * m : ℕ) : ℚ)
      rw [map_mul, hzn, hwN]
      push_cast
      ring
    · rintro ⟨hy, hyn⟩
      have hyn' : Quaternion.normSq y = 2 * (m : ℚ) := by
        rw [hyn]
        push_cast
        ring
      obtain ⟨a, b, c, d, ya, yb, yc, yd⟩ := int_coords y hy m hyn'
      obtain ⟨z, z0, z1, z2, z3⟩ := exq ((y.re + y.imI) / 2) ((y.imI - y.re) / 2)
        ((y.imJ - y.imK) / 2) ((y.imJ + y.imK) / 2)
      have hzw : z * w = y := by
        obtain ⟨p0, p1, p2, p3⟩ := Section73b.mul_comp z w
        first
        | refine Quaternion.ext _ _ ?_ ?_ ?_ ?_
        | refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_
        · rw [p0, hw0, hw1, hw2, hw3, z0, z1, z2, z3]; ring
        · rw [p1, hw0, hw1, hw2, hw3, z0, z1, z2, z3]; ring
        · rw [p2, hw0, hw1, hw2, hw3, z0, z1, z2, z3]; ring
        · rw [p3, hw0, hw1, hw2, hw3, z0, z1, z2, z3]; ring
      have hzn : Quaternion.normSq z = (m : ℚ) := by
        have h := congrArg Quaternion.normSq hzw
        rw [map_mul, hwN, hyn'] at h
        linarith
      refine ⟨z, ⟨?_, hzn⟩, hzw⟩
      have hS : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 2 * (m : ℤ) := by
        have : (a : ℚ) ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 2 * m := by
          rw [← hyn', Quaternion.normSq_def', ya, yb, yc, yd]
        exact_mod_cast this
      obtain ⟨ka, ea⟩ := ev_sq a
      obtain ⟨kb, eb⟩ := ev_sq b
      obtain ⟨kc, ec⟩ := ev_sq c
      obtain ⟨kd, ed⟩ := ev_sq d
      unfold QH Section71c.H
      rcases Int.even_or_odd' (a + b) with ⟨k, hk | hk⟩
      · have hcd : (c + d) % 2 = 0 := by omega
        obtain ⟨l, hl⟩ : ∃ l : ℤ, c + d = 2 * l := ⟨(c + d) / 2, by omega⟩
        have hk' : (a : ℚ) + b = 2 * k := by exact_mod_cast hk
        have hl' : (c : ℚ) + d = 2 * l := by exact_mod_cast hl
        left
        refine ⟨k, k - a, l - d, l, ?_, ?_, ?_, ?_⟩
        · rw [z0, ya, yb]; linarith
        · rw [z1, ya, yb]; push_cast; linarith
        · rw [z2, yc, yd]; push_cast; linarith
        · rw [z3, yc, yd]; linarith
      · have hcd : (c + d) % 2 = 1 := by omega
        obtain ⟨l, hl⟩ : ∃ l : ℤ, c + d = 2 * l + 1 := ⟨(c + d) / 2, by omega⟩
        have hk' : (a : ℚ) + b = 2 * k + 1 := by exact_mod_cast hk
        have hl' : (c : ℚ) + d = 2 * l + 1 := by exact_mod_cast hl
        right
        refine ⟨k, k - a, l - d, l, ?_, ?_, ?_, ?_⟩
        · rw [z0, ya, yb]; linarith
        · rw [z1, ya, yb]; push_cast; linarith
        · rw [z2, yc, yd]; push_cast; linarith
        · rw [z3, yc, yd]; linarith
  rw [← himg, Set.ncard_image_of_injective _ inj]

end Section75a

namespace Section77a
open Section71d

/-! Stage77a (UNTESTED when written).  PROVES, if it compiles: for every natural n the set Hn n of Hurwitz quaternions of
norm n is finite.  Hand derivation: for x in Hn n put a_i = 2 * (coordinate i), integers (coord_int) with
a0^2+a1^2+a2^2+a3^2 = 4n, so |a_i| <= 4n; the map x -> (a_i) is injective into a finite box.
DOES NOT PROVE: any count of Hn n. -/

theorem bnd_up (a : ℤ) (n : ℕ) (h : a ^ 2 ≤ 4 * (n : ℤ)) : a ≤ 4 * (n : ℤ) := by
  by_contra h'
  push_neg at h'
  have h1 : 4 * (n : ℤ) + 1 ≤ a := h'
  have hn0 : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (by linarith : (0 : ℤ) ≤ a + (4 * n + 1))]

theorem bnd (a : ℤ) (n : ℕ) (h : a ^ 2 ≤ 4 * (n : ℤ)) : -(4 * (n : ℤ)) ≤ a ∧ a ≤ 4 * (n : ℤ) := by
  refine ⟨?_, bnd_up a n h⟩
  have := bnd_up (-a) n (by simpa using h)
  linarith

theorem repr {n : ℕ} {x : Quaternion ℚ} (hx : x ∈ Section75a.Hn n) :
    ∃ a0 a1 a2 a3 : ℤ, 2 * x.re = a0 ∧ 2 * x.imI = a1 ∧ 2 * x.imJ = a2 ∧ 2 * x.imK = a3 ∧
      a0 ^ 2 + a1 ^ 2 + a2 ^ 2 + a3 ^ 2 = 4 * (n : ℤ) := by
  obtain ⟨hxH, hxn⟩ := hx
  obtain ⟨a0, a1, a2, a3, e0, e1, e2, e3⟩ := Section74b.coord_int hxH
  refine ⟨a0, a1, a2, a3, e0, e1, e2, e3, ?_⟩
  have hs : (a0 : ℚ) ^ 2 + a1 ^ 2 + a2 ^ 2 + a3 ^ 2 = 4 * n := by
    rw [← e0, ← e1, ← e2, ← e3, ← hxn, Quaternion.normSq_def']
    ring
  exact_mod_cast hs

theorem Hn_finite (n : ℕ) : (Section75a.Hn n).Finite := by
  classical
  let f : Quaternion ℚ → (Fin 4 → ℤ) := fun x i => ⌊(2 : ℚ) * ![x.re, x.imI, x.imJ, x.imK] i⌋
  have hf : ∀ x ∈ Section75a.Hn n, ∃ a0 a1 a2 a3 : ℤ, f x = ![a0, a1, a2, a3] ∧
      2 * x.re = a0 ∧ 2 * x.imI = a1 ∧ 2 * x.imJ = a2 ∧ 2 * x.imK = a3 ∧
      a0 ^ 2 + a1 ^ 2 + a2 ^ 2 + a3 ^ 2 = 4 * (n : ℤ) := by
    intro x hx
    obtain ⟨a0, a1, a2, a3, e0, e1, e2, e3, hs⟩ := repr hx
    refine ⟨a0, a1, a2, a3, ?_, e0, e1, e2, e3, hs⟩
    funext i
    fin_cases i <;> simp [f, e0, e1, e2, e3]
  refine Set.Finite.of_injOn (f := f)
    (t := Set.pi Set.univ (fun _ : Fin 4 => Set.Icc (-(4 * (n : ℤ))) (4 * (n : ℤ)))) ?_ ?_
    (Set.Finite.pi (fun _ => Set.finite_Icc _ _))
  · intro x hx
    obtain ⟨a0, a1, a2, a3, hfx, -, -, -, -, hs⟩ := hf x hx
    intro i _
    rw [hfx]
    have h0 := bnd a0 n (by nlinarith [sq_nonneg a1, sq_nonneg a2, sq_nonneg a3])
    have h1 := bnd a1 n (by nlinarith [sq_nonneg a0, sq_nonneg a2, sq_nonneg a3])
    have h2 := bnd a2 n (by nlinarith [sq_nonneg a1, sq_nonneg a0, sq_nonneg a3])
    have h3 := bnd a3 n (by nlinarith [sq_nonneg a1, sq_nonneg a2, sq_nonneg a0])
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  · intro x hx y hy hxy
    obtain ⟨a0, a1, a2, a3, hfx, e0, e1, e2, e3, -⟩ := hf x hx
    obtain ⟨b0, b1, b2, b3, hfy, g0, g1, g2, g3, -⟩ := hf y hy
    have hh : (![a0, a1, a2, a3] : Fin 4 → ℤ) = ![b0, b1, b2, b3] := by rw [← hfx, ← hfy]; exact hxy
    have k0 : a0 = b0 := congrFun hh 0
    have k1 : a1 = b1 := congrFun hh 1
    have k2 : a2 = b2 := congrFun hh 2
    have k3 : a3 = b3 := congrFun hh 3
    subst k0 k1 k2 k3
    refine Quaternion.ext _ _ ?_ ?_ ?_ ?_ <;> linarith

end Section77a

namespace Section78a
open Section71d

/-! Stage78a (UNTESTED when written).  Counting pieces for the Hurwitz recurrence.  Fix an odd prime p, xs ys with
xs^2+ys^2=-1 in ZMod p.  Notation: h(n) = (Hn n).ncard, the number of Hurwitz quaternions of norm n.
PROVES, if it compiles:
 * ncard_Ik_Hn: for each key k, the Hurwitz elements of norm p*m lying in Ik k number exactly h(m)
   (bijection b -> g*b with g the norm-p generator of Ik k from gen_exists);
 * count_pairs: (p+1) h(m) = h(p m) + p * #{x in Hn(p m) : red x = 0}   (double counting over keys, using Stage76b);
 * zero_count: #{x in Hn(p m) : red x = 0} = h(m/p) if p | m, else 0;
 * recur: (p+1) h(m) = h(p m) + (if p | m then p * h(m/p) else 0).
DOES NOT PROVE h(m) = 24 sigma(m): that needs h(1)=24 (units), the induction on prime factorisation, and the link to FourSq.R. -/

variable (p : ℕ) [Fact p.Prime]

theorem QH_int (a : ℤ) : QH ((a : ℚ) : Quaternion ℚ) := by
  unfold QH Section71c.H
  left
  exact ⟨a, 0, 0, 0, by simp, by simp, by simp, by simp⟩

theorem QH_smul_nat {z : Quaternion ℚ} (hz : QH z) : QH ((p : ℚ) • z) := by
  have : ((p : ℚ) • z) = (((p : ℤ) : ℚ) : Quaternion ℚ) * z := by
    refine Quaternion.ext _ _ ?_ ?_ ?_ ?_ <;>
      simp [Quaternion.mul_re, Quaternion.mul_imI, Quaternion.mul_imJ, Quaternion.mul_imK]
  rw [this]
  exact QH_mul (QH_int (p : ℤ)) hz

theorem normSq_smul_nat (z : Quaternion ℚ) :
    Quaternion.normSq ((p : ℚ) • z) = (p : ℚ) ^ 2 * Quaternion.normSq z := by
  rw [← Quaternion.coe_mul_eq_smul, map_mul, Quaternion.normSq_coe]

theorem p_ne_zero_Q : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero

theorem ncard_Ik_Hn (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)
    (k : Option (ZMod p)) (m : ℕ) :
    ({x | x ∈ Section75b.Ik p xs ys k ∧ Quaternion.normSq x = ((p * m : ℕ) : ℚ)} : Set (Quaternion ℚ)).ncard
      = (Section75a.Hn m).ncard := by
  obtain ⟨g, hgI, hgn, hgen⟩ := Section75b.gen_exists p h2 xs ys hxy k
  have hI := Section75b.Ik_ideal p h2 xs ys hxy k
  have hp := p_ne_zero_Q p
  have hg0 : g ≠ 0 := by
    intro h
    apply hp
    rw [← hgn, h]
    simp
  have himg : ({x | x ∈ Section75b.Ik p xs ys k ∧ Quaternion.normSq x = ((p * m : ℕ) : ℚ)} : Set (Quaternion ℚ))
      = (fun b => g * b) '' (Section75a.Hn m) := by
    ext x
    constructor
    · rintro ⟨hxI, hxn⟩
      obtain ⟨y, hy, rfl⟩ := hgen x hxI
      refine ⟨y, ⟨hy, ?_⟩, rfl⟩
      rw [map_mul, hgn] at hxn
      push_cast at hxn
      exact mul_left_cancel₀ hp hxn
    · rintro ⟨b, ⟨hb, hbn⟩, rfl⟩
      refine ⟨hI.mul_mem g hgI b hb, ?_⟩
      rw [map_mul, hgn, hbn]
      push_cast
      ring
  rw [himg]
  apply Set.ncard_image_of_injOn
  intro a _ b _ hab
  exact mul_left_cancel₀ hg0 hab

end Section78a

namespace Section78b
open Section71d

/-! Stage78b: the double count over keys (UNTESTED when written). -/

variable (p : ℕ) [Fact p.Prime]

theorem count_pairs (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1) (m : ℕ) :
    (p + 1) * (Section75a.Hn m).ncard = (Section75a.Hn (p * m)).ncard +
      p * ({x | x ∈ Section75a.Hn (p * m) ∧ Section74b.red p xs ys x = 0} : Set (Quaternion ℚ)).ncard := by
  classical
  set S : Finset (Quaternion ℚ) := (Section77a.Hn_finite (p * m)).toFinset with hSdef
  have hS : ∀ x, x ∈ S ↔ x ∈ Section75a.Hn (p * m) := fun x => Set.Finite.mem_toFinset _
  have hcard : ∀ T : Finset (Quaternion ℚ), (↑T : Set (Quaternion ℚ)).ncard = T.card := by
    intro T
    first | exact Set.ncard_coe_finset T | exact Set.ncard_coe_Finset T
  have hA : ∀ k : Option (ZMod p),
      (S.filter (fun x => x ∈ Section75b.Ik p xs ys k)).card = (Section75a.Hn m).ncard := by
    intro k
    rw [← Section78a.ncard_Ik_Hn p h2 xs ys hxy k m, ← hcard]
    congr 1
    ext x
    simp only [Finset.coe_filter, Set.mem_setOf_eq, hS]
    constructor
    · rintro ⟨⟨_, hn⟩, hk⟩
      exact ⟨hk, hn⟩
    · rintro ⟨hk, hn⟩
      exact ⟨⟨hk.1, hn⟩, hk⟩
  have hdiv : (((p * m : ℕ)) : ZMod p) = 0 := by
    simp
  have hB : ∀ x ∈ S, (Finset.univ.filter (fun k : Option (ZMod p) => x ∈ Section75b.Ik p xs ys k)).card =
      if Section74b.red p xs ys x = 0 then p + 1 else 1 := by
    intro x hx
    obtain ⟨hxH, hxn⟩ := (hS x).1 hx
    by_cases hz : Section74b.red p xs ys x = 0
    · rw [if_pos hz]
      have : Finset.univ.filter (fun k : Option (ZMod p) => x ∈ Section75b.Ik p xs ys k) = Finset.univ := by
        apply Finset.filter_true_of_mem
        intro k _
        exact Section76b.Ik_zero p xs ys hxH hz k
      rw [this, Finset.card_univ, Fintype.card_option, ZMod.card]
    · rw [if_neg hz]
      obtain ⟨k, hk, hku⟩ := Section76b.Ik_existsUnique p h2 xs ys hxy hxH (p * m) hxn hdiv hz
      rw [Finset.card_eq_one]
      refine ⟨k, ?_⟩
      ext k'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h => hku k' h, fun h => h ▸ hk⟩
  have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := S) (t := (Finset.univ : Finset (Option (ZMod p))))
    (fun x k => x ∈ Section75b.Ik p xs ys k)
  simp only [Finset.bipartiteAbove, Finset.bipartiteBelow] at hdc
  rw [Finset.sum_congr rfl hB] at hdc
  have hrhs : ∑ k : Option (ZMod p), (S.filter (fun x => x ∈ Section75b.Ik p xs ys k)).card
      = (p + 1) * (Section75a.Hn m).ncard := by
    rw [Finset.sum_congr rfl (fun k _ => hA k), Finset.sum_const, Finset.card_univ, Fintype.card_option,
      ZMod.card, smul_eq_mul]
  rw [hrhs] at hdc
  rw [Finset.sum_ite] at hdc
  simp only [Finset.sum_const, smul_eq_mul] at hdc
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card (s := S)
    (fun x => Section74b.red p xs ys x = 0)
  have e1 : (Section75a.Hn (p * m)).ncard = S.card := by
    rw [← hcard]
    congr 1
    exact (Set.Finite.coe_toFinset _).symm
  have e2 : ({x | x ∈ Section75a.Hn (p * m) ∧ Section74b.red p xs ys x = 0} : Set (Quaternion ℚ)).ncard
      = (S.filter (fun x => Section74b.red p xs ys x = 0)).card := by
    rw [← hcard]
    congr 1
    ext x
    simp [hS]
  rw [e1, e2]
  nlinarith [hdc, hsplit]

end Section78b

namespace Section78c
open Section71d

/-! Stage78c: elements of norm p*m with zero reduction are exactly p times elements of norm m/p (UNTESTED). -/

variable (p : ℕ) [Fact p.Prime]

theorem zero_red_form (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1) (m : ℕ)
    {x : Quaternion ℚ} (hx : x ∈ Section75a.Hn (p * m)) (hz : Section74b.red p xs ys x = 0) :
    ∃ y : Quaternion ℚ, QH y ∧ x = (p : ℚ) • y ∧ ∃ n' : ℕ, Quaternion.normSq y = (n' : ℚ) ∧ m = p * n' := by
  obtain ⟨hxH, hxn⟩ := hx
  obtain ⟨y, hy, rfl⟩ := Section74b.red_ker p h2 xs ys hxy hxH hz
  obtain ⟨n', hn'⟩ := Section73c.normSq_nat hy
  refine ⟨y, hy, rfl, n', hn', ?_⟩
  rw [Section78a.normSq_smul_nat, hn'] at hxn
  have hp := Section78a.p_ne_zero_Q p
  have : (p : ℚ) * (p * n') = (p : ℚ) * m := by
    push_cast at hxn
    linear_combination hxn
  have := mul_left_cancel₀ hp this
  exact_mod_cast this.symm

theorem zero_count (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1) (m : ℕ) :
    ({x | x ∈ Section75a.Hn (p * m) ∧ Section74b.red p xs ys x = 0} : Set (Quaternion ℚ)).ncard =
      if p ∣ m then (Section75a.Hn (m / p)).ncard else 0 := by
  have hp := Section78a.p_ne_zero_Q p
  by_cases hdv : p ∣ m
  · rw [if_pos hdv]
    obtain ⟨m', rfl⟩ := hdv
    have hpos : 0 < p := (Fact.out : p.Prime).pos
    have hdiv : p * m' / p = m' := Nat.mul_div_cancel_left m' hpos
    rw [hdiv]
    have himg : ({x | x ∈ Section75a.Hn (p * (p * m')) ∧ Section74b.red p xs ys x = 0} : Set (Quaternion ℚ))
        = (fun y => (p : ℚ) • y) '' (Section75a.Hn m') := by
      ext x
      constructor
      · intro hx
        obtain ⟨hx1, hx2⟩ := hx
        obtain ⟨y, hy, rfl, n', hn', hmn⟩ := zero_red_form p h2 xs ys hxy (p * m') hx1 hx2
        have : m' = n' := Nat.eq_of_mul_eq_mul_left hpos hmn
        subst this
        exact ⟨y, ⟨hy, hn'⟩, rfl⟩
      · rintro ⟨y, ⟨hy, hyn⟩, rfl⟩
        refine ⟨⟨Section78a.QH_smul_nat p hy, ?_⟩, Section75b.red_smul_p p xs ys hy⟩
        rw [Section78a.normSq_smul_nat, hyn]
        push_cast
        ring
    rw [himg]
    apply Set.ncard_image_of_injOn
    intro a _ b _ hab
    exact smul_right_injective (Quaternion ℚ) hp hab
  · rw [if_neg hdv]
    have : ({x | x ∈ Section75a.Hn (p * m) ∧ Section74b.red p xs ys x = 0} : Set (Quaternion ℚ)) = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hx1, hx2⟩
      obtain ⟨y, hy, rfl, n', hn', hmn⟩ := zero_red_form p h2 xs ys hxy m hx1 hx2
      exact hdv ⟨n', hmn⟩
    rw [this]
    simp

theorem recur (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1) (m : ℕ) :
    (p + 1) * (Section75a.Hn m).ncard = (Section75a.Hn (p * m)).ncard +
      (if p ∣ m then p * (Section75a.Hn (m / p)).ncard else 0) := by
  rw [Section78b.count_pairs p h2 xs ys hxy m, zero_count p h2 xs ys hxy m]
  split_ifs <;> simp

end Section78c

#print axioms Section78a.ncard_Ik_Hn
#print axioms Section78b.count_pairs
#print axioms Section78c.zero_count
#print axioms Section78c.recur

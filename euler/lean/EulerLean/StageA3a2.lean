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

#print axioms Section74c.psi_surj
#print axioms Section74c.red_surj
#print axioms Section74c.det_red

/-! # StageA1 (layer A for H31gt3): conjugation and invertibility of the reduction map (UNTESTED when written)

Everything above this block is Stage74c.lean unchanged (compiled in an earlier run). Only the section below is new.

WHAT THIS SECTION PROVES, if it compiles.  Let p be a prime with 2 ≠ 0 in ZMod p, xs, ys with xs^2 + ys^2 = -1, and
red the reduction map of Section74b.  For a Hurwitz quaternion x (QH x) of norm n:
 * psi_conj: psi(a,-b,-c,-d) is the adjugate of psi(a,b,c,d), over any commutative ring;
 * red_star: red (star x) = adjugate (red x);
 * red_star_mul: red (star x) * red x = n • 1, a scalar matrix;
 * red_isUnit: if p does not divide n, red x is an invertible matrix.
Hand derivation.  adjugate [[m00, m01], [m10, m11]] = [[m11, -m01], [-m10, m00]].  With
psi(a,b,c,d) = [[a + c x - d y, -b + c y + d x], [b + c y + d x, a - c x + d y]] the adjugate is
[[a - c x + d y, b - c y - d x], [-b - c y - d x, a + c x - d y]] = psi(a,-b,-c,-d).  Conjugation keeps re and negates
imI, imJ, imK; cz commutes with negation when 2q is an integer, which holds for Hurwitz coordinates (coord_int).
adjugate A * A = det A • 1 (Mathlib) and det (red x) = n (Section74c.det_red).  In PGL2 this says red(star x) is the
inverse of red x, which is what the self-adjointness of T_m uses later.

DOES NOT PROVE: anything about PGL2 as a quotient group, the operator T_m, Y_p, O_p, the torus, the factor 8 or
constancy.  Those are stages A2-A4.  Nothing here is about H31gt3 itself. -/

namespace SectionA1
open Section71d

theorem psi_conj {K : Type*} [CommRing K] (x y a b c d : K) :
    Section74a.psi x y a (-b) (-c) (-d) = (Section74a.psi x y a b c d).adjugate := by
  rw [Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Section74a.psi] <;> ring

variable (p : ℕ) [Fact p.Prime]

theorem cz_neg (q : ℚ) (z : ℤ) (h : 2 * q = (z : ℚ)) :
    Section74b.cz p (-q) = - Section74b.cz p q := by
  rw [Section74b.cz_eq p (-q) (-z) (by push_cast; linarith), Section74b.cz_eq p q z h]
  push_cast
  ring

theorem red_star (xs ys : ZMod p) {x : Quaternion ℚ} (hx : QH x) :
    Section74b.red p xs ys (star x) = (Section74b.red p xs ys x).adjugate := by
  obtain ⟨a0, a1, a2, a3, ha0, ha1, ha2, ha3⟩ := Section74b.coord_int hx
  have s0 : (star x).re = x.re := by first | rfl | simp
  have s1 : (star x).imI = -x.imI := by first | rfl | simp
  have s2 : (star x).imJ = -x.imJ := by first | rfl | simp
  have s3 : (star x).imK = -x.imK := by first | rfl | simp
  unfold Section74b.red
  rw [s0, s1, s2, s3, cz_neg p _ a1 ha1, cz_neg p _ a2 ha2, cz_neg p _ a3 ha3]
  exact psi_conj _ _ _ _ _ _

theorem red_star_mul (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)
    {x : Quaternion ℚ} (hx : QH x) (n : ℕ) (hn : Quaternion.normSq x = (n : ℚ)) :
    Section74b.red p xs ys (star x) * Section74b.red p xs ys x
      = (n : ZMod p) • (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
  rw [red_star p xs ys hx, Matrix.adjugate_mul, Section74c.det_red p h2 xs ys hxy hx n hn]

theorem red_isUnit (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)
    {x : Quaternion ℚ} (hx : QH x) (n : ℕ) (hn : Quaternion.normSq x = (n : ℚ)) (hpn : ¬ p ∣ n) :
    IsUnit (Section74b.red p xs ys x) := by
  rw [Matrix.isUnit_iff_isUnit_det, Section74c.det_red p h2 xs ys hxy hx n hn]
  apply isUnit_iff_ne_zero.mpr
  intro h0
  first
  | exact hpn ((ZMod.natCast_eq_zero_iff n p).mp h0)
  | exact hpn ((ZMod.natCast_zmod_eq_zero_iff_dvd n p).mp h0)

end SectionA1

#print axioms SectionA1.psi_conj
#print axioms SectionA1.cz_neg
#print axioms SectionA1.red_star
#print axioms SectionA1.red_star_mul
#print axioms SectionA1.red_isUnit

/-! # StageA2 (layer A for H31gt3): the projective inverse identity (UNTESTED when written)

Everything above this block is StageA1.lean unchanged (compiled green in Actions run 44451078572, commit 6ad51f10).
Only the section below is new.

WHAT THIS SECTION PROVES, if it compiles.  With the hypotheses of `SectionA1.red_isUnit` (p prime, 2 ≠ 0 in ZMod p,
xs^2 + ys^2 = -1, x Hurwitz of norm n, p ∤ n): let U(x) be red x as a unit of 2x2 matrices over ZMod p, and let
PGL2 p := (2x2 units) ⧸ center.  Then
   [U(star x)] * [U(x)] = 1   in PGL2 p,
because U(star x) * U(x) = (n : ZMod p) • 1 (SectionA1.red_star_mul) is a scalar matrix, hence central.
Hand derivation: scalar matrices commute with every matrix, so the unit with value c • 1 lies in the center; the
quotient map kills the center.  Here n is invertible mod p only because p ∤ n (red_isUnit), so U(x) exists.

DOES NOT PROVE: that PGL2 p here equals Mathlib's or the paper's G_p in any other presentation (it is defined as
units ⧸ center, which for ZMod p, 2x2, is the usual PGL2(F_p) but that identification is not proved here); the group
Gamma_p, the quotient Y_p, the operator T_m, or anything about H31gt3.  It is the algebraic input for the
self-adjointness step (rho(conj alpha) = rho(alpha)^{-1}) only. -/

namespace SectionA2
open Section71d

variable (p : ℕ) [Fact p.Prime]

/-- PGL2 over F_p presented as units of 2x2 matrices modulo the center. -/
abbrev PGL2 : Type :=
  (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ ⧸ Subgroup.center (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ

/-- The reduction of a Hurwitz quaternion prime to p, as a unit. -/
noncomputable def redUnit (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)
    {x : Quaternion ℚ} (hx : QH x) (n : ℕ) (hn : Quaternion.normSq x = (n : ℚ)) (hpn : ¬ p ∣ n) :
    (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ :=
  (SectionA1.red_isUnit p h2 xs ys hxy hx n hn hpn).unit

theorem redUnit_coe (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)
    {x : Quaternion ℚ} (hx : QH x) (n : ℕ) (hn : Quaternion.normSq x = (n : ℚ)) (hpn : ¬ p ∣ n) :
    ((redUnit p h2 xs ys hxy hx n hn hpn : (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ) :
      Matrix (Fin 2) (Fin 2) (ZMod p)) = Section74b.red p xs ys x :=
  IsUnit.unit_spec _

theorem star_mul_central (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)
    {x : Quaternion ℚ} (hx : QH x) (n : ℕ) (hn : Quaternion.normSq x = (n : ℚ)) (hpn : ¬ p ∣ n) :
    redUnit p h2 xs ys hxy (Section73a.QH_star hx) n
        (by rw [Section73a.normSq_star']; exact hn) hpn
      * redUnit p h2 xs ys hxy hx n hn hpn
      ∈ Subgroup.center (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ := by
  rw [Subgroup.mem_center_iff]
  intro g
  have key : ((redUnit p h2 xs ys hxy (Section73a.QH_star hx) n
        (by rw [Section73a.normSq_star']; exact hn) hpn : (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ) :
        Matrix (Fin 2) (Fin 2) (ZMod p)) *
      ((redUnit p h2 xs ys hxy hx n hn hpn : (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ) :
        Matrix (Fin 2) (Fin 2) (ZMod p))
      = (n : ZMod p) • (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
    rw [redUnit_coe, redUnit_coe]
    exact SectionA1.red_star_mul p h2 xs ys hxy hx n hn
  apply Units.ext
  simp only [Units.val_mul]
  rw [key]
  simp [Matrix.mul_smul, Matrix.smul_mul]

/-- In PGL2(F_p): [red (star x)] * [red x] = 1, i.e. rho(conj x) = rho(x)^{-1}. -/
theorem pgl_star_mul_eq_one (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)
    {x : Quaternion ℚ} (hx : QH x) (n : ℕ) (hn : Quaternion.normSq x = (n : ℚ)) (hpn : ¬ p ∣ n) :
    (QuotientGroup.mk (redUnit p h2 xs ys hxy (Section73a.QH_star hx) n
        (by rw [Section73a.normSq_star']; exact hn) hpn) : PGL2 p)
      * (QuotientGroup.mk (redUnit p h2 xs ys hxy hx n hn hpn) : PGL2 p) = 1 := by
  rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
  exact star_mul_central p h2 xs ys hxy hx n hn hpn

end SectionA2

#print axioms SectionA2.redUnit_coe
#print axioms SectionA2.star_mul_central
#print axioms SectionA2.pgl_star_mul_eq_one

/-! # StageA3a (layer A for H31gt3): the kernel of the projective reduction on Hurwitz units (UNTESTED when written)

Everything above this block is StageA2.lean unchanged (compiled green in Actions run 44477338706, commit dd96675).
Only the section below is new.

WHAT THIS SECTION PROVES, if it compiles.  Let p be a prime with 2 ≠ 0 in ZMod p (so p is odd), xs^2 + ys^2 = -1,
and u a Hurwitz quaternion (QH u) of norm 1.  Let rho(u) = [red u] in PGL2 p (A2's quotient of units by the center).
 * `kernel_iff`:  rho(u) = 1  <->  u = 1 or u = -1.
Hand derivation.  (<-) red 1 = 1 and red (-1) = (-1) • 1 are scalar matrices, hence central.  (->) a unit commuting
with the transvections [[1,1],[0,1]] and [[1,0],[1,1]] is scalar; for psi(a,b,c,d) that forces b = 0, c y + d x = 0,
c x - d y = 0, hence c = d = 0 because x^2 + y^2 = -1.  Now c = cz(imJ) = (2 imJ) / 2 with 2 imJ an integer z, so
p | z.  Norm 1 gives z0^2 + z1^2 + z2^2 + z3^2 = 4, so |z| <= 2 < 3 <= p, hence z = 0.  So imI = imJ = imK = 0 and
re^2 = 1.

DOES NOT PROVE: that rho is a group homomorphism on the unit group, that there are exactly 24 Hurwitz units, or that
the image has order 12.  Those are A3a-ii.  Nothing here is about Y_p, T_m or H31gt3. -/

namespace SectionA3a
open Section71d

variable (p : ℕ) [Fact p.Prime]

theorem not_dvd_one_p : ¬ p ∣ 1 := fun h => (Fact.out : p.Prime).ne_one (Nat.dvd_one.mp h)

theorem three_le_p (h2 : (2 : ZMod p) ≠ 0) : (3 : ℤ) ≤ (p : ℤ) := by
  have h2le : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hne : p ≠ 2 := by
    intro h
    have e : ((2 : ℕ) : ZMod p) = 0 :=
      (congrArg (Nat.cast : ℕ → ZMod p) h).symm.trans (ZMod.natCast_self p)
    exact h2 (by simpa using e)
  have : 3 ≤ p := by omega
  exact_mod_cast this

theorem int_zero_of_dvd_sq (h3 : (3 : ℤ) ≤ (p : ℤ)) (x : ℤ) (hx : x ^ 2 ≤ 4) (hd : (p : ℤ) ∣ x) : x = 0 := by
  apply Int.eq_zero_of_abs_lt_dvd hd
  apply abs_lt_of_sq_lt_sq _ (by positivity)
  nlinarith

/-- A scalar matrix, as a unit, is central. -/
theorem central_of_scalar (z : (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ) (c : ZMod p)
    (h : (z : Matrix (Fin 2) (Fin 2) (ZMod p)) = c • (1 : Matrix (Fin 2) (Fin 2) (ZMod p))) :
    z ∈ Subgroup.center (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Units.ext
  simp only [Units.val_mul]
  rw [h]
  simp [Matrix.mul_smul, Matrix.smul_mul]

/-- The transvection [[1,1],[0,1]] as a unit. -/
def tU : (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ :=
  ⟨!![1, 1; 0, 1], !![1, -1; 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

/-- The transvection [[1,0],[1,1]] as a unit. -/
def lU : (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ :=
  ⟨!![1, 0; 1, 1], !![1, 0; -1, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

/-- A central unit of the form psi(a,b,c,d) has b = c = d = 0. -/
theorem central_coords (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)
    (M : (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ) (a b c d : ZMod p)
    (hM : (M : Matrix (Fin 2) (Fin 2) (ZMod p)) = Section74a.psi xs ys a b c d)
    (hc : M ∈ Subgroup.center (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ) :
    b = 0 ∧ c = 0 ∧ d = 0 := by
  have ht := congrArg Units.val (Subgroup.mem_center_iff.mp hc (tU p))
  have hl := congrArg Units.val (Subgroup.mem_center_iff.mp hc (lU p))
  simp only [Units.val_mul] at ht hl
  rw [hM] at ht hl
  have t00 := congrFun (congrFun ht 0) 0
  have t01 := congrFun (congrFun ht 0) 1
  have l00 := congrFun (congrFun hl 0) 0
  simp [tU, lU, Matrix.mul_apply, Fin.sum_univ_two, Section74a.psi] at t00 t01 l00
  have e10 : b + c * ys + d * xs = 0 := by
    first | linear_combination t00 | linear_combination (-1 : ZMod p) * t00
  have e11 : c * xs - d * ys = 0 := by
    have : (2 : ZMod p) * (c * xs - d * ys) = 0 := by
      first | linear_combination t01 | linear_combination (-1 : ZMod p) * t01
    exact (mul_eq_zero.mp this).resolve_left h2
  have e01 : -b + c * ys + d * xs = 0 := by
    first | linear_combination l00 | linear_combination (-1 : ZMod p) * l00
  have hb : b = 0 := by
    have : (2 : ZMod p) * b = 0 := by linear_combination e10 - e01
    exact (mul_eq_zero.mp this).resolve_left h2
  have hv : c * ys + d * xs = 0 := by linear_combination e10 - hb
  have hcc : c = 0 := by linear_combination (-1 : ZMod p) * (xs * e11 + ys * hv) + c * hxy
  have hdd : d = 0 := by linear_combination (-1 : ZMod p) * (xs * hv - ys * e11) + d * hxy
  exact ⟨hb, hcc, hdd⟩

theorem cz_zero (h2 : (2 : ZMod p) ≠ 0) : Section74b.cz p 0 = 0 := by
  rw [Section74b.cz_eq p 0 0 (by norm_num)]
  simp

theorem cz_negone (h2 : (2 : ZMod p) ≠ 0) : Section74b.cz p (-1) = -1 := by
  rw [Section74b.cz_eq p (-1) (-2) (by norm_num)]
  push_cast
  have h : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ h2
  linear_combination (-1 : ZMod p) * h

theorem red_negone (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) :
    Section74b.red p xs ys (-1) = (-1 : ZMod p) • (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
  unfold Section74b.red
  have e0 : (-1 : Quaternion ℚ).re = -1 := by first | rfl | simp
  have e1 : (-1 : Quaternion ℚ).imI = 0 := by first | rfl | simp
  have e2 : (-1 : Quaternion ℚ).imJ = 0 := by first | rfl | simp
  have e3 : (-1 : Quaternion ℚ).imK = 0 := by first | rfl | simp
  rw [e0, e1, e2, e3, cz_negone p h2, cz_zero p h2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Section74a.psi]

theorem kernel_iff (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)
    {u : Quaternion ℚ} (hu : QH u) (hn : Quaternion.normSq u = 1) :
    (QuotientGroup.mk (SectionA2.redUnit p h2 xs ys hxy hu 1 (by rw [hn]; norm_num)
        (not_dvd_one_p p)) : SectionA2.PGL2 p) = 1 ↔ u = 1 ∨ u = -1 := by
  constructor
  · intro h
    rw [QuotientGroup.eq_one_iff] at h
    have hM : ((SectionA2.redUnit p h2 xs ys hxy hu 1 (by rw [hn]; norm_num) (not_dvd_one_p p) :
          (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ) : Matrix (Fin 2) (Fin 2) (ZMod p))
        = Section74a.psi xs ys (Section74b.cz p u.re) (Section74b.cz p u.imI)
            (Section74b.cz p u.imJ) (Section74b.cz p u.imK) := by
      rw [SectionA2.redUnit_coe]; rfl
    obtain ⟨hb, hc, hd⟩ := central_coords p h2 xs ys hxy _ _ _ _ _ hM h
    obtain ⟨a0, a1, a2, a3, ha0, ha1, ha2, ha3⟩ := Section74b.coord_int hu
    have hq : u.re ^ 2 + u.imI ^ 2 + u.imJ ^ 2 + u.imK ^ 2 = 1 := by
      rw [← Quaternion.normSq_def']; exact hn
    have hQ : ((a0 : ℚ) ^ 2 + (a1 : ℚ) ^ 2 + (a2 : ℚ) ^ 2 + (a3 : ℚ) ^ 2) = 4 := by
      rw [← ha0, ← ha1, ← ha2, ← ha3]; nlinarith [hq]
    have hZ : a0 ^ 2 + a1 ^ 2 + a2 ^ 2 + a3 ^ 2 = 4 := by exact_mod_cast hQ
    have h3 := three_le_p p h2
    have dvd_of : ∀ (q : ℚ) (z : ℤ), 2 * q = (z : ℚ) → Section74b.cz p q = 0 → (p : ℤ) ∣ z := by
      intro q z hz hcz
      rw [Section74b.cz_eq p q z hz] at hcz
      have hz0 : (z : ZMod p) = 0 := (mul_eq_zero.mp hcz).resolve_right (inv_ne_zero h2)
      first
      | exact (ZMod.intCast_zmod_eq_zero_iff_dvd z p).mp hz0
      | exact (ZMod.intCast_eq_zero_iff_dvd z p).mp hz0
    have z1 : a1 = 0 := int_zero_of_dvd_sq p h3 a1 (by nlinarith [sq_nonneg a0, sq_nonneg a2, sq_nonneg a3])
      (dvd_of _ _ ha1 hb)
    have z2 : a2 = 0 := int_zero_of_dvd_sq p h3 a2 (by nlinarith [sq_nonneg a0, sq_nonneg a1, sq_nonneg a3])
      (dvd_of _ _ ha2 hc)
    have z3 : a3 = 0 := int_zero_of_dvd_sq p h3 a3 (by nlinarith [sq_nonneg a0, sq_nonneg a1, sq_nonneg a2])
      (dvd_of _ _ ha3 hd)
    have i1 : u.imI = 0 := by rw [z1] at ha1; push_cast at ha1; linarith
    have i2 : u.imJ = 0 := by rw [z2] at ha2; push_cast at ha2; linarith
    have i3 : u.imK = 0 := by rw [z3] at ha3; push_cast at ha3; linarith
    have hre : (u.re - 1) * (u.re + 1) = 0 := by rw [i1, i2, i3] at hq; nlinarith [hq]
    have o0 : (1 : Quaternion ℚ).re = 1 := by first | rfl | simp
    have o1 : (1 : Quaternion ℚ).imI = 0 := by first | rfl | simp
    have o2 : (1 : Quaternion ℚ).imJ = 0 := by first | rfl | simp
    have o3 : (1 : Quaternion ℚ).imK = 0 := by first | rfl | simp
    have n0 : (-1 : Quaternion ℚ).re = -1 := by first | rfl | simp
    have n1 : (-1 : Quaternion ℚ).imI = 0 := by first | rfl | simp
    have n2 : (-1 : Quaternion ℚ).imJ = 0 := by first | rfl | simp
    have n3 : (-1 : Quaternion ℚ).imK = 0 := by first | rfl | simp
    rcases mul_eq_zero.mp hre with h1 | h1
    · left
      first | refine Quaternion.ext _ _ ?_ ?_ ?_ ?_ | refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_
      · rw [o0]; linarith
      · rw [o1]; exact i1
      · rw [o2]; exact i2
      · rw [o3]; exact i3
    · right
      first | refine Quaternion.ext _ _ ?_ ?_ ?_ ?_ | refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_
      · rw [n0]; linarith
      · rw [n1]; exact i1
      · rw [n2]; exact i2
      · rw [n3]; exact i3
  · intro h
    rw [QuotientGroup.eq_one_iff]
    rcases h with rfl | rfl
    · apply central_of_scalar p _ 1
      rw [SectionA2.redUnit_coe, Section74b.red_one p h2 xs ys]
      simp
    · apply central_of_scalar p _ (-1)
      rw [SectionA2.redUnit_coe, red_negone p h2 xs ys]

end SectionA3a

#print axioms SectionA3a.central_coords
#print axioms SectionA3a.red_negone
#print axioms SectionA3a.kernel_iff

/-! # StageA3a2 (layer A for H31gt3): the Hurwitz unit group, the homomorphism to PGL2, kernel of size 2 (UNTESTED when written)

Everything above this block is StageA3a.lean unchanged (compiled green in Actions run 44557311038, commit 6cec1df).
Only the section below is new.

WHAT THIS SECTION PROVES, if it compiles.
 * `HurU`: the Hurwitz unit group as a Subgroup of (Quaternion Q)ˣ: units u with QH u and normSq u = 1.
 * `rho : HurU →* PGL2 p`, u ↦ [red u] (A2's quotient of 2x2 units by the center), for p with 2 ≠ 0 in ZMod p and
   xs^2 + ys^2 = -1.  It is a group homomorphism because red is multiplicative on Hurwitz quaternions (red_mul) and the
   quotient map is.
 * `rho_eq_one_iff`: rho u = 1 iff u = 1 or u = -1 (A3a's kernel_iff, restated for units).
 * `card_ker`: the kernel has exactly 2 elements.
 * `card_range_mul_two`: Nat.card (range rho) * 2 = Nat.card HurU.  (Index times order of the kernel.)
Hand derivation of the last two: ker rho = {1, -1}, and -1 ≠ 1.  For any hom f, |G / ker f| * |ker f| = |G| and
G / ker f ≃ range f.

DOES NOT PROVE: that Nat.card HurU = 24 (the unit count, next), hence NOT yet that the image has order 12.  Nothing
about Y_p, T_m or H31gt3. -/

namespace SectionA3a2
open Section71d

variable (p : ℕ) [Fact p.Prime]

/-- The Hurwitz unit group: units of Quaternion Q with Hurwitz coordinates and norm 1. -/
def HurU : Subgroup (Quaternion ℚ)ˣ where
  carrier := {u | QH (u : Quaternion ℚ) ∧ Quaternion.normSq (u : Quaternion ℚ) = 1}
  mul_mem' := by
    rintro a b ⟨ha, hna⟩ ⟨hb, hnb⟩
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]; exact QH_mul ha hb
    · rw [Units.val_mul, map_mul, hna, hnb, one_mul]
  one_mem' := ⟨Section73b.QH_one, by simp⟩
  inv_mem' := by
    rintro a ⟨ha, hna⟩
    obtain ⟨v, hv, hav, hva⟩ := Section73b.unit_inv (a : Quaternion ℚ) ha hna
    have h1 : ((a⁻¹ : (Quaternion ℚ)ˣ) : Quaternion ℚ) * ((a : Quaternion ℚ) * v)
        = (((a⁻¹ : (Quaternion ℚ)ˣ) : Quaternion ℚ) * (a : Quaternion ℚ)) * v := (mul_assoc _ _ _).symm
    rw [hav, mul_one, Units.inv_mul, one_mul] at h1
    have hnv : Quaternion.normSq v = 1 := by
      have := congrArg Quaternion.normSq hav
      rw [map_mul, hna, one_mul, map_one] at this
      exact this
    refine ⟨?_, ?_⟩
    · rw [h1]; exact hv
    · rw [h1]; exact hnv

theorem mem_iff (u : (Quaternion ℚ)ˣ) :
    u ∈ HurU ↔ QH (u : Quaternion ℚ) ∧ Quaternion.normSq (u : Quaternion ℚ) = 1 := Iff.rfl

variable (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)

/-- The class of the reduction of a Hurwitz unit in PGL2 (as a plain function). -/
noncomputable def rhoFun (u : HurU) : SectionA2.PGL2 p :=
  QuotientGroup.mk (SectionA2.redUnit p h2 xs ys hxy (mem_iff _ |>.mp u.2).1 1
    (by rw [(mem_iff _ |>.mp u.2).2]; norm_num) (SectionA3a.not_dvd_one_p p))

/-- rho : HurU →* PGL2 p. -/
noncomputable def rho : HurU →* SectionA2.PGL2 p where
  toFun := rhoFun p h2 xs ys hxy
  map_one' := by
    unfold rhoFun
    have hu : QH (((1 : HurU) : (Quaternion ℚ)ˣ) : Quaternion ℚ) := (mem_iff _ |>.mp (1 : HurU).2).1
    have hn : Quaternion.normSq (((1 : HurU) : (Quaternion ℚ)ˣ) : Quaternion ℚ) = 1 :=
      (mem_iff _ |>.mp (1 : HurU).2).2
    exact (SectionA3a.kernel_iff p h2 xs ys hxy hu hn).mpr (Or.inl (by simp))
  map_mul' := by
    intro x y
    unfold rhoFun
    rw [← QuotientGroup.mk_mul]
    congr 1
    apply Units.ext
    rw [Units.val_mul, SectionA2.redUnit_coe, SectionA2.redUnit_coe, SectionA2.redUnit_coe]
    have hx := (mem_iff _ |>.mp x.2).1
    have hy := (mem_iff _ |>.mp y.2).1
    simp only [Subgroup.coe_mul, Units.val_mul]
    exact Section74b.red_mul p h2 xs ys hxy hx hy

/-- The element -1 of HurU. -/
def negOne : HurU :=
  ⟨-1, by
    refine ⟨?_, ?_⟩
    · have h := Section71c.H_neg Section71c.H_one
      have e : QH (((-1 : (Quaternion ℚ)ˣ)) : Quaternion ℚ) := by
        unfold QH
        first
          | exact h
          | (simp only [Units.val_neg, Units.val_one]; exact h)
          | simpa using h
      exact e
    · simp⟩

theorem rho_eq_one_iff (u : HurU) :
    rho p h2 xs ys hxy u = 1 ↔ u = 1 ∨ u = negOne := by
  have hu := (mem_iff _ |>.mp u.2).1
  have hn := (mem_iff _ |>.mp u.2).2
  have key := SectionA3a.kernel_iff p h2 xs ys hxy hu hn
  change (rhoFun p h2 xs ys hxy u = 1) ↔ _
  unfold rhoFun
  rw [key]
  constructor
  · rintro (h | h)
    · left; apply Subtype.ext; apply Units.ext; simpa using h
    · right; apply Subtype.ext; apply Units.ext; simpa [negOne] using h
  · rintro (h | h)
    · left; have := congrArg (fun w : HurU => ((w : (Quaternion ℚ)ˣ) : Quaternion ℚ)) h; simpa using this
    · right; have := congrArg (fun w : HurU => ((w : (Quaternion ℚ)ˣ) : Quaternion ℚ)) h; simpa [negOne] using this

theorem negOne_ne_one : (negOne : HurU) ≠ 1 := by
  intro h
  have := congrArg (fun w : HurU => ((w : (Quaternion ℚ)ˣ) : Quaternion ℚ).re) h
  have h2 : ((((negOne : HurU) : (Quaternion ℚ)ˣ) : Quaternion ℚ)).re = -1 := rfl
  have h3 : ((((1 : HurU) : (Quaternion ℚ)ˣ) : Quaternion ℚ)).re = 1 := rfl
  have h4 : (-1 : ℚ) = 1 := h2.symm.trans (this.trans h3)
  norm_num at h4

theorem card_ker : Nat.card (rho p h2 xs ys hxy).ker = 2 := by
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨1, by simp⟩, ⟨negOne, (rho_eq_one_iff p h2 xs ys hxy negOne).mpr (Or.inr rfl)⟩, ?_, ?_⟩
  · intro h
    exact negOne_ne_one (congrArg Subtype.val h).symm
  · ext ⟨z, hz⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    have hz' : rho p h2 xs ys hxy z = 1 := hz
    rcases (rho_eq_one_iff p h2 xs ys hxy z).mp hz' with h | h
    · left; exact Subtype.ext h
    · right; exact Subtype.ext h

theorem card_range_mul_two :
    Nat.card (rho p h2 xs ys hxy).range * 2 = Nat.card HurU := by
  have h1 : Nat.card (HurU ⧸ (rho p h2 xs ys hxy).ker) = Nat.card (rho p h2 xs ys hxy).range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange (rho p h2 xs ys hxy)).toEquiv
  have h2' := Subgroup.index_mul_card (rho p h2 xs ys hxy).ker
  rw [Subgroup.index, card_ker p h2 xs ys hxy, h1] at h2'
  exact h2'

end SectionA3a2

#print axioms SectionA3a2.rho
#print axioms SectionA3a2.rho_eq_one_iff
#print axioms SectionA3a2.card_ker
#print axioms SectionA3a2.card_range_mul_two

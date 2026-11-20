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


/-! # StageA3a3 (layer A for H31gt3): |HurU| = 24 and the image of rho has order 12 (UNTESTED when written)

Everything above this block is StageA3a2.lean unchanged (compiled green in Actions run 44566755331, commit 52ec8dc).
Only the section below is new.

WHAT THIS SECTION PROVES, if it compiles.
 * `H_two`, `H_of_two`: Hurwitz coordinates (a,b,c,d) correspond exactly to integer vectors z = 2(a,b,c,d) whose
   entries have a common parity.
 * `zc`: the injective coordinate map HurU -> Z^4, u |-> (floor 2 re u, floor 2 imI u, floor 2 imJ u, floor 2 imK u).
   For u in HurU the entries are the doubled coordinates, have common parity, and sum of squares 4 (norm 1).
 * `zT`: HurU -> {z in Tset}, where Tset is the explicit finite set of z in [-2,2]^4 with sum of squares 4 and common
   parity.  `zT` is injective and surjective (surjective: every such z gives a Hurwitz quaternion of norm 1, invertible
   by Section73b.unit_inv).
 * `Tset_card`: Tset.card = 24, by kernel evaluation (`decide +kernel`, no native_decide).
 * `card_HurU`: Nat.card HurU = 24.
 * `card_range_twelve`: Nat.card (range rho) = 12, from A3a2's `card_range_mul_two`.

DOES NOT PROVE: anything about Y_p, T_m or H31gt3.  The action of Gamma_p and the quotient are A3b. -/

namespace SectionA3a3
open Section71d SectionA3a2

theorem H_two {a b c d : ℚ} (h : Section71c.H a b c d) :
    ∃ z0 z1 z2 z3 : ℤ, 2 * a = z0 ∧ 2 * b = z1 ∧ 2 * c = z2 ∧ 2 * d = z3 ∧
      (z0 - z1) % 2 = 0 ∧ (z0 - z2) % 2 = 0 ∧ (z0 - z3) % 2 = 0 := by
  rcases h with ⟨p, q, r, s, rfl, rfl, rfl, rfl⟩ | ⟨p, q, r, s, rfl, rfl, rfl, rfl⟩
  · refine ⟨2 * p, 2 * q, 2 * r, 2 * s, ?_, ?_, ?_, ?_, by omega, by omega, by omega⟩ <;>
      push_cast <;> ring
  · refine ⟨2 * p + 1, 2 * q + 1, 2 * r + 1, 2 * s + 1, ?_, ?_, ?_, ?_, by omega, by omega, by omega⟩ <;>
      push_cast <;> ring

theorem H_of_two (z0 z1 z2 z3 : ℤ) (h1 : (z0 - z1) % 2 = 0) (h2 : (z0 - z2) % 2 = 0)
    (h3 : (z0 - z3) % 2 = 0) :
    Section71c.H ((z0 : ℚ) / 2) ((z1 : ℚ) / 2) ((z2 : ℚ) / 2) ((z3 : ℚ) / 2) := by
  rcases Int.emod_two_eq_zero_or_one z0 with h | h
  · left
    obtain ⟨m0, hm0⟩ : ∃ m : ℤ, z0 = 2 * m := ⟨z0 / 2, by omega⟩
    obtain ⟨m1, hm1⟩ : ∃ m : ℤ, z1 = 2 * m := ⟨z1 / 2, by omega⟩
    obtain ⟨m2, hm2⟩ : ∃ m : ℤ, z2 = 2 * m := ⟨z2 / 2, by omega⟩
    obtain ⟨m3, hm3⟩ : ∃ m : ℤ, z3 = 2 * m := ⟨z3 / 2, by omega⟩
    refine ⟨m0, m1, m2, m3, ?_, ?_, ?_, ?_⟩
    · have : (z0 : ℚ) = 2 * m0 := by exact_mod_cast hm0
      linarith
    · have : (z1 : ℚ) = 2 * m1 := by exact_mod_cast hm1
      linarith
    · have : (z2 : ℚ) = 2 * m2 := by exact_mod_cast hm2
      linarith
    · have : (z3 : ℚ) = 2 * m3 := by exact_mod_cast hm3
      linarith
  · right
    obtain ⟨m0, hm0⟩ : ∃ m : ℤ, z0 = 2 * m + 1 := ⟨z0 / 2, by omega⟩
    obtain ⟨m1, hm1⟩ : ∃ m : ℤ, z1 = 2 * m + 1 := ⟨z1 / 2, by omega⟩
    obtain ⟨m2, hm2⟩ : ∃ m : ℤ, z2 = 2 * m + 1 := ⟨z2 / 2, by omega⟩
    obtain ⟨m3, hm3⟩ : ∃ m : ℤ, z3 = 2 * m + 1 := ⟨z3 / 2, by omega⟩
    refine ⟨m0, m1, m2, m3, ?_, ?_, ?_, ?_⟩
    · have : (z0 : ℚ) = 2 * m0 + 1 := by exact_mod_cast hm0
      linarith
    · have : (z1 : ℚ) = 2 * m1 + 1 := by exact_mod_cast hm1
      linarith
    · have : (z2 : ℚ) = 2 * m2 + 1 := by exact_mod_cast hm2
      linarith
    · have : (z3 : ℚ) = 2 * m3 + 1 := by exact_mod_cast hm3
      linarith

/-- the underlying quaternion of an element of HurU -/
abbrev qv (u : HurU) : Quaternion ℚ := ((u : (Quaternion ℚ)ˣ) : Quaternion ℚ)

theorem qv_QH (u : HurU) : QH (qv u) := (mem_iff _ |>.mp u.2).1

theorem qv_norm (u : HurU) : Quaternion.normSq (qv u) = 1 := (mem_iff _ |>.mp u.2).2

/-- doubled coordinates, as integers -/
def zc (u : HurU) : ℤ × ℤ × ℤ × ℤ :=
  (⌊2 * (qv u).re⌋, ⌊2 * (qv u).imI⌋, ⌊2 * (qv u).imJ⌋, ⌊2 * (qv u).imK⌋)

theorem zc_spec (u : HurU) :
    (((zc u).1 : ℤ) : ℚ) = 2 * (qv u).re ∧ (((zc u).2.1 : ℤ) : ℚ) = 2 * (qv u).imI ∧
    (((zc u).2.2.1 : ℤ) : ℚ) = 2 * (qv u).imJ ∧ (((zc u).2.2.2 : ℤ) : ℚ) = 2 * (qv u).imK ∧
    ((zc u).1 - (zc u).2.1) % 2 = 0 ∧ ((zc u).1 - (zc u).2.2.1) % 2 = 0 ∧
    ((zc u).1 - (zc u).2.2.2) % 2 = 0 := by
  obtain ⟨z0, z1, z2, z3, e0, e1, e2, e3, p1, p2, p3⟩ := H_two (qv_QH u)
  have f0 : ⌊2 * (qv u).re⌋ = z0 := by rw [e0]; exact Int.floor_intCast z0
  have f1 : ⌊2 * (qv u).imI⌋ = z1 := by rw [e1]; exact Int.floor_intCast z1
  have f2 : ⌊2 * (qv u).imJ⌋ = z2 := by rw [e2]; exact Int.floor_intCast z2
  have f3 : ⌊2 * (qv u).imK⌋ = z3 := by rw [e3]; exact Int.floor_intCast z3
  have hz : zc u = (z0, z1, z2, z3) := by simp only [zc, f0, f1, f2, f3]
  rw [hz]
  exact ⟨e0.symm, e1.symm, e2.symm, e3.symm, p1, p2, p3⟩

theorem zc_sumsq (u : HurU) :
    (zc u).1 ^ 2 + (zc u).2.1 ^ 2 + (zc u).2.2.1 ^ 2 + (zc u).2.2.2 ^ 2 = 4 := by
  obtain ⟨a0, a1, a2, a3, -, -, -⟩ := zc_spec u
  have hn := qv_norm u
  rw [Quaternion.normSq_def'] at hn
  have h : (((zc u).1 ^ 2 + (zc u).2.1 ^ 2 + (zc u).2.2.1 ^ 2 + (zc u).2.2.2 ^ 2 : ℤ) : ℚ) = 4 := by
    push_cast
    rw [a0, a1, a2, a3]
    linear_combination 4 * hn
  exact_mod_cast h

/-- the explicit finite set of doubled coordinates -/
noncomputable def Tset : Finset (ℤ × ℤ × ℤ × ℤ) :=
  ((Finset.Icc (-2 : ℤ) 2) ×ˢ (Finset.Icc (-2 : ℤ) 2) ×ˢ (Finset.Icc (-2 : ℤ) 2) ×ˢ
      (Finset.Icc (-2 : ℤ) 2)).filter
    (fun z => z.1 ^ 2 + z.2.1 ^ 2 + z.2.2.1 ^ 2 + z.2.2.2 ^ 2 = 4 ∧ (z.1 - z.2.1) % 2 = 0 ∧
      (z.1 - z.2.2.1) % 2 = 0 ∧ (z.1 - z.2.2.2) % 2 = 0)

theorem Tset_card : Tset.card = 24 := by
  first
    | decide +kernel
    | rfl

theorem bnd2 {a b c d : ℤ} (h : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 4) : -2 ≤ a ∧ a ≤ 2 := by
  constructor
  · by_contra hc
    push_neg at hc
    nlinarith [sq_nonneg b, sq_nonneg c, sq_nonneg d]
  · by_contra hc
    push_neg at hc
    nlinarith [sq_nonneg b, sq_nonneg c, sq_nonneg d]

theorem mem_Tset (z : ℤ × ℤ × ℤ × ℤ) :
    z ∈ Tset ↔ (z.1 ^ 2 + z.2.1 ^ 2 + z.2.2.1 ^ 2 + z.2.2.2 ^ 2 = 4 ∧ (z.1 - z.2.1) % 2 = 0 ∧
      (z.1 - z.2.2.1) % 2 = 0 ∧ (z.1 - z.2.2.2) % 2 = 0) := by
  obtain ⟨a, b, c, d⟩ := z
  simp only [Tset, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    have h0 : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 4 := h.1
    have hb : b ^ 2 + a ^ 2 + c ^ 2 + d ^ 2 = 4 := by linarith
    have hc : c ^ 2 + a ^ 2 + b ^ 2 + d ^ 2 = 4 := by linarith
    have hd : d ^ 2 + a ^ 2 + b ^ 2 + c ^ 2 = 4 := by linarith
    exact ⟨⟨bnd2 h0, bnd2 hb, bnd2 hc, bnd2 hd⟩, h⟩

noncomputable def zT (u : HurU) : {z // z ∈ Tset} :=
  ⟨zc u, (mem_Tset _).2 ⟨zc_sumsq u, (zc_spec u).2.2.2.2.1, (zc_spec u).2.2.2.2.2.1,
    (zc_spec u).2.2.2.2.2.2⟩⟩

theorem zT_inj : Function.Injective zT := by
  intro u v h
  have h' : zc u = zc v := congrArg Subtype.val h
  obtain ⟨a0, a1, a2, a3, -, -, -⟩ := zc_spec u
  obtain ⟨b0, b1, b2, b3, -, -, -⟩ := zc_spec v
  have e0 : (((zc u).1 : ℤ) : ℚ) = (((zc v).1 : ℤ) : ℚ) := by rw [h']
  have e1 : (((zc u).2.1 : ℤ) : ℚ) = (((zc v).2.1 : ℤ) : ℚ) := by rw [h']
  have e2 : (((zc u).2.2.1 : ℤ) : ℚ) = (((zc v).2.2.1 : ℤ) : ℚ) := by rw [h']
  have e3 : (((zc u).2.2.2 : ℤ) : ℚ) = (((zc v).2.2.2 : ℤ) : ℚ) := by rw [h']
  rw [a0, b0] at e0
  rw [a1, b1] at e1
  rw [a2, b2] at e2
  rw [a3, b3] at e3
  have g0 : (qv u).re = (qv v).re := by linarith
  have g1 : (qv u).imI = (qv v).imI := by linarith
  have g2 : (qv u).imJ = (qv v).imJ := by linarith
  have g3 : (qv u).imK = (qv v).imK := by linarith
  exact Subtype.ext (Units.ext (QuaternionAlgebra.ext g0 g1 g2 g3))

theorem zT_surj : Function.Surjective zT := by
  rintro ⟨⟨z0, z1, z2, z3⟩, hz⟩
  obtain ⟨hs, p1, p2, p3⟩ := (mem_Tset _).1 hz
  have hs' : z0 ^ 2 + z1 ^ 2 + z2 ^ 2 + z3 ^ 2 = 4 := hs
  have p1' : (z0 - z1) % 2 = 0 := p1
  have p2' : (z0 - z2) % 2 = 0 := p2
  have p3' : (z0 - z3) % 2 = 0 := p3
  have hH := H_of_two z0 z1 z2 z3 p1' p2' p3'
  have hqH : QH (QuaternionAlgebra.mk ((z0 : ℚ) / 2) ((z1 : ℚ) / 2) ((z2 : ℚ) / 2) ((z3 : ℚ) / 2) :
      Quaternion ℚ) := hH
  have hqn : Quaternion.normSq (QuaternionAlgebra.mk ((z0 : ℚ) / 2) ((z1 : ℚ) / 2) ((z2 : ℚ) / 2)
      ((z3 : ℚ) / 2) : Quaternion ℚ) = 1 := by
    rw [Quaternion.normSq_def']
    have h4 : ((z0 ^ 2 + z1 ^ 2 + z2 ^ 2 + z3 ^ 2 : ℤ) : ℚ) = 4 := by exact_mod_cast hs'
    push_cast at h4
    show ((z0 : ℚ) / 2) ^ 2 + ((z1 : ℚ) / 2) ^ 2 + ((z2 : ℚ) / 2) ^ 2 + ((z3 : ℚ) / 2) ^ 2 = 1
    linear_combination (1 / 4) * h4
  obtain ⟨v, hv, hqv, hvq⟩ := Section73b.unit_inv _ hqH hqn
  have f : ∀ x : ℤ, ⌊2 * ((x : ℚ) / 2)⌋ = x := fun x => by
    have : 2 * ((x : ℚ) / 2) = (x : ℚ) := by ring
    rw [this]
    exact Int.floor_intCast x
  refine ⟨⟨⟨_, v, hqv, hvq⟩, (mem_iff _).2 ⟨hqH, hqn⟩⟩, ?_⟩
  apply Subtype.ext
  exact Prod.ext (f z0) (Prod.ext (f z1) (Prod.ext (f z2) (f z3)))

theorem card_HurU : Nat.card HurU = 24 := by
  have hb : Function.Bijective zT := ⟨zT_inj, zT_surj⟩
  rw [Nat.card_eq_of_bijective zT hb, Nat.card_eq_fintype_card, Fintype.card_coe, Tset_card]

variable (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)

theorem card_range_twelve : Nat.card (rho p h2 xs ys hxy).range = 12 := by
  have h := card_range_mul_two p h2 xs ys hxy
  rw [card_HurU] at h
  omega

end SectionA3a3


/-! # StageA3b: Gamma_p in PGL2(F_p), freeness, |G_p| = 12 |Gamma_p \ G_p|
PROVES, if it compiles: Gam = image of HurU under rho has order 12; left translation is free; Y_p (right-coset
quotient) has the cardinality of the left-coset quotient; Nat.card (PGL2 p) = Nat.card Y_p * 12.
DOES NOT PROVE: a closed form for |PGL2 p|, functions on Y_p, the counting inner product, T_m, or H31gt3. -/

namespace SectionA3b

variable (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)

noncomputable def Gam : Subgroup (SectionA2.PGL2 p) :=
  (SectionA3a2.rho p h2 xs ys hxy).range

theorem card_Gam : Nat.card (Gam p h2 xs ys hxy) = 12 :=
  SectionA3a3.card_range_twelve p h2 xs ys hxy

theorem free_left (γ g : SectionA2.PGL2 p) (h : γ * g = g) : γ = 1 :=
  mul_right_cancel (h.trans (one_mul g).symm)

abbrev Yp : Type :=
  Quotient (QuotientGroup.rightRel (Gam p h2 xs ys hxy))

theorem card_Yp_eq :
    Nat.card (Yp p h2 xs ys hxy) = Nat.card (SectionA2.PGL2 p ⧸ Gam p h2 xs ys hxy) :=
  Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel (Gam p h2 xs ys hxy))

theorem card_PGL_eq_card_Yp_mul :
    Nat.card (SectionA2.PGL2 p) = Nat.card (Yp p h2 xs ys hxy) * 12 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Gam p h2 xs ys hxy)
  rw [card_Gam p h2 xs ys hxy, ← card_Yp_eq p h2 xs ys hxy] at h
  exact h

end SectionA3b


/-! # StageA3c: the constant 12 in sums over G_p of functions lifted from Y_p
Proves (if it compiles): for f on the orbit space Y_p = Gamma_p \ G_p, the sum over g in G_p of f(class of g)
equals 12 times the sum over Y_p of f; and the same for the complex counting inner product.
Does NOT prove: self-adjointness, T_m, the recurrence, or H31gt3. -/

namespace SectionA3c

theorem sum_lift_left_coset {G M : Type*} [Group G] [AddCommMonoid M] (H : Subgroup G)
    [Fintype G] [Fintype (G ⧸ H)] [Fintype H] (f : G ⧸ H → M) :
    ∑ g : G, f (g : G ⧸ H) = Fintype.card H • ∑ q : G ⧸ H, f q := by
  have e : ∑ g : G, f (g : G ⧸ H) = ∑ x : (G ⧸ H) × H, f x.1 :=
    Fintype.sum_equiv (Subgroup.groupEquivQuotientProdSubgroup (s := H)) _ _ (fun g => rfl)
  rw [e, Fintype.sum_prod_type]
  simp [Finset.sum_const, Finset.card_univ, Finset.smul_sum]

theorem sum_lift_right_coset {G M : Type*} [Group G] [AddCommMonoid M] (H : Subgroup G)
    [Fintype G] [Fintype (G ⧸ H)] [Fintype H] (f : Quotient (QuotientGroup.rightRel H) → M) :
    ∑ g : G, f (Quotient.mk (QuotientGroup.rightRel H) g)
      = Fintype.card H • ∑ y : Quotient (QuotientGroup.rightRel H), f y := by
  set e := QuotientGroup.quotientRightRelEquivQuotientLeftRel H with he
  have h1 : ∀ g : G, f (Quotient.mk (QuotientGroup.rightRel H) g)
      = (f ∘ e.symm) ((g⁻¹ : G) : G ⧸ H) := by
    intro g
    have hg : e (Quotient.mk (QuotientGroup.rightRel H) g) = ((g⁻¹ : G) : G ⧸ H) := rfl
    simp only [Function.comp]
    rw [← hg, Equiv.symm_apply_apply]
  calc ∑ g : G, f (Quotient.mk (QuotientGroup.rightRel H) g)
      = ∑ g : G, (f ∘ e.symm) ((g⁻¹ : G) : G ⧸ H) := Finset.sum_congr rfl (fun g _ => h1 g)
    _ = ∑ g : G, (f ∘ e.symm) (g : G ⧸ H) :=
        Fintype.sum_equiv (Equiv.inv G) _ _ (fun g => rfl)
    _ = Fintype.card H • ∑ q : G ⧸ H, (f ∘ e.symm) q := sum_lift_left_coset H _
    _ = Fintype.card H • ∑ y : Quotient (QuotientGroup.rightRel H), f y := by
        congr 1
        exact Equiv.sum_comp e.symm f

variable (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)

theorem sum_Yp {M : Type*} [AddCommMonoid M]
    [Fintype (SectionA2.PGL2 p)] [Fintype (SectionA2.PGL2 p ⧸ SectionA3b.Gam p h2 xs ys hxy)]
    [Fintype (SectionA3b.Gam p h2 xs ys hxy)] (f : SectionA3b.Yp p h2 xs ys hxy → M) :
    ∑ g : SectionA2.PGL2 p, f (Quotient.mk _ g) = 12 • ∑ y : SectionA3b.Yp p h2 xs ys hxy, f y := by
  have h := sum_lift_right_coset (SectionA3b.Gam p h2 xs ys hxy) f
  have hc : Fintype.card (SectionA3b.Gam p h2 xs ys hxy) = 12 := by
    rw [← Nat.card_eq_fintype_card]
    exact SectionA3b.card_Gam p h2 xs ys hxy
  rw [hc] at h
  exact h

theorem inner_Yp
    [Fintype (SectionA2.PGL2 p)] [Fintype (SectionA2.PGL2 p ⧸ SectionA3b.Gam p h2 xs ys hxy)]
    [Fintype (SectionA3b.Gam p h2 xs ys hxy)] (f g : SectionA3b.Yp p h2 xs ys hxy → ℂ) :
    ∑ x : SectionA2.PGL2 p, f (Quotient.mk _ x) * (starRingEnd ℂ) (g (Quotient.mk _ x))
      = 12 * ∑ y : SectionA3b.Yp p h2 xs ys hxy, f y * (starRingEnd ℂ) (g y) := by
  have h := sum_Yp p h2 xs ys hxy (fun y => f y * (starRingEnd ℂ) (g y))
  simpa [nsmul_eq_mul] using h

end SectionA3c


/-! # StageA4a: the operator T_a on functions on Y_p = Gamma_p \ G_p, and its self-adjointness (UNTESTED when written)

Everything above this block is StageA3c.lean unchanged (compiled green in Actions run 44621132526, commit c2206c8).
Only the section below is new.

WHAT THIS SECTION PROVES, if it compiles.  Let G be a finite group, Gamma a subgroup, iota a finite index type,
a : iota -> G, and sigma a permutation of iota with a (sigma i) = (a i)^-1.
 * `TG a F g = sum_i F (a i * g)` on functions F : G -> C, and `TG_adjoint`: the counting inner product on G is
   unchanged when T moves across (self-adjointness on G).  Proof: reindex g -> (a i)^-1 g, then sigma.
 * `TY Gamma a f y = sum_i f [a i * (representative of y)]` on functions on Y = right-coset quotient Gamma\G, and
   `TY_mk`: TY f [g] = sum_i f [a i * g] whenever the family is right-Gamma-stable up to left Gamma
   (hinv: for gamma in Gamma there is a permutation pi of iota and delta in Gamma with a (pi i) = delta * (a i * gamma)).
 * `TY_adjoint`: sum_y (TY f y) conj (h y) = sum_y f y conj (TY h y).  Proof: lift to G (StageA3c.sum_lift_right_coset,
   the constant is card Gamma, nonzero), apply TG_adjoint, cancel card Gamma.
 * `pgl_star_eq_inv`: for a Hurwitz x of norm n with p not dividing n, [red (star x)] = [red x]^-1 in PGL2 p.
   (A2's pgl_star_mul_eq_one rearranged.)  `TY_adjoint_Yp` is TY_adjoint for G = PGL2 p, Gamma = Gam.

DOES NOT PROVE: that the family a_alpha = [red alpha], alpha running over the Hurwitz elements of norm m (p not
dividing m), satisfies hinv (right multiplication by a Hurwitz unit permutes the set) or has a star-involution sigma
as an Equiv of a Fintype index (needs the finiteness of that set, Stage77a); the recurrence for T_m; any eigenvalue
bound; H31gt3.  Those are the next stage. -/

namespace SectionA4a

/-- The operator T_a on functions on a group G: (T F)(g) = sum over i of F(a i * g). -/
def TG {G ι : Type*} [Mul G] [Fintype ι] (a : ι → G) (F : G → ℂ) : G → ℂ :=
  fun g => ∑ i, F (a i * g)

theorem TG_adjoint {G ι : Type*} [Group G] [Fintype G] [Fintype ι] (a : ι → G) (σ : ι ≃ ι)
    (hσ : ∀ i, a (σ i) = (a i)⁻¹) (F H : G → ℂ) :
    ∑ g : G, TG a F g * (starRingEnd ℂ) (H g) = ∑ g : G, F g * (starRingEnd ℂ) (TG a H g) := by
  have h1 : ∀ i : ι, ∑ g : G, F (a i * g) * (starRingEnd ℂ) (H g)
      = ∑ g : G, F g * (starRingEnd ℂ) (H ((a i)⁻¹ * g)) := by
    intro i
    exact Fintype.sum_equiv (Equiv.mulLeft (a i)) _ _ (fun x => by simp)
  calc ∑ g : G, TG a F g * (starRingEnd ℂ) (H g)
      = ∑ i : ι, ∑ g : G, F (a i * g) * (starRingEnd ℂ) (H g) := by
        simp only [TG, Finset.sum_mul]; exact Finset.sum_comm
    _ = ∑ i : ι, ∑ g : G, F g * (starRingEnd ℂ) (H ((a i)⁻¹ * g)) :=
        Finset.sum_congr rfl (fun i _ => h1 i)
    _ = ∑ i : ι, ∑ g : G, F g * (starRingEnd ℂ) (H (a (σ i) * g)) := by simp only [hσ]
    _ = ∑ i : ι, ∑ g : G, F g * (starRingEnd ℂ) (H (a i * g)) :=
        Equiv.sum_comp σ (fun i => ∑ g : G, F g * (starRingEnd ℂ) (H (a i * g)))
    _ = ∑ g : G, F g * (starRingEnd ℂ) (TG a H g) := by
        simp only [TG, map_sum, Finset.mul_sum]; exact Finset.sum_comm

section Quot

variable {G ι : Type*} [Group G] (Γ : Subgroup G) [Fintype ι] (a : ι → G)

theorem mk_eq_of_eq_mul {g g' : G} (δ : G) (hδ : δ ∈ Γ) (h : g' = δ * g) :
    Quotient.mk (QuotientGroup.rightRel Γ) g' = Quotient.mk (QuotientGroup.rightRel Γ) g := by
  apply Quotient.sound
  apply QuotientGroup.rightRel_apply.2
  subst h
  have e : g * (δ * g)⁻¹ = δ⁻¹ := by group
  rw [e]
  exact Γ.inv_mem hδ

theorem out_mk (g : G) :
    ∃ γ ∈ Γ, (Quotient.mk (QuotientGroup.rightRel Γ) g).out = γ * g := by
  have h := Quotient.mk_out (s := QuotientGroup.rightRel Γ) g
  have h' := QuotientGroup.rightRel_apply.1 h
  refine ⟨(g * (Quotient.mk (QuotientGroup.rightRel Γ) g).out⁻¹)⁻¹, Γ.inv_mem h', ?_⟩
  group

/-- T_a on functions on Gamma \ G (right cosets Gamma g), computed through a representative. -/
noncomputable def TY (f : Quotient (QuotientGroup.rightRel Γ) → ℂ) :
    Quotient (QuotientGroup.rightRel Γ) → ℂ :=
  fun y => ∑ i, f (Quotient.mk (QuotientGroup.rightRel Γ) (a i * y.out))

theorem TY_mk (hinv : ∀ γ ∈ Γ, ∃ π : ι ≃ ι, ∀ i, ∃ δ ∈ Γ, a (π i) = δ * (a i * γ))
    (f : Quotient (QuotientGroup.rightRel Γ) → ℂ) (g : G) :
    TY Γ a f (Quotient.mk (QuotientGroup.rightRel Γ) g)
      = ∑ i, f (Quotient.mk (QuotientGroup.rightRel Γ) (a i * g)) := by
  obtain ⟨γ, hγ, ho⟩ := out_mk Γ g
  obtain ⟨π, hπ⟩ := hinv γ hγ
  unfold TY
  rw [ho]
  calc ∑ i, f (Quotient.mk (QuotientGroup.rightRel Γ) (a i * (γ * g)))
      = ∑ i, f (Quotient.mk (QuotientGroup.rightRel Γ) (a (π i) * g)) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        obtain ⟨δ, hδ, he⟩ := hπ i
        exact congrArg f (mk_eq_of_eq_mul Γ δ hδ (by rw [he]; group)).symm
    _ = ∑ i, f (Quotient.mk (QuotientGroup.rightRel Γ) (a i * g)) :=
        Equiv.sum_comp π (fun i => f (Quotient.mk (QuotientGroup.rightRel Γ) (a i * g)))

theorem TY_adjoint [Fintype G] [Fintype (G ⧸ Γ)] [Fintype Γ] (σ : ι ≃ ι)
    (hσ : ∀ i, a (σ i) = (a i)⁻¹)
    (hinv : ∀ γ ∈ Γ, ∃ π : ι ≃ ι, ∀ i, ∃ δ ∈ Γ, a (π i) = δ * (a i * γ))
    (f h : Quotient (QuotientGroup.rightRel Γ) → ℂ) :
    ∑ y : Quotient (QuotientGroup.rightRel Γ), TY Γ a f y * (starRingEnd ℂ) (h y)
      = ∑ y : Quotient (QuotientGroup.rightRel Γ), f y * (starRingEnd ℂ) (TY Γ a h y) := by
  have hL := SectionA3c.sum_lift_right_coset Γ
    (fun y => TY Γ a f y * (starRingEnd ℂ) (h y))
  have hR := SectionA3c.sum_lift_right_coset Γ
    (fun y => f y * (starRingEnd ℂ) (TY Γ a h y))
  have hG := TG_adjoint a σ hσ (fun g => f (Quotient.mk (QuotientGroup.rightRel Γ) g))
    (fun g => h (Quotient.mk (QuotientGroup.rightRel Γ) g))
  have e1 : ∑ g : G, TG a (fun g => f (Quotient.mk (QuotientGroup.rightRel Γ) g)) g
        * (starRingEnd ℂ) (h (Quotient.mk (QuotientGroup.rightRel Γ) g))
      = ∑ g : G, TY Γ a f (Quotient.mk (QuotientGroup.rightRel Γ) g)
        * (starRingEnd ℂ) (h (Quotient.mk (QuotientGroup.rightRel Γ) g)) := by
    refine Finset.sum_congr rfl (fun g _ => ?_)
    rw [TY_mk Γ a hinv f g]; rfl
  have e2 : ∑ g : G, (fun g => f (Quotient.mk (QuotientGroup.rightRel Γ) g)) g
        * (starRingEnd ℂ) (TG a (fun g => h (Quotient.mk (QuotientGroup.rightRel Γ) g)) g)
      = ∑ g : G, f (Quotient.mk (QuotientGroup.rightRel Γ) g)
        * (starRingEnd ℂ) (TY Γ a h (Quotient.mk (QuotientGroup.rightRel Γ) g)) := by
    refine Finset.sum_congr rfl (fun g _ => ?_)
    rw [TY_mk Γ a hinv h g]; rfl
  have hc : (Fintype.card Γ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have key : (Fintype.card Γ : ℂ) *
      ∑ y : Quotient (QuotientGroup.rightRel Γ), TY Γ a f y * (starRingEnd ℂ) (h y)
      = (Fintype.card Γ : ℂ) *
      ∑ y : Quotient (QuotientGroup.rightRel Γ), f y * (starRingEnd ℂ) (TY Γ a h y) := by
    rw [← nsmul_eq_mul, ← nsmul_eq_mul, ← hL, ← hR, ← e1, ← e2]
    exact hG
  exact mul_left_cancel₀ hc key

end Quot

end SectionA4a


namespace SectionA4a
open Section71d

variable (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)

theorem pgl_star_eq_inv {x : Quaternion ℚ} (hx : QH x) (n : ℕ)
    (hn : Quaternion.normSq x = (n : ℚ)) (hpn : ¬ p ∣ n) :
    (QuotientGroup.mk (SectionA2.redUnit p h2 xs ys hxy (Section73a.QH_star hx) n
        (by rw [Section73a.normSq_star']; exact hn) hpn) : SectionA2.PGL2 p)
      = (QuotientGroup.mk (SectionA2.redUnit p h2 xs ys hxy hx n hn hpn) : SectionA2.PGL2 p)⁻¹ :=
  eq_inv_of_mul_eq_one_left (SectionA2.pgl_star_mul_eq_one p h2 xs ys hxy hx n hn hpn)

theorem TY_adjoint_Yp {ι : Type*} [Fintype ι] (a : ι → SectionA2.PGL2 p) (σ : ι ≃ ι)
    (hσ : ∀ i, a (σ i) = (a i)⁻¹)
    (hinv : ∀ γ ∈ SectionA3b.Gam p h2 xs ys hxy, ∃ π : ι ≃ ι, ∀ i,
      ∃ δ ∈ SectionA3b.Gam p h2 xs ys hxy, a (π i) = δ * (a i * γ))
    [Fintype (SectionA2.PGL2 p)] [Fintype (SectionA2.PGL2 p ⧸ SectionA3b.Gam p h2 xs ys hxy)]
    [Fintype (SectionA3b.Gam p h2 xs ys hxy)] (f h : SectionA3b.Yp p h2 xs ys hxy → ℂ) :
    ∑ y : SectionA3b.Yp p h2 xs ys hxy,
        TY (SectionA3b.Gam p h2 xs ys hxy) a f y * (starRingEnd ℂ) (h y)
      = ∑ y : SectionA3b.Yp p h2 xs ys hxy,
        f y * (starRingEnd ℂ) (TY (SectionA3b.Gam p h2 xs ys hxy) a h y) :=
  TY_adjoint (SectionA3b.Gam p h2 xs ys hxy) a σ hσ hinv f h

end SectionA4a


/-! # StageA4b: T_m on Y_p for the Hurwitz quaternions of norm m, and its self-adjointness
(compiled here against the pinned Mathlib with StageA4a above unchanged; Actions run pending when written)

Everything above this block is StageA4a.lean unchanged (compiled green in Actions run 44629351934, commit 3fd0ebc, if that
run is green; check it).  Only the section below is new.

WHAT THIS SECTION PROVES, if it compiles.  Let p be a prime with 2 not zero in ZMod p, xs^2 + ys^2 = -1, and m a natural
number with p not dividing m.
 * `Hm m`: the Hurwitz quaternions of norm m, with `Hm_finite` and a Fintype instance (the coordinates 2 * (re, imI, imJ,
   imK) are integers whose squares sum to 4 m, so they lie in a box).
 * `aH`: alpha goes to the class of its reduction in PGL2(F_p); `aH_star`: aH (star alpha) = (aH alpha)^-1 (StageA4a's
   pgl_star_eq_inv with the proof terms matched).
 * `rmulEquiv u`: right multiplication by a Hurwitz unit u permutes Hm m; `aH_rmul`: aH (alpha u) = aH alpha * rho u;
   `aH_stable`: for gamma in Gamma_p the family is right-stable (delta = 1), which is the hypothesis `hinv` of StageA4a.
 * `Tm_adjoint`: with TY the StageA4a operator for the family aH, sum_y (TY f y) conj (h y) = sum_y f y conj (TY h y):
   the operator T_m (sum over alpha of norm m, f at [reduction of alpha times g]) is self-adjoint on functions on Y_p
   for the counting inner product.

DOES NOT PROVE: the recurrence T_p T_m = T_{pm} + p T_{m/p}; that T_m commutes with T_n; any eigenvalue bound; that
Hm m is nonempty or has size 24 sigma(m) for odd m (Stage80a, not in this chain); anything about H31gt3 or Lemma 3.2.
Self-adjointness is the spectral set-up only. -/

namespace SectionA4b
open Section71d

/-- Hurwitz quaternions of norm m. -/
def Hm (m : ℕ) : Type := {α : Quaternion ℚ // QH α ∧ Quaternion.normSq α = (m : ℚ)}

theorem Hm_finite (m : ℕ) : Finite (Hm m) := by
  classical
  have hc : ∀ α : Hm m, ∃ z : ℤ × ℤ × ℤ × ℤ, 2 * α.1.re = z.1 ∧ 2 * α.1.imI = z.2.1 ∧
      2 * α.1.imJ = z.2.2.1 ∧ 2 * α.1.imK = z.2.2.2 := by
    intro α
    obtain ⟨a0, a1, a2, a3, e0, e1, e2, e3⟩ := Section74b.coord_int α.2.1
    exact ⟨(a0, a1, a2, a3), e0, e1, e2, e3⟩
  choose f hf using hc
  have hinj : Function.Injective f := by
    intro α β h
    obtain ⟨a0, a1, a2, a3⟩ := hf α
    obtain ⟨b0, b1, b2, b3⟩ := hf β
    have c0 : (f α).1 = (f β).1 := by rw [h]
    have c1 : (f α).2.1 = (f β).2.1 := by rw [h]
    have c2 : (f α).2.2.1 = (f β).2.2.1 := by rw [h]
    have c3 : (f α).2.2.2 = (f β).2.2.2 := by rw [h]
    have g0 : α.1.re = β.1.re := by
      have : (2 : ℚ) * α.1.re = 2 * β.1.re := by rw [a0, b0, c0]
      linarith
    have g1 : α.1.imI = β.1.imI := by
      have : (2 : ℚ) * α.1.imI = 2 * β.1.imI := by rw [a1, b1, c1]
      linarith
    have g2 : α.1.imJ = β.1.imJ := by
      have : (2 : ℚ) * α.1.imJ = 2 * β.1.imJ := by rw [a2, b2, c2]
      linarith
    have g3 : α.1.imK = β.1.imK := by
      have : (2 : ℚ) * α.1.imK = 2 * β.1.imK := by rw [a3, b3, c3]
      linarith
    exact Subtype.ext (QuaternionAlgebra.ext g0 g1 g2 g3)
  let B : ℤ := 2 * (m : ℤ)
  let S : Finset (ℤ × ℤ × ℤ × ℤ) :=
    Finset.Icc (-B) B ×ˢ (Finset.Icc (-B) B ×ˢ (Finset.Icc (-B) B ×ˢ Finset.Icc (-B) B))
  have hmem : ∀ α : Hm m, f α ∈ S := by
    intro α
    obtain ⟨a0, a1, a2, a3⟩ := hf α
    have hn : (α.1.re) ^ 2 + (α.1.imI) ^ 2 + (α.1.imJ) ^ 2 + (α.1.imK) ^ 2 = (m : ℚ) := by
      have := α.2.2
      rw [Quaternion.normSq_def'] at this
      exact this
    have hsum : ((f α).1 : ℚ) ^ 2 + ((f α).2.1 : ℚ) ^ 2 + ((f α).2.2.1 : ℚ) ^ 2
        + ((f α).2.2.2 : ℚ) ^ 2 = 4 * m := by
      rw [← a0, ← a1, ← a2, ← a3]
      nlinarith [hn]
    have hmm : (m : ℤ) ≤ (m : ℤ) ^ 2 := by
      have : (0 : ℤ) ≤ (m : ℤ) := Int.natCast_nonneg m
      nlinarith
    have key : ∀ z : ℤ, (z : ℚ) ^ 2 ≤ 4 * m → -B ≤ z ∧ z ≤ B := by
      intro z hz
      have hz' : z ^ 2 ≤ B ^ 2 := by
        have : (z : ℚ) ^ 2 ≤ ((B : ℤ) : ℚ) ^ 2 := by
          have hB : ((B : ℤ) : ℚ) = 2 * (m : ℚ) := by simp [B]
          have hmq : (m : ℚ) ≤ (m : ℚ) ^ 2 := by exact_mod_cast hmm
          rw [hB]; nlinarith
        exact_mod_cast this
      exact abs_le_of_sq_le_sq' hz' (by simp [B])
    have s0 : ((f α).1 : ℚ) ^ 2 ≤ 4 * m := by nlinarith [sq_nonneg ((f α).2.1 : ℚ), sq_nonneg ((f α).2.2.1 : ℚ), sq_nonneg ((f α).2.2.2 : ℚ)]
    have s1 : ((f α).2.1 : ℚ) ^ 2 ≤ 4 * m := by nlinarith [sq_nonneg ((f α).1 : ℚ), sq_nonneg ((f α).2.2.1 : ℚ), sq_nonneg ((f α).2.2.2 : ℚ)]
    have s2 : ((f α).2.2.1 : ℚ) ^ 2 ≤ 4 * m := by nlinarith [sq_nonneg ((f α).1 : ℚ), sq_nonneg ((f α).2.1 : ℚ), sq_nonneg ((f α).2.2.2 : ℚ)]
    have s3 : ((f α).2.2.2 : ℚ) ^ 2 ≤ 4 * m := by nlinarith [sq_nonneg ((f α).1 : ℚ), sq_nonneg ((f α).2.1 : ℚ), sq_nonneg ((f α).2.2.1 : ℚ)]
    simp only [S, Finset.mem_product, Finset.mem_Icc]
    exact ⟨key _ s0, key _ s1, key _ s2, key _ s3⟩
  exact Finite.of_injective (fun α => (⟨f α, hmem α⟩ : S)) (fun α β h => hinj (congrArg Subtype.val h))

noncomputable instance (m : ℕ) : Fintype (Hm m) :=
  @Fintype.ofFinite _ (Hm_finite m)

variable (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)
variable (m : ℕ) (hpm : ¬ p ∣ m)

/-- The class in PGL2(F_p) of the reduction of a Hurwitz quaternion of norm m (p not dividing m). -/
noncomputable def aH (α : Hm m) : SectionA2.PGL2 p :=
  QuotientGroup.mk (SectionA2.redUnit p h2 xs ys hxy α.2.1 m α.2.2 hpm)

/-- Conjugation on Hurwitz quaternions of norm m. -/
def starH (α : Hm m) : Hm m :=
  ⟨star α.1, Section73a.QH_star α.2.1, by rw [Section73a.normSq_star']; exact α.2.2⟩

def starEquiv : Hm m ≃ Hm m where
  toFun := starH m
  invFun := starH m
  left_inv := fun α => Subtype.ext (star_star α.1)
  right_inv := fun α => Subtype.ext (star_star α.1)

theorem aH_star (α : Hm m) :
    aH p h2 xs ys hxy m hpm (starEquiv m α) = (aH p h2 xs ys hxy m hpm α)⁻¹ :=
  SectionA4a.pgl_star_eq_inv p h2 xs ys hxy α.2.1 m α.2.2 hpm

/-- Right multiplication by a Hurwitz unit, as a permutation of the Hurwitz quaternions of norm m. -/
def rmul (u : SectionA3a2.HurU) (α : Hm m) : Hm m :=
  ⟨α.1 * ((u : (Quaternion ℚ)ˣ) : Quaternion ℚ),
    QH_mul α.2.1 ((SectionA3a2.mem_iff _ |>.mp u.2).1),
    by rw [map_mul, α.2.2, (SectionA3a2.mem_iff _ |>.mp u.2).2, mul_one]⟩

def rmulEquiv (u : SectionA3a2.HurU) : Hm m ≃ Hm m where
  toFun := rmul m u
  invFun := rmul m u⁻¹
  left_inv := fun α => by
    apply Subtype.ext
    show α.1 * ((u : (Quaternion ℚ)ˣ) : Quaternion ℚ) * (((u⁻¹ : SectionA3a2.HurU) : (Quaternion ℚ)ˣ) : Quaternion ℚ) = α.1
    rw [mul_assoc]
    have : ((u : (Quaternion ℚ)ˣ) : Quaternion ℚ) * (((u⁻¹ : SectionA3a2.HurU) : (Quaternion ℚ)ˣ) : Quaternion ℚ) = 1 := by
      have := Units.mul_inv (u : (Quaternion ℚ)ˣ)
      simpa using this
    rw [this, mul_one]
  right_inv := fun α => by
    apply Subtype.ext
    show α.1 * (((u⁻¹ : SectionA3a2.HurU) : (Quaternion ℚ)ˣ) : Quaternion ℚ) * ((u : (Quaternion ℚ)ˣ) : Quaternion ℚ) = α.1
    rw [mul_assoc]
    have : (((u⁻¹ : SectionA3a2.HurU) : (Quaternion ℚ)ˣ) : Quaternion ℚ) * ((u : (Quaternion ℚ)ˣ) : Quaternion ℚ) = 1 := by
      have := Units.inv_mul (u : (Quaternion ℚ)ˣ)
      simpa using this
    rw [this, mul_one]

theorem aH_rmul (u : SectionA3a2.HurU) (α : Hm m) :
    aH p h2 xs ys hxy m hpm (rmulEquiv m u α) =
      aH p h2 xs ys hxy m hpm α * SectionA3a2.rho p h2 xs ys hxy u := by
  show QuotientGroup.mk _ = QuotientGroup.mk _ * QuotientGroup.mk _
  rw [← QuotientGroup.mk_mul]
  congr 1
  apply Units.ext
  rw [Units.val_mul, SectionA2.redUnit_coe, SectionA2.redUnit_coe, SectionA2.redUnit_coe]
  exact Section74b.red_mul p h2 xs ys hxy α.2.1 ((SectionA3a2.mem_iff _ |>.mp u.2).1)

theorem aH_stable (γ : SectionA2.PGL2 p) (hγ : γ ∈ SectionA3b.Gam p h2 xs ys hxy) :
    ∃ π : Hm m ≃ Hm m, ∀ α, ∃ δ ∈ SectionA3b.Gam p h2 xs ys hxy,
      aH p h2 xs ys hxy m hpm (π α) = δ * (aH p h2 xs ys hxy m hpm α * γ) := by
  obtain ⟨u, rfl⟩ := hγ
  exact ⟨rmulEquiv m u, fun α => ⟨1, Subgroup.one_mem _, by
    rw [one_mul]; exact aH_rmul p h2 xs ys hxy m hpm u α⟩⟩

/-- T_m on functions on Y_p: sum over the Hurwitz quaternions of norm m. -/
theorem Tm_adjoint
    [Fintype (SectionA2.PGL2 p)] [Fintype (SectionA2.PGL2 p ⧸ SectionA3b.Gam p h2 xs ys hxy)]
    [Fintype (SectionA3b.Gam p h2 xs ys hxy)] (f h : SectionA3b.Yp p h2 xs ys hxy → ℂ) :
    ∑ y : SectionA3b.Yp p h2 xs ys hxy,
        SectionA4a.TY (SectionA3b.Gam p h2 xs ys hxy) (aH p h2 xs ys hxy m hpm) f y
          * (starRingEnd ℂ) (h y)
      = ∑ y : SectionA3b.Yp p h2 xs ys hxy,
        f y * (starRingEnd ℂ)
          (SectionA4a.TY (SectionA3b.Gam p h2 xs ys hxy) (aH p h2 xs ys hxy m hpm) h y) :=
  SectionA4a.TY_adjoint_Yp p h2 xs ys hxy (aH p h2 xs ys hxy m hpm) (starEquiv m)
    (aH_star p h2 xs ys hxy m hpm) (aH_stable p h2 xs ys hxy m hpm) f h

end SectionA4b


/-! ### Stages 73c-78c imported from Stage80a (verbatim, lines 926-1719), needed by A4c. -/
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
    refine Quaternion.ext _ _ ?_ ?_ ?_ ?_
    · rw [(Section73b.mul_comp _ z).1]; simp
    · rw [(Section73b.mul_comp _ z).2.1]; simp
    · rw [(Section73b.mul_comp _ z).2.2.1]; simp
    · rw [(Section73b.mul_comp _ z).2.2.2]; simp
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

/-! # StageA4c (layer A for H31gt3): the weighted Hecke counting identity (compiled in the cloud before commit)

Fix a prime `l` (the Hecke prime; Stages 75-78 call it `p`), the keys `k : Option (ZMod l)`, and generators `g k` of the
right ideals `Ik k`.  PROVES: for every weight `Φ : Quaternion ℚ → ℂ` and every `m`,
  ∑_k ∑_{b of norm m} Φ(g_k b) = ∑_{x of norm l m} Φ x + l * (if l ∣ m then ∑_{y of norm m/l} Φ(l y) else 0).
This is Stage78b's double count with a weight in place of the counting measure; the cardinality statement is the case Φ = 1.
The new section is `SectionA4c`; Stages 73c-78c are copied verbatim from Stage80a (lines 926-1719) because they are not in
the earlier A-files.
DOES NOT PROVE: anything about the operators on Y_p (that is A4d: the reduction of g_k b and the unit reindexing), commutation,
eigenvalue bounds, the size 24 σ(m), or H31gt3. -/

open Section71d Finset

namespace SectionA4c

/-- STAGE A4c (weighted double count over keys).  Hecke prime `l` (Stage 75-78 call it `p`), keys `k : Option (ZMod l)`,
generators `g k` of the right ideals `Ik k`.  For any weight `Φ` on quaternions:
  ∑_k ∑_{b ∈ Hn m} Φ(g_k b)  =  ∑_{x ∈ Hn(l m)} Φ x  +  l * ∑_{x ∈ Hn(l m), red x = 0} Φ x. -/
theorem weighted_count (l : ℕ) [Fact l.Prime] (h2 : (2 : ZMod l) ≠ 0) (xs ys : ZMod l)
    (hxy : xs ^ 2 + ys ^ 2 = -1) (g : Option (ZMod l) → Quaternion ℚ)
    (hg : ∀ k, g k ∈ Section75b.Ik l xs ys k ∧ Quaternion.normSq (g k) = (l : ℚ) ∧
      ∀ x ∈ Section75b.Ik l xs ys k, ∃ y, QH y ∧ x = g k * y)
    (Φ : Quaternion ℚ → ℂ) (m : ℕ) :
    ∑ k : Option (ZMod l), ∑ b ∈ (Section77a.Hn_finite m).toFinset, Φ (g k * b)
      = ∑ x ∈ (Section77a.Hn_finite (l * m)).toFinset, Φ x
        + (l : ℂ) * ∑ x ∈ (Section77a.Hn_finite (l * m)).toFinset.filter
            (fun x => Section74b.red l xs ys x = 0), Φ x := by
  classical
  set S : Finset (Quaternion ℚ) := (Section77a.Hn_finite (l * m)).toFinset with hSdef
  set Sm : Finset (Quaternion ℚ) := (Section77a.Hn_finite m).toFinset with hSmdef
  have hS : ∀ x, x ∈ S ↔ x ∈ Section75a.Hn (l * m) := fun x => Set.Finite.mem_toFinset _
  have hSm : ∀ x, x ∈ Sm ↔ x ∈ Section75a.Hn m := fun x => Set.Finite.mem_toFinset _
  have hl : (l : ℚ) ≠ 0 := Section78a.p_ne_zero_Q l
  -- per-key: sum over b equals sum over the elements of S lying in Ik k
  have hA : ∀ k : Option (ZMod l),
      ∑ b ∈ Sm, Φ (g k * b) = ∑ x ∈ S.filter (fun x => x ∈ Section75b.Ik l xs ys k), Φ x := by
    intro k
    obtain ⟨hgI, hgn, hgen⟩ := hg k
    have hI := Section75b.Ik_ideal l h2 xs ys hxy k
    have hg0 : g k ≠ 0 := by
      intro h; apply hl; rw [← hgn, h]; simp
    refine Finset.sum_bij (fun b _ => g k * b) ?_ ?_ ?_ ?_
    · intro b hb
      obtain ⟨hbH, hbn⟩ := (hSm b).1 hb
      rw [Finset.mem_filter, hS]
      refine ⟨⟨QH_mul (hI.all_H _ hgI) hbH, ?_⟩, hI.mul_mem _ hgI b hbH⟩
      rw [map_mul, hgn, hbn]; push_cast; ring
    · intro a _ b _ hab
      exact mul_left_cancel₀ hg0 hab
    · intro x hx
      rw [Finset.mem_filter, hS] at hx
      obtain ⟨⟨hxH, hxn⟩, hxI⟩ := hx
      obtain ⟨y, hy, rfl⟩ := hgen x hxI
      refine ⟨y, (hSm y).2 ⟨hy, ?_⟩, rfl⟩
      rw [map_mul, hgn] at hxn
      push_cast at hxn
      exact mul_left_cancel₀ hl hxn
    · intro b _; rfl
  have hdiv : (((l * m : ℕ)) : ZMod l) = 0 := by simp
  -- number of keys whose ideal contains x
  have hB : ∀ x ∈ S, (Finset.univ.filter (fun k : Option (ZMod l) => x ∈ Section75b.Ik l xs ys k)).card =
      if Section74b.red l xs ys x = 0 then l + 1 else 1 := by
    intro x hx
    obtain ⟨hxH, hxn⟩ := (hS x).1 hx
    by_cases hz : Section74b.red l xs ys x = 0
    · rw [if_pos hz]
      have : Finset.univ.filter (fun k : Option (ZMod l) => x ∈ Section75b.Ik l xs ys k) = Finset.univ := by
        apply Finset.filter_true_of_mem
        intro k _
        exact Section76b.Ik_zero l xs ys hxH hz k
      rw [this, Finset.card_univ, Fintype.card_option, ZMod.card]
    · rw [if_neg hz]
      obtain ⟨k, hk, hku⟩ := Section76b.Ik_existsUnique l h2 xs ys hxy hxH (l * m) hxn hdiv hz
      rw [Finset.card_eq_one]
      refine ⟨k, ?_⟩
      ext k'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h => hku k' h, fun h => h ▸ hk⟩
  -- swap the order of summation
  have hswap : ∑ k : Option (ZMod l), ∑ x ∈ S.filter (fun x => x ∈ Section75b.Ik l xs ys k), Φ x
      = ∑ x ∈ S, ((Finset.univ.filter (fun k : Option (ZMod l) => x ∈ Section75b.Ik l xs ys k)).card : ℂ) * Φ x := by
    have h1 : ∀ k : Option (ZMod l), ∑ x ∈ S.filter (fun x => x ∈ Section75b.Ik l xs ys k), Φ x
        = ∑ x ∈ S, if x ∈ Section75b.Ik l xs ys k then Φ x else 0 := by
      intro k; rw [Finset.sum_filter]
    rw [Finset.sum_congr rfl (fun k _ => h1 k), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_congr rfl (fun k _ => hA k), hswap]
  have hS' : ∀ x ∈ S, ((Finset.univ.filter (fun k : Option (ZMod l) => x ∈ Section75b.Ik l xs ys k)).card : ℂ) * Φ x
      = Φ x + (l : ℂ) * (if Section74b.red l xs ys x = 0 then Φ x else 0) := by
    intro x hx
    rw [hB x hx]
    by_cases hz : Section74b.red l xs ys x = 0
    · simp [hz]; ring
    · simp [hz]
  rw [Finset.sum_congr rfl hS', Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_filter]


/-- The zero-reduction fibre, weighted: for `l ∣ m` it is `l • Hn(m/l)`; otherwise empty. -/
theorem zero_fibre_sum (l : ℕ) [Fact l.Prime] (h2 : (2 : ZMod l) ≠ 0) (xs ys : ZMod l)
    (hxy : xs ^ 2 + ys ^ 2 = -1) (Φ : Quaternion ℚ → ℂ) (m : ℕ) :
    ∑ x ∈ (Section77a.Hn_finite (l * m)).toFinset.filter (fun x => Section74b.red l xs ys x = 0), Φ x
      = if l ∣ m then ∑ y ∈ (Section77a.Hn_finite (m / l)).toFinset, Φ ((l : ℚ) • y) else 0 := by
  classical
  have hl := Section78a.p_ne_zero_Q l
  have hpos : 0 < l := (Fact.out : l.Prime).pos
  by_cases hdv : l ∣ m
  · rw [if_pos hdv]
    obtain ⟨m', rfl⟩ := hdv
    have hdiv : l * m' / l = m' := Nat.mul_div_cancel_left m' hpos
    rw [hdiv]
    symm
    refine Finset.sum_bij (fun y _ => (l : ℚ) • y) ?_ ?_ ?_ ?_
    · intro y hy
      have hy' : y ∈ Section75a.Hn m' := (Set.Finite.mem_toFinset _).1 hy
      obtain ⟨hyH, hyn⟩ := hy'
      rw [Finset.mem_filter]
      refine ⟨(Set.Finite.mem_toFinset _).2 ⟨Section78a.QH_smul_nat l hyH, ?_⟩, Section75b.red_smul_p l xs ys hyH⟩
      rw [Section78a.normSq_smul_nat, hyn]; push_cast; ring
    · intro a _ b _ hab
      exact smul_right_injective (Quaternion ℚ) hl hab
    · intro x hx
      rw [Finset.mem_filter] at hx
      obtain ⟨hx1, hx2⟩ := hx
      have hx1' : x ∈ Section75a.Hn (l * (l * m')) := (Set.Finite.mem_toFinset _).1 hx1
      obtain ⟨y, hy, rfl, n', hn', hmn⟩ := Section78c.zero_red_form l h2 xs ys hxy (l * m') hx1' hx2
      have : m' = n' := Nat.eq_of_mul_eq_mul_left hpos hmn
      subst this
      exact ⟨y, (Set.Finite.mem_toFinset _).2 ⟨hy, hn'⟩, rfl⟩
    · intro y _; rfl
  · rw [if_neg hdv]
    apply Finset.sum_eq_zero
    intro x hx
    exfalso
    rw [Finset.mem_filter] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hx1' : x ∈ Section75a.Hn (l * m) := Set.Finite.mem_toFinset _ |>.1 hx1
    obtain ⟨y, hy, rfl, n', hn', hmn⟩ := Section78c.zero_red_form l h2 xs ys hxy m hx1' hx2
    exact hdv ⟨n', hmn⟩

/-- STAGE A4c, final form (the weighted Hecke count): for `l` prime and `m`,
  ∑_k ∑_{b ∈ Hn m} Φ(g_k b) = ∑_{x ∈ Hn(l m)} Φ x + l * (if l ∣ m then ∑_{y ∈ Hn(m/l)} Φ(l y) else 0). -/
theorem hecke_count (l : ℕ) [Fact l.Prime] (h2 : (2 : ZMod l) ≠ 0) (xs ys : ZMod l)
    (hxy : xs ^ 2 + ys ^ 2 = -1) (g : Option (ZMod l) → Quaternion ℚ)
    (hg : ∀ k, g k ∈ Section75b.Ik l xs ys k ∧ Quaternion.normSq (g k) = (l : ℚ) ∧
      ∀ x ∈ Section75b.Ik l xs ys k, ∃ y, QH y ∧ x = g k * y)
    (Φ : Quaternion ℚ → ℂ) (m : ℕ) :
    ∑ k : Option (ZMod l), ∑ b ∈ (Section77a.Hn_finite m).toFinset, Φ (g k * b)
      = ∑ x ∈ (Section77a.Hn_finite (l * m)).toFinset, Φ x
        + (l : ℂ) * (if l ∣ m then ∑ y ∈ (Section77a.Hn_finite (m / l)).toFinset, Φ ((l : ℚ) • y) else 0) := by
  rw [weighted_count l h2 xs ys hxy g hg Φ m, zero_fibre_sum l h2 xs ys hxy Φ m]

end SectionA4c

/-! ### Stages 72a, 73e imported from Stage80a (verbatim, lines 1721-1951): the 24 Hurwitz units. -/
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
      obtain ⟨u, e0, e1, e2, e3⟩ : ∃ u : Quaternion ℚ,
          u.re = x 0 ∧ u.imI = x 1 ∧ u.imJ = x 2 ∧ u.imK = x 3 := by
        first
        | exact ⟨⟨x 0, x 1, x 2, x 3⟩, rfl, rfl, rfl, rfl⟩
        | exact ⟨QuaternionAlgebra.mk (x 0) (x 1) (x 2) (x 3), rfl, rfl, rfl, rfl⟩
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
        fin_cases i <;> simp [f, e0, e1, e2, e3]
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

/-! # StageA4d (layer A for H31gt3): the Hecke count with the full norm-l family, factor 24 (compiled in the cloud before commit)

Same data as StageA4c (prime `l`, keys, generators `g k`).  PROVES, for every weight `Φ` and every `m`:
  ∑_{c of norm l} ∑_{b of norm m} Φ(c b) = 24 * ( ∑_{x of norm l m} Φ x + l * (if l ∣ m then ∑_{y of norm m/l} Φ(l y) else 0) ).
Ingredients: every element of norm `l` is `g_k * u` for exactly one key `k` and one unit `u` (`sum_Hn_l`); left multiplication by a
unit permutes the elements of norm `m` (`sum_lmul`); there are 24 units (Stage73e, copied verbatim from Stage80a lines 1721-1951);
then StageA4c's `hecke_count`.
CORRECTS the plan: the one-generator-per-key operator V_l is not well defined on Y_p, so the statement uses the full family.
DOES NOT PROVE: anything on Y_p (that is A4e: reduction is multiplicative for two moduli, the `Hm`/`Hn` bridge, assembly),
commutation, eigenvalue bounds, the size 24 σ(m), or H31gt3. -/

open Section71d Finset


namespace SectionA4d


/-- left multiplication by a Hurwitz unit permutes the elements of norm `m` -/
theorem sum_lmul (m : ℕ) {u : Quaternion ℚ} (hu : QH u) (hun : Quaternion.normSq u = 1)
    (F : Quaternion ℚ → ℂ) :
    ∑ b ∈ (Section77a.Hn_finite m).toFinset, F (u * b) = ∑ b ∈ (Section77a.Hn_finite m).toFinset, F b := by
  refine Finset.sum_bij (fun b _ => u * b) ?_ ?_ ?_ ?_
  · intro b hb
    obtain ⟨hbH, hbn⟩ := (Set.Finite.mem_toFinset _).1 hb
    refine (Set.Finite.mem_toFinset _).2 ⟨QH_mul hu hbH, ?_⟩
    rw [map_mul, hun, hbn, one_mul]
  · intro a _ b _ hab
    have h0 : (star u * u) * a = (star u * u) * b := by rw [mul_assoc, hab, ← mul_assoc]
    have e : star u * u = 1 := by
      have := Quaternion.star_mul_self u
      rw [hun] at this; simpa using this
    rwa [e, one_mul, one_mul] at h0
  · intro b' hb'
    obtain ⟨hbH, hbn⟩ := (Set.Finite.mem_toFinset _).1 hb'
    refine ⟨star u * b', (Set.Finite.mem_toFinset _).2 ⟨QH_mul (Section73a.QH_star hu) hbH, ?_⟩, ?_⟩
    · rw [map_mul, Section73a.normSq_star', hun, hbn, one_mul]
    · have e : u * star u = 1 := by
        have := Quaternion.self_mul_star u
        rw [hun] at this; simpa using this
      show u * (star u * b') = b'
      rw [← mul_assoc, e, one_mul]
  · intro b _; rfl

theorem Hn_one_card : ((Section77a.Hn_finite 1).toFinset).card = 24 := by
  have e : (Section77a.Hn_finite 1).toFinset.card = (Section75a.Hn 1).ncard := by
    rw [← Set.ncard_coe_finset, Set.Finite.coe_toFinset]
  rw [e]
  have : Section75a.Hn 1 = {u : Quaternion ℚ | QH u ∧ Quaternion.normSq u = 1} := by
    ext x; simp [Section75a.Hn]
  rw [this]; exact Section73e.units_QH_count

variable (l : ℕ) [Fact l.Prime] (h2 : (2 : ZMod l) ≠ 0) (xs ys : ZMod l) (hxy : xs ^ 2 + ys ^ 2 = -1)
include h2 hxy

/-- an element of norm l has nonzero reduction mod l -/
theorem red_ne_zero {c : Quaternion ℚ} (hc : c ∈ Section75a.Hn l) : Section74b.red l xs ys c ≠ 0 := by
  intro hz
  have hc' : c ∈ Section75a.Hn (l * 1) := by simpa using hc
  obtain ⟨y, hy, rfl, n', hn', hmn⟩ := Section78c.zero_red_form l h2 xs ys hxy 1 hc' hz
  have h1 := (Fact.out : l.Prime).one_lt
  have : l ∣ 1 := ⟨n', hmn⟩
  exact absurd (Nat.le_of_dvd one_pos this) (by omega)

/-- every element of norm l lies in exactly one Ik, hence is `g_k * y` with `y` of norm 1 -/
theorem decomp (g : Option (ZMod l) → Quaternion ℚ)
    (hg : ∀ k, g k ∈ Section75b.Ik l xs ys k ∧ Quaternion.normSq (g k) = (l : ℚ) ∧
      ∀ x ∈ Section75b.Ik l xs ys k, ∃ y, QH y ∧ x = g k * y)
    {c : Quaternion ℚ} (hc : c ∈ Section75a.Hn l) :
    ∃! k : Option (ZMod l), c ∈ Section75b.Ik l xs ys k := by
  obtain ⟨hcH, hcn⟩ := hc
  exact Section76b.Ik_existsUnique l h2 xs ys hxy hcH l hcn (by simp) (red_ne_zero l h2 xs ys hxy ⟨hcH, hcn⟩)

theorem sum_Hn_l (g : Option (ZMod l) → Quaternion ℚ)
    (hg : ∀ k, g k ∈ Section75b.Ik l xs ys k ∧ Quaternion.normSq (g k) = (l : ℚ) ∧
      ∀ x ∈ Section75b.Ik l xs ys k, ∃ y, QH y ∧ x = g k * y)
    (Ψ : Quaternion ℚ → ℂ) :
    ∑ c ∈ (Section77a.Hn_finite l).toFinset, Ψ c
      = ∑ k : Option (ZMod l), ∑ u ∈ (Section77a.Hn_finite 1).toFinset, Ψ (g k * u) := by
  classical
  have hl : (l : ℚ) ≠ 0 := Section78a.p_ne_zero_Q l
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_bij (fun ku _ => g ku.1 * ku.2) ?_ ?_ ?_ ?_
  · rintro ⟨k, u⟩ hku
    rw [Finset.mem_product] at hku
    obtain ⟨-, hu⟩ := hku
    obtain ⟨huH, hun⟩ := (Set.Finite.mem_toFinset _).1 hu
    obtain ⟨hgI, hgn, -⟩ := hg k
    have hI := Section75b.Ik_ideal l h2 xs ys hxy k
    refine (Set.Finite.mem_toFinset _).2 ⟨QH_mul (hI.all_H _ hgI) huH, ?_⟩
    rw [map_mul, hgn, hun]; push_cast; ring
  · rintro ⟨k, u⟩ hku ⟨k', u'⟩ hku' h
    simp only at h
    rw [Finset.mem_product] at hku hku'
    obtain ⟨huH, hun⟩ := (Set.Finite.mem_toFinset _).1 hku.2
    obtain ⟨huH', hun'⟩ := (Set.Finite.mem_toFinset _).1 hku'.2
    obtain ⟨hgI, hgn, -⟩ := hg k
    obtain ⟨hgI', hgn', -⟩ := hg k'
    have hI := Section75b.Ik_ideal l h2 xs ys hxy k
    have hI' := Section75b.Ik_ideal l h2 xs ys hxy k'
    have hc : g k * u ∈ Section75a.Hn l := by
      refine ⟨QH_mul (hI.all_H _ hgI) huH, ?_⟩
      rw [map_mul, hgn, hun]; push_cast; ring
    have m1 : g k * u ∈ Section75b.Ik l xs ys k := hI.mul_mem _ hgI u huH
    have m2 : g k * u ∈ Section75b.Ik l xs ys k' := by rw [h]; exact hI'.mul_mem _ hgI' u' huH'
    obtain ⟨k0, _, hk0⟩ := decomp l h2 xs ys hxy g hg hc
    have e1 := hk0 k m1
    have e2 := hk0 k' m2
    have hkk : k = k' := e1.trans e2.symm
    subst hkk
    have hg0 : g k ≠ 0 := by
      intro h0; apply hl; rw [← hgn, h0]; simp
    exact Prod.ext rfl (mul_left_cancel₀ hg0 h)
  · intro c hc
    have hc' := (Set.Finite.mem_toFinset _).1 hc
    obtain ⟨k, hk, -⟩ := decomp l h2 xs ys hxy g hg hc'
    obtain ⟨hgI, hgn, hgen⟩ := hg k
    obtain ⟨y, hy, rfl⟩ := hgen c hk
    refine ⟨(k, y), ?_, rfl⟩
    rw [Finset.mem_product]
    refine ⟨Finset.mem_univ _, (Set.Finite.mem_toFinset _).2 ⟨hy, ?_⟩⟩
    have := hc'.2
    rw [map_mul, hgn] at this
    have : (l : ℚ) * Quaternion.normSq y = (l : ℚ) * 1 := by simpa using this
    simpa using mul_left_cancel₀ hl this
  · intro ku _; rfl

/-- STAGE A4d: ∑_{c of norm l} ∑_{b of norm m} Φ(c b) = 24 * (the Stage A4c right-hand side). -/
theorem hecke_U (g : Option (ZMod l) → Quaternion ℚ)
    (hg : ∀ k, g k ∈ Section75b.Ik l xs ys k ∧ Quaternion.normSq (g k) = (l : ℚ) ∧
      ∀ x ∈ Section75b.Ik l xs ys k, ∃ y, QH y ∧ x = g k * y)
    (Φ : Quaternion ℚ → ℂ) (m : ℕ) :
    ∑ c ∈ (Section77a.Hn_finite l).toFinset, ∑ b ∈ (Section77a.Hn_finite m).toFinset, Φ (c * b)
      = 24 * (∑ x ∈ (Section77a.Hn_finite (l * m)).toFinset, Φ x
        + (l : ℂ) * (if l ∣ m then ∑ y ∈ (Section77a.Hn_finite (m / l)).toFinset, Φ ((l : ℚ) • y) else 0)) := by
  rw [sum_Hn_l l h2 xs ys hxy g hg (fun c => ∑ b ∈ (Section77a.Hn_finite m).toFinset, Φ (c * b))]
  have step : ∀ k : Option (ZMod l), ∀ u ∈ (Section77a.Hn_finite 1).toFinset,
      ∑ b ∈ (Section77a.Hn_finite m).toFinset, Φ (g k * u * b)
        = ∑ b ∈ (Section77a.Hn_finite m).toFinset, Φ (g k * b) := by
    intro k u hu
    obtain ⟨huH, hun⟩ := (Set.Finite.mem_toFinset _).1 hu
    have := sum_lmul m huH (by simpa using hun) (fun b => Φ (g k * b))
    simpa [mul_assoc] using this
  have hk : ∀ k : Option (ZMod l), ∑ u ∈ (Section77a.Hn_finite 1).toFinset,
      ∑ b ∈ (Section77a.Hn_finite m).toFinset, Φ (g k * u * b)
      = 24 * ∑ b ∈ (Section77a.Hn_finite m).toFinset, Φ (g k * b) := by
    intro k
    rw [Finset.sum_congr rfl (fun u hu => step k u hu), Finset.sum_const, Hn_one_card, nsmul_eq_mul]
    push_cast; ring
  rw [Finset.sum_congr rfl (fun k _ => hk k), ← Finset.mul_sum,
    SectionA4c.hecke_count l h2 xs ys hxy g hg Φ m]

end SectionA4d

/-! # StageA4e (layer A for H31gt3): the Hecke relation on functions on Y_p (compiled in the cloud before commit)

PROVES: for primes `p` (the level, with the usual `h2 xs ys hxy`) and `l` (the Hecke prime, with its own `h2l xsl ysl hxyl`),
`l` not divisible by `p`, `m` not divisible by `p`, every `f : Y_p → ℂ` and every `y : Y_p`:
  (U_m (U_l f)) y = 24 * ( (U_{l m} f) y + l * (if l ∣ m then (U_{m/l} f) y else 0) ),
where `U_n = TY Γ (aH n)` is the unnormalised sum over all Hurwitz quaternions of norm `n` (Stage A4a/A4b).
Ingredients: `rhoT` (the reduction class as a total function) with `rhoT_mul` and `rhoT_natsmul` (the scalar l is trivial in PGL2),
`sum_Hm` (the `Hm` subtype versus the `Hn` finset), `U_mk` (U_n as a finset sum over norm `n`), then StageA4d's `hecke_U`.
DOES NOT PROVE: commutation of the U_n with one another, multiplicativity for coprime m, n, eigenvalue bounds, the size 24 σ(m),
or H31gt3.  The normalisation (dividing by 24) is not done here. -/

open Section71d Finset


namespace SectionA4e

variable (p : ℕ) [Fact p.Prime]

open Classical in
/-- the reduction class of an arbitrary quaternion, total: `[red x]` when `red x` is invertible, else `1`. -/
noncomputable def rhoT (xs ys : ZMod p) (x : Quaternion ℚ) : SectionA2.PGL2 p :=
  if h : IsUnit (Section74b.red p xs ys x) then QuotientGroup.mk h.unit else 1

theorem rhoT_of_unit (xs ys : ZMod p) {x : Quaternion ℚ} (h : IsUnit (Section74b.red p xs ys x)) :
    rhoT p xs ys x = QuotientGroup.mk h.unit := by
  unfold rhoT; rw [dif_pos h]

theorem rhoT_aH (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)
    (n : ℕ) (hpn : ¬ p ∣ n) (α : SectionA4b.Hm n) :
    rhoT p xs ys α.1 = SectionA4b.aH p h2 xs ys hxy n hpn α := by
  have hu := SectionA1.red_isUnit p h2 xs ys hxy α.2.1 n α.2.2 hpn
  rw [rhoT_of_unit p xs ys hu]; rfl

theorem rhoT_mul (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)
    {x y : Quaternion ℚ} (hxQ : QH x) (hyQ : QH y)
    (hx : IsUnit (Section74b.red p xs ys x)) (hy : IsUnit (Section74b.red p xs ys y)) :
    rhoT p xs ys (x * y) = rhoT p xs ys x * rhoT p xs ys y := by
  have hm : IsUnit (Section74b.red p xs ys (x * y)) := by
    rw [Section74b.red_mul p h2 xs ys hxy hxQ hyQ]; exact hx.mul hy
  rw [rhoT_of_unit p xs ys hm, rhoT_of_unit p xs ys hx, rhoT_of_unit p xs ys hy, ← QuotientGroup.mk_mul]
  congr 1
  apply Units.ext
  rw [Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec, IsUnit.unit_spec]
  exact Section74b.red_mul p h2 xs ys hxy hxQ hyQ

theorem red_natcast (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (l : ℕ) :
    Section74b.red p xs ys (((l : ℚ)) : Quaternion ℚ) = (l : ZMod p) • (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
  unfold Section74b.red
  have e0 : ((l : ℚ) : Quaternion ℚ).re = (l : ℚ) := by simp
  have e1 : ((l : ℚ) : Quaternion ℚ).imI = 0 := by simp
  have e2 : ((l : ℚ) : Quaternion ℚ).imJ = 0 := by simp
  have e3 : ((l : ℚ) : Quaternion ℚ).imK = 0 := by simp
  have cl : Section74b.cz p (l : ℚ) = (l : ZMod p) := by
    rw [Section74b.cz_eq p (l : ℚ) ((2 * l : ℕ) : ℤ) (by push_cast; ring)]
    push_cast
    field_simp
  have c0 : Section74b.cz p 0 = 0 := by
    rw [Section74b.cz_eq p 0 0 (by norm_num)]; simp
  rw [e0, e1, e2, e3, cl, c0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Section74a.psi]

theorem rhoT_natsmul (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)
    (l : ℕ) (hl : ¬ p ∣ l) {y : Quaternion ℚ} (hyQ : QH y) (hy : IsUnit (Section74b.red p xs ys y)) :
    rhoT p xs ys ((l : ℚ) • y) = rhoT p xs ys y := by
  have hQ : QH (((l : ℚ)) : Quaternion ℚ) := by
    have := Section78a.QH_int (l : ℤ)
    simpa using this
  have hsm : ((l : ℚ) • y) = (((l : ℚ)) : Quaternion ℚ) * y := (Quaternion.coe_mul_eq_smul _ _).symm
  have hred : Section74b.red p xs ys ((l : ℚ) • y)
      = (l : ZMod p) • Section74b.red p xs ys y := by
    rw [hsm, Section74b.red_mul p h2 xs ys hxy hQ hyQ, red_natcast p h2 xs ys l, Matrix.smul_mul, one_mul]
  have hlu : IsUnit (l : ZMod p) := by
    rw [isUnit_iff_ne_zero]
    intro h
    exact hl ((ZMod.natCast_eq_zero_iff l p).1 h)
  have hs1 : IsUnit ((l : ZMod p) • (1 : Matrix (Fin 2) (Fin 2) (ZMod p))) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    simp [Matrix.det_smul]
    exact hlu.ne_zero
  have hunit : IsUnit (Section74b.red p xs ys ((l : ℚ) • y)) := by
    rw [hred]
    have : (l : ZMod p) • Section74b.red p xs ys y
        = ((l : ZMod p) • (1 : Matrix (Fin 2) (Fin 2) (ZMod p))) * Section74b.red p xs ys y := by
      rw [Matrix.smul_mul, one_mul]
    rw [this]; exact hs1.mul hy
  rw [rhoT_of_unit p xs ys hunit, rhoT_of_unit p xs ys hy]
  set z : (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ := hs1.unit with hz
  have hzc : z ∈ Subgroup.center (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Units.ext
    simp only [Units.val_mul, hz, IsUnit.unit_spec]
    simp [Matrix.mul_smul, Matrix.smul_mul]
  have heq : hunit.unit = z * hy.unit := by
    apply Units.ext
    rw [Units.val_mul, IsUnit.unit_spec, hz, IsUnit.unit_spec, IsUnit.unit_spec, hred, Matrix.smul_mul, one_mul]
  rw [heq, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff z).2 hzc, one_mul]


theorem sum_Hm (n : ℕ) (F : Quaternion ℚ → ℂ) :
    ∑ α : SectionA4b.Hm n, F α.1 = ∑ x ∈ (Section77a.Hn_finite n).toFinset, F x := by
  classical
  refine Finset.sum_bij (fun α _ => α.1) ?_ ?_ ?_ ?_
  · intro α _
    exact (Set.Finite.mem_toFinset _).2 ⟨α.2.1, α.2.2⟩
  · intro a _ b _ h; exact Subtype.ext h
  · intro x hx
    obtain ⟨hxH, hxn⟩ := (Set.Finite.mem_toFinset _).1 hx
    exact ⟨⟨x, hxH, hxn⟩, Finset.mem_univ _, rfl⟩
  · intro a _; rfl

variable (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)

/-- the unnormalised Hecke operator U_n on functions on Y_p -/
noncomputable def U (n : ℕ) (hpn : ¬ p ∣ n) (f : SectionA3b.Yp p h2 xs ys hxy → ℂ) :
    SectionA3b.Yp p h2 xs ys hxy → ℂ :=
  SectionA4a.TY (SectionA3b.Gam p h2 xs ys hxy) (SectionA4b.aH p h2 xs ys hxy n hpn) f

theorem U_mk (n : ℕ) (hpn : ¬ p ∣ n) (f : SectionA3b.Yp p h2 xs ys hxy → ℂ) (g : SectionA2.PGL2 p) :
    U p h2 xs ys hxy n hpn f (Quotient.mk (QuotientGroup.rightRel (SectionA3b.Gam p h2 xs ys hxy)) g)
      = ∑ x ∈ (Section77a.Hn_finite n).toFinset,
          f (Quotient.mk (QuotientGroup.rightRel (SectionA3b.Gam p h2 xs ys hxy)) (rhoT p xs ys x * g)) := by
  unfold U
  rw [SectionA4a.TY_mk _ _ (SectionA4b.aH_stable p h2 xs ys hxy n hpn) f g]
  rw [← sum_Hm n (fun x => f (Quotient.mk (QuotientGroup.rightRel (SectionA3b.Gam p h2 xs ys hxy)) (rhoT p xs ys x * g)))]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [rhoT_aH p h2 xs ys hxy n hpn α]


theorem isUnit_red_of_mem (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)
    {n : ℕ} (hpn : ¬ p ∣ n) {x : Quaternion ℚ} (hx : x ∈ Section75a.Hn n) :
    IsUnit (Section74b.red p xs ys x) :=
  SectionA1.red_isUnit p h2 xs ys hxy hx.1 n hx.2 hpn

/-- STAGE A4e: the Hecke relation `U_m U_l = 24 (U_{l m} + l U_{m/l})` on functions on Y_p. -/
theorem hecke_Yp (l : ℕ) [Fact l.Prime] (h2l : (2 : ZMod l) ≠ 0) (xsl ysl : ZMod l)
    (hxyl : xsl ^ 2 + ysl ^ 2 = -1) (hpl : ¬ p ∣ l) (m : ℕ) (hpm : ¬ p ∣ m)
    (f : SectionA3b.Yp p h2 xs ys hxy → ℂ) (y : SectionA3b.Yp p h2 xs ys hxy) :
    U p h2 xs ys hxy m hpm (U p h2 xs ys hxy l hpl f) y
      = 24 * (U p h2 xs ys hxy (l * m) (fun h => (Nat.Prime.dvd_mul (Fact.out : p.Prime)).1 h |>.elim hpl hpm) f y
          + (l : ℂ) * (if hd : l ∣ m then
              U p h2 xs ys hxy (m / l) (fun h => hpm (dvd_trans h (Nat.div_dvd_of_dvd hd))) f y else 0)) := by
  classical
  choose g hgI hgn hgen using fun k => Section75b.gen_exists l h2l xsl ysl hxyl k
  have hg : ∀ k, g k ∈ Section75b.Ik l xsl ysl k ∧ Quaternion.normSq (g k) = (l : ℚ) ∧
      ∀ x ∈ Section75b.Ik l xsl ysl k, ∃ y, QH y ∧ x = g k * y := fun k => ⟨hgI k, hgn k, hgen k⟩
  have hplm : ¬ p ∣ l * m := fun h => (Nat.Prime.dvd_mul (Fact.out : p.Prime)).1 h |>.elim hpl hpm
  refine Quotient.inductionOn y (fun g0 => ?_)
  set Φ : Quaternion ℚ → ℂ := fun x =>
    f (Quotient.mk (QuotientGroup.rightRel (SectionA3b.Gam p h2 xs ys hxy)) (rhoT p xs ys x * g0)) with hΦ
  have hLHS : U p h2 xs ys hxy m hpm (U p h2 xs ys hxy l hpl f)
        (Quotient.mk (QuotientGroup.rightRel (SectionA3b.Gam p h2 xs ys hxy)) g0)
      = ∑ c ∈ (Section77a.Hn_finite l).toFinset, ∑ b ∈ (Section77a.Hn_finite m).toFinset, Φ (c * b) := by
    rw [U_mk p h2 xs ys hxy m hpm _ g0, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b hb => ?_)
    rw [U_mk p h2 xs ys hxy l hpl f]
    refine Finset.sum_congr rfl (fun c hc => ?_)
    have hb' := (Set.Finite.mem_toFinset _).1 hb
    have hc' := (Set.Finite.mem_toFinset _).1 hc
    simp only [hΦ]
    rw [rhoT_mul p h2 xs ys hxy hc'.1 hb'.1 (isUnit_red_of_mem p h2 xs ys hxy hpl hc')
      (isUnit_red_of_mem p h2 xs ys hxy hpm hb'), mul_assoc]
  rw [hLHS, SectionA4d.hecke_U l h2l xsl ysl hxyl g hg Φ m]
  have e1 : ∑ x ∈ (Section77a.Hn_finite (l * m)).toFinset, Φ x
      = U p h2 xs ys hxy (l * m) hplm f
          (Quotient.mk (QuotientGroup.rightRel (SectionA3b.Gam p h2 xs ys hxy)) g0) :=
    (U_mk p h2 xs ys hxy (l * m) hplm f g0).symm
  have e2 : (if l ∣ m then ∑ y ∈ (Section77a.Hn_finite (m / l)).toFinset, Φ ((l : ℚ) • y) else 0)
      = (if hd : l ∣ m then
          U p h2 xs ys hxy (m / l) (fun h => hpm (dvd_trans h (Nat.div_dvd_of_dvd hd))) f
            (Quotient.mk (QuotientGroup.rightRel (SectionA3b.Gam p h2 xs ys hxy)) g0) else 0) := by
    by_cases hd : l ∣ m
    · rw [if_pos hd, dif_pos hd, U_mk p h2 xs ys hxy (m / l) _ f g0]
      refine Finset.sum_congr rfl (fun y hy => ?_)
      have hy' := (Set.Finite.mem_toFinset _).1 hy
      simp only [hΦ]
      rw [rhoT_natsmul p h2 xs ys hxy l hpl hy'.1
        (isUnit_red_of_mem p h2 xs ys hxy (fun h => hpm (dvd_trans h (Nat.div_dvd_of_dvd hd))) hy')]
    · rw [if_neg hd, dif_neg hd]
  rw [e1, e2]

end SectionA4e

/-! # StageA4f: the unnormalised Hecke operators U_l and U_m commute on functions on Y_p

PROVES (`SectionA4f.U_comm`): for a prime l and any m, both prime to p, `U_m (U_l f) = U_l (U_m f)` for every function f on Y_p.
Method: by StageA4e `hecke_Yp`, `U_m U_l = 24 (U_{lm} + l U_{m/l})` is a real combination of operators that are self-adjoint by
StageA4b `Tm_adjoint`, so it is self-adjoint; on the other hand `<U_m U_l f, h> = <f, U_l U_m h>` by two applications of `Tm_adjoint`.
Testing against point masses gives the identity.
DOES NOT PROVE: commutation of U_m with U_n for composite n (this needs recurrences for composite n), multiplicativity for coprime
m, n, eigenvalue bounds, the size 24 sigma(m), the normalisation by 24, or H31gt3. -/

namespace SectionA4f
open SectionA4e

variable (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)

theorem lin_left {ι : Type*} [Fintype ι] (a b h : ι → ℂ) (c L : ℂ) :
    ∑ y, (c * (a y + L * b y)) * (starRingEnd ℂ) (h y)
      = c * (∑ y, a y * (starRingEnd ℂ) (h y) + L * ∑ y, b y * (starRingEnd ℂ) (h y)) := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun y _ => by ring)

theorem lin_right {ι : Type*} [Fintype ι] (a b f : ι → ℂ) (c L : ℂ)
    (hc : (starRingEnd ℂ) c = c) (hL : (starRingEnd ℂ) L = L) :
    ∑ y, f y * (starRingEnd ℂ) (c * (a y + L * b y))
      = c * (∑ y, f y * (starRingEnd ℂ) (a y) + L * ∑ y, f y * (starRingEnd ℂ) (b y)) := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, map_mul, map_add, hc, hL]
  exact Finset.sum_congr rfl (fun y _ => by ring)

variable [Fintype (SectionA2.PGL2 p)] [Fintype (SectionA2.PGL2 p ⧸ SectionA3b.Gam p h2 xs ys hxy)]
  [Fintype (SectionA3b.Gam p h2 xs ys hxy)]

theorem U_adj (n : ℕ) (hn : ¬ p ∣ n) (f h : SectionA3b.Yp p h2 xs ys hxy → ℂ) :
    ∑ y, U p h2 xs ys hxy n hn f y * (starRingEnd ℂ) (h y)
      = ∑ y, f y * (starRingEnd ℂ) (U p h2 xs ys hxy n hn h y) :=
  SectionA4b.Tm_adjoint p h2 xs ys hxy n hn f h

/-- STAGE A4f: for a prime l (p ∤ l) and any m (p ∤ m), U_m and U_l commute on functions on Y_p. -/
theorem U_comm (l : ℕ) [Fact l.Prime] (h2l : (2 : ZMod l) ≠ 0) (xsl ysl : ZMod l)
    (hxyl : xsl ^ 2 + ysl ^ 2 = -1) (hpl : ¬ p ∣ l) (m : ℕ) (hpm : ¬ p ∣ m)
    (f : SectionA3b.Yp p h2 xs ys hxy → ℂ) :
    U p h2 xs ys hxy m hpm (U p h2 xs ys hxy l hpl f)
      = U p h2 xs ys hxy l hpl (U p h2 xs ys hxy m hpm f) := by
  classical
  have hplm : ¬ p ∣ l * m := fun h => (Nat.Prime.dvd_mul (Fact.out : p.Prime)).1 h |>.elim hpl hpm
  set A : (SectionA3b.Yp p h2 xs ys hxy → ℂ) → SectionA3b.Yp p h2 xs ys hxy → ℂ :=
    fun f => U p h2 xs ys hxy (l * m) hplm f with hA
  set B : (SectionA3b.Yp p h2 xs ys hxy → ℂ) → SectionA3b.Yp p h2 xs ys hxy → ℂ :=
    fun f y => (if hd : l ∣ m then
      U p h2 xs ys hxy (m / l) (fun h => hpm (dvd_trans h (Nat.div_dvd_of_dvd hd))) f y else 0) with hB
  have hS : ∀ f y, U p h2 xs ys hxy m hpm (U p h2 xs ys hxy l hpl f) y
      = (24 : ℂ) * (A f y + (l : ℂ) * B f y) := fun f y =>
    hecke_Yp p h2 xs ys hxy l h2l xsl ysl hxyl hpl m hpm f y
  have hBadj : ∀ f h : SectionA3b.Yp p h2 xs ys hxy → ℂ,
      ∑ y, B f y * (starRingEnd ℂ) (h y) = ∑ y, f y * (starRingEnd ℂ) (B h y) := by
    intro f h
    by_cases hd : l ∣ m
    · simp only [hB, dif_pos hd]
      exact U_adj p h2 xs ys hxy (m / l) _ f h
    · simp [hB, dif_neg hd]
  have h24 : (starRingEnd ℂ) (24 : ℂ) = 24 := map_ofNat _ 24
  have hl : (starRingEnd ℂ) (l : ℂ) = l := map_natCast _ l
  have selfadj : ∀ f h : SectionA3b.Yp p h2 xs ys hxy → ℂ,
      ∑ y, U p h2 xs ys hxy m hpm (U p h2 xs ys hxy l hpl f) y * (starRingEnd ℂ) (h y)
        = ∑ y, f y * (starRingEnd ℂ) (U p h2 xs ys hxy m hpm (U p h2 xs ys hxy l hpl h) y) := by
    intro f h
    simp only [hS]
    rw [lin_left, lin_right _ _ _ _ _ h24 hl]
    congr 2
    · exact U_adj p h2 xs ys hxy (l * m) hplm f h
    · congr 1; exact hBadj f h
  have key : ∀ f h : SectionA3b.Yp p h2 xs ys hxy → ℂ,
      ∑ y, f y * (starRingEnd ℂ) (U p h2 xs ys hxy m hpm (U p h2 xs ys hxy l hpl h) y)
        = ∑ y, f y * (starRingEnd ℂ) (U p h2 xs ys hxy l hpl (U p h2 xs ys hxy m hpm h) y) := by
    intro f h
    rw [← selfadj, U_adj p h2 xs ys hxy m hpm (U p h2 xs ys hxy l hpl f) h,
      U_adj p h2 xs ys hxy l hpl f (U p h2 xs ys hxy m hpm h)]
  funext y0
  have := key (fun y => if y = y0 then 1 else 0) f
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
  exact (starRingEnd ℂ).injective this

end SectionA4f

/-! # StageA4g: the normalised Hecke operators T_n = U_n / 24 on functions on Y_p

PROVES: `SectionA4g.Tn_rel`: for a prime l and any m, both prime to p, `T_m T_l = T_{lm} + l T_{m/l}` (the second term is 0 unless l | m),
the classical Hecke recurrence for the normalised operators; `Tn_comm`: `T_m T_l = T_l T_m` (from StageA4f).
DOES NOT PROVE: the relation for composite l, multiplicativity for coprime m, n, eigenvalue bounds, that the family of
operators is nonzero (the size 24 sigma(m) of Hm m, Stage80a, is not in this chain), or H31gt3. -/

namespace SectionA4g
open SectionA4e

variable (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)

/-- U_n is homogeneous of degree one under division by a constant -/
theorem U_div (n : ℕ) (hn : ¬ p ∣ n) (c : ℂ) (g : SectionA3b.Yp p h2 xs ys hxy → ℂ)
    (y : SectionA3b.Yp p h2 xs ys hxy) :
    U p h2 xs ys hxy n hn (fun z => g z / c) y = U p h2 xs ys hxy n hn g y / c := by
  refine Quotient.inductionOn y (fun g0 => ?_)
  rw [U_mk, U_mk, Finset.sum_div]

/-- the normalised Hecke operator T_n = U_n / 24 -/
noncomputable def Tn (n : ℕ) (hn : ¬ p ∣ n) (f : SectionA3b.Yp p h2 xs ys hxy → ℂ) :
    SectionA3b.Yp p h2 xs ys hxy → ℂ := fun y => U p h2 xs ys hxy n hn f y / 24

/-- STAGE A4g: the normalised Hecke relation `T_m T_l = T_{l m} + l T_{m/l}` -/
theorem Tn_rel (l : ℕ) [Fact l.Prime] (h2l : (2 : ZMod l) ≠ 0) (xsl ysl : ZMod l)
    (hxyl : xsl ^ 2 + ysl ^ 2 = -1) (hpl : ¬ p ∣ l) (m : ℕ) (hpm : ¬ p ∣ m)
    (f : SectionA3b.Yp p h2 xs ys hxy → ℂ) (y : SectionA3b.Yp p h2 xs ys hxy) :
    Tn p h2 xs ys hxy m hpm (Tn p h2 xs ys hxy l hpl f) y
      = Tn p h2 xs ys hxy (l * m) (fun h => (Nat.Prime.dvd_mul (Fact.out : p.Prime)).1 h |>.elim hpl hpm) f y
        + (l : ℂ) * (if hd : l ∣ m then
            Tn p h2 xs ys hxy (m / l) (fun h => hpm (dvd_trans h (Nat.div_dvd_of_dvd hd))) f y else 0) := by
  unfold Tn
  rw [U_div, SectionA4e.hecke_Yp p h2 xs ys hxy l h2l xsl ysl hxyl hpl m hpm f y]
  by_cases hd : l ∣ m
  · simp only [dif_pos hd]; ring
  · simp only [dif_neg hd]; ring

theorem Tn_comm (l : ℕ) [Fact l.Prime] (h2l : (2 : ZMod l) ≠ 0) (xsl ysl : ZMod l)
    (hxyl : xsl ^ 2 + ysl ^ 2 = -1) (hpl : ¬ p ∣ l) (m : ℕ) (hpm : ¬ p ∣ m)
    [Fintype (SectionA2.PGL2 p)] [Fintype (SectionA2.PGL2 p ⧸ SectionA3b.Gam p h2 xs ys hxy)]
    [Fintype (SectionA3b.Gam p h2 xs ys hxy)]
    (f : SectionA3b.Yp p h2 xs ys hxy → ℂ) :
    Tn p h2 xs ys hxy m hpm (Tn p h2 xs ys hxy l hpl f)
      = Tn p h2 xs ys hxy l hpl (Tn p h2 xs ys hxy m hpm f) := by
  funext y
  unfold Tn
  rw [U_div, U_div]
  have := congrFun (SectionA4f.U_comm p h2 xs ys hxy l h2l xsl ysl hxyl hpl m hpm f) y
  rw [this]

end SectionA4g

/-! # StageA4h: T_1 is the identity, and every T_n (n odd, prime to p) commutes with every T_m (m prime to p)

PROVES: `U_one`: U_1 f = 24 f (the 24 Hurwitz units all act through Gamma_p); `Tn_one`: T_1 f = f; `comm_all`: for odd n and any m, both
prime to p, `T_m (T_n f) = T_n (T_m f)`.  Method: strong induction on n.  For n > 1 take the least prime l | n (odd), n = l m';
StageA4g `Tn_rel` gives T_n = T_{m'} T_l - l T_{m'/l} (second term only if l | m'), and the induction hypothesis, StageA4g `Tn_comm`
and linearity (`Tn_sub`) transport T_m through each term.
DOES NOT PROVE: coprime multiplicativity T_{mn} = T_m T_n, eigenvalue bounds, that T_n is nonzero (size of Hm n), or H31gt3.
The restriction to odd n is because the Hecke prime needs 2 invertible mod l (an input of `hecke_Yp`); even n is not covered. -/

namespace SectionA4h
open SectionA4e

variable (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)

theorem U_sub (n : ℕ) (hn : ¬ p ∣ n) (a b : SectionA3b.Yp p h2 xs ys hxy → ℂ) (c : ℂ)
    (y : SectionA3b.Yp p h2 xs ys hxy) :
    U p h2 xs ys hxy n hn (fun z => a z - c * b z) y
      = U p h2 xs ys hxy n hn a y - c * U p h2 xs ys hxy n hn b y := by
  refine Quotient.inductionOn y (fun g0 => ?_)
  rw [U_mk, U_mk, U_mk, Finset.sum_sub_distrib, Finset.mul_sum]

theorem U_zero (n : ℕ) (hn : ¬ p ∣ n) (y : SectionA3b.Yp p h2 xs ys hxy) :
    U p h2 xs ys hxy n hn (fun _ => 0) y = 0 := by
  refine Quotient.inductionOn y (fun g0 => ?_)
  rw [U_mk]; simp

theorem Tn_sub (n : ℕ) (hn : ¬ p ∣ n) (a b : SectionA3b.Yp p h2 xs ys hxy → ℂ) (c : ℂ)
    (y : SectionA3b.Yp p h2 xs ys hxy) :
    SectionA4g.Tn p h2 xs ys hxy n hn (fun z => a z - c * b z) y
      = SectionA4g.Tn p h2 xs ys hxy n hn a y - c * SectionA4g.Tn p h2 xs ys hxy n hn b y := by
  unfold SectionA4g.Tn
  rw [U_sub]; ring

theorem Tn_zero (n : ℕ) (hn : ¬ p ∣ n) (y : SectionA3b.Yp p h2 xs ys hxy) :
    SectionA4g.Tn p h2 xs ys hxy n hn (fun _ => 0) y = 0 := by
  unfold SectionA4g.Tn
  rw [U_zero]; simp

theorem rhoT_unit_mem {x : Quaternion ℚ} (hx : x ∈ Section75a.Hn 1) :
    rhoT p xs ys x ∈ SectionA3b.Gam p h2 xs ys hxy := by
  have hQ : QH x := hx.1
  have hn : Quaternion.normSq x = 1 := by simpa using hx.2
  have hx0 : x ≠ 0 := by
    intro h; rw [h] at hn; simp at hn
  let u : (Quaternion ℚ)ˣ := Units.mk0 x hx0
  have hu : u ∈ SectionA3a2.HurU := (SectionA3a2.mem_iff u).2 ⟨hQ, hn⟩
  refine ⟨⟨u, hu⟩, ?_⟩
  have hred : IsUnit (Section74b.red p xs ys x) :=
    SectionA1.red_isUnit p h2 xs ys hxy hQ 1 (by simpa using hn) (SectionA3a.not_dvd_one_p p)
  rw [rhoT_of_unit p xs ys hred]
  change SectionA3a2.rhoFun p h2 xs ys hxy ⟨u, hu⟩ = _
  unfold SectionA3a2.rhoFun
  congr 1

theorem U_one (hp1 : ¬ p ∣ 1) (f : SectionA3b.Yp p h2 xs ys hxy → ℂ) (y : SectionA3b.Yp p h2 xs ys hxy) :
    U p h2 xs ys hxy 1 hp1 f y = 24 * f y := by
  refine Quotient.inductionOn y (fun g0 => ?_)
  rw [U_mk]
  have : ∀ x ∈ (Section77a.Hn_finite 1).toFinset,
      f (Quotient.mk (QuotientGroup.rightRel (SectionA3b.Gam p h2 xs ys hxy)) (rhoT p xs ys x * g0))
        = f (Quotient.mk (QuotientGroup.rightRel (SectionA3b.Gam p h2 xs ys hxy)) g0) := by
    intro x hx
    have hx' := (Set.Finite.mem_toFinset _).1 hx
    congr 1
    apply Quotient.sound
    apply QuotientGroup.rightRel_apply.2
    simpa using rhoT_unit_mem p h2 xs ys hxy hx'
  rw [Finset.sum_congr rfl this, Finset.sum_const, SectionA4d.Hn_one_card]
  simp

end SectionA4h

namespace SectionA4h
open SectionA4e

variable (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)

theorem Tn_one (hp1 : ¬ p ∣ 1) (f : SectionA3b.Yp p h2 xs ys hxy → ℂ) :
    SectionA4g.Tn p h2 xs ys hxy 1 hp1 f = f := by
  funext y
  unfold SectionA4g.Tn
  rw [U_one]; ring

theorem comm_all [Fintype (SectionA2.PGL2 p)] [Fintype (SectionA2.PGL2 p ⧸ SectionA3b.Gam p h2 xs ys hxy)]
    [Fintype (SectionA3b.Gam p h2 xs ys hxy)] (n : ℕ) :
    Odd n → ∀ (hpn : ¬ p ∣ n) (m : ℕ) (hpm : ¬ p ∣ m) (f : SectionA3b.Yp p h2 xs ys hxy → ℂ),
      SectionA4g.Tn p h2 xs ys hxy m hpm (SectionA4g.Tn p h2 xs ys hxy n hpn f)
        = SectionA4g.Tn p h2 xs ys hxy n hpn (SectionA4g.Tn p h2 xs ys hxy m hpm f) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hodd hpn m hpm f
  by_cases hn1 : n = 1
  · subst hn1
    rw [Tn_one, Tn_one]
  · have hlp : n.minFac.Prime := Nat.minFac_prime hn1
    have hdl : n.minFac ∣ n := Nat.minFac_dvd n
    generalize n.minFac = l at hlp hdl
    haveI : Fact l.Prime := ⟨hlp⟩
    obtain ⟨m', hm'⟩ := hdl
    have hdl : l ∣ n := ⟨m', hm'⟩
    have hlodd : Odd l := Odd.of_dvd_nat hodd hdl
    have h2l : (2 : ZMod l) ≠ 0 := by
      intro h
      have h' : ((2 : ℕ) : ZMod l) = 0 := by exact_mod_cast h
      have hd : l ∣ 2 := (ZMod.natCast_eq_zero_iff 2 l).1 h'
      have : l = 2 := (Nat.prime_dvd_prime_iff_eq hlp Nat.prime_two).1 hd
      rw [this] at hlodd; exact absurd hlodd (by decide)
    obtain ⟨xsl, ysl, hxyl⟩ := ZMod.sq_add_sq l (-1)
    have hm'pos : 0 < m' := by
      rcases Nat.eq_zero_or_pos m' with h | h
      · rw [h, mul_zero] at hm'; rw [hm'] at hodd; exact absurd hodd (by decide)
      · exact h
    have hlt : m' < n := by
      rw [hm']; have := hlp.two_le; nlinarith
    have hpl : ¬ p ∣ l := fun h => hpn (dvd_trans h hdl)
    have hpm' : ¬ p ∣ m' := fun h => hpn (by rw [hm']; exact Dvd.dvd.mul_left h l)
    have hodd' : Odd m' := (Nat.odd_mul.1 (by rw [← hm']; exact hodd)).2
    have hE : ∀ g : SectionA3b.Yp p h2 xs ys hxy → ℂ,
        SectionA4g.Tn p h2 xs ys hxy n hpn g = fun y =>
          SectionA4g.Tn p h2 xs ys hxy m' hpm' (SectionA4g.Tn p h2 xs ys hxy l hpl g) y
            - (l : ℂ) * (if hd : l ∣ m' then
                SectionA4g.Tn p h2 xs ys hxy (m' / l) (fun h => hpm' (dvd_trans h (Nat.div_dvd_of_dvd hd))) g y
                else 0) := by
      intro g
      funext y
      have := SectionA4g.Tn_rel p h2 xs ys hxy l h2l xsl ysl hxyl hpl m' hpm' g y
      have e : (SectionA4g.Tn p h2 xs ys hxy (l * m') (fun h => (Nat.Prime.dvd_mul (Fact.out : p.Prime)).1 h |>.elim hpl hpm') g y)
          = SectionA4g.Tn p h2 xs ys hxy n hpn g y := by
        have key : ∀ k (hk : ¬ p ∣ k), k = n → SectionA4g.Tn p h2 xs ys hxy k hk g y
            = SectionA4g.Tn p h2 xs ys hxy n hpn g y := by
          intro k hk h; subst h; rfl
        exact key _ _ hm'.symm
      rw [e] at this
      rw [this]; ring
    have e3 : ∀ g : SectionA3b.Yp p h2 xs ys hxy → ℂ, ∀ y,
        SectionA4g.Tn p h2 xs ys hxy m hpm (fun z => if hd : l ∣ m' then
          SectionA4g.Tn p h2 xs ys hxy (m' / l) (fun h => hpm' (dvd_trans h (Nat.div_dvd_of_dvd hd))) g z else 0) y
        = (if hd : l ∣ m' then
          SectionA4g.Tn p h2 xs ys hxy (m' / l) (fun h => hpm' (dvd_trans h (Nat.div_dvd_of_dvd hd)))
            (SectionA4g.Tn p h2 xs ys hxy m hpm g) y else 0) := by
      intro g y
      by_cases hd : l ∣ m'
      · simp only [dif_pos hd]
        have hq : m' / l < n := lt_of_le_of_lt (Nat.div_le_self _ _) hlt
        have hqo : Odd (m' / l) := Odd.of_dvd_nat hodd' (Nat.div_dvd_of_dvd hd)
        exact congrFun (ih (m' / l) hq hqo _ m hpm g) y
      · simp only [dif_neg hd]
        exact Tn_zero p h2 xs ys hxy m hpm y
    have e1 := ih m' hlt hodd' hpm' m hpm (SectionA4g.Tn p h2 xs ys hxy l hpl f)
    have e2 := SectionA4g.Tn_comm p h2 xs ys hxy l h2l xsl ysl hxyl hpl m hpm f
    funext y
    rw [hE f]
    rw [Tn_sub p h2 xs ys hxy m hpm _ _ _ y, e3 f y]
    rw [hE (SectionA4g.Tn p h2 xs ys hxy m hpm f)]
    rw [congrFun e1 y, e2]

end SectionA4h

/-! # StageA4i: multiplicativity of the normalised Hecke operators for coprime indices

PROVES (`SectionA4i.mult`): for odd n and any m with gcd(m, n) = 1, both prime to p, `T_{mn} f = T_m (T_n f)` for every function f on Y_p.
Method: strong induction on n.  Write n = l n' with l the least prime factor (odd); StageA4g `Tn_rel` expresses T_n and T_{mn} through
T_l with the same correction term, l not dividing m makes the correction terms correspond, and the induction hypothesis applies to
n' and n'/l.  `Tn_split` is the recurrence solved for T_n.
DOES NOT PROVE: eigenvalue bounds, that T_n is nonzero (size of Hm n, Stage80a), the case of even n, or H31gt3. -/

namespace SectionA4i
open SectionA4e

variable (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)

theorem Tn_congr {k n : ℕ} (hk : ¬ p ∣ k) (hn : ¬ p ∣ n) (h : k = n)
    (g : SectionA3b.Yp p h2 xs ys hxy → ℂ) :
    SectionA4g.Tn p h2 xs ys hxy k hk g = SectionA4g.Tn p h2 xs ys hxy n hn g := by
  subst h; rfl

/-- the recurrence solved for T_n, n = l m' -/
theorem Tn_split (l : ℕ) [Fact l.Prime] (h2l : (2 : ZMod l) ≠ 0) (xsl ysl : ZMod l)
    (hxyl : xsl ^ 2 + ysl ^ 2 = -1) (hpl : ¬ p ∣ l) (m' n : ℕ) (hn : n = l * m')
    (hpn : ¬ p ∣ n) (hpm' : ¬ p ∣ m') (g : SectionA3b.Yp p h2 xs ys hxy → ℂ) :
    SectionA4g.Tn p h2 xs ys hxy n hpn g = fun y =>
      SectionA4g.Tn p h2 xs ys hxy m' hpm' (SectionA4g.Tn p h2 xs ys hxy l hpl g) y
        - (l : ℂ) * (if hd : l ∣ m' then
            SectionA4g.Tn p h2 xs ys hxy (m' / l) (fun h => hpm' (dvd_trans h (Nat.div_dvd_of_dvd hd))) g y
            else 0) := by
  funext y
  have := SectionA4g.Tn_rel p h2 xs ys hxy l h2l xsl ysl hxyl hpl m' hpm' g y
  have e := congrFun (Tn_congr p h2 xs ys hxy
    (fun h => (Nat.Prime.dvd_mul (Fact.out : p.Prime)).1 h |>.elim hpl hpm') hpn hn.symm g) y
  rw [e] at this
  rw [this]; ring

theorem mult [Fintype (SectionA2.PGL2 p)] [Fintype (SectionA2.PGL2 p ⧸ SectionA3b.Gam p h2 xs ys hxy)]
    [Fintype (SectionA3b.Gam p h2 xs ys hxy)] (n : ℕ) :
    Odd n → ∀ (m : ℕ), Nat.Coprime m n → ∀ (hpn : ¬ p ∣ n) (hpm : ¬ p ∣ m) (hpmn : ¬ p ∣ m * n)
      (f : SectionA3b.Yp p h2 xs ys hxy → ℂ),
      SectionA4g.Tn p h2 xs ys hxy (m * n) hpmn f
        = SectionA4g.Tn p h2 xs ys hxy m hpm (SectionA4g.Tn p h2 xs ys hxy n hpn f) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hodd m hcop hpn hpm hpmn f
  by_cases hn1 : n = 1
  · subst hn1
    rw [SectionA4h.Tn_one]
    exact Tn_congr p h2 xs ys hxy hpmn hpm (mul_one m) f
  · have hlp : n.minFac.Prime := Nat.minFac_prime hn1
    have hdl : n.minFac ∣ n := Nat.minFac_dvd n
    generalize n.minFac = l at hlp hdl
    haveI : Fact l.Prime := ⟨hlp⟩
    obtain ⟨n', hn'⟩ := hdl
    have hdl : l ∣ n := ⟨n', hn'⟩
    have hlodd : Odd l := Odd.of_dvd_nat hodd hdl
    have h2l : (2 : ZMod l) ≠ 0 := by
      intro h
      have h' : ((2 : ℕ) : ZMod l) = 0 := by exact_mod_cast h
      have hd : l ∣ 2 := (ZMod.natCast_eq_zero_iff 2 l).1 h'
      have : l = 2 := (Nat.prime_dvd_prime_iff_eq hlp Nat.prime_two).1 hd
      rw [this] at hlodd; exact absurd hlodd (by decide)
    obtain ⟨xsl, ysl, hxyl⟩ := ZMod.sq_add_sq l (-1)
    have hn'pos : 0 < n' := by
      rcases Nat.eq_zero_or_pos n' with h | h
      · rw [h, mul_zero] at hn'; rw [hn'] at hodd; exact absurd hodd (by decide)
      · exact h
    have hlt : n' < n := by
      rw [hn']; have := hlp.two_le; nlinarith
    have hpl : ¬ p ∣ l := fun h => hpn (dvd_trans h hdl)
    have hpn' : ¬ p ∣ n' := fun h => hpn (by rw [hn']; exact Dvd.dvd.mul_left h l)
    have hodd' : Odd n' := (Nat.odd_mul.1 (by rw [← hn']; exact hodd)).2
    have hcl : ¬ l ∣ m := fun h => by
      have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_right hdl hcop |>.symm) h
      exact hlp.one_lt.ne' this
    have hcn' : Nat.Coprime m n' := Nat.Coprime.coprime_dvd_right (Dvd.intro_left l hn'.symm) hcop
    have hpmn' : ¬ p ∣ m * n' := fun h => (Nat.Prime.dvd_mul (Fact.out : p.Prime)).1 h |>.elim hpm hpn'
    have hsplitL := Tn_split p h2 xs ys hxy l h2l xsl ysl hxyl hpl (m * n') (m * n)
      (by rw [hn']; ring) hpmn hpmn' f
    have hsplitR := Tn_split p h2 xs ys hxy l h2l xsl ysl hxyl hpl n' n hn' hpn hpn' f
    have ihA := ih n' hlt hodd' m hcn' hpn' hpm hpmn' (SectionA4g.Tn p h2 xs ys hxy l hpl f)
    rw [hsplitL, hsplitR]
    funext y
    rw [SectionA4h.Tn_sub p h2 xs ys hxy m hpm _ _ _ y, ← congrFun ihA y]
    congr 2
    by_cases hd : l ∣ n'
    · have hdm : l ∣ m * n' := Dvd.dvd.mul_left hd m
      simp only [dif_pos hd, dif_pos hdm]
      have hq : n' / l < n := lt_of_le_of_lt (Nat.div_le_self _ _) hlt
      have hqo : Odd (n' / l) := Odd.of_dvd_nat hodd' (Nat.div_dvd_of_dvd hd)
      have hcq : Nat.Coprime m (n' / l) :=
        Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd hd) hcn'
      have hpq : ¬ p ∣ n' / l := fun h => hpn' (dvd_trans h (Nat.div_dvd_of_dvd hd))
      have hpmq : ¬ p ∣ m * (n' / l) := fun h =>
        (Nat.Prime.dvd_mul (Fact.out : p.Prime)).1 h |>.elim hpm hpq
      have e := ih (n' / l) hq hqo m hcq hpq hpm hpmq f
      rw [← congrFun e y]
      exact congrFun (Tn_congr p h2 xs ys hxy _ hpmq (by rw [Nat.mul_div_assoc _ hd]) f) y
    · have hdm : ¬ l ∣ m * n' := fun h =>
        (Nat.Prime.dvd_mul hlp).1 h |>.elim hcl hd
      simp only [dif_neg hd, dif_neg hdm]
      exact (SectionA4h.Tn_zero p h2 xs ys hxy m hpm y).symm

end SectionA4i

namespace Section79a

/-! Stage79a (UNTESTED when written).  The Hecke relation for the divisor sum sg = sigma_1, over the naturals:
   sg(p m) + (if p | m then p * sg(m/p) else 0) = (p+1) * sg m      for p prime, m not 0.
Hand derivation: write m = p^e v with p not dividing v, so sg is multiplicative across p^e and v.  With
S(e) = sg(p^e) = 1 + p + ... + p^e one has p S(e) + 1 = S(e+1); then S(f+2) + p S(f) = (p+1) S(f+1) (from the two
instances for e=f+1 and e=f), and S(1) = p+1 handles e=0.  DOES NOT PROVE anything about Hurwitz quaternions.
sg is definitionally Section51.sig (both are ArithmeticFunction.sigma 1 m). -/

def sg (m : ℕ) : ℕ := ArithmeticFunction.sigma 1 m

lemma sg_pp {p : ℕ} (hp : p.Prime) (e : ℕ) :
    sg (p ^ e) = ∑ k ∈ Finset.range (e + 1), p ^ k := by
  unfold sg
  exact ArithmeticFunction.sigma_one_apply_prime_pow hp

lemma sg_mul {a b : ℕ} (h : Nat.Coprime a b) : sg (a * b) = sg a * sg b :=
  (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime h

lemma sg_one : sg 1 = 1 := (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_one

lemma geom_sum (p e : ℕ) :
    p * (∑ k ∈ Finset.range (e + 1), p ^ k) + 1 = ∑ k ∈ Finset.range (e + 1 + 1), p ^ k := by
  induction e with
  | zero => simp [Finset.sum_range_succ, add_comm]
  | succ e ih =>
    have h1 : ∑ k ∈ Finset.range (e + 1 + 1 + 1), p ^ k = ∑ k ∈ Finset.range (e + 1 + 1), p ^ k + p ^ (e + 1 + 1) :=
      Finset.sum_range_succ _ _
    have h2 : ∑ k ∈ Finset.range (e + 1 + 1), p ^ k = ∑ k ∈ Finset.range (e + 1), p ^ k + p ^ (e + 1) :=
      Finset.sum_range_succ _ _
    rw [h2] at ih
    rw [h1, h2]
    have h3 : p * p ^ (e + 1) = p ^ (e + 1 + 1) := by ring
    nlinarith [ih, h3]

lemma geom_sg {p : ℕ} (hp : p.Prime) (e : ℕ) : p * sg (p ^ e) + 1 = sg (p ^ (e + 1)) := by
  rw [sg_pp hp e, sg_pp hp (e + 1)]
  exact geom_sum p e

lemma sg_prime {p : ℕ} (hp : p.Prime) : sg p = p + 1 := by
  have := geom_sg hp 0
  rw [pow_zero, sg_one, zero_add, pow_one] at this
  omega

lemma pp_hecke {p : ℕ} (hp : p.Prime) (f : ℕ) :
    sg (p ^ (f + 2)) + p * sg (p ^ f) = (p + 1) * sg (p ^ (f + 1)) := by
  have a : p * sg (p ^ (f + 1)) + 1 = sg (p ^ (f + 2)) := geom_sg hp (f + 1)
  have b : p * sg (p ^ f) + 1 = sg (p ^ (f + 1)) := geom_sg hp f
  nlinarith [a, b]

theorem sg_hecke (p : ℕ) (hp : p.Prime) (m : ℕ) (hm : m ≠ 0) :
    sg (p * m) + (if p ∣ m then p * sg (m / p) else 0) = (p + 1) * sg m := by
  obtain ⟨e, v, hv, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm p hp.ne_one
  have hc : ∀ j : ℕ, Nat.Coprime (p ^ j) v := fun j =>
    Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd hp).2 hv)
  rcases Nat.eq_zero_or_pos e with he | he
  · subst he
    simp only [pow_zero, one_mul]
    rw [if_neg hv, add_zero]
    have hc1 : Nat.Coprime p v := (Nat.Prime.coprime_iff_not_dvd hp).2 hv
    rw [sg_mul hc1, sg_prime hp]
  · obtain ⟨f, rfl⟩ : ∃ f, e = f + 1 := ⟨e - 1, by omega⟩
    have hdvd : p ∣ p ^ (f + 1) * v := dvd_mul_of_dvd_left (dvd_pow_self p (Nat.succ_ne_zero f)) v
    have hdiv : p ^ (f + 1) * v / p = p ^ f * v :=
      Nat.div_eq_of_eq_mul_left hp.pos (by ring)
    have h1 : p * (p ^ (f + 1) * v) = p ^ (f + 2) * v := by ring
    rw [if_pos hdvd, hdiv, h1, sg_mul (hc (f + 2)), sg_mul (hc f), sg_mul (hc (f + 1))]
    have H := pp_hecke hp f
    calc sg (p ^ (f + 2)) * sg v + p * (sg (p ^ f) * sg v)
        = (sg (p ^ (f + 2)) + p * sg (p ^ f)) * sg v := by ring
      _ = (p + 1) * (sg (p ^ (f + 1)) * sg v) := by rw [H]; ring

end Section79a

namespace Section79b
open Section71d

/-! Stage79b (UNTESTED when written).  PROVES, if it compiles: for every odd m, the number of Hurwitz quaternions of norm m
equals 24 * sg m.  Strong induction on m: m = 1 is units_QH_count; for m > 1 let p = minFac m (odd, since m is odd),
m = p m'; Stage78c.recur at m' and Section79a.sg_hecke give  h(p m') + [p|m'] p h(m'/p) = 24((p+1) sg m'), and the
induction hypothesis on m' and m'/p finishes.  DOES NOT PROVE HJac: |FourSq.R(2m)| = h(m) still needs the
numerator <-> quaternion bridge and the norm-doubling bijection (Section75a.double_card). -/

theorem h_one : (Section75a.Hn 1).ncard = 24 := by
  have : Section75a.Hn 1 = {u : Quaternion ℚ | QH u ∧ Quaternion.normSq u = 1} := by
    ext x
    simp [Section75a.Hn]
  rw [this]
  exact Section73e.units_QH_count

theorem recur_p (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (m : ℕ) :
    (p + 1) * (Section75a.Hn m).ncard = (Section75a.Hn (p * m)).ncard +
      (if p ∣ m then p * (Section75a.Hn (m / p)).ncard else 0) := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (ZMod p) p] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1 h')
  obtain ⟨xs, ys, hxy⟩ := ZMod.sq_add_sq p (-1)
  exact Section78c.recur p h2 xs ys hxy m

theorem h_eq (m : ℕ) (hm : m % 2 = 1) : (Section75a.Hn m).ncard = 24 * Section79a.sg m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases h1 : m = 1
    · subst h1
      rw [h_one, Section79a.sg_one]
    · have hm0 : m ≠ 0 := by omega
      have hpr : (Nat.minFac m).Prime := Nat.minFac_prime h1
      haveI : Fact (Nat.minFac m).Prime := ⟨hpr⟩
      obtain ⟨m', hm'⟩ := Nat.minFac_dvd m
      set p := Nat.minFac m with hpdef
      have hp2 : p ≠ 2 := by
        intro h
        rw [h] at hm'
        omega
      have hpos : 0 < p := hpr.pos
      have hm'0 : m' ≠ 0 := by
        rintro rfl
        omega
      have hm'odd : m' % 2 = 1 := by
        rcases Nat.mod_two_eq_zero_or_one m' with h | h
        · exfalso
          have : m % 2 = 0 := by rw [hm', Nat.mul_mod, h]; simp
          omega
        · exact h
      have hlt : m' < m := by
        rw [hm']
        have : 2 ≤ p := hpr.two_le
        nlinarith [Nat.pos_of_ne_zero hm'0]
      have ihm' := ih m' hlt hm'odd
      have hrec := recur_p p hp2 m'
      have hsg := Section79a.sg_hecke p hpr m' hm'0
      rw [hm']
      by_cases hd : p ∣ m'
      · rw [if_pos hd] at hrec hsg
        obtain ⟨q, hq⟩ := hd
        have hqlt : m' / p < m := by
          calc m' / p ≤ m' := Nat.div_le_self _ _
            _ < m := hlt
        have hqodd : (m' / p) % 2 = 1 := by
          have hdq : m' / p = q := by
            rw [hq]; exact Nat.mul_div_cancel_left q hpos
          rw [hdq]
          rcases Nat.mod_two_eq_zero_or_one q with h | h
          · exfalso
            have : m' % 2 = 0 := by rw [hq, Nat.mul_mod, h]; simp
            omega
          · exact h
        have ihq := ih (m' / p) hqlt hqodd
        rw [ihq, ihm'] at hrec
        nlinarith [hrec, hsg]
      · rw [if_neg hd] at hrec hsg
        rw [ihm'] at hrec
        nlinarith [hrec, hsg]

end Section79b

/-! # StageA4j: the constant function is an eigenfunction, T_m 1 = sigma(m) 1

PROVES (`SectionA4j.Tn_const`): for odd m prime to p, the normalised Hecke operator on Y_p sends the constant function 1 to sigma(m) times
1 (`U_const`: U_m 1 = 24 sigma(m)).  Input: the count of Hurwitz quaternions of norm m, `Section79b.h_eq`, copied verbatim with
`Section79a` from Stage80a (lines 1953 to 2109; compiled clean there).
This is the first of the two exceptional modes named in the ledger (the other, T_m chi = (m/p) sigma(m) chi, is not done here).
DOES NOT PROVE: the bound on T_m for the orthogonal complement (Lemma 3.2: needs Jacquet-Langlands and Ramanujan-Petersson, not in
Mathlib), the chi eigenvalue, or H31gt3. -/

namespace SectionA4j
open SectionA4e

variable (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)

/-- U_m applied to the constant function 1 is the number of Hurwitz quaternions of norm m, i.e. 24 sigma(m) for odd m. -/
theorem U_const (m : ℕ) (hm : m % 2 = 1) (hpm : ¬ p ∣ m) (y : SectionA3b.Yp p h2 xs ys hxy) :
    U p h2 xs ys hxy m hpm (fun _ => (1 : ℂ)) y = 24 * (Section79a.sg m : ℂ) := by
  refine Quotient.inductionOn y (fun g0 => ?_)
  rw [U_mk]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  have e : ((Section77a.Hn_finite m).toFinset.card) = (Section75a.Hn m).ncard := by
    rw [← Set.ncard_coe_finset, Set.Finite.coe_toFinset]
  rw [e, Section79b.h_eq m hm]
  push_cast; ring

/-- STAGE A4j: the constant function is an eigenfunction, T_m 1 = sigma(m) 1 (odd m prime to p). -/
theorem Tn_const (m : ℕ) (hm : m % 2 = 1) (hpm : ¬ p ∣ m) (y : SectionA3b.Yp p h2 xs ys hxy) :
    SectionA4g.Tn p h2 xs ys hxy m hpm (fun _ => (1 : ℂ)) y = (Section79a.sg m : ℂ) := by
  unfold SectionA4g.Tn
  rw [U_const p h2 xs ys hxy m hm hpm y]; ring

end SectionA4j

#print axioms SectionA4j.Tn_const

import Mathlib

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

#print axioms Section74a.psi_one
#print axioms Section74a.psi_mul
#print axioms Section74a.psi_det
#print axioms Section74a.psi_eq_zero

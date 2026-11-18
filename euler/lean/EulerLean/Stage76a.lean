import Mathlib

/-! # Stage76a: line keys for 2x2 matrices over a field (UNTESTED when written)

WHAT THIS FILE PROVES, if it compiles.  Over any field F, key vectors kvF none = (0,1), kvF (some t) = (1,t) represent the
p+1 lines when F = F_p.  A matrix M "lies in the key k" (InKey) when both columns are multiples of the key vector.
 * indep: distinct keys give independent vectors, v.1 w.2 - v.2 w.1 != 0;
 * key_unique: a matrix lying in two keys with independent vectors is 0;
 * key_exists: a nonzero matrix with det = 0 lies in some key.
Hand derivation: columns of M are (M00,M10) and (M01,M11).  If M00 != 0 take t = M10/M00, r = M00, s = M01 (det = 0 gives
M11 = M01 t).  If M00 = 0 and M10 != 0 then det = -M01 M10 = 0 forces M01 = 0 and the key is (0,1).  If M00 = M10 = 0 the
nonzero column is (M01,M11); take t = M11/M01 if M01 != 0, else key (0,1).
DOES NOT PROVE: anything about Hurwitz elements; that connection is the next stage. -/

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

#print axioms Section76a.indep
#print axioms Section76a.key_unique
#print axioms Section76a.key_exists

import StageA4o

namespace EDb6
open SectionA4o

/-- α(x) = x · (1+i)⁻¹ = x (1-i)/2 for the quaternion x = x0 + x1 i + x2 j + x3 k -/
noncomputable def alphaOf (x : Fin 4 → ℤ) : Quaternion ℚ :=
  ⟨((x 0 : ℚ) + x 1) / 2, ((x 1 : ℚ) - x 0) / 2, ((x 2 : ℚ) - x 3) / 2, ((x 2 : ℚ) + x 3) / 2⟩

theorem alpha_mul (x : Fin 4 → ℤ) :
    alphaOf x * qci 1 1 = ⟨(x 0 : ℚ), (x 1 : ℚ), (x 2 : ℚ), (x 3 : ℚ)⟩ := by
  ext <;> simp [alphaOf, qci] <;> ring

theorem alpha_inj {x y : Fin 4 → ℤ} (h : alphaOf x = alphaOf y) : x = y := by
  have h1 := alpha_mul x
  have h2 := alpha_mul y
  rw [h] at h1
  have h3 : (⟨(x 0 : ℚ), (x 1 : ℚ), (x 2 : ℚ), (x 3 : ℚ)⟩ : Quaternion ℚ) = ⟨(y 0 : ℚ), (y 1 : ℚ), (y 2 : ℚ), (y 3 : ℚ)⟩ :=
    h1.symm.trans h2
  have e0 := congrArg QuaternionAlgebra.re h3
  have e1 := congrArg QuaternionAlgebra.imI h3
  have e2 := congrArg QuaternionAlgebra.imJ h3
  have e3 := congrArg QuaternionAlgebra.imK h3
  simp at e0 e1 e2 e3
  funext i; fin_cases i <;> simp [e0, e1, e2, e3]

theorem alpha_mem (m : ℕ) (x : Fin 4 → ℤ) (h01 : (x 0 + x 1) % 2 = 1) (h23 : (x 2 + x 3) % 2 = 1)
    (hn : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 = ((2 * m : ℕ) : ℤ)) :
    alphaOf x ∈ Section75a.Hn m := by
  refine ⟨Or.inr ?_, ?_⟩
  · obtain ⟨a, ha⟩ : ∃ a : ℤ, x 0 + x 1 = 2 * a + 1 := ⟨(x 0 + x 1) / 2, by omega⟩
    obtain ⟨b, hb⟩ : ∃ b : ℤ, x 1 - x 0 = 2 * b + 1 := ⟨(x 1 - x 0) / 2, by omega⟩
    obtain ⟨c, hc⟩ : ∃ c : ℤ, x 2 - x 3 = 2 * c + 1 := ⟨(x 2 - x 3) / 2, by omega⟩
    obtain ⟨d, hd⟩ : ∃ d : ℤ, x 2 + x 3 = 2 * d + 1 := ⟨(x 2 + x 3) / 2, by omega⟩
    refine ⟨a, b, c, d, ?_, ?_, ?_, ?_⟩
    · simp only [alphaOf]
      have : ((x 0 : ℚ) + x 1) = 2 * a + 1 := by exact_mod_cast ha
      rw [this]; ring
    · simp only [alphaOf]
      have : ((x 1 : ℚ) - x 0) = 2 * b + 1 := by exact_mod_cast hb
      rw [this]; ring
    · simp only [alphaOf]
      have : ((x 2 : ℚ) - x 3) = 2 * c + 1 := by exact_mod_cast hc
      rw [this]; ring
    · simp only [alphaOf]
      have : ((x 2 : ℚ) + x 3) = 2 * d + 1 := by exact_mod_cast hd
      rw [this]; ring
  · rw [Quaternion.normSq_def']
    have hq : (x 0 : ℚ) ^ 2 + (x 1 : ℚ) ^ 2 + (x 2 : ℚ) ^ 2 + (x 3 : ℚ) ^ 2 = 2 * (m : ℚ) := by
      exact_mod_cast hn
    simp only [alphaOf]
    linear_combination hq / 2

end EDb6
#print axioms EDb6.alpha_mem
#print axioms EDb6.alpha_inj

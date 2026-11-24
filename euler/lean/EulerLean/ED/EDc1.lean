import EDcDefs

/-!
# EDc1.lean   (PRODUCTION-FACING; UNTESTED until compiled by CI)

Phase 8B.  Chebyshev (2.04) copies of the production one-vector chain, so that the A-shaped hypothesis can be
consumed.  Imports `EDcDefs` (hence `EDc0`, `Stage83cut`, `StageA4o`).  No `EDb8`, no `EDcert*`.

Every proof is a textual copy of the production proof (`SectionA4m.lemma32_of_prime_case`, `SectionA4m2.lemma32_of_prime_case_Yp`,
`SectionA4n.quad_bound`, `pointwise_Yp`, `SectionA4o.pointwise_OK`, `pointwise_Kp`, all in `euler/lean/EulerLean/StageA4o.lean`) with exactly these changes:
  * a parameter `X ≥ 1`; prime-case bound `2 X √l ‖f‖`, required ONLY for primes `l ≡ 3 (mod 4)`;
  * an extra hypothesis `hmq`: every prime factor of the index `m` is `≡ 3 (mod 4)`;
  * `S_norm_le`-reduction ⟶ `EDc0.reduction_cheb`; the divisor bound `τ(m)` ⟶ `EDc0.Amaj X m`.
Nothing is assumed beyond `hprime`.  `HPrime204Restricted` is NOT used here (it is consumed in EDc2).
-/

namespace EDc1

open SectionA4l SectionA4m SectionA4m2 SectionA4n SectionA4o

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- Chebyshev version of `SectionA4m.lemma32_of_prime_case`. -/
theorem lemma32_cheb (p : ℕ) (hp : p.Prime) (X : ℝ) (hX : 1 ≤ X) (u v : E) (T : ℕ → E →ₗ[ℂ] E)
    (h1 : T 1 = LinearMap.id)
    (hmul : ∀ m n, Adm p m → Adm p n → Nat.Coprime m n → T (m * n) = T m ∘ₗ T n)
    (hrec : ∀ l, l.Prime → Adm p l → ∀ k : ℕ,
      T (l ^ (k + 2)) = T l ∘ₗ T (l ^ (k + 1)) - (l : ℂ) • T (l ^ k))
    (hsymm : ∀ n, Adm p n → (T n).IsSymmetric)
    (hu : ∀ n, Adm p n → ∃ a : ℝ, T n u = (a : ℂ) • u)
    (hv : ∀ n, Adm p n → ∃ a : ℝ, T n v = (a : ℂ) • v)
    (hprime : ∀ l, l.Prime → l % 4 = 3 → Adm p l → ∀ f : E, inner ℂ u f = 0 → inner ℂ v f = 0 →
      ‖T l f‖ ≤ 2 * X * Real.sqrt l * ‖f‖) :
    ∀ n, Adm p n → (∀ q : ℕ, q.Prime → q ∣ n → q % 4 = 3) → ∀ f : E, inner ℂ u f = 0 → inner ℂ v f = 0 →
      ‖T n f‖ ≤ EDc0.Amaj X n * Real.sqrt n * ‖f‖ := by
  classical
  set W : Submodule ℂ E := (Submodule.span ℂ ({u, v} : Set E))ᗮ with hW
  have hinv : ∀ n, Adm p n → ∀ f ∈ W, T n f ∈ W := by
    intro n hn f hf
    rw [hW, mem_W] at hf ⊢
    obtain ⟨a, ha⟩ := hu n hn
    obtain ⟨b, hb⟩ := hv n hn
    constructor
    · have := hsymm n hn u f
      rw [ha, inner_smul_left, hf.1, mul_zero] at this
      exact this.symm
    · have := hsymm n hn v f
      rw [hb, inner_smul_left, hf.2, mul_zero] at this
      exact this.symm
  let T' : ℕ → W →ₗ[ℂ] W := fun n =>
    if h : Adm p n then (T n).restrict (hinv n h) else 0
  have hT' : ∀ n (h : Adm p n) (f : W), ((T' n f : W) : E) = T n (f : E) := by
    intro n h f
    simp only [T', dif_pos h, LinearMap.coe_restrict_apply]
  have hone : Adm p 1 := ⟨odd_one, fun h => hp.one_lt.ne' (Nat.dvd_one.1 h)⟩
  have key := EDc0.reduction_cheb p T' X hX
    (by
      apply LinearMap.ext; intro f; apply Subtype.ext
      rw [hT' 1 hone, h1]; rfl)
    (by
      intro m n hm hn hmn
      apply LinearMap.ext; intro f; apply Subtype.ext
      rw [hT' _ (Adm_mul p hp hm hn), hmul m n hm hn hmn]
      simp only [LinearMap.comp_apply]
      rw [hT' m hm, hT' n hn])
    (by
      intro l hl hAl k
      have hA2 := Adm_pow p hp hAl (k + 2)
      have hA1 := Adm_pow p hp hAl (k + 1)
      have hA0 := Adm_pow p hp hAl k
      apply LinearMap.ext; intro f; apply Subtype.ext
      rw [hT' _ hA2]
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, Submodule.coe_sub,
        Submodule.coe_smul]
      rw [hT' l hAl, hT' _ hA1, hT' _ hA0, hrec l hl hAl k]
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply])
    (by
      intro l hl hAl f g
      have := hsymm l hAl f g
      simpa [Submodule.coe_inner, hT' l hAl] using this)
    (by
      intro l hl hl4 hAl f
      have := hprime l hl hl4 hAl f ((mem_W u v f).1 f.2).1 ((mem_W u v f).1 f.2).2
      simpa [Submodule.coe_norm, hT' l hAl] using this)
  intro n hn hmod f hfu hfv
  have hf : f ∈ W := (mem_W u v f).2 ⟨hfu, hfv⟩
  have := key n hn hmod ⟨f, hf⟩
  simpa [Submodule.coe_norm, hT' n hn] using this


end

section
variable (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)
variable [Fintype (SectionA2.PGL2 p)] [Fintype (SectionA2.PGL2 p ⧸ SectionA3b.Gam p h2 xs ys hxy)]
  [Fintype (SectionA3b.Gam p h2 xs ys hxy)]

/-- Chebyshev version of `SectionA4m2.lemma32_of_prime_case_Yp`. -/
theorem lemma32_Yp_cheb (X : ℝ) (hX : 1 ≤ X)
    (hprime : ∀ l : ℕ, l.Prime → l % 4 = 3 → Adm p l → ∀ f : EY p h2 xs ys hxy,
      inner ℂ (oneY p h2 xs ys hxy) f = 0 → inner ℂ (chiE p h2 xs ys hxy) f = 0 →
      ‖Tl p h2 xs ys hxy l f‖ ≤ 2 * X * Real.sqrt l * ‖f‖) :
    ∀ n : ℕ, Adm p n → (∀ q : ℕ, q.Prime → q ∣ n → q % 4 = 3) → ∀ f : EY p h2 xs ys hxy,
      inner ℂ (oneY p h2 xs ys hxy) f = 0 → inner ℂ (chiE p h2 xs ys hxy) f = 0 →
      ‖Tl p h2 xs ys hxy n f‖ ≤ EDc0.Amaj X n * Real.sqrt n * ‖f‖ :=
  lemma32_cheb p (Fact.out) X hX (oneY p h2 xs ys hxy) (chiE p h2 xs ys hxy) (Tl p h2 xs ys hxy)
    (Tl_one p h2 xs ys hxy)
    (fun m n hm hn hmn => Tl_mul p h2 xs ys hxy m n hm hn hmn)
    (fun l hl hA k => Tl_rec p h2 xs ys hxy l hl hA k)
    (fun n h => Tl_symm p h2 xs ys hxy n h)
    (fun n h => Tl_one_eig p h2 xs ys hxy n h)
    (fun n h => Tl_chi_eig p h2 xs ys hxy n h)
    hprime

/-- Chebyshev version of `SectionA4n.quad_bound`. -/
theorem quad_bound_cheb
    (X : ℝ) (hX : 1 ≤ X)
    (hprime : ∀ l : ℕ, l.Prime → l % 4 = 3 → Adm p l → ∀ f : EY p h2 xs ys hxy,
      inner ℂ (oneY p h2 xs ys hxy) f = 0 → inner ℂ (chiE p h2 xs ys hxy) f = 0 →
      ‖Tl p h2 xs ys hxy l f‖ ≤ 2 * X * Real.sqrt l * ‖f‖)
    (m : ℕ) (hm : Adm p m) (hmq : ∀ q : ℕ, q.Prime → q ∣ m → q % 4 = 3) (h : SectionA3b.Yp p h2 xs ys hxy → ℝ)
    (hsum : ∑ y, h y = 0) (hchi : ∑ y, SectionA4k.chiY p h2 xs ys hxy y * (h y : ℂ) = 0) :
    ∑ y, h y * TR p h2 xs ys hxy m hm.2 h y
      ≤ EDc0.Amaj X m * Real.sqrt m * ∑ y, h y ^ 2 := by
  set H : EY p h2 xs ys hxy := WithLp.toLp 2 (fun y => (h y : ℂ)) with hH
  have hreal : ∀ y, (starRingEnd ℂ) (SectionA4k.chiY p h2 xs ys hxy y) = SectionA4k.chiY p h2 xs ys hxy y := by
    intro y
    refine Quotient.inductionOn y (fun g => ?_)
    rw [SectionA4k.chiY_mk]; simp
  have h1 : inner ℂ (oneY p h2 xs ys hxy) H = 0 := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, oneY, hH, map_one, mul_one]
    rw [← Complex.ofReal_sum, hsum, Complex.ofReal_zero]
  have h2' : inner ℂ (chiE p h2 xs ys hxy) H = 0 := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, chiE, hH, hreal]
    rw [← hchi]; exact Finset.sum_congr rfl (fun y _ => by ring)
  have key := lemma32_Yp_cheb p h2 xs ys hxy X hX hprime m hm hmq H h1 h2'
  have hnorm : ‖H‖ ^ 2 = ∑ y, h y ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    simp [hH, Complex.norm_real, sq_abs]
  have hre : ∑ y, h y * TR p h2 xs ys hxy m hm.2 h y = (inner ℂ H (Tl p h2 xs ys hxy m H)).re := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, Complex.re_sum]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [Tl_apply p h2 xs ys hxy m hm]
    simp [hH, TR, mul_comm]
  have hcs : (inner ℂ H (Tl p h2 xs ys hxy m H)).re ≤ ‖H‖ * ‖Tl p h2 xs ys hxy m H‖ :=
    le_trans (Complex.re_le_norm _) (norm_inner_le_norm _ _)
  rw [hre, ← hnorm]
  calc _ ≤ ‖H‖ * ‖Tl p h2 xs ys hxy m H‖ := hcs
    _ ≤ ‖H‖ * (EDc0.Amaj X m * Real.sqrt m * ‖H‖) :=
        mul_le_mul_of_nonneg_left key (norm_nonneg _)
    _ = _ := by ring


open Classical in
/-- Chebyshev version of `SectionA4n.pointwise_Yp`. -/
theorem pointwise_Yp_cheb
    (X : ℝ) (hX : 1 ≤ X)
    (hprime : ∀ l : ℕ, l.Prime → l % 4 = 3 → Adm p l → ∀ f : EY p h2 xs ys hxy,
      inner ℂ (oneY p h2 xs ys hxy) f = 0 → inner ℂ (chiE p h2 xs ys hxy) f = 0 →
      ‖Tl p h2 xs ys hxy l f‖ ≤ 2 * X * Real.sqrt l * ‖f‖)
    (m : ℕ) (hm : Adm p m) (hmq : ∀ q : ℕ, q.Prime → q ∣ m → q % 4 = 3) (O : Finset (SectionA3b.Yp p h2 xs ys hxy)) (y₀ : SectionA3b.Yp p h2 xs ys hxy)
    (hy₀ : y₀ ∈ O)
    (hconst : ∀ y ∈ O, TR p h2 xs ys hxy m hm.2 (fun z => if z ∈ O then (1 : ℝ) else 0) y
        = TR p h2 xs ys hxy m hm.2 (fun z => if z ∈ O then (1 : ℝ) else 0) y₀)
    (hchiO : ∑ y ∈ O, SectionA4k.chiY p h2 xs ys hxy y = 0) :
    TR p h2 xs ys hxy m hm.2 (fun z => if z ∈ O then (1 : ℝ) else 0) y₀
      ≤ (Section79a.sg m : ℝ) * ((O.card : ℝ) / (Fintype.card (SectionA3b.Yp p h2 xs ys hxy) : ℝ))
        + EDc0.Amaj X m * Real.sqrt m
          * (1 - (O.card : ℝ) / (Fintype.card (SectionA3b.Yp p h2 xs ys hxy) : ℝ)) := by
  have hcard : (0 : ℝ) < (Fintype.card (SectionA3b.Yp p h2 xs ys hxy) : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.2 ⟨y₀⟩
  set μ : ℝ := (O.card : ℝ) / (Fintype.card (SectionA3b.Yp p h2 xs ys hxy) : ℝ) with hμdef
  have hμ : μ * (Fintype.card (SectionA3b.Yp p h2 xs ys hxy) : ℝ) = (O.card : ℝ) := by
    rw [hμdef]; field_simp
  have hmo : m % 2 = 1 := Nat.odd_iff.1 hm.1
  refine EulerBridge.pointwise_of_quadform (TR p h2 xs ys hxy m hm.2) (Section79a.sg m : ℝ)
    (EDc0.Amaj X m * Real.sqrt m) μ O y₀ hy₀ _ (fun _ => rfl) ?_ ?_ hconst hμ ?_
  · funext y
    simp only [TR, LinearMap.coe_mk, AddHom.coe_mk]
    have : (fun z : SectionA3b.Yp p h2 xs ys hxy => (((1 : ℝ)) : ℂ)) = fun _ => (1 : ℂ) := by funext z; simp
    rw [this, SectionA4j.Tn_const p h2 xs ys hxy m hmo hm.2 y]
    simp
  · intro u v
    have e := Tn_adj p h2 xs ys hxy m hm.2 (fun z => (u z : ℂ)) (fun z => (v z : ℂ))
    have e2 := congrArg Complex.re e
    have L : ∀ y, (SectionA4g.Tn p h2 xs ys hxy m hm.2 (fun z => (u z : ℂ)) y * (starRingEnd ℂ) (v y : ℂ)).re
        = (SectionA4g.Tn p h2 xs ys hxy m hm.2 (fun z => (u z : ℂ)) y).re * v y := by
      intro y; simp [Complex.conj_ofReal]
    have R : ∀ y, ((u y : ℂ) * (starRingEnd ℂ) (SectionA4g.Tn p h2 xs ys hxy m hm.2 (fun z => (v z : ℂ)) y)).re
        = u y * (SectionA4g.Tn p h2 xs ys hxy m hm.2 (fun z => (v z : ℂ)) y).re := by
      intro y; simp
    simp only [Complex.re_sum, L, R] at e2
    exact e2.symm
  · have hsumO : ∑ y, (if y ∈ O then (1 : ℝ) else 0) = (O.card : ℝ) := by
      rw [Finset.sum_ite_mem, Finset.univ_inter]; simp
    have hchiA : ∑ y, SectionA4k.chiY p h2 xs ys hxy y * (((if y ∈ O then (1 : ℝ) else 0 : ℝ)) : ℂ)
        = ∑ y ∈ O, SectionA4k.chiY p h2 xs ys hxy y := by
      calc _ = ∑ y, if y ∈ O then SectionA4k.chiY p h2 xs ys hxy y else 0 :=
            Finset.sum_congr rfl (fun y _ => by split_ifs <;> simp)
        _ = _ := by rw [Finset.sum_ite_mem, Finset.univ_inter]
    apply quad_bound_cheb p h2 xs ys hxy X hX hprime m hm hmq
    · simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [hsumO]; linarith [hμ]
    · have : ∀ y, SectionA4k.chiY p h2 xs ys hxy y * (((if y ∈ O then (1 : ℝ) else 0) - μ : ℝ) : ℂ)
          = SectionA4k.chiY p h2 xs ys hxy y * (((if y ∈ O then (1 : ℝ) else 0 : ℝ)) : ℂ)
            - (μ : ℂ) * SectionA4k.chiY p h2 xs ys hxy y := by
        intro y; push_cast; ring
      simp only [this, Finset.sum_sub_distrib, ← Finset.mul_sum, hchiA, hchiO, sum_chi p h2 xs ys hxy]
      simp


open Classical in
/-- Chebyshev version of `SectionA4o.pointwise_OK`. -/
theorem pointwise_OK_cheb
    (X : ℝ) (hX : 1 ≤ X)
    (hprime : ∀ l : ℕ, l.Prime → l % 4 = 3 → Adm p l → ∀ f : EY p h2 xs ys hxy,
      inner ℂ (oneY p h2 xs ys hxy) f = 0 → inner ℂ (chiE p h2 xs ys hxy) f = 0 →
      ‖Tl p h2 xs ys hxy l f‖ ≤ 2 * X * Real.sqrt l * ‖f‖)
    (m : ℕ) (hm : Adm p m) (hmq : ∀ q : ℕ, q.Prime → q ∣ m → q % 4 = 3) (K : Subgroup (SectionA2.PGL2 p)) (k₀ : SectionA2.PGL2 p) (hk₀ : k₀ ∈ K)
    (hchi : ((SectionA4k.chiP p k₀ : ℤˣ) : ℤ) = -1) :
    TR p h2 xs ys hxy m hm.2 (fun z => if z ∈ OK p h2 xs ys hxy K then (1 : ℝ) else 0) (mkY p h2 xs ys hxy 1)
      ≤ (Section79a.sg m : ℝ) * (((OK p h2 xs ys hxy K).card : ℝ) / (Fintype.card (SectionA3b.Yp p h2 xs ys hxy) : ℝ))
        + EDc0.Amaj X m * Real.sqrt m
          * (1 - ((OK p h2 xs ys hxy K).card : ℝ) / (Fintype.card (SectionA3b.Yp p h2 xs ys hxy) : ℝ)) :=
  pointwise_Yp_cheb p h2 xs ys hxy X hX hprime m hm hmq (OK p h2 xs ys hxy K) (mkY p h2 xs ys hxy 1)
    ((mem_OK p h2 xs ys hxy K _).2 ⟨1, K.one_mem, rfl⟩)
    (fun y hy => const_OK p h2 xs ys hxy K m hm.2 y hy)
    (sum_chi_OK p h2 xs ys hxy K k₀ hk₀ hchi)



open Classical in
include h2 hxy in
/-- Chebyshev version of `SectionA4o.pointwise_Kp`; `Kp` and `OK` are the production definitions. -/
theorem pointwise_Kp_cheb
    (X : ℝ) (hX : 1 ≤ X)
    (hprime : ∀ l : ℕ, l.Prime → l % 4 = 3 → Adm p l → ∀ f : EY p h2 xs ys hxy,
      inner ℂ (oneY p h2 xs ys hxy) f = 0 → inner ℂ (chiE p h2 xs ys hxy) f = 0 →
      ‖Tl p h2 xs ys hxy l f‖ ≤ 2 * X * Real.sqrt l * ‖f‖)
    (m : ℕ) (hm : Adm p m) (hmq : ∀ q : ℕ, q.Prime → q ∣ m → q % 4 = 3) :
    TR p h2 xs ys hxy m hm.2 (fun z => if z ∈ OK p h2 xs ys hxy (Kp p xs ys) then (1 : ℝ) else 0)
        (mkY p h2 xs ys hxy 1)
      ≤ (Section79a.sg m : ℝ) * (((OK p h2 xs ys hxy (Kp p xs ys)).card : ℝ)
            / (Fintype.card (SectionA3b.Yp p h2 xs ys hxy) : ℝ))
        + EDc0.Amaj X m * Real.sqrt m
          * (1 - ((OK p h2 xs ys hxy (Kp p xs ys)).card : ℝ)
            / (Fintype.card (SectionA3b.Yp p h2 xs ys hxy) : ℝ)) := by
  obtain ⟨k₀, hk₀, hchi⟩ := Kp_has_nonsquare p h2 xs ys hxy
  exact pointwise_OK_cheb p h2 xs ys hxy X hX hprime m hm hmq (Kp p xs ys) k₀ hk₀ hchi


end

end EDc1
#print axioms EDc1.lemma32_cheb
#print axioms EDc1.pointwise_Kp_cheb

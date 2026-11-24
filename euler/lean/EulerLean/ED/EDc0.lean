import StageA4o

/-!
# EDc0.lean   (PRODUCTION-FACING; UNTESTED until compiled)

Phase 8A, first additive integration module.  Imports ONLY the tracked `StageA4o` (`euler/lean/EulerLean/StageA4o.lean`, commit f8f8766, where `SectionA4l` lives).
`Stage83cut`, `EDb8` and every `EDcert*` module are NOT needed.  It redefines NOTHING
that production already has: `w`, `u`, `u_eq`, `S`, `S_eigen`, `Adm`, `Adm_mul_left/right`, `Adm_of_pow`,
`T_pow_eq_S` are the production declarations of `SectionA4l`, reached through `open SectionA4l`.
No `EDcert*` module is needed.

New here (all copied from the locally Lean-checked isolated files, with the isolated duplicates removed):
  * scalar majorant   |w t k| ≤ w X k   (|t| ≤ X, X ≥ 1)        [ChebMajorant_isolated]
  * `S_norm_le_cheb`  ‖S l T k f‖ ≤ √l^k · w X k · ‖f‖            [SNormCheb_isolated]
  * `Amaj`, positivity, multiplicativity, `reduction_cheb`        [AMajorant_isolated]
  * `tau_le_Amaj`     τ(n) ≤ Amaj X n for X ≥ 1, n ≠ 0   (NEW, not in any isolated file; no mod-4 hypothesis)
-/

namespace EDc0

open SectionA4l


/-! ## 2. NEW: positivity and monotonicity of U_k on [1, ∞) -/

/-- w t k ≥ 0 and nondecreasing in k, for t ≥ 1 -/
theorem w_nonneg_mono {t : ℝ} (ht : 1 ≤ t) :
    ∀ k : ℕ, 0 ≤ w t k ∧ w t k ≤ w t (k + 1) := by
  intro k
  induction k with
  | zero =>
    simp only [w]
    constructor <;> linarith
  | succ k ih =>
    obtain ⟨h0, h1⟩ := ih
    have hk1 : 0 ≤ w t (k + 1) := le_trans h0 h1
    constructor
    · exact hk1
    · show w t (k + 1) ≤ 2 * t * w t (k + 1) - w t k
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * t - 2) hk1]

/-- D_k = w x k - w t k satisfies 0 ≤ D_k ≤ D_{k+1} for 1 ≤ t ≤ x.
The step is the identity
D_{k+2} - D_{k+1} = (2x-2) D_{k+1} + (D_{k+1} - D_k) + 2 (x-t) w t (k+1). -/
theorem w_sub_mono {t x : ℝ} (ht : 1 ≤ t) (htx : t ≤ x) :
    ∀ k : ℕ, 0 ≤ w x k - w t k ∧ w x k - w t k ≤ w x (k + 1) - w t (k + 1) := by
  intro k
  induction k with
  | zero =>
    simp only [w]
    constructor <;> linarith
  | succ k ih =>
    obtain ⟨h0, h1⟩ := ih
    have hD1 : 0 ≤ w x (k + 1) - w t (k + 1) := le_trans h0 h1
    have hp : 0 ≤ w t (k + 1) := (w_nonneg_mono ht (k + 1)).1
    constructor
    · exact hD1
    · show w x (k + 1) - w t (k + 1)
          ≤ (2 * x * w x (k + 1) - w x k) - (2 * t * w t (k + 1) - w t k)
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * x - 2) hD1,
                 mul_nonneg (by linarith : (0 : ℝ) ≤ x - t) hp]

/-- U_k(1) = k + 1 -/
theorem w_one : ∀ k : ℕ, w 1 k = (k : ℝ) + 1 ∧ w 1 (k + 1) = (k : ℝ) + 2 := by
  intro k
  induction k with
  | zero => constructor <;> norm_num [w]
  | succ k ih =>
    obtain ⟨a, b⟩ := ih
    refine ⟨by push_cast; rw [b]; ring, ?_⟩
    show 2 * 1 * w 1 (k + 1) - w 1 k = ((k + 1 : ℕ) : ℝ) + 2
    rw [b, a]; push_cast; ring

/-- parity: U_k(-c) = (-1)^k U_k(c) -/
theorem w_neg (c : ℝ) : ∀ k : ℕ,
    w (-c) k = (-1) ^ k * w c k ∧ w (-c) (k + 1) = (-1) ^ (k + 1) * w c (k + 1) := by
  intro k
  induction k with
  | zero => constructor <;> simp [w]
  | succ k ih =>
    obtain ⟨a, b⟩ := ih
    refine ⟨b, ?_⟩
    show 2 * (-c) * w (-c) (k + 1) - w (-c) k
        = (-1) ^ (k + 1 + 1) * (2 * c * w c (k + 1) - w c k)
    rw [a, b]; ring

/-! ## 3. NEW: the majorant theorem -/

/-- For X ≥ 1 and |t| ≤ X:  |U_k(t)| ≤ U_k(X). -/
theorem w_abs_le_w {X t : ℝ} (hX : 1 ≤ X) (ht : |t| ≤ X) (k : ℕ) : |w t k| ≤ w X k := by
  by_cases h1 : |t| ≤ 1
  · have a := w_abs_le t h1 k
    have b := (w_one k).1
    have c := (w_sub_mono (le_refl (1 : ℝ)) hX k).1
    linarith
  · push_neg at h1
    have hs : (1 : ℝ) ≤ |t| := h1.le
    have hmono := (w_sub_mono hs ht k).1
    have hnn := (w_nonneg_mono hs k).1
    have habs : |w t k| = w (|t|) k := by
      rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩
      · rw [h] at hnn ⊢
        exact abs_of_nonneg hnn
      · have ht' : t = -|t| := by linarith
        have hp := (w_neg (|t|) k).1
        rw [← ht'] at hp
        rw [hp, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg hnn]
    rw [habs]
    linarith

/-- transport to the operator recurrence u (the scalar that `S_norm_le` consumes) -/
theorem u_abs_le_cheb (l : ℝ) (hl : 0 < l) (X : ℝ) (hX : 1 ≤ X) (μ : ℝ)
    (hμ : |μ| ≤ 2 * X * Real.sqrt l) (k : ℕ) :
    |u l μ k| ≤ Real.sqrt l ^ k * w X k := by
  have hs : 0 < Real.sqrt l := Real.sqrt_pos.2 hl
  have hc : |μ / (2 * Real.sqrt l)| ≤ X := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.sqrt l), div_le_iff₀ (by positivity)]
    exact le_of_le_of_eq hμ (by ring)
  rw [(u_eq l hl μ k).1, abs_mul, abs_pow, abs_of_pos hs]
  exact mul_le_mul_of_nonneg_left (w_abs_le_w hX hc k) (by positivity)

/-- the case used by the 2.04 route: 2X = 51/25 -/
theorem u_abs_le_cheb_51_50 (l : ℝ) (hl : 0 < l) (μ : ℝ)
    (hμ : |μ| ≤ (51 / 25) * Real.sqrt l) (k : ℕ) :
    |u l μ k| ≤ Real.sqrt l ^ k * w (51 / 50) k :=
  u_abs_le_cheb l hl (51 / 50) (by norm_num) μ (by linarith) k

/-- the original Ramanujan case X = 1 is recovered (w 1 k = k+1) -/
theorem u_abs_le_cheb_one (l : ℝ) (hl : 0 < l) (μ : ℝ)
    (hμ : |μ| ≤ 2 * Real.sqrt l) (k : ℕ) :
    |u l μ k| ≤ ((k : ℝ) + 1) * Real.sqrt l ^ k := by
  have := u_abs_le_cheb l hl 1 le_rfl μ (by linarith) k
  rw [(w_one k).1] at this
  linarith [mul_comm (Real.sqrt l ^ k) ((k : ℝ) + 1)]

section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-! ## 5. NEW: S_norm_le generalised over the spectral constant X ≥ 1

`hb` is the prime-level hypothesis ‖T f‖ ≤ 2 X √l ‖f‖ (X = 1: Ramanujan; X = 51/50: the 2.04 route).
The proof is the proof of `SectionA4l.S_norm_le` with the single scalar input `u_abs_le` replaced by
`u_abs_le_cheb` and the constant B = (k+1) √l^k replaced by √l^k · w X k. -/

theorem S_norm_le_cheb (l : ℝ) (hl : 0 < l) (X : ℝ) (hX : 1 ≤ X) (T : E →ₗ[ℂ] E)
    (hT : T.IsSymmetric)
    (hb : ∀ f : E, ‖T f‖ ≤ 2 * X * Real.sqrt l * ‖f‖) (k : ℕ) (f : E) :
    ‖S l T k f‖ ≤ Real.sqrt l ^ k * w X k * ‖f‖ := by
  set n := Module.finrank ℂ E with hn
  set b := hT.eigenvectorBasis (n := n) rfl with hbdef
  have hmu : ∀ i, |hT.eigenvalues (n := n) rfl i| ≤ 2 * X * Real.sqrt l := by
    intro i
    have h := hb (b i)
    rw [hbdef, hT.apply_eigenvectorBasis, norm_smul, b.orthonormal.1 i] at h
    simpa [Complex.norm_real] using h
  set B : ℝ := Real.sqrt l ^ k * w X k with hB
  have hB0 : 0 ≤ B := mul_nonneg (by positivity) (w_nonneg_mono hX k).1
  have hdiag : ∀ i, S l T k (b i) = (u l (hT.eigenvalues (n := n) rfl i) k : ℂ) • b i := fun i =>
    (S_eigen l T (b i) _ (hT.apply_eigenvectorBasis rfl i) k).1
  set c : Fin n → ℂ := fun i => (b.repr f).ofLp i with hc
  have hf : f = ∑ i, c i • b i := (b.sum_repr f).symm
  have hSf : S l T k f = ∑ i, (c i * (u l (hT.eigenvalues (n := n) rfl i) k : ℂ)) • b i := by
    conv_lhs => rw [hf]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, hdiag, smul_smul]
  have hinner : ∀ (a : Fin n → ℂ) (i : Fin n), inner ℂ (b i) (∑ j, a j • b j) = a i := by
    intro a i
    rw [inner_sum]
    simp only [inner_smul_right, orthonormal_iff_ite.1 b.orthonormal]
    simp
  have hnormsq : ∀ (a : Fin n → ℂ), ‖∑ j, a j • b j‖ ^ 2 = ∑ i, ‖a i‖ ^ 2 := by
    intro a
    rw [← b.sum_sq_norm_inner_right]
    exact (Finset.sum_congr rfl (fun i _ => by rw [hinner])).symm
  have h1 : ‖S l T k f‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 * |u l (hT.eigenvalues (n := n) rfl i) k| ^ 2 := by
    rw [hSf, hnormsq]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs]
  have h2 : ‖f‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 := by
    have := hnormsq c
    rwa [← hf] at this
  have h3 : ‖S l T k f‖ ^ 2 ≤ (B * ‖f‖) ^ 2 := by
    rw [h1, mul_pow, h2, Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    have := u_abs_le_cheb l hl X hX _ (hmu i) k
    have h4 : |u l (hT.eigenvalues (n := n) rfl i) k| ^ 2 ≤ B ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) this 2
    nlinarith [sq_nonneg ‖c i‖]
  exact le_trans (le_abs_self _) (abs_le_of_sq_le_sq h3 (by positivity)) |>.trans (by rw [hB])

/-- one theorem, both spectral bounds: X = 1 gives the original (k+1) √l^k estimate of `S_norm_le` -/
theorem S_norm_le_via_cheb (l : ℝ) (hl : 0 < l) (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    (hb : ∀ f : E, ‖T f‖ ≤ 2 * Real.sqrt l * ‖f‖) (k : ℕ) (f : E) :
    ‖S l T k f‖ ≤ ((k : ℝ) + 1) * Real.sqrt l ^ k * ‖f‖ := by
  have := S_norm_le_cheb l hl 1 le_rfl T hT (by simpa using hb) k f
  rw [(w_one k).1] at this
  linarith [mul_comm (Real.sqrt l ^ k) ((k : ℝ) + 1)]

/-- the 2.04 case -/
theorem S_norm_le_51_50 (l : ℝ) (hl : 0 < l) (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    (hb : ∀ f : E, ‖T f‖ ≤ (51 / 25) * Real.sqrt l * ‖f‖) (k : ℕ) (f : E) :
    ‖S l T k f‖ ≤ Real.sqrt l ^ k * w (51 / 50) k * ‖f‖ :=
  S_norm_le_cheb l hl (51 / 50) (by norm_num) T hT
    (fun g => by have := hb g; linarith) k f




/-! ## 7. NEW: the multiplicative majorant A_X(n) = ∏_{l^e ∥ n} U_e(X) -/

/-- A_X(n) = product over the prime factors l of n of w X (v_l(n)) -/
noncomputable def Amaj (X : ℝ) (n : ℕ) : ℝ := ∏ q ∈ n.primeFactors, w X (n.factorization q)

theorem Amaj_one (X : ℝ) : Amaj X 1 = 1 := by simp [Amaj]

theorem Amaj_pp (X : ℝ) {l : ℕ} (hl : l.Prime) {k : ℕ} (hk : 0 < k) :
    Amaj X (l ^ k) = w X k := by
  unfold Amaj
  rw [Nat.primeFactors_prime_pow hk.ne' hl, Finset.prod_singleton, hl.factorization_pow]
  simp

theorem Amaj_mul (X : ℝ) {a b : ℕ} (hab : Nat.Coprime a b) :
    Amaj X (a * b) = Amaj X a * Amaj X b := by
  unfold Amaj
  rw [Nat.Coprime.primeFactors_mul hab,
    Finset.prod_union (Nat.Coprime.disjoint_primeFactors hab)]
  congr 1
  · refine Finset.prod_congr rfl (fun q hq => ?_)
    have hqa : q ∣ a := Nat.dvd_of_mem_primeFactors hq
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hnb : ¬ q ∣ b := fun hb => by
      have : q ∣ Nat.gcd a b := Nat.dvd_gcd hqa hb
      rw [hab.gcd_eq_one] at this
      exact hqp.not_dvd_one this
    have h0 : b.factorization q = 0 := Nat.factorization_eq_zero_of_not_dvd hnb
    rw [Nat.factorization_mul_of_coprime hab]
    simp [h0]
  · refine Finset.prod_congr rfl (fun q hq => ?_)
    have hqb : q ∣ b := Nat.dvd_of_mem_primeFactors hq
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hna : ¬ q ∣ a := fun ha => by
      have : q ∣ Nat.gcd a b := Nat.dvd_gcd ha hqb
      rw [hab.gcd_eq_one] at this
      exact hqp.not_dvd_one this
    have h0 : a.factorization q = 0 := Nat.factorization_eq_zero_of_not_dvd hna
    rw [Nat.factorization_mul_of_coprime hab]
    simp [h0]

theorem w_pos_of_one_le {X : ℝ} (hX : 1 ≤ X) (e : ℕ) : 0 < w X e := by
  have h := (w_sub_mono (le_refl (1 : ℝ)) hX e).1
  rw [(w_one e).1] at h
  have : (0 : ℝ) < (e : ℝ) + 1 := by positivity
  linarith

theorem Amaj_pos {X : ℝ} (hX : 1 ≤ X) (n : ℕ) : 0 < Amaj X n :=
  Finset.prod_pos (fun q _ => w_pos_of_one_le hX _)

theorem Amaj_nonneg {X : ℝ} (hX : 1 ≤ X) (n : ℕ) : 0 ≤ Amaj X n := (Amaj_pos hX n).le

/-! ## 7b. NEW: τ ≤ A_X  (no mod-4 hypothesis; used for the p ∣ m branch of the A-shaped H31 chain) -/

/-- U_e(X) ≥ e + 1 for X ≥ 1 (U_e(1) = e + 1 and U_e is monotone in X on [1, ∞)). -/
theorem w_ge_succ {X : ℝ} (hX : 1 ≤ X) (e : ℕ) : (e : ℝ) + 1 ≤ w X e := by
  have h := (w_sub_mono (le_refl (1 : ℝ)) hX e).1
  rw [(w_one e).1] at h
  linarith

/-- τ(n) ≤ A_X(n).  `ArithmeticFunction.sigma 0 n` is `Section51.tau n` by `rfl` (Stage83cut.lean:740). -/
theorem tau_le_Amaj {X : ℝ} (hX : 1 ≤ X) (n : ℕ) (hn : n ≠ 0) :
    ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) ≤ Amaj X n := by
  have hτ : ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ)
      = ∏ q ∈ n.primeFactors, ((n.factorization q : ℝ) + 1) := by
    rw [ArithmeticFunction.sigma_zero_apply, Nat.card_divisors hn, Nat.cast_prod]
    push_cast
    try rfl
  rw [hτ]
  unfold Amaj
  exact Finset.prod_le_prod (fun q _ => by positivity) (fun q _ => w_ge_succ hX _)

/-! ## 8. NEW: `reduction` with the majorant A_X and the restriction l ≡ 3 (mod 4)

Same proof as `SectionA4l.reduction`; the two changes are `S_norm_le` ⟶ `S_norm_le_cheb` and
τ(n) ⟶ Amaj X n, and `hprime` / the conclusion are restricted to primes l ≡ 3 (mod 4). -/

theorem reduction_cheb (p : ℕ) (T : ℕ → E →ₗ[ℂ] E) (X : ℝ) (hX : 1 ≤ X)
    (h1 : T 1 = LinearMap.id)
    (hmul : ∀ m n, Adm p m → Adm p n → Nat.Coprime m n → T (m * n) = T m ∘ₗ T n)
    (hrec : ∀ l, l.Prime → Adm p l → ∀ k : ℕ,
      T (l ^ (k + 2)) = T l ∘ₗ T (l ^ (k + 1)) - (l : ℂ) • T (l ^ k))
    (hsymm : ∀ l, l.Prime → Adm p l → (T l).IsSymmetric)
    (hprime : ∀ l, l.Prime → l % 4 = 3 → Adm p l → ∀ f : E,
      ‖T l f‖ ≤ 2 * X * Real.sqrt l * ‖f‖) :
    ∀ n, Adm p n → (∀ q : ℕ, q.Prime → q ∣ n → q % 4 = 3) → ∀ f : E,
      ‖T n f‖ ≤ Amaj X n * Real.sqrt n * ‖f‖ := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => intro h; exact absurd h.1 (by simp)
  | one =>
    intro _ _ f
    rw [h1]
    simp [Amaj_one]
  | prime_pow l k hlp hk =>
    intro hA hmod f
    have hl := Adm_of_pow hk hA
    have hl4 : l % 4 = 3 := hmod l hlp (dvd_pow_self l hk.ne')
    have hS := (T_pow_eq_S T l h1 (hrec l hlp hl) k).1
    have hl0 : (0 : ℝ) < l := by exact_mod_cast hlp.pos
    have := S_norm_le_cheb (l : ℝ) hl0 X hX (T l) (hsymm l hlp hl)
      (hprime l hlp hl4 hl) k f
    rw [hS, Amaj_pp X hlp hk]
    have e : Real.sqrt ((l ^ k : ℕ) : ℝ) = Real.sqrt l ^ k := by
      push_cast; rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
      rw [← mul_pow, Real.mul_self_sqrt hl0.le]
    rw [e]
    calc ‖S (l : ℝ) (T l) k f‖ ≤ Real.sqrt l ^ k * w X k * ‖f‖ := this
      _ = w X k * Real.sqrt l ^ k * ‖f‖ := by ring
  | coprime a b ha hb hab iha ihb =>
    intro hA hmod f
    have hAa := Adm_mul_left hA
    have hAb := Adm_mul_right hA
    have hma : ∀ q : ℕ, q.Prime → q ∣ a → q % 4 = 3 :=
      fun q hq hd => hmod q hq (dvd_mul_of_dvd_left hd b)
    have hmb : ∀ q : ℕ, q.Prime → q ∣ b → q % 4 = 3 :=
      fun q hq hd => hmod q hq (dvd_mul_of_dvd_right hd a)
    rw [hmul a b hAa hAb hab]
    simp only [LinearMap.comp_apply]
    have e1 := iha hAa hma (T b f)
    have e2 := ihb hAb hmb f
    have hm : Amaj X (a * b) = Amaj X a * Amaj X b := Amaj_mul X hab
    have hsq : Real.sqrt ((a * b : ℕ) : ℝ) = Real.sqrt a * Real.sqrt b := by
      push_cast; exact Real.sqrt_mul (by positivity) _
    rw [hm, hsq]
    have ha0 : (0 : ℝ) ≤ Amaj X a * Real.sqrt a :=
      mul_nonneg (Amaj_nonneg hX a) (Real.sqrt_nonneg _)
    calc ‖T a (T b f)‖ ≤ Amaj X a * Real.sqrt a * ‖T b f‖ := e1
      _ ≤ Amaj X a * Real.sqrt a * (Amaj X b * Real.sqrt b * ‖f‖) :=
          mul_le_mul_of_nonneg_left e2 ha0
      _ = _ := by ring

end

end EDc0

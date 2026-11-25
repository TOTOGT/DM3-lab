import EDc4
import EDc7

/-!
# splitting_transport.lean   (UNTESTED: never compiled; draft by the splitting-transport author)

Module header.  Labels follow the plan: NEW PROOF / CONDITIONAL REDUCTION / FINITE BOOKKEEPING.

## Part A : the conjugacy `EDc7.Conj` is discharged (new proof, finite algebra, UNTESTED)

`Section74b.red p xs ys q := Section74a.psi xs ys (cz p q.re) (cz p q.imI) (cz p q.imJ) (cz p q.imK)` (StageA4o l.~700, `rfl`
unfolding), so `red` depends on the splitting `(xs, ys)` only through `psi xs ys a b c d`.  Hand derivation: put
`F = [[y+v, -(x-u)], [x-u, y+v]]`, `S = [[x+u, -(v-y)], [v-y, x+u]]` for `psi x y` versus `psi u v`.  Each entry of
`F psi_{x,y} - psi_{u,v} F` and of `S psi_{x,y} - psi_{u,v} S` is `± a coordinate * (x²+y²-u²-v²)`, hence zero when both
`x²+y²=-1=u²+v²` (checked by sympy; the `linear_combination` coefficients were checked against the sympy expansion).
`det F + det S = 2(x²+y²+u²+v²) = -4`, so one of the two is invertible when `2 ≠ 0`.  Thus for every two splittings with
`xs²+ys² = -1 = xs'²+ys'²` and `2 ≠ 0 in F_p` there is a unit `c` with `red xs' ys' q = c * red xs ys q * c⁻¹` for ALL
quaternions `q` (in particular all Hurwitz `q`), i.e. `EDc7.Conj p xs ys xs' ys' c`.  This is an elementary matrix
computation; no Skolem-Noether is invoked.  It supersedes the drafts/handoff/EDcSplittingConjugacy.lean (same
mathematics, with the `GL` unit built by `IsUnit.unit` instead of an unchecked Mathlib name).

## Part B : EY-level isometry (new proof, finite bookkeeping, UNTESTED)

For an equivalence `e : Y_p ≃ Y_p'` (from `EDc7.transport`), `Lmap e : EY → EY'`, `f ↦ f ∘ e⁻¹`, is a linear bijection
preserving the inner product (`Lmap_inner`; norm preservation follows, not separately proved), with `Lmap (Tl n f) = Tl' n (Lmap f)` for EVERY `n` (admissible: from
`transport`; inadmissible: both sides are 0), `Lmap oneY = oneY'`, `Lmap chiE = chiE'`.  Stated as bijective + inner-preserving
linear map rather than as a bundled `≃ₗᵢ` (avoids relying on an unchecked Mathlib constructor).

## Part C : conditional reduction (CONDITIONAL REDUCTION)

`RPEigenAt p h2 xs ys hxy` is the statement of `EDc4.RPEigen` at one fixed `(p, xs, ys)` and all primes `l ≡ 3 mod 4`.
* `rpeigenAt_transport` : `RPEigenAt xs ys → RPEigenAt xs' ys'` given `Conj`.
* `rpeigenAt_all`       : `RPEigenAt xs ys → RPEigenAt xs' ys'` for ALL splittings (Conj from Part A).
* `rpeigen_of_one_splitting` : (for every `p ≡ 3 mod 4`, `p > 3`, and `2 ≠ 0`, some splitting satisfies `RPEigenAt`) → `EDc4.RPEigen`.

## What this does NOT establish
It does not prove `RPEigenAt` at any splitting, nor `EDc4.RPEigen`; `RPEigen` is OPEN and appears only as hypothesis or
inside the implication.  It does not say that the splitting used by the geometric identification (Codogni-Lido,
Jacquet-Langlands, Deuring) is any particular `(xs, ys)`; that identification stays external.  Part C is only an
implication; it carries no information about the size of any eigenvalue.

## Names verified by grep (StageA4o.lean, EDc7.lean, EDc4.lean)
Section74a.psi, Section74b.red, Section74b.cz, Matrix.isUnit_iff_isUnit_det (used l.860, l.4019), isUnit_iff_ne_zero (l.861),
IsUnit.unit_spec, Units.mul_inv (l.1837), SectionA4m2.{EY,Tl,Tl_apply,oneY,chiE}, SectionA4l.Adm, SectionA4g.Tn,
SectionA4e.U (U_mk), SectionA4k.chiY, EDc7.{Conj,transport}, EDc4.RPEigen, Fintype.sum_equiv (l.1508).
## Unverified (Mathlib only, not grep-able here)
`Matrix.mul_apply`/`Fin.sum_univ_two`/`fin_cases` simp-shapes in the matrix identities (same pattern as StageA4o `psi_mul`,
but the goals differ); `PiLp.inner_apply`, `RCLike.inner_apply` (used the same way in StageA4o l.4683); `WithLp.ofLp_toLp`
as `rfl`; `Equiv.apply_symm_apply`, `Equiv.symm_apply_apply`.
-/

namespace EDcSplitTransport
open SectionA4l SectionA4m SectionA4m2 SectionA4n SectionA4o

/-! ### Part A : explicit intertwiners -/
section PartA
variable {K : Type*} [Field K]

def firstCandidate (x y u v : K) : Matrix (Fin 2) (Fin 2) K :=
  !![y + v, -(x - u); x - u, y + v]

def secondCandidate (x y u v : K) : Matrix (Fin 2) (Fin 2) K :=
  !![x + u, -(v - y); v - y, x + u]

theorem first_intertwines (x y u v : K)
    (hxy : x ^ 2 + y ^ 2 = -1) (huv : u ^ 2 + v ^ 2 = -1) (a b c d : K) :
    firstCandidate x y u v * Section74a.psi x y a b c d =
      Section74a.psi u v a b c d * firstCandidate x y u v := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [firstCandidate, Section74a.psi, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination -d * hxy + d * huv
  · simp [firstCandidate, Section74a.psi, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination c * hxy - c * huv
  · simp [firstCandidate, Section74a.psi, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination c * hxy - c * huv
  · simp [firstCandidate, Section74a.psi, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination d * hxy - d * huv

theorem second_intertwines (x y u v : K)
    (hxy : x ^ 2 + y ^ 2 = -1) (huv : u ^ 2 + v ^ 2 = -1) (a b c d : K) :
    secondCandidate x y u v * Section74a.psi x y a b c d =
      Section74a.psi u v a b c d * secondCandidate x y u v := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [secondCandidate, Section74a.psi, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination c * hxy - c * huv
  · simp [secondCandidate, Section74a.psi, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination d * hxy - d * huv
  · simp [secondCandidate, Section74a.psi, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination d * hxy - d * huv
  · simp [secondCandidate, Section74a.psi, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination -c * hxy + c * huv

theorem det_sum (x y u v : K)
    (hxy : x ^ 2 + y ^ 2 = -1) (huv : u ^ 2 + v ^ 2 = -1) :
    (firstCandidate x y u v).det + (secondCandidate x y u v).det = -4 := by
  simp [firstCandidate, secondCandidate, Matrix.det_fin_two]
  linear_combination 2 * hxy + 2 * huv

theorem exists_intertwiner (h2 : (2 : K) ≠ 0) (x y u v : K)
    (hxy : x ^ 2 + y ^ 2 = -1) (huv : u ^ 2 + v ^ 2 = -1) :
    ∃ C : Matrix (Fin 2) (Fin 2) K, C.det ≠ 0 ∧
      ∀ a b c d : K, C * Section74a.psi x y a b c d = Section74a.psi u v a b c d * C := by
  by_cases hc : (firstCandidate x y u v).det = 0
  · refine ⟨secondCandidate x y u v, ?_, second_intertwines x y u v hxy huv⟩
    intro hd
    have hs := det_sum x y u v hxy huv
    rw [hc, hd] at hs
    have h4 : (4 : K) ≠ 0 := by
      simpa only [show (2 : K) * 2 = 4 by ring] using mul_ne_zero h2 h2
    apply h4
    linear_combination hs
  · exact ⟨firstCandidate x y u v, hc, first_intertwines x y u v hxy huv⟩

end PartA

variable (p : ℕ) [Fact p.Prime]

theorem exists_red_conjugator (h2 : (2 : ZMod p) ≠ 0) (x y u v : ZMod p)
    (hxy : x ^ 2 + y ^ 2 = -1) (huv : u ^ 2 + v ^ 2 = -1) :
    ∃ c : (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ, ∀ q : Quaternion ℚ,
      Section74b.red p u v q =
        (c : Matrix (Fin 2) (Fin 2) (ZMod p)) * Section74b.red p x y q *
          ((c⁻¹ : (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ) : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
  obtain ⟨C, hC, hpsi⟩ := exists_intertwiner h2 x y u v hxy huv
  have hU : IsUnit C := (Matrix.isUnit_iff_isUnit_det C).2 (isUnit_iff_ne_zero.2 hC)
  let c : (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ := hU.unit
  have hc : (c : Matrix (Fin 2) (Fin 2) (ZMod p)) = C := IsUnit.unit_spec hU
  have hmi : (c : Matrix (Fin 2) (Fin 2) (ZMod p)) *
      ((c⁻¹ : (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ) : Matrix (Fin 2) (Fin 2) (ZMod p)) = 1 :=
    Units.mul_inv c
  refine ⟨c, fun q => ?_⟩
  have hred : C * Section74b.red p x y q = Section74b.red p u v q * C := by
    unfold Section74b.red
    exact hpsi _ _ _ _
  calc Section74b.red p u v q
      = Section74b.red p u v q * ((c : Matrix (Fin 2) (Fin 2) (ZMod p)) *
          ((c⁻¹ : (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ) : Matrix (Fin 2) (Fin 2) (ZMod p))) := by
        rw [hmi, mul_one]
    _ = (Section74b.red p u v q * (c : Matrix (Fin 2) (Fin 2) (ZMod p))) *
          ((c⁻¹ : (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ) : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
        rw [mul_assoc]
    _ = (C * Section74b.red p x y q) *
          ((c⁻¹ : (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ) : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
        rw [hc, hred]
    _ = (c : Matrix (Fin 2) (Fin 2) (ZMod p)) * Section74b.red p x y q *
          ((c⁻¹ : (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ) : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
        rw [hc]

/-- `EDc7.Conj` holds for every pair of splittings (finite algebra; discharges the hypothesis of EDc7). -/
theorem conj_of_splittings (h2 : (2 : ZMod p) ≠ 0) (xs ys xs' ys' : ZMod p)
    (hxy : xs ^ 2 + ys ^ 2 = -1) (hxy' : xs' ^ 2 + ys' ^ 2 = -1) :
    ∃ c : (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ, EDc7.Conj p xs ys xs' ys' c := by
  obtain ⟨c, hc⟩ := exists_red_conjugator p h2 xs ys xs' ys' hxy hxy'
  exact ⟨c, fun x _ => hc x⟩

/-! ### Part B : the isometry on `EY` -/
section PartB
variable (h2 : (2 : ZMod p) ≠ 0) (xs ys xs' ys' : ZMod p)
  (hxy : xs ^ 2 + ys ^ 2 = -1) (hxy' : xs' ^ 2 + ys' ^ 2 = -1)

/-- composition with `e.symm` -/
noncomputable def Lmap (e : SectionA3b.Yp p h2 xs ys hxy ≃ SectionA3b.Yp p h2 xs' ys' hxy') :
    EY p h2 xs ys hxy →ₗ[ℂ] EY p h2 xs' ys' hxy' where
  toFun f := WithLp.toLp 2 (fun y' => f.ofLp (e.symm y'))
  map_add' f g := by ext y; simp
  map_smul' c f := by ext y; simp

variable (e : SectionA3b.Yp p h2 xs ys hxy ≃ SectionA3b.Yp p h2 xs' ys' hxy')

theorem Lmap_apply (f : EY p h2 xs ys hxy) (y' : SectionA3b.Yp p h2 xs' ys' hxy') :
    (Lmap p h2 xs ys xs' ys' hxy hxy' e f).ofLp y' = f.ofLp (e.symm y') := rfl

theorem Lmap_injective : Function.Injective (Lmap p h2 xs ys xs' ys' hxy hxy' e) := by
  intro f g h
  ext y
  have := congrArg (fun F : EY p h2 xs' ys' hxy' => F.ofLp (e y)) h
  simpa [Lmap_apply] using this

theorem Lmap_surjective : Function.Surjective (Lmap p h2 xs ys xs' ys' hxy hxy' e) := by
  intro f'
  refine ⟨WithLp.toLp 2 (fun y => f'.ofLp (e y)), ?_⟩
  ext y'
  simp [Lmap_apply]

open Classical in
theorem Lmap_inner (f g : EY p h2 xs ys hxy) :
    inner ℂ (Lmap p h2 xs ys xs' ys' hxy hxy' e f) (Lmap p h2 xs ys xs' ys' hxy hxy' e g)
      = inner ℂ f g := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, Lmap_apply]
  exact Fintype.sum_equiv e.symm _ _ (fun y' => rfl)

open Classical in
theorem Lmap_oneY :
    Lmap p h2 xs ys xs' ys' hxy hxy' e (oneY p h2 xs ys hxy) = oneY p h2 xs' ys' hxy' := by
  ext y'
  rfl

open Classical in
theorem Lmap_chiE
    (hchi : ∀ y, SectionA4k.chiY p h2 xs' ys' hxy' (e y) = SectionA4k.chiY p h2 xs ys hxy y) :
    Lmap p h2 xs ys xs' ys' hxy hxy' e (chiE p h2 xs ys hxy) = chiE p h2 xs' ys' hxy' := by
  ext y'
  show SectionA4k.chiY p h2 xs ys hxy (e.symm y') = SectionA4k.chiY p h2 xs' ys' hxy' y'
  have := hchi (e.symm y')
  rw [Equiv.apply_symm_apply] at this
  exact this.symm

open Classical in
theorem Lmap_Tl
    (hU : ∀ (n : ℕ) (hn : ¬ p ∣ n) (f : SectionA3b.Yp p h2 xs ys hxy → ℂ)
        (y : SectionA3b.Yp p h2 xs ys hxy),
        SectionA4e.U p h2 xs' ys' hxy' n hn (f ∘ e.symm) (e y) = SectionA4e.U p h2 xs ys hxy n hn f y)
    (n : ℕ) (f : EY p h2 xs ys hxy) :
    Lmap p h2 xs ys xs' ys' hxy hxy' e (Tl p h2 xs ys hxy n f)
      = Tl p h2 xs' ys' hxy' n (Lmap p h2 xs ys xs' ys' hxy hxy' e f) := by
  by_cases h : Adm p n
  · ext y'
    rw [Lmap_apply, Tl_apply p h2 xs ys hxy n h f (e.symm y'),
      Tl_apply p h2 xs' ys' hxy' n h (Lmap p h2 xs ys xs' ys' hxy hxy' e f) y']
    have h1 := hU n h.2 f.ofLp (e.symm y')
    rw [Equiv.apply_symm_apply] at h1
    simp only [SectionA4g.Tn]
    rw [← h1]
    rfl
  · ext y'
    simp [Tl, h, Lmap_apply]

end PartB

/-! ### Part C : conditional reduction -/

open Classical in
/-- `EDc4.RPEigen` at one fixed `(p, xs, ys)`.  OPEN as a hypothesis; never asserted here. -/
def RPEigenAt (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p)
    (hxy : xs ^ 2 + ys ^ 2 = -1) : Prop :=
  ∀ (l : ℕ), l.Prime → l % 4 = 3 → Adm p l →
    ∀ (μ : ℝ) (f : EY p h2 xs ys hxy), f ≠ 0 →
      inner ℂ (oneY p h2 xs ys hxy) f = 0 → inner ℂ (chiE p h2 xs ys hxy) f = 0 →
      Tl p h2 xs ys hxy l f = (μ : ℂ) • f → |μ| ≤ 2 * Real.sqrt l

open Classical in
theorem rpeigenAt_transport (h2 : (2 : ZMod p) ≠ 0) (xs ys xs' ys' : ZMod p)
    (hxy : xs ^ 2 + ys ^ 2 = -1) (hxy' : xs' ^ 2 + ys' ^ 2 = -1)
    (c : (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ) (hc : EDc7.Conj p xs ys xs' ys' c)
    (hR : RPEigenAt p h2 xs ys hxy) : RPEigenAt p h2 xs' ys' hxy' := by
  obtain ⟨e, -, hchi, hU⟩ := EDc7.transport (p := p) (h2 := h2) (xs := xs) (ys := ys) (xs' := xs')
    (ys' := ys') (hxy := hxy) (hxy' := hxy') (c := c) hc
  intro l hl hl4 hA μ f' hf' h1 h2' hT
  obtain ⟨f, hf⟩ := Lmap_surjective p h2 xs ys xs' ys' hxy hxy' e f'
  have hone := Lmap_oneY p h2 xs ys xs' ys' hxy hxy' e
  have hchiE := Lmap_chiE p h2 xs ys xs' ys' hxy hxy' e hchi
  have hTl := Lmap_Tl p h2 xs ys xs' ys' hxy hxy' e hU l f
  refine hR l hl hl4 hA μ f ?_ ?_ ?_ ?_
  · intro h0
    apply hf'
    rw [← hf, h0, map_zero]
  · rw [← Lmap_inner p h2 xs ys xs' ys' hxy hxy' e, hone, hf]; exact h1
  · rw [← Lmap_inner p h2 xs ys xs' ys' hxy hxy' e, hchiE, hf]; exact h2'
  · apply Lmap_injective p h2 xs ys xs' ys' hxy hxy' e
    rw [hTl, map_smul, hf]
    exact hT

open Classical in
/-- Conditional reduction: `RPEigen` at one splitting gives it at every splitting with the same `p`.
The conjugacy `Conj` is supplied by Part A (no hypothesis). -/
theorem rpeigenAt_all (h2 : (2 : ZMod p) ≠ 0) (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1)
    (hR : RPEigenAt p h2 xs ys hxy) (xs' ys' : ZMod p) (hxy' : xs' ^ 2 + ys' ^ 2 = -1) :
    RPEigenAt p h2 xs' ys' hxy' := by
  obtain ⟨c, hc⟩ := conj_of_splittings p h2 xs ys xs' ys' hxy hxy'
  exact rpeigenAt_transport p h2 xs ys xs' ys' hxy hxy' c hc hR

open Classical in
/-- Conditional reduction: it suffices to know `RPEigen` at ONE splitting per prime `p ≡ 3 (mod 4)`, `p > 3`. -/
theorem rpeigen_of_one_splitting
    (H : ∀ (p : ℕ) [Fact p.Prime], p % 4 = 3 → 3 < p → ∀ (h2 : (2 : ZMod p) ≠ 0),
      ∃ (xs ys : ZMod p) (hxy : xs ^ 2 + ys ^ 2 = -1), RPEigenAt p h2 xs ys hxy) :
    EDc4.RPEigen := by
  intro p _ hp3 hp4 h2 xs ys hxy
  obtain ⟨xs0, ys0, hxy0, h0⟩ := H p hp3 hp4 h2
  exact rpeigenAt_all p h2 xs0 ys0 hxy0 h0 xs ys hxy

end EDcSplitTransport

#print axioms EDcSplitTransport.exists_red_conjugator
#print axioms EDcSplitTransport.conj_of_splittings
#print axioms EDcSplitTransport.Lmap_inner
#print axioms EDcSplitTransport.Lmap_Tl
#print axioms EDcSplitTransport.rpeigenAt_transport
#print axioms EDcSplitTransport.rpeigenAt_all
#print axioms EDcSplitTransport.rpeigen_of_one_splitting

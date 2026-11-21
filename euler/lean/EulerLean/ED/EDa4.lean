import Mathlib

namespace EDa4

variable (p : ℕ) [Fact p.Prime]

abbrev GL2 := Matrix.GeneralLinearGroup (Fin 2) (ZMod p)
abbrev PGL2 : Type :=
  (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ ⧸ Subgroup.center (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ

/-- the matrix a + bI, I = [[0,-1],[1,0]]; this is `psi x y a b 0 0` of Stage74a -/
def cm (a b : ZMod p) : Matrix (Fin 2) (Fin 2) (ZMod p) := !![a, -b; b, a]

theorem det_cm (a b : ZMod p) : (cm p a b).det = a ^ 2 + b ^ 2 := by
  simp [cm, Matrix.det_fin_two]; ring

theorem isUnit_cm_iff (a b : ZMod p) : IsUnit (cm p a b) ↔ a ^ 2 + b ^ 2 ≠ 0 := by
  rw [Matrix.isUnit_iff_isUnit_det, det_cm, isUnit_iff_ne_zero]

theorem cm_mul (a b a' b' : ZMod p) :
    cm p a b * cm p a' b' = cm p (a * a' - b * b') (a * b' + b * a') := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cm, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem cm_smul (c a b : ZMod p) : cm p (c * a) (c * b) = c • cm p a b := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cm]

theorem mk_scalar_mul (c : (ZMod p)ˣ) (g : GL2 p) :
    (QuotientGroup.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) c * g) : PGL2 p) = QuotientGroup.mk g := by
  have hz : (Matrix.GeneralLinearGroup.scalar (Fin 2) c) ∈ Subgroup.center (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr hz, one_mul]

/-- the class of an invertible a + bI -/
noncomputable def cls (a b : ZMod p) (h : a ^ 2 + b ^ 2 ≠ 0) : PGL2 p :=
  QuotientGroup.mk ((isUnit_cm_iff p a b).2 h).unit

/-- scaling (a,b) by a unit does not change the class -/
theorem cls_smul (c a b : ZMod p) (hc : c ≠ 0) (h : a ^ 2 + b ^ 2 ≠ 0)
    (h' : (c * a) ^ 2 + (c * b) ^ 2 ≠ 0) :
    cls p (c * a) (c * b) h' = cls p a b h := by
  unfold cls
  have hcu : IsUnit c := isUnit_iff_ne_zero.2 hc
  have : ((isUnit_cm_iff p (c * a) (c * b)).2 h').unit =
      Matrix.GeneralLinearGroup.scalar (Fin 2) hcu.unit * ((isUnit_cm_iff p a b).2 h).unit := by
    apply Units.ext
    simp [cm_smul, Matrix.GeneralLinearGroup.scalar]
    exact Matrix.smul_eq_diagonal_mul _ _
  rw [this, mk_scalar_mul]

/-- the set C_p of classes of invertible a + bI -/
def Cset : Set (PGL2 p) := {g | ∃ (a b : ZMod p) (h : a ^ 2 + b ^ 2 ≠ 0), g = cls p a b h}

noncomputable def rep (o : Option (ZMod p)) : PGL2 p :=
  match o with
  | none => cls p 1 0 (by simp)
  | some s => if h : s ^ 2 + 1 ^ 2 ≠ 0 then cls p s 1 h else cls p 1 0 (by simp)

theorem Cset_subset_range : Cset p ⊆ Set.range (rep p) := by
  rintro g ⟨a, b, h, rfl⟩
  by_cases hb : b = 0
  · subst hb
    have ha : a ≠ 0 := by intro h0; apply h; simp [h0]
    refine ⟨none, ?_⟩
    simp only [rep]
    have h1 : (a * 1) ^ 2 + (a * 0) ^ 2 ≠ 0 := by simpa using h
    have := cls_smul p a 1 0 ha (by simp) h1
    simpa using this.symm
  · refine ⟨some (a / b), ?_⟩
    have hs : (a / b) ^ 2 + 1 ^ 2 ≠ 0 := by
      intro h0
      apply h
      have : a ^ 2 + b ^ 2 = b ^ 2 * ((a / b) ^ 2 + 1 ^ 2) := by field_simp
      rw [this, h0, mul_zero]
    simp only [rep, dif_pos hs]
    have e1 : b * (a / b) = a := by field_simp
    have e2 : b * 1 = b := mul_one b
    have := cls_smul p b (a / b) 1 hb hs (by rw [e1, e2]; exact h)
    simp only [e1, e2] at this
    exact this.symm

theorem Cset_ncard_le : (Cset p).ncard ≤ p + 1 := by
  calc (Cset p).ncard ≤ (Set.range (rep p)).ncard :=
        Set.ncard_le_ncard (Cset_subset_range p) (Set.toFinite _)
    _ ≤ Nat.card (Option (ZMod p)) := by
        rw [← Set.image_univ]
        calc (rep p '' Set.univ).ncard ≤ (Set.univ : Set (Option (ZMod p))).ncard :=
              Set.ncard_image_le (Set.toFinite _)
          _ = Nat.card (Option (ZMod p)) := by simp [Set.ncard_univ]
    _ = p + 1 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_option, ZMod.card]

theorem norm_mul' (a b a' b' : ZMod p) :
    (a * a' - b * b') ^ 2 + (a * b' + b * a') ^ 2 = (a ^ 2 + b ^ 2) * (a' ^ 2 + b' ^ 2) := by ring

theorem cls_mul (a b a' b' : ZMod p) (h : a ^ 2 + b ^ 2 ≠ 0) (h' : a' ^ 2 + b' ^ 2 ≠ 0)
    (h'' : (a * a' - b * b') ^ 2 + (a * b' + b * a') ^ 2 ≠ 0) :
    cls p a b h * cls p a' b' h' = cls p (a * a' - b * b') (a * b' + b * a') h'' := by
  unfold cls
  rw [← QuotientGroup.mk_mul]
  congr 1
  apply Units.ext
  simp [cm_mul]

theorem cls_one : cls p 1 0 (by simp) = 1 := by
  unfold cls
  have : ((isUnit_cm_iff p 1 0).2 (by simp)).unit = 1 := by
    apply Units.ext
    ext i j; fin_cases i <;> fin_cases j <;> simp [cm]
  rw [this]; rfl

theorem cls_congr {a b a' b' : ZMod p} (ha : a = a') (hb : b = b') (h : a ^ 2 + b ^ 2 ≠ 0)
    (h' : a' ^ 2 + b' ^ 2 ≠ 0) : cls p a b h = cls p a' b' h' := by
  subst ha; subst hb; rfl

theorem cls_inv (a b : ZMod p) (h : a ^ 2 + b ^ 2 ≠ 0) (h' : a ^ 2 + (-b) ^ 2 ≠ 0) :
    (cls p a b h)⁻¹ = cls p a (-b) h' := by
  rw [inv_eq_iff_mul_eq_one]
  have hn : (a * a - b * -b) ^ 2 + (a * -b + b * a) ^ 2 ≠ 0 := by
    have : (a * a - b * -b) ^ 2 + (a * -b + b * a) ^ 2 = (a ^ 2 + b ^ 2) ^ 2 := by ring
    rw [this]; exact pow_ne_zero 2 h
  rw [cls_mul p a b a (-b) h h' hn]
  have e := cls_congr p (a := a * a - b * -b) (b := a * -b + b * a)
    (a' := (a ^ 2 + b ^ 2) * 1) (b' := (a ^ 2 + b ^ 2) * 0) (by ring) (by ring) hn
    (by simpa using h)
  rw [e, cls_smul p (a ^ 2 + b ^ 2) 1 0 h (by simp) (by simpa using h)]
  exact cls_one p

/-- C_p as a subgroup of PGL2 -/
noncomputable def Csub : Subgroup (PGL2 p) where
  carrier := Cset p
  one_mem' := ⟨1, 0, by simp, (cls_one p).symm⟩
  mul_mem' := by
    rintro _ _ ⟨a, b, h, rfl⟩ ⟨a', b', h', rfl⟩
    have h'' : (a * a' - b * b') ^ 2 + (a * b' + b * a') ^ 2 ≠ 0 := by
      rw [norm_mul']; exact mul_ne_zero h h'
    exact ⟨_, _, h'', cls_mul p a b a' b' h h' h''⟩
  inv_mem' := by
    rintro _ ⟨a, b, h, rfl⟩
    have h' : a ^ 2 + (-b) ^ 2 ≠ 0 := by simpa using h
    exact ⟨a, -b, h', cls_inv p a b h h'⟩

theorem card_Csub_le : Nat.card (Csub p) ≤ p + 1 := by
  have : Nat.card (Csub p) = (Cset p).ncard := by
    rw [← Nat.card_coe_set_eq]; rfl
  rw [this]; exact Cset_ncard_le p

/-- the matrix of j: [[x, y],[y, -x]] with x^2 + y^2 = -1 -/
def jm (x y : ZMod p) : Matrix (Fin 2) (Fin 2) (ZMod p) := !![x, y; y, -x]

theorem jm_cm (x y a b : ZMod p) : jm p x y * cm p a b = cm p a (-b) * jm p x y := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [jm, cm, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem jm_sq (x y : ZMod p) (h : x ^ 2 + y ^ 2 = -1) : jm p x y * jm p x y = (-1 : ZMod p) • (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [jm, Matrix.mul_apply, Fin.sum_univ_two]
  · rw [← sq, ← sq]; linear_combination h
  · ring
  · ring
  · rw [← sq, ← sq]; linear_combination h

theorem isUnit_jm (x y : ZMod p) (h : x ^ 2 + y ^ 2 = -1) : IsUnit (jm p x y) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  simp [jm, Matrix.det_fin_two]
  intro h0
  have : (-1 : ZMod p) = 0 := by rw [← h]; linear_combination (-1 : ZMod p) * h0
  exact one_ne_zero (neg_eq_zero.1 this)

noncomputable def jcls (x y : ZMod p) (h : x ^ 2 + y ^ 2 = -1) : PGL2 p :=
  QuotientGroup.mk (isUnit_jm p x y h).unit

theorem jcls_cls (x y : ZMod p) (h : x ^ 2 + y ^ 2 = -1) (a b : ZMod p)
    (hab : a ^ 2 + b ^ 2 ≠ 0) (hab' : a ^ 2 + (-b) ^ 2 ≠ 0) :
    jcls p x y h * cls p a b hab = cls p a (-b) hab' * jcls p x y h := by
  unfold jcls cls
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  apply Units.ext
  simp [jm_cm]

theorem jcls_sq (x y : ZMod p) (h : x ^ 2 + y ^ 2 = -1) : jcls p x y h * jcls p x y h = 1 := by
  unfold jcls
  rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Matrix.GeneralLinearGroup.center_eq_range_scalar]
  refine ⟨-1, ?_⟩
  apply Units.ext
  simp [jm_sq p x y h, Matrix.GeneralLinearGroup.scalar]

theorem jcls_normalises (x y : ZMod p) (h : x ^ 2 + y ^ 2 = -1) (c : PGL2 p) :
    c ∈ Csub p ↔ jcls p x y h * c * (jcls p x y h)⁻¹ ∈ Csub p := by
  have key : ∀ c ∈ Csub p, jcls p x y h * c * (jcls p x y h)⁻¹ ∈ Csub p := by
    rintro _ ⟨a, b, hab, rfl⟩
    have hab' : a ^ 2 + (-b) ^ 2 ≠ 0 := by simpa using hab
    rw [jcls_cls p x y h a b hab hab', mul_assoc, mul_inv_cancel, mul_one]
    exact ⟨a, -b, hab', rfl⟩
  have jinv : (jcls p x y h)⁻¹ = jcls p x y h := inv_eq_of_mul_eq_one_right (jcls_sq p x y h)
  constructor
  · exact key c
  · intro hc
    have := key _ hc
    rw [jinv] at this hc
    have e : jcls p x y h * (jcls p x y h * c * jcls p x y h) * jcls p x y h = c := by
      rw [show jcls p x y h * (jcls p x y h * c * jcls p x y h) * jcls p x y h
          = (jcls p x y h * jcls p x y h) * c * (jcls p x y h * jcls p x y h) by group,
        jcls_sq p x y h, one_mul, mul_one]
    rw [e] at this
    exact this

end EDa4
#print axioms EDa4.jcls_normalises
#print axioms EDa4.jcls_sq

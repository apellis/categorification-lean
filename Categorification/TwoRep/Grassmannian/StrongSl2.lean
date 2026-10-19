/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.Grassmannian.Adjunctions
import Categorification.TwoRep.Sl2

/-!
# The categorified irreducible representation of highest weight `2`

The cohomology rings of the Grassmannians `Gr(0,2) = pt`, `Gr(1,2) = ℙ¹` and `Gr(2,2) = pt`,
with induction and restriction bimodules, form a strong 2-representation of `sl₂` in the sense of
S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, Definition 1.2. It categorifies the irreducible representation of highest
weight `2`. This gives a concrete datum for the Cautis–Lauda results, e.g. `StrongSl2.bbw`.

Object `r` has weight `2 r - 2`: `obj 0 = H*(pt)`, `obj 1 = H*(ℙ¹) = k[x]/(x²)` (`x` in
degree `2`), `obj 2 = H*(pt)`, and the zero algebra elsewhere. The 1-morphisms are

* `E 0 = H*(ℙ¹)` as a `(H*(pt), H*(ℙ¹))`-bimodule, `E 1 = H*(ℙ¹)` as a
  `(H*(ℙ¹), H*(pt))`-bimodule, both unshifted;
* `F 0 = E 1 ⟨1⟩`, `F 1 = E 0 ⟨1⟩`;

and the 2-morphisms are the dot `x` on `E 0`, the dot `-x` on `E 1`, and the crossing
`a ⊗ b ↦ -(a b)₁ (1 ⊗ 1)` on `E 0 E 1`, where `(c)₁` is the coefficient of `x`; the scalar
`r_i` is `1`.

## Main definitions

* `Grassmannian.l2 k`: the strong 2-representation, for a field `k` of characteristic zero.
-/

noncomputable section

namespace Categorification.TwoRep.Grassmannian

open CategoryTheory CategoryTheory.Limits TensorProduct Bicategory ZeroObject

universe u

variable (k : Type u) [Field k]

local notation "𝔻" => GrAlg.dual k

/-- The objects: `H*(pt)`, `H*(ℙ¹)`, `H*(pt)` in positions `0, 1, 2`, the zero algebra
elsewhere. -/
def l2Obj : ℤ → GrAlg k
  | .ofNat 0 => GrAlg.unit k
  | .ofNat 1 => GrAlg.dual k
  | .ofNat 2 => GrAlg.unit k
  | _ => GrAlg.trivial k

/-- `E`: `H*(ℙ¹)` as a `(H*(pt), H*(ℙ¹))`-bimodule, then as a `(H*(ℙ¹), H*(pt))`-bimodule. -/
def l2E : ∀ r : ℤ, l2Obj k r ⟶ l2Obj k (r + 1)
  | .ofNat 0 => GBim.up 𝔻 0
  | .ofNat 1 => GBim.down 𝔻 0
  | _ => 0

/-- `F`: `E 1 ⟨1⟩`, then `E 0 ⟨1⟩`. -/
def l2F : ∀ r : ℤ, l2Obj k (r + 1) ⟶ l2Obj k r
  | .ofNat 0 => GBim.down 𝔻 (-1)
  | .ofNat 1 => GBim.up 𝔻 (-1)
  | _ => 0

variable {k}

theorem isZero_id_trivial : IsZero (𝟙 (GrAlg.trivial k)) := by
  have : Subsingleton (𝟙 (GrAlg.trivial k) : GrAlg.trivial k ⟶ GrAlg.trivial k).carrier :=
    inferInstanceAs (Subsingleton PUnit)
  exact GBim.isZero_of_subsingleton _

theorem l2Obj_eq_trivial {r : ℤ} (h0 : r ≠ 0) (h1 : r ≠ 1) (h2 : r ≠ 2) :
    l2Obj k r = GrAlg.trivial k :=
  match r, h0, h1, h2 with
  | .ofNat 0, h0, _, _ => absurd rfl h0
  | .ofNat 1, _, h1, _ => absurd rfl h1
  | .ofNat 2, _, _, h2 => absurd rfl h2
  | .ofNat (_ + 3), _, _, _ => rfl
  | .negSucc _, _, _, _ => rfl

theorem isZero_id_l2Obj {r : ℤ} (h0 : r ≠ 0) (h1 : r ≠ 1) (h2 : r ≠ 2) :
    IsZero (𝟙 (l2Obj k r)) := by
  rw [l2Obj_eq_trivial h0 h1 h2]
  exact isZero_id_trivial

/-! ### Endomorphisms of the identity bimodules -/

namespace GBim

variable {A : GrAlg k} {l : ℤ}

/-- The value at `1` of a 2-morphism `id A ⟶ (id A)⟨l⟩`. -/
def homVal (f : id A ⟶ (id A).shiftObj l) : A := (idEquiv A).symm (f.1 (idEquiv A 1))

theorem hom_idEquiv (f : id A ⟶ (id A).shiftObj l) (b : A) :
    f.1 (idEquiv A b) = idEquiv A (b * homVal f) := by
  have h := hom_actR f b (idEquiv A 1)
  rw [id_actR, mul_one] at h
  rw [h, homVal]
  exact id_actR (A := A) b _

theorem deg_homVal (f : id A ⟶ (id A).shiftObj l) : A.deg (homVal f) = l • homVal f := by
  have h := hom_D f (idEquiv A 1)
  rw [id_D, A.deg_one, map_zero, map_zero, shiftObj_D, LinearMap.sub_apply,
    LinearMap.smul_apply, Module.End.one_apply, hom_idEquiv, one_mul, id_D, eq_comm,
    sub_eq_zero] at h
  exact (idEquiv A).injective (by rw [h, map_zsmul])

theorem hom_eq_zero (f : id A ⟶ (id A).shiftObj l) (h : homVal f = 0) : f = 0 :=
  hom_ext (LinearMap.ext fun x => by
    obtain ⟨x, rfl⟩ := (idEquiv A).surjective x
    rw [hom_idEquiv, h, mul_zero, map_zero]
    rfl)

/-- If every endomorphism of `id A` is right multiplication by a scalar, then `End(id A)` is
one-dimensional. -/
theorem finrank_end_id_eq_one {A : GrAlg k} [Nontrivial A]
    (h : ∀ f : id A ⟶ (id A).shiftObj 0, ∃ c : k, homVal f = algebraMap k A c) :
    Module.finrank k (id A ⟶ id A) = 1 := by
  refine (finrank_eq_one_iff_of_nonzero' (𝟙 (id A)) fun h0 => ?_).mpr fun w => ?_
  · have := congrArg (fun f : id A ⟶ id A => (idEquiv A).symm (f.1 (idEquiv A 1))) h0
    simp only [id_val, LinearMap.id_apply, LinearEquiv.symm_apply_apply, zero_val,
      LinearMap.zero_apply, map_zero] at this
    exact one_ne_zero this
  · obtain ⟨c, hc⟩ := h w
    refine ⟨c, hom_ext (LinearMap.ext fun x => ?_)⟩
    obtain ⟨x, rfl⟩ := (idEquiv A).surjective x
    have hw := hom_idEquiv (l := 0) w x
    rw [hc] at hw
    rw [smul_val, id_val, LinearMap.smul_apply, LinearMap.id_apply]
    refine Eq.trans ?_ hw.symm
    rw [← map_smul, Algebra.smul_def, mul_comm]

end GBim

open GBim

variable [CharZero k] in
theorem homVal_eq_zero_unit {l : ℤ} (hl : l ≠ 0) (f : GBim.id (GrAlg.unit k) ⟶ (GBim.id _).shiftObj l) :
    homVal f = 0 := by
  have h := deg_homVal f
  rw [GrAlg.unit_deg, eq_comm, ← Int.cast_smul_eq_zsmul k] at h
  exact (smul_eq_zero.mp h).resolve_left (Int.cast_ne_zero.mpr hl)

theorem homVal_dual {l : ℤ} (f : GBim.id 𝔻 ⟶ (GBim.id _).shiftObj l) :
    (l : k) * ((GrAlg.dualEquiv k).symm (homVal f)).fst = 0 ∧
      (2 - l : k) * ((GrAlg.dualEquiv k).symm (homVal f)).snd = 0 := by
  have h := congrArg (GrAlg.dualEquiv k).symm (deg_homVal f)
  obtain ⟨a, ha⟩ := (GrAlg.dualEquiv k).surjective (homVal f)
  rw [← ha] at h ⊢
  rw [GrAlg.dual_deg, AlgEquiv.symm_apply_apply, ← Int.cast_smul_eq_zsmul k, map_smul,
    AlgEquiv.symm_apply_apply] at h
  simp only [AlgEquiv.symm_apply_apply]
  refine ⟨?_, ?_⟩
  · have := congrArg TrivSqZeroExt.fst h
    simp only [GrAlg.dualDeg_fst, TrivSqZeroExt.fst_smul, smul_eq_mul] at this
    exact this.symm
  · have := congrArg TrivSqZeroExt.snd h
    simp only [GrAlg.dualDeg_snd, TrivSqZeroExt.snd_smul, smul_eq_mul] at this
    linear_combination this

/-! ### The decomposition `E F 1_2 ≅ 1_2⟨1⟩ ⊕ 1_2⟨-1⟩` -/

namespace GBim

variable {e g : ℤ}

/-- The coefficient of `1`, `a ⊗ b ↦ (a b)₀`. -/
def fstₗ (e g : ℤ) : (comp (up 𝔻 g) (down 𝔻 e)).carrier →ₗ[k] (id (GrAlg.unit k)).carrier :=
  cdesc (TensorProduct.lift (LinearMap.mk₂ k (fun x y => idEquiv _ (GrAlg.unitEquiv k
      ((GrAlg.dualEquiv k).symm ((upEquiv 𝔻 g).symm x * (downEquiv 𝔻 e).symm y)).fst))
      (fun _ _ _ => by simp [add_mul, -TrivSqZeroExt.fst_mul, -map_mul])
      (fun _ _ _ => by simp [-TrivSqZeroExt.fst_mul, -map_mul]; rw [← smul_eq_mul, map_smul, map_smul])
      (fun _ _ _ => by simp [mul_add, -TrivSqZeroExt.fst_mul, -map_mul])
      (fun _ _ _ => by simp [-TrivSqZeroExt.fst_mul, -map_mul]; rw [← smul_eq_mul, map_smul, map_smul])))
    (fun b x y => by
      obtain ⟨x, rfl⟩ := (upEquiv 𝔻 g).surjective x
      obtain ⟨y, rfl⟩ := (downEquiv 𝔻 e).surjective y
      simp [mul_assoc, mul_left_comm _ b, -TrivSqZeroExt.fst_mul, -map_mul])

@[simp] theorem fstₗ_tmk (x y : DualNumber k) :
    fstₗ e g (tmk _ _ (upEquiv 𝔻 g (GrAlg.dualEquiv k x) ⊗ₜ downEquiv 𝔻 e (GrAlg.dualEquiv k y))) =
      idEquiv _ (GrAlg.unitEquiv k (x * y).fst) := rfl

theorem cast_add_add_one (h : e + g = -1) : (e : k) + g + 1 = 0 := by
  have := congrArg (Int.cast : ℤ → k) (show e + g + 1 = 0 by omega)
  push_cast at this
  exact this

/-- The projection onto `1⟨1⟩`. -/
def splitFst (h : e + g = -1) : comp (up 𝔻 g) (down 𝔻 e) ⟶ (id (GrAlg.unit k)).shiftObj 1 :=
  mkHomₗ (fstₗ e g)
    (fun c => comp_ext fun x y => by
      obtain ⟨x, rfl⟩ := ((GrAlg.dualEquiv k).toLinearEquiv.trans (upEquiv 𝔻 g)).surjective x
      obtain ⟨y, rfl⟩ := ((GrAlg.dualEquiv k).toLinearEquiv.trans (downEquiv 𝔻 e)).surjective y
      obtain ⟨c, rfl⟩ := (GrAlg.unitEquiv k).surjective c
      simp only [LinearEquiv.trans_apply, AlgEquiv.toLinearEquiv_apply, LinearMap.comp_apply,
        comp_actL_tmk, up_actL, ← map_smul, fstₗ_tmk]
      exact congrArg (idEquiv _) (by
        simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_smul, smul_eq_mul, map_mul]
        change c * x.fst * y.fst = c * (x.fst * y.fst)
        ring))
    (fun c => comp_ext fun x y => by
      obtain ⟨x, rfl⟩ := ((GrAlg.dualEquiv k).toLinearEquiv.trans (upEquiv 𝔻 g)).surjective x
      obtain ⟨y, rfl⟩ := ((GrAlg.dualEquiv k).toLinearEquiv.trans (downEquiv 𝔻 e)).surjective y
      obtain ⟨c, rfl⟩ := (GrAlg.unitEquiv k).surjective c
      simp only [LinearEquiv.trans_apply, AlgEquiv.toLinearEquiv_apply, LinearMap.comp_apply,
        comp_actR_tmk, down_actR, ← map_smul, fstₗ_tmk]
      exact congrArg (idEquiv _) (by
        simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_smul, smul_eq_mul, map_mul]
        change x.fst * (c * y.fst) = c * (x.fst * y.fst)
        ring))
    (comp_ext fun x y => by
      obtain ⟨x, rfl⟩ := ((GrAlg.dualEquiv k).toLinearEquiv.trans (upEquiv 𝔻 g)).surjective x
      obtain ⟨y, rfl⟩ := ((GrAlg.dualEquiv k).toLinearEquiv.trans (downEquiv 𝔻 e)).surjective y
      have h' := cast_add_add_one (k := k) h
      simp only [LinearEquiv.trans_apply, AlgEquiv.toLinearEquiv_apply, LinearMap.comp_apply,
        comp_D_tmk, up_D, down_D, GrAlg.dual_deg, ← Int.cast_smul_eq_zsmul k, map_add, tmul_add,
        add_tmul, ← smul_tmul', tmul_smul, map_smul, fstₗ_tmk, shiftObj_D, LinearMap.sub_apply,
        LinearMap.smul_apply, Module.End.one_apply, unit_id_D]
      simp only [← map_smul, ← map_add, ← map_neg, zero_sub]
      congr 2
      simp only [TrivSqZeroExt.fst_mul, GrAlg.dualDeg_fst, smul_eq_mul, zero_mul, mul_zero]
      push_cast
      linear_combination (x.fst * y.fst) * h')

/-- The projection onto `1⟨-1⟩`. -/
def splitSnd (h : e + g = -1) : comp (up 𝔻 g) (down 𝔻 e) ⟶ (id (GrAlg.unit k)).shiftObj (-1) :=
  mkHomₗ (traceₗ e g)
    (fun c => comp_ext fun x y => by
      obtain ⟨x, rfl⟩ := ((GrAlg.dualEquiv k).toLinearEquiv.trans (upEquiv 𝔻 g)).surjective x
      obtain ⟨y, rfl⟩ := ((GrAlg.dualEquiv k).toLinearEquiv.trans (downEquiv 𝔻 e)).surjective y
      obtain ⟨c, rfl⟩ := (GrAlg.unitEquiv k).surjective c
      simp only [LinearEquiv.trans_apply, AlgEquiv.toLinearEquiv_apply, LinearMap.comp_apply,
        comp_actL_tmk, up_actL, ← map_smul, traceₗ_tmk]
      exact congrArg (idEquiv _) (by
        simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_smul, TrivSqZeroExt.fst_smul,
          smul_eq_mul, op_smul_eq_mul]
        change c * x.fst * y.snd + c * x.snd * y.fst = c * (x.fst * y.snd + x.snd * y.fst)
        ring))
    (fun c => comp_ext fun x y => by
      obtain ⟨x, rfl⟩ := ((GrAlg.dualEquiv k).toLinearEquiv.trans (upEquiv 𝔻 g)).surjective x
      obtain ⟨y, rfl⟩ := ((GrAlg.dualEquiv k).toLinearEquiv.trans (downEquiv 𝔻 e)).surjective y
      obtain ⟨c, rfl⟩ := (GrAlg.unitEquiv k).surjective c
      simp only [LinearEquiv.trans_apply, AlgEquiv.toLinearEquiv_apply, LinearMap.comp_apply,
        comp_actR_tmk, down_actR, ← map_smul, traceₗ_tmk]
      exact congrArg (idEquiv _) (by
        simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_smul, TrivSqZeroExt.fst_smul,
          smul_eq_mul, op_smul_eq_mul]
        change x.fst * (c * y.snd) + x.snd * (c * y.fst) = c * (x.fst * y.snd + x.snd * y.fst)
        ring))
    (comp_ext fun x y => by
      obtain ⟨x, rfl⟩ := ((GrAlg.dualEquiv k).toLinearEquiv.trans (upEquiv 𝔻 g)).surjective x
      obtain ⟨y, rfl⟩ := ((GrAlg.dualEquiv k).toLinearEquiv.trans (downEquiv 𝔻 e)).surjective y
      have h' := cast_add_add_one (k := k) h
      simp only [LinearEquiv.trans_apply, AlgEquiv.toLinearEquiv_apply, LinearMap.comp_apply,
        comp_D_tmk, up_D, down_D, GrAlg.dual_deg, ← Int.cast_smul_eq_zsmul k, map_add, tmul_add,
        add_tmul, ← smul_tmul', tmul_smul, map_smul, traceₗ_tmk, shiftObj_D, LinearMap.sub_apply,
        LinearMap.smul_apply, Module.End.one_apply, unit_id_D]
      simp only [← map_smul, ← map_add, ← map_neg, zero_sub]
      congr 2
      simp only [TrivSqZeroExt.snd_mul, GrAlg.dualDeg_fst, GrAlg.dualDeg_snd, smul_eq_mul,
        op_smul_eq_mul]
      push_cast
      linear_combination (x.fst * y.snd + x.snd * y.fst) * h')

/-- `k` as the carrier of the identity bimodule of `H*(pt)`. -/
def unitVec : k ≃ₗ[k] (id (GrAlg.unit k)).carrier :=
  (GrAlg.unitEquiv k).toLinearEquiv.trans (idEquiv _)

theorem unitVec_def (c : k) : idEquiv (GrAlg.unit k) (GrAlg.unitEquiv k c) = unitVec c := rfl

theorem actL_unit {B : GrAlg k} (X : GBim (GrAlg.unit k) B) (a : (GrAlg.unit k).carrier)
    (v : X) : X.actL a v = ((GrAlg.unitEquiv k).symm a) • v := by
  have := X.actL.commutes ((GrAlg.unitEquiv k).symm a)
  exact LinearMap.congr_fun this v

theorem actR_unit {A : GrAlg k} (X : GBim A (GrAlg.unit k)) (a : (GrAlg.unit k).carrier)
    (v : X) : X.actR a v = ((GrAlg.unitEquiv k).symm a) • v := by
  have := X.actR.commutes ((GrAlg.unitEquiv k).symm a)
  exact LinearMap.congr_fun this v

theorem unitShift_D (m : ℤ) (x : k) :
    ((id (GrAlg.unit k)).shiftObj m).D (unitVec (k := k) x) = unitVec (k := k) (-(m : k) * x) := by
  rw [shiftObj_D, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    show (id (GrAlg.unit k)).D (unitVec (k := k) x) = 0 from unit_id_D x, zero_sub,
    ← Int.cast_smul_eq_zsmul k, ← map_smul, ← map_neg, smul_eq_mul, neg_mul]

/-- `c ↦ c v`. -/
def inclₗ {M : Type*} [AddCommGroup M] [Module k M] (v : M) :
    (id (GrAlg.unit k)).carrier →ₗ[k] M :=
  LinearMap.toSpanSingleton k _ v ∘ₗ (unitVec (k := k)).symm.toLinearMap

@[simp] theorem inclₗ_apply {M : Type*} [AddCommGroup M] [Module k M] (v : M) (c : k) :
    inclₗ v (unitVec (k := k) c) = c • v := by
  simp [inclₗ]

/-- `c ↦ c v`, for `v` a vector of degree `n`. -/
def unitIncl {X : GBim (GrAlg.unit k) (GrAlg.unit k)} (n : ℤ) (v : X) (hv : X.D v = -(n • v)) :
    (id (GrAlg.unit k)).shiftObj n ⟶ X :=
  mkHom (inclₗ v)
    (fun a x => by
      obtain ⟨x, rfl⟩ := (unitVec (k := k)).surjective x
      obtain ⟨a, rfl⟩ := (GrAlg.unitEquiv k).surjective a
      rw [actL_unit, actL_unit, ← map_smul, inclₗ_apply, inclₗ_apply, smul_smul]
      rfl)
    (fun a x => by
      obtain ⟨x, rfl⟩ := (unitVec (k := k)).surjective x
      obtain ⟨a, rfl⟩ := (GrAlg.unitEquiv k).surjective a
      rw [actR_unit, actR_unit, ← map_smul, inclₗ_apply, inclₗ_apply, smul_smul]
      rfl)
    (fun x => by
      obtain ⟨x, rfl⟩ := (unitVec (k := k)).surjective x
      rw [unitShift_D, inclₗ_apply, inclₗ_apply, map_smul, hv, ← Int.cast_smul_eq_zsmul k,
        smul_neg, smul_smul, ← neg_smul]
      congr 1
      ring)

@[simp] theorem unitIncl_apply {X : GBim (GrAlg.unit k) (GrAlg.unit k)} (n : ℤ) (v : X) (hv)
    (c : k) : (unitIncl n v hv).1 (unitVec (k := k) c) = c • v :=
  inclₗ_apply v c

variable (e g) in
/-- The class of `x ⊗ y` in `up (dual k) g ⊗ down (dual k) e`. -/
abbrev tv (x y : DualNumber k) : (comp (up 𝔻 g) (down 𝔻 e)).carrier :=
  tmk _ _ (upEquiv 𝔻 g (GrAlg.dualEquiv k x) ⊗ₜ downEquiv 𝔻 e (GrAlg.dualEquiv k y))

theorem tv_eq (x y : DualNumber k) :
    tv e g x y = (x * y).fst • tv e g 1 1 + (x * y).snd • tv e g 1 DualNumber.eps := by
  have h1 : tv e g x y = tv e g 1 (x * y) := by
    have := tmk_actR (X := up 𝔻 g) (Y := down 𝔻 e) (GrAlg.dualEquiv k x)
      (upEquiv 𝔻 g (GrAlg.dualEquiv k 1)) (downEquiv 𝔻 e (GrAlg.dualEquiv k y))
    simp only [up_actR, down_actL, ← map_mul, mul_one] at this
    exact this
  rw [h1]
  have h2 : x * y = (x * y).fst • (1 : DualNumber k) + (x * y).snd • DualNumber.eps := by
    ext <;> simp
  conv_lhs => rw [h2]
  simp only [tv, map_add, map_smul, tmul_add, tmul_smul]

theorem tv_D (x y : DualNumber k) :
    (comp (up 𝔻 g) (down 𝔻 e)).D (tv e g x y) =
      tv e g (GrAlg.dualDeg x) y + tv e g x (GrAlg.dualDeg y) + (g + e : ℤ) • tv e g x y := by
  simp only [tv, comp_D_tmk, up_D, down_D, GrAlg.dual_deg, tmul_add, add_tmul, map_add,
    ← smul_tmul', tmul_smul, map_zsmul, add_smul]
  abel

theorem tv_one_one_D' : (comp (up 𝔻 0) (down 𝔻 0)).D (tv 0 0 1 1) = 0 := by
  rw [tv_D, show GrAlg.dualDeg (1 : DualNumber k) = 0 by ext <;> simp]
  simp [tv]

theorem tv_one_one_D (h : e + g = -1) :
    (comp (up 𝔻 g) (down 𝔻 e)).D (tv e g 1 1) = -((1 : ℤ) • tv e g 1 1) := by
  rw [tv_D, show GrAlg.dualDeg (1 : DualNumber k) = 0 by ext <;> simp, show g + e = -1 by omega]
  simp [tv]

theorem tv_one_eps_D (h : e + g = -1) :
    (comp (up 𝔻 g) (down 𝔻 e)).D (tv e g 1 DualNumber.eps) =
      -((-1 : ℤ) • tv e g 1 DualNumber.eps) := by
  rw [tv_D, show GrAlg.dualDeg (1 : DualNumber k) = 0 by ext <;> simp, GrAlg.dualDeg_eps,
    show g + e = -1 by omega]
  simp only [tv, map_zero, zero_tmul, map_smul, tmul_smul, zero_add]
  rw [← Int.cast_smul_eq_zsmul k, ← add_smul, ← neg_smul]
  congr 1
  norm_num

theorem smul_unitVec_one (c : k) : c • unitVec (k := k) 1 = unitVec c := by
  rw [← map_smul, smul_eq_mul, mul_one]

theorem splitFst_tv (h : e + g = -1) (x y : DualNumber k) :
    (splitFst h).1 (tv e g x y) = unitVec (x * y).fst := rfl

theorem splitSnd_tv (h : e + g = -1) (x y : DualNumber k) :
    (splitSnd h).1 (tv e g x y) = unitVec (x * y).snd := rfl

/-- `up (dual k) g ⊗ down (dual k) e ≅ 1⟨1⟩ ⊕ 1⟨-1⟩` for `e + g = -1`: `H*(P¹) ≅ k ⊕ k⟨-2⟩`
as a graded vector space. -/
def splitIso (h : e + g = -1) :
    comp (up 𝔻 g) (down 𝔻 e) ≅ (id (GrAlg.unit k)).shiftObj 1 ⊞ (id (GrAlg.unit k)).shiftObj (-1) :=
  KrullSchmidtCat.isoOfData (unitIncl 1 (tv e g 1 1) (tv_one_one_D h)) (splitFst h)
    (unitIncl (-1) (tv e g 1 DualNumber.eps) (tv_one_eps_D h)) (splitSnd h)
    (hom_ext (LinearMap.ext fun v => by
      obtain ⟨c, rfl⟩ := (unitVec (k := k)).surjective v
      simp only [splitFst, comp_val, mkHomₗ_val, LinearMap.comp_apply]
      rw [unitIncl_apply, map_smul, fstₗ_tmk, ← unitVec_def]
      simp
      exact smul_unitVec_one c))
    (hom_ext (LinearMap.ext fun v => by
      obtain ⟨c, rfl⟩ := (unitVec (k := k)).surjective v
      simp only [splitSnd, comp_val, mkHomₗ_val, LinearMap.comp_apply]
      rw [unitIncl_apply, map_smul, traceₗ_tmk, ← unitVec_def]
      simp
      exact smul_unitVec_one c))
    (hom_ext (LinearMap.ext fun v => by
      obtain ⟨c, rfl⟩ := (unitVec (k := k)).surjective v
      simp only [splitSnd, comp_val, mkHomₗ_val, LinearMap.comp_apply]
      rw [unitIncl_apply, map_smul, traceₗ_tmk, ← unitVec_def]
      simp))
    (hom_ext (LinearMap.ext fun v => by
      obtain ⟨c, rfl⟩ := (unitVec (k := k)).surjective v
      simp only [splitFst, comp_val, mkHomₗ_val, LinearMap.comp_apply]
      rw [unitIncl_apply, map_smul, fstₗ_tmk, ← unitVec_def]
      simp))
    (hom_ext (comp_ext fun x y => by
      obtain ⟨x, rfl⟩ := ((GrAlg.dualEquiv k).toLinearEquiv.trans (upEquiv 𝔻 g)).surjective x
      obtain ⟨y, rfl⟩ := ((GrAlg.dualEquiv k).toLinearEquiv.trans (downEquiv 𝔻 e)).surjective y
      change (splitFst h ≫ unitIncl 1 _ (tv_one_one_D h) +
        splitSnd h ≫ unitIncl (-1) _ (tv_one_eps_D h)).1 (tv e g x y) = tv e g x y
      rw [add_val, LinearMap.add_apply, comp_val, comp_val, LinearMap.comp_apply,
        LinearMap.comp_apply, splitFst_tv, splitSnd_tv, unitIncl_apply, unitIncl_apply, tv_eq x y]))

/-! ### Dots and crossings -/

section Action

variable {A B : GrAlg k}

/-- Right multiplication by `b` of degree `n`, `X ⟶ X⟨n⟩`. -/
def actRHom (X : GBim A B) (n : ℤ) (b : B) (hb : B.deg b = n • b) : X ⟶ X.shiftObj n :=
  mkHom (X.actR b)
    (fun a x => (LinearMap.congr_fun (X.comm a b) x).symm)
    (fun b' x => by
      simp only [← Module.End.mul_apply, ← map_mul, mul_comm])
    (fun x => by
      have := LinearMap.congr_fun (X.D_actR b) x
      simp only [Module.End.mul_apply, LinearMap.add_apply, hb, map_zsmul,
        LinearMap.smul_apply] at this
      rw [shiftObj_D, LinearMap.sub_apply, this, LinearMap.smul_apply, Module.End.one_apply]
      abel)

/-- Left multiplication by `a` of degree `n`, `X ⟶ X⟨n⟩`. -/
def actLHom (X : GBim A B) (n : ℤ) (a : A) (ha : A.deg a = n • a) : X ⟶ X.shiftObj n :=
  mkHom (X.actL a)
    (fun a' x => by
      simp only [← Module.End.mul_apply, ← map_mul, mul_comm])
    (fun b x => LinearMap.congr_fun (X.comm a b) x)
    (fun x => by
      have := LinearMap.congr_fun (X.D_actL a) x
      simp only [Module.End.mul_apply, LinearMap.add_apply, ha, map_zsmul,
        LinearMap.smul_apply] at this
      rw [shiftObj_D, LinearMap.sub_apply, this, LinearMap.smul_apply, Module.End.one_apply]
      abel)

@[simp] theorem actRHom_val (X : GBim A B) (n : ℤ) (b : B) (hb) :
    (actRHom X n b hb).1 = X.actR b := rfl

@[simp] theorem actLHom_val (X : GBim A B) (n : ℤ) (a : A) (ha) :
    (actLHom X n a ha).1 = X.actL a := rfl

end Action

/-- A linear map between `(k, k)`-bimodules commuting with the degree operators. -/
def unitHom {X Y : GBim (GrAlg.unit k) (GrAlg.unit k)} (f : X →ₗ[k] Y)
    (hD : ∀ x, f (X.D x) = Y.D (f x)) : X ⟶ Y :=
  mkHom f (fun a x => by rw [actL_unit, actL_unit, map_smul])
    (fun a x => by rw [actR_unit, actR_unit, map_smul]) hD

@[simp] theorem unitHom_val {X Y : GBim (GrAlg.unit k) (GrAlg.unit k)} (f : X →ₗ[k] Y) (hD) :
    (unitHom f hD).1 = f := rfl

theorem dual_deg_eps :
    (GrAlg.dual k).deg (GrAlg.dualEquiv k DualNumber.eps) =
      (2 : ℤ) • GrAlg.dualEquiv k DualNumber.eps := by
  rw [GrAlg.dual_deg, GrAlg.dualDeg_eps, map_smul, ← Int.cast_smul_eq_zsmul k]
  norm_num

/-- The crossing on `up (dual k) 0 ⊗ down (dual k) 0`: `x ⊗ y ↦ -(x y)₁ (1 ⊗ 1)`. -/
def crossₗ : (comp (up 𝔻 0) (down 𝔻 0)).carrier →ₗ[k] (comp (up 𝔻 0) (down 𝔻 0)).carrier :=
  -(inclₗ (tv 0 0 1 1) ∘ₗ traceₗ 0 0)

theorem crossₗ_tv (x y : DualNumber k) :
    crossₗ (tv 0 0 x y) = -((x * y).snd • tv 0 0 1 1) := by
  simp only [crossₗ, LinearMap.neg_apply, LinearMap.comp_apply, traceₗ_tmk, unitVec_def,
    inclₗ_apply]

/-- The crossing, of degree `-2`. -/
def crossHom : comp (up 𝔻 0) (down 𝔻 0) ⟶ (comp (up 𝔻 0) (down 𝔻 0)).shiftObj (-2) :=
  unitHom crossₗ fun t => by
    induction t using comp_induction with
    | hadd p q hp hq => simp only [map_add, hp, hq]
    | ht x y =>
      obtain ⟨x, rfl⟩ := ((GrAlg.dualEquiv k).toLinearEquiv.trans (upEquiv 𝔻 0)).surjective x
      obtain ⟨y, rfl⟩ := ((GrAlg.dualEquiv k).toLinearEquiv.trans (downEquiv 𝔻 0)).surjective y
      change crossₗ ((comp (up 𝔻 0) (down 𝔻 0)).D (tv 0 0 x y)) =
        ((comp (up 𝔻 0) (down 𝔻 0)).shiftObj (-2)).D (crossₗ (tv 0 0 x y))
      rw [tv_D, shiftObj_D, LinearMap.sub_apply, map_add, map_add, crossₗ_tv, crossₗ_tv,
        crossₗ_tv]
      simp only [map_neg, map_smul, tv_one_one_D', LinearMap.smul_apply, Module.End.one_apply,
        TrivSqZeroExt.snd_mul, GrAlg.dualDeg_fst, GrAlg.dualDeg_snd, smul_eq_mul,
        op_smul_eq_mul, add_zero, zero_smul, smul_zero, neg_zero, map_zero]
      rw [← Int.cast_smul_eq_zsmul k]
      module

theorem tv_ext {e g : ℤ} {M : Type*} [AddCommGroup M] [Module k M]
    {f f' : (comp (up 𝔻 g) (down 𝔻 e)).carrier →ₗ[k] M}
    (h : ∀ x y, f (tv e g x y) = f' (tv e g x y)) : f = f' :=
  comp_ext fun x y => by
    obtain ⟨x, rfl⟩ := ((GrAlg.dualEquiv k).toLinearEquiv.trans (upEquiv 𝔻 g)).surjective x
    obtain ⟨y, rfl⟩ := ((GrAlg.dualEquiv k).toLinearEquiv.trans (downEquiv 𝔻 e)).surjective y
    exact h x y

end GBim

open GBim

/-! ### Values of shifted 2-morphisms -/

section Values

variable {A B C : GrAlg k}

/-- The underlying linear map of a 2-morphism of `GrAlg k`. -/
def hv {X Y : A ⟶ B} (f : X ⟶ Y) : GBim.carrier X →ₗ[k] GBim.carrier Y :=
  (show (X : GBim A B) ⟶ (Y : GBim A B) from f).1

/-- The underlying linear map of a shifted 2-morphism (a shift does not change carriers). -/
def shv {X Y : A ⟶ B} {a : ℤ} (f : ShiftedHom X Y a) : GBim.carrier X →ₗ[k] GBim.carrier Y :=
  hv (Y := Y⟦a⟧) f

theorem shv_ext {X Y : A ⟶ B} {a : ℤ} {f g : ShiftedHom X Y a} (h : shv f = shv g) : f = g :=
  hom_ext h

theorem shv_sub {X Y : A ⟶ B} {a : ℤ} (f g : ShiftedHom X Y a) : shv (f - g) = shv f - shv g :=
  rfl

theorem shv_zero {X Y : A ⟶ B} {a : ℤ} : shv (0 : ShiftedHom X Y a) = 0 := rfl

theorem shv_comp {X Y Z : A ⟶ B} {a b c : ℤ} (f : ShiftedHom X Y a)
    (g : ShiftedHom Y Z b) (h : b + a = c) : shv (f.comp g h) = shv g ∘ₗ shv f := by
  subst h
  simp only [ShiftedHom.comp, shiftFunctorAdd'_eq_shiftFunctorAdd]
  rfl

theorem shv_mk₀_smul_id {X : A ⟶ B} (c : k) :
    shv (ShiftedHom.mk₀ (0 : ℤ) rfl (c • 𝟙 X)) = c • LinearMap.id := by
  simp only [ShiftedHom.mk₀, shiftFunctorZero', Iso.trans_inv, NatTrans.comp_app,
    eqToIso_refl, Iso.refl_inv, NatTrans.id_app]
  rfl

end Values

/-! ### The nil-Hecke action on `E E 1_{-2}` -/

/-- `E 1_{-2}` as a 1-morphism of `GrAlg k`. -/
abbrev E0 : GrAlg.unit k ⟶ 𝔻 := up 𝔻 0

/-- `E 1_0` as a 1-morphism of `GrAlg k`. -/
abbrev E1 : 𝔻 ⟶ GrAlg.unit k := down 𝔻 0

/-- The generators `x ⊗ y` of `E E 1_{-2}`. -/
def tv0 (x y : DualNumber k) : GBim.carrier (E0 (k := k) ≫ E1) := tv 0 0 x y

theorem tv0_eq (x y : DualNumber k) :
    tv0 x y = (x * y).fst • tv0 1 1 + (x * y).snd • tv0 1 DualNumber.eps :=
  tv_eq x y

theorem tv0_ext {M : Type*} [AddCommGroup M] [Module k M]
    {f f' : GBim.carrier (E0 (k := k) ≫ E1) →ₗ[k] M} (h : ∀ x y, f (tv0 x y) = f' (tv0 x y)) :
    f = f' :=
  tv_ext h

/-- The dot on `E 1_{-2} = up (dual k) 0`: multiplication by `x`. -/
def dot0 : ShiftedHom (E0 (k := k)) E0 (2 : ℤ) :=
  actRHom _ 2 _ dual_deg_eps

/-- The dot on `E 1_0 = down (dual k) 0`: multiplication by `-x`. -/
def dot1 : ShiftedHom (E1 (k := k)) E1 (2 : ℤ) :=
  -actLHom _ 2 _ dual_deg_eps

/-- The crossing on `E E 1_{-2}`. -/
def cross0 : ShiftedHom (E0 (k := k) ≫ E1) (E0 ≫ E1) (-2 : ℤ) :=
  crossHom

theorem wl_dot1_tv (x y : DualNumber k) :
    shv (shWhiskerLeft E0 dot1) (tv0 x y) = -tv0 x (DualNumber.eps * y) := by
  have : shv (shWhiskerLeft E0 dot1) (tv0 x y) = tmk (up 𝔻 0) (down 𝔻 0)
      (upEquiv 𝔻 0 (GrAlg.dualEquiv k x) ⊗ₜ
        (-downEquiv 𝔻 0 (GrAlg.dualEquiv k (DualNumber.eps * y)))) := by
    rw [map_mul]; rfl
  rw [this, tmul_neg, map_neg]
  rfl

theorem wr_dot0_tv (x y : DualNumber k) :
    shv (shWhiskerRight dot0 E1) (tv0 x y) = tv0 (DualNumber.eps * x) y := by
  have : tv0 (DualNumber.eps * x) y = tmk (up 𝔻 0) (down 𝔻 0)
      (upEquiv 𝔻 0 (GrAlg.dualEquiv k DualNumber.eps * GrAlg.dualEquiv k x) ⊗ₜ
        downEquiv 𝔻 0 (GrAlg.dualEquiv k y)) := by
    rw [← map_mul]; rfl
  rw [this]; rfl

theorem cross0_tv (x y : DualNumber k) :
    shv (cross0 (k := k)) (tv0 x y) = -((x * y).snd • tv0 1 1) :=
  crossₗ_tv x y

theorem cross0_sq : (cross0 (k := k)).comp cross0 (by norm_num : (-2 : ℤ) + -2 = -4) = 0 :=
  shv_ext (tv0_ext fun x y => by
    rw [shv_comp, LinearMap.comp_apply, cross0_tv, map_neg, map_smul, cross0_tv, shv_zero]
    simp)

theorem dot_slide_left0 :
    ShiftedHom.mk₀ (0 : ℤ) rfl (((1 : kˣ) : k) • 𝟙 (E0 (k := k) ≫ E1)) =
      (shWhiskerLeft E0 dot1).comp cross0 (by norm_num : (-2 : ℤ) + 2 = 0) -
        cross0.comp (shWhiskerRight dot0 E1) (by norm_num : (2 : ℤ) + -2 = 0) :=
  shv_ext (tv0_ext fun x y => by
    rw [shv_mk₀_smul_id, shv_sub, LinearMap.sub_apply, shv_comp, shv_comp, LinearMap.comp_apply,
      LinearMap.comp_apply, wl_dot1_tv, cross0_tv, map_neg, cross0_tv, map_neg, map_smul,
      wr_dot0_tv]
    rw [LinearMap.smul_apply, LinearMap.id_apply, tv0_eq x y, tv0_eq (DualNumber.eps * 1) 1]
    simp only [Units.val_one, one_smul, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul,
      DualNumber.fst_eps, DualNumber.snd_eps, TrivSqZeroExt.fst_one, TrivSqZeroExt.snd_one,
      smul_eq_mul, op_smul_eq_mul]
    module)

theorem dot_slide_right0 :
    ShiftedHom.mk₀ (0 : ℤ) rfl (((1 : kˣ) : k) • 𝟙 (E0 (k := k) ≫ E1)) =
      cross0.comp (shWhiskerLeft E0 dot1) (by norm_num : (2 : ℤ) + -2 = 0) -
        (shWhiskerRight dot0 E1).comp cross0 (by norm_num : (-2 : ℤ) + 2 = 0) :=
  shv_ext (tv0_ext fun x y => by
    rw [shv_mk₀_smul_id, shv_sub, LinearMap.sub_apply, shv_comp, shv_comp, LinearMap.comp_apply,
      LinearMap.comp_apply, cross0_tv, map_neg, map_smul, wl_dot1_tv, wr_dot0_tv, cross0_tv]
    rw [LinearMap.smul_apply, LinearMap.id_apply, tv0_eq x y, tv0_eq 1 (DualNumber.eps * 1)]
    simp only [Units.val_one, one_smul, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul,
      DualNumber.fst_eps, DualNumber.snd_eps, TrivSqZeroExt.fst_one, TrivSqZeroExt.snd_one,
      smul_eq_mul, op_smul_eq_mul]
    module)

variable [CharZero k]

theorem subsingleton_hom_unit {l : ℤ} (hl : l ≠ 0) :
    Subsingleton (GBim.id (GrAlg.unit k) ⟶ (GBim.id _).shiftObj l) :=
  ⟨fun f g => (hom_eq_zero f (homVal_eq_zero_unit hl f)).trans
    (hom_eq_zero g (homVal_eq_zero_unit hl g)).symm⟩

theorem homVal_eq_zero_dual {l : ℤ} (hl : l < 0) (f : GBim.id 𝔻 ⟶ (GBim.id _).shiftObj l) :
    homVal f = 0 := by
  obtain ⟨h1, h2⟩ := homVal_dual f
  have hl0 : (l : k) ≠ 0 := Int.cast_ne_zero.mpr hl.ne
  have hl2 : (2 - l : k) ≠ 0 := by
    have : ((2 - l : ℤ) : k) ≠ 0 := Int.cast_ne_zero.mpr (by omega)
    push_cast at this
    exact this
  apply (GrAlg.dualEquiv k).symm.injective
  rw [map_zero]
  ext
  · exact (mul_eq_zero.mp h1).resolve_left hl0
  · exact (mul_eq_zero.mp h2).resolve_left hl2

theorem subsingleton_hom_dual {l : ℤ} (hl : l < 0) :
    Subsingleton (GBim.id 𝔻 ⟶ (GBim.id _).shiftObj l) :=
  ⟨fun f g => (hom_eq_zero f (homVal_eq_zero_dual hl f)).trans
    (hom_eq_zero g (homVal_eq_zero_dual hl g)).symm⟩

omit [CharZero k] in
theorem finrank_end_id_unit : Module.finrank k (GBim.id (GrAlg.unit k) ⟶ GBim.id _) = 1 :=
  have : Nontrivial (GrAlg.unit k) := inferInstanceAs (Nontrivial k)
  finrank_end_id_eq_one fun f => ⟨homVal f, rfl⟩

theorem finrank_end_id_dual : Module.finrank k (GBim.id 𝔻 ⟶ GBim.id _) = 1 := by
  have : Nontrivial 𝔻 := inferInstanceAs (Nontrivial (DualNumber k))
  refine finrank_end_id_eq_one fun f => ⟨((GrAlg.dualEquiv k).symm (homVal f)).fst, ?_⟩
  have h2 := (homVal_dual f).2
  rw [Int.cast_zero, sub_zero] at h2
  apply (GrAlg.dualEquiv k).symm.injective
  rw [AlgEquiv.commutes]
  ext
  · rfl
  · exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

/-! ### Vanishing outside the weight string -/

omit [CharZero k] in
theorem GBim.isZero_of_trivial_left {B : GrAlg k} (X : GBim (GrAlg.trivial k) B) : IsZero X := by
  have : Subsingleton X := ⟨fun x y => by
    have h1 : (1 : (GrAlg.trivial k).carrier) = 0 :=
      @Subsingleton.elim _ (inferInstanceAs (Subsingleton PUnit)) _ _
    have h : ∀ z : X, z = 0 := fun z => by
      have := LinearMap.congr_fun (map_one X.actL) z
      rw [h1, map_zero, LinearMap.zero_apply, Module.End.one_apply] at this
      exact this.symm
    rw [h x, h y]⟩
  exact isZero_of_subsingleton X

omit [CharZero k] in
theorem GBim.isZero_of_trivial_right {A : GrAlg k} (X : GBim A (GrAlg.trivial k)) : IsZero X := by
  have : Subsingleton X := ⟨fun x y => by
    have h1 : (1 : (GrAlg.trivial k).carrier) = 0 :=
      @Subsingleton.elim _ (inferInstanceAs (Subsingleton PUnit)) _ _
    have h : ∀ z : X, z = 0 := fun z => by
      have := LinearMap.congr_fun (map_one X.actR) z
      rw [h1, map_zero, LinearMap.zero_apply, Module.End.one_apply] at this
      exact this.symm
    rw [h x, h y]⟩
  exact isZero_of_subsingleton X

omit [CharZero k] in
theorem isZero_of_l2Obj_left {r : ℤ} (h0 : r ≠ 0) (h1 : r ≠ 1) (h2 : r ≠ 2) {B : GrAlg k}
    (X : l2Obj k r ⟶ B) : IsZero X := by
  revert X
  rw [l2Obj_eq_trivial h0 h1 h2]
  exact GBim.isZero_of_trivial_left

omit [CharZero k] in
theorem isZero_of_l2Obj_right {r : ℤ} (h0 : r ≠ 0) (h1 : r ≠ 1) (h2 : r ≠ 2) {A : GrAlg k}
    (X : A ⟶ l2Obj k r) : IsZero X := by
  revert X
  rw [l2Obj_eq_trivial h0 h1 h2]
  exact GBim.isZero_of_trivial_right

omit [CharZero k] in
theorem isZero_l2E {r : ℤ} (h0 : r ≠ 0) (h1 : r ≠ 1) : IsZero (l2E k r) := by
  by_cases h2 : r = 2
  · subst h2
    exact isZero_of_l2Obj_right (r := 2 + 1) (by norm_num) (by norm_num) (by norm_num) _
  · exact isZero_of_l2Obj_left h0 h1 h2 _

omit [CharZero k] in
theorem isZero_l2F {r : ℤ} (h0 : r ≠ 0) (h1 : r ≠ 1) : IsZero (l2F k r) := by
  by_cases h2 : r = 2
  · subst h2
    exact isZero_of_l2Obj_left (r := 2 + 1) (by norm_num) (by norm_num) (by norm_num) _
  · exact isZero_of_l2Obj_right h0 h1 h2 _

omit [CharZero k] in
theorem isZero_biprod {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C] {X Y : C}
    (hX : IsZero X) (hY : IsZero Y) : IsZero (X ⊞ Y) :=
  hY.of_iso (isoZeroBiprod hX).symm

/-- Arithmetic side conditions after matching on an integer. -/
macro "l2_omega" : tactic =>
  `(tactic| ((try simp only [Int.ofNat_eq_natCast, Int.negSucc_eq] at *); omega))

omit [CharZero k] in
theorem isZero_lsum {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] : ∀ L : List C, (∀ X ∈ L, IsZero X) → IsZero (lsum L)
  | [], _ => isZero_zero _
  | X :: L, h => by
    rw [lsum_cons]
    exact isZero_biprod (h X List.mem_cons_self)
      (isZero_lsum L fun Y hY => h Y (List.mem_cons_of_mem _ hY))

omit [CharZero k] in
theorem isZero_qsum {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    {X : C} (hX : IsZero X) (d : ℤ) (n : ℕ) : IsZero (qsum d n X) :=
  isZero_lsum _ fun Y hY => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hY
    exact Functor.map_isZero _ hX

/-! ### The strong 2-representation -/

/-- The dots. -/
def l2Dot : ∀ r : ℤ, ShiftedHom (l2E k r) (l2E k r) (2 : ℤ)
  | .ofNat 0 => dot0
  | .ofNat 1 => dot1
  | _ => 0

/-- The crossings. -/
def l2Cross : ∀ r : ℤ, ShiftedHom (l2E k r ≫ l2E k (r + 1)) (l2E k r ≫ l2E k (r + 1)) (-2 : ℤ)
  | .ofNat 0 => cross0
  | _ => 0

omit [CharZero k] in
theorem isZero_l2EE {r : ℤ} (h0 : r ≠ 0) : IsZero (l2E k r ≫ l2E k (r + 1)) := by
  by_cases h1 : r = 1
  · subst h1
    exact isZero_comp_right _ (isZero_l2E (r := 1 + 1) (by norm_num) (by norm_num))
  · exact isZero_comp_left (isZero_l2E h0 h1) _

omit [CharZero k] in
theorem isZero_l2EEE (r : ℤ) : IsZero (l2E k r ≫ l2E k (r + 1) ≫ l2E k (r + 1 + 1)) := by
  by_cases h0 : r = 0
  · subst h0
    exact isZero_comp_right _ (isZero_comp_right _ (isZero_l2E (r := 0 + 1 + 1) (by norm_num)
      (by norm_num)))
  · by_cases h1 : r = 1
    · subst h1
      exact isZero_comp_right _ (isZero_comp_left (isZero_l2E (r := 1 + 1) (by norm_num)
        (by norm_num)) _)
    · exact isZero_comp_left (isZero_l2E h0 h1) _

/-- The adjunctions `E 1_n ⊣ 1_n F ⟨n + 1⟩`. -/
def l2Adj : ∀ r : ℤ, l2E k r ⊣ (l2F k r)⟦-2 + 2 * r + 1⟧
  | .ofNat 0 => GBim.upDownAdj 𝔻 (e := 0) (g := 0) rfl
  | .ofNat 1 =>
    have h : (0 : ℤ) + -2 = -2 := by norm_num
    GBim.downUpAdj (k := k) h
  | .ofNat (r + 2) => adjunctionOfIsZero (isZero_l2E (by l2_omega) (by l2_omega))
      (Functor.map_isZero _ (isZero_l2F (by l2_omega) (by l2_omega)))
  | .negSucc r => adjunctionOfIsZero (isZero_l2E (by l2_omega) (by l2_omega))
      (Functor.map_isZero _ (isZero_l2F (by l2_omega) (by l2_omega)))

omit [CharZero k] in
theorem l2_exists_leftAdj (r : ℤ) : ∃ L : l2Obj k (r + 1) ⟶ l2Obj k r, Nonempty (L ⊣ l2E k r) :=
  match r with
  | .ofNat 0 =>
    have h : (-2 : ℤ) + 0 = -2 := by norm_num
    ⟨GBim.down 𝔻 (-2), ⟨GBim.downUpAdj (k := k) h⟩⟩
  | .ofNat 1 => ⟨GBim.up 𝔻 0, ⟨GBim.upDownAdj 𝔻 (e := 0) (g := 0) rfl⟩⟩
  | .ofNat (r + 2) => ⟨0, ⟨adjunctionOfIsZero (isZero_zero _) (isZero_l2E (by l2_omega) (by l2_omega))⟩⟩
  | .negSucc r => ⟨0, ⟨adjunctionOfIsZero (isZero_zero _) (isZero_l2E (by l2_omega) (by l2_omega))⟩⟩

omit [CharZero k] in
theorem isZero_qsum_zero {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] [HasShift C ℤ] (d : ℤ) (X : C) : IsZero (qsum d 0 X) :=
  isZero_zero _

/-- `F E 1_0 ≅ E F 1_0`: both are `H*(ℙ¹) ⊗ H*(ℙ¹) ⟨-1⟩` over `H*(pt)`. -/
def l2EF0 : l2F k 0 ≫ l2E k 0 ≅ l2E k 1 ≫ l2F k 1 :=
  GBim.whiskerRightShift (down 𝔻 0) (up 𝔻 0) 1 ≪≫
    (GBim.whiskerLeftShift (down 𝔻 0) (up 𝔻 0) 1).symm

/-- `splitIso` as an isomorphism in the Hom category of `GrAlg k`. -/
def splitIsoQ {e g : ℤ} (h : e + g = -1) :
    (up 𝔻 g ≫ down 𝔻 e : GrAlg.unit k ⟶ GrAlg.unit k) ≅ qsum 1 2 (𝟙 (GrAlg.unit k)) :=
  (GBim.splitIso h : _ ≅ ((𝟙 (GrAlg.unit k))⟦(1 : ℤ)⟧ ⊞ (𝟙 (GrAlg.unit k))⟦(-1 : ℤ)⟧ :
    GrAlg.unit k ⟶ GrAlg.unit k)) ≪≫
    biprod.mapIso (Iso.refl _) (isoBiprodZero (isZero_zero _))

/-- Append a zero summand on the left of `qsum 1 2 (𝟙 A)`. -/
def isoZeroQsum {A : GrAlg k} {X Y : A ⟶ A} (i : X ≅ qsum 1 2 (𝟙 A)) (hY : IsZero Y) :
    X ≅ Y ⊞ qsum 1 2 (𝟙 A) :=
  i ≪≫ isoZeroBiprod hY

/-- `E F 1_2 ≅ 1_2⟨1⟩ ⊕ 1_2⟨-1⟩`. -/
def l2EF1 : l2F k 1 ≫ l2E k 1 ≅ (l2E k 2 ≫ l2F k 2) ⊞ qsum 1 2 (𝟙 (l2Obj k 2)) :=
  isoZeroQsum (A := l2Obj k 2) (splitIsoQ (show (0 : ℤ) + -1 = -1 by norm_num))
    (isZero_comp_left (isZero_l2E (r := 2) (by norm_num) (by norm_num)) _)

/-- `F E 1_{-2} ≅ 1_{-2}⟨1⟩ ⊕ 1_{-2}⟨-1⟩`. -/
def l2FE0 : l2E k 0 ≫ l2F k 0 ≅ (l2F k (-1) ≫ l2E k (-1)) ⊞ qsum 1 2 (𝟙 (l2Obj k 0)) :=
  isoZeroQsum (A := l2Obj k 0) (splitIsoQ (show (-1 : ℤ) + 0 = -1 by norm_num))
    (isZero_comp_left (isZero_l2F (r := -1) (by norm_num) (by norm_num)) _)

variable (k) in
/-- **The categorified irreducible representation of `sl₂` of highest weight `2`**, on the
cohomology rings of `Gr(0,2)`, `Gr(1,2)`, `Gr(2,2)`: a strong 2-representation of `sl₂` (S. Cautis,
A. D. Lauda, arXiv:1111.1431v3, Definition 1.2) for a field `k` of characteristic zero. -/
def l2 : StrongSl2 k (GrAlg k) where
  n₀ := -2
  obj := l2Obj k
  E := l2E k
  F := l2F k
  adj := l2Adj
  exists_leftAdj := l2_exists_leftAdj
  integrable := ⟨3, fun r hr => isZero_id_l2Obj (by rintro rfl; norm_num at hr)
    (by rintro rfl; norm_num at hr) (by rintro rfl; norm_num at hr)⟩
  hom_neg r l hl := by
    match r with
    | .ofNat 0 =>
      have : Subsingleton (𝟙 (l2Obj k 0) ⟶ (𝟙 (l2Obj k 0))⟦l⟧) := subsingleton_hom_unit hl.ne
      exact Module.finrank_zero_of_subsingleton
    | .ofNat 1 =>
      have : Subsingleton (𝟙 (l2Obj k 1) ⟶ (𝟙 (l2Obj k 1))⟦l⟧) := subsingleton_hom_dual hl
      exact Module.finrank_zero_of_subsingleton
    | .ofNat 2 =>
      have : Subsingleton (𝟙 (l2Obj k 2) ⟶ (𝟙 (l2Obj k 2))⟦l⟧) := subsingleton_hom_unit hl.ne
      exact Module.finrank_zero_of_subsingleton
    | .ofNat (r + 3) =>
      have : Subsingleton (𝟙 (l2Obj k (.ofNat (r + 3))) ⟶ (𝟙 (l2Obj k (.ofNat (r + 3))))⟦l⟧) :=
        ⟨(isZero_id_l2Obj (by l2_omega) (by l2_omega) (by l2_omega)).eq_of_src⟩
      exact Module.finrank_zero_of_subsingleton
    | .negSucc r =>
      have : Subsingleton (𝟙 (l2Obj k (.negSucc r)) ⟶ (𝟙 (l2Obj k (.negSucc r)))⟦l⟧) :=
        ⟨(isZero_id_l2Obj (by l2_omega) (by l2_omega) (by l2_omega)).eq_of_src⟩
      exact Module.finrank_zero_of_subsingleton
  hom_zero r hr := by
    match r with
    | .ofNat 0 => exact finrank_end_id_unit
    | .ofNat 1 => exact finrank_end_id_dual
    | .ofNat 2 => exact finrank_end_id_unit
    | .ofNat (r + 3) => exact absurd (isZero_id_l2Obj (by l2_omega) (by l2_omega) (by l2_omega)) hr
    | .negSucc r => exact absurd (isZero_id_l2Obj (by l2_omega) (by l2_omega) (by l2_omega)) hr
  EF r hr := by
    match r with
    | .ofNat 0 => exact ⟨l2EF0 ≪≫ isoBiprodZero (isZero_qsum_zero _ _)⟩
    | .ofNat 1 => exact ⟨l2EF1⟩
    | .ofNat (r + 2) =>
      refine ⟨IsZero.iso ?_ ?_⟩
      · exact isZero_comp_left (isZero_l2F (by l2_omega) (by l2_omega)) _
      · exact isZero_biprod (isZero_of_l2Obj_left (by l2_omega) (by l2_omega)
          (by l2_omega) _) (isZero_qsum (isZero_id_l2Obj (by l2_omega) (by l2_omega)
            (by l2_omega)) _ _)
    | .negSucc r => l2_omega
  FE r hr := by
    match r with
    | .ofNat 0 => exact ⟨l2EF0.symm ≪≫ isoBiprodZero (isZero_qsum_zero _ _)⟩
    | .ofNat (r + 1) => l2_omega
    | .negSucc 0 => exact ⟨l2FE0⟩
    | .negSucc (r + 1) =>
      refine ⟨IsZero.iso ?_ ?_⟩
      · exact isZero_comp_left (isZero_l2E (by l2_omega) (by l2_omega)) _
      · exact isZero_biprod (isZero_comp_left (isZero_l2F (by l2_omega)
          (by l2_omega)) _) (isZero_qsum (isZero_id_l2Obj (by l2_omega) (by l2_omega)
            (by l2_omega)) _ _)
  rQ := 1
  dot := l2Dot
  cross := l2Cross
  cross_sq r := by
    match r with
    | .ofNat 0 => exact cross0_sq
    | .ofNat (r + 1) => exact (isZero_l2EE (by l2_omega)).eq_of_src _ _
    | .negSucc r => exact (isZero_l2EE (by l2_omega)).eq_of_src _ _
  dot_slide_left r := by
    match r with
    | .ofNat 0 => exact dot_slide_left0
    | .ofNat (r + 1) => exact (isZero_l2EE (by l2_omega)).eq_of_src _ _
    | .negSucc r => exact (isZero_l2EE (by l2_omega)).eq_of_src _ _
  dot_slide_right r := by
    match r with
    | .ofNat 0 => exact dot_slide_right0
    | .ofNat (r + 1) => exact (isZero_l2EE (by l2_omega)).eq_of_src _ _
    | .negSucc r => exact (isZero_l2EE (by l2_omega)).eq_of_src _ _
  braid r := (isZero_l2EEE r).eq_of_src _ _

/-- The weight-`0` object `H*(ℙ¹)` of `l2` is nonzero: its identity 1-morphism has a
one-dimensional space of degree-zero endomorphisms. -/
theorem not_isZero_id_l2Obj_one : ¬ IsZero (𝟙 ((l2 k).obj 1)) := by
  intro h
  have : Subsingleton (GBim.id 𝔻 ⟶ GBim.id 𝔻) := ⟨fun a b => h.eq_of_src a b⟩
  have h1 := finrank_end_id_dual (k := k)
  rw [Module.finrank_zero_of_subsingleton] at h1
  exact zero_ne_one h1

end Categorification.TwoRep.Grassmannian

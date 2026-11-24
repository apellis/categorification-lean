/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DiagramWeightBimodule
import DG.Module.Cohomology

/-!
# Degree-zero tensor comparison for weight modules

The tensor coend of a degree-zero right coefficient with a nonpositive
resolution computes the ordinary tensor in cohomological degree zero.
-/

noncomputable section

set_option maxHeartbeats 1800000
set_option maxRecDepth 2048

namespace Categorification

open CategoryTheory DG MulOpposite
open scoped DG.DegreeZero

universe u v w
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C]

/-- A dg additive group concentrated in cohomological degree zero. -/
structure PureDegreeZero (M : Type*) [AddCommGroup M] [DGAddCommGroup M] : Prop where
  mem_zero : ∀ x : M, x ∈ DG.grading (0 : ℤ)
  d_zero : ∀ x : M, d x = 0

private theorem PureDegreeZero.homogeneous_ne_zero {M : Type*} [AddCommGroup M] [DGAddCommGroup M]
    (hM : PureDegreeZero M) {i : ℤ} {x : M} (hi : i ≠ 0) (hx : x ∈ DG.grading i) : x = 0 := by
  have h := DirectSum.decompose_of_mem_ne (DG.grading (M := M)) (hM.mem_zero x) hi.symm
  rw [DirectSum.decompose_of_mem_same _ hx] at h
  exact h

private def PureDegreeZero.evalCohomologyZero {M : Type*} [AddCommGroup M] [DGAddCommGroup M]
    (hM : PureDegreeZero M) : cohomology M 0 →+ M :=
  cohomology.lift (cocycles M 0).subtype (fun z ⟨y, _, hy⟩ => by
    change z.val = 0
    exact hy.symm.trans (hM.d_zero y))

private theorem PureDegreeZero.evalCohomologyZero_mk {M : Type*} [AddCommGroup M]
    [DGAddCommGroup M] (hM : PureDegreeZero M) (z : cocycles M 0) :
    hM.evalCohomologyZero (cohomology.mk M 0 z) = z.val := by
  unfold evalCohomologyZero
  exact cohomology.lift_mk (cocycles M 0).subtype _ z

private def PureDegreeZero.cohomologyZeroEquiv {M : Type*} [AddCommGroup M] [DGAddCommGroup M]
    (hM : PureDegreeZero M) : cohomology M 0 ≃+ M where
  __ := hM.evalCohomologyZero
  invFun x := cohomology.mkOf (hM.mem_zero x) (hM.d_zero x)
  left_inv z := by
    induction z using cohomology.induction_on with
    | h z =>
      change cohomology.mkOf (hM.mem_zero (hM.evalCohomologyZero (cohomology.mk M 0 z)))
        (hM.d_zero _) = _
      rw [hM.evalCohomologyZero_mk]
      rfl
  right_inv x := hM.evalCohomologyZero_mk ⟨x, hM.mem_zero x, hM.d_zero x⟩

variable {L : CatModule.{w} (DGOpposite C)} {P E : CatModule.{w} C}
  (hL : ∀ Y, PureDegreeZero (L.obj (DG.DGOpposite.op Y)))
  (hE : ∀ Y, PureDegreeZero (E.obj Y))
  (hP : ∀ (Y : C) {x : P.obj Y}, x ∈ DG.grading (0 : ℤ) → d x = 0)
  (f : P ⟶ E) (hf : CatModule.IsQuasiIso f)

private def weightTensorCohomologyMap :
    cohomology (CatTensorProduct L P) 0 →+ cohomology (CatTensorProduct L E) 0 :=
  cohomology.mapAddMonoidHom (CatTensorProduct.map (𝟙 L) f)
    (CatTensorProduct.map_mem (𝟙 L) f) (CatTensorProduct.map_d (𝟙 L) f) 0

private def pointZeroEquiv (Y : C) : cohomology (P.obj Y) 0 ≃+ E.obj Y :=
  (AddEquiv.ofBijective (cohomology.mapAddMonoidHom (f.app Y) f.map_mem f.map_d 0)
    (hf Y 0)).trans (PureDegreeZero.cohomologyZeroEquiv (hE Y))

omit [DGCategory C] in
private theorem pointZeroEquiv_mk (Y : C) (z : cocycles (P.obj Y) 0) :
    pointZeroEquiv hE f hf Y (cohomology.mk _ 0 z) = f.app Y z.val := by
  change (hE Y).evalCohomologyZero
    (cohomology.mapAddMonoidHom (f.app Y) f.map_mem f.map_d 0 (cohomology.mk _ 0 z)) = _
  rw [cohomology.mapAddMonoidHom_mk, PureDegreeZero.evalCohomologyZero_mk]
  rfl

private def pureOnCohomology (Y : C) (a : L.obj (DG.DGOpposite.op Y)) :
    cohomology (P.obj Y) 0 →+ cohomology (CatTensorProduct L P) 0 :=
  cohomology.mapAddMonoidHom (CatTensorProduct.tmulAddHom L P Y a)
    (fun {i x} hx => by
      change CatTensorProduct.tmul Y a x ∈ DG.grading i
      have h := CatTensorProduct.tmul_mem_grading ((hL Y).mem_zero a) hx
      rwa [zero_add] at h)
    (fun x => by
      change CatTensorProduct.tmul Y a (d x) = d (CatTensorProduct.tmul Y a x)
      rw [CatTensorProduct.d_tmul_of_mem Y ((hL Y).mem_zero a), (hL Y).d_zero a,
        CatTensorProduct.zero_tmul, koszulSign_zero, one_smul, zero_add]) 0

private theorem pureOnCohomology_mk (Y : C) (a : L.obj (DG.DGOpposite.op Y))
    (z : cocycles (P.obj Y) 0) :
    pureOnCohomology hL Y a (cohomology.mk _ 0 z) =
    cohomology.mkOf
      (by simpa only [add_zero] using CatTensorProduct.tmul_mem_grading ((hL Y).mem_zero a) z.property.1)
      (by rw [CatTensorProduct.d_tmul_of_mem Y ((hL Y).mem_zero a), (hL Y).d_zero a,
        z.property.2, CatTensorProduct.zero_tmul, CatTensorProduct.tmul_zero, _root_.smul_zero, add_zero]) := rfl


private theorem pureOnCohomology_zero (Y : C) :
    pureOnCohomology (P := P) hL Y 0 = 0 := by
  apply AddMonoidHom.ext
  intro z
  induction z using cohomology.induction_on with
  | h z =>
    rw [pureOnCohomology_mk]
    exact (cohomology.mkOf_eq_zero_iff _ _).mpr
      (by rw [CatTensorProduct.zero_tmul]; exact zero_mem _)

private theorem pureOnCohomology_add (Y : C) (a b : L.obj (DG.DGOpposite.op Y)) :
    pureOnCohomology (P := P) hL Y (a + b) =
      pureOnCohomology hL Y a + pureOnCohomology hL Y b := by
  apply AddMonoidHom.ext
  intro z
  induction z using cohomology.induction_on with
  | h z =>
    rw [AddMonoidHom.add_apply, pureOnCohomology_mk, pureOnCohomology_mk, pureOnCohomology_mk]
    rw [← cohomology.mkOf_add]
    apply congrArg (cohomology.mk _ _)
    exact Subtype.ext (CatTensorProduct.add_tmul Y a b z.val)

private def liftTensorAt (Y : C) :
    L.obj (DG.DGOpposite.op Y) →+ E.obj Y →+ cohomology (CatTensorProduct L P) 0 where
  toFun a := (pureOnCohomology hL Y a).comp (pointZeroEquiv hE f hf Y).symm.toAddMonoidHom
  map_zero' := by rw [pureOnCohomology_zero]; rfl
  map_add' a b := by rw [pureOnCohomology_add]; rfl

private theorem liftTensorAt_apply (Y : C) (a : L.obj (DG.DGOpposite.op Y))
    (z : cocycles (P.obj Y) 0) :
    liftTensorAt hL hE f hf Y a (f.app Y z.val) =
      pureOnCohomology hL Y a (cohomology.mk _ 0 z) := by
  change pureOnCohomology hL Y a ((pointZeroEquiv hE f hf Y).symm (f.app Y z.val)) = _
  rw [← pointZeroEquiv_mk hE f hf Y z, AddEquiv.symm_apply_apply]

include hP in
private theorem liftTensor_balanced (hC : ∀ {X Y : C} (g : X ⟶ Y), g ∈ DG.grading (0 : ℤ)) :
    CatTensorProduct.Balanced (liftTensorAt hL hE f hf) := by
  intro Y Z g a b
  obtain ⟨c, hc⟩ := (pointZeroEquiv hE f hf Y).surjective b
  obtain ⟨z, rfl⟩ := cohomology.mk_surjective (P.obj Y) 0 c
  rw [pointZeroEquiv_mk hE f hf Y z] at hc
  subst b
  have hact : P.act g z.val ∈ DG.grading (0 : ℤ) := by
    simpa only [add_zero] using P.act_mem' (hC g) z.property.1
  let z' : cocycles (P.obj Z) 0 := ⟨P.act g z.val, hact, hP Z hact⟩
  have hh : g • (f.app Y z.val) = f.app Z z'.val :=
    (f.map_smul g z.val).symm
  rw [hh, liftTensorAt_apply, liftTensorAt_apply,
    pureOnCohomology_mk, pureOnCohomology_mk]
  apply congrArg (cohomology.mk _ _)
  exact Subtype.ext (CatTensorProduct.ract_tmul g a z.val)


include hL hE in
private theorem tensorPureDegreeZero : PureDegreeZero (CatTensorProduct L E) where
  mem_zero x := by
    induction x using CatTensorProduct.induction_on with
    | zero => exact zero_mem _
    | tmul Y a b =>
      have h := CatTensorProduct.tmul_mem_grading ((hL Y).mem_zero a) ((hE Y).mem_zero b)
      rwa [add_zero] at h
    | add x y hx hy => exact add_mem hx hy
  d_zero x := by
    induction x using CatTensorProduct.induction_on with
    | zero => exact d_zero
    | tmul Y a b =>
      rw [CatTensorProduct.d_tmul_of_mem Y ((hL Y).mem_zero a), (hL Y).d_zero a,
        (hE Y).d_zero b, CatTensorProduct.zero_tmul, CatTensorProduct.tmul_zero,
        smul_zero, add_zero]
    | add x y hx hy => rw [d_add, hx, hy, add_zero]

private def tensorH0Forward : cohomology (CatTensorProduct L P) 0 →+ CatTensorProduct L E :=
  (PureDegreeZero.cohomologyZeroEquiv (tensorPureDegreeZero hL hE)).toAddMonoidHom.comp
    (weightTensorCohomologyMap f)

private theorem tensorH0Forward_mk (z : cocycles (CatTensorProduct L P) 0) :
    tensorH0Forward hL hE f (cohomology.mk _ 0 z) =
      CatTensorProduct.map (𝟙 L) f z.val := by
  change (tensorPureDegreeZero hL hE).evalCohomologyZero
    (weightTensorCohomologyMap f (cohomology.mk _ 0 z)) = _
  unfold weightTensorCohomologyMap
  rw [cohomology.mapAddMonoidHom_mk (CatTensorProduct.map (𝟙 L) f)
    (CatTensorProduct.map_mem (𝟙 L) f) (CatTensorProduct.map_d (𝟙 L) f),
    PureDegreeZero.evalCohomologyZero_mk]
  rfl

private theorem tensorH0Forward_pure (Y : C) (a : L.obj (DG.DGOpposite.op Y))
    (z : cocycles (P.obj Y) 0) :
    tensorH0Forward hL hE f (pureOnCohomology hL Y a (cohomology.mk _ 0 z)) =
      CatTensorProduct.tmul Y a (f.app Y z.val) := by
  rw [pureOnCohomology_mk, cohomology.mkOf_eq_mk, tensorH0Forward_mk, CatTensorProduct.map_tmul]
  rfl

private def tensorH0Backward (hC : ∀ {X Y : C} (g : X ⟶ Y), g ∈ DG.grading (0 : ℤ)) :
    CatTensorProduct L E →+ cohomology (CatTensorProduct L P) 0 :=
  CatTensorProduct.lift (liftTensorAt hL hE f hf) (liftTensor_balanced hL hE hP f hf hC)

private theorem tensorH0Backward_pure
    (hC : ∀ {X Y : C} (g : X ⟶ Y), g ∈ DG.grading (0 : ℤ))
    (Y : C) (a : L.obj (DG.DGOpposite.op Y)) (z : cocycles (P.obj Y) 0) :
    tensorH0Backward hL hE hP f hf hC (CatTensorProduct.tmul Y a (f.app Y z.val)) =
      pureOnCohomology hL Y a (cohomology.mk _ 0 z) := by
  exact (CatTensorProduct.lift_tmul (liftTensorAt hL hE f hf)
    (liftTensor_balanced hL hE hP f hf hC) Y a (f.app Y z.val)).trans
    (liftTensorAt_apply hL hE f hf Y a z)

private theorem tensorH0Forward_rightInverse
    (hC : ∀ {X Y : C} (g : X ⟶ Y), g ∈ DG.grading (0 : ℤ)) :
    Function.RightInverse (tensorH0Backward hL hE hP f hf hC) (tensorH0Forward hL hE f) := by
  suffices (tensorH0Forward hL hE f).comp (tensorH0Backward hL hE hP f hf hC) =
      AddMonoidHom.id _ from DFunLike.congr_fun this
  apply CatTensorProduct.addHom_ext
  intro Y a b
  obtain ⟨c, hc⟩ := (pointZeroEquiv hE f hf Y).surjective b
  obtain ⟨z, rfl⟩ := cohomology.mk_surjective (P.obj Y) 0 c
  rw [pointZeroEquiv_mk hE f hf Y z] at hc
  subst b
  change tensorH0Forward hL hE f (tensorH0Backward hL hE hP f hf hC
    (CatTensorProduct.tmul Y a (f.app Y z.val))) = _
  rw [tensorH0Backward_pure, tensorH0Forward_pure]
  rfl

include hL hP in
private theorem tensorH0_zeroDegreeCycles {t : CatTensorProduct L P}
    (ht : t ∈ DG.grading (0 : ℤ)) : d t = 0 := by
  refine CatTensorProduct.induction_on_mem_grading (P := fun t => d t = 0)
    d_zero ?_ ?_ ?_ ht
  · intro Y i j a b ha hb hij
    by_cases hi : i = 0
    · have hj : j = 0 := by omega
      subst i j
      rw [CatTensorProduct.d_tmul_of_mem Y ha, (hL Y).d_zero a,
        hP Y hb, CatTensorProduct.zero_tmul, CatTensorProduct.tmul_zero, smul_zero, add_zero]
    · rw [(hL Y).homogeneous_ne_zero hi ha, CatTensorProduct.zero_tmul, d_zero]
  · intro x y hx hy
    rw [d_add, hx, hy, add_zero]
  · intro x hx
    rw [d_neg, hx, neg_zero]

private theorem tensorH0Forward_leftInverse
    (hC : ∀ {X Y : C} (g : X ⟶ Y), g ∈ DG.grading (0 : ℤ)) :
    Function.LeftInverse (tensorH0Backward hL hE hP f hf hC) (tensorH0Forward hL hE f) := by
  let e := (tensorH0Backward hL hE hP f hf hC).comp (tensorH0Forward hL hE f)
  intro c
  induction c using cohomology.induction_on with
  | h z =>
    change e (cohomology.mk _ 0 z) = cohomology.mk _ 0 z
    suffices ∀ (t : CatTensorProduct L P), t ∈ DG.grading (0 : ℤ) →
        t ∈ DG.grading (0 : ℤ) ∧
          ∀ (ht : t ∈ DG.grading (0 : ℤ)) (hdt : d t = 0),
            e (cohomology.mkOf ht hdt) = cohomology.mkOf ht hdt by
      exact (this z.val z.property.1).2 z.property.1 z.property.2
    intro t ht
    refine CatTensorProduct.induction_on_mem_grading
      (P := fun x => x ∈ DG.grading (0 : ℤ) ∧
        ∀ (hx : x ∈ DG.grading (0 : ℤ)) (hdx : d x = 0),
          e (cohomology.mkOf hx hdx) = cohomology.mkOf hx hdx) ?_ ?_ ?_ ?_ ht
    · refine ⟨zero_mem _, ?_⟩
      intro hz hdz
      have h : cohomology.mkOf hz hdz = 0 :=
        (cohomology.mkOf_eq_zero_iff _ _).mpr (zero_mem _)
      rw [h, map_zero]
    · intro Y i j a b ha hb hij
      refine ⟨hij ▸ CatTensorProduct.tmul_mem_grading ha hb, ?_⟩
      intro ht hdt
      by_cases hi : i = 0
      · have hj : j = 0 := by omega
        subst i j
        let z' : cocycles (P.obj Y) 0 := ⟨b, hb, hP Y hb⟩
        change tensorH0Backward hL hE hP f hf hC
          (tensorH0Forward hL hE f (cohomology.mkOf ht hdt)) = _
        rw [← pureOnCohomology_mk hL Y a z', tensorH0Forward_pure, tensorH0Backward_pure]
      · have hzero : CatTensorProduct.tmul Y a b = 0 := by
          rw [(hL Y).homogeneous_ne_zero hi ha, CatTensorProduct.zero_tmul]
        have h : cohomology.mkOf ht hdt = 0 :=
          (cohomology.mkOf_eq_zero_iff _ _).mpr (by rw [hzero]; exact zero_mem _)
        rw [h, map_zero]
    · intro x y hx hy
      refine ⟨add_mem hx.1 hy.1, ?_⟩
      intro hxy hdxy
      have hdx := tensorH0_zeroDegreeCycles hL hP hx.1
      have hdy := tensorH0_zeroDegreeCycles hL hP hy.1
      rw [cohomology.mkOf_add hx.1 hdx hy.1 hdy, map_add, hx.2, hy.2]
    · intro x hx
      refine ⟨neg_mem hx.1, ?_⟩
      intro hn hdn
      have hd := tensorH0_zeroDegreeCycles hL hP hx.1
      rw [cohomology.mkOf_neg hx.1 hd, map_neg, hx.2]


/-- Tensoring a degree-zero right coefficient with a nonpositive resolution computes
ordinary tensor in cohomological degree zero. -/
def catTensorCohomologyZeroEquivOfQuasiIso
    (hC : ∀ {X Y : C} (g : X ⟶ Y), g ∈ DG.grading (0 : ℤ)) :
    cohomology (CatTensorProduct L P) 0 ≃+ CatTensorProduct L E where
  __ := tensorH0Forward hL hE f
  invFun := tensorH0Backward hL hE hP f hf hC
  left_inv := tensorH0Forward_leftInverse hL hE hP f hf hC
  right_inv := tensorH0Forward_rightInverse hL hE hP f hf hC


/-- The H₀ comparison is induced by the original resolution augmentation. -/
theorem catTensorCohomologyZeroEquivOfQuasiIso_mk
    (hC : ∀ {X Y : C} (g : X ⟶ Y), g ∈ DG.grading (0 : ℤ))
    (z : cocycles (CatTensorProduct L P) 0) :
    catTensorCohomologyZeroEquivOfQuasiIso hL hE hP f hf hC (cohomology.mk _ 0 z) =
      CatTensorProduct.map (𝟙 L) f z.val :=
  tensorH0Forward_mk hL hE f z

end Categorification

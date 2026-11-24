/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.BalancedTensor
import Categorification.Algebra.DerivedTensorDegreeZero
import DG.Derived.ConnectiveResolution
import DG.Derived.DegreeZeroHomology
import DG.Homotopy.OrdinaryTensorHomology

/-!
# Degree-zero cohomology of derived tensor of ordinary bimodules

Webster, arXiv:1309.3796v2, Lemma 6.8, proof of (6.21), identifies the cohomology
map in degree zero with the ordinary balanced tensor map. The comparison is
natural in the ordinary module and uses connective K-projective resolutions.
-/

open CategoryTheory DG DG.DerivedCategory MulOpposite
open scoped DG.DegreeZero

noncomputable section

namespace Categorification

universe w u

section KProjectiveNaturality

variable {A B M : Type u} [Ring A] [Ring B] [AddCommGroup M] [Module A M]
  [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]
  [HasDerivedCategory.{w, u} A] [HasDerivedCategory.{w, u} B]

set_option backward.isDefEq.respectTransparency false in
/-- The model comparison for the derived tensor is natural on K-projective dg modules. -/
theorem derivedTensorObjIso_naturality {X Y : DGModuleCat.{u} B} (f : X ⟶ Y)
    (hX : IsKProjective.{u} B X) (hY : IsKProjective.{u} B Y) :
    (derivedTensor.{w} A B M).map (Q.map f) ≫ (derivedTensorObjIso hY).hom =
      (derivedTensorObjIso hX).hom ≫
        Q.map ((DGModuleCat.tensorFunctor A (InDegreeZero M)).map f) := by
  let E := kProjectiveEquivalence.{w} B
  let ι := (DG.HomotopyCategory.subcategoryKProjective B).ι
  let T := DG.HomotopyCategory.tensorFunctor (B := B) A (InDegreeZero M)
  let U := DGModuleCat.tensorFunctor (B := B) A (InDegreeZero M)
  let q := DG.HomotopyCategory.quotient B
  let V : KProjective B :=
    ⟨q.obj X, (DG.HomotopyCategory.quotient_obj_mem_subcategoryKProjective_iff X).mpr hX⟩
  let W : KProjective B :=
    ⟨q.obj Y, (DG.HomotopyCategory.quotient_obj_mem_subcategoryKProjective_iff Y).mpr hY⟩
  let a : V ⟶ W := ObjectProperty.homMk (q.map f)
  let e := DG.HomotopyCategory.tensorFunctorQuotientIso (B := B) A (InDegreeZero M)
  have h₁ := E.unitIso.inv.naturality a
  have h₂ := e.hom.naturality f
  change E.inverse.map (Q.map f) ≫ E.unitIso.inv.app W =
    E.unitIso.inv.app V ≫ a at h₁
  change (T.map (q.map f)) ≫ e.hom.app Y = e.hom.app X ≫
    (DG.HomotopyCategory.quotient A).map (U.map f) at h₂
  have h₁' := congrArg (fun b => Qh.map (T.map (ι.map b))) h₁
  have h₂' := congrArg (fun b => Qh.map b) h₂
  simp only [Functor.map_comp] at h₁' h₂'
  have ha : ι.map a = q.map f := rfl
  rw [ha] at h₁'
  simp only [derivedTensor, Functor.comp_map, derivedTensorObjIso, Functor.mapIso_hom,
    Iso.trans_hom, Functor.map_comp, Iso.symm_hom]
  change Qh.map (T.map (ι.map (E.inverse.map (Q.map f)))) ≫
      (Qh.map (T.map (ι.map (E.unitIso.inv.app W))) ≫ Qh.map (e.hom.app Y)) =
    (Qh.map (T.map (ι.map (E.unitIso.inv.app V))) ≫ Qh.map (e.hom.app X)) ≫
      Qh.map ((DG.HomotopyCategory.quotient A).map (U.map f))
  rw [← Category.assoc, h₁', Category.assoc, h₂', ← Category.assoc]

end KProjectiveNaturality

section DerivedComparison

variable {A B M : Type u} [Ring A] [Ring B] [AddCommGroup M] [Module A M]
  [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]
  [HasDerivedCategory.{w, u} A] [HasDerivedCategory.{w, u} B]

private abbrev F := derivedTensor.{w} A B M
private abbrev H := homologyFunctor (A := A) ℤ 0
private abbrev T := DGModuleCat.tensorFunctor (B := B) A (InDegreeZero M)

private theorem degreeZero_nonpos (X : Type u) [AddCommGroup X] : IsNonposGraded (InDegreeZero X) :=
  isNonposGraded_iff.mpr fun _ hn _ hx =>
    ((InDegreeZero.mem_grading_iff _).mp hx).resolve_left hn.ne'

omit [HasDerivedCategory B] in
private theorem ring_nonpos : IsNonposGraded B :=
  isNonposGraded_iff.mpr fun _ hn _ hx => (DegreeZero.mem_grading_iff.mp hx).resolve_left hn.ne'

variable {X Y : Type u} [AddCommGroup X] [Module B X] [AddCommGroup Y] [Module B Y]

private abbrev model (X : Type u) [AddCommGroup X] [Module B X] :=
  DGModuleCat.of B (ConnectiveResolution.Colim B (InDegreeZero X))

private abbrev aug (X : Type u) [AddCommGroup X] [Module B X] :
    model (B := B) X ⟶ DGModuleCat.of B (InDegreeZero X) :=
  DGModuleCat.ofHom (ConnectiveResolution.π B (InDegreeZero X))

omit [HasDerivedCategory B] in
private theorem model_kproj (X : Type u) [AddCommGroup X] [Module B X] :
    IsKProjective.{u} B (model (B := B) X) :=
  (ConnectiveResolution.semiFreeFiltration B (InDegreeZero X)).isKProjective

omit [HasDerivedCategory B] in
private theorem aug_quasi (X : Type u) [AddCommGroup X] [Module B X] :
    (aug (B := B) X).hom.IsQuasiIso :=
  ConnectiveResolution.isQuasiIso_π B (InDegreeZero X) ring_nonpos (degreeZero_nonpos X)

private instance aug_iso (X : Type u) [AddCommGroup X] [Module B X] :
    IsIso (Q.map (aug (B := B) X)) := (isIso_Q_map_iff _).mpr (aug_quasi X)

omit [HasDerivedCategory B] in
private theorem aug_tensor_iso_H0 (X : Type u) [AddCommGroup X] [Module B X] :
    IsIso ((H (A := A)).map (Q.map ((T (A := A) (M := M)).map (aug (B := B) X)))) := by
  let e := homologyFunctorFactors (A := A) ℤ 0
  let p := (T (A := A) (M := M)).map (aug (B := B) X)
  apply (NatIso.isIso_map_iff e p).mpr
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective (cohomology.map p.hom 0)
  let : Fact (∀ m : InDegreeZero M, m ∈ grading 0) := ⟨fun _ =>
    (InDegreeZero.mem_grading_iff (M := M)).mpr (Or.inl rfl)⟩
  let : Fact (∀ x : InDegreeZero X, x ∈ grading 0) := ⟨fun _ =>
    (InDegreeZero.mem_grading_iff (M := X)).mpr (Or.inl rfl)⟩
  exact DG.tensor_aug_bijective_H0 (A := A) (M := InDegreeZero M)
    (ConnectiveResolution.π B (InDegreeZero X))
    ((aug_quasi (B := B) X) 0)
    (fun x hx => (ConnectiveResolution.isNonposGraded_colim B (InDegreeZero X) ring_nonpos).eq_zero one_pos hx)

/-- The derived tensor of ordinary modules agrees with ordinary tensor in degree zero. -/
def derivedTensorHomologyIsoOrdinary (X : Type u) [AddCommGroup X] [Module B X] :
    (H (A := A)).obj ((F (A := A) (B := B) (M := M)).obj (Q.obj (DGModuleCat.of B (InDegreeZero X)))) ≅
      (H (A := A)).obj (Q.obj ((T (A := A) (B := B) (M := M)).obj (DGModuleCat.of B (InDegreeZero X)))) := by
  have := aug_tensor_iso_H0 (A := A) (B := B) (M := M) X
  exact (H (A := A)).mapIso ((F (A := A) (B := B) (M := M)).mapIso (asIso (Q.map (aug (B := B) X))).symm ≪≫
    derivedTensorObjIso (A := A) (M := M) (model_kproj (B := B) X)) ≪≫
    asIso ((H (A := A)).map (Q.map ((T (A := A) (M := M)).map (aug (B := B) X))))

private theorem compatible_model_morphism
    (f : DGModuleCat.of B (InDegreeZero X) ⟶ DGModuleCat.of B (InDegreeZero Y)) :
    ∃ a : model (B := B) X ⟶ model (B := B) Y,
      Q.map a ≫ Q.map (aug (B := B) Y) = Q.map (aug (B := B) X) ≫ Q.map f ∧
      Q.map ((T (A := A) (M := M)).map a) ≫ Q.map (T.map (aug (B := B) Y)) =
        Q.map (T.map (aug (B := B) X)) ≫ Q.map (T.map f) := by
  obtain ⟨a, ha⟩ := exists_Q_map_eq (model_kproj (B := B) X)
    (Q.map (aug (B := B) X) ≫ Q.map f ≫ inv (Q.map (aug (B := B) Y)))
  have h : Q.map a ≫ Q.map (aug (B := B) Y) = Q.map (aug (B := B) X) ≫ Q.map f := by
    simp [ha, Category.assoc]
  refine ⟨a, h, ?_⟩
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  have h' : Q.map (a ≫ aug (B := B) Y) = Q.map (aug (B := B) X ≫ f) := by
    simpa only [Functor.map_comp] using h
  have hh := (Q_map_eq_iff (model_kproj (B := B) X) _ _).mp h'
  exact congrArg Qh.map ((DG.HomotopyCategory.quotient_map_eq_iff _ _).mpr
    (DG.HomotopyCategory.tensorFunctor_homotopic A (InDegreeZero M) _ _ hh))


set_option backward.isDefEq.respectTransparency false in
/-- The degree-zero comparison of the derived and ordinary tensors is natural. -/
theorem derivedTensorHomologyIsoOrdinary_naturality
    (f : DGModuleCat.of B (InDegreeZero X) ⟶ DGModuleCat.of B (InDegreeZero Y)) :
    (H (A := A)).map ((F (M := M)).map (Q.map f)) ≫
        (derivedTensorHomologyIsoOrdinary (A := A) (B := B) (M := M) Y).hom =
      (derivedTensorHomologyIsoOrdinary (A := A) (B := B) (M := M) X).hom ≫
        (H (A := A)).map (Q.map ((T (A := A) (M := M)).map f)) := by
  let L := F (A := A) (B := B) (M := M) ⋙ H (A := A)
  let J := Q ⋙ H (A := A)
  let G := T (A := A) (B := B) (M := M)
  let aX := L.map (Q.map (aug (B := B) X))
  let aY := L.map (Q.map (aug (B := B) Y))
  let bX := H.map (derivedTensorObjIso (A := A) (M := M) (model_kproj (B := B) X)).hom
  let bY := H.map (derivedTensorObjIso (A := A) (M := M) (model_kproj (B := B) Y)).hom
  let cX := J.map (G.map (aug (B := B) X))
  let cY := J.map (G.map (aug (B := B) Y))
  let eX := (derivedTensorHomologyIsoOrdinary (A := A) (B := B) (M := M) X).hom
  let eY := (derivedTensorHomologyIsoOrdinary (A := A) (B := B) (M := M) Y).hom
  have hX : aX ≫ eX = bX ≫ cX := by
    simp [aX, bX, cX, eX, L, J, G, derivedTensorHomologyIsoOrdinary]
  have hY : aY ≫ eY = bY ≫ cY := by
    simp [aY, bY, cY, eY, L, J, G, derivedTensorHomologyIsoOrdinary]
  obtain ⟨a, ha, hTa⟩ := compatible_model_morphism (A := A) (M := M) f
  have ha' : L.map (Q.map a) ≫ aY = aX ≫ L.map (Q.map f) := by
    simpa only [aX, aY, Functor.map_comp] using congrArg L.map ha
  have hTa' : J.map (G.map a) ≫ cY = cX ≫ J.map (G.map f) := by
    simpa only [J, cY, cX, G, Functor.comp_map, Functor.map_comp] using
      congrArg ((H (A := A)).map) hTa
  have hb : L.map (Q.map a) ≫ bY = bX ≫ J.map (G.map a) := by
    have h := derivedTensorObjIso_naturality (A := A) (M := M) a
      (model_kproj (B := B) X) (model_kproj (B := B) Y)
    simpa only [L, bY, bX, J, G, Functor.comp_map, Functor.map_comp] using
      congrArg ((H (A := A)).map) h
  change L.map (Q.map f) ≫ eY = eX ≫ J.map (G.map f)
  have : IsIso aX := by dsimp [aX]; infer_instance
  rw [← cancel_epi aX, ← Category.assoc, ← ha', Category.assoc, hY,
    ← Category.assoc, hb, Category.assoc, hTa', ← Category.assoc, ← hX, Category.assoc]

end DerivedComparison

section BalancedComparison

variable {k A B M N : Type*} [CommRing k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M] [Module Bᵐᵒᵖ M]
  [SMulCommClass A Bᵐᵒᵖ M] [AddCommGroup N] [Module k N] [Module B N] [IsScalarTower k B N]

private def compareTo : TensorProductOver B M N →+ BalancedTensor k A B M N :=
  TensorProductOver.lift
    { toFun := fun m => (BalancedTensor.mkBil k A B M N m).toAddMonoidHom
      map_zero' := by ext n; simp [BalancedTensor.mkBil]
      map_add' := by intro m n; ext x; simp [BalancedTensor.mkBil] }
    (by intro b m n; exact BalancedTensor.op_smul_tmul m b n)

private def compareFrom (hM : ∀ (c : k) (m : M), op (algebraMap k B c) • m = c • m) :
    BalancedTensor k A B M N →+ TensorProductOver B M N :=
  letI : Module k (TensorProductOver B M N) := Module.compHom _ (algebraMap k A)
  (BalancedTensor.lift
    { toFun := fun m =>
      { toFun := fun n => TensorProductOver.tmul B m n
        map_add' := TensorProductOver.tmul_add m
        map_smul' := fun c n => by
          change TensorProductOver.tmul B m (c • n) = (algebraMap k A c) • TensorProductOver.tmul B m n
          rw [← IsScalarTower.algebraMap_smul B c n, ← TensorProductOver.op_smul_tmul,
            hM, ← IsScalarTower.algebraMap_smul A c m, TensorProductOver.smul_tmul] }
      map_add' := by intro m m'; ext n; exact TensorProductOver.add_tmul m m' n
      map_smul' := fun c m => by
        ext n
        change TensorProductOver.tmul B (c • m) n = (algebraMap k A c) • TensorProductOver.tmul B m n
        rw [TensorProductOver.smul_tmul, IsScalarTower.algebraMap_smul A c m] }
    (fun m b n => TensorProductOver.op_smul_tmul b m n)).toAddMonoidHom

/-- The two balanced tensor products agree on underlying additive groups. -/
def ordinaryBalancedTensorAddEquiv (hM : ∀ (c : k) (m : M), op (algebraMap k B c) • m = c • m) :
    TensorProductOver B M N ≃+ BalancedTensor k A B M N where
  __ := compareTo
  invFun := compareFrom hM
  left_inv := by
    intro x
    change compareFrom hM (compareTo x) = x
    induction x using TensorProductOver.induction_on with
    | zero => simp
    | tmul m n => rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  right_inv := by
    intro x
    change compareTo (compareFrom hM x) = x
    induction x using BalancedTensor.induction_on with
    | zero => simp
    | tmul m n => rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]

@[simp]
theorem ordinaryBalancedTensorAddEquiv_tmul (hM : ∀ (c : k) (m : M),
    op (algebraMap k B c) • m = c • m) (m : M) (n : N) :
    ordinaryBalancedTensorAddEquiv (A := A) hM (TensorProductOver.tmul B m n) =
      BalancedTensor.tmul m n := rfl

end BalancedComparison

section LocalizedTensorHomology

variable {A : Type u} [Ring A] [HasDerivedCategory.{w, u} A]

variable {B M N P : Type u} [Ring B]
  [AddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]
  [AddCommGroup N] [Module B N] [AddCommGroup P] [Module B P]

/-- Ordinary balanced tensor identifies with degree-zero cohomology of its localization. -/
def tensorHomologyQEquiv :
    TensorProductOver B (InDegreeZero M) (InDegreeZero N) ≃+
      (DG.DerivedCategory.homologyFunctor ℤ 0).obj
        (Q.obj ((DGModuleCat.tensorFunctor A (InDegreeZero M)).obj
          (DGModuleCat.of B (InDegreeZero N)))) :=
  degreeZeroHomologyQEquiv (DGModuleCat.of A (TensorProductOver B (InDegreeZero M) (InDegreeZero N)))
    TensorProductOver.mem_grading_zero_inDegreeZero
    TensorProductOver.d_inDegreeZero

set_option backward.isDefEq.respectTransparency false in
/-- On balanced pure tensors, degree-zero cohomology of the localized tensor map applies
the original module map in the right factor. -/
theorem tensorHomologyQEquiv_tmul_naturality
    (f : DGModuleCat.of B (InDegreeZero N) ⟶ DGModuleCat.of B (InDegreeZero P))
    (m : InDegreeZero M) (n : InDegreeZero N) :
    (DG.DerivedCategory.homologyFunctor ℤ 0).map
      (Q.map ((DGModuleCat.tensorFunctor A (InDegreeZero M)).map f))
      (tensorHomologyQEquiv (A := A) (B := B) (M := M) (N := N) (TensorProductOver.tmul B m n)) =
    tensorHomologyQEquiv (A := A) (B := B) (M := M) (N := P) (TensorProductOver.tmul B m (f n)) := by
  let G := DGModuleCat.tensorFunctor (B := B) A (InDegreeZero M)
  let X := G.obj (DGModuleCat.of B (InDegreeZero N))
  let Y := G.obj (DGModuleCat.of B (InDegreeZero P))
  have hX : ∀ x : X, x ∈ grading 0 := TensorProductOver.mem_grading_zero_inDegreeZero
  have hdX : ∀ x : X, d x = 0 := TensorProductOver.d_inDegreeZero
  have hY : ∀ y : Y, y ∈ grading 0 := TensorProductOver.mem_grading_zero_inDegreeZero
  have hdY : ∀ y : Y, d y = 0 := TensorProductOver.d_inDegreeZero
  have h := degreeZeroHomologyQEquiv_naturality (G.map f) hX hdX hY hdY
    (TensorProductOver.tmul B m n)
  change _ = degreeZeroHomologyQEquiv Y hY hdY (G.map f (TensorProductOver.tmul B m n))
  exact h


set_option backward.isDefEq.respectTransparency false in
/-- An injective balanced map with the pure-tensor formula for a module map induces a
monomorphism on degree-zero cohomology of the localized tensor map. -/
theorem mono_tensorHomologyQ_of_balanced
    (f : DGModuleCat.of B (InDegreeZero N) ⟶ DGModuleCat.of B (InDegreeZero P))
    (μ : TensorProductOver B (InDegreeZero M) (InDegreeZero N) →+
      TensorProductOver B (InDegreeZero M) (InDegreeZero P))
    (hμ : ∀ (m : InDegreeZero M) (n : InDegreeZero N),
      μ (TensorProductOver.tmul B m n) = TensorProductOver.tmul B m (f n))
    (hinj : Function.Injective μ) :
    Mono ((DG.DerivedCategory.homologyFunctor ℤ 0).map
      (Q.map ((DGModuleCat.tensorFunctor A (InDegreeZero M)).map f))) := by
  let eX := tensorHomologyQEquiv (A := A) (B := B) (M := M) (N := N)
  let eY := tensorHomologyQEquiv (A := A) (B := B) (M := M) (N := P)
  let H := (DG.DerivedCategory.homologyFunctor ℤ 0).map
    (Q.map ((DGModuleCat.tensorFunctor A (InDegreeZero M)).map f))
  have h : (H.hom.toAddMonoidHom.comp eX.toAddMonoidHom) = eY.toAddMonoidHom.comp μ := by
    apply TensorProductOver.addHom_ext
    intro m n
    change H (eX (TensorProductOver.tmul B m n)) = eY (μ (TensorProductOver.tmul B m n))
    rw [hμ]
    exact tensorHomologyQEquiv_tmul_naturality (A := A) f m n
  apply (ModuleCat.mono_iff_injective H).mpr
  rintro x y hxy
  obtain ⟨x, rfl⟩ := eX.surjective x
  obtain ⟨y, rfl⟩ := eX.surjective y
  have comm (z : TensorProductOver B (InDegreeZero M) (InDegreeZero N)) :
      H (eX z) = eY (μ z) := DFunLike.congr_fun h z
  rw [comm, comm] at hxy
  exact congrArg eX (hinj (eY.injective hxy))

end LocalizedTensorHomology

section BalancedHomologyMap

variable {k A B M N P : Type u} [CommRing k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  [HasDerivedCategory.{w, u} A]
  [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M] [Module Bᵐᵒᵖ M]
  [SMulCommClass A Bᵐᵒᵖ M] [AddCommGroup N] [Module k N] [Module B N] [IsScalarTower k B N]
  [AddCommGroup P] [Module k P] [Module B P] [IsScalarTower k B P]

set_option backward.isDefEq.respectTransparency false in
/-- Injectivity of the ordinary balanced map implies the monomorphism on H⁰ of its
localized degree-zero DG tensor model. -/
theorem mono_tensorHomologyQ_of_ordinaryBalanced
    (hM : ∀ (c : k) (m : M), op (algebraMap k B c) • m = c • m)
    (f : DGModuleCat.of B (InDegreeZero N) ⟶ DGModuleCat.of B (InDegreeZero P))
    (μ : BalancedTensor k A B M N →+ BalancedTensor k A B M P)
    (hμ : ∀ (m : M) (n : N), μ (BalancedTensor.tmul m n) = BalancedTensor.tmul m (f n))
    (hinj : Function.Injective μ) :
    Mono ((DG.DerivedCategory.homologyFunctor ℤ 0).map
      (Q.map ((DGModuleCat.tensorFunctor A (InDegreeZero M)).map f))) := by
  let eX := ordinaryBalancedTensorAddEquiv (A := A) (N := N) hM
  let eY := ordinaryBalancedTensorAddEquiv (A := A) (N := P) hM
  let τ := eY.symm.toAddMonoidHom.comp (μ.comp eX.toAddMonoidHom)
  apply mono_tensorHomologyQ_of_balanced (A := A) f τ
  · intro m n
    change eY.symm (μ (eX (TensorProductOver.tmul B m n))) =
      TensorProductOver.tmul B m (f n)
    apply eY.injective
    rw [AddEquiv.apply_symm_apply]
    exact hμ _ _
  · exact eY.symm.injective.comp (hinj.comp eX.injective)


set_option backward.isDefEq.respectTransparency false in
/-- The injective ordinary balanced map is monic on the actual degree-zero derived tensor map. -/
theorem mono_derivedTensorHomology_of_ordinaryBalanced [HasDerivedCategory.{w, u} B]
    (hM : ∀ (c : k) (m : M), op (algebraMap k B c) • m = c • m)
    (f : DGModuleCat.of B (InDegreeZero N) ⟶ DGModuleCat.of B (InDegreeZero P))
    (μ : BalancedTensor k A B M N →+ BalancedTensor k A B M P)
    (hμ : ∀ (m : M) (n : N), μ (BalancedTensor.tmul m n) = BalancedTensor.tmul m (f n))
    (hinj : Function.Injective μ) :
    Mono ((DG.DerivedCategory.homologyFunctor ℤ 0).map ((derivedTensor A B M).map (Q.map f))) := by
  let H := DG.DerivedCategory.homologyFunctor (A := A) ℤ 0
  let g := H.map ((derivedTensor A B M).map (Q.map f))
  let eX := derivedTensorHomologyIsoOrdinary (A := A) (B := B) (M := M) N
  let eY := derivedTensorHomologyIsoOrdinary (A := A) (B := B) (M := M) P
  have := mono_tensorHomologyQ_of_ordinaryBalanced (A := A) hM f μ hμ hinj
  have : Mono (g ≫ eY.hom) := by
    rw [show g ≫ eY.hom = eX.hom ≫ H.map
      (Q.map ((DGModuleCat.tensorFunctor A (InDegreeZero M)).map f)) from
        derivedTensorHomologyIsoOrdinary_naturality f]
    infer_instance
  exact mono_of_mono g eY.hom

end BalancedHomologyMap

end Categorification

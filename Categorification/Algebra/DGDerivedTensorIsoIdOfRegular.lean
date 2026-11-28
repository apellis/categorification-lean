/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DGDerivedTensorQuasiIso
import Categorification.Algebra.DGBimoduleTruncation
import Categorification.Algebra.DerivedTensorTwist

set_option backward.isDefEq.respectTransparency false

/-!
# A derived tensor functor fixing the regular module is the identity

Let `T` be a ring concentrated in degree `0` and `X` a dg `(T, T)`-bimodule, in arbitrary
degrees, with derived tensor functor `S = X ⊗ᴸ_T - : D(T) ⥤ D(T)`. Suppose given an
isomorphism `φ : S(T) ≅ T` in `D(T)` which commutes with the right multiplications
`ρ_t : T → T, x ↦ x t` (the endomorphisms of the left module `T`):
`S(ρ_t) ≫ φ = φ ≫ ρ_t` for all `t`. Then `S ≅ 𝟭`
(`Categorification.dgDerivedTensorIsoIdOfRegularIso`).

The proof is the standard one. `S(T) ≅ X` (`dgDerivedTensorRegularObjIso`), so `X ≅ T` in
`D(T)` and the cohomology of `X` is concentrated in degree `0`. The zig-zag of bimodule
quasi-isomorphisms `X ← τ^{≤ 0} X → H⁰(X)` (`DGBimoduleTruncation.lean`) and the
quasi-isomorphism invariance of `X ⊗ᴸ_T -` (`dgDerivedTensorIsoOfQuasiIso`) give
`S ≅ H⁰(X) ⊗ᴸ_T -`. The isomorphism `H⁰(X) ≅ T` in `D(T)` comes from a module isomorphism
(modules in degree `0` embed fully faithfully, `degreeZeroModuleFunctor_comp_Q_full`), which
is right `T`-linear because `φ` commutes with the `ρ_t` (faithfulness). So `H⁰(X) ≅ T` as
bimodules, and `T ⊗ᴸ_T - ≅ 𝟭`.

This is the generic step of the bimodule form of B. Webster, *Knot invariants and higher
representation theory*, arXiv:1309.3796v3, proof of Proposition 7.22 ("any choice of
isomorphism `S(P_∅) ≅ P_∅` induces isomorphisms between functors"), for right modules over
`T^λ` (take `T = (T^λ)ᵐᵒᵖ`; the right multiplications of `Tᵐᵒᵖ` are the left multiplications
of `T^λ`). The input `φ` is what strong equivariance and fullness provide; the presentation
`S = - ⊗ᴸ X` is an input as well.
-/

open CategoryTheory DG DG.DerivedCategory MulOpposite
open scoped DG.DegreeZero

noncomputable section

namespace Categorification

attribute [local instance] tensorFunctorSignCommShift homotopyTensorFunctorSignCommShift

section Naturality

universe u

variable {A B : Type u} [Ring A] [Ring B] [HasDerivedCategory.{u, u} A]
  [HasDerivedCategory.{u, u} B]
  {X : Type u} [AddCommGroup X] [DGAddCommGroup X] [Module A X] [Module Bᵐᵒᵖ X]
  [DGBimodule A B X]

/-- `dgDerivedTensorObjIso` is natural in maps between K-projective modules. -/
theorem dgDerivedTensorObjIso_naturality {P P' : DGModuleCat.{u} B} (hP : IsKProjective.{u} B P)
    (hP' : IsKProjective.{u} B P') (g : P ⟶ P') :
    (dgDerivedTensor.{u} A B X).map (Q.map g) ≫ (dgDerivedTensorObjIso (X := X) hP').hom =
      (dgDerivedTensorObjIso (X := X) hP).hom ≫ Q.map ((DGModuleCat.tensorFunctor A X).map g) := by
  let E := kProjectiveEquivalence.{u} B
  let ι := (DG.HomotopyCategory.subcategoryKProjective B).ι
  let q := DG.HomotopyCategory.quotient B
  let V : KProjective B := ⟨q.obj P,
    (DG.HomotopyCategory.quotient_obj_mem_subcategoryKProjective_iff P).mpr hP⟩
  let V' : KProjective B := ⟨q.obj P',
    (DG.HomotopyCategory.quotient_obj_mem_subcategoryKProjective_iff P').mpr hP'⟩
  let gV : V ⟶ V' := ObjectProperty.homMk (q.map g)
  let T := DG.HomotopyCategory.tensorFunctor (B := B) A X
  let e := DG.HomotopyCategory.tensorFunctorQuotientIso (B := B) A X
  have h₁ := E.unitIso.inv.naturality gV
  have h₂ := e.hom.naturality g
  have h₃ : ι.map (E.inverse.map (Q.map g)) ≫ ι.map (E.unitIso.inv.app V') =
      ι.map (E.unitIso.inv.app V) ≫ q.map g := by
    exact (ι.map_comp _ _).symm.trans ((congrArg ι.map h₁).trans (ι.map_comp _ _))
  simp only [dgDerivedTensorObjIso, Functor.mapIso_hom, Iso.trans_hom, Functor.map_comp,
    Iso.symm_hom, Iso.app_hom]
  change Qh.map (T.map (ι.map (E.inverse.map (Q.map g)))) ≫
      (Qh.map (T.map (ι.map (E.unitIso.inv.app V'))) ≫ Qh.map (e.hom.app P')) =
    (Qh.map (T.map (ι.map (E.unitIso.inv.app V))) ≫ Qh.map (e.hom.app P)) ≫
      Qh.map ((DG.HomotopyCategory.quotient A).map ((DGModuleCat.tensorFunctor A X).map g))
  simp only [← Functor.map_comp, Category.assoc]
  rw [← Category.assoc (T.map _) (T.map _), ← T.map_comp, h₃, T.map_comp, Category.assoc]
  exact congrArg (fun k => Qh.map (T.map (ι.map (E.unitIso.inv.app V)) ≫ k)) h₂

end Naturality

section Regular

variable {T : Type} [Ring T]
  {X : Type} [AddCommGroup X] [DGAddCommGroup X] [Module T X] [Module Tᵐᵒᵖ X] [DGBimodule T T X]

omit [Ring T] in
theorem ring_mem_grading_zero' [Ring T] (t : T) : t ∈ grading (M := T) 0 :=
  (InDegreeZero.ring_mem_grading_iff (R := T)).2 (Or.inl rfl)

variable (T) in
/-- **Right multiplication** `x ↦ x t` on the regular module, an endomorphism of the left dg
module `T`. -/
def regularRightMul (t : T) : DGModuleCat.of T T ⟶ DGModuleCat.of T T :=
  DGModuleCat.ofHom
    { toFun := fun x => x * t
      map_add' := fun x y => add_mul x y t
      map_smul' := fun a x => mul_assoc a x t
      map_mem' := fun {n x} hx => by
        rcases (InDegreeZero.ring_mem_grading_iff (R := T)).1 hx with rfl | rfl
        · exact ring_mem_grading_zero' _
        · rw [zero_mul]; exact zero_mem _
      map_d' := fun x => by
        rw [DegreeZero.d_apply, DegreeZero.d_apply, zero_mul] }

@[simp]
theorem regularRightMul_apply (t x : T) : regularRightMul T t x = x * t := rfl

variable (X) in
/-- **The right action** `x ↦ x • t` of `t ∈ T` on a dg `(T, T)`-bimodule, an endomorphism of
the left dg module `X`. -/
def bimoduleRightAct (t : T) : DGModuleCat.of T X ⟶ DGModuleCat.of T X :=
  DGModuleCat.ofHom
    { toFun := fun x => op t • x
      map_add' := smul_add (op t)
      map_smul' := fun a x => (smul_comm a (op t) x).symm
      map_mem' := fun {n x} hx => by simpa using op_smul_mem_grading (ring_mem_grading_zero' t) hx
      map_d' := fun x => (d_op_smul_of_d_eq_zero' (DegreeZero.d_apply t) x).symm }

@[simp]
theorem bimoduleRightAct_apply (t : T) (x : X) : bimoduleRightAct X t x = op t • x := rfl

theorem tensorRegularDGIso_rightMul (t : T) :
    (DGModuleCat.tensorFunctor T X).map (regularRightMul T t) ≫ (tensorRegularDGIso X).hom =
      (tensorRegularDGIso X).hom ≫ bimoduleRightAct X t :=
  DGModuleCat.tensor_hom_ext (A := T) (M := X) fun m b => by
    change op (b * t) • m = op t • (op b • m)
    rw [op_mul, mul_smul]

variable [HasDerivedCategory.{0, 0} T]

variable (X) in
/-- `X ⊗ᴸ_T T ≅ X` in `D(T)`. -/
def dgDerivedTensorRegularObjIso :
    (dgDerivedTensor.{0} T T X).obj (Q.obj (DGModuleCat.of T T)) ≅ Q.obj (DGModuleCat.of T X) :=
  dgDerivedTensorObjIso (A := T) (X := X) (isKProjective_self.{0} (A := T) :
      IsKProjective.{0} T (DGModuleCat.of T T)) ≪≫
    Q.mapIso (tensorRegularDGIso X)

theorem dgDerivedTensorRegularObjIso_rightMul (t : T) :
    (dgDerivedTensor.{0} T T X).map (Q.map (regularRightMul T t)) ≫
        (dgDerivedTensorRegularObjIso X).hom =
      (dgDerivedTensorRegularObjIso X).hom ≫ Q.map (bimoduleRightAct X t) := by
  have hP : IsKProjective.{0} T (DGModuleCat.of T T) := isKProjective_self.{0} (A := T)
  have h := dgDerivedTensorObjIso_naturality (A := T) (X := X) hP hP (regularRightMul T t)
  simp only [dgDerivedTensorRegularObjIso, Iso.trans_hom, Functor.mapIso_hom, ← Category.assoc, h]
  simp only [Category.assoc, ← Q.map_comp, tensorRegularDGIso_rightMul]

omit [HasDerivedCategory.{0, 0} T] in
theorem subsingleton_cohomology_ring_degreeZero {k : ℤ} (hk : k ≠ 0) :
    Subsingleton (cohomology T k) :=
  subsingleton_cohomology_iff.mpr fun m hm _ => by
    rw [((InDegreeZero.ring_mem_grading_iff (R := T)).1 hm).resolve_left hk]
    exact zero_mem _

/-- A dg module isomorphic to `T` in `D(T)` has cohomology concentrated in degree `0`. -/
theorem subsingleton_cohomology_of_iso_regular
    (e : Q.obj (DGModuleCat.of T X) ≅ Q.obj (DGModuleCat.of T T)) {k : ℤ} (hk : k ≠ 0) :
    Subsingleton (cohomology X k) := by
  have h := isZero_homologyFunctor_iff_of_iso e k
  rw [isZero_homologyFunctor_Q_obj_iff, isZero_homologyFunctor_Q_obj_iff] at h
  exact h.mpr (subsingleton_cohomology_ring_degreeZero hk)

variable (T) in
/-- The regular module `T` placed in degree `0` is the dg module `T`. -/
def regularInDegreeZeroEquiv : InDegreeZero T ≃ᵈᵍ[T] T :=
  DGModuleEquiv.ofDegreeZero (LinearEquiv.refl T T)
    (fun hx hn => ((InDegreeZero.mem_grading_iff _).mp hx).resolve_left hn)
    (fun x => InDegreeZero.d_apply _ x) ring_mem_grading_zero' (fun t => DegreeZero.d_apply t)

/-- **The right action** `x ↦ x • t` of `t ∈ T` on a `(T, T)`-bimodule, as a map of left
modules. -/
def moduleRightAct (M : Type) [AddCommGroup M] [Module T M] [Module Tᵐᵒᵖ M]
    [SMulCommClass T Tᵐᵒᵖ M] (t : T) : ModuleCat.of T M ⟶ ModuleCat.of T M :=
  ModuleCat.ofHom
    { toFun := fun x => op t • x
      map_add' := smul_add (op t)
      map_smul' := fun a x => (smul_comm a (op t) x).symm }

omit [HasDerivedCategory.{0, 0} T] in
theorem regularInDegreeZeroEquiv_rightMul (t : T) :
    regularRightMul T t ≫ (regularInDegreeZeroEquiv T).toDGModuleCatIso.inv =
      (regularInDegreeZeroEquiv T).toDGModuleCatIso.inv ≫
        (degreeZeroModuleFunctor T).map (moduleRightAct T t) :=
  DGModuleCat.hom_ext_apply fun x => (op_smul_eq_mul (α := T) t x).symm

omit [HasDerivedCategory.{0, 0} T] in
theorem bimoduleTruncLE_subtype_rightAct (t : T) :
    bimoduleRightAct (bimoduleTruncLE T T X) t ≫
        DGModuleCat.ofHom (bimoduleTruncLE T T X).subtype =
      DGModuleCat.ofHom (bimoduleTruncLE T T X).subtype ≫ bimoduleRightAct X t :=
  DGModuleCat.hom_ext_apply fun _ => rfl

omit [HasDerivedCategory.{0, 0} T] in
theorem bimoduleCohomologyZeroπ_rightAct (t : T) :
    bimoduleRightAct (bimoduleTruncLE T T X) t ≫
        DGModuleCat.ofHom (bimoduleCohomologyZeroπ T T X) =
      DGModuleCat.ofHom (bimoduleCohomologyZeroπ T T X) ≫
        (degreeZeroModuleFunctor T).map (moduleRightAct (bimoduleCohomologyZero T T X) t) :=
  DGModuleCat.hom_ext_apply fun _ => rfl

section CohomologyZero

variable (χ : Q.obj (DGModuleCat.of T X) ≅ Q.obj (DGModuleCat.of T T))
  (hX : ∀ k : ℤ, k ≠ 0 → Subsingleton (cohomology X k))

/-- The isomorphism `H⁰(X) ≅ T` in `D(T)` obtained from `χ : X ≅ T` and the zig-zag
`H⁰(X) ← τ^{≤ 0} X → X`. -/
def cohomologyZeroRegularIso :
    (degreeZeroModuleFunctor T ⋙ Q).obj (ModuleCat.of T (bimoduleCohomologyZero T T X)) ≅
      (degreeZeroModuleFunctor T ⋙ Q).obj (ModuleCat.of T T) :=
  have : IsIso (Q.map (DGModuleCat.ofHom (bimoduleCohomologyZeroπ T T X))) :=
    (isIso_Q_map_iff _).mpr (isQuasiIso_bimoduleCohomologyZeroπ hX)
  have : IsIso (Q.map (DGModuleCat.ofHom (bimoduleTruncLE T T X).subtype)) :=
    (isIso_Q_map_iff _).mpr (isQuasiIso_bimoduleTruncLE_subtype fun k hk => hX k hk.ne')
  (asIso (Q.map (DGModuleCat.ofHom (bimoduleCohomologyZeroπ T T X)))).symm ≪≫
    asIso (Q.map (DGModuleCat.ofHom (bimoduleTruncLE T T X).subtype)) ≪≫ χ ≪≫
      Q.mapIso (regularInDegreeZeroEquiv T).toDGModuleCatIso.symm

/-- **`H⁰(X) ≅ T` as left `T`-modules**, the preimage of `cohomologyZeroRegularIso` under the
fully faithful embedding of modules into `D(T)`. -/
def cohomologyZeroLinearEquiv : bimoduleCohomologyZero T T X ≃ₗ[T] T :=
  ((degreeZeroModuleFunctor T ⋙ Q).preimageIso (cohomologyZeroRegularIso χ hX)).toLinearEquiv

theorem cohomologyZeroRegularIso_rightAct
    (hχ : ∀ t : T, Q.map (bimoduleRightAct X t) ≫ χ.hom = χ.hom ≫ Q.map (regularRightMul T t))
    (t : T) :
    (degreeZeroModuleFunctor T ⋙ Q).map (moduleRightAct (bimoduleCohomologyZero T T X) t) ≫
        (cohomologyZeroRegularIso χ hX).hom =
      (cohomologyZeroRegularIso χ hX).hom ≫
        (degreeZeroModuleFunctor T ⋙ Q).map (moduleRightAct T t) := by
  have : IsIso (Q.map (DGModuleCat.ofHom (bimoduleCohomologyZeroπ T T X))) :=
    (isIso_Q_map_iff _).mpr (isQuasiIso_bimoduleCohomologyZeroπ hX)
  have hπ : Q.map ((degreeZeroModuleFunctor T).map
        (moduleRightAct (bimoduleCohomologyZero T T X) t)) ≫
        inv (Q.map (DGModuleCat.ofHom (bimoduleCohomologyZeroπ T T X))) =
      inv (Q.map (DGModuleCat.ofHom (bimoduleCohomologyZeroπ T T X))) ≫
        Q.map (bimoduleRightAct (bimoduleTruncLE T T X) t) := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, ← Q.map_comp, ← bimoduleCohomologyZeroπ_rightAct,
      Q.map_comp, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hι := congrArg Q.map (bimoduleTruncLE_subtype_rightAct (X := X) t)
  have hr := congrArg Q.map (regularInDegreeZeroEquiv_rightMul t)
  simp only [Q.map_comp] at hι hr
  simp only [cohomologyZeroRegularIso, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
    Functor.mapIso_hom, Functor.comp_map, Category.assoc]
  rw [reassoc_of% hπ, reassoc_of% hι, reassoc_of% (hχ t), hr]

theorem cohomologyZeroLinearEquiv_op_smul
    (hχ : ∀ t : T, Q.map (bimoduleRightAct X t) ≫ χ.hom = χ.hom ≫ Q.map (regularRightMul T t))
    (t : T) (h : bimoduleCohomologyZero T T X) :
    cohomologyZeroLinearEquiv χ hX (op t • h) = op t • cohomologyZeroLinearEquiv χ hX h := by
  let F := degreeZeroModuleFunctor T ⋙ Q
  have key : moduleRightAct (bimoduleCohomologyZero T T X) t ≫
        (F.preimageIso (cohomologyZeroRegularIso χ hX)).hom =
      (F.preimageIso (cohomologyZeroRegularIso χ hX)).hom ≫ moduleRightAct T t := by
    apply F.map_injective
    simp only [F.map_comp, Functor.preimageIso_hom, Functor.map_preimage]
    exact cohomologyZeroRegularIso_rightAct χ hX hχ t
  exact congrArg (fun f => f.hom h) key

/-- `H⁰(X) ≅ T` as dg bimodules in degree `0`. -/
def cohomologyZeroRegularDGEquiv : InDegreeZero (bimoduleCohomologyZero T T X) ≃ᵈᵍ[T] T :=
  DGModuleEquiv.ofDegreeZero (cohomologyZeroLinearEquiv χ hX)
    (fun hx hn => ((InDegreeZero.mem_grading_iff _).mp hx).resolve_left hn)
    (fun x => InDegreeZero.d_apply _ x) ring_mem_grading_zero' (fun t => DegreeZero.d_apply t)

end CohomologyZero

/-- **A derived tensor functor fixing the regular module is the identity.** Let `X` be a dg
`(T, T)`-bimodule over a ring `T` in degree `0`, and `φ : X ⊗ᴸ_T T ≅ T` an isomorphism in `D(T)`
commuting with the right multiplications `ρ_t` of `T` (`hφ`). Then `X ⊗ᴸ_T - ≅ 𝟭`. -/
def dgDerivedTensorIsoIdOfRegularIso
    (φ : (dgDerivedTensor.{0} T T X).obj (Q.obj (DGModuleCat.of T T)) ≅
      Q.obj (DGModuleCat.of T T))
    (hφ : ∀ t : T, (dgDerivedTensor.{0} T T X).map (Q.map (regularRightMul T t)) ≫ φ.hom =
      φ.hom ≫ Q.map (regularRightMul T t)) :
    dgDerivedTensor.{0} T T X ≅ 𝟭 _ :=
  let χ := (dgDerivedTensorRegularObjIso X).symm ≪≫ φ
  have hχ : ∀ t : T,
      Q.map (bimoduleRightAct X t) ≫ χ.hom = χ.hom ≫ Q.map (regularRightMul T t) := fun t => by
    have h : Q.map (bimoduleRightAct X t) ≫ (dgDerivedTensorRegularObjIso X).inv =
        (dgDerivedTensorRegularObjIso X).inv ≫
          (dgDerivedTensor.{0} T T X).map (Q.map (regularRightMul T t)) := by
      rw [Iso.eq_inv_comp, ← Category.assoc, ← dgDerivedTensorRegularObjIso_rightMul,
        Category.assoc, Iso.hom_inv_id, Category.comp_id]
    simp only [χ, Iso.trans_hom, Iso.symm_hom, Category.assoc, ← hφ t]
    rw [reassoc_of% h]
  have hX : ∀ k : ℤ, k ≠ 0 → Subsingleton (cohomology X k) :=
    fun _ hk => subsingleton_cohomology_of_iso_regular χ hk
  (dgDerivedTensorIsoOfQuasiIso (bimoduleTruncLE T T X).subtype
      (bimoduleTruncLE_subtype_op_smul (A := T) (B := T) (X := X))
      (isQuasiIso_bimoduleTruncLE_subtype fun k hk => hX k hk.ne')).symm ≪≫
    dgDerivedTensorIsoOfQuasiIso (bimoduleCohomologyZeroπ T T X)
      (fun b x => bimoduleCohomologyZeroπ_op_smul (A := T) (B := T) (X := X) b x)
      (isQuasiIso_bimoduleCohomologyZeroπ hX) ≪≫
    dgDerivedTensorIsoOfEquiv.{0} (cohomologyZeroRegularDGEquiv χ hX)
      (fun b x => cohomologyZeroLinearEquiv_op_smul χ hX hχ b x) ≪≫
    dgDerivedTensorRegularIso T

end Regular

end Categorification

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensorCompComparison
import Categorification.Algebra.DerivedTensorProjective
import Categorification.Algebra.DerivedTensorRingEquiv

set_option backward.isDefEq.respectTransparency false

/-!
# Transport of derived tensor products along ring isomorphisms

For a ring isomorphism `φ : C ≃+* D`, the twisted bimodule `ᵠD` (`D` with `c • x = φ c * x` and
the regular right action) gives the functor `T_φ = - ⊗ᴸ_C ᵠD : D(Cᵒᵖ) ⥤ D(Dᵒᵖ)`, restriction of
scalars along `φ⁻¹`. These functors compose, `T_φ ⋙ T_ψ ≅ T_{ψ ∘ φ}` (`twistFunctorCompIso`), and
`T_id ≅ 𝟭` (`twistFunctorReflIso`), so each `T_φ` is an equivalence (`twistEquivalence`).

A bimodule isomorphism `N ≅ N'` over ring isomorphisms `φ`, `ψ` conjugates the derived tensor
products: `(- ⊗ᴸ N) ⋙ T_ψ ≅ T_φ ⋙ (- ⊗ᴸ N')` (`derivedRightTensorTwistConjIso`), so one is an
equivalence when the other is (`isEquivalence_derivedRightTensor_of_twistConj`).

This is used for B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, proof of Theorem 6.15, to relabel the red strands of the braiding functors.
-/

noncomputable section

namespace Categorification

open CategoryTheory CategoryTheory.Limits DG DG.DerivedCategory MulOpposite
open scoped DG.DegreeZero

/-- A module over `D`, regarded as a module over `C` through a ring homomorphism `φ : C →+* D`;
the other actions are unchanged. -/
def LeftTwist {C D : Type} [Ring C] [Ring D] (_φ : C →+* D) (N : Type) : Type := N

namespace LeftTwist

variable {C D : Type} [Ring C] [Ring D] (φ : C →+* D) (N : Type) [AddCommGroup N] [Module D N]

instance : AddCommGroup (LeftTwist φ N) := inferInstanceAs (AddCommGroup N)

instance : Module C (LeftTwist φ N) := Module.compHom N φ

/-- The identity, from `N` to its twist. -/
def of : N ≃+ LeftTwist φ N := AddEquiv.refl N

theorem smul_def (c : C) (x : LeftTwist φ N) :
    c • x = of φ N (φ c • (of φ N).symm x) := rfl

instance {E : Type} [Ring E] [Module E N] : Module E (LeftTwist φ N) :=
  inferInstanceAs (Module E N)

instance {E : Type} [Ring E] [Module E N] [SMulCommClass D E N] :
    SMulCommClass C E (LeftTwist φ N) where
  smul_comm c e x := smul_comm (φ c) e (show N from x)

end LeftTwist

/-- The twisted bimodule `ᵠD` of a ring isomorphism `φ : C ≃+* D`: the `(C, D)`-bimodule `D`
with `c • x = φ c * x`. -/
abbrev TwistBimodule {C D : Type} [Ring C] [Ring D] (φ : C ≃+* D) : Type :=
  LeftTwist (φ : C →+* D) D

variable {C D E : Type} [Ring C] [Ring D] [Ring E]

/-- The twisted bimodule is free of rank one as a right module. -/
def twistBimoduleRightEquiv (φ : C ≃+* D) :
    OpBimodule C (TwistBimodule φ) ≃ₗ[Dᵐᵒᵖ] Dᵐᵒᵖ where
  toFun x := op (show D from x)
  invFun y := (unop y : D)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance projective_twistBimodule (φ : C ≃+* D) :
    Module.Projective Dᵐᵒᵖ (OpBimodule C (TwistBimodule φ)) :=
  Module.Projective.of_equiv (twistBimoduleRightEquiv φ).symm

section Iso

variable [HasDerivedCategory.{0, 0} Cᵐᵒᵖ] [HasDerivedCategory.{0, 0} Dᵐᵒᵖ]
  [HasDerivedCategory.{0, 0} Eᵐᵒᵖ]

/-- A bimodule isomorphism `N ≅ N'` in degree zero, as an isomorphism of dg bimodules over
`(Dᵒᵖ, Cᵒᵖ)`. -/
def opBimoduleDGEquiv {N N' : Type} [AddCommGroup N] [Module C N] [Module Dᵐᵒᵖ N]
    [AddCommGroup N'] [Module C N'] [Module Dᵐᵒᵖ N'] (e : N ≃ₗ[Dᵐᵒᵖ] N') :
    InDegreeZero (OpBimodule C N) ≃ᵈᵍ[Dᵐᵒᵖ] InDegreeZero (OpBimodule C N') :=
  DGModuleEquiv.ofDegreeZero
    { toFun := fun x => (e (show N from x) : N')
      invFun := fun y => (e.symm (show N' from y) : N)
      left_inv := fun x => e.symm_apply_apply (show N from x)
      right_inv := fun y => e.apply_symm_apply (show N' from y)
      map_add' := fun x y => e.map_add (show N from x) (show N from y)
      map_smul' := fun d x => e.map_smul d (show N from x) }
    (fun hx hn => by
      rcases (InDegreeZero.mem_grading_iff _).mp hx with h | h
      · exact absurd h hn
      · exact h)
    (fun x => InDegreeZero.d_apply _ x)
    (fun _ => (InDegreeZero.mem_grading_iff _).mpr (Or.inl rfl))
    (fun y => InDegreeZero.d_apply _ y)

/-- **Derived tensor products with isomorphic bimodules are isomorphic.** -/
def derivedRightTensorIsoOfEquiv {N N' : Type} [AddCommGroup N] [Module C N] [Module Dᵐᵒᵖ N]
    [SMulCommClass C Dᵐᵒᵖ N] [AddCommGroup N'] [Module C N'] [Module Dᵐᵒᵖ N']
    [SMulCommClass C Dᵐᵒᵖ N'] (e : N ≃ₗ[Dᵐᵒᵖ] N') (he : ∀ (c : C) (x : N), e (c • x) = c • e x) :
    derivedRightTensor.{0} C D N ≅ derivedRightTensor.{0} C D N' :=
  dgDerivedTensorIsoOfEquiv (opBimoduleDGEquiv e) fun b x => he b.unop (show N from x)

end Iso

section TwistFirst

variable (φ : C ≃+* D) (N : Type) [AddCommGroup N] [Module D N] [Module Eᵐᵒᵖ N]
  [SMulCommClass D Eᵐᵒᵖ N]

local notation "TT" => TensorProductOver Dᵐᵒᵖ (InDegreeZero (OpBimodule D N))
  (InDegreeZero (OpBimodule C (TwistBimodule φ)))
local notation "NT" => InDegreeZero (OpBimodule C (LeftTwist (φ : C →+* D) N))

/-- The action map `N ⊗_D ᵠD → ᵠN`, `m ⊗ x ↦ x m`. -/
def twistFirstMul : TT →+ NT :=
  TensorProductOver.lift
    (AddMonoidHom.mk' (fun m : InDegreeZero (OpBimodule D N) =>
      AddMonoidHom.mk' (fun x : InDegreeZero (OpBimodule C (TwistBimodule φ)) =>
        (((show D from x) • (show N from m) : N) : NT))
        fun x y => add_smul (show D from x) (show D from y) (show N from m))
      fun m m' => by
        ext x
        exact smul_add (show D from x) (show N from m) (show N from m'))
    fun a m x => (mul_smul (show D from x) a.unop (show N from m)).symm

theorem twistFirstMul_tmul (m : InDegreeZero (OpBimodule D N))
    (x : InDegreeZero (OpBimodule C (TwistBimodule φ))) :
    twistFirstMul φ N (TensorProductOver.tmul _ m x) =
      (((show D from x) • (show N from m) : N) : NT) := rfl

/-- The inverse `m ↦ m ⊗ 1`. -/
def twistFirstMulInv : NT →+ TT where
  toFun m := TensorProductOver.tmul _ (show N from m) ((1 : D) : TwistBimodule φ)
  map_zero' := TensorProductOver.zero_tmul _
  map_add' _ _ := TensorProductOver.add_tmul _ _ _

theorem twistFirstMul_inv (t : TT) : twistFirstMulInv φ N (twistFirstMul φ N t) = t := by
  induction t using TensorProductOver.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul m x =>
    rw [twistFirstMul_tmul]
    change TensorProductOver.tmul _ ((op (op (show D from x)) •
      (m : InDegreeZero (OpBimodule D N))) : InDegreeZero (OpBimodule D N)) _ = _
    rw [TensorProductOver.op_smul_tmul]
    congr 1
    exact one_mul (show D from x)
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem twistFirstMul_inv' (m : NT) : twistFirstMul φ N (twistFirstMulInv φ N m) = m :=
  one_smul D (show N from m)

theorem twistFirstMul_smul (b : Eᵐᵒᵖ) (t : TT) :
    twistFirstMul φ N (b • t) = b • twistFirstMul φ N t := by
  induction t using TensorProductOver.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul m x =>
    rw [TensorProductOver.smul_tmul]
    exact smul_comm (show D from x) b (show N from m)
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

open TensorProductOver.RightAction in
theorem twistFirstMul_op_smul (b : Cᵐᵒᵖ) (t : TT) :
    twistFirstMul φ N (op b • t) = op b • twistFirstMul φ N t := by
  induction t using TensorProductOver.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul m x =>
    rw [TensorProductOver.op_smul_tmul_right]
    exact mul_smul (φ b.unop) (show D from x) (show N from m)
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- `N ⊗_D ᵠD ≅ ᵠN`, as dg bimodules in degree zero. -/
def twistFirstEquiv : TT ≃ᵈᵍ[Eᵐᵒᵖ] NT :=
  DGModuleEquiv.ofDegreeZero
    { toFun := twistFirstMul φ N
      invFun := twistFirstMulInv φ N
      left_inv := twistFirstMul_inv φ N
      right_inv := twistFirstMul_inv' φ N
      map_add' := map_add _
      map_smul' := twistFirstMul_smul φ N }
    (fun hx hn => TensorProductOver.eq_zero_of_mem_grading_inDegreeZero hn hx)
    TensorProductOver.d_inDegreeZero
    (fun _ => (InDegreeZero.mem_grading_iff _).mpr (Or.inl rfl))
    (fun y => InDegreeZero.d_apply _ y)

variable [HasDerivedCategory.{0, 0} Cᵐᵒᵖ] [HasDerivedCategory.{0, 0} Dᵐᵒᵖ]
  [HasDerivedCategory.{0, 0} Eᵐᵒᵖ]

open TensorProductOver.RightAction in
/-- **Restriction of scalars, then a derived tensor product**: `(- ⊗ᴸ_C ᵠD) ⊗ᴸ_D N ≅ - ⊗ᴸ_C ᵠN`.
-/
def twistFunctorCompDerivedRightTensorIso :
    derivedRightTensor.{0} C D (TwistBimodule φ) ⋙ derivedRightTensor.{0} D E N ≅
      derivedRightTensor.{0} C E (LeftTwist (φ : C →+* D) N) :=
  derivedTensorCompIsoOfTorVanishing Eᵐᵒᵖ Dᵐᵒᵖ Cᵐᵒᵖ (OpBimodule D N)
      (OpBimodule C (TwistBimodule φ))
      (fun n hn => isZero_derivedTensor_homology_of_projective _ _ n hn) ≪≫
    dgDerivedTensorIsoOfEquiv (twistFirstEquiv φ N) (twistFirstMul_op_smul φ N)

end TwistFirst

section Regular

/-- **The derived tensor product with the regular bimodule is the identity.** -/
def dgDerivedTensorRegularIso (A : Type) [Ring A] [HasDerivedCategory.{0, 0} A] :
    dgDerivedTensor.{0} A A A ≅ 𝟭 (DerivedCategory.{0} A) :=
  Functor.isoWhiskerLeft (kProjectiveEquivalence.{0} A).inverse
      (Functor.isoWhiskerLeft (DG.HomotopyCategory.subcategoryKProjective A).ι
        (Functor.isoWhiskerRight
          (DG.HomotopyCategory.liftNatIso _ (fun _ _ h => h) (DGModuleCat.tensorFunctorRegularIso A)
            ≪≫ DG.HomotopyCategory.liftFunctorIdIso) DG.DerivedCategory.Qh ≪≫
          Functor.leftUnitor _)) ≪≫
    (kProjectiveEquivalence.{0} A).counitIso

/-- The twisted bimodule of the identity is the regular dg bimodule. -/
def twistBimoduleReflEquiv :
    InDegreeZero (OpBimodule C (TwistBimodule (RingEquiv.refl C))) ≃ᵈᵍ[Cᵐᵒᵖ] Cᵐᵒᵖ :=
  DGModuleEquiv.ofDegreeZero
    { toFun := fun x => op (show C from x)
      invFun := fun y => (unop y : C)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    (fun hx hn => by
      rcases (InDegreeZero.mem_grading_iff _).mp hx with h | h
      · exact absurd h hn
      · exact h)
    (fun x => InDegreeZero.d_apply _ x)
    (fun _ => (InDegreeZero.ring_mem_grading_iff).mpr (Or.inl rfl))
    (fun y => InDegreeZero.ring_d_apply y)

variable [HasDerivedCategory.{0, 0} Cᵐᵒᵖ]

/-- **Restriction of scalars along the identity is the identity.** -/
def twistFunctorReflIso :
    derivedRightTensor.{0} C C (TwistBimodule (RingEquiv.refl C)) ≅ 𝟭 _ :=
  dgDerivedTensorIsoOfEquiv twistBimoduleReflEquiv (fun _ _ => rfl) ≪≫
    dgDerivedTensorRegularIso Cᵐᵒᵖ

end Regular

section Equivalence

variable [HasDerivedCategory.{0, 0} Cᵐᵒᵖ] [HasDerivedCategory.{0, 0} Dᵐᵒᵖ]
  [HasDerivedCategory.{0, 0} Eᵐᵒᵖ]

/-- Twisted bimodules of equal ring isomorphisms give isomorphic functors. -/
def twistFunctorCongr {φ φ' : C ≃+* D} (h : ∀ c, φ c = φ' c) :
    derivedRightTensor.{0} C D (TwistBimodule φ) ≅ derivedRightTensor.{0} C D (TwistBimodule φ') :=
  derivedRightTensorIsoOfEquiv
    { toFun := fun x => (show D from x)
      invFun := fun y => (show D from y)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    fun c x => by
      change φ c * (show D from x) = φ' c * (show D from x)
      rw [h]

/-- **Restrictions of scalars compose**: `T_φ ⋙ T_ψ ≅ T_{ψ ∘ φ}`. -/
def twistFunctorCompIso (φ : C ≃+* D) (ψ : D ≃+* E) :
    derivedRightTensor.{0} C D (TwistBimodule φ) ⋙ derivedRightTensor.{0} D E (TwistBimodule ψ) ≅
      derivedRightTensor.{0} C E (TwistBimodule (φ.trans ψ)) :=
  twistFunctorCompDerivedRightTensorIso φ (TwistBimodule ψ) ≪≫
    derivedRightTensorIsoOfEquiv
      { toFun := fun x => (show E from x)
        invFun := fun y => (show E from y)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
      fun _ _ => rfl

/-- **Restriction of scalars along a ring isomorphism is an equivalence** of derived categories
of right modules, with inverse the restriction along the inverse. -/
def twistEquivalence (φ : C ≃+* D) : DerivedCategory.{0} Cᵐᵒᵖ ≌ DerivedCategory.{0} Dᵐᵒᵖ :=
  CategoryTheory.Equivalence.mk (derivedRightTensor.{0} C D (TwistBimodule φ))
    (derivedRightTensor.{0} D C (TwistBimodule φ.symm))
    (twistFunctorReflIso.symm ≪≫
      twistFunctorCongr (φ' := φ.trans φ.symm) (fun c => (φ.symm_apply_apply c).symm) ≪≫
      (twistFunctorCompIso φ φ.symm).symm)
    (twistFunctorCompIso φ.symm φ ≪≫
      twistFunctorCongr (φ' := RingEquiv.refl D) (fun d => φ.apply_symm_apply d) ≪≫
      twistFunctorReflIso)

theorem twistEquivalence_functor (φ : C ≃+* D) :
    (twistEquivalence φ).functor = derivedRightTensor.{0} C D (TwistBimodule φ) := rfl

end Equivalence

section RegularCoefficient

variable {A B : Type} [Ring A] [Ring B] (M : Type) [AddCommGroup M] [Module A M]
  [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M] (e : M ≃ₗ[Bᵐᵒᵖ] B)

/-- The action map `M ⊗_B P → P`, `m ⊗ p ↦ e(m) p`, for a coefficient `M` free of rank one as a
right module. -/
def regularCoefficientMul (P : Type) [AddCommGroup P] [DGAddCommGroup P] [Module B P]
    [DGModule B P] : TensorProductOver B (InDegreeZero M) P →+ P :=
  TensorProductOver.lift
    (AddMonoidHom.mk' (fun m : InDegreeZero M =>
      AddMonoidHom.mk' (fun p : P => e (show M from m) • p) fun p p' => smul_add _ p p')
      fun m m' => by
        ext p
        change e (show M from m + m') • p = e (show M from m) • p + e (show M from m') • p
        rw [map_add, add_smul])
    fun a m p => by
      change e (op a • (show M from m)) • p = e (show M from m) • (a • p)
      rw [e.map_smul, op_smul_eq_mul, mul_smul]

/-- **Tensoring with a coefficient that is free of rank one on the right** changes nothing up to
isomorphism of dg abelian groups: `M ⊗_B P ≅ P`. -/
def regularCoefficientEquiv (P : Type) [AddCommGroup P] [DGAddCommGroup P] [Module B P]
    [DGModule B P] : DGAddEquiv (TensorProductOver B (InDegreeZero M) P) P :=
  DGAddEquiv.ofAddMonoidHom (regularCoefficientMul M e P)
    { toFun := fun p => TensorProductOver.tmul B (e.symm 1 : InDegreeZero M) p
      map_zero' := TensorProductOver.tmul_zero _
      map_add' := fun _ _ => TensorProductOver.tmul_add _ _ _ }
    (fun y => by
      induction y using TensorProductOver.induction_on with
      | zero => rw [map_zero]; exact TensorProductOver.tmul_zero _
      | tmul m p =>
        change TensorProductOver.tmul B (e.symm 1 : InDegreeZero M) (e (show M from m) • p) = _
        rw [← TensorProductOver.op_smul_tmul]
        congr 1
        change op (e (show M from m)) • e.symm 1 = (show M from m)
        rw [← e.symm.map_smul, op_smul_eq_mul, one_mul, e.symm_apply_apply]
      | add x y hx hy => rw [map_add, AddMonoidHom.map_add, hx, hy])
    (fun p => by
      change e (e.symm 1) • p = p
      rw [e.apply_symm_apply, one_smul])
    (fun hy => TensorProductOver.lift_mem _ _ (fun {i j m p} hm hp => by
      rcases (InDegreeZero.mem_grading_iff _).mp hm with rfl | rfl
      · exact smul_mem_grading
          ((InDegreeZero.ring_mem_grading_iff (R := B) (r := e (show M from m))).mpr
            (Or.inl rfl)) hp
      · change e 0 • p ∈ _
        rw [map_zero, zero_smul]
        exact zero_mem _) hy)
    (fun y => TensorProductOver.lift_d _ _ (fun {i m} hm p => by
      change d (e (show M from m) • p) = e (show M from (d m : InDegreeZero M)) • p +
        koszulSign i • (e (show M from m) • d p)
      rw [d_smul ((InDegreeZero.ring_mem_grading_iff (R := B) (r := e (show M from m))).mpr
        (Or.inl rfl)), InDegreeZero.ring_d_apply,
        zero_smul, zero_add, InDegreeZero.d_apply, map_zero, zero_smul, zero_add]
      rcases (InDegreeZero.mem_grading_iff _).mp hm with rfl | h
      · rfl
      · rw [show (show M from m) = 0 from h, map_zero, zero_smul, smul_zero, smul_zero]) y)

omit [SMulCommClass A Bᵐᵒᵖ M] in
private theorem subsingleton_cohomology_inDegreeZero' (N : Type) [AddCommGroup N] {n : ℤ}
    (hn : n ≠ 0) : Subsingleton (cohomology (InDegreeZero N) n) := by
  have : Subsingleton (cocycles (InDegreeZero N) n) := ⟨fun x y => Subtype.ext (by
    rcases (InDegreeZero.mem_grading_iff _).mp (mem_cocycles.mp x.2).1 with h | hx
    · exact absurd h hn
    rcases (InDegreeZero.mem_grading_iff _).mp (mem_cocycles.mp y.2).1 with h | hy
    · exact absurd h hn
    exact hx.trans hy.symm)⟩
  exact (cohomology.mk_surjective _ n).subsingleton

variable [HasDerivedCategory.{0, 0} A] [HasDerivedCategory.{0, 0} B]

include e in
/-- **Derived tensor products with a coefficient free of rank one on the right are concentrated
in degree `0`** on modules in degree `0`. -/
theorem isZero_derivedTensor_homology_of_regular (N : Type) [AddCommGroup N] [Module B N]
    (n : ℤ) (hn : n ≠ 0) :
    IsZero ((homologyFunctor (A := A) ℤ n).obj ((derivedTensor.{0} A B M).obj
      (DG.DerivedCategory.Q.obj (DGModuleCat.of B (InDegreeZero N))))) := by
  let R : ProjectiveResolution (ModuleCat.of B N) := projectiveResolution _
  let q := projectiveResolutionDGAugToOrdinary R
  have hq : q.hom.IsQuasiIso := projectiveResolutionDGAugToOrdinary_quasiIso R
  have : IsIso (DG.DerivedCategory.Q.map q) := (isIso_Q_map_iff q).mpr hq
  let Z := (DGModuleCat.tensorFunctor A (InDegreeZero M)).obj (projectiveResolutionDGModel R)
  let iso := (homologyFunctor (A := A) ℤ n).mapIso ((derivedTensor.{0} A B M).mapIso
    (asIso (DG.DerivedCategory.Q.map q)).symm ≪≫
      derivedTensorObjIso (projectiveResolutionDGModel_kProjective R))
  have hP : Subsingleton (cohomology (projectiveResolutionDGModel R) n) :=
    have := subsingleton_cohomology_inDegreeZero' N hn
    (hq n).1.subsingleton
  have hZ : Subsingleton (cohomology Z n) :=
    subsingleton_cohomology_of_dgAddEquiv (regularCoefficientEquiv M e _) n
  exact (ModuleCat.isZero_iff_subsingleton.mpr
    ((cohomologyAddEquiv ℤ Z n).surjective.subsingleton)).of_iso iso

end RegularCoefficient

/-- A right module over `C'`, regarded as a right module over `D'` through a ring homomorphism
`f : D' →+* C'`; the other actions are unchanged. -/
def RightTwist {C' D' : Type} [Ring C'] [Ring D'] (_f : D' →+* C') (N : Type) : Type := N

namespace RightTwist

variable {C' D' : Type} [Ring C'] [Ring D'] (f : D' →+* C') (N : Type) [AddCommGroup N]
  [Module C'ᵐᵒᵖ N]

instance : AddCommGroup (RightTwist f N) := inferInstanceAs (AddCommGroup N)

instance : Module D'ᵐᵒᵖ (RightTwist f N) := Module.compHom N (RingHom.op f)

instance {E : Type} [Ring E] [Module E N] : Module E (RightTwist f N) :=
  inferInstanceAs (Module E N)

instance {E : Type} [Ring E] [Module E N] [SMulCommClass E C'ᵐᵒᵖ N] :
    SMulCommClass E D'ᵐᵒᵖ (RightTwist f N) where
  smul_comm e d x := smul_comm e (RingHom.op f d) (show N from x)

end RightTwist

section TwistSecond

variable {C' D' : Type} [Ring C'] [Ring D'] (ψ : C' ≃+* D') (N : Type) [AddCommGroup N]
  [Module C'ᵐᵒᵖ N]

/-- The twisted bimodule `ᵠD'` is free of rank one as a right module over `C'`, through `ψ`. -/
def twistBimoduleLeftEquiv :
    OpBimodule C' (TwistBimodule ψ) ≃ₗ[C'ᵐᵒᵖᵐᵒᵖ] C'ᵐᵒᵖ where
  toFun x := op (ψ.symm (show D' from x))
  invFun y := (ψ (unop y) : D')
  left_inv x := ψ.apply_symm_apply (show D' from x)
  right_inv y := by
    change op (ψ.symm (ψ (unop y))) = y
    rw [ψ.symm_apply_apply, op_unop]
  map_add' x y := by
    change op (ψ.symm ((show D' from x) + (show D' from y))) = _
    rw [map_add, MulOpposite.op_add]
  map_smul' c x := by
    change op (ψ.symm (ψ c.unop.unop * (show D' from x))) = _
    rw [map_mul, ψ.symm_apply_apply, MulOpposite.op_mul]; rfl

local notation "ST" => TensorProductOver C'ᵐᵒᵖ (InDegreeZero (OpBimodule C' (TwistBimodule ψ)))
  (InDegreeZero (OpBimodule C N))
local notation "SN" => InDegreeZero (OpBimodule C (RightTwist (ψ.symm : D' →+* C') N))

/-- The action map `ᵠD' ⊗ N → Nᵠ`, `m ⊗ n ↦ n ψ⁻¹(m)` (with `N ⊗_{C'} ᵠD'` written through the
opposite rings). -/
def twistSecondMul : ST →+ SN :=
  TensorProductOver.lift
    (AddMonoidHom.mk' (fun m : InDegreeZero (OpBimodule C' (TwistBimodule ψ)) =>
      AddMonoidHom.mk' (fun x : InDegreeZero (OpBimodule C N) =>
        ((op (ψ.symm (show D' from m)) • (show N from x) : N) : SN))
        fun x y => smul_add _ (show N from x) (show N from y))
      fun m m' => by
        ext x
        change op (ψ.symm ((show D' from m) + (show D' from m'))) • (show N from x) = _
        rw [map_add, MulOpposite.op_add, add_smul]; rfl)
    fun a m x => by
      change op (ψ.symm (ψ a.unop * (show D' from m))) • (show N from x) =
        op (ψ.symm (show D' from m)) • (a • (show N from x))
      rw [map_mul, ψ.symm_apply_apply, MulOpposite.op_mul, op_unop, mul_smul]

omit [Ring C] in
theorem twistSecondMul_tmul (m : InDegreeZero (OpBimodule C' (TwistBimodule ψ)))
    (x : InDegreeZero (OpBimodule C N)) :
    twistSecondMul ψ N (TensorProductOver.tmul _ m x) =
      ((op (ψ.symm (show D' from m)) • (show N from x) : N) : SN) := rfl

/-- The inverse `n ↦ 1 ⊗ n`. -/
def twistSecondMulInv : SN →+ ST where
  toFun x := TensorProductOver.tmul _ ((1 : D') : TwistBimodule ψ) (show N from x)
  map_zero' := TensorProductOver.tmul_zero _
  map_add' _ _ := TensorProductOver.tmul_add _ _ _

omit [Ring C] in
theorem twistSecondMul_inv (t : ST) : twistSecondMulInv ψ N (twistSecondMul ψ N t) = t := by
  induction t using TensorProductOver.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul m x =>
    rw [twistSecondMul_tmul]
    change TensorProductOver.tmul _ _
      ((op (ψ.symm (show D' from m)) • (x : InDegreeZero (OpBimodule C N))) :
        InDegreeZero (OpBimodule C N)) = _
    rw [← TensorProductOver.op_smul_tmul]
    congr 1
    change ψ (ψ.symm (show D' from m)) * 1 = (show D' from m)
    rw [ψ.apply_symm_apply, mul_one]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

omit [Ring C] in
theorem twistSecondMul_inv' (x : SN) : twistSecondMul ψ N (twistSecondMulInv ψ N x) = x := by
  change op (ψ.symm 1) • (show N from x) = (show N from x)
  rw [map_one, MulOpposite.op_one, one_smul]

omit [Ring C] in
theorem twistSecondMul_smul (b : D'ᵐᵒᵖ) (t : ST) :
    twistSecondMul ψ N (b • t) = b • twistSecondMul ψ N t := by
  induction t using TensorProductOver.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul m x =>
    rw [TensorProductOver.smul_tmul]
    change op (ψ.symm ((show D' from m) * b.unop)) • (show N from x) =
      op (ψ.symm b.unop) • (op (ψ.symm (show D' from m)) • (show N from x))
    rw [map_mul, MulOpposite.op_mul, mul_smul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

variable [Module C N] [SMulCommClass C C'ᵐᵒᵖ N]

open TensorProductOver.RightAction in
theorem twistSecondMul_op_smul (b : Cᵐᵒᵖ) (t : ST) :
    twistSecondMul ψ N (op b • t) = op b • twistSecondMul ψ N t := by
  induction t using TensorProductOver.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul m x =>
    rw [TensorProductOver.op_smul_tmul_right]
    exact (smul_comm b.unop (op (ψ.symm (show D' from m))) (show N from x)).symm
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- `N ⊗_{C'} ᵠD' ≅ Nᵠ`, as dg bimodules in degree zero. -/
def twistSecondEquiv : ST ≃ᵈᵍ[D'ᵐᵒᵖ] SN :=
  DGModuleEquiv.ofDegreeZero
    { toFun := twistSecondMul ψ N
      invFun := twistSecondMulInv ψ N
      left_inv := twistSecondMul_inv ψ N
      right_inv := twistSecondMul_inv' ψ N
      map_add' := map_add _
      map_smul' := twistSecondMul_smul ψ N }
    (fun hx hn => TensorProductOver.eq_zero_of_mem_grading_inDegreeZero hn hx)
    TensorProductOver.d_inDegreeZero
    (fun _ => (InDegreeZero.mem_grading_iff _).mpr (Or.inl rfl))
    (fun y => InDegreeZero.d_apply _ y)

variable [HasDerivedCategory.{0, 0} Cᵐᵒᵖ] [HasDerivedCategory.{0, 0} C'ᵐᵒᵖ]
  [HasDerivedCategory.{0, 0} D'ᵐᵒᵖ]

open TensorProductOver.RightAction in
/-- **A derived tensor product, then restriction of scalars**:
`(- ⊗ᴸ_C N) ⊗ᴸ_{C'} ᵠD' ≅ - ⊗ᴸ_C Nᵠ`. -/
def derivedRightTensorCompTwistFunctorIso :
    derivedRightTensor.{0} C C' N ⋙ derivedRightTensor.{0} C' D' (TwistBimodule ψ) ≅
      derivedRightTensor.{0} C D' (RightTwist (ψ.symm : D' →+* C') N) :=
  derivedTensorCompIsoOfTorVanishing D'ᵐᵒᵖ C'ᵐᵒᵖ Cᵐᵒᵖ (OpBimodule C' (TwistBimodule ψ))
      (OpBimodule C N)
      (fun n hn => isZero_derivedTensor_homology_of_regular _ (twistBimoduleLeftEquiv ψ) _ n hn)
      ≪≫
    dgDerivedTensorIsoOfEquiv (twistSecondEquiv ψ N) (twistSecondMul_op_smul ψ N)

end TwistSecond

section Conj

variable {C' D' : Type} [Ring C'] [Ring D'] (φ : C ≃+* D) (ψ : C' ≃+* D')
  {N : Type} [AddCommGroup N] [Module C N] [Module C'ᵐᵒᵖ N] [SMulCommClass C C'ᵐᵒᵖ N]
  {N' : Type} [AddCommGroup N'] [Module D N'] [Module D'ᵐᵒᵖ N'] [SMulCommClass D D'ᵐᵒᵖ N']
  (g : N ≃+ N') (hg : ∀ (c : C) (x : N), g (c • x) = φ c • g x)
  (hg' : ∀ (c : C'ᵐᵒᵖ) (x : N), g (c • x) = op (ψ c.unop) • g x)
  [HasDerivedCategory.{0, 0} Cᵐᵒᵖ] [HasDerivedCategory.{0, 0} C'ᵐᵒᵖ]
  [HasDerivedCategory.{0, 0} Dᵐᵒᵖ] [HasDerivedCategory.{0, 0} D'ᵐᵒᵖ]

/-- The bimodule isomorphism `Nᵠ ≅ ᵠN'`. -/
def rightTwistLeftTwistEquiv :
    RightTwist (ψ.symm : D' →+* C') N ≃ₗ[D'ᵐᵒᵖ] LeftTwist (φ : C →+* D) N' where
  toFun x := g (show N from x)
  invFun y := g.symm (show N' from y)
  left_inv x := g.symm_apply_apply (show N from x)
  right_inv y := g.apply_symm_apply (show N' from y)
  map_add' x y := g.map_add (show N from x) (show N from y)
  map_smul' b x := by
    change g (op (ψ.symm b.unop) • (show N from x)) = b • g (show N from x)
    rw [hg', unop_op, ψ.apply_symm_apply, op_unop]

include hg hg' in
/-- **A bimodule isomorphism over ring isomorphisms conjugates the derived tensor products**:
`(- ⊗ᴸ N) ⋙ T_ψ ≅ T_φ ⋙ (- ⊗ᴸ N')`. -/
def derivedRightTensorTwistConjIso :
    derivedRightTensor.{0} C C' N ⋙ derivedRightTensor.{0} C' D' (TwistBimodule ψ) ≅
      derivedRightTensor.{0} C D (TwistBimodule φ) ⋙ derivedRightTensor.{0} D D' N' :=
  derivedRightTensorCompTwistFunctorIso ψ N ≪≫
    derivedRightTensorIsoOfEquiv (rightTwistLeftTwistEquiv φ ψ g hg') (fun c x => hg c x) ≪≫
    (twistFunctorCompDerivedRightTensorIso φ N').symm

include hg hg' in
/-- **Equivalences transport along bimodule isomorphisms over ring isomorphisms**: if
`- ⊗ᴸ N'` is an equivalence, so is `- ⊗ᴸ N`. -/
theorem isEquivalence_derivedRightTensor_of_twistConj
    [(derivedRightTensor.{0} D D' N').IsEquivalence] :
    (derivedRightTensor.{0} C C' N).IsEquivalence := by
  have : (derivedRightTensor.{0} C D (TwistBimodule φ)).IsEquivalence :=
    (twistEquivalence φ).isEquivalence_functor
  have : (derivedRightTensor.{0} C' D' (TwistBimodule ψ)).IsEquivalence :=
    (twistEquivalence ψ).isEquivalence_functor
  have : (derivedRightTensor.{0} C C' N ⋙
      derivedRightTensor.{0} C' D' (TwistBimodule ψ)).IsEquivalence :=
    Functor.isEquivalence_of_iso (derivedRightTensorTwistConjIso φ ψ g hg hg').symm
  exact Functor.isEquivalence_of_comp_right _ (derivedRightTensor.{0} C' D' (TwistBimodule ψ))

end Conj

end Categorification

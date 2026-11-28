/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721CrossCoefficient
import Categorification.WeightedKLR.Rigidity.CupCapProp721TwoStepComparison
import Categorification.Algebra.DegreewiseTensorElements

/-!
# The crossing on the dg derived `𝔈_i²` is left multiplication on dg modules

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21. Degreewise, under `CupCap.tensorComplexTwoStep`, the dg crossing
`Stendhal.blackCrossTensorNat` on `e' T^λ_{ν+i} ⊗ (e' T^λ_{ν+2i} ⊗ -)` is the crossing
`blackCross` on `Eᵢ²` (`Stendhal.blackCrossTensorNat_degreewise`): both send `m ⊗ (n ⊗ x)` to
`ψ m n x`. Hence the crossing `CupCap.dgBlackCross` on the dg derived `𝔈_i²` is induced on dg
modules by `Stendhal.blackCrossTensorNat` (`Stendhal.dgBlackCross_QComp`), and it commutes with
the derived tensor shift (`Stendhal.dgBlackCross_commShift`), with no hypothesis.

## Main results

* `Stendhal.blackCrossTensorNat_degreewise`.
* `Stendhal.dgBlackCross_QComp`.
* `Stendhal.dgBlackCross_commShift`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory MulOpposite InductionAlong KLR DG DG.DegreeZero

universe u

section Generic

variable {A B : Type u} [Ring A] [Ring B]
  (M : Type u) [AddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]
  {G : ModuleCat.{u} B ⥤ ModuleCat.{u} A} [G.Additive] (e : ordTensor A B M ≅ G)

/-- `CupCap.tensorComplexIsoOfIso` on `m ⊗ y` for `y` homogeneous of degree `p`. -/
theorem tensorComplexIsoOfIso_hom_f_tmul (Y : DGModuleCat.{u} B) {p : ℤ}
    (m : InDegreeZero M) (y : Y) (hy : y ∈ grading p)
    (h : TensorProductOver.tmul B m y ∈
      gradingSubmodule A ((DGModuleCat.tensorFunctor A (InDegreeZero M)).obj Y) p) :
    (((CupCap.tensorComplexIsoOfIso M e).hom.app Y).f p).hom ⟨TensorProductOver.tmul B m y, h⟩ =
      (e.hom.app ((complexFunctor B).obj Y |>.X p)).hom (TensorProductOver.tmul B m
        (show InDegreeZero (gradingSubmodule B Y p) from ⟨y, mem_gradingSubmodule.mpr hy⟩)) := by
  simp only [CupCap.tensorComplexIsoOfIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, HomologicalComplex.comp_f,
    ModuleCat.hom_comp, LinearMap.comp_apply, tensorFunctorCompComplexIso_hom_f_tmul M Y m y hy h]
  rfl

/-- `n ⊗ x` is homogeneous of the degree of `x` for `n` of degree `0`. -/
theorem tmul_mem_grading_of_inDegreeZero {C : Type u} [Ring C] {N : Type u} [AddCommGroup N]
    [Module B N] [Module Cᵐᵒᵖ N] [SMulCommClass B Cᵐᵒᵖ N] (X : DGModuleCat.{u} C) {p : ℤ}
    (n : InDegreeZero N) {x : X} (hx : x ∈ grading p) :
    TensorProductOver.tmul C n x ∈ grading p := by
  have hn : n ∈ grading 0 := (InDegreeZero.mem_grading_iff (M := N)).mpr (Or.inl rfl)
  simpa using TensorProductOver.tmul_mem_grading (A := C) hn hx

/-- Evaluating a composite of module maps at an element whose image under the first is known. -/
theorem hom_comp_apply_of_eq {R : Type u} [Ring R] {X Y Z : ModuleCat.{u} R} (f : X ⟶ Y)
    (g : Y ⟶ Z) {x : X} {y : Y} (h : f.hom x = y) : (f ≫ g).hom x = g.hom y := by
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, h]

section ResTwo

variable {A B C : Type u} [Ring A] [Ring B] [Ring C] (φ₁ : A →ₙ+* B) (φ₂ : B →ₙ+* C)

/-- **The two-step comparison for restrictions on a generator**: degreewise,
`e₁B ⊗_B (e₂C ⊗_C X) → Res φ₁ (Res φ₂ X)` sends `z₁ ⊗ (z₂ ⊗ x)` to `φ₂(z₁) z₂ x`. -/
theorem resTwoStep_val (X : DGModuleCat.{u} C) {p : ℤ} (z₁ : InDegreeZero (RCorner φ₁))
    (z₂ : InDegreeZero (RCorner φ₂)) (x : X) (hx : x ∈ grading p)
    (h : TensorProductOver.tmul C z₂ x ∈ gradingSubmodule B
      ((DGModuleCat.tensorFunctor B (InDegreeZero (RCorner φ₂))).obj X) p) :
    ((Res.val (φ := φ₂) (M := gradingSubmodule C X p) (Res.val (φ := φ₁)
      (((((resFunctor.{u, u} φ₁).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((CupCap.tensorComplexIsoOfIso (RCorner φ₂) (resOrdIso φ₂)).hom.app X)).f p ≫
        ((Functor.mapHomologicalComplexCompIso
          (Iso.refl (resFunctor.{u, u} φ₂ ⋙ resFunctor.{u, u} φ₁)) (ComplexShape.up ℤ)).hom.app
            ((complexFunctor C).obj X)).f p).hom
        (((resOrdIso φ₁).hom.app _).hom (TensorProductOver.tmul B z₁
          (show InDegreeZero (gradingSubmodule B
            ((DGModuleCat.tensorFunctor B (InDegreeZero (RCorner φ₂))).obj X) p) from
            ⟨TensorProductOver.tmul C z₂ x, h⟩)))))) : X) =
      (φ₂ (z₁ : RCorner φ₁).1 * (z₂ : RCorner φ₂).1) • x := by
  have e : ((z₁ : RCorner φ₁).1 • (⟨TensorProductOver.tmul C z₂ x, h⟩ : gradingSubmodule B
      ((DGModuleCat.tensorFunctor B (InDegreeZero (RCorner φ₂))).obj X) p)) =
      ⟨TensorProductOver.tmul C
        (show InDegreeZero (RCorner φ₂) from (z₁ : RCorner φ₁).1 • (z₂ : RCorner φ₂)) x,
        mem_gradingSubmodule.mpr (tmul_mem_grading_of_inDegreeZero (B := B) X _ hx)⟩ :=
    Subtype.ext rfl
  change ((Res.val (φ := φ₂) (M := gradingSubmodule C X p)
    ((((CupCap.tensorComplexIsoOfIso (RCorner φ₂) (resOrdIso φ₂)).hom.app X).f p).hom
      ((z₁ : RCorner φ₁).1 •
        (⟨TensorProductOver.tmul C z₂ x, h⟩ : gradingSubmodule B
      ((DGModuleCat.tensorFunctor B (InDegreeZero (RCorner φ₂))).obj X) p)))) : X) = _
  rw [e, tensorComplexIsoOfIso_hom_f_tmul _ _ _ _ _ hx]
  rfl

end ResTwo

end Generic

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (ν : Multiset I) (i : I)

set_option hygiene false in
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
set_option hygiene false in
local notation "νᵢᵢ" =>
  ((Singleton.singleton i : Multiset I) + ((Singleton.singleton i : Multiset I) + ν))
set_option hygiene false in
local notation "TA" μ:max => TensorProductAlgebra k Q Λ μ

/-- The generator `e'` of `e' T^λ_{ν+i}`, as an element of the degree-zero dg module. -/
def crossGen₁ : InDegreeZero (RCorner (appendBlackOp Q Λ i ν)) := RCorner.gen _

/-- `ψ φ(m) n` in `e' T^λ_{ν+2i}`, as an element of the degree-zero dg module. -/
def crossGen₂ (m : InDegreeZero (RCorner (appendBlackOp Q Λ i ν)))
    (n : InDegreeZero (RCorner (appendBlackOp Q Λ i νᵢ))) :
    InDegreeZero (RCorner (appendBlackOp Q Λ i νᵢ)) :=
  RCorner.twoStepElem (op (appendedCross Q Λ i ν)) (op_appendedCross_fix Q Λ i ν) m n

/-- `e' · ψ φ(m) n = ψ φ(m) n`. -/
theorem crossGen_mul (m : RCorner (appendBlackOp Q Λ i ν))
    (n : RCorner (appendBlackOp Q Λ i νᵢ)) :
    appendBlackOp Q Λ i νᵢ (crossGen₁ Q Λ ν i : RCorner (appendBlackOp Q Λ i ν)).1 *
        (crossGen₂ Q Λ ν i m n : RCorner (appendBlackOp Q Λ i νᵢ)).1 =
      op (appendedCross Q Λ i ν) * (appendBlackOp Q Λ i νᵢ m.1 * n.1) := by
  change appendBlackOp Q Λ i νᵢ (appendBlackOp Q Λ i ν 1) *
      (op (appendedCross Q Λ i ν) * appendBlackOp Q Λ i νᵢ m.1 * n.1) = _
  rw [← mul_assoc, ← mul_assoc, ← op_appendedCross_commute, mul_assoc (op _),
    mul_assoc (op _), ← map_mul,
    show appendBlackOp Q Λ i ν 1 * m.1 = m.1 from m.2]

/-- **Degreewise, the dg crossing is the crossing on `Eᵢ²`** (Webster, arXiv:1309.3796v3, §7.3):
under `CupCap.tensorComplexTwoStep`, `Stendhal.blackCrossTensorNat` is `blackCross` applied
degreewise. -/
theorem blackCrossTensorNat_degreewise (X : DGModuleCat.{0} (TA νᵢᵢ)ᵐᵒᵖ) :
    (complexFunctor (TA ν)ᵐᵒᵖ).map ((blackCrossTensorNat Q Λ ν i).app X) ≫
        (CupCap.tensorComplexTwoStep (RCorner (appendBlackOp Q Λ i ν))
          (RCorner (appendBlackOp Q Λ i νᵢ)) (resOrdIso (appendBlackOp Q Λ i ν))
          (resOrdIso (appendBlackOp Q Λ i νᵢ))).hom.app X =
      (CupCap.tensorComplexTwoStep (RCorner (appendBlackOp Q Λ i ν))
          (RCorner (appendBlackOp Q Λ i νᵢ)) (resOrdIso (appendBlackOp Q Λ i ν))
          (resOrdIso (appendBlackOp Q Λ i νᵢ))).hom.app X ≫
        (NatTrans.mapHomologicalComplex (blackCross Q Λ i ν) (ComplexShape.up ℤ)).app
          ((complexFunctor (TA νᵢᵢ)ᵐᵒᵖ).obj X) := by
  refine complexFunctor_tensorTwo_hom_ext _ _ X fun p m n x hx => ?_
  rw [CupCap.tensorComplexTwoStep_hom_app]
  simp only [Category.assoc, HomologicalComplex.comp_f]
  have hn : (n : InDegreeZero (RCorner (appendBlackOp Q Λ i νᵢ))) ∈ grading 0 :=
    (InDegreeZero.mem_grading_iff (M := RCorner (appendBlackOp Q Λ i νᵢ))).mpr (Or.inl rfl)
  have hnx : TensorProductOver.tmul (TA νᵢᵢ)ᵐᵒᵖ n x ∈ grading p := by
    simpa using TensorProductOver.tmul_mem_grading hn hx
  refine Eq.trans ?_ (hom_comp_apply_of_eq _ _
    (tensorComplexIsoOfIso_hom_f_tmul _ _ _ m _ hnx _)).symm
  have h1 : (((complexFunctor (TA ν)ᵐᵒᵖ).map ((blackCrossTensorNat Q Λ ν i).app X)).f p).hom
      ⟨TensorProductOver.tmul (TA νᵢ)ᵐᵒᵖ m (TensorProductOver.tmul (TA νᵢᵢ)ᵐᵒᵖ n x),
        mem_gradingSubmodule.mpr (tmul_tmul_mem_grading _ _ X m n hx)⟩ =
      ⟨TensorProductOver.tmul (TA νᵢ)ᵐᵒᵖ (crossGen₁ Q Λ ν i)
          (TensorProductOver.tmul (TA νᵢᵢ)ᵐᵒᵖ (crossGen₂ Q Λ ν i m n) x),
        mem_gradingSubmodule.mpr (tmul_tmul_mem_grading (RCorner (appendBlackOp Q Λ i ν))
          (RCorner (appendBlackOp Q Λ i νᵢ)) X (crossGen₁ Q Λ ν i) (crossGen₂ Q Λ ν i m n) hx)⟩ :=
    Subtype.ext rfl
  refine (hom_comp_apply_of_eq _ _ h1).trans ?_
  refine (hom_comp_apply_of_eq _ _ (tensorComplexIsoOfIso_hom_f_tmul _ _ _ _ _
    (tmul_mem_grading_of_inDegreeZero (B := (TA νᵢ)ᵐᵒᵖ) X (crossGen₂ Q Λ ν i m n) hx) _)).trans ?_
  refine Res.ext (Res.ext (Subtype.ext ?_))
  have hR := resTwoStep_val (appendBlackOp Q Λ i ν) (appendBlackOp Q Λ i νᵢ) X m n x hx
    (mem_gradingSubmodule.mpr (tmul_mem_grading_of_inDegreeZero (B := (TA νᵢ)ᵐᵒᵖ) X n hx))
  refine (resTwoStep_val _ _ X _ _ x hx _).trans ?_
  refine Eq.trans ?_ (Eq.trans (congrArg (fun y : X => op (appendedCross Q Λ i ν) • y) hR.symm) ?_)
  rotate_left
  · rfl
  exact (congrArg (· • x) (crossGen_mul Q Λ ν i m n)).trans (mul_smul _ _ _)

universe w w'

variable [DG.HasDerivedCategory.{w} (TA ν)ᵐᵒᵖ] [DG.HasDerivedCategory.{w} (TA νᵢ)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{w} (TA νᵢᵢ)ᵐᵒᵖ]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TA ν)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TA νᵢ)ᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} (TA νᵢᵢ)ᵐᵒᵖ)]

/-- **The crossing on the dg derived `𝔈_i²` is induced on dg modules by left multiplication by
the crossing** (Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21). -/
theorem dgBlackCross_QComp :
    Functor.whiskerLeft DG.DerivedCategory.Q
        (CupCap.dgBlackCross.{w, w'} (Q := Q) (Λ := Λ) ν i) ≫
        (QCompDerivedTensorTwoIso.{w} (A := (TA ν)ᵐᵒᵖ) (B := (TA νᵢ)ᵐᵒᵖ)
          (C := (TA νᵢᵢ)ᵐᵒᵖ) (RCorner (appendBlackOp Q Λ i ν))
          (RCorner (appendBlackOp Q Λ i νᵢ))).hom =
      (QCompDerivedTensorTwoIso.{w} (A := (TA ν)ᵐᵒᵖ) (B := (TA νᵢ)ᵐᵒᵖ)
          (C := (TA νᵢᵢ)ᵐᵒᵖ) (RCorner (appendBlackOp Q Λ i ν))
          (RCorner (appendBlackOp Q Λ i νᵢ))).hom ≫
        Functor.whiskerRight (blackCrossTensorNat Q Λ ν i) DG.DerivedCategory.Q :=
  CupCap.whiskerLeft_Q_comparisonConj_of_degreewise.{w, w'} _ _ (resOrdIso (appendBlackOp Q Λ i ν))
    (resOrdIso (appendBlackOp Q Λ i νᵢ)) (blackCrossTensorNat Q Λ ν i) (blackCross Q Λ i ν)
    (blackCrossTensorNat_degreewise Q Λ ν i)

/-- **The crossing on the dg derived `𝔈_i²` commutes with the derived tensor shift** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21): the hypothesis `hcross` of
`CupCap.capFQuantumTraceShiftIso_cross`, with no hypothesis. -/
instance dgBlackCross_commShift :
    NatTrans.CommShift (CupCap.dgBlackCross.{w, w'} (Q := Q) (Λ := Λ) ν i) ℤ :=
  dgBlackCross_commShift_of_QComp Q Λ ν i (dgBlackCross_QComp Q Λ ν i)

end Categorification.Stendhal

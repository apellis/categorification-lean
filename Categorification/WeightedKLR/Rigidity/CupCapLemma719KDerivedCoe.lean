/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KFlip
import Categorification.WeightedKLR.Rigidity.CupCapFunctor
import Categorification.WeightedKLR.RedStrands.BraidedAppendDerived
import Categorification.Algebra.DegreewiseTensor

/-!
# The coevaluation functor on derived categories of left modules

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
Definition 7.18 and Lemma 7.19 (K). The coevaluation functor `𝕂 = - ⊗ᴸ_{T^λ} K^{λ⁺}_λ`
(`coevaluationFunctor`) acts on the derived category of right `T^λ`-modules. Through the
horizontal reflections `σ` (`tensorFlipRingEquiv`) it becomes a functor on derived categories of
left modules, and this functor is the derived functor of the exact functor
`M ↦ K^σ ⊗_{T^λ} M` (`CoeTensor`):

* on modules, `K^{λ⁺}_λ ⊗_{(T^λ)ᵐᵒᵖ} M^σ`, read back along `σ`, is `K^σ ⊗_{T^λ} M`
  (`coeOrdIso`);
* `K^{λ⁺}_λ` is projective as a left `T^λ`-module, so the derived tensor product is computed
  degreewise without resolutions (`derivedTensorComparisonIso`), and
  `coevaluationFunctor` corresponds, under the comparison of derived categories of dg modules
  with Mathlib's derived categories of modules, to `(CoeTensor).mapDerivedCategory`
  (`coevaluationComparisonIso`).

## Main definitions

* `Stendhal.CupCap.coeTensorFunctor`: `M ↦ K^σ ⊗_{T^λ} M` on left modules.
* `Stendhal.CupCap.coeOrdIso`: its comparison with the ordinary right tensor product.
* `Stendhal.CupCap.coevaluationComparisonIso`: `coevaluationFunctor`, read on left modules
  through `σ`, is `coeTensorFunctor.mapDerivedCategory`.

Route hypotheses (only for the projectivity of `K^{λ⁺}_λ`, as in `projective_midCapBimodule`):
`hL`, `hQ`, `hκ`, `hP`, `hPL`, and `hfin`, `hproj` (the pieces `L e(t)` are finitely generated
projective over `k`). The reflection is taken over a field, as in Webster's paper.
-/

set_option backward.isDefEq.respectTransparency false

universe w w'

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory KLR KLRAlgebra TypeA MulOpposite DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} (j : ℕ) (hj : j ≤ ℓ)
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  (ν ν₀ : Multiset I)

set_option hygiene false in
local notation "T" => TensorProductAlgebra k Q Λ ν
set_option hygiene false in
local notation "Tp" => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
set_option hygiene false in
local notation "σ" => tensorFlipRingEquiv (Q := Q) (Λ := Λ) ν
set_option hygiene false in
local notation "σp" => tensorFlipRingEquiv (Q := Q) (Λ := plusLabels Λ Λc j hj) (ν + ν₀)
set_option hygiene false in
local notation "Cap" => CapBimodule k Q Λ Λc j hj ν ν₀ L

variable (L : Type) [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

/-! ### The reflected coevaluation functor on left modules -/

/-- **The reflected coevaluation functor** `M ↦ K^σ ⊗_{T^λ} M` on left modules. -/
def coeTensorFunctor : ModuleCat.{0} T ⥤ ModuleCat.{0} Tp where
  obj X := ModuleCat.of Tp (CoeTensor j hj Q Λ Λc ν ν₀ L X)
  map g := ModuleCat.ofHom (coeTensorMap g.hom)
  map_id _ := ModuleCat.hom_ext coeTensorMap_id
  map_comp f g := ModuleCat.hom_ext (coeTensorMap_comp f.hom g.hom)

instance : (coeTensorFunctor j hj Q Λ Λc ν ν₀ L).Additive where
  map_add {_ _ f g} := ModuleCat.hom_ext (BalancedTensor.extB fun z m =>
    BalancedTensor.tmul_add z (f.hom m) (g.hom m))

/-! ### Comparison with the ordinary right tensor product -/

set_option hygiene false in
local notation "OrdK" => ordTensor Tpᵐᵒᵖ Tᵐᵒᵖ (OpBimodule T Cap)

set_option hygiene false in
local notation "Rσ" => ModuleCat.restrictScalars.{0} ((σ).symm : Tᵐᵒᵖ →+* T)

set_option hygiene false in
local notation "Rσp" => ModuleCat.restrictScalars.{0} (σp : Tp →+* Tpᵐᵒᵖ)

variable {j hj Q Λ Λc ν ν₀ L}

theorem tensorFlip_symm_op_symm (b : Tᵐᵒᵖ) : (σ).symm (op ((σ).symm b)) = unop b :=
  tensorFlip_tensorFlip _

variable (X : ModuleCat.{0} T)

/-- The bilinear map `c, x ↦ c ⊗ x` from the right to the reflected tensor product. -/
def coeOrdBil :
    InDegreeZero (OpBimodule T Cap) →+ InDegreeZero ((Rσ).obj X) →+
      CoeTensor j hj Q Λ Λc ν ν₀ L X :=
  AddMonoidHom.mk' (fun c => AddMonoidHom.mk'
      (fun x => BalancedTensor.tmul (toReflectedCap (c : Cap)) (x : X))
      (fun x y => BalancedTensor.tmul_add _ (x : X) (y : X)))
    (fun c c' => AddMonoidHom.ext fun x => BalancedTensor.add_tmul
      (toReflectedCap (c : Cap)) (toReflectedCap (c' : Cap)) (x : X))

theorem coeOrdBil_balanced (b : Tᵐᵒᵖ) (c : InDegreeZero (OpBimodule T Cap))
    (x : InDegreeZero ((Rσ).obj X)) :
    coeOrdBil X (op b • c) x = coeOrdBil X c (b • x) := by
  have h := BalancedTensor.op_smul_tmul (k := ℤ) (B := Tp) (toReflectedCap (c : Cap))
    ((σ).symm b) (x : X)
  rw [op_smul_toReflectedCap, tensorFlip_symm_op_symm] at h
  exact h

/-- `K^{λ⁺}_λ ⊗_{(T^λ)ᵐᵒᵖ} M^σ → K^σ ⊗_{T^λ} M`, `c ⊗ x ↦ c ⊗ x`. -/
def coeOrdFwd : (OrdK).obj ((Rσ).obj X) →+ CoeTensor j hj Q Λ Λc ν ν₀ L X :=
  DG.TensorProductOver.lift (coeOrdBil X) (coeOrdBil_balanced X)

/-- `K^σ ⊗_{T^λ} M → K^{λ⁺}_λ ⊗_{(T^λ)ᵐᵒᵖ} M^σ`, `c ⊗ x ↦ c ⊗ x`. -/
def coeOrdBwd : CoeTensor j hj Q Λ Λc ν ν₀ L X →+ (OrdK).obj ((Rσ).obj X) :=
  (BalancedTensor.lift (k := ℤ) (B := Tp)
    (AddMonoidHom.toIntLinearMap (AddMonoidHom.mk'
      (fun c : ReflectedCap j hj Q Λ Λc ν ν₀ L => (AddMonoidHom.mk'
        (fun x : X => DG.TensorProductOver.tmul (M := InDegreeZero (OpBimodule T Cap))
          (N := InDegreeZero ((Rσ).obj X)) Tᵐᵒᵖ
          (ofReflectedCap c : InDegreeZero (OpBimodule T Cap))
          (x : InDegreeZero ((Rσ).obj X)))
        (fun _ _ => DG.TensorProductOver.tmul_add (A := Tᵐᵒᵖ) _ _ _)).toIntLinearMap)
      (fun _ _ => LinearMap.ext fun _ => DG.TensorProductOver.add_tmul (A := Tᵐᵒᵖ) _ _ _)))
    (fun c t x => (DG.TensorProductOver.op_smul_tmul (A := Tᵐᵒᵖ)
      (M := InDegreeZero (OpBimodule T Cap)) (N := InDegreeZero ((Rσ).obj X)) ((σ) t)
      (ofReflectedCap c : InDegreeZero (OpBimodule T Cap))
      (x : InDegreeZero ((Rσ).obj X))).trans
        (congrArg (DG.TensorProductOver.tmul (M := InDegreeZero (OpBimodule T Cap))
          (N := InDegreeZero ((Rσ).obj X)) Tᵐᵒᵖ (ofReflectedCap c))
          (congrArg (· • (x : X)) ((σ).symm_apply_apply t))))).toAddMonoidHom

theorem coeOrdBwd_fwd (t : (OrdK).obj ((Rσ).obj X)) : coeOrdBwd X (coeOrdFwd X t) = t :=
  DFunLike.congr_fun (DG.TensorProductOver.addHom_ext (f := (coeOrdBwd X).comp (coeOrdFwd X))
    (g := AddMonoidHom.id _) fun _ _ => rfl) t

theorem coeOrdFwd_bwd (t : CoeTensor j hj Q Λ Λc ν ν₀ L X) : coeOrdFwd X (coeOrdBwd X t) = t := by
  induction t using BalancedTensor.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul c x => rfl
  | add t t' ht ht' => rw [map_add, map_add, ht, ht']

theorem coeOrdFwd_smul (s : Tp) (t : (Rσp).obj ((OrdK).obj ((Rσ).obj X))) :
    coeOrdFwd X (s • t) = s • coeOrdFwd X t := by
  induction t using DG.TensorProductOver.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul c x => exact (BalancedTensor.smul_tmul' s _ _).symm
  | add t t' ht ht' => rw [smul_add, map_add, map_add, ht, ht', smul_add]

/-- **`K^{λ⁺}_λ ⊗_{(T^λ)ᵐᵒᵖ} M^σ`, read along `σ`, is `K^σ ⊗_{T^λ} M`.** -/
def coeOrdEquiv :
    (Rσp).obj ((OrdK).obj ((Rσ).obj X)) ≃ₗ[Tp] CoeTensor j hj Q Λ Λc ν ν₀ L X where
  toFun := coeOrdFwd X
  invFun := coeOrdBwd X
  map_add' := map_add _
  map_smul' := coeOrdFwd_smul X
  left_inv := coeOrdBwd_fwd X
  right_inv := coeOrdFwd_bwd X

variable (j hj Q Λ Λc ν ν₀ L) in
/-- **The coevaluation functor on modules, read on left modules through `σ`, is the reflected
coevaluation functor** `M ↦ K^σ ⊗_{T^λ} M`, naturally in `M`. -/
def coeOrdIso : Rσ ⋙ OrdK ⋙ Rσp ≅ coeTensorFunctor j hj Q Λ Λc ν ν₀ L :=
  NatIso.ofComponents (fun X => (coeOrdEquiv X).toModuleIso) fun _ =>
    ModuleCat.hom_ext (LinearMap.toAddMonoidHom_injective
      (DG.TensorProductOver.addHom_ext fun _ _ => rfl))

/-! ### Exactness -/

section Exact

variable (j hj Q Λ Λc ν ν₀ L)

variable [Module.Projective Tᵐᵒᵖ (ReflectedCap j hj Q Λ Λc ν ν₀ L)]

instance coeTensorFunctor_preservesHomology :
    (coeTensorFunctor j hj Q Λ Λc ν ν₀ L).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ fun S hS => by
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
    exact coeTensorMap_exact hS

instance : Limits.PreservesFiniteLimits (coeTensorFunctor j hj Q Λ Λc ν ν₀ L) :=
  Functor.preservesFiniteLimits_of_preservesHomology _

instance : Limits.PreservesFiniteColimits (coeTensorFunctor j hj Q Λ Λc ν ν₀ L) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

end Exact

/-! ### The coevaluation functor on derived categories of left modules -/

section Derived

attribute [local instance] OpBimodule.projective_opOp

variable (j hj Q Λ Λc ν ν₀ L)
variable [DG.HasDerivedCategory.{w, 0} Tᵐᵒᵖ] [DG.HasDerivedCategory.{w, 0} Tpᵐᵒᵖ]
  [HasDerivedCategory.{w'} (ModuleCat.{0} T)] [HasDerivedCategory.{w'} (ModuleCat.{0} Tᵐᵒᵖ)]
  [HasDerivedCategory.{w'} (ModuleCat.{0} Tp)] [HasDerivedCategory.{w'} (ModuleCat.{0} Tpᵐᵒᵖ)]

set_option hygiene false in
local notation "Coev" => coevaluationFunctor.{0, w} k Q Λ Λc j hj ν ν₀ L

/-- **The coevaluation functor on derived categories of left modules**: `𝕂` read through the
comparison of derived categories of dg modules with Mathlib's derived categories of modules,
and through the horizontal reflections `σ` on both sides. -/
def leftCoevaluationFunctor :
    DerivedCategory (ModuleCat.{0} T) ⥤ DerivedCategory (ModuleCat.{0} Tp) :=
  (Rσ).mapDerivedCategory ⋙ (derivedComparisonEquivalence.{w, w'} Tᵐᵒᵖ).inverse ⋙ Coev ⋙
    derivedComparison.{w, w'} Tpᵐᵒᵖ ⋙ (Rσp).mapDerivedCategory

/-- For `K^{λ⁺}_λ` projective as a left `T^λ`-module, `𝕂` on Mathlib's derived categories of
right modules is the derived functor of the ordinary tensor product with `K^{λ⁺}_λ`. -/
def coevaluationOrdIso [Module.Projective T Cap] :
    (derivedComparisonEquivalence.{w, w'} Tᵐᵒᵖ).inverse ⋙ Coev ⋙
        derivedComparison.{w, w'} Tpᵐᵒᵖ ≅ (OrdK).mapDerivedCategory :=
  Functor.isoWhiskerLeft _ (derivedTensorComparisonIso Tpᵐᵒᵖ Tᵐᵒᵖ (OpBimodule T Cap)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (derivedComparisonEquivalence.{w, w'} Tᵐᵒᵖ).counitIso _ ≪≫
    Functor.leftUnitor _

/-- **`𝕂`, on derived categories of left modules, is the derived functor of the exact functor
`M ↦ K^σ ⊗_{T^λ} M`** (Webster, arXiv:1309.3796v3, Definition 7.18, read through the horizontal
reflections), for `K^{λ⁺}_λ` projective as a left `T^λ`-module. -/
def leftCoevaluationIsoOfProjective [Module.Projective T Cap]
    [Module.Projective Tᵐᵒᵖ (ReflectedCap j hj Q Λ Λc ν ν₀ L)] :
    leftCoevaluationFunctor j hj Q Λ Λc ν ν₀ L ≅
      (coeTensorFunctor j hj Q Λ Λc ν ν₀ L).mapDerivedCategory :=
  Functor.isoWhiskerLeft (Rσ).mapDerivedCategory
      (Functor.isoWhiskerRight (coevaluationOrdIso j hj Q Λ Λc ν ν₀ L)
        (Rσp).mapDerivedCategory) ≪≫
    Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso _ _) ≪≫
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
    mapDerivedCategoryIsoOfIso (coeOrdIso j hj Q Λ Λc ν ν₀ L)

/-- **`𝕂` on derived categories of left modules is the derived functor of
`M ↦ K^σ ⊗_{T^λ} M`** (Webster, arXiv:1309.3796v3, Definition 7.18, read through the horizontal
reflections).

Route hypotheses (beyond Webster's setting), used only for the projectivity of `K^{λ⁺}_λ` as a
left `T^λ`-module (`projective_midCapBimodule`): `hL` (violated idempotents act by zero on `L`),
`hQ` (symmetric `Q`), `hκ` (the cup scalars are units), `hP`, `hPL` (the pull-off identities),
`hfin` and `hproj` (the pieces `L e(t)` are finitely generated projective `k`-modules). -/
def leftCoevaluationIso [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (hQ : KLRSymm Q) (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i)) (hP : PullOff k Q Λc ν₀ L)
    (hPL : PullOffLeft k Q Λc ν₀ L)
    (hfin : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Finite k
      (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht))))
    (hproj : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Projective k
      (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht)))) :
    have := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := ν) hL hQ hκ hP hPL hfin
      hproj
    have := projective_reflectedCap (j := j) (hj := hj) (Λ := Λ) (ν := ν) hL hQ hκ hP hPL hfin
      hproj
    leftCoevaluationFunctor j hj Q Λ Λc ν ν₀ L ≅
      (coeTensorFunctor j hj Q Λ Λc ν ν₀ L).mapDerivedCategory :=
  have := projective_midCapBimodule (j := j) (hj := hj) (Λ := Λ) (ν := ν) hL hQ hκ hP hPL hfin
    hproj
  have := projective_reflectedCap (j := j) (hj := hj) (Λ := Λ) (ν := ν) hL hQ hκ hP hPL hfin
    hproj
  leftCoevaluationIsoOfProjective j hj Q Λ Λc ν ν₀ L

end Derived

end Categorification.Stendhal.CupCap

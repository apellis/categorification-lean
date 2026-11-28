/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.ExactDerivedTensor
import Categorification.Algebra.DerivedTensorFiltration
import Categorification.Algebra.ProjectiveFlat
import DG.Derived.ComparisonRing

/-!
# The tensor product with an ordinary bimodule is computed degreewise

For rings `A`, `B` (dg rings in degree `0`) and an `(A, B)`-bimodule `M`, the tensor product
`M ⊗_B X` of a dg `B`-module `X` is, on underlying cochain complexes, the ordinary functor
`M ⊗_B -` applied degreewise: `(M ⊗_B X)ⁿ = M ⊗_B Xⁿ`, since `X` is the direct sum of its
components (`tensorComplexSumIso`, `tensorFunctorCompComplexIso`).

This is the input for comparing the derived tensor products of B. Webster, *Knot invariants and
higher representation theory*, arXiv:1309.3796v3, with the functors induced on derived categories
by exact functors of modules (Definition 7.18 and Lemma 7.19 (K): the coevaluation functor
`𝕂 = - ⊗ᴸ K^{λ⁺}_λ` against the standardization functors, which are exact).

## Main definitions

* `Categorification.dgUnderlying A`: the underlying module of a dg module.
* `Categorification.ordTensor A B M`: the ordinary functor `M ⊗_B - : ModuleCat B ⥤ ModuleCat A`.
* `Categorification.tensorComplexSumIso`: `M ⊗_B (⨁ₙ Kⁿ) ≅ ⨁ₙ (M ⊗_B Kⁿ)`, naturally in `K`.
* `Categorification.tensorFunctorCompComplexIso`: the underlying complex of `M ⊗_B X` is
  `M ⊗_B -` applied degreewise to the underlying complex of `X`.

## Main results

* `Categorification.ordTensor_exact`: `M ⊗_B -` is exact for `M` projective over `Bᵐᵒᵖ`.
* `Categorification.derivedTensorComparisonIso`: for such `M`, `M ⊗ᴸ_B -` corresponds, under
  `DG.DegreeZero.derivedComparison`, to `(M ⊗_B -).mapDerivedCategory`.
-/

open CategoryTheory DG DG.DegreeZero MulOpposite

universe w w' u

noncomputable section

namespace Categorification

/-- **The underlying module of a dg module** over a ring in degree `0`. -/
def dgUnderlying (A : Type u) [Ring A] : DGModuleCat.{u} A ⥤ ModuleCat.{u} A where
  obj X := ModuleCat.of A X
  map f := ModuleCat.ofHom f.hom.toLinearMap
  map_id _ := rfl
  map_comp _ _ := rfl

instance (A : Type u) [Ring A] : (dgUnderlying A).Additive where
  map_add := rfl

variable (A B : Type u) [Ring A] [Ring B] (M : Type u) [AddCommGroup M] [Module A M]
  [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]

/-- A map of `B`-modules, as a map of the modules concentrated in degree `0`. -/
def idzHom {N N' : ModuleCat.{u} B} (g : N ⟶ N') : InDegreeZero N →ₗ[B] InDegreeZero N' where
  toFun x := g.hom x
  map_add' := map_add g.hom
  map_smul' := map_smul g.hom

/-- `M ⊗_B g` for a map `g` of `B`-modules, linearly over `A`. -/
def ordTensorMap {N N' : ModuleCat.{u} B} (g : N ⟶ N') :
    TensorProductOver B (InDegreeZero M) (InDegreeZero N) →ₗ[A]
      TensorProductOver B (InDegreeZero M) (InDegreeZero N') where
  toFun := TensorProductOver.map (LinearMap.id : InDegreeZero M →ₗ[Bᵐᵒᵖ] InDegreeZero M)
    (idzHom B g)
  map_add' := map_add _
  map_smul' a t := by
    induction t using TensorProductOver.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | tmul m n => rfl
    | add t t' ht ht' => rw [smul_add, map_add, map_add, ht, ht', smul_add]

/-- **The ordinary tensor product** `M ⊗_B - : ModuleCat B ⥤ ModuleCat A` with an
`(A, B)`-bimodule `M`. -/
def ordTensor : ModuleCat.{u} B ⥤ ModuleCat.{u} A where
  obj N := ModuleCat.of A (TensorProductOver B (InDegreeZero M) (InDegreeZero N))
  map g := ModuleCat.ofHom (ordTensorMap A B M g)
  map_id _ := ModuleCat.hom_ext (LinearMap.toAddMonoidHom_injective
    (TensorProductOver.addHom_ext fun _ _ => rfl))
  map_comp _ _ := ModuleCat.hom_ext (LinearMap.toAddMonoidHom_injective
    (TensorProductOver.addHom_ext fun _ _ => rfl))

variable {A B M}

theorem ordTensor_map_tmul {N N' : ModuleCat.{u} B} (g : N ⟶ N') (m : InDegreeZero M)
    (n : InDegreeZero N) :
    ((ordTensor A B M).map g).hom (TensorProductOver.tmul B m n) =
      TensorProductOver.tmul B m (g.hom n : InDegreeZero N') := rfl

instance : (ordTensor A B M).Additive where
  map_add {_ N' f g} := ModuleCat.hom_ext (LinearMap.toAddMonoidHom_injective
    (TensorProductOver.addHom_ext fun m n =>
      TensorProductOver.tmul_add (A := B) m (f.hom n : InDegreeZero N')
        (g.hom n : InDegreeZero N')))

/-! ### Exactness for a projective right module -/

section Exact

variable [Module.Projective Bᵐᵒᵖ M]

/-- **`M ⊗_B -` is exact for `M` projective as a right `B`-module**: write `M` as a retract of
a free module and use the coordinates `M ⊗_B V → (M →₀ V)`. -/
theorem ordTensor_exact {U V W : ModuleCat.{u} B} (f : U ⟶ V) (g : V ⟶ W)
    (h : Function.Exact f.hom g.hom) :
    Function.Exact ((ordTensor A B M).map f).hom ((ordTensor A B M).map g).hom := by
  classical
  obtain ⟨s, hs⟩ := Module.Projective.out (R := Bᵐᵒᵖ) (P := M)
  intro t
  constructor
  · intro ht
    let c := InDegreeZero.coord s t
    have hc : ∀ p, ∃ u : U, f.hom u = c p := fun p => (h (c p)).mp (by
      have h1 := InDegreeZero.coord_map s (idzHom B g) t p
      have h2 : TensorProductOver.map LinearMap.id (idzHom B g) t = 0 := ht
      rw [h2, map_zero] at h1
      exact h1.symm)
    choose u hu using hc
    refine ⟨∑ p ∈ c.support, TensorProductOver.tmul B (p : InDegreeZero M)
      (u p : InDegreeZero U), ?_⟩
    have h3 : InDegreeZero.recomb c = t := InDegreeZero.recomb_coord s hs t
    refine (map_sum (ordTensorMap A B M f) _ _).trans (Eq.trans ?_ h3)
    refine Finset.sum_congr rfl fun p _ => ?_
    exact congrArg (TensorProductOver.tmul B (p : InDegreeZero M)) (hu p)
  · rintro ⟨u, rfl⟩
    have hfg : f ≫ g = 0 := ModuleCat.hom_ext (LinearMap.ext fun x => h.apply_apply_eq_zero x)
    change ((ordTensor A B M).map f ≫ (ordTensor A B M).map g).hom u = 0
    rw [← Functor.map_comp, hfg, Functor.map_zero]
    rfl

instance ordTensor_preservesHomology : (ordTensor A B M).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ fun S hS => by
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
    exact ordTensor_exact S.f S.g hS

instance : Limits.PreservesFiniteLimits (ordTensor A B M) :=
  Functor.preservesFiniteLimits_of_preservesHomology _

instance : Limits.PreservesFiniteColimits (ordTensor A B M) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

end Exact

section ComplexSum

variable (K : CochainComplex (ModuleCat.{u} B) ℤ)

set_option hygiene false in
local notation "GK" => (ordTensor A B M).mapHomologicalComplex (ComplexShape.up ℤ) |>.obj K

/-- The bilinear map `m, z ↦ ∑ₙ m ⊗ zₙ` defining `M ⊗_B (⨁ₙ Kⁿ) → ⨁ₙ (M ⊗_B Kⁿ)`. -/
def tensorComplexSumBil : InDegreeZero M →+ ComplexSum K →+ ComplexSum GK :=
  (show ComplexSum K →+ InDegreeZero M →+ ComplexSum GK from
    DirectSum.toAddMonoid (β := fun n => K.X n) fun n =>
      (AddMonoidHom.compHom (ComplexSum.of GK n).toAddMonoidHom).comp
        (TensorProductOver.tmulAddHom B (InDegreeZero M) (InDegreeZero (K.X n))).flip).flip

theorem tensorComplexSumBil_of (m : InDegreeZero M) (n : ℤ) (x : K.X n) :
    tensorComplexSumBil (A := A) K m (ComplexSum.of K n x) =
      ComplexSum.of GK n (TensorProductOver.tmul B m (x : InDegreeZero (K.X n))) :=
  by
  change (DirectSum.toAddMonoid (β := fun n => K.X n) (fun n =>
    (AddMonoidHom.compHom (ComplexSum.of GK n).toAddMonoidHom).comp
      (TensorProductOver.tmulAddHom B (InDegreeZero M) (InDegreeZero (K.X n))).flip)
    (DirectSum.of (fun n => K.X n) n x)) m = _
  rw [DirectSum.toAddMonoid_of]
  rfl

theorem tensorComplexSumBil_balanced (b : B) (m : InDegreeZero M) (z : ComplexSum K) :
    tensorComplexSumBil (A := A) K (op b • m) z = tensorComplexSumBil (A := A) K m (b • z) := by
  induction z using ComplexSum.induction_on with
  | zero => rw [smul_zero, map_zero, map_zero]
  | of n x =>
    rw [← map_smul, tensorComplexSumBil_of, tensorComplexSumBil_of]
    exact congrArg (ComplexSum.of GK n)
      (TensorProductOver.op_smul_tmul (A := B) b m (x : InDegreeZero (K.X n)))
  | add z z' hz hz' => rw [smul_add, map_add, map_add, hz, hz']

/-- `M ⊗_B (⨁ₙ Kⁿ) → ⨁ₙ (M ⊗_B Kⁿ)`, `m ⊗ z ↦ ∑ₙ m ⊗ zₙ`. -/
def tensorComplexSumFwd :
    TensorProductOver B (InDegreeZero M) (ComplexSum K) →+ ComplexSum GK :=
  TensorProductOver.lift (tensorComplexSumBil (A := A) K) (tensorComplexSumBil_balanced K)

theorem tensorComplexSumFwd_tmul_of (m : InDegreeZero M) (n : ℤ) (x : K.X n) :
    tensorComplexSumFwd (A := A) K (TensorProductOver.tmul B m (ComplexSum.of K n x)) =
      ComplexSum.of GK n (TensorProductOver.tmul B m (x : InDegreeZero (K.X n))) :=
  tensorComplexSumBil_of K m n x

/-- `⨁ₙ (M ⊗_B Kⁿ) → M ⊗_B (⨁ₙ Kⁿ)`, the sum of the maps `M ⊗_B Kⁿ → M ⊗_B (⨁ₙ Kⁿ)`. -/
def tensorComplexSumBwd :
    ComplexSum GK →+ TensorProductOver B (InDegreeZero M) (ComplexSum K) :=
  DirectSum.toAddMonoid (β := fun n => (GK).X n) fun n =>
    TensorProductOver.map (LinearMap.id : InDegreeZero M →ₗ[Bᵐᵒᵖ] InDegreeZero M)
      (ComplexSum.of K n : InDegreeZero (K.X n) →ₗ[B] ComplexSum K)

theorem tensorComplexSumBwd_of_tmul (m : InDegreeZero M) (n : ℤ) (x : K.X n) :
    tensorComplexSumBwd (A := A) K
        (ComplexSum.of GK n (TensorProductOver.tmul B m (x : InDegreeZero (K.X n)))) =
      TensorProductOver.tmul B m (ComplexSum.of K n x) :=
  DirectSum.toAddMonoid_of (β := fun n => (GK).X n) _ n _

theorem tensorComplexSumBwd_fwd (t : TensorProductOver B (InDegreeZero M) (ComplexSum K)) :
    tensorComplexSumBwd (A := A) K (tensorComplexSumFwd K t) = t := by
  induction t using TensorProductOver.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul m z =>
    induction z using ComplexSum.induction_on with
    | zero => rw [TensorProductOver.tmul_zero, map_zero, map_zero]
    | of n x => rw [tensorComplexSumFwd_tmul_of, tensorComplexSumBwd_of_tmul]
    | add z z' hz hz' => rw [TensorProductOver.tmul_add, map_add, map_add, hz, hz']
  | add t t' ht ht' => rw [map_add, map_add, ht, ht']

theorem tensorComplexSumFwd_bwd_of (n : ℤ)
    (y : TensorProductOver B (InDegreeZero M) (InDegreeZero (K.X n))) :
    tensorComplexSumFwd K (tensorComplexSumBwd (A := A) K (ComplexSum.of GK n y)) =
      ComplexSum.of GK n y := by
  let φ : TensorProductOver B (InDegreeZero M) (InDegreeZero (K.X n)) →+ ComplexSum GK :=
    (ComplexSum.of GK n).toAddMonoidHom
  have h : (tensorComplexSumFwd K).comp ((tensorComplexSumBwd (A := A) K).comp φ) = φ :=
    TensorProductOver.addHom_ext fun m x =>
      (congrArg (tensorComplexSumFwd K) (tensorComplexSumBwd_of_tmul K m n x)).trans
        (tensorComplexSumFwd_tmul_of K m n x)
  exact DFunLike.congr_fun h y

theorem tensorComplexSumFwd_bwd (z : ComplexSum GK) :
    tensorComplexSumFwd K (tensorComplexSumBwd (A := A) K z) = z := by
  induction z using ComplexSum.induction_on with
  | zero => rw [map_zero, map_zero]
  | of n y => exact tensorComplexSumFwd_bwd_of K n y
  | add z z' hz hz' => rw [map_add, map_add, hz, hz']

theorem tensorComplexSumFwd_smul (a : A)
    (t : TensorProductOver B (InDegreeZero M) (ComplexSum K)) :
    tensorComplexSumFwd (A := A) K (a • t) = a • tensorComplexSumFwd K t := by
  induction t using TensorProductOver.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul m z =>
    induction z using ComplexSum.induction_on with
    | zero => rw [TensorProductOver.tmul_zero, smul_zero, map_zero, smul_zero]
    | of n x =>
      rw [TensorProductOver.smul_tmul, tensorComplexSumFwd_tmul_of, tensorComplexSumFwd_tmul_of]
      exact map_smul (ComplexSum.of GK n) a
        (TensorProductOver.tmul B m (x : InDegreeZero (K.X n)))
    | add z z' hz hz' =>
      rw [TensorProductOver.tmul_add, smul_add, map_add, map_add, hz, hz', smul_add]
  | add t t' ht ht' => rw [smul_add, map_add, map_add, ht, ht', smul_add]

theorem tensorComplexSumFwd_mem {k : ℤ} {t : TensorProductOver B (InDegreeZero M) (ComplexSum K)}
    (ht : t ∈ grading k) : tensorComplexSumFwd K t ∈ grading (M := ComplexSum GK) k := by
  refine TensorProductOver.induction_on_mem_grading
    (P := fun t => tensorComplexSumFwd (A := A) K t ∈ grading (M := ComplexSum GK) k)
    ?_ ?_ ?_ ?_ ht
  · rw [map_zero]; exact zero_mem _
  · intro i j m z hm hz hij
    obtain ⟨x, rfl⟩ := ComplexSum.mem_grading_iff.mp hz
    rw [InDegreeZero.mem_grading_iff] at hm
    rcases hm with rfl | rfl
    · rw [tensorComplexSumFwd_tmul_of, ← hij, zero_add]
      exact ComplexSum.of_mem_grading _ _
    · rw [TensorProductOver.zero_tmul, map_zero]; exact zero_mem _
  · intro x y hx hy; rw [map_add]; exact add_mem hx hy
  · intro x hx; rw [map_neg]; exact neg_mem hx

theorem tensorComplexSumFwd_d (t : TensorProductOver B (InDegreeZero M) (ComplexSum K)) :
    tensorComplexSumFwd K (d t) = d (tensorComplexSumFwd (A := A) K t) := by
  induction t using TensorProductOver.induction_on with
  | zero => rw [d_zero, map_zero, d_zero]
  | tmul m z =>
    have hm : m ∈ grading (M := InDegreeZero M) 0 := by
      rw [InDegreeZero.mem_grading_iff]; exact Or.inl rfl
    rw [TensorProductOver.d_tmul_of_mem hm, InDegreeZero.d_apply, TensorProductOver.zero_tmul,
      zero_add, koszulSign_zero, one_smul]
    induction z using ComplexSum.induction_on with
    | zero => rw [d_zero, TensorProductOver.tmul_zero, map_zero, d_zero]
    | of n x =>
      rw [ComplexSum.d_of, tensorComplexSumFwd_tmul_of, tensorComplexSumFwd_tmul_of]
      exact (ComplexSum.d_of (K := GK) n
        (TensorProductOver.tmul B m (x : InDegreeZero (K.X n)))).symm
    | add z z' hz hz' =>
      rw [d_add, TensorProductOver.tmul_add, map_add, hz, hz', TensorProductOver.tmul_add,
        map_add, d_add]
  | add t t' ht ht' => rw [d_add, map_add, map_add, ht, ht', d_add]

/-- **`M ⊗_B (⨁ₙ Kⁿ) ≅ ⨁ₙ (M ⊗_B Kⁿ)`** as dg `A`-modules. -/
def tensorComplexSumEquiv :
    TensorProductOver B (InDegreeZero M) (ComplexSum K) ≃ᵈᵍ[A] ComplexSum GK where
  toFun := tensorComplexSumFwd K
  invFun := tensorComplexSumBwd K
  map_add' := map_add _
  map_smul' := tensorComplexSumFwd_smul K
  left_inv := tensorComplexSumBwd_fwd K
  right_inv := tensorComplexSumFwd_bwd K
  map_mem' := tensorComplexSumFwd_mem K
  map_d' := tensorComplexSumFwd_d K

end ComplexSum

variable (A M) in
/-- **`M ⊗_B (⨁ₙ Kⁿ) ≅ ⨁ₙ (M ⊗_B Kⁿ)`, naturally in the complex `K`.** -/
def tensorComplexSumIso :
    DGModuleCat.ofComplex B ⋙ DGModuleCat.tensorFunctor A (InDegreeZero M) ≅
      (ordTensor A B M).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DGModuleCat.ofComplex A :=
  NatIso.ofComponents (fun K => DGModuleCat.isoOfDGModuleEquiv (tensorComplexSumEquiv K))
    fun {K L} φ => DGModuleCat.tensor_hom_ext fun m z => by
      change tensorComplexSumFwd L (TensorProductOver.tmul B m (ComplexSum.map φ z)) =
        ComplexSum.map ((ordTensor A B M).mapHomologicalComplex _ |>.map φ)
          (tensorComplexSumFwd K (TensorProductOver.tmul B m z))
      induction z using ComplexSum.induction_on with
      | zero => rw [map_zero, TensorProductOver.tmul_zero, TensorProductOver.tmul_zero,
          map_zero, map_zero, map_zero]
      | of n x =>
        rw [ComplexSum.map_of, tensorComplexSumFwd_tmul_of, tensorComplexSumFwd_tmul_of]
        erw [ComplexSum.map_of]
        rfl
      | add z z' hz hz' => rw [map_add, TensorProductOver.tmul_add, TensorProductOver.tmul_add,
          map_add, map_add, map_add, hz, hz']

variable (A M) in
/-- **The underlying complex of `M ⊗_B X` is `M ⊗_B -` applied degreewise** to the underlying
complex of the dg module `X`, naturally in `X`. -/
def tensorFunctorCompComplexIso :
    DGModuleCat.tensorFunctor A (InDegreeZero M) ⋙ complexFunctor A ≅
      complexFunctor B ⋙ (ordTensor A B M).mapHomologicalComplex (ComplexShape.up ℤ) :=
  Functor.isoWhiskerRight (Functor.leftUnitor _).symm _ ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight (complexEquivalence B).unitIso _) _ ≪≫
    Functor.isoWhiskerRight (Functor.associator _ _ _) _ ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft (complexFunctor B)
      (tensorComplexSumIso A M)) _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ (ofComplexCompIso A)) ≪≫
    Functor.isoWhiskerLeft _ (Functor.rightUnitor _)

/-! ### The derived tensor product and the derived functor of `M ⊗_B -` -/

section Derived

variable (A B M) [Module.Projective Bᵐᵒᵖ M] [HasDerivedCategory.{w, u} A]
  [HasDerivedCategory.{w, u} B] [_root_.HasDerivedCategory.{w'} (ModuleCat.{u} A)]
  [_root_.HasDerivedCategory.{w'} (ModuleCat.{u} B)]

/-- On dg modules, `M ⊗ᴸ_B -` followed by the comparison with Mathlib's derived category is the
comparison followed by the derived functor of the exact functor `M ⊗_B -`. -/
def QCompDerivedTensorComparisonIso :
    DG.DerivedCategory.Q ⋙ derivedTensor.{w} A B M ⋙ derivedComparison.{w, w'} A ≅
      DG.DerivedCategory.Q ⋙ derivedComparison.{w, w'} B ⋙
        (ordTensor A B M).mapDerivedCategory :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (QCompDerivedTensorIso A B M) _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (QCompDerivedComparisonIso A) ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (tensorFunctorCompComplexIso A M) _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (ordTensor A B M).mapDerivedCategoryFactors.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (QCompDerivedComparisonIso B).symm _ ≪≫ Functor.associator _ _ _

/-- **`M ⊗ᴸ_B -` is the derived functor of the exact functor `M ⊗_B -`** for `M` projective as
a right `B`-module, under the comparison of the derived category of dg modules over a ring with
Mathlib's derived category of modules. -/
def derivedTensorComparisonIso :
    derivedTensor.{w} A B M ⋙ derivedComparison.{w, w'} A ≅
      derivedComparison.{w, w'} B ⋙ (ordTensor A B M).mapDerivedCategory :=
  (Localization.whiskeringLeftFunctor' DG.DerivedCategory.Q (DGModuleCat.quasiIso B)
    (_root_.DerivedCategory (ModuleCat.{u} A))).preimageIso
    (QCompDerivedTensorComparisonIso A B M)

end Derived

/-! ### Exact functors of module categories on derived categories -/

section MapDerived

/-- Restriction of scalars preserves homology. -/
theorem restrictScalars_preservesHomology {R S : Type u} [Ring R] [Ring S] (f : R →+* S) :
    (ModuleCat.restrictScalars.{u} f).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ fun S hS => by
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
    exact hS

instance restrictScalars_preservesFiniteLimits {R S : Type u} [Ring R] [Ring S] (f : R →+* S) :
    Limits.PreservesFiniteLimits (ModuleCat.restrictScalars.{u} f) :=
  have := restrictScalars_preservesHomology f
  Functor.preservesFiniteLimits_of_preservesHomology _

variable {C₁ C₂ : Type*} [Category* C₁] [Abelian C₁] [_root_.HasDerivedCategory.{w} C₁]
  [Category* C₂] [Abelian C₂] [_root_.HasDerivedCategory.{w'} C₂]
  {F G : C₁ ⥤ C₂} [F.Additive] [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
  [G.Additive] [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]

/-- Isomorphic exact functors induce isomorphic functors on derived categories. -/
def mapDerivedCategoryIsoOfIso (e : F ≅ G) : F.mapDerivedCategory ≅ G.mapDerivedCategory :=
  (Localization.whiskeringLeftFunctor' _root_.DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ)) (_root_.DerivedCategory C₂)).preimageIso
    (F.mapDerivedCategoryFactors ≪≫
      Functor.isoWhiskerRight (NatIso.mapHomologicalComplex e _) _ ≪≫
      G.mapDerivedCategoryFactors.symm)

end MapDerived

end Categorification

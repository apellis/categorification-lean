/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.OrderedWeightDGProjectivity
import Categorification.Algebra.DiagramWeightLoadingVanish

/-!
# Derived vanishing from an ordered standard resolution

Webster, arXiv:1309.3796v2, Lemma 6.11. The actual graded resolution has
negative terms supported on strictly higher loading idempotents. If those
idempotents annihilate the coefficient filtration layers, the derived tensor
with the homogeneous standard is concentrated in degree zero.
-/

noncomputable section

namespace Categorification
open CategoryTheory DG
open scoped DG.DegreeZero

variable {R : Type} [Ring R] [InternalGrading R] [BigradedDGRing R]
  (P : ℕ → WeightGradedTerm R)
  (δ : ∀ n, (P (n+1)).obj →ₗ[R] (P n).obj)
  (hδ : ∀ n j {x : (P (n+1)).obj}, x ∈ (P (n+1)).grade j → δ n x ∈ (P n).grade j)
  (hc : ∀ n (x : (P (n+2)).obj), δ n (δ (n+1) x) = 0)

local notation "TermComplex" => weightCochainOfGradedChain P δ hδ hc
local notation "Model" => weightDgModuleOfGradedChain P δ hδ hc

/-- The inclusion of one graded chain term in the corresponding cohomological degree. -/
def weightDgChainTermOf (X : WeightCategory R) (n : ℕ) :
    (P n).grade X.as →+ (Model).obj X :=
  (ComplexSum.of ((TermComplex).obj X) (-(n : ℤ))).toAddMonoidHom.comp
    (weightCochainOfGradedChain_coordinate P δ hδ hc X n).inv.hom.toAddMonoidHom

theorem weightDgChainTerm_exists_of (X : WeightCategory R) (n : ℕ) (x : (Model).obj X)
    (hx : x ∈ DG.grading (-(n : ℤ))) : ∃ y, weightDgChainTermOf P δ hδ hc X n y = x := by
  obtain ⟨u, hu⟩ := diagramWeightModuleOfComplex_mem_grading_iff (TermComplex) X (-(n : ℤ)) x |>.mp hx
  refine ⟨(weightCochainOfGradedChain_coordinate P δ hδ hc X n).hom u, ?_⟩
  change ComplexSum.of ((TermComplex).obj X) (-(n : ℤ))
    ((weightCochainOfGradedChain_coordinate P δ hδ hc X n).inv
      ((weightCochainOfGradedChain_coordinate P δ hδ hc X n).hom u)) = x
  erw [Iso.hom_inv_id_apply]
  exact hu

theorem weightDgChainTermOf_act {X Y : WeightCategory R} (a : X ⟶ Y) (n : ℕ)
    (x : (P n).grade X.as) :
    (Model).act a (weightDgChainTermOf P δ hδ hc X n x) =
      weightDgChainTermOf P δ hδ hc Y n ⟨a.val • x.val, by
        have h := (P n).smul_mem a.property x.property
        rwa [show Y.as - X.as + X.as = Y.as by omega] at h⟩ := by
  let u := (weightCochainOfGradedChain_coordinate P δ hδ hc X n).inv x
  change (diagramWeightModuleOfComplex (TermComplex)).act a (ComplexSum.of ((TermComplex).obj X) (-(n : ℤ)) u) =
    ComplexSum.of ((TermComplex).obj Y) (-(n : ℤ))
      ((weightCochainOfGradedChain_coordinate P δ hδ hc Y n).inv _)
  rw [diagramWeightModuleOfComplex_act_of]
  apply congrArg (ComplexSum.of ((TermComplex).obj Y) (-(n : ℤ)))
  apply (ModuleCat.mono_iff_injective (weightCochainOfGradedChain_coordinate P δ hδ hc Y n).hom).mp
    inferInstance
  erw [weightCochainOfGradedChain_coordinate_act, Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]

/-- A graded loading span for an ordinary chain term gives the transported
loading span in the corresponding cohomological term of its dg realization. -/
theorem weightDgChainTerm_loading_support (n : ℕ)
    {I : Type} (e : I → R) (he : ∀ i, e i ∈ wgrading 0)
    (hspan : ∀ j (y : (P n).obj), y ∈ (P n).grade j →
      y ∈ AddSubgroup.closure {z | ∃ (i : I) (k : ℤ) (g : (P n).obj),
        g ∈ (P n).grade k ∧ e i • g = g ∧ ∃ a : wgrading (M := R) (j-k), a.val • g = z})
    (X : WeightCategory R) (x : (Model).obj X) (hx : x ∈ DG.grading (-(n : ℤ))) :
    x ∈ AddSubgroup.closure (diagramWeightLoadingGenerators (Model)
      (fun W i => WeightCategory.homMk (e i) (by simpa only [sub_self] using he i)) X) := by
  let load (W : WeightCategory R) (i : I) : W ⟶ W :=
    WeightCategory.homMk (e i) (by simpa only [sub_self] using he i)
  let D := AddSubgroup.closure (diagramWeightLoadingGenerators (Model) load X)
  change x ∈ D
  obtain ⟨y, rfl⟩ := weightDgChainTerm_exists_of P δ hδ hc X n x hx
  let inc := weightDgChainTermOf P δ hδ hc X n
  let Q := (D.comap inc).map (AddSubgroupClass.subtype ((P n).grade X.as))
  have hle : AddSubgroup.closure {z | ∃ (i : I) (k : ℤ) (g : (P n).obj),
      g ∈ (P n).grade k ∧ e i • g = g ∧
      ∃ a : wgrading (M := R) (X.as-k), a.val • g = z} ≤ Q := by
    apply (AddSubgroup.closure_le _).mpr
    rintro _ ⟨i, k, g, hg, hfix, a, rfl⟩
    let W : WeightCategory R := ⟨k⟩
    let u : (P n).grade W.as := ⟨g, hg⟩
    let f : W ⟶ X := a
    have hu : (Model).act (load W i) (weightDgChainTermOf P δ hδ hc W n u) =
        weightDgChainTermOf P δ hδ hc W n u := by
      rw [weightDgChainTermOf_act]
      exact congrArg _ (Subtype.ext hfix)
    let z : (P n).grade X.as := ⟨a.val • g, by
      have h := (P n).smul_mem a.property hg
      rwa [sub_add_cancel] at h⟩
    refine ⟨z, ?_, rfl⟩
    change inc z ∈ D
    apply AddSubgroup.subset_closure
    refine ⟨W, i, f, weightDgChainTermOf P δ hδ hc W n u, ?_⟩
    rw [hu, weightDgChainTermOf_act]
  obtain ⟨z, hz, hzy⟩ := hle (hspan X.as y.val y.property)
  have hEq : z = y := Subtype.ext hzy
  subst z
  exact hz

end Categorification

namespace Categorification.ModuleFiltration

open CategoryTheory DG
open scoped DG.DegreeZero

variable {R : Type} [Ring R] [InternalGrading R] [BigradedDGRing R]
  {Label : Type} {S : Label → ModuleCat R} {e : Label → R} {above : Label → Label → Prop}
  (data : OrderedStandardCovers S e above) (s : Label)
  (he₀ : ∀ i, e i ∈ wgrading (M := R) 0)
  (he : ∀ i, IsIdempotentElem (e i)) (htrans : ∀ a b c, above a b → above b c → above a c)
  (T : ℤ → AddSubgroup (S s)) [DirectSum.Decomposition T]
  (hsmul : ∀ {i j : ℤ} {a : R} {x : S s}, a ∈ wgrading i → x ∈ T j → a • x ∈ T (i + j))
  (hq : ∀ ⦃n : ℤ⦄ ⦃x : lIdeal (e s)⦄, x.val ∈ wgrading n → data.quotient s x ∈ T n)

local notation "A" => wgrading (M := R)
local notation "W" => WeightCategory R
/-- Every negative cohomological term of the ordered model is supported on
transports of strictly higher loading idempotents. -/
theorem orderedWeightDgResolution_loading_support
    (n : ℕ) (X : W) (x : (orderedWeightDgResolution data s he₀ he htrans T hq).obj X)
    (hx : x ∈ DG.grading (-((n + 1 : ℕ) : ℤ))) :
    x ∈ AddSubgroup.closure (diagramWeightLoadingGenerators
      (orderedWeightDgResolution data s he₀ he htrans T hq)
      (fun Z (i : {i // above s i}) => WeightCategory.homMk (e i.val)
        (by simpa only [sub_self] using he₀ i.val)) X) := by
  apply weightDgChainTerm_loading_support _ _ _ _ (n+1)
    (fun i : {i // above s i} => e i.val) (fun i => he₀ i.val) _ X x hx
  intro j y hy
  refine (AddSubgroup.closure_le _).mpr ?_
    (gradedLoadingResolutionPositive_support data s A (orderedWeightScalarMul (R := R)) he₀ he htrans T hq n j y hy)
  rintro z ⟨i, hi, k, g, hg, hfix, a, ha⟩
  exact AddSubgroup.subset_closure ⟨⟨i, hi⟩, k, g, hg, hfix, a, ha⟩


section Tensor

universe v

variable {B P : Type} [Ring B] [InternalGrading B] [BigradedDGRing B]
  [AddCommGroup P] [Module B P] [Module Rᵐᵒᵖ P] [SMulCommClass B Rᵐᵒᵖ P]
  (G : ℤ → AddSubgroup P)
  (hl : ∀ {i j : ℤ} {a : B} {x : P}, a ∈ wgrading i → x ∈ G j → a • x ∈ G (i+j))
  (hr : ∀ {i j : ℤ} {a : R} {x : P}, a ∈ wgrading i → x ∈ G j → MulOpposite.op a • x ∈ G (j+i))
  [CatModule.HasDerivedCategory.{v,0} (WeightCategory B)]
  [CatModule.HasDerivedCategory.{v,0} (WeightCategory R)]

include data he₀ he htrans hq in
/-- The ordered support and filtered-coefficient step of Webster,
arXiv:1309.3796v2, Lemma 6.11. If every strictly higher loading kills every coefficient layer, the derived tensor has cohomology only in degree zero. -/
theorem orderedWeightDerivedTensor_cohomology_isZero_of_filtered_loading_support
    {η : Type} {L : η → ModuleCat.{0} Rᵐᵒᵖ} {layers : List η}
    (hF : HasFiltration L layers (ModuleCat.of Rᵐᵒᵖ P))
    (hk : ∀ i, above s i → ∀ c ∈ layers, ∀ z : L c, MulOpposite.op (e i) • z = 0)
    (X : WeightCategory B) (n : ℤ) (hn : n ≠ 0) :
    CategoryTheory.Limits.IsZero ((CatModule.DerivedCategory.cohomologyFunctor X n).obj
      ((diagramWeightDerivedTensor G hl hr).obj
        (CatModule.DerivedCategory.Q.obj (orderedWeightDgTarget s T hsmul)))) := by
  let load (Z : W) (i : {i // above s i}) : Z ⟶ Z :=
    WeightCategory.homMk (e i.val) (by simpa only [sub_self] using he₀ i.val)
  refine diagramWeightDerivedTensor_cohomology_isZero_of_filtered_loading_support G hl hr
    (orderedWeightDgAugmentation data s he₀ he htrans T hsmul hq)
    (orderedWeightDgResolution_isKProjective data s he₀ he htrans T hq)
    (orderedWeightDgAugmentation_quasiIso data s he₀ he htrans T hsmul hq)
    X n load (fun _ i => congrArg MulOpposite.op (he i.val).eq) ?_ hF
    (fun _ i => hk i.val i.property)
  intro Z x hx
  by_cases hn' : n < 0
  · let j := (-(n + 1)).toNat
    have hj : -((j + 1 : ℕ) : ℤ) = n := by dsimp [j]; omega
    exact orderedWeightDgResolution_loading_support data s he₀ he htrans T hq j Z x
      (by rw [hj]; exact hx)
  · let K := weightCochainOfGradedChain (orderedWeightTerms data s he₀ he htrans T hq)
        (orderedWeightDifferentials data s he₀ he htrans T hq)
        (orderedWeightDifferentials_mem data s he₀ he htrans T hq)
        (orderedWeightDifferentials_comp data s he₀ he htrans T hq)
    have hzero := weightCochainOfGradedChain_positive_isZero
      (orderedWeightTerms data s he₀ he htrans T hq) (orderedWeightDifferentials data s he₀ he htrans T hq)
      (orderedWeightDifferentials_mem data s he₀ he htrans T hq)
      (orderedWeightDifferentials_comp data s he₀ he htrans T hq) Z n (by omega)
    change (x : ComplexSum (K.obj Z)) ∈ DG.grading (M := ComplexSum (K.obj Z)) n at hx
    obtain ⟨y, hy⟩ := ComplexSum.mem_grading_iff.mp hx
    have hy₀ : y = 0 := (ModuleCat.isZero_iff_subsingleton.mp hzero).elim _ _
    have hx₀ : x = 0 := hy.symm.trans (hy₀ ▸ map_zero _)
    rw [hx₀]
    exact zero_mem _

end Tensor
end Categorification.ModuleFiltration

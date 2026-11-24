/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.GradedMiddleResolution

/-!
# Mixed differentials on the diagram-weight projectives

For Webster, arXiv:1309.3796v2, §7.1, Lemma 7.3 in fundamental type
A₁, the mixed crossings of the middle resolution give degree-zero maps
on the shifted loading projectives in the diagram-weight category.
-/

noncomputable section
namespace Categorification.Stendhal.FundamentalCorner
open CategoryTheory DG CatModule MulOpposite StendhalAlgebraAllOrders
open scoped DG.DegreeZero
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
local notation "T" => TensorProductAlgebra ℚ Q wt ({()} : Multiset Unit)
local notation "𝒜" => tensorProductGrade grading ({()} : Multiset Unit)
local notation "μ" => stendhalWeight 2 ({()} : Multiset Unit)
local instance : InternalGrading Tᵐᵒᵖ := gradedAlgebraInternalGrading (Graded.oppositeGrade 𝒜)
local instance : BigradedDGRing Tᵐᵒᵖ := gradedAlgebraBigradedDGRing (Graded.oppositeGrade 𝒜)
local instance : InternalGrading ℚ := scalarInternalGrading ℚ
local instance : BigradedDGRing ℚ := scalarBigradedDGRing ℚ

def loadingValue {s : KLR.Seq μ} {hs : IsRedOrdered s} {j : ℤ} {k : WeightCategory Tᵐᵒᵖ}
    (x : (shiftedLoadingModule s hs j).obj k) : rIdeal (project (e s)) := by
  refine ⟨x.val.val.unop, ?_⟩
  change project (e s) * x.val.val.unop = x.val.val.unop
  rw [projectedLoading_eq_mk_e s hs]
  exact congrArg (fun f : (⟨j⟩ : WeightCategory Tᵐᵒᵖ) ⟶ k => f.val.unop) x.property

theorem loadingValue_degree {s : KLR.Seq μ} {hs : IsRedOrdered s} {j : ℤ} {k : WeightCategory Tᵐᵒᵖ}
    (x : (shiftedLoadingModule s hs j).obj k) : (loadingValue x).val ∈ 𝒜 (k.as - j) := by
  exact x.val.property

def loadingElement {s : KLR.Seq μ} {hs : IsRedOrdered s} {j : ℤ} {k : WeightCategory Tᵐᵒᵖ}
    (x : rIdeal (project (e s))) (hx : x.val ∈ 𝒜 (k.as-j)) : (shiftedLoadingModule s hs j).obj k := by
  let y : (⟨j⟩ : WeightCategory Tᵐᵒᵖ) ⟶ k :=
    ⟨op x.val, hx⟩
  refine ⟨y, WeightCategory.hom_ext ?_⟩
  change op (TensorProductAlgebra.mk Q wt {()} (StendhalAlgebra.e s hs) * x.val) = op x.val
  rw [← projectedLoading_eq_mk_e s hs]
  exact congrArg op x.property

theorem loadingExt {s : KLR.Seq μ} {hs : IsRedOrdered s} {j : ℤ} {k : WeightCategory Tᵐᵒᵖ}
    {x y : (shiftedLoadingModule s hs j).obj k} (h : (loadingValue x).val = (loadingValue y).val) : x = y :=
  Subtype.ext (WeightCategory.hom_ext (congrArg op h))

theorem loading_mem_grading {s : KLR.Seq μ} {hs : IsRedOrdered s} {j n : ℤ} {k : WeightCategory Tᵐᵒᵖ}
    (x : (shiftedLoadingModule s hs j).obj k) : x ∈ DG.grading n ↔ n = 0 ∨ x = 0 := by
  change x.val.val ∈ DG.grading n ↔ _
  rw [InDegreeZero.ring_mem_grading_iff]
  constructor
  · exact Or.imp_right (fun h => loadingExt (congrArg unop h))
  · exact Or.imp_right (fun h => h ▸ rfl)

theorem loading_d {s : KLR.Seq μ} {hs : IsRedOrdered s} {j : ℤ} {k : WeightCategory Tᵐᵒᵖ}
    (x : (shiftedLoadingModule s hs j).obj k) : d x = 0 := loadingExt (congrArg unop (InDegreeZero.ring_d_apply x.val.val))

def loadingMap {s t : KLR.Seq μ} {hs : IsRedOrdered s} {ht : IsRedOrdered t} {a b : ℤ}
    (f : rIdeal (project (e s)) →ₗ[Tᵐᵒᵖ] rIdeal (project (e t)))
    (hf : ∀ n x, x.val ∈ 𝒜 (n-a) → (f x).val ∈ 𝒜 (n-b)) :
    shiftedLoadingModule s hs a ⟶ shiftedLoadingModule t ht b where
  app k := {
    toFun := fun x => loadingElement (f (loadingValue x)) (hf k.as _ (loadingValue_degree x))
    map_zero' := loadingExt (congrArg Subtype.val f.map_zero)
    map_add' := fun x y => loadingExt (congrArg Subtype.val (f.map_add (loadingValue x) (loadingValue y))) }
  map_mem' {X n x} hx := by
    apply (loading_mem_grading _).mpr
    rcases (loading_mem_grading x).mp hx with h | rfl
    · exact Or.inl h
    · exact Or.inr (loadingExt (congrArg Subtype.val f.map_zero))
  map_d' x := by
    rw [loading_d x, loading_d]
    exact loadingExt (congrArg Subtype.val f.map_zero)
  map_smul' g x := loadingExt (congrArg Subtype.val (f.map_smul g.val (loadingValue x)))

private theorem mid_ordered : IsRedOrdered middle := by unfold IsRedOrdered; decide +kernel
local notation "P₀" => shiftedLoadingModule middle mid_ordered 0
local notation "P₁" => shiftedLoadingModule terminal terminal_ordered 1
local notation "P₂" => shiftedLoadingModule middle mid_ordered 2

/-- The first mixed crossing, from the syzygy generated at internal weight two. -/
def gradedMiddleD₂ : P₂ ⟶ P₁ := loadingMap fundamentalResolutionMap (fun n => (middleResolution_maps_degree n).1)

/-- The second mixed crossing lands in the middle loading projective generated at weight zero. -/
def gradedMiddleD₁ : P₁ ⟶ P₀ :=
  loadingMap terminalToMiddle (fun n x hx => by simpa only [sub_zero] using (middleResolution_maps_degree n).2 x hx)

private theorem scalar_mem_grading {n : ℤ} {k : WeightCategory Tᵐᵒᵖ} (x : gradedMiddleSimple.obj k) :
    x ∈ DG.grading n ↔ n = 0 ∨ x = 0 := by
  change x.val ∈ DG.grading n ↔ _
  rw [InDegreeZero.ring_mem_grading_iff]
  exact ⟨Or.imp_right (fun h => Subtype.ext h), Or.imp_right (fun h => h ▸ rfl)⟩

private theorem scalar_d {k : WeightCategory Tᵐᵒᵖ} (x : gradedMiddleSimple.obj k) :
    d x = 0 := Subtype.ext (InDegreeZero.ring_d_apply x.val)

/-- The homogeneous augmentation by the character at the middle cut. -/
def gradedMiddleAugmentation : P₀ ⟶ gradedMiddleSimple where
  app k := {
    toFun := fun x => ⟨middleCharacter (loadingValue x).val, by
      have h := gradedMiddleCharacter_mem_weight x.val.property
      change middleCharacter x.val.val.unop ∈ DG.wgrading (M := ℚ) (k.as - 0)
      exact h⟩
    map_zero' := Subtype.ext (map_zero middleCharacter)
    map_add' := fun x y => Subtype.ext (map_add middleCharacter (loadingValue x).val (loadingValue y).val) }
  map_mem' {k n x} hx := by
    apply (scalar_mem_grading _).mpr
    rcases (loading_mem_grading x).mp hx with h | rfl
    · exact Or.inl h
    · exact Or.inr (Subtype.ext (map_zero middleCharacter))
  map_d' x := by rw [loading_d x, scalar_d]; exact Subtype.ext (map_zero middleCharacter)
  map_smul' g x := Subtype.ext ((map_mul middleCharacter (loadingValue x).val g.val.unop).trans (mul_comm _ _))

/-- The two crossing maps followed by the scalar augmentation form an exact
sequence of diagram-weight modules at every internal weight. -/
theorem gradedMiddleComplex_exact (k : WeightCategory Tᵐᵒᵖ) :
    Function.Injective (gradedMiddleD₂.app k) ∧ Function.Exact (gradedMiddleD₂.app k) (gradedMiddleD₁.app k) ∧
      Function.Exact (gradedMiddleD₁.app k) (gradedMiddleAugmentation.app k) ∧
      Function.Surjective (gradedMiddleAugmentation.app k) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y h
    apply loadingExt
    apply congrArg Subtype.val
    apply fundamentalResolutionMap_injective
    exact Subtype.ext (congrArg (fun z => (loadingValue z).val) h)
  · intro x
    constructor
    · intro h
      have hz : terminalToMiddle (loadingValue x) = 0 := Subtype.ext (congrArg (fun z => (loadingValue z).val) h)
      obtain ⟨y, hy, he⟩ := (middleResolution_exact_terminal k.as _ (loadingValue_degree x)).mp hz
      exact ⟨loadingElement y hy, loadingExt (congrArg Subtype.val he)⟩
    · rintro ⟨y, rfl⟩
      apply loadingExt
      have h := LinearMap.congr_fun terminalToMiddle_comp (loadingValue y)
      exact congrArg Subtype.val h
  · intro x
    have hx : (loadingValue x).val ∈ 𝒜 k.as := by simpa only [sub_zero] using loadingValue_degree x
    constructor
    · intro h
      obtain ⟨y, hy, he⟩ := (middleResolution_exact_middle k.as _ hx).mp (congrArg Subtype.val h)
      exact ⟨loadingElement y hy, loadingExt (congrArg Subtype.val he)⟩
    · rintro ⟨y, hy⟩
      apply Subtype.ext
      exact (middleResolution_exact_middle k.as _ hx).mpr
        ⟨loadingValue y, loadingValue_degree y, Subtype.ext (congrArg (fun z => (loadingValue z).val) hy)⟩
  · intro z
    have hz : k.as = 0 ∨ z.val = 0 := by
      have h : z.val ∈ DG.grading (k.as - 0) := z.property
      simpa only [sub_zero, InDegreeZero.ring_mem_grading_iff] using h
    obtain ⟨x, hx, he⟩ := middleResolution_augmentation_surjective _ _ hz
    exact ⟨loadingElement x (by simpa only [sub_zero] using hx), Subtype.ext he⟩

end Categorification.Stendhal.FundamentalCorner

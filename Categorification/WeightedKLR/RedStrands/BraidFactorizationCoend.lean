/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidFactorizationDegree
import Categorification.Algebra.DiagramWeightCorner

/-!
# The graded braid factorization equivalence

Ordinary factorization spans the actual quotient coefficient by products.
Projection to each degree gives surjectivity of the corresponding tensor
map over the intermediate weight category.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR TypeA Equiv CategoryTheory
open scoped List

variable {I : Type} [DecidableEq I] {k : Type*} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
  {lower middle upper : List (Fin ℓ)}
  {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}

local notation "A" => ViolQuotient k Q Λ ν
local notation "ep" κ:arg => violMk k Q Λ ν (redProj k Q Λ ν κ)
local notation "hE" κ:arg => isIdempotentElem_violMk_redProj k Q Λ ν κ
local notation "Co" a:arg b:arg => braidingBimodule k Q Λ ν a b
local notation "T" => CornerTensor k A (ep upper) (ep middle) (ep lower)

/-- Under the factorization hypothesis, the unrestricted products of the two
diagram coefficients span the actual target corner as an additive group. -/
theorem braidingCoefficientMul_span (hρ : IsReducedChoice ρ) (hQ : KLRSymm Q)
    (h0 : lower.Nodup) (hp : lower.Perm middle)
    (H : ∀ x y, [x, y] <+ lower → [y, x] <+ middle → [y, x] <+ upper) :
    AddSubgroup.closure
      (Set.range (fun z : Co upper middle × Co middle lower => braidingCoefficientMul z.1 z.2)) =
      ⊤ := by
  apply top_unique
  intro z _
  let φ := violCornerTensorMulEquiv (k := k) (Q := Q) (Λ := Λ) (ν := ν) hρ hQ h0 hp H
  obtain ⟨t, rfl⟩ := φ.surjective z
  induction t using CornerTensor.induction_on with
  | tmul x y =>
    let x' : Co upper middle := ⟨ep upper * x * ep middle, mem_cornerBimodule.mpr
      ⟨by simp only [← mul_assoc, (hE upper).eq],
        by rw [mul_assoc _ (ep middle) (ep middle), (hE middle).eq]⟩⟩
    let y' : Co middle lower := ⟨ep middle * y * ep lower, mem_cornerBimodule.mpr
      ⟨by simp only [← mul_assoc, (hE middle).eq],
        by rw [mul_assoc _ (ep lower) (ep lower), (hE lower).eq]⟩⟩
    apply AddSubgroup.subset_closure
    refine ⟨(x', y'), Subtype.ext ?_⟩
    change (ep upper * x * ep middle) * (ep middle * y * ep lower) =
      CornerTensor.mult (k := k) (hE upper) (hE middle) (hE lower) (CornerTensor.tmul x y : T)
    rw [CornerTensor.mult_tmul]
    simp only [← mul_assoc]
    rw [mul_assoc (ep upper * x) (ep middle) (ep middle), (hE middle).eq]
  | add x y hx hy =>
    exact (map_add φ x y).symm ▸ add_mem (hx (by simp)) (hy (by simp))

section Graded

open DG QuantumGroup
open scoped DG.DegreeZero

variable (C : CartanDatum I) (hQ : IsRouquierQ C Q)

local notation "G" => stendhalGradingDatum Λ hQ.gradingDatum (UDot.di C)
  (fun i => Eq.trans (IsRouquierQ.gradingDatum_degX hQ i) (Eq.symm (UDot.two_mul_di C i)))
local notation "V" => violAuxiliaryGrade (ν := ν) G
local notation "H₀" κ:arg => redProj_mem_violAuxiliaryGrade (ν := ν) G κ
local notation "S" κ:arg => Graded.oppositeGrade (Graded.cornerGrading V (hE κ))

/-- Under the ordinary factorization condition, the right-module tensor
over the intermediate weight category maps onto the actual homogeneous
quotient coefficient at every endpoint weight. -/
theorem braidFactorizationCoend_surjective (hρ : IsReducedChoice ρ)
    (h0 : lower.Nodup) (hp : lower.Perm middle)
    (H : ∀ x y, [x, y] <+ lower → [y, x] <+ middle → [y, x] <+ upper) :
    letI := Graded.cornerGradedAlgebra V (hE upper) (H₀ upper)
    letI := Graded.cornerGradedAlgebra V (hE middle) (H₀ middle)
    letI := Graded.cornerGradedAlgebra V (hE lower) (H₀ lower)
    letI := gradedAlgebraInternalGrading (S upper)
    letI := gradedAlgebraInternalGrading (S middle)
    letI := gradedAlgebraInternalGrading (S lower)
    letI := gradedAlgebraBigradedDGRing (S upper)
    letI := gradedAlgebraBigradedDGRing (S middle)
    letI := gradedAlgebraBigradedDGRing (S lower)
    ∀ (X : WeightCategory (hE lower).Cornerᵐᵒᵖ) (Z : WeightCategory (hE upper).Cornerᵐᵒᵖ),
      Function.Surjective (diagramCornerWeightRightCoendProduct V (hE upper) (hE middle)
        (H₀ upper) (H₀ middle) (hE lower) (H₀ lower) X Z) := by
  apply diagramCornerWeightRightCoendProduct_surjective
  · exact diagramCornerWeight_isInternal V (H₀ middle) (H₀ lower)
  · exact diagramCornerWeight_isInternal V (H₀ upper) (H₀ middle)
  · exact diagramCornerWeight_isInternal V (H₀ upper) (H₀ lower)
  · have hs := braidingCoefficientMul_span (k := k) (Q := Q) (Λ := Λ) (ν := ν)
      hρ (fun i j hij => (hQ.symm i j hij).symm) h0 hp H
    have hrange :
        Set.range (fun z : Co middle lower × Co upper middle => cornerRightProduct z.1 z.2) =
          Set.range (fun z : Co upper middle × Co middle lower => braidingCoefficientMul z.1 z.2) := by
      ext z
      constructor
      · rintro ⟨⟨x, y⟩, rfl⟩
        exact ⟨(y, x), rfl⟩
      · rintro ⟨⟨x, y⟩, rfl⟩
        exact ⟨(y, x), rfl⟩
    rw [hrange]
    exact hs

/-- Length-additive multiplication is bijective on each actual weight coend. -/
theorem braidFactorizationCoend_bijective (hρ : IsReducedChoice ρ)
    (h0 : lower.Nodup) (hp : lower.Perm middle)
    (H : ∀ x y, [x, y] <+ lower → [y, x] <+ middle → [y, x] <+ upper) :
    letI := Graded.cornerGradedAlgebra V (hE upper) (H₀ upper)
    letI := Graded.cornerGradedAlgebra V (hE middle) (H₀ middle)
    letI := Graded.cornerGradedAlgebra V (hE lower) (H₀ lower)
    letI := gradedAlgebraInternalGrading (S upper)
    letI := gradedAlgebraInternalGrading (S middle)
    letI := gradedAlgebraInternalGrading (S lower)
    letI := gradedAlgebraBigradedDGRing (S upper)
    letI := gradedAlgebraBigradedDGRing (S middle)
    letI := gradedAlgebraBigradedDGRing (S lower)
    ∀ (X : WeightCategory (hE lower).Cornerᵐᵒᵖ) (Z : WeightCategory (hE upper).Cornerᵐᵒᵖ),
      Function.Bijective (diagramCornerWeightRightCoendProduct V (hE upper) (hE middle)
        (H₀ upper) (H₀ middle) (hE lower) (H₀ lower) X Z) := by
  let := Graded.cornerGradedAlgebra V (hE upper) (H₀ upper)
  let := Graded.cornerGradedAlgebra V (hE middle) (H₀ middle)
  let := Graded.cornerGradedAlgebra V (hE lower) (H₀ lower)
  let := gradedAlgebraInternalGrading (S upper)
  let := gradedAlgebraInternalGrading (S middle)
  let := gradedAlgebraInternalGrading (S lower)
  let := gradedAlgebraBigradedDGRing (S upper)
  let := gradedAlgebraBigradedDGRing (S middle)
  let := gradedAlgebraBigradedDGRing (S lower)
  intro X Z
  refine ⟨?_, braidFactorizationCoend_surjective C hQ hρ h0 hp H X Z⟩
  exact diagramCornerWeightRightCoendProduct_injective V (hE upper) (hE middle) (hE lower)
    (H₀ upper) (H₀ middle) (H₀ lower)
    (diagramCornerWeight_isInternal V (H₀ middle) (H₀ lower))
    (diagramCornerWeight_isInternal V (H₀ upper) (H₀ middle))
    (violMk_mult_injective (k := k) (Q := Q) (Λ := Λ) (ν := ν) hρ
      (fun i j hij => (hQ.symm i j hij).symm) h0 hp H) X Z

/-- The ordinary graded factorization equivalence of the actual right coefficients. -/
def braidFactorizationCoendEquiv (hρ : IsReducedChoice ρ)
    (h0 : lower.Nodup) (hp : lower.Perm middle)
    (H : ∀ x y, [x, y] <+ lower → [y, x] <+ middle → [y, x] <+ upper) :
    letI := Graded.cornerGradedAlgebra V (hE upper) (H₀ upper)
    letI := Graded.cornerGradedAlgebra V (hE middle) (H₀ middle)
    letI := Graded.cornerGradedAlgebra V (hE lower) (H₀ lower)
    letI := gradedAlgebraInternalGrading (S upper)
    letI := gradedAlgebraInternalGrading (S middle)
    letI := gradedAlgebraInternalGrading (S lower)
    letI := gradedAlgebraBigradedDGRing (S upper)
    letI := gradedAlgebraBigradedDGRing (S middle)
    letI := gradedAlgebraBigradedDGRing (S lower)
    (X : WeightCategory (hE lower).Cornerᵐᵒᵖ) → (Z : WeightCategory (hE upper).Cornerᵐᵒᵖ) →
      CatTensorProduct
        ((diagramCornerWeightRightBimodule V (hE middle) (hE lower) (H₀ middle) (H₀ lower)).right X)
        ((diagramCornerWeightRightBimodule V (hE upper) (hE middle) (H₀ upper) (H₀ middle)).left Z) ≃+
      InDegreeZero (diagramCornerWeight (e := ep upper) (e' := ep lower) V (X.as - Z.as)) := by
  letI := Graded.cornerGradedAlgebra V (hE upper) (H₀ upper)
  letI := Graded.cornerGradedAlgebra V (hE middle) (H₀ middle)
  letI := Graded.cornerGradedAlgebra V (hE lower) (H₀ lower)
  letI := gradedAlgebraInternalGrading (S upper)
  letI := gradedAlgebraInternalGrading (S middle)
  letI := gradedAlgebraInternalGrading (S lower)
  letI := gradedAlgebraBigradedDGRing (S upper)
  letI := gradedAlgebraBigradedDGRing (S middle)
  letI := gradedAlgebraBigradedDGRing (S lower)
  intro X Z
  exact AddEquiv.ofBijective _ (braidFactorizationCoend_bijective C hQ hρ h0 hp H X Z)

/-- The ordinary graded braid factorization as a natural isomorphism of dg module families. -/
def braidFactorizationCoendNatIso (hρ : IsReducedChoice ρ)
    (h0 : lower.Nodup) (hp : lower.Perm middle)
    (H : ∀ x y, [x, y] <+ lower → [y, x] <+ middle → [y, x] <+ upper) :
    letI := Graded.cornerGradedAlgebra V (hE upper) (H₀ upper)
    letI := Graded.cornerGradedAlgebra V (hE middle) (H₀ middle)
    letI := Graded.cornerGradedAlgebra V (hE lower) (H₀ lower)
    letI := gradedAlgebraInternalGrading (S upper)
    letI := gradedAlgebraInternalGrading (S middle)
    letI := gradedAlgebraInternalGrading (S lower)
    letI := gradedAlgebraBigradedDGRing (S upper)
    letI := gradedAlgebraBigradedDGRing (S middle)
    letI := gradedAlgebraBigradedDGRing (S lower)
    diagramCornerWeightRightFamily V (hE upper) (hE middle) (H₀ upper) (H₀ middle) ⋙
      (diagramCornerWeightRightBimodule V (hE middle) (hE lower) (H₀ middle) (H₀ lower)).tensorFunctor ≅
        diagramCornerWeightRightFamily V (hE upper) (hE lower) (H₀ upper) (H₀ lower) := by
  letI := Graded.cornerGradedAlgebra V (hE upper) (H₀ upper)
  letI := Graded.cornerGradedAlgebra V (hE middle) (H₀ middle)
  letI := Graded.cornerGradedAlgebra V (hE lower) (H₀ lower)
  letI := gradedAlgebraInternalGrading (S upper)
  letI := gradedAlgebraInternalGrading (S middle)
  letI := gradedAlgebraInternalGrading (S lower)
  letI := gradedAlgebraBigradedDGRing (S upper)
  letI := gradedAlgebraBigradedDGRing (S middle)
  letI := gradedAlgebraBigradedDGRing (S lower)
  exact diagramCornerWeightRightCoendNatIso V (hE upper) (hE middle) (hE lower)
    (H₀ upper) (H₀ middle) (H₀ lower) (braidFactorizationCoend_bijective C hQ hρ h0 hp H)

/-- The length-additive graded braid composite at a source weight is computed
by the product coefficient if tensoring preserves the resolution augmentation. -/
def braidFactorizationDerivedCoendOfResolution (hρ : IsReducedChoice ρ)
    (h0 : lower.Nodup) (hp : lower.Perm middle)
    (H : ∀ x y, [x, y] <+ lower → [y, x] <+ middle → [y, x] <+ upper) :
    letI := Graded.cornerGradedAlgebra V (hE upper) (H₀ upper)
    letI := Graded.cornerGradedAlgebra V (hE middle) (H₀ middle)
    letI := Graded.cornerGradedAlgebra V (hE lower) (H₀ lower)
    letI := gradedAlgebraInternalGrading (S upper)
    letI := gradedAlgebraInternalGrading (S middle)
    letI := gradedAlgebraInternalGrading (S lower)
    letI := gradedAlgebraBigradedDGRing (S upper)
    letI := gradedAlgebraBigradedDGRing (S middle)
    letI := gradedAlgebraBigradedDGRing (S lower)
    [CatModule.HasDerivedCategory (WeightCategory (hE middle).Cornerᵐᵒᵖ)] →
    [CatModule.HasDerivedCategory (WeightCategory (hE lower).Cornerᵐᵒᵖ)] →
    ∀ (Z : WeightCategory (hE upper).Cornerᵐᵒᵖ)
      {K : CatModule (WeightCategory (hE middle).Cornerᵐᵒᵖ)}
      (f : K ⟶ (diagramCornerWeightRightBimodule V (hE upper) (hE middle)
        (H₀ upper) (H₀ middle)).left Z),
      CatModule.IsKProjective K → CatModule.IsQuasiIso f →
      CatModule.IsQuasiIso ((diagramCornerWeightRightBimodule V (hE middle) (hE lower)
        (H₀ middle) (H₀ lower)).tensorMap f) →
      ((diagramCornerWeightDerivedRightTensor V (hE middle) (hE lower) (H₀ middle) (H₀ lower)).obj
        (CatModule.DerivedCategory.Q.obj ((diagramCornerWeightRightBimodule V (hE upper) (hE middle)
          (H₀ upper) (H₀ middle)).left Z)) ≅ CatModule.DerivedCategory.Q.obj
            ((diagramCornerWeightRightBimodule V (hE upper) (hE lower)
              (H₀ upper) (H₀ lower)).left Z)) := by
  letI := Graded.cornerGradedAlgebra V (hE upper) (H₀ upper)
  letI := Graded.cornerGradedAlgebra V (hE middle) (H₀ middle)
  letI := Graded.cornerGradedAlgebra V (hE lower) (H₀ lower)
  letI := gradedAlgebraInternalGrading (S upper)
  letI := gradedAlgebraInternalGrading (S middle)
  letI := gradedAlgebraInternalGrading (S lower)
  letI := gradedAlgebraBigradedDGRing (S upper)
  letI := gradedAlgebraBigradedDGRing (S middle)
  letI := gradedAlgebraBigradedDGRing (S lower)
  intro hM hL Z K f hK hf ht
  exact diagramCornerWeightRightDerivedFactorizationOfResolution V (hE upper) (hE middle) (hE lower)
    (H₀ upper) (H₀ middle) (H₀ lower) (braidFactorizationCoend_bijective C hQ hρ h0 hp H)
    Z f hK hf ht

/-- The graded derived composition with the source identity braid needs no
resolution hypothesis. -/
def braidFactorizationDerivedCoendIdentity (hρ : IsReducedChoice ρ)
    (h0 : lower.Nodup) (hp : lower.Perm middle) :
    letI := Graded.cornerGradedAlgebra V (hE middle) (H₀ middle)
    letI := Graded.cornerGradedAlgebra V (hE lower) (H₀ lower)
    letI := gradedAlgebraInternalGrading (S middle)
    letI := gradedAlgebraInternalGrading (S lower)
    letI := gradedAlgebraBigradedDGRing (S middle)
    letI := gradedAlgebraBigradedDGRing (S lower)
    [CatModule.HasDerivedCategory (WeightCategory (hE middle).Cornerᵐᵒᵖ)] →
    [CatModule.HasDerivedCategory (WeightCategory (hE lower).Cornerᵐᵒᵖ)] →
    ∀ Z : WeightCategory (hE middle).Cornerᵐᵒᵖ,
      ((diagramCornerWeightDerivedRightTensor V (hE middle) (hE lower) (H₀ middle) (H₀ lower)).obj
        (CatModule.DerivedCategory.Q.obj ((diagramCornerWeightRightBimodule V (hE middle) (hE middle)
          (H₀ middle) (H₀ middle)).left Z)) ≅ CatModule.DerivedCategory.Q.obj
            ((diagramCornerWeightRightBimodule V (hE middle) (hE lower)
              (H₀ middle) (H₀ lower)).left Z)) := by
  letI := Graded.cornerGradedAlgebra V (hE middle) (H₀ middle)
  letI := Graded.cornerGradedAlgebra V (hE lower) (H₀ lower)
  letI := gradedAlgebraInternalGrading (S middle)
  letI := gradedAlgebraInternalGrading (S lower)
  letI := gradedAlgebraBigradedDGRing (S middle)
  letI := gradedAlgebraBigradedDGRing (S lower)
  intro hM hL Z
  exact diagramCornerWeightRightDerivedFactorizationSelf V (hE middle) (hE lower)
    (H₀ middle) (H₀ lower)
    (braidFactorizationCoend_bijective C hQ hρ h0 hp (upper := middle) (fun _ _ _ h => h)) Z

end Graded

end Categorification.Stendhal.BraidedStendhalAlgebra

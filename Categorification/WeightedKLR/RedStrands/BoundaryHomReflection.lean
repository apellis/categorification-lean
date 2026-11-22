/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.Projectives
import Categorification.WeightedKLR.RedStrands.RepresentationLift
import Categorification.WeightedKLR.RedStrands.StendhalTensorGrading
import Categorification.KLR.GradingFlip
import Categorification.Algebra.Graded.Duality

/-!
# Horizontal reflection of boundary Hom spaces

Webster, arXiv:1309.3796v2, Definitions 4.5–4.7 and §4.7, Lemma 4.36.
Horizontal reflection interchanges the two degree-zero boundary
idempotents in the homogeneous Hom space of the associated projectives.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra Categorification.Graded MulOpposite
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type*} [DecidableEq I] [Field k] {ℓ : ℕ} {ν : Multiset I}
    {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}

local notation "μ" => stendhalWeight ℓ ν
local notation "S" => stendhalQ Q Λ
local notation "A" => KLRAlgebra k S μ
local notation "T" => TensorProductAlgebra k Q Λ ν
local notation "π" => stendhalTensorProjection (Q := Q) Λ ν

private def affineFlipProjection : A →ₐ[k] Tᵐᵒᵖ :=
  (π).op.comp (KLRAlgebra.flipH k S μ).toAlgHom

private theorem affineFlipProjection_apply (a : A) :
    affineFlipProjection (Q := Q) (Λ := Λ) (ν := ν) a = op (π (hflip a)) := rfl

private theorem affineFlipProjection_relations :
    TensorRepresentationRelations (affineFlipProjection (Q := Q) (Λ := Λ) (ν := ν)) where
  red_dot a s ha := by
    rw [affineFlipProjection_apply, hflip_mul, hflip_e, hflip_x, e_mul_x,
      (tensorRepresentationRelations_projection (Q := Q) (Λ := Λ) (ν := ν)).red_dot a s ha, op_zero]
  red_cross j hj s ha hb := by
    rw [affineFlipProjection_apply, hflip_mul, hflip_e, hflip_ψ, e_mul_ψ]
    let t := TypeA.sadj (Multiset.card μ) j • s
    have h₁ : (t.lbl ⟨j, by omega⟩).isRight := by rwa [lbl_sadj_left hj]
    have h₂ : (t.lbl ⟨j + 1, hj⟩).isRight := by rwa [lbl_sadj_right hj]
    rw [(tensorRepresentationRelations_projection (Q := Q) (Λ := Λ) (ν := ν)).red_cross j hj t h₁ h₂, op_zero]
  unordered s hs := by
    rw [affineFlipProjection_apply, hflip_e,
      (tensorRepresentationRelations_projection (Q := Q) (Λ := Λ) (ν := ν)).unordered s hs, op_zero]
  violated s ho hv := by
    rw [affineFlipProjection_apply, hflip_e,
      (tensorRepresentationRelations_projection (Q := Q) (Λ := Λ) (ν := ν)).violated s ho hv, op_zero]

private def reflection : T →ₐ[k] Tᵐᵒᵖ :=
  tensorRepresentationLift affineFlipProjection affineFlipProjection_relations

local notation "R" => reflection (Q := Q) (Λ := Λ) (ν := ν)

private theorem reflection_projection (a : A) : R (π a) = op (π (hflip a)) := by
  exact DFunLike.congr_fun
    (tensorRepresentationLift_comp affineFlipProjection affineFlipProjection_relations) a

private abbrev reflect (z : T) : T := (R z).unop

private theorem reflect_projection (a : A) : reflect (π a) = π (hflip a) :=
  congrArg unop (reflection_projection a)

private theorem reflect_reflect (z : T) : reflect (reflect z) = z := by
  obtain ⟨a, rfl⟩ :=
    ((show Function.Surjective (TensorProductAlgebra.mk Q Λ ν) from RingCon.mkₐ_surjective _).comp
      ((orderProjection_surjective Q Λ ν).comp
        (StendhalAlgebraAllOrders.ofKLR_surjective (k := k) (Q := Q) (Λ := Λ) (ν := ν)))) z
  change reflect (reflect (π a)) = _
  rw [reflect_projection, reflect_projection, hflip_hflip]
  rfl

private theorem reflect_mul (x y : T) : reflect (x * y) = reflect y * reflect x := by
  change unop (R (x * y)) = _
  rw [map_mul, unop_mul]

private theorem reflect_e (s : Seq μ) (hs : IsRedOrdered s) :
    reflect (TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e s hs)) =
      TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e s hs) := by
  rw [← stendhalTensorProjection_e (Q := Q) Λ ν s hs, reflect_projection, hflip_e]

private theorem reflect_mem_grade (G : GradingDatum S)
    (hsymm : ∀ a b, G.degΨ a b = G.degΨ b a) {d : ℤ} {z : T}
    (hz : z ∈ tensorProductGrade G ν d) : reflect z ∈ tensorProductGrade G ν d := by
  obtain ⟨a, ha, rfl⟩ := stendhalTensorProjection_grade_lift Λ G ν hz
  rw [reflect_projection]
  exact stendhalTensorProjection_mem_grade Λ G ν (G.hflip_mem_grade hsymm ha)

section Corner

variable {B : Type*} [Ring B] [Algebra k B] {𝒜 : ℤ → Submodule k B} [GradedAlgebra 𝒜]

private abbrev homCorner (e f : B) (d : ℤ) :=
  idem (Graded.submodule 𝒜 (leftIdeal f)) e d

private def homCornerFlip
    (F : B →ₗ[k] B)
    (hmul : ∀ x y, F (x * y) = F y * F x)
    (hgrade : ∀ {d z}, z ∈ 𝒜 d → F z ∈ 𝒜 d)
    (e f : B) (he : F e = e) (hf : F f = f) (d : ℤ) :
    homCorner (𝒜 := 𝒜) e f d → homCorner (𝒜 := 𝒜) f e d := fun z => by
  let x := z.val.val.val
  have hleft : e * x = x := congrArg Subtype.val z.val.2
  have hright : x * f = x := z.val.val.2
  have h₁ : F x * e = F x := by rw [← he, ← hmul, hleft]
  have h₂ : f * F x = F x := by rw [← hf, ← hmul, hright]
  exact ⟨⟨⟨F x, h₁⟩, Subtype.ext h₂⟩, hgrade z.2⟩

private def homCornerFlipEquiv
    (F : B →ₗ[k] B) (hF : Function.Involutive F)
    (hmul : ∀ x y, F (x * y) = F y * F x)
    (hgrade : ∀ {d z}, z ∈ 𝒜 d → F z ∈ 𝒜 d)
    (e f : B) (he : F e = e) (hf : F f = f) (d : ℤ) :
    homCorner (𝒜 := 𝒜) e f d ≃ₗ[k] homCorner (𝒜 := 𝒜) f e d where
  toFun := homCornerFlip F hmul hgrade e f he hf d
  invFun := homCornerFlip F hmul hgrade f e hf he d
  left_inv z := Subtype.ext (Subtype.ext (Subtype.ext (hF z.val.val.val)))
  right_inv z := Subtype.ext (Subtype.ext (Subtype.ext (hF z.val.val.val)))
  map_add' x y := Subtype.ext (Subtype.ext (Subtype.ext (F.map_add x.val.val.val y.val.val.val)))
  map_smul' c x := Subtype.ext (Subtype.ext (Subtype.ext (F.map_smul c x.val.val.val)))

end Corner

private def reflectLinear : T →ₗ[k] T where
  toFun := reflect (Q := Q) (Λ := Λ)
  map_add' x y := by
    change (R (x + y)).unop = (R x).unop + (R y).unop
    rw [map_add, unop_add]
  map_smul' c x := by
    change (R (c • x)).unop = c • (R x).unop
    rw [map_smul]
    rfl

/-- Horizontal reflection of the tensor product algebra, with the grading from
Webster, arXiv:1309.3796v2, Definitions 4.5–4.7. -/
def tensorReflection (G : GradingDatum S)
    (hsymm : ∀ a b, G.degΨ a b = G.degΨ b a) :
    GradedAntiInvolution (tensorProductGrade G ν) where
  toLinearMap := reflectLinear
  map_mul' := reflect_mul
  map_one' := congrArg unop (map_one R)
  invol' := reflect_reflect
  mem_grade' := fun {_ _} ha => reflect_mem_grade G hsymm ha

@[simp] theorem tensorReflection_e (G : GradingDatum S)
    (hsymm : ∀ a b, G.degΨ a b = G.degΨ b a) (s : Seq μ) (hs : IsRedOrdered s) :
    tensorReflection G hsymm (TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e s hs)) =
      TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e s hs) :=
  reflect_e s hs

/-- In Webster, arXiv:1309.3796v2, Definitions 4.5–4.7 and Lemma 4.36,
horizontal reflection exchanges the source and target of a sequence
projective Hom space and preserves its degree. -/
theorem homGdimPoly_sequenceProj_symm (G : GradingDatum S)
    (hsymm : ∀ a b, G.degΨ a b = G.degΨ b a) (s t : Seq μ)
    (hs : IsRedOrdered s) (ht : IsRedOrdered t) :
    gdimPoly (homGrade T (sequenceProj (Q := Q) G s hs).grading (sequenceProj (Q := Q) G t ht).grading) =
      gdimPoly (homGrade T (sequenceProj (Q := Q) G t ht).grading (sequenceProj (Q := Q) G s hs).grading) := by
  have h (d : ℤ) :
      Module.finrank k (homGrade T (sequenceProj (Q := Q) G s hs).grading (sequenceProj (Q := Q) G t ht).grading d) =
        Module.finrank k (homGrade T (sequenceProj (Q := Q) G t ht).grading (sequenceProj (Q := Q) G s hs).grading d) := by
    let e := TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e s hs)
    let f := TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e t ht)
    let F : T →ₗ[k] T := reflectLinear
    have h₁ := (homGradeIdemEquiv (ℳ := (sequenceProj (Q := Q) G t ht).grading)
      (isIdempotentElem_mk_e s hs) (mk_e_mem_tensorProductGrade G ν s hs) d).finrank_eq
    have h₂ := (homGradeIdemEquiv (ℳ := (sequenceProj (Q := Q) G s hs).grading)
      (isIdempotentElem_mk_e t ht) (mk_e_mem_tensorProductGrade G ν t ht) d).finrank_eq
    have hflip := (homCornerFlipEquiv (𝒜 := tensorProductGrade G ν) F
      reflect_reflect reflect_mul (fun hz => reflect_mem_grade G hsymm hz) e f
      (reflect_e s hs) (reflect_e t ht) d).finrank_eq
    exact h₁.trans (hflip.trans h₂.symm)
  classical
  let polynomial (f : ℤ → ℤ) : LaurentPolynomial ℤ :=
    if hf : (Function.support f).Finite then .ofCoeff (Finsupp.ofSupportFinite f hf) else 0
  change polynomial _ = polynomial _
  exact congrArg polynomial (funext fun d => congrArg (fun n : ℕ => (n : ℤ)) (h d))

/-- Horizontal reflection of the tensor product algebra, as an algebra homomorphism into the
opposite algebra: the map induced by the horizontal flip `hflip` of the KLR algebra. -/
def tensorReflect : T →ₐ[k] Tᵐᵒᵖ := R

theorem tensorReflect_projection (a : A) :
    tensorReflect (Q := Q) (Λ := Λ) (ν := ν) (π a) = op (π (hflip a)) :=
  reflection_projection a

theorem unop_tensorReflect_unop_tensorReflect (z : T) :
    (tensorReflect (Q := Q) (Λ := Λ) (ν := ν)
      (tensorReflect (Q := Q) (Λ := Λ) (ν := ν) z).unop).unop = z :=
  reflect_reflect z

/-- The reflection fixes the idempotents `e(s)` of red-ordered sequences. -/
theorem unop_tensorReflect_e (s : Seq μ) (hs : IsRedOrdered s) :
    (tensorReflect (Q := Q) (Λ := Λ) (ν := ν)
      (TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e s hs))).unop =
      TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e s hs) :=
  reflect_e s hs

theorem tensorReflect_injective :
    Function.Injective (tensorReflect (Q := Q) (Λ := Λ) (ν := ν)) := fun x y h => by
  rw [← unop_tensorReflect_unop_tensorReflect x, ← unop_tensorReflect_unop_tensorReflect y, h]

end Categorification.Stendhal

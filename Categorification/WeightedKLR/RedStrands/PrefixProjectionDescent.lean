/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicAffineQuotients
import Categorification.WeightedKLR.RedStrands.RepresentationLift

/-!
# Maps out of a red subfamily through the tensor product algebra

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
Definitions 4.5–4.7, as used in the proof of Proposition 5.21. The projection of the affine
KLR algebra of a red subfamily onto the tensor product algebra `T^{λ'}` is universal among
multiplicative maps: a multiplicative linear map killing red dots, crossings of two red strands,
unordered idempotents and violated idempotents factors through it. The map need not be unital;
it is made unital by passing to the corner of the image of `1`.

## Main results

* `exists_redSubfamilyProjection_factor`: the factorization.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR KLRAlgebra
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type*} [DecidableEq I] [CommRing k] {m n : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin n → I →₀ ℕ)
    (f : Fin m → Fin n) (hf : Function.Injective f) (ν : Multiset I)
    {C : Type*} [Ring C] [Algebra k C]

local notation "c" => Sum.map (id : I → I) f
local notation "μ" => stendhalWeight m ν
local notation "S" => stendhalQ Q Λ
local notation "ρ" => redSubfamilyRelabel Q Λ f hf ν

/-- The red relations of Definitions 4.5–4.7, on a map out of the ambient KLR algebra of a red
subfamily, phrased through the source loadings. -/
structure RedSubfamilyRelations (G : KLRAlgebra k S ((μ).map c) →ₙₐ[k] C) : Prop where
  red_dot : ∀ (s : Seq μ) (a : Fin (μ).card), (s.lbl a).isRight →
    G (x (Fin.cast (Multiset.card_map c μ).symm a) * e (Seq.map c s)) = 0
  red_cross : ∀ (j : ℕ) (hj : j+1 < (μ).card) (s : Seq μ),
    (s.lbl ⟨j, by omega⟩).isRight → (s.lbl ⟨j+1, hj⟩).isRight →
    G (ψ j * e (Seq.map c s)) = 0
  unordered : ∀ s : Seq μ, ¬ IsRedOrdered s → G (e (Seq.map c s)) = 0
  violated : ∀ s : Seq μ, IsRedOrdered s → IsViolated s → G (e (Seq.map c s)) = 0

section
variable (G : KLRAlgebra k (stendhalQ Q Λ)
  ((stendhalWeight m ν).map (Sum.map (id : I → I) f)) →ₙₐ[k] C)
include hf

private def pulled : KLRAlgebra k (stendhalQ Q (Λ ∘ f)) μ →ₙₐ[k] C :=
  G.comp (relabelEquiv ρ).toAlgHom.toNonUnitalAlgHom

local notation "g" => pulled Q Λ f hf ν G

private theorem pulled_apply (z : KLRAlgebra k (stendhalQ Q (Λ ∘ f)) μ) :
    g z = G (relabelEquiv ρ z) := rfl

private theorem pulled_one_idem : IsIdempotentElem (g 1) := by
  unfold IsIdempotentElem; rw [← map_mul, one_mul]

private def pulledCorner :
    KLRAlgebra k (stendhalQ Q (Λ ∘ f)) μ →ₐ[k] (pulled_one_idem Q Λ f hf ν G).Corner where
  toFun a := KLR.Corner.mk (g a) (by rw [← map_mul, ← map_mul, one_mul, mul_one])
  map_zero' := Subtype.ext (map_zero (g))
  map_add' a b := Subtype.ext (map_add (g) a b)
  map_mul' a b := Subtype.ext (map_mul (g) a b)
  map_one' := rfl
  commutes' r := Subtype.ext (by
    change g (algebraMap k _ r) = r • g 1
    rw [← map_smul, Algebra.smul_def, mul_one])

private theorem pulledCorner_val (a : KLRAlgebra k (stendhalQ Q (Λ ∘ f)) μ) :
    (pulledCorner Q Λ f hf ν G a).val = G (relabelEquiv ρ a) := rfl

private theorem relabel_e' (s : Seq μ) : relabelEquiv ρ (e s) = e (Seq.map c s) :=
  relabelHom_e _ _

private theorem relabel_x' (a : Fin (μ).card) :
    relabelEquiv ρ (x a) = x (Fin.cast (Multiset.card_map c μ).symm a) :=
  relabelHom_x _ _

private theorem relabel_ψ' (j : ℕ) : relabelEquiv ρ (ψ j) = ψ j :=
  relabelHom_ψ _ _

private theorem pulledCorner_relations (hG : RedSubfamilyRelations Q Λ f ν G) :
    TensorRepresentationRelations (pulledCorner Q Λ f hf ν G) where
  red_dot a s ha := KLR.Corner.ext (by
    rw [pulledCorner_val Q Λ f hf ν G, map_mul, relabel_x' Q Λ f hf ν, relabel_e' Q Λ f hf ν]
    exact hG.red_dot s a ha)
  red_cross j hj s ha hb := KLR.Corner.ext (by
    rw [pulledCorner_val Q Λ f hf ν G, map_mul, relabel_ψ' Q Λ f hf ν, relabel_e' Q Λ f hf ν]
    exact hG.red_cross j hj s ha hb)
  unordered s hs := KLR.Corner.ext (by
    rw [pulledCorner_val Q Λ f hf ν G, relabel_e' Q Λ f hf ν]
    exact hG.unordered s hs)
  violated s hs hv := KLR.Corner.ext (by
    rw [pulledCorner_val Q Λ f hf ν G, relabel_e' Q Λ f hf ν]
    exact hG.violated s hs hv)

end

/-- The inclusion of a corner, as a multiplicative `k`-linear map. -/
private def cornerValAlg {A : Type*} [Ring A] [Algebra k A] {E : A} (idem : IsIdempotentElem E) :
    idem.Corner →ₙₐ[k] A where
  toFun a := a.val
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl

variable {Q Λ f hf ν}

/-- **Universal property of the red-subfamily projection** (Webster, arXiv:1309.3796v3,
Definitions 4.5–4.7). A multiplicative linear map out of the ambient KLR algebra of a red
subfamily which satisfies the red relations factors through the projection onto the tensor
product algebra. -/
theorem exists_redSubfamilyProjection_factor (G : KLRAlgebra k S ((μ).map c) →ₙₐ[k] C)
    (hG : RedSubfamilyRelations Q Λ f ν G) :
    ∃ G' : TensorProductAlgebra k Q (Λ ∘ f) ν →ₙₐ[k] C,
      ∀ z, G z = G' (redSubfamilyProjection Q Λ f hf ν z) := by
  have hrel := pulledCorner_relations Q Λ f hf ν G hG
  let L := tensorRepresentationLift (pulledCorner Q Λ f hf ν G) hrel
  refine ⟨(cornerValAlg (pulled_one_idem Q Λ f hf ν G)).comp L.toNonUnitalAlgHom, ?_⟩
  intro z
  obtain ⟨w, rfl⟩ := (relabelEquiv ρ).surjective z
  have hL := congrArg (fun φ => (φ w).val)
    (tensorRepresentationLift_comp (pulledCorner Q Λ f hf ν G) hrel)
  simp only [AlgHom.comp_apply] at hL
  change G (relabelEquiv ρ w) = (L _).val
  rw [← pulledCorner_val Q Λ f hf ν G w, ← hL]
  simp only [redSubfamilyProjection, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.symm_apply_apply]
  rfl

end Categorification.Stendhal

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.CornerSimple
import Categorification.WeightedKLR.RedStrands.LastRedLayerClasses

/-!
# Simple tops detected on a last-red layer

Webster, arXiv:1309.3796v2, §4.7, proof of Theorem 4.38. For a fixed
split of black content, restricting a simple top to the corresponding
corner detects its shift class whenever the restriction is nonzero.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR Categorification.Graded
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type*} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ+1) → I →₀ ℕ)
  {ν θ β : Multiset I} (G : GradingDatum (stendhalQ Q Λ))
  (p : Fin (stendhalWeight (ℓ+1) ν).card)
  (h : stendhalWeight (ℓ+1) θ + β.map Sum.inl = stendhalWeight (ℓ+1) ν)
  (ha : (stendhalWeight (ℓ+1) θ).card = p.val+1)
local notation "L" => TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) θ
local notation "Rfin" => CycKLR k Q (fun i => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i) β
local notation "B" => (L ⊗[k] Rfin)
local notation "Layer" => IsIdempotentElem.Corner (lastRedLayerIdem_idem Q Λ p h)
local instance detectedCornerRing : Ring Layer := _root_.instRingCorner _ _
local notation "φ" => lastRedLayerTensor Q Λ p h ha
local notation "𝓑" => tensorGrading (tensorProductGrade (restrictRedGrading Q Λ G) θ)
  (CycKLR.grade (restrictBlackGrading Q Λ G) (Λ (Fin.last ℓ)) β)
local notation "Cₚ" => RingCon.Quotient (TwoSidedIdeal.ringCon (smallerSuffixIdeal Q Λ p))
local notation "Eₚ" => lastRedLayerIdem Q Λ p h
local notation "𝓒" => lastRedLayerGrade Q Λ G p

/-- Juxtaposition viewed in the entire quotient by smaller suffixes. Its
image is the corner cut out by the fixed split of the black content. -/
def lastRedLayerAction : B →ₙₐ[k] Cₚ where
  toFun z := (φ z).1
  map_zero' := congrArg Subtype.val (map_zero (φ))
  map_add' a b := congrArg Subtype.val (map_add (φ) a b)
  map_mul' a b := congrArg Subtype.val (map_mul (φ) a b)
  map_smul' c a := (congrArg Subtype.val (map_smul (φ) c a)).trans
    ((IsIdempotentElem.cornerVal (R := k) (lastRedLayerIdem_idem Q Λ p h)).map_smul _ _)

local notation "ψ" => lastRedLayerAction Q Λ p h ha

/-- On the fixed split, an indecomposable projective of the layer quotient is
determined up to shift by its simple top restricted to the two factors. -/
def lastRedLayerClassEmbedding {D : QuantumGroup.CartanDatum I} (hQ : IsRouquierQ D Q) :
    let := tensorProductAlgebra_finite Λ ν hQ
    let := Module.Finite.of_surjective (R := k) ((smallerSuffixIdeal Q Λ p).ringCon.mkₐ k).toLinearMap
      (RingCon.mkₐ_surjective (α := k) (smallerSuffixIdeal Q Λ p).ringCon)
    let := HasGdim.of_finiteDimensional 𝓒
    {s : GProj.IndecClass 𝓒 // Nontrivial (boundaryFixed ψ s.top)} ↪ GProj.IndecClass 𝓑 := by
  dsimp only
  let := tensorProductAlgebra_finite Λ ν hQ
  let := Module.Finite.of_surjective (R := k) ((smallerSuffixIdeal Q Λ p).ringCon.mkₐ k).toLinearMap
    (RingCon.mkₐ_surjective (α := k) (smallerSuffixIdeal Q Λ p).ringCon)
  let := HasGdim.of_finiteDimensional 𝓒
  let := lastRedLayerSource_finite hQ (Λ ∘ Fin.castSucc) θ (Λ (Fin.last ℓ)) β
  let := HasGdim.of_finiteDimensional 𝓑
  apply boundaryClassEmbedding
  · intro d z hz
    exact lastRedLayerTensor_mem_grade Q Λ G p h ha hz
  · intro a
    have hOne : ψ 1 = Eₚ := congrArg Subtype.val (map_one (φ))
    have he := (lastRedLayerIdem_idem Q Λ p h).eq
    have hmem : Eₚ * a * Eₚ ∈ Subsemigroup.corner Eₚ := by
      apply (Subsemigroup.mem_corner_iff (lastRedLayerIdem_idem Q Λ p h)).2
      constructor
      · simp only [← mul_assoc, he]
      · simp only [mul_assoc, he]
    obtain ⟨b, hb⟩ := lastRedLayerTensor_surjective Q Λ p h ha ⟨_, hmem⟩
    exact ⟨b, (congrArg Subtype.val hb).trans (by rw [hOne])⟩

end Categorification.Stendhal

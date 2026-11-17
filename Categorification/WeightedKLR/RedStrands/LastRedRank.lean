/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Rouquier.PolynomialDegree
import Categorification.WeightedKLR.RedStrands.LastRedDetectedClasses
import Categorification.WeightedKLR.RedStrands.LastRedQuotientClasses
import Categorification.WeightedKLR.RedStrands.LastRedSupport

/-!
# The last-red rank bound

Webster, arXiv:1309.3796v2, §4.7, upper-bound step in the proof of Theorem
4.38. Assign each simple top a surviving last-red position furthest to the
right and a weight split there. The smaller-suffix quotient acts on the
whole top. For a common split, restriction to its corner distinguishes the
simple tops. The tensor product presentation then bounds the number of
projective shift classes by the sum of products for the two factors.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR Categorification.Graded GProj
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type*} [Field k] {ℓ : ℕ}
    {Q : I → I → MvPolynomial (Fin 2) k} {D : QuantumGroup.CartanDatum I}
    (Λ : Fin (ℓ+1) → I →₀ ℕ) (ν : Multiset I) (hQ : IsRouquierQ D Q)
    (G : GradingDatum (stendhalQ Q Λ))

/-- Division of the black content between the prefix and the final cyclotomic block. -/
abbrev LastRedWeightSplit (ν : Multiset I) := {u : Multiset I × Multiset I // u.1+u.2=ν}

variable (u : LastRedWeightSplit ν)

omit [DecidableEq I] in
/-- Position of the last red strand in this split. -/
def LastRedWeightSplit.position (ℓ : ℕ) : Fin (stendhalWeight (ℓ+1) ν).card :=
  ⟨u.1.1.card+ℓ, by
    have hc := congrArg Multiset.card u.2
    simp only [Multiset.card_add] at hc
    simp [stendhalWeight]
    omega⟩

omit [DecidableEq I] in
/-- Concatenating the augmented prefix and black suffix recovers the whole weight. -/
theorem LastRedWeightSplit.content (ℓ : ℕ) :
    stendhalWeight (ℓ+1) u.1.1 + u.1.2.map Sum.inl = stendhalWeight (ℓ+1) ν := by
  conv_rhs => rw [← u.2]
  simp only [stendhalWeight, Multiset.map_add]
  ac_rfl

omit [DecidableEq I] in
/-- The augmented prefix ends at the last red position. -/
theorem LastRedWeightSplit.length (ℓ : ℕ) :
    (stendhalWeight (ℓ+1) u.1.1).card = (LastRedWeightSplit.position ν u ℓ).val+1 := by
  simp [stendhalWeight, LastRedWeightSplit.position, Nat.add_assoc]

local notation "P" => LastRedWeightSplit.position ν u ℓ
local notation "HW" => LastRedWeightSplit.content ν u ℓ
local notation "HL" => LastRedWeightSplit.length ν u ℓ
local notation "J" => smallerSuffixIdeal Q Λ P
local notation "𝓒" => lastRedLayerGrade Q Λ G P
local notation "𝓐" => tensorProductGrade G ν
local notation "T" => TensorProductAlgebra k Q Λ ν
local notation "E" => lastRedLayerIdem Q Λ P HW
local notation "ψ" => lastRedLayerAction Q Λ P HW HL

/-- The pair of projective shift classes contributed by a given weight split. -/
abbrev LastRedFactorClasses :=
  IndecClass (tensorProductGrade (restrictRedGrading Q Λ G) u.1.1) ×
    IndecClass (CycKLR.grade (restrictBlackGrading Q Λ G) (Λ (Fin.last ℓ)) u.1.2)

private def detectedClasses := {c : IndecClass 𝓒 // Nontrivial (boundaryFixed ψ c.top)}

private def detectedPairEmbedding : detectedClasses Λ ν G u ↪ LastRedFactorClasses Λ ν G u :=
  (lastRedLayerClassEmbedding Q Λ G P HW HL hQ).trans
    (lastRedLayerSourceIndecClassEquiv hQ (Λ ∘ Fin.castSucc) u.1.1 (Λ (Fin.last ℓ)) u.1.2
      (restrictRedGrading Q Λ G) (restrictBlackGrading Q Λ G)).toEmbedding

private def detectedTop (s : IndecClass 𝓐) (v : Σ u : LastRedWeightSplit ν, detectedClasses Λ ν G u) : Prop :=
  RestrictsToTop ((smallerSuffixIdeal Q Λ (LastRedWeightSplit.position ν v.1 ℓ)).ringCon.mkₐ k) s v.2.1

include hQ in
private theorem exists_detectedTop (s : IndecClass 𝓐) :
    ∃ v, detectedTop Λ ν G s v := by
  let := tensorProductAlgebra_finite Λ ν hQ
  let := HasGdim.of_finiteDimensional 𝓐
  let := (IndecClass.isGradedSimple_top s).nontrivial
  let ρ : T →ₐ[k] Module.End k s.top := Algebra.lsmul k k s.top
  obtain ⟨p,θ,β,h,σ,hν,ha,hσ,hne⟩ := exists_detecting_lastRedCorner ρ
  let u : LastRedWeightSplit ν := ⟨(θ,β),hν⟩
  have hp : LastRedWeightSplit.position ν u ℓ = p := by
    apply Fin.ext
    change θ.card + ℓ = p.val
    simp [stendhalWeight] at ha
    omega
  subst p
  let q := (smallerSuffixIdeal Q Λ (LastRedWeightSplit.position ν u ℓ)).ringCon.mkₐ k
  let 𝓠 := lastRedLayerGrade Q Λ G (LastRedWeightSplit.position ν u ℓ)
  let := Module.Finite.of_surjective (R := k) q.toLinearMap (RingCon.mkₐ_surjective (α := k) (smallerSuffixIdeal Q Λ (LastRedWeightSplit.position ν u ℓ)).ringCon)
  let := HasGdim.of_finiteDimensional 𝓠
  have hlift (d : ℤ) (z) (hz : z ∈ 𝓠 d) : ∃ a ∈ 𝓐 d, q a=z := Submodule.mem_map.mp hz
  obtain ⟨c,hc,w,hw,he⟩ := exists_restrictsToTop (𝒜 := 𝓐) (𝒞 := 𝓠) q s σ hσ hlift _
    (lastRedLayerIdem_idem Q Λ (LastRedWeightSplit.position ν u ℓ) h) hne
  let ψ' := lastRedLayerAction Q Λ (LastRedWeightSplit.position ν u ℓ) (LastRedWeightSplit.content ν u ℓ) (LastRedWeightSplit.length ν u ℓ)
  have hone : ψ' 1 = lastRedLayerIdem Q Λ (LastRedWeightSplit.position ν u ℓ) h :=
    congrArg (fun z : (lastRedLayerIdem_idem Q Λ (LastRedWeightSplit.position ν u ℓ) h).Corner => z.val)
      (map_one (lastRedLayerTensor Q Λ (LastRedWeightSplit.position ν u ℓ) h ha))
  have hfix : ψ' 1 • w = w := by rw [hone]; exact he
  let w' : boundaryFixed ψ' c.top := ⟨w,hfix⟩
  have hn : Nontrivial (boundaryFixed ψ' c.top) := ⟨⟨w',0,fun hzero => hw (congrArg Subtype.val hzero)⟩⟩
  exact ⟨⟨u,⟨c,hn⟩⟩,hc⟩

/-- The upper rank bound in Webster, arXiv:1309.3796v2, §4.7, proof of
Theorem 4.38. Over any field with the Rouquier parameters, the global
projective shift classes inject into the disjoint union, over black-weight
splits, of pairs of shift classes from the shorter red family and the
ordinary cyclotomic algebra for the final weight. -/
def lastRedRankEmbedding :
    IndecClass 𝓐 ↪ Σ u : LastRedWeightSplit ν, LastRedFactorClasses Λ ν G u := by
  classical
  let := tensorProductAlgebra_finite Λ ν hQ
  let := HasGdim.of_finiteDimensional 𝓐
  let pick (s : IndecClass 𝓐) := (exists_detectedTop Λ ν hQ G s).choose
  have hinj : Function.Injective pick := by
    intro s t he
    have hs := (exists_detectedTop Λ ν hQ G s).choose_spec
    have ht := (exists_detectedTop Λ ν hQ G t).choose_spec
    change detectedTop Λ ν G s (pick s) at hs
    change detectedTop Λ ν G t (pick t) at ht
    rw [he] at hs
    exact RestrictsToTop.inj _ hs ht
  exact (Function.Embedding.mk pick hinj).trans
    (Function.Embedding.sigmaMap (Function.Embedding.refl _) (detectedPairEmbedding Λ ν hQ G))


include hQ in
/-- The integral Laurent rank of the tensor block is bounded by the sum,
over black-content splits, of the products of the earlier tensor-block rank
and the final cyclotomic rank (Webster, arXiv:1309.3796v2, proof of Theorem
4.38). -/
theorem lastRedK0_rank_le : Module.rank (LaurentPolynomial ℤ) (K0 𝓐) ≤
    Cardinal.sum (fun u : LastRedWeightSplit ν =>
      Module.rank (LaurentPolynomial ℤ) (K0 (tensorProductGrade (restrictRedGrading Q Λ G) u.1.1)) *
      Module.rank (LaurentPolynomial ℤ) (K0 (CycKLR.grade (restrictBlackGrading Q Λ G)
        (Λ (Fin.last ℓ)) u.1.2))) := by
  let := tensorProductAlgebra_finite Λ ν hQ
  let := HasGdim.of_finiteDimensional 𝓐
  calc
    _ = Cardinal.mk (IndecClass 𝓐) := (K0.indecBasis 𝓐).mk_eq_rank''.symm
    _ ≤ Cardinal.mk (Σ u : LastRedWeightSplit ν, LastRedFactorClasses Λ ν G u) :=
      Cardinal.mk_le_of_injective (lastRedRankEmbedding Λ ν hQ G).injective
    _ = Cardinal.sum (fun u : LastRedWeightSplit ν => Cardinal.mk (LastRedFactorClasses Λ ν G u)) :=
      Cardinal.mk_sigma _
    _ = _ := by
      apply congrArg Cardinal.sum
      funext u
      let 𝓔 := tensorProductGrade (restrictRedGrading Q Λ G) u.1.1
      let 𝓕 := CycKLR.grade (restrictBlackGrading Q Λ G) (Λ (Fin.last ℓ)) u.1.2
      let := tensorProductAlgebra_finite (Λ ∘ Fin.castSucc) u.1.1 hQ
      let := CycKLR.module_finite (ν := u.1.2) (Q := Q) (fun i j hij => by
        obtain ⟨c,hc,he⟩ := hQ.polyInY_leading i j hij
        rw [he]
        exact hc.map Polynomial.C) (fun i => Polynomial.monic_X_pow (R := k) (Λ (Fin.last ℓ) i))
      let := HasGdim.of_finiteDimensional 𝓔
      let := HasGdim.of_finiteDimensional 𝓕
      change Cardinal.mk (IndecClass 𝓔 × IndecClass 𝓕) = _
      rw [Cardinal.mk_prod]
      simp only [Cardinal.lift_id, (K0.indecBasis 𝓔).mk_eq_rank'', (K0.indecBasis 𝓕).mk_eq_rank'']
      rfl

end Categorification.Stendhal

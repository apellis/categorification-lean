/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicStandardDesc
import Categorification.WeightedKLR.RedStrands.TwoPieceStandardComparison

/-!
# The prefix action on a two-piece standard module

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.21. For a red-ordered loading `t` of the first `ℓ` red strands and a black
sequence `u`, the diagrams on the first `ℓ` red strands act on the standard module
`S_{t λ_{ℓ+1} u}` of Definition 5.1 by juxtaposition with the identity on the last block. This
action satisfies the red relations of Definitions 4.5–4.7, so it factors through the tensor
product algebra `T^{λ'}` of the first `ℓ` red strands.

## Main results

* `twoPiecePrefixAction`: the action of the prefix diagrams on `S_{t λ_{ℓ+1} u}`.
* `concatLeftHom`: juxtaposition with the identity on a right block, as a non-unital map.
* `twoPiecePrefixAction_relations`: the prefix action satisfies the red relations.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR KLRAlgebra
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Kill

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} {ν : Multiset I}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}
  {s : Seq (stendhalWeight ℓ ν)} (hs : IsRedOrdered s)
  {X : Multiset (I ⊕ Fin ℓ)} (h : X = stendhalWeight ℓ ν)

local notation "Ω" => leftStandardAllOrders Q Λ s hs
local notation "ι" => StendhalAlgebraAllOrders.ofKLR k Q Λ ν

/-- A dot on a red strand acts by zero, through any reindexing of the weight. -/
theorem leftStandardAllOrders_cast_x_mul_e (w : Seq X) (b : Fin (Multiset.card X))
    (hb : (w.lbl b).isRight) :
    Ω (ι (castKLR (stendhalQ Q Λ) h (x b * e w))) = 0 := by
  subst h
  rw [castKLR_rfl, map_mul]
  change Ω (StendhalAlgebraAllOrders.x b * StendhalAlgebraAllOrders.e w) = 0
  rw [StendhalAlgebraAllOrders.x_mul_e_of_red b w hb, map_zero]

/-- A crossing of two red strands acts by zero, through any reindexing of the weight. -/
theorem leftStandardAllOrders_cast_ψ_mul_e (w : Seq X) (j : ℕ) (hj : j + 1 < Multiset.card X)
    (h₁ : (w.lbl ⟨j, by omega⟩).isRight) (h₂ : (w.lbl ⟨j + 1, hj⟩).isRight) :
    Ω (ι (castKLR (stendhalQ Q Λ) h (ψ j * e w))) = 0 := by
  subst h
  rw [castKLR_rfl, map_mul]
  change Ω (StendhalAlgebraAllOrders.ψ j * StendhalAlgebraAllOrders.e w) = 0
  rw [StendhalAlgebraAllOrders.ψ_mul_e_of_red j hj w h₁ h₂, map_zero]

/-- The idempotent of a reindexed loading acts as the idempotent of the loading. -/
theorem leftStandardAllOrders_cast_e (w : Seq X) :
    Ω (ι (castKLR (stendhalQ Q Λ) h (e w))) = Ω (StendhalAlgebraAllOrders.e (Seq.cast h w)) := by
  rw [castKLR_e]; rfl

end Kill

section Append

variable {I : Type*} {ℓ : ℕ}

/-- The left block of a red-ordered concatenation is red-ordered. -/
theorem isRedOrdered_of_append {μ μ' : Multiset (I ⊕ Fin ℓ)} {s : Seq μ} {d : Seq μ'}
    (hs : IsRedOrdered (s.append d)) : IsRedOrdered s := by
  intro a b r r' hab ha hb
  refine hs (Seq.posL μ' a) (Seq.posL μ' b) r r' (by rwa [Fin.lt_def] at hab ⊢) ?_ ?_
  · rw [Seq.lbl, Seq.append_posL]; exact ha
  · rw [Seq.lbl, Seq.append_posL]; exact hb

/-- A concatenation whose left block is violated is violated. -/
theorem isViolated_append_of_left {μ μ' : Multiset (I ⊕ Fin ℓ)} {s : Seq μ} (d : Seq μ')
    (hs : IsViolated s) : IsViolated (s.append d) := by
  obtain ⟨h0, hv⟩ := hs
  refine ⟨by simp only [Multiset.card_add]; omega, ?_⟩
  have := Seq.append_posL s d ⟨0, h0⟩
  rw [show Seq.posL μ' ⟨0, h0⟩ = ⟨0, by simp only [Multiset.card_add]; omega⟩ from
    Fin.ext rfl] at this
  rw [Seq.lbl, this]; exact hv

theorem isViolated_seqCast {μ μ' : Multiset (I ⊕ Fin ℓ)} (h : μ = μ') {s : Seq μ}
    (hs : IsViolated s) : IsViolated (Seq.cast h s) := by
  subst h; exact hs

end Append

section Juxtapose

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {C : Type*} [Ring C] [Algebra k C]

theorem concat_tmul_one_mul {μ μ' : Multiset I} {Q' : I → I → MvPolynomial (Fin 2) k}
    (a b : KLRAlgebra k Q' μ) :
    concat Q' μ μ' ((a * b) ⊗ₜ 1) = concat Q' μ μ' (a ⊗ₜ 1) * concat Q' μ μ' (b ⊗ₜ 1) := by
  rw [← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

variable (Q' : I → I → MvPolynomial (Fin 2) k) (μ μ' : Multiset I)

/-- Juxtaposition `a ↦ a ⊗ 1` on the left block, followed by an algebra map out of the
concatenated weight. It is multiplicative but not unital. -/
def concatLeftHom (G : KLRAlgebra k Q' (μ + μ') →ₐ[k] C) : KLRAlgebra k Q' μ →ₙₐ[k] C where
  toFun a := G (concat Q' μ μ' (a ⊗ₜ 1))
  map_add' a b := by rw [TensorProduct.add_tmul, map_add, map_add]
  map_smul' c a := by
    change G (concat Q' μ μ' ((c • a) ⊗ₜ 1)) = c • G (concat Q' μ μ' (a ⊗ₜ 1))
    rw [← TensorProduct.smul_tmul', LinearMap.map_smul, map_smul]
  map_zero' := by rw [TensorProduct.zero_tmul, map_zero, map_zero]
  map_mul' a b := by
    change G (concat Q' μ μ' ((a * b) ⊗ₜ 1)) =
      G (concat Q' μ μ' (a ⊗ₜ 1)) * G (concat Q' μ μ' (b ⊗ₜ 1))
    rw [concat_tmul_one_mul, map_mul]

theorem concatLeftHom_apply (G : KLRAlgebra k Q' (μ + μ') →ₐ[k] C) (a : KLRAlgebra k Q' μ) :
    concatLeftHom Q' μ μ' G a = G (concat Q' μ μ' (a ⊗ₜ 1)) := rfl

theorem concatLeftHom_e (G : KLRAlgebra k Q' (μ + μ') →ₐ[k] C) (w : Seq μ) :
    concatLeftHom Q' μ μ' G (e w) = ∑ d : Seq μ', G (e (w.append d)) := by
  rw [concatLeftHom_apply, concat_e_tmul_one, map_sum]

theorem concatLeftHom_x_mul_e (G : KLRAlgebra k Q' (μ + μ') →ₐ[k] C)
    (a : Fin (Multiset.card μ)) (w : Seq μ) :
    concatLeftHom Q' μ μ' G (x a * e w) =
      ∑ d : Seq μ', G (x (Seq.posL μ' a) * e (w.append d)) := by
  rw [concatLeftHom_apply, concat_tmul_one_mul, concat_x_tmul_one, mul_assoc,
    oneConcat_mul_concat, concat_e_tmul_one, Finset.mul_sum, map_sum]

theorem concatLeftHom_ψ_mul_e (G : KLRAlgebra k Q' (μ + μ') →ₐ[k] C) {j : ℕ}
    (hj : j + 1 < Multiset.card μ) (w : Seq μ) :
    concatLeftHom Q' μ μ' G (ψ j * e w) = ∑ d : Seq μ', G (ψ j * e (w.append d)) := by
  rw [concatLeftHom_apply, concat_tmul_one_mul, KLR.KLRAlgebra.concat_ψ_tmul_one hj, mul_assoc,
    oneConcat_mul_concat, concat_e_tmul_one, Finset.mul_sum, map_sum]

end Juxtapose

section Prefix

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ+1) → I →₀ ℕ) {θ β : Multiset I}
  {t : Seq (stendhalWeight ℓ θ)} (ht : IsRedOrdered t) (u : Seq β)

local notation "S" => stendhalQ Q Λ
local notation "α" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ)
local notation "δ" =>
  Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ)) (stendhalWeight 1 β)
local notation "H" => parabolicInputWeights_add (ℓ := ℓ) θ β
local notation "tp" => twoPieceLoading θ β t u
local notation "htp" => isRedOrdered_twoPieceLoading ht u
local notation "Z" => leftStandard Q Λ (twoPieceLoading θ β t u) (isRedOrdered_twoPieceLoading ht u)
local notation "κ" => parabolicDescAction Q Λ θ β (Algebra.lsmul k k Z)
local notation "ι" => StendhalAlgebraAllOrders.ofKLR k Q Λ (θ + β)

theorem twoPieceDescAction_apply (a : KLRAlgebra k S (α + δ)) :
    κ a = leftStandardAllOrders Q Λ tp htp (ι (castKLR S H a)) := rfl

/-- **The prefix action** on `S_{t λ_{ℓ+1} u}`: a diagram `a` on the first `ℓ` red strands acts
as the juxtaposition `a ⊗ 1` with the identity on the last block. -/
def twoPiecePrefixAction : KLRAlgebra k S α →ₙₐ[k] Module.End k Z :=
  concatLeftHom S α δ κ

theorem twoPiecePrefixAction_apply (a : KLRAlgebra k S α) :
    twoPiecePrefixAction Q Λ ht u a = κ (concat S α δ (a ⊗ₜ 1)) := rfl

theorem twoPiecePrefixAction_red_dot (s : Seq (stendhalWeight ℓ θ))
    (a : Fin (stendhalWeight ℓ θ).card) (ha : (s.lbl a).isRight) :
    twoPiecePrefixAction Q Λ ht u
      (x (Fin.cast (Multiset.card_map (addRedColor ℓ) _).symm a) *
        e (Seq.map (addRedColor ℓ) s)) = 0 := by
  rw [twoPiecePrefixAction, concatLeftHom_x_mul_e]
  refine Finset.sum_eq_zero fun d _ => leftStandardAllOrders_cast_x_mul_e htp H _ _ ?_
  rw [Seq.lbl, Seq.append_posL]
  change ((Seq.map (addRedColor ℓ) s).lbl _).isRight = true
  rw [Seq.map_lbl, Fin.cast_cast, Fin.cast_eq_self]
  simpa [addRedColor] using ha

theorem twoPiecePrefixAction_red_cross (j : ℕ) (hj : j + 1 < (stendhalWeight ℓ θ).card)
    (s : Seq (stendhalWeight ℓ θ)) (ha : (s.lbl ⟨j, by omega⟩).isRight)
    (hb : (s.lbl ⟨j + 1, hj⟩).isRight) :
    twoPiecePrefixAction Q Λ ht u (ψ j * e (Seq.map (addRedColor ℓ) s)) = 0 := by
  have hj' : j + 1 < Multiset.card α := by simpa using hj
  rw [twoPiecePrefixAction, concatLeftHom_ψ_mul_e _ _ _ _ hj']
  refine Finset.sum_eq_zero fun d _ => leftStandardAllOrders_cast_ψ_mul_e htp H _ j
    (by simp only [Multiset.card_add]; omega) ?_ ?_
  · rw [show (⟨j, _⟩ : Fin _) = Seq.posL _ ⟨j, by omega⟩ from Fin.ext rfl, Seq.lbl,
      Seq.append_posL]
    change ((Seq.map (addRedColor ℓ) s).lbl _).isRight = true
    rw [Seq.map_lbl]
    simpa [addRedColor] using ha
  · rw [show (⟨j + 1, _⟩ : Fin _) = Seq.posL _ ⟨j + 1, hj'⟩ from Fin.ext rfl, Seq.lbl,
      Seq.append_posL]
    change ((Seq.map (addRedColor ℓ) s).lbl _).isRight = true
    rw [Seq.map_lbl]
    simpa [addRedColor] using hb

theorem twoPiecePrefixAction_unordered (s : Seq (stendhalWeight ℓ θ))
    (hs : ¬IsRedOrdered s) :
    twoPiecePrefixAction Q Λ ht u (e (Seq.map (addRedColor ℓ) s)) = 0 := by
  rw [twoPiecePrefixAction, concatLeftHom_e]
  refine Finset.sum_eq_zero fun d _ => ?_
  rw [twoPieceDescAction_apply Q Λ ht, leftStandardAllOrders_cast_e]
  refine leftStandardAllOrders_e_unordered htp fun ho => hs ?_
  exact isRedOrdered_of_map_castSucc (isRedOrdered_of_append ((isRedOrdered_cast H _).1 ho))

theorem twoPiecePrefixAction_violated (s : Seq (stendhalWeight ℓ θ)) (hv : IsViolated s) :
    twoPiecePrefixAction Q Λ ht u (e (Seq.map (addRedColor ℓ) s)) = 0 := by
  rw [twoPiecePrefixAction, concatLeftHom_e]
  refine Finset.sum_eq_zero fun d _ => ?_
  rw [twoPieceDescAction_apply Q Λ ht, leftStandardAllOrders_cast_e]
  refine leftStandardAllOrders_e_violated htp (isViolated_seqCast H
    (isViolated_append_of_left d ?_))
  obtain ⟨h0, hv⟩ := hv
  exact ⟨by simpa using h0, by simpa using hv⟩

/-- The prefix action satisfies the red relations of Definitions 4.5–4.7, so it factors
through the tensor product algebra of the first `ℓ` red strands. -/
theorem twoPiecePrefixAction_relations :
    RedSubfamilyRelations Q Λ Fin.castSucc θ (twoPiecePrefixAction Q Λ ht u) where
  red_dot := twoPiecePrefixAction_red_dot Q Λ ht u
  red_cross := twoPiecePrefixAction_red_cross Q Λ ht u
  unordered := twoPiecePrefixAction_unordered Q Λ ht u
  violated s _ := twoPiecePrefixAction_violated Q Λ ht u s

end Prefix

end Categorification.Stendhal

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
* `exists_twoPiecePrefixAction_factor`: it factors through `T^{λ'}`.
* `twoPieceLastAction`: the action of the last red strand and the black strands to its right.
* `exists_twoPieceLastAction_factor`: it factors through the cyclotomic quotient
  `R^{λ_{ℓ+1}}`; the cyclotomic relation holds by equation (4.2) (`twoPiece_lastRed_dot_pow`).
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

theorem leftStandardAllOrders_cast_x_pow_mul_e (w : Seq X) (b : Fin (Multiset.card X)) (n : ℕ) :
    Ω (ι (castKLR (stendhalQ Q Λ) h (x b ^ n * e w))) =
      Ω (StendhalAlgebraAllOrders.x (Fin.cast (congrArg Multiset.card h) b) ^ n *
        StendhalAlgebraAllOrders.e (Seq.cast h w)) := by
  subst h
  rw [castKLR_rfl, map_mul, map_pow]
  rfl

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

theorem concat_e_tmul_x_pow_mul_e {J : Type*} [DecidableEq J]
    (P : J → J → MvPolynomial (Fin 2) k) {α β : Multiset J} (a : Seq α) (b : Seq β)
    (z : Fin β.card) (d : ℕ) :
    concat P α β (e a ⊗ₜ (x z ^ d * e b)) = x (Seq.posR α z) ^ d * e (a.append b) := by
  simpa [ψw, TypeA.shiftWord, pol_X] using concat_pol_ψw_e (Q := P) (1 : MvPolynomial _ k)
    (MvPolynomial.X z ^ d) (α := []) (α' := []) (by simp) (by simp) a b

theorem concat_one_tmul_x_pow_mul_e {J : Type*} [DecidableEq J]
    (P : J → J → MvPolynomial (Fin 2) k) {α β : Multiset J} (b : Seq β)
    (z : Fin β.card) (d : ℕ) :
    concat P α β (1 ⊗ₜ (x z ^ d * e b)) =
      ∑ a : Seq α, x (Seq.posR α z) ^ d * e (a.append b) := by
  rw [← sum_e, TensorProduct.sum_tmul, map_sum]
  exact Finset.sum_congr rfl fun a _ => concat_e_tmul_x_pow_mul_e P a b z d

/-- Juxtaposition `z ↦ e(w) ⊗ z` on the right block, next to a fixed idempotent of the left
block, followed by an algebra map out of the concatenated weight. -/
def concatRightHom (G : KLRAlgebra k Q' (μ + μ') →ₐ[k] C) (w : Seq μ) :
    KLRAlgebra k Q' μ' →ₙₐ[k] C where
  toFun z := G (concat Q' μ μ' (e w ⊗ₜ z))
  map_add' a b := by rw [TensorProduct.tmul_add, map_add, map_add]
  map_smul' c a := by
    change G (concat Q' μ μ' (e w ⊗ₜ (c • a))) = c • G (concat Q' μ μ' (e w ⊗ₜ a))
    rw [TensorProduct.tmul_smul, LinearMap.map_smul, map_smul]
  map_zero' := by rw [TensorProduct.tmul_zero, map_zero, map_zero]
  map_mul' a b := by
    change G (concat Q' μ μ' (e w ⊗ₜ (a * b))) =
      G (concat Q' μ μ' (e w ⊗ₜ a)) * G (concat Q' μ μ' (e w ⊗ₜ b))
    rw [← map_mul, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, e_mul_e, ite_eq_left rfl]

theorem concatRightHom_apply (G : KLRAlgebra k Q' (μ + μ') →ₐ[k] C) (w : Seq μ)
    (z : KLRAlgebra k Q' μ') :
    concatRightHom Q' μ μ' G w z = G (concat Q' μ μ' (e w ⊗ₜ z)) := rfl

theorem concatRightHom_e (G : KLRAlgebra k Q' (μ + μ') →ₐ[k] C) (w : Seq μ) (d : Seq μ') :
    concatRightHom Q' μ μ' G w (e d) = G (e (w.append d)) := by
  rw [concatRightHom_apply, concat_e_tmul_e]

theorem concatRightHom_x_mul_e (G : KLRAlgebra k Q' (μ + μ') →ₐ[k] C) (w : Seq μ)
    (b : Fin (Multiset.card μ')) (d : Seq μ') :
    concatRightHom Q' μ μ' G w (x b * e d) = G (x (Seq.posR μ b) * e (w.append d)) := by
  rw [concatRightHom_apply, ← pow_one (x b), concat_e_tmul_x_pow_mul_e, pow_one]

theorem concatRightHom_x_pow_mul_e (G : KLRAlgebra k Q' (μ + μ') →ₐ[k] C) (w : Seq μ)
    (b : Fin (Multiset.card μ')) (n : ℕ) (d : Seq μ') :
    concatRightHom Q' μ μ' G w (x b ^ n * e d) =
      G (x (Seq.posR μ b) ^ n * e (w.append d)) := by
  rw [concatRightHom_apply, concat_e_tmul_x_pow_mul_e]

theorem concatRightHom_cast_x_pow_mul_e (G : KLRAlgebra k Q' (μ + μ') →ₐ[k] C) (w : Seq μ)
    {ν : Multiset I} (h : ν = μ') (b : Fin (Multiset.card ν)) (n : ℕ) (d : Seq ν) :
    concatRightHom Q' μ μ' G w (castKLR Q' h (x b ^ n * e d)) =
      G (x (Seq.posR μ (Fin.cast (congrArg Multiset.card h) b)) ^ n *
        e (w.append (Seq.cast h d))) := by
  subst h
  rw [castKLR_rfl, concatRightHom_x_pow_mul_e]
  rfl

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

local notation "rₗ" => ({Sum.inr (Fin.last ℓ)} : Multiset (I ⊕ Fin (ℓ+1)))
local notation "B₀" => Multiset.map (Sum.inl : I → I ⊕ Fin (ℓ+1)) β
local notation "hB" => lastRedBlackWeight (ℓ := ℓ) β

/-- **The last-block action** on `S_{t λ_{ℓ+1} u}`: a diagram `z` on the last red strand and the
black strands to its right acts as the juxtaposition `e(t) ⊗ z`. -/
def twoPieceLastAction : KLRAlgebra k S (rₗ + B₀) →ₙₐ[k] Module.End k Z :=
  (concatRightHom S α δ κ (Seq.map (addRedColor ℓ) t)).comp
    (castKLR S hB).toAlgHom.toNonUnitalAlgHom

theorem twoPieceLastAction_apply (z : KLRAlgebra k S (rₗ + B₀)) :
    twoPieceLastAction Q Λ ht u z =
      κ (concat S α δ (e (Seq.map (addRedColor ℓ) t) ⊗ₜ castKLR S hB z)) := rfl

theorem twoPieceLastAction_violated (d : Seq (rₗ + B₀)) (hd : IsViolated d) :
    twoPieceLastAction Q Λ ht u (e d) = 0 := by
  change concatRightHom S α δ κ _ (castKLR S hB (e d)) = 0
  rw [castKLR_e, concatRightHom_e, twoPieceDescAction_apply Q Λ ht, leftStandardAllOrders_cast_e]
  exact leftStandardAllOrders_e htp
    (stendhalLT_twoPiece_concatLoading_violated t u (isViolated_seqCast hB hd))

theorem twoPieceLastAction_red_dot (a : Fin (rₗ + B₀).card) (d : Seq (rₗ + B₀))
    (ha : (d.1 a).isRight) : twoPieceLastAction Q Λ ht u (x a * e d) = 0 := by
  change concatRightHom S α δ κ _ (castKLR S hB (x a * e d)) = 0
  rw [map_mul, castKLR_x, castKLR_e, concatRightHom_x_mul_e]
  refine leftStandardAllOrders_cast_x_mul_e htp H _ _ ?_
  rw [Seq.lbl, Seq.append_posR, Seq.cast_apply]
  rwa [Fin.cast_cast, Fin.cast_eq_self]

/-- A dot power at the first black strand after the last red kills `S_{t λ_{ℓ+1} u}` on loadings
above `t λ_{ℓ+1} u`: by equation (4.2) it factors through a strictly higher loading. -/
theorem twoPiece_lastRed_dot_pow (s : Seq (stendhalWeight (ℓ+1) (θ + β))) (j : ℕ)
    (h : j + 1 < Multiset.card (stendhalWeight (ℓ+1) (θ + β))) (i : I)
    (hr : s.lbl ⟨j, by omega⟩ = .inr (Fin.last ℓ)) (hi : s.lbl ⟨j+1, h⟩ = .inl i)
    (hle : StendhalLE tp s) :
    leftStandardAllOrders Q Λ tp htp (StendhalAlgebraAllOrders.x ⟨j+1, h⟩ ^ Λ (Fin.last ℓ) i *
      StendhalAlgebraAllOrders.e s) = 0 := by
  have hlt := stendhalLT_sadj h hr hi fun d hd => lbl_eq_inr_unique hd hr
  have hlt' : StendhalLT tp (TypeA.sadj _ j • s) :=
    ⟨fun R i => le_trans (hle R i) (hlt.1 R i),
      fun hc => hlt.2 fun R i => le_trans (hc R i) (hle R i)⟩
  rw [lastRed_dot_pow_factor Q Λ s j h i hr hi, map_mul, map_mul,
    leftStandardAllOrders_e htp hlt', mul_zero, zero_mul]

theorem twoPieceLastAction_cyc (b : Seq β) :
    twoPieceLastAction Q Λ ht u (concat S rₗ B₀ (1 ⊗ₜ blackSuffixReindex Q Λ β
      (cycElt Q (fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i) b))) = 0 := by
  by_cases hb : 0 < β.card
  · let z : Fin β.card := ⟨0, hb⟩
    have hx : blackSuffixReindex Q Λ β (x z) =
        x (Fin.cast (Multiset.card_map Sum.inl β).symm z) := reindexEquiv_x _ z
    have he : blackSuffixReindex Q Λ β (e b) = e (Seq.map Sum.inl b) := reindexEquiv_e _ b
    rw [cycElt_of_pos _ _ _ hb, map_pow, Polynomial.aeval_X, map_mul, map_pow, hx, he,
      concat_one_tmul_x_pow_mul_e, map_sum]
    refine Finset.sum_eq_zero fun a _ => ?_
    change concatRightHom S α δ κ _ (castKLR S hB (_ * _)) = 0
    rw [concatRightHom_cast_x_pow_mul_e, twoPieceDescAction_apply Q Λ ht,
      leftStandardAllOrders_cast_x_pow_mul_e]
    have hα : Multiset.card α = Multiset.card (stendhalWeight ℓ θ) := Multiset.card_map _ _
    have hm : Multiset.card α + 1 < Multiset.card (stendhalWeight (ℓ+1) (θ + β)) := by
      have h1 := congrArg Multiset.card H
      have h2 := congrArg Multiset.card hB
      simp only [Multiset.card_add, Multiset.card_singleton, Multiset.card_map] at h1 h2 ⊢
      omega
    have hc : Fin.cast (congrArg Multiset.card H) (Seq.posR α (Fin.cast
        (congrArg Multiset.card hB) (Seq.posR rₗ (Fin.cast
          (Multiset.card_map Sum.inl β).symm z)))) = ⟨Multiset.card α + 1, hm⟩ := by
      ext
      simp only [Fin.val_cast, Seq.posR_val, z, Multiset.card_singleton]
    rw [hc]
    refine twoPiece_lastRed_dot_pow Q Λ ht u _ _ hm _ ?_ ?_
      (stendhalLE_twoPiece_concatLoading u (fun _ _ => le_rfl) _)
    · have ha : a.1 ⟨0, by simp⟩ = .inr (Fin.last ℓ) := by
        have hm := Multiset.mem_map_of_mem a.1 (Finset.mem_univ_val (⟨0, by simp⟩ : Fin (Multiset.card rₗ)))
        rw [a.2] at hm
        exact Multiset.mem_singleton.1 hm
      rw [Seq.lbl, Seq.cast_apply,
        show Fin.cast _ (⟨Multiset.card α, _⟩ : Fin _) = Seq.posR α ⟨0, by simp [stendhalWeight]⟩ from
          Fin.ext (by simp), Seq.append_posR, Seq.cast_apply]
      exact (Seq.append_posL a (Seq.map Sum.inl b) ⟨0, by simp⟩).trans ha
    · rw [← hc, Seq.lbl, Seq.cast_apply, Fin.cast_cast, Fin.cast_eq_self, Seq.append_posR,
        Seq.cast_apply, Fin.cast_cast, Fin.cast_eq_self, Seq.append_posR]
      rfl
  · have h0 : cycElt Q (fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i) b = 0 :=
      dite_eq_right hb
    simp only [h0, map_zero, TensorProduct.tmul_zero]

/-- The prefix action factors through the tensor product algebra `T^{λ'}` of the first `ℓ` red
strands. -/
theorem exists_twoPiecePrefixAction_factor :
    ∃ G' : TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) θ →ₙₐ[k] Module.End k Z,
      ∀ z, twoPiecePrefixAction Q Λ ht u z =
        G' (redSubfamilyProjection Q Λ Fin.castSucc (Fin.castSucc_injective ℓ) θ z) :=
  exists_redSubfamilyProjection_factor _ (twoPiecePrefixAction_relations Q Λ ht u)

/-- The last-block action factors through the cyclotomic quotient `R^{λ_{ℓ+1}}`. -/
theorem exists_twoPieceLastAction_factor :
    ∃ G' : CycKLR k Q (fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i) β
        →ₙₐ[k] Module.End k Z,
      ∀ z, twoPieceLastAction Q Λ ht u z = G' (parabolicLastCyclotomic Q Λ β (castKLR S hB z)) :=
  exists_lastRedBlack_factor _ (twoPieceLastAction_violated Q Λ ht u)
    (twoPieceLastAction_red_dot Q Λ ht u) (twoPieceLastAction_cyc Q Λ ht u)

end Prefix

end Categorification.Stendhal

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.RedFirstBaseCrossing
import Categorification.WeightedKLR.RedStrands.RedBlackCrossingFrame

/-!
# Rightmost red–black crossing on an ordered projective

Webster, arXiv:1309.3796v2, Lemma 5.23, used at (6.21).
The single crossing at the right edge acts injectively with any earlier red prefix.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA InductionAlong QuantumGroup KL3.Diagram
open scoped TensorProduct

variable {I k : Type} [decI : DecidableEq I] [Field k]
  {C : CartanDatum I}

local notation "QL" => CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)
local notation "Si" i:max => (Singleton.singleton i : Multiset I)

/-- The top loading ending in black, red belongs to the bottom Mackey block. -/
private theorem cast_rightmost_blackRedLoading_mem_botSet
    {ℓ : ℕ} {a b : Multiset (I ⊕ Fin (ℓ + 1))} (i : I) (θ : Multiset I)
    (u : Seq (stendhalWeight ℓ (θ + 0)))
    (w : a + b + {Sum.inl i} = stendhalWeight (ℓ + 1) (Si i + (θ + 0)))
    (hb₁ : b.card = 1) (hb : ∀ r ∈ b, r = Sum.inr (Fin.last ℓ)) :
    Seq.cast w.symm (appendRedLoading (appendBlackLoading i (θ + 0) u)) ∈
      botSet (firstQuad_h a b (Sum.inl i)) := by
  let s := appendRedLoading (appendBlackLoading i (θ + 0) u)
  let j : I ⊕ Fin (ℓ + 1) := .inl i
  let h := firstQuad_h a b j
  let z := seqCast h.symm (Seq.cast w.symm s)
  have hlen := congrArg Multiset.card (h.trans w)
  have hz : z ∈ concatSet (a + {j}) b := by
    rw [mem_concatSet_iff_hasTail hb]
    refine ⟨by simp [hb₁], ?_⟩
    intro p hp
    have hlast : s.lbl (lastRedPosition ℓ (Si i + (θ + 0))) = Sum.inr (Fin.last ℓ) :=
      hasLastRed_appendRedLoading (appendBlackLoading i (θ + 0) u)
    change (seqCast h.symm (Seq.cast w.symm s)).1 p = _
    rw [seqCast_apply, Seq.cast_apply]
    convert hlast using 1
    change s.lbl _ = s.lbl _
    apply congrArg s.lbl
    apply Fin.ext
    have hp' := hlen.ge.trans hp
    have hpl := p.isLt.trans_le hlen.le
    rw [hb₁] at hp'
    simp [stendhalWeight] at hp' hpl
    simp only [Fin.val_cast, lastRedPosition, Multiset.card_add, Multiset.card_singleton, add_zero]
    omega
  refine Finset.mem_image.2 ⟨z, hz, ?_⟩
  simp only [z, seqCast_eq_cast, Seq.cast_cast_symm, s]

/-- The bottom loading ending in red, black belongs to the singleton-black block. -/
private theorem cast_rightmost_redBlackLoading_mem_concatSet
    {ℓ : ℕ} {a b : Multiset (I ⊕ Fin (ℓ + 1))} (i : I) (θ : Multiset I)
    (u : Seq (stendhalWeight ℓ (θ + 0)))
    (w : a + b + {Sum.inl i} = stendhalWeight (ℓ + 1) (Si i + (θ + 0))) :
    Seq.cast w.symm (appendBlackLoading i (θ + 0) (appendRedLoading u)) ∈
      concatSet (a + b) {Sum.inl i} := by
  rw [mem_concatSet_singleton_iff, Seq.cast_apply]
  apply appendBlackLoading_lbl_of_eq
  change (a + b).card = (stendhalWeight (ℓ + 1) (θ + 0)).card
  have hlen := congrArg Multiset.card w
  simp [stendhalWeight] at hlen ⊢
  omega

section Last

variable {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I) (θ : Multiset I)
  (u : Seq (stendhalWeight ℓ (θ + 0)))

local notation "ν" => (Si i + (θ + 0))
local notation "s" => appendRedLoading (appendBlackLoading i (θ + 0) u)
local notation "t" => appendBlackLoading i (θ + 0) (appendRedLoading u)
local notation "a" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ)
local notation "b" => Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ))
  (stendhalWeight 1 (0 : Multiset I))
local notation "j" => (Sum.inl i : I ⊕ Fin (ℓ + 1))
local notation "w" => firstInd_klrWeight (ℓ := ℓ) i θ 0
local notation "s'" => Seq.cast (Eq.symm w) s
local notation "t'" => Seq.cast (Eq.symm w) t

omit [DecidableEq I] in
private theorem firstFactorCrossingIndex : (a).card = (stendhalWeight ℓ (θ + 0)).card := by
  simp [stendhalWeight]

omit [DecidableEq I] in
private theorem firstFactorSwap : sadj (a + b + {j}).card (a).card • s' = t' := by
  have hb : (b).card = 1 := by simp [stendhalWeight]
  rw [← quadPerm_firstQuad_eq_sadj a b j hb]
  have h := congrArg (Seq.cast (Eq.symm w)) (cast_quadPerm_smul_base i θ u)
  rwa [Seq.cast_symm_cast] at h

end Last

/-- Right multiplication by the oriented crossing at the last two positions is injective on
its source loading projective at the standard Khovanov–Lauda parameters. -/
theorem eq_zero_of_mul_rightmostRedCrossing
    (hR : IsRouquierQ C QL) (hQs : KLRSymm QL)
    {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I) (θ : Multiset I)
    (u : Seq (stendhalWeight ℓ (θ + 0))) (hu : IsRedOrdered u)
    (x : TensorProductAlgebra k QL Λ (Si i + (θ + 0)))
    (hx : x * tensorOfKLR QL Λ _ (e (appendRedLoading (appendBlackLoading i (θ + 0) u))) = x)
    (h0 : x * tensorOfKLR QL Λ _ (ψ (stendhalWeight ℓ (θ + 0)).card *
      e (appendBlackLoading i (θ + 0) (appendRedLoading u))) = 0) : x = 0 := by
  let d : DecidableEq I := fun a b => Classical.propDecidable (a = b)
  have hd : decI = d := Subsingleton.elim _ _
  subst decI
  let _ : DecidableEq I := d
  let A := Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ)
  let B := Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ))
    (stendhalWeight 1 (0 : Multiset I))
  let j : I ⊕ Fin (ℓ + 1) := .inl i
  let G := firstG (stendhalQ QL Λ) A B j
  let s := appendRedLoading (appendBlackLoading i (θ + 0) u)
  let t := appendBlackLoading i (θ + 0) (appendRedLoading u)
  have hs : IsRedOrdered s := (appendRedLoading_ordered_iff _).2
    (appendBlackLoading_ordered i (θ + 0) u hu)
  have hsrc : redCrossIdem QL Λ i θ u hu = tensorOfKLR QL Λ _ (e s) := by
    rw [redCrossIdem_eq]
    exact (tensorOfKLR_e_of_ordered _ _ hs).symm
  have hb : B.card = 1 := by simp [B, stendhalWeight]
  have hframe := e_mul_firstG_eq_ψ_mul_e_of_singleton (stendhalQ QL Λ) A B j hb
    (Seq.cast (firstInd_klrWeight (ℓ := ℓ) i θ 0).symm s)
    (Seq.cast (firstInd_klrWeight (ℓ := ℓ) i θ 0).symm t)
    (cast_rightmost_blackRedLoading_mem_botSet i θ u (firstInd_klrWeight (ℓ := ℓ) i θ 0) hb
      (by simp [stendhalWeight]))
    (cast_rightmost_redBlackLoading_mem_concatSet i θ u (firstInd_klrWeight (ℓ := ℓ) i θ 0)) (firstFactorSwap i θ u)
  have hclip : redCrossIdem QL Λ i θ u hu * firstIndAffine QL Λ i θ 0 G =
      tensorOfKLR QL Λ _ (ψ (stendhalWeight ℓ (θ + 0)).card * e t) := by
    have he : redCrossIdem QL Λ i θ u hu = redLoadingIdem QL Λ _ s hs :=
      redCrossIdem_eq QL Λ i θ u hu
    rw [he, ← firstIndAffine_e_cast QL Λ i θ 0 s hs, ← map_mul]
    change firstIndAffine QL Λ i θ 0 (_ * firstG _ A B j) = _
    rw [hframe, firstIndAffine_apply, map_mul, castKLR_ψ, castKLR_e, Seq.cast_cast_symm,
      show A.card = (stendhalWeight ℓ (θ + 0)).card from firstFactorCrossingIndex (I := I) θ]
  have hcross := IsRedBlackCrossing.crossing (Q := QL) Λ i θ u hu
  refine (IsRedBlackCrossing.eq_zero hR hQs hcross).2 x (by rw [hsrc]; exact hx) ?_
  change x * firstIndAffine QL Λ i θ 0 G = 0
  calc
    x * firstIndAffine QL Λ i θ 0 G =
        x * (redCrossIdem QL Λ i θ u hu * firstIndAffine QL Λ i θ 0 G) := by
      rw [← mul_assoc, hsrc, hx]
    _ = 0 := by rw [hclip]; exact h0

end Categorification.Stendhal

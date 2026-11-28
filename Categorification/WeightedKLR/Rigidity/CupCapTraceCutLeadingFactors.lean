/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapTraceCutTopOneRelabel
import Categorification.WeightedKLR.Rigidity.CupCapTraceCutSubfamilyConcat

/-!
# The head and tail factors of `R(γ) ⊗ R(δ)` at the leading Mackey data

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half, step L5 (the intertwining
of the bottom corners).

For the leading Mackey datum `q` of the outer cut of `S_+` (weight of the window) and `q'` of
the cut of `S_cut` (weight `0`), `R(q'.γ) ⊗ R(q'.δ)` acts on `E' · Res X` through the head
factor `cutPrefixProjection (ι(1 ⊗ a))` and the tail factor `cutSuffixProjection (ι(1_0 ⊗ b))`,
and `R(q.γ) ⊗ R(q.δ)` acts on `E · BlocksMid X` through the analogous factors at the outer cut
(`botCornerBlocksEquiv_smul`). Along `cutPlusRelabel` these factors agree:

* **(T) tail.** Writing `b` as the relabelling of an element `c` of the KLR algebra of the last
  block (`subfamilyRelabel`), the tail factor of `S_cut` is the image of `c` in
  `T^{λ_{j+1}…λ_ℓ}(γ)` (`cutSuffixProjection_leading_tail`); at the outer cut of `S_+`, the
  image of `ι(1_β ⊗ b)` in `T^{μ μ*; λ_{j+1}…λ_ℓ}` is `ι(1 ⊗ tailLift c)` of the two inner blocks
  (`cutSuffixProjection_plus_tail`), and the inner block projection of `tailLift c` is again
  the image of `c` (`relabel_cutSuffixProjection_tailLift`).
* **(H) head.** The head factor of `S_+`, relabelled along `plusBlockLabels_head`, is the head
  factor of `S_cut` (`relabel_cutPrefixProjection_leading_head`). This generalizes
  `relabel_botHeadIdem_eq_cutBotHeadIdem` (the case `a = 1`).

All of these are instances of `redSubfamilyProjection_castAlg_concat`, after composing
relabellings (`relabelHom_relabelHom`, `algHom_ext_of_gen`).

Webster's proof does not spell this out. No new hypothesis.

## Main definitions

* `Stendhal.CupCap.tailLift`.

## Main results

* `Stendhal.CupCap.cutPlusRelabel_subfamilyRelabel_tail`,
  `Stendhal.CupCap.cutSuffixProjection_leading_tail`,
  `Stendhal.CupCap.cutSuffixProjection_plus_tail`,
  `Stendhal.CupCap.relabel_cutSuffixProjection_tailLift`,
  `Stendhal.CupCap.relabel_cutPrefixProjection_leading_head`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA
open scoped TensorProduct

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ} (j : ℕ) (hj : j ≤ ℓ)
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)

local notation "φ" => cutToPlusColour (I := I) j hj
local notation "Λp" => plusBlockLabels Λ Λc j hj

/-! ### The tail -/

omit [DecidableEq I] in
/-- The parameters of the last inner block of `λ⁺` are those of the last block of `λ`. -/
theorem stendhalQ_tail_eq (a b : I ⊕ Fin (ℓ - j)) :
    stendhalQ Q (blocksTailLabels (plusBlockLabels Λ Λc j hj) ∘ Fin.natAdd 2) a b =
      stendhalQ Q (cutLabels j hj Λ ∘ Fin.natAdd j) a b := by
  rw [plusBlockLabels_tail]
  rfl

/-- **The tail element read in the two inner blocks of `λ⁺`**: an element `c` of the KLR
algebra of the last block of `λ` (weight `γ`), as an element of the KLR algebra of the last of
the inner blocks `μ μ* | λ_{j+1}…λ_ℓ`. -/
def tailLift {γ : Multiset I}
    (c : KLRAlgebra k (stendhalQ Q (cutLabels j hj Λ ∘ Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)) :
    KLRAlgebra k (stendhalQ Q (blocksTailLabels (plusBlockLabels Λ Λc j hj)))
      ((stendhalWeight (ℓ - j) γ).map (Sum.map (id : I → I) (Fin.natAdd 2))) :=
  relabelHom (redSubfamilyRelabel Q (blocksTailLabels (plusBlockLabels Λ Λc j hj)) (Fin.natAdd 2)
    (Fin.natAdd_injective _ 2) γ)
    (relabelHom (SeqRelabel.ofParams (fun a b _ => stendhalQ_tail_eq j hj Q Λ Λc a b) _) c)

omit [DecidableEq I] in
private theorem seq_map_apply {J J' : Type*} (g : J → J') {ν : Multiset J} (i : Seq ν)
    (a : Fin (Multiset.card (ν.map g))) :
    (Seq.map g i).1 a = g (i.1 (Fin.cast (Multiset.card_map g ν) a)) := rfl

omit [DecidableEq I] in
private theorem seq_tail_eq {γ : Multiset I} {δ' : Multiset (I ⊕ Fin (j + (ℓ - j)))}
    {δ : Multiset (I ⊕ Fin (j + (2 + (ℓ - j))))}
    (hδ' : (stendhalWeight (ℓ - j) γ).map (Sum.map (id : I → I) (Fin.natAdd j)) = δ')
    (hδ : δ'.map φ = δ)
    (hγ : ((stendhalWeight (ℓ - j) γ).map (Sum.map (id : I → I) (Fin.natAdd 2))).map
      (Sum.map (id : I → I) (Fin.natAdd j)) = δ)
    (i : Seq (stendhalWeight (ℓ - j) γ)) :
    seqCast hδ (Seq.map φ (seqCast hδ' (Seq.map (Sum.map (id : I → I) (Fin.natAdd j)) i))) =
      seqCast hγ (Seq.map (Sum.map (id : I → I) (Fin.natAdd j))
        (Seq.map (Sum.map (id : I → I) (Fin.natAdd 2)) i)) := by
  apply Subtype.ext
  funext a
  rw [seqCast_apply, seqCast_apply, seq_map_apply, seqCast_apply, seq_map_apply, seq_map_apply,
    seq_map_apply]
  refine (congrFun (cutToPlusColour_comp_natAdd j hj) _).trans ?_
  exact congrArg (fun y => Sum.map (id : I → I) (Fin.natAdd j)
    (Sum.map (id : I → I) (Fin.natAdd 2 : Fin (ℓ - j) → Fin (2 + (ℓ - j))) y))
    (Seq.apply_congr i (by simp))

/-- **The two relabellings of the tail element agree**: relabelling `c` into `q'.δ` and then
along `cutPlusRelabel` is relabelling `tailLift c` into `q.δ`. -/
theorem cutPlusRelabel_subfamilyRelabel_tail {γ : Multiset I}
    {δ' : Multiset (I ⊕ Fin (j + (ℓ - j)))} {δ : Multiset (I ⊕ Fin (j + (2 + (ℓ - j))))}
    (hδ' : (stendhalWeight (ℓ - j) γ).map (Sum.map (id : I → I) (Fin.natAdd j)) = δ')
    (hδ : δ'.map φ = δ)
    (hγ : ((stendhalWeight (ℓ - j) γ).map (Sum.map (id : I → I) (Fin.natAdd 2))).map
      (Sum.map (id : I → I) (Fin.natAdd j)) = δ)
    (c : KLRAlgebra k (stendhalQ Q (cutLabels j hj Λ ∘ Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)) :
    relabelHom (cutPlusRelabel j hj Q Λ Λc hδ)
        (relabelHom (subfamilyRelabel Q (cutLabels j hj Λ) (Fin.natAdd_injective _ j) hδ') c) =
      relabelHom (subfamilyRelabel Q (plusBlockLabels Λ Λc j hj) (Fin.natAdd_injective _ j) hγ)
        (tailLift j hj Q Λ Λc c) := by
  have hc : (relabelHom (cutPlusRelabel j hj Q Λ Λc hδ)).comp
      (relabelHom (subfamilyRelabel Q (cutLabels j hj Λ) (Fin.natAdd_injective _ j) hδ')) =
      (relabelHom (subfamilyRelabel Q (plusBlockLabels Λ Λc j hj)
        (Fin.natAdd_injective _ j) hγ)).comp
        ((relabelHom (redSubfamilyRelabel Q (blocksTailLabels (plusBlockLabels Λ Λc j hj))
          (Fin.natAdd 2) (Fin.natAdd_injective _ 2) γ)).comp
          (relabelHom (SeqRelabel.ofParams (fun a b _ => stendhalQ_tail_eq j hj Q Λ Λc a b) _))) :=
    algHom_ext_of_gen (fun i => by
        simp only [AlgHom.comp_apply, relabelHom_e]
        congr 1
        rw [cutPlusRelabel_equiv, subfamilyRelabel_equiv, subfamilyRelabel_equiv,
          SeqRelabel.ofParams_equiv]
        exact seq_tail_eq j hj hδ' hδ hγ i)
      (fun a => by simp [Fin.cast_cast]) (fun l => by simp)
  exact DFunLike.congr_fun hc c

/-- **(T), the cut side**: for `q'.β = 0` the tail factor of `ι_{0,q'.δ}(1 ⊗ b)` at the cut of
`S_cut`, with `b` the relabelling of `c` from the last block, is the image of `c`. -/
theorem cutSuffixProjection_leading_tail {γ : Multiset I} {β' δ' : Multiset (I ⊕ Fin (j + (ℓ - j)))}
    (hβ : β' = 0)
    (h₄ : β' + δ' = (stendhalWeight (ℓ - j) γ).map (Sum.map (id : I → I) (Fin.natAdd j)))
    (hδ' : (stendhalWeight (ℓ - j) γ).map (Sum.map (id : I → I) (Fin.natAdd j)) = δ')
    (c : KLRAlgebra k (stendhalQ Q (cutLabels j hj Λ ∘ Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)) :
    cutSuffixProjection (a := j) (r := ℓ - j) Q (cutLabels j hj Λ) γ
        (castAlg (stendhalQ Q (cutLabels j hj Λ)) h₄ (concat (stendhalQ Q (cutLabels j hj Λ)) β' δ'
          (1 ⊗ₜ relabelHom (subfamilyRelabel Q (cutLabels j hj Λ) (Fin.natAdd_injective _ j) hδ')
            c))) =
      tensorOfKLR Q (cutLabels j hj Λ ∘ Fin.natAdd j) γ c := by
  have h0 : (0 : Multiset (I ⊕ Fin (ℓ - j))).map (Sum.map (id : I → I) (Fin.natAdd j)) = β' := by
    rw [Multiset.map_zero, hβ]
  have key := redSubfamilyProjection_castAlg_concat Q (cutLabels j hj Λ)
    (Fin.natAdd_injective _ j) γ (zero_add _) h0 hδ' h₄ (1 ⊗ₜ c)
  rw [Algebra.TensorProduct.map_tmul, map_one] at key
  rw [key, concat_one_left]

/-- **(T), the outer cut of `S_+`**: the image of `ι_{q.β,q.δ}(1 ⊗ b)` in the algebra of the two
inner blocks, for `b` the relabelling of `b̃` from the last inner block, is the image of
`ι(1 ⊗ b̃)` of the two inner blocks. -/
theorem cutSuffixProjection_plus_tail {ν₀ γ : Multiset I}
    {β δ : Multiset (I ⊕ Fin (j + (2 + (ℓ - j))))}
    (hβ : ((stendhalWeight 2 ν₀).map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j)))).map
      (Sum.map (id : I → I) (Fin.natAdd j)) = β)
    (hγ : ((stendhalWeight (ℓ - j) γ).map (Sum.map (id : I → I) (Fin.natAdd 2))).map
      (Sum.map (id : I → I) (Fin.natAdd j)) = δ)
    (h₄ : β + δ = (stendhalWeight (2 + (ℓ - j)) (ν₀ + γ)).map (Sum.map (id : I → I) (Fin.natAdd j)))
    (b : KLRAlgebra k (stendhalQ Q (blocksTailLabels (plusBlockLabels Λ Λc j hj)))
      ((stendhalWeight (ℓ - j) γ).map (Sum.map (id : I → I) (Fin.natAdd 2)))) :
    cutSuffixProjection (a := j) (r := 2 + (ℓ - j)) Q (plusBlockLabels Λ Λc j hj) (ν₀ + γ)
        (castAlg (stendhalQ Q (plusBlockLabels Λ Λc j hj)) h₄
          (concat (stendhalQ Q (plusBlockLabels Λ Λc j hj)) β δ
            (1 ⊗ₜ relabelHom (subfamilyRelabel Q (plusBlockLabels Λ Λc j hj)
              (Fin.natAdd_injective _ j) hγ) b))) =
      affineToTensor (a := 2) (r := ℓ - j) Q (blocksTailLabels (plusBlockLabels Λ Λc j hj)) ν₀ γ
        (concat (stendhalQ Q (blocksTailLabels (plusBlockLabels Λ Λc j hj)))
          ((stendhalWeight 2 ν₀).map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))))
          ((stendhalWeight (ℓ - j) γ).map (Sum.map (id : I → I) (Fin.natAdd 2))) (1 ⊗ₜ b)) := by
  have key := redSubfamilyProjection_castAlg_concat Q (plusBlockLabels Λ Λc j hj)
    (Fin.natAdd_injective _ j) (ν₀ + γ) (cutInputWeights_add (a := 2) (r := ℓ - j) ν₀ γ) hβ hγ
    h₄ (1 ⊗ₜ b)
  rw [Algebra.TensorProduct.map_tmul, map_one] at key
  exact key

/-- **(T), the inner block projection**: the last inner block projection of `tailLift c`,
relabelled along `plusBlockLabels_tail`, is the image of `c`. -/
theorem relabel_cutSuffixProjection_tailLift {γ : Multiset I}
    (c : KLRAlgebra k (stendhalQ Q (cutLabels j hj Λ ∘ Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)) :
    relabelTensorProductAlgebra Q (plusBlockLabels_tail Λ Λc j hj) γ
        (cutSuffixProjection (a := 2) (r := ℓ - j) Q (blocksTailLabels (plusBlockLabels Λ Λc j hj))
          γ (tailLift j hj Q Λ Λc c)) =
      tensorOfKLR Q (cutLabels j hj Λ ∘ Fin.natAdd j) γ c := by
  rw [tailLift, redSubfamilyProjection_relabel_apply]
  exact relabelTensorProductAlgebra_tensorOfKLR_ofParams Q γ (plusBlockLabels_tail Λ Λc j hj) _ c

/-! ### The head -/

omit [DecidableEq I] in
/-- The red strand `r < j` of `λ` is the red strand `r` of `λ⁺`. -/
theorem cutToPlusColour_comp_castAdd :
    cutToPlusColour (I := I) j hj ∘ Sum.map (id : I → I) (Fin.castAdd (ℓ - j)) =
      Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)) : Fin j → Fin (j + (2 + (ℓ - j)))) := by
  funext a
  rcases a with a | u
  · rfl
  · simp only [Function.comp_apply, Sum.map_inr, Sum.inr.injEq]
    apply Fin.ext
    simp [oldRed, u.2]

omit [DecidableEq I] in
/-- The parameters of the first block of `λ⁺` are those of the first block of `λ`. -/
theorem stendhalQ_head_eq (a b : I ⊕ Fin j) :
    stendhalQ Q (plusBlockLabels Λ Λc j hj ∘ Fin.castAdd (2 + (ℓ - j))) a b =
      stendhalQ Q (cutLabels j hj Λ ∘ Fin.castAdd (ℓ - j)) a b := by
  rw [plusBlockLabels_head]
  rfl

omit [DecidableEq I] in
private theorem seq_head_eq {γh : Multiset (I ⊕ Fin j)} {γ' : Multiset (I ⊕ Fin (j + (ℓ - j)))}
    {γ : Multiset (I ⊕ Fin (j + (2 + (ℓ - j))))}
    (hγ' : γh.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) = γ') (hγ : γ'.map φ = γ)
    (hγp : γh.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) = γ) (i : Seq γh) :
    seqCast hγ (Seq.map φ (seqCast hγ' (Seq.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) i))) =
      seqCast hγp (Seq.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) i) := by
  apply Subtype.ext
  funext a
  rw [seqCast_apply, seqCast_apply, seq_map_apply, seqCast_apply, seq_map_apply, seq_map_apply]
  refine (congrFun (cutToPlusColour_comp_castAdd j hj) _).trans ?_
  exact congrArg (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)) : Fin j → _))
    (Seq.apply_congr i (by simp))

/-- **The two relabellings of a head element agree**: relabelling `c` into `q'.γ` and then along
`cutPlusRelabel` is relabelling `c`, read with the parameters of `λ⁺`, into `q.γ`. -/
theorem cutPlusRelabel_subfamilyRelabel_head {γh : Multiset (I ⊕ Fin j)}
    {γ' : Multiset (I ⊕ Fin (j + (ℓ - j)))} {γ : Multiset (I ⊕ Fin (j + (2 + (ℓ - j))))}
    (hγ' : γh.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) = γ') (hγ : γ'.map φ = γ)
    (hγp : γh.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) = γ)
    (c : KLRAlgebra k (stendhalQ Q (cutLabels j hj Λ ∘ Fin.castAdd (ℓ - j))) γh) :
    relabelHom (cutPlusRelabel j hj Q Λ Λc hγ)
        (relabelHom (subfamilyRelabel Q (cutLabels j hj Λ) (Fin.castAdd_injective _ _) hγ') c) =
      relabelHom (subfamilyRelabel Q (plusBlockLabels Λ Λc j hj) (Fin.castAdd_injective _ _) hγp)
        (relabelHom (SeqRelabel.ofParams (fun a b _ => stendhalQ_head_eq j hj Q Λ Λc a b) γh)
          c) := by
  have hc : (relabelHom (cutPlusRelabel j hj Q Λ Λc hγ)).comp
      (relabelHom (subfamilyRelabel Q (cutLabels j hj Λ) (Fin.castAdd_injective _ _) hγ')) =
      (relabelHom (subfamilyRelabel Q (plusBlockLabels Λ Λc j hj)
        (Fin.castAdd_injective _ _) hγp)).comp
        (relabelHom (SeqRelabel.ofParams (fun a b _ => stendhalQ_head_eq j hj Q Λ Λc a b) γh)) :=
    algHom_ext_of_gen (fun i => by
        simp only [AlgHom.comp_apply, relabelHom_e]
        congr 1
        rw [cutPlusRelabel_equiv, subfamilyRelabel_equiv, subfamilyRelabel_equiv,
          SeqRelabel.ofParams_equiv]
        exact seq_head_eq j hj hγ' hγ hγp i)
      (fun a => by simp [Fin.cast_cast]) (fun l => by simp)
  exact DFunLike.congr_fun hc c

variable {Q Λ Λc} {θ γ ν₀ : Multiset I}

/-- **(H) The head factors of `R(γ)` at the leading Mackey data agree** (Webster v3,
Lemma 7.19, trace half, step L5). For `a ∈ R(q'.γ)`, the head factor of `ι_{q.α,q.γ}(1 ⊗ a)` at
the outer cut of `S_+` (with `a` relabelled along `cutPlusRelabel`), relabelled along
`plusBlockLabels_head`, is the head factor of `ι_{q'.α,q'.γ}(1 ⊗ a)` at the cut of `S_cut`. -/
theorem relabel_cutPrefixProjection_leading_head (s : Seq (stendhalWeight ℓ (θ + γ)))
    (w : Seq (stendhalWeight 2 ν₀))
    (hs : ∀ a : Fin (Multiset.card (stendhalWeight ℓ (θ + γ))), a.val < midPos j s →
      ∀ u : Fin ℓ, s.lbl a = .inr u → u.val < j)
    (q : MackeyQuad (Seq.prefixWt (windowLoading j hj θ γ ν₀ s w)
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
      (Seq.suffixWt (windowLoading j hj θ γ ν₀ s w)
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ))
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
        (stendhalWeight (2 + (ℓ - j)) (ν₀ + γ))))
    (hq : q.β = (stendhalWeight 2 ν₀).map (windowColour j hj))
    (q' : MackeyQuad (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
        (midPos_le_card_cut s))
      (Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s))
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ))
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)))
    (hq' : q'.β = 0) (a : KLRAlgebra k (stendhalQ Q (cutLabels j hj Λ)) q'.γ) :
    relabelTensorProductAlgebra Q (plusBlockLabels_head Λ Λc j hj) θ
        (cutPrefixProjection (a := j) (r := 2 + (ℓ - j)) Q (plusBlockLabels Λ Λc j hj) θ
          (castAlg (stendhalQ Q (plusBlockLabels Λ Λc j hj)) q.h₃
            (concat (stendhalQ Q (plusBlockLabels Λ Λc j hj)) q.α q.γ
              (1 ⊗ₜ relabelHom (cutPlusRelabel j hj Q Λ Λc
                (leadingQuad_γ_eq_map j hj s w q hq q' hq').symm) a)))) =
      cutPrefixProjection (a := j) (r := ℓ - j) Q (cutLabels j hj Λ) θ
        (castAlg (stendhalQ Q (cutLabels j hj Λ)) q'.h₃
          (concat (stendhalQ Q (cutLabels j hj Λ)) q'.α q'.γ (1 ⊗ₜ a))) := by
  obtain ⟨αh, hαh⟩ := exists_headWeight_prefixWt (hj := hj) s hs
  have hα' : q'.α = αh.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) := by
    have h1 := q'.h₁
    rw [hq', add_zero] at h1
    refine h1.trans ?_
    rw [prefixWt_cutLoading, hαh, Multiset.map_map]
    refine Multiset.map_congr rfl fun x _ => ?_
    rcases x with b | u
    · rfl
    · exact congrArg Sum.inr (Fin.ext rfl)
  have hα : q.α = αh.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) := by
    have h1 := q.h₁.trans (prefixWt_windowLoading s w)
    rw [hq, hαh, Multiset.map_map, add_left_inj] at h1
    rw [h1]
    refine Multiset.map_congr rfl fun x _ => ?_
    rcases x with b | u
    · rfl
    · refine congrArg Sum.inr (Fin.ext ?_)
      simp [oldRed, u.2]
  have hinj : Function.Injective (Sum.map (id : I → I) (Fin.castAdd (ℓ - j) : Fin j → _)) :=
    Sum.map_injective.2 ⟨Function.injective_id, Fin.castAdd_injective j (ℓ - j)⟩
  have hle : αh ≤ stendhalWeight j θ := by
    have h3 := Multiset.le_add_right q'.α q'.γ
    rw [q'.h₃, hα'] at h3
    exact (Multiset.map_le_map_iff hinj).1 h3
  have hh : αh + (stendhalWeight j θ - αh) = stendhalWeight j θ := add_tsub_cancel_of_le hle
  have hγ' : (stendhalWeight j θ - αh).map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) =
      q'.γ := by
    have h3 : αh.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) + q'.γ =
        αh.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) +
          (stendhalWeight j θ - αh).map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) := by
      rw [← Multiset.map_add, hh, ← hα', q'.h₃]
    exact (add_left_cancel h3).symm
  have hγp : (stendhalWeight j θ - αh).map
      (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) = q.γ := by
    rw [leadingQuad_γ_eq_map j hj s w q hq q' hq', ← hγ', Multiset.map_map,
      cutToPlusColour_comp_castAdd]
  obtain ⟨c, rfl⟩ : ∃ c, relabelHom (subfamilyRelabel Q (cutLabels j hj Λ)
      (Fin.castAdd_injective _ _) hγ') c = a :=
    ⟨(relabelEquiv _).symm a, (relabelEquiv _).apply_symm_apply a⟩
  rw [cutPlusRelabel_subfamilyRelabel_head j hj Q Λ Λc hγ' _ hγp]
  have kp := redSubfamilyProjection_castAlg_concat Q (plusBlockLabels Λ Λc j hj)
    (Fin.castAdd_injective _ _) θ hh hα.symm hγp q.h₃
    (1 ⊗ₜ relabelHom (SeqRelabel.ofParams (fun a b _ => stendhalQ_head_eq j hj Q Λ Λc a b) _) c)
  have kc := redSubfamilyProjection_castAlg_concat Q (cutLabels j hj Λ)
    (Fin.castAdd_injective _ _) θ hh hα'.symm hγ' q'.h₃ (1 ⊗ₜ c)
  rw [Algebra.TensorProduct.map_tmul, map_one] at kp kc
  rw [kp, kc, castKLR_concat_one_tmul_ofParams]
  exact relabelTensorProductAlgebra_tensorOfKLR_ofParams Q θ (plusBlockLabels_head Λ Λc j hj) _ _

end Categorification.Stendhal.CupCap

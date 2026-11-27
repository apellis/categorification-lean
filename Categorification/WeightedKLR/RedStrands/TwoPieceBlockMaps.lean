/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TwoPieceBlocks
import Categorification.KLR.BlockEmbCompose

/-!
# The block maps of `ℓ + 1` red strands restrict to those of `ℓ` red strands

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1,
Proposition 5.3 and the proof of Proposition 5.5. Let `b` be a block decomposition for `ℓ + 1`
red strands, `θ` the black weight of its first `ℓ + 1` blocks and `β` that of its last block.
A diagram `a` on the first `ℓ` red strands and the black strands of weight `θ` gives the diagram
`C a` on all strands, which is `a` followed by the last red strand and the identity on the black
words of the last block (`prefixBlockMap`). This is multiplicative (but not unital), and it
carries the block maps of `ℓ` red strands to those of `ℓ + 1` red strands:
`C (℘'_j a) = ℘_j a` for the blocks `j ≤ ℓ` (`prefixBlockMap_blockEmb`).

## Main definitions

* `lastWordIdem β`: the sum of the idempotents `e(λ_{ℓ+1} u)`, `u` a black word of weight `β`.
* `prefixBlockMap θ β`: the map `a ↦ a ⊠ lastWordIdem β`.

## Main results

* `prefixBlockMap_e`, `prefixBlockMap_eSum`: idempotents go to sums over two-piece loadings.
* `prefixBlockMap_x_mul`, `prefixBlockMap_ψ_mul`: dots and crossings commute past the map.
* `prefixBlockMap_blockEmb`: the block maps of the first `ℓ + 1` blocks are compatible.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra
open scoped TensorProduct

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (θ β : Multiset I)

local notation "lc" => Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ)
local notation "S" => stendhalQ Q Λ
local notation "S'" => stendhalQ Q (Λ ∘ Fin.castSucc)
local notation "ρ" => redSubfamilyRelabel Q Λ Fin.castSucc (Fin.castSucc_injective ℓ) θ
local notation "A" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ)
local notation "δ" => Multiset.map lc (stendhalWeight 1 β)
local notation "H" => parabolicInputWeights_add (ℓ := ℓ) θ β

/-- The black words of the last block, after the last red strand. -/
def lastWords : Finset (Seq ((stendhalWeight 1 β).map lc)) :=
  Finset.univ.image fun u : Seq β => Seq.map lc (SingleRed.insertWord β u)

omit [DecidableEq I] in
theorem lastWord_injective :
    Function.Injective fun u : Seq β => Seq.map lc (SingleRed.insertWord β u) := fun _ _ h =>
  SingleRed.insertWord_injective (ν := β) (seq_map_injective
    (Sum.map_injective.2 ⟨Function.injective_id, fun _ _ _ => Subsingleton.elim _ _⟩) h)

/-- The sum of the idempotents `e(λ_{ℓ+1} u)` of the last block. -/
abbrev lastWordIdem : KLRAlgebra k S δ := eSum S (lastWords (ℓ := ℓ) β)

/-- **The prefix map** `a ↦ a ⊠ ∑_u e(λ_{ℓ+1} u)`: a diagram on the first `ℓ` red strands,
followed by the last red strand and the black words of the last block. -/
def prefixBlockMap :
    KLRAlgebra k S' (stendhalWeight ℓ θ) →ₙₐ[k] KLRAlgebra k S (stendhalWeight (ℓ + 1) (θ + β)) where
  toFun a := castKLR S H (concat S A δ (relabelEquiv ρ a ⊗ₜ lastWordIdem Q Λ β))
  map_smul' c a := by
    rw [map_smul, ← TensorProduct.smul_tmul', map_smul, map_smul]; rfl
  map_zero' := by rw [map_zero, TensorProduct.zero_tmul, map_zero, map_zero]
  map_add' a a' := by rw [map_add, TensorProduct.add_tmul, map_add, map_add]
  map_mul' a a' := by
    change castKLR S H (concat S A δ (relabelEquiv ρ (a * a') ⊗ₜ lastWordIdem Q Λ β)) =
      castKLR S H (concat S A δ (relabelEquiv ρ a ⊗ₜ lastWordIdem Q Λ β)) *
        castKLR S H (concat S A δ (relabelEquiv ρ a' ⊗ₜ lastWordIdem Q Λ β))
    rw [← map_mul (castKLR S H), ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul,
      (eSum_idem _).eq, map_mul (relabelEquiv ρ)]

theorem prefixBlockMap_apply (a : KLRAlgebra k S' (stendhalWeight ℓ θ)) :
    prefixBlockMap Q Λ θ β a =
      castKLR S H (concat S A δ (relabelEquiv ρ a ⊗ₜ lastWordIdem Q Λ β)) := rfl

theorem prefixBlockMap_e (t : Seq (stendhalWeight ℓ θ)) :
    prefixBlockMap Q Λ θ β (e t) = ∑ u : Seq β, e (twoPieceLoading θ β t u) := by
  rw [prefixBlockMap_apply, relabelEquiv_apply, relabelHom_e, lastWordIdem, eSum, lastWords,
    Finset.sum_image fun u _ v _ h => lastWord_injective β h, TensorProduct.tmul_sum, map_sum,
    map_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [concat_e_tmul_e, castKLR_e]
  rfl

theorem prefixBlockMap_eSum (T : Finset (Seq (stendhalWeight ℓ θ))) :
    prefixBlockMap Q Λ θ β (eSum S' T) =
      eSum S ((T ×ˢ Finset.univ).image fun p => twoPieceLoading θ β p.1 p.2) := by
  rw [eSum, map_sum, eSum, Finset.sum_image fun p _ q _ h => twoPieceLoading_injective θ β h,
    Finset.sum_product]
  exact Finset.sum_congr rfl fun t _ => prefixBlockMap_e Q Λ θ β t

theorem prefixBlockMap_x_mul (p : Fin (Multiset.card (stendhalWeight ℓ θ)))
    (q : Fin (Multiset.card (stendhalWeight (ℓ + 1) (θ + β)))) (hq : q.val = p.val)
    (z : KLRAlgebra k S' (stendhalWeight ℓ θ)) :
    prefixBlockMap Q Λ θ β (x p * z) = x q * prefixBlockMap Q Λ θ β z := by
  rw [prefixBlockMap_apply, prefixBlockMap_apply, map_mul (relabelEquiv ρ), relabelEquiv_apply,
    relabelHom_x]
  have h : (x (Fin.cast (ρ).card_eq p) * relabelEquiv ρ z) ⊗ₜ[k] lastWordIdem Q Λ β =
      (x (Fin.cast (ρ).card_eq p) ⊗ₜ[k] (1 : KLRAlgebra k S δ)) *
        (relabelEquiv ρ z ⊗ₜ[k] lastWordIdem Q Λ β) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [h, concat_mul, concat_x_tmul_one, mul_assoc, oneConcat_mul_concat, map_mul, castKLR_x]
  congr 2
  exact Fin.ext hq.symm

theorem prefixBlockMap_ψ_mul {j : ℕ} (hj : j + 1 < Multiset.card (stendhalWeight ℓ θ))
    (z : KLRAlgebra k S' (stendhalWeight ℓ θ)) :
    prefixBlockMap Q Λ θ β (ψ j * z) = ψ j * prefixBlockMap Q Λ θ β z := by
  rw [prefixBlockMap_apply, prefixBlockMap_apply, map_mul (relabelEquiv ρ), relabelEquiv_apply,
    relabelHom_ψ]
  have h : (ψ j * relabelEquiv ρ z) ⊗ₜ[k] lastWordIdem Q Λ β =
      ((ψ j : KLRAlgebra k S A) ⊗ₜ[k] (1 : KLRAlgebra k S δ)) *
        (relabelEquiv ρ z ⊗ₜ[k] lastWordIdem Q Λ β) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [h, concat_mul, concat_ψ_tmul_one (by rwa [Multiset.card_map]), mul_assoc,
    oneConcat_mul_concat, map_mul, castKLR_ψ]

omit [DecidableEq I] in
/-- The labels of `t λ_{ℓ+1} u` at the positions of `t` are those of `t`. -/
theorem twoPieceLoading_apply_of_val_eq (t : Seq (stendhalWeight ℓ θ)) (u : Seq β)
    (p : Fin (Multiset.card (stendhalWeight (ℓ + 1) (θ + β))))
    (q : Fin (Multiset.card (stendhalWeight ℓ θ))) (h : p.val = q.val) :
    (twoPieceLoading θ β t u).1 p = addRedColor ℓ (t.1 q) := by
  rw [twoPieceLoading, concatLoading, Seq.cast_apply]
  have hp : Fin.cast (congrArg Multiset.card H).symm p =
      Seq.posL _ (Fin.cast (Multiset.card_map (addRedColor ℓ) _).symm q) := Fin.ext (by simp [h])
  rw [hp, Seq.append_posL]
  rfl

section Reindex

variable {n : ℕ} (Λ' : Fin n → I →₀ ℕ) (μ₀ : Multiset I)

/-- The KLR algebra of black strands inside the KLR algebra of the Stendhal data. -/
def blackReindex :
    KLRAlgebra k Q μ₀ ≃ₐ[k] KLRAlgebra k (stendhalQ Q Λ') (μ₀.map (Sum.inl : I → I ⊕ Fin n)) :=
  KLRAlgebra.reindexEquiv Sum.inl_injective (stendhalQ Q Λ') μ₀

theorem blackReindex_e (i : Seq μ₀) : blackReindex Q Λ' μ₀ (e i) = e (Seq.map Sum.inl i) :=
  KLRAlgebra.reindexEquiv_e _ i

theorem blackReindex_x (a : Fin (Multiset.card μ₀)) :
    blackReindex Q Λ' μ₀ (x a) = x (Fin.cast (Multiset.card_map _ μ₀).symm a) :=
  KLRAlgebra.reindexEquiv_x _ a

theorem blackReindex_ψ (l : ℕ) : blackReindex Q Λ' μ₀ (ψ l) = ψ l :=
  KLRAlgebra.reindexEquiv_ψ _ l

end Reindex

section Blocks

variable (b : Fin (ℓ + 2) → Multiset I) {j : ℕ} (hj : j < ℓ + 1)

local notation "θb" => initWeight b
local notation "βb" => lastBlock b
local notation "B'" => StendhalAlgebra.blockEmb (b := initBlocks b) (ν := initWeight b) rfl j hj
local notation "D" => StendhalAlgebra.blockEmb (b := b) (blockPrefix_last b) j (by omega)

theorem prefixBlockMap_eSum_rootSet :
    prefixBlockMap Q Λ θb βb (eSum S' (StendhalAlgebra.rootSet θb (blockRoot (initBlocks b)))) =
      eSum S (StendhalAlgebra.rootSet (θb + βb) (blockRoot b)) := by
  rw [prefixBlockMap_eSum]
  congr 1
  ext s
  simp only [Finset.mem_image, Finset.mem_product, Finset.mem_univ, and_true, Prod.exists]
  rw [mem_rootSet_blockRoot_iff]
  exact ⟨fun ⟨t, u, ht, h⟩ => ⟨t, ht, u, h⟩, fun ⟨t, ht, u, h⟩ => ⟨t, u, ht, h⟩⟩

theorem blockEmb_o_eq : (D).o = (B').o := blockStart_initBlocks b hj.le

theorem prefixBlockMap_eF (i : Seq ((initBlocks b ⟨j, hj⟩).map (Sum.inl : I → I ⊕ Fin ℓ)))
    (i' : Seq ((b ⟨j, by omega⟩).map (Sum.inl : I → I ⊕ Fin (ℓ + 1))))
    (hi : ∀ (a : Fin (Multiset.card ((initBlocks b ⟨j, hj⟩).map (Sum.inl : I → I ⊕ Fin ℓ))))
      (a' : Fin (Multiset.card ((b ⟨j, by omega⟩).map (Sum.inl : I → I ⊕ Fin (ℓ + 1))))),
      a.val = a'.val → i'.1 a' = addRedColor ℓ (i.1 a)) :
    prefixBlockMap Q Λ θb βb ((B').eF S' i) = (D).eF S i' := by
  rw [BlockEmb.eF, BlockEmb.eF, prefixBlockMap_eSum]
  congr 1
  ext s
  simp only [StendhalAlgebra.blockEmb, BlockEmb.window, Finset.mem_image, Finset.mem_product,
    Finset.mem_univ, and_true, Prod.exists, Finset.mem_filter]
  have hpos : ∀ (t : Seq (stendhalWeight ℓ θb)) (u : Seq βb)
      (a : Fin (Multiset.card ((initBlocks b ⟨j, hj⟩).map (Sum.inl : I → I ⊕ Fin ℓ))))
      (a' : Fin (Multiset.card ((b ⟨j, by omega⟩).map (Sum.inl : I → I ⊕ Fin (ℓ + 1))))),
      a.val = a'.val → (twoPieceLoading θb βb t u).1
        (KLRAlgebra.windowPos (blockStart b j) (blockEnd_le (blockPrefix_last b) (by omega)) a') =
        addRedColor ℓ (t.1 (KLRAlgebra.windowPos (blockStart (initBlocks b) j)
          (blockEnd_le rfl hj) a)) := by
    intro t u a a' h
    apply twoPieceLoading_apply_of_val_eq
    simp [KLRAlgebra.windowPos, h, blockStart_initBlocks b hj.le]
  constructor
  · rintro ⟨t, u, ⟨ht, hw⟩, rfl⟩
    refine ⟨twoPieceLoading_mem_rootSet b ht u, fun a' => ?_⟩
    have ha : (Fin.cast (Multiset.card_map _ _).symm (Fin.cast (Multiset.card_map _ _) a') :
      Fin (Multiset.card ((initBlocks b ⟨j, hj⟩).map (Sum.inl : I → I ⊕ Fin ℓ)))).val =
        a'.val := rfl
    rw [hpos t u _ a' ha, hw, hi _ _ ha]
  · rintro ⟨hs, hw⟩
    obtain ⟨t, ht, u, rfl⟩ := (mem_rootSet_blockRoot_iff b s).1 hs
    refine ⟨t, u, ⟨ht, fun a => ?_⟩, rfl⟩
    have ha : a.val = (Fin.cast (Multiset.card_map _ _).symm (Fin.cast (Multiset.card_map _ _) a) :
      Fin (Multiset.card ((b ⟨j, by omega⟩).map (Sum.inl : I → I ⊕ Fin (ℓ + 1))))).val := rfl
    have := hw (Fin.cast (Multiset.card_map _ _).symm (Fin.cast (Multiset.card_map _ _) a))
    rw [hpos t u a _ ha, hi a _ ha] at this
    exact addRedColor_injective ℓ this

/-- **The prefix map carries the block maps of `ℓ` red strands to those of `ℓ + 1` red
strands** (arXiv:1309.3796v3, proof of Proposition 5.5): for a block `j ≤ ℓ`, a diagram of
weight `b_j` placed on the block `j` of the first `ℓ` red strands and then extended by the last
red strand and the black words of the last block is the same diagram placed on the block `j` of
all `ℓ + 1` red strands. -/
theorem prefixBlockMap_blockEmb (a : KLRAlgebra k Q (b ⟨j, by omega⟩)) :
    prefixBlockMap Q Λ θb βb ((B').hom S'
        (blackReindex Q (Λ ∘ Fin.castSucc) (initBlocks b ⟨j, hj⟩) a)).val =
      ((D).hom S (blackReindex Q Λ (b ⟨j, by omega⟩) a)).val := by
  have hcard : Multiset.card ((initBlocks b ⟨j, hj⟩).map (Sum.inl : I → I ⊕ Fin ℓ)) =
      Multiset.card ((b ⟨j, by omega⟩).map (Sum.inl : I → I ⊕ Fin (ℓ + 1))) := by
    rw [Multiset.card_map, Multiset.card_map]; rfl
  refine BlockEmb.map_hom_val_eq (Q₀ := Q) (μ₀ := b ⟨j, by omega⟩) (B') (D)
    (prefixBlockMap Q Λ θb βb)
    (blackReindex Q (Λ ∘ Fin.castSucc) (initBlocks b ⟨j, hj⟩)).toAlgHom
    (blackReindex Q Λ (b ⟨j, by omega⟩)).toAlgHom
    (prefixBlockMap_eSum_rootSet Q Λ b) (fun i => ?_) (fun c => ?_) (fun l => ?_) a
  · simp only [AlgEquiv.coe_toAlgHom, blackReindex_e, BlockEmb.hom_e,
      BlockEmb.val_gE]
    exact prefixBlockMap_eF Q Λ b hj _ _ fun a a' h => by
      simp only [Seq.map_lbl]
      congr 2
      exact Fin.ext (by simpa using h.symm)
  · simp only [AlgEquiv.coe_toAlgHom, blackReindex_x, BlockEmb.hom_x,
      val_polCorner, BlockEmb.pol_X_pos]
    rw [← prefixBlockMap_eSum_rootSet Q Λ b]
    exact prefixBlockMap_x_mul Q Λ _ _ _ _ (by simp [blockEmb_o_eq b hj]) _
  · simp only [AlgEquiv.coe_toAlgHom, blackReindex_ψ, BlockEmb.hom_ψ]
    by_cases hl : l + 1 < Multiset.card ((initBlocks b ⟨j, hj⟩).map (Sum.inl : I → I ⊕ Fin ℓ))
    · rw [BlockEmb.val_gψ _ hl, BlockEmb.val_gψ _ (hcard ▸ hl), blockEmb_o_eq b hj,
        prefixBlockMap_ψ_mul Q Λ _ _ ((B').lt_card hl), prefixBlockMap_eSum_rootSet]
    · rw [BlockEmb.gψ_of_not_lt _ hl, BlockEmb.gψ_of_not_lt _ (hcard ▸ hl), Corner.val_zero,
        Corner.val_zero, map_zero]

end Blocks

end Categorification.Stendhal

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TwoPieceBlockMapIdems

/-!
# The block map of the last block of `ℓ + 1` red strands

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1,
Proposition 5.3 and the proof of Proposition 5.5. Let `b` be a block decomposition for `ℓ + 1`
red strands, `θ` the black weight of its first `ℓ + 1` blocks and `β` that of its last block.
A black diagram `y` of weight `β` gives the diagram `λ_{ℓ+1} y` of the last red strand followed
by `y` (`lastBlackMap`), and a diagram `w` on the last red strand and the black strands of the
last block gives `e_{α'} ⊠ w` (`suffixBlockMap`). Their composite is the block map of the last
block: `e_{α'} ⊠ λ_{ℓ+1} a = ℘_{ℓ+1} a` (`suffixBlockMap_lastBlackMap`).

## Main definitions

* `lastBlackMap β`: the map `y ↦ λ_{ℓ+1} y`.
* `suffixBlockMap θ β T`: the map `w ↦ e_T ⊠ w`.

## Main results

* `lastBlackMap_e`, `lastBlackMap_one`, `hflip_lastBlackMap`.
* `suffixBlockMap_lastBlackMap`: the block map of the last block.
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
local notation "R₁" => ({Sum.inr (Fin.last ℓ)} : Multiset (I ⊕ Fin (ℓ + 1)))
local notation "B₁" => Multiset.map (Sum.inl : I → I ⊕ Fin (ℓ + 1)) β
local notation "hB" => lastRedBlackWeight (ℓ := ℓ) β

omit [DecidableEq I] in
theorem lastRedBlack_loading (s : Seq β) (u : Seq R₁) :
    Seq.cast hB (u.append (Seq.map (Sum.inl : I → I ⊕ Fin (ℓ + 1)) s)) =
      Seq.map lc (SingleRed.insertWord β s) := by
  apply Subtype.ext
  funext a
  change (u.append (Seq.map Sum.inl s)).1 (Fin.cast _ a) =
    lc ((SingleRed.insertWord β s).lbl (Fin.cast _ a))
  by_cases hz : a.val = 0
  · rw [Seq.append_apply_lt _ _ _ (by change a.val < (R₁).card; simpa using hz)]
    have hpos : Fin.cast (Multiset.card_map lc _) a = ⟨0, by simp [stendhalWeight]⟩ :=
      Fin.ext hz
    rw [hpos, SingleRed.insertWord_head]
    exact Multiset.mem_singleton.mp (u.mem _)
  · rw [Seq.append_apply_ge _ _ _
      (by change (R₁).card ≤ a.val; simpa using (show 1 ≤ a.val by omega))]
    have hlen := a.isLt
    simp [stendhalWeight] at hlen
    let c : Fin β.card := ⟨a.val - 1, by omega⟩
    have hpos : Fin.cast (Multiset.card_map lc _) a = SingleRed.blackPos β c :=
      Fin.ext (by change a.val = a.val - 1 + 1; omega)
    rw [hpos, SingleRed.insertWord_black]
    change Sum.inl (s.1 _) = Sum.inl (s.1 c)
    congr 2

/-- **The last red strand followed by a black diagram**: `y ↦ λ_{ℓ+1} y`. -/
def lastBlackMap : KLRAlgebra k Q β →ₙₐ[k] KLRAlgebra k S δ where
  toFun y := castKLR S hB (concat S R₁ B₁ (1 ⊗ₜ blackReindex Q Λ β y))
  map_smul' c y := by
    rw [map_smul, TensorProduct.tmul_smul, map_smul, map_smul]; rfl
  map_zero' := by rw [map_zero, TensorProduct.tmul_zero, map_zero, map_zero]
  map_add' y y' := by rw [map_add, TensorProduct.tmul_add, map_add, map_add]
  map_mul' y y' := by
    change castKLR S hB (concat S R₁ B₁ (1 ⊗ₜ blackReindex Q Λ β (y * y'))) =
      castKLR S hB (concat S R₁ B₁ (1 ⊗ₜ blackReindex Q Λ β y)) *
        castKLR S hB (concat S R₁ B₁ (1 ⊗ₜ blackReindex Q Λ β y'))
    rw [← map_mul (castKLR S hB), ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      map_mul (blackReindex Q Λ β)]

theorem lastBlackMap_apply (y : KLRAlgebra k Q β) :
    lastBlackMap Q Λ β y = castKLR S hB (concat S R₁ B₁ (1 ⊗ₜ blackReindex Q Λ β y)) := rfl

theorem lastBlackMap_e (u : Seq β) :
    lastBlackMap Q Λ β (e u) = e (Seq.map lc (SingleRed.insertWord β u)) := by
  rw [lastBlackMap_apply, blackReindex_e,
    ← e_single (Q := S) (Sum.inr (Fin.last ℓ)) (default : Seq R₁), concat_e_tmul_e, castKLR_e,
    lastRedBlack_loading]

theorem lastBlackMap_one : lastBlackMap Q Λ β 1 = lastWordIdem Q Λ β := by
  rw [← sum_e (Q := Q) (ν := β), map_sum, lastWordIdem, eSum, lastWords,
    Finset.sum_image fun u _ v _ h => lastWord_injective β h]
  exact Finset.sum_congr rfl fun u _ => lastBlackMap_e Q Λ β u

theorem castKLR_oneConcat_last :
    castKLR S hB (oneConcat S R₁ B₁) = lastWordIdem Q Λ β := by
  rw [← lastBlackMap_one, lastBlackMap_apply, map_one, concat_one_tmul_one]

theorem lastBlackMap_x (c : Fin (Multiset.card β)) (q : Fin (Multiset.card δ))
    (hq : q.val = c.val + 1) :
    lastBlackMap Q Λ β (x c) = x q * lastWordIdem Q Λ β := by
  rw [lastBlackMap_apply, blackReindex_x, concat_one_tmul_x, map_mul, castKLR_x,
    castKLR_oneConcat_last]
  congr 2
  refine Fin.ext ?_
  change Multiset.card R₁ + c.val = q.val
  rw [hq, Multiset.card_singleton, add_comm]

theorem lastBlackMap_ψ {l : ℕ} (hl : l + 1 < Multiset.card β) :
    lastBlackMap Q Λ β (ψ l) = ψ (l + 1) * lastWordIdem Q Λ β := by
  rw [lastBlackMap_apply, blackReindex_ψ, concat_one_tmul_ψ (by rwa [Multiset.card_map]),
    map_mul, castKLR_ψ, castKLR_oneConcat_last, Multiset.card_singleton, Nat.add_comm 1 l]

/-- The black diagram after the last red strand commutes with the horizontal flip. -/
theorem hflip_lastBlackMap (y : KLRAlgebra k Q β) :
    hflip (lastBlackMap Q Λ β y) = lastBlackMap Q Λ β (hflip y) := by
  have h : hflip (blackReindex Q Λ β y) = blackReindex Q Λ β (hflip y) := hflip_relabelHom _ y
  rw [lastBlackMap_apply, lastBlackMap_apply, hflip_castKLR', hflip_concat_tmul_tmul, hflip_one, h]

/-- **The suffix map** `w ↦ e_T ⊠ w`: an idempotent on the first `ℓ` red strands, followed by
a diagram on the last red strand and the black strands of the last block. -/
def suffixBlockMap (T : Finset (Seq (stendhalWeight ℓ θ))) :
    KLRAlgebra k S δ →ₙₐ[k] KLRAlgebra k S (stendhalWeight (ℓ + 1) (θ + β)) where
  toFun w := castKLR S H (concat S A δ (relabelEquiv ρ (eSum S' T) ⊗ₜ w))
  map_smul' c w := by
    rw [TensorProduct.tmul_smul, map_smul, map_smul]; rfl
  map_zero' := by rw [TensorProduct.tmul_zero, map_zero, map_zero]
  map_add' w w' := by rw [TensorProduct.tmul_add, map_add, map_add]
  map_mul' w w' := by
    change castKLR S H (concat S A δ (relabelEquiv ρ (eSum S' T) ⊗ₜ (w * w'))) =
      castKLR S H (concat S A δ (relabelEquiv ρ (eSum S' T) ⊗ₜ w)) *
        castKLR S H (concat S A δ (relabelEquiv ρ (eSum S' T) ⊗ₜ w'))
    rw [← map_mul (castKLR S H), ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul,
      ← map_mul (relabelEquiv ρ), (eSum_idem _).eq]

theorem suffixBlockMap_apply (T : Finset (Seq (stendhalWeight ℓ θ))) (w : KLRAlgebra k S δ) :
    suffixBlockMap Q Λ θ β T w =
      castKLR S H (concat S A δ (relabelEquiv ρ (eSum S' T) ⊗ₜ w)) := rfl

theorem suffixBlockMap_lastWordIdem (T : Finset (Seq (stendhalWeight ℓ θ))) :
    suffixBlockMap Q Λ θ β T (lastWordIdem Q Λ β) = prefixBlockMap Q Λ θ β (eSum S' T) := rfl

theorem suffixBlockMap_e (T : Finset (Seq (stendhalWeight ℓ θ))) (u : Seq β) :
    suffixBlockMap Q Λ θ β T (e (Seq.map lc (SingleRed.insertWord β u))) =
      eSum S (T.image fun t => twoPieceLoading θ β t u) := by
  rw [suffixBlockMap_apply, eSum, map_sum, TensorProduct.sum_tmul, map_sum, map_sum, eSum,
    Finset.sum_image fun t _ t' _ h => (Prod.ext_iff.1 (twoPieceLoading_injective θ β
      (show twoPieceLoading θ β (t, u).1 (t, u).2 = twoPieceLoading θ β (t', u).1 (t', u).2
        from h))).1]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [relabelEquiv_apply, relabelHom_e, concat_e_tmul_e, castKLR_e]
  rfl

theorem suffixBlockMap_x_mul (T : Finset (Seq (stendhalWeight ℓ θ))) (p : Fin (Multiset.card δ))
    (q : Fin (Multiset.card (stendhalWeight (ℓ + 1) (θ + β))))
    (hq : q.val = Multiset.card A + p.val) (w : KLRAlgebra k S δ) :
    suffixBlockMap Q Λ θ β T (x p * w) = x q * suffixBlockMap Q Λ θ β T w := by
  rw [suffixBlockMap_apply, suffixBlockMap_apply]
  have h : relabelEquiv ρ (eSum S' T) ⊗ₜ[k] (x p * w) =
      ((1 : KLRAlgebra k S A) ⊗ₜ[k] x p) * (relabelEquiv ρ (eSum S' T) ⊗ₜ[k] w) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [h, concat_mul, concat_one_tmul_x, mul_assoc, oneConcat_mul_concat, map_mul, castKLR_x]
  congr 2
  exact Fin.ext hq.symm

theorem suffixBlockMap_ψ_mul (T : Finset (Seq (stendhalWeight ℓ θ))) {l : ℕ}
    (hl : l + 1 < Multiset.card δ) (w : KLRAlgebra k S δ) :
    suffixBlockMap Q Λ θ β T (ψ l * w) =
      ψ (Multiset.card A + l) * suffixBlockMap Q Λ θ β T w := by
  rw [suffixBlockMap_apply, suffixBlockMap_apply]
  have h : relabelEquiv ρ (eSum S' T) ⊗ₜ[k] (ψ l * w) =
      ((1 : KLRAlgebra k S A) ⊗ₜ[k] ψ l) * (relabelEquiv ρ (eSum S' T) ⊗ₜ[k] w) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [h, concat_mul, concat_one_tmul_ψ hl, mul_assoc, oneConcat_mul_concat, map_mul, castKLR_ψ]

/-- `flip(e_T ⊠ w · e(t λ u)) e(t'' λ u'') = ι(e(t) e_T e(t'') ⊗ e(λ u) flip(w) e(λ u''))`. -/
theorem hflip_suffixBlockMap_mul_e_mul_e (T : Finset (Seq (stendhalWeight ℓ θ)))
    (w : KLRAlgebra k S δ) (t t'' : Seq (stendhalWeight ℓ θ)) (u u'' : Seq β) :
    hflip (suffixBlockMap Q Λ θ β T w * e (twoPieceLoading θ β t u)) *
        e (twoPieceLoading θ β t'' u'') =
      castKLR S H (concat S A δ (relabelEquiv ρ (e t * eSum S' T * e t'') ⊗ₜ
        (e (Seq.map lc (SingleRed.insertWord β u)) * hflip w *
          e (Seq.map lc (SingleRed.insertWord β u''))))) := by
  rw [e_twoPieceLoading, e_twoPieceLoading, suffixBlockMap_apply, ← map_mul, ← concat_mul,
    Algebra.TensorProduct.tmul_mul_tmul, ← map_mul (relabelEquiv ρ), hflip_castKLR',
    hflip_concat_tmul_tmul, relabelEquiv_apply, hflip_relabelHom, ← relabelEquiv_apply, hflip_mul,
    hflip_mul, hflip_e, hflip_e, hflip_eSum, ← map_mul, ← concat_mul,
    Algebra.TensorProduct.tmul_mul_tmul, ← map_mul (relabelEquiv ρ)]

/-- `ι(1 ⊗ V) e(t λ u) = ι(e(t) ⊗ V e(λ u))`. -/
theorem concat_one_tmul_mul_e (V : KLRAlgebra k S δ) (t : Seq (stendhalWeight ℓ θ)) (u : Seq β) :
    castKLR S H (concat S A δ (1 ⊗ₜ V)) * e (twoPieceLoading θ β t u) =
      castKLR S H (concat S A δ (relabelEquiv ρ (e t) ⊗ₜ
        (V * e (Seq.map lc (SingleRed.insertWord β u))))) := by
  rw [e_twoPieceLoading, ← map_mul, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

omit [DecidableEq I] in
/-- The labels of `t λ_{ℓ+1} u` at the positions of `u` are those of `u`. -/
theorem twoPieceLoading_apply_of_val_eq_last (t : Seq (stendhalWeight ℓ θ)) (u : Seq β)
    (p : Fin (Multiset.card (stendhalWeight (ℓ + 1) (θ + β)))) (c : Fin (Multiset.card β))
    (h : p.val = Multiset.card A + (c.val + 1)) :
    (twoPieceLoading θ β t u).1 p = Sum.inl (u.1 c) := by
  rw [twoPieceLoading, concatLoading, Seq.cast_apply]
  have hp : Fin.cast (congrArg Multiset.card H).symm p =
      Seq.posR _ (Fin.cast (Multiset.card_map lc _).symm (SingleRed.blackPos β c)) :=
    Fin.ext (by simp [Seq.posR, h, SingleRed.blackPos])
  rw [hp, Seq.append_posR]
  change lc ((SingleRed.insertWord β u).lbl (SingleRed.blackPos β c)) = _
  rw [SingleRed.insertWord_black]
  rfl

section Blocks

variable (b : Fin (ℓ + 2) → Multiset I)

local notation "θb" => initWeight b
local notation "βb" => lastBlock b
local notation "D" => StendhalAlgebra.blockEmb (b := b) (blockPrefix_last b) (ℓ + 1)
  (Nat.lt_succ_self (ℓ + 1))

omit [DecidableEq I] in
theorem blockStart_last :
    blockStart b (ℓ + 1) =
      Multiset.card (Multiset.map (addRedColor ℓ) (stendhalWeight ℓ (initWeight b))) + 1 := by
  rw [blockStart, blockPrefix_initBlocks b le_rfl]
  simp [stendhalWeight, initWeight]
  omega

theorem blockR_hom_val (w : KLRAlgebra k S B₁) :
    ((blockR R₁ B₁).hom S w).val = concat S R₁ B₁ (1 ⊗ₜ w) := by
  rw [concat_tmul, map_one, Corner.val_one, Corner.E_mul_val]

/-- **The block map of the last block** (arXiv:1309.3796v3, proof of Proposition 5.5): a
diagram `a` of weight `b_{ℓ+1}` after the last red strand, preceded by the idempotent `e_{α'}`
of the first `ℓ` red strands, is the diagram `a` on the last block of all `ℓ + 1` red strands. -/
theorem suffixBlockMap_lastBlackMap (a : KLRAlgebra k Q (lastBlock b)) :
    suffixBlockMap Q Λ θb βb (StendhalAlgebra.rootSet θb (blockRoot (initBlocks b)))
        (lastBlackMap Q Λ βb a) =
      ((D).hom S (blackReindex Q Λ (b ⟨ℓ + 1, Nat.lt_succ_self (ℓ + 1)⟩) a)).val := by
  let C : KLRAlgebra k S (R₁ + Multiset.map (Sum.inl : I → I ⊕ Fin (ℓ + 1)) βb) →ₙₐ[k]
      KLRAlgebra k S (stendhalWeight (ℓ + 1) (θb + βb)) :=
    (suffixBlockMap Q Λ θb βb (StendhalAlgebra.rootSet θb (blockRoot (initBlocks b)))).comp
      (castKLR S (lastRedBlackWeight (ℓ := ℓ) βb)).toAlgHom.toNonUnitalAlgHom
  have hC : ∀ y : KLRAlgebra k Q βb, C (((blockR R₁ (Multiset.map Sum.inl βb)).hom S
      (blackReindex Q Λ βb y)).val) =
      suffixBlockMap Q Λ θb βb (StendhalAlgebra.rootSet θb (blockRoot (initBlocks b)))
        (lastBlackMap Q Λ βb y) := fun y => by
    change suffixBlockMap Q Λ θb βb _ (castKLR S _ _) = _
    rw [blockR_hom_val]
    rfl
  rw [← hC]
  refine BlockEmb.map_hom_val_eq (Q₀ := Q) (μ₀ := βb) (blockR R₁ (Multiset.map Sum.inl βb)) (D) C
    (blackReindex Q Λ βb).toAlgHom
    (blackReindex Q Λ (b ⟨ℓ + 1, Nat.lt_succ_self (ℓ + 1)⟩)).toAlgHom ?_ (fun i => ?_)
    (fun c => ?_) (fun l => ?_) a
  · change suffixBlockMap Q Λ θb βb _ (castKLR S _ (oneConcat S _ _)) = _
    rw [castKLR_oneConcat_last, suffixBlockMap_lastWordIdem, prefixBlockMap_eSum_rootSet]
  · rw [AlgEquiv.coe_toAlgHom, hC, lastBlackMap_e, suffixBlockMap_e]
    simp only [AlgEquiv.coe_toAlgHom, blackReindex_e, BlockEmb.hom_e, BlockEmb.val_gE]
    congr 1
    ext s
    simp only [StendhalAlgebra.blockEmb, BlockEmb.window, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨twoPieceLoading_mem_rootSet b ht i, fun a' => ?_⟩
      rw [twoPieceLoading_apply_of_val_eq_last θb βb t i _ (Fin.cast (Multiset.card_map _ _) a')
        (by simp [KLRAlgebra.windowPos, blockStart_last]; omega)]
      rfl
    · rintro ⟨hs, hw⟩
      obtain ⟨t, ht, u, rfl⟩ := (mem_rootSet_blockRoot_iff b s).1 hs
      refine ⟨t, ht, ?_⟩
      congr 1
      refine Subtype.ext (funext fun c => ?_)
      have := hw (Fin.cast (Multiset.card_map _ _).symm c)
      rw [twoPieceLoading_apply_of_val_eq_last θb βb t u _ c
        (by simp [KLRAlgebra.windowPos, blockStart_last]; omega)] at this
      exact (Sum.inl_injective this).symm
  · rw [AlgEquiv.coe_toAlgHom, hC, lastBlackMap_x Q Λ βb c ⟨c.val + 1, by simp [stendhalWeight]⟩
      rfl, suffixBlockMap_x_mul Q Λ θb βb _ _ ((D).pos (Fin.cast (Multiset.card_map _ _).symm c))
      (by simp [StendhalAlgebra.blockEmb, BlockEmb.window, KLRAlgebra.windowPos,
        blockStart_last]; omega),
      suffixBlockMap_lastWordIdem, prefixBlockMap_eSum_rootSet]
    simp only [AlgEquiv.coe_toAlgHom, blackReindex_x, BlockEmb.hom_x, val_polCorner,
      BlockEmb.pol_X_pos]
    congr 2
  · by_cases hl : l + 1 < Multiset.card βb
    · rw [AlgEquiv.coe_toAlgHom, hC, lastBlackMap_ψ Q Λ βb hl,
        suffixBlockMap_ψ_mul Q Λ θb βb _ (by simp [stendhalWeight]; omega),
        suffixBlockMap_lastWordIdem, prefixBlockMap_eSum_rootSet]
      simp only [AlgEquiv.coe_toAlgHom, blackReindex_ψ, BlockEmb.hom_ψ]
      rw [BlockEmb.val_gψ _ (by rwa [Multiset.card_map])]
      congr 2
      change _ = blockStart b (ℓ + 1) + l
      rw [blockStart_last]
      omega
    · simp only [AlgEquiv.coe_toAlgHom, blackReindex_ψ, BlockEmb.hom_ψ]
      rw [BlockEmb.gψ_of_not_lt _ (by rwa [Multiset.card_map]),
        BlockEmb.gψ_of_not_lt _ (by rwa [Multiset.card_map]), Corner.val_zero, Corner.val_zero,
        map_zero]

end Blocks

end Categorification.Stendhal

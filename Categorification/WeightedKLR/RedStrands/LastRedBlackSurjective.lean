/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LastRedBlackBimodule

/-!
# Surjectivity of the bimodule map of Proposition 4.32

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.6,
Proposition 4.32. The map `g ↦ appendRed(g) · lastRedBlackCrossing` of
`Categorification.Stendhal.lastRedBlackMap` is onto `e_ℓ T_{i+ν} ν_i(e_ℓ)`. Webster's argument:
in a diagram from a loading `(s, λ_ℓ, i)` at the bottom to a loading ending in `λ_ℓ` at the top,
the last red strand and the black strand `i` cross, and the diagram can be isotoped so that this
crossing is at the bottom. Here this is a statement about the standard spanning set of
red-ordered Stendhal diagrams, for a choice of reduced words that ends with the crossing
`s_{N₀}` whenever possible.

## Main results

* `exists_lastRedBlackStendhal`: before taking the violating quotient, every diagram of
  `e_ℓ T̃_{i+ν} ν_i(e_ℓ)` is `appendRed(g) · crossingStendhalCut`.
* `exists_lastRedBlackMap_eq`: every element of `e_ℓ T_{i+ν} ν_i(e_ℓ)` lies in the image of
  `lastRedBlackMap`.
-/

noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA Equiv

variable {I : Type} {ℓ : ℕ} [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I) (ν : Multiset I)

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "N₀" => Multiset.card (stendhalWeight ℓ ν)
local notation "m" => Multiset.card (stendhalWeight (ℓ + 1) νᵢ)

section Combinatorics

variable {i ν}

omit [DecidableEq I] in
theorem card_stendhalWeight_addRed_addBlack :
    Multiset.card (stendhalWeight (ℓ + 1) νᵢ) = N₀ + 2 := by
  simp [stendhalWeight]
  omega

omit [DecidableEq I] in
private theorem card_stendhalWeight_addRed :
    Multiset.card (stendhalWeight (ℓ + 1) ν) = N₀ + 1 := by
  simp [stendhalWeight]
  omega

omit [DecidableEq I] in
private theorem lastRedPosition_val :
    (lastRedPosition ℓ ν : ℕ) = N₀ := by
  simp [lastRedPosition, stendhalWeight]

omit [DecidableEq I] in
private theorem lastRedPosition_addBlack_val :
    (lastRedPosition ℓ νᵢ : ℕ) = N₀ + 1 := by
  simp [lastRedPosition, stendhalWeight]
  omega

/-- The position `N₀` of the last red strand in a loading `(s, λ_ℓ, i)`. -/
def redSlot : Fin m := ⟨N₀, by rw [card_stendhalWeight_addRed_addBlack]; omega⟩

/-- The position `N₀ + 1` of the black strand `i` in a loading `(s, λ_ℓ, i)`. -/
def blackSlot : Fin m := ⟨N₀ + 1, by rw [card_stendhalWeight_addRed_addBlack]; omega⟩

omit [DecidableEq I] in
private theorem red_unique {δ : Multiset (I ⊕ Fin (ℓ + 1))} {ν' : Multiset I}
    (h : δ = stendhalWeight (ℓ + 1) ν') (r : Fin (ℓ + 1)) (s : KLR.Seq δ)
    (a b : Fin δ.card) (ha : s.lbl a = Sum.inr r) (hb : s.lbl b = Sum.inr r) : a = b := by
  classical
  subst δ
  have hred : Multiset.count (Sum.inr r : I ⊕ Fin (ℓ + 1)) (ν'.map Sum.inl) = 0 := by
    apply Multiset.count_eq_zero_of_notMem
    simp
  have hcnt : Multiset.count (Sum.inr r : I ⊕ Fin (ℓ + 1)) (stendhalWeight (ℓ + 1) ν') ≤ 1 := by
    rw [stendhalWeight, Multiset.count_add, hred, zero_add]
    exact Multiset.nodup_iff_count_le_one.mp
      (Finset.univ.nodup.map Sum.inr_injective) _
  have hcard : (Finset.univ.filter (fun a => Sum.inr r = s.lbl a)).card ≤ 1 := by
    rw [← s.2, Multiset.count_map] at hcnt
    exact hcnt
  exact Finset.card_le_one_iff.mp hcard (by simp [ha]) (by simp [hb])

variable (i) in
omit [DecidableEq I] in
theorem appendBlackLoading_redSlot (s : Seq (stendhalWeight (ℓ + 1) ν)) (hs : HasLastRed s) :
    (appendBlackLoading i ν s).lbl (redSlot (i := i) (ν := ν)) = .inr (Fin.last ℓ) := by
  rw [appendBlackLoading_lbl_of_lt i ν s _
    (by change N₀ < _; rw [card_stendhalWeight_addRed]; omega)]
  rw [← hs]
  congr 1
  exact Fin.ext (lastRedPosition_val (ν := ν)).symm

variable (i) in
omit [DecidableEq I] in
theorem appendBlackLoading_blackSlot (s : Seq (stendhalWeight (ℓ + 1) ν)) :
    (appendBlackLoading i ν s).lbl (blackSlot (i := i) (ν := ν)) = .inl i :=
  appendBlackLoading_lbl_of_eq i ν s _ (by
    change N₀ + 1 = _; rw [card_stendhalWeight_addRed])

omit [DecidableEq I] in
private theorem sadj_redSlot :
    sadj m N₀ (redSlot (i := i) (ν := ν)) = blackSlot (i := i) (ν := ν) := by
  apply Fin.ext
  rw [sadj_val_of_lt (by rw [card_stendhalWeight_addRed_addBlack]; omega)]
  simp [swapNat, redSlot, blackSlot]

omit [DecidableEq I] in
private theorem sadj_blackSlot :
    sadj m N₀ (blackSlot (i := i) (ν := ν)) = redSlot (i := i) (ν := ν) := by
  apply Fin.ext
  rw [sadj_val_of_lt (by rw [card_stendhalWeight_addRed_addBlack]; omega)]
  simp [swapNat, redSlot, blackSlot]

variable (i) in
/-- The loading `(s, i, λ_ℓ)` at the top of the crossing. -/
def crossedLoading (s : Seq (stendhalWeight (ℓ + 1) ν)) : Seq (stendhalWeight (ℓ + 1) νᵢ) :=
  sadj m N₀ • appendBlackLoading i ν s

variable (i) in
omit [DecidableEq I] in
theorem hasLastRed_crossedLoading (s : Seq (stendhalWeight (ℓ + 1) ν)) (hs : HasLastRed s) :
    HasLastRed (crossedLoading i s) := by
  have hpos : lastRedPosition ℓ νᵢ = blackSlot (i := i) (ν := ν) :=
    Fin.ext (lastRedPosition_addBlack_val (i := i) (ν := ν))
  change (crossedLoading i s).1 (lastRedPosition ℓ νᵢ) = _
  rw [hpos, crossedLoading, Seq.smul_apply, sadj_symm, sadj_blackSlot]
  exact appendBlackLoading_redSlot i s hs

variable (i) in
omit [DecidableEq I] in
theorem isRedOrdered_crossedLoading (s : Seq (stendhalWeight (ℓ + 1) ν)) (ho : IsRedOrdered s) :
    IsRedOrdered (crossedLoading i s) := by
  have hm := card_stendhalWeight_addRed_addBlack (i := i) (ν := ν) (ℓ := ℓ)
  have hlt : N₀ + 1 < m := by omega
  have ho' := appendBlackLoading_ordered i ν s ho
  intro a b r r' hab ha hb
  change (appendBlackLoading i ν s).1 ((sadj m N₀).symm a) = _ at ha
  change (appendBlackLoading i ν s).1 ((sadj m N₀).symm b) = _ at hb
  rw [sadj_symm] at ha hb
  have hva := sadj_val_of_lt hlt a
  have hvb := sadj_val_of_lt hlt b
  rcases lt_trichotomy (sadj m N₀ a) (sadj m N₀ b) with h | h | h
  · exact ho' _ _ r r' h ha hb
  · exact absurd ((sadj m N₀).injective h) (ne_of_lt hab)
  · have hab' : (a : ℕ) < b := hab
    have h' : (sadj m N₀ b : ℕ) < sadj m N₀ a := h
    rw [hva, hvb] at h'
    have hb0 : (b : ℕ) = N₀ + 1 := by
      rcases swapNat_cases N₀ a with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ <;>
      rcases swapNat_cases N₀ b with ⟨h4, h5⟩ | ⟨h4, h5⟩ | ⟨h4, h5, h6⟩ <;> omega
    have hbs : sadj m N₀ b = redSlot (i := i) (ν := ν) := by
      apply Fin.ext; rw [hvb]; simp [swapNat, hb0, redSlot]
    have ha0 : (a : ℕ) = N₀ := by
      rcases swapNat_cases N₀ a with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ <;>
      rcases swapNat_cases N₀ b with ⟨h4, h5⟩ | ⟨h4, h5⟩ | ⟨h4, h5, h6⟩ <;> omega
    have has : sadj m N₀ a = blackSlot (i := i) (ν := ν) := by
      apply Fin.ext; rw [hva]; simp [swapNat, ha0, blackSlot]
    rw [has] at ha
    exact absurd (ha.symm.trans (appendBlackLoading_blackSlot i s)) (by simp)

omit [DecidableEq I] in
/-- If a permutation carries the last red strand of `(s, λ_ℓ, i)` to the far right, it moves
the strands at `N₀` and `N₀ + 1` out of order. -/
theorem lt_of_hasLastRed_smul (s : Seq (stendhalWeight (ℓ + 1) ν)) (hs : HasLastRed s)
    (w : Perm (Fin m)) (hw : HasLastRed (w • appendBlackLoading i ν s)) :
    w (blackSlot (i := i) (ν := ν)) < w (redSlot (i := i) (ν := ν)) := by
  have hpos : lastRedPosition ℓ νᵢ = blackSlot (i := i) (ν := ν) :=
    Fin.ext (lastRedPosition_addBlack_val (i := i) (ν := ν))
  change (w • appendBlackLoading i ν s).1 (lastRedPosition ℓ νᵢ) = _ at hw
  rw [hpos, Seq.smul_apply] at hw
  have he := red_unique rfl _ _ _ _ hw (appendBlackLoading_redSlot i s hs)
  have hw' : w (redSlot (i := i) (ν := ν)) = blackSlot (i := i) (ν := ν) := by
    rw [← he]; exact w.apply_symm_apply _
  rw [hw']
  have hne : w (blackSlot (i := i) (ν := ν)) ≠ blackSlot (i := i) (ν := ν) := by
    intro h
    have h2 := w.injective (h.trans hw'.symm)
    have h3 := congrArg Fin.val h2
    simp only [redSlot, blackSlot] at h3
    omega
  have hle := (w (blackSlot (i := i) (ν := ν))).isLt
  have hm := card_stendhalWeight_addRed_addBlack (i := i) (ν := ν) (ℓ := ℓ)
  change (w (blackSlot (i := i) (ν := ν)) : ℕ) < N₀ + 1
  have : (w (blackSlot (i := i) (ν := ν)) : ℕ) ≠ N₀ + 1 := fun h => hne (Fin.ext h)
  omega

/-- Reduced words ending with the crossing `s_{N₀}` whenever the permutation has a descent at
`N₀`. -/
def lastCrossingWord (w : Perm (Fin m)) : List ℕ :=
  if w (blackSlot (i := i) (ν := ν)) < w (redSlot (i := i) (ν := ν)) then
    canWord m (w * sadj m N₀) ++ [N₀]
  else canWord m w

omit [DecidableEq I] in
theorem lastCrossingWord_spec (w : Perm (Fin m)) :
    IsReduced m (lastCrossingWord (i := i) (ν := ν) w) ∧
      wordProd m (lastCrossingWord (i := i) (ν := ν) w) = w := by
  unfold lastCrossingWord
  split_ifs with h
  · have hm := card_stendhalWeight_addRed_addBlack (i := i) (ν := ν) (ℓ := ℓ)
    have hlt : N₀ + 1 < m := by omega
    have hw : wordProd m (canWord m (w * sadj m N₀) ++ [N₀]) = w := by
      rw [wordProd_append, wordProd_canWord, wordProd_singleton, mul_assoc, TypeA.sadj_mul_self,
        mul_one]
    refine ⟨(isReduced_iff_length_le ?_).2 ?_, hw⟩
    · exact validWord_append.2 ⟨validWord_canWord m _, validWord_cons.2 ⟨hlt, validWord_nil m⟩⟩
    · rw [hw, List.length_append, length_canWord, List.length_singleton]
      exact (length_mul_sadj_of_gt hlt h).le
  · exact ⟨isReduced_canWord m w, wordProd_canWord m w⟩

end Combinatorics

section Stendhal

local notation "A" => StendhalAlgebraAllOrders k Q Λ νᵢ
local notation "P'" => StendhalAlgebraAllOrders.redOrderedIdem k Q Λ νᵢ
local notation "S₀" => StendhalAlgebra k Q (Λ ∘ Fin.castSucc) ν
local notation "S" => StendhalAlgebra k Q Λ νᵢ
local notation "E" => StendhalAlgebra.lastRedIdem Q Λ νᵢ

/-- Webster's map of Proposition 4.32 before taking the violating quotient:
`g ↦ appendRed(g) · crossingStendhalCut`. -/
def lastRedBlackStendhal : StendhalAlgebra k Q (Λ ∘ Fin.castSucc) νᵢ →ₗ[k] S where
  toFun g := appendRedStendhalValue Q Λ νᵢ g * crossingStendhalCut Q Λ i ν
  map_add' g g' := by rw [map_add, add_mul]
  map_smul' c g := by rw [appendRedStendhalValue_smul, smul_mul_assoc]; rfl

theorem lastRedBlackStendhal_apply (g : StendhalAlgebra k Q (Λ ∘ Fin.castSucc) νᵢ) :
    lastRedBlackStendhal Q Λ i ν g =
      appendRedStendhalValue Q Λ νᵢ g * crossingStendhalCut Q Λ i ν := rfl

local instance : Fintype { s : Seq (stendhalWeight (ℓ + 1) ν) // IsRedOrdered s ∧ HasLastRed s } :=
  Fintype.ofFinite _

private theorem sandwich_mem_corner' (z : A) : P' * z * P' ∈ Subsemigroup.corner P' := by
  have h := (StendhalAlgebraAllOrders.isIdempotentElem_redOrderedIdem (k := k) (Q := Q)
    (Λ := Λ) (ν := νᵢ)).eq
  apply (Subsemigroup.mem_corner_iff
    StendhalAlgebraAllOrders.isIdempotentElem_redOrderedIdem).2
  exact ⟨by simp only [← mul_assoc, h], by simp only [mul_assoc, h]⟩

/-- "Red strand, then black strand" on the unit is the sum of the idempotents of the loadings
`(s, λ_ℓ, i)`. -/
theorem redBlackStendhal_one_eq_sum :
    redBlackStendhal Q Λ i ν 1 =
      ∑ u : { s : Seq (stendhalWeight (ℓ + 1) ν) // IsRedOrdered s ∧ HasLastRed s },
        StendhalAlgebra.e (Q := Q) (Λ := Λ) (appendBlackLoading i ν u.1)
          (appendBlackLoading_ordered i ν u.1 u.2.1) := by
  apply Subtype.ext
  rw [KLR.Corner.val_sum]
  change (appendBlackAllOrders Q Λ i ν (appendRedStendhalValue Q Λ ν 1).val).val = _
  rw [appendRedStendhalValue_one, lastRedIdem_val_eq_sum, map_sum, KLR.Corner.val_sum]
  exact Finset.sum_congr rfl fun u _ => appendBlackAllOrders_e Q Λ i ν u.1

private theorem e_mul_redBlackStendhal_one (u : Seq (stendhalWeight (ℓ + 1) ν))
    (ho : IsRedOrdered u) (hu : HasLastRed u) :
    StendhalAlgebra.e (Q := Q) (Λ := Λ) (appendBlackLoading i ν u)
        (appendBlackLoading_ordered i ν u ho) * redBlackStendhal Q Λ i ν 1 =
      StendhalAlgebra.e (appendBlackLoading i ν u) (appendBlackLoading_ordered i ν u ho) := by
  rw [← appendBlackStendhal_e Q Λ i ν u ho]
  change appendBlackStendhal Q Λ i ν _ *
    appendBlackStendhal Q Λ i ν (appendRedStendhalValue Q Λ ν 1) = _
  rw [appendRedStendhalValue_one, ← map_mul, StendhalAlgebra.e_mul_lastRedIdem, ite_eq_left_of_eq_true _ _ (eq_true hu)]

/-- The terms of the spanning set with bottom loading `(u, λ_ℓ, i)`: cut by `e_ℓ` on top, they
are `appendRed(g) · crossingStendhalCut`. -/
private theorem lastRedIdem_mul_stendhalTerm_mem (u : Seq (stendhalWeight (ℓ + 1) ν))
    (ho : IsRedOrdered u) (hu : HasLastRed u)
    (b : {b // IsStendhalTerm (lastCrossingWord (i := i) (ν := ν)) b})
    (hb : b.1.1 = appendBlackLoading i ν u) :
    E * stendhalTerm Q Λ (fun w => (lastCrossingWord_spec (i := i) (ν := ν) w).2) b ∈
      LinearMap.range (lastRedBlackStendhal Q Λ i ν) := by
  obtain ⟨⟨s, w, f⟩, hst⟩ := b
  dsimp only at hb
  subst hb
  set T := stendhalTerm Q Λ (fun w => (lastCrossingWord_spec (i := i) (ν := ν) w).2)
    ⟨(appendBlackLoading i ν u, w, f), hst⟩ with hT
  have h1 : StendhalAlgebra.e _ hst.2.1 * T = T := by
    rw [hT, e_mul_stendhalTerm, ite_eq_left_of_eq_true _ _ (eq_true rfl)]
  by_cases hw : HasLastRed (w • appendBlackLoading i ν u)
  swap
  · rw [← h1, ← mul_assoc, StendhalAlgebra.lastRedIdem_mul_e, ite_eq_right_of_eq_false _ _ (eq_false hw), zero_mul]
    exact zero_mem _
  have hlt := lt_of_hasLastRed_smul u hu w hw
  have hm := card_stendhalWeight_addRed_addBlack (i := i) (ν := ν) (ℓ := ℓ)
  have hlt' : N₀ + 1 < m := by omega
  have hρ : lastCrossingWord (i := i) (ν := ν) w = canWord m (w * sadj m N₀) ++ [N₀] := by
    rw [lastCrossingWord, ite_eq_left_of_eq_true _ _ (eq_true hlt)]
  have hne : (appendBlackLoading i ν u).1 ⟨N₀, by omega⟩ ≠
      (appendBlackLoading i ν u).1 ⟨N₀ + 1, hlt'⟩ := by
    change (appendBlackLoading i ν u).lbl (redSlot (i := i) (ν := ν)) ≠
      (appendBlackLoading i ν u).lbl (blackSlot (i := i) (ν := ν))
    rw [appendBlackLoading_redSlot i u hu, appendBlackLoading_blackSlot i u]
    simp
  set s' := crossedLoading i u with hs'
  set Y : A := StendhalAlgebraAllOrders.ofKLR k Q Λ νᵢ
    (KLRAlgebra.ψw (canWord m (w * sadj m N₀)) *
      KLRAlgebra.pol (swapPol N₀ hlt' (MvPolynomial.monomial f 1))) with hY
  have hTval : T.val = Y * (StendhalAlgebraAllOrders.ψ N₀ *
      StendhalAlgebraAllOrders.e (appendBlackLoading i ν u)) := by
    rw [hT, stendhalTerm_val, KLRAlgebra.stdElt]
    dsimp only
    rw [hρ, ψw_append, ψw_cons, ψw_nil, mul_one, mul_assoc (ψw _), mul_assoc (ψw _),
      ψ_mul_pol_mul_e_of_ne N₀ hlt' hne]
    simp only [hY, StendhalAlgebraAllOrders.ψ, StendhalAlgebraAllOrders.e, map_mul, mul_assoc]
  have hrb : StendhalAlgebraAllOrders.e (appendBlackLoading i ν u) *
      redBlackValue Q Λ i ν (1 : S₀).val = StendhalAlgebraAllOrders.e (appendBlackLoading i ν u) :=
    congrArg Subtype.val (e_mul_redBlackStendhal_one Q Λ i ν u ho hu)
  have hcut : StendhalAlgebraAllOrders.ψ N₀ * StendhalAlgebraAllOrders.e (appendBlackLoading i ν u)
      = StendhalAlgebraAllOrders.e s' * (crossingStendhalCut Q Λ i ν).val := by
    rw [← hrb, ← mul_assoc, StendhalAlgebraAllOrders.ψ_mul_e, mul_assoc,
      ← crossingStendhalCut_val]
    rfl
  have hs'o := isRedOrdered_crossedLoading i u ho
  have hs'l := hasLastRed_crossedLoading i u hu
  let W : S := ⟨P' * (Y * StendhalAlgebraAllOrders.e s') * P', sandwich_mem_corner' Q Λ i ν _⟩
  obtain ⟨v, hv⟩ := exists_appendRedStendhalValue Q Λ νᵢ W
  refine ⟨v, ?_⟩
  rw [lastRedBlackStendhal_apply, hv]
  apply KLR.Corner.val_injective
  have r1 : (E).val * P' = (E).val := KLR.Corner.val_mul_E E
  have r2 : StendhalAlgebraAllOrders.e s' * P' = StendhalAlgebraAllOrders.e s' := by
    rw [StendhalAlgebraAllOrders.e_mul_redOrderedIdem, ite_eq_left_of_eq_true _ _ (eq_true hs'o)]
  have r3 : StendhalAlgebraAllOrders.e s' * (E).val = StendhalAlgebraAllOrders.e s' := by
    have := congrArg Subtype.val (StendhalAlgebra.e_mul_lastRedIdem Q Λ νᵢ s' hs'o)
    rw [ite_eq_left_of_eq_true _ _ (eq_true hs'l), KLR.Corner.val_mul] at this
    exact this
  change (E).val * (P' * (Y * StendhalAlgebraAllOrders.e s') * P') * (E).val *
    (crossingStendhalCut Q Λ i ν).val = (E).val * T.val
  rw [hTval, hcut]
  calc (E).val * (P' * (Y * StendhalAlgebraAllOrders.e s') * P') * (E).val *
        (crossingStendhalCut Q Λ i ν).val
      = ((E).val * P') * Y * (StendhalAlgebraAllOrders.e s' * P') * (E).val *
        (crossingStendhalCut Q Λ i ν).val := by simp only [mul_assoc]
    _ = (E).val * Y * (StendhalAlgebraAllOrders.e s' * (E).val) *
        (crossingStendhalCut Q Λ i ν).val := by rw [r1, r2]; simp only [mul_assoc]
    _ = _ := by rw [r3]; simp only [mul_assoc]

/-- **Every diagram of `e_ℓ T̃_{i+ν} ν_i(e_ℓ)` factors through the crossing** (Webster,
arXiv:1309.3796v3, proof of Proposition 4.32, before taking the violating quotient): it is
`appendRed(g) · crossingStendhalCut` for a diagram `g` on the first `ℓ` red strands. -/
theorem exists_lastRedBlackStendhal (x : S) :
    ∃ g, lastRedBlackStendhal Q Λ i ν g = E * x * redBlackStendhal Q Λ i ν 1 := by
  change E * x * redBlackStendhal Q Λ i ν 1 ∈ LinearMap.range (lastRedBlackStendhal Q Λ i ν)
  rw [redBlackStendhal_one_eq_sum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun u _ => ?_
  have hx : x ∈ Submodule.span k (Set.range (stendhalTerm Q Λ
      (fun w => (lastCrossingWord_spec (i := i) (ν := ν) w).2))) :=
    span_stendhalTerm (Q := Q) (Λ := Λ) (ν := νᵢ)
      (lastCrossingWord_spec (i := i) (ν := ν)) Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, rfl⟩ := hy
    rw [mul_assoc, stendhalTerm_mul_e]
    split_ifs with hb
    · exact lastRedIdem_mul_stendhalTerm_mem Q Λ i ν u.1 u.2.1 u.2.2 b hb
    · rw [mul_zero]; exact zero_mem _
  | zero => rw [mul_zero, zero_mul]; exact zero_mem _
  | add y z _ _ hy hz => rw [mul_add, add_mul]; exact add_mem hy hz
  | smul c y _ hy => rw [mul_smul_comm, smul_mul_assoc]; exact Submodule.smul_mem _ c hy

end Stendhal

section Quotient

local notation "T'" => TensorProductAlgebra k Q Λ νᵢ
local notation "π'" => TensorProductAlgebra.mk Q Λ νᵢ

/-- **Surjectivity in Proposition 4.32** (Webster, arXiv:1309.3796v3): every element of
`e_ℓ T_{i+ν} ν_i(e_ℓ)` is in the image of `lastRedBlackMap`. -/
theorem exists_lastRedBlackMap_eq (y : T')
    (hy : TensorProductAlgebra.lastRedIdem Q Λ νᵢ * y *
      appendBlack Q Λ i ν (TensorProductAlgebra.lastRedIdem Q Λ ν) = y) :
    ∃ g, lastRedBlackMap Q Λ i ν g = y := by
  have hs : Function.Surjective (TensorProductAlgebra.mk (k := k) Q Λ νᵢ) :=
    (StendhalAlgebra.violatedIdeal k Q Λ νᵢ).ringCon.mk'_surjective
  obtain ⟨x, rfl⟩ := hs y
  have h : appendBlack Q Λ i ν (TensorProductAlgebra.lastRedIdem Q Λ ν) =
      π' (redBlackStendhal Q Λ i ν 1) := by
    rw [TensorProductAlgebra.lastRedIdem, ← appendRedStendhalValue_one]
    rfl
  obtain ⟨g, hg⟩ := exists_lastRedBlackStendhal Q Λ i ν x
  refine ⟨TensorProductAlgebra.mk Q (Λ ∘ Fin.castSucc) νᵢ g, ?_⟩
  rw [← hy, h, TensorProductAlgebra.lastRedIdem, ← map_mul, ← map_mul, ← hg,
    lastRedBlackMap_apply, appendRed_mk_val, lastRedBlackCrossing, lastRedBlackStendhal_apply,
    map_mul]

end Quotient

end Categorification.Stendhal

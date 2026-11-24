/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockShuffleColumnKernel
import Categorification.WeightedKLR.RedStrands.BlockPairedCrossingTensor
import Categorification.WeightedKLR.RedStrands.BlockShuffleJointLoading
import Categorification.WeightedKLR.RedStrands.BraidedFactorization

/-!
# Right crossing on the adjacent source column

In Webster (arXiv:1309.3796v2), §6.1, the internal multiplier in the
kernel test (6.21) is the ordered loading-projective crossing of the
paired block. The matching loadings and their projector supports identify
this multiplier before the spectator tensor argument.
-/

noncomputable section
namespace Categorification.Stendhal.RedBlock

open Equiv KLR KLRAlgebra TypeA BraidedStendhalAlgebra

variable {I : Type} [DecidableEq I] {k : Type*} [Field k] {ℓ : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (hQ : KLRSymm Q)
    (L M : List (Fin ℓ × Multiset I)) (f : Fin 2 ↪ Fin ℓ) (β : Multiset I)

local notation "row" => adjacentRow L M f β
local notation "m" => Multiset.card (weightSum row)
local notation "P" => projection Q Λ row
local notation "B₀" => (RedBlock.mk 2 f β)
local notation "W" => Λ ∘ f
local notation "F" => tensorOfKLR Q W β
local notation "T" => TensorProductAlgebra k Q W β
local notation "E" => orderedIdem Q Λ (fun _ => 1) row
local notation "κ" => L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst

include hQ in
/-- The internal column multiplier is injective once the ordered local crossing is
injective for the labels of the distinguished pair. -/
theorem internalColumnDiagonal_eq_zero {ν : Multiset I}
    (h : weightSum row = stendhalWeight ℓ ν)
    (j : ℕ) (hj : j+1 < m) (s : Seq (weightSum row))
    (i : I)
    (hOracle : ∀ (t : Seq (B₀).localWeight) (b : ℕ) (hb : b+1 < (B₀).localWeight.card),
      IsRedOrdered t → t.lbl ⟨b, by omega⟩ = .inl i → t.lbl ⟨b+1,hb⟩ = .inr 1 →
      ∀ y : T, y * F (e t) = y →
        y * F (ψ b * e (sadj (B₀).localWeight.card b • t)) = 0 → y = 0)
    (horder : redWord (Seq.cast h (sadj m j • s)) = κ)
    (hblack : (sadj m j • s).lbl ⟨j,by omega⟩ = .inl i)
    (hred : (sadj m j • s).lbl ⟨j+1,hj⟩ = .inr (f 1))
    (u : ShuffleIndex row) (z₀ z : diagrams Q Λ row)
    (p₀ : IndexedLoadingProjector Q Λ row u (sadj m j • s) z₀)
    (p : IndexedLoadingProjector Q Λ row u s z) (hnz : P z₀ ≠ 0)
    (ha : shufflePerm row u ⟨j,by omega⟩ < shufflePerm row u ⟨j+1,hj⟩)
    (hsame : SameInputBlock row u j hj)
    (x : quotients Q Λ row) (hleft : P E * x = x) (hsource : x * P z₀ = x)
    (hzero : x * (P (insideCrossing Q Λ row (shufflePerm row u ⟨j,by omega⟩).val) * P z) = 0) :
    x = 0 := by
  let q := shufflePerm row u
  let a := (q ⟨j,by omega⟩).val
  rcases shuffleWord_right_ascent row u j hj ha with
    ⟨v, ⟨hv, _, hvbad⟩, _⟩ | ⟨_, hInside, hconsecutive, hperm⟩
  · exact (hvbad ((sameInputBlock_swap_iff row u v j hj hv).2 hsame)).elim
  rcases p₀.support with hz | ⟨v, hv, htop, hz⟩
  · exact (hnz (by rw [hz, map_zero])).elim
  change q • (sadj m j • s) = place row v at htop
  have hc : a + 1 < m := hconsecutive ▸ (q ⟨j+1,hj⟩).isLt
  have hix : (⟨a,by omega⟩ : Fin m) = q ⟨j,by omega⟩ := Fin.ext rfl
  have hiy : (⟨a+1,hc⟩ : Fin m) = q ⟨j+1,hj⟩ := Fin.ext hconsecutive.symm
  have hbl : (place row v).lbl ⟨a,by omega⟩ = .inl i := by
    rw [hix, ← htop]
    change (sadj m j • s).lbl (q.symm (q ⟨j,by omega⟩)) = _
    rwa [q.symm_apply_apply]
  have hrd : (place row v).lbl ⟨a+1,hc⟩ = .inr (f 1) := by
    rw [hiy, ← htop]
    change (sadj m j • s).lbl (q.symm (q ⟨j+1,hj⟩)) = _
    rwa [q.symm_apply_apply]
  have hnd : (κ).Nodup := horder ▸ redWord_nodup _
  have hL : f 1 ∉ L.map Prod.fst := fun hm =>
    (List.nodup_append.mp hnd).2.2 (f 1) hm (f 1) (List.mem_cons_of_mem _ List.mem_cons_self) rfl
  have hM : f 1 ∉ M.map Prod.fst := (List.nodup_cons.mp (List.nodup_cons.mp
    (List.nodup_append.mp hnd).2.1).2).1
  obtain ⟨b,hb,hab,hbi,hbr⟩ := insideBlock_pair_labels L M f β v hc hL hM hInside hbl hrd
  have hb' : b+1 < (B₀).weight.card := by
    rwa [Multiset.card_map]
  let t := swapPairLoading M f β b L v
  have hsrc : swapPairLoading M f β b L t = v := swapPairLoading_involutive M f β b L v
  have ht : q • s = place row t := by
    rw [place_swapPairLoading M f β b hb', ← hab, ← htop, ← mul_smul]
    change q • s = (sadj m a * q) • (sadj m j • s)
    rw [← hperm, mul_smul, ← mul_smul (sadj m j), TypeA.sadj_mul_self, one_smul]
  have hzt : z = loadingIdem Q Λ row t := p.matched t ht
  have hord : redWord (Seq.cast h (place row v)) = κ :=
    (redWord_place_eq_of_shuffleLoading L M f β h _ v hv horder).symm.trans horder
  have huv := (uncrossedLoading_iff L M f β h v).2 hord
  have hvs := redWord_pairLoading M f β L v huv
  have hvt : redWord (pairLoading M f β L t) = List.finRange 2 := by
    change redWord (pairLoading M f β L (swapPairLoading M f β b L v)) = _
    rw [pairLoading_swapPairLoading, redWord_sadj_smul _ hb (by simp [hbi]), hvs]
  have hback : sadj (B₀).localWeight.card b • pairLoading M f β L t = pairLoading M f β L v := by
    rw [← pairLoading_swapPairLoading, hsrc]
  have hlocal := hOracle (pairLoading M f β L v) b hb
    ((redWord_eq_finRange_iff _).1 hvs) hbi hbr
  have hinj : ∀ y : T,
      y * F (e (sadj (B₀).localWeight.card b • pairLoading M f β L t)) = y →
      y * F (ψ b * e (pairLoading M f β L t)) = 0 → y = 0 := by
    intro y hy hz'
    rw [hback] at hy
    apply hlocal y hy
    simpa only [pairLoading_swapPairLoading, t] using hz'
  have hTensor := (pairedCrossing_eq_zero Q Λ hQ M f β b hb' L t hvt (hback ▸ hvs) hinj).2
  apply hTensor x hleft
  · rwa [hsrc, ← hz]
  · rw [← hab, ← hzt, map_mul]
    exact hzero

omit [DecidableEq I] in
private theorem cast_adjacent_smul {δ δ' : Multiset (I ⊕ Fin ℓ)}
    (h : δ = δ') (j : ℕ) (s : Seq δ) :
    Seq.cast h (sadj δ.card j • s) = sadj δ'.card j • Seq.cast h s := by subst δ'; rfl

variable {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "J" => blockUpperIdeal k Q Λ ν (f 0) (f 1)
  (fun r i => boundaryCount (cut (f 0) (f 1) r) i row) κ
local notation "π" => AlgHom.comp (RingCon.mkₐ k (TwoSidedIdeal.ringCon J))
  (AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν))

include hQ in
/-- The right joint crossing detects zero in the source-order column whenever the
ordered two-red loading-projective multiplier detects zero. -/
theorem blockColumn_eq_zero_of_ordered_paired_crossing
    (h : weightSum row = μ) (t s : Seq μ) (j : ℕ) (hj : j+1 < m) (i : I)
    (hOracle : ∀ (r : Seq (B₀).localWeight) (b : ℕ) (hb : b+1 < (B₀).localWeight.card),
      IsRedOrdered r → r.lbl ⟨b, by omega⟩ = .inl i → r.lbl ⟨b+1,hb⟩ = .inr 1 →
      ∀ y : T, y * F (e r) = y →
        y * F (ψ b * e (sadj (B₀).localWeight.card b • r)) = 0 → y = 0)
    (ht : redWord t = κ) :
    let s₀ := sadj (Multiset.card μ) j • s
    let source := Seq.cast h.symm s₀
    redWord s₀ = κ → source.lbl ⟨j,by omega⟩ = .inl i → source.lbl ⟨j+1,hj⟩ = .inr (f 1) →
    ∀ x : blockColumn Q Λ L M f β h,
      π (e t) * x.1 = x.1 → x.1 * π (e s₀) = x.1 → x.1 * π (ψ j * e s) = 0 → x = 0 := by
  intro s₀ source hord hbl hre x hleft hsource hz
  apply blockColumn_eq_zero_of_internal_crossing Q Λ L M f β hQ h t s j hj ht i (f 1)
    hord hbl hre _ x hleft hsource hz
  intro u z₀ z p₀ p hnonzero ha hsame c hleft' hsource' hzero
  have hc : source = sadj m j • Seq.cast h.symm s := cast_adjacent_smul h.symm j s
  have ho : redWord (Seq.cast h (sadj m j • Seq.cast h.symm s)) = κ := by
    have roundtrip {δ δ' : Multiset (I ⊕ Fin ℓ)} (e : δ = δ') (r : Seq δ') :
        Seq.cast e (Seq.cast e.symm r) = r := by subst δ'; rfl
    rw [← hc, show Seq.cast h source = s₀ from roundtrip h s₀]
    exact hord
  exact internalColumnDiagonal_eq_zero Q Λ hQ L M f β h j hj (Seq.cast h.symm s) i
    hOracle ho (hc ▸ hbl) (hc ▸ hre) u z₀ z (hc ▸ p₀) p hnonzero ha hsame
    c hleft' hsource' hzero

end Categorification.Stendhal.RedBlock

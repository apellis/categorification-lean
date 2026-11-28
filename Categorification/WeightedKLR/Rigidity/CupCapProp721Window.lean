/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapDiagrams
import Categorification.WeightedKLR.RedStrands.BlackInduction
import Categorification.KLR.BlockEmbCompose

/-!
# Appending a black strand commutes with the diagrams at the maximum

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21 (the bimodules of `𝔉_i ∘ 𝕂` and `𝕂 ∘ 𝔉_i`, as in the proof of Proposition 6.7).
The functor `𝔉_i` on right modules appends a black strand of colour `i` at the far right
(`Stendhal.appendBlack`). Below a cap generator at a loading `s` of `λ` and `n` strands left of the
maximum, the diagrams at the maximum are placed on the window `[n, n + N)` of `λ⁺`
(`CupCap.insertMap`). Appending the strand at the right of the bottom of `λ⁺` and placing the
window below the generator at the appended loading `s i` of `λ` give the same diagram
(`CupCap.appendPlus_insertMap`).

At the level of KLR algebras, appending the strand is the first block embedding of
`ρ + {i}` (`KLRAlgebra.blockL`), followed by the identification of the weight
`ρ + {i}` of `λ⁺` with the weight of `λ⁺` at the black weight `({i} + ν) + ν₀`
(`CupCap.appendPlus`).

## Main definitions

* `CupCap.plusAddBlack`: the identification of weights.
* `CupCap.appendPlus`: appending the black strand to a KLR diagram of `λ⁺`.

## Main results

* `CupCap.insertSeq_appendBlackLoading`: the bottom loadings agree.
* `CupCap.appendPlus_insertMap`: the diagrams at the maximum agree.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra MvPolynomial

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  (j : ℕ) (hj : j ≤ ℓ) (ν ν₀ : Multiset I) (i : I)

local notation "σᵢ" => (Singleton.singleton (Sum.inl i) : Multiset (I ⊕ Fin (ℓ + 2)))
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "ρ" => stendhalWeight (ℓ + 2) (ν + ν₀)
local notation "ρᵢ" => stendhalWeight (ℓ + 2) (νᵢ + ν₀)
local notation "S⁺" => stendhalQ Q (plusLabels Λ Λc j hj)

omit [DecidableEq I] in
/-- The weight of `λ⁺` with a black strand of colour `i` added at the right is the weight of
`λ⁺` at the black weight `({i} + ν) + ν₀`. -/
theorem plusAddBlack : ρ + σᵢ = ρᵢ := by
  rw [stendhalWeight_addBlack (ℓ := ℓ + 2) i (ν + ν₀), add_assoc]

/-- **Appending a black strand of colour `i` at the right** of a KLR diagram of `λ⁺`: the first
block embedding of `ρ + {i}`, transported to the weight of `λ⁺` at `({i} + ν) + ν₀`. -/
def appendPlus : KLRAlgebra k S⁺ ρ →ₙₐ[k] KLRAlgebra k S⁺ ρᵢ where
  toFun z := castKLR S⁺ (plusAddBlack ν ν₀ i) ((blockL ρ σᵢ).hom S⁺ z).val
  map_zero' := by rw [map_zero, Corner.val_zero, map_zero]
  map_add' x y := by rw [map_add, Corner.val_add, map_add]
  map_mul' x y := by rw [map_mul, Corner.val_mul, map_mul]
  map_smul' c z := by rw [map_smul, Corner.val_smul, map_smul]; rfl

theorem appendPlus_apply (z : KLRAlgebra k S⁺ ρ) :
    appendPlus Q Λ Λc j hj ν ν₀ i z =
      castKLR S⁺ (plusAddBlack ν ν₀ i) ((blockL ρ σᵢ).hom S⁺ z).val := rfl

section Loadings

variable {Q Λ Λc j hj ν ν₀ i}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)

omit [DecidableEq I] in
theorem card_appendBlackWeight :
    Multiset.card (stendhalWeight ℓ νᵢ) = m + 1 := by
  rw [← stendhalWeight_addBlack i ν, Multiset.card_add, Multiset.card_singleton]

omit [DecidableEq I] in
/-- **The bottom loadings agree**: appending a black strand `i` at the right of the bottom
loading of the cap generator at `s` and `n` gives the bottom loading of the cap generator at
the appended loading `s i` and `n`. -/
theorem insertSeq_appendBlackLoading (s : Seq (stendhalWeight ℓ ν)) (n : ℕ) (hn : n ≤ m)
    (hn' : n ≤ Multiset.card (stendhalWeight ℓ νᵢ))
    (t : Seq ((stendhalWeight 2 ν₀).map (cupColour j hj))) :
    Seq.cast (plusAddBlack ν ν₀ i)
        ((insertSeq (j := j) (hj := hj) (ν₀ := ν₀) s n hn t).append (default : Seq σᵢ)) =
      insertSeq (j := j) (hj := hj) (ν₀ := ν₀) (appendBlackLoading i ν s) n hn' t := by
  have hρ := card_plus j hj ν ν₀
  have hρ' := card_plus j hj νᵢ ν₀
  have hm := card_appendBlackWeight (ℓ := ℓ) (ν := ν) (i := i)
  apply Subtype.ext
  funext c
  simp only [Seq.cast_apply]
  by_cases hc : c.val < Multiset.card ρ
  · rw [Seq.append_apply_lt _ _ _ (by simp only [Fin.val_cast]; exact hc)]
    simp only [insertSeq, Function.comp_apply, insertPos, Equiv.coe_fn_symm_mk, Fin.val_cast]
    split_ifs with h1 h2 <;> try omega
    · simp only [Sum.elim_inl, Function.comp_apply]
      exact congrArg _ (appendBlackLoading_lbl_of_lt i ν s ⟨c.val, by omega⟩
        (show c.val < m by omega)).symm
    · rfl
    · simp only [Sum.elim_inl, Function.comp_apply]
      exact congrArg _ (appendBlackLoading_lbl_of_lt i ν s
        ⟨c.val - Multiset.card ((stendhalWeight 2 ν₀).map (cupColour j hj)), by omega⟩
        (show c.val - Multiset.card ((stendhalWeight 2 ν₀).map (cupColour j hj)) < m by
          omega)).symm
  · have hc' : c.val = Multiset.card ρ := by
      have := c.2
      have h2 := congrArg Multiset.card (plusAddBlack (ℓ := ℓ) ν ν₀ i)
      rw [Multiset.card_add, Multiset.card_singleton] at h2
      omega
    rw [Seq.append_apply_ge _ _ _ (by simp only [Fin.val_cast]; omega),
      Multiset.mem_singleton.mp ((default : Seq σᵢ).mem _)]
    simp only [insertSeq, Function.comp_apply, insertPos, Equiv.coe_fn_symm_mk, Fin.val_cast]
    split_ifs with h1 h2 <;> try omega
    simp only [Sum.elim_inl, Function.comp_apply]
    exact (congrArg (oldColour j hj)
      (appendBlackLoading_lbl_of_eq i ν s _ (by simp only; omega))).symm

end Loadings

section Generators

variable {Q Λ Λc j hj ν ν₀ i}

/-- Appending the strand to an idempotent. -/
theorem appendPlus_e (w : Seq ρ) :
    appendPlus Q Λ Λc j hj ν ν₀ i (KLRAlgebra.e w) =
      KLRAlgebra.e (Seq.cast (plusAddBlack ν ν₀ i) (w.append (default : Seq σᵢ))) := by
  have hf : (blockL ρ σᵢ).F w = {w.append (default : Seq σᵢ)} := by
    ext u
    change u ∈ Finset.univ.image (fun a : Seq σᵢ => w.append a) ↔ _
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun ⟨a, ha⟩ => ha ▸ congrArg w.append (Subsingleton.elim a default),
      fun h => ⟨default, h.symm⟩⟩
  rw [appendPlus_apply, BlockEmb.hom_e, BlockEmb.val_gE, BlockEmb.eF, hf, eSum,
    Finset.sum_singleton, castKLR_e]

/-- Appending the strand to a dot. -/
theorem appendPlus_x (c : Fin (Multiset.card ρ)) :
    appendPlus Q Λ Λc j hj ν ν₀ i (KLRAlgebra.x c) =
      KLRAlgebra.x (Fin.cast (congrArg Multiset.card (plusAddBlack ν ν₀ i)) (Seq.posL σᵢ c)) *
        appendPlus Q Λ Λc j hj ν ν₀ i 1 := by
  rw [appendPlus_apply, appendPlus_apply, BlockEmb.hom_x, val_polCorner, pol_X, map_mul,
    castKLR_x, map_one, Corner.val_one]
  rfl

/-- Appending the strand to a crossing. -/
theorem appendPlus_ψ {p : ℕ} (hp : p + 1 < Multiset.card ρ) :
    appendPlus Q Λ Λc j hj ν ν₀ i (KLRAlgebra.ψ p) =
      KLRAlgebra.ψ p * appendPlus Q Λ Λc j hj ν ν₀ i 1 := by
  rw [appendPlus_apply, appendPlus_apply, BlockEmb.hom_ψ, BlockEmb.val_gψ _ hp, map_mul,
    castKLR_ψ, map_one, Corner.val_one]
  simp only [blockL, zero_add]

theorem appendPlus_one_mul (z : KLRAlgebra k S⁺ ρ) :
    appendPlus Q Λ Λc j hj ν ν₀ i 1 * appendPlus Q Λ Λc j hj ν ν₀ i z =
      appendPlus Q Λ Λc j hj ν ν₀ i z := by
  rw [← map_mul, one_mul]

local notation "m" => Multiset.card (stendhalWeight ℓ ν)

/-- **Appending a black strand commutes with the diagrams at the maximum** (arXiv:1309.3796v3,
§7.3, proof of Proposition 7.21): appending the strand at the right of the diagram `ι_{s,n}(x)`
placed on the window below the cap generator at `s` and `n` gives the diagram `ι_{s i,n}(x)`
below the cap generator at the appended loading. -/
theorem appendPlus_insertMap (s : Seq (stendhalWeight ℓ ν)) (n : ℕ) (hn : n ≤ m)
    (hn' : n ≤ Multiset.card (stendhalWeight ℓ νᵢ))
    (x : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) :
    appendPlus Q Λ Λc j hj ν ν₀ i (insertMap (j := j) (hj := hj) Q Λ Λc s n hn x) =
      insertMap (j := j) (hj := hj) Q Λ Λc (appendBlackLoading i ν s) n hn' x := by
  set B := insertEmb (j := j) (hj := hj) (ν₀ := ν₀) s n hn
  set D := insertEmb (j := j) (hj := hj) (ν₀ := ν₀) (appendBlackLoading i ν s) n hn'
  set C := appendPlus Q Λ Λc j hj ν ν₀ i
  have hF : ∀ u, (B.hom S⁺ (KLRAlgebra.e u)).val =
      KLRAlgebra.e (insertSeq (j := j) (hj := hj) (ν₀ := ν₀) s n hn u) := fun u => by
    rw [BlockEmb.hom_e, BlockEmb.val_gE, BlockEmb.eF]
    exact Finset.sum_singleton _ _
  have hF' : ∀ u, (D.hom S⁺ (KLRAlgebra.e u)).val =
      KLRAlgebra.e (insertSeq (j := j) (hj := hj) (ν₀ := ν₀) (appendBlackLoading i ν s) n hn' u) :=
    fun u => by
      rw [BlockEmb.hom_e, BlockEmb.val_gE, BlockEmb.eF]
      exact Finset.sum_singleton _ _
  have he : ∀ u, C (B.hom S⁺ (KLRAlgebra.e u)).val = (D.hom S⁺ (KLRAlgebra.e u)).val :=
    fun u => by rw [hF, hF', appendPlus_e, insertSeq_appendBlackLoading]
  have h1 : C (eSum S⁺ (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s n hn)) =
      eSum S⁺ (insertSet (j := j) (hj := hj) (ν₀ := ν₀) (appendBlackLoading i ν s) n hn') := by
    rw [← B.sum_eF, ← D.sum_eF, map_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    have h := he u
    rwa [BlockEmb.hom_e, BlockEmb.hom_e, BlockEmb.val_gE, BlockEmb.val_gE] at h
  have hE : ∀ z, C (z * eSum S⁺ (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s n hn)) =
      C z * eSum S⁺ (insertSet (j := j) (hj := hj) (ν₀ := ν₀) (appendBlackLoading i ν s) n hn') :=
    fun z => by rw [map_mul, h1]
  have hx : ∀ a, C (B.hom S⁺ (KLRAlgebra.x a)).val = (D.hom S⁺ (KLRAlgebra.x a)).val := by
    intro a
    rw [BlockEmb.hom_x, BlockEmb.hom_x, val_polCorner, val_polCorner, pol_X, pol_X, hE,
      appendPlus_x, mul_assoc, ← h1, appendPlus_one_mul, h1]
    congr 2
  have hψ : ∀ q, C (B.hom S⁺ (KLRAlgebra.ψ q)).val = (D.hom S⁺ (KLRAlgebra.ψ q)).val := by
    intro q
    rw [BlockEmb.hom_ψ, BlockEmb.hom_ψ]
    by_cases hq : q + 1 < Multiset.card ((stendhalWeight 2 ν₀).map (cupColour j hj))
    · rw [BlockEmb.val_gψ _ hq, BlockEmb.val_gψ _ hq, hE, appendPlus_ψ (B.lt_card hq),
        mul_assoc, ← h1, appendPlus_one_mul, h1]
      rfl
    · rw [BlockEmb.gψ_of_not_lt _ hq, BlockEmb.gψ_of_not_lt _ hq, Corner.val_zero,
        Corner.val_zero, map_zero]
  exact BlockEmb.map_hom_val_eq B D C (AlgHom.id k _) (AlgHom.id k _) h1 he hx hψ
    (KLRAlgebra.relabelHom (cupRelabel (j := j) (hj := hj) (ν₀ := ν₀) k Q Λ Λc) x)

end Generators

end Categorification.Stendhal.CupCap

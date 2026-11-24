/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockShufflePermutation

/-!
# Internal crossings of a block row

The internal alternative of the right crossing in the proof of Webster
(arXiv:1309.3796v2), §6.1, Lemma 6.8, comes from the ordinary crossing
in one factor of the exterior product of the blocks.
-/

noncomputable section

namespace Categorification.Stendhal.RedBlock

open KLR KLRAlgebra TypeA BraidedStendhalAlgebra
open scoped TensorProduct

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)

local notation "S" => stendhalQ Q Λ
local notation "X" => diagrams Q Λ

omit [DecidableEq I] in
private theorem insideBlock_valid : ∀ (r : List (RedBlock I ℓ)) (c : ℕ), InsideBlock r c → c + 1 < (weightSum r).card := by
  intro r
  induction r with
  | nil => intro _ hc; exact hc.elim
  | cons C r ih =>
    intro c hc
    rcases hc with hc | ⟨d, rfl, hd⟩
    · change c + 1 < (C.weight + weightSum r).card
      rw [Multiset.card_add]
      omega
    · have hv := ih d hd
      change C.weight.card + d + 1 < (C.weight + weightSum r).card
      rw [Multiset.card_add]
      omega

/-- The ordinary crossing embedded in the exterior product of the blocks.
For an internal position, the units fill all the other factors. -/
def insideCrossing : (row : List (RedBlock I ℓ)) → ℕ → X row
  | [], _ => 0
  | B :: row, a =>
    if a + 1 < B.weight.card then
      ofKLR k Q (Λ ∘ B.label) B.black (ψ a) ⊗ₜ[k] (1 : X row)
    else (1 : diagramAlgebra Q Λ B) ⊗ₜ[k] insideCrossing row (a - B.weight.card)

private theorem readBlock_crossing (B : RedBlock I ℓ) (a : ℕ) :
    readBlock Q Λ B (ofKLR k Q (Λ ∘ B.label) B.black (ψ a)) = ψ a := by
  change relabelEquiv _ (toKLR _ _ _ _ (ofKLR _ _ _ _ (ψ a))) = _
  rw [toKLR_ofKLR_ψ]
  exact relabelHom_ψ _ _

/-- Juxtaposition sends the internal block crossing to the ambient crossing
with the block seam projector on the right. -/
private theorem juxtapose_insideCrossing :
    ∀ (row : List (RedBlock I ℓ)) (a : ℕ), InsideBlock row a →
      juxtapose Q Λ row (insideCrossing Q Λ row a) =
        ψ a * juxtapose Q Λ row (1 : X row)
  | [], _, ha => ha.elim
  | B :: row, a, ha => by
    change (a + 1 < B.weight.card ∨ ∃ b, a = B.weight.card + b ∧ InsideBlock row b) at ha
    let T : KLRAlgebra k S (weightSum row) := juxtapose Q Λ row (1 : X row)
    have hunit : juxtapose Q Λ (B :: row) (1 : X (B :: row)) =
        concat (k := k) S B.weight (weightSum row) ((1 : KLRAlgebra k S B.weight) ⊗ₜ[k] T) := by
      change juxtapose Q Λ (B :: row) ((1 : diagramAlgebra Q Λ B) ⊗ₜ[k] (1 : X row)) = _
      rw [juxtapose_tmul, map_one]
    rcases ha with hh | ⟨b, rfl, hb⟩
    · rw [insideCrossing, ite_eq_left hh, juxtapose_tmul, readBlock_crossing, hunit]
      change concat (k := k) S B.weight (weightSum row) (ψ a ⊗ₜ[k] T) = _
      rw [show ((ψ a : KLRAlgebra k S B.weight) ⊗ₜ[k] T) =
        (ψ a ⊗ₜ[k] (1 : KLRAlgebra k S (weightSum row))) * ((1 : KLRAlgebra k S B.weight) ⊗ₜ[k] T) by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul],
        concat_mul, KLR.KLRAlgebra.concat_ψ_tmul_one hh, mul_assoc, oneConcat_mul_concat]
    · have hh : ¬ (B.weight.card + b + 1 < B.weight.card) := by omega
      rw [insideCrossing, ite_eq_right hh, Nat.add_sub_cancel_left, juxtapose_tmul, map_one,
        juxtapose_insideCrossing row b hb, hunit]
      change concat (k := k) S B.weight (weightSum row) (1 ⊗ₜ[k] (ψ b * T)) = _
      rw [show ((1 : KLRAlgebra k S B.weight) ⊗ₜ[k] (ψ b * T)) =
        ((1 : KLRAlgebra k S B.weight) ⊗ₜ[k] (ψ b : KLRAlgebra k S (weightSum row))) *
          ((1 : KLRAlgebra k S B.weight) ⊗ₜ[k] T) by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one],
        concat_mul, concat_one_tmul_ψ (insideBlock_valid row b hb), mul_assoc, oneConcat_mul_concat]

private theorem juxtapose_one_commute_inside :
    ∀ (row : List (RedBlock I ℓ)) (a : ℕ), InsideBlock row a →
      Commute (juxtapose Q Λ row (1 : X row)) (ψ a)
  | [], _, ha => ha.elim
  | B :: row, a, ha => by
    change (a + 1 < B.weight.card ∨ ∃ b, a = B.weight.card + b ∧ InsideBlock row b) at ha
    let T : KLRAlgebra k S (weightSum row) := juxtapose Q Λ row (1 : X row)
    let P := concat (k := k) S B.weight (weightSum row)
    let t : KLRAlgebra k S B.weight ⊗[k] KLRAlgebra k S (weightSum row) := 1 ⊗ₜ[k] T
    have hunit : juxtapose Q Λ (B :: row) (1 : X (B :: row)) = P t := by
      change juxtapose Q Λ (B :: row) ((1 : diagramAlgebra Q Λ B) ⊗ₜ[k] (1 : X row)) = _
      rw [juxtapose_tmul, map_one]
    have hcomm (b : ℕ) (z : KLRAlgebra k S B.weight ⊗[k] KLRAlgebra k S (weightSum row))
        (hc : P z = ψ b * oneConcat S B.weight (weightSum row))
        (hψ : Commute (oneConcat S B.weight (weightSum row) : KLRAlgebra k S (B.weight + weightSum row))
          (ψ b))
        (hz : Commute t z) : Commute (P t) (ψ b) := by
      change P t * ψ b = ψ b * P t
      have ht := concat_mul_oneConcat t
      have hL := oneConcat_mul_concat t
      calc
        P t * ψ b = (P t * oneConcat S B.weight (weightSum row)) * ψ b := by rw [ht]
        _ = P t * P z := by rw [mul_assoc, hψ.eq, hc]
        _ = P z * P t := by rw [← concat_mul, hz.eq, concat_mul]
        _ = ψ b * P t := by rw [hc, mul_assoc, hL]
    rw [hunit]
    rcases ha with hh | ⟨b, rfl, hb⟩
    · refine hcomm a (ψ a ⊗ₜ[k] 1) (KLR.KLRAlgebra.concat_ψ_tmul_one hh) ?_ ?_
      · change (oneConcat S B.weight (weightSum row) * ψ a : KLRAlgebra k S _) = _
        simpa [ψw, shiftWord] using
          (oneConcat_mul_ψw (Q := S) (k := k) (ν := B.weight) (ν' := weightSum row)
            (α := [a]) (α' := []) (by simpa [ValidWord] using hh) (by simp [ValidWord]))
      · change (1 ⊗ₜ[k] T) * (ψ a ⊗ₜ[k] 1) = (ψ a ⊗ₜ[k] 1) * (1 ⊗ₜ[k] T)
        simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    · refine hcomm _ (1 ⊗ₜ[k] ψ b) (concat_one_tmul_ψ (insideBlock_valid row b hb)) ?_ ?_
      · change (oneConcat S B.weight (weightSum row) * ψ (B.weight.card + b) :
          KLRAlgebra k S _) = _
        have hvalid := insideBlock_valid row b hb
        simpa [ψw, shiftWord] using
          (oneConcat_mul_ψw (Q := S) (k := k) (ν := B.weight) (ν' := weightSum row)
            (α := []) (α' := [b]) (by simp [ValidWord]) (by simpa [ValidWord] using hvalid))
      · change (1 ⊗ₜ[k] T) * (1 ⊗ₜ[k] ψ b) = (1 ⊗ₜ[k] ψ b) * (1 ⊗ₜ[k] T)
        simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
        rw [(juxtapose_one_commute_inside row b hb).eq]

variable (L M : List (Fin ℓ × Multiset I)) (f : Fin 2 ↪ Fin ℓ)
    (β : Multiset I) {ν : Multiset I}

local notation "row" => adjacentRow L M f β

/-- The internal crossing embeds into the ambient algebra on the juxtaposed column. -/
theorem affineStackBlocks_insideCrossing
    (h : weightSum row = stendhalWeight ℓ ν) {a : ℕ} (ha : InsideBlock row a) :
    affineStackBlocks Q Λ L M f β h (insideCrossing Q Λ row a) =
      affineStackBlocks Q Λ L M f β h 1 * ψ a := by
  change castKLR S h (juxtapose Q Λ row (insideCrossing Q Λ row a)) =
    castKLR S h (juxtapose Q Λ row 1) * ψ a
  rw [juxtapose_insideCrossing Q Λ row a ha,
    (juxtapose_one_commute_inside Q Λ row a ha).eq.symm, map_mul, castKLR_ψ]

local notation "μ" => stendhalWeight ℓ ν
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "P" => projection Q Λ row
local notation "α" => fun r i => boundaryCount (cut (f 0) (f 1) r) i row
local notation "κ" => L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst
local notation "J" => blockUpperIdeal k Q Λ ν (f 0) (f 1) α κ
local notation "raw" => ofKLR k Q Λ ν
local notation "mk" => violMk k Q Λ ν
local notation "q" => RingCon.mkₐ k (TwoSidedIdeal.ringCon J)

/-- An internal crossing contributes the crossing in its own block to the unchanged
shuffle coordinate. This lemma reads that leading diagram in the quotient. -/
theorem internalCrossing_leading_coordinate
    (h : weightSum row = μ) {n : ℕ}
    (w : Fin n → R) (G : Fin n → (J).ringCon.Quotient →ₗ[k] quotients Q Λ row)
    (bottom : Fin n → Seq μ → diagrams Q Λ row)
    (hleft : ∀ d x y, G d (q (mk (raw (affineStackBlocks Q Λ L M f β h x * y)))) =
      P x * G d (q (mk (raw y))))
    (hright : ∀ d y s, G d (q (mk (raw (y * e s)))) = G d (q (mk (raw y))) * P (bottom d s))
    (hdiag : ∀ d, G d (q (mk (raw (w d)))) = 1)
    (hoff : ∀ d i, d ≠ i → G d (q (mk (raw (w i)))) = 0)
    (i d : Fin n) (s : Seq μ) (ρ : List ℕ)
    (hw : w i = affineStackBlocks Q Λ L M f β h 1 * ψw ρ)
    {a : ℕ} (ha : InsideBlock row a) :
    G d (q (mk (raw (affineStackBlocks Q Λ L M f β h 1 * (ψ a * ψw ρ * e s))))) =
      if d = i then P (insideCrossing Q Λ row a) * P (bottom d s) else 0 := by
  let stack := affineStackBlocks Q Λ L M f β h
  let x := insideCrossing Q Λ row a
  have hunit : stack x * stack 1 = stack x := by rw [← map_mul stack, mul_one]
  have hc : stack 1 * (ψ a * ψw ρ * e s) = stack x * (w i * e s) := by
    rw [hw, ← mul_assoc (stack x) (stack 1 * ψw ρ) (e s),
      ← mul_assoc (stack x) (stack 1) (ψw ρ), hunit,
      affineStackBlocks_insideCrossing Q Λ L M f β h ha]
    simp only [mul_assoc, stack]
  rw [hc, hleft, hright]
  split_ifs with hd
  · subst d
    rw [hdiag, one_mul]
  · rw [hoff _ _ hd, zero_mul, mul_zero]

end Categorification.Stendhal.RedBlock

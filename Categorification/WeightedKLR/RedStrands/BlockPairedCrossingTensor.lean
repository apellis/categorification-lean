/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.OrderedBlockCrossingInjectivity
import Categorification.WeightedKLR.RedStrands.BlockInsideCrossing
import Categorification.WeightedKLR.RedStrands.BlockPairedCrossingLoading

/-!
# Tensor transfer for the internal paired crossing

In the proof of Webster (arXiv:1309.3796v2), §6.1, Lemma 6.8, the
ordered two-red injection implies injectivity on the supported coefficient
after tensoring the unchanged spectator factors over a field.
-/

noncomputable section

namespace Categorification.Stendhal.RedBlock

open KLR KLRAlgebra TypeA BraidedStendhalAlgebra
open scoped TensorProduct

variable {I : Type} [DecidableEq I] {k : Type*} [Field k] {ℓ : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (hQ : KLRSymm Q)

local notation "P" => projection Q Λ
local notation "E" => orderedIdem Q Λ (fun _ => 1)
local notation "D" => loadingIdem Q Λ
local notation "V" => quotients Q Λ

private theorem proj_loadingIdem_sq : ∀ row (x : Loadings row),
    P row (D row x) * P row (D row x) = P row (D row x)
  | [], _ => by simp [loadingIdem]
  | B :: row, x => by
    rw [loadingIdem, projection, Algebra.TensorProduct.map_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, proj_loadingIdem_sq row x.2, ← map_mul, ← map_mul,
      e_mul_self]

include hQ in
private theorem proj_orderedIdem_sq (row : List (RedBlock I ℓ)) :
    P row (E row) * P row (E row) = P row (E row) := by
  rw [← orderedInclusion_one Q Λ hQ, ← map_mul, one_mul]

variable (M : List (Fin ℓ × Multiset I)) (f : Fin 2 ↪ Fin ℓ) (β : Multiset I) (b : ℕ)

local notation "B₀" => (RedBlock.mk 2 f β)
local notation "row" => fun L => adjacentRow L M f β
local notation "Bload" => pairLoading M f β
local notation "swap" => swapPairLoading M f β b
local notation "Cross" => insideCrossing Q Λ
local notation "W" => (Λ ∘ f)
local notation "T" => TensorProductAlgebra k Q W β
local notation "F" => tensorOfKLR Q W β

include hQ in
/-- The supported crossing in the paired block stays injective with every spectator
tensor factor. The local ordered loading-projective injection is the input. -/
theorem pairedCrossing_eq_zero
    (hb : b+1 < (B₀).weight.card) :
    ∀ L (t : Loadings (row L)),
      redWord (Bload L t) = List.finRange 2 →
      redWord (sadj (B₀).localWeight.card b • Bload L t) = List.finRange 2 →
      (∀ y : T, y * F (e (sadj (B₀).localWeight.card b • Bload L t)) = y →
        y * F (ψ b * e (Bload L t)) = 0 → y = 0) →
      let p := P (row L) (E (row L))
      let e₀ := P (row L) (D (row L) (swap L t))
      let c := P (row L) (Cross (row L) (pairOffset L + b) * D (row L) t)
      e₀ * c = c ∧ ∀ x : V (row L), p * x = x → x * e₀ = x → x * c = 0 → x = 0
  | [], t, ht, hs, hinj => by
    intro p e₀ c
    let B := B₀
    let tail := M.map spectator
    let φ := (violMk k Q (Λ ∘ B.label) B.black).comp (ofKLR k Q (Λ ∘ B.label) B.black)
    let pB := orderedValue Q Λ hQ (fun _ => 1) B 1
    let eB := φ (e (sadj B.localWeight.card b • t.1))
    let cB := φ (ψ b * e t.1)
    let pT := P tail (E tail)
    let eT := P tail (D tail t.2)
    have hp : p = pB ⊗ₜ[k] pT := by
      change P (B :: tail) (E (B :: tail)) = _
      dsimp only [pB, pT]
      rw [orderedIdem, projection, Algebra.TensorProduct.map_tmul, orderedValue_one]
    have he : e₀ = eB ⊗ₜ[k] eT := by
      change P (B :: tail) (D (B :: tail) (sadj B.localWeight.card b • t.1, t.2)) = _
      rw [loadingIdem, projection, Algebra.TensorProduct.map_tmul]
      rfl
    have hc : c = cB ⊗ₜ[k] eT := by
      change P (B :: tail) (Cross (B :: tail) (0 + b) * D (B :: tail) t) = _
      rw [Nat.zero_add, insideCrossing, ite_eq_left hb, loadingIdem,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← map_mul, projection,
        Algebra.TensorProduct.map_tmul]
      rfl
    have hpB : pB * pB = pB := by
      change orderedValue Q Λ hQ (fun _ => 1) B 1 *
        orderedValue Q Λ hQ (fun _ => 1) B 1 = _
      rw [← map_mul, one_mul]
    have heB : eB * eB = eB := by
      dsimp only [eB]
      rw [← map_mul, e_mul_self]
    have hBc : eB * cB = cB := by
      dsimp only [eB,cB]
      rw [← map_mul, ψ_mul_e, ← mul_assoc, e_mul_self]
    have hTc : eT * eT = eT := proj_loadingIdem_sq Q Λ tail t.2
    refine ⟨by rw [he, hc, Algebra.TensorProduct.tmul_mul_tmul, hBc, hTc], ?_⟩
    intro x hx hy hz
    rw [hp] at hx
    rw [he] at hy
    rw [hc] at hz
    exact eq_zero_of_mul_right_rightTensor_cut pT eT pB eB cB hpB heB hBc
      (fun z => eq_zero_of_quotient_mul_identity_ψ Q Λ hQ B b t.1 ht hs hinj z) x hx hy hz
  | x :: L, t, ht, hs, hinj => by
    intro p e₀ c
    let B := spectator x
    let tail := row L
    let pB := violMk k Q (Λ ∘ B.label) B.black
      (redProj k Q (Λ ∘ B.label) B.black ((List.finRange B.size).map (1 : Equiv.Perm (Fin B.size))))
    let eB := ((violMk k Q (Λ ∘ B.label) B.black).comp (ofKLR k Q (Λ ∘ B.label) B.black)) (e t.1)
    let pT := P tail (E tail)
    let eT := P tail (D tail (swap L t.2))
    let cT := P tail (Cross tail (pairOffset L + b) * D tail t.2)
    have hp : p = pB ⊗ₜ[k] pT := by
      change P (B :: tail) (E (B :: tail)) = _
      rw [orderedIdem, projection, Algebra.TensorProduct.map_tmul]
    have he : e₀ = eB ⊗ₜ[k] eT := by
      change P (B :: tail) (D (B :: tail) (t.1, swap L t.2)) = _
      rw [loadingIdem, projection, Algebra.TensorProduct.map_tmul]
      rfl
    have hc : c = eB ⊗ₜ[k] cT := by
      change P (B :: tail) (Cross (B :: tail) ((B.weight.card + pairOffset L) + b) *
        D (B :: tail) t) = _
      have hi : ¬ (B.weight.card + (pairOffset L + b) + 1 < B.weight.card) := by omega
      rw [Nat.add_assoc, insideCrossing, ite_eq_right hi, Nat.add_sub_cancel_left,
        loadingIdem, Algebra.TensorProduct.tmul_mul_tmul, one_mul, projection,
        Algebra.TensorProduct.map_tmul]
      rfl
    have hB : eB * eB = eB := by
      dsimp only [eB]
      rw [← map_mul, e_mul_self]
    obtain ⟨hTc, hT⟩ := pairedCrossing_eq_zero hb L t.2 ht hs hinj
    change eT * cT = cT at hTc
    refine ⟨by rw [he, hc, Algebra.TensorProduct.tmul_mul_tmul, hB, hTc], ?_⟩
    intro z hx hy hz
    rw [hp] at hx
    rw [he] at hy
    rw [hc] at hz
    exact eq_zero_of_mul_right_leftTensor_cut pB eB pT eT cT
      (proj_orderedIdem_sq Q Λ hQ tail) (proj_loadingIdem_sq Q Λ tail (swap L t.2))
      hTc hT z hx hy hz

end Categorification.Stendhal.RedBlock

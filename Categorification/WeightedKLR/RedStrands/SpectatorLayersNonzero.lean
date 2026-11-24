/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.InteriorSpectatorKernel

/-!
# Nonzero retained partial standards in one-black content

Webster, arXiv:1309.3796v2, §4.7 and proof of Lemma 6.8 at (6.21).
The boundary character at a nonviolated loading evaluates its idempotent to one.
It annihilates the higher retained trace, so the loading quotient is nonzero
when every red weight at the black colour is positive.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR MulOpposite TypeA
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type} [DecidableEq I] [CommRing k] [Nontrivial k] {ℓ : ℕ} {i : I}
variable (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
local notation "ν₁" => (Singleton.singleton i : Multiset I)
local notation "μ" => stendhalWeight ℓ ν₁
local notation "κ" => List.finRange ℓ
local notation "T" => IsIdempotentElem.Corner (isIdempotentElem_violRedProj k Q Λ ν₁)
variable (t : Seq (stendhalWeight (I := I) ℓ (Singleton.singleton i : Multiset I))) (a b : Fin ℓ)
local notation "P" => fun h => rIdeal (orderedLoadingIdemAt Q Λ κ t h)
local notation "K" => fun h => blockLoadingKernelAt Q Λ t a b κ h

include t a b

omit [Nontrivial k] in
private theorem kernelAt_eq_trace (κ' : List (Fin ℓ)) (hκ : redWord t = κ') :
    blockLoadingKernelAt Q Λ t a b κ' hκ = ModuleFiltration.idempotentTrace
      {d : (IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν₁ κ'))ᵐᵒᵖ |
        ∃ (u : Seq μ) (hu : redWord u = κ'),
        adjacentBlockRoot a b t < adjacentBlockRoot a b u ∧ d = op (orderedLoadingIdemAt Q Λ κ' u hu)}
      (ModuleCat.of _ (rIdeal (orderedLoadingIdemAt Q Λ κ' t hκ))) := by
  subst κ'
  exact blockLoadingKernel_eq_idempotentTrace Q Λ t a b

/-- The boundary character proves the loading quotient is nonzero
with positive red weights at a nonviolated one-black loading. -/
theorem blockPartialStandardAt_nontrivial_of_positive
    (ho : @redWord I ℓ (Singleton.singleton i : Multiset I) t = List.finRange ℓ)
    (hv : ¬ IsViolated t) (hQ : KLRSymm Q) (hΛ : ∀ r, 0 < Λ r i) :
    Nontrivial (blockPartialStandardAt Q Λ t a b κ ho) := by
  let ρ := canWord (Multiset.card μ)
  have hρ : IsReducedChoice ρ := fun w => ⟨isReduced_canWord _ w, wordProd_canWord _ w⟩
  let q : T ≃+* TensorProductAlgebra k Q Λ ν₁ := violCornerEquiv hρ hQ
  let χ : T →+* k :=
    (FirstWeight.boundaryCharacter Q Λ hΛ t ((redWord_eq_finRange_iff (I := I) (ν := ν₁) t).1 ho) hv).toRingHom.comp q.toRingHom
  have hχ (u : Seq μ) (hu : redWord u = κ) :
      χ (orderedLoadingIdemAt Q Λ κ u hu) = if u = t then 1 else 0 := by
    let z := cornerMk (ofKLR k Q Λ ν₁ (KLRAlgebra.e u))
    have heq : orderedLoadingIdemAt Q Λ κ u hu = violCornerHom k Q Λ ν₁ z := by
      apply Subtype.ext
      rw [violCornerHom_val, cornerMk_e_val hu]
      rfl
    rw [heq]
    change FirstWeight.boundaryCharacter Q Λ hΛ t ((redWord_eq_finRange_iff (I := I) (ν := ν₁) t).1 ho) hv
      (q (violCornerHom k Q Λ ν₁ z)) = _
    rw [violCornerEquiv_violCornerHom hρ hQ, identityCornerHom_e hu, FirstWeight.boundaryCharacter_e]
  have hzero : ∀ x : (P ho), x ∈ (K ho) → χ x.1 = 0 := by
    intro x hx
    change x ∈ blockLoadingKernelAt Q Λ t a b κ ho at hx
    rw [kernelAt_eq_trace Q Λ t a b κ ho] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨d, ⟨u, hu, hlt, rfl⟩, y, rfl⟩ := hx
      change χ (y.1 * orderedLoadingIdemAt Q Λ κ u hu) = 0
      rw [map_mul, hχ, ite_eq_right (fun h => hlt.ne (congrArg (adjacentBlockRoot a b) h).symm),
        mul_zero]
    | zero => exact map_zero χ
    | add x y _ _ hx hy =>
      change χ (x.1 + y.1) = 0
      rw [map_add, hx, hy, add_zero]
    | smul d x _ hx =>
      change χ (x.1 * d.unop) = 0
      rw [map_mul, hx, zero_mul]
  let d := orderedLoadingIdemAt Q Λ κ t ho
  have hraw : IsIdempotentElem
      (KLRAlgebra.e t : KLRAlgebra k (stendhalQ Q Λ) μ) := KLRAlgebra.e_mul_self t
  have hd : IsIdempotentElem d :=
    Subtype.ext ((hraw.map (ofKLR k Q Λ ν₁)).map (violMk k Q Λ ν₁)).eq
  let p : (P ho) := ⟨d, hd.eq⟩
  have hc : χ d = 1 := by rw [hχ, ite_eq_left rfl]
  have hp : p ∉ (K ho) := fun h => one_ne_zero (hc.symm.trans (hzero p h))
  let : AddCommGroup (P ho) := Submodule.addCommGroup (P ho)
  let : Module Tᵐᵒᵖ (P ho) := Submodule.module (P ho)
  exact ⟨⟨Submodule.Quotient.mk p, 0, fun hz => hp ((Submodule.Quotient.mk_eq_zero (K ho)).1 hz)⟩⟩

end Categorification.Stendhal.BraidedStendhalAlgebra


namespace Categorification.Stendhal.BraidedStendhalAlgebra.TwoSpectatorOneBlack

open KLR

variable {k : Type} [CommRing k] [Nontrivial k]
variable (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 4 → Unit →₀ ℕ)

/-- Each candidate layer is nonzero when all four red weights are positive. -/
theorem twoSpectatorLayer_nontrivial (hQ : KLRSymm Q) (hΛ : ∀ r, 0 < Λ r ()) (c : Bool) :
    Nontrivial (twoSpectatorLayer Q Λ c) := by
  cases c
  · exact blockPartialStandardAt_nontrivial_of_positive Q Λ terminalHigher 0 1
      (by decide) (by rintro ⟨_, h⟩; contradiction) hQ hΛ
  · exact blockPartialStandardAt_nontrivial_of_positive Q Λ higher 0 1
      (by decide) (by rintro ⟨_, h⟩; contradiction) hQ hΛ

end Categorification.Stendhal.BraidedStendhalAlgebra.TwoSpectatorOneBlack

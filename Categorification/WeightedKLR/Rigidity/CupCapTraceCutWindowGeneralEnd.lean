/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapTraceCutLeadingWindow

/-!
# The window factor of an arbitrary element of the middle block

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half, step L5 (the window factor
of (T_w) for an arbitrary element of `T^{Λc}(ν₀)`, not only for loading idempotents).

An element `g` of the affine KLR algebra of the labels `Λc = (μ, μ*)` is read in the middle
block of `λ⁺` as `windowBlockElement g`: first relabelled along `plusBlockLabels_cup`, then
included through the red subfamily of the first two labels of the tail. The window factor
`plusWindowEnd` of `windowBlockElement g` is the action of the image of `g` in `T^{Λc}(ν₀)`.

## Main declarations

* `Stendhal.relabelLabelsKLR`: the affine KLR algebras of equal red labels.
* `Stendhal.relabelTensorProductAlgebra_tensorOfKLR_relabelLabelsKLR`.
* `Stendhal.cutPrefixProjection_relabelEquiv`: the first-block projection of a cut on a
  relabelled element.
* `Stendhal.CupCap.windowBlockElement`, `Stendhal.CupCap.windowBlockElement_e`.
* `Stendhal.CupCap.relabel_cutPrefixProjection_windowBlockElement`.
* `Stendhal.CupCap.plusWindowEnd_windowBlockElement`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra

variable {I k : Type*} [DecidableEq I] [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)

/-- The affine KLR algebras of equal red labels. -/
def relabelLabelsKLR {n : ℕ} {Λ₁ Λ₂ : Fin n → I →₀ ℕ} (h : Λ₁ = Λ₂) (ν : Multiset I) :
    KLRAlgebra k (stendhalQ Q Λ₁) (stendhalWeight n ν) ≃ₐ[k]
      KLRAlgebra k (stendhalQ Q Λ₂) (stendhalWeight n ν) := by
  subst h
  exact AlgEquiv.refl

theorem relabelLabelsKLR_e {n : ℕ} {Λ₁ Λ₂ : Fin n → I →₀ ℕ} (h : Λ₁ = Λ₂) (ν : Multiset I)
    (t : Seq (stendhalWeight n ν)) :
    relabelLabelsKLR Q h ν (e t) = e t := by
  subst h
  rfl

/-- Relabelling `T^{Λ₁}(ν)` along `Λ₁ = Λ₂` agrees with relabelling the affine KLR algebra. -/
theorem relabelTensorProductAlgebra_tensorOfKLR_relabelLabelsKLR {n : ℕ}
    {Λ₁ Λ₂ : Fin n → I →₀ ℕ} (h : Λ₁ = Λ₂) (ν : Multiset I)
    (g : KLRAlgebra k (stendhalQ Q Λ₂) (stendhalWeight n ν)) :
    relabelTensorProductAlgebra Q h ν (tensorOfKLR Q Λ₁ ν (relabelLabelsKLR Q h.symm ν g)) =
      tensorOfKLR Q Λ₂ ν g := by
  subst h
  rfl

/-- **The first-block projection of a cut on a relabelled element**: the inclusion of the red
subfamily of the first `a` labels followed by the first-block projection is the quotient onto
`T^{λ_1…λ_a}(θ)`. -/
theorem cutPrefixProjection_relabelEquiv {a r : ℕ} (Λ : Fin (a + r) → I →₀ ℕ) (θ : Multiset I)
    (z : KLRAlgebra k (stendhalQ Q (Λ ∘ Fin.castAdd r)) (stendhalWeight a θ)) :
    cutPrefixProjection (a := a) (r := r) Q Λ θ
        (relabelEquiv (redSubfamilyRelabel Q Λ (Fin.castAdd r) (Fin.castAdd_injective a r) θ) z) =
      tensorOfKLR Q (Λ ∘ Fin.castAdd r) θ z := by
  rw [cutPrefixProjection, redSubfamilyProjection]
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply]

end Categorification.Stendhal

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA
open scoped TensorProduct

section Window

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {θ γ ν₀ : Multiset I}

local notation "Sc" => stendhalQ Q (cutLabels j hj Λ)
local notation "cL" => Sum.map (id : I → I) (Fin.castAdd (ℓ - j) : Fin 2 → Fin (2 + (ℓ - j)))

variable (Q Λ Λc j hj ν₀) in
/-- **An element of the affine KLR algebra of `(μ, μ*)` read in the middle block of `λ⁺`**:
relabel along `plusBlockLabels_cup` and include the red subfamily of the first two labels of
the tail. -/
def windowBlockElement
    (g : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) :
    KLRAlgebra k (stendhalQ Q (blocksTailLabels (plusBlockLabels Λ Λc j hj)))
      ((stendhalWeight 2 ν₀).map cL) :=
  relabelEquiv (redSubfamilyRelabel Q (blocksTailLabels (plusBlockLabels Λ Λc j hj))
      (Fin.castAdd (ℓ - j)) (Fin.castAdd_injective 2 (ℓ - j)) ν₀)
    (relabelLabelsKLR Q (plusBlockLabels_cup Λ Λc j hj).symm ν₀ g)

/-- On loading idempotents, `windowBlockElement` is the relabelling of the window loading. -/
theorem windowBlockElement_e (w : Seq (stendhalWeight 2 ν₀)) :
    windowBlockElement j hj Q Λ Λc ν₀ (e w) = e (Seq.map cL w) := by
  rw [windowBlockElement, relabelLabelsKLR_e, relabelEquiv_apply, relabelHom_e]
  rfl

/-- **The middle-block image of `windowBlockElement g`** is the image of `g` in `T^{Λc}(ν₀)`. -/
theorem relabel_cutPrefixProjection_windowBlockElement
    (g : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) :
    relabelTensorProductAlgebra Q (plusBlockLabels_cup Λ Λc j hj) ν₀
        (cutPrefixProjection (a := 2) (r := ℓ - j) Q (blocksTailLabels (plusBlockLabels Λ Λc j hj))
          ν₀ (windowBlockElement j hj Q Λ Λc ν₀ g)) =
      tensorOfKLR Q Λc ν₀ g := by
  rw [windowBlockElement, cutPrefixProjection_relabelEquiv]
  exact relabelTensorProductAlgebra_tensorOfKLR_relabelLabelsKLR Q _ ν₀ g

attribute [local instance] botCornerModuleRight botCornerModuleRight_isScalarTower

variable (X : Type*) [AddCommGroup X] [Module k X]
  [Module (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X]
  [IsScalarTower k (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X]

local notation "Yc" => CutInput Q (cutLabels j hj Λ) θ γ (PlusRes j hj Q Λ Λc θ γ ν₀ X)

variable (s : Seq (stendhalWeight ℓ (θ + γ)))
  (q' : MackeyQuad (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
        (midPos_le_card_cut s))
      (Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s))
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ))
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)))

/-- **The window factor of an arbitrary element** (Webster v3, Lemma 7.19, trace half, step
L5): `ε` of `windowBlockElement g` on `E' · Res X` is the action of the image of `g` in
`T^{Λc}(ν₀)` on the middle block. -/
theorem plusWindowEnd_windowBlockElement
    (g : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) :
    plusWindowEnd X s q' (windowBlockElement j hj Q Λ Λc ν₀ g) =
      botCornerEnd q' Yc (cutInputHom (a := j) (r := ℓ - j) Q (cutLabels j hj Λ) θ γ
        (plusMidEnd X (tensorOfKLR Q Λc ν₀ g))) := by
  rw [plusWindowEnd, relabel_cutPrefixProjection_windowBlockElement]

end Window

end Categorification.Stendhal.CupCap

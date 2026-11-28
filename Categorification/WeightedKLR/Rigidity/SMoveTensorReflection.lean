/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.SMoveTensorStandardTor

/-!
# Reflection of modules over the tensor product algebra

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22. The pairing of the S-move takes a left module on one side and the
reflection of a left module, a right module, on the other. Transporting the corner flip along
`φ : C ≃ T` (`reflectedLeftCoefficientEquiv`) gives an anti-automorphism of `T = T^{λ ∘ σ}`
(`cornerFlipTensorEquiv`). Restricting scalars along it is the reflection of left `T`-modules
(`tensorReflectFunctor`). It carries the left standard of `s` to the right standard `S_s`
(`tensorReflectLeftStandardEquiv`), and so carries filtrations by left standards to filtrations
by right standards (`hasFiltration_tensorReflect`).

## Main definitions

* `cornerFlipTensorEquiv`: the anti-automorphism `Tᵐᵒᵖ ≃ T`.
* `tensorReflectFunctor`: the reflection of left `T`-modules to right `T`-modules.

## Main results

* `tensorReflectLeftStandardEquiv`: the reflected left standard is the right standard.
* `hasFiltration_tensorReflect`.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open CategoryTheory KLR Equiv MulOpposite CornerEndomorphism

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type} [DecidableEq I] [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
  {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  (hρ : TypeA.IsReducedChoice ρ) (hQ : KLRSymm Q) (σ : Perm (Fin ℓ))

local notation "κ" => List.map σ (List.finRange ℓ)
local notation "C" => ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ
local notation "T" => TensorProductAlgebra k Q (Λ ∘ σ) ν
local notation "μ" => stendhalWeight ℓ ν
local notation "φ" => reflectedLeftCoefficientEquiv (Λ := Λ) hρ hQ σ

/-- **The flip of `T`**: the corner flip transported along `φ : C ≃ T`. -/
def cornerFlipTensorEquiv : Tᵐᵒᵖ ≃+* T :=
  ((RingEquiv.op (φ).symm).trans (cornerFlipEquiv (Q := Q) (Λ := Λ) ν κ)).trans φ

/-- **Reflection of left `T`-modules**: restriction of scalars along the flip of `T`. -/
abbrev tensorReflectFunctor : ModuleCat.{0} T ⥤ ModuleCat.{0} Tᵐᵒᵖ :=
  ModuleCat.restrictScalars (cornerFlipTensorEquiv hρ hQ σ).toRingHom

/-- **The reflected left standard is the right standard** `S_s`. -/
def tensorReflectLeftStandardEquiv {s : Seq μ} (hs : IsRedOrdered s) :
    (tensorReflectFunctor hρ hQ σ).obj (ModuleCat.of T (leftStandard Q (Λ ∘ σ) s hs)) ≃ₗ[Tᵐᵒᵖ]
      tensorRightStandard (Λ := Λ) (ν := ν) hρ hQ σ s where
  toEquiv := (reflectedLoadingStandardLeftEquiv (Λ := Λ) hρ hQ σ hs).toEquiv.symm
  map_add' x y := (reflectedLoadingStandardLeftEquiv (Λ := Λ) hρ hQ σ hs).symm.map_add x y
  map_smul' t x := by
    let e := reflectedLoadingStandardLeftEquiv (Λ := Λ) hρ hQ σ hs
    let c : C := cornerFlipEquiv (Q := Q) (Λ := Λ) ν κ (op ((φ).symm t.unop))
    change e.symm ((φ c) • (show leftStandard Q (Λ ∘ σ) s hs from x)) = _
    refine (e.symm.map_smulₛₗ (φ c) x).trans ?_
    rw [RingHom.id_apply]
    change ((cornerFlipEquiv (Q := Q) (Λ := Λ) ν κ).symm ((φ).symm (φ c))) • e.symm x = _
    rw [RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]
    rfl

/-- **Reflection carries filtrations by left standards to filtrations by right standards.** -/
theorem hasFiltration_tensorReflect {m : List {s : Seq μ // IsRedOrdered s}}
    {Y : ModuleCat.{0} T}
    (hY : ModuleFiltration.HasFiltration (fun s : {s : Seq μ // IsRedOrdered s} =>
      ModuleCat.of T (leftStandard Q (Λ ∘ σ) s.1 s.2)) m Y) :
    ModuleFiltration.HasFiltration (fun t : {s : Seq μ // IsRedOrdered s} =>
      tensorRightStandard (Λ := Λ) (ν := ν) hρ hQ σ t.1) m
      ((tensorReflectFunctor hρ hQ σ).obj Y) := by
  have h₁ := hY.restrictScalars (cornerFlipTensorEquiv hρ hQ σ).toRingHom
  exact h₁.mono (L' := fun t : {s : Seq μ // IsRedOrdered s} =>
    tensorRightStandard (Λ := Λ) (ν := ν) hρ hQ σ t.1)
    fun s => ⟨tensorReflectLeftStandardEquiv hρ hQ σ s.2⟩

end Categorification.Stendhal.BraidedStendhalAlgebra

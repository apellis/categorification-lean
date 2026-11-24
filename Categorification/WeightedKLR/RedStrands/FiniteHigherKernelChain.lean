/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.HigherKernelFiltrationStep

/-!
# Finite higher-projective chains

Webster, arXiv:1309.3796v2, proof of Lemma 6.8 at (6.21).
A sequence of identifications with higher loading projectives yields a filtration by the actual partial-standard quotients.
-/


noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR MulOpposite ModuleFiltration
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe u v

variable {I : Type u} {k : Type v} [DecidableEq I] [CommRing k] {ℓ : ℕ} {ν : Multiset I}
variable (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
variable (a b : Fin ℓ) (κ : List (Fin ℓ))

local notation "T" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν κ)
local notation "C" => {s : Seq (stendhalWeight ℓ ν) // redWord s = κ}
local notation "P" => fun (s : C) => rIdeal (orderedLoadingIdemAt Q Λ κ (Subtype.val s) (Subtype.property s))
local notation "K" => fun (s : C) => blockLoadingKernelAt Q Λ (Subtype.val s) a b κ (Subtype.property s)
local notation "S" => fun (s : C) => blockPartialStandardAt Q Λ (Subtype.val s) a b κ (Subtype.property s)

/-- An ordered loading's higher-cut kernel as a module in the fixed corner. -/
abbrev fixedOrderKernelObj (s : C) : ModuleCat Tᵐᵒᵖ := by
  let : AddCommGroup (P s) := Submodule.addCommGroup (P s)
  let : Module Tᵐᵒᵖ (P s) := Submodule.module (P s)
  let : AddCommGroup (K s) := Submodule.addCommGroup (K s)
  exact ModuleCat.of Tᵐᵒᵖ (K s)

local notation "KO" => fixedOrderKernelObj Q Λ a b κ

/-- A chain of higher projective identifications in one ordered corner. Each
step identifies the current kernel with the next loading projective. -/
inductive HigherProjectiveChain : C → List C → Prop
  | nil (s : C) : Subsingleton (KO s) → HigherProjectiveChain s []
  | cons {s t : C} {m : List C}
      (higher : adjacentBlockRoot a b s.1 < adjacentBlockRoot a b t.1)
      (f : Nonempty ((P t) ≃ₗ[Tᵐᵒᵖ] KO s))
      (tail : HigherProjectiveChain t m) : HigherProjectiveChain s (t :: m)

private theorem hasFiltration_cons_fixedOrder (s t : C) {m : List C}
    (f : (P t) ≃ₗ[Tᵐᵒᵖ] KO s) (h : HasFiltration S m (KO t)) :
    HasFiltration S (t :: m) (KO s) := by
  let : AddCommGroup (P t) := Submodule.addCommGroup (P t)
  let : Module Tᵐᵒᵖ (P t) := Submodule.module (P t)
  have hf : HasFiltration S (t :: m) (ModuleCat.of Tᵐᵒᵖ (P t)) := by
    refine HasFiltration.cons (X := KO t) (Z := S t)
      (K t).subtype (K t).mkQ m t Subtype.val_injective ?_ (K t).mkQ_surjective h
      ⟨LinearEquiv.refl _ _⟩
    intro x
    change (Submodule.Quotient.mk x : (P t) ⧸ (K t)) = 0 ↔
      x ∈ Set.range (fun y : K t => (y : P t))
    exact (Submodule.Quotient.mk_eq_zero (K t)).trans
      ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.2⟩
  exact hf.of_equiv f

/-- Iterating the exact quotient step gives all of the actual partial-standard
quotients along a finite higher-projective chain. -/
theorem HigherProjectiveChain.hasFiltration {s : C} {m : List C}
    (chain : HigherProjectiveChain Q Λ a b κ s m) :
    HasFiltration S m (KO s) := by
  induction chain with
  | nil s h => exact .zero h
  | @cons s t m _ hf _ ih =>
    obtain ⟨f⟩ := hf
    exact hasFiltration_cons_fixedOrder Q Λ a b κ s t f ih

end Categorification.Stendhal.BraidedStendhalAlgebra

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR MulOpposite
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe u v

variable {I : Type u} {k : Type v} [DecidableEq I] [CommRing k] {ℓ : ℕ} {ν : Multiset I}
variable (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
variable (a b : Fin ℓ) (κ : List (Fin ℓ))

local notation "T" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν κ)
local notation "C" => {s : Seq (stendhalWeight ℓ ν) // redWord s = κ}
local notation "KO" => fixedOrderKernelObj Q Λ a b κ

/-- The initial kernel of a higher-projective chain is itself projective. -/
theorem HigherProjectiveChain.projective_source {s : C} {m : List C}
    (chain : HigherProjectiveChain Q Λ a b κ s m) :
    Module.Projective Tᵐᵒᵖ (KO s) := by
  cases chain with
  | nil s hs =>
    let : Subsingleton (KO s) := hs
    let : Module.Free Tᵐᵒᵖ (KO s) := Module.Free.of_subsingleton _ _
    infer_instance
  | @cons s t m _ he _ =>
    obtain ⟨e⟩ := he
    have ht : IsIdempotentElem (orderedLoadingIdemAt Q Λ κ t.1 t.2) := by
      obtain ⟨t, ht⟩ := t
      subst κ
      exact orderedLoadingIdem_idem Q Λ t
    let : Module.Projective Tᵐᵒᵖ (rIdeal (orderedLoadingIdemAt Q Λ κ t.1 t.2)) :=
      rIdeal_projective ht
    exact Module.Projective.of_equiv' e

end Categorification.Stendhal.BraidedStendhalAlgebra

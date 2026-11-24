/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockKernelSingleLayer

/-!
# A projective step in the retained kernel filtration

Webster, arXiv:1309.3796v2, proof of Lemma 6.8 at (6.21).
When a higher loading projective is identified with the source kernel, its own
higher-cut filtration extends by its partial-standard quotient.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR MulOpposite
open ModuleFiltration
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe u v w
variable {I : Type u} {k : Type v} [DecidableEq I] [CommRing k] {ℓ : ℕ} {ν : Multiset I}
variable (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
variable (s t : Seq (stendhalWeight ℓ ν)) (a b : Fin ℓ) (horder : redWord t = redWord s)

local notation "T" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν (redWord s))
local notation "P" => rIdeal (orderedLoadingIdemAt Q Λ (redWord s) t horder)
local notation "K" => blockLoadingKernelAt Q Λ t a b (redWord s) horder
local notation "S" => blockPartialStandardAt Q Λ t a b (redWord s) horder

/-- The higher-cut kernel as a module in the common ordered corner. -/
abbrev blockLoadingKernelObjAt : ModuleCat Tᵐᵒᵖ := by
  let : AddCommGroup P := Submodule.addCommGroup P
  let : Module Tᵐᵒᵖ P := Submodule.module P
  let : AddCommGroup K := Submodule.addCommGroup K
  exact ModuleCat.of Tᵐᵒᵖ K

/-- An isomorphism from a higher loading projective to the source kernel
puts its partial-standard quotient above the layers of its own higher-cut kernel. -/
theorem blockLoadingKernel_hasFiltration_cons_of_equiv
    {ι : Type w} {L : ι → ModuleCat.{max u v} Tᵐᵒᵖ} {m : List ι} (c : ι)
    (f : P ≃ₗ[Tᵐᵒᵖ] blockLoadingKernel Q Λ s a b)
    (h : HasFiltration L m (blockLoadingKernelObjAt Q Λ s t a b horder))
    (e : S ≃ₗ[Tᵐᵒᵖ] L c) :
    HasFiltration L (c :: m) (ModuleCat.of Tᵐᵒᵖ (blockLoadingKernel Q Λ s a b)) := by
  let : AddCommGroup P := Submodule.addCommGroup P
  let : Module Tᵐᵒᵖ P := Submodule.module P
  have hf : HasFiltration L (c :: m) (ModuleCat.of Tᵐᵒᵖ P) := by
    refine HasFiltration.cons (X := blockLoadingKernelObjAt Q Λ s t a b horder) (Z := S)
      (K).subtype (K).mkQ m c Subtype.val_injective ?_ (K).mkQ_surjective h ⟨e⟩
    intro x
    change (Submodule.Quotient.mk x : P ⧸ K) = 0 ↔ x ∈ Set.range (fun y : K => (y : P))
    exact (Submodule.Quotient.mk_eq_zero (K)).trans
      ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.2⟩
  exact hf.of_equiv f

end Categorification.Stendhal.BraidedStendhalAlgebra

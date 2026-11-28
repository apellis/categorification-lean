/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.SMoveModules
import Categorification.WeightedKLR.Rigidity.SMoveTensorReflection

/-!
# The reflected side of the S-move

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22. The S-move pairs the right module `𝕊^{λ_1; λ_2, λ_3}(P_∅ ⊠ L)` with the
left module `𝕊^{λ_1, λ_2; λ_3}(L̇ ⊠ Ṗ_∅)`. The right module is the reflection of the left
module `SMove.leftStd L`, along the flip of `T^{λ_1, λ_2, λ_3}` (`tensorReflectFunctor` at the
trivial braid `σ = 1`). Reflection is exact and carries filtrations by left standards to
filtrations by the right standards `S_t` (labels unchanged), the form taken by the Tor lemmas
(`isZero_derivedTensorHomology_tensor_of_standardFiltrations`).

## Main definitions

* `SMove.leftStdReflected`: `𝕊^{λ_1; λ_2, λ_3}(P_∅ ⊠ −)` followed by reflection.

## Main results

* `SMove.moduleExactFunctor_leftStdReflected`: it is exact.
* `BraidedStendhalAlgebra.hasFiltration_tensorReflect_one`: reflection at `σ = 1` of a module
  filtered by the left standards of `T^λ`.
* `SMove.hasFiltration_leftStdReflected`.
-/

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR Equiv BraidedStendhalAlgebra

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type} [DecidableEq I] [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  (hQ : KLRSymm Q)

namespace BraidedStendhalAlgebra

variable {ℓ : ℕ} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
  {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ} (hρ : TypeA.IsReducedChoice ρ)

/-- **Reflection at the trivial braid** carries a filtration of a left `T^λ`-module by the left
standards of `T^λ` to a filtration of its reflection by the right standards `S_t`, with the
same labels. -/
theorem hasFiltration_tensorReflect_one
    {m : List {s : Seq (stendhalWeight ℓ ν) // IsRedOrdered s}}
    {Y : ModuleCat.{0} (TensorProductAlgebra k Q Λ ν)}
    (hY : ModuleFiltration.HasFiltration
      (fun s : {s : Seq (stendhalWeight ℓ ν) // IsRedOrdered s} =>
        ModuleCat.of (TensorProductAlgebra k Q Λ ν) (leftStandard Q Λ s.1 s.2)) m Y) :
    ModuleFiltration.HasFiltration
      (fun t : {s : Seq (stendhalWeight ℓ ν) // IsRedOrdered s} =>
        tensorRightStandard (Λ := Λ) (ν := ν) hρ hQ 1 t.1) m
      ((tensorReflectFunctor (Λ := Λ) (ν := ν) hρ hQ 1).obj Y) :=
  hasFiltration_tensorReflect hρ hQ 1 hY

end BraidedStendhalAlgebra

namespace SMove

variable (Q) (Λ : Fin (1 + 2) → I →₀ ℕ) (β : Multiset I)
  {ρ : Perm (Fin (Multiset.card (stendhalWeight (1 + 2) β))) → List ℕ}
  (hρ : TypeA.IsReducedChoice ρ)

/-- **The right module of the S-move**: `𝕊^{λ_1; λ_2, λ_3}(P_∅ ⊠ −)` followed by reflection,
from left modules over `T^{λ_2, λ_3}(β)` to right modules over `T^{λ_1, λ_2, λ_3}(β)`. -/
def leftStdReflected :
    ModuleCat.{0} (TensorProductAlgebra k Q (Λ ∘ Fin.natAdd 1) β) ⥤
      ModuleCat.{0} (TensorProductAlgebra k Q Λ β)ᵐᵒᵖ :=
  leftStd Q hQ Λ β ⋙ tensorReflectFunctor (Λ := Λ) (ν := β) hρ hQ 1

/-- The reflected `𝕊^{λ_1; λ_2, λ_3}(P_∅ ⊠ −)` is exact. -/
theorem moduleExactFunctor_leftStdReflected :
    ModuleExactFunctor (leftStdReflected Q hQ Λ β hρ) :=
  (moduleExactFunctor_leftStd Q hQ Λ β).comp (ModuleExactFunctor.restrictScalars _)

/-- If `𝕊^{λ_1; λ_2, λ_3}(P_∅ ⊠ X)` is filtered by left standards, its reflection is filtered
by the right standards `S_t`, with the same labels. -/
theorem hasFiltration_leftStdReflected
    {m : List {s : Seq (stendhalWeight (1 + 2) β) // IsRedOrdered s}}
    {X : ModuleCat.{0} (TensorProductAlgebra k Q (Λ ∘ Fin.natAdd 1) β)}
    (hX : ModuleFiltration.HasFiltration
      (fun s : {s : Seq (stendhalWeight (1 + 2) β) // IsRedOrdered s} =>
        ModuleCat.of (TensorProductAlgebra k Q Λ β) (leftStandard Q Λ s.1 s.2)) m
      ((leftStd Q hQ Λ β).obj X)) :
    ModuleFiltration.HasFiltration
      (fun t : {s : Seq (stendhalWeight (1 + 2) β) // IsRedOrdered s} =>
        tensorRightStandard (Λ := Λ) (ν := β) hρ hQ 1 t.1) m
      ((leftStdReflected Q hQ Λ β hρ).obj X) :=
  hasFiltration_tensorReflect_one hQ hρ hX

end SMove

end Categorification.Stendhal

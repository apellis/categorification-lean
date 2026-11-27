/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FactorAlgebraCast
import Categorification.Algebra.TensorActSplit
import Categorification.Algebra.ModuleFiltrationMap

/-!
# Standardization with a commuting action transports filtrations

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5. A module `Y` over `T^{λ'}(θ) ⊗ (R^{λ_ℓ}(β) ⊗ C)` is a module over the factor
algebra `D = T^{λ'}(θ) ⊗ R^{λ_ℓ}(β)` with a commuting action of `C`; its standardization `S Y` is
then a module over `T^λ(θ + β) ⊗ C` (`splitStandard`). Standardization is exact, so a filtration of
`Y` gives one of `S Y` with the same labels (`hasFiltration_splitStandard`). This carries the
filtrations of the induction on the number of red strands through the two-piece standardization.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra StendhalAlgebra ModuleFiltration
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (hQ : KLRSymm Q)
  (θ β : Multiset I) (C : Type) [Ring C] [Algebra k C]

local notation "Told" => TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) θ
local notation "Cyc" => CycKLR k Q (fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i) β
/-- The algebra `T^{λ'}(θ) ⊗ (R^{λ_ℓ}(β) ⊗ C)`. -/
abbrev SplitAlg : Type := Told ⊗[k] (Cyc ⊗[k] C)

local notation "T" => TensorProductAlgebra k Q Λ (θ + β)

variable {θ β C} in
/-- The action of `C` on the standardization of a split module. -/
def splitStandardAction (Y : Type) [AddCommGroup Y] [Module (SplitAlg Q Λ θ β C) Y] :
    C →ₐ[k] Module.End T (ParabolicStandardT Q Λ θ β (SplitLeft k Told Cyc C Y) hQ) :=
  (parabolicEndAlg Q Λ hQ).comp (SplitLeft.action Y)

/-- **Standardization of a module over `T^{λ'}(θ) ⊗ (R^{λ_ℓ}(β) ⊗ C)`**, a module over
`T^λ(θ + β) ⊗ C`. -/
def splitStandard (Y : ModuleCat.{0} (SplitAlg Q Λ θ β C)) : ModuleCat.{0} (T ⊗[k] C) :=
  ModuleCat.of (T ⊗[k] C) (TensorAct k T C (splitStandardAction Q Λ hQ Y))

variable {θ β C}

theorem splitStandardAction_apply (Y : Type) [AddCommGroup Y] [Module (SplitAlg Q Λ θ β C) Y] (c : C) :
    splitStandardAction Q Λ hQ Y c = parabolicStandardMapT Q Λ hQ (SplitLeft.action (k := k) (A₁ := Told) (A₂ := Cyc) (C := C) Y c) := rfl

theorem splitStandardMapT_comp_action {Y Y' : Type} [AddCommGroup Y] [Module (SplitAlg Q Λ θ β C) Y]
    [AddCommGroup Y'] [Module (SplitAlg Q Λ θ β C) Y'] (f : Y →ₗ[SplitAlg Q Λ θ β C] Y') (c : C) :
    (parabolicStandardMapT Q Λ hQ (SplitLeft.map (k := k) (A₁ := Told) (A₂ := Cyc) (C := C) f) :
        ParabolicStandardT Q Λ θ β (SplitLeft k Told Cyc C Y) hQ →ₗ[T]
          ParabolicStandardT Q Λ θ β (SplitLeft k Told Cyc C Y') hQ).comp
        (splitStandardAction Q Λ hQ Y c) =
      (splitStandardAction Q Λ hQ Y' c).comp (parabolicStandardMapT Q Λ hQ (SplitLeft.map (k := k) (A₁ := Told) (A₂ := Cyc) (C := C) f)) := by
  rw [splitStandardAction_apply Q Λ hQ, splitStandardAction_apply Q Λ hQ,
    ← parabolicStandardMapT_comp,
    ← parabolicStandardMapT_comp]
  exact congrArg (parabolicStandardMapT Q Λ hQ)
    (LinearMap.ext fun y => SplitLeft.map_action f c y)

/-- Standardization on maps of modules over `T^{λ'}(θ) ⊗ (R^{λ_ℓ}(β) ⊗ C)`. -/
def splitStandardMap {Y Y' : Type} [AddCommGroup Y] [Module (SplitAlg Q Λ θ β C) Y] [AddCommGroup Y']
    [Module (SplitAlg Q Λ θ β C) Y'] (f : Y →ₗ[SplitAlg Q Λ θ β C] Y') :
    TensorAct k T C (splitStandardAction Q Λ hQ Y) →ₗ[T ⊗[k] C]
      TensorAct k T C (splitStandardAction Q Λ hQ Y') :=
  TensorAct.map (parabolicStandardMapT Q Λ hQ (SplitLeft.map (k := k) (A₁ := Told) (A₂ := Cyc) (C := C) f))
    (fun c x => LinearMap.congr_fun (splitStandardMapT_comp_action Q Λ hQ f c) x)

/-- **Standardization with a commuting action transports filtrations** (Webster,
arXiv:1309.3796v3, proof of Proposition 5.5). -/
theorem hasFiltration_splitStandard {ι : Type} {L : ι → ModuleCat.{0} (SplitAlg Q Λ θ β C)} {m : List ι}
    {Y : ModuleCat.{0} (SplitAlg Q Λ θ β C)} (hY : HasFiltration L m Y) :
    HasFiltration (fun c => splitStandard Q Λ hQ θ β C (L c)) m
      (splitStandard Q Λ hQ θ β C Y) :=
  HasFiltration.map (splitStandard Q Λ hQ θ β C) (fun f => splitStandardMap Q Λ hQ f)
    (fun _ hf => TensorAct.map_injective _
      (parabolicStandardMap_injective Q Λ θ β hQ _ (SplitLeft.map_injective hf)))
    (fun _ hf => TensorAct.map_surjective _
      (parabolicStandardMap_surjective Q Λ θ β hQ _ (SplitLeft.map_surjective hf)))
    (fun _ _ _ hfg _ => TensorAct.map_exact _ _
      (parabolicStandardMap_exact Q Λ θ β hQ _ _ (SplitLeft.map_exact hfg)))
    hY

end Categorification.Stendhal

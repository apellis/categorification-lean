/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicStandardTensorFiltration
import Categorification.Algebra.ExternalTensorExact
import Categorification.Algebra.ModuleFiltrationMap

/-!
# Standardization of `X ⊠ Y` transports filtrations of `X`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, proof of
Proposition 5.20: the induction on the number of red strands filters a module `X` over
`T^{λ'}` (the first `ℓ` red strands) and then passes this filtration through exterior tensor
product with a module `Y` over `R^{λ_ℓ}` and standardization. Both operations are exact (over
the field `k`, and Proposition 5.7 for standardization), so a filtration of `X` by modules `L c`
gives a filtration of `S(X ⊠ Y)` by the modules `S(L c ⊠ Y)`, with the same labels.

## Main definitions and results

* `tensorFactorMapLeft`: the map `f ⊠ Y` of factor modules.
* `hasFiltration_tensorLayer`: the transported filtration.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open KLR ModuleFiltration
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} {k : Type} [DecidableEq I] [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ)

local notation "old" => Λ ∘ Fin.castSucc
local notation "aΛ" => fun j => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) j
local notation "Told" => TensorProductAlgebra k Q (old)
local notation "Cyc" => CycKLR k Q (aΛ)

/-- The map `f ⊠ Y : X ⊠ Y → X' ⊠ Y` of factor modules. -/
def tensorFactorMapLeft {θ β : Multiset I} {X X' : ModuleCat.{0} (Told θ)}
    (Y : ModuleCat.{0} (Cyc β)) (f : X →ₗ[Told θ] X') :
    (tensorFactor Q Λ X Y).carrier →ₗ[parabolicFactorAlgebra Q Λ θ β]
      (tensorFactor Q Λ X' Y).carrier :=
  ExtTensor.map (k := k) (P := KMod (k := k) X) (P' := KMod (k := k) X')
    (Q := KMod (k := k) Y) (Q' := KMod (k := k) Y) (KMod.map f) LinearMap.id

variable (hQ : KLRSymm Q)

/-- **Standardization of `X ⊠ Y` transports filtrations of `X`** (Webster,
arXiv:1309.3796v2, proof of Proposition 5.20): a filtration of `X` by modules `L c` gives a
filtration of `S(X ⊠ Y)` by the modules `S(L c ⊠ Y)`, with the same labels. -/
theorem hasFiltration_tensorLayer {ι : Type} {θ β ν : Multiset I} (h : θ + β = ν)
    (Y : ModuleCat.{0} (Cyc β)) {L : ι → ModuleCat.{0} (Told θ)} {m : List ι}
    {X : ModuleCat.{0} (Told θ)} (hX : HasFiltration L m X) :
    HasFiltration (fun c => stdLayerModule Q Λ hQ (tensorLayer Q Λ h (L c) Y)) m
      (stdLayerModule Q Λ hQ (tensorLayer Q Λ h X Y)) :=
  HasFiltration.map (fun X => stdLayerModule Q Λ hQ (tensorLayer Q Λ h X Y))
    (fun f => stdLayerMap Q Λ hQ h (tensorFactorMapLeft Q Λ Y f))
    (fun f hf => parabolicStandardMap_injective Q Λ θ β hQ _
      (ExtTensor.map_id_injective (k := k) (P := KMod (k := k) _)
        (P' := KMod (k := k) _) (Q := KMod (k := k) Y) (f := KMod.map f) hf))
    (fun f hf => parabolicStandardMap_surjective Q Λ θ β hQ _
      (ExtTensor.map_id_surjective (k := k) (P := KMod (k := k) _)
        (P' := KMod (k := k) _) (Q := KMod (k := k) Y) (f := KMod.map f) hf))
    (fun f g _ hfg hg => parabolicStandardMap_exact Q Λ θ β hQ _ _
      (ExtTensor.map_id_exact (k := k) (P := KMod (k := k) _) (P' := KMod (k := k) _)
        (P'' := KMod (k := k) _) (Q := KMod (k := k) Y) (f := KMod.map f) (g := KMod.map g)
        hfg hg))
    hX

end Categorification.Stendhal

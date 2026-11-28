/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationSpectatorAssoc
import Categorification.WeightedKLR.RedStrands.PartialStandardizationNatural

/-!
# Naturality of the one-step associativity with a spectator

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1, toward
the derived form of Lemma 7.19 (K): the one-step associativity of the partial
standardizations with a spectator (`spectAssocAddEquiv`) is natural in the module over the
three blocks and the spectator.

## Main results

* `Stendhal.spectAssocAddEquiv_natural`: naturality of `spectAssocAddEquiv`.
-/

set_option backward.isDefEq.respectTransparency false

universe u

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR KLRAlgebra TypeA
open scoped TensorProduct

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

variable {I k : Type u} [DecidableEq I] [CommRing k] {a m : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (a + (m + 1)) → I →₀ ℕ) (θ β γ : Multiset I)
  (E : AlgCat.{u} k) (hQ : KLRSymm Q)

local notation "ΛL" => Λ ∘ Fin.cast (Nat.add_assoc a m 1)
local notation "ΛA" => blocksLeftLabels (a := a) (m := m) (r := 1) ΛL
local notation "Lst" => blocksLastAlgebra (a := a) (m := m) (r := 1) Q ΛL γ
local notation "Hd" => TensorProductAlgebra k Q (Λ ∘ Fin.castAdd (m + 1)) θ

/-- The semiring structure of the algebra of three blocks, through its ring structure. -/
abbrev blocksNonAssocSemiringN :
    NonAssocSemiring (blocksFactorAlgebra (a := a) (m := m) (r := 1) Q Λ θ β γ) :=
  Semiring.toNonAssocSemiring

attribute [local instance high] blocksNonAssocSemiringN

variable {N N' : ModuleCat.{u} (blocksSpectAlgebra Q Λ θ β γ E)}

/-- A map of modules over the three blocks and `E`, as a map over the three blocks. -/
def spectBlocksHom (g : N ⟶ N') :
    SpectBlocks Q Λ θ β γ E N →ₗ[blocksFactorAlgebra (a := a) (m := m) (r := 1) Q Λ θ β γ]
      SpectBlocks Q Λ θ β γ E N' where
  toFun n := g.hom n
  map_add' := g.hom.map_add
  map_smul' d n := g.hom.map_smul (blocksSpectIncl Q Λ θ β γ E d) n

/-- **The one-step associativity with a spectator is natural.** -/
theorem spectAssocAddEquiv_natural (g : N ⟶ N')
    (z : CutSpectStandard Q ΛL (θ + β) γ E (spectLeftMid hQ N) hQ) :
    spectAssocAddEquiv Q Λ θ β γ E hQ N'
        (((cutSpectFunctor (a := a + m) (r := 1) Q ΛL (θ + β) γ E hQ).map
          ((ModuleCat.restrictScalars.{u} (spectLastAlg Q Λ θ β γ E).toRingHom).map
            ((cutSpectFunctor (a := a) (r := m) Q ΛA θ β
                (AlgCat.of k (Lst ⊗[k] E)) hQ).map
              ((ModuleCat.restrictScalars.{u} (spectAssocLeftAlg Q Λ θ β γ E).toRingHom).map
                g)))).hom z) =
      ((cutSpectFunctor (a := a) (r := m + 1) Q Λ θ (β + γ) E hQ).map
          ((ModuleCat.restrictScalars.{u} (spectHeadAlg Q Λ θ β γ E).toRingHom).map
            ((cutSpectFunctor (a := m) (r := 1) Q (Λ ∘ Fin.natAdd a) β γ
                (AlgCat.of k (Hd ⊗[k] E)) hQ).map
              ((ModuleCat.restrictScalars.{u} (spectAssocRightAlg Q Λ θ β γ E).toRingHom).map
                g)))).hom
        (spectAssocAddEquiv Q Λ θ β γ E hQ N z) := by
  let XL := (ModuleCat.restrictScalars.{u} (spectLastAlg Q Λ θ β γ E).toRingHom).map
        ((cutSpectFunctor (a := a) (r := m) Q ΛA θ β (AlgCat.of k (Lst ⊗[k] E)) hQ).map
          ((ModuleCat.restrictScalars.{u} (spectAssocLeftAlg Q Λ θ β γ E).toRingHom).map g))
  let fL : CutSpectInput Q ΛL (θ + β) γ E (spectLeftMid hQ N) →ₗ[cutFactorAlgebra Q ΛL (θ + β) γ]
      CutSpectInput Q ΛL (θ + β) γ E (spectLeftMid hQ N') :=
    cutSpectInputHom Q ΛL (θ + β) γ (E := E) XL.hom
  let μ' : CutSpectInput Q ΛL (θ + β) γ E (spectLeftMid hQ N') →ₗ[cutFactorAlgebra Q ΛL (θ + β) γ]
      BlocksMidL (a := a) (m := m) (r := 1) Q ΛL θ β γ
        (BlocksAssocInput (a := a) (m := m) (r := 1) Q Λ θ β γ (SpectBlocks Q Λ θ β γ E N')) hQ :=
    LinearEquiv.toLinearMap (spectLeftMidEquiv Q Λ θ β γ E hQ N')
  let μ : CutSpectInput Q ΛL (θ + β) γ E (spectLeftMid hQ N) →ₗ[cutFactorAlgebra Q ΛL (θ + β) γ]
      BlocksMidL (a := a) (m := m) (r := 1) Q ΛL θ β γ
        (BlocksAssocInput (a := a) (m := m) (r := 1) Q Λ θ β γ (SpectBlocks Q Λ θ β γ E N)) hQ :=
    LinearEquiv.toLinearMap (spectLeftMidEquiv Q Λ θ β γ E hQ N)
  let gM := blocksMidHomL Q ΛL θ β γ hQ
    (blocksAssocInputHom Q Λ θ β γ (spectBlocksHom Q Λ θ β γ E g))
  let fA := cutSpectInputHom Q ΛA θ β (E := AlgCat.of k (Lst ⊗[k] E))
    ((ModuleCat.restrictScalars.{u} (spectAssocLeftAlg Q Λ θ β γ E).toRingHom).map g).hom
  let κ' : CutSpectInput Q ΛA θ β (AlgCat.of k (Lst ⊗[k] E)) (spectLeftInput Q Λ θ β γ E N') →ₗ[
      cutFactorAlgebra Q ΛA θ β] BlocksInnerL (a := a) (m := m) (r := 1) Q ΛL θ β γ
        (BlocksAssocInput (a := a) (m := m) (r := 1) Q Λ θ β γ (SpectBlocks Q Λ θ β γ E N')) :=
    LinearEquiv.toLinearMap (spectLeftInputEquiv Q Λ θ β γ E N')
  let κ : CutSpectInput Q ΛA θ β (AlgCat.of k (Lst ⊗[k] E)) (spectLeftInput Q Λ θ β γ E N) →ₗ[
      cutFactorAlgebra Q ΛA θ β] BlocksInnerL (a := a) (m := m) (r := 1) Q ΛL θ β γ
        (BlocksAssocInput (a := a) (m := m) (r := 1) Q Λ θ β γ (SpectBlocks Q Λ θ β γ E N)) :=
    LinearEquiv.toLinearMap (spectLeftInputEquiv Q Λ θ β γ E N)
  let gI := blocksInnerHomL Q ΛL θ β γ
    (blocksAssocInputHom Q Λ θ β γ (spectBlocksHom Q Λ θ β γ E g))
  have hL : ∀ y, μ' (fL y) = gM (μ y) := fun y =>
    cutStandardMap_square Q ΛA θ β fA κ' κ gI (fun _ => rfl) y
  have h1 := cutStandardMap_square Q ΛL (θ + β) γ fL μ' μ gM hL z
  have h2 := blocksStandardAssocEquiv_map (a := a) (m := m) (r := 1) Q Λ θ β γ hQ
    (spectBlocksHom Q Λ θ β γ E g) (cutStandardMap Q ΛL (θ + β) γ μ z)
  let XR := (ModuleCat.restrictScalars.{u} (spectHeadAlg Q Λ θ β γ E).toRingHom).map
        ((cutSpectFunctor (a := m) (r := 1) Q (Λ ∘ Fin.natAdd a) β γ
            (AlgCat.of k (Hd ⊗[k] E)) hQ).map
          ((ModuleCat.restrictScalars.{u} (spectAssocRightAlg Q Λ θ β γ E).toRingHom).map g))
  let fR : CutSpectInput Q Λ θ (β + γ) E (spectRightMid hQ N) →ₗ[cutFactorAlgebra Q Λ θ (β + γ)]
      CutSpectInput Q Λ θ (β + γ) E (spectRightMid hQ N') :=
    cutSpectInputHom Q Λ θ (β + γ) (E := E) XR.hom
  let ν' : BlocksMid (a := a) (m := m) (r := 1) Q Λ θ β γ (SpectBlocks Q Λ θ β γ E N') hQ
      →ₗ[cutFactorAlgebra Q Λ θ (β + γ)] CutSpectInput Q Λ θ (β + γ) E (spectRightMid hQ N') :=
    LinearEquiv.toLinearMap (spectRightMidEquiv Q Λ θ β γ E hQ N').symm
  let ν : BlocksMid (a := a) (m := m) (r := 1) Q Λ θ β γ (SpectBlocks Q Λ θ β γ E N) hQ
      →ₗ[cutFactorAlgebra Q Λ θ (β + γ)] CutSpectInput Q Λ θ (β + γ) E (spectRightMid hQ N) :=
    LinearEquiv.toLinearMap (spectRightMidEquiv Q Λ θ β γ E hQ N).symm
  let hM := blocksMidHom Q Λ θ β γ hQ (spectBlocksHom Q Λ θ β γ E g)
  let fB := cutSpectInputHom Q (Λ ∘ Fin.natAdd a) β γ (E := AlgCat.of k (Hd ⊗[k] E))
    ((ModuleCat.restrictScalars.{u} (spectAssocRightAlg Q Λ θ β γ E).toRingHom).map g).hom
  let ρ' : BlocksInner (a := a) (m := m) (r := 1) Q Λ θ β γ (SpectBlocks Q Λ θ β γ E N')
      →ₗ[cutFactorAlgebra Q (Λ ∘ Fin.natAdd a) β γ]
      CutSpectInput Q (Λ ∘ Fin.natAdd a) β γ (AlgCat.of k (Hd ⊗[k] E))
        (spectRightInput Q Λ θ β γ E N') :=
    LinearEquiv.toLinearMap (spectRightInputEquiv Q Λ θ β γ E N').symm
  let ρ : BlocksInner (a := a) (m := m) (r := 1) Q Λ θ β γ (SpectBlocks Q Λ θ β γ E N)
      →ₗ[cutFactorAlgebra Q (Λ ∘ Fin.natAdd a) β γ]
      CutSpectInput Q (Λ ∘ Fin.natAdd a) β γ (AlgCat.of k (Hd ⊗[k] E))
        (spectRightInput Q Λ θ β γ E N) :=
    LinearEquiv.toLinearMap (spectRightInputEquiv Q Λ θ β γ E N).symm
  let hI := blocksInnerHom Q Λ θ β γ (spectBlocksHom Q Λ θ β γ E g)
  have hR : ∀ y, ν' (hM y) = fR (ν y) := fun y =>
    cutStandardMap_square Q (Λ ∘ Fin.natAdd a) β γ hI ρ' ρ fB (fun _ => rfl) y
  have h3 := cutStandardMap_square Q Λ θ (β + γ) hM ν' ν fR hR
    (blocksStandardAssocEquiv (a := a) (m := m) (r := 1) Q Λ θ β γ _ hQ
      (cutStandardMap Q ΛL (θ + β) γ μ z))
  have h4 := (congrArg (fun w => cutStandardMap Q Λ θ (β + γ) ν'
      (blocksStandardAssocEquiv (a := a) (m := m) (r := 1) Q Λ θ β γ _ hQ w)) h1).trans
    ((congrArg (cutStandardMap Q Λ θ (β + γ) ν') h2).trans h3)
  have e1 : ((cutSpectFunctor (a := a + m) (r := 1) Q ΛL (θ + β) γ E hQ).map
          ((ModuleCat.restrictScalars.{u} (spectLastAlg Q Λ θ β γ E).toRingHom).map
            ((cutSpectFunctor (a := a) (r := m) Q ΛA θ β
                (AlgCat.of k (Lst ⊗[k] E)) hQ).map
              ((ModuleCat.restrictScalars.{u} (spectAssocLeftAlg Q Λ θ β γ E).toRingHom).map
                g)))).hom z = cutStandardMap Q ΛL (θ + β) γ fL z := rfl
  have e2 : ∀ w, ((cutSpectFunctor (a := a) (r := m + 1) Q Λ θ (β + γ) E hQ).map
          ((ModuleCat.restrictScalars.{u} (spectHeadAlg Q Λ θ β γ E).toRingHom).map
            ((cutSpectFunctor (a := m) (r := 1) Q (Λ ∘ Fin.natAdd a) β γ
                (AlgCat.of k (Hd ⊗[k] E)) hQ).map
              ((ModuleCat.restrictScalars.{u} (spectAssocRightAlg Q Λ θ β γ E).toRingHom).map
                g)))).hom w = cutStandardMap Q Λ θ (β + γ) fR w := fun _ => rfl
  have e3 : spectAssocAddEquiv Q Λ θ β γ E hQ N' (cutStandardMap Q ΛL (θ + β) γ fL z) =
      cutStandardMap Q Λ θ (β + γ) ν'
        (blocksStandardAssocEquiv (a := a) (m := m) (r := 1) Q Λ θ β γ _ hQ
          (cutStandardMap Q ΛL (θ + β) γ μ' (cutStandardMap Q ΛL (θ + β) γ fL z))) :=
    spectAssocAddEquiv_apply Q Λ θ β γ E hQ N' _
  have e4 : spectAssocAddEquiv Q Λ θ β γ E hQ N z =
      cutStandardMap Q Λ θ (β + γ) ν
        (blocksStandardAssocEquiv (a := a) (m := m) (r := 1) Q Λ θ β γ _ hQ
          (cutStandardMap Q ΛL (θ + β) γ μ z)) :=
    spectAssocAddEquiv_apply Q Λ θ β γ E hQ N z
  exact ((congrArg (spectAssocAddEquiv Q Λ θ β γ E hQ N') e1).trans e3).trans
    (h4.trans ((congrArg (cutStandardMap Q Λ θ (β + γ) fR) e4.symm).trans (e2 _).symm))

end Categorification.Stendhal

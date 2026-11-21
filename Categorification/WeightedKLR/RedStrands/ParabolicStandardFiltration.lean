/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.ModuleFiltration
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastIndShortExact
import Categorification.WeightedKLR.RedStrands.BlackInductionExact

/-!
# `Fᵢ` refines filtrations by standardizations

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, step of the
proof of Proposition 5.21 (and of Corollary 5.22) that applies `Fᵢ` to a filtration whose
subquotients are standardizations. A *standard layer* of black weight `ν` is a module `N` over
`T^{λ'} ⊗ R^{λ_ℓ}_β` together with a split `θ + β = ν`; its module is the standardization
`S(N)`, a module over `T(ν)` (`stdLayerModule`). Proposition 5.5, `F`-part
(`firstIndDeltaT_shortExact`), gives

`0 → S(₁Fᵢ N) → Fᵢ S(N) → S(₂Fᵢ N) → 0`,

so `Fᵢ S(N)` has a filtration with the two layers `S(₂Fᵢ N)` (top) and `S(₁Fᵢ N)`
(`hasFiltration_blackInd_stdLayer`). Since `Fᵢ` is exact (Theorem 4.31), `Fᵢ` turns a filtration
by standard layers into one whose layers are obtained by replacing each layer by these two
(`HasFiltration.blackInd`).

Injectivity of `δ₁` in Proposition 5.5 is the route hypothesis `FirstIndDeltaInjective`, here
required for every layer; the roadmap (`docs/WeightedKLR/tensor-product-roadmap.md`, §5) tracks
its removal by Webster's dimension count.

The identification of these layers with the modules `T^λ e(s', λ_ℓ, w)` and with the quotients
`P^{≥φ}/P^{>φ}` of Proposition 5.21 is not part of this file.

## Main definitions

* `FactorModule`: a module over `T^{λ'}_θ ⊗ R^{λ_ℓ}_β`.
* `StdLayer`: a standard layer of black weight `ν`; `stdLayerModule` its module `S(N)`.
* `StdLayer.first`, `StdLayer.last`: the layers `₁Fᵢ N` and `₂Fᵢ N`.
* `blackIndModule`: `Fᵢ` on modules over `T(ν)`.

## Main results

* `hasFiltration_blackInd_stdLayer`: `Fᵢ S(N)` is filtered by `S(₂Fᵢ N)` over `S(₁Fᵢ N)`.
* `HasFiltration.blackInd`: `Fᵢ` refines filtrations by standard layers.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR KLRAlgebra InductionAlong MulOpposite ModuleFiltration
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} {k : Type} [DecidableEq I] [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ)

local notation "Si" j => (Singleton.singleton j : Multiset I)

/-- A module over the factor algebra `T^{λ'}_θ ⊗ R^{λ_ℓ}_β` of standardization. -/
structure FactorModule (θ β : Multiset I) where
  /-- The underlying type. -/
  carrier : Type
  [addCommGroup : AddCommGroup carrier]
  [moduleK : Module k carrier]
  [moduleFactor : Module (parabolicFactorAlgebra Q Λ θ β) carrier]
  [tower : IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) carrier]

attribute [instance] FactorModule.addCommGroup FactorModule.moduleK FactorModule.moduleFactor
  FactorModule.tower

/-- A standard layer of black weight `ν`: a split `θ + β = ν` and a module over
`T^{λ'}_θ ⊗ R^{λ_ℓ}_β`. -/
structure StdLayer (ν : Multiset I) where
  /-- The black weight of the first factor. -/
  θ : Multiset I
  /-- The black weight on the last red strand. -/
  β : Multiset I
  /-- The split of the black weight. -/
  h : θ + β = ν
  /-- The input module of standardization. -/
  M : FactorModule Q Λ θ β

variable (hQ : KLRSymm Q)

/-- The standardization `S(N)` of a layer, as a module over `T(ν)`. -/
def StdLayer.carrier {ν : Multiset I} (c : StdLayer Q Λ ν) : Type :=
  ParabolicStandard Q Λ c.θ c.β c.M.carrier

instance {ν : Multiset I} (c : StdLayer Q Λ ν) : AddCommGroup (c.carrier Q Λ) :=
  inferInstanceAs (AddCommGroup (ParabolicStandard Q Λ c.θ c.β c.M.carrier))

/-- The `T(ν)`-module structure of `S(N)`, through `T(ν) ≅ T(θ + β)`. -/
abbrev StdLayer.instModule {ν : Multiset I} (c : StdLayer Q Λ ν) :
    Module (TensorProductAlgebra k Q Λ ν) (c.carrier Q Λ) :=
  Module.compHom (ParabolicStandard Q Λ c.θ c.β c.M.carrier)
    ((parabolicStandardAction Q Λ c.θ c.β c.M.carrier hQ).comp
      (castTensorProductAlgebra Q Λ c.h.symm).toAlgHom).toRingHom

/-- **The module `S(N)` of a standard layer**, over `T(ν)`. -/
def stdLayerModule {ν : Multiset I} (c : StdLayer Q Λ ν) :
    ModuleCat.{0} (TensorProductAlgebra k Q Λ ν) :=
  @ModuleCat.of _ _ (c.carrier Q Λ) _ (StdLayer.instModule Q Λ hQ c)

/-- `Fᵢ` on modules over `T(ν)`: induction along `appendBlack`. -/
abbrev blackIndModule (i : I) {ν : Multiset I}
    (X : ModuleCat.{0} (TensorProductAlgebra k Q Λ ν)) :
    ModuleCat.{0} (TensorProductAlgebra k Q Λ ((Si i) + ν)) :=
  ModuleCat.of _ (Ind X (appendBlackNU (Q := Q) (Λ := Λ) i ν))

variable (i : I)

/-- The layer `₁Fᵢ N`, over `T^{λ'}_{i+θ} ⊗ R^{λ_ℓ}_β`. -/
def StdLayer.first {ν : Multiset I} (c : StdLayer Q Λ ν) : StdLayer Q Λ ((Si i) + ν) where
  θ := (Si i) + c.θ
  β := c.β
  h := by rw [add_assoc, c.h]
  M := ⟨FirstIndLeft Q Λ i c.θ c.β c.M.carrier⟩

/-- The layer `₂Fᵢ N`, over `T^{λ'}_θ ⊗ R^{λ_ℓ}_{i+β}`. -/
def StdLayer.last {ν : Multiset I} (c : StdLayer Q Λ ν) : StdLayer Q Λ ((Si i) + ν) where
  θ := c.θ
  β := (Si i) + c.β
  h := by rw [add_left_comm, c.h]
  M := ⟨LastIndRight Q Λ i c.θ c.β c.M.carrier⟩

/-- The two layers of `Fᵢ S(N)`, the top one first. -/
def StdLayer.blackIndLayers {ν : Multiset I} (c : StdLayer Q Λ ν) :
    List (StdLayer Q Λ ((Si i) + ν)) :=
  [c.last Q Λ i, c.first Q Λ i]

/-- The route hypothesis `FirstIndDeltaInjective` for a standard layer. -/
def StdLayer.DeltaInjective {ν : Multiset I} (c : StdLayer Q Λ ν) : Prop :=
  FirstIndDeltaInjective Q Λ i c.θ c.β c.M.carrier hQ

variable {Q Λ hQ}

/-- **`Fᵢ S(N)` is filtered by `S(₂Fᵢ N)` over `S(₁Fᵢ N)`** (Webster, arXiv:1309.3796v3,
Proposition 5.5, `F`-part, given the route hypothesis `FirstIndDeltaInjective`). -/
theorem hasFiltration_blackInd_stdLayer {ν : Multiset I} (c : StdLayer Q Λ ν)
    (hc : StdLayer.DeltaInjective Q Λ hQ i c) :
    HasFiltration (stdLayerModule Q Λ hQ) (c.blackIndLayers Q Λ i)
      (blackIndModule Q Λ i (stdLayerModule Q Λ hQ c)) := by
  obtain ⟨θ, β, h, M⟩ := c
  subst h
  obtain ⟨hinj, hex, hsurj⟩ := firstIndDeltaT_shortExact Q Λ i θ β M.carrier hQ hc
  let eFirst : FirstIndStandardT Q Λ i θ β M.carrier hQ ≃ₗ[TensorProductAlgebra k Q Λ
      ((Si i) + (θ + β))] stdLayerModule Q Λ hQ (StdLayer.first Q Λ i ⟨θ, β, rfl, M⟩) :=
    { toFun := fun x => x
      invFun := fun x => x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let eLast : LastIndStandardT Q Λ i θ β M.carrier hQ ≃ₗ[TensorProductAlgebra k Q Λ
      ((Si i) + (θ + β))] stdLayerModule Q Λ hQ (StdLayer.last Q Λ i ⟨θ, β, rfl, M⟩) :=
    { toFun := fun x => x
      invFun := fun x => x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let eS : stdLayerModule Q Λ hQ ⟨θ, β, rfl, M⟩ ≃ₗ[TensorProductAlgebra k Q Λ (θ + β)]
      ParabolicStandardT Q Λ θ β M.carrier hQ :=
    { toFun := fun x => x
      invFun := fun x => x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hF := HasFiltration.cons (L := stdLayerModule Q Λ hQ)
    (X := ModuleCat.of _ (FirstIndStandardT Q Λ i θ β M.carrier hQ))
    (Y := ModuleCat.of _ (LastIndF Q Λ i θ β M.carrier hQ))
    (Z := ModuleCat.of _ (LastIndStandardT Q Λ i θ β M.carrier hQ))
    (firstIndDeltaT Q Λ i θ β M.carrier hQ) (lastIndQuotientMap Q Λ i θ β M.carrier hQ)
    [StdLayer.first Q Λ i ⟨θ, β, rfl, M⟩] (StdLayer.last Q Λ i ⟨θ, β, rfl, M⟩)
    hinj hex hsurj (HasFiltration.single eFirst) ⟨eLast⟩
  exact hF.of_equiv (Ind.mapEquiv (φ := appendBlackNU (Q := Q) (Λ := Λ) i (θ + β)) eS).symm

/-- Induction of a subsingleton module is a subsingleton. -/
theorem subsingleton_ind {A B : Type} [Ring A] [Ring B] {φ : A →ₙ+* B} {N : Type}
    [AddCommGroup N] [Module A N] [Subsingleton N] : Subsingleton (Ind N φ) := by
  refine ⟨fun a b => ?_⟩
  have h0 : ∀ t : Ind N φ, t = 0 := fun t => by
    induction t using Ind.induction_on with
    | zero => rfl
    | tmul z n => rw [Subsingleton.elim n 0, Ind.tmul_zero]
    | add s t hs ht => rw [hs, ht, add_zero]
  rw [h0 a, h0 b]

/-- **`Fᵢ` refines filtrations by standard layers** (Webster, arXiv:1309.3796v3, proof of
Proposition 5.21): if `X` has a filtration by standardizations with layers `m`, then `Fᵢ X` has
one whose layers replace each `c ∈ m` by `S(₂Fᵢ c)` over `S(₁Fᵢ c)`. Uses the route
hypothesis `FirstIndDeltaInjective` for the layers of `m`, and exactness of `Fᵢ`
(Theorem 4.31). -/
theorem HasFiltration.blackInd (C : QuantumGroup.CartanDatum I) (hR : IsRouquierQ C Q)
    {ν : Multiset I} {m : List (StdLayer Q Λ ν)}
    {X : ModuleCat.{0} (TensorProductAlgebra k Q Λ ν)}
    (h : HasFiltration (stdLayerModule Q Λ hQ) m X)
    (hm : ∀ c ∈ m, StdLayer.DeltaInjective Q Λ hQ i c) :
    HasFiltration (stdLayerModule Q Λ hQ) (m.flatMap (StdLayer.blackIndLayers Q Λ i))
      (blackIndModule Q Λ i X) := by
  induction h with
  | zero hY =>
    exact .zero subsingleton_ind
  | @cons X Y Z f g m c hf hfg hg _ hZ ih =>
    obtain ⟨e⟩ := hZ
    have hc : StdLayer.DeltaInjective Q Λ hQ i c := hm c (List.mem_cons_self ..)
    have hX := ih (fun c' hc' => hm c' (List.mem_cons_of_mem _ hc'))
    have hZ' := (hasFiltration_blackInd_stdLayer i c hc).of_equiv
      (Y' := blackIndModule Q Λ i Z)
      (Ind.mapEquiv (φ := appendBlackNU (Q := Q) (Λ := Λ) i ν) e).symm
    have := hZ'.extension (X := blackIndModule Q Λ i X) (Y := blackIndModule Q Λ i Y)
      (Ind.map (φ := appendBlackNU (Q := Q) (Λ := Λ) i ν) f)
      (Ind.map (φ := appendBlackNU (Q := Q) (Λ := Λ) i ν) g)
      (appendBlack_ind_map_injective C hR hf) (appendBlack_ind_map_exact C hR hfg)
      (Ind.map_surjective hg) hX
    simpa [StdLayer.blackIndLayers] using this

end Categorification.Stendhal

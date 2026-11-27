/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KOneStepLift
import Categorification.WeightedKLR.RedStrands.PartialStandardizationLift
import Categorification.WeightedKLR.RedStrands.PartialStandardizationBlocksPlus

/-!
# Maps out of the partial standardization with three blocks

Webster, arXiv:1309.3796v3, §5.1 (partial standardization with several blocks, after
Definition 5.4), in the form used for the comparison map of Lemma 7.19 (K). Let `X` be a
`T^λ(θ + (β + γ))`-module (a representation `ρ`). A map from a module `N` over the three blocks
to `X` which intertwines the affine KLR algebras of the three blocks (acting on `N` through
`blocksOneStepMap` and on `X` through all strands) induces a `T^λ(θ + (β + γ))`-linear map
`BlocksStandard N → X` (`blocksStandardLift`, `blocksStandardLift_action`), equal to the given
map on the unit (`blocksStandardLift_unit`); a `T^λ(θ + (β + γ))`-linear map out of
`BlocksStandard N` is determined by its values on the unit (`blocksStandardLift_unique`). The
same holds for the partial standardization `PlusStandard` of `λ⁺` with blocks
`λ_1…λ_j; μ μ*; λ_{j+1}…λ_ℓ` (`plusStandardLift`, `plusStandardLift_action`,
`plusStandardLift_unit`, `plusStandardLift_unique`).

## Main definitions

* `Stendhal.blocksOneStepRep`: the affine KLR algebra of all strands of the one-step model,
  acting on `X`.
* `Stendhal.blocksStandardUnit`: the unit `N → BlocksStandard N`.
* `Stendhal.blocksStandardLift`, `Stendhal.CupCap.plusStandardLift`: the induced maps.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA
open scoped TensorProduct

theorem castKLR_symm_eq {J : Type*} [DecidableEq J] {k : Type*} [CommRing k]
    {P : J → J → MvPolynomial (Fin 2) k} {μ μ' : Multiset J} (h : μ = μ') :
    (castKLR P h).symm = castKLR P h.symm := by
  subst h; rfl

variable {I k : Type*} [DecidableEq I] [CommRing k] {a m r : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (a + (m + r)) → I →₀ ℕ) (θ β γ : Multiset I)
  (N : Type*) [AddCommGroup N] [Module k N] [Module (blocksFactorAlgebra Q Λ θ β γ) N]
  [IsScalarTower k (blocksFactorAlgebra Q Λ θ β γ) N]
  {X : Type*} [AddCommGroup X] [Module k X]
  (ρ : TensorProductAlgebra k Q Λ (θ + (β + γ)) →ₐ[k] Module.End k X)

local notation "α" =>
  Multiset.map (Sum.map (id : I → I) (Fin.castAdd (m + r))) (stendhalWeight a θ)
local notation "δ" =>
  Multiset.map (Sum.map (id : I → I) (Fin.natAdd a)) (stendhalWeight (m + r) (β + γ))
local notation "β̂" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd a))
  (Multiset.map (Sum.map (id : I → I) (Fin.castAdd r)) (stendhalWeight m β))
local notation "γ̂" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd a))
  (Multiset.map (Sum.map (id : I → I) (Fin.natAdd m)) (stendhalWeight r γ))
local notation "S" => stendhalQ Q Λ
local notation "N₃" => BlocksOneStepInput Q Λ θ β γ N

omit [DecidableEq I] in
/-- The identification of the weights of all strands of the iterated and one-step models. -/
theorem blocksAllWeight_eq : α + δ = α + (β̂ + γ̂) :=
  add_eq_add_of_eq rfl (blocksWeight_eq β γ)

/-- **The affine KLR algebra of all strands of the one-step model acting on `X`**, through
`T^λ(θ + (β + γ))`. -/
def blocksOneStepRep : KLRAlgebra k S (α + (β̂ + γ̂)) →ₐ[k] Module.End k X :=
  (ρ.comp (cutAffineMap Q Λ θ (β + γ))).comp
    (castKLR S (blocksAllWeight_eq (a := a) (m := m) (r := r) θ β γ)).symm.toAlgHom

theorem blocksOneStepRep_apply (z : KLRAlgebra k S (α + (β̂ + γ̂))) :
    blocksOneStepRep Q Λ θ β γ ρ z = ρ (cutAffineMap Q Λ θ (β + γ)
      ((castKLR S (blocksAllWeight_eq (a := a) (m := m) (r := r) θ β γ)).symm z)) := rfl

theorem blocksOneStepRep_castKLR (z : KLRAlgebra k S (α + δ)) :
    blocksOneStepRep Q Λ θ β γ ρ
        (castKLR S (blocksAllWeight_eq (a := a) (m := m) (r := r) θ β γ) z) =
      ρ (cutAffineMap Q Λ θ (β + γ) z) := by
  rw [blocksOneStepRep_apply, AlgEquiv.symm_apply_apply]

/-- In the one-step model the ordered loadings sum to `1` on `X`. -/
theorem blocksOneStepRep_eSum :
    blocksOneStepRep Q Λ θ β γ ρ (eSum S (blocksOneStepOrdered (a := a) (m := m) (r := r) θ β γ))
      = 1 := by
  rw [blocksOneStepRep_apply, castKLR_symm_eq, blocksOneStepOrdered, castKLR_eSum_redOrdered,
    ← cutOrderedLoadings, cutAffineMap_eSum, map_one]

variable (hQ : KLRSymm Q)

/-- **The unit of the partial standardization with three blocks**: `n ↦ 1 ⊗ n`, through the
one-step model. -/
def blocksStandardUnit : N →ₗ[k] BlocksStandard Q Λ θ β γ N hQ :=
  (blocksStandardOneStepEquiv Q Λ θ β γ N hQ).symm.toLinearMap ∘ₗ
    (Submodule.mkQ _ ∘ₗ (ind3UnitLin : N₃ →ₗ[k] Ind3 S α β̂ γ̂ N₃))

variable {Q Λ θ β γ N ρ}

/-- **The map out of the partial standardization with three blocks** induced by a map
`f : N → X` intertwining the three blocks. -/
def blocksStandardLift (f : N₃ →ₗ[k] X) (hf : IsInd3InputHom (blocksOneStepRep Q Λ θ β γ ρ) f) :
    BlocksStandard Q Λ θ β γ N hQ →ₗ[k] X :=
  (ind3QuotLift _ f hf (blocksOneStepRep_eSum Q Λ θ β γ ρ)).comp
    (blocksStandardOneStepEquiv Q Λ θ β γ N hQ).toLinearMap

theorem blocksStandardLift_apply (f : N₃ →ₗ[k] X)
    (hf : IsInd3InputHom (blocksOneStepRep Q Λ θ β γ ρ) f) (v : BlocksStandard Q Λ θ β γ N hQ) :
    blocksStandardLift hQ f hf v = ind3QuotLift _ f hf (blocksOneStepRep_eSum Q Λ θ β γ ρ)
      (blocksStandardOneStepEquiv Q Λ θ β γ N hQ v) := rfl

/-- **The induced map is linear over `T^λ(θ + (β + γ))`.** -/
theorem blocksStandardLift_action (f : N₃ →ₗ[k] X)
    (hf : IsInd3InputHom (blocksOneStepRep Q Λ θ β γ ρ) f)
    (t : TensorProductAlgebra k Q Λ (θ + (β + γ))) (v : BlocksStandard Q Λ θ β γ N hQ) :
    blocksStandardLift hQ f hf (blocksStandardAction Q Λ θ β γ N hQ t v) =
      ρ t (blocksStandardLift hQ f hf v) := by
  obtain ⟨z, rfl⟩ := cutAffineMap_surjective Q Λ θ (β + γ) t
  obtain ⟨w, rfl⟩ := blocksStandardOfShuffle_surjective Q Λ θ β γ N hQ v
  have h1 : blocksStandardOneStepEquiv Q Λ θ β γ N hQ (blocksStandardAction Q Λ θ β γ N hQ
      (cutAffineMap Q Λ θ (β + γ) z) (blocksStandardOfShuffle Q Λ θ β γ N hQ w)) =
      Submodule.Quotient.mk (castKLR S (blocksAllWeight_eq (a := a) (m := m) (r := r) θ β γ) z •
        blocksShuffleIndEquiv Q Λ θ β γ N w) :=
    blocksStandardOneStepEquiv_smul Q Λ θ β γ N hQ z w
  have h2 := blocksStandardOneStepEquiv_apply Q Λ θ β γ N hQ w
  rw [blocksStandardLift_apply, blocksStandardLift_apply]
  refine (congrArg (ind3QuotLift _ f hf _) h1).trans ?_
  refine (ind3QuotLift_smul _ f hf _ _ _).trans ?_
  exact (LinearMap.congr_fun (blocksOneStepRep_castKLR Q Λ θ β γ ρ z) _).trans
    (congrArg (fun q => ρ (cutAffineMap Q Λ θ (β + γ) z) (ind3QuotLift _ f hf _ q)) h2.symm)

/-- **The induced map is the given map on the unit.** -/
theorem blocksStandardLift_unit (f : N₃ →ₗ[k] X)
    (hf : IsInd3InputHom (blocksOneStepRep Q Λ θ β γ ρ) f) (n : N) :
    blocksStandardLift hQ f hf (blocksStandardUnit Q Λ θ β γ N hQ n) = f n := by
  simp only [blocksStandardLift, blocksStandardUnit, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, Submodule.mkQ_apply, ind3QuotLift_mk]
  exact ind3Lift_unit f hf n

/-- The one-step model, mapped back, is compatible with the actions. -/
theorem blocksStandardOneStepEquiv_symm_smul (z : KLRAlgebra k S (α + δ))
    (y : Ind3 S α β̂ γ̂ N₃) :
    (blocksStandardOneStepEquiv Q Λ θ β γ N hQ).symm (Submodule.Quotient.mk
        (castKLR S (blocksAllWeight_eq (a := a) (m := m) (r := r) θ β γ) z • y)) =
      blocksStandardAction Q Λ θ β γ N hQ (cutAffineMap Q Λ θ (β + γ) z)
        ((blocksStandardOneStepEquiv Q Λ θ β γ N hQ).symm (Submodule.Quotient.mk y)) := by
  obtain ⟨w, rfl⟩ := (blocksShuffleIndEquiv Q Λ θ β γ N).surjective y
  have h1 : blocksStandardOneStepEquiv Q Λ θ β γ N hQ (blocksStandardAction Q Λ θ β γ N hQ
      (cutAffineMap Q Λ θ (β + γ) z) (blocksStandardOfShuffle Q Λ θ β γ N hQ w)) =
      Submodule.Quotient.mk (castKLR S (blocksAllWeight_eq (a := a) (m := m) (r := r) θ β γ) z •
        blocksShuffleIndEquiv Q Λ θ β γ N w) :=
    blocksStandardOneStepEquiv_smul Q Λ θ β γ N hQ z w
  have h2 := blocksStandardOneStepEquiv_apply Q Λ θ β γ N hQ w
  let e := blocksStandardOneStepEquiv Q Λ θ β γ N hQ
  exact (congrArg e.symm h1.symm).trans ((e.symm_apply_apply _).trans
    (congrArg (blocksStandardAction Q Λ θ β γ N hQ (cutAffineMap Q Λ θ (β + γ) z))
      ((e.symm_apply_apply _).symm.trans (congrArg e.symm h2))))

/-- **A `T^λ(θ + (β + γ))`-linear map out of the partial standardization with three blocks is
determined by its values on the unit.** -/
theorem blocksStandardLift_unique {g g' : BlocksStandard Q Λ θ β γ N hQ →ₗ[k] X}
    (hg : ∀ t v, g (blocksStandardAction Q Λ θ β γ N hQ t v) = ρ t (g v))
    (hg' : ∀ t v, g' (blocksStandardAction Q Λ θ β γ N hQ t v) = ρ t (g' v))
    (he : ∀ n, g (blocksStandardUnit Q Λ θ β γ N hQ n) = g' (blocksStandardUnit Q Λ θ β γ N hQ n)) :
    g = g' := by
  let e := (blocksStandardOneStepEquiv Q Λ θ β γ N hQ).symm.toLinearMap ∘ₗ
    (Submodule.mkQ (excludedSpace (Algebra.lsmul k k (Ind3 S α β̂ γ̂ N₃) :
      KLRAlgebra k S (α + (β̂ + γ̂)) →ₐ[k] Module.End k (Ind3 S α β̂ γ̂ N₃))
      (blocksOneStepOrdered (a := a) (m := m) (r := r) θ β γ)))
  have hlin : ∀ h : BlocksStandard Q Λ θ β γ N hQ →ₗ[k] X,
      (∀ t v, h (blocksStandardAction Q Λ θ β γ N hQ t v) = ρ t (h v)) →
      ∀ z y, (h ∘ₗ e) (z • y) = blocksOneStepRep Q Λ θ β γ ρ z ((h ∘ₗ e) y) := by
    intro h hh z y
    obtain ⟨z, rfl⟩ := (castKLR S (blocksAllWeight_eq (a := a) (m := m) (r := r) θ β γ)).surjective
      z
    exact (congrArg h (blocksStandardOneStepEquiv_symm_smul hQ z y)).trans ((hh _ _).trans
      (LinearMap.congr_fun (blocksOneStepRep_castKLR Q Λ θ β γ ρ z).symm _))
  have hge : g ∘ₗ e = g' ∘ₗ e := ind3_ext (hlin g hg) (hlin g' hg') he
  refine LinearMap.ext fun v => ?_
  obtain ⟨q, rfl⟩ := (blocksStandardOneStepEquiv Q Λ θ β γ N hQ).symm.surjective v
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ q
  exact LinearMap.congr_fun hge y

/-! ### The partial standardization of `λ⁺` -/

namespace CupCap

variable {ℓ : ℕ} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {θ β γ : Multiset I}
  {N : Type*} [AddCommGroup N] [Module k N] [Module (PlusFactorAlgebra Q Λ Λc j hj θ β γ) N]
  [IsScalarTower k (PlusFactorAlgebra Q Λ Λc j hj θ β γ) N]
  {ρ : TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (θ + (β + γ)) →ₐ[k] Module.End k X}

/-- The representation `ρ` of `T^{λ⁺}(θ + (β + γ))`, on the labels of the model. -/
abbrev plusBlocksRep :
    TensorProductAlgebra k Q (plusBlockLabels Λ Λc j hj) (θ + (β + γ)) →ₐ[k] Module.End k X :=
  ρ.comp (castLabelsTensorProductAlgebra Q (plusBlock_card j hj) (plusLabels Λ Λc j hj)
    (θ + (β + γ))).toAlgHom

local notation "Nₚ" => BlocksOneStepInput Q (plusBlockLabels Λ Λc j hj) θ β γ
  (PlusInput Q Λ Λc j hj θ β γ N)

/-- **The map out of the partial standardization of `λ⁺`** induced by an intertwining map. -/
def plusStandardLift (f : Nₚ →ₗ[k] X)
    (hf : IsInd3InputHom (blocksOneStepRep Q (plusBlockLabels Λ Λc j hj) θ β γ
      (plusBlocksRep (ρ := ρ))) f) :
    PlusStandard Q Λ Λc j hj θ β γ N hQ →ₗ[k] X :=
  blocksStandardLift hQ f hf

/-- **The map out of the partial standardization of `λ⁺` is linear over `T^{λ⁺}`.** -/
theorem plusStandardLift_action (f : Nₚ →ₗ[k] X)
    (hf : IsInd3InputHom (blocksOneStepRep Q (plusBlockLabels Λ Λc j hj) θ β γ
      (plusBlocksRep (ρ := ρ))) f)
    (t : TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (θ + (β + γ)))
    (v : PlusStandard Q Λ Λc j hj θ β γ N hQ) :
    plusStandardLift hQ f hf (plusStandardAction Q Λ Λc j hj θ β γ N hQ t v) =
      ρ t (plusStandardLift hQ f hf v) := by
  refine (blocksStandardLift_action hQ f hf _ v).trans ?_
  change ρ ((castLabelsTensorProductAlgebra Q (plusBlock_card j hj) (plusLabels Λ Λc j hj)
    (θ + (β + γ))) ((castLabelsTensorProductAlgebra Q (plusBlock_card j hj)
      (plusLabels Λ Λc j hj) (θ + (β + γ))).symm t)) _ = _
  rw [AlgEquiv.apply_symm_apply]
  rfl

/-- The unit of the partial standardization of `λ⁺`. -/
abbrev plusStandardUnit : N →ₗ[k] PlusStandard Q Λ Λc j hj θ β γ N hQ :=
  blocksStandardUnit Q (plusBlockLabels Λ Λc j hj) θ β γ (PlusInput Q Λ Λc j hj θ β γ N) hQ

theorem plusStandardLift_unit (f : Nₚ →ₗ[k] X)
    (hf : IsInd3InputHom (blocksOneStepRep Q (plusBlockLabels Λ Λc j hj) θ β γ
      (plusBlocksRep (ρ := ρ))) f) (n : N) :
    plusStandardLift hQ f hf (plusStandardUnit hQ n) = f n :=
  blocksStandardLift_unit hQ f hf n

/-- **A `T^{λ⁺}`-linear map out of the partial standardization of `λ⁺` is determined by its
values on the unit.** -/
theorem plusStandardLift_unique {g g' : PlusStandard Q Λ Λc j hj θ β γ N hQ →ₗ[k] X}
    (hg : ∀ t v, g (plusStandardAction Q Λ Λc j hj θ β γ N hQ t v) = ρ t (g v))
    (hg' : ∀ t v, g' (plusStandardAction Q Λ Λc j hj θ β γ N hQ t v) = ρ t (g' v))
    (he : ∀ n, g (plusStandardUnit hQ n) = g' (plusStandardUnit hQ n)) : g = g' := by
  have hb : ∀ h : PlusStandard Q Λ Λc j hj θ β γ N hQ →ₗ[k] X,
      (∀ t v, h (plusStandardAction Q Λ Λc j hj θ β γ N hQ t v) = ρ t (h v)) →
      ∀ t v, h (blocksStandardAction Q (plusBlockLabels Λ Λc j hj) θ β γ _ hQ t v) =
        plusBlocksRep (ρ := ρ) t (h v) := by
    intro h hh t v
    have := hh ((castLabelsTensorProductAlgebra Q (plusBlock_card j hj) (plusLabels Λ Λc j hj)
      (θ + (β + γ))) t) v
    change h (blocksStandardAction Q (plusBlockLabels Λ Λc j hj) θ β γ _ hQ
      ((castLabelsTensorProductAlgebra Q (plusBlock_card j hj) (plusLabels Λ Λc j hj)
        (θ + (β + γ))).symm ((castLabelsTensorProductAlgebra Q (plusBlock_card j hj)
          (plusLabels Λ Λc j hj) (θ + (β + γ))) t)) v) = _ at this
    rw [AlgEquiv.symm_apply_apply] at this
    exact this
  exact blocksStandardLift_unique hQ (hb g hg) (hb g' hg') he

end CupCap

end Categorification.Stendhal

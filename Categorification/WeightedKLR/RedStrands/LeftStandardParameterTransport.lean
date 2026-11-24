/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.OrderedStandardResolution

/-!
# Transport of loading standards and their ordered resolutions

The universal property of a loading standard is preserved by an algebra
isomorphism fixing every loading idempotent. This transports the ordered
projective covers of Webster's Corollary 5.21 to another presentation.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR CategoryTheory ModuleFiltration

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type} [DecidableEq I] [Field k] {ℓ : ℕ} {ν : Multiset I}
  {Q Q' : I → I → MvPolynomial (Fin 2) k} (Λ : Fin ℓ → I →₀ ℕ)
  (σ : TensorProductAlgebra k Q Λ ν ≃+* TensorProductAlgebra k Q' Λ ν)
  (hσ : ∀ (t : Seq (stendhalWeight ℓ ν)) (ht : IsRedOrdered t),
    σ (seqIdem Q Λ t ht) = seqIdem Q' Λ t ht)
  (s : Seq (stendhalWeight ℓ ν)) (hs : IsRedOrdered s)

local notation "RingSource" => TensorProductAlgebra k Q Λ ν
local notation "RingTarget" => TensorProductAlgebra k Q' Λ ν
local notation "Source" => leftStandard Q Λ s hs
local notation "Target" => leftStandard Q' Λ s hs
set_option quotPrecheck false in
local notation "Restricted" =>
  (ModuleCat.restrictScalars σ.toRingHom).obj (ModuleCat.of RingTarget Target)
local notation "g" => leftStandardUnit Q Λ s hs
local notation "g'" => leftStandardUnit Q' Λ s hs

private theorem standardUnit_fixed : seqIdem Q' Λ s hs • g' = g' :=
  (leftStandard_mk_eq_smul_unit s hs
    ⟨seqIdem Q' Λ s hs, seqIdem_mul_self Q' Λ s hs⟩).symm

private def standardToRestricted : Source →ₗ[RingSource] Restricted :=
  leftStandardLift s hs (show Restricted from g') (fun t ht a hlt => by
    change σ (seqIdem Q Λ t ht * a) • g' = 0
    rw [map_mul, hσ t ht, mul_smul, seqIdem_smul_leftStandard_eq_zero Q' Λ hs ht hlt])

private theorem standardToRestricted_apply_unit :
    standardToRestricted Λ σ hσ s hs g = g' := by
  apply leftStandardLift_unit
  change σ (seqIdem Q Λ s hs) • g' = g'
  rw [hσ s hs, standardUnit_fixed]

include hσ in
private theorem symm_idem (t : Seq (stendhalWeight ℓ ν)) (ht : IsRedOrdered t) :
    σ.symm (seqIdem Q' Λ t ht) = seqIdem Q Λ t ht :=
  (σ.symm_apply_eq).mpr (hσ t ht).symm

/-- An algebra isomorphism fixing the loading idempotents transports the actual loading
standard to the actual standard with transported parameters. -/
def leftStandardRestrictedEquiv : Source ≃ₗ[RingSource] Restricted := by
  let forward := standardToRestricted Λ σ hσ s hs
  let backward := standardToRestricted Λ σ.symm (symm_idem Λ σ hσ) s hs
  refine { forward with invFun := fun v => backward v, left_inv := ?_, right_inv := ?_ }
  · intro v
    obtain ⟨a, rfl⟩ := leftStandard_exists_smul_unit s hs v
    change backward (forward (a • g)) = a • g
    rw [map_smul, show forward g = g' from standardToRestricted_apply_unit Λ σ hσ s hs]
    change backward (σ a • g') = a • g
    rw [map_smul, show backward g' = g from
      standardToRestricted_apply_unit Λ σ.symm (symm_idem Λ σ hσ) s hs]
    change σ.symm (σ a) • g = a • g
    rw [RingEquiv.symm_apply_apply]
  · intro (v : Target)
    obtain ⟨a, rfl⟩ := leftStandard_exists_smul_unit s hs v
    change forward (backward (a • g')) = a • (g' : Target)
    rw [map_smul, show backward g' = g from
      standardToRestricted_apply_unit Λ σ.symm (symm_idem Λ σ hσ) s hs]
    change forward (σ.symm a • g) = a • (g' : Target)
    rw [map_smul, show forward g = g' from standardToRestricted_apply_unit Λ σ hσ s hs]
    change σ (σ.symm a) • g' = a • g'
    rw [RingEquiv.apply_symm_apply]


local notation "Labels" => {t : Seq (stendhalWeight ℓ ν) // IsRedOrdered t}
set_option quotPrecheck false in
local notation "Std" => fun t : Labels => ModuleCat.of RingSource (leftStandard Q Λ t.1 t.2)
set_option quotPrecheck false in
local notation "StdTarget" => fun t : Labels => ModuleCat.of RingTarget (leftStandard Q' Λ t.1 t.2)
set_option quotPrecheck false in
local notation "U" t:arg =>
  (leftUpper Q Λ t.1 t.2).comap (lIdeal (seqIdem Q Λ t.1 t.2)).subtype
set_option quotPrecheck false in
local notation "above" => fun (c t : Labels) => StendhalLT c.1 t.1
set_option quotPrecheck false in
local notation "idemTarget" => fun t : Labels => seqIdem Q' Λ t.1 t.2

/-- Ordered covers of standards transport under a diagram algebra isomorphism
which preserves loading idempotents. -/
def orderedStandardCoversTransport
    (hU : ∀ t : Labels, ∃ m : List Labels, (∀ v ∈ m, above t v) ∧
      HasFiltration Std m (ModuleCat.of RingSource (U t))) :
    OrderedStandardCovers StdTarget idemTarget above := by
  let D := (orderedStandardCovers Q Λ hU).transport σ
  have he : (fun t : Labels => σ (seqIdem Q Λ t.1 t.2)) = idemTarget :=
    funext fun t => hσ t.1 t.2
  let D' : OrderedStandardCovers
      (fun t => (ModuleCat.restrictScalars σ.symm.toRingHom).obj (Std t)) idemTarget above :=
    he ▸ D
  exact D'.congrLayers fun t => (leftStandardRestrictedEquiv Λ σ.symm
    (symm_idem Λ σ hσ) t.1 t.2).symm

include hσ in
/-- The actual loading standard has an ordered projective resolution after
transporting the higher-kernel filtrations from another parameter. -/
theorem exists_ordered_projectiveResolution_leftStandard_transport
    (hU : ∀ t : Labels, ∃ m : List Labels, (∀ v ∈ m, above t v) ∧
      HasFiltration Std m (ModuleCat.of RingSource (U t))) (c : Labels) :
    ∃ P : ProjectiveResolution (StdTarget c), ∀ n : ℕ,
      ∃ (J : Type) (label : J → Labels)
        (inc : ∀ j, lIdeal (idemTarget (label j)) →ₗ[RingTarget] P.complex.X (n + 1)),
        (∀ j, above c (label j)) ∧ ∀ x : P.complex.X (n + 1),
          x ∈ Submodule.span RingTarget {y | ∃ j z, inc j z = y} := by
  let D := orderedStandardCoversTransport Λ σ hσ hU
  refine ⟨D.projectiveResolution c, D.projectiveResolution_loading_support c ?_⟩
  intro a b c hab hbc
  exact ⟨fun r i => (hab.1 r i).trans (hbc.1 r i), fun hca =>
    hab.2 (fun r i => (hbc.1 r i).trans (hca r i))⟩

end Categorification.Stendhal

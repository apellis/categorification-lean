/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationAssocRelabelComp
import Categorification.WeightedKLR.RedStrands.PartialStandardizationExact
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastIndMap

/-!
# The partial standardization at the last red strand is the parabolic standardization

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1. The
partial standardization at a cut whose second block is the last red strand `λ_{ℓ+1}`
(`CutStandard` with `r = 1`) has the factor algebra `T^{λ_1…λ_ℓ}(θ) ⊗ T^{λ_{ℓ+1}}(β)`; the
parabolic model of the standardization of the last red strand (`ParabolicStandard`), used for
Definition 5.4 in this library, has the factor algebra `T^{λ_1…λ_ℓ}(θ) ⊗ R^{λ_{ℓ+1}}(β)`, with the
cyclotomic quotient as the last factor. The two factor algebras are identified by Webster's
Theorem 4.20 for one red strand (`SingleRed.cyclotomicEquiv`), and the two models agree,
compatibly with the actions of `T^λ(θ + β)` (`parabolicCutStandardEquiv`,
`parabolicCutStandardEquiv_action`).

## Main definitions

* `Stendhal.parabolicCutFactorEquiv`: `T^{λ'}(θ) ⊗ R^{λ_{ℓ+1}}(β) ≃ T^{λ'}(θ) ⊗ T^{λ_{ℓ+1}}(β)`.
* `Stendhal.ParabolicOfCut`: a module over the factor algebra of the cut, as a module over the
  parabolic factor algebra.
* `Stendhal.parabolicCutStandardEquiv`: the parabolic standardization of `N` is the partial
  standardization of `N` at the last cut.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (θ β : Multiset I)

local notation "S" => stendhalQ Q Λ
local notation "α" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ)
local notation "αc" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd 1)) (stendhalWeight ℓ θ)
local notation "δₚ" =>
  Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ)) (stendhalWeight 1 β)
local notation "δ" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd ℓ)) (stendhalWeight 1 β)

omit [DecidableEq I] in
/-- The last red strand, as the image of the second block of the cut. -/
theorem lastIndex_eq_natAdd : (fun _ : Fin 1 => Fin.last ℓ) = Fin.natAdd ℓ :=
  funext fun i => Fin.ext (by simp [Fin.fin_one_eq_zero i])

omit [DecidableEq I] in
/-- The weights of the last red strand in the two models agree. -/
theorem parabolicCutWeight : δₚ = δ :=
  congrArg (fun g => (stendhalWeight 1 β).map (Sum.map (id : I → I) g)) lastIndex_eq_natAdd

omit [DecidableEq I] in
/-- The black and earlier red strands in the two models. -/
theorem parabolicCutPrefix : α = αc := rfl

/-- **The factor algebras of the two models agree**, by Theorem 4.20 for one red strand:
`T^{λ'}(θ) ⊗ R^{λ_{ℓ+1}}(β) ≃ T^{λ'}(θ) ⊗ T^{λ_{ℓ+1}}(β)`. -/
def parabolicCutFactorEquiv :
    parabolicFactorAlgebra Q Λ θ β ≃ₐ[k] cutFactorAlgebra (a := ℓ) (r := 1) Q Λ θ β :=
  Algebra.TensorProduct.congr AlgEquiv.refl
    ((SingleRed.cyclotomicEquiv Q (fun _ : Fin 1 => Λ (Fin.last ℓ)) β).trans
      (tensorProductAlgebraCast Q (congrArg (Λ ∘ ·) lastIndex_eq_natAdd) β))

theorem parabolicCutFactorEquiv_inputMap (t : TensorKLR S α δₚ) :
    parabolicCutFactorEquiv Q Λ θ β (parabolicInputMap Q Λ θ β t) =
      cutInputMap (a := ℓ) (r := 1) Q Λ θ β
        (castTensor S (parabolicCutPrefix θ) (parabolicCutWeight β) t) := by
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => rw [map_add, map_add, ht, ht', map_add, map_add]
  | tmul u w =>
    rw [castTensor_tmul]
    change (parabolicPrefixProjection Q Λ θ u) ⊗ₜ[k]
        tensorProductAlgebraCast Q (congrArg (Λ ∘ ·) lastIndex_eq_natAdd) β
          (SingleRed.cyclotomicEquiv Q (fun _ : Fin 1 => Λ (Fin.last ℓ)) β
            ((SingleRed.cyclotomicEquiv Q (fun _ : Fin 1 => Λ (Fin.last ℓ)) β).symm
              (parabolicLastProjection Q Λ β w))) =
      cutPrefixProjection (a := ℓ) (r := 1) Q Λ θ u ⊗ₜ[k]
        cutSuffixProjection (a := ℓ) (r := 1) Q Λ β (castKLR S (parabolicCutWeight β) w)
    rw [AlgEquiv.apply_symm_apply]
    exact congrArg _ (redSubfamilyProjection_congr Q lastIndex_eq_natAdd _ _ β w)

variable (N : Type*) [AddCommGroup N] [Module k N]
  [Module (cutFactorAlgebra (a := ℓ) (r := 1) Q Λ θ β) N]
  [IsScalarTower k (cutFactorAlgebra (a := ℓ) (r := 1) Q Λ θ β) N]

/-- A module over the factor algebra of the last cut, as a module over the parabolic factor
algebra. -/
@[nolint unusedArguments]
def ParabolicOfCut (_Q : I → I → MvPolynomial (Fin 2) k) (_Λ : Fin (ℓ + 1) → I →₀ ℕ)
    (_θ _β : Multiset I) (N : Type*) : Type _ := N

instance : AddCommGroup (ParabolicOfCut Q Λ θ β N) := inferInstanceAs (AddCommGroup N)
instance : Module k (ParabolicOfCut Q Λ θ β N) := inferInstanceAs (Module k N)
instance : Module (parabolicFactorAlgebra Q Λ θ β) (ParabolicOfCut Q Λ θ β N) :=
  Module.compHom N (parabolicCutFactorEquiv Q Λ θ β).toRingEquiv.toRingHom

omit [Module k N] [IsScalarTower k (cutFactorAlgebra (a := ℓ) (r := 1) Q Λ θ β) N] in
theorem parabolicOfCut_smul (d : parabolicFactorAlgebra Q Λ θ β) (n : ParabolicOfCut Q Λ θ β N) :
    d • n = (parabolicCutFactorEquiv Q Λ θ β d • (show N from n) : N) := rfl

instance : IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) (ParabolicOfCut Q Λ θ β N) where
  smul_assoc c d n := by
    rw [parabolicOfCut_smul, parabolicOfCut_smul, map_smul]
    exact smul_assoc c _ (show N from n)

local notation "Nₚ" => ParabolicOfCut Q Λ θ β N

/-- The identity of `N` intertwines the two input modules of induction. -/
def parabolicCutInputEquiv : ParabolicInput Q Λ θ β Nₚ ≃ₗ[k] CutInput (a := ℓ) (r := 1) Q Λ θ β N :=
  LinearEquiv.refl k N

omit [IsScalarTower k (cutFactorAlgebra (a := ℓ) (r := 1) Q Λ θ β) N] in
theorem parabolicCutInputEquiv_smul (t : TensorKLR S α δₚ) (n : ParabolicInput Q Λ θ β Nₚ) :
    parabolicCutInputEquiv Q Λ θ β N (t • n) =
      castTensor S (parabolicCutPrefix θ) (parabolicCutWeight β) t •
        parabolicCutInputEquiv Q Λ θ β N n := by
  change parabolicCutFactorEquiv Q Λ θ β (parabolicInputMap Q Λ θ β t) • (show N from n) =
    cutInputMap (a := ℓ) (r := 1) Q Λ θ β
      (castTensor S (parabolicCutPrefix θ) (parabolicCutWeight β) t) • (show N from n)
  rw [parabolicCutFactorEquiv_inputMap]

/-- The identification of the affine KLR algebras of all strands of the two models. -/
abbrev parabolicCutKLR : KLRAlgebra k S (α + δₚ) ≃ₐ[k] KLRAlgebra k S (αc + δ) :=
  castKLR S (add_eq_add_of_eq (parabolicCutPrefix θ) (parabolicCutWeight β))

/-- **The affine induced modules of the two models agree.** -/
def parabolicCutShuffleEquiv :
    ParabolicShuffle Q Λ θ β Nₚ ≃ₗ[k] CutShuffle (a := ℓ) (r := 1) Q Λ θ β N :=
  indTransport (parabolicCutKLR Q Λ θ β)
    (castTensor S (parabolicCutPrefix θ) (parabolicCutWeight β))
    (castKLR_concat (Q := S) (parabolicCutPrefix θ) (parabolicCutWeight β))
    (parabolicCutInputEquiv Q Λ θ β N)
    (parabolicCutInputEquiv_smul Q Λ θ β N)

omit [IsScalarTower k (cutFactorAlgebra (a := ℓ) (r := 1) Q Λ θ β) N] in
theorem parabolicCutShuffleEquiv_smul (z : KLRAlgebra k S (α + δₚ))
    (y : ParabolicShuffle Q Λ θ β Nₚ) :
    parabolicCutShuffleEquiv Q Λ θ β N (z • y) =
      parabolicCutKLR Q Λ θ β z • parabolicCutShuffleEquiv Q Λ θ β N y :=
  indTransport_smul _ _ _ _ _ z y

open Classical in
/-- An identification of weights carries the red-ordered loadings to the red-ordered loadings. -/
private theorem castKLR_eSum_redOrdered_last {μ μ' : Multiset (I ⊕ Fin (ℓ + 1))} (h : μ = μ') :
    castKLR S h (eSum S (Finset.univ.filter (fun s : Seq μ => IsRedOrdered s))) =
      eSum S (Finset.univ.filter (fun s : Seq μ' => IsRedOrdered s)) := by
  subst h; rfl

omit [IsScalarTower k (cutFactorAlgebra (a := ℓ) (r := 1) Q Λ θ β) N] in
theorem map_excludedSpace_parabolicCutShuffleEquiv :
    (excludedSpace (parabolicShuffleAction Q Λ θ β Nₚ) (parabolicOrderedLoadings (ℓ := ℓ) θ β)).map
        (parabolicCutShuffleEquiv Q Λ θ β N :
          ParabolicShuffle Q Λ θ β Nₚ →ₗ[k] CutShuffle (a := ℓ) (r := 1) Q Λ θ β N) =
      excludedSpace (cutShuffleAction (a := ℓ) (r := 1) Q Λ θ β N)
        (cutOrderedLoadings (a := ℓ) (r := 1) θ β) := by
  ext v
  obtain ⟨y, rfl⟩ := (parabolicCutShuffleEquiv Q Λ θ β N).surjective v
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]
  change (eSum S (parabolicOrderedLoadings (ℓ := ℓ) θ β) : KLRAlgebra k S (α + δₚ)) • y = 0 ↔
    (eSum S (cutOrderedLoadings (a := ℓ) (r := 1) θ β) : KLRAlgebra k S (αc + δ)) •
      parabolicCutShuffleEquiv Q Λ θ β N y = 0
  rw [show (eSum S (cutOrderedLoadings (a := ℓ) (r := 1) θ β) : KLRAlgebra k S (αc + δ)) =
      parabolicCutKLR Q Λ θ β (eSum S (parabolicOrderedLoadings (ℓ := ℓ) θ β)) from
    (castKLR_eSum_redOrdered_last Q Λ _).symm, ← parabolicCutShuffleEquiv_smul,
    LinearEquiv.map_eq_zero_iff]

/-- **The parabolic standardization is the partial standardization at the last cut**: for a
module `N` over `T^{λ'}(θ) ⊗ T^{λ_{ℓ+1}}(β)`, regarded as a module over
`T^{λ'}(θ) ⊗ R^{λ_{ℓ+1}}(β)`. -/
def parabolicCutStandardEquiv :
    ParabolicStandard Q Λ θ β Nₚ ≃ₗ[k] CutStandard (a := ℓ) (r := 1) Q Λ θ β N :=
  Submodule.Quotient.equiv _ _ (parabolicCutShuffleEquiv Q Λ θ β N)
    (map_excludedSpace_parabolicCutShuffleEquiv Q Λ θ β N)

omit [IsScalarTower k (cutFactorAlgebra (a := ℓ) (r := 1) Q Λ θ β) N] in
theorem parabolicCutStandardEquiv_mk (y : ParabolicShuffle Q Λ θ β Nₚ) :
    parabolicCutStandardEquiv Q Λ θ β N (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (parabolicCutShuffleEquiv Q Λ θ β N y) := by
  rw [parabolicCutStandardEquiv, Submodule.Quotient.equiv_apply, Submodule.mapQ_apply]
  rfl

private theorem castKLR_trans_cut {μ₁ μ₂ μ₃ : Multiset (I ⊕ Fin (ℓ + 1))} (h₁ : μ₁ = μ₂)
    (h₂ : μ₂ = μ₃) (z : KLRAlgebra k S μ₁) :
    castKLR S h₂ (castKLR S h₁ z) = castKLR S (h₁.trans h₂) z := by
  subst h₁ h₂; rfl

variable (hQ : KLRSymm Q)

/-- **The identification of the two models is linear over `T^λ(θ + β)`.** -/
theorem parabolicCutStandardEquiv_action (t : TensorProductAlgebra k Q Λ (θ + β))
    (z : ParabolicStandard Q Λ θ β Nₚ) :
    parabolicCutStandardEquiv Q Λ θ β N (parabolicStandardAction Q Λ θ β Nₚ hQ t z) =
      cutStandardAction (a := ℓ) (r := 1) Q Λ θ β N hQ t
        (parabolicCutStandardEquiv Q Λ θ β N z) := by
  obtain ⟨c, rfl⟩ := cutStandardAffine_surjective (a := ℓ) (r := 1) Q Λ θ β t
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ z
  obtain ⟨c', rfl⟩ := (parabolicCutKLR Q Λ θ β).surjective c
  have ht : castKLR S (cutInputWeights_add (a := ℓ) (r := 1) θ β) (parabolicCutKLR Q Λ θ β c') =
      castKLR S (parabolicInputWeights_add (ℓ := ℓ) θ β) c' :=
    castKLR_trans_cut Q Λ _ _ c'
  have h2 := LinearMap.congr_fun (parabolicStandardAction_affine Q Λ θ β Nₚ hQ c')
    (Submodule.mkQ _ y)
  have h3 := LinearMap.congr_fun
    (cutStandardAction_affine (a := ℓ) (r := 1) Q Λ θ β N hQ (parabolicCutKLR Q Λ θ β c'))
    (parabolicCutStandardEquiv Q Λ θ β N (Submodule.mkQ _ y))
  rw [← ht] at h2
  refine (congrArg (parabolicCutStandardEquiv Q Λ θ β N) h2).trans (Eq.trans ?_ h3.symm)
  exact (parabolicCutStandardEquiv_mk Q Λ θ β N (c' • y)).trans
    (congrArg Submodule.Quotient.mk (parabolicCutShuffleEquiv_smul Q Λ θ β N c' y))

end Categorification.Stendhal

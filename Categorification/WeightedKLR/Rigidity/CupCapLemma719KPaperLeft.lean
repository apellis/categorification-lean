/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KCutData
import Categorification.WeightedKLR.RedStrands.PartialStandardizationSingCut

/-!
# The left side of Lemma 7.19 (K): the standardization in stages at the cut

Webster, arXiv:1309.3796v3, Lemma 7.19 (K), `K S(Z) ≅ S_+(Z ⊠ L)`. For a module `Z` over the
algebra `(T^{λ_1} ⊗ ⋯ ⊗ T^{λ_j}) ⊗ (T^{λ_{j+1}} ⊗ ⋯ ⊗ T^{λ_ℓ})` of the singleton blocks of `λ`,
split at the `j`-th red strand, the standardization in stages `S(Z)` (`singStd`, with the
trivial spectator `k`) is identified with the partial standardization at the cut `KCutStd Y`
of the standardizations `Y` of the two blocks (`singCutEquiv`, the staged associativity), as
modules over `T^λ(θ_h + θ_t)` (`kPaperSEquiv`). Applying the reflected coevaluation gives the
left side `K^σ(S(Z)) ≅ KCutTarget` (`kPaperLeftEquiv`).

## Main definitions

* `Stendhal.CupCap.kPaperZ`: `Z` with the trivial spectator, the input of `singCutEquiv`.
* `Stendhal.CupCap.KPaperY`: the standardizations of the two blocks of `Z`.
* `Stendhal.CupCap.KPaperS`: the standardization in stages `S(Z)`, over `T^λ(θ_h + θ_t)`.
* `Stendhal.CupCap.kPaperSEquiv`: `S(Z) ≅ KCutStd Y`.
* `Stendhal.CupCap.kPaperLeftEquiv`: `K^σ(S(Z)) ≅ KCutTarget`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory KLR KLRAlgebra TypeA
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} (j : ℕ) (hj : j ≤ ℓ)
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
  (θ : Fin (j + (ℓ - j)) → Multiset I) (hQ : KLRSymm Q)

set_option hygiene false in
local notation "Λ'" => cutLabels j hj Λ
set_option hygiene false in
local notation "Sh" => singAlg Q j (Λ' ∘ Fin.castAdd (ℓ - j)) (θ ∘ Fin.castAdd (ℓ - j))
set_option hygiene false in
local notation "St" => singAlg Q (ℓ - j) (Λ' ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j)
set_option hygiene false in
local notation "w₁" => singWeight j (θ ∘ Fin.castAdd (ℓ - j))
set_option hygiene false in
local notation "w₂" => singWeight (ℓ - j) (θ ∘ Fin.natAdd j)
set_option hygiene false in
local notation "Kk" => AlgCat.of k k

/-- The algebra of the singleton blocks of `λ`, split at the cut. -/
abbrev kPaperAlg : AlgCat k := AlgCat.of k (Sh ⊗[k] St)

variable (Z : ModuleCat (kPaperAlg j hj Q Λ θ))

/-- The algebra map `T_h ⊗ (T_t ⊗ k) → T_h ⊗ T_t` dropping the trivial spectator. -/
def kPaperRid : Sh ⊗[k] (AlgCat.of k (St ⊗[k] k) : AlgCat k) →ₐ[k] Sh ⊗[k] St :=
  Algebra.TensorProduct.map (AlgHom.id k _) (Algebra.TensorProduct.rid k k St).toAlgHom

/-- `Z` with the trivial spectator, the input of `singCutEquiv`. -/
abbrev kPaperZ : ModuleCat (Sh ⊗[k] (AlgCat.of k (St ⊗[k] k) : AlgCat k)) :=
  (ModuleCat.restrictScalars (kPaperRid j hj Q Λ θ).toRingHom).obj Z

/-- The standardizations of the two blocks of `Z` at the cut, a module over
`T^{λ_1…λ_j}(θ_h) ⊗ T^{λ_{j+1}…λ_ℓ}(θ_t)`. -/
abbrev KPaperY : Type :=
  CutSpectInput (a := j) (r := ℓ - j) Q Λ' w₁ w₂ Kk
    ((singOuter Q hQ j (ℓ - j) Λ' θ Kk).obj (kPaperZ j hj Q Λ θ Z))

/-- The standardization in stages of all red strands of `Z`. -/
abbrev kPaperStd : ModuleCat (TensorProductAlgebra k Q Λ' (singWeight (j + (ℓ - j)) θ) ⊗[k] Kk) :=
  (singStd Q hQ (j + (ℓ - j)) Λ' θ Kk).obj
    ((ModuleCat.restrictScalars (singSplit Q j (ℓ - j) Λ' θ Kk).toRingHom).obj
      (kPaperZ j hj Q Λ θ Z))

/-- The algebra map `T^λ(θ_h + θ_t) → T^{λ'}(θ_1 + ⋯ + θ_ℓ) ⊗ k`, through the reindexing of the
labels and the weight. -/
def kPaperRho : TensorProductAlgebra k Q Λ (w₁ + w₂) →ₐ[k]
    TensorProductAlgebra k Q Λ' (singWeight (j + (ℓ - j)) θ) ⊗[k] Kk :=
  (Algebra.TensorProduct.includeLeft).comp
    ((castTensorProductAlgebra Q Λ' (singWeight_add j (ℓ - j) θ)).symm.toAlgHom.comp
      (castLabelsTensorProductAlgebra Q (Nat.add_sub_of_le hj) Λ (w₁ + w₂)).symm.toAlgHom)

/-- **The standardization in stages `S(Z)`**, as a module over `T^λ(θ_h + θ_t)`. -/
@[nolint unusedArguments]
def KPaperS : Type := kPaperStd j hj Q Λ θ hQ Z

instance : AddCommGroup (KPaperS j hj Q Λ θ hQ Z) :=
  inferInstanceAs (AddCommGroup (kPaperStd j hj Q Λ θ hQ Z))

instance : Module (TensorProductAlgebra k Q Λ (w₁ + w₂)) (KPaperS j hj Q Λ θ hQ Z) :=
  Module.compHom (kPaperStd j hj Q Λ θ hQ Z) (kPaperRho j hj Q Λ θ).toRingHom

theorem kPaperS_smul_def (t : TensorProductAlgebra k Q Λ (w₁ + w₂))
    (m : KPaperS j hj Q Λ θ hQ Z) :
    t • m = (kPaperRho j hj Q Λ θ t) • (show kPaperStd j hj Q Λ θ hQ Z from m) := rfl

/-- The staged associativity at the cut, `singCutEquiv`, for the trivial spectator. -/
abbrev kPaperCut := singCutEquiv Q hQ j (ℓ - j) Λ' θ Kk (kPaperZ j hj Q Λ θ Z)

/-- The underlying additive isomorphism `S(Z) ≅ KCutStd Y`. -/
def kPaperCutAdd :
    KPaperS j hj Q Λ θ hQ Z ≃+ KCutStd j hj Q Λ w₁ w₂ (KPaperY j hj Q Λ θ hQ Z) hQ :=
  (kPaperCut j hj Q Λ θ hQ Z).equiv

theorem kPaperCutAdd_smul (t : TensorProductAlgebra k Q Λ (w₁ + w₂))
    (m : KPaperS j hj Q Λ θ hQ Z) :
    kPaperCutAdd j hj Q Λ θ hQ Z (t • m) = t • kPaperCutAdd j hj Q Λ θ hQ Z m := by
  have h1 := (kPaperCut j hj Q Λ θ hQ Z).map_smul (kPaperRho j hj Q Λ θ t) m
  have e1 : kPaperCutAdd j hj Q Λ θ hQ Z (t • m) =
      (kPaperCut j hj Q Λ θ hQ Z).equiv
        (kPaperRho j hj Q Λ θ t • (show kPaperStd j hj Q Λ θ hQ Z from m)) := rfl
  rw [e1, h1]
  have hx : (singWeightCast Q j (ℓ - j) Λ' θ Kk).toRingHom (kPaperRho j hj Q Λ θ t) =
      (castLabelsTensorProductAlgebra Q (Nat.add_sub_of_le hj) Λ (w₁ + w₂)).symm t ⊗ₜ[k]
        (1 : Kk) := by
    have h2 : (singWeightCast Q j (ℓ - j) Λ' θ Kk).toRingHom (kPaperRho j hj Q Λ θ t) =
        (castTensorProductAlgebra Q Λ' (singWeight_add j (ℓ - j) θ))
          ((castTensorProductAlgebra Q Λ' (singWeight_add j (ℓ - j) θ)).symm
            ((castLabelsTensorProductAlgebra Q (Nat.add_sub_of_le hj) Λ (w₁ + w₂)).symm t)) ⊗ₜ[k]
          (1 : Kk) := rfl
    rw [h2, AlgEquiv.apply_symm_apply]
  rw [hx]
  have e2 : ((castLabelsTensorProductAlgebra Q (Nat.add_sub_of_le hj) Λ (w₁ + w₂)).symm t ⊗ₜ[k]
        (1 : Kk)) • (kPaperCut j hj Q Λ θ hQ Z).equiv m =
      cutStandardAction Q Λ' w₁ w₂ (KPaperY j hj Q Λ θ hQ Z) hQ
        ((castLabelsTensorProductAlgebra Q (Nat.add_sub_of_le hj) Λ (w₁ + w₂)).symm t)
        (cutSpectAction Q Λ' w₁ w₂ Kk ((singOuter Q hQ j (ℓ - j) Λ' θ Kk).obj
          (kPaperZ j hj Q Λ θ Z)) 1 ((kPaperCut j hj Q Λ θ hQ Z).equiv m)) := rfl
  exact e2.trans (congrArg (cutStandardAction Q Λ' w₁ w₂ (KPaperY j hj Q Λ θ hQ Z) hQ
    ((castLabelsTensorProductAlgebra Q (Nat.add_sub_of_le hj) Λ (w₁ + w₂)).symm t))
    (LinearMap.congr_fun (map_one (cutSpectAction Q Λ' w₁ w₂ Kk
      ((singOuter Q hQ j (ℓ - j) Λ' θ Kk).obj (kPaperZ j hj Q Λ θ Z))))
      ((kPaperCut j hj Q Λ θ hQ Z).equiv m)))

/-- **`S(Z) ≅ KCutStd Y`**: the standardization in stages is the partial standardization at
the cut of the standardizations of the two blocks, linearly over `T^λ(θ_h + θ_t)`. -/
def kPaperSEquiv :
    KPaperS j hj Q Λ θ hQ Z ≃ₗ[TensorProductAlgebra k Q Λ (w₁ + w₂)]
      KCutStd j hj Q Λ w₁ w₂ (KPaperY j hj Q Λ θ hQ Z) hQ :=
  { kPaperCutAdd j hj Q Λ θ hQ Z with
    map_smul' := kPaperCutAdd_smul j hj Q Λ θ hQ Z }

theorem kPaperSEquiv_apply (m : KPaperS j hj Q Λ θ hQ Z) :
    kPaperSEquiv j hj Q Λ θ hQ Z m = kPaperCutAdd j hj Q Λ θ hQ Z m := rfl

variable (Λc : Fin 2 → I →₀ ℕ) (ν₀ : Multiset I) (L' : Type) [AddCommGroup L'] [Module k L']
  [Module (TensorProductAlgebra k Q Λc ν₀) L'] [IsScalarTower k (TensorProductAlgebra k Q Λc ν₀) L']

/-- **The left side of Lemma 7.19 (K)**: `K^σ(S(Z))`, the reflected coevaluation of the
standardization in stages. -/
abbrev KPaperLeft : Type :=
  CoeTensor j hj Q Λ Λc (w₁ + w₂) ν₀ (CapCoef Q Λc ν₀ L') (KPaperS j hj Q Λ θ hQ Z)

set_option hygiene false in
local notation "Tp" => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) ((w₁ + w₂) + ν₀)

/-- The `k`-module structure of the left side, through `k → T^{λ⁺}`. -/
instance : Module k (KPaperLeft j hj Q Λ θ hQ Z Λc ν₀ L') :=
  Module.compHom _ (algebraMap k Tp)

instance : IsScalarTower k Tp (KPaperLeft j hj Q Λ θ hQ Z Λc ν₀ L') where
  smul_assoc c t x := by
    change (c • t) • x = algebraMap k Tp c • t • x
    rw [Algebra.smul_def, mul_smul]

/-- **`K^σ(S(Z)) ≅ K^σ(S_cut Y)`**, linearly over `T^{λ⁺}`. -/
def kPaperLeftEquiv :
    KPaperLeft j hj Q Λ θ hQ Z Λc ν₀ L' ≃ₗ[Tp]
      KCutTarget j hj Q Λ Λc w₁ w₂ ν₀ (KPaperY j hj Q Λ θ hQ Z) hQ L' :=
  LinearEquiv.ofLinearMap (coeTensorMap (kPaperSEquiv j hj Q Λ θ hQ Z).toLinearMap)
    (coeTensorMap (kPaperSEquiv j hj Q Λ θ hQ Z).symm.toLinearMap)
    (by
      rw [← coeTensorMap_comp, LinearEquiv.comp_symm]
      exact coeTensorMap_id)
    (by
      rw [← coeTensorMap_comp, LinearEquiv.symm_comp]
      exact coeTensorMap_id)

end Categorification.Stendhal.CupCap

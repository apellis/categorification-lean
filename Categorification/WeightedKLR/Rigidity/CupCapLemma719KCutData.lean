/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KFlip
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KBlocksLift
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KSpectator
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KCoef

/-!
# The two sides of Lemma 7.19 (K) at the cut

Webster, arXiv:1309.3796v3, Lemma 7.19 (K), `K S(Z) ≅ S_+(Z ⊠ L)`, reduced to the cut at the
`j`-th red strand. For a module `Y` over the algebra `T^{λ_1…λ_j}(θ) ⊗ T^{λ_{j+1}…λ_ℓ}(γ)` of
the two blocks of `λ` at the cut and a left `T^{μ μ*}(ν₀)`-module `L'`:

* the left side is `K^σ(S_cut Y)`, the reflected coevaluation (`CoeTensor`, with the cap
  coefficients `CapCoef L'`) of the partial standardization of `Y` at the cut, a left module
  over `T^{λ⁺}((θ + γ) + ν₀)` (`KCutTarget`);
* the right side is the partial standardization of `λ⁺` with blocks
  `λ_1…λ_j; μ μ*; λ_{j+1}…λ_ℓ` of `Y ⊠ L' = MidSpect Y L'`, a left module over
  `T^{λ⁺}(θ + (ν₀ + γ))` (`PlusStandard`).

The algebra of the two blocks at the cut of `λ` is, definitionally, the tensor product of the
outer blocks of `λ⁺` (`cutFactorAlgebra` at `cutLabels`), so `Y ⊠ L'` is a module over the
algebra of the three blocks of `λ⁺` with no transport. The actions on the left side are
transported along the reindexing `Λ ∘ Fin.cast` of the labels and along
`θ + (ν₀ + γ) = (θ + γ) + ν₀` (`kCutRep`).

## Main definitions

* `Stendhal.CupCap.cutLabels`: the labels of `λ`, indexed by `Fin (j + (ℓ - j))`.
* `Stendhal.CupCap.KCutStd`: the partial standardization of `Y` at the cut, a left
  `T^λ(θ + γ)`-module.
* `Stendhal.CupCap.KCutTarget`: its reflected coevaluation, a `k`-module.
* `Stendhal.CupCap.kCutRep`: the action of `T^{λ⁺}(θ + (ν₀ + γ))` on it.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} (j : ℕ) (hj : j ≤ ℓ)
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  (θ γ ν₀ : Multiset I)

/-- The labels of `λ`, indexed by `Fin (j + (ℓ - j))` for the cut at the `j`-th red strand. -/
abbrev cutLabels : Fin (j + (ℓ - j)) → I →₀ ℕ := Λ ∘ Fin.cast (Nat.add_sub_of_le hj)

/-- **The algebra of the two blocks of `λ` at the cut is the algebra of the outer blocks of
`λ⁺`**, definitionally. -/
theorem cutFactorAlgebra_cutLabels :
    cutFactorAlgebra Q (cutLabels j hj Λ) θ γ =
      (TensorProductAlgebra k Q (Λ ∘ Fin.castLE hj) θ ⊗[k]
        TensorProductAlgebra k Q (plusTailLabels Λ j hj) γ) := rfl

variable (Y : Type) [AddCommGroup Y] [Module k Y]
  [Module (cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) Y]
  [IsScalarTower k (cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) Y] (hQ : KLRSymm Q)

set_option hygiene false in
local notation "Dout" => TensorProductAlgebra k Q (Λ ∘ Fin.castLE hj) θ ⊗[k]
  TensorProductAlgebra k Q (plusTailLabels Λ j hj) γ

/-- `Y` as a module over the outer blocks of `λ⁺` (`cutFactorAlgebra_cutLabels`). -/
instance : Module Dout Y := ‹Module (cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) Y›

instance : IsScalarTower k Dout Y :=
  ‹IsScalarTower k (cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) Y›

/-- **The partial standardization of `Y` at the cut**, as a left `T^λ(θ + γ)`-module. -/
@[nolint unusedArguments]
def KCutStd (_hQ : KLRSymm Q) : Type := CutStandard Q (cutLabels j hj Λ) θ γ Y

instance : AddCommGroup (KCutStd j hj Q Λ θ γ Y hQ) :=
  inferInstanceAs (AddCommGroup (CutStandard Q (cutLabels j hj Λ) θ γ Y))

instance : Module k (KCutStd j hj Q Λ θ γ Y hQ) :=
  inferInstanceAs (Module k (CutStandard Q (cutLabels j hj Λ) θ γ Y))

/-- The action of `T^λ(θ + γ)` on the partial standardization at the cut. -/
def kCutStdAction :
    TensorProductAlgebra k Q Λ (θ + γ) →ₐ[k] Module.End k (KCutStd j hj Q Λ θ γ Y hQ) :=
  (cutStandardAction Q (cutLabels j hj Λ) θ γ Y hQ).comp
    (castLabelsTensorProductAlgebra Q (Nat.add_sub_of_le hj) Λ (θ + γ)).symm.toAlgHom

instance : Module (TensorProductAlgebra k Q Λ (θ + γ)) (KCutStd j hj Q Λ θ γ Y hQ) :=
  Module.compHom _ (kCutStdAction j hj Q Λ θ γ Y hQ).toRingHom

theorem kCutStd_smul_def (t : TensorProductAlgebra k Q Λ (θ + γ))
    (v : KCutStd j hj Q Λ θ γ Y hQ) : t • v = kCutStdAction j hj Q Λ θ γ Y hQ t v := rfl

variable (L' : Type) [AddCommGroup L'] [Module k L']
  [Module (TensorProductAlgebra k Q Λc ν₀) L'] [IsScalarTower k (TensorProductAlgebra k Q Λc ν₀) L']

/-- **The left side of Lemma 7.19 (K) at the cut**: `K^σ(S_cut Y)`, the reflected coevaluation of
the partial standardization of `Y` at the cut, with the cap coefficients `CapCoef L'`. -/
def KCutTarget : Type :=
  CoeTensor j hj Q Λ Λc (θ + γ) ν₀ (CapCoef Q Λc ν₀ L') (KCutStd j hj Q Λ θ γ Y hQ)

set_option hygiene false in
local notation "Tp" => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) ((θ + γ) + ν₀)

instance : AddCommGroup (KCutTarget j hj Q Λ Λc θ γ ν₀ Y hQ L') :=
  inferInstanceAs (AddCommGroup (CoeTensor j hj Q Λ Λc (θ + γ) ν₀ (CapCoef Q Λc ν₀ L')
    (KCutStd j hj Q Λ θ γ Y hQ)))

instance : Module Tp (KCutTarget j hj Q Λ Λc θ γ ν₀ Y hQ L') :=
  inferInstanceAs (Module Tp (CoeTensor j hj Q Λ Λc (θ + γ) ν₀ (CapCoef Q Λc ν₀ L')
    (KCutStd j hj Q Λ θ γ Y hQ)))

/-- The `k`-module structure of the left side, through `k → T^{λ⁺}`. -/
instance : Module k (KCutTarget j hj Q Λ Λc θ γ ν₀ Y hQ L') :=
  Module.compHom _ (algebraMap k Tp)

instance : IsScalarTower k Tp (KCutTarget j hj Q Λ Λc θ γ ν₀ Y hQ L') where
  smul_assoc c t x := by
    change (c • t) • x = algebraMap k Tp c • t • x
    rw [Algebra.smul_def, mul_smul]

instance : SMulCommClass Tp k (KCutTarget j hj Q Λ Λc θ γ ν₀ Y hQ L') where
  smul_comm t c x := by
    change t • algebraMap k Tp c • x = algebraMap k Tp c • t • x
    rw [← mul_smul, ← mul_smul, Algebra.commutes]

omit [DecidableEq I] in
/-- The black weight of `λ⁺` in the model, `θ + (ν₀ + γ)`, is `(θ + γ) + ν₀`. -/
theorem plusWeight_eq : θ + (ν₀ + γ) = (θ + γ) + ν₀ := by
  rw [add_comm ν₀ γ, add_assoc]

/-- **The action of `T^{λ⁺}(θ + (ν₀ + γ))` on the left side.** -/
def kCutRep : TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (θ + (ν₀ + γ)) →ₐ[k]
    Module.End k (KCutTarget j hj Q Λ Λc θ γ ν₀ Y hQ L') :=
  (Algebra.lsmul k k (KCutTarget j hj Q Λ Λc θ γ ν₀ Y hQ L')).comp
    (castTensorProductAlgebra Q (plusLabels Λ Λc j hj) (plusWeight_eq θ γ ν₀)).toAlgHom

example : Module (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) (MidSpect (k := k) Y L') :=
  inferInstance

/-- **The right side of Lemma 7.19 (K) at the cut**: the partial standardization of `λ⁺` of
`Y ⊠ L' = MidSpect Y L'`. -/
abbrev KCutSource : Type :=
  PlusStandard Q Λ Λc j hj θ ν₀ γ (MidSpect (k := k) Y L') hQ

end Categorification.Stendhal.CupCap

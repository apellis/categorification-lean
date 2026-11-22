/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicStandardTensorFiltration

/-!
# The base case of the tensor-form recursion

In the proof of Proposition 5.20 of B. Webster, *Knot invariants and higher representation
theory*, arXiv:1309.3796v2, the projective `T^λ e(s, λ_ℓ, w)` is filtered by standardizations
`S(X ⊠ Y)`, starting from the red layer `T^{λ'} e(s) ⊠ R^{λ_ℓ}_0` and applying `F_w`. This file
proves the base case and records which modules occur.

## Main definitions and results

* `zeroRestrict`: a factor module with empty last block, as a module over `T^{λ'}`.
* `zeroTensorEquiv`: `M ≅ M ⊠ R^{λ_ℓ}_0` (the cyclotomic quotient at weight `0` is `k`).
* `OldGen`, `CycGen`: the inductions of the projectives `T^{λ'} e(s)` and of `R^{λ_ℓ}_0`.
* `tensorForm_redLayer_wordLayers`: every layer of `F_w` applied to the red layer of `T^λ e(s)`
  has the form `S(X ⊠ Y)` with `X ∈ OldGen`, `Y ∈ CycGen`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR KLRAlgebra InductionAlong MulOpposite ModuleFiltration
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} {k : Type} [DecidableEq I] [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ)

local notation "Si" j => (Singleton.singleton j : Multiset I)
local notation "old" => Λ ∘ Fin.castSucc
local notation "aΛ" => fun j => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) j
local notation "Told" => TensorProductAlgebra k Q (old)
local notation "Cyc" => CycKLR k Q (aΛ)

section Zero

variable {θ : Multiset I} (M : FactorModule Q Λ θ 0)

/-- The module structure over `T^{λ'}_θ` of a factor module with empty last block. -/
abbrev zeroRestrictInst : Module (Told θ) M.carrier :=
  Module.compHom _ (emptyFactorEquiv Q Λ θ).symm.toAlgHom.toRingHom

/-- A factor module with empty last block, as a module over `T^{λ'}_θ`. -/
def zeroRestrict : ModuleCat.{0} (Told θ) :=
  letI := zeroRestrictInst Q Λ M
  ModuleCat.of _ M.carrier

theorem emptyFactorEquiv_symm_apply (a : Told θ) :
    (emptyFactorEquiv Q Λ θ).symm a = a ⊗ₜ[k] 1 := by
  apply (emptyFactorEquiv Q Λ θ).injective
  rw [AlgEquiv.apply_symm_apply]
  simp [emptyFactorEquiv]

theorem tmul_eq_algebraMap_mul (a : Told θ) (c : Cyc 0) :
    (a ⊗ₜ[k] c : parabolicFactorAlgebra Q Λ θ 0) =
      algebraMap k _ (cyclotomicZeroEquiv Q (aΛ) c) * (a ⊗ₜ[k] 1) := by
  have hc : c = algebraMap k (Cyc 0) (cyclotomicZeroEquiv Q (aΛ) c) := by
    conv_lhs => rw [← (cyclotomicZeroEquiv Q (aΛ)).symm_apply_apply c]
    exact AlgEquiv.commutes _ _
  conv_lhs => rw [hc]
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
    TensorProduct.tmul_smul, TensorProduct.smul_tmul']

local notation "Z" => tensorFactor Q Λ (zeroRestrict Q Λ M) (ModuleCat.of (Cyc 0) (Cyc 0))

theorem kmod_zeroRestrict_smul (c : k) (x : KMod (k := k) (zeroRestrict Q Λ M)) :
    c • x = (c • (show M.carrier from x) : M.carrier) := by
  change (emptyFactorEquiv Q Λ θ).symm (algebraMap k _ c) • (show M.carrier from x) = _
  rw [AlgEquiv.commutes, algebraMap_smul]

/-- An element of `X ⊠ R^{λ_ℓ}_0`'s first factor, as an element of `M`. -/
def zeroElt (x : KMod (k := k) (zeroRestrict Q Λ M)) : M.carrier := x

/-- An element of the second factor, as an element of `R^{λ_ℓ}_0`. -/
def zeroCyc (c : KMod (k := k) (ModuleCat.of (Cyc 0) (Cyc 0))) : Cyc 0 := c

theorem zeroElt_smul (a : Told θ) (x : KMod (k := k) (zeroRestrict Q Λ M)) :
    zeroElt Q Λ M (a • x) =
      (a ⊗ₜ[k] (1 : Cyc 0) : parabolicFactorAlgebra Q Λ θ 0) • zeroElt Q Λ M x := by
  change (emptyFactorEquiv Q Λ θ).symm a • zeroElt Q Λ M x = _
  rw [emptyFactorEquiv_symm_apply]

/-- The bilinear map `x ⊗ c ↦ ε(c) x`. -/
def zeroTensorBil : KMod (k := k) (zeroRestrict Q Λ M) →ₗ[k] KMod (k := k)
    (ModuleCat.of (Cyc 0) (Cyc 0)) →ₗ[k] M.carrier :=
  LinearMap.mk₂ k (fun x c => cyclotomicZeroEquiv Q (aΛ) (zeroCyc Q Λ c) • zeroElt Q Λ M x)
    (fun x y c => smul_add _ _ _)
    (fun r x c => by
      change _ • zeroElt Q Λ M (r • x) = r • (_ • zeroElt Q Λ M x)
      rw [zeroElt, kmod_zeroRestrict_smul]
      exact smul_comm _ _ _)
    (fun x c d => by
      change cyclotomicZeroEquiv Q (aΛ) (zeroCyc Q Λ c + zeroCyc Q Λ d) • _ = _
      rw [map_add, add_smul])
    (fun r x c => by
      change cyclotomicZeroEquiv Q (aΛ) (algebraMap k _ r * zeroCyc Q Λ c) • _ = _
      rw [map_mul, AlgEquiv.commutes, mul_smul]
      rfl)

/-- The unit of `R^{λ_ℓ}_0`, as an element of the second factor. -/
def oneC : KMod (k := k) (ModuleCat.of (Cyc 0) (Cyc 0)) := (1 : Cyc 0)
/-- An element of `M`, as an element of the first factor. -/
def toZero (m : M.carrier) : KMod (k := k) (zeroRestrict Q Λ M) := m
theorem toZero_smul (r : k) (x : KMod (k := k) (zeroRestrict Q Λ M)) :
    toZero Q Λ M (r • zeroElt Q Λ M x) = r • x :=
  (kmod_zeroRestrict_smul Q Λ M r x).symm
theorem smul_oneC (c : KMod (k := k) (ModuleCat.of (Cyc 0) (Cyc 0))) :
    cyclotomicZeroEquiv Q (aΛ) (zeroCyc Q Λ c) • oneC Q Λ = c := by
  change algebraMap k (Cyc 0) (cyclotomicZeroEquiv Q (aΛ) (zeroCyc Q Λ c)) * 1 = zeroCyc Q Λ c
  rw [mul_one]
  conv_rhs => rw [← (cyclotomicZeroEquiv Q (aΛ)).symm_apply_apply (zeroCyc Q Λ c)]
  exact (AlgEquiv.commutes _ _).symm
/-- `X ⊠ R^{λ_ℓ}_0 ≅ M` for `X = M` viewed over `T^{λ'}_θ`. -/
def zeroTensorEquiv : (Z).carrier ≃ₗ[parabolicFactorAlgebra Q Λ θ 0] M.carrier where
  toFun := ExtTensor.lift (zeroTensorBil Q Λ M)
  map_add' := map_add _
  map_smul' t z := by
    refine ExtTensor.smul_eq_induction (F := ExtTensor.lift (zeroTensorBil Q Λ M))
      (map_add _) (map_zero _) (fun a b x c => ?_) t z
    rw [ExtTensor.smul_tmul, ExtTensor.lift_tmul, ExtTensor.lift_tmul]
    change cyclotomicZeroEquiv Q (aΛ) (b * zeroCyc Q Λ c) • zeroElt Q Λ M (a • x) =
      (a ⊗ₜ[k] b) • (cyclotomicZeroEquiv Q (aΛ) (zeroCyc Q Λ c) • zeroElt Q Λ M x)
    rw [zeroElt_smul, tmul_eq_algebraMap_mul Q Λ a b, map_mul, mul_smul, mul_smul,
      algebraMap_smul, smul_comm ((cyclotomicZeroEquiv Q (aΛ)) (zeroCyc Q Λ c))]
  invFun m := ExtTensor.tmul (toZero Q Λ M m) (oneC Q Λ)
  left_inv z := by
    induction z using ExtTensor.induction_on with
    | zero => exact ExtTensor.zero_tmul _
    | tmul x c =>
      change ExtTensor.tmul (toZero Q Λ M (cyclotomicZeroEquiv Q (aΛ) (zeroCyc Q Λ c) •
        zeroElt Q Λ M x)) (oneC Q Λ) = ExtTensor.tmul x c
      rw [toZero_smul, ← ExtTensor.smul_tmul', ← ExtTensor.tmul_smul, smul_oneC]
    | add x y hx hy =>
      rw [map_add]
      conv_rhs => rw [← hx, ← hy]
      exact ExtTensor.add_tmul _ _ _
  right_inv m := by
    change cyclotomicZeroEquiv Q (aΛ) 1 • m = m
    rw [map_one, one_smul]

variable {Q Λ}

/-- A factor module with empty last block has tensor form `M ⊠ R^{λ_ℓ}_0`, when its restriction
to `T^{λ'}_θ` lies in `𝒳` and `R^{λ_ℓ}_0` lies in `𝒴`. -/
theorem FactorModule.TensorForm.zero
    {𝒳 : ∀ θ : Multiset I, ModuleCat.{0} (Told θ) → Prop}
    {𝒴 : ∀ β : Multiset I, ModuleCat.{0} (Cyc β) → Prop}
    (hX : 𝒳 θ (zeroRestrict Q Λ M)) (hY : 𝒴 0 (ModuleCat.of (Cyc 0) (Cyc 0))) :
    M.TensorForm Q Λ 𝒳 𝒴 :=
  ⟨zeroRestrict Q Λ M, ModuleCat.of (Cyc 0) (Cyc 0), hX, hY,
    ⟨(zeroTensorEquiv Q Λ M).symm⟩⟩

end Zero

/-- The modules over `T^{λ'}` that occur as first factors in the recursion of Proposition 5.20:
the projectives `T^{λ'} e(s)` (as restrictions of the red factor modules) and their black
inductions. -/
inductive OldGen : ∀ θ : Multiset I, ModuleCat.{0} (Told θ) → Prop
  | base {θ : Multiset I} (s : Seq (stendhalWeight ℓ (θ + 0))) (hs : IsRedOrdered s) :
      OldGen θ (zeroRestrict Q Λ (redFactorModule Q Λ θ s hs))
  | ind (j : I) {θ : Multiset I} (X : ModuleCat.{0} (Told θ)) :
      OldGen θ X → OldGen ((Si j) + θ) (oldIndModule Q Λ j X)

/-- The modules over the cyclotomic quotients `R^{λ_ℓ}` that occur as second factors in the
recursion of Proposition 5.20: `R^{λ_ℓ}_0` and its black inductions. -/
inductive CycGen : ∀ β : Multiset I, ModuleCat.{0} (Cyc β) → Prop
  | base : CycGen 0 (ModuleCat.of (Cyc 0) (Cyc 0))
  | ind (j : I) {β : Multiset I} (Y : ModuleCat.{0} (Cyc β)) :
      CycGen β Y → CycGen ((Si j) + β) (cycIndModule Q Λ j Y)

/-- Every layer of `F_w T^λ e(s)`'s standard filtration has the form `S(X ⊠ Y)` with `X` an
induction of `T^{λ'} e(s)` and `Y` an induction of `R^{λ_ℓ}_0` (Webster, arXiv:1309.3796v2,
proof of Proposition 5.20). -/
theorem tensorForm_redLayer_wordLayers (w : List I) {θ : Multiset I}
    (s : Seq (stendhalWeight ℓ (θ + 0))) (hs : IsRedOrdered s) :
    ∀ c ∈ (redLayer Q Λ θ s hs).wordLayers Q Λ w, c.TensorForm Q Λ (OldGen Q Λ) (CycGen Q Λ) :=
  StdLayer.TensorForm.wordLayers (fun j _ X hX => OldGen.ind j X hX)
    (fun j _ Y hY => CycGen.ind j Y hY) w
    (FactorModule.TensorForm.zero _ (OldGen.base s hs) CycGen.base)

end Categorification.Stendhal

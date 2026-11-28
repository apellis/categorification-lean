/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.RigidityExtStdResolution
import Categorification.WeightedKLR.RedStrands.Vacuum

/-!
# Factor modules with no black strands left of the last red strand

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.1, proof of
Proposition 7.8: the last term of the resolution of `L_λ` is a sum of standardizations over the
split `0 + ν`, whose factor algebra is `T^{λ'}_0 ⊗ R^{λ_ℓ}_ν ≅ R^{λ_ℓ}_ν`, since `T^{λ'}_0` is the
ground field (`tensorProductAlgebraZeroEquiv`). A factor module `N` over this split is
`T^{λ'}_0 ⊠ N|_{R^{λ_ℓ}}` (`vacuumTensorEquiv`), the mirror of `zeroTensorEquiv`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR KLRAlgebra
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} {k : Type} [DecidableEq I] [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ)

local notation "old" => Λ ∘ Fin.castSucc
local notation "aΛ" => fun j => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) j
local notation "Told" => TensorProductAlgebra k Q (old)
local notation "Cyc" => CycKLR k Q (aΛ)

section Vacuum

variable {β : Multiset I} (M : FactorModule Q Λ 0 β)

/-- The module structure over `R^{λ_ℓ}_β` of a factor module with no black strand left of the
last red strand, through `c ↦ 1 ⊗ c`. -/
abbrev vacuumRestrictInst : Module (Cyc β) M.carrier :=
  Module.compHom _ (Algebra.TensorProduct.includeRight (R := k) (A := Told 0)
    (B := Cyc β)).toRingHom

/-- A factor module over the split `0 + β`, as a module over `R^{λ_ℓ}_β`. -/
def vacuumRestrict : ModuleCat.{0} (Cyc β) :=
  letI := vacuumRestrictInst Q Λ M
  ModuleCat.of _ M.carrier

/-- The regular module of `T^{λ'}_0`. -/
abbrev vacuumRegular : ModuleCat.{0} (Told 0) := ModuleCat.of (Told 0) (Told 0)

local notation "Z" => tensorFactor Q Λ (vacuumRegular Q Λ) (vacuumRestrict Q Λ M)
local notation "φ" => tensorProductAlgebraZeroEquiv (k := k) Q (old)

theorem kmod_vacuumRestrict_smul (c : k) (x : KMod (k := k) (vacuumRestrict Q Λ M)) :
    c • x = (c • (show M.carrier from x) : M.carrier) := by
  change (1 ⊗ₜ[k] algebraMap k (Cyc β) c : parabolicFactorAlgebra Q Λ 0 β) •
    (show M.carrier from x) = _
  rw [← Algebra.TensorProduct.algebraMap_apply', algebraMap_smul]

/-- An element of the second factor, as an element of `M`. -/
def vacuumElt (x : KMod (k := k) (vacuumRestrict Q Λ M)) : M.carrier := x

/-- An element of the first factor, as an element of `T^{λ'}_0`. -/
def vacuumScalar (a : KMod (k := k) (vacuumRegular Q Λ)) : Told 0 := a

theorem vacuumElt_smul (b : Cyc β) (x : KMod (k := k) (vacuumRestrict Q Λ M)) :
    vacuumElt Q Λ M (b • x) =
      ((1 : Told 0) ⊗ₜ[k] b : parabolicFactorAlgebra Q Λ 0 β) • vacuumElt Q Λ M x := rfl

theorem tmul_eq_algebraMap_mul_vacuum (a : Told 0) (b : Cyc β) :
    (a ⊗ₜ[k] b : parabolicFactorAlgebra Q Λ 0 β) =
      algebraMap k _ (φ a) * ((1 : Told 0) ⊗ₜ[k] b) := by
  have ha : a = algebraMap k (Told 0) (φ a) := by
    conv_lhs => rw [← (φ).symm_apply_apply a]
    exact AlgEquiv.commutes _ _
  conv_lhs => rw [ha]
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    mul_one]

/-- The bilinear map `a ⊗ x ↦ φ(a) x`. -/
def vacuumTensorBil : KMod (k := k) (vacuumRegular Q Λ) →ₗ[k]
    KMod (k := k) (vacuumRestrict Q Λ M) →ₗ[k] M.carrier :=
  LinearMap.mk₂ k (fun a x => φ (vacuumScalar Q Λ a) • vacuumElt Q Λ M x)
    (fun a a' x => by
      change φ (vacuumScalar Q Λ a + vacuumScalar Q Λ a') • _ = _
      rw [map_add, add_smul])
    (fun r a x => by
      change φ (algebraMap k _ r * vacuumScalar Q Λ a) • _ = _
      rw [map_mul, AlgEquiv.commutes, mul_smul]
      rfl)
    (fun a x y => smul_add _ _ _)
    (fun r a x => by
      change _ • vacuumElt Q Λ M (r • x) = r • (_ • vacuumElt Q Λ M x)
      rw [vacuumElt, kmod_vacuumRestrict_smul]
      exact smul_comm _ _ _)

/-- The unit of `T^{λ'}_0`, as an element of the first factor. -/
def oneT : KMod (k := k) (vacuumRegular Q Λ) := (1 : Told 0)

/-- An element of `M`, as an element of the second factor. -/
def toVacuum (m : M.carrier) : KMod (k := k) (vacuumRestrict Q Λ M) := m

theorem toVacuum_smul (r : k) (x : KMod (k := k) (vacuumRestrict Q Λ M)) :
    toVacuum Q Λ M (r • vacuumElt Q Λ M x) = r • x :=
  (kmod_vacuumRestrict_smul Q Λ M r x).symm

theorem smul_oneT (a : KMod (k := k) (vacuumRegular Q Λ)) :
    φ (vacuumScalar Q Λ a) • oneT Q Λ = a := by
  change algebraMap k (Told 0) (φ (vacuumScalar Q Λ a)) * 1 = vacuumScalar Q Λ a
  rw [mul_one]
  conv_rhs => rw [← (φ).symm_apply_apply (vacuumScalar Q Λ a)]
  exact (AlgEquiv.commutes _ _).symm

/-- **`T^{λ'}_0 ⊠ N|_{R^{λ_ℓ}} ≅ N`** for a factor module `N` over the split `0 + β`. -/
def vacuumTensorEquiv : (Z).carrier ≃ₗ[parabolicFactorAlgebra Q Λ 0 β] M.carrier where
  toFun := ExtTensor.lift (vacuumTensorBil Q Λ M)
  map_add' := map_add _
  map_smul' t z := by
    refine ExtTensor.smul_eq_induction (F := ExtTensor.lift (vacuumTensorBil Q Λ M))
      (map_add _) (map_zero _) (fun a b c x => ?_) t z
    rw [ExtTensor.smul_tmul, ExtTensor.lift_tmul, ExtTensor.lift_tmul]
    change φ (a * vacuumScalar Q Λ c) • vacuumElt Q Λ M (b • x) =
      (a ⊗ₜ[k] b) • (φ (vacuumScalar Q Λ c) • vacuumElt Q Λ M x)
    rw [vacuumElt_smul, tmul_eq_algebraMap_mul_vacuum Q Λ a b, map_mul, mul_smul, mul_smul,
      algebraMap_smul, smul_comm (φ (vacuumScalar Q Λ c))]
  invFun m := ExtTensor.tmul (oneT Q Λ) (toVacuum Q Λ M m)
  left_inv z := by
    induction z using ExtTensor.induction_on with
    | zero => exact ExtTensor.tmul_zero _
    | tmul c x =>
      change ExtTensor.tmul (oneT Q Λ) (toVacuum Q Λ M (φ (vacuumScalar Q Λ c) •
        vacuumElt Q Λ M x)) = ExtTensor.tmul c x
      rw [toVacuum_smul, ExtTensor.tmul_smul, ExtTensor.smul_tmul', smul_oneT]
    | add x y hx hy =>
      rw [map_add]
      conv_rhs => rw [← hx, ← hy]
      exact ExtTensor.tmul_add _ _ _
  right_inv m := by
    change φ 1 • m = m
    rw [map_one, one_smul]

end Vacuum

end Categorification.Stendhal

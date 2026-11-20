/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.IndLastStrandFirstFactor
import Categorification.KLR.IndLastStrandDescent

/-!
# The last strand of an induced module through an idempotent quotient, one-sided case

Khovanov–Lauda I (arXiv:0803.4121v2), Proposition 2.18, for `ν' = ν₀' + i` and `i ∉ ν`,
descended to the quotient of `Ind_{ν,ν'} N` by the kernel of an idempotent `P` commuting with
`e = 1_{-,i}` (`lastIdemOf`). If `P e = ι(P₂ ⊗ 1_i)`, then `Φ` induces an isomorphism

`Ind_{ν,ν₀'} ₂N / ker P₂ ≃ Ind_{ν,ν'} N / ker (P e)`

(`oneSidedDescendEquiv`). This is the KLR input of B. Webster, *Knot invariants and higher
representation theory*, arXiv:1309.3796v3, proof of Proposition 5.5, when `i` occurs in the
weight of the last block only.

Symmetrically, for `ν = ν₀ + i` and `i ∉ ν'`, with `P e = ι(P₁ ⊗ 1_i)`, the map `Ψ` of
`IndLastStrandFirstFactor` induces `Ind_{ν₀,ν'} ₁N / ker P₁ ≃ Ind_{ν,ν'} N / ker (P e)`
(`firstSidedDescendEquiv`), the case where `i` occurs in the weight of the first block only.

## Main results

* `oneSidedDescend_surjective`, `oneSidedDescendEquiv` (`i ∉ ν`);
* `indFirst_smul`, `firstSidedDescend_surjective`, `firstSidedDescendEquiv` (`i ∉ ν'`).
-/

namespace Categorification.KLR

open IdempotentQuotient
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}

local notation "Si" i:max => (Singleton.singleton i : Multiset I)

namespace KLRAlgebra

section OneSidedDescent

variable {ν ν₀' : Multiset I} {i : I}

theorem lastIdemOf_mul_self :
    lastIdemOf Q ν ν₀' i * lastIdemOf Q ν ν₀' i = lastIdemOf Q ν ν₀' i := by
  rw [lastIdemOf, ← map_mul, oneConcat_idem.eq]

variable {N : Type*} [AddCommGroup N] [Module k N]
  [Module (TensorKLR Q ν (ν₀' + ({i} : Multiset I))) N]
  [IsScalarTower k (TensorKLR Q ν (ν₀' + ({i} : Multiset I))) N]

local notation "Φ" => indAppend (Q := Q) (ν := ν) (ν₀' := ν₀') (i := i) (N := N)
local notation "L" => Algebra.lsmul k k (Ind Q ν (ν₀' + Si i) N)
local notation "Lt" => Algebra.lsmul k k (Ind Q ν ν₀' (ResRight Q ν ν₀' i N))

-- `{i}` rather than the `Si` notation: notation is not hygienic inside `variable` binders.
variable {P : KLRAlgebra k Q (ν + (ν₀' + {i}))} {P₂ : KLRAlgebra k Q (ν + ν₀')}
  (hP : IsIdempotentElem P) (hc : Commute P (lastIdemOf Q ν ν₀' i))
  (hP₂ : P * lastIdemOf Q ν ν₀' i =
    castKLR Q (add_assoc ν ν₀' {i}) (appendR Q (ν + ν₀') i P₂))

include hP₂ in
theorem indAppend_smul_oneSided (x : Ind Q ν ν₀' (ResRight Q ν ν₀' i N)) :
    Φ (P₂ • x) = (L P * L (lastIdemOf Q ν ν₀' i)) (Φ x) := by
  simp only [indAppend_smul, Module.End.mul_apply, Algebra.lsmul_coe, smul_smul, hP₂]

/-- `Φ : Ind_{ν,ν₀'} ₂N / ker P₂ → Ind_{ν,ν'} N / ker (P e)`. -/
noncomputable abbrev oneSidedDescend :=
  descend (Lt P₂) (L P * L (lastIdemOf Q ν ν₀' i)) Φ (indAppend_smul_oneSided hP₂)

variable (hsym : KLRSymm Q)

include hsym in
theorem oneSidedDescend_injective : Function.Injective (oneSidedDescend (N := N) hP₂) :=
  descend_injective _ _ _ _ (indAppend_injective hsym)

include hsym hP hc in
/-- **For `i ∉ ν`, `Φ` descends to a surjection.** -/
theorem oneSidedDescend_surjective (hi : i ∉ ν) :
    Function.Surjective (oneSidedDescend (N := N) hP₂) := by
  intro w
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  have hfix : lastIdemOf Q ν ν₀' i • (P * lastIdemOf Q ν ν₀' i) • y =
      (P * lastIdemOf Q ν ν₀' i) • y := by
    rw [smul_smul, ← mul_assoc, ← hc.eq, mul_assoc, lastIdemOf_mul_self]
  obtain ⟨x, hx⟩ := mem_range_indAppend_of_lastIdemOf_smul hsym hi hfix
  refine ⟨Submodule.Quotient.mk x, ?_⟩
  change Submodule.Quotient.mk (Φ x) = _
  rw [hx, Submodule.Quotient.eq, LinearMap.mem_ker, map_sub, sub_eq_zero]
  have hid : IsIdempotentElem (P * lastIdemOf Q ν ν₀' i) :=
    IsIdempotentElem.mul_of_commute hc hP lastIdemOf_mul_self
  simp only [Module.End.mul_apply, Algebra.lsmul_coe, smul_smul, ← mul_assoc]
  rw [mul_assoc (P * lastIdemOf Q ν ν₀' i), hid.eq]

/-- **`Ind_{ν,ν₀'} ₂N / ker P₂ ≃ Ind_{ν,ν'} N / ker (P e)` for `i ∉ ν`.** -/
noncomputable def oneSidedDescendEquiv (hi : i ∉ ν) :
    (Ind Q ν ν₀' (ResRight Q ν ν₀' i N) ⧸ LinearMap.ker (Lt P₂)) ≃ₗ[k]
      (Ind Q ν (ν₀' + Si i) N ⧸ LinearMap.ker (L P * L (lastIdemOf Q ν ν₀' i))) :=
  LinearEquiv.ofBijective (oneSidedDescend hP₂)
    ⟨oneSidedDescend_injective hP₂ hsym, oneSidedDescend_surjective hP hc hP₂ hsym hi⟩

theorem oneSidedDescendEquiv_mk (hi : i ∉ ν) (x : Ind Q ν ν₀' (ResRight Q ν ν₀' i N)) :
    oneSidedDescendEquiv hP hc hP₂ hsym hi (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (Φ x) := rfl

end OneSidedDescent

section FirstSidedDescent

variable {ν₀ ν' : Multiset I} {i : I}

/-- `a ↦ ι(a ⊗ 1_i)`, `R(ν₀ + ν') → R(ν + ν')`, for `ν = ν₀ + i`. -/
noncomputable def firstAppend (i : I) (a : KLRAlgebra k Q (ν₀ + ν')) :
    KLRAlgebra k Q (ν₀ + Si i + ν') :=
  castKLR Q (firstQuad_h ν₀ ν' i).symm (appendR Q _ i a)

theorem firstIdem_mul_self :
    firstIdem Q ν₀ ν' i * firstIdem Q ν₀ ν' i = firstIdem Q ν₀ ν' i := by
  rw [firstIdem, ← map_mul, oneConcat_idem.eq]

theorem firstBimod_smul (a : KLRAlgebra k Q (ν₀ + ν')) (r : IndBimod Q ν₀ ν') :
    firstBimod Q ν₀ ν' i (a • r) = firstAppend i a • firstBimod Q ν₀ ν' i r :=
  Subtype.ext (by
    rw [Submodule.coe_smul, smul_eq_mul, firstBimod_apply, firstBimod_apply, coe_firstElt,
      coe_firstElt, Submodule.coe_smul, smul_eq_mul, firstAppend]
    simp only [map_mul, mul_assoc])

variable {N : Type*} [AddCommGroup N] [Module k N]
  [Module (TensorKLR Q (ν₀ + ({i} : Multiset I)) ν') N]
  [IsScalarTower k (TensorKLR Q (ν₀ + ({i} : Multiset I)) ν') N]

/-- **`Ψ` intertwines `a` with `ι(a ⊗ 1_i)`.** -/
theorem indFirst_smul (hi : i ∉ ν') (a : KLRAlgebra k Q (ν₀ + ν'))
    (x : Ind Q ν₀ ν' (ResFirst Q ν₀ ν' i N)) :
    indFirst N hi (a • x) = firstAppend i a • indFirst N hi x := by
  induction x using BalancedTensor.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul r n =>
    rw [BalancedTensor.smul_tmul', indFirst_tmul, indFirst_tmul, firstBimod_smul,
      BalancedTensor.smul_tmul']
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

local notation "Lf" => Algebra.lsmul k k (Ind Q (ν₀ + Si i) ν' N)
local notation "Lo" => Algebra.lsmul k k (Ind Q ν₀ ν' (ResFirst Q ν₀ ν' i N))

-- `{i}` rather than the `Si` notation: notation is not hygienic inside `variable` binders.
variable {P : KLRAlgebra k Q (ν₀ + {i} + ν')} {P₁ : KLRAlgebra k Q (ν₀ + ν')}
  (hP : IsIdempotentElem P) (hc : Commute P (firstIdem Q ν₀ ν' i))
  (hP₁ : P * firstIdem Q ν₀ ν' i = firstAppend i P₁) (hi : i ∉ ν')

include hP₁ in
theorem indFirst_smul_firstSided (x : Ind Q ν₀ ν' (ResFirst Q ν₀ ν' i N)) :
    indFirst N hi (P₁ • x) = (Lf P * Lf (firstIdem Q ν₀ ν' i)) (indFirst N hi x) := by
  simp only [indFirst_smul, Module.End.mul_apply, Algebra.lsmul_coe, smul_smul, hP₁]

/-- `Ψ : Ind_{ν₀,ν'} ₁N / ker P₁ → Ind_{ν,ν'} N / ker (P e)`. -/
noncomputable abbrev firstSidedDescend :=
  descend (Lo P₁) (Lf P * Lf (firstIdem Q ν₀ ν' i)) (indFirst N hi)
    (indFirst_smul_firstSided hP₁ hi)

variable (hsym : KLRSymm Q)

include hsym in
theorem firstSidedDescend_injective : Function.Injective (firstSidedDescend (N := N) hP₁ hi) :=
  descend_injective _ _ _ _ (indFirst_injective hsym hi)

include hsym hP hc in
/-- **For `i ∉ ν'`, `Ψ` descends to a surjection.** -/
theorem firstSidedDescend_surjective : Function.Surjective (firstSidedDescend (N := N) hP₁ hi) := by
  intro w
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  have hfix : firstIdem Q ν₀ ν' i • (P * firstIdem Q ν₀ ν' i) • y =
      (P * firstIdem Q ν₀ ν' i) • y := by
    rw [smul_smul, ← mul_assoc, ← hc.eq, mul_assoc, firstIdem_mul_self]
  obtain ⟨x, hx⟩ := mem_range_indFirst hsym hi hfix
  refine ⟨Submodule.Quotient.mk x, ?_⟩
  change Submodule.Quotient.mk (indFirst N hi x) = _
  rw [hx, Submodule.Quotient.eq, LinearMap.mem_ker, map_sub, sub_eq_zero]
  have hid : IsIdempotentElem (P * firstIdem Q ν₀ ν' i) :=
    IsIdempotentElem.mul_of_commute hc hP firstIdem_mul_self
  simp only [Module.End.mul_apply, Algebra.lsmul_coe, smul_smul, ← mul_assoc]
  rw [mul_assoc (P * firstIdem Q ν₀ ν' i), hid.eq]

/-- **`Ind_{ν₀,ν'} ₁N / ker P₁ ≃ Ind_{ν,ν'} N / ker (P e)` for `i ∉ ν'`.** -/
noncomputable def firstSidedDescendEquiv :
    (Ind Q ν₀ ν' (ResFirst Q ν₀ ν' i N) ⧸ LinearMap.ker (Lo P₁)) ≃ₗ[k]
      (Ind Q (ν₀ + Si i) ν' N ⧸ LinearMap.ker (Lf P * Lf (firstIdem Q ν₀ ν' i))) :=
  LinearEquiv.ofBijective (firstSidedDescend hP₁ hi)
    ⟨firstSidedDescend_injective hP₁ hi hsym, firstSidedDescend_surjective hP hc hP₁ hi hsym⟩

theorem firstSidedDescendEquiv_mk (x : Ind Q ν₀ ν' (ResFirst Q ν₀ ν' i N)) :
    firstSidedDescendEquiv hP hc hP₁ hi hsym (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (indFirst N hi x) := rfl

end FirstSidedDescent

end KLRAlgebra

end Categorification.KLR

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.IndLastStrandExact
import Categorification.Algebra.IdempotentQuotientExact

/-!
# The last strand of an induced module, through an idempotent quotient

Khovanov–Lauda I (arXiv:0803.4121v2), Proposition 2.18, descended to the quotient of
`Ind_{ν,ν'} N` (`ν = ν₀ + i`, `ν' = ν₀' + i`) by the kernel of an idempotent `P` of
`R(ν + ν')` commuting with `1_{-,i}`. This is the form used in the proof of B. Webster,
*Knot invariants and higher representation theory*, arXiv:1309.3796v3, Proposition 5.5,
where `P` is the sum of the idempotents of the red-ordered loadings and the quotient is a
standard module.

Write `e = 1_{-,i}` and suppose `P e = ι(P₂ ⊗ 1_i)` for some `P₂ ∈ R(ν + ν₀')`; let
`P₁ ∈ R(ν₀ + ν')` be `P₂` transported along `ν₀ + ν' = ν + ν₀'`. The surjection
`π : Ind_{ν,ν'} N → Ind_{ν₀,ν'} ₁N`, `y ↦ Ψ⁻¹[e y]` (`lastProj`), and `Φ` give the exact
sequence

`0 → Ind_{ν,ν₀'} ₂N / ker P₂ → Ind_{ν,ν'} N / ker (P e) → Ind_{ν₀,ν'} ₁N / ker P₁ → 0`

(`lastDescend_injective`, `lastDescend_exact`, `lastDescend_surjective`). The middle term is the
`e`-fixed part of `Ind_{ν,ν'} N / ker P` (`IdempotentQuotient.rangeEquiv`).

## Main results

* `indLast_smul`, `lastProj_smul`: `Ψ` and `π` intertwine `a` with `ι(a ⊗ 1_i)`;
* `lastDescend_injective`, `lastDescend_exact`, `lastDescend_surjective`.
-/

namespace Categorification.KLR

open Equiv MvPolynomial TypeA MulOpposite IdempotentQuotient
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}

local notation "Si" i:max => (Singleton.singleton i : Multiset I)

namespace KLRAlgebra

section Descent

variable {ν₀ ν₀' : Multiset I} {i : I}

/-- `a ↦ ι(a ⊗ 1_i)`, `R(ν₀ + ν') → R(ν + ν')`, for `ν = ν₀ + i`, `ν' = ν₀' + i`. -/
noncomputable def lastAppend (a : KLRAlgebra k Q (ν₀ + (ν₀' + Si i))) :
    KLRAlgebra k Q (ν₀ + Si i + (ν₀' + Si i)) :=
  castKLR Q (add_assoc (ν₀ + Si i) ν₀' (Si i))
    (appendR Q _ i (castKLR Q (lastQuad_h₁ ν₀ ν₀' i) a))

theorem lastIdem_mul_self :
    lastIdem Q ν₀ ν₀' i * lastIdem Q ν₀ ν₀' i = lastIdem Q ν₀ ν₀' i := by
  rw [lastIdem, ← map_mul, oneConcat_idem.eq]

theorem lastIdem_mul_lastAppend (a : KLRAlgebra k Q (ν₀ + (ν₀' + Si i))) :
    lastIdem Q ν₀ ν₀' i * lastAppend a = lastAppend a := by
  rw [lastIdem, lastAppend, ← map_mul, ← appendR_one, ← map_mul, one_mul]

theorem lastAppend_mul_lastIdem (a : KLRAlgebra k Q (ν₀ + (ν₀' + Si i))) :
    lastAppend a * lastIdem Q ν₀ ν₀' i = lastAppend a := by
  rw [lastIdem, lastAppend, ← map_mul, ← appendR_one, ← map_mul, mul_one]

theorem lastBimod_smul (a : KLRAlgebra k Q (ν₀ + (ν₀' + Si i))) (r : IndBimod Q ν₀ (ν₀' + Si i)) :
    lastBimod Q ν₀ ν₀' i (a • r) = lastAppend a • lastBimod Q ν₀ ν₀' i r :=
  Subtype.ext (by
    rw [Submodule.coe_smul, smul_eq_mul, lastBimod_apply, lastBimod_apply, coe_lastElt,
      coe_lastElt, Submodule.coe_smul, smul_eq_mul, lastAppend]
    simp only [map_mul, mul_assoc])

variable {N : Type*} [AddCommGroup N] [Module k N]
  [Module (TensorKLR Q (ν₀ + ({i} : Multiset I)) (ν₀' + ({i} : Multiset I))) N]
  [IsScalarTower k (TensorKLR Q (ν₀ + ({i} : Multiset I)) (ν₀' + ({i} : Multiset I))) N]

local notation "Φ" => indAppend (Q := Q) (ν := ν₀ + Si i) (ν₀' := ν₀') (i := i) (N := N)
local notation "L" => Algebra.lsmul k k (Ind Q (ν₀ + Si i) (ν₀' + Si i) N)

theorem lastAppend_smul_mem_range (a : KLRAlgebra k Q (ν₀ + (ν₀' + Si i)))
    {y : Ind Q (ν₀ + Si i) (ν₀' + Si i) N} (hy : y ∈ LinearMap.range Φ) :
    lastAppend a • y ∈ LinearMap.range Φ := by
  obtain ⟨x, rfl⟩ := hy
  exact ⟨castKLR Q (lastQuad_h₁ ν₀ ν₀' i) a • x, indAppend_smul _ x⟩

/-- `ι(a ⊗ 1_i)` on `Ind_{ν,ν'} N / Φ(Ind_{ν,ν₀'} ₂N)`. -/
noncomputable def lastQuotSMul (a : KLRAlgebra k Q (ν₀ + (ν₀' + Si i))) :
    (Ind Q (ν₀ + Si i) (ν₀' + Si i) N ⧸ LinearMap.range Φ) →ₗ[k]
      (Ind Q (ν₀ + Si i) (ν₀' + Si i) N ⧸ LinearMap.range Φ) :=
  (LinearMap.range Φ).mapQ (LinearMap.range Φ) (L (lastAppend a))
    (fun _ hy => lastAppend_smul_mem_range a hy)

theorem lastQuotSMul_mk (a : KLRAlgebra k Q (ν₀ + (ν₀' + Si i)))
    (y : Ind Q (ν₀ + Si i) (ν₀' + Si i) N) :
    lastQuotSMul a (Submodule.Quotient.mk y : _ ⧸ LinearMap.range Φ) =
      Submodule.Quotient.mk (lastAppend a • y) := rfl

/-- **`Ψ` intertwines `a` with `ι(a ⊗ 1_i)`.** -/
theorem indLast_smul (a : KLRAlgebra k Q (ν₀ + (ν₀' + Si i)))
    (x : Ind Q ν₀ (ν₀' + Si i) (ResAppendL Q ν₀ ν₀' i N)) :
    indLast (a • x) = lastQuotSMul a (indLast x) := by
  induction x using BalancedTensor.induction_on with
  | zero => rw [smul_zero, map_zero, map_zero]
  | tmul r n =>
    rw [BalancedTensor.smul_tmul', indLast_tmul, indLast_tmul, lastQuotSMul_mk, lastBimod_smul,
      BalancedTensor.smul_tmul']
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, map_add]

variable (hsym : KLRSymm Q)

include hsym in
theorem lastIdem_smul_mem_range_indLast (y : Ind Q (ν₀ + Si i) (ν₀' + Si i) N) :
    (Submodule.Quotient.mk (lastIdem Q ν₀ ν₀' i • y) : _ ⧸ LinearMap.range Φ) ∈
      LinearMap.range (indLast (Q := Q) (ν₀ := ν₀) (ν₀' := ν₀') (i := i) (N := N)) := by
  obtain ⟨x, hx⟩ := exists_indLast_eq hsym (y := lastIdem Q ν₀ ν₀' i • y)
    (by rw [smul_smul, lastIdem_mul_self])
  exact ⟨x, hx⟩

/-- **The surjection `π : Ind_{ν,ν'} N → Ind_{ν₀,ν'} ₁N`**, `y ↦ Ψ⁻¹[1_{-,i} y]`. -/
noncomputable def lastProj :
    Ind Q (ν₀ + Si i) (ν₀' + Si i) N →ₗ[k] Ind Q ν₀ (ν₀' + Si i) (ResAppendL Q ν₀ ν₀' i N) :=
  (LinearEquiv.ofInjective _ (indLast_injective (N := N) hsym)).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict _ ((LinearMap.range Φ).mkQ ∘ₗ L (lastIdem Q ν₀ ν₀' i))
      (lastIdem_smul_mem_range_indLast hsym)

theorem indLast_lastProj (y : Ind Q (ν₀ + Si i) (ν₀' + Si i) N) :
    indLast (lastProj hsym y) = Submodule.Quotient.mk (lastIdem Q ν₀ ν₀' i • y) := by
  have h := (LinearEquiv.ofInjective _ (indLast_injective (N := N) hsym)).apply_symm_apply
    ⟨_, lastIdem_smul_mem_range_indLast hsym y⟩
  rw [Subtype.ext_iff, LinearEquiv.ofInjective_apply] at h
  exact h

theorem lastProj_eq_iff {y : Ind Q (ν₀ + Si i) (ν₀' + Si i) N}
    {x : Ind Q ν₀ (ν₀' + Si i) (ResAppendL Q ν₀ ν₀' i N)} :
    lastProj hsym y = x ↔ indLast x = Submodule.Quotient.mk (lastIdem Q ν₀ ν₀' i • y) := by
  rw [← indLast_lastProj hsym]
  exact ⟨fun h => h ▸ rfl, fun h => (indLast_injective hsym h).symm⟩

theorem lastProj_eq_zero_iff (y : Ind Q (ν₀ + Si i) (ν₀' + Si i) N) :
    lastProj hsym y = 0 ↔ lastIdem Q ν₀ ν₀' i • y ∈ LinearMap.range Φ := by
  rw [lastProj_eq_iff, map_zero, eq_comm, Submodule.Quotient.mk_eq_zero]

/-- **`π` intertwines `ι(a ⊗ 1_i)` with `a`.** -/
theorem lastProj_smul (a : KLRAlgebra k Q (ν₀ + (ν₀' + Si i)))
    (y : Ind Q (ν₀ + Si i) (ν₀' + Si i) N) :
    lastProj hsym (lastAppend a • y) = a • lastProj hsym y := by
  rw [lastProj_eq_iff, indLast_smul, indLast_lastProj, lastQuotSMul_mk, smul_smul, smul_smul,
    lastIdem_mul_lastAppend, lastAppend_mul_lastIdem]

theorem lastProj_surjective :
    Function.Surjective (lastProj hsym : Ind Q (ν₀ + Si i) (ν₀' + Si i) N →ₗ[k] _) := by
  intro x
  obtain ⟨y, hy, hxy⟩ := exists_lastIdem_smul_indLast_eq x
  exact ⟨y, (lastProj_eq_iff hsym).2 (by rw [hy, hxy])⟩

/-! ### Descent to idempotent quotients -/

-- `{i}` rather than the `Si` notation: notation is not hygienic inside `variable` binders.
variable {P : KLRAlgebra k Q (ν₀ + {i} + (ν₀' + {i}))} {P₂ : KLRAlgebra k Q (ν₀ + {i} + ν₀')}
  (hP : IsIdempotentElem P) (hc : Commute P (lastIdem Q ν₀ ν₀' i))
  (hP₂ : P * lastIdem Q ν₀ ν₀' i =
    castKLR Q (add_assoc (ν₀ + {i}) ν₀' {i}) (appendR Q (ν₀ + {i} + ν₀') i P₂))

/-- `P₂` transported to `R(ν₀ + ν')`. -/
noncomputable abbrev lastIdemOne (P₂ : KLRAlgebra k Q (ν₀ + Si i + ν₀')) :
    KLRAlgebra k Q (ν₀ + (ν₀' + Si i)) :=
  castKLR Q (lastQuad_h₁ ν₀ ν₀' i).symm P₂

include hP₂ in
theorem lastAppend_lastIdemOne : lastAppend (lastIdemOne P₂) = P * lastIdem Q ν₀ ν₀' i := by
  rw [lastAppend, lastIdemOne, castKLR_castAlg_symm, hP₂]

include hP₂ in
theorem indAppend_smul_lastIdemTwo
    (x : Ind Q (ν₀ + Si i) ν₀' (ResRight Q (ν₀ + Si i) ν₀' i N)) :
    Φ (P₂ • x) = (L P * L (lastIdem Q ν₀ ν₀' i)) (Φ x) := by
  simp only [indAppend_smul, Module.End.mul_apply, Algebra.lsmul_coe, smul_smul, hP₂]

omit [IsScalarTower k (TensorKLR Q (ν₀ + {i}) (ν₀' + {i})) N] in
include hP hc in
theorem isIdempotentElem_lsmul_mul :
    IsIdempotentElem (L P * L (lastIdem Q ν₀ ν₀' i)) := by
  rw [← map_mul]
  exact (IsIdempotentElem.mul_of_commute hc hP lastIdem_mul_self).map _

include hP₂ in
theorem lastProj_smul_lastIdemOne (y : Ind Q (ν₀ + Si i) (ν₀' + Si i) N) :
    lastProj hsym ((L P * L (lastIdem Q ν₀ ν₀' i)) y) = lastIdemOne P₂ • lastProj hsym y := by
  simp only [← lastProj_smul, lastAppend_lastIdemOne hP₂, Module.End.mul_apply,
    Algebra.lsmul_coe, smul_smul]

local notation "Lt" => Algebra.lsmul k k (Ind Q (ν₀ + Si i) ν₀' (ResRight Q (ν₀ + Si i) ν₀' i N))
local notation "Lo" => Algebra.lsmul k k (Ind Q ν₀ (ν₀' + Si i) (ResAppendL Q ν₀ ν₀' i N))

/-- `Φ : Ind_{ν,ν₀'} ₂N / ker P₂ → Ind_{ν,ν'} N / ker (P e)`. -/
noncomputable abbrev lastDescendTwo :=
  descend (Lt P₂) (L P * L (lastIdem Q ν₀ ν₀' i)) Φ (indAppend_smul_lastIdemTwo hP₂)

/-- `π : Ind_{ν,ν'} N / ker (P e) → Ind_{ν₀,ν'} ₁N / ker P₁`. -/
noncomputable abbrev lastDescendOne :=
  descend (L P * L (lastIdem Q ν₀ ν₀' i)) (Lo (lastIdemOne P₂)) (lastProj hsym)
    (lastProj_smul_lastIdemOne hsym hP₂)

include hsym in
/-- **The submodule of the last-strand sequence**: `Φ` descends to an injection. -/
theorem lastDescend_injective : Function.Injective (lastDescendTwo (N := N) hP₂) :=
  descend_injective _ _ _ _ (indAppend_injective hsym)

include hP hc in
/-- **The last-strand sequence is exact in the middle.** -/
theorem lastDescend_exact :
    Function.Exact (lastDescendTwo (N := N) hP₂) (lastDescendOne (N := N) hsym hP₂) := by
  refine exact_descend _ _ _ _ _ _ _ (isIdempotentElem_lsmul_mul hP hc) fun y => ?_
  simp only [lastProj_eq_zero_iff, Module.End.mul_apply, Algebra.lsmul_coe, smul_smul]
  rw [← mul_assoc, ← hc.eq, mul_assoc, lastIdem_mul_self, hc.eq]

/-- **The quotient of the last-strand sequence**: `π` descends to a surjection. -/
theorem lastDescend_surjective : Function.Surjective (lastDescendOne (N := N) hsym hP₂) :=
  descend_surjective _ _ _ _ (lastProj_surjective hsym)

end Descent

end KLRAlgebra

end Categorification.KLR

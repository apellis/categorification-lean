/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.IndLastStrandDescent

/-!
# Naturality of the last-strand maps of induced modules

Khovanov–Lauda I (arXiv:0803.4121v2), Proposition 2.18, as used in B. Webster, *Knot invariants
and higher representation theory*, arXiv:1309.3796v3, proof of Proposition 5.5. For
`ν = ν₀ + i`, `ν' = ν₀' + i` and a map `f : N → N'` of modules over `R(ν) ⊗ R(ν')`, the maps
`Φ : Ind_{ν,ν₀'} ₂N → Ind_{ν,ν'} N`, `Ψ : Ind_{ν₀,ν'} ₁N → Ind_{ν,ν'} N / im Φ` and
`π : Ind_{ν,ν'} N → Ind_{ν₀,ν'} ₁N` commute with the maps induced by `f`
(`indAppend_mapRight`, `indLast_mapRight`, `lastProj_mapRight`).
-/

universe w

namespace Categorification.KLR

open MulOpposite
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}

local notation "Si" i:max => (Singleton.singleton i : Multiset I)

namespace KLRAlgebra

variable {ν₀ ν₀' : Multiset I} {i : I}
  {N N' : Type w} [AddCommGroup N] [Module k N]
  [Module (TensorKLR Q (ν₀ + ({i} : Multiset I)) (ν₀' + ({i} : Multiset I))) N]
  [IsScalarTower k (TensorKLR Q (ν₀ + ({i} : Multiset I)) (ν₀' + ({i} : Multiset I))) N]
  [AddCommGroup N'] [Module k N']
  [Module (TensorKLR Q (ν₀ + ({i} : Multiset I)) (ν₀' + ({i} : Multiset I))) N']
  [IsScalarTower k (TensorKLR Q (ν₀ + ({i} : Multiset I)) (ν₀' + ({i} : Multiset I))) N']
  (f : N →ₗ[TensorKLR Q (ν₀ + ({i} : Multiset I)) (ν₀' + ({i} : Multiset I))] N')

/-- **`Φ` is natural.** -/
theorem indAppend_mapRight (v : Ind Q (ν₀ + Si i) ν₀' (ResRight Q (ν₀ + Si i) ν₀' i N)) :
    BalancedTensor.mapRight f (indAppend v) =
      indAppend (BalancedTensor.mapRight
        (InductionAlong.Res.map (φ := tensorAppendHom Q (ν₀ + Si i) ν₀' i) f) v) := by
  induction v using BalancedTensor.induction_on with
  | zero => simp only [map_zero]
  | tmul r n => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem mapRight_mem_range_indAppend {y : Ind Q (ν₀ + Si i) (ν₀' + Si i) N}
    (hy : y ∈ LinearMap.range (indAppend (Q := Q) (ν := ν₀ + Si i) (ν₀' := ν₀') (i := i)
      (N := N))) :
    BalancedTensor.mapRight f y ∈ LinearMap.range (indAppend (Q := Q) (ν := ν₀ + Si i)
      (ν₀' := ν₀') (i := i) (N := N')) := by
  obtain ⟨v, rfl⟩ := hy
  exact ⟨_, (indAppend_mapRight f v).symm⟩

/-- The map of `Ind_{ν,ν'} N / im Φ` induced by `f`. -/
noncomputable def lastQuotMap :
    (Ind Q (ν₀ + Si i) (ν₀' + Si i) N ⧸
        LinearMap.range (indAppend (Q := Q) (ν := ν₀ + Si i) (ν₀' := ν₀') (i := i) (N := N))) →ₗ[k]
      (Ind Q (ν₀ + Si i) (ν₀' + Si i) N' ⧸
        LinearMap.range (indAppend (Q := Q) (ν := ν₀ + Si i) (ν₀' := ν₀') (i := i) (N := N'))) :=
  Submodule.mapQ _ _ ((BalancedTensor.mapRight f).restrictScalars k)
    fun _ hy => mapRight_mem_range_indAppend f hy

theorem lastQuotMap_mk (y : Ind Q (ν₀ + Si i) (ν₀' + Si i) N) :
    lastQuotMap f (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (BalancedTensor.mapRight f y) := rfl

/-- **`Ψ` is natural.** -/
theorem indLast_mapRight (u : Ind Q ν₀ (ν₀' + Si i) (ResAppendL Q ν₀ ν₀' i N)) :
    indLast (BalancedTensor.mapRight
        (InductionAlong.Res.map (φ := tensorAppendLHom Q ν₀ ν₀' i) f) u) =
      lastQuotMap f (indLast u) := by
  induction u using BalancedTensor.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul r n => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

variable (hsym : KLRSymm Q)

/-- **`π` is natural.** -/
theorem lastProj_mapRight (y : Ind Q (ν₀ + Si i) (ν₀' + Si i) N) :
    lastProj hsym (BalancedTensor.mapRight f y) =
      BalancedTensor.mapRight (InductionAlong.Res.map (φ := tensorAppendLHom Q ν₀ ν₀' i) f)
        (lastProj hsym y) := by
  rw [lastProj_eq_iff, indLast_mapRight, indLast_lastProj, lastQuotMap_mk, map_smul]

end KLRAlgebra

end Categorification.KLR

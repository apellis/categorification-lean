/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicQuantumCommutator

/-!
# Toral operators on the cyclotomic projective Grothendieck group

On the content-β summand, a coweight y acts by the Laurent monomial of
exponent ⟨y, Λ − β⟩. Induction and restriction change this exponent by
the pairing with a simple root (Kang–Kashiwara, §6).
-/

noncomputable section
namespace Categorification.KLR.CycKLR
open KLRAlgebra KLRAlgebra.AbsentColour Categorification.Graded QuantumGroup QuantumGroup.UDot
local notation "LP" => LaurentPolynomial ℤ
local notation "T" => LaurentPolynomial.T (R := ℤ)

variable {k I : Type*} [Field k] [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k}
    (G : GradingDatum Q) (Λ : I → ℕ)
    {C : CartanDatum I} {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (RD : WeightDatum C X Y) (highest : X)

local notation "P" => projectiveK0 G Λ
local notation "ι" => DirectSum.lof LP (Multiset I) (fun ν => K0 (grade G Λ ν))
local notation "wt" => fun (ν : Multiset I) => highest - Multiset.sum (Multiset.map RD.iX ν)

/-- The integral torus on the graded projective Grothendieck group. -/
def toral (y : Y) : Module.End LP P :=
  DirectSum.toModule LP _ _ fun ν => T (RD.pair y (wt ν)) • ι ν

@[simp] theorem toral_lof (y : Y) (ν : Multiset I) (x : K0 (grade G Λ ν)) :
    toral G Λ RD highest y (ι ν x) = T (RD.pair y (wt ν)) • ι ν x := by
  rw [toral, DirectSum.toModule_lof, LinearMap.smul_apply]

/-- The additive coweight lattice acts multiplicatively. -/
def torus : Multiplicative Y →* Module.End LP P where
  toFun y := toral G Λ RD highest y.toAdd
  map_one' := by
    apply DirectSum.linearMap_ext
    intro ν
    apply LinearMap.ext
    intro x
    change toral G Λ RD highest 0 (ι ν x) = ι ν x
    simp
  map_mul' y z := by
    apply DirectSum.linearMap_ext
    intro ν
    apply LinearMap.ext
    intro x
    change toral G Λ RD highest (y.toAdd + z.toAdd) (ι ν x) =
      toral G Λ RD highest y.toAdd (toral G Λ RD highest z.toAdd (ι ν x))
    simp only [toral_lof, map_add, AddMonoidHom.add_apply, map_smul, smul_smul,
      ← LaurentPolynomial.T_add]
    rw [add_comm]

local notation "K" => toral G Λ RD highest

/-- Toral conjugation of unshifted projective induction. -/
theorem toral_lower (y : Y) (i : I) :
    K y * lower G Λ i = T (-(RD.pair y (RD.iX i))) • (lower G Λ i * K y) := by
  apply DirectSum.linearMap_ext
  intro ν
  apply LinearMap.ext
  intro x
  change K y (lower G Λ i (ι ν x)) = T _ • lower G Λ i (K y (ι ν x))
  simp only [lower_lof, toral_lof, map_smul, smul_smul, ← LaurentPolynomial.T_add,
    Multiset.map_add, Multiset.map_singleton, Multiset.sum_add, Multiset.sum_singleton,
    map_sub, map_add]
  congr 2
  abel

variable (hsym : KLRSymm Q)
    (hQ : ∀ s t : I, s ≠ t → ∃ c : k, IsUnit c ∧ (polyInY (Q s t)).leadingCoeff = Polynomial.C c)

local notation "E" => fun i => raise G Λ i hsym hQ C

/-- Toral conjugation of normalized projective restriction. -/
theorem toral_raise (y : Y) (i : I) :
    K y * E i = T (RD.pair y (RD.iX i)) • (E i * K y) := by
  apply DirectSum.linearMap_ext
  intro ν
  apply LinearMap.ext
  intro x
  change K y (E i (ι ν x)) = T _ • E i (K y (ι ν x))
  by_cases hi : i ∈ ν
  · obtain ⟨μ, hμ⟩ := Multiset.exists_cons_of_mem hi
    rw [← Multiset.singleton_add] at hμ
    subst ν
    simp only [raise_lof, toral_lof, map_smul, smul_smul, ← LaurentPolynomial.T_add,
      Multiset.map_add, Multiset.map_singleton, Multiset.sum_add, Multiset.sum_singleton,
      map_sub, map_add]
    congr 2
    abel
  · simp [toral_lof, raise_lof_of_notMem _ _ _ _ _ _ _ hi]

end Categorification.KLR.CycKLR

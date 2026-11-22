/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Crystal.Thm317
import Categorification.KLR.BasisTheoremGeneral

/-!
# Simple KLR modules with proportional characters

Two consequences of Khovanov–Lauda, arXiv:0803.4121v2, Theorem 3.17 (`thm_3_17_ungraded`):

* `KLRAlgebra.nonempty_equiv_of_dimCh_proportional`: finite-dimensional simple `R(ν)`-modules
  with nilpotent dots whose characters are proportional (`m · ch L = n · ch L'`, `m ≠ 0`) are
  isomorphic;
* `KLR.exists_factor_of_klrSymm`: symmetric KLR data with nonzero `Q_{ab}` (`a ≠ b`), e.g. the
  data of a Rouquier polynomial, admit the factorization `Q_{ab}(u, v) = P_{ba}(u, v) P_{ab}(v, u)`
  required by the basis theorem and by Theorem 3.17.

These are inputs for Webster, arXiv:1309.3796v2, Proposition 5.11.
-/

set_option backward.isDefEq.respectTransparency false

namespace Categorification.KLR

universe u

open MvPolynomial

variable {I : Type*} [DecidableEq I]

omit [DecidableEq I] in
/-- Symmetric KLR data with nonzero off-diagonal polynomials factor as
`Q_{ab} = P_{ba} · P_{ab}(v, u)` with nonzero `P`: order `I` by a well-ordering and put `P_{ab} = 1`
for `a < b` and `P_{ab} = Q_{ba}` otherwise. -/
theorem exists_factor_of_klrSymm {K : Type*} [CommRing K] [Nontrivial K]
    {Q : I → I → MvPolynomial (Fin 2) K} (hs : KLRSymm Q) (h0 : ∀ a b, a ≠ b → Q a b ≠ 0) :
    ∃ P : I → I → MvPolynomial (Fin 2) K,
      (∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b)) ∧ ∀ a b, a ≠ b → P a b ≠ 0 := by
  classical
  let r : I → I → Prop := WellOrderingRel
  refine ⟨fun a b => if r a b then 1 else Q b a, fun a b hab => ?_, fun a b hab => ?_⟩
  · rcases trichotomous_of r a b with h | h | h
    · have : ¬ r b a := asymm h
      simp only [h, this, ite_true, ite_false, map_one, mul_one]
    · exact absurd h hab
    · have : ¬ r a b := asymm h
      simp only [h, this, ite_true, ite_false, one_mul]
      exact hs b a hab.symm
  · dsimp only
    split_ifs
    · exact one_ne_zero
    · exact h0 b a hab.symm

namespace KLRAlgebra

variable {K : Type*} [Field K] {Q : I → I → MvPolynomial (Fin 2) K}
  {P : I → I → MvPolynomial (Fin 2) K}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)

include hPQ hP in
/-- **Proportional characters** (from KL I, Theorem 3.17): finite-dimensional simple
`R(ν)`-modules with nilpotent dots and proportional characters `m · ch L = n · ch L'`, `m ≠ 0`,
are isomorphic. -/
theorem nonempty_equiv_of_dimCh_proportional {ν : Multiset I} {L L' : Type u}
    [AddCommGroup L] [Module K L] [Module (KLRAlgebra K Q ν) L]
    [IsScalarTower K (KLRAlgebra K Q ν) L] [FiniteDimensional K L]
    [IsSimpleModule (KLRAlgebra K Q ν) L]
    [AddCommGroup L'] [Module K L'] [Module (KLRAlgebra K Q ν) L']
    [IsScalarTower K (KLRAlgebra K Q ν) L'] [FiniteDimensional K L']
    [IsSimpleModule (KLRAlgebra K Q ν) L']
    (hnil : ∀ a, SmulNilpotent (x a : KLRAlgebra K Q ν) L)
    (hnil' : ∀ a, SmulNilpotent (x a : KLRAlgebra K Q ν) L')
    {m n : ℕ} (hm : m ≠ 0) (h : ∀ s, m * dimCh Q ν L s = n * dimCh Q ν L' s) :
    Nonempty (L ≃ₗ[KLRAlgebra K Q ν] L') := by
  by_contra hne
  let F : Bool → Type u := fun b => cond b L L'
  let i₁ : ∀ b, AddCommGroup (F b) := fun b => match b with
    | true => (inferInstance : AddCommGroup L) | false => (inferInstance : AddCommGroup L')
  let i₂ : ∀ b, Module K (F b) := fun b => match b with
    | true => (inferInstance : Module K L) | false => (inferInstance : Module K L')
  let i₃ : ∀ b, Module (KLRAlgebra K Q ν) (F b) := fun b => match b with
    | true => (inferInstance : Module (KLRAlgebra K Q ν) L)
    | false => (inferInstance : Module (KLRAlgebra K Q ν) L')
  have i₄ : ∀ b, IsScalarTower K (KLRAlgebra K Q ν) (F b) := fun b => match b with
    | true => (inferInstance : IsScalarTower K (KLRAlgebra K Q ν) L)
    | false => (inferInstance : IsScalarTower K (KLRAlgebra K Q ν) L')
  have i₅ : ∀ b, FiniteDimensional K (F b) := fun b => match b with
    | true => (inferInstance : FiniteDimensional K L)
    | false => (inferInstance : FiniteDimensional K L')
  have i₆ : ∀ b, IsSimpleModule (KLRAlgebra K Q ν) (F b) := fun b => match b with
    | true => (inferInstance : IsSimpleModule (KLRAlgebra K Q ν) L)
    | false => (inferInstance : IsSimpleModule (KLRAlgebra K Q ν) L')
  have hli := thm_3_17_ungraded hPQ hP F
    (fun b => match b with | true => hnil | false => hnil')
    (fun b b' hb => match b, b', hb with
      | true, true, _ => rfl
      | false, false, _ => rfl
      | true, false, ⟨φ⟩ => (hne ⟨φ⟩).elim
      | false, true, ⟨φ⟩ => (hne ⟨φ.symm⟩).elim)
  have := Fintype.linearIndependent_iff.mp hli (fun b => cond b (m : ℤ) (-(n : ℤ)))
    (by
      rw [Fintype.sum_bool]
      funext s
      have hs := congrArg (fun z : ℕ => (z : ℤ)) (h s)
      push_cast at hs
      change (m : ℤ) * (dimCh Q ν L s : ℤ) + -(n : ℤ) * (dimCh Q ν L' s : ℤ) = 0
      rw [hs]
      ring) true
  exact hm (by simpa using this)

end KLRAlgebra

end Categorification.KLR

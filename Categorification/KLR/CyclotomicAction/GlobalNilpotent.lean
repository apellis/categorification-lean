/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.Global
import Categorification.KLR.CyclotomicNilpotent
import Categorification.TwoRep.SumInvPointwise

/-!
# Nilpotent dots on cyclotomic weight spaces

J. Brundan, A. Kleshchev, *Blocks of cyclotomic Hecke algebras and Khovanov–Lauda algebras*,
arXiv:0808.2032v3, §2.2, Lemma 2.1, on weight spaces. The weight space of the cyclotomic family
at `x` is the product of the module categories of the blocks `R^Λ(β)` of weight `x`, so the dot
`globalDot` on `E_i` is nilpotent with one exponent for all blocks only when there are
finitely many of them. This file treats the case of at most one block of each weight (a
weight datum graded by the root lattice), where the dot on `E_i` is nilpotent for the undeformed
cyclotomic polynomials `a_j = y^{Λ_j}`.

## Main results

* `TwoRep.blockSumMap_comp`, `TwoRep.powComp_blockSumMap`: block sums of transformations
  compose blockwise.
* `CyclotomicAction.globalDot_powComp_eq_zero`: if each weight has at most one block, some power
  of `globalDot` vanishes.
-/

open CategoryTheory CategoryTheory.Limits

namespace Categorification

namespace TwoRep

universe u₁ u₂ v₁ v₂ w₁ w₂

variable {A : Type w₁} {Dd : Type w₂} (s : A → Dd)
  {C : A → Type u₁} [∀ a, Category.{v₁} (C a)] {D : Dd → Type u₂} [∀ d, Category.{v₂} (D d)]
  [∀ d, Finite {a // s a = d}] [∀ d, Preadditive (D d)] [∀ d, HasFiniteBiproducts (D d)]

theorem blockSumMap_comp {L L' L'' : ∀ (a : A) (d : Dd), s a = d → C a ⥤ D d}
    (α : ∀ a d h, L a d h ⟶ L' a d h) (α' : ∀ a d h, L' a d h ⟶ L'' a d h) :
    blockSumMap s α ≫ blockSumMap s α' = blockSumMap s fun a d h => α a d h ≫ α' a d h := by
  ext M : 2
  funext d
  refine biproduct.hom_ext' _ _ fun p => ?_
  change blockι s L M p ≫ (blockSumMap s α).app M d ≫ (blockSumMap s α').app M d =
    blockι s L M p ≫ (blockSumMap s fun a d h => α a d h ≫ α' a d h).app M d
  rw [← Category.assoc, blockι_blockSumMap, Category.assoc, blockι_blockSumMap,
    blockι_blockSumMap]
  simp

theorem blockSumMap_id {L : ∀ (a : A) (d : Dd), s a = d → C a ⥤ D d} :
    blockSumMap s (fun a d h => 𝟙 (L a d h)) = 𝟙 _ := by
  ext M : 2
  funext d
  refine biproduct.hom_ext' _ _ fun p => ?_
  change blockι s L M p ≫ (blockSumMap s fun a d h => 𝟙 (L a d h)).app M d = blockι s L M p ≫ 𝟙 _
  rw [blockι_blockSumMap]
  simp

theorem powComp_blockSumMap {L : ∀ (a : A) (d : Dd), s a = d → C a ⥤ D d}
    (α : ∀ a d h, L a d h ⟶ L a d h) (n : ℕ) :
    powComp (blockSumMap s α) n = blockSumMap s fun a d h => powComp (α a d h) n := by
  induction n with
  | zero => exact (blockSumMap_id s).symm
  | succ n ih => rw [powComp_succ, ih, blockSumMap_comp]; rfl

theorem blockSumMap_zero [∀ a, Preadditive (C a)] {L L' : ∀ (a : A) (d : Dd), s a = d → C a ⥤ D d}
    [∀ a d h, (L' a d h).PreservesZeroMorphisms] :
    blockSumMap s (fun a d h => (0 : L a d h ⟶ L' a d h)) = 0 := by
  ext M : 2
  funext d
  refine biproduct.hom_ext' _ _ fun p => ?_
  change blockι s L M p ≫ (blockSumMap s fun a d h => (0 : L a d h ⟶ L' a d h)).app M d =
    blockι s L M p ≫ 0
  rw [blockι_blockSumMap]
  simp

omit [∀ d, Finite {a // s a = d}] [∀ d, Preadditive (D d)] [∀ d, HasFiniteBiproducts (D d)] in
theorem powComp_eq_endPow {E : Type*} [Category E] {Z : E} (f : End Z) :
    ∀ n : ℕ, powComp f n = f ^ n
  | 0 => rfl
  | n + 1 => by rw [powComp_succ, powComp_eq_endPow f n, pow_succ']; rfl

end TwoRep

namespace KLR.CyclotomicAction

open TwoRep Polynomial

universe u v w u₁

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k}
  {C : QuantumGroup.CartanDatum I} {Xw Yw : Type u₁} [AddCommGroup Xw] [AddCommGroup Yw]
  (RD : QuantumGroup.UDot.WeightDatum C Xw Yw) (Λ : Xw)

/-- **The dot on `E_i` is nilpotent on weight spaces with at most one block** (Brundan–Kleshchev,
arXiv:0808.2032v3, Lemma 2.1): for `a_j = y^{Λ'_j}` and `Q_{ij}(0, v)` a unit multiple of a
power of `v`, some power of `globalDot` vanishes, when each weight has at most one block. -/
theorem globalDot_powComp_eq_zero
    (hQ0 : ∀ i j : I, i ≠ j → ∃ (c : k) (d : ℕ), IsUnit c ∧
      MvPolynomial.aeval (![0, MvPolynomial.X 1] : Fin 2 → MvPolynomial (Fin 2) k) (Q i j) =
        MvPolynomial.C c * MvPolynomial.X 1 ^ d)
    (Λ' : I → ℕ) (hsub : ∀ x, Subsingleton (WeightBlocks RD Λ x))
    (i : I) {x y : Xw} (h : x + RD.iX i = y) :
    ∃ N : ℕ, powComp (globalDot.{u, v, w} Q (fun j => X ^ Λ' j) RD Λ i h) N = 0 := by
  suffices key : ∃ N : ℕ, powComp (blockSumMap (blockSucc RD Λ i h)
      fun _ _ hβ => dot.{u, v, w} Q (fun j => X ^ Λ' j) i (blockSucc_eq RD Λ i hβ)) N = 0 by
    obtain ⟨N, hN⟩ := key
    exact ⟨N, ObjectProperty.hom_ext _ ((LinearCat.powComp_hom _ N).trans hN)⟩
  by_cases hx : Nonempty (WeightBlocks RD Λ x)
  · obtain ⟨β⟩ := hx
    obtain ⟨N, hN⟩ := dot_pow_eq_zero.{u, v, w} hQ0 Λ' i (blockSucc_eq RD Λ i
      (rfl : blockSucc RD Λ i h β = _))
    refine ⟨N, ?_⟩
    rw [powComp_blockSumMap]
    refine Eq.trans ?_ (blockSumMap_zero (blockSucc RD Λ i h))
    congr 1
    funext β' δ hβ
    obtain rfl : β' = β := Subsingleton.elim _ _
    subst hβ
    rw [powComp_eq_endPow (End.of _)]
    exact hN
  · refine ⟨1, ?_⟩
    rw [powComp_blockSumMap]
    refine Eq.trans ?_ (blockSumMap_zero (blockSucc RD Λ i h))
    congr 1
    funext β'
    exact (hx ⟨β'⟩).elim

end KLR.CyclotomicAction

end Categorification

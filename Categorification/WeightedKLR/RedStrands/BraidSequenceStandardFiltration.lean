/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidSequenceDimension
import Categorification.WeightedKLR.RedStrands.BraidFiltrationDimension
import Categorification.WeightedKLR.RedStrands.GradedBraidStandardFiltration
import Categorification.WeightedKLR.RedStrands.RowFigureFiveLoading

set_option backward.isDefEq.respectTransparency false

/-!
# Standard filtrations of the braid of a sequence projective

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §6.1, proof
of Lemma 6.11, step `p_n → f_n`. Let `D = 𝔅_w (e(t) T^λ)`. Webster filters `D` by the images
`D_{≤φ}` of the diagrams `y_φ`, for `φ` in the parameter set `Φ` of Proposition 5.20 with its
blocks permuted by `w`, and obtains surjections `S_φ ↠ D_{≤φ} / D_{<φ}` from the standard
modules. Since `𝔅_w` categorifies the permutation of the tensor factors at `q = 1`,
`dim D = Σ_φ dim S_φ`, so all these surjections are isomorphisms.

Here `Φ` is `loadingMono` of `t` (`finrank_braidF_rightSequence`), and `S_φ`, for the monomial
`φ = (d, u)`, is the loading standard at the row loading of `u ∘ w` (`rowSeq`). This file
supplies the dimension bookkeeping (dimensions through the scalars of an algebra, of the row
standards and of the loading monomials); the filtration itself is assembled in
`BraidColumnCutFiltration` (`hasCornerStandardFiltration_braidF_rightSequence`).
-/

noncomputable section

/-! ### Dimensions through the scalars of an algebra -/

namespace Categorification.ModuleFiltration

open scoped ModuleCat.Algebra

variable {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A] {Y : ModuleCat A}
  {M : Type*} [AddCommGroup M] [Module k M]

/-- An additive identification of an `A`-module, with its `k`-module structure through `A`,
with a `k`-module, compatible with the scalars, as a `k`-linear equivalence. -/
def algebraModuleEquiv (e : Y ≃+ M) (h : ∀ (c : k) (y : Y), e (algebraMap k A c • y) = c • e y) :
    Y ≃ₗ[k] M :=
  { e with map_smul' := fun c y => h c y }

theorem finrank_algebraModule (e : Y ≃+ M)
    (h : ∀ (c : k) (y : Y), e (algebraMap k A c • y) = c • e y) :
    Module.finrank k Y = Module.finrank k M :=
  (algebraModuleEquiv e h).finrank_eq

theorem finiteDimensional_algebraModule (e : Y ≃+ M)
    (h : ∀ (c : k) (y : Y), e (algebraMap k A c • y) = c • e y) [FiniteDimensional k M] :
    FiniteDimensional k Y :=
  Module.Finite.equiv (algebraModuleEquiv e h).symm

end Categorification.ModuleFiltration

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}

/-- Scalars act on a loading standard through the corner. -/
theorem algebraMap_smul_loadingStandard (t : Seq (stendhalWeight ℓ ν)) (κ : List (Fin ℓ))
    (c : k) (x : ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) t κ) :
    algebraMap k (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ)ᵐᵒᵖ c • x = c • x := by
  induction x using Submodule.Quotient.induction_on with
  | H y =>
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul]
    congr 1
    apply Subtype.ext
    rw [violCorner_smul_val]
    have hy := (mem_violCorner_iff (s := t) (κ := κ)).1 y.2
    rw [MulOpposite.algebraMap_apply, MulOpposite.unop_op, Submodule.coe_smul_of_tower]
    change (y : ViolQuotient k Q Λ ν) * (algebraMap k _ c * violMk k Q Λ ν (redProj k Q Λ ν κ)) = _
    rw [← mul_assoc, ← Algebra.commutes c (y : ViolQuotient k Q Λ ν), mul_assoc, hy.2,
      ← Algebra.smul_def]

end Categorification.Stendhal.BraidedStendhalAlgebra

namespace Categorification.Stendhal.FirstWeight

open KLR KLRAlgebra KLGamma Categorification.Graded QuantumGroup QuantumGroup.UDot
open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF ModuleFiltration
open BraidedStendhalAlgebra
open scoped RatFunc

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
local notation "LP" => LaurentPolynomial ℤ
local notation "𝕂" => RatFunc ℚ

/-! ### Row loadings of a given black content -/

section Row

variable {I : Type} [DecidableEq I]

omit [DecidableEq I] in
/-- A row loading is not violated: it starts with a red strand. -/
theorem not_isViolated_rowLoading : ∀ (n : ℕ) (u : Fin n → List I),
    ¬ IsViolated (rowLoading n u)
  | 0, u => by
    rintro ⟨h, -⟩
    have h0 := ofFn_rowLoading 0 u
    rw [rowWord, List.finRange_zero, List.flatMap_nil, List.ofFn_eq_nil_iff] at h0
    omega
  | n + 1, u => not_isViolated_of_ofFn _ (by
      rw [ofFn_rowLoading, rowWord, List.finRange_succ, List.flatMap_cons, List.cons_append])

omit [DecidableEq I] in
/-- The row loading of `u`, as a non-violated loading of the identity red order of black content
`ν = blockContent u`. -/
def rowSeq {ℓ : ℕ} {ν : Multiset I} (u : Fin ℓ → List I) (hν : blockContent u = ν) :
    {s : Seq (stendhalWeight ℓ ν) // redWord s = List.finRange ℓ ∧ ¬ IsViolated s} := by
  subst hν
  exact ⟨rowLoading ℓ u, (redWord_eq_finRange_iff _).2 (isRedOrdered_rowLoading ℓ u),
    not_isViolated_rowLoading ℓ u⟩

end Row

variable {I : Type} {k : Type} {Y : Type*} [DecidableEq I] [Field k] [AddCommGroup Y] [Finite I]
    {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)
    {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular) {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ)
    (wt : Fin ℓ → Dom R) (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i))
    [∀ (Ω : Fin ℓ → I →₀ ℕ) (ν : Multiset I), Module.Finite k (TensorProductAlgebra k Q Ω ν)]

omit [Finite I] [∀ (Ω : Fin ℓ → I →₀ ℕ) (ν : Multiset I),
  Module.Finite k (TensorProductAlgebra k Q Ω ν)] in
theorem finrank_rowSeq {ν : Multiset I} (u : Fin ℓ → List I) (hν : blockContent u = ν) :
    Module.finrank k (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) (rowSeq u hν).1
      (List.finRange ℓ)) = Module.finrank k (rightRowStandard C hQ Λ u).carrier := by
  subst hν
  rfl

omit [Finite I] [∀ (Ω : Fin ℓ → I →₀ ℕ) (ν : Multiset I),
  Module.Finite k (TensorProductAlgebra k Q Ω ν)] in
include C hQ in
theorem finiteDimensional_rowSeq {ν : Multiset I} (u : Fin ℓ → List I)
    (hν : blockContent u = ν) :
    FiniteDimensional k (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) (rowSeq u hν).1
      (List.finRange ℓ)) := by
  subst hν
  exact (rightRowStandard C hQ Λ u).finiteDimensional

omit [Finite I] in
theorem blockContent_comp_of_mem_loadingMono (w : Equiv.Perm (Fin ℓ)) {ν : Multiset I}
    (t : Seq (stendhalWeight ℓ ν)) {p : ℤ × (Fin ℓ → List I)}
    (hp : p ∈ loadingMono wt (Seq.toList t)) : blockContent (p.2 ∘ w) = ν := by
  rw [blockContent_comp_equiv, blockContent_of_mem_loadingMono _ wt hp, blackLetters_toList]

end Categorification.Stendhal.FirstWeight

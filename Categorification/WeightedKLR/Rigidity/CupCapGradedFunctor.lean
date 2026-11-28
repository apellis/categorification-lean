/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapGrading
import Categorification.WeightedKLR.Rigidity.CupCapFunctor
import Categorification.Algebra.DiagramWeightForgetDerived

/-!
# The graded coevaluation functor

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3,
Definition 7.18 and the proof of Proposition 7.20.

The grading of `K^{λ⁺}_λ` (`CupCapGrading`) is compatible with the diagram gradings of `T^λ`
acting from the top and of `T^{λ⁺}` acting from the bottom (`capLeftHom_mem_capGrade`,
`capRightHom_mem_capGrade`). With the grading translated by an integer `s`
(`coevGrade s n = capGrade (n + s)`), the derived diagram tensor with `K^{λ⁺}_λ` is a functor
between the derived categories of graded right modules (`gradedCoevaluationFunctor s`), and
forgetting the weights after it is the ungraded coevaluation functor `coevaluationFunctor` after
forgetting the weights (`gradedCoevaluationFunctorForgetIso`).

## Hypotheses and normalization

* `CapBalanced Λc ν₀ G d` (the strands at the maximum have total weight `μ + μ*` for the KL
  degrees) makes (max1) and (max2) homogeneous, and `IsGradedCoeff` says that `L` is a graded
  right module over `T̃^{(μ, μ*)}`. Both hold for Webster's `L_μ` with the KL degrees; Webster
  does not state the grading of `K̃^{λ⁺}_λ` explicitly, and the one used here gives
  `a · cap(s, n, v) · b` the degree `deg a + deg v + deg b`.
* The translation `s` is a parameter. In the proof of Proposition 7.20 the comparison with the
  standardization carries the shift `(2⟨λ, ρ⟩)`; matching it with a concrete `s` (and the sign
  convention of the translation) is left to the comparison itself.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR MulOpposite CategoryTheory DG DirectSum Categorification.Graded
open scoped TensorProduct DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe u v w

variable {I : Type u} [DecidableEq I] {k : Type u} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν ν₀ : Multiset I}
  (G : KLR.GradingDatum Q) (d : I → ℤ) (hd : ∀ i, G.degX i = 2 * d i)
  {L : Type u} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  (ℒ : ℤ → AddSubgroup L) [Decomposition ℒ]
  (hbal : CapBalanced Λc ν₀ G d) (hℒ : IsGradedCoeff (Λc := Λc) (ν₀ := ν₀) G d hd ℒ)

set_option hygiene false in
local notation "Gt" => stendhalGradingDatum Λ G d hd
set_option hygiene false in
local notation "Gb" => stendhalGradingDatum (plusLabels Λ Λc j hj) G d hd
set_option hygiene false in
local notation "At" => TensorProductAlgebra k Q Λ ν
set_option hygiene false in
local notation "Ab" => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
set_option hygiene false in
local notation "Cp" => CapBimodule k Q Λ Λc j hj ν ν₀ L
set_option hygiene false in
local notation "𝒦'" => capGrade Λ j hj ν G d hd ℒ hbal hℒ
set_option hygiene false in
local notation "𝐐" => capQuotProj (Λ := Λ) (j := j) (hj := hj) (ν := ν) G d hd ℒ hbal hℒ

/-! ### The actions of the tensor product algebras are graded -/

theorem capLeftHom_mem_capGrade {i e : ℤ} {a : At} (ha : a ∈ tensorProductGrade (Gt) ν i)
    {x : Cap k Q Λ Λc j hj ν ν₀ L} (hx : x ∈ 𝒦' e) :
    capLeftHom k Q Λ Λc j hj ν ν₀ L a x ∈ 𝒦' (i + e) := by
  obtain ⟨a', ha', rfl⟩ := Submodule.mem_map.1 ha
  have h := envMk_smul_mem_capGrade G d hd ℒ hbal hℒ ha'

    (SetLike.GradedOne.one_mem (A := stendhalGrade (Gb) (ν + ν₀))) hx
  rw [add_zero] at h
  exact h

theorem capRightHom_mem_capGrade {i e : ℤ} {b : Ab}
    (hb : b ∈ tensorProductGrade (Gb) (ν + ν₀) i) {x : Cap k Q Λ Λc j hj ν ν₀ L}
    (hx : x ∈ 𝒦' e) : capRightHom k Q Λ Λc j hj ν ν₀ L (op b) x ∈ 𝒦' (i + e) := by
  obtain ⟨b', hb', rfl⟩ := Submodule.mem_map.1 hb
  have h := envMk_smul_mem_capGrade G d hd ℒ hbal hℒ
    (SetLike.GradedOne.one_mem (A := stendhalGrade (Gt) ν)) hb' hx
  rw [zero_add] at h
  exact h

/-! ### The translated grading of the coefficient bimodule -/

variable (Λ j hj ν) in
/-- The grading of `K^{λ⁺}_λ` translated by `s`, on the coefficient bimodule of the derived
tensor over `T^λ`. -/
def coevGrade (s : ℤ) : ℤ → AddSubgroup (OpBimodule At Cp) := fun n => 𝒦' (n + s)

set_option hygiene false in
local notation "𝒞" => coevGrade Λ j hj ν G d hd ℒ hbal hℒ

theorem isInternal_coevGrade (s : ℤ) : IsInternal (𝒞 s) :=
  isInternal_range_of_projections (fun n => 𝐐 (n + s))
    (fun q q' x => by
      rw [capQuotProj_capQuotProj]
      by_cases h : q = q' <;> simp [h])
    fun x => (iSup_le fun q => le_iSup_of_le (q - s) (by rw [sub_add_cancel]) :
      (⨆ q, (𝐐 q).range) ≤ ⨆ n, (𝐐 (n + s)).range)
        (mem_iSup_capQuotProj_range G d hd ℒ hbal hℒ x)

noncomputable instance coevDecomposition (s : ℤ) : Decomposition (𝒞 s) :=
  (isInternal_coevGrade (Λ := Λ) (j := j) (hj := hj) (ν := ν) G d hd ℒ hbal hℒ
    s).chooseDecomposition _

set_option hygiene false in
local notation "SB" => oppositeGrade (tensorProductGrade (Gb) (ν + ν₀))
set_option hygiene false in
local notation "ST" => oppositeGrade (tensorProductGrade (Gt) ν)

theorem coevGrade_left_mem (s : ℤ) :
    letI := gradedAlgebraInternalGrading (SB)
    ∀ {i e : ℤ} {a : Abᵐᵒᵖ} {x : OpBimodule At Cp}, a ∈ wgrading i → x ∈ 𝒞 s e →
      a • x ∈ 𝒞 s (i + e) := by
  let := gradedAlgebraInternalGrading (SB)
  intro i e a x ha hx
  induction a using MulOpposite.rec' with
  | h b =>
  have h := capRightHom_mem_capGrade G d hd ℒ hbal hℒ (show b ∈ _ from ha) hx
  rw [← add_assoc] at h
  exact h

theorem coevGrade_right_mem (s : ℤ) :
    letI := gradedAlgebraInternalGrading (ST)
    ∀ {i e : ℤ} {b : Atᵐᵒᵖ} {x : OpBimodule At Cp}, b ∈ wgrading i → x ∈ 𝒞 s e →
      op b • x ∈ 𝒞 s (e + i) := by
  let := gradedAlgebraInternalGrading (ST)
  intro i e b x hb hx
  have h := capLeftHom_mem_capGrade G d hd ℒ hbal hℒ (show b.unop ∈ _ from hb) hx
  rw [show i + (e + s) = e + i + s by omega] at h
  exact h

/-! ### The graded coevaluation functor -/

/-- **The graded coevaluation functor** `𝕂^{λ⁺}_λ` (arXiv:1309.3796v3, Definition 7.18): the
derived diagram tensor with `K^{λ⁺}_λ`, graded by `capGrade` translated by `s`, from the derived
category of graded right `T^λ`-modules to that of graded right `T^{λ⁺}`-modules. -/
def gradedCoevaluationFunctor (s : ℤ) :
    letI := gradedAlgebraInternalGrading (SB)
    letI := gradedAlgebraInternalGrading (ST)
    letI := gradedAlgebraBigradedDGRing (SB)
    letI := gradedAlgebraBigradedDGRing (ST)
    [CatModule.HasDerivedCategory.{v,u} (WeightCategory Abᵐᵒᵖ)] →
    [CatModule.HasDerivedCategory.{v,u} (WeightCategory Atᵐᵒᵖ)] →
    CatModule.DerivedCategory.{v,u} (WeightCategory Atᵐᵒᵖ) ⥤
      CatModule.DerivedCategory.{v,u} (WeightCategory Abᵐᵒᵖ) :=
  letI := gradedAlgebraInternalGrading (SB)
  letI := gradedAlgebraInternalGrading (ST)
  letI := gradedAlgebraBigradedDGRing (SB)
  letI := gradedAlgebraBigradedDGRing (ST)
  diagramWeightDerivedTensor (A := Abᵐᵒᵖ) (B := Atᵐᵒᵖ) (𝒞 s)
    (coevGrade_left_mem G d hd ℒ hbal hℒ s) (coevGrade_right_mem G d hd ℒ hbal hℒ s)

/-- **The graded coevaluation functor forgets to the ungraded one**: forgetting the weights
after the graded `𝕂^{λ⁺}_λ` is the coevaluation functor `- ⊗ᴸ_{T^λ} K^{λ⁺}_λ` of
arXiv:1309.3796v3, Definition 7.18, after forgetting the weights. -/
def gradedCoevaluationFunctorForgetIso (s : ℤ) :
    letI := gradedAlgebraInternalGrading (SB)
    letI := gradedAlgebraInternalGrading (ST)
    letI := gradedAlgebraBigradedDGRing (SB)
    letI := gradedAlgebraBigradedDGRing (ST)
    [CatModule.HasDerivedCategory.{v,u} (WeightCategory Abᵐᵒᵖ)] →
    [CatModule.HasDerivedCategory.{v,u} (WeightCategory Atᵐᵒᵖ)] →
    [DG.HasDerivedCategory.{w,u} Abᵐᵒᵖ] → [DG.HasDerivedCategory.{w,u} Atᵐᵒᵖ] →
    (gradedCoevaluationFunctor G d hd ℒ hbal hℒ s ⋙ CatModule.weightForgetDerived Abᵐᵒᵖ ≅
      CatModule.weightForgetDerived Atᵐᵒᵖ ⋙
        coevaluationFunctor.{u, w} k Q Λ Λc j hj ν ν₀ L) := by
  letI := gradedAlgebraInternalGrading (SB)
  letI := gradedAlgebraInternalGrading (ST)
  letI := gradedAlgebraBigradedDGRing (SB)
  letI := gradedAlgebraBigradedDGRing (ST)
  intro _ _ _ _
  exact diagramWeightForgetDerivedIso (A := Abᵐᵒᵖ) (B := Atᵐᵒᵖ) (𝒞 s)
    (coevGrade_left_mem G d hd ℒ hbal hℒ s) (coevGrade_right_mem G d hd ℒ hbal hℒ s)

end Categorification.Stendhal.CupCap

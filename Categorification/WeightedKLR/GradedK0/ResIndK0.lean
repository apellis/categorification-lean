/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.GradedK0.ResIndTensor

/-!
# The graded Mackey formula for `Res ∘ Ind` in graded `K₀`

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, proof of
Theorem 2.19 (after Khovanov–Lauda, arXiv:0803.4121v2, Proposition 2.18). For
`ν₁ + ν₂ = ν' + ν''` and finitely generated graded projective modules `P` over `W_{ν'}` and `P'`
over `W_{ν''}`, the class of `Res_{ν₁;ν₂} Ind_{ν';ν''} (P ⊠ P')` in the graded `K₀` of
`W_{ν₁} ⊗ W_{ν₂}` is a sum over the shuffle types, each term being `q^{s}` times the class of the
middle balanced tensor product `ResIndPiece L ⊗ (P ⊠ P')` with its unshifted grading, where
`s = middleShift G a b c d` is the shift of the subquotient of the Mackey filtration. This is the
graded form of `exists_resK0_indK0_eq_sum`.

## Main definitions and results

* `ResIndPiece.baseGrading`: the unshifted grading of a piece (the grading of the middle balanced
  tensor product); `ResIndPiece.grading` is its shift by `middleShift`.
* `ResIndPiece.tensorGProj`: `ResIndPiece L ⊗_{W_{ν'} ⊗ W_{ν''}} X` with the unshifted grading.
* `exists_resK0_indK0_eq_sum_graded`: the graded Mackey formula in graded `K₀`.
-/

noncomputable section

namespace Categorification.WeightedKLR

open FullChamber GalleryAlgebra Juxtapose MulOpposite Categorification.Graded DirectSum
open scoped TensorProduct

universe u v w

variable {I : Type u} [DecidableEq I] {𝕜 : Type v} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜]

section CommRing

variable {k : Type w} [CommRing k] {Γ : WeightedGraph I 𝕜 k}

namespace ResIndPiece

variable {ν' ν'' ν₁ ν₂ : I →₀ ℕ} (L : ShuffleLayout ν' ν'' ν₁ ν₂) (G : GradingDatum Γ)

/-- The unshifted grading of the piece of a four-block layout: the grading of the middle balanced
tensor product. -/
def baseGrading : ℤ → Submodule k (ResIndPiece k Γ L) :=
  middleGrading G L.a L.b L.c L.d

theorem grading_eq_shift_baseGrading :
    grading L G = Graded.shift (baseGrading L G) (middleShift G L.a L.b L.c L.d) := rfl

instance : Decomposition (baseGrading L G) :=
  inferInstanceAs (Decomposition (middleGrading G L.a L.b L.c L.d))

instance : SetLike.GradedSMul (tensorGrading (G.klrGrade ν₁) (G.klrGrade ν₂))
    (baseGrading L G) where
  smul_mem {i j u x} hu hx := by
    rw [smul_left_def, ResIndPiece.leftAct, middleLeftAct_apply]
    have := middleCornerMap_mem_middleGrading G (L.leftEquiv_symm_mem G hu)
      (SetLike.GradedOne.one_mem (A := tensorGrading (G.klrGrade (L.a + L.b))
        (G.klrGrade (L.c + L.d)))) hx
    rw [show i +ᵥ j = i + j + 0 by rw [vadd_eq_add, add_zero]]
    exact this

/-- The right action on a piece raises degrees, for the unshifted grading. -/
theorem op_smul_mem_baseGrading {i l : ℤ} {x : ResIndPiece k Γ L}
    {w : WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν''}
    (hx : x ∈ baseGrading L G i) (hw : w ∈ tensorGrading (G.klrGrade ν') (G.klrGrade ν'') l) :
    op w • x ∈ baseGrading L G (i + l) := by
  rw [smul_right_def, ResIndPiece.rightAct, middleRightAct_apply]
  have := middleCornerMap_mem_middleGrading G
    (SetLike.GradedOne.one_mem (A := tensorGrading (G.klrGrade (L.a + L.c))
      (G.klrGrade (L.b + L.d)))) (L.rightEquiv_symm_mem G hw) hx
  rw [show i + l = 0 + i + l by ring]
  exact this

end ResIndPiece

end CommRing

section Field

variable {k : Type w} [Field k] {Γ : WeightedGraph I 𝕜 k} {ν₁ ν₂ ν' ν'' : I →₀ ℕ}

namespace ResIndPiece

variable (L : ShuffleLayout ν' ν'' ν₁ ν₂) (G : GradingDatum Γ) (hD : Γ.Dagger)
  (hZ : Γ.NoZeroLoops) (hS : Γ.Standing)

/-- `ResIndPiece L ⊗_{W_{ν'} ⊗ W_{ν''}} X`, with the unshifted grading of the piece, as a finitely
generated graded projective `W_{ν₁} ⊗ W_{ν₂}`-module, under the standing hypothesis. -/
def tensorGProj (X : GProj (tensorGrading (G.klrGrade ν') (G.klrGrade ν''))) :
    GProj (tensorGrading (G.klrGrade ν₁) (G.klrGrade ν₂)) :=
  haveI := balancedTensor_finite L X.carrier hD hZ hS
  haveI := balancedTensor_projective L X.carrier hD hZ hS
  balancedTensorGProj (tensorGrading (G.klrGrade ν₁) (G.klrGrade ν₂))
    (tensorGrading (G.klrGrade ν') (G.klrGrade ν'')) X.grading (ResIndPiece k Γ L)
    (baseGrading L G) fun _ _ _ _ hx hw => op_smul_mem_baseGrading L G hx hw

end ResIndPiece

/-- **The graded Mackey formula for `Res ∘ Ind`** (B. Webster, arXiv:1209.2463v4, proof of
Theorem 2.19; after Khovanov–Lauda, arXiv:0803.4121v2, Proposition 2.18), over a field `k`,
under the standing hypothesis. Let `ν₁ + ν₂ = ν' + ν''`. There are four-block layouts `L i`, one
for each shuffle type of `(ν', ν''; ν₁, ν₂)`, such that for all finitely generated graded
projective `P` over `W_{ν'}` and `P'` over `W_{ν''}`,
`Res_{ν₁;ν₂} [Ind (P ⊠ P')] = ∑ᵢ q^{sᵢ} [ResIndPiece (L i) ⊗_{W_{ν'} ⊗ W_{ν''}} (P ⊠ P')]`
in the graded `K₀` of `W_{ν₁} ⊗ W_{ν₂}`, where `sᵢ = middleShift G a b c d` for the blocks of
`L i` and the piece carries the grading of the middle balanced tensor product. Here `K₀(W_{ν'+ν''})`
is identified with `K₀(W_{ν₁+ν₂})` along `castW`. -/
theorem exists_resK0_indK0_eq_sum_graded (G : GradingDatum Γ) (hD : Γ.Dagger)
    (hZ : Γ.NoZeroLoops) (hS : Γ.Standing) (hν₁ : ν₁ + ν₂ = ν' + ν'') :
    ∃ (n : ℕ) (L : Fin n → ShuffleLayout ν' ν'' ν₁ ν₂),
      Function.Injective (fun i => ⇑(L i).c) ∧
      Set.range (fun i => ⇑(L i).c) = Set.range (shuffleType (ν := ν' + ν'') ν' ν₁) ∧
      ∀ (Q : GProj (G.klrGrade ν')) (Q' : GProj (G.klrGrade ν'')),
        G.resK0 ν₁ ν₂ hD hZ hS (K0.map (castW k Γ hν₁.symm)
            (fun _ _ h => G.castW_symm_mem_klrGrade hν₁.symm h)
            (G.indK0 ν' ν'' (K0.of Q) (K0.of Q'))) =
          ∑ i, (LaurentPolynomial.T (middleShift G (L i).a (L i).b (L i).c (L i).d) :
              LaurentPolynomial ℤ) •
            K0.of (ResIndPiece.tensorGProj (L i) G hD hZ hS (Q.extTensor Q')) := by
  choose Pc hP using fun C E : FullChamber Γ (ν' + ν'') => exists_isChamberSegment hD hZ C E
  obtain ⟨n, L, hinj, hrange, h⟩ := exists_resInd_balancedTensor_eq_sum_graded (k := k) hP hD hZ
    hS.psymm (fun w => hS.isRegular_factor w) hS.isRegular_loopFactor' rfl hν₁ G
  refine ⟨n, L, hinj, hrange, fun Q Q' => ?_⟩
  have hfin := fun i => ResIndPiece.balancedTensor_finite (L i) (Q.extTensor Q').carrier hD hZ hS
  have hproj := fun i =>
    ResIndPiece.balancedTensor_projective (L i) (Q.extTensor Q').carrier hD hZ hS
  obtain ⟨_, _, hsum⟩ := h (Q.extTensor Q').carrier (Q.extTensor Q').grading
  rw [resK0_map_indK0_eq hP hD hZ hS.psymm (fun w => hS.isRegular_factor w)
    hS.isRegular_loopFactor' hν₁ G hS Q Q', hsum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact K0.of_balancedTensorGProj_shift_left _ _ _ (ResIndPiece.baseGrading (L i) G) _
    (fun _ _ _ _ hx hw => ResIndPiece.op_smul_mem_baseGrading (L i) G hx hw) _

end Field

end Categorification.WeightedKLR

end

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.EmptyTensorWordEquiv
import Categorification.WeightedKLR.RedStrands.CyclotomicMaskTests
import Categorification.WeightedKLR.RedStrands.PrefixStandardCharacter
import Categorification.WeightedKLR.RedStrands.StandardizationProductTest
import Categorification.WeightedKLR.RedStrands.TensorFactorRank
import Categorification.WeightedKLR.RedStrands.TensorFactorSeparation

/-!
# The integral tensor-product categorification on projective classes

Webster, arXiv:1309.3796v2, §4.7, Theorem 4.38. The split Grothendieck group of
graded projectives is the integral tensor product of the highest-weight modules. The
comparison sends prescribed divided words to their word vectors. The proof compares
ordinary loading characters on standardizations of pairs of simple tops, using
Webster's last-red filtration for the rank bound and the bar coproduct for these characters.
-/
noncomputable section
namespace Categorification.Stendhal.FirstWeight
open KLR KLRAlgebra Categorification.Graded GProj QuantumGroup LieLean LieLean.QuantumGroup
  LieLean.QuantumGroup.GrandLoop LusztigF
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

local notation "LP" => LaurentPolynomial ℤ
local notation "L" => RatFunc ℚ
private abbrev inversion := (LaurentPolynomial.invert (R := ℤ)).toRingEquiv
private local instance tensorModuleInversionPair : RingHomInvPair inversion.toRingHom inversion.toRingHom := RingHomInvPair.of_ringEquiv inversion

variable {I : Type} {k Y : Type*} [DecidableEq I] [Field k] [AddCommGroup Y] [Finite I]
  {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)
  {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular) {ℓ : ℕ}

private abbrev moduleGrading {m : ℕ} (Λ : Fin m → I →₀ ℕ) :=
  stendhalGradingDatum Λ hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)

private abbrev wordComparison {m : ℕ} (Λ : Fin m → I →₀ ℕ) (wt : Fin m → Dom R) :=
  ∃ e : DirectSum (Multiset I) (fun β => K0 (tensorProductGrade (moduleGrading C hQ Λ) β))
      ≃ₛₗ[inversion.toRingHom] integralTensor wt,
    ∀ w, e (tensorWordProjectiveClass Λ C hQ w) = integralWordVector (C := C) wt w

include hR

private theorem comparison_succ (Λ : Fin (ℓ+1) → I →₀ ℕ) (wt : Fin (ℓ+1) → Dom R)
    (hwt : ∀ i, (Λ (Fin.last ℓ) i : ℤ) = (wt (Fin.last ℓ)).1 (R.coroot i))
    (earlier : wordComparison C hQ (Λ ∘ Fin.castSucc) (fun j => wt (Fin.castSucc j))) :
    wordComparison C hQ Λ wt := by
  let Λ₀ := Λ ∘ Fin.castSucc
  let wt₀ := fun j : Fin ℓ => wt (Fin.castSucc j)
  let μ := Λ (Fin.last ℓ)
  let lastWeight := wt (Fin.last ℓ)
  let A := Σ θ : Multiset I, IndecClass (tensorProductGrade (moduleGrading C hQ Λ₀) θ)
  let B := Σ β : Multiset I, IndecClass (CycKLR.grade hQ.gradingDatum μ β)
  obtain ⟨E,hE⟩ := earlier
  let f := prefixTopTest Λ₀ C hQ wt₀ hR E
  let g := cyclotomicTopTest C μ hQ lastWeight hwt hR
  let G := moduleGrading C hQ Λ
  let S (ν : Multiset I) (j : A × B) : GFin (tensorProductGrade G ν) :=
    standardizationTestAt Λ G j.1.1 j.2.1 (fun i i' h => (hQ.symm i i' h).symm)
      (prefixStandardTop Λ C hQ j.1.1 j.1.2) (cyclotomicSimpleTop C μ hQ j.2.1 j.2.2) ν
  let t (j : A × B) := (factorTensorTest f g j.1 j.2).comp (tensorSplitLast wt).toLinearMap
  apply exists_tensorWordEquiv_of_prefixShuffle C wt hR Λ hQ hwt
    ((exists_tensorWordEquiv_iff Λ₀ C hQ wt₀ hR).mp ⟨E,hE⟩) S (fun _ => t)
  · intro ν
    exact barWeightCoordinates_injective_of_factorTests C wt hR ν
      (prefixBasisPoint Λ₀ C hQ wt₀ hR E) (cyclotomicBasisPoint C μ hQ lastWeight hwt hR) f g
      (prefixBasisPoint_span Λ₀ C hQ wt₀ hR E) (span_cyclotomicBasisPoint C μ hQ lastWeight hwt hR)
      (fun a i => by
        by_cases h : a = i <;> simpa [h] using prefixTopTest_point Λ₀ C hQ wt₀ hR E a i)
      (fun b i => by
        by_cases h : b = i <;> simpa [h] using cyclotomicTopTest_point C μ hQ lastWeight hwt hR b i)
  · rintro ν w ⟨⟨θ,a⟩,⟨β,b⟩⟩
    exact standardizationTestAt_word Λ C hQ θ β (prefixStandardTop Λ C hQ θ a)
      (cyclotomicSimpleTop C μ hQ β b) wt f g ⟨θ,a⟩ ⟨β,b⟩ (fun i => (hwt i).symm) ν w
      (prefixStandardTop_mask Λ C hQ wt hR E hE θ a w.1)
      (cyclotomicTopTest_mask Λ C hQ θ β wt hwt hR b w.1)
      (prefixTopTest_mask_of_ne Λ C hQ wt hR E hE θ a w.1)
      (cyclotomicTopTest_mask_of_ne Λ C hQ β wt hwt hR b w.1)

/-- **Webster, arXiv:1309.3796v2, Theorem 4.38 (underlying integral module)**.
For a family of dominant highest weights the Laurent-semilinear equivalence from the
split Grothendieck group of graded projectives sends every divided projective word
to the corresponding tensor vector. -/
theorem exists_tensorWordEquiv (Λ : Fin ℓ → I →₀ ℕ) (wt : Fin ℓ → Dom R)
    (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i)) :
    ∃ e : DirectSum (Multiset I) (fun β => K0 (tensorProductGrade
      (stendhalGradingDatum Λ hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)) β))
        ≃ₛₗ[inversion.toRingHom] integralTensor wt,
      ∀ w, e (tensorWordProjectiveClass Λ C hQ w) = integralWordVector (C := C) wt w := by
  induction ℓ with
  | zero => exact exists_emptyTensorWordEquiv C hQ wt Λ
  | succ m ih =>
    exact comparison_succ C hQ hR Λ wt (hwt (Fin.last m))
      (ih (Λ ∘ Fin.castSucc) (fun j => wt (Fin.castSucc j)) (fun j => hwt (Fin.castSucc j)))

end Categorification.Stendhal.FirstWeight

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorModuleEquiv
import Categorification.WeightedKLR.RedStrands.TensorWordIntertwining

/-!
# Webster's canonical identification on projective classes

Webster, arXiv:1309.3796v2, §4.7, Theorem 4.38, underlying integral
module. Lemma 4.37 makes the prescribed images determine a unique map.
The recursion before Lemma 4.36 identifies its action on the functors
of right black induction and terminal-red induction.
-/

noncomputable section
namespace Categorification.Stendhal.FirstWeight

open KLR Categorification.Graded QuantumGroup LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
local notation "LP" => LaurentPolynomial ℤ
local notation "v" => (RatFunc.X : RatFunc ℚ)
local instance : NeZero v := ⟨RatFunc.X_ne_zero⟩
private abbrev inversion := (LaurentPolynomial.invert (R := ℤ)).toRingEquiv
local instance : RingHomInvPair inversion.toRingHom inversion.toRingHom := RingHomInvPair.of_ringEquiv inversion

variable {I : Type} {k Y : Type*} [DecidableEq I] [Field k] [AddCommGroup Y] [Finite I]
  {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)
  {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular) {ℓ : ℕ}

section Comparison
variable (Λ : Fin ℓ → I →₀ ℕ) (wt : Fin ℓ → Dom R)
  (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i))

local notation "K" => DirectSum (Multiset I) (tensorProjectiveGroup C hQ Λ)
local notation "G" => stendhalGradingDatum Λ hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)

/-- The canonical integral identification specified by the projective words in
Webster, arXiv:1309.3796v2, Theorem 4.38. The grading variable maps to its inverse. -/
def tensorModuleEquiv : K ≃ₛₗ[inversion.toRingHom] integralTensor wt :=
  (exists_tensorWordEquiv C hQ hR Λ wt hwt).choose

local notation "η" => tensorModuleEquiv C hQ hR Λ wt hwt

/-- Webster, Theorem 4.38, on every shifted divided-word projective. -/
@[simp] theorem tensorModuleEquiv_word (w : TensorWord I ℓ) :
    η (tensorWordProjectiveClass Λ C hQ w) = integralWordVector (C := C) wt w :=
  (exists_tensorWordEquiv C hQ hR Λ wt hwt).choose_spec w

/-- Webster, §4.7, Lemma 4.37 and Theorem 4.38. The specified values uniquely
determine the semilinear map, including its values on all direct summands. -/
theorem tensorModuleEquiv_unique (g : K →ₛₗ[inversion.toRingHom] integralTensor wt)
    (hw : ∀ w, g (tensorWordProjectiveClass Λ C hQ w) = integralWordVector (C := C) wt w) :
    g = (η).toLinearMap := by
  apply LinearMap.ext_on_range (span_tensorWordProjectiveClass Λ C hQ)
  exact fun w => (hw w).trans (tensorModuleEquiv_word C hQ hR Λ wt hwt w).symm

/-- Webster, §4.6 and the recursion preceding Lemma 4.36. The image of right
black induction is the iterated coproduct action of the lowering generator. -/
theorem tensorModuleEquiv_F (i : I) (x : K) :
    (η (blackLower G i x) : TensorSpace wt) = tensorRepresentation wt (F R v i) (η x : TensorSpace wt) :=
  map_blackLower C hQ Λ wt (η).toLinearMap (tensorModuleEquiv_word C hQ hR Λ wt hwt) i x

/-- The divided-power version of the lowering formula for Webster's
Theorem 4.38 holds on the entire integral lattice. -/
theorem tensorModuleEquiv_dividedF (i : I) (n : ℕ) (x : K) :
    (η (blackDividedLower Λ C hQ i n x) : TensorSpace wt) =
      tensorRepresentation wt (qDivPow (v ^ C.toLusztig.d i) n (F R v i)) (η x : TensorSpace wt) :=
  map_blackDividedLower C hQ Λ wt (η).toLinearMap (tensorModuleEquiv_word C hQ hR Λ wt hwt) i n x

end Comparison

/-- Under Webster's identification, adjoining the terminal red strand tensors
every projective class with the final highest vector (the recursion before Lemma 4.36). -/
theorem tensorModuleEquiv_lastRed (Λ : Fin (ℓ+1) → I →₀ ℕ) (wt : Fin (ℓ+1) → Dom R)
    (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i))
    (x : DirectSum (Multiset I) (tensorProjectiveGroup C hQ (Λ ∘ Fin.castSucc))) :
    (tensorModuleEquiv C hQ hR Λ wt hwt (totalLastRedIndK0 C hQ Λ x) : TensorSpace wt) =
      appendTensor wt (tensorModuleEquiv C hQ hR (Λ ∘ Fin.castSucc) (fun j => wt (Fin.castSucc j))
        (fun j => hwt (Fin.castSucc j)) x) (IrreducibleModule.hwv R v (wt (Fin.last ℓ)).1) :=
  map_totalLastRedIndK0 C hQ Λ wt _ _ (tensorModuleEquiv_word C hQ hR _ _ _)
    (tensorModuleEquiv_word C hQ hR Λ wt hwt) x

end Categorification.Stendhal.FirstWeight

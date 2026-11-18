/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorWordInduction
import Categorification.WeightedKLR.RedStrands.EqualBlackProjectives
import Categorification.WeightedKLR.RedStrands.MixedBlackProjectives
import Categorification.WeightedKLR.RedStrands.RaisingAppendRed

/-! # Inducing a word after an upward black strand

Webster, arXiv:1309.3796v2, §4.7, Lemma 4.35. In the projective action,
the part of the word following the upward strand acts by successive
right black and last-red inductions. The tensor-module proof uses a finite set
of simple roots, Rouquier parameters over a field, and the Cartan grading on
the prefix blocks. These objectwise isomorphisms concern projectives obtained
from the functor action in the ordered Stendhal blocks. Identification with
the signed boundary ideals of Definition 4.34 requires the double diagram algebra.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR Categorification.Graded
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type*} [DecidableEq I] [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
    {m n : ℕ} {Λ₀ : Fin m → I →₀ ℕ} {Λ : Fin n → I →₀ ℕ}
    {G₀ : GradingDatum (stendhalQ Q Λ₀)} {G : GradingDatum (stendhalQ Q Λ)}
    {β ν : Multiset I}

/-- A sequence of ordinary black and red inductions, with its source and target blocks. -/
inductive WordSuffix (G₀ : GradingDatum (stendhalQ Q Λ₀)) (β : Multiset I) :
    {n : ℕ} → {Λ : Fin n → I →₀ ℕ} → GradingDatum (stendhalQ Q Λ) → Multiset I → Type _ where
  | nil : WordSuffix G₀ β G₀ β
  | black {n : ℕ} {Λ : Fin n → I →₀ ℕ} {G : GradingDatum (stendhalQ Q Λ)} {ν}
      (w : WordSuffix G₀ β G ν) (i : I) : WordSuffix G₀ β G ((Singleton.singleton i : Multiset I) + ν)
  | red {n : ℕ} {Λ : Fin (n+1) → I →₀ ℕ} (G : GradingDatum (stendhalQ Q Λ)) {ν}
      (w : WordSuffix G₀ β (restrictRedGrading Q Λ G) ν) : WordSuffix G₀ β G ν

/-- Apply the suffix to a graded projective. -/
def WordSuffix.induceProj (w : WordSuffix G₀ β G ν)
    (P : GProj (tensorProductGrade G₀ β)) : GProj (tensorProductGrade G ν) := by
  induction w with
  | nil => exact P
  | black w i ih => exact blackIndProj _ i _ ih
  | red G w ih => exact lastRedIndProj G _ ih

/-- The Laurent-linear action of the same suffix on projective classes. -/
def WordSuffix.induceK0 (w : WordSuffix G₀ β G ν) :
    K0 (tensorProductGrade G₀ β) →ₗ[LaurentPolynomial ℤ] K0 (tensorProductGrade G ν) := by
  induction w with
  | nil => exact LinearMap.id
  | black w i ih => exact (blackIndK0 _ i _).comp ih
  | red G w ih => exact (lastRedIndK0 G _).comp ih

@[simp] theorem WordSuffix.induceK0_of (w : WordSuffix G₀ β G ν)
    (P : GProj (tensorProductGrade G₀ β)) :
    w.induceK0 (K0.of P) = K0.of (w.induceProj P) := by
  induction w with
  | nil => rfl
  | black w i ih =>
    change blackIndK0 _ i _ (w.induceK0 (K0.of P)) = K0.of (blackIndProj _ i _ (w.induceProj P))
    rw [ih, blackIndK0_of]
  | red G w ih =>
    change lastRedIndK0 G _ (w.induceK0 (K0.of P)) = K0.of (lastRedIndProj G _ (w.induceProj P))
    rw [ih, lastRedIndK0_of]

/-- Projective associated to a single upward strand between the ordered prefix
loading and a red/black suffix. An absent upward colour gives the zero projective. -/
def oneUpwardProj (C : QuantumGroup.CartanDatum I) (hQ : IsRouquierQ C Q) (i : I)
    (s : Seq (stendhalWeight m β)) (hs : IsRedOrdered s)
    (w : WordSuffix G₀ (β.erase i) G ν) : GProj (tensorProductGrade G ν) :=
  w.induceProj (FirstWeight.blackRaiseProjAt G₀ i β C hQ (sequenceProj G₀ s hs))

/-- An interval of consecutive red strands between two black positions. -/
inductive RedRun (Λ₀ : Fin m → I →₀ ℕ) : {n : ℕ} → (Fin n → I →₀ ℕ) → Type _ where
  | nil : RedRun Λ₀ Λ₀
  | snoc {n : ℕ} (Λ : Fin (n+1) → I →₀ ℕ)
      (r : RedRun Λ₀ (Λ ∘ Fin.castSucc)) : RedRun Λ₀ Λ

end Categorification.Stendhal

namespace Categorification.Stendhal
open KLR Categorification.Graded FirstWeight
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} {k : Type*} [DecidableEq I] [Field k] [Finite I]
  {Q : I → I → MvPolynomial (Fin 2) k} (C : QuantumGroup.CartanDatum I) (hQ : IsRouquierQ C Q)
  {l m n : ℕ} {Λ₀ : Fin l → I →₀ ℕ} {Λ₁ : Fin m → I →₀ ℕ} {Λ : Fin n → I →₀ ℕ}
  {D : GradingDatum (stendhalQ Q Λ)} {ν : Multiset I}

private abbrev wordGrade {t : ℕ} (L : Fin t → I →₀ ℕ) :=
  stendhalGradingDatum L hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)

private abbrev addColor (i : I) (β : Multiset I) : Multiset I := ({i} : Multiset I) + β

local notation "G₀" => wordGrade C hQ Λ₀
local notation "G₁" => wordGrade C hQ Λ₁

/-- Apply the red interval to the prefix projective in any black block. -/
def RedRun.induceProj (r : RedRun Λ₀ Λ₁) (β : Multiset I)
    (P : GProj (tensorProductGrade G₀ β)) : GProj (tensorProductGrade G₁ β) := by
  induction r with
  | nil => exact P
  | snoc L r ih => exact redIndProj C hQ L β ih

/-- The class map of a red interval. -/
def RedRun.induceK0 (r : RedRun Λ₀ Λ₁) (β : Multiset I) :
    K0 (tensorProductGrade G₀ β) →ₗ[LaurentPolynomial ℤ] K0 (tensorProductGrade G₁ β) := by
  induction r with
  | nil => exact LinearMap.id
  | snoc L r ih => exact (redIndK0 C hQ L β).comp ih

omit [Finite I] in
@[simp] theorem RedRun.induceK0_of (r : RedRun Λ₀ Λ₁) (β : Multiset I)
    (P : GProj (tensorProductGrade G₀ β)) :
    r.induceK0 C hQ β (K0.of P) = K0.of (r.induceProj C hQ β P) := by
  induction r with
  | nil => rfl
  | snoc L r ih =>
    change redIndK0 C hQ L β (r.induceK0 C hQ β (K0.of P)) =
      K0.of (redIndProj C hQ L β (r.induceProj C hQ β P))
    rw [ih, redIndK0_of]

private theorem class_raiseAt_redRun (r : RedRun Λ₀ Λ₁) (i : I) (β : Multiset I)
    (P : GProj (tensorProductGrade G₀ β)) :
    K0.of (blackRaiseProjAt G₁ i β C hQ (r.induceProj C hQ β P)) =
      r.induceK0 C hQ (β.erase i) (K0.of (blackRaiseProjAt G₀ i β C hQ P)) := by
  induction r with
  | nil => rfl
  | snoc L r ih =>
    change K0.of (blackRaiseProjAt _ i β C hQ (redIndProj C hQ L _ (r.induceProj C hQ _ P))) =
      redIndK0 C hQ L _ (r.induceK0 C hQ _ _)
    rw [K0.of_eq_of_iso (blackRaiseProjAt_redIndProj_iso C hQ L i β _).some, ← redIndK0_of, ih]

private theorem map_sumShifts {A B : Type*} [Ring A] [Ring B] [Algebra k A] [Algebra k B]
    {𝒜 : ℤ → Submodule k A} {ℬ : ℤ → Submodule k B} [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
    (f : K0 𝒜 →ₗ[LaurentPolynomial ℤ] K0 ℬ) (P : GProj 𝒜) (P' : GProj ℬ)
    (h : f (K0.of P) = K0.of P') (s : ℕ → ℤ) (a : ℕ) :
    f (K0.of (sumShifts P s a)) = K0.of (sumShifts P' s a) := by
  induction a with
  | zero => simp [sumShifts, K0.of_eq_zero_of_subsingleton]
  | succ a ih =>
    simp only [sumShifts, K0.of_prod, map_add, ← K0.T_smul_of, map_smul, h, ih]

omit [Finite I] in
include hQ in
private theorem wordHasGdim (ν : Multiset I) : HasGdim (tensorProductGrade D ν) := by
  let := tensorProductAlgebra_finite Λ ν hQ
  exact HasGdim.of_finiteDimensional _

local notation "B₀" => tensorProductGrade G₀
local notation "B₁" => tensorProductGrade G₁

/-- Raise before the intervening red strands and lower after them. The object
is zero when the raising operator kills the input block. -/
def RedRun.indRaiseProj (r : RedRun Λ₀ Λ₁) (i : I) (β : Multiset I)
    (P : GProj (B₀ β)) : GProj (B₁ β) :=
  if h : i ∈ β then
    let e : addColor i (β.erase i) = β := (Multiset.singleton_add ..).trans (Multiset.cons_erase h)
    projectiveBlockCast G₁ e (blackIndProj G₁ i (β.erase i) (r.induceProj C hQ (β.erase i)
      (blackRaiseProj G₀ i (β.erase i) C hQ (projectiveBlockCast G₀ e.symm P))))
  else GProj.zeroObj _

private theorem class_raise_redRun (r : RedRun Λ₀ Λ₁) (i : I) (β : Multiset I)
    (P : GProj (B₀ (addColor i β))) :
    K0.of (𝒜 := B₁ β) (blackRaiseProj G₁ i β C hQ (r.induceProj C hQ (addColor i β) P)) =
      K0.of (r.induceProj C hQ β (blackRaiseProj G₀ i β C hQ P)) := by
  induction r with
  | nil => rfl
  | snoc L r ih =>
    change K0.of (blackRaiseProj (wordGrade C hQ L) i β C hQ
      (redIndProj C hQ L (addColor i β) (r.induceProj C hQ (addColor i β) P))) =
      K0.of (redIndProj C hQ L β (r.induceProj C hQ β (blackRaiseProj G₀ i β C hQ P)))
    rw [K0.of_eq_of_iso (blackRaiseProj_redIndProj_iso C hQ L i β _).some, ← redIndK0_of,
      ← redIndK0_of, ih]

private theorem class_indRaise_redRun (r : RedRun Λ₀ Λ₁) (i : I) (β : Multiset I)
    (P : GProj (B₀ β)) :
    K0.of (blackIndRaiseProj C hQ Λ₁ i β (r.induceProj C hQ β P)) =
      K0.of (r.indRaiseProj C hQ i β P) := by
  have eval (γ : Multiset I) (e : addColor i γ = β) :
      K0.of (projectiveBlockCast G₁ e (blackIndProj G₁ i γ (blackRaiseProj G₁ i γ C hQ
        (projectiveBlockCast G₁ e.symm (r.induceProj C hQ β P))))) =
      K0.of (projectiveBlockCast G₁ e (blackIndProj G₁ i γ (r.induceProj C hQ γ
        (blackRaiseProj G₀ i γ C hQ (projectiveBlockCast G₀ e.symm P))))) := by
    subst β
    simpa only [projectiveBlockCast, blackIndK0_of] using
      congrArg (blackIndK0 G₁ i γ) (class_raise_redRun C hQ r i γ P)
  unfold blackIndRaiseProj RedRun.indRaiseProj
  split
  next h =>
    exact eval _ ((Multiset.singleton_add ..).trans (Multiset.cons_erase h))
  next => rfl

local notation "EF" => fun i β P => blackRaiseProj G₁ i β C hQ (blackIndProj G₁ i β P)
local notation "pair" => blackBlockPairing C Λ₁
local notation "shifts" => fun (i : I) (a : ℕ) (j : ℕ) =>
  (C.toLusztig.d i : ℤ) * (2 * j + 1 - (a : ℤ))

omit [Finite I] in
private theorem castProjectiveClass {β γ : Multiset I} (e : β = γ) {P P' : GProj (B₁ β)}
    (h : K0.of P = K0.of P') :
    K0.of (projectiveBlockCast G₁ e P) = K0.of (projectiveBlockCast G₁ e P') := by
  subst γ
  exact h

/-- Lower immediately after the red interval and raise at the next black gap. -/
def RedRun.raiseAfterLower (r : RedRun Λ₀ Λ₁) (i j : I) (β : Multiset I)
    (P : GProj (B₀ β)) : GProj (B₁ ((addColor j β).erase i)) :=
  blackRaiseProjAt G₁ i (addColor j β) C hQ (blackIndProj G₁ j β (r.induceProj C hQ β P))

/-- Raise before the red interval, then lower at its right end. -/
def RedRun.lowerAfterRaise (r : RedRun Λ₀ Λ₁) (i j : I) (hij : i ≠ j) (β : Multiset I)
    (P : GProj (B₀ β)) : GProj (B₁ ((addColor j β).erase i)) :=
  projectiveBlockCast G₁ (Multiset.erase_add_right_neg (a := i) (s := {j}) β (by simpa using hij)).symm
    (blackIndProj G₁ j (β.erase i) (r.induceProj C hQ (β.erase i) (blackRaiseProjAt G₀ i β C hQ P)))

/-- Distinct colours in Webster, arXiv:1309.3796v2, Lemma 4.35. The upward strand
passes the intervening reds and the adjacent downward strand; both words then
act by the same suffix. The erased block also covers an absent upward colour. -/
theorem oneUpward_swap_ne (i j : I) (hij : i ≠ j) (β : Multiset I)
    (P : GProj (B₀ β)) (r : RedRun Λ₀ Λ₁)
    (w : WordSuffix G₁ ((addColor j β).erase i) D ν) :
    Nonempty ((w.induceProj (r.raiseAfterLower C hQ i j β P)).Iso
      (w.induceProj (r.lowerAfterRaise C hQ i j hij β P))) := by
  let := wordHasGdim (D := D) C hQ ν
  apply K0.of_eq_of_iff.mp
  unfold RedRun.raiseAfterLower RedRun.lowerAfterRaise
  rw [← WordSuffix.induceK0_of, ← WordSuffix.induceK0_of,
    K0.of_eq_of_iso (blackRaiseProjAt_blackIndProj_iso_of_ne C hQ Λ₁ i j hij β _).some]
  apply congrArg
  have hr := class_raiseAt_redRun C hQ r i β P
  rw [RedRun.induceK0_of] at hr
  have hf := congrArg (blackIndK0 G₁ j (β.erase i)) hr
  rw [blackIndK0_of, blackIndK0_of] at hf
  exact castProjectiveClass C hQ _ hf

/-- Webster, arXiv:1309.3796v2, Lemma 4.35, at nonnegative coroot pairing.
The copies carry the quantum-integer shifts on the projective obtained by deleting
both black positions and retaining every intervening red and suffix strand. -/
theorem oneUpward_swap_of_nonneg (i : I) (β : Multiset I) (P : GProj (B₀ β))
    (r : RedRun Λ₀ Λ₁) (w : WordSuffix G₁ β D ν) (h : 0 ≤ pair i β) :
    Nonempty ((w.induceProj (EF i β (r.induceProj C hQ β P))).Iso
      ((w.induceProj (r.indRaiseProj C hQ i β P)).prod
        (sumShifts (w.induceProj (r.induceProj C hQ β P)) (shifts i (pair i β).toNat) (pair i β).toNat))) := by
  let := wordHasGdim (D := D) C hQ ν
  apply K0.of_eq_of_iff.mp
  let f := w.induceK0
  have hP : f (K0.of (r.induceProj C hQ β P)) = K0.of (w.induceProj (r.induceProj C hQ β P)) := by
    simp [f]
  have hc := congrArg f (K0.of_eq_of_iso (blackRaiseInd_iso_of_nonneg C hQ Λ₁ i β (r.induceProj C hQ β P) h).some)
  rw [K0.of_prod, map_add] at hc
  change _ = _ + f (K0.of (sumShifts (r.induceProj C hQ β P) (shifts i (pair i β).toNat) (pair i β).toNat)) at hc
  rw [map_sumShifts f _ _ hP] at hc
  rw [K0.of_prod]
  simpa only [← WordSuffix.induceK0_of, class_indRaise_redRun, f] using hc

/-- Webster, arXiv:1309.3796v2, Lemma 4.35, at nonpositive coroot pairing.
The copies carry the quantum-integer shifts on the projective obtained by deleting
both black positions and retaining every intervening red and suffix strand. -/
theorem oneUpward_swap_of_nonpos (i : I) (β : Multiset I) (P : GProj (B₀ β))
    (r : RedRun Λ₀ Λ₁) (w : WordSuffix G₁ β D ν) (h : pair i β ≤ 0) :
    Nonempty ((w.induceProj (r.indRaiseProj C hQ i β P)).Iso
      ((w.induceProj (EF i β (r.induceProj C hQ β P))).prod
        (sumShifts (w.induceProj (r.induceProj C hQ β P)) (shifts i (-(pair i β)).toNat) (-(pair i β)).toNat))) := by
  let := wordHasGdim (D := D) C hQ ν
  apply K0.of_eq_of_iff.mp
  let f := w.induceK0
  have hP : f (K0.of (r.induceProj C hQ β P)) = K0.of (w.induceProj (r.induceProj C hQ β P)) := by
    simp [f]
  have hc := congrArg f (K0.of_eq_of_iso (blackIndRaise_iso_of_nonpos C hQ Λ₁ i β (r.induceProj C hQ β P) h).some)
  rw [K0.of_prod, map_add] at hc
  change _ = _ + f (K0.of (sumShifts (r.induceProj C hQ β P) (shifts i (-(pair i β)).toNat) (-(pair i β)).toNat)) at hc
  rw [map_sumShifts f _ _ hP] at hc
  rw [K0.of_prod]
  simpa only [← WordSuffix.induceK0_of, class_indRaise_redRun, f] using hc

end Categorification.Stendhal

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackRaising
import Categorification.Algebra.Graded.KrullSchmidt

/-! # Normalized black restriction on projectives

Webster, arXiv:1309.3796v2, §4.6, Definition 4.30 and §4.7, Lemma 4.35.
The projective form of the normalized raising operator represents the
Grothendieck group action in each block.
-/

noncomputable section
namespace Categorification.Stendhal.FirstWeight

open KLR Categorification.Graded QuantumGroup
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

local notation "LP" => LaurentPolynomial ℤ

variable {I k : Type*} [DecidableEq I] [Field k] {ℓ : ℕ}
    {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}
    (G : GradingDatum (stendhalQ Q Λ)) (i : I) (ν : Multiset I)
    (C : CartanDatum I) (hQ : IsRouquierQ C Q)

/-- Right black restriction with the shift defining Webster's raising operator. -/
def blackRaiseProj (P : GProj (tensorProductGrade G ({i} + ν))) :
    GProj (tensorProductGrade G ν) :=
  (blackResProj G i ν C hQ P).shift (CycKLR.raiseShift (fun j => ∑ r, Λ r j) i ν C)

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "src" => tensorProductGrade G νᵢ
local notation "dst" => tensorProductGrade G ν

@[simp] theorem blackRaiseK0_of (P : GProj src) :
    (blackRaiseK0 (Q := Q) (Λ := Λ) G i ν C hQ)
        (@K0.of k _ (TensorProductAlgebra k Q Λ νᵢ) _ _ src P) =
      @K0.of k _ (TensorProductAlgebra k Q Λ ν) _ _ dst (blackRaiseProj G i ν C hQ P) := by
  change (LaurentPolynomial.T _ : LP) • blackResK0 G i ν C hQ (K0.of P) = _
  rw [blackResK0_of, K0.T_smul_of]
  rfl

/-- Normalized right black restriction on any block, with the zero object
as its value when the restricted colour is absent. -/
def blackRaiseProjAt (P : GProj (tensorProductGrade G ν)) :
    GProj (tensorProductGrade G (ν.erase i)) :=
  if hi : i ∈ ν then
    let e : {i} + ν.erase i = ν := (Multiset.singleton_add ..).trans (Multiset.cons_erase hi)
    blackRaiseProj G i (ν.erase i) C hQ (e.symm ▸ P)
  else GProj.zeroObj _

/-- Transport a graded projective along an equality of black contents. -/
def projectiveBlockCast {β γ : Multiset I} (e : β = γ)
    (P : GProj (tensorProductGrade G β)) : GProj (tensorProductGrade G γ) :=
  e ▸ P

/-- A block obtained by adjoining its restricted colour uses the ordinary
normalized restriction after identifying the erased content. -/
theorem blackRaiseProjAt_singleton_add_iso (P : GProj src) :
    Nonempty ((projectiveBlockCast G
      (show (νᵢ).erase i = ν from (congrArg (·.erase i) (Multiset.singleton_add i ν)).trans
        (Multiset.erase_cons_head i ν))
      (blackRaiseProjAt G i νᵢ C hQ P)).Iso (blackRaiseProj G i ν C hQ P)) := by
  have eq_on (β : Multiset I) (e : β = ν) (f : {i} + β = νᵢ) :
      projectiveBlockCast G e (blackRaiseProj G i β C hQ (projectiveBlockCast G f.symm P)) =
        blackRaiseProj G i ν C hQ P := by
    subst β
    rfl
  have hm : i ∈ νᵢ := Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton_self i))
  have hErase : (νᵢ).erase i = ν :=
    (congrArg (·.erase i) (Multiset.singleton_add i ν)).trans (Multiset.erase_cons_head i ν)
  have hAdd : {i} + (νᵢ).erase i = νᵢ :=
    (Multiset.singleton_add ..).trans (Multiset.cons_erase hm)
  rw [blackRaiseProjAt, dite_eq_left hm]
  exact (congrArg (fun X : GProj dst => Nonempty (X.Iso (blackRaiseProj G i ν C hQ P)))
    (eq_on _ hErase hAdd)).mpr ⟨GradedEquiv.refl _⟩

/-- Transporting a projective along a block equality preserves its total class. -/
theorem lof_of_transport {β γ : Multiset I} (h : β = γ)
    (P : GProj (tensorProductGrade G β)) :
    DirectSum.lof LP _ (fun δ => K0 (tensorProductGrade G δ)) γ
        (K0.of (h ▸ P : GProj (tensorProductGrade G γ))) =
      DirectSum.lof LP _ (fun δ => K0 (tensorProductGrade G δ)) β (K0.of P) := by
  subst γ
  rfl

/-- The normalized projective restriction represents the raising operator on
each direct-sum component, including on a block missing the restricted colour. -/
theorem blackRaise_lof_of_projAt (P : GProj (tensorProductGrade G ν)) :
    blackRaise G i C hQ (DirectSum.lof LP _ (fun β => K0 (tensorProductGrade G β)) ν (K0.of P)) =
      DirectSum.lof LP _ (fun β => K0 (tensorProductGrade G β)) (ν.erase i)
        (K0.of (blackRaiseProjAt G i ν C hQ P)) := by
  by_cases hi : i ∈ ν
  · rw [blackRaiseProjAt, dite_eq_left hi, ← blackRaiseK0_of, ← blackRaise_lof G i,
      lof_of_transport]
  · rw [blackRaise_lof_of_notMem G i ν C hQ hi, blackRaiseProjAt, dite_eq_right hi,
      K0.of_eq_zero_of_subsingleton, map_zero]

end Categorification.Stendhal.FirstWeight

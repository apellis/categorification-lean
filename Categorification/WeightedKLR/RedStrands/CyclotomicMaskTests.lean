/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.CyclotomicTopTests
import Categorification.WeightedKLR.RedStrands.LastRedMaskWords

/-!
# Cyclotomic simple characters on masked last-red words

Webster, arXiv:1309.3796v2, §§4.6–4.7, Theorem 4.38. Removing the initial
red strand of the final input of a surviving shuffle leaves its assigned
black subword. The graded dimension of that loading equals the value of
the one-factor simple character on the corresponding lowering word.
-/

noncomputable section
namespace Categorification.Stendhal.FirstWeight
open KLR KLRAlgebra Categorification.Graded GProj QuantumGroup QuantumGroup.UDot
open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF

variable {I : Type} [DecidableEq I] {ℓ : ℕ} {k : Type*} [Field k]
    {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin (ℓ+1) → I →₀ ℕ)
    (C : CartanDatum I) (hQ : IsRouquierQ C Q) (θ β : Multiset I)
local notation "last" => Sum.inr (α := I) (Fin.last ℓ)
local notation "ι" => (Sum.inl : I → I ⊕ Fin (ℓ+1))
local notation "f" => Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ)
local notation "α" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ)
local notation "δ" => Multiset.map f (stendhalWeight 1 β)
local notation "μ" => Λ (Fin.last ℓ)

omit [DecidableEq I] in
/-- The labels of the final input of a surviving shuffle: the last red strand followed by
the black word. -/
theorem lastInput_labels (p : Seq β) :
    List.ofFn (Seq.map f (SingleRed.insertWord β p)).1 = last :: (List.ofFn p.1).map ι := by
  apply List.ext_getElem
  · simp [stendhalWeight, add_comm]
  · intro j hj hj'
    rw [List.getElem_ofFn]
    cases j with
    | zero =>
      rw [List.getElem_cons_zero]
      exact congrArg f (SingleRed.insertWord_head β p)
    | succ j =>
      rw [List.getElem_cons_succ, List.getElem_map, List.getElem_ofFn]
      have h : j < β.card := by simpa using hj'
      change f ((SingleRed.insertWord β p).lbl ⟨j+1,_⟩) = ι (p.lbl ⟨j,h⟩)
      exact congrArg f (SingleRed.insertWord_black β p ⟨j,h⟩)

variable [Finite I] {Y : Type*} [AddCommGroup Y] {R : C.toLusztig.RootDatum Y}
    (wt : Fin (ℓ+1) → Dom R) (hwt : ∀ i, (Λ (Fin.last ℓ) i : ℤ) = (wt (Fin.last ℓ)).1 (R.coroot i))
    (hR : R.IsXRegular)
variable (j : IndecClass (CycKLR.grade hQ.gradingDatum (Λ (Fin.last ℓ)) β)) (w : TensorWord I (ℓ+1))

/-- A suffix mask of different black content pairs to zero with the final simple. -/
theorem cyclotomicTopTest_mask_of_ne (c : Fin (lastRedWord w).2.length → Bool)
    (h : (maskSubword true (lastRedBlackTags w c) : Multiset _) ≠ δ) :
    cyclotomicTopTest C (Λ (Fin.last ℓ)) hQ (wt (Fin.last ℓ)) hwt hR
      ⟨β,j⟩ (finalMaskVector w wt c) = 0 := by
  exact cyclotomicTopTest_word_of_ne C (Λ (Fin.last ℓ)) hQ (wt (Fin.last ℓ)) hwt hR
    (finalMaskLetters w c) (fun he => h ((finalMaskContent_iff w β c).mpr he)) j

/-- The final factor dimension in a surviving parabolic permutation is exactly the
cyclotomic top test on the final masked subword. -/
theorem cyclotomicTopTest_mask (s : Seq (α+δ)) (hw : List.ofFn s.1 = expandDiv w.blocks)
    (u : {u : ShuffleOf α δ s // (List.ofFn u.split.2.1).head? = some last}) :
    integralLaurentEval (gdimPoly (Graded.idem (cyclotomicSimpleTop C μ hQ β j).grading
      (parabolicLastCyclotomic Q Λ β (e u.1.split.2)))) =
      cyclotomicTopTest C μ hQ (wt (Fin.last ℓ)) hwt hR ⟨β,j⟩
        (finalMaskVector w wt (ordinaryShuffleEquiv w s hw u).1) := by
  let c := ordinaryShuffleEquiv w s hw u
  let l := finalMaskLetters w c.1
  have h : (l : Multiset I) = β := (finalMaskContent_iff w β c.1).mp c.2.2
  let p := Seq.ofList l h
  have he : u.1.split.2 = Seq.map f (SingleRed.insertWord β p) := by
    apply Subtype.ext
    apply List.ofFn_injective
    rw [lastInput_labels]
    have hp : List.ofFn p.1 = l := Seq.ofFn_ofList l h
    rw [hp]
    exact ordinaryShuffleEquiv_right_word w s hw u
  rw [he, parabolicLastCyclotomic_e]
  exact (cyclotomicTopTest_word C μ hQ (wt (Fin.last ℓ)) hwt hR l h j).symm

end Categorification.Stendhal.FirstWeight

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiveSlotCentralFlagInjection

/-!
# Stable words into the two-black left-extreme loading

For the five-slot specialization of Webster, arXiv:1309.3796v2, §6.1, proof
of Lemma 6.8 after (6.21), each bottom has two permutations matching the
left-extreme top. Choose a word preserving the order of the black strands
and its product on the left by the final black transposition. If either black
lies before red zero, the common word passes through a violated loading.
Otherwise its mixed and red crossings act by variable permutation in the
descending red orientation.
-/

namespace Categorification.Stendhal.FiveSlotFlag
open KLR KLRAlgebra TypeA Equiv BraidedStendhalAlgebra

local notation "N" => weight.card
local notation "E₀" => fixedTopFourExitCut 0

private def rank : Unit ⊕ Fin 3 → ℕ
  | .inl _ => 1
  | .inr r => if r=0 then 0 else r.val+1

private def firstInversion (s : Seq weight) : Option (Fin 4) :=
  (List.finRange 4).find? fun j =>
    rank (s.lbl ⟨j+1,lt_of_lt_of_le (Nat.succ_lt_succ j.isLt) (by decide)⟩) <
    rank (s.lbl ⟨j,lt_of_lt_of_le j.isLt (by decide)⟩)

private def sortWord : ℕ → Seq weight → List ℕ
  | 0,_ => []
  | n+1,s =>
    match firstInversion s with
    | none => []
    | some j => sortWord n (sadj N j • s) ++ [j.val]

/-- The initial bubble of the first black to the left edge. -/
def firstBlackWord (s : Seq weight) := List.range (firstBlack s).val

/-- The common reduced route to the extreme, preserving the black order.
When a black precedes the spectator, send it first to the violated edge. -/
def stableBottomWord (s : Seq weight) : List ℕ :=
  if 0 ∈ redsBefore s (firstBlack s) then sortWord 10 s
  else sortWord 10 (wordProd N (firstBlackWord s) • s) ++ firstBlackWord s

/-- An elementary unit in the descending red orientation is a red left of
a black or a larger red left of a smaller red. -/
def unitLabels : Unit ⊕ Fin 3 → Unit ⊕ Fin 3 → Bool
  | .inr _,.inl _ => true
  | .inr a,.inr b => decide (b<a)
  | _,_ => false

/-- Every crossing acts by a positional permutation in the oriented polynomial test. -/
def unitPath (s : Seq weight) : List ℕ → Bool
  | [] => true
  | j::l =>
    if h : j+1<N then
      let t := wordProd N l • s
      unitPath s l && unitLabels (t.lbl ⟨j,by omega⟩) (t.lbl ⟨j+1,h⟩)
    else false

private theorem word_check (s : Seq weight) :
    let l := stableBottomWord s
    ((l.all (fun j => decide (j+1<N)))=true ∧ l.length=invCount N (wordProd N l)) ∧
    ((1::l).length=invCount N (wordProd N (1::l))) ∧
    wordProd N l • s=E₀ ∧ wordProd N l (firstBlack s)=⟨1,by decide⟩ ∧
    (0 ∈ redsBefore s (firstBlack s) → unitPath s l=true) ∧
    ((wordProd N (firstBlackWord s) • s).lbl ⟨0,by decide⟩).isLeft := by
  obtain ⟨u,rfl⟩ := Seq.exists_smul_eq E₀ s
  have all : ∀ u : Perm (Fin N),
      let t := u • E₀
      let l := stableBottomWord t
      ((l.all (fun j => decide (j+1<N)))=true ∧ l.length=invCount N (wordProd N l)) ∧
      ((1::l).length=invCount N (wordProd N (1::l))) ∧
      wordProd N l • t=E₀ ∧ wordProd N l (firstBlack t)=⟨1,by decide⟩ ∧
      (0 ∈ redsBefore t (firstBlack t) → unitPath t l=true) ∧
      ((wordProd N (firstBlackWord t) • t).lbl ⟨0,by decide⟩).isLeft := by decide +kernel
  exact all u

theorem stableBottomWord_reduced (s : Seq weight) : IsReduced N (stableBottomWord s) :=
  ⟨fun j hj => of_decide_eq_true ((List.all_eq_true.1 (word_check s).1.1) j hj),by rw [length_eq_invCount]; exact (word_check s).1.2⟩

theorem stableBottomWord_flip_reduced (s : Seq weight) : IsReduced N (1::stableBottomWord s) :=
  ⟨validWord_cons.2 ⟨by decide,(stableBottomWord_reduced s).1⟩,
    by rw [length_eq_invCount]; exact (word_check s).2.1⟩

theorem stableBottomWord_top (s : Seq weight) : wordProd N (stableBottomWord s) • s=E₀ :=
  (word_check s).2.2.1

theorem stableBottomWord_first (s : Seq weight) : wordProd N (stableBottomWord s) (firstBlack s)=⟨1,by decide⟩ :=
  (word_check s).2.2.2.1

theorem stableBottomWord_unit (s : Seq weight) (h : 0 ∈ redsBefore s (firstBlack s)) :
    unitPath s (stableBottomWord s)=true := (word_check s).2.2.2.2.1 h

theorem firstBlackWord_violated (s : Seq weight) : IsViolated (wordProd N (firstBlackWord s) • s) :=
  ⟨by decide,(word_check s).2.2.2.2.2⟩

theorem stableBottomWord_matching (s : Seq weight) (u : Perm (Fin N)) :
    u • s=E₀ ↔ u=wordProd N (stableBottomWord s) ∨ u=wordProd N (1::stableBottomWord s) := by
  let w := wordProd N (stableBottomWord s)
  have top : w • s=E₀ := stableBottomWord_top s
  have flip : sadj N 1 • E₀=E₀ := by decide
  constructor
  · intro hu
    have fix : (u*w⁻¹) • E₀=E₀ := by rw [← top,mul_smul,inv_smul_smul,hu,top]
    have both : ∀ v : Perm (Fin N), v • E₀=E₀ → v=1 ∨ v=sadj N 1 := by decide +kernel
    obtain h|h := both _ fix
    · exact Or.inl ((mul_inv_eq_one.mp h))
    · right
      rw [wordProd_cons]
      exact (mul_inv_eq_iff_eq_mul.mp h)
  · rintro (rfl|rfl)
    · exact top
    · rw [wordProd_cons,mul_smul,stableBottomWord_top,flip]

end Categorification.Stendhal.FiveSlotFlag

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCapSuccessorTransfer
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapBubbleExitQ
import Categorification.WeightedKLR.RedStrands.DoubleViolatingBubbleSweepQ

/-!
# The closed cup in an ordinary signed matrix entry

In Webster, arXiv:1309.3796v2, §4.5, Lemma 4.28, closing both cap legs
produces a bubble at an intermediate cut. The cut carries a signed triple
because it is reached from an ordered loading. Passing the bubble through
the intervening strands and using the violating relation at the far left
reduces the entry to forward paths with no additional crossings.

This is the version of `DoubleCapBubblePosition` in which the black strands carry the relations of
Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, Definition 1.1, `r = 1`; `CLQ.pres RD k sc`) instead
of the KL III relations. Each declaration carries the suffix `Q`.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.Stendhal.DoubleDiagram
open CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams KLR KLR.Diagram
universe u v w
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {ℓ : ℕ} {weights : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}}
  {k : Type w} [CommRing k] {sc : KL3.Diagram.CL.CLScalars C k} {ν : Multiset I}
local notation "lab" => (Subtype.val ∘ weights)
variable (P : Presentation.{w,max u v} (signature RD (Subtype.val ∘ weights)) k)
  (kl : ∀ j : (KL3.Diagram.CLQ.pres RD k sc).Rel, P.lin (blackMirrorLinear RD (Subtype.val ∘ weights) ((KL3.Diagram.CLQ.pres RD k sc).rel j)) = 0)
local notation "Ord" => {s : Seq (stendhalWeight ℓ ν) // IsRedOrdered s}
local notation "W" => fun s : Ord => obj RD lab 0 (List.map DoubleStrand.down (word (Subtype.val s)))
local notation "B" => DoubleStrand I ℓ

private theorem signedDownEntry_cutScalarQ (s t : Ord) (w : List B) (p : W s ⟶ obj RD lab 0 w)
    (q : obj RD lab 0 w ⟶ W t) (β : End ((KL3.Diagram.CLQ.pres RD k sc).obj (KL3.Diagram.ob RD (endWeight RD lab 0 []) []))) :
    ∃ r : k, ∀ f : End (P.obj (obj RD lab 0 w)),
      signedDownEntry P s t (P.diag p ≫ (f ≫ blackCutHomQ RD lab sc P kl 0 [] w w rfl β) ≫ P.diag q) =
        r • signedDownEntry P s t (P.diag p ≫ f ≫ P.diag q) := by
  obtain ⟨b,hb,_⟩ := existsUnique_triple_at_cut RD weights (downTriple RD weights s) p
  have hw : b.val.word = w := by
    have h := congrArg (fun a : Obj (signature RD lab) => a.word.map Prod.snd) hb
    simpa only [obj,forget_colours] using h
  subst w
  exact farLeftBlackCut_project_comp_scalarQ sc P kl b (downTriple RD weights s) (downTriple RD weights t)
    (InducedCategory.homMk (P.diag p)) (InducedCategory.homMk (P.diag q)) LinearMap.id β

variable (Q : I → I → MvPolynomial (Fin 2) k) (e : Fin ℓ → I →₀ ℕ) (t : I → I → k)
local notation "A" => signedCapKLPresentationQ RD lab sc P Q e t
local notation "K" => signedCapKL_reflectedBlackQ RD lab sc P Q e t

/-- The cup producing both endpoints of the cap, evaluated in an ordinary matrix entry. -/
theorem capSuccessor_downCupBothQ (hshift : ∀ r i, (e r i : ℤ) = KL3.Diagram.ip RD i (weights r).val)
    (s z : Ord) (L R : List B) (l : KL3.Diagram.Letter I) :
    CapSuccessorAt k (fun f : W s ⟶ W z => signedDownEntry (A) s z ((A).diag f)) (.cup l.dual)
      L R L [] l R := by
  refine capSuccessorAt_of_projected (A) (signedDownEntry (A) s z) _ _ _ _ _ _ _
    (by simp [CapPredecessor.top,KL3.Diagram.Letter.dual_dual,List.append_assoc]) ?_
  intro μ p hp _ d tail
  have hμ : μ = 0 := (Diagram.chain p).start_eq
  subst μ
  change W s ⟶ obj RD lab 0 (L ++ [] ++ R) at p
  let w := L ++ [] ++ R
  have hleft := signedDownEntry_cutScalarQ (A) (K) s z w p tail
  have hred := signedCapKL_redBubbleSlidesLeftQ sc RD lab P Q e t 0 w hshift
  have hc (b : BubbleOrientation) (i : I) := capBlock_push_cupBubbleQ RD lab sc (A) (K) 0 w
    (signedDownEntry (A) s z) p hp tail hred (fun γ _ => hleft γ) L R (by simp [w]) b i d
  apply Submodule.mem_sup_left
  obtain ⟨ε,i⟩ := l
  cases ε
  · simpa only [CapPredecessor.cost,List.length_nil,Nat.add_zero,CapPredecessor.rows,CapPredecessor.bottom,BubbleOrientation.cupLetter,KL3.Diagram.Letter.dual_mk,Bool.not_true,Bool.not_false,List.singleton_append,w] using hc .clockwise i
  · simpa only [CapPredecessor.cost,List.length_nil,Nat.add_zero,CapPredecessor.rows,CapPredecessor.bottom,BubbleOrientation.cupLetter,KL3.Diagram.Letter.dual_mk,Bool.not_true,Bool.not_false,List.singleton_append,w] using hc .counterclockwise i

end Categorification.Stendhal.DoubleDiagram

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CLQ.CyclicDown
import Categorification.WeightedKLR.RedStrands.BlackModuleAdjunctionQ
import Categorification.WeightedKLR.RedStrands.DoubleDownBlackNewStrandQ
import Categorification.WeightedKLR.Rigidity.CupCapProp721TraceCyclicAction

/-!
# The dot of the completed black action is cyclic

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, Theorems
4.28 and 4.31, as used in §7.3, proof of Proposition 7.21. The downward dot of Cautis–Lauda's
`U_Q(g)` (arXiv:1111.1431v3, Definition 1.1, `r = 1`) is cyclic for the biadjunction of the
downward strand (`CLQ.downdot_isCyclic`). Its image under the completed black action
(`blackActionCompletedQ`) is the completion of the action `blackMapQ` of the dot `dnDotQ`
(`DoubleDiagram.blackActionCompletedQ_map₂_downStrandDotQ`), and it is cyclic for the two
adjunctions `blackCompletedAdjunctionQ`, `blackCompletedAdjunctionOpQ` between the completed
downward and upward strands (`DoubleDiagram.blackCompleted_dot_isCyclicQ`). This is the
hypothesis of `KLR.Diagram.MatEnd.resIndTrace_cyclic` for the trace of Theorem 4.31.

## Main definitions

* `DoubleDiagram.downStrandDotQ`: the dot on the downward strand, as a 2-morphism of the
  bicategory of `U_Q(g)`.

## Main results

* `DoubleDiagram.downStrandDotQ_isCyclic`: it is cyclic for the biadjunction of the strand.
* `DoubleDiagram.blackActionCompletedQ_map₂_downStrandDotQ`: its image under the completed
  black action is `completionMap₂ (blackMapQ P hP h h (dnDotQ i μ))`.
* `DoubleDiagram.blackCompleted_dot_isCyclicQ`: that image is cyclic for the completed
  adjunctions.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory CategoryTheory.Idempotents QuantumGroup QuantumGroup.UDot StringDiagrams
  KLR TwoRep KL3.Diagram Diagrams.BicatInterp

universe w u v

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}} {k : Type w} [CommRing k]
  {sc : KL3.Diagram.CL.CLScalars C k}

/-- Conjugating a conjugate by `eqToHom` back. -/
theorem eqToHom_conj_conj_self {D : Type*} [Category D] {a b : D} (e : a = b) (x : b ⟶ b) :
    eqToHom e.symm ≫ (eqToHom e ≫ x ≫ eqToHom e.symm) ≫ eqToHom e = x := by
  subst e; simp

/-- Conjugating by `eqToHom` of a loop. -/
theorem eqToHom_conj_self {D : Type*} [Category D] {a : D} (e : a = a) (x : a ⟶ a) :
    eqToHom e ≫ x ≫ eqToHom e.symm = x := by
  simp

/-- **The dot on the downward strand** `F_i 1_μ` of `U_Q(g)`, as a 2-morphism of its
bicategory: `dnDotQ` read on the boundary of `downStrandHomQ`. -/
def downStrandDotQ (i : I) {μ ν : X} (h : wt RD μ [(false, i)] = ν) :
    downStrandHomQ (k := k) (sc := sc) i h ⟶ downStrandHomQ (k := k) (sc := sc) i h :=
  show (CLQ.pres RD k sc).obj (downStrandHomQ (k := k) (sc := sc) i h).obj ⟶
    (CLQ.pres RD k sc).obj (downStrandHomQ (k := k) (sc := sc) i h).obj from
  eqToHom (congrArg (CLQ.pres RD k sc).obj (homObj_eqQ (downStrandHomQ i h))) ≫
    (dnDotQ i μ : (CLQ.pres RD k sc).obj (ob RD μ [dn i]) ⟶ _) ≫
      eqToHom (congrArg (CLQ.pres RD k sc).obj (homObj_eqQ (downStrandHomQ i h))).symm

theorem homTrQ_downStrandDotQ (i : I) {μ ν : X} (h : wt RD μ [(false, i)] = ν) :
    homTrQ (downStrandDotQ (k := k) (sc := sc) i h) = dnDotQ i μ := by
  exact eqToHom_conj_conj_self (D := (CLQ.pres RD k sc).Presented)
    (congrArg (CLQ.pres RD k sc).obj (homObj_eqQ (downStrandHomQ i h))) (dnDotQ i μ)

/-- **The downward dot is cyclic for the biadjunction of the downward strand** of `U_Q(g)`
(Cautis–Lauda, arXiv:1111.1431v3, Definition 1.1, `eq_cyclic_dot`). -/
theorem downStrandDotQ_isCyclic (i : I) {μ ν : X} (h : wt RD μ [(false, i)] = ν) :
    Biadjunction.IsCyclic (CLQ.biadjColour RD k sc (downStrandHomQ i h) ⟨dn i, μ⟩ rfl)
      (CLQ.biadjColour RD k sc (downStrandHomQ i h) ⟨dn i, μ⟩ rfl)
      (downStrandDotQ (k := k) (sc := sc) i h) := by
  subst h
  have hg := genValid_downdot RD i μ
  have hc := (Presentation.isCyclic_biadj_iff_single (CLQ.biadjColour RD k sc)
    (c := ⟨dn i, μ⟩) (c' := ⟨dn i, μ⟩) rfl rfl _).1 (CLQ.downdot_isCyclic RD k sc i μ hg)
  have he : downStrandDotQ (k := k) (sc := sc) i (rfl : wt RD μ [(false, i)] = _) =
      (CLQ.pres RD k sc).gen2 _ hg := by
    refine (eqToHom_conj_self (D := (CLQ.pres RD k sc).Presented) _ (dnDotQ i μ)).trans ?_
    exact (CLQ.pres RD k sc).diag_eq_of_layers_eq rfl
  rw [he]
  exact hc

variable (P : Presentation (signature RD (fun r => (Λ r).val)) k)
  (hP : ∀ r : (CLQ.pres RD k sc).Rel,
    P.lin (blackMirrorLinear RD (fun r => (Λ r).val) ((CLQ.pres RD k sc).rel r)) = 0)

/-- **The completed black action of the downward dot** (Webster, arXiv:1309.3796v3,
Theorem 4.28): its image under `blackActionCompletedQ` is the completion of the action of the
Cautis–Lauda dot `dnDotQ`. -/
theorem blackActionCompletedQ_map₂_downStrandDotQ (i : I) {μ ν : X}
    (h : wt RD μ [(false, i)] = ν) :
    ((blackActionCompletedQ sc P hP).map₂ (f := RevBicat.of (downStrandHomQ i h))
        (g := RevBicat.of (downStrandHomQ i h)) (downStrandDotQ (k := k) i h)).toNatTrans =
      completionMap₂ (blackMapQ P hP h h (dnDotQ i μ)) := by
  change completionMap₂ (blackMapQ P hP _ _ (homTrQ (downStrandDotQ (k := k) i h))) = _
  rw [homTrQ_downStrandDotQ]

/-- **The completed black-action dot is cyclic** (Webster, arXiv:1309.3796v3, Theorems 4.28 and
4.31): the conjugate along `Fᵢ ⊣ Eᵢ` (`blackCompletedAdjunctionQ`) of the completed dot on the
downward strand, conjugated back along `Eᵢ ⊣ Fᵢ` (`blackCompletedAdjunctionOpQ`), is the dot
again. -/
theorem blackCompleted_dot_isCyclicQ (i : I) {μ ν : X} (h : wt RD μ [(false, i)] = ν)
    (h' : wt RD ν [(true, i)] = μ) :
    conjugateEquiv (blackCompletedAdjunctionOpQ P hP i h h')
        (blackCompletedAdjunctionOpQ P hP i h h')
        (conjugateEquiv (blackCompletedAdjunctionQ P hP i h h')
          (blackCompletedAdjunctionQ P hP i h h')
          (completionMap₂ (blackMapQ P hP h h (dnDotQ i μ)))) =
      completionMap₂ (blackMapQ P hP h h (dnDotQ i μ)) := by
  have hc := Stendhal.CupCap.isCyclic_map_ofCat (blackActionCompletedQ sc P hP)
    (RevBicat.adjunction (CLQ.biadjColour RD k sc (downStrandHomQ i h) ⟨dn i, μ⟩ rfl).right)
    (RevBicat.adjunction (CLQ.biadjColour RD k sc (downStrandHomQ i h) ⟨dn i, μ⟩ rfl).left)
    (downStrandDotQ (k := k) i h)
    (Stendhal.CupCap.isCyclic_rev_of_biadjunction _ _ (downStrandDotQ_isCyclic i h))
  rw [blackActionCompletedQ_map₂_downStrandDotQ] at hc
  exact hc

end Categorification.Stendhal.DoubleDiagram

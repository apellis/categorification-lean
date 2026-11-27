/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleBlackActionHorizontal
import Categorification.WeightedKLR.RedStrands.DoubleBlackActionCompQ
import Categorification.WeightedKLR.RedStrands.DoubleBlackPresentationQ

/-!
# Horizontal composition and the black action

Webster, arXiv:1309.3796v3, §4.5, Theorem 4.28. Reflection reverses the order of
1-morphisms: a Khovanov–Lauda diagram whiskered on the right by `c` reflects to the reflected
diagram whiskered on the left by the reflection of `c`, and conversely. This file records these
two identities for the reflection functor into a signed presentation.

This is the version of `DoubleBlackActionHorizontal` in which the black strands carry the relations of
Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, Definition 1.1, `r = 1`; `CLQ.pres RD k sc`) instead
of the KL III relations. Each declaration carries the suffix `Q`.
-/

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe u v

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}} {k : Type*} [CommRing k] {sc : KL3.Diagram.CL.CLScalars C k}
  (P : Presentation (signature RD (fun r => (Λ r).val)) k)

variable (hP : ∀ r : (CLQ.pres RD k sc).Rel,
  P.lin (blackMirrorLinear RD (fun r => (Λ r).val) ((CLQ.pres RD k sc).rel r)) = 0)

/-- Reflection sends right whiskering of black Khovanov–Lauda diagrams to left whiskering. -/
theorem blackMirrorInto_wRAtQ {a b c : Obj (psig RD)} {r : X}
    (hac : a.Composable c) (hbc : b.Composable c)
    (ψ : (CLQ.pres RD k sc).obj a ⟶ (CLQ.pres RD k sc).obj b) (ha : a.start = r) (hb : b.start = r) :
    (blackMirrorIntoOf RD (fun r => (Λ r).val) (CLQ.pres RD k sc) (clqPres_wfDomQ RD k sc) P hP).map ((CLQ.pres RD k sc).wRAt r ψ c ha hb) =
      eqToHom (congrArg P.obj (mirror_tensor hac.endR_eq)) ≫
        P.wL ((blackMirror RD (fun r => (Λ r).val)).obj c)
          ((blackMirrorIntoOf RD (fun r => (Λ r).val) (CLQ.pres RD k sc) (clqPres_wfDomQ RD k sc) P hP).map ψ) ≫
          eqToHom (congrArg P.obj (mirror_tensor hbc.endR_eq)).symm := by
  by_cases hne : Nonempty (a ⟶ b)
  · have hw : a.WhiskerOK (Obj.nil r) c.word :=
      ⟨trivial, ha.symm, hac.endR_eq ▸ hac.right_wf⟩
    have hl : (blackMirror RD (fun r => (Λ r).val)).leftObj a c.word =
        (blackMirror RD (fun r => (Λ r).val)).obj c := by
      apply Obj.ext
      · show (blackMirror RD (fun r => (Λ r).val)).region ((psig RD).endR a.endR c.word) =
          (blackMirror RD (fun r => (Λ r).val)).region c.endR
        rw [hac.endR_eq]; rfl
      · rfl
    simp only [Presentation.wRAt, Presentation.wL, Functor.map_comp, eqToHom_map]
    unfold blackMirrorIntoOf
    erw [SigMirror.lift_whisk _ _ _ _ _ hac.left_wf hw hne, whisk_congr_left P _ hl]
    exact eqToHom_sandwich_three (D := P.Presented) _ _ _ _ _ _ _ _ _ _ _
  · obtain ⟨f, rfl⟩ := (CLQ.pres RD k sc).lin_surjective ψ
    have : IsEmpty (a ⟶ b) := not_nonempty_iff.mp hne
    rw [linDiagram_eq_zero_of_isEmpty f]
    erw [Presentation.lin_zero, Presentation.wRAt_zero, Functor.map_zero, Functor.map_zero,
      Presentation.wL_zero]
    simp only [Limits.zero_comp, Limits.comp_zero]
    rfl

/-- Reflection sends left whiskering of black Khovanov–Lauda diagrams to right whiskering. -/
theorem blackMirrorInto_wLQ {a b c : Obj (psig RD)}
    (hca : c.Composable a) (hcb : c.Composable b) (hab : a.endR = b.endR)
    (ψ : (CLQ.pres RD k sc).obj a ⟶ (CLQ.pres RD k sc).obj b) :
    (blackMirrorIntoOf RD (fun r => (Λ r).val) (CLQ.pres RD k sc) (clqPres_wfDomQ RD k sc) P hP).map ((CLQ.pres RD k sc).wL c ψ) =
      eqToHom (congrArg P.obj (mirror_tensor hca.endR_eq)) ≫
        P.wRAt ((blackMirror RD (fun r => (Λ r).val)).obj a).start
          ((blackMirrorIntoOf RD (fun r => (Λ r).val) (CLQ.pres RD k sc) (clqPres_wfDomQ RD k sc) P hP).map ψ)
          ((blackMirror RD (fun r => (Λ r).val)).obj c) rfl
          (by show (blackMirror RD (fun r => (Λ r).val)).region b.endR = _; rw [← hab]; rfl) ≫
          eqToHom (congrArg P.obj (mirror_tensor hcb.endR_eq)).symm := by
  by_cases hne : Nonempty (a ⟶ b)
  · have hw : a.WhiskerOK c [] := ⟨hca.left_wf, hca.endR_eq, trivial⟩
    simp only [Presentation.wRAt, Presentation.wL, Functor.map_comp, eqToHom_map]
    unfold blackMirrorIntoOf
    erw [SigMirror.lift_whisk _ _ _ _ _ hca.right_wf hw hne]
    exact eqToHom_sandwich_two (D := P.Presented) _ _ _ _ _ _ _ _ _
  · obtain ⟨f, rfl⟩ := (CLQ.pres RD k sc).lin_surjective ψ
    have : IsEmpty (a ⟶ b) := not_nonempty_iff.mp hne
    rw [linDiagram_eq_zero_of_isEmpty f]
    erw [Presentation.lin_zero, Presentation.wL_zero, Functor.map_zero, Functor.map_zero,
      Presentation.wRAt_zero]
    erw [Limits.zero_comp, Limits.comp_zero]
    rfl

end Categorification.Stendhal.DoubleDiagram

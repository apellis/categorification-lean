/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleBlackActionWhisker
import Categorification.WeightedKLR.RedStrands.DoubleBlackActionHorizontalQ
import Categorification.WeightedKLR.RedStrands.DoubleRightWhiskerHorizontal

/-!
# Whiskered Khovanov–Lauda diagrams and the black action

Webster, arXiv:1309.3796v3, §4.5, Theorem 4.28. Khovanov–Lauda words act on the violating
quotients by right whiskering with their mirror words, and the action of a concatenation
`s ++ t` is the action of `t` followed by that of `s`. This file shows that horizontal
composites of Khovanov–Lauda diagrams act by the corresponding whiskered natural
transformations: `1_s ⊗ ψ` acts by the action of `ψ` followed by the action of `s`, and
`χ ⊗ 1_t` acts by the action of `t` followed by the action of `χ`.

This is the version of `DoubleBlackActionWhisker` in which the black strands carry the relations of
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

section Left

variable {μ ν₁ : X} {s t t' : List (Letter I)} (ht : wt RD μ t = ν₁) (ht' : wt RD μ t' = ν₁)
  (ψ : (CLQ.pres RD k sc).obj (ob RD μ t) ⟶ (CLQ.pres RD k sc).obj (ob RD μ t'))

/-- The Khovanov–Lauda diagram `1_s ⊗ ψ`. -/
def wLObQ (s : List (Letter I)) : (CLQ.pres RD k sc).obj (ob RD μ (s ++ t)) ⟶
    (CLQ.pres RD k sc).obj (ob RD μ (s ++ t')) :=
  eqToHom (congrArg (CLQ.pres RD k sc).obj (ob_tensor_ob s t ht).symm) ≫
    (CLQ.pres RD k sc).wL (ob RD ν₁ s) ψ ≫ eqToHom (congrArg (CLQ.pres RD k sc).obj (ob_tensor_ob s t' ht'))

/-- The mirror image of `1_s ⊗ ψ` is the mirror image of `ψ` with the mirror word of `s`
placed to its right. -/
theorem blackMirrorHom_wLObQ :
    blackMirrorHomQ P hP (wLObQ ht ht' ψ s) =
      eqToHom (congrArg P.obj (congrArg (obj RD (fun r => (Λ r).val) μ)
          (blackWord_append' s t))) ≫
        wRWord P ((endWeight_blackWord RD _ μ t).trans ht)
          ((endWeight_blackWord RD _ μ t').trans ht') (v₂ := blackWord s)
          (blackMirrorHomQ P hP ψ) ≫
          eqToHom (congrArg P.obj (congrArg (obj RD (fun r => (Λ r).val) μ)
            (blackWord_append' s t').symm)) := by
  have hca : (ob RD ν₁ s).Composable (ob RD μ t) :=
    ⟨ob_wf RD _ _, (ob_endR RD ν₁ s).trans ht.symm, ob_wf RD _ _⟩
  have hcb : (ob RD ν₁ s).Composable (ob RD μ t') :=
    ⟨ob_wf RD _ _, (ob_endR RD ν₁ s).trans ht'.symm, ob_wf RD _ _⟩
  simp only [blackMirrorHomQ, conjMap, wRWord, wLObQ]
  erw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map,
    blackMirrorInto_wLQ P hP hca hcb ((ob_endR RD μ t).trans (ob_endR RD μ t').symm) ψ]
  have h₁ := (endWeight_blackWord RD (fun r => (Λ r).val) μ t).trans ht
  have h₁' := (endWeight_blackWord RD (fun r => (Λ r).val) μ t').trans ht'
  have hok : (signature RD (fun r => (Λ r).val)).ok
      ((blackMirror RD (fun r => (Λ r).val)).obj (ob RD μ t')).endR
      (obj RD (fun r => (Λ r).val) ν₁ (blackWord s)).word := by
    rw [blackMirror_obj_ob]
    exact (composable_append (Λ := Λ) (blackWord t') (blackWord s) h₁').ok_endR
  erw [wRAt_congr_region P _ (ob_endR RD μ t),
    wRAt_congr_obj P _ (blackMirror_obj_ob RD (fun r => (Λ r).val) ν₁ s),
    P.wRAt_comp (r := μ) rfl (ob_endR RD μ t) rfl,
    P.wRAt_comp (r := μ) (ob_endR RD μ t) (ob_endR RD μ t') rfl,
    P.wRAt_eqToHom _ _ (composable_append (Λ := Λ) (blackWord t) (blackWord s) h₁).ok_endR,
    P.wRAt_eqToHom _ _ hok]
  exact eqToHom_sandwich_four (D := P.Presented) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- A diagram whiskered on the left by `s` acts by the right whiskering of its action by the
action of `s` (Webster, arXiv:1309.3796v3, §4.5, Theorem 4.28). -/
theorem blackMap_wLObQ {ν₂ : X} (hs : wt RD ν₁ s = ν₂) (hst : wt RD μ (s ++ t) = ν₂)
    (hst' : wt RD μ (s ++ t') = ν₂) :
    blackMapQ P hP hst hst' (wLObQ ht ht' ψ s) =
      (blackActAppend P s t ht hs hst).hom ≫
        Functor.whiskerRight (blackMapQ P hP ht ht' ψ) (blackAct P s hs) ≫
          (blackActAppend P s t' ht' hs hst').inv := by
  have h₁ := (endWeight_blackWord RD (fun r => (Λ r).val) μ t).trans ht
  have h₁' := (endWeight_blackWord RD (fun r => (Λ r).val) μ t').trans ht'
  have h₂ := (endWeight_blackWord RD (fun r => (Λ r).val) ν₁ s).trans hs
  rw [blackMapQ, blackMirrorHom_wLObQ,
    violatingWhiskerLeft_congr P (blackWord_append' s t) (blackWord_append' s t') _ _
      (redFree_append (blackWord_redFree t) (blackWord_redFree s))
      (redFree_append (blackWord_redFree t') (blackWord_redFree s)) _ _
      (endWeight_append_of_eq h₁ h₂) (endWeight_append_of_eq h₁' h₂),
    violatingWhiskerLeft_wRWord P (blackWord_redFree t) (blackWord_redFree t')
      (blackWord_redFree s) h₁ h₁' h₂]
  simp only [blackActAppend, blackMapQ, blackAct, Iso.trans_hom, Iso.trans_inv, eqToIso.hom,
    eqToIso.inv, Category.assoc]

end Left

section Right

variable {μ ν₁ ν₂ : X} {s s' t : List (Letter I)} (ht : wt RD μ t = ν₁)
  (hs : wt RD ν₁ s = ν₂) (hs' : wt RD ν₁ s' = ν₂)
  (χ : (CLQ.pres RD k sc).obj (ob RD ν₁ s) ⟶ (CLQ.pres RD k sc).obj (ob RD ν₁ s'))

/-- The diagram `χ ⊗ 1_t`: `χ` placed to the left of the identity diagram of `t`. -/
def wRObQ (t : List (Letter I)) (ht : wt RD μ t = ν₁) :
    (CLQ.pres RD k sc).obj (ob RD μ (s ++ t)) ⟶ (CLQ.pres RD k sc).obj (ob RD μ (s' ++ t)) :=
  eqToHom (congrArg (CLQ.pres RD k sc).obj (ob_tensor_ob s t ht).symm) ≫
    (CLQ.pres RD k sc).wRAt ν₂ χ (ob RD μ t) hs hs' ≫
      eqToHom (congrArg (CLQ.pres RD k sc).obj (ob_tensor_ob s' t ht))

/-- Reflection sends `χ ⊗ 1_t` to the mirror of `χ` placed to the right of the mirror word
of `t` (Webster, arXiv:1309.3796v3, §4.5, Theorem 4.28). -/
theorem blackMirrorHom_wRObQ :
    blackMirrorHomQ P hP (wRObQ hs hs' χ t ht) =
      eqToHom (congrArg P.obj
          (congrArg (obj RD (fun r => (Λ r).val) μ) (blackWord_append' s t))) ≫
        wLWord P ((endWeight_blackWord RD _ μ t).trans ht) (v₂ := blackWord s)
            (v₂' := blackWord s') (blackMirrorHomQ P hP χ) ≫
          eqToHom (congrArg P.obj
            (congrArg (obj RD (fun r => (Λ r).val) μ) (blackWord_append' s' t)).symm) := by
  have hac : (ob RD ν₁ s).Composable (ob RD μ t) :=
    ⟨ob_wf RD _ _, (ob_endR RD ν₁ s).trans ht.symm, ob_wf RD _ _⟩
  have hbc : (ob RD ν₁ s').Composable (ob RD μ t) :=
    ⟨ob_wf RD _ _, (ob_endR RD ν₁ s').trans ht.symm, ob_wf RD _ _⟩
  have h₁ := (endWeight_blackWord RD (fun r => (Λ r).val) μ t).trans ht
  simp only [blackMirrorHomQ, conjMap, wLWord, wRObQ]
  erw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map,
    blackMirrorInto_wRAtQ P hP hac hbc χ hs hs',
    wL_congr_obj P _ (blackMirror_obj_ob RD (fun r => (Λ r).val) μ t)]
  have hc' : (obj RD (fun r => (Λ r).val) μ (blackWord t)).Composable
      ((blackMirror RD (fun r => (Λ r).val)).obj (ob RD ν₁ s')) := by
    rw [blackMirror_obj_ob]; exact composable_append (Λ := Λ) _ _ h₁
  erw [P.wL_comp, P.wL_comp,
    P.wL_eqToHom_of_composable _ (composable_append (Λ := Λ) _ (blackWord s) h₁),
    P.wL_eqToHom_of_composable _ hc']
  exact eqToHom_sandwich_four (D := P.Presented) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- A diagram whiskered on the right by `t` acts by the left whiskering of its action by the
action of `t` (Webster, arXiv:1309.3796v3, §4.5, Theorem 4.28). -/
theorem blackMap_wRObQ (hst : wt RD μ (s ++ t) = ν₂) (hs't : wt RD μ (s' ++ t) = ν₂) :
    blackMapQ P hP hst hs't (wRObQ hs hs' χ t ht) =
      (blackActAppend P s t ht hs hst).hom ≫
        Functor.whiskerLeft (blackAct P t ht) (blackMapQ P hP hs hs' χ) ≫
          (blackActAppend P s' t ht hs' hs't).inv := by
  have h₁ := (endWeight_blackWord RD (fun r => (Λ r).val) μ t).trans ht
  have h₂ := (endWeight_blackWord RD (fun r => (Λ r).val) ν₁ s).trans hs
  have h₂' := (endWeight_blackWord RD (fun r => (Λ r).val) ν₁ s').trans hs'
  rw [blackMapQ, blackMirrorHom_wRObQ,
    violatingWhiskerLeft_congr P (blackWord_append' s t) (blackWord_append' s' t) _ _
      (redFree_append (blackWord_redFree t) (blackWord_redFree s))
      (redFree_append (blackWord_redFree t) (blackWord_redFree s')) _ _
      (endWeight_append_of_eq h₁ h₂) (endWeight_append_of_eq h₁ h₂'),
    violatingWhiskerLeft_wLWord P (blackWord_redFree t) (blackWord_redFree s)
      (blackWord_redFree s') h₁ h₂ h₂']
  simp only [blackActAppend, blackMapQ, blackAct, Iso.trans_hom, Iso.trans_inv, eqToIso.hom,
    eqToIso.inv, Category.assoc]

end Right

end Categorification.Stendhal.DoubleDiagram

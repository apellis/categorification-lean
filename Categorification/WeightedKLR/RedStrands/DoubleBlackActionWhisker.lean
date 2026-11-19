/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleBlackActionHorizontal
import Categorification.WeightedKLR.RedStrands.DoubleRightWhiskerHorizontal

/-!
# Whiskered Khovanov–Lauda diagrams and the black action

Webster, arXiv:1309.3796v3, §4.5, Theorem 4.28. Khovanov–Lauda words act on the violating
quotients by right whiskering with their mirror words, and the action of a concatenation
`s ++ t` is the action of `t` followed by that of `s`. This file shows that horizontal
composites of Khovanov–Lauda diagrams act by the corresponding whiskered natural
transformations: `1_s ⊗ ψ` acts by the action of `ψ` followed by the action of `s`, and
`χ ⊗ 1_t` acts by the action of `t` followed by the action of `χ`.
-/

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe u v

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}} {k : Type*} [CommRing k]
  (P : Presentation (signature RD (fun r => (Λ r).val)) k)

/-- Concatenation of Khovanov–Lauda words is the tensor product of their objects. -/
theorem ob_tensor_ob {μ ν : X} (s t : List (Letter I)) (ht : wt RD μ t = ν) :
    (ob RD ν s).tensor (ob RD μ t) = ob RD μ (s ++ t) := by
  subst ht
  apply Obj.ext
  · exact (wt_append RD μ s t).symm
  · exact (wd_append RD μ s t).symm

/-- Natural transformations between right whiskerings, along equalities of the words. -/
theorem violatingWhiskerLeft_congr {μ ν : X} {v v' w w' : List (DoubleStrand I ℓ)}
    (h : v = w) (h' : v' = w') (hv : RedFree v) (hv' : RedFree v') (hw : RedFree w)
    (hw' : RedFree w') (hν : endWeight RD (fun r => (Λ r).val) μ v = ν)
    (hν' : endWeight RD (fun r => (Λ r).val) μ v' = ν)
    (hμ : endWeight RD (fun r => (Λ r).val) μ w = ν)
    (hμ' : endWeight RD (fun r => (Λ r).val) μ w' = ν)
    (φ : P.obj (obj RD (fun r => (Λ r).val) μ w) ⟶ P.obj (obj RD (fun r => (Λ r).val) μ w')) :
    violatingWhiskerLeft P hv hv' hν hν'
        (eqToHom (by rw [h]) ≫ φ ≫ eqToHom (by rw [h'])) =
      eqToHom (violatingWhiskerRight_congr P h hv hw hν hμ) ≫
        violatingWhiskerLeft P hw hw' hμ hμ' φ ≫
          eqToHom (violatingWhiskerRight_congr P h' hv' hw' hν' hμ').symm := by
  subst h h'
  simp

/-- Right whiskering along an equality of the regions. -/
theorem wRAt_congr_region {S : Signature} {R : Type*} [CommRing R] (Q : Presentation S R)
    {a a' b : Obj S} {r r' : S.Region} (f : Q.obj a ⟶ Q.obj a') (h : r = r')
    (ha : a.start = r) (ha' : a'.start = r) :
    Q.wRAt r f b ha ha' = Q.wRAt r' f b (ha.trans h) (ha'.trans h) := by
  subst h; rfl

/-- Two nested composites of a morphism with transports agree. -/
theorem eqToHom_sandwich_four {D : Type*} [Category D]
    {a a₁ a₂ a₃ b c c₁ c₂ c₃ d a₄ a₅ c₄ c₅ : D} (g : b ⟶ c) (h₁ : a = a₁) (h₂ : a₁ = a₂)
    (h₃ : a₂ = a₃) (h₄ : a₃ = b) (h₅ : c = c₁) (h₆ : c₁ = c₂) (h₇ : c₂ = c₃) (h₈ : c₃ = d)
    (h₉ : a = a₄) (h₁₀ : a₄ = a₅) (h₁₁ : a₅ = b) (h₁₂ : c = c₄) (h₁₃ : c₄ = c₅)
    (h₁₄ : c₅ = d) :
    eqToHom h₁ ≫ (eqToHom h₂ ≫ (eqToHom h₃ ≫ (eqToHom h₄ ≫ g ≫ eqToHom h₅) ≫
        eqToHom h₆) ≫ eqToHom h₇) ≫ eqToHom h₈ =
      eqToHom h₉ ≫ (eqToHom h₁₀ ≫ (eqToHom h₁₁ ≫ g ≫ eqToHom h₁₂) ≫ eqToHom h₁₃) ≫
        eqToHom h₁₄ := by
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]

variable (hP : ∀ r : (pres RD k).Rel,
  P.lin (blackMirrorLinear RD (fun r => (Λ r).val) ((pres RD k).rel r)) = 0)

section Left

variable {μ ν₁ : X} {s t t' : List (Letter I)} (ht : wt RD μ t = ν₁) (ht' : wt RD μ t' = ν₁)
  (ψ : (pres RD k).obj (ob RD μ t) ⟶ (pres RD k).obj (ob RD μ t'))

/-- The Khovanov–Lauda diagram `1_s ⊗ ψ`. -/
def wLOb (s : List (Letter I)) : (pres RD k).obj (ob RD μ (s ++ t)) ⟶
    (pres RD k).obj (ob RD μ (s ++ t')) :=
  eqToHom (congrArg (pres RD k).obj (ob_tensor_ob s t ht).symm) ≫
    (pres RD k).wL (ob RD ν₁ s) ψ ≫ eqToHom (congrArg (pres RD k).obj (ob_tensor_ob s t' ht'))

/-- The mirror image of `1_s ⊗ ψ` is the mirror image of `ψ` with the mirror word of `s`
placed to its right. -/
theorem blackMirrorHom_wLOb :
    blackMirrorHom P hP (wLOb ht ht' ψ s) =
      eqToHom (congrArg P.obj (congrArg (obj RD (fun r => (Λ r).val) μ)
          (blackWord_append' s t))) ≫
        wRWord P ((endWeight_blackWord RD _ μ t).trans ht)
          ((endWeight_blackWord RD _ μ t').trans ht') (v₂ := blackWord s)
          (blackMirrorHom P hP ψ) ≫
          eqToHom (congrArg P.obj (congrArg (obj RD (fun r => (Λ r).val) μ)
            (blackWord_append' s t').symm)) := by
  have hca : (ob RD ν₁ s).Composable (ob RD μ t) :=
    ⟨ob_wf RD _ _, (ob_endR RD ν₁ s).trans ht.symm, ob_wf RD _ _⟩
  have hcb : (ob RD ν₁ s).Composable (ob RD μ t') :=
    ⟨ob_wf RD _ _, (ob_endR RD ν₁ s).trans ht'.symm, ob_wf RD _ _⟩
  simp only [blackMirrorHom, conjMap, wRWord, wLOb]
  erw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map,
    blackMirrorInto_wL P hP hca hcb ((ob_endR RD μ t).trans (ob_endR RD μ t').symm) ψ]
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
theorem blackMap_wLOb {ν₂ : X} (hs : wt RD ν₁ s = ν₂) (hst : wt RD μ (s ++ t) = ν₂)
    (hst' : wt RD μ (s ++ t') = ν₂) :
    blackMap P hP hst hst' (wLOb ht ht' ψ s) =
      (blackActAppend P s t ht hs hst).hom ≫
        Functor.whiskerRight (blackMap P hP ht ht' ψ) (blackAct P s hs) ≫
          (blackActAppend P s t' ht' hs hst').inv := by
  have h₁ := (endWeight_blackWord RD (fun r => (Λ r).val) μ t).trans ht
  have h₁' := (endWeight_blackWord RD (fun r => (Λ r).val) μ t').trans ht'
  have h₂ := (endWeight_blackWord RD (fun r => (Λ r).val) ν₁ s).trans hs
  rw [blackMap, blackMirrorHom_wLOb,
    violatingWhiskerLeft_congr P (blackWord_append' s t) (blackWord_append' s t') _ _
      (redFree_append (blackWord_redFree t) (blackWord_redFree s))
      (redFree_append (blackWord_redFree t') (blackWord_redFree s)) _ _
      (endWeight_append_of_eq h₁ h₂) (endWeight_append_of_eq h₁' h₂),
    violatingWhiskerLeft_wRWord P (blackWord_redFree t) (blackWord_redFree t')
      (blackWord_redFree s) h₁ h₁' h₂]
  simp only [blackActAppend, blackMap, blackAct, Iso.trans_hom, Iso.trans_inv, eqToIso.hom,
    eqToIso.inv, Category.assoc]

end Left

section Right

variable {μ ν₁ ν₂ : X} {s s' t : List (Letter I)} (ht : wt RD μ t = ν₁)
  (hs : wt RD ν₁ s = ν₂) (hs' : wt RD ν₁ s' = ν₂)
  (χ : (pres RD k).obj (ob RD ν₁ s) ⟶ (pres RD k).obj (ob RD ν₁ s'))

/-- The diagram `χ ⊗ 1_t`: `χ` placed to the left of the identity diagram of `t`. -/
def wROb (t : List (Letter I)) (ht : wt RD μ t = ν₁) :
    (pres RD k).obj (ob RD μ (s ++ t)) ⟶ (pres RD k).obj (ob RD μ (s' ++ t)) :=
  eqToHom (congrArg (pres RD k).obj (ob_tensor_ob s t ht).symm) ≫
    (pres RD k).wRAt ν₂ χ (ob RD μ t) hs hs' ≫
      eqToHom (congrArg (pres RD k).obj (ob_tensor_ob s' t ht))

/-- Reflection sends `χ ⊗ 1_t` to the mirror of `χ` placed to the right of the mirror word
of `t` (Webster, arXiv:1309.3796v3, §4.5, Theorem 4.28). -/
theorem blackMirrorHom_wROb :
    blackMirrorHom P hP (wROb hs hs' χ t ht) =
      eqToHom (congrArg P.obj
          (congrArg (obj RD (fun r => (Λ r).val) μ) (blackWord_append' s t))) ≫
        wLWord P ((endWeight_blackWord RD _ μ t).trans ht) (v₂ := blackWord s)
            (v₂' := blackWord s') (blackMirrorHom P hP χ) ≫
          eqToHom (congrArg P.obj
            (congrArg (obj RD (fun r => (Λ r).val) μ) (blackWord_append' s' t)).symm) := by
  have hac : (ob RD ν₁ s).Composable (ob RD μ t) :=
    ⟨ob_wf RD _ _, (ob_endR RD ν₁ s).trans ht.symm, ob_wf RD _ _⟩
  have hbc : (ob RD ν₁ s').Composable (ob RD μ t) :=
    ⟨ob_wf RD _ _, (ob_endR RD ν₁ s').trans ht.symm, ob_wf RD _ _⟩
  have h₁ := (endWeight_blackWord RD (fun r => (Λ r).val) μ t).trans ht
  simp only [blackMirrorHom, conjMap, wLWord, wROb]
  erw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map,
    blackMirrorInto_wRAt P hP hac hbc χ hs hs',
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
theorem blackMap_wROb (hst : wt RD μ (s ++ t) = ν₂) (hs't : wt RD μ (s' ++ t) = ν₂) :
    blackMap P hP hst hs't (wROb hs hs' χ t ht) =
      (blackActAppend P s t ht hs hst).hom ≫
        Functor.whiskerLeft (blackAct P t ht) (blackMap P hP hs hs' χ) ≫
          (blackActAppend P s' t ht hs' hs't).inv := by
  have h₁ := (endWeight_blackWord RD (fun r => (Λ r).val) μ t).trans ht
  have h₂ := (endWeight_blackWord RD (fun r => (Λ r).val) ν₁ s).trans hs
  have h₂' := (endWeight_blackWord RD (fun r => (Λ r).val) ν₁ s').trans hs'
  rw [blackMap, blackMirrorHom_wROb,
    violatingWhiskerLeft_congr P (blackWord_append' s t) (blackWord_append' s' t) _ _
      (redFree_append (blackWord_redFree t) (blackWord_redFree s))
      (redFree_append (blackWord_redFree t) (blackWord_redFree s')) _ _
      (endWeight_append_of_eq h₁ h₂) (endWeight_append_of_eq h₁ h₂'),
    violatingWhiskerLeft_wLWord P (blackWord_redFree t) (blackWord_redFree s)
      (blackWord_redFree s') h₁ h₂ h₂']
  simp only [blackActAppend, blackMap, blackAct, Iso.trans_hom, Iso.trans_inv, eqToIso.hom,
    eqToIso.inv, Category.assoc]

end Right

end Categorification.Stendhal.DoubleDiagram

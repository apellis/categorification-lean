/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleRightWhiskerComp

/-!
# Horizontal composites of whiskered diagrams

Webster, arXiv:1309.3796v3, §4.5, before Theorem 4.28. A diagram `φ₂` between red-free words
`v₂, v₂'`, placed to the right of a word `v₁`, acts on the boundary categories by the
natural transformation of `φ₂` whiskered by the right whiskering along `v₁`. This file proves
this compatibility of the right action with the horizontal composition of diagrams.
-/

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

variable {I : Type*} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type*}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}} {k : Type*} [CommRing k]
  (P : Presentation (signature RD (fun r => (Λ r).val)) k)

/-- Left whiskering along an equality of the whiskering objects. -/
theorem wL_congr_obj {a a' : Obj (signature RD (fun r => (Λ r).val))} {b b' : Obj _}
    (g : P.obj b ⟶ P.obj b') (h : a = a') :
    P.wL a g = eqToHom (by rw [h]) ≫ P.wL a' g ≫ eqToHom (by rw [h]) := by
  subst h; simp

/-- Two composites of a morphism with transports agree. -/
theorem eqToHom_sandwich_nested {D : Type*} [Category D] {a a₁ b c c₁ d a₂ a₃ a₄ c₂ c₃ c₄ : D}
    (g : b ⟶ c) (h₁ : a = a₁) (h₂ : a₁ = b) (h₃ : c = c₁) (h₄ : c₁ = d) (h₅ : a = a₂)
    (h₆ : a₂ = a₃) (h₇ : a₃ = a₄) (h₈ : a₄ = b) (h₉ : c = c₂) (h₁₀ : c₂ = c₃) (h₁₁ : c₃ = c₄)
    (h₁₂ : c₄ = d) :
    eqToHom h₁ ≫ (eqToHom h₂ ≫ g ≫ eqToHom h₃) ≫ eqToHom h₄ =
      eqToHom h₅ ≫ (eqToHom h₆ ≫ (eqToHom h₇ ≫ (eqToHom h₈ ≫ g ≫ eqToHom h₉) ≫
        eqToHom h₁₀) ≫ eqToHom h₁₁) ≫ eqToHom h₁₂ := by
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]

@[simp] theorem whiskerRightAppend_inv_app_hom {μ ν₁ ν₂ : X} {v₁ v₂ : List (DoubleStrand I ℓ)}
    (hv₁ : RedFree v₁) (hv₂ : RedFree v₂) (h₁ : endWeight RD (fun r => (Λ r).val) μ v₁ = ν₁)
    (h₂ : endWeight RD (fun r => (Λ r).val) ν₁ v₂ = ν₂) (x : BoundaryCategory P μ) :
    ((whiskerRightAppend P hv₁ hv₂ h₁ h₂).inv.app x).hom =
      eqToHom (congrArg (tripleObj P) (appendRight_append hv₁ hv₂ h₁ h₂ x)).symm :=
  rfl

@[simp] theorem whiskerRight_map_hom {μ ν : X} {v : List (DoubleStrand I ℓ)} (hv : RedFree v)
    (hν : endWeight RD (fun r => (Λ r).val) μ v = ν) {x y : BoundaryCategory P μ} (f : x ⟶ y) :
    ((whiskerRight P v hv hν).map f).hom =
      eqToHom (tripleObj_appendRight P v hv hν x) ≫
        P.wRAt (0 : X) f.hom (obj RD (fun r => (Λ r).val) μ v) rfl rfl ≫
          eqToHom (tripleObj_appendRight P v hv hν y).symm :=
  rfl

section Left

variable {μ ν₁ ν₂ : X} {v₁ v₂ v₂' : List (DoubleStrand I ℓ)} (hv₁ : RedFree v₁)
  (hv₂ : RedFree v₂) (hv₂' : RedFree v₂') (h₁ : endWeight RD (fun r => (Λ r).val) μ v₁ = ν₁)
  (h₂ : endWeight RD (fun r => (Λ r).val) ν₁ v₂ = ν₂)
  (h₂' : endWeight RD (fun r => (Λ r).val) ν₁ v₂' = ν₂)
  (φ₂ : P.obj (obj RD (fun r => (Λ r).val) ν₁ v₂) ⟶
    P.obj (obj RD (fun r => (Λ r).val) ν₁ v₂'))

/-- A diagram placed to the right of the word `v₁`. -/
def wLWord : P.obj (obj RD (fun r => (Λ r).val) μ (v₁ ++ v₂)) ⟶
    P.obj (obj RD (fun r => (Λ r).val) μ (v₁ ++ v₂')) :=
  eqToHom (congrArg P.obj (obj_tensor_obj_of_eq h₁ v₂).symm) ≫
    P.wL (obj RD (fun r => (Λ r).val) μ v₁) φ₂ ≫
      eqToHom (congrArg P.obj (obj_tensor_obj_of_eq h₁ v₂'))

/-- The diagram `1_{v₁} ⊗ φ₂` acts by the natural transformation of `φ₂` whiskered by the
right whiskering along `v₁` (Webster, arXiv:1309.3796v3, §4.5, before Theorem 4.28). -/
theorem whiskerLeft_wLWord :
    whiskerLeft P (redFree_append hv₁ hv₂) (redFree_append hv₁ hv₂')
        (endWeight_append_of_eq h₁ h₂) (endWeight_append_of_eq h₁ h₂') (wLWord P h₁ φ₂) =
      (whiskerRightAppend P hv₁ hv₂ h₁ h₂).hom ≫
        Functor.whiskerLeft (whiskerRight P v₁ hv₁ h₁) (whiskerLeft P hv₂ hv₂' h₂ h₂' φ₂) ≫
          (whiskerRightAppend P hv₁ hv₂' h₁ h₂').inv := by
  ext x
  have hc := composable P x v₁
  have hc₂ := composable_append (Λ := Λ) v₁ v₂ h₁
  have hC := wL_congr_obj P φ₂ (obj_tensor_obj_of_eq (Λ := Λ) (endWeight_word x) v₁).symm
  rw [P.wL_tensor hc hc₂ φ₂] at hC
  simp only [whiskerLeft_app_hom, wLWord, NatTrans.comp_app, Functor.whiskerLeft_app,
    InducedCategory.comp_hom, whiskerRightAppend_hom_app_hom, whiskerRightAppend_inv_app_hom]
  erw [hC]
  have hc' : (obj RD (fun r => (Λ r).val) 0 x.val.word).Composable
      ((obj RD (fun r => (Λ r).val) μ v₁).tensor (obj RD (fun r => (Λ r).val) ν₁ v₂')) :=
    (obj_tensor_obj_of_eq h₁ v₂') ▸ composable P x (v₁ ++ v₂')
  rw [P.wL_comp, P.wL_comp, P.wL_eqToHom_of_composable _ (composable P x (v₁ ++ v₂)),
    P.wL_eqToHom_of_composable _ hc']
  exact eqToHom_sandwich_nested (D := P.Presented) _ _ _ _ _ _ _ _ _ _ _ _ _

/-- `whiskerLeft_wLWord` on the violating quotients. -/
theorem violatingWhiskerLeft_wLWord :
    violatingWhiskerLeft P (redFree_append hv₁ hv₂) (redFree_append hv₁ hv₂')
        (endWeight_append_of_eq h₁ h₂) (endWeight_append_of_eq h₁ h₂') (wLWord P h₁ φ₂) =
      (violatingWhiskerRightAppend P hv₁ hv₂ h₁ h₂).hom ≫
        Functor.whiskerLeft (violatingWhiskerRight P v₁ hv₁ h₁)
          (violatingWhiskerLeft P hv₂ hv₂' h₂ h₂' φ₂) ≫
          (violatingWhiskerRightAppend P hv₁ hv₂' h₁ h₂').inv := by
  apply CategoryTheory.Quotient.natTrans_ext
  ext x
  have h := congrArg (fun τ => (violatingFunctor P ν₂).map (τ.app x))
    (whiskerLeft_wLWord P hv₁ hv₂ hv₂' h₁ h₂ h₂' φ₂)
  simp only [NatTrans.comp_app, Functor.map_comp] at h
  exact h

end Left

section Right

variable {μ ν₁ ν₂ : X} {v₁ v₁' v₂ : List (DoubleStrand I ℓ)} (hv₁ : RedFree v₁)
  (hv₁' : RedFree v₁') (hv₂ : RedFree v₂) (h₁ : endWeight RD (fun r => (Λ r).val) μ v₁ = ν₁)
  (h₁' : endWeight RD (fun r => (Λ r).val) μ v₁' = ν₁)
  (h₂ : endWeight RD (fun r => (Λ r).val) ν₁ v₂ = ν₂)
  (φ₁ : P.obj (obj RD (fun r => (Λ r).val) μ v₁) ⟶
    P.obj (obj RD (fun r => (Λ r).val) μ v₁'))

/-- A diagram placed to the left of the word `v₂`. -/
def wRWord : P.obj (obj RD (fun r => (Λ r).val) μ (v₁ ++ v₂)) ⟶
    P.obj (obj RD (fun r => (Λ r).val) μ (v₁' ++ v₂)) :=
  eqToHom (congrArg P.obj (obj_tensor_obj_of_eq h₁ v₂).symm) ≫
    P.wRAt μ φ₁ (obj RD (fun r => (Λ r).val) ν₁ v₂) rfl rfl ≫
      eqToHom (congrArg P.obj (obj_tensor_obj_of_eq h₁' v₂))

/-- The diagram `φ₁ ⊗ 1_{v₂}` acts by the natural transformation of `φ₁` whiskered by the
right whiskering along `v₂` (Webster, arXiv:1309.3796v3, §4.5, before Theorem 4.28). -/
theorem whiskerLeft_wRWord :
    whiskerLeft P (redFree_append hv₁ hv₂) (redFree_append hv₁' hv₂)
        (endWeight_append_of_eq h₁ h₂) (endWeight_append_of_eq h₁' h₂) (wRWord P h₁ h₁' φ₁) =
      (whiskerRightAppend P hv₁ hv₂ h₁ h₂).hom ≫
        Functor.whiskerRight (whiskerLeft P hv₁ hv₁' h₁ h₁' φ₁) (whiskerRight P v₂ hv₂ h₂) ≫
          (whiskerRightAppend P hv₁' hv₂ h₁' h₂).inv := by
  ext x
  have hc := composable P x v₁
  have hc₂ := composable_append (Λ := Λ) v₁ v₂ h₁
  have hc₂' := composable_append (Λ := Λ) v₁' v₂ h₁'
  simp only [whiskerLeft_app_hom, wRWord, NatTrans.comp_app, Functor.whiskerRight_app,
    InducedCategory.comp_hom, whiskerRightAppend_hom_app_hom, whiskerRightAppend_inv_app_hom,
    whiskerRight_map_hom]
  have hd : (obj RD (fun r => (Λ r).val) 0 x.val.word).Composable
      ((obj RD (fun r => (Λ r).val) μ v₁').tensor (obj RD (fun r => (Λ r).val) ν₁ v₂)) :=
    (obj_tensor_obj_of_eq h₁' v₂) ▸ composable P x (v₁' ++ v₂)
  rw [P.wL_comp, P.wL_comp, P.wL_eqToHom_of_composable _ (composable P x (v₁ ++ v₂)),
    P.wL_eqToHom_of_composable _ hd]
  erw [P.wRAt_comp (r := (0 : X)) rfl rfl rfl, P.wRAt_comp (r := (0 : X)) rfl rfl rfl,
    P.wRAt_eqToHom _ _ (ok_endR P (appendRight v₁ hv₁ h₁ x) v₂),
    P.wRAt_eqToHom _ _ ((composable P x v₁').tensor_left hc₂').ok_endR,
    P.wRAt_wL (r := (0 : X)) (s := μ) hc hc₂ φ₁ rfl rfl rfl]
  exact eqToHom_sandwich_nested (D := P.Presented) _ _ _ _ _ _ _ _ _ _ _ _ _

/-- `whiskerLeft_wRWord` on the violating quotients. -/
theorem violatingWhiskerLeft_wRWord :
    violatingWhiskerLeft P (redFree_append hv₁ hv₂) (redFree_append hv₁' hv₂)
        (endWeight_append_of_eq h₁ h₂) (endWeight_append_of_eq h₁' h₂) (wRWord P h₁ h₁' φ₁) =
      (violatingWhiskerRightAppend P hv₁ hv₂ h₁ h₂).hom ≫
        Functor.whiskerRight (violatingWhiskerLeft P hv₁ hv₁' h₁ h₁' φ₁)
          (violatingWhiskerRight P v₂ hv₂ h₂) ≫
          (violatingWhiskerRightAppend P hv₁' hv₂ h₁' h₂).inv := by
  apply CategoryTheory.Quotient.natTrans_ext
  ext x
  have h := congrArg (fun τ => (violatingFunctor P ν₂).map (τ.app x))
    (whiskerLeft_wRWord P hv₁ hv₁' hv₂ h₁ h₁' h₂ φ₁)
  simp only [NatTrans.comp_app, Functor.map_comp] at h
  exact h

end Right

end Categorification.Stendhal.DoubleDiagram

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleRedUpNaturality
import StringDiagrams.Transport

/-!
# Red bigons across a word of upward strands

Webster, arXiv:1309.3796v2, §4.5, Definition 4.24 and the reduction in
Lemma 4.28. A red strand crossing a block of upward black strands and
then returning past them has all its crossings removed by (4.4e).
-/
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams

universe w u v
variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)
  {k : Type w} [CommRing k] (P : Presentation.{w,max u v} (signature RD Λ) k)
  (μ : X) (r : Fin ℓ) (u : List (DoubleStrand I ℓ)) (s : List I) (v : List (DoubleStrand I ℓ))
local notation "T" => addRedUpRelations RD Λ k P

private def castIso {a b a' b' : Obj (signature RD Λ)} (ha : a = a') (hb : b = b')
    (e : P.obj a ≅ P.obj b) : P.obj a' ≅ P.obj b' where
  hom := P.castHom ha hb e.hom
  inv := P.castHom hb ha e.inv
  hom_inv_id := by rw [← Presentation.castHom_comp, Iso.hom_inv_id, Presentation.castHom_id]
  inv_hom_id := by rw [← Presentation.castHom_comp, Iso.inv_hom_id, Presentation.castHom_id]

private def wordIso (u : List (DoubleStrand I ℓ)) (s : List I) (v : List (DoubleStrand I ℓ)) :
    (T).obj (obj RD Λ μ (u ++ [.inr r] ++ upBlackWord s ++ v)) ≅
      (T).obj (obj RD Λ μ (u ++ upBlackWord s ++ [.inr r] ++ v)) :=
  match s with
  | [] => eqToIso (congrArg (T).obj (by simp [upBlackWord]))
  | i :: t =>
    let e := redUpCrossingIso RD Λ P μ u r i (upBlackWord t ++ v)
    let f := wordIso (u ++ [.inl (true, i)]) t v
    castIso RD Λ (T) (by simp [upBlackWord, List.append_assoc]) (by simp [List.append_assoc]) e ≪≫
      castIso RD Λ (T) rfl (by simp [upBlackWord, List.append_assoc]) f

private theorem wordIso_hom :
    (wordIso RD Λ P μ r u s v).hom = (T).diag (redThroughUpWord RD Λ μ r u s v) := by
  induction s generalizing u with
  | nil => simp [wordIso, redThroughUpWord, Presentation.diag_eqToHom]
  | cons i s ih =>
    simp only [wordIso, redThroughUpWord, Iso.trans_hom, castIso, ih, Presentation.diag_comp,
      redUpCrossingIso, Presentation.castHom_diag]

private theorem wordIso_inv :
    (wordIso RD Λ P μ r u s v).inv = (T).diag (upWordThroughRed RD Λ μ r u s v) := by
  induction s generalizing u with
  | nil => simp [wordIso, upWordThroughRed, Presentation.diag_eqToHom]
  | cons i s ih =>
    simp only [wordIso, upWordThroughRed, Iso.trans_inv, castIso, ih, Presentation.diag_comp,
      redUpCrossingIso, Presentation.castHom_diag]

/-- The two physical sequences of crossings that move a red strand past a
whole upward word are inverse, by Webster (4.4e). -/
def redUpWordIso :
    (T).obj (obj RD Λ μ (u ++ [.inr r] ++ upBlackWord s ++ v)) ≅
      (T).obj (obj RD Λ μ (u ++ upBlackWord s ++ [.inr r] ++ v)) where
  hom := (T).diag (redThroughUpWord RD Λ μ r u s v)
  inv := (T).diag (upWordThroughRed RD Λ μ r u s v)
  hom_inv_id := by rw [← wordIso_hom, ← wordIso_inv, Iso.hom_inv_id]
  inv_hom_id := by rw [← wordIso_hom, ← wordIso_inv, Iso.inv_hom_id]

/-- Clear an enclosed upward dot or black crossing and remove the surrounding red
bigons. For a crossing this reduces a five-crossing subdiagram to the single black
crossing. For a dot it removes both crossings and keeps the dot. -/
theorem redUp_enclosed_move (u : List (DoubleStrand I ℓ)) (g : UpBlackMove I) (v : List (DoubleStrand I ℓ)) :
    let P' := addRedUpRelations RD Λ k (addRedUpSlideRelations RD Λ P)
    P'.diag (redUpSlide RD Λ μ u r g v true) ≫
      P'.diag (upWordThroughRed RD Λ μ r u g.top v) =
    P'.diag (upBlackMoveDiagram RD Λ μ (u ++ [.inr r]) g v) := by
  let P' := addRedUpRelations RD Λ k (addRedUpSlideRelations RD Λ P)
  have h : P'.diag (redUpSlide RD Λ μ u r g v false) =
      P'.diag (redUpSlide RD Λ μ u r g v true) :=
    P'.diag_eq_of_rel (.inl (.inr ⟨μ, u, r, g, v, false⟩)) rfl
  let e := redUpWordIso RD Λ (addRedUpSlideRelations RD Λ P) μ r u g.top v
  change P'.diag (redUpSlide RD Λ μ u r g v true) ≫ e.inv = _
  rw [← h]
  change P'.diag (_ ≫ _) ≫ e.inv = _
  rw [P'.diag_comp, Category.assoc]
  change P'.diag _ ≫ e.hom ≫ e.inv = _
  rw [Iso.hom_inv_id, Category.comp_id]

end Categorification.Stendhal.DoubleDiagram

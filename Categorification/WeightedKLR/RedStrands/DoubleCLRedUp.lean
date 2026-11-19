/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLBlackComparison
import Categorification.WeightedKLR.RedStrands.DoubleRedUp

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams TwoRep

universe w u v

theorem obj_whisker_nil_nil {S : Signature} {a : Obj S} {r : S.Region} (h : a.start = r) :
    a.whisker (Obj.nil r) [] = a := by
  exact (Obj.tensor_eq_whisker_nil_of_start (Obj.nil a.endR) h).symm.trans
    (Obj.tensor_nil a a.endR)

/-- Whiskering by empty objects is the identity, up to the identification of the objects. -/
theorem whisk_nil_nil {S : Signature} {R : Type*} [CommRing R] (Q : Presentation S R)
    {a a' : Obj S} (f : Q.obj a ⟶ Q.obj a') (ha : a.WF) {r : S.Region} (hr : a.start = r)
    (hr' : a'.start = r) :
    Q.whisk f (Obj.nil r) [] = eqToHom (congrArg Q.obj (obj_whisker_nil_nil hr)) ≫ f ≫
      eqToHom (congrArg Q.obj (obj_whisker_nil_nil hr')).symm := by
  have h := Q.wRAt_nil f ha rfl hr hr'
  unfold Presentation.wRAt at h
  have h2 := congrArg (fun x => eqToHom (congrArg Q.obj
      (Obj.tensor_eq_whisker_nil_of_start (Obj.nil a.endR) hr)).symm ≫ x ≫
      eqToHom (congrArg Q.obj (Obj.tensor_eq_whisker_nil_of_start (Obj.nil a.endR) hr'))) h
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
    eqToHom_trans_assoc, Category.id_comp] at h2
  exact h2.trans (by simp)

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {C' : CartanDatum (I ⊕ Fin ℓ)}
  {X Y : Type v} [AddCommGroup X] [AddCommGroup Y] (W : WeightDatum C' X Y)
  (hC : ∀ i j, C'.dot (.inl i) (.inl j) = C.dot i j) (o : X)
  {k : Type w} [CommRing k] {v' : Type*}

local notation "RD" => blackDatum W hC
local notation "Λ" => redWeight W

theorem coverObj_move (μ : X) (w : List (DoubleStrand I ℓ)) :
    (coverColourMap W hC o).obj ((coverMirror W hC o).obj (obj RD Λ μ ([] ++ w ++ []))) =
      ob W (o - μ) (coverWord w) := by
  simp only [List.nil_append, List.append_nil]
  refine Obj.ext ?_ (coverColours W hC o μ w)
  exact (congrArg (fun x : X => o - x) (colours_endR RD Λ μ w)).trans
    (wt_coverWord W hC o μ w).symm

theorem coverMove_congr (Q : Presentation.{w, v'} (psig W) k) (m : Move I ℓ) {ν ν' : X}
    (h : ν = ν') {A B : Q.Presented} (e₁ : A = Q.obj (ob W ν (coverWord m.bottom)))
    (e₂ : Q.obj (ob W ν (coverWord m.top)) = B) (e₁' : A = Q.obj (ob W ν' (coverWord m.bottom)))
    (e₂' : Q.obj (ob W ν' (coverWord m.top)) = B) :
    eqToHom e₁ ≫ Q.diag (coverMove W ν m) ≫ eqToHom e₂ =
      eqToHom e₁' ≫ Q.diag (coverMove W ν' m) ≫ eqToHom e₂' := by
  subst h
  rfl

/-- A single move, with no strands on either side, is sent by the reflected
local map to the KL diagram of the reflected move, rescaled by its weight. -/
theorem coverLin_moveDiagram (Q : Presentation.{w, v'} (psig W) k) (σ : Move I ℓ → k)
    (μ : X) (m : Move I ℓ) :
    ∃ (e₁ : Q.obj ((coverColourMap W hC o).obj ((coverMirror W hC o).obj
        (obj RD Λ μ ([] ++ m.bottom ++ [])))) = Q.obj (ob W (o - μ) (coverWord m.bottom)))
      (e₂ : Q.obj (ob W (o - μ) (coverWord m.top)) = Q.obj ((coverColourMap W hC o).obj
        ((coverMirror W hC o).obj (obj RD Λ μ ([] ++ m.top ++ []))))),
      coverLin W hC o Q σ (LinDiagram.of (moveDiagram RD Λ μ [] m [])) =
        σ m • (eqToHom e₁ ≫ Q.diag (coverMove W (o - μ) m) ≫ eqToHom e₂) := by
  refine ⟨congrArg Q.obj (coverObj_move W hC o μ _), (congrArg Q.obj (coverObj_move W hC o μ _)).symm, ?_⟩
  rw [coverLin, LayerMap.lin_of, LinDiagram.of, freeLift_map_single, one_smul]
  change eqToHom _ ≫ (eqToHom _ ≫
    Q.whisk (coverImage W hC o Q σ (endWeight RD Λ μ [], m)) (Obj.nil _) [] ≫
      eqToHom _) ≫ eqToHom _ = _
  rw [whisk_nil_nil Q _ (by rw [genDom_cover]; exact ob_wf _ _ _) ?h1 ?h2]
  case h1 => rfl
  case h2 => rfl
  rw [coverImage]
  simp only [Linear.comp_smul, Linear.smul_comp, Category.assoc, eqToHom_trans,
    eqToHom_trans_assoc]
  congr 1
  exact coverMove_congr W Q m (by simp [endWeight]) _ _ _ _

variable (Q : Presentation.{w, v'} (psig W) k)

/-- The two red/upward bigons (4.4e) of Webster, arXiv:1309.3796v3, §4.5, Definition 4.24,
vanish after reflection whenever the reflected sideways crossings of a red and a black strand
are mutually inverse in `Q`. -/
theorem coverLin_redUpRel [DecidableEq I]
    (hRL : ∀ ν r j, Q.diag (crossr W (.inr r) (.inl j) ν ≫ crossl W (.inr r) (.inl j) ν) = 𝟙 _)
    (hUL : ∀ ν r j, Q.diag (crossl W (.inr r) (.inl j) ν ≫ crossr W (.inr r) (.inl j) ν) = 𝟙 _)
    (a : RedUpRelation X I ℓ) :
    coverLin W hC o Q coverSign (LinDiagram.of (bareBigon RD Λ a.leftWeight a.red a.up a.side) -
      LinDiagram.of (𝟙 _)) = 0 := by
  obtain ⟨μ, r, i, s⟩ := a
  rw [show ∀ {a b} (f g : LinDiagram k a b), coverLin W hC o Q coverSign (f - g) =
      coverLin W hC o Q coverSign f - coverLin W hC o Q coverSign g from fun f g => by
    simp only [coverLin, freeLift_map_layerLin, Functor.map_sub], sub_eq_zero]
  change _ = coverLin W hC o Q coverSign (𝟙 (Free.of k _))
  rw [coverLin_id]
  cases s with
  | redLeft =>
    change coverLin W hC o Q coverSign (LinDiagram.of (moveDiagram RD Λ μ [] (.redBlack r (true, i)) [] ≫
      moveDiagram RD Λ μ [] (.blackRed (true, i) r) [])) = _
    rw [LinDiagram.of_comp, coverLin_comp]
    obtain ⟨e₁, e₂, h₁⟩ := coverLin_moveDiagram W hC o Q coverSign μ (.redBlack r (true, i))
    obtain ⟨e₃, e₄, h₂⟩ := coverLin_moveDiagram W hC o Q coverSign μ (.blackRed (true, i) r)
    rw [h₁, h₂]
    change ((1 : k) • _) ≫ ((1 : k) • _) = _
    simp only [one_smul, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    change eqToHom e₁ ≫ Q.diag (crossr W (.inr r) (.inl i) (o - μ)) ≫
      Q.diag (crossl W (.inr r) (.inl i) (o - μ)) ≫ eqToHom e₄ = _
    rw [← Category.assoc (Q.diag _), ← Q.diag_comp, hRL]
    erw [Category.id_comp, eqToHom_trans, eqToHom_refl]
    rfl
  | upLeft =>
    change coverLin W hC o Q coverSign (LinDiagram.of (moveDiagram RD Λ μ [] (.blackRed (true, i) r) [] ≫
      moveDiagram RD Λ μ [] (.redBlack r (true, i)) [])) = _
    rw [LinDiagram.of_comp, coverLin_comp]
    obtain ⟨e₁, e₂, h₁⟩ := coverLin_moveDiagram W hC o Q coverSign μ (.blackRed (true, i) r)
    obtain ⟨e₃, e₄, h₂⟩ := coverLin_moveDiagram W hC o Q coverSign μ (.redBlack r (true, i))
    rw [h₁, h₂]
    change ((1 : k) • _) ≫ ((1 : k) • _) = _
    simp only [one_smul, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    change eqToHom e₁ ≫ Q.diag (crossl W (.inr r) (.inl i) (o - μ)) ≫
      Q.diag (crossr W (.inr r) (.inl i) (o - μ)) ≫ eqToHom e₄ = _
    rw [← Category.assoc (Q.diag _), ← Q.diag_comp, hUL]
    erw [Category.id_comp, eqToHom_trans, eqToHom_refl]
    rfl

end Categorification.Stendhal.DoubleDiagram

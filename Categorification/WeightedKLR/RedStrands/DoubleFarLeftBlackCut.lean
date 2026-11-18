/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleBlackBubbleSlide
import Categorification.WeightedKLR.RedStrands.DoubleFirstRed

/-! # Evaluating the black cut to the left of a signed boundary
Webster, arXiv:1309.3796v2, §4.5, Lemma 4.28.
-/
noncomputable section
namespace Categorification.Stendhal.DoubleDiagram
open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams
universe u v w
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {ℓ : ℕ} {weights : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}}
  {k : Type w} [CommRing k]
variable (P : Presentation.{w,max u v} (signature RD (Subtype.val ∘ weights)) k)
  (kl : ∀ z : (pres RD k).Rel, P.lin (blackMirrorLinear RD (Subtype.val ∘ weights) ((pres RD k).rel z)) = 0)
  {η : X} (b : BoundaryCategory (Λ := weights) P η)
local notation "lab" => (Subtype.val ∘ weights)
local notation "V" => violatingFunctor P η
local notation "K" => pres RD k
local notation "U" => endWeight RD lab 0 []
local notation "cut" => blackCutHom RD lab P kl 0 [] b.val.word b.val.word (List.nil_append _)

/-- Project an endomorphism of a signed word to its class in the violating quotient. -/
def cutProjection : End (P.obj (obj RD lab 0 b.val.word)) →ₗ[k] End ((V).obj b) where
  toFun f := (V).map (InducedCategory.homMk (X := b) (Y := b) f)
  map_add' f g := (V).map_add (f := InducedCategory.homMk (X := b) (Y := b) f)
    (g := InducedCategory.homMk (X := b) (Y := b) g)
  map_smul' c f := (V).map_smul c (InducedCategory.homMk (X := b) (Y := b) f)

/-- The entire black empty-word endomorphism algebra acts through scalars
on the far-left cut of any signed boundary. -/
theorem farLeftBlackCut_scalar (β : End ((K).obj (ob RD U []))) :
    ∃ c : k, cutProjection P b ((cut) β) = c • 𝟙 _ := by
  induction β using (K).hom_induction with
  | diag f =>
    obtain ⟨xs,hx,rfl⟩ := exists_mkD RD U f
    cases xs with
    | nil =>
      have hf : mkD RD U [] hx = 𝟙 _ := Diagram.ext rfl
      refine ⟨1, ?_⟩
      rw [hf, Presentation.diag_id, blackCutHom_id, one_smul]
      exact (V).map_id b
    | cons x xs =>
      refine ⟨0, ?_⟩
      rw [zero_smul, ← Presentation.lin_of, blackCutHom_lin, blackLinear_of, LinDiagram.cast_of,
        Presentation.lin_of]
      let d := blackDiagram RD lab 0 [] b.val.word (mkD RD U (x :: xs) hx)
      let e : obj RD lab 0 ([] ++ blackWord [] ++ b.val.word) = obj RD lab 0 b.val.word := by simp [blackWord]
      change (V).map (InducedCategory.homMk (X := b) (Y := b) (P.diag (Diagram.cast d e e))) = 0
      apply diagram_eq_zero_of_leftEmptyLayer P b b (Diagram.cast d e e)
        (L := layer RD lab 0 ([] ++ blackWord x.2.2) (.black (Sig.shape x.2.1))
          (blackWord x.1 ++ b.val.word))
      · rw [Diagram.layers_cast, show Diagram.layers d = _ from layers_blackDiagram_mkD RD lab 0
          [] b.val.word (x :: xs) hx]
        exact List.mem_cons_self
      · have hr : x.2.2 = [] := (List.append_eq_nil_iff.mp hx.1.symm).2
        rw [hr]
        rfl
  | zero => exact ⟨0, by simp⟩
  | add f g hf hg =>
    obtain ⟨a,ha⟩ := hf
    obtain ⟨c,hc⟩ := hg
    exact ⟨a+c, by rw [map_add, map_add, ha, hc, add_smul]⟩
  | smul a f hf =>
    obtain ⟨c,hc⟩ := hf
    exact ⟨a*c, by rw [map_smul, map_smul, hc, smul_smul]⟩

/-- Far-left bubble evaluation remains scalar after an arbitrary preceding
endomorphism of the same boundary. -/
theorem farLeftBlackCut_comp_scalar (β : End ((K).obj (ob RD U []))) :
    ∃ c : k, ∀ f, cutProjection P b (f ≫ (cut) β) = c • cutProjection P b f := by
  obtain ⟨c,hc⟩ := farLeftBlackCut_scalar P kl b β
  refine ⟨c, fun f => ?_⟩
  have hm : cutProjection P b (f ≫ (cut) β) = cutProjection P b f ≫ cutProjection P b ((cut) β) :=
    (V).map_comp (InducedCategory.homMk (X := b) (Y := b) f) (InducedCategory.homMk ((cut) β))
  rw [hm, hc, Linear.comp_smul, Category.comp_id]

end Categorification.Stendhal.DoubleDiagram

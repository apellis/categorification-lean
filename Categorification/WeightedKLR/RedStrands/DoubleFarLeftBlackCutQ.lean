/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleFarLeftBlackCut
import Categorification.WeightedKLR.RedStrands.DoubleBlackBubbleSlideQ
import Categorification.WeightedKLR.RedStrands.DoubleFirstRed

/-! # Evaluating the black cut to the left of a signed boundary
Webster, arXiv:1309.3796v2, §4.5, Lemma 4.28.

This is the version of `DoubleFarLeftBlackCut` in which the black strands carry the relations of
Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, Definition 1.1, `r = 1`; `CLQ.pres RD k sc`) instead
of the KL III relations. Each declaration carries the suffix `Q`.
-/
noncomputable section
namespace Categorification.Stendhal.DoubleDiagram
open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams
universe u v w
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {ℓ : ℕ} {weights : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}}
  {k : Type w} [CommRing k] {sc : KL3.Diagram.CL.CLScalars C k}
variable (P : Presentation.{w,max u v} (signature RD (Subtype.val ∘ weights)) k)
  (kl : ∀ z : (CLQ.pres RD k sc).Rel, P.lin (blackMirrorLinear RD (Subtype.val ∘ weights) ((CLQ.pres RD k sc).rel z)) = 0)
  {η : X} (b : BoundaryCategory (Λ := weights) P η)
local notation "lab" => (Subtype.val ∘ weights)
local notation "V" => violatingFunctor P η
local notation "K" => CLQ.pres RD k sc
local notation "CLQ.U" => endWeight RD lab 0 []
local notation "cut" => blackCutHomQ RD lab sc P kl 0 [] b.val.word b.val.word (List.nil_append _)

/-- The entire black empty-word endomorphism algebra acts through scalars
on the far-left cut of any signed boundary. -/
theorem farLeftBlackCut_scalarQ (β : End ((K).obj (ob RD CLQ.U []))) :
    ∃ c : k, cutProjection P b ((cut) β) = c • 𝟙 _ := by
  induction β using (K).hom_induction with
  | diag f =>
    obtain ⟨xs,hx,rfl⟩ := exists_mkD RD CLQ.U f
    cases xs with
    | nil =>
      have hf : mkD RD CLQ.U [] hx = 𝟙 _ := Diagram.ext rfl
      refine ⟨1, ?_⟩
      rw [hf, Presentation.diag_id, blackCutHom_idQ, one_smul]
      exact (V).map_id b
    | cons x xs =>
      refine ⟨0, ?_⟩
      rw [zero_smul, ← Presentation.lin_of, blackCutHom_linQ, blackLinear_of, LinDiagram.cast_of,
        Presentation.lin_of]
      let d := blackDiagram RD lab 0 [] b.val.word (mkD RD CLQ.U (x :: xs) hx)
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
theorem farLeftBlackCut_comp_scalarQ (β : End ((K).obj (ob RD CLQ.U []))) :
    ∃ c : k, ∀ f, cutProjection P b (f ≫ (cut) β) = c • cutProjection P b f := by
  obtain ⟨c,hc⟩ := farLeftBlackCut_scalarQ P kl b β
  refine ⟨c, fun f => ?_⟩
  have hm : cutProjection P b (f ≫ (cut) β) = cutProjection P b f ≫ cutProjection P b ((cut) β) :=
    (V).map_comp (InducedCategory.homMk (X := b) (Y := b) f) (InducedCategory.homMk ((cut) β))
  rw [hm, hc, Linear.comp_smul, Category.comp_id]

end Categorification.Stendhal.DoubleDiagram

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleDownContext
import StringDiagrams.LayerMap.Basic

/-!
# Downward relations in signed contexts lie in the ideal of the empty-context relations

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29. The downward translation of a KLR
relation, whiskered by ordinary words and placed between two signed words, is a whiskered
copy of the downward translation of the relation in the empty context (with the matching left
region). Hence it lies in the tensor ideal of the presentation `emptyDownPres` whose
relations are these empty-context translations (`downLinear_whisker_relation_mem_ideal`).
-/

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams

universe w u v₁ v₂

/-- The top word of a KLR relation is a permutation of its bottom word. -/
theorem relCod_perm_dom {J : Type u} (r : KLR.Diagram.Rel J) : r.cod.word.Perm r.dom.word := by
  cases r with
  | sqEq c => exact List.Perm.refl _
  | sqNe c d _ => exact List.Perm.refl _
  | slideLEq c => exact List.Perm.refl _
  | slideLNe c d _ => exact List.Perm.swap c d []
  | slideREq c => exact List.Perm.refl _
  | slideRNe c d _ => exact List.Perm.swap c d []
  | braid c d e _ => exact List.reverse_perm [c, d, e]
  | braidQ c d _ => exact List.Perm.refl _

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X : Type v₁} {Y : Type v₂}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)
  (k : Type w) [CommRing k] (Q : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k)

/-- The downward translations of the KLR relations in the empty signed context, one for each
left region. -/
def emptyDownPres : Presentation.{w, max u v₁} (signature RD Λ) k where
  Rel := X × KLR.Diagram.Rel (I ⊕ Fin ℓ)
  dom p := downContextObj RD Λ p.1 [] [] p.2.dom
  cod p := downContextObj RD Λ p.1 [] [] p.2.cod
  rel p := downLinear RD Λ k p.1 [] [] (KLR.Diagram.relation k Q p.2)

theorem emptyDownPres_wfDom : (emptyDownPres RD Λ k Q).WFDom := fun _ => colours_ok ..

/-- **A downward KLR relation in any context lies in the tensor ideal of the empty-context
downward relations.** -/
theorem downLinear_whisker_relation_mem_ideal (μ : X) (u v : List (DoubleStrand I ℓ))
    (r : KLR.Diagram.Rel (I ⊕ Fin ℓ)) (a : Obj (KLR.Diagram.sig (I ⊕ Fin ℓ)))
    (b : List (I ⊕ Fin ℓ)) (h : r.dom.WhiskerOK a b) :
    downLinear RD Λ k μ u v (LinDiagram.whisker (KLR.Diagram.relation k Q r) a b h) ∈
      (emptyDownPres RD Λ k Q).ideal _ _ := by
  rw [downLinear_whisker]
  set u' := u ++ a.word.map DoubleStrand.down
  set v' := b.map DoubleStrand.down ++ v
  have ha : endWeight RD Λ (endWeight RD Λ μ u') (r.dom.word.map DoubleStrand.down) =
      endWeight RD Λ (endWeight RD Λ μ u') (r.dom.word.map DoubleStrand.down) := rfl
  have hb : endWeight RD Λ (endWeight RD Λ μ u') (r.cod.word.map DoubleStrand.down) =
      endWeight RD Λ (endWeight RD Λ μ u') (r.dom.word.map DoubleStrand.down) :=
    endWeight_map_down_of_perm RD Λ _ (relCod_perm_dom r)
  rw [downLinear_eq_whisker RD Λ μ u' v' _ k _ ha hb]
  simp only [LinDiagram.cast_eq_comp]
  refine Presentation.comp_mem_ideal _ _ (Presentation.mem_ideal_comp _ ?_ _)
  refine Presentation.comp_mem_ideal _ _ (Presentation.mem_ideal_comp _ ?_ _)
  exact (emptyDownPres RD Λ k Q).whisker_rel_mem_ideal
    (.user (⟨endWeight RD Λ μ u', r⟩ : X × KLR.Diagram.Rel (I ⊕ Fin ℓ))) _ _ _

end Categorification.Stendhal.DoubleDiagram

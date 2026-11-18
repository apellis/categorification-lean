/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleDiagramCut
import Categorification.WeightedKLR.RedStrands.DoubleViolatingQuotient
import StringDiagrams.Generation

/-!
# The zero-red double Stendhal vacuum

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
§4.5, Lemma 4.28, surjectivity for the empty red family and the empty boundary.
Any diagram on the vacuum with a first layer starts with a black cup. The cut
above that cup has a black strand first, and the diagram vanishes in the
violating quotient of Definition 4.27. This holds for any choice of presentation
relations on the double diagram signature.
-/

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

variable {I X Y k : Type*} {C : CartanDatum I} [AddCommGroup X] [AddCommGroup Y]
  [CommRing k] {RD : WeightDatum C X Y}
  {Λ : Fin 0 → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}}

variable (P : Presentation (signature RD (fun r => (Λ r).val)) k)

local notation "labels" => (Subtype.val ∘ Λ)
local notation "raw" => obj RD labels (0 : X) []

/-- The empty double Stendhal triple in the weight-zero fibre. -/
def vacuumBoundary : BoundaryCategory P (0 : X) :=
  ⟨⟨[], rfl⟩, by simp [DoubleBoundary.rightWeight]⟩

local notation "vacuum" => vacuumBoundary P

/-- The empty word as an object of the violating quotient. -/
def vacuumObj : ViolatingCategory P (0 : X) := (violatingFunctor P 0).obj vacuum

private def vacuumProjection : (P.obj raw ⟶ P.obj raw) →ₗ[k] End (vacuumObj P) :=
  ((violatingFunctor P 0).mapLinearMap k (X := vacuum) (Y := vacuum)).comp
    (InducedCategory.homLinearEquiv (R := k) (X := vacuum) (Y := vacuum)).symm.toLinearMap

private theorem first_layer_head (L : Layer (signature RD labels)) (hL : L.dom = raw) :
    ∃ l : Letter I, (L.cod.word.map Prod.snd).head? = some (.inl l) := by
  let left : List (X × DoubleStrand I 0) := L.left
  let right : List (X × DoubleStrand I 0) := L.right
  have h : (left ++ colours RD labels L.gen.1 L.gen.2.bottom) ++ right = [] :=
    congrArg Obj.word hL
  simp only [List.append_eq_nil_iff, and_assoc] at h
  have hbottom : L.gen.2.bottom = [] := by
    cases hb : L.gen.2.bottom with
    | nil => rfl
    | cons a w => simp [hb, colours] at h
  obtain ⟨hl, _, hr⟩ := h
  change ∃ l : Letter I,
    (((left ++ colours RD labels L.gen.1 L.gen.2.top) ++ right).map Prod.snd).head? =
      some (.inl l)
  rw [hl, hr, List.nil_append, List.append_nil]
  cases hg : L.gen.2 with
  | black s =>
    cases s with
    | cup l => exact ⟨l, rfl⟩
    | _ => simp [hg, Move.bottom, Shape.dom] at hbottom
  | _ => simp [hg, Move.bottom] at hbottom

private theorem vacuum_diag_eq_zero (L : Layer (signature RD labels))
    (ls : List (Layer (signature RD labels))) (h : Chain raw (L :: ls) raw) :
    vacuumProjection P (P.diag (Diagram.mk (L :: ls) h)) = 0 := by
  let first := Diagram.layer L h.1 h.2.1 rfl
  obtain ⟨cut, hc, _⟩ := existsUnique_triple_at_cut RD Λ vacuum first
  obtain ⟨l, hl⟩ := first_layer_head L h.2.1
  have hv : cut.val.IsViolated := by
    refine ⟨l, ?_⟩
    have he := congrArg (fun z : Obj (signature RD labels) =>
      (z.word.map Prod.snd).head?) hc
    have hw := he.trans hl
    cases hword : cut.val.word <;> simp [obj, colours, hword] at hw ⊢
    exact hw
  let u := Diagram.cast first rfl hc.symm
  let v := Diagram.cast (Diagram.mk ls h.2.2) hc.symm rfl
  have hcomp : Diagram.mk (L :: ls) h = u ≫ v := by
    apply Diagram.ext
    rfl
  have hdiag := (congrArg (P.diag (a := raw) (b := raw)) hcomp).trans (P.diag_comp u v)
  refine (congrArg (vacuumProjection P) hdiag).trans ?_
  exact DoubleViolatingQuotient.map_eq_zero_of_factor k (tripleObj P)
    (x := vacuum) (y := vacuum) (z := cut) hv
    (InducedCategory.homMk (P.diag u)) (InducedCategory.homMk (P.diag v))

/-- The vacuum endomorphisms are spanned by the identity in the violating quotient.
This is the surjectivity in Webster, arXiv:1309.3796v2, §4.5, Lemma 4.28,
for the empty red family and the empty boundary. -/
theorem vacuum_algebraMap_surjective : Function.Surjective (algebraMap k (End (vacuumObj P))) := by
  let q := violatingFunctor P (0 : X)
  intro f
  obtain ⟨⟨f⟩, rfl⟩ := q.map_surjective f
  change (P.obj raw ⟶ P.obj raw) at f
  change ∃ r : k, r • 𝟙 (vacuumObj P) = vacuumProjection P f
  induction f using P.hom_induction with
  | diag d =>
    obtain ⟨ls, h⟩ := d
    cases ls with
    | nil =>
      refine ⟨1, ?_⟩
      rw [one_smul]
      change 𝟙 (vacuumObj P) = vacuumProjection P (P.diag (𝟙 raw))
      rw [P.diag_id]
      exact (q.map_id vacuum).symm
    | cons L ls =>
      exact ⟨0, by rw [zero_smul]; exact (vacuum_diag_eq_zero P L ls h).symm⟩
  | zero =>
    exact ⟨0, by rw [zero_smul, map_zero]⟩
  | add f g hf hg =>
    obtain ⟨r, hr⟩ := hf
    obtain ⟨s, hs⟩ := hg
    exact ⟨r + s, by rw [add_smul, map_add, hr, hs]⟩
  | smul r f hf =>
    obtain ⟨s, hs⟩ := hf
    exact ⟨r * s, by rw [mul_smul, map_smul, hs]⟩

end Categorification.Stendhal.DoubleDiagram

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleDownDiagram
import StringDiagrams.Biadjunction.PivotalExtension
import StringDiagrams.Positional

/-!
# Downward local relations of double Stendhal diagrams

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
§4.5, Definition 4.24 and Lemma 4.28. The downward relations are the signed
images of the ordinary black and red/black KLR relations of Definition 4.5.
The ambient presentation allows auxiliary words with arbitrary red lists so
that the ordinary diagram functor is defined on every word. Every signed
layer preserves the red list, so words with repeated or unordered reds do
not occur in the ordered double Stendhal fibre.
-/

-- Source layer chains and their boundary equalities use the unweighted signature.
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams

universe w u v₁ v₂

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X : Type v₁} {Y : Type v₂}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)
  {k : Type w} [CommRing k]

/-- A local ordinary relation with the signed words around it and with ordinary whiskering. -/
structure DownRelation (X : Type v₁) (I : Type u) (ℓ : ℕ) where
  leftWeight : X
  leftSigned : List (DoubleStrand I ℓ)
  rightSigned : List (DoubleStrand I ℓ)
  rel : KLR.Diagram.Rel (I ⊕ Fin ℓ)
  left : Obj (KLR.Diagram.sig (I ⊕ Fin ℓ))
  right : List (I ⊕ Fin ℓ)

private def DownRelation.dom (a : DownRelation X I ℓ) : Obj (signature RD Λ) :=
  downContextObj RD Λ a.leftWeight a.leftSigned a.rightSigned (a.rel.dom.whisker a.left a.right)

private def DownRelation.cod (a : DownRelation X I ℓ) : Obj (signature RD Λ) :=
  downContextObj RD Λ a.leftWeight a.leftSigned a.rightSigned (a.rel.cod.whisker a.left a.right)

variable (Q : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k)

/-- Adjoin the signed images of ordinary KLR relations in every context. Use the
polynomials `stendhalQ` for Webster's downward relations. -/
def addDownRelations (P : Presentation.{w, max u v₁} (signature RD Λ) k) :
    Presentation.{w, max u v₁} (signature RD Λ) k :=
  P.addRels _ (DownRelation.dom RD Λ) (DownRelation.cod RD Λ) fun a =>
    downLinear RD Λ k a.leftWeight a.leftSigned a.rightSigned
      (LinDiagram.whisker (KLR.Diagram.relation k Q a.rel) a.left a.right
        (Obj.whiskerOK_of_subsingleton ..))

/-- Every translated ordinary local relation vanishes, including all whiskered instances. -/
theorem lin_downRelation (P : Presentation.{w, max u v₁} (signature RD Λ) k)
    (μ : X) (u v : List (DoubleStrand I ℓ)) (r : KLR.Diagram.Rel (I ⊕ Fin ℓ))
    (a : Obj (KLR.Diagram.sig (I ⊕ Fin ℓ))) (b : List (I ⊕ Fin ℓ))
    (h : r.dom.WhiskerOK a b) :
    (addDownRelations RD Λ Q P).lin
      (downLinear RD Λ k μ u v (LinDiagram.whisker (KLR.Diagram.relation k Q r) a b h)) = 0 :=
  (addDownRelations RD Λ Q P).lin_rel_self (.inr ⟨μ, u, v, r, a, b⟩)

section Interchange

local notation "S" => KLR.Diagram.sig (I ⊕ Fin ℓ)
local notation "T" => signature RD Λ

variable (μ : X) (u v : List (DoubleStrand I ℓ))

private theorem downLinear_pair {a b : Obj S} {L M : Layer S} (h : Chain a [L, M] b) :
    downLinear RD Λ k μ u v (LinDiagram.of (Diagram.mk [L, M] h)) =
      LinDiagram.cast (downLinearLayer RD Λ k μ u v L)
        (congrArg (downContextObj RD Λ μ u v) h.2.1) rfl ≫
      LinDiagram.cast (downLinearLayer RD Λ k μ u v M)
        (congrArg (downContextObj RD Λ μ u v) h.2.2.2.1)
        (congrArg (downContextObj RD Λ μ u v) h.2.2.2.2) := by
  have e : Diagram.mk [L, M] h = Diagram.layer L h.1 h.2.1 rfl ≫
      Diagram.layer M h.2.2.1 h.2.2.2.1 h.2.2.2.2 := by
    apply Diagram.ext
    rfl
  rw [e, LinDiagram.of_comp, downLinear_comp, downLinear_layer, downLinear_layer]

private def downPair {a b : Obj S} {L M : Layer S} (h : Chain a [L, M] b)
    {g j : Move I ℓ} (hg : downMove L.gen = some g) (hj : downMove M.gen = some j) :
    downContextObj RD Λ μ u v a ⟶ downContextObj RD Λ μ u v b :=
  Diagram.cast (downLayerDiagram RD Λ μ u v L hg)
    (congrArg (downContextObj RD Λ μ u v) h.2.1) rfl ≫
  Diagram.cast (downLayerDiagram RD Λ μ u v M hj)
    (congrArg (downContextObj RD Λ μ u v) h.2.2.2.1)
    (congrArg (downContextObj RD Λ μ u v) h.2.2.2.2)

private theorem downLinear_pair_of_moves {a b : Obj S} {L M : Layer S} (h : Chain a [L, M] b)
    {g j : Move I ℓ} (hg : downMove L.gen = some g) (hj : downMove M.gen = some j) :
    downLinear RD Λ k μ u v (LinDiagram.of (Diagram.mk [L, M] h)) =
      LinDiagram.of (downPair RD Λ μ u v h hg hj) := by
  rw [downLinear_pair, downLinearLayer_of_move _ _ _ _ _ _ _ hg,
    downLinearLayer_of_move _ _ _ _ _ _ _ hj, LinDiagram.cast_of, LinDiagram.cast_of,
    ← LinDiagram.of_comp]
  rfl

private theorem downLinear_pair_zero_left {a b : Obj S} {L M : Layer S} (h : Chain a [L, M] b)
    (hg : downMove L.gen = none) :
    downLinear RD Λ k μ u v (LinDiagram.of (Diagram.mk [L, M] h)) = 0 := by
  rw [downLinear_pair]
  rw [downLinearLayer_of_none _ _ _ _ _ _ _ hg]
  simp only [LinDiagram.cast, Finsupp.mapDomain_zero, Limits.zero_comp]

private theorem downLinear_pair_zero_right {a b : Obj S} {L M : Layer S} (h : Chain a [L, M] b)
    (hj : downMove M.gen = none) :
    downLinear RD Λ k μ u v (LinDiagram.of (Diagram.mk [L, M] h)) = 0 := by
  rw [downLinear_pair]
  rw [downLinearLayer_of_none _ _ _ _ _ _ _ hj]
  simp only [LinDiagram.cast, Finsupp.mapDomain_zero, Limits.comp_zero]

/-- A translated interchange already holds in every signed presentation. If either generator
has zero image, both orders have zero image. Otherwise the two translated layers are the two
orders of the corresponding signed interchange. -/
theorem lin_downInterchange (P : Presentation (signature RD Λ) k) (x : InterchangeData S)
    (hx : x.Valid) (a : Obj S) (b : List (I ⊕ Fin ℓ)) (hw : x.dom.WhiskerOK a b) :
    P.lin (downLinear RD Λ k μ u v (LinDiagram.whisker (InterchangeData.rel k hx) a b hw)) = 0 := by
  let hgh : Chain (x.dom.whisker a b) [x.gh₁.whisker a b, x.gh₂.whisker a b]
      (x.cod.whisker a b) := Diagram.chain (Diagram.whisker (InterchangeData.ghDiagram hx) a b hw)
  let hhg : Chain (x.dom.whisker a b) [x.hg₁.whisker a b, x.hg₂.whisker a b]
      (x.cod.whisker a b) := Diagram.chain (Diagram.whisker (InterchangeData.hgDiagram hx) a b hw)
  rw [InterchangeData.rel]
  simp only [InterchangeData.sign, Bool.false_and, Bool.false_eq_true,
    ↓reduceIte, Int.cast_one, one_smul, LinDiagram.whisker_sub, LinDiagram.whisker_of, map_sub,
    Presentation.lin_sub, sub_eq_zero]
  change P.lin (downLinear RD Λ k μ u v
      (LinDiagram.of (Diagram.mk [x.gh₁.whisker a b, x.gh₂.whisker a b] hgh))) =
    P.lin (downLinear RD Λ k μ u v
      (LinDiagram.of (Diagram.mk [x.hg₁.whisker a b, x.hg₂.whisker a b] hhg)))
  cases hg : downMove x.g with
  | none =>
    rw [downLinear_pair_zero_left RD Λ μ u v hgh hg,
      downLinear_pair_zero_right RD Λ μ u v hhg hg]
  | some g =>
    cases hj : downMove x.h with
    | none =>
      rw [downLinear_pair_zero_right RD Λ μ u v hgh hj,
        downLinear_pair_zero_left RD Λ μ u v hhg hj]
    | some j =>
      rw [downLinear_pair_of_moves RD Λ μ u v hgh hg hj,
        downLinear_pair_of_moves RD Λ μ u v hhg hj hg, Presentation.lin_of, Presentation.lin_of]
      let left := u ++ a.word.map DoubleStrand.down
      let mid := x.mid.map DoubleStrand.down
      let right := b.map DoubleStrand.down ++ v
      let s := endWeight RD Λ μ left
      let t := endWeight RD Λ s g.bottom
      let r := endWeight RD Λ t mid
      apply P.diag_interchange_of_layers_of_even μ (colours RD Λ μ left)
        (colours RD Λ t mid) (colours RD Λ (endWeight RD Λ r j.bottom) right)
        (s, g) (r, j) (Or.inl rfl)
      · simp [downPair, layer, InterchangeData.gh₁, InterchangeData.gh₂, Layer.whisker,
          left, mid, right, s, t, r, signature, List.append_assoc, colours_append,
          endWeight_append, ← (downMove_words hg).2, ← (downMove_words hj).1, g.endWeight_top]
      · simp [downPair, layer, InterchangeData.hg₁, InterchangeData.hg₂, Layer.whisker,
          left, mid, right, s, t, r, signature, List.append_assoc, colours_append,
          endWeight_append, ← (downMove_words hg).1, ← (downMove_words hj).2, j.endWeight_top]

end Interchange

section Descent

local notation "S" => KLR.Diagram.sig (I ⊕ Fin ℓ)

variable (P : Presentation.{w, max u v₁} (signature RD Λ) k)
  (μ : X) (u v : List (DoubleStrand I ℓ))

local notation "P₁" => addDownRelations RD Λ Q P
local notation "F" => Interpretation.functor (downInterpretation RD Λ k μ u v) ⋙
  Presentation.linFunctor P₁

private theorem freeLift_downPresented_map {a b : Obj S} (f : LinDiagram k a b) :
    (freeLift k F).map f = (P₁).lin (downLinear RD Λ k μ u v f) := by
  change (freeLift k F).map f =
    (P₁).linFunctor.map ((freeLift k (downInterpretation RD Λ k μ u v).functor).map f)
  simp only [freeLift_map, Functor.comp_map, Finsupp.sum, Functor.map_sum, Functor.map_smul]

private theorem downRespects : (KLR.Diagram.pres k Q).Respects F where
  rel i a b hw := by
    rw [freeLift_downPresented_map]
    exact lin_downRelation RD Λ Q P μ u v i a b hw
  interchange x hx a b hw := by
    rw [freeLift_downPresented_map]
    exact lin_downInterchange RD Λ μ u v P₁ x hx a b hw

/-- The ordinary KLR functor after adjoining the downward local relations.
This includes both ordinary black and red/black layers in Webster's Lemma 4.28. -/
def downPresentedFunctor : (KLR.Diagram.pres k Q).Presented ⥤ (P₁).Presented :=
  (KLR.Diagram.pres k Q).lift (downRespects RD Λ Q P μ u v)

instance : (downPresentedFunctor RD Λ Q P μ u v).Additive := by
  unfold downPresentedFunctor
  infer_instance

instance : (downPresentedFunctor RD Λ Q P μ u v).Linear k := by
  unfold downPresentedFunctor
  infer_instance

@[simp] theorem downPresentedFunctor_obj (a : Obj S) :
    (downPresentedFunctor RD Λ Q P μ u v).obj ((KLR.Diagram.pres k Q).obj a) =
      (P₁).obj (downContextObj RD Λ μ u v a) := rfl

@[simp] theorem downPresentedFunctor_lin {a b : Obj S} (f : LinDiagram k a b) :
    (downPresentedFunctor RD Λ Q P μ u v).map ((KLR.Diagram.pres k Q).lin f) =
      (P₁).lin (downLinear RD Λ k μ u v f) :=
  (Presentation.lift_lin _ _).trans (freeLift_downPresented_map RD Λ Q P μ u v f)

theorem downPresentedFunctor_layer {a b : Obj S} (L : Layer S) (hv : L.Valid)
    (ha : L.dom = a) (hb : L.cod = b) {g : Move I ℓ} (hg : downMove L.gen = some g) :
    (downPresentedFunctor RD Λ Q P μ u v).map ((KLR.Diagram.pres k Q).diag
      (Diagram.layer L hv ha hb)) =
      (P₁).diag (Diagram.cast (downLayerDiagram RD Λ μ u v L hg)
        (congrArg (downContextObj RD Λ μ u v) ha) (congrArg (downContextObj RD Λ μ u v) hb)) := by
  rw [Presentation.diag, downPresentedFunctor_lin, downLinear_layer, downLinearLayer_of_move,
    LinDiagram.cast_of, Presentation.lin_of]

theorem downPresentedFunctor_layer_zero {a b : Obj S} (L : Layer S) (hv : L.Valid)
    (ha : L.dom = a) (hb : L.cod = b) (hg : downMove L.gen = none) :
    (downPresentedFunctor RD Λ Q P μ u v).map ((KLR.Diagram.pres k Q).diag
      (Diagram.layer L hv ha hb)) = 0 := by
  rw [Presentation.diag, downPresentedFunctor_lin, downLinear_layer,
    downLinearLayer_of_none _ _ _ _ _ _ _ hg]
  simp only [LinDiagram.cast, Finsupp.mapDomain_zero, Presentation.lin_zero]

end Descent

end Categorification.Stendhal.DoubleDiagram

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KLR.Basic
import Categorification.WeightedKLR.RedStrands.DoubleDiagram

/-!
# Ordinary diagrams with downward black strands

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
§4.5, Definition 4.27 and Lemma 4.28. Ordinary Stendhal diagrams are read as
double Stendhal diagrams with downward black strands. On the free linear
category for the KLR presentation of Definition 4.5, red dots and red/red
crossings have image zero. Each other generator gives one signed layer.
-/

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams

universe w u v₁ v₂

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X : Type v₁} {Y : Type v₂}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)

/-- The ordinary KLR boundary with all black strands oriented downward, placed between
two signed words with the given left region. -/
def downContextObj (μ : X) (u v : List (DoubleStrand I ℓ))
    (a : Obj (KLR.Diagram.sig (I ⊕ Fin ℓ))) : Obj (signature RD Λ) :=
  obj RD Λ μ (u ++ a.word.map DoubleStrand.down ++ v)

/-- Ordinary dots and crossings represented by a single signed generator.
Red dots and crossings of two red strands have image zero. -/
def downMove : KLR.Diagram.Gen (I ⊕ Fin ℓ) → Option (Move I ℓ)
  | .dot (.inl i) => some (.black (.dot (false, i)))
  | .dot (.inr _) => none
  | .cross (.inl i) (.inl j) => some (.black (.cross false i j))
  | .cross (.inl i) (.inr r) => some (.blackRed (false, i) r)
  | .cross (.inr r) (.inl i) => some (.redBlack r (false, i))
  | .cross (.inr _) (.inr _) => none

theorem downMove_words {g : KLR.Diagram.Gen (I ⊕ Fin ℓ)} {h : Move I ℓ}
    (hg : downMove g = some h) :
    h.bottom = g.dom.map DoubleStrand.down ∧ h.top = g.cod.map DoubleStrand.down := by
  cases g with
  | dot i =>
    cases i <;> simp [downMove] at hg
    subst h
    exact ⟨rfl, rfl⟩
  | cross i j =>
    cases i <;> cases j <;> simp [downMove] at hg
    all_goals subst h; exact ⟨rfl, rfl⟩

variable (k : Type w) [CommRing k]

/-- The signed layer of an ordinary generator that survives the translation. -/
def downLayerDiagram (μ : X) (u v : List (DoubleStrand I ℓ))
    (L : Layer (KLR.Diagram.sig (I ⊕ Fin ℓ))) {g : Move I ℓ} (hg : downMove L.gen = some g) :
    downContextObj RD Λ μ u v L.dom ⟶ downContextObj RD Λ μ u v L.cod :=
  Diagram.cast
    (moveDiagram RD Λ μ (u ++ L.left.map DoubleStrand.down) g
      (L.right.map DoubleStrand.down ++ v))
    (by simp [downContextObj, Layer.dom, (downMove_words hg).1, List.append_assoc])
    (by simp [downContextObj, Layer.cod, (downMove_words hg).2, List.append_assoc])

@[simp] theorem layers_downLayerDiagram (μ : X) (u v : List (DoubleStrand I ℓ))
    (L : Layer (KLR.Diagram.sig (I ⊕ Fin ℓ))) {g : Move I ℓ} (hg : downMove L.gen = some g) :
    Diagram.layers (downLayerDiagram RD Λ μ u v L hg) =
      [layer RD Λ μ (u ++ L.left.map DoubleStrand.down) g (L.right.map DoubleStrand.down ++ v)] :=
  rfl

/-- Translate an ordinary layer inside arbitrary signed words. -/
def downLinearLayer (μ : X) (u v : List (DoubleStrand I ℓ))
    (L : Layer (KLR.Diagram.sig (I ⊕ Fin ℓ))) :
    LinDiagram k (downContextObj RD Λ μ u v L.dom) (downContextObj RD Λ μ u v L.cod) :=
  match hg : downMove L.gen with
  | none => 0
  | some _ => LinDiagram.of (downLayerDiagram RD Λ μ u v L hg)

theorem downLinearLayer_of_move (μ : X) (u v : List (DoubleStrand I ℓ))
    (L : Layer (KLR.Diagram.sig (I ⊕ Fin ℓ))) {g : Move I ℓ} (hg : downMove L.gen = some g) :
    downLinearLayer RD Λ k μ u v L = LinDiagram.of (downLayerDiagram RD Λ μ u v L hg) := by
  unfold downLinearLayer
  split
  · rename_i hn
    rw [hg] at hn
    contradiction
  · rename_i g' hg'
    obtain rfl : g' = g := Option.some.inj (hg'.symm.trans hg)
    rfl

theorem downLinearLayer_of_none (μ : X) (u v : List (DoubleStrand I ℓ))
    (L : Layer (KLR.Diagram.sig (I ⊕ Fin ℓ))) (hg : downMove L.gen = none) :
    downLinearLayer RD Λ k μ u v L = 0 := by
  unfold downLinearLayer
  split
  · rfl
  · rename_i g hg'
    rw [hg] at hg'
    contradiction

/-- The interpretation of unweighted layers in the free linear category of double diagrams. -/
def downInterpretation (μ : X) (u v : List (DoubleStrand I ℓ)) :
    Interpretation (KLR.Diagram.sig (I ⊕ Fin ℓ)) (Free k (Obj (signature RD Λ))) where
  obj a := Free.of k (downContextObj RD Λ μ u v a)
  layer L _ := downLinearLayer RD Λ k μ u v L

/-- The linear translation with vertical composition between fixed exterior words. -/
def downLinearFunctor (μ : X) (u v : List (DoubleStrand I ℓ)) :
    Free k (Obj (KLR.Diagram.sig (I ⊕ Fin ℓ))) ⥤ Free k (Obj (signature RD Λ)) :=
  freeLift k (downInterpretation RD Λ k μ u v).functor

instance (μ : X) (u v : List (DoubleStrand I ℓ)) :
    (downLinearFunctor RD Λ k μ u v).Additive :=
  inferInstanceAs (freeLift k (downInterpretation RD Λ k μ u v).functor).Additive

instance (μ : X) (u v : List (DoubleStrand I ℓ)) :
    (downLinearFunctor RD Λ k μ u v).Linear k :=
  (inferInstance : (freeLift k (downInterpretation RD Λ k μ u v).functor).Linear k)

/-- Translate a linear combination of ordinary KLR diagrams. -/
def downLinear (μ : X) (u v : List (DoubleStrand I ℓ))
    {a b : Obj (KLR.Diagram.sig (I ⊕ Fin ℓ))} :
    LinDiagram k a b →ₗ[k]
      LinDiagram k (downContextObj RD Λ μ u v a) (downContextObj RD Λ μ u v b) :=
  (downLinearFunctor RD Λ k μ u v).mapLinearMap k

@[simp] theorem downLinear_comp (μ : X) (u v : List (DoubleStrand I ℓ))
    {a b c : Obj (KLR.Diagram.sig (I ⊕ Fin ℓ))} (f : LinDiagram k a b) (g : LinDiagram k b c) :
    downLinear RD Λ k μ u v (f ≫ g) = downLinear RD Λ k μ u v f ≫ downLinear RD Λ k μ u v g :=
  (downLinearFunctor RD Λ k μ u v).map_comp f g

@[simp] theorem downLinear_id (μ : X) (u v : List (DoubleStrand I ℓ))
    (a : Obj (KLR.Diagram.sig (I ⊕ Fin ℓ))) :
    downLinear RD Λ k μ u v (𝟙 (Free.of k a)) = 𝟙 _ :=
  (downLinearFunctor RD Λ k μ u v).map_id _

@[simp] theorem downLinear_ofLayer (μ : X) (u v : List (DoubleStrand I ℓ))
    (L : Layer (KLR.Diagram.sig (I ⊕ Fin ℓ))) (hv : L.Valid) :
    downLinear RD Λ k μ u v (LinDiagram.of (Diagram.ofLayer L hv)) =
      downLinearLayer RD Λ k μ u v L := by
  exact (freeLift_map_of _ _).trans ((downInterpretation RD Λ k μ u v).functor_map_ofLayer L hv)

/-- A typed ordinary layer translates by sending its two boundary equalities along the
boundary translation. -/
theorem downLinear_layer (μ : X) (u v : List (DoubleStrand I ℓ))
    (L : Layer (KLR.Diagram.sig (I ⊕ Fin ℓ))) (hv : L.Valid)
    {a b : Obj (KLR.Diagram.sig (I ⊕ Fin ℓ))} (ha : L.dom = a) (hb : L.cod = b) :
    downLinear RD Λ k μ u v (LinDiagram.of (Diagram.layer L hv ha hb)) =
      LinDiagram.cast (downLinearLayer RD Λ k μ u v L)
        (congrArg (downContextObj RD Λ μ u v) ha) (congrArg (downContextObj RD Λ μ u v) hb) := by
  subst ha hb
  rw [LinDiagram.cast_rfl]
  exact downLinear_ofLayer RD Λ k μ u v L hv

end Categorification.Stendhal.DoubleDiagram

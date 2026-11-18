/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleDiagram
import Categorification.Diagrams.KL3.SymmetrySigma
import Categorification.Diagrams.KL3.SpanningBasic

/-!
# Black KL diagrams in double Stendhal diagrams

Webster, arXiv:1309.3796v2, §2.1 after Definition 2.2 and §4.5,
Definitions 4.22 and 4.24. The CL convention places the weight of a signed
word on its right. Webster places that weight on its left and reflects the
diagram in a vertical line. In particular, a cup with top `[l, l*]` has
reflected top `[l*, l]`. The same left region and the actual prefix and
suffix of double strands are used through every layer.

This module translates raw black diagrams and their linear combinations.
Scalar equations for those diagrams belong to the local relations of
Definition 4.24.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams CategoryTheory

universe w u v
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
    (RD : WeightDatum C X Y) {ℓ : ℕ} (Λ : Fin ℓ → X)

/-- The left-to-right black word obtained by reflecting a CL word. -/
def blackWord (s : List (Letter I)) : List (DoubleStrand I ℓ) := s.reverse.map Sum.inl

private theorem blackWord_append (s t : List (Letter I)) :
    blackWord (ℓ := ℓ) (s ++ t) = blackWord t ++ blackWord s := by
  simp [blackWord]

/-- The right region of the reflected word is the left region of the CL word. -/
theorem endWeight_blackWord (μ : X) (s : List (Letter I)) :
    endWeight RD Λ μ (blackWord s) = wt RD μ s := by
  induction s with
  | nil => simp [blackWord, endWeight]
  | cons l s ih =>
    simp only [blackWord, List.reverse_cons, List.map_append, List.map_cons, List.map_nil] at *
    rw [endWeight_append, ih, endWeight_cons]
    change (wt RD μ s + sh RD l) + 0 = sh RD l + wt RD μ s
    simp [add_comm]

private def blackLayer (μ : X) (u v : List (DoubleStrand I ℓ)) (x : LayerData I) :
    Layer (signature RD Λ) :=
  layer RD Λ μ (u ++ blackWord x.2.2) (.black (Sig.shape x.2.1)) (blackWord x.1 ++ v)

private theorem blackChain (μ : X) (u v : List (DoubleStrand I ℓ)) {s t : List (Letter I)}
    {xs : List (LayerData I)} (h : SChain s xs t) :
    Chain (obj RD Λ μ (u ++ blackWord s ++ v)) (xs.map (blackLayer RD Λ μ u v))
      (obj RD Λ μ (u ++ blackWord t ++ v)) := by
  induction xs generalizing s with
  | nil => cases h; rfl
  | cons x xs ih =>
    obtain ⟨rfl, h⟩ := h
    refine ⟨layer_valid .., ?_, ?_⟩
    · simp only [blackLayer, layer_dom, Move.bottom, Sig.shape_dom, blackWord_append,
        List.append_assoc]
      rfl
    · rw [blackLayer, layer_cod]
      simpa only [Move.top, Sig.shape_cod, blackWord, List.reverse_append, List.map_append,
        List.append_assoc] using ih h

private def blackLayerData (L : Layer (psig RD)) : LayerData I :=
  (L.left.map Col.l, shapeOf RD L.gen, L.right.map Col.l)

private theorem blackLayerData_lay (μ : X) (x : LayerData I) :
    blackLayerData RD (lay RD μ x.1 x.2.1 x.2.2) = x := by
  obtain ⟨u, g, v⟩ := x
  simp only [blackLayerData, lay, map_l_wd, Prod.mk.injEq, true_and, and_true]
  cases g <;> rfl

private theorem rawBlackChain (μ : X) {s t : List (Letter I)} (d : ob RD μ s ⟶ ob RD μ t) :
    SChain s ((Diagram.layers d).map (blackLayerData RD)) t := by
  obtain ⟨xs, h, rfl⟩ := exists_mkD RD μ d
  simpa [layList, List.map_map, Function.comp_def, blackLayerData_lay] using h

/-- Reflect a CL diagram through the vertical axis and place it between
arbitrary words of double strands. The prefix determines its left weight. -/
def blackDiagram (μ : X) (u v : List (DoubleStrand I ℓ)) {s t : List (Letter I)}
    (d : ob RD (endWeight RD Λ μ u) s ⟶ ob RD (endWeight RD Λ μ u) t) :
    obj RD Λ μ (u ++ blackWord s ++ v) ⟶ obj RD Λ μ (u ++ blackWord t ++ v) :=
  Diagram.mk _ (blackChain RD Λ μ u v (rawBlackChain RD _ d))

/-- An explicit CL diagram reflects its layers in place, swapping their
left and right strands while retaining their vertical order. -/
theorem layers_blackDiagram_mkD (μ : X) (u v : List (DoubleStrand I ℓ))
    {s t : List (Letter I)} (xs : List (LayerData I)) (h : SChain s xs t) :
    Diagram.layers (blackDiagram RD Λ μ u v (mkD RD (endWeight RD Λ μ u) xs h)) =
      xs.map (fun x => layer RD Λ μ (u ++ blackWord x.2.2)
        (.black (Sig.shape x.2.1)) (blackWord x.1 ++ v)) := by
  simp [blackDiagram, layList, List.map_map, Function.comp_def, blackLayerData_lay, blackLayer]

@[simp] theorem blackDiagram_id (μ : X) (u v : List (DoubleStrand I ℓ)) (s : List (Letter I)) :
    blackDiagram RD Λ μ u v (𝟙 (ob RD (endWeight RD Λ μ u) s)) = 𝟙 _ := by
  apply Diagram.ext
  rfl

@[simp] theorem blackDiagram_comp (μ : X) (u v : List (DoubleStrand I ℓ))
    {s t z : List (Letter I)}
    (d : ob RD (endWeight RD Λ μ u) s ⟶ ob RD (endWeight RD Λ μ u) t)
    (e : ob RD (endWeight RD Λ μ u) t ⟶ ob RD (endWeight RD Λ μ u) z) :
    blackDiagram RD Λ μ u v (d ≫ e) = blackDiagram RD Λ μ u v d ≫ blackDiagram RD Λ μ u v e := by
  apply Diagram.ext
  change (((Diagram.layers d ++ Diagram.layers e).map _).map _) = _
  simp [blackDiagram, List.map_append]

/-- Linear extension of reflection and insertion in a double Stendhal diagram. -/
def blackLinear (k : Type w) [CommRing k] (μ : X) (u v : List (DoubleStrand I ℓ))
    {s t : List (Letter I)} :
    LinDiagram k (ob RD (endWeight RD Λ μ u) s) (ob RD (endWeight RD Λ μ u) t) →ₗ[k]
      LinDiagram k (obj RD Λ μ (u ++ blackWord s ++ v)) (obj RD Λ μ (u ++ blackWord t ++ v)) :=
  Finsupp.lmapDomain k k (blackDiagram RD Λ μ u v)

@[simp] theorem blackLinear_of (k : Type w) [CommRing k] (μ : X) (u v : List (DoubleStrand I ℓ))
    {s t : List (Letter I)} (d : ob RD (endWeight RD Λ μ u) s ⟶ ob RD (endWeight RD Λ μ u) t) :
    blackLinear RD Λ k μ u v (LinDiagram.of d) = LinDiagram.of (blackDiagram RD Λ μ u v d) :=
  Finsupp.mapDomain_single

private theorem blackLinear_single (k : Type w) [CommRing k] (μ : X)
    (u v : List (DoubleStrand I ℓ)) {s t : List (Letter I)}
    (d : ob RD (endWeight RD Λ μ u) s ⟶ ob RD (endWeight RD Λ μ u) t) (a : k) :
    blackLinear RD Λ k μ u v (Finsupp.single d a) = Finsupp.single (blackDiagram RD Λ μ u v d) a :=
  Finsupp.mapDomain_single

/-- Vertical composition of linear combinations, including a factorization through the
empty black word, is preserved inside the surrounding strands. -/
theorem blackLinear_comp (k : Type w) [CommRing k] (μ : X) (u v : List (DoubleStrand I ℓ))
    {s t z : List (Letter I)}
    (f : LinDiagram k (ob RD (endWeight RD Λ μ u) s) (ob RD (endWeight RD Λ μ u) t))
    (g : LinDiagram k (ob RD (endWeight RD Λ μ u) t) (ob RD (endWeight RD Λ μ u) z)) :
    blackLinear RD Λ k μ u v (f ≫ g) =
      blackLinear RD Λ k μ u v f ≫ blackLinear RD Λ k μ u v g := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
    erw [Preadditive.add_comp, map_add, map_add, ha, hb, Preadditive.add_comp]
  | single d r =>
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb =>
      erw [Preadditive.comp_add, map_add, map_add, ha, hb, Preadditive.comp_add]
    | single e q =>
      have h₁ := Free.single_comp_single k (Obj (psig RD)) d e r q
      have h₂ := Free.single_comp_single k (Obj (signature RD Λ)) (blackDiagram RD Λ μ u v d)
        (blackDiagram RD Λ μ u v e) r q
      erw [h₁, blackLinear_single, blackLinear_single, blackLinear_single, h₂, blackDiagram_comp]

end Categorification.Stendhal.DoubleDiagram

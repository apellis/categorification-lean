/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleDownWhisker

/-!
# Signed contexts of downward diagrams

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.6, proof of
Lemma 4.29. A KLR diagram permutes the colours of its boundary (`KLR.perm_word_of_hom`), so its
downward translation does not change the region on the right of its strands. Hence the
translation between two signed words `u` and `v` is the translation in the empty context
(with left region the region on the right of `u`), whiskered by `u` and `v`
(`downLinear_eq_whisker`).
-/

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams

universe w u v₁ v₂

variable {I : Type u} {ℓ : ℕ}

/-- The top word of a valid KLR layer is a permutation of its bottom word. -/
theorem perm_cod_word (L : Layer (KLR.Diagram.sig (I ⊕ Fin ℓ))) :
    L.cod.word.Perm L.dom.word := by
  change (L.left ++ L.gen.cod ++ L.right).Perm (L.left ++ L.gen.dom ++ L.right)
  refine (List.Perm.append_left _ ?_).append_right _
  cases L.gen with
  | dot c => exact List.Perm.refl _
  | cross c d => exact List.Perm.swap c d []

/-- **A KLR diagram permutes the colours of its boundary.** -/
theorem perm_word_of_hom {a b : Obj (KLR.Diagram.sig (I ⊕ Fin ℓ))} (d : a ⟶ b) :
    b.word.Perm a.word := by
  obtain ⟨ls, h⟩ := d
  induction ls generalizing a with
  | nil => obtain rfl : a = b := h; exact List.Perm.refl _
  | cons L ls ih =>
    obtain ⟨_, rfl, hc⟩ := h
    exact (ih hc).trans (perm_cod_word L)

variable {C : CartanDatum I} {X : Type v₁} {Y : Type v₂}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)

theorem endWeight_map_down_of_perm (μ : X) {w w' : List (I ⊕ Fin ℓ)} (h : w'.Perm w) :
    endWeight RD Λ μ (w'.map DoubleStrand.down) = endWeight RD Λ μ (w.map DoubleStrand.down) := by
  unfold endWeight
  rw [((h.map DoubleStrand.down).map (DoubleStrand.weight RD Λ)).sum_eq]


theorem endWeight_down_of_hom (μ : X) {a b : Obj (KLR.Diagram.sig (I ⊕ Fin ℓ))} (d : a ⟶ b) :
    endWeight RD Λ μ (b.word.map DoubleStrand.down) =
      endWeight RD Λ μ (a.word.map DoubleStrand.down) :=
  endWeight_map_down_of_perm RD Λ μ (perm_word_of_hom d)

variable (μ : X) (u v : List (DoubleStrand I ℓ)) (τ : X)

/-- The boundary of a downward translation in the signed context `u`, `v` is the boundary in
the empty context, whiskered by `u` and `v`. -/
theorem downContextObj_eq_whisker (x : Obj (KLR.Diagram.sig (I ⊕ Fin ℓ)))
    (hx : endWeight RD Λ (endWeight RD Λ μ u) (x.word.map DoubleStrand.down) = τ) :
    (downContextObj RD Λ (endWeight RD Λ μ u) [] [] x).whisker (obj RD Λ μ u)
        (colours RD Λ τ v) = downContextObj RD Λ μ u v x := by
  subst hx
  simp only [downContextObj, obj, Obj.whisker, colours_append, List.nil_append,
    List.append_nil]
  rw [endWeight_append]
  rfl

theorem downContextObj_whiskerOK (x : Obj (KLR.Diagram.sig (I ⊕ Fin ℓ)))
    (hx : endWeight RD Λ (endWeight RD Λ μ u) (x.word.map DoubleStrand.down) = τ) :
    (downContextObj RD Λ (endWeight RD Λ μ u) [] [] x).WhiskerOK (obj RD Λ μ u)
      (colours RD Λ τ v) := by
  refine ⟨colours_ok .., colours_endR .., ?_⟩
  show (signature RD Λ).ok ((signature RD Λ).endR (endWeight RD Λ μ u : X) (colours RD Λ
    (endWeight RD Λ μ u) ([] ++ x.word.map DoubleStrand.down ++ []))) (colours RD Λ τ v)
  rw [colours_endR]
  simpa [hx] using colours_ok RD Λ τ v

variable (k : Type w) [CommRing k]

/-- One layer of the downward translation in a signed context is the whiskered layer of the
empty context. -/
theorem downLinearLayer_eq_whisker (L : Layer (KLR.Diagram.sig (I ⊕ Fin ℓ)))
    (hL : endWeight RD Λ (endWeight RD Λ μ u) (L.dom.word.map DoubleStrand.down) = τ)
    (hL' : endWeight RD Λ (endWeight RD Λ μ u) (L.cod.word.map DoubleStrand.down) = τ) :
    downLinearLayer RD Λ k μ u v L =
      LinDiagram.cast (LinDiagram.whisker (downLinearLayer RD Λ k (endWeight RD Λ μ u) [] [] L)
          (obj RD Λ μ u) (colours RD Λ τ v) (downContextObj_whiskerOK RD Λ μ u v τ _ hL))
        (downContextObj_eq_whisker RD Λ μ u v τ _ hL)
        (downContextObj_eq_whisker RD Λ μ u v τ _ hL') := by
  cases hg : downMove L.gen with
  | none =>
    rw [downLinearLayer_of_none RD Λ k μ u v L hg, downLinearLayer_of_none RD Λ k _ _ _ L hg]
    erw [LinDiagram.whisker_zero]
    exact Finsupp.mapDomain_zero.symm
  | some g =>
    rw [downLinearLayer_of_move RD Λ k μ u v L hg, downLinearLayer_of_move RD Λ k _ _ _ L hg]
    erw [LinDiagram.whisker_of, LinDiagram.cast_of]
    congr 1
    apply Diagram.ext
    rw [Diagram.layers_cast, layers_downLayerDiagram]
    erw [Diagram.layers_whisker, layers_downLayerDiagram]
    have hb := (downMove_words hg).1
    have hτ : endWeight RD Λ (endWeight RD Λ (endWeight RD Λ (endWeight RD Λ μ u)
        (L.left.map DoubleStrand.down)) g.bottom) (L.right.map DoubleStrand.down) = τ := by
      rw [← hL, hb, ← endWeight_append, ← endWeight_append]
      simp [Layer.dom, List.append_assoc]
    simp only [List.map_cons, List.map_nil, layer, Layer.whisker, obj, List.nil_append,
      List.append_nil, colours_append, endWeight_append, hτ]
    rfl

/-- **The downward translation of a diagram between signed words is the translation in the
empty context, whiskered by the two words.** -/
theorem downLinear_eq_whisker_of {a b : Obj (KLR.Diagram.sig (I ⊕ Fin ℓ))} (d : a ⟶ b)
    (ha : endWeight RD Λ (endWeight RD Λ μ u) (a.word.map DoubleStrand.down) = τ) :
    downLinear RD Λ k μ u v (LinDiagram.of d) =
      LinDiagram.cast (LinDiagram.whisker
          (downLinear RD Λ k (endWeight RD Λ μ u) [] [] (LinDiagram.of d))
          (obj RD Λ μ u) (colours RD Λ τ v) (downContextObj_whiskerOK RD Λ μ u v τ _ ha))
        (downContextObj_eq_whisker RD Λ μ u v τ _ ha)
        (downContextObj_eq_whisker RD Λ μ u v τ _
          ((endWeight_down_of_hom RD Λ _ d).trans ha)) := by
  obtain ⟨ls, h⟩ := d
  induction ls generalizing a with
  | nil =>
    have hab : a = b := h
    subst hab
    have e : (⟨[], h⟩ : a ⟶ a) = 𝟙 a := Diagram.ext rfl
    rw [e]
    erw [downLinear_id, downLinear_id]
    show LinDiagram.of (𝟙 _) = LinDiagram.cast (LinDiagram.whisker (LinDiagram.of (𝟙 _)) _ _ _) _ _
    erw [LinDiagram.whisker_of, LinDiagram.cast_of]
    congr 1
  | cons L ls ih =>
    obtain ⟨hv, rfl, hc⟩ := h
    have e : (⟨L :: ls, ⟨hv, rfl, hc⟩⟩ : L.dom ⟶ b) = Diagram.ofLayer L hv ≫ ⟨ls, hc⟩ :=
      Diagram.ext rfl
    have hL' : endWeight RD Λ (endWeight RD Λ μ u) (L.cod.word.map DoubleStrand.down) = τ :=
      (endWeight_map_down_of_perm RD Λ _ (perm_cod_word L)).trans ha
    rw [e, LinDiagram.of_comp, downLinear_comp, downLinear_comp, downLinear_ofLayer,
      downLinear_ofLayer, ih hL' hc, downLinearLayer_eq_whisker RD Λ μ u v τ k L ha hL',
      LinDiagram.whisker_comp _ _ _ _ (downContextObj_whiskerOK RD Λ μ u v τ _ ha)
        (downContextObj_whiskerOK RD Λ μ u v τ _ hL')]
    simp only [LinDiagram.cast_eq_comp, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]

/-- **The downward translation of a linear combination between signed words is the
translation in the empty context, whiskered by the two words.** -/
theorem downLinear_eq_whisker {a b : Obj (KLR.Diagram.sig (I ⊕ Fin ℓ))} (f : LinDiagram k a b)
    (ha : endWeight RD Λ (endWeight RD Λ μ u) (a.word.map DoubleStrand.down) = τ)
    (hb : endWeight RD Λ (endWeight RD Λ μ u) (b.word.map DoubleStrand.down) = τ) :
    downLinear RD Λ k μ u v f =
      LinDiagram.cast (LinDiagram.whisker (downLinear RD Λ k (endWeight RD Λ μ u) [] [] f)
          (obj RD Λ μ u) (colours RD Λ τ v) (downContextObj_whiskerOK RD Λ μ u v τ _ ha))
        (downContextObj_eq_whisker RD Λ μ u v τ _ ha)
        (downContextObj_eq_whisker RD Λ μ u v τ _ hb) := by
  induction f using Finsupp.induction_linear with
  | zero =>
    rw [map_zero, map_zero]
    erw [LinDiagram.whisker_zero]
    exact Finsupp.mapDomain_zero.symm
  | add f g hf hg =>
    rw [map_add, hf, hg, map_add]
    erw [LinDiagram.whisker_add, LinDiagram.cast_add]
  | single d r =>
    have e : (Finsupp.single d r : LinDiagram k a b) = r • LinDiagram.of d :=
      (Finsupp.smul_single_one d r).symm
    rw [e]
    erw [map_smul, map_smul, LinDiagram.whisker_smul, LinDiagram.cast_smul,
      downLinear_eq_whisker_of RD Λ μ u v τ k d ha]
    rfl

end Categorification.Stendhal.DoubleDiagram

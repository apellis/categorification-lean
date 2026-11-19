/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleDownDiagram

/-!
# Whiskering and the downward translation

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §4.5,
proof of Lemma 4.28. Translating an ordinary KLR diagram whiskered by `a` on the left and
`b` on the right between the signed words `u` and `v` is the same as translating the
unwhiskered diagram between `u ++ a↓` and `b↓ ++ v` (`downLinear_whisker`). Thus every
relation of the tensor ideal of the KLR presentation is translated as an unwhiskered
relation in a larger signed context.
-/

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams

universe w u v₁ v₂

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X : Type v₁} {Y : Type v₂}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)
  (k : Type w) [CommRing k] (μ : X) (u v : List (DoubleStrand I ℓ))

/-- The boundary of a whiskered ordinary object, read in the larger signed context. -/
theorem downContextObj_whisker (a a' : Obj (KLR.Diagram.sig (I ⊕ Fin ℓ)))
    (b' : List (I ⊕ Fin ℓ)) :
    downContextObj RD Λ μ (u ++ a'.word.map DoubleStrand.down)
        (b'.map DoubleStrand.down ++ v) a =
      downContextObj RD Λ μ u v (a.whisker a' b') := by
  simp [downContextObj, List.append_assoc]

theorem downLinearLayer_whisker (L : Layer (KLR.Diagram.sig (I ⊕ Fin ℓ)))
    (a' : Obj (KLR.Diagram.sig (I ⊕ Fin ℓ))) (b' : List (I ⊕ Fin ℓ)) :
    downLinearLayer RD Λ k μ u v (L.whisker a' b') =
      LinDiagram.cast (downLinearLayer RD Λ k μ (u ++ a'.word.map DoubleStrand.down)
          (b'.map DoubleStrand.down ++ v) L)
        ((downContextObj_whisker RD Λ μ u v L.dom a' b').trans
          (congrArg (downContextObj RD Λ μ u v) (Layer.whisker_dom L a' b').symm))
        ((downContextObj_whisker RD Λ μ u v L.cod a' b').trans
          (congrArg (downContextObj RD Λ μ u v) (Layer.whisker_cod L a' b').symm)) := by
  cases hg : downMove L.gen with
  | none =>
    rw [downLinearLayer_of_none RD Λ k μ u v (L.whisker a' b') hg,
      downLinearLayer_of_none RD Λ k μ _ _ L hg]
    exact (Finsupp.mapDomain_zero).symm
  | some g =>
    rw [downLinearLayer_of_move RD Λ k μ u v (L.whisker a' b') hg,
      downLinearLayer_of_move RD Λ k μ _ _ L hg, LinDiagram.cast_of]
    congr 1
    apply Diagram.ext
    rw [Diagram.layers_cast, layers_downLayerDiagram]
    simp [Layer.whisker, List.append_assoc]

private theorem whisker_ofLayer_comp (L : Layer (KLR.Diagram.sig (I ⊕ Fin ℓ))) (hv : L.Valid)
    {b : Obj (KLR.Diagram.sig (I ⊕ Fin ℓ))} (d : L.cod ⟶ b)
    (a' : Obj (KLR.Diagram.sig (I ⊕ Fin ℓ))) (b' : List (I ⊕ Fin ℓ))
    (hw : L.dom.WhiskerOK a' b') :
    Diagram.whisker (Diagram.ofLayer L hv ≫ d) a' b' hw =
      Diagram.layer (L.whisker a' b') (hv.whisker hw) (Layer.whisker_dom L a' b')
          (Layer.whisker_cod L a' b') ≫
        Diagram.whisker d a' b' ((Diagram.chain (Diagram.ofLayer L hv)).whiskerOK hw) := by
  rw [Diagram.whisker_comp]
  congr 1

/-- **Whiskering commutes with the downward translation**, diagram by diagram. -/
theorem downLinear_whisker_of (a' : Obj (KLR.Diagram.sig (I ⊕ Fin ℓ)))
    (b' : List (I ⊕ Fin ℓ)) {a b : Obj (KLR.Diagram.sig (I ⊕ Fin ℓ))} (d : a ⟶ b)
    (hw : a.WhiskerOK a' b') :
    downLinear RD Λ k μ u v (LinDiagram.of (Diagram.whisker d a' b' hw)) =
      LinDiagram.cast (downLinear RD Λ k μ (u ++ a'.word.map DoubleStrand.down)
          (b'.map DoubleStrand.down ++ v) (LinDiagram.of d))
        (downContextObj_whisker RD Λ μ u v a a' b')
        (downContextObj_whisker RD Λ μ u v b a' b') := by
  obtain ⟨ls, h⟩ := d
  induction ls generalizing a with
  | nil =>
    have hab : a = b := h
    subst hab
    have e : (⟨[], h⟩ : a ⟶ a) = 𝟙 a := Diagram.ext rfl
    rw [e, Diagram.whisker_id]
    erw [downLinear_id, downLinear_id]
    rw [LinDiagram.cast_eq_comp]
    simp
  | cons L ls ih =>
    obtain ⟨hv, rfl, hc⟩ := h
    have e : (⟨L :: ls, ⟨hv, rfl, hc⟩⟩ : L.dom ⟶ b) = Diagram.ofLayer L hv ≫ ⟨ls, hc⟩ :=
      Diagram.ext rfl
    rw [e, whisker_ofLayer_comp, LinDiagram.of_comp, LinDiagram.of_comp, downLinear_comp,
      downLinear_comp, downLinear_layer, downLinear_ofLayer, ih _ hc, downLinearLayer_whisker]
    simp only [LinDiagram.cast_eq_comp, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]

private theorem downLinear_whisker_single (a' : Obj (KLR.Diagram.sig (I ⊕ Fin ℓ)))
    (b' : List (I ⊕ Fin ℓ)) {a b : Obj (KLR.Diagram.sig (I ⊕ Fin ℓ))} (d : a ⟶ b) (r : k)
    (hw : a.WhiskerOK a' b') :
    downLinear RD Λ k μ u v (LinDiagram.whisker (Finsupp.single d r : LinDiagram k a b) a' b' hw) =
      LinDiagram.cast (downLinear RD Λ k μ (u ++ a'.word.map DoubleStrand.down)
          (b'.map DoubleStrand.down ++ v) (Finsupp.single d r : LinDiagram k a b))
        (downContextObj_whisker RD Λ μ u v a a' b')
        (downContextObj_whisker RD Λ μ u v b a' b') := by
  have e : (Finsupp.single d r : LinDiagram k a b) = r • LinDiagram.of d :=
    (Finsupp.smul_single_one d r).symm
  rw [e, LinDiagram.whisker_smul, map_smul, map_smul,
    LinDiagram.cast_smul]
  rw [LinDiagram.whisker_of]
  exact congrArg (r • ·) (downLinear_whisker_of RD Λ k μ u v a' b' d hw)

/-- **Whiskering commutes with the downward translation.** A whiskered linear combination
of ordinary diagrams translates as the unwhiskered combination in the larger signed
context. -/
theorem downLinear_whisker (a' : Obj (KLR.Diagram.sig (I ⊕ Fin ℓ)))
    (b' : List (I ⊕ Fin ℓ)) {a b : Obj (KLR.Diagram.sig (I ⊕ Fin ℓ))} (f : LinDiagram k a b)
    (hw : a.WhiskerOK a' b') :
    downLinear RD Λ k μ u v (LinDiagram.whisker f a' b' hw) =
      LinDiagram.cast (downLinear RD Λ k μ (u ++ a'.word.map DoubleStrand.down)
          (b'.map DoubleStrand.down ++ v) f)
        (downContextObj_whisker RD Λ μ u v a a' b')
        (downContextObj_whisker RD Λ μ u v b a' b') := by
  induction f using Finsupp.induction_linear with
  | zero =>
    rw [LinDiagram.whisker_zero, map_zero, map_zero]
    exact Finsupp.mapDomain_zero.symm
  | add f g hf hg =>
    rw [LinDiagram.whisker_add, map_add, hf, hg, map_add, LinDiagram.cast_add]
  | single d r =>
    exact downLinear_whisker_single RD Λ k μ u v a' b' d r hw

end Categorification.Stendhal.DoubleDiagram

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleDownRelations
import Categorification.WeightedKLR.RedStrands.DoubleDiagramCut

/-!
# Reading a downward double diagram as an ordinary diagram

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
§4.5, proof of Lemma 4.28. A double diagram whose layers are downward dots
and crossings can be read as an ordinary Stendhal diagram. This is the last
step of the surjectivity argument once the relations have removed the cups,
caps and upward strands.
-/

-- Matching well-formed layers uses both signatures and the dependent boundary equalities.
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams

universe w u v₁ v₂

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X : Type v₁} {Y : Type v₂}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)
  (k : Type w) [CommRing k] (μ : X)

local notation "S" => KLR.Diagram.sig (I ⊕ Fin ℓ)
local notation "T" => signature RD Λ
local notation "O" => downContextObj RD Λ μ [] []

private theorem map_erase_down (w : List (I ⊕ Fin ℓ)) :
    (w.map DoubleStrand.down).map DoubleStrand.erase = w := by
  induction w <;> simp [*]

private theorem map_down_erase_of_subset {p : List (DoubleStrand I ℓ)} {z : List (I ⊕ Fin ℓ)}
    (h : p ⊆ z.map DoubleStrand.down) :
    (p.map DoubleStrand.erase).map DoubleStrand.down = p := by
  rw [List.map_map]
  refine (List.map_congr_left (g := id) (fun s hs => ?_)).trans (List.map_id p)
  obtain ⟨r, -, rfl⟩ := List.mem_map.mp (h hs)
  simp

private theorem recoverLabelledWord (x : X) (w : List (X × DoubleStrand I ℓ))
    (hw : (T).ok x w) : colours RD Λ x (w.map Prod.snd) = w := by
  induction w generalizing x with
  | nil => rfl
  | cons a w ih =>
    obtain ⟨t, a⟩ := a
    obtain ⟨rfl, hw⟩ := hw
    exact congrArg ((t, a) :: ·) (ih _ hw)

private theorem layer_eq_context (L : Layer T) (hv : L.Valid) :
    layer RD Λ L.start (L.left.map Prod.snd) L.gen.2 (L.right.map Prod.snd) = L := by
  have hl := recoverLabelledWord RD Λ L.start L.left hv.left_ok
  have hgen : endWeight RD Λ L.start (L.left.map Prod.snd) = L.gen.1 := by
    rw [← colours_endR, hl]
    exact hv.left_end
  apply Layer.ext
  · rfl
  · exact hl
  · exact Prod.ext hgen rfl
  · change colours RD Λ (endWeight RD Λ (endWeight RD Λ L.start (L.left.map Prod.snd))
      L.gen.2.bottom) (L.right.map Prod.snd) = L.right
    rw [hgen]
    exact recoverLabelledWord RD Λ _ L.right hv.right_ok

private theorem downContextObj_injective : Function.Injective (O : Obj S → Obj T) := by
  intro a b h
  apply KLR.Diagram.obj_ext
  have he := congrArg (fun z : Obj T => (z.word.map Prod.snd).map DoubleStrand.erase) h
  simpa only [downContextObj, obj, List.nil_append, List.append_nil, forget_colours,
    map_erase_down] using he

private theorem exists_downLayerLift {a : Obj S} (L : Layer T) (hv : L.Valid)
    (ha : L.dom = O a) (g : KLR.Diagram.Gen (I ⊕ Fin ℓ)) (hg : downMove g = some L.gen.2) :
    ∃ (b : Obj S) (hb : L.cod = O b) (f : a ⟶ b),
      downLinear RD Λ k μ [] [] (LinDiagram.of f) =
        LinDiagram.of (Diagram.layer L hv ha hb) := by
  let p : List (DoubleStrand I ℓ) := L.left.map Prod.snd
  let q : List (DoubleStrand I ℓ) := L.right.map Prod.snd
  have hsplit : p ++ g.dom.map DoubleStrand.down ++ q = a.word.map DoubleStrand.down := by
    have he := congrArg (fun z : Obj T => z.word.map Prod.snd) ha
    simpa only [Layer.dom_word, List.map_append, signature, forget_colours, downContextObj,
      obj, List.nil_append, List.append_nil, (downMove_words hg).1] using he
  have hp : (p.map DoubleStrand.erase).map DoubleStrand.down = p := by
    apply map_down_erase_of_subset (z := a.word)
    intro s hs
    rw [← hsplit]
    simp [hs]
  have hq : (q.map DoubleStrand.erase).map DoubleStrand.down = q := by
    apply map_down_erase_of_subset (z := a.word)
    intro s hs
    rw [← hsplit]
    simp [hs]
  let K := KLR.Diagram.lay (p.map DoubleStrand.erase) g (q.map DoubleStrand.erase)
  have hKdom : K.dom = a := by
    apply KLR.Diagram.obj_ext
    simpa only [K, Layer.dom_word, KLR.Diagram.lay_left, KLR.Diagram.lay_gen,
      KLR.Diagram.lay_right, KLR.Diagram.sig_dom, List.map_append, map_erase_down] using
      congrArg (List.map DoubleStrand.erase) hsplit
  have hstart : L.start = μ := congrArg Obj.start ha
  have hKcod : L.cod = O K.cod := by
    rw [← layer_eq_context RD Λ L hv, layer_cod]
    simp only [hstart, K, Layer.cod_word, KLR.Diagram.lay_left, KLR.Diagram.lay_gen,
      KLR.Diagram.lay_right, downContextObj, List.nil_append,
      List.append_nil, List.map_append, hp, hq, ← (downMove_words hg).2]
    rfl
  refine ⟨K.cod, hKcod, Diagram.layer K (Layer.valid_of_subsingleton _) hKdom rfl, ?_⟩
  rw [downLinear_layer, downLinearLayer_of_move _ _ _ _ _ _ _ hg, LinDiagram.cast_of]
  apply congrArg LinDiagram.of
  apply Diagram.ext
  simp only [Diagram.layers_cast, layers_downLayerDiagram, Diagram.layers_layer,
    K, KLR.Diagram.lay_left, KLR.Diagram.lay_right, List.nil_append, List.append_nil,
    hp, hq, ← hstart]
  exact congrArg (fun M => [M]) (layer_eq_context RD Λ L hv)

private theorem exists_downChainLift {a b : Obj S} {ls : List (Layer T)}
    (h : Chain (O a) ls (O b))
    (hdown : ∀ L ∈ ls, ∃ g, downMove g = some L.gen.2) :
    ∃ f : a ⟶ b, downLinear RD Λ k μ [] [] (LinDiagram.of f) =
      LinDiagram.of (Diagram.mk ls h) := by
  induction ls generalizing a with
  | nil =>
    obtain rfl : a = b := downContextObj_injective RD Λ μ h
    exact ⟨𝟙 _, downLinear_id RD Λ k μ [] [] _⟩
  | cons L ls ih =>
    obtain ⟨g, hg⟩ := hdown L (by simp)
    obtain ⟨c, hc, f, hf⟩ := exists_downLayerLift RD Λ k μ L h.1 h.2.1 g hg
    have hrest : Chain (O c) ls (O b) := hc ▸ h.2.2
    obtain ⟨d, hd⟩ := ih hrest (fun M hM => hdown M (List.mem_cons_of_mem _ hM))
    refine ⟨f ≫ d, ?_⟩
    rw [LinDiagram.of_comp, downLinear_comp, hf, hd, ← LinDiagram.of_comp]
    apply congrArg LinDiagram.of
    apply Diagram.ext
    rfl

/-- A signed diagram on all-down boundaries whose layers are downward dots and crossings
is the image of an ordinary KLR diagram. -/
theorem exists_downDiagramLift {a b : Obj S} (d : O a ⟶ O b)
    (h : ∀ L ∈ Diagram.layers d, ∃ g, downMove g = some L.gen.2) :
    ∃ f : a ⟶ b, downLinear RD Λ k μ [] [] (LinDiagram.of f) = LinDiagram.of d := by
  obtain ⟨ls, hd⟩ := d
  exact exists_downChainLift RD Λ k μ hd h

/-- The class of a raw diagram with downward layers has a preimage under the ordinary
presented functor. -/
theorem exists_downPresentedLift (Q : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k)
    (P : Presentation.{w, max u v₁} T k) {a b : Obj S} (d : O a ⟶ O b)
    (h : ∀ L ∈ Diagram.layers d, ∃ g, downMove g = some L.gen.2) :
    ∃ f : (KLR.Diagram.pres k Q).obj a ⟶ (KLR.Diagram.pres k Q).obj b,
      (downPresentedFunctor RD Λ Q P μ [] []).map f = (addDownRelations RD Λ Q P).diag d := by
  obtain ⟨f, hf⟩ := exists_downDiagramLift RD Λ k μ d h
  refine ⟨(KLR.Diagram.pres k Q).diag f, ?_⟩
  rw [Presentation.diag, downPresentedFunctor_lin, hf, Presentation.lin_of]

end Categorification.Stendhal.DoubleDiagram

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleBlackAction
import Categorification.WeightedKLR.RedStrands.DoubleAllDownMap
import Categorification.WeightedKLR.RedStrands.BlackInduction

/-!
# The black action on all-down boundaries

Webster, arXiv:1309.3796v3, §4.5, Theorem 4.31, and §5, the module functors `Fᵢ`. The
action of the Khovanov–Lauda word `Fᵢ` appends one downward black strand of colour `i` on the
right of every boundary. On an all-down boundary with loading `s` this is the all-down
boundary of the loading `s` followed by `i` (`Stendhal.appendBlackLoading`), and on a single
displayed layer it is the same layer with the new strand added on its right.
-/

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams KLR KLR.Diagram KL3.Diagram

universe u v

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}}

section Whisker

variable {k : Type*} [CommRing k] (L : Fin ℓ → X) (Pr : Presentation (signature RD L) k)

/-- A layer with a word added on its right, as a layer with an extended right part. -/
theorem layer_wr {μ ν : X} (u : List (DoubleStrand I ℓ)) (g : Move I ℓ)
    (v v' : List (DoubleStrand I ℓ)) (h : endWeight RD L μ (u ++ g.bottom ++ v) = ν) :
    (layer RD L μ u g v).wr (obj RD L ν v').word = layer RD L μ u g (v ++ v') := by
  rw [endWeight_append, endWeight_append] at h
  simp only [layer, Layer.wr, obj, colours_append, h]
  rfl

private theorem tensor_obj {μ ν : X} {w : List (DoubleStrand I ℓ)}
    (h : endWeight RD L μ w = ν) (v : List (DoubleStrand I ℓ)) :
    (obj RD L μ w).tensor (obj RD L ν v) = obj RD L μ (w ++ v) := by
  subst h; simp only [obj, Obj.tensor, colours_append]; rfl

/-- Right whiskering a single layer by the identity of a word extends its right part. -/
theorem wRAt_layer {μ ν : X} (u : List (DoubleStrand I ℓ)) (g : Move I ℓ)
    (v v' : List (DoubleStrand I ℓ)) {w w' : List (DoubleStrand I ℓ)}
    (hw : u ++ g.bottom ++ v = w) (hw' : u ++ g.top ++ v = w')
    (h : endWeight RD L μ w = ν) :
    Pr.wRAt μ (Pr.layer (layer RD L μ u g v) (layer_valid ..)
        ((layer_dom ..).trans (congrArg (obj RD L μ) hw))
        ((layer_cod ..).trans (congrArg (obj RD L μ) hw')))
      (obj RD L ν v') rfl rfl =
      Pr.layer (layer RD L μ u g (v ++ v')) (layer_valid ..)
        ((layer_dom ..).trans (by rw [tensor_obj L h, ← hw]; simp))
        ((layer_cod ..).trans (by
          rw [tensor_obj L (?_ : endWeight RD L μ w' = ν), ← hw']; · simp
          rw [← hw', ← h, ← hw, endWeight_append, endWeight_append, endWeight_append,
            endWeight_append, g.endWeight_top])) := by
  have hc : (obj RD L μ w).Composable (obj RD L ν v') :=
    ⟨colours_ok .., (colours_endR ..).trans h, colours_ok ..⟩
  refine (Pr.wRAt_diag (r := μ) (Diagram.layer _ _ _ _) _ hc rfl rfl).trans ?_
  apply Pr.diag_eq_of_layers_eq
  rw [Diagram.layers_rwhisker]
  change [(layer RD L μ u g v).wr (obj RD L ν v').word] = [layer RD L μ u g (v ++ v')]
  rw [layer_wr L u g v v' (hw ▸ h)]

theorem eqToHom_comp_layer_comp_eqToHom {a a' b b' : Obj (signature RD L)}
    (M : Layer (signature RD L)) (hv : M.Valid) (ha : M.dom = a) (hb : M.cod = b)
    (ha' : M.dom = a') (hb' : M.cod = b') (h : Pr.obj a' = Pr.obj a)
    (h' : Pr.obj b = Pr.obj b') :
    eqToHom h ≫ Pr.layer M hv ha hb ≫ eqToHom h' = Pr.layer M hv ha' hb' := by
  subst ha ha' hb hb'; simp

theorem eqToHom_comp_layer {a a' b : Obj (signature RD L)} (M : Layer (signature RD L))
    (hv : M.Valid) (ha : M.dom = a) (hb : M.cod = b) (h : Pr.obj a' = Pr.obj a) (e : a' = a) :
    eqToHom h ≫ Pr.layer M hv ha hb = Pr.layer M hv (ha.trans e.symm) hb := by
  subst e; simp

theorem layer_comp_eqToHom {a b b' : Obj (signature RD L)} (M : Layer (signature RD L))
    (hv : M.Valid) (ha : M.dom = a) (hb : M.cod = b) (h : Pr.obj b = Pr.obj b') (e : b = b') :
    Pr.layer M hv ha hb ≫ eqToHom h = Pr.layer M hv ha (hb.trans e) := by
  subst e; simp

end Whisker

section Boundary

variable {k : Type*} [CommRing k] (P : Presentation (signature RD (fun r => (Λ r).val)) k)

/-- A signed layer between two double Stendhal triples whose words are its boundaries. -/
def boundaryLayer {μ : X} (b c : DoubleStendhalTriple RD Λ 0 μ) (u : List (DoubleStrand I ℓ))
    (g : Move I ℓ) (v : List (DoubleStrand I ℓ)) (hs : u ++ g.bottom ++ v = b.val.word)
    (ht : u ++ g.top ++ v = c.val.word) :
    (violatingFunctor P μ).obj b ⟶ (violatingFunctor P μ).obj c :=
  (violatingFunctor P _).map (InducedCategory.homMk
    (P.layer (layer RD (fun r => (Λ r).val) 0 u g v) (layer_valid ..)
      ((layer_dom ..).trans (congrArg (obj RD (fun r => (Λ r).val) 0) hs))
      ((layer_cod ..).trans (congrArg (obj RD (fun r => (Λ r).val) 0) ht))))

/-- Right whiskering by a red-free word extends the right part of a boundary layer. -/
theorem violatingWhiskerRight_boundaryLayer {μ ν : X} (w : List (DoubleStrand I ℓ))
    (hw : RedFree w) (hν : endWeight RD (fun r => (Λ r).val) μ w = ν)
    (b c : DoubleStendhalTriple RD Λ 0 μ) (u : List (DoubleStrand I ℓ)) (g : Move I ℓ)
    (v : List (DoubleStrand I ℓ)) (hs : u ++ g.bottom ++ v = b.val.word)
    (ht : u ++ g.top ++ v = c.val.word) :
    (violatingWhiskerRight P w hw hν).map (boundaryLayer P b c u g v hs ht) =
      boundaryLayer P (appendRight w hw hν b) (appendRight w hw hν c) u g (v ++ w)
        (by rw [← List.append_assoc, hs]; rfl) (by rw [← List.append_assoc, ht]; rfl) := by
  change (violatingFunctor P ν).map (whiskerRightHom P w hw hν _) = _
  congr 1
  unfold whiskerRightHom
  congr 1
  erw [wRAt_layer _ P u g v w hs ht (endWeight_word b)]
  exact eqToHom_comp_layer_comp_eqToHom _ P _ _ _ _ _ _ _ _

/-- A boundary layer along equalities of its boundary triples. -/
theorem boundaryLayer_congr {μ : X} {b b' c c' : DoubleStendhalTriple RD Λ 0 μ} (hb : b = b')
    (hc : c = c') (u : List (DoubleStrand I ℓ)) (g : Move I ℓ) (v : List (DoubleStrand I ℓ))
    (hs : u ++ g.bottom ++ v = b.val.word) (ht : u ++ g.top ++ v = c.val.word) :
    boundaryLayer P b c u g v hs ht = eqToHom (by rw [hb]) ≫
      boundaryLayer P b' c' u g v (hb ▸ hs) (hc ▸ ht) ≫ eqToHom (by rw [hc]) := by
  subst hb hc
  simp

end Boundary

section Loading

variable (i : I) (ν : Multiset I)

/-- The word of the loading with an appended black strand. -/
theorem ofFn_appendBlackLoading (s : Seq (stendhalWeight ℓ ν)) :
    List.ofFn (appendBlackLoading i ν s).lbl = List.ofFn s.lbl ++ [.inl i] := by
  apply List.ext_get
  · simp [stendhalWeight]
  · intro n h₁ h₂
    simp only [List.get_eq_getElem, List.getElem_ofFn]
    by_cases hn : n < Multiset.card (stendhalWeight ℓ ν)
    · rw [List.getElem_append_left (by simpa using hn), List.getElem_ofFn,
        appendBlackLoading_lbl_of_lt i ν s _ hn]
    · have hn' : n = Multiset.card (stendhalWeight ℓ ν) := by
        simp only [List.length_ofFn] at h₁; simp [stendhalWeight] at h₁ hn ⊢; omega
      rw [List.getElem_append_right (by simpa using Nat.le_of_not_lt hn),
        appendBlackLoading_lbl_of_eq i ν s _ hn']
      simp [hn']

end Loading

/-- The weight equation of the word `Fᵢ` between the all-down weights. -/
theorem wt_downRightWeight (i : I) (ν : Multiset I) :
    wt RD (downRightWeight RD Λ ν) [(false, i)] = downRightWeight RD Λ ({i} + ν) := by
  simp only [wt_cons, wt_nil, sh, downRightWeight, Multiset.map_add, Multiset.map_singleton,
    Multiset.sum_add, Multiset.sum_singleton]
  change (-1 : ℤ) • RD.iX i + _ = _
  abel

/-- Appending `Fᵢ` to an all-down triple gives the all-down triple of the appended loading. -/
theorem appendRight_downTriple (i : I) (ν : Multiset I)
    (s : {s : Seq (stendhalWeight ℓ ν) // IsRedOrdered s}) :
    appendRight (blackWord [(false, i)]) (blackWord_redFree _)
        ((endWeight_blackWord RD _ _ _).trans (wt_downRightWeight i ν)) (downTriple RD Λ s) =
      downTriple RD Λ ⟨appendBlackLoading i ν s.val, appendBlackLoading_ordered i ν s.val
        s.property⟩ := by
  apply Subtype.ext
  apply DoubleBoundary.ext
  change (List.ofFn s.val.lbl).map DoubleStrand.down ++ _ =
    (List.ofFn (appendBlackLoading i ν s.val).lbl).map DoubleStrand.down
  rw [ofFn_appendBlackLoading]
  simp [blackWord, DoubleStrand.down]

section Down

variable {k : Type*} [CommRing k] (P : Presentation (signature RD (fun r => (Λ r).val)) k)
  (i : I) {ν : Multiset I}

/-- The all-down loading with a downward black strand of colour `i` appended on the right. -/
abbrev appendDown (s : {s : Seq (stendhalWeight ℓ ν) // IsRedOrdered s}) :
    {s : Seq (stendhalWeight ℓ ({i} + ν)) // IsRedOrdered s} :=
  ⟨appendBlackLoading i ν s.val, appendBlackLoading_ordered i ν s.val s.property⟩

/-- The action of `Fᵢ` on an all-down boundary object. -/
theorem blackAct_downObj (s : {s : Seq (stendhalWeight ℓ ν) // IsRedOrdered s}) :
    (blackAct P [(false, i)] (wt_downRightWeight i ν)).obj (downObj P s) =
      downObj P (appendDown i s) :=
  congrArg (violatingFunctor P _).obj (appendRight_downTriple i ν s)

theorem word_appendDown (s : {s : Seq (stendhalWeight ℓ ν) // IsRedOrdered s}) :
    (word (appendDown i s).val).map DoubleStrand.down =
      (word s.val).map DoubleStrand.down ++ [.inl (false, i)] := by
  simp only [word, ofFn_appendBlackLoading, List.map_append]
  rfl

/-- The action of `Fᵢ` on a displayed all-down layer adds the new strand on its right. -/
theorem blackAct_downLayer (s t : {s : Seq (stendhalWeight ℓ ν) // IsRedOrdered s})
    (u : List (DoubleStrand I ℓ)) (g : Move I ℓ) (v : List (DoubleStrand I ℓ))
    (hs : u ++ g.bottom ++ v = (word s.val).map DoubleStrand.down)
    (ht : u ++ g.top ++ v = (word t.val).map DoubleStrand.down) :
    (blackAct P [(false, i)] (wt_downRightWeight i ν)).map (downLayer P s t u g v hs ht) =
      eqToHom (blackAct_downObj P i s) ≫
        downLayer P (appendDown i s) (appendDown i t) u g (v ++ [.inl (false, i)])
          (by rw [word_appendDown, ← hs]; simp only [List.append_assoc])
          (by rw [word_appendDown, ← ht]; simp only [List.append_assoc]) ≫
        eqToHom (blackAct_downObj P i t).symm := by
  change (violatingWhiskerRight P _ _ _).map (boundaryLayer P (downTriple RD Λ s)
    (downTriple RD Λ t) u g v hs ht) = _
  refine (violatingWhiskerRight_boundaryLayer P _ _ _ (downTriple RD Λ s) (downTriple RD Λ t)
    u g v hs ht).trans ?_
  exact boundaryLayer_congr P (appendRight_downTriple i ν s) (appendRight_downTriple i ν t) _ _ _
    _ _

end Down

end Categorification.Stendhal.DoubleDiagram

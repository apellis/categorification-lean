/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleBlackDiagram
import Categorification.WeightedKLR.RedStrands.DoubleViolatedCut
import StringDiagrams.Generation

/-!
# Reduction to black diagrams with one red strand

Webster, arXiv:1309.3796v3, Definition 4.26 and Lemma 4.29. With one red
strand a raw signed diagram either has a cut with a black strand at the
far left, or has a fixed leftmost red strand and is a black KL diagram
inserted to its right. This reduction precedes the black straightening
and bubble removal in the proof of surjectivity.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (Λ : Fin 1 → X)

private abbrev red : DoubleStrand I 1 := Sum.inr 0
private abbrev redPrefix : List (DoubleStrand I 1) := [red]
private abbrev redObj (s : List (Letter I)) := obj RD Λ 0 (redPrefix ++ blackWord s ++ [])
private abbrev η := endWeight RD Λ 0 (redPrefix (I := I))
local notation "S" => signature RD Λ
local notation "O" => redObj RD Λ

private theorem no_red_iff_black (w : List (DoubleStrand I 1)) :
    w.filterMap DoubleStrand.redLabel = [] → ∃ a : List (Letter I), blackWord a = w := by
  induction w with
  | nil => exact fun _ => ⟨[], rfl⟩
  | cons x w ih =>
    cases x with
    | inl c =>
      intro h
      obtain ⟨a, ha⟩ := ih h
      exact ⟨a ++ [c], by simp [blackWord, ← ha]⟩
    | inr r => simp [DoubleStrand.redLabel]

private theorem recover_labelled (μ : X) (w : List (X × DoubleStrand I 1)) (hw : (S).ok μ w) :
    colours RD Λ μ (w.map Prod.snd) = w := by
  induction w generalizing μ with
  | nil => rfl
  | cons c w ih =>
    obtain ⟨rfl, hw⟩ := hw
    exact congrArg ((c.1, c.2) :: ·) (ih _ hw)

private theorem head_black_or_red (a : Obj S) (h : (a.word.map Prod.snd).filterMap
    DoubleStrand.redLabel = [0]) (hstart : a.start = (0 : X)) (hok : (S).ok a.start a.word) :
    (∃ l, (a.word.map Prod.snd).head? = some (.inl l)) ∨ ∃ s, a = O s := by
  have hw := recover_labelled RD Λ a.start a.word hok
  rw [hstart] at hw
  generalize hz : a.word.map Prod.snd = z at h hw ⊢
  cases z with
  | nil => simp at h
  | cons x z =>
    cases x with
    | inl l => exact Or.inl ⟨l, rfl⟩
    | inr r =>
      have ht : z.filterMap DoubleStrand.redLabel = [] := by
        simpa [DoubleStrand.redLabel, Fin.fin_one_eq_zero r] using h
      obtain ⟨s, hs⟩ := no_red_iff_black z ht
      refine Or.inr ⟨s, Obj.ext hstart ?_⟩
      simpa only [redObj, obj, List.singleton_append, List.append_nil, hs, Fin.fin_one_eq_zero r] using hw.symm

private theorem blackWord_injective :
    Function.Injective (blackWord (I := I) (ℓ := 1)) := by
  intro a b h
  have hn (s : List (Letter I)) :
      (blackWord (I := I) (ℓ := 1) s).filterMap Sum.getLeft? = s.reverse := by
    simp [blackWord, List.filterMap_map]
  exact List.reverse_injective (by simpa only [hn] using congrArg (List.filterMap Sum.getLeft?) h)

private theorem redObj_injective : Function.Injective O := by
  intro s t h
  have hword := congrArg (fun a : Obj S => a.word.map Prod.snd) h
  simp only [redObj, obj, forget_colours, List.append_nil, List.singleton_append,
    List.cons.injEq, true_and] at hword
  exact blackWord_injective hword

private theorem blackHasNoRed (s : List (Letter I)) :
    (blackWord (ℓ := 1) s).filterMap DoubleStrand.redLabel = [] := by
  simp [blackWord, List.filterMap_map, DoubleStrand.redLabel]

private theorem reds_redObj (s : List (Letter I)) :
    ((O s).word.map Prod.snd).filterMap DoubleStrand.redLabel = [0] := by
  change ((colours RD Λ 0 (redPrefix ++ blackWord s ++ [])).map Prod.snd).filterMap
    DoubleStrand.redLabel = [0]
  rw [forget_colours, List.append_nil, List.singleton_append, List.filterMap_cons,
    blackHasNoRed]
  rfl

private theorem layer_eq_context (L : Layer S) (hv : L.Valid) :
    layer RD Λ L.start (L.left.map Prod.snd) L.gen.2 (L.right.map Prod.snd) = L := by
  have hl := recover_labelled RD Λ L.start L.left hv.left_ok
  have hg : endWeight RD Λ L.start (L.left.map Prod.snd) = L.gen.1 := by
    rw [← colours_endR, hl]
    exact hv.left_end
  exact Layer.ext rfl hl (Prod.ext hg rfl) (by
    change colours RD Λ (endWeight RD Λ (endWeight RD Λ L.start (L.left.map Prod.snd))
      L.gen.2.bottom) (L.right.map Prod.snd) = L.right
    rw [hg]
    exact recover_labelled RD Λ _ _ hv.right_ok)

private theorem layer_words (L : Layer S) :
    L.dom.word.map Prod.snd = L.left.map Prod.snd ++ L.gen.2.bottom ++ L.right.map Prod.snd ∧
    L.cod.word.map Prod.snd = L.left.map Prod.snd ++ L.gen.2.top ++ L.right.map Prod.snd := by
  constructor <;> simp [Layer.dom, Layer.cod, signature, forget_colours, List.map_append]

private theorem redLayer_lift (L : Layer S) (hv : L.Valid) {s t : List (Letter I)}
    (hs : L.dom = O s) (ht : L.cod = O t) :
    ∃ x : LayerData I, SChain s [x] t ∧
      L = layer RD Λ 0 (redPrefix ++ blackWord x.2.2) (.black (Sig.shape x.2.1)) (blackWord x.1 ++ []) := by
  have hl := layer_eq_context RD Λ L hv
  have hstart : L.start = (0 : X) := congrArg Obj.start hs
  rw [hstart] at hl
  let p := L.left.map Prod.snd
  let q := L.right.map Prod.snd
  have hd : p ++ L.gen.2.bottom ++ q = red :: blackWord s := by
    rw [← (layer_words RD Λ L).1, hs]
    simp [redObj, obj, forget_colours]
  have hc : p ++ L.gen.2.top ++ q = red :: blackWord t := by
    rw [← (layer_words RD Λ L).2, ht]
    simp [redObj, obj, forget_colours]
  have hp : p ≠ [] := by
    intro h
    rw [h, List.nil_append] at hd hc
    cases hg : L.gen.2 with
    | black g =>
      rw [hg] at hd hc
      cases g <;> simp [Move.bottom, Move.top, Shape.dom, Shape.cod, red] at hd hc
    | blackRed => simp [hg, Move.bottom, red] at hd
    | redBlack => simp [hg, Move.top, red] at hc
  obtain ⟨z, p', hplist⟩ := List.exists_cons_of_ne_nil hp
  have hz : z = red := by
    have h := congrArg List.head? hd
    simpa [hplist] using h
  subst z
  have hpq : p'.filterMap DoubleStrand.redLabel = [] ∧ q.filterMap DoubleStrand.redLabel = [] ∧
      (L.gen.2.bottom).filterMap DoubleStrand.redLabel = [] := by
    have h := congrArg (List.filterMap DoubleStrand.redLabel) hd
    rw [hplist] at h
    simp only [List.cons_append, List.filterMap_cons, List.filterMap_append,
      show DoubleStrand.redLabel (red (I := I)) = some 0 by rfl, blackHasNoRed] at h
    have hh := (List.cons.inj h).2
    have he := List.append_eq_nil_iff.mp hh
    exact ⟨(List.append_eq_nil_iff.mp he.1).1, he.2, (List.append_eq_nil_iff.mp he.1).2⟩
  obtain ⟨l, hleft⟩ := no_red_iff_black p' hpq.1
  obtain ⟨r, hright⟩ := no_red_iff_black q hpq.2.1
  cases hg : L.gen.2 with
  | black g =>
    have hs0 : s = r ++ (Sig.shape g).dom ++ l := by
      apply blackWord_injective
      rw [hplist, ← hleft, ← hright, hg] at hd
      have h := (List.cons.inj hd).2
      simpa [blackWord, Sig.shape_dom, List.reverse_append, List.append_assoc, Move.bottom] using h.symm
    have ht0 : t = r ++ (Sig.shape g).cod ++ l := by
      apply blackWord_injective
      rw [hplist, ← hleft, ← hright, hg] at hc
      have h := (List.cons.inj hc).2
      simpa [blackWord, Sig.shape_cod, List.reverse_append, List.append_assoc, Move.top] using h.symm
    refine ⟨(r, Sig.shape g, l), ⟨hs0, ht0.symm⟩, ?_⟩
    have hz : Sig.shape (Sig.shape g) = g := by cases g <;> simp
    rw [← hl]
    change layer RD Λ 0 p L.gen.2 q = _
    rw [hplist, ← hleft, ← hright, hg, hz]
    rw [List.append_nil]
    rfl
  | blackRed =>
    have h := hpq.2.2
    rw [hg] at h
    simp [Move.bottom] at h
  | redBlack =>
    have h := hpq.2.2
    rw [hg] at h
    simp [Move.bottom] at h

section Raw

/-- A cut of a raw diagram at which the leftmost strand is black. -/
def HasBlackLeftCut {a b : Obj S} (d : a ⟶ b) : Prop :=
  ∃ (c : Obj S) (f : a ⟶ c) (g : c ⟶ b), d = f ≫ g ∧
    ∃ l, (c.word.map Prod.snd).head? = some (.inl l)

private theorem singleRed_chain {s t : List (Letter I)} {ls : List (Layer S)}
    (h : Chain (O s) ls (O t)) :
    HasBlackLeftCut RD Λ (Diagram.mk ls h) ∨
      ∃ f : ob RD (η RD Λ) s ⟶ ob RD (η RD Λ) t,
        blackDiagram RD Λ 0 redPrefix [] f = Diagram.mk ls h := by
  induction ls generalizing s with
  | nil =>
    obtain rfl : s = t := redObj_injective RD Λ h
    exact Or.inr ⟨𝟙 _, blackDiagram_id RD Λ 0 redPrefix [] s⟩
  | cons L ls ih =>
    let f : O s ⟶ L.cod := Diagram.layer L h.1 h.2.1 rfl
    have hk : (L.cod.word.map Prod.snd).filterMap DoubleStrand.redLabel = [0] := by
      rw [← reds_redObj RD Λ s]
      exact chain_wordInvariant RD Λ (·.filterMap DoubleStrand.redLabel)
        (fun u g v => by simp [g.top_reds]) (Diagram.chain f)
    have hv : (S).ok L.cod.start L.cod.word := by
      rcases h.1 with ⟨hl, he, _, _, hm, he', hr⟩
      simpa [Layer.cod, Signature.ok_append, he, he', hl, hm] using hr
    obtain hc | ⟨a, ha⟩ := head_black_or_red RD Λ L.cod hk (Diagram.chain f).start_eq hv
    · exact Or.inl ⟨_, f, Diagram.mk ls h.2.2, Diagram.eq_layer_comp h, hc⟩
    have hls : Chain (O a) ls (O t) := ha ▸ h.2.2
    obtain ⟨x, hx, hL⟩ := redLayer_lift RD Λ L h.1 h.2.1 ha
    let d : ob RD (η RD Λ) s ⟶ ob RD (η RD Λ) a := mkD RD (η RD Λ) [x] hx
    have heq : Diagram.mk (L :: ls) h = blackDiagram RD Λ 0 redPrefix [] d ≫ Diagram.mk ls hls := by
      apply Diagram.ext
      rw [Diagram.layers_comp, layers_blackDiagram_mkD]
      change L :: ls = layer RD Λ 0 (redPrefix ++ blackWord x.2.2)
        (.black (Sig.shape x.2.1)) (blackWord x.1 ++ []) :: ls
      rw [hL]
    rcases ih hls with hi | ⟨g, hg⟩
    · obtain ⟨c, g, j, hj, hblack⟩ := hi
      exact Or.inl ⟨c, blackDiagram RD Λ 0 redPrefix [] d ≫ g, j,
        by rw [heq, hj, Category.assoc], hblack⟩
    · exact Or.inr ⟨d ≫ g, by rw [blackDiagram_comp, hg, ← heq]⟩

/-- A raw diagram between boundaries whose unique red strand is first either
passes through a violated cut or is a reflected black KL diagram to the
right of the fixed red strand. -/
theorem singleRed_diagram_hasBlackLeftCut_or_blackDiagram {s t : List (Letter I)}
    (d : O s ⟶ O t) :
    HasBlackLeftCut RD Λ d ∨ ∃ f : ob RD (η RD Λ) s ⟶ ob RD (η RD Λ) t,
      blackDiagram RD Λ 0 redPrefix [] f = d := by
  obtain ⟨ls, hd⟩ := d
  exact singleRed_chain RD Λ hd

end Raw

section Violating

variable {Λ} {Λd : Fin 1 → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}}
  {k : Type w} [CommRing k] {right : X}
  (P : Presentation.{w, max u v} (signature RD (Subtype.val ∘ Λd)) k)

local notation "labels" => Subtype.val ∘ Λd

/-- A one-red boundary with the black word occurring entirely to the right of
the red strand. The argument `s` is read in KL word order. -/
def singleRedTriple (s : List (Letter I))
    (h : endWeight RD labels 0 (redPrefix ++ blackWord s ++ []) = right) :
    DoubleStendhalTriple RD Λd 0 right :=
  ⟨⟨redPrefix ++ blackWord s ++ [], by
    rw [List.append_nil, List.singleton_append, List.filterMap_cons, blackHasNoRed]
    rfl⟩, h⟩

variable {RD}

/-- The linear projection of presented morphisms between fixed-red boundaries
to the violating quotient. -/
def singleRedProjection (s t : List (Letter I))
    (hs : endWeight RD labels 0 (redPrefix ++ blackWord s ++ []) = right)
    (ht : endWeight RD labels 0 (redPrefix ++ blackWord t ++ []) = right) :
    (P.obj (redObj RD labels s) ⟶ P.obj (redObj RD labels t)) →ₗ[k]
      ((violatingFunctor P right).obj (singleRedTriple RD s hs) ⟶
        (violatingFunctor P right).obj (singleRedTriple RD t ht)) :=
  ((violatingFunctor P right).mapLinearMap k
    (X := singleRedTriple RD s hs) (Y := singleRedTriple RD t ht)).comp
    (InducedCategory.homLinearEquiv (R := k) (F := tripleObj P (right := right))
      (X := singleRedTriple RD s hs) (Y := singleRedTriple RD t ht)).symm.toLinearMap

theorem singleRedProjection_comp (s t z : List (Letter I))
    (hs : endWeight RD labels 0 (redPrefix ++ blackWord s ++ []) = right)
    (ht : endWeight RD labels 0 (redPrefix ++ blackWord t ++ []) = right)
    (hz : endWeight RD labels 0 (redPrefix ++ blackWord z ++ []) = right)
    (f : P.obj (redObj RD labels s) ⟶ P.obj (redObj RD labels t))
    (g : P.obj (redObj RD labels t) ⟶ P.obj (redObj RD labels z)) :
    singleRedProjection P s z hs hz (f ≫ g) =
      singleRedProjection P s t hs ht f ≫ singleRedProjection P t z ht hz g :=
  (violatingFunctor P right).map_comp
    (InducedCategory.homMk (X := singleRedTriple RD s hs) (Y := singleRedTriple RD t ht) f)
    (InducedCategory.homMk (X := singleRedTriple RD t ht) (Y := singleRedTriple RD z hz) g)

theorem singleRedProjection_id (s : List (Letter I))
    (hs : endWeight RD labels 0 (redPrefix ++ blackWord s ++ []) = right) :
    singleRedProjection P s s hs hs (𝟙 _) = 𝟙 _ :=
  (violatingFunctor P right).map_id (singleRedTriple RD s hs)

/-- Send a black linear diagram to the signed violating Hom by inserting the fixed
red strand on its physical left. -/
def singleRedBlackEntry (s t : List (Letter I))
    (hs : endWeight RD labels 0 (redPrefix ++ blackWord s ++ []) = right)
    (ht : endWeight RD labels 0 (redPrefix ++ blackWord t ++ []) = right) :
    LinDiagram k (ob RD (η RD labels) s) (ob RD (η RD labels) t) →ₗ[k]
      ((violatingFunctor P right).obj (singleRedTriple RD s hs) ⟶
        (violatingFunctor P right).obj (singleRedTriple RD t ht)) :=
  (singleRedProjection P s t hs ht).comp
    ((P.linFunctor.mapLinearMap k).comp (blackLinear RD labels k 0 redPrefix []))

/-- Every signed morphism between one-red, red-first boundaries has a preimage
among black linear diagrams. The adjoining red strand stays at the far left
through the entire representative. This holds for any signed presentation. -/
theorem singleRedBlackEntry_surjective (s t : List (Letter I))
    (hs : endWeight RD labels 0 (redPrefix ++ blackWord s ++ []) = right)
    (ht : endWeight RD labels 0 (redPrefix ++ blackWord t ++ []) = right) :
    Function.Surjective (singleRedBlackEntry P s t hs ht) := by
  let q := violatingFunctor P right
  intro f
  obtain ⟨⟨g⟩, rfl⟩ := q.map_surjective f
  apply LinearMap.mem_range.mp
  change singleRedProjection P s t hs ht g ∈ (singleRedBlackEntry P s t hs ht).range
  induction g using P.hom_induction with
  | diag d =>
    rcases singleRed_diagram_hasBlackLeftCut_or_blackDiagram RD labels d with h | ⟨e, rfl⟩
    · obtain ⟨c, u, v, rfl, hleft⟩ := h
      have he := diagram_eq_zero_of_black_at_cut P (singleRedTriple RD s hs)
        (singleRedTriple RD t ht) u v hleft
      change singleRedProjection P s t hs ht (P.diag (u ≫ v)) = 0 at he
      rw [he]
      exact Submodule.zero_mem _
    · refine ⟨LinDiagram.of e, ?_⟩
      change singleRedProjection P s t hs ht
        (P.lin (blackLinear RD labels k 0 redPrefix [] (LinDiagram.of e))) = _
      rw [blackLinear_of, Presentation.lin_of]
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add g h hg hh => rw [map_add]; exact Submodule.add_mem _ hg hh
  | smul r f hf => rw [map_smul]; exact Submodule.smul_mem _ r hf

end Violating

end Categorification.Stendhal.DoubleDiagram

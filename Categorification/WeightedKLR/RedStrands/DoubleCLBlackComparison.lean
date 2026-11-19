/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLBlackRelations
import Categorification.WeightedKLR.RedStrands.DoubleCLLocalMap
import Categorification.WeightedKLR.RedStrands.DoubleBlackPresentation


/-!
# The black relations of the cyclotomic action, compared with a restricted Rouquier family

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29. The cover functor sends the black
strands of a double diagram to KL diagrams of the enlarged Cartan datum. On black diagrams
this agrees with the reflection `Ω` followed by the restriction to the black colours
(`coverLin_blackMirror`), up to the identification of the boundary words.

The presentation `admissibleKernel G` has as relations all linear combinations killed by every
admissible evaluation of the generator images `G`. For the generator images of a Rouquier
family satisfying Brundan's upward KLR relations with the standard scalars on the black
colours, the reflected black KL III relations hold in it (`coverLin_blackRel`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams TwoRep

universe w u v

/-- A layer is determined by its domain, generator and left length. -/
theorem Layer.ext_of_dom' {S : Signature} {L₁ L₂ : Layer S} (hd : L₁.dom = L₂.dom)
    (hg : L₁.gen = L₂.gen) (hl : L₁.left.length = L₂.left.length) : L₁ = L₂ := by
  obtain ⟨s₁, l₁, g₁, r₁⟩ := L₁
  obtain ⟨s₂, l₂, g₂, r₂⟩ := L₂
  simp only at hg hl
  subst hg
  have hs : s₁ = s₂ := congrArg Obj.start hd
  have hw : l₁ ++ S.dom g₁ ++ r₁ = l₂ ++ S.dom g₁ ++ r₂ := congrArg Obj.word hd
  rw [List.append_assoc, List.append_assoc] at hw
  obtain ⟨rfl, hw'⟩ := List.append_inj hw hl
  rw [List.append_cancel_left hw', hs]

/-- Single-layer diagrams with equal generators and offsets have the same image. -/
theorem diag_single_layer {S : Signature} {R : Type*} [CommRing R] (Q : Presentation S R)
    {a b a' b' : Obj S} (d : a ⟶ b) (d' : a' ⟶ b') {L L' : Layer S}
    (h : Diagram.layers d = [L]) (h' : Diagram.layers d' = [L']) (hg : L.gen = L'.gen)
    (hl : L.left.length = L'.left.length) (ha : Q.obj a = Q.obj a') (hb : Q.obj b = Q.obj b') :
    Q.diag d = eqToHom ha ≫ Q.diag d' ≫ eqToHom hb.symm := by
  obtain rfl := Q.obj_injective ha
  have c := Diagram.chain d
  have c' := Diagram.chain d'
  rw [h] at c
  rw [h'] at c'
  obtain ⟨_, hd, hc⟩ := c
  obtain ⟨_, hd', hc'⟩ := c'
  obtain rfl : L = L' := Layer.ext_of_dom' (hd.trans hd'.symm) hg hl
  obtain rfl : b = b' := (hc : L.cod = b).symm.trans hc'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact Q.diag_eq_of_layers_eq (h.trans h'.symm)

/-- A scaled, whiskered single-layer image is the scaled image of the whiskered layer. -/
theorem whisk_single_layer {S : Signature} {R : Type*} [CommRing R] (Q : Presentation S R)
    {x y a b : Obj S} (r : R) (e2 : Q.obj x = Q.obj a) (d₀ : a ⟶ b) (e3 : Q.obj b = Q.obj y)
    (u : Obj S) (v : List S.Colour) (hw : x.WhiskerOK u v) {L₀ : Layer S}
    (h₀ : Diagram.layers d₀ = [L₀]) {a' b' : Obj S} (d' : a' ⟶ b') {L' : Layer S}
    (h' : Diagram.layers d' = [L']) (hg : L₀.gen = L'.gen)
    (hl : u.word.length + L₀.left.length = L'.left.length) {z z' : Obj S}
    (e0 : Q.obj a' = Q.obj z) (e1 : Q.obj z = Q.obj (x.whisker u v))
    (e4 : Q.obj (y.whisker u v) = Q.obj z') (e5 : Q.obj z' = Q.obj b') :
    eqToHom e0 ≫ (eqToHom e1 ≫ Q.whisk (r • (eqToHom e2 ≫ Q.diag d₀ ≫ eqToHom e3)) u v ≫
      eqToHom e4) ≫ eqToHom e5 = r • Q.diag d' := by
  obtain rfl := Q.obj_injective e2
  obtain rfl := Q.obj_injective e3
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rw [Q.whisk_smul, Q.whisk_diag _ _ _ hw, Linear.smul_comp, Linear.comp_smul, Linear.smul_comp,
    Linear.comp_smul,
    diag_single_layer Q (Diagram.whisker d₀ u v hw) d'
      (L := L₀.whisker u v) (by rw [Diagram.layers_whisker, h₀]; rfl) h' hg
      (by simpa [Layer.whisker] using hl) (e0.trans e1).symm (e4.trans e5)]
  simp

section Kernel
open Diagrams.BicatInterp

variable {S : Signature} {B : Type*} [Bicategory B] {M₀ : Model S B} {k : Type*} [CommRing k]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]

/-- The linear combinations of diagrams killed by every admissible evaluation of `G`,
as a presentation. -/
def admissibleKernel (G : GenImg M₀) : Presentation S k where
  Rel := Σ (a b : Obj S), {f : LinDiagram k a b //
    ∀ (s t : S.Region) (ha : Cond s t a) (hb : Cond s t b), admissibleMap G ha hb f = 0}
  dom r := r.1
  cod r := r.2.1
  rel r := r.2.2.1

theorem admissibleKernel_rel (G : GenImg M₀) (i : (admissibleKernel (k := k) G).Rel)
    {s t : S.Region} (ha : Cond s t ((admissibleKernel G).dom i))
    (hb : Cond s t ((admissibleKernel G).cod i)) :
    admissibleMap G ha hb ((admissibleKernel G).rel i) = 0 :=
  i.2.2.2 s t ha hb

theorem admissibleKernel_lin_eq_zero (G : GenImg M₀) {a b : Obj S} (f : LinDiagram k a b)
    (hf : ∀ (s t : S.Region) (ha : Cond s t a) (hb : Cond s t b), admissibleMap G ha hb f = 0) :
    (admissibleKernel G).lin f = 0 :=
  (admissibleKernel G).lin_rel_self ⟨a, b, f, hf⟩

end Kernel

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {C' : CartanDatum (I ⊕ Fin ℓ)}
  {X Y : Type v} [AddCommGroup X] [AddCommGroup Y] (W : WeightDatum C' X Y)
  (hC : ∀ i j, C'.dot (.inl i) (.inl j) = C.dot i j) (o : X)
  (ho : ∀ i, W.pair (W.iY (.inl i)) o = 0)

local notation "RD" => blackDatum W hC
local notation "Λ" => redWeight W

include ho in
/-- The restriction datum of the black vertices with base weight `o`. -/
def coverRestrict : RestrictData RD W where
  e := Sum.inl
  o := o
  iX _ := rfl
  pair i x := by
    change W.pair (W.iY (.inl i)) x = W.pair (W.iY (.inl i)) (o + x)
    rw [map_add, ho, zero_add]
  inj := Sum.inl_injective

/-- The cover of the black mirror of a word is the restriction of its reflection. -/
theorem cover_obj (a : Obj (psig RD)) (ha : a.WF) :
    (coverColourMap W hC o).obj ((coverMirror W hC o).obj ((blackMirror RD Λ).obj a)) =
      (coverRestrict W hC o ho).sigMap.toColourMap.obj (Omega.obj RD a) := by
  refine Obj.ext ?_ ?_
  · have h := MirrorColourMap.obj_endR (blackMirror RD Λ).toMirrorColourMap ha
    exact (congrArg (fun x : X => o - x) h).trans (sub_eq_add_neg _ _)
  · change ((((a.word.map _).reverse).map _).reverse) = (a.word.map _).map _
    rw [List.map_reverse, List.reverse_reverse, List.map_map, List.map_map]
    refine List.map_congr_left fun c _ => ?_
    change (⟨coverLetter (.inl c.l), o - c.r⟩ : Col (I ⊕ Fin ℓ) X) = ⟨_, o + -c.r⟩
    rw [sub_eq_add_neg]
    rfl

include ho in
/-- The move of a reflected black generator is a single layer with the restricted generator. -/
theorem coverMove_layers (g : (psig RD).Gen) :
    ∃ L' : Layer (psig W), Diagram.layers
        (coverMove W 
          (@HSub.hSub X X X _ o ((psig RD).right g)) (.black (Sig.shape (shapeOf RD g)))) = [L'] ∧
      L'.gen = (coverRestrict W hC o ho).gen (Omega.gen g) ∧ L'.left = [] := by
  rcases g with (⟨c⟩ | ⟨ε, i, j, ν⟩) | c | c
  · exact ⟨_, rfl, congrArg (fun r => PivotalGen.gen (Gen0.dot
      (⟨((!c.l.1, Sum.inl c.l.2) : Letter (I ⊕ Fin ℓ)), r⟩ : Col (I ⊕ Fin ℓ) X)))
      (sub_eq_add_neg o c.r), rfl⟩
  · exact ⟨_, rfl, congrArg (fun r => PivotalGen.gen (Gen0.cross (!ε) (Sum.inl i) (Sum.inl j) r))
      (sub_eq_add_neg o ν), rfl⟩
  · refine ⟨_, rfl, ?_, rfl⟩
    change PivotalGen.cup (⟨_, _⟩ : Col (I ⊕ Fin ℓ) X) = PivotalGen.cup ⟨_, _⟩
    congr 1
    refine Col.ext rfl ?_
    change sh W ((coverRestrict W hC o ho).letter c.l.dual.dual) + (o - (sh RD c.l + c.r)) =
      o + -c.r
    rw [RestrictData.sh_letter, Letter.dual_dual]
    abel
  · exact ⟨_, rfl, congrArg (fun r => PivotalGen.cap
      (⟨((!c.l.1, Sum.inl c.l.2) : Letter (I ⊕ Fin ℓ)), r⟩ : Col (I ⊕ Fin ℓ) X))
      (sub_eq_add_neg o c.r), rfl⟩

/-- The cover sign of a black shape is the sign of the reflection. -/
theorem coverSign_shape [DecidableEq I] {k : Type*} [CommRing k] (g : (psig RD).Gen) :
    coverSign (k := k) (ℓ := ℓ) (.black (Sig.shape (shapeOf RD g))) = omegaSign RD g := by
  rcases g with (⟨c⟩ | ⟨ε, i, j, ν⟩) | c | c
  · simp [coverSign, omegaSign, Sig.sgnG, Sig.shape, shapeOf]
  · by_cases h : i = j
    · subst h; simp [coverSign, omegaSign, Sig.sgnG, Sig.shape, shapeOf]
    · simp [coverSign, omegaSign, Sig.sgnG, Sig.shape, shapeOf, h, Ne.symm h]
  · simp [coverSign, omegaSign, Sig.sgnG, Sig.shape, shapeOf]
  · simp [coverSign, omegaSign, Sig.sgnG, Sig.shape, shapeOf]

local notation "κ" => coverColourMap W hC o
local notation "BM" => blackMirror RD Λ
local notation "CM" => coverMirror W hC o

/-- **The cover functor on black diagrams** is the reflection followed by the restriction to
the black colours, up to the identifications of the boundary words. -/
theorem coverLin_blackMirror [DecidableEq I] {k : Type w} [CommRing k]
    (Q : Presentation (psig W) k) {a b : Obj (psig RD)} (f : LinDiagram k a b)
    (ha : a.WF) (hb : b.WF) :
    coverLin W hC o Q coverSign (blackMirrorLinear RD Λ f) =
      eqToHom (congrArg Q.obj (cover_obj W hC o ho a ha)) ≫
        Q.lin ((coverRestrict W hC o ho).sigMap.toLayerMap.lin
          ((omegaLayerMap RD).lin (wlin (omegaSign RD) f))) ≫
        eqToHom (congrArg Q.obj (cover_obj W hC o ho b hb)).symm := by
  change (freeLift k _).map ((CM).toLayerMap.lin ((BM).toLayerMap.lin f)) = _
  rw [freeLift_map_layerLin, freeLift_map_layerLin, ← LayerMap.lin_comp',
    ← freeLift_toPresented_eq]
  refine freeLift_map_eq_of_layer
    ((BM).toLayerMap.functor ⋙ ((CM).toLayerMap.functor ⋙
      (LocalMap.ofGen κ (coverImage W hC o Q coverSign)).functor))
    (((omegaLayerMap RD).comp (coverRestrict W hC o ho).sigMap.toLayerMap).toPresented Q
      (omegaSign RD))
    (fun a ha => congrArg Q.obj (cover_obj W hC o ho a ha)) ?_ f ha hb
  intro L hv
  rw [LayerMap.toPresented_map]
  have hwt : Diagram.weight (omegaSign RD (k := k)) (Diagram.ofLayer L hv) =
      omegaSign RD L.gen := by
    simp [Diagram.weight, Diagram.weightList]
  obtain ⟨L', hL', hg, hl⟩ := coverMove_layers W hC o ho L.gen
  let L'' := (CM).toLayerMap.layer ((BM).toLayerMap.layer L)
  have hv'' : L''.Valid := (CM).toLayerMap.valid ((BM).toLayerMap.valid hv)
  refine (whisk_single_layer Q _ _ _ _ ((coverColourMap W hC o).obj ⟨L''.start, L''.left⟩)
    ((coverColourMap W hC o).word L''.right)
    (LocalMap.genDom_whiskerOK κ hv'') hL' (Diagram.cast
      (((omegaLayerMap RD).comp (coverRestrict W hC o ho).sigMap.toLayerMap).map
        (Diagram.ofLayer L hv)) (cover_obj W hC o ho _ hv.wf_dom).symm
        (cover_obj W hC o ho _ hv.wf_cod).symm) rfl hg ?_ _ _ _ _).trans ?_
  · rw [hl]
    simp only [L'', List.length_nil, add_zero]
    change ((coverColourMap W hC o).word ((CM).word ((BM).word L.left))).length =
      ((coverRestrict W hC o ho).sigMap.word (Omega.word L.left)).length
    rw [ColourMap.word_eq, ColourMap.word_eq]
    simp [MirrorColourMap.word, Omega.word]
  · have hs : coverSign (k := k) (ℓ := ℓ)
        ((CM).toLayerMap.layer ((BM).toLayerMap.layer L)).gen.2 = omegaSign RD L.gen :=
      coverSign_shape W hC L.gen
    erw [hs, hwt, Q.diag_cast]
    simp

section Rouquier
open Diagrams.BicatInterp

variable {B : Type*} [Bicategory B] [∀ a b : B, Preadditive (a ⟶ b)] (S : RouqFamily (B := B) W)
  [AdditiveWhiskering B] {k : Type w} [CommRing k] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ (a b c : B) (f : a ⟶ b), (Bicategory.precomp c f).Linear k]
  [∀ (a b c : B) (g : b ⟶ c), (Bicategory.postcomp a g).Linear k]

include ho in
/-- **The black KL relations hold after reflection.** The image of a reflected black KL III
relation under the KL diagrams of the moves is killed by every admissible evaluation of a
Rouquier family for `W` with Cautis–Lauda scalars, Brundan's upward relations and invertible
mixed crossings, provided `t = 1` on the black vertices and `s` vanishes there in the degrees
below the extremal ones. -/
theorem coverLin_blackRel [DecidableEq I] (Sc : CL.CLScalars C' k)
    (ht : ∀ i j, Sc.t (.inl i) (.inl j) = 1)
    (hs : ∀ i j p q, p < C.dij i j → q < C.dij j i → Sc.s (.inl i) (.inl j) p q = 0)
    (H : BrundanUpKLR S Sc) (Mi : BrundanMixedInversion S) (r : (pres RD k).Rel) :
    coverLin W hC o (admissibleKernel (S.genImg Sc)) coverSign
      (blackMirrorLinear RD Λ ((pres RD k).rel r)) = 0 := by
  by_cases h0 : (pres RD k).rel r = 0
  · rw [h0, map_zero]
    simp [coverLin, LayerMap.lin]
  obtain ⟨d, -⟩ := Finsupp.ne_iff.mp h0
  have hdom : ((pres RD k).dom r).WF := pres_dom_wf r
  have hcod : ((pres RD k).cod r).WF := (Diagram.chain d).wf hdom
  rw [coverLin_blackMirror W hC o ho _ _ hdom hcod,
    admissibleKernel_lin_eq_zero _ _ ?_, Limits.zero_comp, Limits.comp_zero]
  intro s t ha hb
  have hwd : (Omega.obj RD ((pres RD k).dom r)).WF := (Omega.ok_word _ _ hdom).1
  have hwc : (Omega.obj RD ((pres RD k).cod r)).WF := (Omega.ok_word _ _ hcod).1
  obtain ⟨rfl, rfl, ha'⟩ := cond_of_map (coverRestrict W hC o ho).sigMap hwd ha
  obtain ⟨hs', ht', hb'⟩ := cond_of_map (coverRestrict W hC o ho).sigMap hwc hb
  have hinj : Function.Injective (coverRestrict W hC o ho).sigMap.region :=
    fun x y h => @add_left_cancel X _ _ o x y h
  have hb'' : Cond (S := psig RD) (Omega.obj RD ((pres RD k).dom r)).start
      ((psig RD).endR (Omega.obj RD ((pres RD k).dom r)).start
        (Omega.obj RD ((pres RD k).dom r)).word)
      ((omegaLayerMap RD).obj ((pres RD k).cod r)) := by
    have e1 := hinj hs'
    have e2 := hinj ht'
    refine ⟨e1 ▸ hb'.1, ?_, e1.symm⟩
    rw [e2, e1]
    rfl
  exact omega_rel_restrict (coverRestrict W hC o ho) S Sc hC ht hs H Mi r ha' hb''

end Rouquier

end Categorification.Stendhal.DoubleDiagram

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CLQ.BubbleSlidesQGap
import Categorification.Diagrams.CLQ.EndOne
import Categorification.Diagrams.CLQ.Pitchfork
import Categorification.Diagrams.KL3.SpanningBasic

/-!
# Normal forms of all diagrams of `U`, and bubbles sliding across a strand

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.1.2
(Propositions 3.3, 3.4, labels `prop_bubble_slide1`, `prop_bubble_slide2`) and §3.2.1 (proof of
Proposition 3.6: "Crossingless diagrams that contain nested bubbles can be written as linear
combinations of crossingless nonnested diagrams using the bubble slide equations").

## Normal forms

Every diagram of the presented 2-category `U` between normal-form objects `E_s 1_μ` and
`E_t 1_μ` is a normal-form diagram `mkD μ ls h` (`exists_mkD`): its layers are determined by
their signed letters and the rightmost region. Consequently every 2-morphism is a linear
combination of classes `dg μ s t ls` (`hom_ext_dg`: linear maps agreeing on the classes `dg`
agree).

## Bubbles sliding across a strand

For a strand `l` with rightmost region `μ`, `slideSetR μ l` is the span of the 2-morphisms
`x^a ⊗ γ` (`a` dots on the strand, an element `γ` of the image of `Π_μ` to its right), and
`slideSetL μ l` the span of `γ ⊗ x^a` (`γ` in the image of `Π_{μ + l_X}` to its left). The
bubble slides of KL III, Propositions 3.3 and 3.4 (in all degrees, `BubbleSlidesAll`), say that
a generator of `Π` to the left of an upward strand lies in `slideSetR` (`cw_slideR_up`,
`ccw_slideR_up`), and one to the right of an upward strand in `slideSetL` (`cw_slideL_up`,
`ccw_slideL_up`). As the slide sets are closed under composition (`slideSetR_comp`), every
element of the image of `Π` slides (`bubLU_mem_of_gen`, `bubLU_up_mem_gen`, `bubRU_up_mem_gen`).
For a downward strand `F_j` the slides are obtained by rotation (`rotT`: the cup `1 → F E` and
the cap `E F → 1`, zigzag relations, cyclicity of dots; `rotT_bubRU`, `rotT_dots_bubLU`):
`bubLU_dn_mem_gen`. Altogether `bubLU_mem_slideSetR_gen`: every element of the image of `Π`
placed to the left of any strand `l` lies in `slideSetR μ l`.

KL III state the bubble slides only for `i = j`, `i·j = -1` and `i·j = 0` (the simply-laced
case, their main case of interest `sl(n)`). For `i ≠ j` we use the bubble slides in all degrees
for general Cautis–Lauda scalars of `Categorification.Diagrams.CLQ.BubbleSlidesQGap` (`slidesQ`,
cf. Brundan–Ellis, arXiv:1701.04133v2, Proposition 7.3(iii)), so these results hold for every
Cartan datum and every choice of the scalars `t_ij`, `s_ij^{pq}`. The forms `bubLU_up_mem`, `bubRU_up_mem`, `bubLU_dn_mem`,
`bubLU_mem_slideSetR` with a (now superfluous) hypothesis `SimplyLaced C` are kept for the
simply-laced developments that use them.

## Other tools

`dg_closed_right`, `dg_closed_left`: a closed diagram commutes with any diagram on the strands to
its right (left) (interchange law); `wnf`: normalization of lists of layers keeping
`map (whL u v)` folded.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram.CLQ

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k] (sc : CL.CLScalars C k)

/-! ## Normal forms of layers and diagrams -/







/-- Linear maps on the `Hom`-spaces of `U` between normal-form objects agree if they agree on the
classes `dg μ s t ls` of all normal-form diagrams. -/
theorem hom_ext_dg (μ : X) {s t : List (Letter I)} {M : Type*} [AddCommGroup M] [Module k M]
    (φ ψ : ((pres RD k sc).obj (ob RD μ s) ⟶ (pres RD k sc).obj (ob RD μ t)) →ₗ[k] M)
    (h : ∀ ls : List (LayerData I), SChain s ls t → φ (dg RD k sc μ s t ls) = ψ (dg RD k sc μ s t ls)) :
    φ = ψ := by
  refine hom_ext_diag RD k sc φ ψ fun d => ?_
  obtain ⟨ls, hls, rfl⟩ := exists_mkD RD μ d
  rw [← dg_of hls]
  exact h ls hls

/-- Every 2-morphism of `U` between normal-form objects is a linear combination of classes of
normal-form diagrams. -/
theorem mem_span_dg (μ : X) {s t : List (Letter I)}
    (f : (pres RD k sc).obj (ob RD μ s) ⟶ (pres RD k sc).obj (ob RD μ t)) :
    f ∈ Submodule.span k {g | ∃ ls, SChain s ls t ∧ g = dg RD k sc μ s t ls} := by
  obtain ⟨F, rfl⟩ := (pres RD k sc).lin_surjective f
  induction F using Finsupp.induction_linear with
  | zero => rw [Presentation.lin_zero]; exact Submodule.zero_mem _
  | add F₁ F₂ h₁ h₂ => rw [Presentation.lin_add]; exact Submodule.add_mem _ h₁ h₂
  | single d r =>
    rw [Presentation.lin_single]
    refine Submodule.smul_mem _ r (Submodule.subset_span ?_)
    obtain ⟨ls, hls, rfl⟩ := exists_mkD RD μ d
    exact ⟨ls, hls, (dg_of hls).symm⟩

/-! ## Closed diagrams commute with everything they do not touch -/

section Interchange

variable {RD k sc}

/-- A closed diagram `D` placed between the strands `u` and `t` commutes with a diagram `A` on
the strands `t` to its right. -/
theorem dg_closed_right (μ : X) {S T : List (Letter I)} (pre post : List (LayerData I))
    (u : List (Letter I)) {t t' : List (Letter I)} {D A : List (LayerData I)}
    (hD : SChain [] D []) (hA : SChain t A t') :
    dg RD k sc μ S T (pre ++ D.map (whL u t) ++ A.map (whL u []) ++ post) =
      dg RD k sc μ S T (pre ++ A.map (whL u []) ++ D.map (whL u t') ++ post) := by
  have h := dg_interchange (RD := RD) (k := k) (sc := sc) (μ := μ) (S := S) (T := T) pre post
    (hD.whisk u []) hA
  simp only [List.map_map, Function.comp_def, whL, List.append_nil, List.nil_append] at h ⊢
  exact h

/-- A closed diagram `D` placed between the strands `s` and `v` commutes with a diagram `A` on
the strands `s` to its left. -/
theorem dg_closed_left (μ : X) {S T : List (Letter I)} (pre post : List (LayerData I))
    {s s' : List (Letter I)} (v : List (Letter I)) {D A : List (LayerData I)}
    (hD : SChain [] D []) (hA : SChain s A s') :
    dg RD k sc μ S T (pre ++ A.map (whL [] v) ++ D.map (whL s' v) ++ post) =
      dg RD k sc μ S T (pre ++ D.map (whL s v) ++ A.map (whL [] v) ++ post) := by
  have h := dg_interchange (RD := RD) (k := k) (sc := sc) (μ := μ) (S := S) (T := T) pre post
    hA (hD.whisk [] v)
  simp only [List.map_map, Function.comp_def, whL, List.append_nil, List.nil_append] at h ⊢
  exact h

end Interchange

/-! ## The sets `x^a ⊗ Π` next to a strand -/

variable (μ : X) (l : Letter I)

/-- The span of `x^a ⊗ γ`: `a` dots on the strand `l` and an element `γ` of the image of
`Π_μ` to its right (rightmost region `μ`). -/
def slideSetR : Submodule k (End ((pres RD k sc).obj (ob RD μ [l]))) :=
  Submodule.span k {f | ∃ (a : ℕ) (γ : End ((pres RD k sc).obj (ob RD μ []))),
    IsBub RD k sc μ γ ∧ f = dotsU RD k sc μ l a ≫ bubRU RD k sc μ l γ}

/-- The span of `γ ⊗ x^a`: `a` dots on the strand `l` and an element `γ` of the image of
`Π_{μ + l_X}` to its left (rightmost region `μ`). -/
def slideSetL : Submodule k (End ((pres RD k sc).obj (ob RD μ [l]))) :=
  Submodule.span k {f | ∃ (a : ℕ) (γ : End ((pres RD k sc).obj (ob RD (wt RD μ [l]) []))),
    IsBub RD k sc (wt RD μ [l]) γ ∧ f = dotsU RD k sc μ l a ≫ bubLU RD k sc μ l γ}

variable {RD k sc μ l}

theorem mem_slideSetR {a : ℕ} {γ : End ((pres RD k sc).obj (ob RD μ []))} (hγ : IsBub RD k sc μ γ) :
    dotsU RD k sc μ l a ≫ bubRU RD k sc μ l γ ∈ slideSetR RD k sc μ l :=
  Submodule.subset_span ⟨a, γ, hγ, rfl⟩

theorem mem_slideSetR' {a : ℕ} {γ : End ((pres RD k sc).obj (ob RD μ []))} (hγ : IsBub RD k sc μ γ) :
    bubRU RD k sc μ l γ ≫ dotsU RD k sc μ l a ∈ slideSetR RD k sc μ l := by
  rw [bubRU_comm]; exact mem_slideSetR hγ

theorem mem_slideSetR_bub {γ : End ((pres RD k sc).obj (ob RD μ []))} (hγ : IsBub RD k sc μ γ) :
    bubRU RD k sc μ l γ ∈ slideSetR RD k sc μ l := by
  simpa [dotsU_zero] using mem_slideSetR (l := l) (a := 0) hγ

theorem mem_slideSetL {a : ℕ} {γ : End ((pres RD k sc).obj (ob RD (wt RD μ [l]) []))}
    (hγ : IsBub RD k sc (wt RD μ [l]) γ) :
    dotsU RD k sc μ l a ≫ bubLU RD k sc μ l γ ∈ slideSetL RD k sc μ l :=
  Submodule.subset_span ⟨a, γ, hγ, rfl⟩

theorem mem_slideSetL' {a : ℕ} {γ : End ((pres RD k sc).obj (ob RD (wt RD μ [l]) []))}
    (hγ : IsBub RD k sc (wt RD μ [l]) γ) :
    bubLU RD k sc μ l γ ≫ dotsU RD k sc μ l a ∈ slideSetL RD k sc μ l := by
  rw [bubLU_comm]; exact mem_slideSetL hγ

theorem mem_slideSetL_bub {γ : End ((pres RD k sc).obj (ob RD (wt RD μ [l]) []))}
    (hγ : IsBub RD k sc (wt RD μ [l]) γ) : bubLU RD k sc μ l γ ∈ slideSetL RD k sc μ l := by
  simpa [dotsU_zero] using mem_slideSetL (l := l) (a := 0) hγ

theorem slideSetR_comp {f g : End ((pres RD k sc).obj (ob RD μ [l]))} (hf : f ∈ slideSetR RD k sc μ l)
    (hg : g ∈ slideSetR RD k sc μ l) : f ≫ g ∈ slideSetR RD k sc μ l := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, γ, hγ, rfl⟩ := hf
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨b, δ, hδ, rfl⟩ := hg
      rw [Category.assoc, ← Category.assoc (bubRU RD k sc μ l γ), bubRU_comm, Category.assoc,
        ← Category.assoc, dotsU_add, ← bubRU_comp]
      exact mem_slideSetR (IsBub.comp hγ hδ)
    | zero => rw [Limits.comp_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [Preadditive.comp_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [Linear.comp_smul]; exact Submodule.smul_mem _ r hx
  | zero => rw [Limits.zero_comp]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Preadditive.add_comp]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [Linear.smul_comp]; exact Submodule.smul_mem _ r hx

theorem slideSetL_comp {f g : End ((pres RD k sc).obj (ob RD μ [l]))} (hf : f ∈ slideSetL RD k sc μ l)
    (hg : g ∈ slideSetL RD k sc μ l) : f ≫ g ∈ slideSetL RD k sc μ l := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, γ, hγ, rfl⟩ := hf
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨b, δ, hδ, rfl⟩ := hg
      rw [Category.assoc, ← Category.assoc (bubLU RD k sc μ l γ), bubLU_comm, Category.assoc,
        ← Category.assoc, dotsU_add, ← bubLU_comp]
      exact mem_slideSetL (IsBub.comp hγ hδ)
    | zero => rw [Limits.comp_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [Preadditive.comp_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [Linear.comp_smul]; exact Submodule.smul_mem _ r hx
  | zero => rw [Limits.zero_comp]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Preadditive.add_comp]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [Linear.smul_comp]; exact Submodule.smul_mem _ r hx

/-- If the generators of `Π_{μ + l_X}` placed to the left of the strand `l` lie in `slideSetR`,
then so does every element of the image of `Π_{μ + l_X}`. -/
theorem bubLU_mem_of_gen
    (hgen : ∀ (i : I) (α : ℕ), bubLU RD k sc μ l (bubGen RD k sc (wt RD μ [l]) i α) ∈ slideSetR RD k sc μ l)
    {β : End ((pres RD k sc).obj (ob RD (wt RD μ [l]) []))} (hβ : IsBub RD k sc (wt RD μ [l]) β) :
    bubLU RD k sc μ l β ∈ slideSetR RD k sc μ l := by
  obtain ⟨p, hp⟩ := hβ
  have hβ' : β = (bubMap RD k sc (wt RD μ [l]) p).val := (congrArg EndOne.val hp).symm
  subst hβ'
  clear hp
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.algHom_C, EndOne.val_algebraMap,
      show bubLU RD k sc μ l (a • 𝟙 _) = a • bubLU RD k sc μ l (𝟙 _) from LinearMap.map_smul _ a _,
      bubLU_id]
    refine Submodule.smul_mem _ a ?_
    simpa [bubRU_id, dotsU_zero] using mem_slideSetR (l := l) (a := 0) (μ := μ) (IsBub.id)
  | add p q hp hq =>
    rw [map_add, EndOne.val_add, show ∀ x y : End ((pres RD k sc).obj (ob RD (wt RD μ [l]) [])),
      bubLU RD k sc μ l (x + y) = bubLU RD k sc μ l x + bubLU RD k sc μ l y from
        fun x y => LinearMap.map_add _ x y]
    exact Submodule.add_mem _ hp hq
  | mul_X p x hp =>
    rw [map_mul, EndOne.val_mul, bubLU_comp]
    refine slideSetR_comp ?_ hp
    simp only [bubMap, MvPolynomial.aeval_X, EndOne.val_of]
    exact hgen x.1 (x.2 + 1)

/-- If the generators of `Π_μ` placed to the right of the strand `l` lie in `slideSetL`, then so
does every element of the image of `Π_μ`. -/
theorem bubRU_mem_of_gen
    (hgen : ∀ (i : I) (α : ℕ), bubRU RD k sc μ l (bubGen RD k sc μ i α) ∈ slideSetL RD k sc μ l)
    {β : End ((pres RD k sc).obj (ob RD μ []))} (hβ : IsBub RD k sc μ β) :
    bubRU RD k sc μ l β ∈ slideSetL RD k sc μ l := by
  obtain ⟨p, hp⟩ := hβ
  have hβ' : β = (bubMap RD k sc μ p).val := (congrArg EndOne.val hp).symm
  subst hβ'
  clear hp
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.algHom_C, EndOne.val_algebraMap,
      show bubRU RD k sc μ l (a • 𝟙 _) = a • bubRU RD k sc μ l (𝟙 _) from LinearMap.map_smul _ a _,
      bubRU_id]
    refine Submodule.smul_mem _ a ?_
    have := mem_slideSetL (l := l) (a := 0) (μ := μ) (IsBub.id (RD := RD) (k := k) (sc := sc))
    rwa [bubLU_id, dotsU_zero, Category.comp_id] at this
  | add p q hp hq =>
    rw [map_add, EndOne.val_add, show ∀ x y : End ((pres RD k sc).obj (ob RD μ [])),
      bubRU RD k sc μ l (x + y) = bubRU RD k sc μ l x + bubRU RD k sc μ l y from
        fun x y => LinearMap.map_add _ x y]
    exact Submodule.add_mem _ hp hq
  | mul_X p x hp =>
    rw [map_mul, EndOne.val_mul, bubRU_comp]
    refine slideSetL_comp ?_ hp
    simp only [bubMap, MvPolynomial.aeval_X, EndOne.val_of]
    exact hgen x.1 (x.2 + 1)

/-! ## Bubble slides across an upward strand -/


section UpSlides

variable (μ : X)

theorem dotsU_mem_slideSetR' (l : Letter I) (a : ℕ) : dotsU RD k sc μ l a ∈ slideSetR RD k sc μ l := by
  have := mem_slideSetR (RD := RD) (k := k) (sc := sc) (μ := μ) (l := l) (a := a) IsBub.id
  rwa [bubRU_id, Category.comp_id] at this

theorem dotsU_mem_slideSetL' (l : Letter I) (a : ℕ) : dotsU RD k sc μ l a ∈ slideSetL RD k sc μ l := by
  have := mem_slideSetL (RD := RD) (k := k) (sc := sc) (μ := μ) (l := l) (a := a) IsBub.id
  rwa [bubLU_id, Category.comp_id] at this

theorem τQ_mem_slideSetR (i j : I) (e : ℕ) :
    τQ RD k sc μ i j e ∈ slideSetR RD k sc μ (up j) :=
  Submodule.smul_mem _ _ (Submodule.sum_mem _ fun _ _ =>
    Submodule.smul_mem _ _ (dotsU_mem_slideSetR' μ _ _))

theorem τQ_mem_slideSetL (i j : I) (e : ℕ) :
    τQ RD k sc μ i j e ∈ slideSetL RD k sc μ (up j) :=
  Submodule.smul_mem _ _ (Submodule.sum_mem _ fun _ _ =>
    Submodule.smul_mem _ _ (dotsU_mem_slideSetL' μ _ _))

/-- A clockwise bubble moves from the left to the right of an upward strand (KL III
Proposition 3.3, second display; for `i ≠ j` and general Cautis–Lauda scalars, `slidesQ`). -/
theorem cw_slideR_up (i j : I) (α : ℕ) :
    bubLU RD k sc μ (up j) (cwU RD k sc (wt RD μ [up j]) i (ip RD i (wt RD μ [up j]) - 1 + α)) ∈
      slideSetR RD k sc μ (up j) := by
  by_cases hij : i = j
  · subst hij
    have h := prop33_cw_same_all RD k sc μ i α
    rw [lin_bubL_eq] at h
    rw [h]
    refine Submodule.sum_mem _ fun ℓ _ => ?_
    rw [lin_bubR_eq]
    exact nsmul_mem (mem_slideSetR' (cwU_isBub _ _)) _
  · change wLs RD k sc μ i (up j) α ∈ _
    rw [(slidesQ RD k sc μ hij).2 α, sconv_τQ_wRs RD k sc μ hij]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ ?_)
    split_ifs
    · rw [End.mul_def]; exact mem_slideSetR' (cwU_isBub _ _)
    · exact Submodule.zero_mem _

/-- A counterclockwise bubble moves from the left to the right of an upward strand (KL III
Proposition 3.4, second display, and Proposition 3.3 for `i · j = 0`; `slidesQ` in general). -/
theorem ccw_slideR_up (i j : I) (α : ℕ) :
    bubLU RD k sc μ (up j) (ccwU RD k sc (wt RD μ [up j]) i (-ip RD i (wt RD μ [up j]) - 1 + α)) ∈
      slideSetR RD k sc μ (up j) := by
  by_cases hij : i = j
  · subst hij
    have h := prop34_ccw_same_all RD k sc μ i α
    rw [lin_bubL_eq, lin_bubR_eq, lin_bubR_eq, lin_bubR_eq] at h
    rw [h]
    refine Submodule.add_mem _ (Submodule.sub_mem _ (mem_slideSetR' (ccwU_isBub _ _))
      (nsmul_mem (mem_slideSetR' (ccwU_isBub _ _)) _)) (mem_slideSetR_bub (ccwU_isBub _ _))
  · change cLs RD k sc μ i (up j) α ∈ _
    induction α using Nat.strong_induction_on with
    | _ α ih =>
    have h := (slidesQ RD k sc μ hij).1 α
    rw [sconv_eq_add_last, τQ_zero RD k sc μ hij, mul_one, ← sub_eq_iff_eq_add'] at h
    rw [← h]
    refine Submodule.sub_mem _ (mem_slideSetR_bub (ccwU_isBub _ _))
      (Submodule.sum_mem _ fun a ha => ?_)
    rw [End.mul_def]
    exact slideSetR_comp (τQ_mem_slideSetR μ i j _) (ih a (Finset.mem_range.1 ha))

/-- A clockwise bubble moves from the right to the left of an upward strand (KL III
Proposition 3.4, first display, and Proposition 3.3 for `i · j = 0`; `slidesQ` in general). -/
theorem cw_slideL_up (i j : I) (α : ℕ) :
    bubRU RD k sc μ (up j) (cwU RD k sc μ i (ip RD i μ - 1 + α)) ∈ slideSetL RD k sc μ (up j) := by
  by_cases hij : i = j
  · subst hij
    have h := prop34_cw_same_all RD k sc μ i α
    rw [lin_bubR_eq, lin_bubL_eq, lin_bubL_eq, lin_bubL_eq] at h
    rw [h]
    refine Submodule.add_mem _ (Submodule.sub_mem _ (mem_slideSetL' (cwU_isBub _ _))
      (nsmul_mem (mem_slideSetL' (cwU_isBub _ _)) _)) (mem_slideSetL_bub (cwU_isBub _ _))
  · change wRs RD k sc μ i (up j) α ∈ _
    induction α using Nat.strong_induction_on with
    | _ α ih =>
    have h := (slidesQ RD k sc μ hij).2 α
    rw [sconv, Finset.sum_range_succ', Nat.sub_zero, τQ_zero RD k sc μ hij, one_mul,
      ← sub_eq_iff_eq_add'] at h
    rw [← h]
    refine Submodule.sub_mem _ (mem_slideSetL_bub (cwU_isBub _ _))
      (Submodule.sum_mem _ fun a ha => ?_)
    have ha := Finset.mem_range.1 ha
    rw [End.mul_def]
    exact slideSetL_comp (ih _ (by omega)) (τQ_mem_slideSetL μ i j _)

/-- A counterclockwise bubble moves from the right to the left of an upward strand (KL III
Proposition 3.3, first display; `slidesQ` in general). -/
theorem ccw_slideL_up (i j : I) (α : ℕ) :
    bubRU RD k sc μ (up j) (ccwU RD k sc μ i (-ip RD i μ - 1 + α)) ∈ slideSetL RD k sc μ (up j) := by
  by_cases hij : i = j
  · subst hij
    have h := prop33_ccw_same_all RD k sc μ i α
    rw [lin_bubR_eq] at h
    rw [h]
    refine Submodule.sum_mem _ fun ℓ _ => ?_
    rw [lin_bubL_eq]
    exact nsmul_mem (mem_slideSetL' (ccwU_isBub _ _)) _
  · change cRs RD k sc μ i (up j) α ∈ _
    rw [(slidesQ RD k sc μ hij).1 α, sconv_cLs_τQ RD k sc μ hij]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ ?_)
    split_ifs
    · rw [End.mul_def]; exact mem_slideSetL (ccwU_isBub _ _)
    · exact Submodule.zero_mem _

/-- **Bubble slides across an upward strand, left to right**: every element of the image of
`Π_{μ + j_X}` placed to the left of `E_j` is a linear combination of dots on `E_j` times
elements of the image of `Π_μ` to its right. -/
theorem bubLU_up_mem_gen (j : I) {β : End ((pres RD k sc).obj (ob RD (wt RD μ [up j]) []))}
    (hβ : IsBub RD k sc (wt RD μ [up j]) β) : bubLU RD k sc μ (up j) β ∈ slideSetR RD k sc μ (up j) := by
  refine bubLU_mem_of_gen (fun i α => ?_) hβ
  unfold bubGen
  split_ifs
  · exact cw_slideR_up μ i j α
  · exact ccw_slideR_up μ i j α

/-- **Bubble slides across an upward strand, right to left.** -/
theorem bubRU_up_mem_gen (j : I) {β : End ((pres RD k sc).obj (ob RD μ []))} (hβ : IsBub RD k sc μ β) :
    bubRU RD k sc μ (up j) β ∈ slideSetL RD k sc μ (up j) := by
  refine bubRU_mem_of_gen (fun i α => ?_) hβ
  unfold bubGen
  split_ifs
  · exact cw_slideL_up μ i j α
  · exact ccw_slideL_up μ i j α

end UpSlides

/-! ## Bubble slides across a downward strand, by rotation -/





/-- `wtTransport` as a linear map. -/
def wtTransportL {x y : X} (h : x = y) :
    End ((pres RD k sc).obj (ob RD x [])) →ₗ[k] End ((pres RD k sc).obj (ob RD y [])) where
  toFun := wtTransport RD k sc h
  map_add' := wtTransport_add RD k sc h
  map_smul' := wtTransport_smul RD k sc h

theorem wtTransport_dg {x y : X} (h : x = y) (D : List (LayerData I)) :
    wtTransport RD k sc h (dg RD k sc x [] [] D) = dg RD k sc y [] [] D := by
  subst h; simp [wtTransport]

theorem IsBub.wtTransport {x y : X} (h : x = y) {β : End ((pres RD k sc).obj (ob RD x []))}
    (hβ : IsBub RD k sc x β) : IsBub RD k sc y (wtTransport RD k sc h β) := by
  subst h; simpa [CLQ.wtTransport] using hβ

section Rotation

variable (RD k sc μ) (j : I)

/-- Rotation of an endomorphism of the upward strand `E_j` (right region `μ - j_X`) into an
endomorphism of the downward strand `F_j` (right region `μ`): the cup `1 → F E` on the left and
the cap `E F → 1` on the right (as in KL III (3.3)). -/
def rotT : End ((pres RD k sc).obj (ob RD (wt RD μ [dn j]) [up j])) →ₗ[k]
    End ((pres RD k sc).obj (ob RD μ [dn j])) where
  toFun f := dg RD k sc μ [dn j] [dn j, up j, dn j] [([], .cup (dn j), [dn j])] ≫
    plcL RD k sc μ [dn j] [dn j] [up j] [up j] f ≫
      dg RD k sc μ [dn j, up j, dn j] [dn j] [([dn j], .cap (dn j), [])]
  map_add' f g := by rw [map_add, Preadditive.add_comp, Preadditive.comp_add]
  map_smul' r f := by rw [map_smul, Linear.smul_comp, Linear.comp_smul]; rfl

theorem rotT_apply (f : End ((pres RD k sc).obj (ob RD (wt RD μ [dn j]) [up j]))) :
    rotT RD k sc μ j f = dg RD k sc μ [dn j] [dn j, up j, dn j] [([], .cup (dn j), [dn j])] ≫
      plcL RD k sc μ [dn j] [dn j] [up j] [up j] f ≫
        dg RD k sc μ [dn j, up j, dn j] [dn j] [([dn j], .cap (dn j), [])] := rfl

theorem rotT_dg (A : List (LayerData I)) (hA : SChain [up j] A [up j]) :
    rotT RD k sc μ j (dg RD k sc (wt RD μ [dn j]) [up j] [up j] A) =
      dg RD k sc μ [dn j] [dn j] ([([], .cup (dn j), [dn j])] ++ A.map (whL [dn j] [dn j]) ++
        [([dn j], .cap (dn j), [])]) := by
  rw [rotT_apply, plcL_dg]
  have h₁ : SChain [dn j] [([], .cup (dn j), [dn j])] [dn j, up j, dn j] := by schain
  have h₂ : SChain [dn j, up j, dn j] (A.map (whL [dn j] [dn j])) [dn j, up j, dn j] := by
    simpa using hA.whisk [dn j] [dn j]
  have h₃ : SChain [dn j, up j, dn j] [([dn j], .cap (dn j), [])] [dn j] := by schain
  show dg RD k sc μ [dn j] [dn j, up j, dn j] _ ≫
    dg RD k sc μ [dn j, up j, dn j] [dn j, up j, dn j] (A.map (whL [dn j] [dn j])) ≫
      dg RD k sc μ [dn j, up j, dn j] [dn j] _ = _
  rw [dg_comp h₂ h₃, dg_comp h₁ (h₂.append h₃), List.append_assoc]

/-- Rotating a bubble to the right of `E_j` gives the bubble to the left of `F_j`. -/
theorem rotT_bubRU (β : End ((pres RD k sc).obj (ob RD (wt RD μ [dn j]) []))) :
    rotT RD k sc μ j (bubRU RD k sc (wt RD μ [dn j]) (up j) β) = bubLU RD k sc μ (dn j) β := by
  have key := hom_ext_dg RD k sc (wt RD μ [dn j]) (s := []) (t := [])
    ((rotT RD k sc μ j).comp (plcL RD k sc (wt RD μ [dn j]) [up j] [] [] []))
    (plcL RD k sc μ [] [dn j] [] []) (fun B hB => ?_)
  · exact LinearMap.congr_fun key β
  simp only [LinearMap.comp_apply]
  have e₀ : plcL RD k sc μ [] [dn j] [] [] (dg RD k sc (wt RD μ [dn j]) [] [] B) =
      dg RD k sc μ [dn j] [dn j] (B.map (whL [] [dn j])) := plcL_dg RD k sc μ [] [dn j] [] [] B
  have e₀' : plcL RD k sc (wt RD μ [dn j]) [up j] [] [] [] (dg RD k sc (wt RD μ [dn j]) [] [] B) =
      dg RD k sc (wt RD μ [dn j]) [up j] [up j] (B.map (whL [up j] [])) :=
    plcL_dg RD k sc (wt RD μ [dn j]) [up j] [] [] [] B
  erw [e₀, e₀', rotT_dg RD k sc μ j _ (by simpa using hB.whisk [up j] [])]
  wnf
  -- move the closed diagram below the cup
  have e₁ := dg_closed_left (RD := RD) (k := k) (sc := sc) μ (S := [dn j]) (T := [dn j]) []
    [([dn j], .cap (dn j), [])] (s := []) (s' := [dn j, up j]) [dn j] hB
    (A := [([], .cup (dn j), [])]) (by schain)
  wnf at e₁
  rw [e₁]
  -- the zigzag
  have hB' : SChain [dn j] (B.map (whL [] [dn j])) [dn j] := by simpa using hB.whisk [] [dn j]
  refine (dg_step RD k sc μ (s₀ := [dn j]) (t₀ := [dn j]) (B.map (whL [] [dn j])) [] [] []
    (dg_zigL' RD k sc μ (dn j)) (by simpa using hB') (by schain) ?_ rfl).trans ?_
  · wnf
  · wnf

/-- A zigzag on `F_j` with `a` upward dots on its middle segment is `a` downward dots. -/
theorem dg_zig_dots (a : ℕ) :
    dg RD k sc μ [dn j] [dn j] ([([], .cup (dn j), [dn j])] ++
        List.replicate a ([dn j], .dot (up j), [dn j]) ++ [([dn j], .cap (dn j), [])]) =
      dg RD k sc μ [dn j] [dn j] (List.replicate a ([], .dot (dn j), [])) := by
  dstepQ [] [([dn j], .cap (dn j), [])] [] [dn j] (dg_dots_cupDn RD k sc j (wt RD μ [dn j]) a)
  dstepQ [([], .cup (dn j), [dn j])] [] [] []
    (dg_swap_rep' RD k sc μ [] [] [] (.cap (dn j)) (.dot (dn j)) rfl a)
  dstepQ [] (List.replicate a ([], .dot (dn j), [])) [] [] (dg_zigL' RD k sc μ (dn j))
  simp

/-- Rotating dots and a bubble to the left of `E_j` gives dots and the bubble to the right of
`F_j`. -/
theorem rotT_dots_bubLU (a : ℕ)
    (δ : End ((pres RD k sc).obj (ob RD (wt RD (wt RD μ [dn j]) [up j]) []))) :
    rotT RD k sc μ j (dotsU RD k sc (wt RD μ [dn j]) (up j) a ≫ bubLU RD k sc (wt RD μ [dn j]) (up j) δ) =
      dotsU RD k sc μ (dn j) a ≫
        bubRU RD k sc μ (dn j) (wtTransport RD k sc (by simp : wt RD (wt RD μ [dn j]) [up j] = μ) δ) := by
  have hμ : wt RD (wt RD μ [dn j]) [up j] = μ := by simp
  have key := hom_ext_dg RD k sc (wt RD (wt RD μ [dn j]) [up j]) (s := []) (t := [])
    ((rotT RD k sc μ j).comp ((Linear.leftComp k _ (dotsU RD k sc (wt RD μ [dn j]) (up j) a)).comp
      (plcL RD k sc (wt RD μ [dn j]) [] [up j] [] [])))
    ((Linear.leftComp k _ (dotsU RD k sc μ (dn j) a)).comp
      ((plcL RD k sc μ [dn j] [] [] []).comp (wtTransportL (RD := RD) (k := k) (sc := sc) hμ))) (fun D hD => ?_)
  · exact LinearMap.congr_fun key δ
  change rotT RD k sc μ j (dotsU RD k sc (wt RD μ [dn j]) (up j) a ≫ plcL RD k sc (wt RD μ [dn j]) [] [up j] [] []
      (dg RD k sc (wt RD (wt RD μ [dn j]) [up j]) [] [] D)) =
    dotsU RD k sc μ (dn j) a ≫ plcL RD k sc μ [dn j] [] [] []
      (wtTransport RD k sc hμ (dg RD k sc (wt RD (wt RD μ [dn j]) [up j]) [] [] D))
  have e₀ : plcL RD k sc (wt RD μ [dn j]) [] [up j] [] []
      (dg RD k sc (wt RD (wt RD μ [dn j]) [up j]) [] [] D) =
      dg RD k sc (wt RD μ [dn j]) [up j] [up j] (D.map (whL [] [up j])) :=
    plcL_dg RD k sc (wt RD μ [dn j]) [] [up j] [] [] D
  have e₁ : plcL RD k sc μ [dn j] [] [] [] (dg RD k sc (wt RD μ []) [] [] D) =
      dg RD k sc μ [dn j] [dn j] (D.map (whL [dn j] [])) := plcL_dg RD k sc μ [dn j] [] [] [] D
  have hD₁ : SChain [up j] (D.map (whL [] [up j])) [up j] := by simpa using hD.whisk [] [up j]
  have hD₂ : SChain [dn j] (D.map (whL [dn j] [])) [dn j] := by simpa using hD.whisk [dn j] []
  have hrep : SChain [up j] (List.replicate a ([], .dot (up j), [])) [up j] :=
    SChain.replicate_of (by schain) a
  have hrep' : SChain [dn j] (List.replicate a ([], .dot (dn j), [])) [dn j] :=
    SChain.replicate_of (by schain) a
  rw [e₀, wtTransport_dg, e₁]
  rw [dotsU, dotsU, dg_comp hrep hD₁, dg_comp hrep' hD₂,
    rotT_dg RD k sc μ j _ (hrep.append hD₁)]
  wnf
  have e₂ := dg_closed_right (RD := RD) (k := k) (sc := sc) μ (S := [dn j]) (T := [dn j])
    ([([], .cup (dn j), [dn j])] ++ List.replicate a ([dn j], .dot (up j), [dn j])) [] [dn j]
    (t := [up j, dn j]) (t' := []) hD (A := [([], .cap (dn j), [])]) (by schain)
  wnf at e₂
  rw [e₂]
  have hX : SChain [dn j] ([([], .cup (dn j), [dn j])] ++
      List.replicate a ([dn j], .dot (up j), [dn j]) ++ [([dn j], .cap (dn j), [])]) [dn j] := by
    schain
  rw [show ([], Shape.cup (dn j), [dn j]) :: (List.replicate a ([dn j], .dot (up j), [dn j]) ++
      ([dn j], Shape.cap (dn j), []) :: D.map (whL [dn j] [])) =
      ([([], .cup (dn j), [dn j])] ++ List.replicate a ([dn j], .dot (up j), [dn j]) ++
        [([dn j], .cap (dn j), [])]) ++ D.map (whL [dn j] []) by simp,
    ← dg_comp hX hD₂, ← dg_comp hrep' hD₂, dg_zig_dots]

theorem rotT_slideSetL {f : End ((pres RD k sc).obj (ob RD (wt RD μ [dn j]) [up j]))}
    (hf : f ∈ slideSetL RD k sc (wt RD μ [dn j]) (up j)) : rotT RD k sc μ j f ∈ slideSetR RD k sc μ (dn j) := by
  have : slideSetL RD k sc (wt RD μ [dn j]) (up j) ≤ (slideSetR RD k sc μ (dn j)).comap (rotT RD k sc μ j) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨a, δ, hδ, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, rotT_dots_bubLU]
    exact mem_slideSetR (IsBub.wtTransport _ hδ)
  exact this hf

end Rotation

/-- **Bubble slides across a downward strand, left to right** (obtained from the right-to-left
slides across an upward strand by rotation): every element of the image of `Π_{μ - j_X}` placed
to the left of `F_j` is a linear combination of dots on `F_j` times elements of the image of
`Π_μ` to its right. -/
theorem bubLU_dn_mem_gen (μ : X) (j : I)
    {β : End ((pres RD k sc).obj (ob RD (wt RD μ [dn j]) []))} (hβ : IsBub RD k sc (wt RD μ [dn j]) β) :
    bubLU RD k sc μ (dn j) β ∈ slideSetR RD k sc μ (dn j) := by
  rw [← rotT_bubRU]
  exact rotT_slideSetL RD k sc μ j (bubRU_up_mem_gen (wt RD μ [dn j]) j hβ)

/-- **Bubble slides across any strand, left to right** (KL III Propositions 3.3, 3.4, and their
rotations): every element of the image of `Π_{μ + l_X}` placed to the left of the strand `l`
lies in `slideSetR μ l`. -/
theorem bubLU_mem_slideSetR_gen (μ : X) (l : Letter I)
    {β : End ((pres RD k sc).obj (ob RD (wt RD μ [l]) []))} (hβ : IsBub RD k sc (wt RD μ [l]) β) :
    bubLU RD k sc μ l β ∈ slideSetR RD k sc μ l := by
  obtain ⟨b, j⟩ := l
  cases b
  · exact bubLU_dn_mem_gen μ j hβ
  · exact bubLU_up_mem_gen μ j hβ

/-! ### The simply-laced forms (special cases) -/

theorem bubLU_up_mem (_hSL : SimplyLaced C) (μ : X) (j : I)
    {β : End ((pres RD k sc).obj (ob RD (wt RD μ [up j]) []))} (hβ : IsBub RD k sc (wt RD μ [up j]) β) :
    bubLU RD k sc μ (up j) β ∈ slideSetR RD k sc μ (up j) := bubLU_up_mem_gen μ j hβ

theorem bubRU_up_mem (_hSL : SimplyLaced C) (μ : X) (j : I) {β : End ((pres RD k sc).obj (ob RD μ []))}
    (hβ : IsBub RD k sc μ β) : bubRU RD k sc μ (up j) β ∈ slideSetL RD k sc μ (up j) :=
  bubRU_up_mem_gen μ j hβ

theorem bubLU_dn_mem (_hSL : SimplyLaced C) (μ : X) (j : I)
    {β : End ((pres RD k sc).obj (ob RD (wt RD μ [dn j]) []))} (hβ : IsBub RD k sc (wt RD μ [dn j]) β) :
    bubLU RD k sc μ (dn j) β ∈ slideSetR RD k sc μ (dn j) := bubLU_dn_mem_gen μ j hβ

theorem bubLU_mem_slideSetR (_hSL : SimplyLaced C) (μ : X) (l : Letter I)
    {β : End ((pres RD k sc).obj (ob RD (wt RD μ [l]) []))} (hβ : IsBub RD k sc (wt RD μ [l]) β) :
    bubLU RD k sc μ l β ∈ slideSetR RD k sc μ l := bubLU_mem_slideSetR_gen μ l hβ

end Categorification.KL3.Diagram.CLQ

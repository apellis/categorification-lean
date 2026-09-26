/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.EndOne
import Categorification.Diagrams.KL3.Pitchfork

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
element of the image of `Π` slides (`bubLU_mem_of_gen`, `bubLU_up_mem`, `bubRU_up_mem`).
For a downward strand `F_j` the slides are obtained by rotation (`rotT`: the cup `1 → F E` and
the cap `E F → 1`, zigzag relations, cyclicity of dots; `rotT_bubRU`, `rotT_dots_bubLU`):
`bubLU_dn_mem`. Altogether `bubLU_mem_slideSetR`: every element of the image of `Π` placed to
the left of any strand `l` lies in `slideSetR μ l`.

KL III state the bubble slides only for `i = j`, `i·j = -1` and `i·j = 0` (the simply-laced
case, their main case of interest `sl(n)`); accordingly these results assume that the Cartan
datum is simply laced (`SimplyLaced`).

## Other tools

`dg_closed_right`, `dg_closed_left`: a closed diagram commutes with any diagram on the strands to
its right (left) (interchange law); `wnf`: normalization of lists of layers keeping
`map (whL u v)` folded.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (k : Type w) [CommRing k]

/-! ## Normal forms of layers and diagrams -/

/-- The shape of a generator of `psig`. -/
def shapeOf : (psig RD).Gen → Shape I
  | .gen (.dot c) => .dot c.l
  | .gen (.cross ε i j _) => .cross ε i j
  | .cup c => .cup c.l
  | .cap c => .cap c.l

theorem map_l_wd (μ : X) (t : List (Letter I)) : (wd RD μ t).map Col.l = t := by
  induction t with
  | nil => rfl
  | cons l t ih => simp [ih]

theorem length_wd (μ : X) (t : List (Letter I)) : (wd RD μ t).length = t.length := by
  rw [← List.length_map (f := Col.l), map_l_wd]

theorem map_l_dom (g : (psig RD).Gen) : ((psig RD).dom g).map Col.l = (shapeOf RD g).dom := by
  rcases g with (⟨c⟩ | ⟨ε, i, j, ν⟩) | c | c <;> rfl

/-- **Every layer is in normal form**: a valid layer whose bottom boundary is `E_s 1_μ` is
`lay μ u g v` with `s = u ++ g.dom ++ v`. -/
theorem layer_eq_lay (μ : X) (s : List (Letter I)) (L : Layer (psig RD)) (hv : L.Valid)
    (hd : L.dom = ob RD μ s) :
    s = L.left.map Col.l ++ (shapeOf RD L.gen).dom ++ L.right.map Col.l ∧
      L = lay RD μ (L.left.map Col.l) (shapeOf RD L.gen) (L.right.map Col.l) := by
  obtain ⟨st, lf, g, rt⟩ := L
  have hs : st = wt RD μ s := congrArg Obj.start hd
  have hw : lf ++ (psig RD).dom g ++ rt = wd RD μ s := congrArg Obj.word hd
  set u := lf.map Col.l
  set v := rt.map Col.l
  have hsd : s = u ++ (shapeOf RD g).dom ++ v := by
    have := congrArg (List.map Col.l) hw
    rw [map_l_wd, List.map_append, List.map_append, map_l_dom] at this
    exact this.symm
  refine ⟨hsd, ?_⟩
  subst hsd
  rw [wd_append, wd_append] at hw
  have hl1 : lf.length = (wd RD (wt RD (wt RD μ v) (shapeOf RD g).dom) u).length := by
    rw [length_wd]; simp [u]
  have hl3 : rt.length = (wd RD μ v).length := by rw [length_wd]; simp [v]
  rw [List.append_assoc, List.append_assoc] at hw
  obtain ⟨h1, hw'⟩ := List.append_inj hw hl1
  have hl2 : ((psig RD).dom g).length = (wd RD (wt RD μ v) (shapeOf RD g).dom).length := by
    have := congrArg List.length hw'
    simp only [List.length_append] at this
    omega
  obtain ⟨h2, h3⟩ := List.append_inj hw' hl2
  have hgen : g = (shapeOf RD g).gen RD (wt RD μ v) := by
    rcases g with (⟨c⟩ | ⟨ε, i, j, ν⟩) | c | c
    · have : c = ⟨c.l, wt RD μ v⟩ := by
        have h2' : [c] = [(⟨c.l, wt RD μ v⟩ : Col I X)] := h2
        simpa using h2'
      exact congrArg (fun c => (PivotalGen.gen (Gen0.dot c) : (psig RD).Gen)) this
    · have h2' : wd RD ν [(ε, i), (ε, j)] = wd RD (wt RD μ v) [(ε, i), (ε, j)] := h2
      simp only [wd_cons, wd_nil, List.cons.injEq, Col.mk.injEq, and_true, true_and] at h2'
      have hν : ν = wt RD μ v := h2'.2
      subst hν; rfl
    · -- cup: the region is determined by validity
      have hle := hv.left_end
      simp only [Signature.pivotal_endR] at hle
      have hsθ : st = wt RD μ (u ++ v) := by rw [hs]; simp [shapeOf]
      have e1 : lf = wd RD (wt RD μ v) u := by simpa using h1
      have hL : (psig RD).endR st lf = wt RD μ v := by
        rw [e1, hsθ, wt_append]; exact endR_wd RD _ u
      have hleft : (psig RD).left (PivotalGen.cup c : (psig RD).Gen) = sh RD c.l + c.r := rfl
      rw [Signature.pivotal_endR] at hL
      have hc : sh RD c.l + c.r = wt RD μ v := by rw [← hL, ← hleft]; exact hle.symm
      show PivotalGen.cup c = PivotalGen.cup ⟨c.l, sh RD c.l.dual + wt RD μ v⟩
      congr 1
      refine Col.ext rfl ?_
      rw [← hc, ← add_assoc, sh_dual_add_sh, zero_add]
    · have h2' : [(⟨c.l.dual, sh RD c.l + c.r⟩ : Col I X), c] =
          [⟨c.l.dual, sh RD c.l + wt RD μ v⟩, ⟨c.l, wt RD μ v⟩] := h2
      simp only [List.cons.injEq, and_true] at h2'
      have : c = ⟨c.l, wt RD μ v⟩ := h2'.2
      exact congrArg (fun c => (PivotalGen.cap c : (psig RD).Gen)) this
  refine Layer.ext ?_ ?_ ?_ ?_
  · simp only [lay, hs]
  · simp only [lay]; rw [h1, wt_append]
  · exact hgen
  · simp only [lay]; exact h3

/-- **Every diagram of `U` between normal-form objects is a normal-form diagram.** -/
theorem exists_mkD (μ : X) {s t : List (Letter I)} (d : ob RD μ s ⟶ ob RD μ t) :
    ∃ (ls : List (LayerData I)) (h : SChain s ls t), d = mkD RD μ ls h := by
  obtain ⟨Ls, hc⟩ := d
  induction Ls generalizing s with
  | nil =>
    have e : ob RD μ s = ob RD μ t := hc
    have e' : s = t := by
      have := congrArg (fun o => (Obj.word o).map Col.l) e
      simpa [map_l_wd] using this
    subst e'
    exact ⟨[], rfl, rfl⟩
  | cons L Ls ih =>
    obtain ⟨hv, hd, hc'⟩ := hc
    obtain ⟨hs, hL⟩ := layer_eq_lay RD μ s L hv hd
    set x : LayerData I := (L.left.map Col.l, shapeOf RD L.gen, L.right.map Col.l)
    have hcod : L.cod = ob RD μ (x.1 ++ x.2.1.cod ++ x.2.2) := by
      rw [hL]; exact lay_cod RD μ _ _ _
    rw [hcod] at hc'
    obtain ⟨ls, h, e⟩ := ih hc'
    refine ⟨x :: ls, ⟨hs, h⟩, ?_⟩
    apply Subtype.ext
    have e' := congrArg Subtype.val e
    simp only at e'
    show L :: Ls = layList RD μ (x :: ls)
    rw [layList_cons, ← hL]
    exact congrArg (L :: ·) e'

/-- Linear maps on the `Hom`-spaces of `U` between normal-form objects agree if they agree on the
classes `dg μ s t ls` of all normal-form diagrams. -/
theorem hom_ext_dg (μ : X) {s t : List (Letter I)} {M : Type*} [AddCommGroup M] [Module k M]
    (φ ψ : ((pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ t)) →ₗ[k] M)
    (h : ∀ ls : List (LayerData I), SChain s ls t → φ (dg RD k μ s t ls) = ψ (dg RD k μ s t ls)) :
    φ = ψ := by
  refine hom_ext_diag RD k φ ψ fun d => ?_
  obtain ⟨ls, hls, rfl⟩ := exists_mkD RD μ d
  rw [← dg_of hls]
  exact h ls hls

/-- Every 2-morphism of `U` between normal-form objects is a linear combination of classes of
normal-form diagrams. -/
theorem mem_span_dg (μ : X) {s t : List (Letter I)}
    (f : (pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ t)) :
    f ∈ Submodule.span k {g | ∃ ls, SChain s ls t ∧ g = dg RD k μ s t ls} := by
  obtain ⟨F, rfl⟩ := (pres RD k).lin_surjective f
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

variable {RD k}

/-- A closed diagram `D` placed between the strands `u` and `t` commutes with a diagram `A` on
the strands `t` to its right. -/
theorem dg_closed_right (μ : X) {S T : List (Letter I)} (pre post : List (LayerData I))
    (u : List (Letter I)) {t t' : List (Letter I)} {D A : List (LayerData I)}
    (hD : SChain [] D []) (hA : SChain t A t') :
    dg RD k μ S T (pre ++ D.map (whL u t) ++ A.map (whL u []) ++ post) =
      dg RD k μ S T (pre ++ A.map (whL u []) ++ D.map (whL u t') ++ post) := by
  have h := dg_interchange (RD := RD) (k := k) (μ := μ) (S := S) (T := T) pre post
    (hD.whisk u []) hA
  simp only [List.map_map, Function.comp_def, whL, List.append_nil, List.nil_append] at h ⊢
  exact h

/-- A closed diagram `D` placed between the strands `s` and `v` commutes with a diagram `A` on
the strands `s` to its left. -/
theorem dg_closed_left (μ : X) {S T : List (Letter I)} (pre post : List (LayerData I))
    {s s' : List (Letter I)} (v : List (Letter I)) {D A : List (LayerData I)}
    (hD : SChain [] D []) (hA : SChain s A s') :
    dg RD k μ S T (pre ++ A.map (whL [] v) ++ D.map (whL s' v) ++ post) =
      dg RD k μ S T (pre ++ D.map (whL s v) ++ A.map (whL [] v) ++ post) := by
  have h := dg_interchange (RD := RD) (k := k) (μ := μ) (S := S) (T := T) pre post
    hA (hD.whisk [] v)
  simp only [List.map_map, Function.comp_def, whL, List.append_nil, List.nil_append] at h ⊢
  exact h

end Interchange

/-! ## The sets `x^a ⊗ Π` next to a strand -/

variable (μ : X) (l : Letter I)

/-- The span of `x^a ⊗ γ`: `a` dots on the strand `l` and an element `γ` of the image of
`Π_μ` to its right (rightmost region `μ`). -/
def slideSetR : Submodule k (End ((pres RD k).obj (ob RD μ [l]))) :=
  Submodule.span k {f | ∃ (a : ℕ) (γ : End ((pres RD k).obj (ob RD μ []))),
    IsBub RD k μ γ ∧ f = dotsU RD k μ l a ≫ bubRU RD k μ l γ}

/-- The span of `γ ⊗ x^a`: `a` dots on the strand `l` and an element `γ` of the image of
`Π_{μ + l_X}` to its left (rightmost region `μ`). -/
def slideSetL : Submodule k (End ((pres RD k).obj (ob RD μ [l]))) :=
  Submodule.span k {f | ∃ (a : ℕ) (γ : End ((pres RD k).obj (ob RD (wt RD μ [l]) []))),
    IsBub RD k (wt RD μ [l]) γ ∧ f = dotsU RD k μ l a ≫ bubLU RD k μ l γ}

variable {RD k μ l}

theorem mem_slideSetR {a : ℕ} {γ : End ((pres RD k).obj (ob RD μ []))} (hγ : IsBub RD k μ γ) :
    dotsU RD k μ l a ≫ bubRU RD k μ l γ ∈ slideSetR RD k μ l :=
  Submodule.subset_span ⟨a, γ, hγ, rfl⟩

theorem mem_slideSetR' {a : ℕ} {γ : End ((pres RD k).obj (ob RD μ []))} (hγ : IsBub RD k μ γ) :
    bubRU RD k μ l γ ≫ dotsU RD k μ l a ∈ slideSetR RD k μ l := by
  rw [bubRU_comm]; exact mem_slideSetR hγ

theorem mem_slideSetR_bub {γ : End ((pres RD k).obj (ob RD μ []))} (hγ : IsBub RD k μ γ) :
    bubRU RD k μ l γ ∈ slideSetR RD k μ l := by
  simpa [dotsU_zero] using mem_slideSetR (l := l) (a := 0) hγ

theorem mem_slideSetL {a : ℕ} {γ : End ((pres RD k).obj (ob RD (wt RD μ [l]) []))}
    (hγ : IsBub RD k (wt RD μ [l]) γ) :
    dotsU RD k μ l a ≫ bubLU RD k μ l γ ∈ slideSetL RD k μ l :=
  Submodule.subset_span ⟨a, γ, hγ, rfl⟩

theorem mem_slideSetL' {a : ℕ} {γ : End ((pres RD k).obj (ob RD (wt RD μ [l]) []))}
    (hγ : IsBub RD k (wt RD μ [l]) γ) :
    bubLU RD k μ l γ ≫ dotsU RD k μ l a ∈ slideSetL RD k μ l := by
  rw [bubLU_comm]; exact mem_slideSetL hγ

theorem mem_slideSetL_bub {γ : End ((pres RD k).obj (ob RD (wt RD μ [l]) []))}
    (hγ : IsBub RD k (wt RD μ [l]) γ) : bubLU RD k μ l γ ∈ slideSetL RD k μ l := by
  simpa [dotsU_zero] using mem_slideSetL (l := l) (a := 0) hγ

theorem slideSetR_comp {f g : End ((pres RD k).obj (ob RD μ [l]))} (hf : f ∈ slideSetR RD k μ l)
    (hg : g ∈ slideSetR RD k μ l) : f ≫ g ∈ slideSetR RD k μ l := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, γ, hγ, rfl⟩ := hf
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨b, δ, hδ, rfl⟩ := hg
      rw [Category.assoc, ← Category.assoc (bubRU RD k μ l γ), bubRU_comm, Category.assoc,
        ← Category.assoc, dotsU_add, ← bubRU_comp]
      exact mem_slideSetR (IsBub.comp hγ hδ)
    | zero => rw [Limits.comp_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [Preadditive.comp_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [Linear.comp_smul]; exact Submodule.smul_mem _ r hx
  | zero => rw [Limits.zero_comp]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Preadditive.add_comp]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [Linear.smul_comp]; exact Submodule.smul_mem _ r hx

theorem slideSetL_comp {f g : End ((pres RD k).obj (ob RD μ [l]))} (hf : f ∈ slideSetL RD k μ l)
    (hg : g ∈ slideSetL RD k μ l) : f ≫ g ∈ slideSetL RD k μ l := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, γ, hγ, rfl⟩ := hf
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨b, δ, hδ, rfl⟩ := hg
      rw [Category.assoc, ← Category.assoc (bubLU RD k μ l γ), bubLU_comm, Category.assoc,
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
    (hgen : ∀ (i : I) (α : ℕ), bubLU RD k μ l (bubGen RD k (wt RD μ [l]) i α) ∈ slideSetR RD k μ l)
    {β : End ((pres RD k).obj (ob RD (wt RD μ [l]) []))} (hβ : IsBub RD k (wt RD μ [l]) β) :
    bubLU RD k μ l β ∈ slideSetR RD k μ l := by
  obtain ⟨p, hp⟩ := hβ
  have hβ' : β = (bubMap RD k (wt RD μ [l]) p).val := (congrArg EndOne.val hp).symm
  subst hβ'
  clear hp
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.algHom_C, EndOne.val_algebraMap,
      show bubLU RD k μ l (a • 𝟙 _) = a • bubLU RD k μ l (𝟙 _) from LinearMap.map_smul _ a _,
      bubLU_id]
    refine Submodule.smul_mem _ a ?_
    simpa [bubRU_id, dotsU_zero] using mem_slideSetR (l := l) (a := 0) (μ := μ) (IsBub.id)
  | add p q hp hq =>
    rw [map_add, EndOne.val_add, show ∀ x y : End ((pres RD k).obj (ob RD (wt RD μ [l]) [])),
      bubLU RD k μ l (x + y) = bubLU RD k μ l x + bubLU RD k μ l y from
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
    (hgen : ∀ (i : I) (α : ℕ), bubRU RD k μ l (bubGen RD k μ i α) ∈ slideSetL RD k μ l)
    {β : End ((pres RD k).obj (ob RD μ []))} (hβ : IsBub RD k μ β) :
    bubRU RD k μ l β ∈ slideSetL RD k μ l := by
  obtain ⟨p, hp⟩ := hβ
  have hβ' : β = (bubMap RD k μ p).val := (congrArg EndOne.val hp).symm
  subst hβ'
  clear hp
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.algHom_C, EndOne.val_algebraMap,
      show bubRU RD k μ l (a • 𝟙 _) = a • bubRU RD k μ l (𝟙 _) from LinearMap.map_smul _ a _,
      bubRU_id]
    refine Submodule.smul_mem _ a ?_
    have := mem_slideSetL (l := l) (a := 0) (μ := μ) (IsBub.id (RD := RD) (k := k))
    rwa [bubLU_id, dotsU_zero, Category.comp_id] at this
  | add p q hp hq =>
    rw [map_add, EndOne.val_add, show ∀ x y : End ((pres RD k).obj (ob RD μ [])),
      bubRU RD k μ l (x + y) = bubRU RD k μ l x + bubRU RD k μ l y from
        fun x y => LinearMap.map_add _ x y]
    exact Submodule.add_mem _ hp hq
  | mul_X p x hp =>
    rw [map_mul, EndOne.val_mul, bubRU_comp]
    refine slideSetL_comp ?_ hp
    simp only [bubMap, MvPolynomial.aeval_X, EndOne.val_of]
    exact hgen x.1 (x.2 + 1)

/-! ## Bubble slides across an upward strand -/

/-- The Cartan datum is simply laced: `i · j ∈ {0, -1}` for `i ≠ j` (the case of KL III's bubble
slides, Propositions 3.3 and 3.4). -/
def SimplyLaced (C : CartanDatum I) : Prop := ∀ i j, i ≠ j → C.dot i j = 0 ∨ C.dot i j = -1

section UpSlides

variable (hSL : SimplyLaced C) (μ : X)
include hSL

/-- A clockwise bubble moves from the left to the right of an upward strand (KL III
Proposition 3.3, second display). -/
theorem cw_slideR_up (i j : I) (α : ℕ) :
    bubLU RD k μ (up j) (cwU RD k (wt RD μ [up j]) i (ip RD i (wt RD μ [up j]) - 1 + α)) ∈
      slideSetR RD k μ (up j) := by
  by_cases hij : i = j
  · subst hij
    have h := prop33_cw_same_all RD k μ i α
    rw [lin_bubL_eq] at h
    rw [h]
    refine Submodule.sum_mem _ fun ℓ _ => ?_
    rw [lin_bubR_eq]
    exact nsmul_mem (mem_slideSetR' (cwU_isBub _ _)) _
  · rcases hSL i j hij with h0 | h1
    · have h := prop33_cw_orth_all RD k μ i j h0 α
      have hn : ip RD i (wt RD μ [up j]) = ip RD i μ := by
        rw [ip_wt_up, A_of_dot_zero h0, zero_add]
      rw [lin_bubL_eq, lin_bubR_eq] at h
      rw [hn, h]; exact mem_slideSetR_bub (cwU_isBub _ _)
    · have h := prop33_cw_adj_all RD k μ i j h1 α
      rw [lin_bubL_eq, lin_bubR_eq, lin_bubR_eq] at h
      rw [h]
      exact Submodule.add_mem _ (mem_slideSetR' (cwU_isBub _ _)) (mem_slideSetR_bub (cwU_isBub _ _))

/-- A counterclockwise bubble moves from the left to the right of an upward strand (KL III
Proposition 3.4, second display, and Proposition 3.3 for `i · j = 0`). -/
theorem ccw_slideR_up (i j : I) (α : ℕ) :
    bubLU RD k μ (up j) (ccwU RD k (wt RD μ [up j]) i (-ip RD i (wt RD μ [up j]) - 1 + α)) ∈
      slideSetR RD k μ (up j) := by
  by_cases hij : i = j
  · subst hij
    have h := prop34_ccw_same_all RD k μ i α
    rw [lin_bubL_eq, lin_bubR_eq, lin_bubR_eq, lin_bubR_eq] at h
    rw [h]
    refine Submodule.add_mem _ (Submodule.sub_mem _ (mem_slideSetR' (ccwU_isBub _ _))
      (nsmul_mem (mem_slideSetR' (ccwU_isBub _ _)) _)) (mem_slideSetR_bub (ccwU_isBub _ _))
  · rcases hSL i j hij with h0 | h1
    · have h := prop33_ccw_orth_all RD k μ i j h0 α
      have hn : ip RD i (wt RD μ [up j]) = ip RD i μ := by
        rw [ip_wt_up, A_of_dot_zero h0, zero_add]
      rw [lin_bubL_eq, lin_bubR_eq] at h
      rw [hn, ← h]; exact mem_slideSetR_bub (ccwU_isBub _ _)
    · have h := prop34_ccw_adj_all RD k μ i j h1 α
      rw [lin_bubL_eq] at h
      rw [h]
      refine Submodule.sum_mem _ fun f _ => ?_
      rw [lin_bubR_eq]
      exact zsmul_mem (mem_slideSetR' (ccwU_isBub _ _)) _

/-- A clockwise bubble moves from the right to the left of an upward strand (KL III
Proposition 3.4, first display, and Proposition 3.3 for `i · j = 0`). -/
theorem cw_slideL_up (i j : I) (α : ℕ) :
    bubRU RD k μ (up j) (cwU RD k μ i (ip RD i μ - 1 + α)) ∈ slideSetL RD k μ (up j) := by
  by_cases hij : i = j
  · subst hij
    have h := prop34_cw_same_all RD k μ i α
    rw [lin_bubR_eq, lin_bubL_eq, lin_bubL_eq, lin_bubL_eq] at h
    rw [h]
    refine Submodule.add_mem _ (Submodule.sub_mem _ (mem_slideSetL' (cwU_isBub _ _))
      (nsmul_mem (mem_slideSetL' (cwU_isBub _ _)) _)) (mem_slideSetL_bub (cwU_isBub _ _))
  · rcases hSL i j hij with h0 | h1
    · have h := prop33_cw_orth_all RD k μ i j h0 α
      rw [lin_bubL_eq, lin_bubR_eq] at h
      rw [← h]; exact mem_slideSetL_bub (cwU_isBub _ _)
    · have h := prop34_cw_adj_all RD k μ i j h1 α
      rw [lin_bubR_eq] at h
      rw [h]
      refine Submodule.sum_mem _ fun f _ => ?_
      rw [lin_bubL_eq]
      exact zsmul_mem (mem_slideSetL' (cwU_isBub _ _)) _

/-- A counterclockwise bubble moves from the right to the left of an upward strand (KL III
Proposition 3.3, first display). -/
theorem ccw_slideL_up (i j : I) (α : ℕ) :
    bubRU RD k μ (up j) (ccwU RD k μ i (-ip RD i μ - 1 + α)) ∈ slideSetL RD k μ (up j) := by
  by_cases hij : i = j
  · subst hij
    have h := prop33_ccw_same_all RD k μ i α
    rw [lin_bubR_eq] at h
    rw [h]
    refine Submodule.sum_mem _ fun ℓ _ => ?_
    rw [lin_bubL_eq]
    exact nsmul_mem (mem_slideSetL' (ccwU_isBub _ _)) _
  · rcases hSL i j hij with h0 | h1
    · have h := prop33_ccw_orth_all RD k μ i j h0 α
      rw [lin_bubL_eq, lin_bubR_eq] at h
      rw [h]; exact mem_slideSetL_bub (ccwU_isBub _ _)
    · have h := prop33_ccw_adj_all RD k μ i j h1 α
      rw [lin_bubR_eq, lin_bubL_eq, lin_bubL_eq] at h
      rw [h]
      exact Submodule.add_mem _ (mem_slideSetL_bub (ccwU_isBub _ _)) (mem_slideSetL' (ccwU_isBub _ _))

/-- **Bubble slides across an upward strand, left to right**: every element of the image of
`Π_{μ + j_X}` placed to the left of `E_j` is a linear combination of dots on `E_j` times
elements of the image of `Π_μ` to its right. -/
theorem bubLU_up_mem (j : I) {β : End ((pres RD k).obj (ob RD (wt RD μ [up j]) []))}
    (hβ : IsBub RD k (wt RD μ [up j]) β) : bubLU RD k μ (up j) β ∈ slideSetR RD k μ (up j) := by
  refine bubLU_mem_of_gen (fun i α => ?_) hβ
  unfold bubGen
  split_ifs
  · exact cw_slideR_up hSL μ i j α
  · exact ccw_slideR_up hSL μ i j α

/-- **Bubble slides across an upward strand, right to left.** -/
theorem bubRU_up_mem (j : I) {β : End ((pres RD k).obj (ob RD μ []))} (hβ : IsBub RD k μ β) :
    bubRU RD k μ (up j) β ∈ slideSetL RD k μ (up j) := by
  refine bubRU_mem_of_gen (fun i α => ?_) hβ
  unfold bubGen
  split_ifs
  · exact cw_slideL_up hSL μ i j α
  · exact ccw_slideL_up hSL μ i j α

end UpSlides

/-! ## Bubble slides across a downward strand, by rotation -/

@[simp] theorem whL_mk (u v a b : List (Letter I)) (g : Shape I) :
    whL u v (a, g, b) = (u ++ a, g, b ++ v) := rfl

@[simp] theorem map_whL_whL (u v u' v' : List (Letter I)) (A : List (LayerData I)) :
    (A.map (whL u' v')).map (whL u v) = A.map (whL (u ++ u') (v' ++ v)) := by
  simp [List.map_map, Function.comp_def, whL, List.append_assoc]

/-- Normal form of lists of layers that keeps `map (whL u v)` folded. -/
syntax "wnf" (ppSpace Lean.Parser.Tactic.location)? : tactic

macro_rules
  | `(tactic| wnf $[$loc]?) => `(tactic| simp only [map_whL_whL, whL_mk, List.map_cons,
      List.map_nil, List.map_append, List.cons_append, List.nil_append, List.append_nil,
      List.singleton_append, List.append_assoc, map_whL_nil_nil, List.map_replicate] $[$loc]?)

/-- `wtTransport` as a linear map. -/
def wtTransportL {x y : X} (h : x = y) :
    End ((pres RD k).obj (ob RD x [])) →ₗ[k] End ((pres RD k).obj (ob RD y [])) where
  toFun := wtTransport RD k h
  map_add' := wtTransport_add RD k h
  map_smul' := wtTransport_smul RD k h

theorem wtTransport_dg {x y : X} (h : x = y) (D : List (LayerData I)) :
    wtTransport RD k h (dg RD k x [] [] D) = dg RD k y [] [] D := by
  subst h; simp [wtTransport]

theorem IsBub.wtTransport {x y : X} (h : x = y) {β : End ((pres RD k).obj (ob RD x []))}
    (hβ : IsBub RD k x β) : IsBub RD k y (Diagram.wtTransport RD k h β) := by
  subst h; simpa [Diagram.wtTransport] using hβ

section Rotation

variable (RD k μ) (j : I)

/-- Rotation of an endomorphism of the upward strand `E_j` (right region `μ - j_X`) into an
endomorphism of the downward strand `F_j` (right region `μ`): the cup `1 → F E` on the left and
the cap `E F → 1` on the right (as in KL III (3.3)). -/
def rotT : End ((pres RD k).obj (ob RD (wt RD μ [dn j]) [up j])) →ₗ[k]
    End ((pres RD k).obj (ob RD μ [dn j])) where
  toFun f := dg RD k μ [dn j] [dn j, up j, dn j] [([], .cup (dn j), [dn j])] ≫
    plcL RD k μ [dn j] [dn j] [up j] [up j] f ≫
      dg RD k μ [dn j, up j, dn j] [dn j] [([dn j], .cap (dn j), [])]
  map_add' f g := by rw [map_add, Preadditive.add_comp, Preadditive.comp_add]
  map_smul' r f := by rw [map_smul, Linear.smul_comp, Linear.comp_smul]; rfl

theorem rotT_apply (f : End ((pres RD k).obj (ob RD (wt RD μ [dn j]) [up j]))) :
    rotT RD k μ j f = dg RD k μ [dn j] [dn j, up j, dn j] [([], .cup (dn j), [dn j])] ≫
      plcL RD k μ [dn j] [dn j] [up j] [up j] f ≫
        dg RD k μ [dn j, up j, dn j] [dn j] [([dn j], .cap (dn j), [])] := rfl

theorem rotT_dg (A : List (LayerData I)) (hA : SChain [up j] A [up j]) :
    rotT RD k μ j (dg RD k (wt RD μ [dn j]) [up j] [up j] A) =
      dg RD k μ [dn j] [dn j] ([([], .cup (dn j), [dn j])] ++ A.map (whL [dn j] [dn j]) ++
        [([dn j], .cap (dn j), [])]) := by
  rw [rotT_apply, plcL_dg]
  have h₁ : SChain [dn j] [([], .cup (dn j), [dn j])] [dn j, up j, dn j] := by schain
  have h₂ : SChain [dn j, up j, dn j] (A.map (whL [dn j] [dn j])) [dn j, up j, dn j] := by
    simpa using hA.whisk [dn j] [dn j]
  have h₃ : SChain [dn j, up j, dn j] [([dn j], .cap (dn j), [])] [dn j] := by schain
  show dg RD k μ [dn j] [dn j, up j, dn j] _ ≫
    dg RD k μ [dn j, up j, dn j] [dn j, up j, dn j] (A.map (whL [dn j] [dn j])) ≫
      dg RD k μ [dn j, up j, dn j] [dn j] _ = _
  rw [dg_comp h₂ h₃, dg_comp h₁ (h₂.append h₃), List.append_assoc]

/-- Rotating a bubble to the right of `E_j` gives the bubble to the left of `F_j`. -/
theorem rotT_bubRU (β : End ((pres RD k).obj (ob RD (wt RD μ [dn j]) []))) :
    rotT RD k μ j (bubRU RD k (wt RD μ [dn j]) (up j) β) = bubLU RD k μ (dn j) β := by
  have key := hom_ext_dg RD k (wt RD μ [dn j]) (s := []) (t := [])
    ((rotT RD k μ j).comp (plcL RD k (wt RD μ [dn j]) [up j] [] [] []))
    (plcL RD k μ [] [dn j] [] []) (fun B hB => ?_)
  · exact LinearMap.congr_fun key β
  simp only [LinearMap.comp_apply]
  have e₀ : plcL RD k μ [] [dn j] [] [] (dg RD k (wt RD μ [dn j]) [] [] B) =
      dg RD k μ [dn j] [dn j] (B.map (whL [] [dn j])) := plcL_dg RD k μ [] [dn j] [] [] B
  have e₀' : plcL RD k (wt RD μ [dn j]) [up j] [] [] [] (dg RD k (wt RD μ [dn j]) [] [] B) =
      dg RD k (wt RD μ [dn j]) [up j] [up j] (B.map (whL [up j] [])) :=
    plcL_dg RD k (wt RD μ [dn j]) [up j] [] [] [] B
  erw [e₀, e₀', rotT_dg RD k μ j _ (by simpa using hB.whisk [up j] [])]
  wnf
  -- move the closed diagram below the cup
  have e₁ := dg_closed_left (RD := RD) (k := k) μ (S := [dn j]) (T := [dn j]) []
    [([dn j], .cap (dn j), [])] (s := []) (s' := [dn j, up j]) [dn j] hB
    (A := [([], .cup (dn j), [])]) (by schain)
  wnf at e₁
  rw [e₁]
  -- the zigzag
  have hB' : SChain [dn j] (B.map (whL [] [dn j])) [dn j] := by simpa using hB.whisk [] [dn j]
  refine (dg_step RD k μ (s₀ := [dn j]) (t₀ := [dn j]) (B.map (whL [] [dn j])) [] [] []
    (dg_zigL' RD k μ (dn j)) (by simpa using hB') (by schain) ?_ rfl).trans ?_
  · wnf
  · wnf

/-- A zigzag on `F_j` with `a` upward dots on its middle segment is `a` downward dots. -/
theorem dg_zig_dots (a : ℕ) :
    dg RD k μ [dn j] [dn j] ([([], .cup (dn j), [dn j])] ++
        List.replicate a ([dn j], .dot (up j), [dn j]) ++ [([dn j], .cap (dn j), [])]) =
      dg RD k μ [dn j] [dn j] (List.replicate a ([], .dot (dn j), [])) := by
  dstep [] [([dn j], .cap (dn j), [])] [] [dn j] (dg_dots_cupDn RD k j (wt RD μ [dn j]) a)
  dstep [([], .cup (dn j), [dn j])] [] [] []
    (dg_swap_rep' RD k μ [] [] [] (.cap (dn j)) (.dot (dn j)) rfl a)
  dstep [] (List.replicate a ([], .dot (dn j), [])) [] [] (dg_zigL' RD k μ (dn j))
  simp

/-- Rotating dots and a bubble to the left of `E_j` gives dots and the bubble to the right of
`F_j`. -/
theorem rotT_dots_bubLU (a : ℕ)
    (δ : End ((pres RD k).obj (ob RD (wt RD (wt RD μ [dn j]) [up j]) []))) :
    rotT RD k μ j (dotsU RD k (wt RD μ [dn j]) (up j) a ≫ bubLU RD k (wt RD μ [dn j]) (up j) δ) =
      dotsU RD k μ (dn j) a ≫
        bubRU RD k μ (dn j) (wtTransport RD k (by simp : wt RD (wt RD μ [dn j]) [up j] = μ) δ) := by
  have hμ : wt RD (wt RD μ [dn j]) [up j] = μ := by simp
  have key := hom_ext_dg RD k (wt RD (wt RD μ [dn j]) [up j]) (s := []) (t := [])
    ((rotT RD k μ j).comp ((Linear.leftComp k _ (dotsU RD k (wt RD μ [dn j]) (up j) a)).comp
      (plcL RD k (wt RD μ [dn j]) [] [up j] [] [])))
    ((Linear.leftComp k _ (dotsU RD k μ (dn j) a)).comp
      ((plcL RD k μ [dn j] [] [] []).comp (wtTransportL (RD := RD) (k := k) hμ))) (fun D hD => ?_)
  · exact LinearMap.congr_fun key δ
  change rotT RD k μ j (dotsU RD k (wt RD μ [dn j]) (up j) a ≫ plcL RD k (wt RD μ [dn j]) [] [up j] [] []
      (dg RD k (wt RD (wt RD μ [dn j]) [up j]) [] [] D)) =
    dotsU RD k μ (dn j) a ≫ plcL RD k μ [dn j] [] [] []
      (wtTransport RD k hμ (dg RD k (wt RD (wt RD μ [dn j]) [up j]) [] [] D))
  have e₀ : plcL RD k (wt RD μ [dn j]) [] [up j] [] []
      (dg RD k (wt RD (wt RD μ [dn j]) [up j]) [] [] D) =
      dg RD k (wt RD μ [dn j]) [up j] [up j] (D.map (whL [] [up j])) :=
    plcL_dg RD k (wt RD μ [dn j]) [] [up j] [] [] D
  have e₁ : plcL RD k μ [dn j] [] [] [] (dg RD k (wt RD μ []) [] [] D) =
      dg RD k μ [dn j] [dn j] (D.map (whL [dn j] [])) := plcL_dg RD k μ [dn j] [] [] [] D
  have hD₁ : SChain [up j] (D.map (whL [] [up j])) [up j] := by simpa using hD.whisk [] [up j]
  have hD₂ : SChain [dn j] (D.map (whL [dn j] [])) [dn j] := by simpa using hD.whisk [dn j] []
  have hrep : SChain [up j] (List.replicate a ([], .dot (up j), [])) [up j] :=
    SChain.replicate_of (by schain) a
  have hrep' : SChain [dn j] (List.replicate a ([], .dot (dn j), [])) [dn j] :=
    SChain.replicate_of (by schain) a
  rw [e₀, wtTransport_dg, e₁]
  rw [dotsU, dotsU, dg_comp hrep hD₁, dg_comp hrep' hD₂,
    rotT_dg RD k μ j _ (hrep.append hD₁)]
  wnf
  have e₂ := dg_closed_right (RD := RD) (k := k) μ (S := [dn j]) (T := [dn j])
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

theorem rotT_slideSetL {f : End ((pres RD k).obj (ob RD (wt RD μ [dn j]) [up j]))}
    (hf : f ∈ slideSetL RD k (wt RD μ [dn j]) (up j)) : rotT RD k μ j f ∈ slideSetR RD k μ (dn j) := by
  have : slideSetL RD k (wt RD μ [dn j]) (up j) ≤ (slideSetR RD k μ (dn j)).comap (rotT RD k μ j) := by
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
theorem bubLU_dn_mem (hSL : SimplyLaced C) (μ : X) (j : I)
    {β : End ((pres RD k).obj (ob RD (wt RD μ [dn j]) []))} (hβ : IsBub RD k (wt RD μ [dn j]) β) :
    bubLU RD k μ (dn j) β ∈ slideSetR RD k μ (dn j) := by
  rw [← rotT_bubRU]
  exact rotT_slideSetL RD k μ j (bubRU_up_mem hSL (wt RD μ [dn j]) j hβ)

/-- **Bubble slides across any strand, left to right** (KL III Propositions 3.3, 3.4, and their
rotations): every element of the image of `Π_{μ + l_X}` placed to the left of the strand `l`
lies in `slideSetR μ l`. -/
theorem bubLU_mem_slideSetR (hSL : SimplyLaced C) (μ : X) (l : Letter I)
    {β : End ((pres RD k).obj (ob RD (wt RD μ [l]) []))} (hβ : IsBub RD k (wt RD μ [l]) β) :
    bubLU RD k μ l β ∈ slideSetR RD k μ l := by
  obtain ⟨b, j⟩ := l
  cases b
  · exact bubLU_dn_mem hSL μ j hβ
  · exact bubLU_up_mem hSL μ j hβ

end Categorification.KL3.Diagram

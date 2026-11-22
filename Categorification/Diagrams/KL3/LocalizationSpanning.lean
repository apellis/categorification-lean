/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.Diagrams.KL3.LocalizationBend

/-!
# Webster's Lemma 3.29: the family `B′` spans the 2-morphisms of `U′`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, Lemma 3.29:
let `B′_{𝐢,𝐣}` be obtained from the spanning set `B_{𝐢,𝐣}` of KL III Proposition 3.11 by allowing
both positive and negative numbers of dots at the designated position on each strand; then
`B′_{𝐢,𝐣}` spans `Hom_{U′}(𝐢, 𝐣)`, where `U′` is the localization of `U` at the dots
(Definition 3.28, `presLoc`).

## The family `B′`

An element `y = (σ, e, m)` of the index set `LSpanIdx s t` is a pairing `σ` of the boundary word
`s* t`, an integer `e a` for each strand `a` of `σ`, and a bubble monomial `m`. The designated
position of a strand in `B_{𝐢,𝐣}` (`twoB`) is its left end in the one-sided diagram. The
element `oneBL y` of `B′_{∅, s* t}` is the canonical diagram of `σ` with `e a` dots at the left
end of the strand `a` when `e a ≥ 0` and `-e a` inverse dots there when `e a < 0`, followed by
the bubble monomial `m` on the far right; `twoBL y` is its bending (`bendLoc`). For `e ≥ 0`,
`twoBL y` is the image of the element `twoB` of `B_{s,t}` (`twoBL_of_nonneg`).

## Main results

* `dInv`: the inverse in `U′` of the dots at given positions.
* `oneBL`, `twoBL`: the families `B′_{∅,v}` and `B′_{s,t}`.
* `oneBL_cancel`: dots and inverse dots on the same strand cancel.
* `canonSpanLe_le_good`: by induction on the number of crossings, a canonical diagram followed
  by inverse dots at arbitrary positions is a combination of elements of `B′`.
* **`span_oneBL_eq_top`**, **`span_twoBL_eq_top`**: Webster's Lemma 3.29.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation
open StringDiagrams.Chord (Same Valid Lettered canon ofMatching lettersOf matchingOf)

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {k : Type w} [Field k]

/-! ## Inverse dots -/

section InvDots

open Classical in
variable (RD k) in
/-- **Inverse dots** in `U′`: the inverse of the dots at the positions `is` on the strands `v`
(`0` if a position is out of range). -/
def dInv (μ : X) (v : List (Letter I)) (is : List ℕ) :
    (toLoc RD k).obj ((pres RD k).obj (ob RD μ v)) ⟶ (toLoc RD k).obj ((pres RD k).obj (ob RD μ v)) :=
  if h : ∀ i ∈ is, i < v.length then
    @CategoryTheory.inv _ _ _ _ ((toLoc RD k).map (dD RD k μ v is)) (isIso_toLoc_dD μ v is h)
  else 0

theorem dInv_of (μ : X) {v : List (Letter I)} {is : List ℕ} (h : ∀ i ∈ is, i < v.length) :
    dInv RD k μ v is =
      @CategoryTheory.inv _ _ _ _ ((toLoc RD k).map (dD RD k μ v is)) (isIso_toLoc_dD μ v is h) := by
  classical
  rw [dInv, dite_eq_left h]

theorem dInv_of_not (μ : X) {v : List (Letter I)} {is : List ℕ} (h : ¬ ∀ i ∈ is, i < v.length) :
    dInv RD k μ v is = 0 := by
  classical
  rw [dInv, dite_eq_right h]

theorem toLoc_dD_comp_dInv (μ : X) {v : List (Letter I)} {is : List ℕ}
    (h : ∀ i ∈ is, i < v.length) :
    (toLoc RD k).map (dD RD k μ v is) ≫ dInv RD k μ v is = 𝟙 ((toLoc RD k).obj ((pres RD k).obj (ob RD μ v))) := by
  rw [dInv_of μ h]
  exact @IsIso.hom_inv_id _ _ _ _ _ (isIso_toLoc_dD μ v is h)

theorem dInv_comp_toLoc_dD (μ : X) {v : List (Letter I)} {is : List ℕ}
    (h : ∀ i ∈ is, i < v.length) :
    dInv RD k μ v is ≫ (toLoc RD k).map (dD RD k μ v is) =
      𝟙 ((toLoc RD k).obj ((pres RD k).obj (ob RD μ v))) := by
  rw [dInv_of μ h]
  exact @IsIso.inv_hom_id _ _ _ _ _ (isIso_toLoc_dD μ v is h)

theorem eq_dInv (μ : X) {v : List (Letter I)} {is : List ℕ} (h : ∀ i ∈ is, i < v.length)
    (Z : (toLoc RD k).obj ((pres RD k).obj (ob RD μ v)) ⟶
      (toLoc RD k).obj ((pres RD k).obj (ob RD μ v)))
    (hZ : (toLoc RD k).map (dD RD k μ v is) ≫ Z = 𝟙 ((toLoc RD k).obj ((pres RD k).obj (ob RD μ v)))) :
    dInv RD k μ v is = Z := by
  have e := toLoc_dD_comp_dInv (RD := RD) (k := k) μ h
  calc dInv RD k μ v is = dInv RD k μ v is ≫ ((toLoc RD k).map (dD RD k μ v is) ≫ Z) := by
        rw [hZ, Category.comp_id]
    _ = Z := by rw [← Category.assoc, dInv_comp_toLoc_dD μ h, Category.id_comp]

theorem dInv_nil (μ : X) (v : List (Letter I)) :
    dInv RD k μ v [] = 𝟙 ((toLoc RD k).obj ((pres RD k).obj (ob RD μ v))) := by
  refine eq_dInv μ (by simp) _ ?_
  rw [show dD RD k μ v [] = 𝟙 _ from dg_nil μ v, CategoryTheory.Functor.map_id,
    Category.comp_id]

theorem dInv_perm (μ : X) {v : List (Letter I)} {is js : List ℕ} (hp : is.Perm js)
    (h : ∀ i ∈ is, i < v.length) : dInv RD k μ v is = dInv RD k μ v js := by
  have hj : ∀ j ∈ js, j < v.length := fun j hj => h j (hp.mem_iff.2 hj)
  refine eq_dInv μ h _ ?_
  rw [dD_perm μ hp h]
  exact toLoc_dD_comp_dInv μ hj

theorem toLoc_dD_comp_dInv_comm (μ : X) {v : List (Letter I)} {is js : List ℕ}
    (hi : ∀ i ∈ is, i < v.length) (hj : ∀ j ∈ js, j < v.length) :
    (toLoc RD k).map (dD RD k μ v js) ≫ dInv RD k μ v is =
      dInv RD k μ v is ≫ (toLoc RD k).map (dD RD k μ v js) := by
  calc (toLoc RD k).map (dD RD k μ v js) ≫ dInv RD k μ v is
      = dInv RD k μ v is ≫ ((toLoc RD k).map (dD RD k μ v is) ≫
          (toLoc RD k).map (dD RD k μ v js)) ≫ dInv RD k μ v is := by
        rw [← Category.assoc, ← Category.assoc, dInv_comp_toLoc_dD μ hi, Category.id_comp]
    _ = dInv RD k μ v is ≫ (toLoc RD k).map (dD RD k μ v js) := by
        rw [toLoc_dD_comm μ hi hj, Category.assoc, toLoc_dD_comp_dInv μ hi, Category.comp_id]

theorem dInv_append (μ : X) {v : List (Letter I)} {is js : List ℕ}
    (hi : ∀ i ∈ is, i < v.length) (hj : ∀ j ∈ js, j < v.length) :
    dInv RD k μ v (is ++ js) = dInv RD k μ v is ≫ dInv RD k μ v js := by
  have hij : ∀ i ∈ is ++ js, i < v.length := by
    intro i h; rcases List.mem_append.1 h with h | h
    · exact hi i h
    · exact hj i h
  refine eq_dInv μ hij _ ?_
  rw [dD_append μ hi hj, Functor.map_comp, toLoc_dD_comm μ hi hj, Category.assoc,
    ← Category.assoc ((toLoc RD k).map (dD RD k μ v is)), toLoc_dD_comp_dInv μ hi,
    Category.id_comp, toLoc_dD_comp_dInv μ hj]

end InvDots

/-! ## Dots on the strands of a pairing -/

section ArcDots

omit [AddCommGroup X] [AddCommGroup Y] in
theorem arcDots_add {v : List (Letter I)} {σ : Equiv.Perm (Fin (ρW [] ++ v).length)}
    (p q : Arc [] v σ → ℕ) :
    (arcDots (p + q)).Perm (arcDots p ++ arcDots q) := by
  rw [List.perm_iff_count]
  intro n
  rw [List.count_append, count_dotList, count_dotList, count_dotList,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs <;> simp

omit [AddCommGroup X] [AddCommGroup Y] in
theorem arcDots_lt {v : List (Letter I)} {σ : Equiv.Perm (Fin (ρW [] ++ v).length)}
    (p : Arc [] v σ → ℕ) : ∀ i ∈ arcDots p, i < v.length := by
  intro i hi
  by_contra hlt
  have h0 : (arcDots p).count i = 0 := by
    rw [count_dotList]
    refine Finset.sum_eq_zero fun a _ => ite_eq_right_iff.2 fun h => absurd ?_ hlt
    rw [← h]
    exact a.1.2
  exact absurd h0 (List.count_pos_iff.2 hi).ne'

omit [AddCommGroup X] [AddCommGroup Y] in
/-- A list of positions on the strands of `σ`, each the left end of a strand, is a permutation of
the dot list of its multiplicities. -/
theorem perm_arcDots_count {v : List (Letter I)} {σ : Equiv.Perm (Fin (ρW [] ++ v).length)}
    {is : List ℕ} (hleft : ∀ i ∈ is, ∃ a : Arc [] v σ, a.1.val = i) :
    is.Perm (arcDots (v := v) (σ := σ) fun a => is.count a.1.val) := by
  rw [List.perm_iff_count]
  intro n
  rw [count_dotList]
  by_cases hn' : n ∈ is
  · obtain ⟨a₀, ha₀⟩ := hleft n hn'
    rw [Finset.sum_eq_single a₀ (fun b _ hb => ite_eq_right fun h => hb (Subtype.ext (Fin.ext
      (h.trans ha₀.symm)))) (fun h => absurd (Finset.mem_univ _) h), ite_eq_left ha₀, ha₀]
  · rw [List.count_eq_zero_of_not_mem hn']
    refine (Finset.sum_eq_zero fun a _ => ?_).symm
    split_ifs with h
    · rw [h]; exact List.count_eq_zero_of_not_mem hn'
    · rfl

omit [AddCommGroup X] [AddCommGroup Y] in
/-- **The pairing of a canonical chord state**: a valid lettered chord state `s` on `v` has the
canonical diagram of a pairing `σ` of `v`, and the left ends of the arcs of `s` are the left ends
of the strands of `σ`. -/
theorem exists_pairing {v : List (Letter I)} {s : List (ℕ × Letter I)}
    (hv : Valid s) (hl : Lettered Letter.dual s) (hsv : s.map Prod.snd = v) :
    ∃ σ : {σ // σ ∈ pairings [] v}, canon (pState σ.1) = canon s ∧
      ∀ i, i < s.length → (¬ ∃ j, j < i ∧ Same s i j) → ∃ a : Arc [] v σ.1, a.1.val = i := by
  have hn : s.length = (ρW [] ++ v).length := by
    show s.length = v.length
    rw [← hsv, List.length_map]
  set σ := matchingOf hv hn with hσdef
  have hL : lettersOf s hn = bwL v := by
    funext p
    have hp : p.val < (s.map Prod.snd).length := by rw [List.length_map, hn]; exact p.2
    show (s[p.val]'(by rw [hn]; exact p.2)).2 = v[p.val]'p.2
    have := List.getElem_of_eq hsv hp
    simp only [List.getElem_map] at this
    exact this
  have hσ : σ ∈ pairings [] v := by
    have := isMatching_lettersOf hv hl hn
    rw [hL] at this
    exact mem_matchings.2 this
  refine ⟨⟨σ, hσ⟩, ?_, ?_⟩
  · rw [← Chord.canon_ofMatching_matchingOf hv hn, hL]
  · intro i hi1 hi2
    refine ⟨⟨⟨i, by rw [← hn]; exact hi1⟩, ?_⟩, rfl⟩
    have hs := (Chord.same_iff_matchingOf hv hn ⟨i, by rw [← hn]; exact hi1⟩
      (σ ⟨i, by rw [← hn]; exact hi1⟩)).2 rfl
    rcases lt_or_gt_of_ne (show i ≠ (σ ⟨i, _⟩ : ℕ) from hs.1) with h | h
    · exact h
    · exact absurd ⟨_, h, hs⟩ hi2

end ArcDots

/-! ## Cancellation of dots and inverse dots -/

section Cancel

/-- Splitting a diagram before a chain. -/
theorem dg_append_of_right {ν : X} {s m t : List (Letter I)} {B : List (LayerData I)}
    (hB : SChain m B t) (A : List (LayerData I)) :
    dg RD k ν s t (A ++ B) = dg RD k ν s m A ≫ dg RD k ν m t B := by
  by_cases hA : SChain s A m
  · rw [dg_comp hA hB]
  · rw [dg_of_not hA, Limits.zero_comp, dg_of_not]
    intro h
    obtain ⟨m', h1, h2⟩ := SChain.split h
    rw [SChain.eq_source h2 hB] at h1
    exact hA h1

/-- Further dots at the end of a diagram ending with dots. -/
theorem dg_dotsL_append (ν : X) {v : List (Letter I)} {js ws : List ℕ}
    (hw : ∀ i ∈ ws, i < v.length) (P : List (LayerData I)) :
    dg RD k ν [] v (P ++ dotsL v (js ++ ws)) = dg RD k ν [] v (P ++ dotsL v js) ≫ dD RD k ν v ws := by
  rw [dotsL_append, ← List.append_assoc]
  exact dg_append_of_right (sChain_dotsL hw) _

variable (RD k) in
/-- A diagram `P` followed by dots at `js`, the bubbles `β` on the far right and inverse dots
at `ls`, in `U′`. -/
def dotX (μ : X) (v : List (Letter I)) (P : List (LayerData I))
    (β : End ((pres RD k).obj (ob RD μ []))) (js ls : List ℕ) :
    (toLoc RD k).obj ((pres RD k).obj (ob RD μ [])) ⟶
      (toLoc RD k).obj ((pres RD k).obj (ob RD μ v)) :=
  (toLoc RD k).map (dg RD k μ [] v (P ++ dotsL v js) ≫ bubAt RD k μ v β) ≫ dInv RD k μ v ls

/-- A dot and an inverse dot on the same strand cancel. -/
theorem dotX_cancel (μ : X) {v : List (Letter I)} (P : List (LayerData I))
    (β : End ((pres RD k).obj (ob RD μ []))) {js ls ws : List ℕ}
    (hl : ∀ i ∈ ls, i < v.length) (hw : ∀ i ∈ ws, i < v.length) :
    dotX RD k μ v P β (js ++ ws) (ls ++ ws) = dotX RD k μ v P β js ls := by
  simp only [dotX]
  rw [dg_dotsL_append μ hw, Category.assoc, ← bubAt_comm RD k μ β, ← Category.assoc,
    Functor.map_comp, dInv_append μ hl hw, Category.assoc, ← Category.assoc _ (dInv _ _ _ _ _),
    toLoc_dD_comp_dInv_comm μ hl hw, Category.assoc, toLoc_dD_comp_dInv μ hw, Category.comp_id]

/-- Dots and inverse dots on distinct strands commute. -/
theorem dotX_perm (μ : X) {v : List (Letter I)} (P : List (LayerData I))
    (β : End ((pres RD k).obj (ob RD μ []))) {js js' ls ls' : List ℕ}
    (hj : js.Perm js') (hl : ls.Perm ls') (hjb : ∀ i ∈ js, i < v.length)
    (hlb : ∀ i ∈ ls, i < v.length) :
    dotX RD k μ v P β js ls = dotX RD k μ v P β js' ls' := by
  simp only [dotX]
  have e := dotsL_perm (RD := RD) (k := k) (t := v) hj hjb P [] μ [] v
  simp only [List.append_nil] at e
  rw [e, dInv_perm μ hl hlb]

theorem dotX_zero (μ : X) (v : List (Letter I)) (P : List (LayerData I)) (js ls : List ℕ) :
    dotX RD k μ v P 0 js ls = 0 := by
  simp only [dotX, map_zero, Limits.comp_zero, Functor.map_zero, Limits.zero_comp]

theorem dotX_add (μ : X) (v : List (Letter I)) (P : List (LayerData I))
    (β γ : End ((pres RD k).obj (ob RD μ []))) (js ls : List ℕ) :
    dotX RD k μ v P (β + γ) js ls = dotX RD k μ v P β js ls + dotX RD k μ v P γ js ls := by
  simp only [dotX, map_add]
  erw [Preadditive.comp_add]
  rw [Functor.map_add, Preadditive.add_comp]

theorem dotX_smul (μ : X) (v : List (Letter I)) (P : List (LayerData I)) (r : k)
    (β : End ((pres RD k).obj (ob RD μ []))) (js ls : List ℕ) :
    dotX RD k μ v P (r • β) js ls = r • dotX RD k μ v P β js ls := by
  simp only [dotX, map_smul]
  erw [Linear.comp_smul]
  rw [Functor.map_smul, Linear.smul_comp]

end Cancel

/-! ## The family `B′` -/

section Family

/-- **The index set of `B′_{𝐢,𝐣}`** (Webster arXiv:1309.3796v2, Lemma 3.29): a pairing `D` of
`(𝐢, 𝐣)`, an integer number of dots on each strand of `D`, and a monomial in the generators of
`Π_λ`. -/
def LSpanIdx (s t : List (Bool × I)) : Type u :=
  Σ σ : {σ // σ ∈ pairings s t}, (Arc s t σ.1 → ℤ) × ((I × ℕ) →₀ ℕ)

/-- The `(s, t)`-pairings are the pairings of the one-sided word `s* t` (definitionally). -/
def lIdx {s t : List (Letter I)} (y : LSpanIdx s t) : LSpanIdx [] (rd s ++ t) := y

variable (RD k) in
/-- **The element of `B′_{∅,v}` indexed by `y = (σ, e, m)`** (Webster arXiv:1309.3796v2,
Lemma 3.29): the canonical diagram of the pairing `σ`, with `e a` dots (if `e a ≥ 0`) or `-e a`
inverse dots (if `e a < 0`) at the left end of each strand `a`, followed by the bubble monomial
`m` on the far right. -/
def oneBL (μ : X) (v : List (Letter I)) (y : LSpanIdx [] v) :
    (presLoc RD k).obj ((incl RD).obj (ob RD μ [])) ⟶
      (presLoc RD k).obj ((incl RD).obj (ob RD μ v)) :=
  dotX RD k μ v (chL [] (canon (pState y.1.1))) (bubMon RD k μ y.2.2)
    (arcDots fun a => (y.2.1 a).toNat) (arcDots fun a => (-y.2.1 a).toNat)

variable (RD k) in
/-- **The element of `B′_{s,t}` indexed by `y`** (Webster arXiv:1309.3796v2, Lemma 3.29): the
element of `B′_{∅, s* t}` with the same index, its lower endpoints bent back down. -/
def twoBL (μ : X) (s t : List (Letter I)) (y : LSpanIdx s t) :
    (presLoc RD k).obj ((incl RD).obj (ob RD μ s)) ⟶
      (presLoc RD k).obj ((incl RD).obj (ob RD μ t)) :=
  bendLoc RD k μ s t (oneBL RD k μ (rd s ++ t) (lIdx y))

omit [AddCommGroup X] [AddCommGroup Y] in
theorem arcDots_zero {v : List (Letter I)} {σ : Equiv.Perm (Fin (ρW [] ++ v).length)} :
    arcDots (v := v) (σ := σ) (fun _ => 0) = [] := by
  simp [dotList]

/-- **`B′` contains `B`**: with nonnegative exponents, the element of `B′_{∅,v}` is the image of
the element of `B_{∅,v}` with the same index. -/
theorem oneBL_of_nonneg (μ : X) (v : List (Letter I)) (x : SpanIdx [] v) :
    oneBL RD k μ v ⟨x.1, fun a => (x.2.1 a : ℤ), x.2.2⟩ = (toLoc RD k).map (oneB RD k μ v x) := by
  have e1 : (fun a : Arc [] v x.1.1 => ((x.2.1 a : ℤ)).toNat) = x.2.1 := funext fun a => by simp
  have e2 : (fun a : Arc [] v x.1.1 => (-(x.2.1 a : ℤ)).toNat) = fun _ => 0 :=
    funext fun a => by omega
  simp only [oneBL, dotX, e1, e2, arcDots_zero, dInv_nil, Category.comp_id]
  rfl

/-- **`B′` contains `B`**: with nonnegative exponents, the element of `B′_{s,t}` is the image of
the element `twoB` of `B_{s,t}` with the same index. -/
theorem twoBL_of_nonneg (μ : X) (s t : List (Letter I)) (x : SpanIdx s t) :
    twoBL RD k μ s t ⟨x.1, fun a => (x.2.1 a : ℤ), x.2.2⟩ = (toLoc RD k).map (twoB RD k μ s t x) := by
  rw [twoBL, twoB, ← bendLoc_toLoc]
  exact congrArg (bendLoc RD k μ s t) (oneBL_of_nonneg μ (rd s ++ t) (oneIdx x))

/-- Dots and inverse dots on the strands of a pairing reduce to an element of `B′`. -/
theorem dotX_eq_oneBL (μ : X) {v : List (Letter I)} (σ : {σ // σ ∈ pairings [] v})
    (m : (I × ℕ) →₀ ℕ) (p q : Arc [] v σ.1 → ℕ) :
    dotX RD k μ v (chL [] (canon (pState σ.1))) (bubMon RD k μ m) (arcDots p) (arcDots q) =
      oneBL RD k μ v ⟨σ, fun a => (p a : ℤ) - q a, m⟩ := by
  have key : ∀ (e₁ e₂ w p q : Arc [] v σ.1 → ℕ), p = e₁ + w → q = e₂ + w →
      dotX RD k μ v (chL [] (canon (pState σ.1))) (bubMon RD k μ m) (arcDots p) (arcDots q) =
        dotX RD k μ v (chL [] (canon (pState σ.1))) (bubMon RD k μ m) (arcDots e₁)
          (arcDots e₂) := by
    intro e₁ e₂ w p q hp hq
    subst hp hq
    rw [dotX_perm μ _ _ (arcDots_add e₁ w) (arcDots_add e₂ w) (arcDots_lt _) (arcDots_lt _),
      dotX_cancel μ _ _ (arcDots_lt _) (arcDots_lt _)]
  refine key _ _ (fun a => min (p a) (q a)) p q (funext fun a => ?_) (funext fun a => ?_)
  · simp only [Pi.add_apply]; omega
  · simp only [Pi.add_apply]; omega

end Family

/-! ## Spanning -/

section Span

variable [DecidableEq I]

variable (RD k) in
/-- The span of `B′_{∅,v}`. -/
abbrev spanL (μ : X) (v : List (Letter I)) :
    Submodule k ((presLoc RD k).obj ((incl RD).obj (ob RD μ [])) ⟶
      (presLoc RD k).obj ((incl RD).obj (ob RD μ v))) :=
  Submodule.span k (Set.range (oneBL RD k μ v))

variable (RD k) in
/-- The 2-morphisms `g` of `U` such that `g` followed by inverse dots at arbitrary positions is a
combination of elements of `B′`. -/
def good (μ : X) (v : List (Letter I)) :
    Submodule k ((pres RD k).obj (ob RD μ []) ⟶ (pres RD k).obj (ob RD μ v)) where
  carrier := {g | ∀ ls : List ℕ, (toLoc RD k).map g ≫ dInv RD k μ v ls ∈ spanL RD k μ v}
  zero_mem' := fun ls => by
    rw [Functor.map_zero, Limits.zero_comp]; exact Submodule.zero_mem _
  add_mem' := fun ha hb ls => by
    rw [Functor.map_add, Preadditive.add_comp]; exact Submodule.add_mem _ (ha ls) (hb ls)
  smul_mem' := fun r g hg ls => by
    rw [Functor.map_smul, Linear.smul_comp]; exact Submodule.smul_mem _ r (hg ls)

omit [DecidableEq I] in
theorem bnd_of_left {v : List (Letter I)} {s : List (ℕ × Letter I)} (hsv : s.map Prod.snd = v)
    {is : List ℕ} (his : ∀ i ∈ is, i < s.length ∧ ¬ ∃ j, j < i ∧ Same s i j) :
    ∀ i ∈ is, i < v.length := fun i hi => by
  rw [← hsv, List.length_map]; exact (his i hi).1

omit [DecidableEq I] in
/-- **The base case**: a canonical diagram with dots and inverse dots at the left ends of its
arcs, followed by an element of the image of `Π_μ`, is a combination of elements of `B′`. -/
theorem dotX_left_mem (μ : X) {v : List (Letter I)} {s : List (ℕ × Letter I)}
    (hv : Valid s) (hl : Lettered Letter.dual s) (hsv : s.map Prod.snd = v) {js ls : List ℕ}
    (hjs : ∀ i ∈ js, i < s.length ∧ ¬ ∃ j, j < i ∧ Same s i j)
    (hls : ∀ i ∈ ls, i < s.length ∧ ¬ ∃ j, j < i ∧ Same s i j)
    {β : End ((pres RD k).obj (ob RD μ []))} (hβ : IsBub RD k μ β) :
    dotX RD k μ v (chL [] (canon s)) β js ls ∈ spanL RD k μ v := by
  obtain ⟨σ, hcanon, hleft⟩ := exists_pairing hv hl hsv
  have hmem := isBub_mem_span hβ
  clear hβ
  induction hmem using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    have hj := perm_arcDots_count (σ := σ.1) fun i hi => hleft i (hjs i hi).1 (hjs i hi).2
    have hl' := perm_arcDots_count (σ := σ.1) fun i hi => hleft i (hls i hi).1 (hls i hi).2
    rw [← hcanon, dotX_perm μ _ _ hj hl' (bnd_of_left hsv hjs) (bnd_of_left hsv hls),
      dotX_eq_oneBL]
    exact Submodule.subset_span ⟨_, rfl⟩
  | zero => rw [dotX_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [dotX_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [dotX_smul]; exact Submodule.smul_mem _ r hx

/-- **A dot moves to the left end of its arc**, modulo diagrams with fewer crossings, also in the
presence of dots at the left ends and of bubbles. -/
theorem dot_lEnd_sub_mem (μ : X) {s : List (ℕ × Letter I)} (hv : Valid s)
    (hl : Lettered Letter.dual s) {js : List ℕ} (hjs : ∀ i ∈ js, i < s.length)
    {β : End ((pres RD k).obj (ob RD μ []))} (hβ : IsBub RD k μ β) {p : ℕ} (hp : p < s.length) :
    (dg RD k μ [] (s.map Prod.snd) (chL [] (canon s) ++ dotsL (s.map Prod.snd) js) ≫
        bubAt RD k μ (s.map Prod.snd) β) ≫ dD RD k μ (s.map Prod.snd) [p] -
      (dg RD k μ [] (s.map Prod.snd) (chL [] (canon s) ++ dotsL (s.map Prod.snd) js) ≫
        bubAt RD k μ (s.map Prod.snd) β) ≫ dD RD k μ (s.map Prod.snd) [lEnd s p] ∈
      Lo RD k μ [] (s.map Prod.snd) (ncr (canon s)) := by
  have hjs' : ∀ i ∈ js, i < (s.map Prod.snd).length := by simpa using hjs
  have e : ∀ x, x < s.length →
      (dg RD k μ [] (s.map Prod.snd) (chL [] (canon s) ++ dotsL (s.map Prod.snd) js) ≫
        bubAt RD k μ (s.map Prod.snd) β) ≫ dD RD k μ (s.map Prod.snd) [x] =
      dg RD k μ [] (s.map Prod.snd)
        (chL [] (canon s) ++ dotsL (s.map Prod.snd) [x] ++ dotsL (s.map Prod.snd) js) ≫
        bubAt RD k μ (s.map Prod.snd) β := by
    intro x hx
    have hx' : ∀ i ∈ [x], i < (s.map Prod.snd).length := by simpa using hx
    rw [Category.assoc, bubAt_comm RD k μ β, ← Category.assoc, ← dg_dotsL_append μ hx']
    have := dotsL_perm (RD := RD) (k := k) (t := s.map Prod.snd) (List.perm_append_comm
      (l₁ := js) (l₂ := [x])) (by
        intro i h; rcases List.mem_append.1 h with h | h
        · exact hjs' i h
        · exact hx' i h) (chL [] (canon s)) [] μ [] (s.map Prod.snd)
    simp only [List.append_nil] at this
    rw [this, dotsL_append, List.append_assoc]
  rw [e p hp, e _ (lEnd_lt hp), ← Preadditive.sub_comp]
  refine lo_comp_bubAt_mem_of ?_ hβ
  have := dots_left (RD := RD) (k := k) μ hv hl [p] (by simpa using hp)
    (dotsL (s.map Prod.snd) js) (s.map Prod.snd)
  simpa using this

omit [DecidableEq I] in
/-- An inverse dot moves to another strand, modulo the difference of the dots on the two strands. -/
theorem toLoc_comp_dInv_move (μ : X) {V : List (Letter I)} {p ℓ : ℕ} (hp : p < V.length)
    (hℓ : ℓ < V.length) (g : (pres RD k).obj (ob RD μ []) ⟶ (pres RD k).obj (ob RD μ V)) :
    (toLoc RD k).map g ≫ dInv RD k μ V [p] = (toLoc RD k).map g ≫ dInv RD k μ V [ℓ] -
      (toLoc RD k).map (g ≫ dD RD k μ V [p] - g ≫ dD RD k μ V [ℓ]) ≫
        dInv RD k μ V [p] ≫ dInv RD k μ V [ℓ] := by
  have hp' : ∀ i ∈ [p], i < V.length := by simpa using hp
  have hℓ' : ∀ i ∈ [ℓ], i < V.length := by simpa using hℓ
  rw [Functor.map_sub, Functor.map_comp, Functor.map_comp, Preadditive.sub_comp,
    Category.assoc, Category.assoc, ← Category.assoc ((toLoc RD k).map (dD RD k μ V [p])),
    toLoc_dD_comp_dInv μ hp', Category.id_comp,
    ← Category.assoc ((toLoc RD k).map (dD RD k μ V [ℓ])), toLoc_dD_comp_dInv_comm μ hp' hℓ',
    Category.assoc, toLoc_dD_comp_dInv μ hℓ', Category.comp_id, sub_sub_cancel]

/-- **Inverse dots at arbitrary positions**: a canonical diagram with dots at the left ends of its
arcs and bubbles, followed by inverse dots at arbitrary positions, is a combination of elements of
`B′`, provided the diagrams with fewer crossings are. -/
theorem dotX_mem (μ : X) {s : List (ℕ × Letter I)} (hv : Valid s) (hl : Lettered Letter.dual s)
    {js : List ℕ} (hjs : ∀ i ∈ js, i < s.length ∧ ¬ ∃ j, j < i ∧ Same s i j)
    {β : End ((pres RD k).obj (ob RD μ []))} (hβ : IsBub RD k μ β)
    (hLo : ∀ L ∈ Lo RD k μ [] (s.map Prod.snd) (ncr (canon s)), L ∈ good RD k μ (s.map Prod.snd)) :
    ∀ (is ls : List ℕ), (∀ i ∈ ls, i < s.length ∧ ¬ ∃ j, j < i ∧ Same s i j) →
      dotX RD k μ (s.map Prod.snd) (chL [] (canon s)) β js (ls ++ is) ∈
        spanL RD k μ (s.map Prod.snd) := by
  intro is
  induction is with
  | nil =>
    intro ls hls
    rw [List.append_nil]
    exact dotX_left_mem μ hv hl rfl hjs hls hβ
  | cons p is ih =>
    intro ls hls
    by_cases hb : ∀ i ∈ ls ++ p :: is, i < (s.map Prod.snd).length
    swap
    · rw [dotX, dInv_of_not μ hb, Limits.comp_zero]
      exact Submodule.zero_mem _
    have hp : p < s.length := by simpa using hb p (by simp)
    by_cases hpl : ¬ ∃ j, j < p ∧ Same s p j
    · have := ih (ls ++ [p]) (by
        intro i hi
        rcases List.mem_append.1 hi with h | h
        · exact hls i h
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          subst h
          exact ⟨hp, hpl⟩)
      simpa using this
    have hℓ : lEnd s p < s.length := lEnd_lt hp
    have hV : (s.map Prod.snd).length = s.length := List.length_map _
    have hrest : ∀ i ∈ ls ++ is, i < (s.map Prod.snd).length := by
      intro i hi
      exact hb i (List.perm_middle.symm.subset (List.mem_cons_of_mem _ hi))
    have hpV : ∀ i ∈ [p], i < (s.map Prod.snd).length := by simpa using hp
    have hℓV : ∀ i ∈ [lEnd s p], i < (s.map Prod.snd).length := by simpa using hℓ
    have hpℓV : ∀ i ∈ [p] ++ [lEnd s p], i < (s.map Prod.snd).length := by
      intro i hi; simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hi
      rcases hi with rfl | rfl
      · rw [hV]; exact hp
      · rw [hV]; exact hℓ
    have h1 : dInv RD k μ (s.map Prod.snd) (ls ++ p :: is) =
        dInv RD k μ (s.map Prod.snd) [p] ≫ dInv RD k μ (s.map Prod.snd) (ls ++ is) := by
      rw [dInv_perm μ List.perm_middle hb]
      exact dInv_append μ hpV hrest
    have hb2 : ∀ i ∈ ls ++ lEnd s p :: is, i < (s.map Prod.snd).length := by
      intro i hi
      rcases List.mem_cons.1 (List.perm_middle.subset hi) with rfl | hi
      · rw [hV]; exact hℓ
      · exact hrest i hi
    have h2 : dInv RD k μ (s.map Prod.snd) (ls ++ [lEnd s p] ++ is) =
        dInv RD k μ (s.map Prod.snd) [lEnd s p] ≫ dInv RD k μ (s.map Prod.snd) (ls ++ is) := by
      rw [List.append_assoc, List.singleton_append, dInv_perm μ List.perm_middle hb2]
      exact dInv_append μ hℓV hrest
    have h3 : dInv RD k μ (s.map Prod.snd) ([p] ++ [lEnd s p] ++ (ls ++ is)) =
        dInv RD k μ (s.map Prod.snd) [p] ≫ dInv RD k μ (s.map Prod.snd) [lEnd s p] ≫
          dInv RD k μ (s.map Prod.snd) (ls ++ is) := by
      rw [dInv_append μ hpℓV hrest, dInv_append μ hpV hℓV, Category.assoc]
    have hL := dot_lEnd_sub_mem (RD := RD) (k := k) μ hv hl (fun i hi => (hjs i hi).1) hβ hp
    have key := ih (ls ++ [lEnd s p]) (by
        intro i hi
        rcases List.mem_append.1 hi with h | h
        · exact hls i h
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          subst h
          exact ⟨hℓ, lEnd_isLeft hv p⟩)
    have hLg := hLo _ hL ([p] ++ [lEnd s p] ++ (ls ++ is))
    rw [h3] at hLg
    rw [dotX, h2] at key
    rw [dotX, h1, ← Category.assoc, toLoc_comp_dInv_move μ (by rw [hV]; exact hp)
      (by rw [hV]; exact hℓ), Preadditive.sub_comp]
    simp only [Category.assoc] at key hLg ⊢
    exact Submodule.sub_mem _ key hLg

/-- **Canonical diagrams with at most `c` crossings** are good: followed by inverse dots at
arbitrary positions, they are combinations of elements of `B′`. -/
theorem canonSpanLe_le_good (μ : X) (v : List (Letter I)) :
    ∀ c, canonSpanLe RD k μ v c ≤ good RD k μ v := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
  rw [canonSpanLe, Submodule.span_le]
  rintro _ ⟨s, js, β, hv, hl, hsv, hjs, hβ, hc, rfl⟩
  subst hsv
  have hLo : ∀ L ∈ Lo RD k μ [] (s.map Prod.snd) (ncr (canon s)),
      L ∈ good RD k μ (s.map Prod.snd) := by
    intro L hL
    cases hn : ncr (canon s) with
    | zero =>
      rw [hn, lo_zero (RD := RD) (k := k) μ [] (s.map Prod.snd), Submodule.mem_bot] at hL
      rw [hL]
      exact Submodule.zero_mem _
    | succ n =>
      rw [hn] at hL
      exact ih n (by omega) (lo_le_canonSpanLe μ _ n hL)
  intro ls
  have := dotX_mem μ hv hl hjs hβ hLo ls [] (by simp)
  rw [List.nil_append] at this
  exact this

/-- Every 2-morphism `1_μ ⟶ E_v 1_μ` of `U′` is a combination of elements of `B′_{∅,v}`. -/
theorem mem_spanL (μ : X) (v : List (Letter I))
    (F : (presLoc RD k).obj ((incl RD).obj (ob RD μ [])) ⟶
      (presLoc RD k).obj ((incl RD).obj (ob RD μ v))) : F ∈ spanL RD k μ v := by
  obtain ⟨is, his, g, e⟩ := mem_coreSet μ v F
  have hF : F = (toLoc RD k).map g ≫ dInv RD k μ v is := by
    rw [← e, Category.assoc, toLoc_dD_comp_dInv μ his]
    exact (Category.comp_id F).symm
  have hg : g ∈ good RD k μ v := by
    refine (show CanonSpan RD k μ v ≤ good RD k μ v from ?_) (mem_canonSpan μ v g)
    rw [CanonSpan, Submodule.span_le]
    rintro _ ⟨s, js, β, hv, hl, hsv, hjs, hβ, rfl⟩
    exact canonSpanLe_le_good μ v (ncr (canon s))
      (Submodule.subset_span ⟨s, js, β, hv, hl, hsv, hjs, hβ, le_rfl, rfl⟩)
  rw [hF]
  exact hg is

/-- **Webster's Lemma 3.29 for one-sided boundary words** (Webster arXiv:1309.3796v2,
Lemma 3.29): the elements of `B′_{∅,v}` span the 2-morphisms `1_μ ⟶ E_v 1_μ` of `U′`. -/
theorem span_oneBL_eq_top (μ : X) (v : List (Letter I)) :
    Submodule.span k (Set.range (oneBL RD k μ v)) = ⊤ :=
  eq_top_iff.2 fun F _ => mem_spanL μ v F

/-- **Webster's Lemma 3.29** (B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v2, Lemma 3.29; any Cartan datum): the set `B′_{s,t}`, obtained from the spanning
set `B_{s,t}` of KL III Proposition 3.11 (`twoB`) by allowing both positive and negative numbers
of dots at the designated position on each strand, spans `Hom_{U′}(E_s 1_μ, E_t 1_μ)`, where
`U′` is the localization of `U` at the dots (Definition 3.28). -/
theorem span_twoBL_eq_top (μ : X) (s t : List (Letter I)) :
    Submodule.span k (Set.range (twoBL RD k μ s t)) = ⊤ := by
  refine eq_top_iff.2 fun f _ => ?_
  obtain ⟨F, rfl⟩ := exists_bendLoc_eq RD k μ s t f
  have h := Submodule.mem_map_of_mem (f := bendLoc RD k μ s t) (mem_spanL μ (rd s ++ t) F)
  rw [Submodule.map_span, ← Set.range_comp] at h
  exact h

end Span

end Categorification.KL3.Diagram

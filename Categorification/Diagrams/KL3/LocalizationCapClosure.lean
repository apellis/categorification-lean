/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.Diagrams.KL3.LocalizationCap

/-!
# Core morphisms of `U′` are closed under caps

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, proof of
Lemma 3.29. For a cap `E_{l^∨} E_l → 1` between the strands `u` and `v`, let `D` be the position
of its downward strand. A 2-morphism `g : 1_μ → E_s 1_μ` of `U` is *cap-good* if, for every `n`,
the morphism `g x_D^{-n}` of `U′` followed by the cap is a core morphism. Cap-good morphisms form
a submodule closed under dots and bubbles, and containing every morphism that factors through
a cup at the cap's position (a negative bubble).

## Main results

* `capSet`: the cap-good 2-morphisms.
* `capSet_comp_dD`, `capSet_comp_bubAt`, `comp_cup_mem_capSet`: closure properties.
* `mem_capSet_of_arc`: a morphism on which a dot on `D` equals, modulo cap-good morphisms, a dot
  on a strand away from the cap is cap-good.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {k : Type w} [CommRing k]

/-- The position of the downward strand of the cap between `u` and `v`. -/
abbrev capPos (u : List (Letter I)) (l : Letter I) : ℕ := u.length + capDn l

theorem capPos_lt (u v : List (Letter I)) (l : Letter I) :
    capPos u l < (u ++ [l.dual, l] ++ v).length := by
  have := capDn_lt l; simp; omega

theorem replicate_capPos_lt (u v : List (Letter I)) (l : Letter I) (n : ℕ) :
    ∀ q ∈ List.replicate n (capPos u l), q < (u ++ [l.dual, l] ++ v).length := by
  intro q hq; rw [List.eq_of_mem_replicate hq]; exact capPos_lt u v l

/-- The dots `x_D^n` on the downward strand of the cap. -/
abbrev capDots (μ : X) (u v : List (Letter I)) (l : Letter I) (n : ℕ) :
    (presLoc RD k).obj ((incl RD).obj (ob RD μ (u ++ [l.dual, l] ++ v))) ⟶
      (presLoc RD k).obj ((incl RD).obj (ob RD μ (u ++ [l.dual, l] ++ v))) :=
  (toLoc RD k).map (dD RD k μ (u ++ [l.dual, l] ++ v) (List.replicate n (capPos u l)))

theorem isIso_capDots (μ : X) (u v : List (Letter I)) (l : Letter I) (n : ℕ) :
    IsIso (capDots (RD := RD) (k := k) μ u v l n) :=
  isIso_toLoc_dD μ _ _ (replicate_capPos_lt u v l n)

theorem capDots_cancel (μ : X) (u v : List (Letter I)) (l : Letter I) (n : ℕ)
    {Y Z : (presLoc RD k).obj ((incl RD).obj (ob RD μ [])) ⟶
      (presLoc RD k).obj ((incl RD).obj (ob RD μ (u ++ [l.dual, l] ++ v)))}
    (h : Y ≫ capDots μ u v l n = Z ≫ capDots μ u v l n) : Y = Z := by
  have := isIso_capDots (RD := RD) (k := k) μ u v l n
  exact (cancel_mono _).1 h

theorem exists_comp_capDots (μ : X) (u v : List (Letter I)) (l : Letter I) (n : ℕ)
    (W : (presLoc RD k).obj ((incl RD).obj (ob RD μ [])) ⟶
      (presLoc RD k).obj ((incl RD).obj (ob RD μ (u ++ [l.dual, l] ++ v)))) :
    ∃ Y, Y ≫ capDots (RD := RD) (k := k) μ u v l n = W := by
  have := isIso_capDots (RD := RD) (k := k) μ u v l n
  exact ⟨W ≫ CategoryTheory.inv (capDots μ u v l n),
    by rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]⟩

theorem toLoc_dD_comm (μ : X) {s : List (Letter I)} {is js : List ℕ}
    (hi : ∀ i ∈ is, i < s.length) (hj : ∀ j ∈ js, j < s.length) :
    (toLoc RD k).map (dD RD k μ s is) ≫ (toLoc RD k).map (dD RD k μ s js) =
      (toLoc RD k).map (dD RD k μ s js) ≫ (toLoc RD k).map (dD RD k μ s is) := by
  rw [← Functor.map_comp, ← Functor.map_comp, dD_comm μ hi hj]

theorem dD_single_lt {s : List (Letter I)} {q : ℕ} (hq : q < s.length) :
    ∀ i ∈ [q], i < s.length := by
  intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; subst hi; exact hq

variable (RD k) in
/-- **Cap-good 2-morphisms** of `U` (Webster arXiv:1309.3796v2, proof of Lemma 3.29): those
`g : 1_μ → E_s 1_μ`, `s = u l^∨ l v`, such that for every `n` the morphism `g x_D^{-n}` of `U′`,
followed by the cap, is a core morphism. -/
def capSet (μ : X) (u v : List (Letter I)) (l : Letter I) :
    Submodule k ((pres RD k).obj (ob RD μ []) ⟶ (pres RD k).obj (ob RD μ (u ++ [l.dual, l] ++ v)))
    where
  carrier := {g | ∀ (n : ℕ) (Y : (presLoc RD k).obj ((incl RD).obj (ob RD μ [])) ⟶
      (presLoc RD k).obj ((incl RD).obj (ob RD μ (u ++ [l.dual, l] ++ v)))),
      Y ≫ capDots μ u v l n = (toLoc RD k).map g →
        Y ≫ (toLoc RD k).map (cp μ u v l) ∈ coreSet RD k μ (u ++ [] ++ v)}
  zero_mem' := by
    intro n Y hY
    have : Y = 0 := capDots_cancel μ u v l n (by rw [hY, Functor.map_zero, Limits.zero_comp])
    rw [this, Limits.zero_comp]
    exact Submodule.zero_mem _
  add_mem' := by
    intro g₁ g₂ h₁ h₂ n Y hY
    obtain ⟨Y₁, e₁⟩ := exists_comp_capDots (RD := RD) (k := k) μ u v l n ((toLoc RD k).map g₁)
    obtain ⟨Y₂, e₂⟩ := exists_comp_capDots (RD := RD) (k := k) μ u v l n ((toLoc RD k).map g₂)
    have : Y = Y₁ + Y₂ := capDots_cancel μ u v l n
      (by rw [hY, Preadditive.add_comp, e₁, e₂, Functor.map_add])
    rw [this, Preadditive.add_comp]
    exact Submodule.add_mem _ (h₁ n Y₁ e₁) (h₂ n Y₂ e₂)
  smul_mem' := by
    intro c g h n Y hY
    obtain ⟨Y₁, e₁⟩ := exists_comp_capDots (RD := RD) (k := k) μ u v l n ((toLoc RD k).map g)
    have : Y = c • Y₁ := capDots_cancel μ u v l n
      (by rw [hY, Linear.smul_comp, e₁, Functor.map_smul])
    rw [this, Linear.smul_comp]
    exact Submodule.smul_mem _ c (h n Y₁ e₁)

theorem capDots_zero (μ : X) (u v : List (Letter I)) (l : Letter I) :
    capDots (RD := RD) (k := k) μ u v l 0 = 𝟙 _ := by
  rw [capDots, List.replicate_zero, show dD RD k μ (u ++ [l.dual, l] ++ v) [] = 𝟙 _ from
    dg_nil μ _]
  exact (toLoc RD k).map_id _

theorem capDots_succ (μ : X) (u v : List (Letter I)) (l : Letter I) (n : ℕ) :
    capDots (RD := RD) (k := k) μ u v l (n + 1) =
      capDots μ u v l n ≫ (toLoc RD k).map (dD RD k μ (u ++ [l.dual, l] ++ v) [capPos u l]) := by
  rw [capDots, List.replicate_succ', dD_append μ (replicate_capPos_lt u v l n)
    (dD_single_lt (capPos_lt u v l)), Functor.map_comp]

/-- With no inverse dots, every morphism closes up with the cap to a core morphism. -/
theorem capDots_zero_comp_cap (μ : X) (u v : List (Letter I)) (l : Letter I)
    (g : (pres RD k).obj (ob RD μ []) ⟶ (pres RD k).obj (ob RD μ (u ++ [l.dual, l] ++ v)))
    {Y : (presLoc RD k).obj ((incl RD).obj (ob RD μ [])) ⟶
      (presLoc RD k).obj ((incl RD).obj (ob RD μ (u ++ [l.dual, l] ++ v)))}
    (hY : Y ≫ capDots μ u v l 0 = (toLoc RD k).map g) :
    Y ≫ (toLoc RD k).map (cp μ u v l) ∈ coreSet RD k μ (u ++ [] ++ v) := by
  rw [capDots_zero, Category.comp_id] at hY
  rw [hY, ← Functor.map_comp]
  exact toLoc_mem_coreSet μ _ _

/-- Cap-good morphisms are closed under a dot on the downward strand of the cap. -/
theorem capSet_comp_dD_capPos (μ : X) (u v : List (Letter I)) (l : Letter I) {g}
    (hg : g ∈ capSet RD k μ u v l) :
    g ≫ dD RD k μ (u ++ [l.dual, l] ++ v) [capPos u l] ∈ capSet RD k μ u v l := by
  intro n Y hY
  cases n with
  | zero => exact capDots_zero_comp_cap μ u v l _ hY
  | succ m =>
    have := isIso_toLoc_dD_single (RD := RD) (k := k) μ (capPos_lt u v l)
    refine hg m Y ((cancel_mono ((toLoc RD k).map
      (dD RD k μ (u ++ [l.dual, l] ++ v) [capPos u l]))).1 ?_)
    rw [Category.assoc, ← capDots_succ, hY, Functor.map_comp]

theorem comp_dD_comp_capDots (μ : X) (u v : List (Letter I)) (l : Letter I) {q : ℕ}
    (hq : q < (u ++ [l.dual, l] ++ v).length) (n : ℕ)
    (Y₀ : (presLoc RD k).obj ((incl RD).obj (ob RD μ [])) ⟶
      (presLoc RD k).obj ((incl RD).obj (ob RD μ (u ++ [l.dual, l] ++ v)))) :
    (Y₀ ≫ (toLoc RD k).map (dD RD k μ (u ++ [l.dual, l] ++ v) [q])) ≫ capDots μ u v l n =
      (Y₀ ≫ capDots μ u v l n) ≫ (toLoc RD k).map (dD RD k μ (u ++ [l.dual, l] ++ v) [q]) := by
  rw [Category.assoc, Category.assoc, capDots,
    toLoc_dD_comm μ (dD_single_lt hq) (replicate_capPos_lt u v l n)]

/-- A dot on either strand of the cap followed by the cap. -/
theorem dD_comp_cap_of_near (μ : X) (u v : List (Letter I)) (l : Letter I) {q : ℕ}
    (hq : q = u.length ∨ q = u.length + 1) :
    dD RD k μ (u ++ [l.dual, l] ++ v) [q] ≫ cp (RD := RD) (k := k) μ u v l =
      dD RD k μ (u ++ [l.dual, l] ++ v) [capPos u l] ≫ cp μ u v l := by
  obtain ⟨b, i⟩ := l
  have e := dD_near_comp_cap (RD := RD) (k := k) μ u v (b, i)
  cases b <;> rcases hq with rfl | rfl <;> simp only [capPos, capDn, Nat.add_zero] <;>
    first | rfl | exact e | exact e.symm

/-- Cap-good morphisms are closed under a dot on any strand. -/
theorem capSet_comp_dD_single (μ : X) (u v : List (Letter I)) (l : Letter I) {q : ℕ}
    (hq : q < (u ++ [l.dual, l] ++ v).length) {g} (hg : g ∈ capSet RD k μ u v l) :
    g ≫ dD RD k μ (u ++ [l.dual, l] ++ v) [q] ∈ capSet RD k μ u v l := by
  intro n Y hY
  obtain ⟨Y₀, e₀⟩ := exists_comp_capDots (RD := RD) (k := k) μ u v l n ((toLoc RD k).map g)
  have hYe : Y = Y₀ ≫ (toLoc RD k).map (dD RD k μ (u ++ [l.dual, l] ++ v) [q]) :=
    capDots_cancel μ u v l n (by rw [hY, comp_dD_comp_capDots μ u v l hq, e₀, Functor.map_comp])
  rw [hYe, Category.assoc]
  rcases (show q < u.length ∨ q = u.length ∨ q = u.length + 1 ∨ u.length + 2 ≤ q by omega) with
    h | h | h | h
  · rw [← Functor.map_comp, dD_left_comp_cap μ u v l h, Functor.map_comp, ← Category.assoc]
    exact coreSet_comp_dD μ (by simp; omega) (hg n Y₀ e₀)
  · rw [← Functor.map_comp, dD_comp_cap_of_near μ u v l (Or.inl h), Functor.map_comp,
      ← Category.assoc]
    exact capSet_comp_dD_capPos μ u v l hg n _
      (by rw [comp_dD_comp_capDots μ u v l (capPos_lt u v l), e₀, Functor.map_comp])
  · rw [← Functor.map_comp, dD_comp_cap_of_near μ u v l (Or.inr h), Functor.map_comp,
      ← Category.assoc]
    exact capSet_comp_dD_capPos μ u v l hg n _
      (by rw [comp_dD_comp_capDots μ u v l (capPos_lt u v l), e₀, Functor.map_comp])
  · have hq' : q < u.length + 2 + v.length := by simp at hq; omega
    rw [← Functor.map_comp, dD_right_comp_cap μ u v l h hq', Functor.map_comp, ← Category.assoc]
    exact coreSet_comp_dD μ (by simp; omega) (hg n Y₀ e₀)

/-- Cap-good morphisms are closed under dots. -/
theorem capSet_comp_dD (μ : X) (u v : List (Letter I)) (l : Letter I) :
    ∀ {is : List ℕ}, (∀ i ∈ is, i < (u ++ [l.dual, l] ++ v).length) → ∀ {g},
      g ∈ capSet RD k μ u v l → g ≫ dD RD k μ (u ++ [l.dual, l] ++ v) is ∈ capSet RD k μ u v l
  | [], _, g, hg => by
    rw [show dD RD k μ (u ++ [l.dual, l] ++ v) [] = 𝟙 _ from dg_nil μ _, Category.comp_id]
    exact hg
  | q :: is, h, g, hg => by
    have hq : q < (u ++ [l.dual, l] ++ v).length := h q List.mem_cons_self
    rw [show q :: is = [q] ++ is from rfl, dD_append μ (dD_single_lt hq)
      (fun i hi => h i (List.mem_cons_of_mem _ hi)), ← Category.assoc]
    exact capSet_comp_dD μ u v l (fun i hi => h i (List.mem_cons_of_mem _ hi))
      (capSet_comp_dD_single μ u v l hq hg)

/-- Cap-good morphisms are closed under bubbles on the far right. -/
theorem capSet_comp_bubAt (μ : X) (u v : List (Letter I)) (l : Letter I)
    (β : End ((pres RD k).obj (ob RD μ []))) {g} (hg : g ∈ capSet RD k μ u v l) :
    g ≫ bubAt RD k μ (u ++ [l.dual, l] ++ v) β ∈ capSet RD k μ u v l := by
  intro n Y hY
  obtain ⟨Y₀, e₀⟩ := exists_comp_capDots (RD := RD) (k := k) μ u v l n ((toLoc RD k).map g)
  have hYe : Y = Y₀ ≫ (toLoc RD k).map (bubAt RD k μ (u ++ [l.dual, l] ++ v) β) := by
    refine capDots_cancel μ u v l n ?_
    rw [hY, Functor.map_comp, ← e₀, Category.assoc, Category.assoc]
    congr 1
    rw [capDots, ← Functor.map_comp, ← Functor.map_comp,
      bubAt_comm_dg RD k μ β _ (sChain_dotsL (replicate_capPos_lt u v l n))]
  rw [hYe, Category.assoc, ← Functor.map_comp, bubAt_comm_dg RD k μ β _ (sChain_cp u v l),
    Functor.map_comp, ← Category.assoc]
  exact coreSet_comp_bubAt μ _ β (hg n Y₀ e₀)

/-- **A morphism through a cup at the cap's position is cap-good**: the cup, inverse dots and
cap form a negative bubble (Webster arXiv:1309.3796v2, Definition 3.28). -/
theorem comp_cup_mem_capSet (μ : X) (u v : List (Letter I)) (l : Letter I)
    (H : (pres RD k).obj (ob RD μ []) ⟶ (pres RD k).obj (ob RD μ (u ++ [] ++ v))) :
    H ≫ dg RD k μ (u ++ [] ++ v) (u ++ [l.dual, l] ++ v) [(u, .cup l.dual, v)] ∈
      capSet RD k μ u v l := by
  intro n Y hY
  obtain ⟨Z, eZ, h, eh⟩ := cup_invDots_cap_placed (RD := RD) (k := k) μ u v l n
  have hYe : Y = (toLoc RD k).map H ≫ Z :=
    capDots_cancel μ u v l n (by rw [hY, Category.assoc, capDots, eZ, Functor.map_comp])
  rw [hYe, Category.assoc, eh, ← Functor.map_comp]
  exact toLoc_mem_coreSet μ _ _

/-- The position of a strand away from the cap after the cap. -/
def capShift (u : List (Letter I)) (p : ℕ) : ℕ := if p < u.length then p else p - 2

/-- A dot away from the cap passes it. -/
theorem dD_comp_cap_of_far (μ : X) (u v : List (Letter I)) (l : Letter I) {p : ℕ}
    (hp : p < (u ++ [l.dual, l] ++ v).length) (hn : p ≠ u.length ∧ p ≠ u.length + 1) :
    dD RD k μ (u ++ [l.dual, l] ++ v) [p] ≫ cp (RD := RD) (k := k) μ u v l =
      cp μ u v l ≫ dD RD k μ (u ++ [] ++ v) [capShift u p] ∧
      capShift u p < (u ++ [] ++ v).length := by
  unfold capShift
  split_ifs with h
  · exact ⟨dD_left_comp_cap μ u v l h, by simp; omega⟩
  · have hp' : p < u.length + 2 + v.length := by simp at hp; omega
    exact ⟨dD_right_comp_cap μ u v l (by omega) hp', by simp at hp ⊢; omega⟩

/-- **Sliding a dot off the cap** (Webster arXiv:1309.3796v2, proof of Lemma 3.29): if a dot on
the downward strand of the cap equals, modulo cap-good morphisms, a dot on a strand `p` away from
the cap, then the morphism is cap-good. -/
theorem mem_capSet_of_arc (μ : X) (u v : List (Letter I)) (l : Letter I) {p : ℕ}
    (hp : p < (u ++ [l.dual, l] ++ v).length) (hn : p ≠ u.length ∧ p ≠ u.length + 1)
    (G : (pres RD k).obj (ob RD μ []) ⟶ (pres RD k).obj (ob RD μ (u ++ [l.dual, l] ++ v)))
    (hG : G ≫ dD RD k μ _ [capPos u l] - G ≫ dD RD k μ _ [p] ∈ capSet RD k μ u v l) :
    G ∈ capSet RD k μ u v l := by
  obtain ⟨hpass, hsh⟩ := dD_comp_cap_of_far (RD := RD) (k := k) μ u v l hp hn
  intro n
  induction n with
  | zero => exact fun Y hY => capDots_zero_comp_cap μ u v l _ hY
  | succ n ih =>
    intro Y hY
    have hV : (Y ≫ (toLoc RD k).map (dD RD k μ _ [capPos u l])) ≫ capDots μ u v l n =
        (toLoc RD k).map G := by
      rw [Category.assoc, show (toLoc RD k).map (dD RD k μ _ [capPos u l]) ≫ capDots μ u v l n =
        capDots μ u v l (n + 1) from by
          rw [capDots_succ]
          exact toLoc_dD_comm μ (dD_single_lt (capPos_lt u v l)) (replicate_capPos_lt u v l n),
        hY]
    obtain ⟨W, eW⟩ := exists_comp_capDots (RD := RD) (k := k) μ u v l (n + 1)
      ((toLoc RD k).map (G ≫ dD RD k μ _ [capPos u l] - G ≫ dD RD k μ _ [p]))
    have hYp : (Y ≫ (toLoc RD k).map (dD RD k μ _ [p]) :
        (presLoc RD k).obj ((incl RD).obj (ob RD μ [])) ⟶
          (presLoc RD k).obj ((incl RD).obj (ob RD μ (u ++ [l.dual, l] ++ v)))) =
        (Y ≫ (toLoc RD k).map (dD RD k μ _ [capPos u l]) :
        (presLoc RD k).obj ((incl RD).obj (ob RD μ [])) ⟶
          (presLoc RD k).obj ((incl RD).obj (ob RD μ (u ++ [l.dual, l] ++ v)))) - W := by
      refine capDots_cancel μ u v l (n + 1) ?_
      rw [Preadditive.sub_comp, eW, comp_dD_comp_capDots μ u v l hp,
        comp_dD_comp_capDots μ u v l (capPos_lt u v l), hY, Functor.map_sub,
        Functor.map_comp, Functor.map_comp, sub_sub_cancel]
    have hmem : (Y ≫ (toLoc RD k).map (cp μ u v l)) ≫
        (toLoc RD k).map (dD RD k μ (u ++ [] ++ v) [capShift u p]) ∈
          coreSet RD k μ (u ++ [] ++ v) := by
      rw [Category.assoc, ← Functor.map_comp, ← hpass, Functor.map_comp, ← Category.assoc, hYp,
        Preadditive.sub_comp]
      exact Submodule.sub_mem _ (ih _ hV) (hG (n + 1) W eW)
    exact coreSet_of_comp_dD μ (dD_single_lt hsh) hmem

/-! ## Canonical diagrams are cap-good -/

section Canonical

open StringDiagrams.Chord (Move canon Same Valid Lettered)

variable [DecidableEq I]

/-- **A canonical diagram is cap-good** (Webster arXiv:1309.3796v2, proof of Lemma 3.29), if the
lower terms are. The downward strand `D` of the cap is joined by an arc to a strand `p`. If `p` is
the other strand of the cap, the arc is, modulo lower terms, a cup at the cap's position (a
negative bubble). Otherwise a dot slides along the arc from `D` to `p`, modulo lower terms. -/
theorem canon_mem_capSet (μ : X) (u v : List (Letter I)) (l : Letter I)
    {σ : List (ℕ × Letter I)} (hv : Valid σ) (hl : Lettered Letter.dual σ)
    (hsv : σ.map Prod.snd = u ++ [l.dual, l] ++ v)
    (hlo : ∀ m ≤ ncr (canon σ), Lo RD k μ [] (u ++ [l.dual, l] ++ v) m ≤ capSet RD k μ u v l) :
    dg RD k μ [] (u ++ [l.dual, l] ++ v) (chL [] (canon σ)) ∈ capSet RD k μ u v l := by
  have hlen : σ.length = (u ++ [l.dual, l] ++ v).length := by rw [← hsv, List.length_map]
  have hsc : SChain [] (chL [] (canon σ)) (u ++ [l.dual, l] ++ v) := by
    have := sChain_chL (l := []) (canon_letters hv hl).1
    rwa [(canon_letters hv hl).2, hsv] at this
  obtain ⟨p, hp⟩ := hv.exists (show capPos u l < σ.length by rw [hlen]; exact capPos_lt u v l)
  by_cases hB : Same σ u.length (u.length + 1)
  · -- the arc of `D` is a cup at the cap's position
    have hl2 : u.length + 2 ≤ σ.length := hB.lt_right
    obtain ⟨x, hx⟩ : ∃ x, x = (σ[u.length]'hB.lt_left).2 := ⟨_, rfl⟩
    obtain ⟨t, ht⟩ : ∃ t, t = Chord.rmAt σ u.length := ⟨_, rfl⟩
    have hvt : Valid t := ht ▸ hv.rmAt hB
    have hlt : Lettered Letter.dual t := ht ▸ hl.rmAt hl2
    obtain ⟨hft, hct⟩ := canon_letters hvt hlt
    have heq := Chord.canon_cup hv hB
    rw [← ht, ← hx] at heq
    obtain ⟨-, hsound⟩ := equiv_sound (RD := RD) (k := k) heq (canon_letters hv hl).1
    have hv' : σ.map Prod.snd = lst (t.map Prod.snd) (.cup u.length x) := by
      rw [ht, hx]; exact map_snd_adj hl hB
    have htl : u.length ≤ (t.map Prod.snd).length := by
      rw [List.length_map, ht, Chord.length_rmAt σ hl2]; omega
    obtain ⟨u', w', htw, hu'⟩ := exists_split_cup htl
    rw [htw, ← hu', lst_cup, hsv] at hv'
    obtain ⟨hu, hxw⟩ := List.append_inj
      (show u ++ (l.dual :: l :: v) = u' ++ (x :: x.dual :: w') by simpa using hv') hu'.symm
    subst hu
    simp only [List.cons.injEq] at hxw
    obtain ⟨hxl, -, hvw⟩ := hxw
    subst hxl hvw
    have hsc' : SChain [] (chL [] (canon t)) (u ++ [] ++ v) := by
      rw [show u ++ [] ++ v = u ++ v by simp]
      have := sChain_chL (l := []) hft
      rwa [hct, htw] at this
    have hC' : dg RD k μ [] (u ++ [l.dual, l] ++ v) (chL [] (canon t ++ [.cup u.length l.dual])) =
        dg RD k μ [] (u ++ [] ++ v) (chL [] (canon t)) ≫
          dg RD k μ (u ++ [] ++ v) (u ++ [l.dual, l] ++ v) [(u, .cup l.dual, v)] := by
      rw [← dg_append_of_left hsc', chL_append, hct, htw]
      simp [chL]
    have hsub := hlo _ le_rfl (hsound μ (u ++ [l.dual, l] ++ v))
    rw [hC'] at hsub
    have := Submodule.add_mem _ hsub (comp_cup_mem_capSet μ u v l
      (dg RD k μ [] (u ++ [] ++ v) (chL [] (canon t))))
    rwa [sub_add_cancel] at this
  · -- a dot slides along the arc of `D` to a strand away from the cap
    have hfar : p ≠ u.length ∧ p ≠ u.length + 1 := by
      have hne : capPos u l ≠ p := hp.ne
      rcases (show capDn l = 0 ∨ capDn l = 1 by have := capDn_lt l; omega) with h | h
      · have hp' : Same σ u.length p := by simpa [capPos, h] using hp
        refine ⟨fun e => ?_, fun e => hB (by subst e; exact hp')⟩
        simp [capPos, h, e] at hne
      · have hp' : Same σ (u.length + 1) p := by simpa [capPos, h] using hp
        refine ⟨fun e => hB (by subst e; exact hp'.symm), fun e => ?_⟩
        simp [capPos, h, e] at hne
    have hpl : p < (u ++ [l.dual, l] ++ v).length := hlen ▸ hp.lt_right
    refine mem_capSet_of_arc μ u v l hpl hfar _ ?_
    have hA := arc_dot (RD := RD) (k := k) μ (σ.length + Chord.cr σ + 1) (by omega) hv hl
      hp.symm [] (u ++ [l.dual, l] ++ v)
    rw [hsv, ccnt_nil, add_zero] at hA
    have e : ∀ q, dg RD k μ [] (u ++ [l.dual, l] ++ v) (chL [] (canon σ)) ≫
        dD RD k μ (u ++ [l.dual, l] ++ v) [q] = dg RD k μ [] (u ++ [l.dual, l] ++ v)
          (chL [] (canon σ) ++ dotAt (u ++ [l.dual, l] ++ v) q ++ []) := fun q => by
      rw [List.append_assoc (chL [] (canon σ)), dg_append_of_left hsc]
      rfl
    rw [e, e]
    exact hlo _ le_rfl hA

variable {k : Type w} [Field k]

/-- **The filtered canonical span is cap-good** (Webster arXiv:1309.3796v2, proof of
Lemma 3.29). -/
theorem canonSpanLe_le_capSet (μ : X) (u v : List (Letter I)) (l : Letter I) :
    ∀ c, canonSpanLe RD k μ (u ++ [l.dual, l] ++ v) c ≤ capSet RD k μ u v l := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ihc =>
  have hlo : ∀ m ≤ c, Lo RD k μ [] (u ++ [l.dual, l] ++ v) m ≤ capSet RD k μ u v l := by
    intro m hm
    cases m with
    | zero => rw [lo_zero]; exact bot_le
    | succ m => exact (lo_le_canonSpanLe μ _ m).trans (ihc m (by omega))
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨σ, is, β, hv, hl, hsv, his, -, hc, rfl⟩
  have hlen : σ.length = (u ++ [l.dual, l] ++ v).length := by rw [← hsv, List.length_map]
  have hsc : SChain [] (chL [] (canon σ)) (u ++ [l.dual, l] ++ v) := by
    have := sChain_chL (l := []) (canon_letters hv hl).1
    rwa [(canon_letters hv hl).2, hsv] at this
  rw [SetLike.mem_coe, dg_append_of_left hsc]
  exact capSet_comp_bubAt μ u v l β (capSet_comp_dD μ u v l
    (fun i hi => hlen ▸ (his i hi).1)
    (canon_mem_capSet μ u v l hv hl hsv (fun m hm => hlo m (hm.trans hc))))

/-- **Every 2-morphism of `U` is cap-good** (Webster arXiv:1309.3796v2, proof of Lemma 3.29). -/
theorem mem_capSet (μ : X) (u v : List (Letter I)) (l : Letter I)
    (g : (pres RD k).obj (ob RD μ []) ⟶ (pres RD k).obj (ob RD μ (u ++ [l.dual, l] ++ v))) :
    g ∈ capSet RD k μ u v l := by
  have h := mem_span_dg (RD := RD) (k := k) μ g
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨L, -, rfl⟩ := hx
    exact canonSpanLe_le_capSet μ u v l _ (mem_canonSpanLe μ _ (ccnt L) L le_rfl)
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul r x _ hx => exact Submodule.smul_mem _ r hx

/-! ## Core morphisms are closed under caps -/

omit [DecidableEq I] in
/-- Dots on the strands of a cap, followed by the cap, are dots on its downward strand. -/
theorem dD_near_list_comp_cap (μ : X) (u v : List (Letter I)) (l : Letter I) :
    ∀ {is : List ℕ}, (∀ q ∈ is, q = u.length ∨ q = u.length + 1) →
      dD RD k μ (u ++ [l.dual, l] ++ v) is ≫ cp (RD := RD) (k := k) μ u v l =
        dD RD k μ (u ++ [l.dual, l] ++ v) (List.replicate is.length (capPos u l)) ≫ cp μ u v l
  | [], _ => rfl
  | q :: is, h => by
    have hq : q < (u ++ [l.dual, l] ++ v).length := by
      rcases h q List.mem_cons_self with rfl | rfl <;> simp
    have his : ∀ i ∈ is, i < (u ++ [l.dual, l] ++ v).length := by
      intro i hi; rcases h i (List.mem_cons_of_mem _ hi) with rfl | rfl <;> simp
    rw [show q :: is = [q] ++ is from rfl, dD_append μ (dD_single_lt hq) his, Category.assoc,
      dD_near_list_comp_cap μ u v l (fun i hi => h i (List.mem_cons_of_mem _ hi)),
      ← Category.assoc, dD_comm μ (dD_single_lt hq) (replicate_capPos_lt u v l _),
      Category.assoc, dD_comp_cap_of_near μ u v l (h q List.mem_cons_self), ← Category.assoc,
      ← dD_append μ (replicate_capPos_lt u v l _) (dD_single_lt (capPos_lt u v l)),
      ← List.replicate_succ']
    rfl

omit [DecidableEq I] in
/-- Dots away from a cap pass it. -/
theorem dD_far_list_comp_cap (μ : X) (u v : List (Letter I)) (l : Letter I) :
    ∀ {is : List ℕ}, (∀ q ∈ is, q < (u ++ [l.dual, l] ++ v).length ∧
      q ≠ u.length ∧ q ≠ u.length + 1) →
      dD RD k μ (u ++ [l.dual, l] ++ v) is ≫ cp (RD := RD) (k := k) μ u v l =
        cp μ u v l ≫ dD RD k μ (u ++ [] ++ v) (is.map (capShift u)) ∧
      ∀ q ∈ is.map (capShift u), q < (u ++ [] ++ v).length
  | [], _ => ⟨by rw [List.map_nil, show dD RD k μ (u ++ [l.dual, l] ++ v) [] = 𝟙 _ from
      dg_nil μ _, show dD RD k μ (u ++ [] ++ v) [] = 𝟙 _ from dg_nil μ _, Category.id_comp,
      Category.comp_id], by simp⟩
  | q :: is, h => by
    obtain ⟨hq, hn⟩ := h q List.mem_cons_self
    have his : ∀ i ∈ is, i < (u ++ [l.dual, l] ++ v).length :=
      fun i hi => (h i (List.mem_cons_of_mem _ hi)).1
    obtain ⟨ih, ihb⟩ := dD_far_list_comp_cap μ u v l (fun i hi => h i (List.mem_cons_of_mem _ hi))
    obtain ⟨hpass, hsh⟩ := dD_comp_cap_of_far (RD := RD) (k := k) μ u v l hq hn
    refine ⟨?_, ?_⟩
    · rw [show q :: is = [q] ++ is from rfl, dD_append μ (dD_single_lt hq) his, Category.assoc,
        ih, ← Category.assoc, hpass, Category.assoc, List.map_append,
        ← dD_append μ (by simpa using hsh) ihb]
      rfl
    · intro i hi
      rw [List.map_cons, List.mem_cons] at hi
      rcases hi with rfl | hi
      · exact hsh
      · exact ihb i hi

variable {k : Type w} [Field k]

/-- **Core morphisms of `U′` are closed under caps** (Webster arXiv:1309.3796v2, proof of
Lemma 3.29). -/
theorem coreSet_comp_cap (μ : X) (u v : List (Letter I)) (l : Letter I) {f}
    (hf : f ∈ coreSet RD k μ (u ++ [l.dual, l] ++ v)) :
    f ≫ (toLoc RD k).map (cp μ u v l) ∈ coreSet RD k μ (u ++ [] ++ v) := by
  obtain ⟨is, his, g, e⟩ := hf
  let P : ℕ → Bool := fun q => decide (q = u.length ∨ q = u.length + 1)
  have hperm : is.Perm (is.filter (fun q => !P q) ++ is.filter P) :=
    (List.filter_append_perm P is).symm.trans List.perm_append_comm
  have hfar : ∀ q ∈ is.filter (fun q => !P q), q < (u ++ [l.dual, l] ++ v).length ∧
      q ≠ u.length ∧ q ≠ u.length + 1 := by
    intro q hq
    rw [List.mem_filter] at hq
    have h2 : ¬(q = u.length ∨ q = u.length + 1) := by simpa [P] using hq.2
    exact ⟨his q hq.1, fun e => h2 (Or.inl e), fun e => h2 (Or.inr e)⟩
  have hnear : ∀ q ∈ is.filter P, q = u.length ∨ q = u.length + 1 := by
    intro q hq
    rw [List.mem_filter] at hq
    simpa [P] using hq.2
  have hnb : ∀ q ∈ is.filter P, q < (u ++ [l.dual, l] ++ v).length := by
    intro q hq; rcases hnear q hq with rfl | rfl <;> simp
  have e' : (f ≫ (toLoc RD k).map (dD RD k μ _ (is.filter (fun q => !P q)))) ≫
      (toLoc RD k).map (dD RD k μ _ (is.filter P)) = (toLoc RD k).map g := by
    rw [Category.assoc, ← Functor.map_comp, ← dD_append μ (fun q hq => (hfar q hq).1) hnb,
      ← dD_perm μ hperm his]
    exact e
  obtain ⟨V, hV⟩ := exists_comp_capDots (RD := RD) (k := k) μ u v l (is.filter P).length
    (f ≫ (toLoc RD k).map (dD RD k μ _ (is.filter (fun q => !P q))))
  have hY : (V ≫ (toLoc RD k).map (dD RD k μ _ (is.filter P))) ≫
      capDots μ u v l (is.filter P).length = (toLoc RD k).map g := by
    calc (V ≫ (toLoc RD k).map (dD RD k μ _ (is.filter P))) ≫
          capDots μ u v l (is.filter P).length =
        (V ≫ capDots μ u v l (is.filter P).length) ≫
          (toLoc RD k).map (dD RD k μ _ (is.filter P)) := by
          rw [Category.assoc, Category.assoc, capDots,
            toLoc_dD_comm μ hnb (replicate_capPos_lt u v l _)]
      _ = (toLoc RD k).map g := by rw [hV]; exact e'
  have hc := mem_capSet μ u v l g _ _ hY
  have h1 : (f ≫ (toLoc RD k).map (dD RD k μ _ (is.filter (fun q => !P q)))) ≫
      (toLoc RD k).map (cp μ u v l) ∈ coreSet RD k μ (u ++ [] ++ v) := by
    rw [← hV]
    have : (V ≫ (toLoc RD k).map (dD RD k μ _ (is.filter P))) ≫ (toLoc RD k).map (cp μ u v l) =
        (V ≫ capDots μ u v l (is.filter P).length) ≫ (toLoc RD k).map (cp μ u v l) := by
      rw [Category.assoc, Category.assoc, ← Functor.map_comp,
        dD_near_list_comp_cap μ u v l hnear, Functor.map_comp]
    rw [← this]
    exact hc
  obtain ⟨hpass, hb⟩ := dD_far_list_comp_cap (RD := RD) (k := k) μ u v l hfar
  refine coreSet_of_comp_dD μ hb ?_
  rw [Category.assoc, ← Functor.map_comp, ← hpass, Functor.map_comp, ← Category.assoc]
  exact h1

/-- **Every 2-morphism of `U′` out of `1_μ` is a core morphism** (Webster arXiv:1309.3796v2,
proof of Lemma 3.29): it becomes the image of a 2-morphism of `U` after adding some dots. -/
theorem mem_coreSet (μ : X) (s : List (Letter I))
    (f : (presLoc RD k).obj ((incl RD).obj (ob RD μ [])) ⟶
      (presLoc RD k).obj ((incl RD).obj (ob RD μ s))) : f ∈ coreSet RD k μ s := by
  refine loc_mem_of_layers RD k μ (coreSet RD k μ) (id_mem_coreSet μ) ?_
    (fun u i w f hf => coreSet_comp_invDot μ u i w hf) s f
  intro u g v f hf
  cases g with
  | dot l => exact coreSet_comp_dot μ u l v hf
  | cross ε c d => exact coreSet_comp_cross μ u v ε c d hf
  | cup l => exact coreSet_comp_cup μ u v l hf
  | cap l => exact coreSet_comp_cap μ u v l hf

end Canonical

end Categorification.KL3.Diagram

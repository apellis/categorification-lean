/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.MarkovLeft
import Categorification.Diagrams.KL3.Pitchfork

/-!
# Straightening monotone diagrams

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.1.1
(Definition 3.1: biadjointness (3.1), (3.2) and cyclicity (3.3), `eq_cyclic_cross-gen`), used in
§3.2.2 (proof of Lemma 3.9, label `lem_surjective`; TeX locators
`sources/klr/kl3/0807.3250v1.txt`, lines 1690–1790).

A normal-form diagram of `U` is **monotone of type `RL`** if its cups are all of the form
`1 → F_j E_j` and its caps all of the form `E_j F_j → 1` (together with arbitrary dots and
crossings), and **monotone of type `LR`** if its cups are all `1 → E_j F_j` and its caps all
`F_j E_j → 1`. In a monotone diagram every strand turns in the same direction at each cup and
each cap, so that a monotone diagram between two upward sequences is isotopic to an upward
diagram. This file proves this with the relations of `U`:

* downward dots and downward crossings are rotations of upward ones (KL III (3.3),
  `eq_cyclic_cross-gen`), by cups and caps of the same type (`dg_rotRL`, `dg_rotLR`);
* afterwards a downward strand is never touched between the cup creating it and the cap
  consuming it. All layers in between act either to its left or to its right (`Sep`), so they
  can be moved below the cup or above the cap by the interchange law (`Sep.dg_eq`); the cup and
  the cap then form a zigzag, which is removed (KL III (3.1), (3.2)).

No relation other than the interchange law, the zigzag relations and the cyclicity relations is
used; in particular no relation holds only modulo diagrams with fewer crossings.

## Main results

* `straightenRL`, `straightenLR`: **a monotone diagram (of either type) between two upward
  sequences is equal to an upward diagram** (with the same boundary).
* `straightenRL_mem_upSpan`, `straightenLR_mem_upSpan`: such diagrams lie in `upSpan`.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {k : Type w} [CommRing k]

/-! ## Monotone shapes -/

namespace Shape

/-- Shapes of monotone diagrams of type `RL`: dots, crossings, cups `1 → F E` and caps
`E F → 1`. -/
def isRL : Shape I → Bool
  | .dot _ => true
  | .cross _ _ _ => true
  | .cup l => !l.1
  | .cap l => !l.1

/-- Shapes of monotone diagrams of type `LR`: dots, crossings, cups `1 → E F` and caps
`F E → 1`. -/
def isLR : Shape I → Bool
  | .dot _ => true
  | .cross _ _ _ => true
  | .cup l => l.1
  | .cap l => l.1

/-- Shapes of rotated monotone diagrams of type `RL`: upward dots, upward crossings, cups
`1 → F E` and caps `E F → 1`. -/
def isRLu : Shape I → Bool
  | .dot l => l.1
  | .cross ε _ _ => ε
  | .cup l => !l.1
  | .cap l => !l.1

/-- Shapes of rotated monotone diagrams of type `LR`: upward dots, upward crossings, cups
`1 → E F` and caps `F E → 1`. -/
def isLRu : Shape I → Bool
  | .dot l => l.1
  | .cross ε _ _ => ε
  | .cup l => l.1
  | .cap l => l.1

end Shape

/-- All layers satisfy the predicate `p` on shapes. -/
def AllSh (p : Shape I → Bool) (ls : List (LayerData I)) : Prop := ∀ x ∈ ls, p x.2.1 = true

theorem AllSh.append {p : Shape I → Bool} {a b : List (LayerData I)} (ha : AllSh p a)
    (hb : AllSh p b) : AllSh p (a ++ b) := by
  intro x hx
  rcases List.mem_append.1 hx with h | h
  · exact ha x h
  · exact hb x h

theorem AllSh.of_append_left {p : Shape I → Bool} {a b : List (LayerData I)}
    (h : AllSh p (a ++ b)) : AllSh p a := fun x hx => h x (List.mem_append_left _ hx)

theorem AllSh.of_append_right {p : Shape I → Bool} {a b : List (LayerData I)}
    (h : AllSh p (a ++ b)) : AllSh p b := fun x hx => h x (List.mem_append_right _ hx)

theorem AllSh.map_whL {p : Shape I → Bool} {a : List (LayerData I)} (h : AllSh p a)
    (u v : List (Letter I)) : AllSh p (a.map (whL u v)) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  exact h y hy

theorem AllSh.of_perm {p : Shape I → Bool} {a b : List (LayerData I)}
    (hp : List.Perm (a.map (·.2.1)) (b.map (·.2.1))) (h : AllSh p b) : AllSh p a := by
  intro x hx
  have hm : x.2.1 ∈ b.map (·.2.1) := hp.subset (List.mem_map_of_mem hx)
  obtain ⟨y, hy, e⟩ := List.mem_map.1 hm
  rw [← e]
  exact h y hy

theorem ncc_eq_of_perm {a b : List (LayerData I)}
    (hp : List.Perm (a.map (·.2.1)) (b.map (·.2.1))) : ncc a = ncc b := by
  have h := hp.countP_eq (fun g => g.isCupCap)
  simpa [ncc, List.countP_map, Function.comp_def] using h

theorem ncc_map_whL (a : List (LayerData I)) (u v : List (Letter I)) :
    ncc (a.map (whL u v)) = ncc a := by
  simp [ncc, List.countP_map, Function.comp_def, whL]

theorem positive_append {a b : List (Letter I)} : Positive (a ++ b) ↔ Positive a ∧ Positive b := by
  simp only [Positive, List.mem_append]
  exact ⟨fun h => ⟨fun l hl => h l (Or.inl hl), fun l hl => h l (Or.inr hl)⟩,
    fun h l hl => hl.elim (h.1 l) (h.2 l)⟩

theorem positive_cons {l : Letter I} {a : List (Letter I)} :
    Positive (l :: a) ↔ l.1 = true ∧ Positive a := by
  simp only [Positive, List.mem_cons, forall_eq_or_imp]

/-! ## Layers separated by a downward strand -/

/-- `Sep j L R B L' R'`: the layers `B` act on words `L ++ F_j :: R` without touching the
strand `F_j`: each layer acts either on the strands to its left or on the strands to its right;
the left part goes from `L` to `L'` and the right part from `R` to `R'`. -/
inductive Sep (j : I) :
    List (Letter I) → List (Letter I) → List (LayerData I) → List (Letter I) → List (Letter I) →
      Prop
  | nil (L R : List (Letter I)) : Sep j L R [] L R
  | left (u v R : List (Letter I)) (g : Shape I) {B : List (LayerData I)}
      {L' R' : List (Letter I)} :
      Sep j (u ++ g.cod ++ v) R B L' R' →
        Sep j (u ++ g.dom ++ v) R ((u, g, v ++ dn j :: R) :: B) L' R'
  | right (L u v : List (Letter I)) (g : Shape I) {B : List (LayerData I)}
      {L' R' : List (Letter I)} :
      Sep j L (u ++ g.cod ++ v) B L' R' →
        Sep j L (u ++ g.dom ++ v) ((L ++ dn j :: u, g, v) :: B) L' R'

/-- **Layers not touching a downward strand split into a left and a right part** (interchange
law): `B` equals its left part (with the strand and everything to its right as spectators)
followed by its right part. -/
theorem Sep.dg_eq {j : I} {L R : List (Letter I)} {B : List (LayerData I)}
    {L' R' : List (Letter I)} (hS : Sep j L R B L' R') :
    ∃ BL BR : List (LayerData I), SChain L BL L' ∧ SChain R BR R' ∧
      List.Perm ((BL ++ BR).map (·.2.1)) (B.map (·.2.1)) ∧
      ∀ (μ : X) (S T : List (Letter I)) (pre post : List (LayerData I)),
        dg RD k μ S T (pre ++ B ++ post) =
          dg RD k μ S T (pre ++ BL.map (whL [] (dn j :: R)) ++
            BR.map (whL (L' ++ [dn j]) []) ++ post) := by
  induction hS with
  | nil L R => exact ⟨[], [], rfl, rfl, by simp, fun μ S T pre post => by simp⟩
  | left u v R g hS ih =>
    obtain ⟨BL, BR, hL, hR, hp, hd⟩ := ih
    refine ⟨(u, g, v) :: BL, BR, ⟨rfl, hL⟩, hR, ?_, fun μ S T pre post => ?_⟩
    · simpa using hp
    · have e := hd μ S T (pre ++ [(u, g, v ++ dn j :: R)]) post
      simp only [List.append_assoc, List.singleton_append] at e ⊢
      rw [e]
      simp [whL]
  | right L u v g hS ih =>
    rename_i B L' R'
    obtain ⟨BL, BR, hL, hR, hp, hd⟩ := ih
    refine ⟨BL, (u, g, v) :: BR, hL, ⟨rfl, hR⟩, ?_, fun μ S T pre post => ?_⟩
    · simp only [List.map_append, List.map_cons]
      refine List.perm_middle.trans ?_
      simpa using hp
    · have e := hd μ S T (pre ++ [(L ++ dn j :: u, g, v)]) post
      have ei := dg_interchange (RD := RD) (k := k) (μ := μ) (S := S) (T := T) pre
        (BR.map (whL (L' ++ [dn j]) []) ++ post) hL
        (B := [(dn j :: u, g, v)]) (t := dn j :: (u ++ g.dom ++ v))
        (t' := dn j :: (u ++ g.cod ++ v)) ⟨by simp, by simp⟩
      simp only [List.append_assoc, List.singleton_append] at e ei ⊢
      rw [e]
      simp only [whL, List.map_cons, List.map_nil, List.append_nil, List.cons_append,
        List.nil_append, List.singleton_append, List.append_assoc] at ei ⊢
      rw [← ei]

/-! ## Locating a strand in a layer -/

theorem split3 {α : Type*} {L R₀ u d v : List α} {x : α} (h : L ++ x :: R₀ = u ++ d ++ v) :
    (∃ v', L = u ++ d ++ v' ∧ v = v' ++ x :: R₀) ∨ (∃ u', u = L ++ x :: u' ∧ R₀ = u' ++ d ++ v) ∨
      (∃ d₁ d₂, d = d₁ ++ x :: d₂ ∧ L = u ++ d₁ ∧ R₀ = d₂ ++ v) := by
  rw [List.append_assoc] at h
  rcases List.append_eq_append_iff.1 h with ⟨a', hu, hb⟩ | ⟨c', hL, hd⟩
  · cases a' with
    | nil =>
      simp only [List.append_nil] at hu
      subst hu
      cases d with
      | nil =>
        simp only [List.nil_append] at hb
        exact Or.inl ⟨[], by simp, hb.symm⟩
      | cons y d' =>
        simp only [List.nil_append, List.cons_append, List.cons.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        exact Or.inr (Or.inr ⟨[], d', rfl, by simp, rfl⟩)
    | cons y a₂ =>
      simp only [List.cons_append, List.cons.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact Or.inr (Or.inl ⟨a₂, hu, by simp⟩)
  · rcases List.append_eq_append_iff.1 hd with ⟨a', hc, hv⟩ | ⟨c₂, hdd, hxv⟩
    · exact Or.inl ⟨a', by rw [hL, hc, List.append_assoc], hv⟩
    · cases c₂ with
      | nil =>
        simp only [List.append_nil, List.nil_append] at hdd hxv
        exact Or.inl ⟨[], by rw [hL, hdd]; simp, hxv.symm⟩
      | cons y c₃ =>
        simp only [List.cons_append, List.cons.injEq] at hxv
        obtain ⟨rfl, rfl⟩ := hxv
        exact Or.inr (Or.inr ⟨c', c₃, hdd, hL, rfl⟩)

/-- A layer of a rotated monotone diagram of type `RL` acting on `L ++ F_j :: R₀` acts to the left
of `F_j`, to its right, or is a cap `E_j F_j → 1` consuming it. -/
theorem classifyRL {L R₀ u v : List (Letter I)} {g : Shape I} {j : I} (hg : g.isRLu = true)
    (h : L ++ dn j :: R₀ = u ++ g.dom ++ v) :
    (∃ v', L = u ++ g.dom ++ v' ∧ v = v' ++ dn j :: R₀) ∨
      (∃ u', u = L ++ dn j :: u' ∧ R₀ = u' ++ g.dom ++ v) ∨
      (L = u ++ [up j] ∧ g = .cap (dn j) ∧ v = R₀) := by
  rcases split3 h with h1 | h2 | ⟨d₁, d₂, hd, hL, hR⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · refine Or.inr (Or.inr ?_)
    cases g with
    | dot l =>
      simp only [Shape.isRLu] at hg
      cases d₁ with
      | nil => simp only [Shape.dom_dot, List.nil_append, List.cons.injEq] at hd; simp [hd.1] at hg
      | cons y d₁ => simp at hd
    | cross ε a b =>
      simp only [Shape.isRLu] at hg
      subst hg
      rcases d₁ with _ | ⟨y, _ | ⟨z, d₁⟩⟩ <;> simp at hd
    | cup l => cases d₁ <;> simp at hd
    | cap l =>
      obtain ⟨b, i⟩ := l
      cases b
      · rcases d₁ with _ | ⟨y, _ | ⟨z, d₁⟩⟩
        · simp [Letter.dual] at hd
        · simp only [Shape.dom_cap, Letter.dual_mk, Bool.not_false, List.singleton_append,
            List.cons.injEq, List.nil_eq] at hd
          obtain ⟨rfl, ⟨rfl, rfl⟩, rfl⟩ := hd
          simp only [List.nil_append] at hR
          exact ⟨hL, rfl, hR.symm⟩
        · simp at hd
      · simp [Shape.isRLu] at hg

/-- The mirror of `classifyRL`: a layer of a rotated monotone diagram of type `LR` acting on
`L ++ F_j :: R₀` acts to the left of `F_j`, to its right, or is a cap `F_j E_j → 1` consuming
it. -/
theorem classifyLR {L R₀ u v : List (Letter I)} {g : Shape I} {j : I} (hg : g.isLRu = true)
    (h : L ++ dn j :: R₀ = u ++ g.dom ++ v) :
    (∃ v', L = u ++ g.dom ++ v' ∧ v = v' ++ dn j :: R₀) ∨
      (∃ u', u = L ++ dn j :: u' ∧ R₀ = u' ++ g.dom ++ v) ∨
      (L = u ∧ g = .cap (up j) ∧ R₀ = up j :: v) := by
  rcases split3 h with h1 | h2 | ⟨d₁, d₂, hd, hL, hR⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · refine Or.inr (Or.inr ?_)
    cases g with
    | dot l =>
      simp only [Shape.isLRu] at hg
      cases d₁ with
      | nil => simp only [Shape.dom_dot, List.nil_append, List.cons.injEq] at hd; simp [hd.1] at hg
      | cons y d₁ => simp at hd
    | cross ε a b =>
      simp only [Shape.isLRu] at hg
      subst hg
      rcases d₁ with _ | ⟨y, _ | ⟨z, d₁⟩⟩ <;> simp at hd
    | cup l => cases d₁ <;> simp at hd
    | cap l =>
      obtain ⟨b, i⟩ := l
      cases b
      · simp [Shape.isLRu] at hg
      · rcases d₁ with _ | ⟨y, _ | ⟨z, d₁⟩⟩
        · simp only [Shape.dom_cap, Letter.dual_mk, Bool.not_true, List.nil_append,
            List.cons.injEq] at hd
          obtain ⟨⟨-, rfl⟩, rfl⟩ := hd
          simp only [List.append_nil] at hL
          exact ⟨hL, rfl, hR⟩
        · simp at hd
        · simp at hd

/-! ## The first cup and its partner cap -/

theorem positive_step {u v : List (Letter I)} {g : Shape I} (hg : g.isUp = true)
    (h : Positive (u ++ g.dom ++ v)) : Positive (u ++ g.cod ++ v) := by
  obtain ⟨-, hc, -⟩ := upShape_dom_positive hg
  rw [positive_append, positive_append] at h ⊢
  exact ⟨⟨h.1.1, hc⟩, h.2⟩

theorem not_positive_dn {a b : List (Letter I)} {j : I} (h : Positive (a ++ dn j :: b)) :
    False := by
  have := h (dn j) (by simp)
  simp at this

/-- **The first cup of a rotated monotone diagram** (type `RL`) starting at an upward sequence:
either there is no cup (and then the diagram is upward), or there is a first cup `1 → F_j E_j`,
below which the diagram is upward. -/
theorem firstCupRL : ∀ (ls : List (LayerData I)) {s t : List (Letter I)},
    AllSh Shape.isRLu ls → Positive s → SChain s ls t →
    Upward ls ∨ ∃ (A : List (LayerData I)) (w₁ w₂ : List (Letter I)) (j : I)
      (R : List (LayerData I)), ls = A ++ (w₁, Shape.cup (dn j), w₂) :: R ∧ Upward A ∧
        SChain s A (w₁ ++ w₂) := by
  intro ls
  induction ls with
  | nil => intro s t _ _ _; exact Or.inl (fun x hx => by simp at hx)
  | cons x ls ih =>
    intro s t hls hs h
    obtain ⟨u, g, v⟩ := x
    obtain ⟨h₀, h⟩ := h
    subst h₀
    have hx : g.isRLu = true := hls _ List.mem_cons_self
    have hls' : AllSh Shape.isRLu ls := fun y hy => hls y (List.mem_cons_of_mem _ hy)
    have hstep : g.isUp = true → Upward ls ∨ ∃ (A : List (LayerData I)) (w₁ w₂ : List (Letter I))
        (j : I) (R : List (LayerData I)), ls = A ++ (w₁, Shape.cup (dn j), w₂) :: R ∧ Upward A ∧
          SChain (u ++ g.cod ++ v) A (w₁ ++ w₂) := fun hu => ih hls' (positive_step hu hs) h
    have hup : g.isUp = true → Upward ((u, g, v) :: ls) ∨ ∃ (A : List (LayerData I))
        (w₁ w₂ : List (Letter I)) (j : I) (R : List (LayerData I)),
          (u, g, v) :: ls = A ++ (w₁, Shape.cup (dn j), w₂) :: R ∧ Upward A ∧
            SChain (u ++ g.dom ++ v) A (w₁ ++ w₂) := by
      intro hu
      rcases hstep hu with hl | ⟨A, w₁, w₂, j, R, rfl, hA, hch⟩
      · refine Or.inl fun y hy => ?_
        rcases List.mem_cons.1 hy with rfl | hy
        · exact hu
        · exact hl y hy
      · refine Or.inr ⟨(u, g, v) :: A, w₁, w₂, j, R, rfl, fun y hy => ?_, ⟨rfl, hch⟩⟩
        rcases List.mem_cons.1 hy with rfl | hy
        · exact hu
        · exact hA y hy
    cases g with
    | dot l => exact hup hx
    | cross ε a b => exact hup hx
    | cup l =>
      obtain ⟨b, j⟩ := l
      cases b
      · exact Or.inr ⟨[], u, v, j, ls, rfl, fun y hy => by simp at hy, by simp⟩
      · simp [Shape.isRLu] at hx
    | cap l =>
      obtain ⟨b, j⟩ := l
      cases b
      · exact (not_positive_dn (a := u ++ [up j]) (b := v) (j := j) (by simpa using hs)).elim
      · simp [Shape.isRLu] at hx

/-- The mirror of `firstCupRL`, type `LR`: the first cup is `1 → E_j F_j`. -/
theorem firstCupLR : ∀ (ls : List (LayerData I)) {s t : List (Letter I)},
    AllSh Shape.isLRu ls → Positive s → SChain s ls t →
    Upward ls ∨ ∃ (A : List (LayerData I)) (w₁ w₂ : List (Letter I)) (j : I)
      (R : List (LayerData I)), ls = A ++ (w₁, Shape.cup (up j), w₂) :: R ∧ Upward A ∧
        SChain s A (w₁ ++ w₂) := by
  intro ls
  induction ls with
  | nil => intro s t _ _ _; exact Or.inl (fun x hx => by simp at hx)
  | cons x ls ih =>
    intro s t hls hs h
    obtain ⟨u, g, v⟩ := x
    obtain ⟨h₀, h⟩ := h
    subst h₀
    have hx : g.isLRu = true := hls _ List.mem_cons_self
    have hls' : AllSh Shape.isLRu ls := fun y hy => hls y (List.mem_cons_of_mem _ hy)
    have hstep : g.isUp = true → Upward ls ∨ ∃ (A : List (LayerData I)) (w₁ w₂ : List (Letter I))
        (j : I) (R : List (LayerData I)), ls = A ++ (w₁, Shape.cup (up j), w₂) :: R ∧ Upward A ∧
          SChain (u ++ g.cod ++ v) A (w₁ ++ w₂) := fun hu => ih hls' (positive_step hu hs) h
    have hup : g.isUp = true → Upward ((u, g, v) :: ls) ∨ ∃ (A : List (LayerData I))
        (w₁ w₂ : List (Letter I)) (j : I) (R : List (LayerData I)),
          (u, g, v) :: ls = A ++ (w₁, Shape.cup (up j), w₂) :: R ∧ Upward A ∧
            SChain (u ++ g.dom ++ v) A (w₁ ++ w₂) := by
      intro hu
      rcases hstep hu with hl | ⟨A, w₁, w₂, j, R, rfl, hA, hch⟩
      · refine Or.inl fun y hy => ?_
        rcases List.mem_cons.1 hy with rfl | hy
        · exact hu
        · exact hl y hy
      · refine Or.inr ⟨(u, g, v) :: A, w₁, w₂, j, R, rfl, fun y hy => ?_, ⟨rfl, hch⟩⟩
        rcases List.mem_cons.1 hy with rfl | hy
        · exact hu
        · exact hA y hy
    cases g with
    | dot l => exact hup hx
    | cross ε a b => exact hup hx
    | cup l =>
      obtain ⟨b, j⟩ := l
      cases b
      · simp [Shape.isLRu] at hx
      · exact Or.inr ⟨[], u, v, j, ls, rfl, fun y hy => by simp at hy, by simp⟩
    | cap l =>
      obtain ⟨b, j⟩ := l
      cases b
      · simp [Shape.isLRu] at hx
      · exact (not_positive_dn (a := u) (b := up j :: v) (j := j) (by simpa using hs)).elim

/-- **The partner cap** (type `RL`): following a downward strand `F_j` upwards through a rotated
monotone diagram ending at an upward sequence, the first layer touching it is a cap
`E_j F_j → 1`; the layers below act to its left or to its right. -/
theorem findPartnerRL (j : I) : ∀ (R : List (LayerData I)) (L R₀ : List (Letter I))
    {t : List (Letter I)}, AllSh Shape.isRLu R → Positive t → SChain (L ++ dn j :: R₀) R t →
    ∃ (B : List (LayerData I)) (L₁ R' : List (Letter I)) (C : List (LayerData I)),
      R = B ++ (L₁, Shape.cap (dn j), R') :: C ∧ Sep j L R₀ B (L₁ ++ [up j]) R' ∧
        SChain (L₁ ++ R') C t := by
  intro R
  induction R with
  | nil =>
    intro L R₀ t _ ht h
    exact (not_positive_dn (h ▸ ht)).elim
  | cons x R ih =>
    intro L R₀ t hls ht h
    obtain ⟨u, g, v⟩ := x
    obtain ⟨h₀, h⟩ := h
    have hx : g.isRLu = true := hls _ List.mem_cons_self
    have hls' : AllSh Shape.isRLu R := fun y hy => hls y (List.mem_cons_of_mem _ hy)
    rcases classifyRL hx h₀ with ⟨v', rfl, rfl⟩ | ⟨u', rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨B, L₁, R', C, rfl, hS, hC⟩ :=
        ih (u ++ g.cod ++ v') R₀ hls' ht (by simpa [List.append_assoc] using h)
      exact ⟨(u, g, v' ++ dn j :: R₀) :: B, L₁, R', C, rfl, Sep.left u v' R₀ g hS, hC⟩
    · obtain ⟨B, L₁, R', C, rfl, hS, hC⟩ :=
        ih L (u' ++ g.cod ++ v) hls' ht (by simpa [List.append_assoc] using h)
      exact ⟨(L ++ dn j :: u', g, v) :: B, L₁, R', C, rfl, Sep.right L u' v g hS, hC⟩
    · exact ⟨[], u, v, R, rfl, Sep.nil _ _, by simpa using h⟩

/-- The mirror of `findPartnerRL`, type `LR`: the partner cap is `F_j E_j → 1`. -/
theorem findPartnerLR (j : I) : ∀ (R : List (LayerData I)) (L R₀ : List (Letter I))
    {t : List (Letter I)}, AllSh Shape.isLRu R → Positive t → SChain (L ++ dn j :: R₀) R t →
    ∃ (B : List (LayerData I)) (L' R₁ : List (Letter I)) (C : List (LayerData I)),
      R = B ++ (L', Shape.cap (up j), R₁) :: C ∧ Sep j L R₀ B L' (up j :: R₁) ∧
        SChain (L' ++ R₁) C t := by
  intro R
  induction R with
  | nil =>
    intro L R₀ t _ ht h
    exact (not_positive_dn (h ▸ ht)).elim
  | cons x R ih =>
    intro L R₀ t hls ht h
    obtain ⟨u, g, v⟩ := x
    obtain ⟨h₀, h⟩ := h
    have hx : g.isLRu = true := hls _ List.mem_cons_self
    have hls' : AllSh Shape.isLRu R := fun y hy => hls y (List.mem_cons_of_mem _ hy)
    rcases classifyLR hx h₀ with ⟨v', rfl, rfl⟩ | ⟨u', rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨B, L', R₁, C, rfl, hS, hC⟩ :=
        ih (u ++ g.cod ++ v') R₀ hls' ht (by simpa [List.append_assoc] using h)
      exact ⟨(u, g, v' ++ dn j :: R₀) :: B, L', R₁, C, rfl, Sep.left u v' R₀ g hS, hC⟩
    · obtain ⟨B, L', R₁, C, rfl, hS, hC⟩ :=
        ih L (u' ++ g.cod ++ v) hls' ht (by simpa [List.append_assoc] using h)
      exact ⟨(L ++ dn j :: u', g, v) :: B, L', R₁, C, rfl, Sep.right L u' v g hS, hC⟩
    · exact ⟨[], L, v, R, rfl, Sep.nil _ _, by simpa using h⟩

/-! ## Removing a downward strand -/

theorem dg_list_eq {μ : X} {s t : List (Letter I)} {L L' : List (LayerData I)} (h : L = L') :
    dg RD k μ s t L = dg RD k μ s t L' := by rw [h]

theorem allSh_of_mem {p : Shape I → Bool} {a b : List (LayerData I)} (h : AllSh p b)
    (hab : ∀ x ∈ a, x ∈ b) : AllSh p a := fun x hx => h x (hab x hx)

/-- **Elimination of downward strands** (type `RL`): a rotated monotone diagram of type `RL`
between upward sequences equals an upward diagram. By induction on the number of cups and caps:
the downward leg of the first cup is untouched until its partner cap (`findPartnerRL`); the
layers in between are moved below the cup or above the cap (`Sep.dg_eq`, interchange law), and
the cup and the cap cancel by a zigzag relation. -/
theorem elimRL : ∀ (n : ℕ) (ls : List (LayerData I)) {s t : List (Letter I)}, ncc ls < n →
    AllSh Shape.isRLu ls → Positive s → Positive t → SChain s ls t →
    ∃ A : List (LayerData I), Upward A ∧ SChain s A t ∧
      ∀ μ : X, dg RD k μ s t ls = dg RD k μ s t A := by
  intro n
  induction n with
  | zero => intro ls s t hn; exact absurd hn (Nat.not_lt_zero _)
  | succ n ih =>
    intro ls s t hn hls hs ht h
    rcases firstCupRL ls hls hs h with hup | ⟨A₀, w₁, w₂, j, R, rfl, -, hA₀⟩
    · exact ⟨ls, hup, h, fun μ => rfl⟩
    have hR : SChain (w₁ ++ dn j :: up j :: w₂) R t := by
      have h' := (sChain_append_iff A₀ _ _ hA₀).1 h
      simpa using h'.2
    have hlsR : AllSh Shape.isRLu R := allSh_of_mem hls (fun y hy => by simp [hy])
    obtain ⟨B, L₁, R', C, rfl, hS, hC⟩ := findPartnerRL j R w₁ (up j :: w₂) hlsR ht hR
    obtain ⟨BL, BR, hBL, hBR, hp, hd⟩ := hS.dg_eq (RD := RD) (k := k)
    have hB : AllSh Shape.isRLu B := allSh_of_mem hls (fun y hy => by simp [hy])
    have hBLR : AllSh Shape.isRLu (BL ++ BR) := AllSh.of_perm hp hB
    have hls' : AllSh Shape.isRLu (A₀ ++ BL.map (whL [] w₂) ++ BR.map (whL L₁ []) ++ C) := by
      refine ((AllSh.append (allSh_of_mem hls (fun y hy => by simp [hy]))
        ((hBLR.of_append_left).map_whL _ _)).append ((hBLR.of_append_right).map_whL _ _)).append
        (allSh_of_mem hls (fun y hy => by simp [hy]))
    have hn' : ncc (A₀ ++ BL.map (whL [] w₂) ++ BR.map (whL L₁ []) ++ C) < n := by
      have e1 := ncc_eq_of_perm hp
      simp only [ncc_append, ncc_map_whL] at e1 ⊢
      simp only [ncc_append, ncc_cons, Shape.isCupCap, if_true] at hn
      omega
    have h1 : SChain (w₁ ++ w₂) (BL.map (whL [] w₂)) (L₁ ++ up j :: w₂) := by
      simpa using hBL.whisk [] w₂
    have h2 : SChain (L₁ ++ up j :: w₂) (BR.map (whL L₁ [])) (L₁ ++ R') := by
      simpa using hBR.whisk L₁ []
    have h' : SChain s (A₀ ++ BL.map (whL [] w₂) ++ BR.map (whL L₁ []) ++ C) t :=
      ((hA₀.append h1).append h2).append hC
    obtain ⟨A, hAu, hA, hE⟩ := ih _ hn' hls' hs ht h'
    refine ⟨A, hAu, hA, fun μ => ?_⟩
    rw [← hE μ]
    have ei1 := dg_interchange (RD := RD) (k := k) (μ := μ) (S := s) (T := t) A₀
      (BR.map (whL (L₁ ++ [up j] ++ [dn j]) []) ++ ([(L₁, .cap (dn j), R')] ++ C)) hBL
      (B := [([], .cup (dn j), w₂)]) (t := w₂) (t' := dn j :: up j :: w₂) ⟨by simp, by simp⟩
    have ei2 := dg_interchange (RD := RD) (k := k) (μ := μ) (S := s) (T := t)
      (A₀ ++ BL.map (whL [] w₂) ++ [(L₁ ++ [up j], .cup (dn j), w₂)]) C
      (A := [(L₁, .cap (dn j), [])]) (s := L₁ ++ [up j, dn j]) (s' := L₁)
      ⟨by simp, by simp⟩ hBR
    have hz := dg_step RD k μ (s₀ := s) (t₀ := t) (A₀ ++ BL.map (whL [] w₂))
      (BR.map (whL L₁ []) ++ C) L₁ w₂ (dg_zigR' RD k (wt RD μ w₂) (dn j))
      (by simpa using hA₀.append h1) (by simpa using h2.append hC) rfl rfl
    calc dg RD k μ s t (A₀ ++ (w₁, Shape.cup (dn j), w₂) :: (B ++ (L₁, Shape.cap (dn j), R') :: C))
        = dg RD k μ s t ((A₀ ++ [(w₁, .cup (dn j), w₂)]) ++ B ++
            ([(L₁, .cap (dn j), R')] ++ C)) := dg_list_eq (by simp)
      _ = dg RD k μ s t ((A₀ ++ [(w₁, .cup (dn j), w₂)]) ++
            BL.map (whL [] (dn j :: up j :: w₂)) ++ BR.map (whL (L₁ ++ [up j] ++ [dn j]) []) ++
              ([(L₁, .cap (dn j), R')] ++ C)) := hd μ s t _ _
      _ = dg RD k μ s t (A₀ ++ BL.map (whL [] w₂) ++
            [([], Shape.cup (dn j), w₂)].map (whL (L₁ ++ [up j]) []) ++
              (BR.map (whL (L₁ ++ [up j] ++ [dn j]) []) ++ ([(L₁, .cap (dn j), R')] ++ C))) :=
          (dg_list_eq (by simp)).trans ei1.symm
      _ = dg RD k μ s t (A₀ ++ BL.map (whL [] w₂) ++ [(L₁ ++ [up j], .cup (dn j), w₂)] ++
            [(L₁, Shape.cap (dn j), [])].map (whL [] (up j :: w₂)) ++ BR.map (whL L₁ []) ++ C) :=
          (dg_list_eq (by simp)).trans ei2.symm
      _ = dg RD k μ s t (A₀ ++ BL.map (whL [] w₂) ++ [].map (whL L₁ w₂) ++
            (BR.map (whL L₁ []) ++ C)) := (dg_list_eq (by simp)).trans hz
      _ = dg RD k μ s t (A₀ ++ BL.map (whL [] w₂) ++ BR.map (whL L₁ []) ++ C) :=
          dg_list_eq (by simp)

/-- **Elimination of downward strands** (type `LR`), the mirror of `elimRL`: the partner cap is
`F_j E_j → 1` and the zigzag is the other one. -/
theorem elimLR : ∀ (n : ℕ) (ls : List (LayerData I)) {s t : List (Letter I)}, ncc ls < n →
    AllSh Shape.isLRu ls → Positive s → Positive t → SChain s ls t →
    ∃ A : List (LayerData I), Upward A ∧ SChain s A t ∧
      ∀ μ : X, dg RD k μ s t ls = dg RD k μ s t A := by
  intro n
  induction n with
  | zero => intro ls s t hn; exact absurd hn (Nat.not_lt_zero _)
  | succ n ih =>
    intro ls s t hn hls hs ht h
    rcases firstCupLR ls hls hs h with hup | ⟨A₀, w₁, w₂, j, R, rfl, -, hA₀⟩
    · exact ⟨ls, hup, h, fun μ => rfl⟩
    have hR : SChain ((w₁ ++ [up j]) ++ dn j :: w₂) R t := by
      have h' := (sChain_append_iff A₀ _ _ hA₀).1 h
      simpa using h'.2
    have hlsR : AllSh Shape.isLRu R := allSh_of_mem hls (fun y hy => by simp [hy])
    obtain ⟨B, L', R₁, C, rfl, hS, hC⟩ := findPartnerLR j R (w₁ ++ [up j]) w₂ hlsR ht hR
    obtain ⟨BL, BR, hBL, hBR, hp, hd⟩ := hS.dg_eq (RD := RD) (k := k)
    have hB : AllSh Shape.isLRu B := allSh_of_mem hls (fun y hy => by simp [hy])
    have hBLR : AllSh Shape.isLRu (BL ++ BR) := AllSh.of_perm hp hB
    have hls' : AllSh Shape.isLRu (A₀ ++ BR.map (whL w₁ []) ++ BL.map (whL [] R₁) ++ C) := by
      refine ((AllSh.append (allSh_of_mem hls (fun y hy => by simp [hy]))
        ((hBLR.of_append_right).map_whL _ _)).append ((hBLR.of_append_left).map_whL _ _)).append
        (allSh_of_mem hls (fun y hy => by simp [hy]))
    have hn' : ncc (A₀ ++ BR.map (whL w₁ []) ++ BL.map (whL [] R₁) ++ C) < n := by
      have e1 := ncc_eq_of_perm hp
      simp only [ncc_append, ncc_map_whL] at e1 ⊢
      simp only [ncc_append, ncc_cons, Shape.isCupCap, if_true] at hn
      omega
    have h1 : SChain (w₁ ++ w₂) (BR.map (whL w₁ [])) (w₁ ++ up j :: R₁) := by
      simpa using hBR.whisk w₁ []
    have h2 : SChain (w₁ ++ up j :: R₁) (BL.map (whL [] R₁)) (L' ++ R₁) := by
      simpa using hBL.whisk [] R₁
    have h' : SChain s (A₀ ++ BR.map (whL w₁ []) ++ BL.map (whL [] R₁) ++ C) t :=
      ((hA₀.append h1).append h2).append hC
    obtain ⟨A, hAu, hA, hE⟩ := ih _ hn' hls' hs ht h'
    refine ⟨A, hAu, hA, fun μ => ?_⟩
    rw [← hE μ]
    have ei1 := dg_interchange (RD := RD) (k := k) (μ := μ) (S := s) (T := t)
      (A₀ ++ [(w₁, .cup (up j), w₂)]) ([(L', .cap (up j), R₁)] ++ C) hBL
      (B := BR.map (whL [dn j] [])) (t := dn j :: w₂) (t' := dn j :: up j :: R₁)
      (by simpa using hBR.whisk [dn j] [])
    have ei2 := dg_interchange (RD := RD) (k := k) (μ := μ) (S := s) (T := t) A₀
      (BL.map (whL [] (dn j :: up j :: R₁)) ++ ([(L', .cap (up j), R₁)] ++ C))
      (A := [(w₁, .cup (up j), [])]) (s := w₁) (s' := w₁ ++ [up j, dn j])
      ⟨by simp, by simp⟩ hBR
    have ei3 := dg_interchange (RD := RD) (k := k) (μ := μ) (S := s) (T := t)
      (A₀ ++ BR.map (whL w₁ []) ++ [(w₁, .cup (up j), up j :: R₁)]) C hBL
      (B := [([], .cap (up j), R₁)]) (t := dn j :: up j :: R₁) (t' := R₁) ⟨by simp, by simp⟩
    have hz := dg_step RD k μ (s₀ := s) (t₀ := t) (A₀ ++ BR.map (whL w₁ []))
      (BL.map (whL [] R₁) ++ C) w₁ R₁ (dg_zigL' RD k (wt RD μ R₁) (up j))
      (by simpa using hA₀.append h1) (by simpa using h2.append hC) rfl rfl
    calc dg RD k μ s t (A₀ ++ (w₁, Shape.cup (up j), w₂) :: (B ++ (L', Shape.cap (up j), R₁) :: C))
        = dg RD k μ s t ((A₀ ++ [(w₁, .cup (up j), w₂)]) ++ B ++
            ([(L', .cap (up j), R₁)] ++ C)) := dg_list_eq (by simp)
      _ = dg RD k μ s t ((A₀ ++ [(w₁, .cup (up j), w₂)]) ++
            BL.map (whL [] (dn j :: w₂)) ++ BR.map (whL (L' ++ [dn j]) []) ++
              ([(L', .cap (up j), R₁)] ++ C)) := hd μ s t _ _
      _ = dg RD k μ s t ((A₀ ++ [(w₁, .cup (up j), w₂)]) ++
            (BR.map (whL [dn j] [])).map (whL (w₁ ++ [up j]) []) ++
              BL.map (whL [] (dn j :: up j :: R₁)) ++ ([(L', .cap (up j), R₁)] ++ C)) :=
          (dg_list_eq (by simp)).trans ei1
      _ = dg RD k μ s t (A₀ ++ [(w₁, Shape.cup (up j), [])].map (whL [] w₂) ++
            BR.map (whL (w₁ ++ [up j, dn j]) []) ++
              (BL.map (whL [] (dn j :: up j :: R₁)) ++ ([(L', .cap (up j), R₁)] ++ C))) :=
          dg_list_eq (by simp)
      _ = dg RD k μ s t (A₀ ++ BR.map (whL w₁ []) ++
            [(w₁, Shape.cup (up j), [])].map (whL [] (up j :: R₁)) ++
              (BL.map (whL [] (dn j :: up j :: R₁)) ++ ([(L', .cap (up j), R₁)] ++ C))) := ei2
      _ = dg RD k μ s t ((A₀ ++ BR.map (whL w₁ []) ++ [(w₁, .cup (up j), up j :: R₁)]) ++
            BL.map (whL [] (dn j :: up j :: R₁)) ++ [([], Shape.cap (up j), R₁)].map (whL L' []) ++
              C) := dg_list_eq (by simp)
      _ = dg RD k μ s t ((A₀ ++ BR.map (whL w₁ []) ++ [(w₁, .cup (up j), up j :: R₁)]) ++
            [([], Shape.cap (up j), R₁)].map (whL (w₁ ++ [up j]) []) ++ BL.map (whL [] R₁) ++
              C) := ei3
      _ = dg RD k μ s t (A₀ ++ BR.map (whL w₁ []) ++
            [([], Shape.cup (up j), [up j]), ([up j], Shape.cap (up j), [])].map (whL w₁ R₁) ++
              (BL.map (whL [] R₁) ++ C)) := dg_list_eq (by simp)
      _ = dg RD k μ s t (A₀ ++ BR.map (whL w₁ []) ++ [].map (whL w₁ R₁) ++
            (BL.map (whL [] R₁) ++ C)) := hz
      _ = dg RD k μ s t (A₀ ++ BR.map (whL w₁ []) ++ BL.map (whL [] R₁) ++ C) :=
          dg_list_eq (by simp)


/-! ## Rotating downward dots and crossings -/

/-- Downward dots and crossings rotated into upward ones by cups `1 → F E` and caps `E F → 1`
(KL III (3.3), `eq_cyclic_cross-gen`, left-hand pictures); other layers are unchanged. -/
def rotRL : LayerData I → List (LayerData I)
  | (u, .dot (false, i), v) =>
    [(u, .cup (dn i), dn i :: v), (u ++ [dn i], .dot (up i), dn i :: v),
      (u ++ [dn i], .cap (dn i), v)]
  | (u, .cross false j i, v) =>
    [([], .cup (dn i), [dn j, dn i]), ([dn i], .cup (dn j), [up i, dn j, dn i]),
      ([dn i, dn j], .cross true j i, [dn j, dn i]), ([dn i, dn j, up i], .cap (dn j), [dn i]),
      ([dn i, dn j], .cap (dn i), [])].map (whL u v)
  | x => [x]

/-- Downward dots and crossings rotated into upward ones by cups `1 → E F` and caps `F E → 1`
(KL III (3.3), `eq_cyclic_cross-gen`, right-hand pictures); other layers are unchanged. -/
def rotLR : LayerData I → List (LayerData I)
  | (u, .dot (false, i), v) =>
    [(u ++ [dn i], .cup (up i), v), (u ++ [dn i], .dot (up i), dn i :: v),
      (u, .cap (up i), dn i :: v)]
  | (u, .cross false j i, v) =>
    [([dn j, dn i], .cup (up j), []), ([dn j, dn i, up j], .cup (up i), [dn j]),
      ([dn j, dn i], .cross true j i, [dn i, dn j]), ([dn j], .cap (up i), [up j, dn i, dn j]),
      ([], .cap (up j), [dn i, dn j])].map (whL u v)
  | x => [x]

theorem allSh_rotRL (x : LayerData I) (hx : x.2.1.isRL = true) : AllSh Shape.isRLu (rotRL x) := by
  obtain ⟨u, g, v⟩ := x
  cases g with
  | dot l =>
    obtain ⟨b, i⟩ := l
    cases b <;> simp [rotRL, AllSh, Shape.isRLu]
  | cross ε a c =>
    cases ε <;> simp [rotRL, AllSh, Shape.isRLu, whL]
  | cup l =>
    obtain ⟨b, i⟩ := l
    cases b <;> simp_all [rotRL, AllSh, Shape.isRLu, Shape.isRL]
  | cap l =>
    obtain ⟨b, i⟩ := l
    cases b <;> simp_all [rotRL, AllSh, Shape.isRLu, Shape.isRL]

theorem allSh_rotLR (x : LayerData I) (hx : x.2.1.isLR = true) : AllSh Shape.isLRu (rotLR x) := by
  obtain ⟨u, g, v⟩ := x
  cases g with
  | dot l =>
    obtain ⟨b, i⟩ := l
    cases b <;> simp [rotLR, AllSh, Shape.isLRu]
  | cross ε a c =>
    cases ε <;> simp [rotLR, AllSh, Shape.isLRu, whL]
  | cup l =>
    obtain ⟨b, i⟩ := l
    cases b <;> simp_all [rotLR, AllSh, Shape.isLRu, Shape.isLR]
  | cap l =>
    obtain ⟨b, i⟩ := l
    cases b <;> simp_all [rotLR, AllSh, Shape.isLRu, Shape.isLR]

theorem rotRL_dg (x : LayerData I) {s t : List (Letter I)} (h : SChain s [x] t) :
    SChain s (rotRL x) t ∧ ∀ μ : X, dg RD k μ s t [x] = dg RD k μ s t (rotRL x) := by
  obtain ⟨u, g, v⟩ := x
  obtain ⟨rfl, rfl⟩ := h
  cases g with
  | dot l =>
    obtain ⟨b, i⟩ := l
    cases b
    · refine ⟨by simp [rotRL], fun μ => ?_⟩
      exact dg_step RD k μ [] [] u v (dg_cycDotL RD k i (wt RD μ v)) (by simp) (by simp)
        (by simp) (by simp [rotRL])
    · exact ⟨by simp [rotRL], fun μ => by simp [rotRL]⟩
  | cross ε a c =>
    cases ε
    · refine ⟨by simp [rotRL], fun μ => ?_⟩
      exact dg_step RD k μ [] [] u v (dg_cycCrossL RD k a c (wt RD μ v)) (by simp) (by simp)
        (by simp) (by simp [rotRL])
    · exact ⟨by simp [rotRL], fun μ => by simp [rotRL]⟩
  | cup l => exact ⟨by simp [rotRL], fun μ => by simp [rotRL]⟩
  | cap l => exact ⟨by simp [rotRL], fun μ => by simp [rotRL]⟩

theorem rotLR_dg (x : LayerData I) {s t : List (Letter I)} (h : SChain s [x] t) :
    SChain s (rotLR x) t ∧ ∀ μ : X, dg RD k μ s t [x] = dg RD k μ s t (rotLR x) := by
  obtain ⟨u, g, v⟩ := x
  obtain ⟨rfl, rfl⟩ := h
  cases g with
  | dot l =>
    obtain ⟨b, i⟩ := l
    cases b
    · refine ⟨by simp [rotLR], fun μ => ?_⟩
      exact dg_step RD k μ [] [] u v (dg_cycDotR RD k i (wt RD μ v)) (by simp) (by simp)
        (by simp) (by simp [rotLR])
    · exact ⟨by simp [rotLR], fun μ => by simp [rotLR]⟩
  | cross ε a c =>
    cases ε
    · refine ⟨by simp [rotLR], fun μ => ?_⟩
      exact dg_step RD k μ [] [] u v (dg_cycCrossR RD k a c (wt RD μ v)) (by simp) (by simp)
        (by simp) (by simp [rotLR])
    · exact ⟨by simp [rotLR], fun μ => by simp [rotLR]⟩
  | cup l => exact ⟨by simp [rotLR], fun μ => by simp [rotLR]⟩
  | cap l => exact ⟨by simp [rotLR], fun μ => by simp [rotLR]⟩

/-- Rotation of all layers. -/
def rotAll (r : LayerData I → List (LayerData I)) : List (LayerData I) → List (LayerData I)
  | [] => []
  | x :: ls => r x ++ rotAll r ls

theorem rotAll_dg (r : LayerData I → List (LayerData I))
    (hr : ∀ (x : LayerData I) {s t : List (Letter I)}, SChain s [x] t →
      SChain s (r x) t ∧ ∀ μ : X, dg RD k μ s t [x] = dg RD k μ s t (r x)) :
    ∀ (ls : List (LayerData I)) {s t : List (Letter I)}, SChain s ls t →
      SChain s (rotAll r ls) t ∧ ∀ μ : X, dg RD k μ s t ls = dg RD k μ s t (rotAll r ls) := by
  intro ls
  induction ls with
  | nil => intro s t h; exact ⟨h, fun μ => rfl⟩
  | cons x ls ih =>
    intro s t h
    have hx : SChain s [x] (x.1 ++ x.2.1.cod ++ x.2.2) := ⟨h.1, rfl⟩
    obtain ⟨hr1, hr2⟩ := hr x hx
    obtain ⟨hi1, hi2⟩ := ih h.2
    refine ⟨hr1.append hi1, fun μ => ?_⟩
    rw [show x :: ls = [x] ++ ls from rfl, ← dg_comp hx h.2, hr2 μ, hi2 μ, dg_comp hr1 hi1]
    rfl

theorem allSh_rotAll {p q : Shape I → Bool} (r : LayerData I → List (LayerData I))
    (hr : ∀ x : LayerData I, p x.2.1 = true → AllSh q (r x)) :
    ∀ ls : List (LayerData I), AllSh p ls → AllSh q (rotAll r ls) := by
  intro ls
  induction ls with
  | nil => intro _ y hy; simp [rotAll] at hy
  | cons x ls ih =>
    intro h
    exact (hr x (h x List.mem_cons_self)).append (ih fun y hy => h y (List.mem_cons_of_mem _ hy))

/-! ## Main results -/

/-- **A monotone diagram of type `RL` between upward sequences equals an upward diagram**: all
cups are `1 → F_j E_j` and all caps `E_j F_j → 1` (dots and crossings arbitrary). -/
theorem straightenRL {s t : List (Letter I)} (hs : Positive s) (ht : Positive t)
    {ls : List (LayerData I)} (hls : AllSh Shape.isRL ls) (h : SChain s ls t) :
    ∃ A : List (LayerData I), Upward A ∧ SChain s A t ∧
      ∀ μ : X, dg RD k μ s t ls = dg RD k μ s t A := by
  obtain ⟨h1, h2⟩ := rotAll_dg (RD := RD) (k := k) rotRL (fun x _ _ hx => rotRL_dg x hx) ls h
  obtain ⟨A, hA, hc, he⟩ := elimRL (RD := RD) (k := k) _ (rotAll rotRL ls) (Nat.lt_succ_self _)
    (allSh_rotAll rotRL allSh_rotRL ls hls) hs ht h1
  exact ⟨A, hA, hc, fun μ => (h2 μ).trans (he μ)⟩

/-- **A monotone diagram of type `LR` between upward sequences equals an upward diagram**: all
cups are `1 → E_j F_j` and all caps `F_j E_j → 1` (dots and crossings arbitrary). -/
theorem straightenLR {s t : List (Letter I)} (hs : Positive s) (ht : Positive t)
    {ls : List (LayerData I)} (hls : AllSh Shape.isLR ls) (h : SChain s ls t) :
    ∃ A : List (LayerData I), Upward A ∧ SChain s A t ∧
      ∀ μ : X, dg RD k μ s t ls = dg RD k μ s t A := by
  obtain ⟨h1, h2⟩ := rotAll_dg (RD := RD) (k := k) rotLR (fun x _ _ hx => rotLR_dg x hx) ls h
  obtain ⟨A, hA, hc, he⟩ := elimLR (RD := RD) (k := k) _ (rotAll rotLR ls) (Nat.lt_succ_self _)
    (allSh_rotAll rotLR allSh_rotLR ls hls) hs ht h1
  exact ⟨A, hA, hc, fun μ => (h2 μ).trans (he μ)⟩

theorem dg_upward_mem_upSpan {μ : X} {s t : List (Letter I)} {A : List (LayerData I)}
    (hA : Upward A) (h : SChain s A t) : dg RD k μ s t A ∈ upSpan RD k μ s t :=
  Submodule.subset_span ⟨A, 𝟙 _, hA, h, IsBub.id, by rw [bubAt_id, Category.comp_id]⟩

theorem straightenRL_mem_upSpan (μ : X) {s t : List (Letter I)} (hs : Positive s)
    (ht : Positive t) {ls : List (LayerData I)} (hls : AllSh Shape.isRL ls) (h : SChain s ls t) :
    dg RD k μ s t ls ∈ upSpan RD k μ s t := by
  obtain ⟨A, hA, hc, he⟩ := straightenRL (RD := RD) (k := k) hs ht hls h
  rw [he μ]
  exact dg_upward_mem_upSpan hA hc

theorem straightenLR_mem_upSpan (μ : X) {s t : List (Letter I)} (hs : Positive s)
    (ht : Positive t) {ls : List (LayerData I)} (hls : AllSh Shape.isLR ls) (h : SChain s ls t) :
    dg RD k μ s t ls ∈ upSpan RD k μ s t := by
  obtain ⟨A, hA, hc, he⟩ := straightenLR (RD := RD) (k := k) hs ht hls h
  rw [he μ]
  exact dg_upward_mem_upSpan hA hc

end Categorification.KL3.Diagram

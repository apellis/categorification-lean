/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.Presentation

/-!
# Lists of layers of normal-form diagrams of `U`

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.1.

The combinatorics of lists of layers `(u, g, v)` (see `Categorification.Diagrams.KL3.Basic`)
that does not depend on the relations of `U`: placement of a layer between strands (`whL`),
chaining (`SChain`), the exchange of two layers (`swapLR`, `swapRL`), the named lists of layers
of crossings, bubbles and the decompositions, and the tactics `schain` (typing side conditions),
`lnf` and `dnorm` (normal form of lists of layers). The calculus of diagram classes built on it
is `Categorification.Diagrams.KL3.NormalForm`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y)

/-! ## Whiskering and chaining of layer data -/

/-- The layer datum `x` placed between the strands `u` (left) and `v` (right). -/
def whL (u v : List (Letter I)) (x : LayerData I) : LayerData I := (u ++ x.1, x.2.1, x.2.2 ++ v)

@[simp] theorem whL_nil_nil (x : LayerData I) : whL [] [] x = x := by
  obtain ⟨a, g, b⟩ := x; simp [whL]

@[simp] theorem map_whL_nil_nil (l : List (LayerData I)) : l.map (whL [] []) = l := by
  simp [List.map_congr_left (fun x _ => whL_nil_nil x)]

theorem SChain.whisk {s t : List (Letter I)} {ls : List (LayerData I)} (h : SChain s ls t)
    (u v : List (Letter I)) : SChain (u ++ s ++ v) (ls.map (whL u v)) (u ++ t ++ v) := by
  induction ls generalizing s with
  | nil => cases h; rfl
  | cons x ls ih =>
    obtain ⟨rfl, h⟩ := h
    refine ⟨by simp [whL], ?_⟩
    have := ih h
    simpa [whL] using this

/-- The weight of the left region is constant along a chain of layers. -/
theorem SChain.wt_eq (ν : X) {s t : List (Letter I)} {ls : List (LayerData I)} (h : SChain s ls t) :
    wt RD ν t = wt RD ν s := by
  induction ls generalizing s with
  | nil => cases h; rfl
  | cons x ls ih =>
    obtain ⟨rfl, h⟩ := h
    rw [ih h, wt_lay_dom]

theorem SChain.wt_mem (ν : X) {s t : List (Letter I)} {ls : List (LayerData I)}
    (h : SChain s ls t) : ∀ x ∈ ls, wt RD ν (x.1 ++ x.2.1.dom ++ x.2.2) = wt RD ν s := by
  induction ls generalizing s with
  | nil => simp
  | cons x ls ih =>
    obtain ⟨rfl, h⟩ := h
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · rfl
    · rw [ih h y hy, wt_lay_dom]

theorem SChain.eq_target {s t t' : List (Letter I)} {ls : List (LayerData I)} (h : SChain s ls t)
    (h' : SChain s ls t') : t = t' := by
  induction ls generalizing s with
  | nil => exact h.symm.trans h'
  | cons x ls ih => exact ih h.2 h'.2

theorem SChain.split {s t : List (Letter I)} {ls ms : List (LayerData I)} (h : SChain s (ls ++ ms) t) :
    ∃ a, SChain s ls a ∧ SChain a ms t := by
  induction ls generalizing s with
  | nil => exact ⟨s, rfl, h⟩
  | cons x ls ih =>
    obtain ⟨rfl, h⟩ := h
    obtain ⟨a, h₁, h₂⟩ := ih h
    exact ⟨a, ⟨rfl, h₁⟩, h₂⟩

/-- A placed layer in normal form. -/
theorem lay_whisker (μ : X) (u v a : List (Letter I)) (g : Shape I) (b s : List (Letter I))
    (hs : wt RD (wt RD μ v) (a ++ g.dom ++ b) = wt RD (wt RD μ v) s) :
    (lay RD (wt RD μ v) a g b).whisker (ob RD (wt RD (wt RD μ v) s) u) (wd RD μ v) =
      lay RD μ (u ++ a) g (b ++ v) := by
  have e₁ : wt RD μ (g.dom ++ b ++ v) = wt RD (wt RD μ v) (g.dom ++ b) := by
    simp only [List.append_assoc, wt_append]
  have hs' : wt RD (wt RD (wt RD μ v) (g.dom ++ b)) a = wt RD (wt RD μ v) s := by
    rw [← wt_append, ← List.append_assoc]; exact hs
  refine Layer.ext ?_ ?_ ?_ ?_
  · simp only [Layer.whisker, ob_start, lay, List.append_assoc, wt_append] at hs ⊢
    rw [hs]
  · simp only [wt_append] at hs'
    simp only [Layer.whisker, ob_word, lay, List.append_assoc, wd_append, wt_append]
    rw [hs']
  · simp only [Layer.whisker, lay, wt_append]
  · simp only [Layer.whisker, lay, wd_append]

theorem layList_whisker (μ : X) (u v : List (Letter I)) {s t : List (Letter I)}
    {ls : List (LayerData I)} (h : SChain s ls t) :
    (layList RD (wt RD μ v) ls).map (·.whisker (ob RD (wt RD (wt RD μ v) s) u) (wd RD μ v)) =
      layList RD μ (ls.map (whL u v)) := by
  have hm := h.wt_mem RD (wt RD μ v)
  simp only [layList, List.map_map]
  refine List.map_congr_left fun x hx => ?_
  exact lay_whisker RD μ u v x.1 x.2.1 x.2.2 s (hm x hx)

theorem whiskerOK_ob (μ : X) (u v s : List (Letter I)) :
    (ob RD (wt RD μ v) s).WhiskerOK (ob RD (wt RD (wt RD μ v) s) u) (wd RD μ v) :=
  ⟨ok_wd RD _ u, endR_wd RD _ u, by rw [ob_endR]; exact ok_wd RD μ v⟩

theorem ob_whisker (μ : X) (u v s s' : List (Letter I))
    (hs : wt RD (wt RD μ v) s' = wt RD (wt RD μ v) s) :
    (ob RD (wt RD μ v) s').whisker (ob RD (wt RD (wt RD μ v) s) u) (wd RD μ v) =
      ob RD μ (u ++ s' ++ v) := by
  refine Obj.ext ?_ ?_
  · simp only [Obj.whisker_start, ob_start, List.append_assoc, wt_append, hs]
  · simp only [Obj.whisker_word, ob_word, List.append_assoc, wd_append, wt_append, hs]

variable {RD} in
/-- The objects `E_{u s v} 1_μ` and the whiskering of `E_s 1_{μ + v_X}`. -/
abbrev obW (μ : X) (u v s : List (Letter I)) :=
  (ob RD (wt RD μ v) s).whisker (ob RD (wt RD (wt RD μ v) s) u) (wd RD μ v)

theorem SChain.nil' (s : List (Letter I)) : SChain s [] s := rfl

theorem SChain.eq_source {b b' t : List (Letter I)} {ls : List (LayerData I)} (h : SChain b ls t)
    (h' : SChain b' ls t) : b = b' := by
  cases ls with
  | nil => exact h.trans h'.symm
  | cons x ls => exact h.1.trans h'.1.symm

theorem SChain.of_whisk {u v s t : List (Letter I)} {ls : List (LayerData I)}
    (h : SChain (u ++ s ++ v) (ls.map (whL u v)) (u ++ t ++ v)) : SChain s ls t := by
  induction ls generalizing s with
  | nil =>
    have h' : u ++ s ++ v = u ++ t ++ v := h
    simpa using h'
  | cons x ls ih =>
    obtain ⟨h₁, h₂⟩ := h
    have e : s = x.1 ++ x.2.1.dom ++ x.2.2 := by
      have h₁' : u ++ (s ++ v) = u ++ ((x.1 ++ x.2.1.dom ++ x.2.2) ++ v) := by
        simpa [whL, List.append_assoc] using h₁
      exact List.append_cancel_right (List.append_cancel_left h₁')
    subst e
    refine ⟨rfl, ih ?_⟩
    simpa [whL] using h₂

theorem sChain_append_iff {s t : List (Letter I)} (ls ms : List (LayerData I)) (a : List (Letter I))
    (h : SChain s ls a) : SChain s (ls ++ ms) t ↔ SChain a ms t := by
  constructor
  · intro h'
    obtain ⟨b, h₁, h₂⟩ := SChain.split h'
    obtain rfl := h.eq_target h₁
    exact h₂
  · exact h.append

/-- A block of dots (or other generators with equal source and target) does not change the
boundary. -/
theorem sChain_replicate_append {s t : List (Letter I)} (n : ℕ) (x : LayerData I)
    (hx : x.2.1.dom = x.2.1.cod) (ls : List (LayerData I))
    (hs : s = x.1 ++ x.2.1.dom ++ x.2.2) :
    SChain s (List.replicate n x ++ ls) t ↔ SChain s ls t := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, sChain_cons]
    constructor
    · rintro ⟨-, h⟩; rw [← hx, ← hs] at h; exact ih.1 h
    · intro h; exact ⟨hs, by rw [← hx, ← hs]; exact ih.2 h⟩

theorem sChain_replicate {s t : List (Letter I)} (n : ℕ) (x : LayerData I)
    (hx : x.2.1.dom = x.2.1.cod) (hs : s = x.1 ++ x.2.1.dom ++ x.2.2) :
    SChain s (List.replicate n x) t ↔ s = t := by
  have := sChain_replicate_append (t := t) n x hx [] hs
  rwa [List.append_nil] at this

@[simp] theorem sh_dual_add_sh_add (l : Letter I) (ν : X) : sh RD l.dual + (sh RD l + ν) = ν := by
  rw [← add_assoc, sh_dual_add_sh, zero_add]

@[simp] theorem sh_add_sh_dual_add (l : Letter I) (ν : X) : sh RD l + (sh RD l.dual + ν) = ν := by
  rw [← add_assoc, sh_add_sh_dual, zero_add]

@[simp] theorem sh_up_dn_add (i : I) (ν : X) : sh RD (up i) + (sh RD (dn i) + ν) = ν :=
  sh_add_sh_dual_add RD (up i) ν

@[simp] theorem sh_dn_up_add (i : I) (ν : X) : sh RD (dn i) + (sh RD (up i) + ν) = ν :=
  sh_dual_add_sh_add RD (up i) ν

theorem sign_even {a b a' b' : Obj (psig RD)} (f : a ⟶ b) (g : a' ⟶ b') :
    ((-1 : ℤ) ^ (Diagram.oddCount f * Diagram.oddCount g)) = 1 := by
  simp [Diagram.oddCount, Diagram.oddCountList, Signature.IsEven.odd_eq_false]

/-- Closes `SChain s ls t` for explicit lists of layers, possibly containing blocks of dots
`List.replicate n x`. -/
macro "schain" : tactic => `(tactic| (
  try simp only [whL, List.map_append, List.map_cons, List.map_nil, List.map_replicate,
    List.append_assoc, List.cons_append, List.nil_append, List.singleton_append, List.append_nil]
  repeat' (first
    | exact rfl
    | refine ⟨rfl, ?_⟩
    | refine (sChain_replicate_append _ _ (by rfl) _ (by rfl)).2 ?_
    | refine (sChain_replicate _ _ (by rfl) (by rfl)).2 ?_)))

theorem SChain.replicate_of {s : List (Letter I)} {x : LayerData I} (hx : SChain s [x] s)
    (n : ℕ) : SChain s (List.replicate n x) s := by
  induction n with
  | zero => rfl
  | succ n ih => exact hx.append ih

/-- Normal form of lists of layers. -/
macro "lnf" : tactic => `(tactic| simp only [whL, List.map_append, List.map_cons, List.map_nil,
  List.map_replicate, List.cons_append, List.nil_append, List.append_nil, List.singleton_append,
  List.append_assoc])

/-- The layers of the sideways crossing `crossl RD i j : E_i F_j ⟶ F_j E_i`. -/
def crosslL (i j : I) : List (LayerData I) :=
  [([], .cup (dn j), [up i, dn j]), ([dn j], .cross true j i, [dn j]), ([dn j, up i], .cap (dn j), [])]

/-- The layers of the sideways crossing `crossr RD i j : F_j E_i ⟶ E_i F_j`. -/
def crossrL (i j : I) : List (LayerData I) :=
  [([dn j, up i], .cup (up j), []), ([dn j], .cross true i j, [dn j]), ([], .cap (up j), [up i, dn j])]

/-! ## Exchanging two layers -/

theorem list_split_at (L : List (LayerData I)) (n : ℕ) (x y : LayerData I)
    (rest : List (LayerData I)) (hL : L.drop n = x :: y :: rest) :
    L = L.take n ++ [x, y] ++ rest := by
  rw [List.append_assoc, List.cons_append, List.cons_append, List.nil_append, ← hL,
    List.take_append_drop]

/-- Exchange of the layers `x` (below) and `y` (above), the generator of `x` being to the left of
that of `y`: the strands between the two generators are computed from the layers. -/
def swapLR (x y : LayerData I) : List (LayerData I) :=
  [(x.1 ++ x.2.1.dom ++ y.1.drop (x.1.length + x.2.1.cod.length), y.2.1, y.2.2),
    (x.1, x.2.1, y.1.drop (x.1.length + x.2.1.cod.length) ++ y.2.1.cod ++ y.2.2)]

/-- Exchange of the layers `x` (below) and `y` (above), the generator of `x` being to the right
of that of `y`. -/
def swapRL (x y : LayerData I) : List (LayerData I) :=
  [(y.1, y.2.1, x.1.drop (y.1.length + y.2.1.dom.length) ++ x.2.1.dom ++ x.2.2),
    (y.1 ++ y.2.1.cod ++ x.1.drop (y.1.length + y.2.1.dom.length), x.2.1, x.2.2)]

theorem sChain_swap_iff (a m b : List (Letter I)) (g h : Shape I) (s t : List (Letter I)) :
    SChain s [(a, g, m ++ h.dom ++ b), (a ++ g.cod ++ m, h, b)] t ↔
      SChain s [(a ++ g.dom ++ m, h, b), (a, g, m ++ h.cod ++ b)] t := by
  simp only [sChain_cons, sChain_nil, List.append_assoc, true_and]

theorem list_split_at' (L : List (LayerData I)) (n l : ℕ) :
    L = L.take n ++ (L.drop n).take l ++ L.drop (n + l) := by
  rw [List.append_assoc, ← List.drop_drop, List.take_append_drop, List.take_append_drop]

@[simp] theorem Letter.dual_up (i : I) : Letter.dual (up i) = dn i := rfl

@[simp] theorem Letter.dual_dn (i : I) : Letter.dual (dn i) = up i := rfl

/-- Normalizes the lists of layers produced by `dswap` and `dat`. -/
macro "dnorm" : tactic => `(tactic| simp only [swapLR, swapRL, whL, crosslL, crossrL,
  List.take_succ_cons, List.length_map,
  List.take_zero, List.take_nil, List.drop_succ_cons, List.drop_zero, List.drop_nil,
  List.length_cons, List.length_nil, List.length_append, Shape.dom_dot, Shape.dom_cross,
  Shape.dom_cup, Shape.dom_cap, Shape.cod_dot, Shape.cod_cross, Shape.cod_cup, Shape.cod_cap,
  Letter.dual_up, Letter.dual_dn, List.map_cons, List.map_nil, List.cons_append,
  List.nil_append, List.append_nil, List.singleton_append, List.append_assoc, Nat.add_zero,
  Nat.zero_add, Nat.reduceAdd])

/-! ## Named lists of layers -/

/-- The layers of the counterclockwise bubble with `m` dots (`ccwReal`). -/
def ccwLs (i : I) (m : ℕ) : List (LayerData I) :=
  [([], .cup (dn i), [])] ++ List.replicate m ([dn i], .dot (up i), []) ++ [([], .cap (up i), [])]

/-- The layers of the clockwise bubble with `m` dots (`cwReal`). -/
def cwLs (i : I) (m : ℕ) : List (LayerData I) :=
  [([], .cup (up i), [])] ++ List.replicate m ([up i], .dot (dn i), []) ++ [([], .cap (dn i), [])]

theorem sChain_ccwLs (i : I) (m : ℕ) : SChain [] (ccwLs i m) [] := by
  unfold ccwLs; schain

theorem sChain_cwLs (i : I) (m : ℕ) : SChain [] (cwLs i m) [] := by
  unfold cwLs; schain

/-- The layers of `dotCapEF`. -/
def dotCapEFLs (i : I) (m : ℕ) : List (LayerData I) :=
  List.replicate m ([], .dot (up i), [dn i]) ++ [([], .cap (dn i), [])]

/-- The layers of `cupDotEF`. -/
def cupDotEFLs (i : I) (m : ℕ) : List (LayerData I) :=
  [([], .cup (up i), [])] ++ List.replicate m ([up i], .dot (dn i), [])

/-- The layers of `dotCapFE`. -/
def dotCapFELs (i : I) (m : ℕ) : List (LayerData I) :=
  List.replicate m ([], .dot (dn i), [up i]) ++ [([], .cap (up i), [])]

/-- The layers of `cupDotFE`. -/
def cupDotFELs (i : I) (m : ℕ) : List (LayerData I) :=
  [([], .cup (dn i), [])] ++ List.replicate m ([dn i], .dot (up i), [])

-- `schain` also unfolds the named lists of layers of this file.
macro_rules
  | `(tactic| schain) => `(tactic| (
      simp only [dotCapEFLs, cupDotEFLs, dotCapFELs, cupDotFELs, ccwLs, cwLs]
      schain))

end Categorification.KL3.Diagram

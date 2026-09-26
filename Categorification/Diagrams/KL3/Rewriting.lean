/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.SlideCalculus

/-!
# Positional rewriting of normal-form diagrams of `U`

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.1.

Certificate chains in `Categorification.Diagrams.KL3.SlideCalculus` (`dg_step`, `dstep`) name the
layers below and above a rewritten subdiagram explicitly. This file adds a positional front end
in which only the position of the subdiagram in the list of layers is given; the surrounding
layers are computed with `List.take` and `List.drop`:

* `dg_congr_ctx`: a subdiagram with the same typing behaviour and the same class can be replaced
  in any context (no typing side conditions);
* `swapLR`, `swapRL`, `dg_swapLR_at`, `dg_swapRL_at` and the tactic `dswap n`: the interchange
  law for the layers `n` and `n + 1`, the placement of the strands being computed from the
  layers;
* `dg_step_at` and the tactic `dat n u v E`: rewrite the subdiagram starting at the layer `n`
  by the local equation `E`, placed between the strands `u` and `v`;
* `dg_stepL_at`: the same with a right-hand side that is a linear combination;
* `dg_braid`: the braid relation of `R(ν)` (KL III `eq_r3_easy-gen`, `eq_r3_hard-gen` without
  correction term) on upward strands, in normal form;
* `dg_interchange_one`, `dg_interchange`: the interchange law for blocks of layers (a diagram on
  the left strands and a diagram on the right strands can be exchanged), in any context.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {k : Type w} [CommRing k]

/-! ## Replacing a subdiagram in context -/

/-- A subdiagram `A` may be replaced by `B` in any context if `A` and `B` chain between the same
boundaries and have the same class whenever they chain. -/
theorem dg_congr_ctx {μ : X} {A B : List (LayerData I)}
    (hc : ∀ s t, SChain s A t → SChain s B t) (hc' : ∀ s t, SChain s B t → SChain s A t)
    (hd : ∀ s t, SChain s A t → dg RD k μ s t A = dg RD k μ s t B)
    (s₀ t₀ : List (Letter I)) (pre post : List (LayerData I)) :
    dg RD k μ s₀ t₀ (pre ++ A ++ post) = dg RD k μ s₀ t₀ (pre ++ B ++ post) := by
  by_cases h : SChain s₀ (pre ++ A ++ post) t₀
  · obtain ⟨b, h₁, h₂⟩ := SChain.split h
    obtain ⟨a, h₃, h₄⟩ := SChain.split h₁
    rw [← dg_comp h₁ h₂, ← dg_comp h₃ h₄, hd a b h₄, dg_comp h₃ (hc a b h₄),
      dg_comp (h₃.append (hc a b h₄)) h₂]
  · rw [dg_of_not h, dg_of_not]
    intro h'
    obtain ⟨b, h₁, h₂⟩ := SChain.split h'
    obtain ⟨a, h₃, h₄⟩ := SChain.split h₁
    exact h ((h₃.append (hc' a b h₄)).append h₂)

theorem list_split_at (L : List (LayerData I)) (n : ℕ) (x y : LayerData I)
    (rest : List (LayerData I)) (hL : L.drop n = x :: y :: rest) :
    L = L.take n ++ [x, y] ++ rest := by
  rw [List.append_assoc, List.cons_append, List.cons_append, List.nil_append, ← hL,
    List.take_append_drop]

/-! ## The interchange law at a position -/

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

/-- **The interchange law at the position `n`**: the layers `n` (generator on the left) and
`n + 1` (generator on the right) of a normal-form diagram are exchanged. -/
theorem dg_swapLR_at {μ : X} {s t : List (Letter I)} (L : List (LayerData I)) (n : ℕ)
    (x y : LayerData I) (rest : List (LayerData I)) (hL : L.drop n = x :: y :: rest)
    (hx : x.2.2 = y.1.drop (x.1.length + x.2.1.cod.length) ++ y.2.1.dom ++ y.2.2)
    (hy : y.1 = x.1 ++ x.2.1.cod ++ y.1.drop (x.1.length + x.2.1.cod.length)) :
    dg RD k μ s t L = dg RD k μ s t (L.take n ++ swapLR x y ++ rest) := by
  rw [congrArg (dg RD k μ s t) (list_split_at L n x y rest hL)]
  obtain ⟨a, g, r⟩ := x
  obtain ⟨p, h, b⟩ := y
  simp only [swapLR] at hx hy ⊢
  generalize p.drop (a.length + g.cod.length) = m at hx hy ⊢
  subst hx hy
  exact dg_congr_ctx (fun s t => (sChain_swap_iff a m b g h s t).1)
    (fun s t => (sChain_swap_iff a m b g h s t).2) (fun s t _ => dg_swap RD k μ s t a m b g h)
    s t _ _

/-- **The interchange law at the position `n`**: the layers `n` (generator on the right) and
`n + 1` (generator on the left) of a normal-form diagram are exchanged. -/
theorem dg_swapRL_at {μ : X} {s t : List (Letter I)} (L : List (LayerData I)) (n : ℕ)
    (x y : LayerData I) (rest : List (LayerData I)) (hL : L.drop n = x :: y :: rest)
    (hx : x.1 = y.1 ++ y.2.1.dom ++ x.1.drop (y.1.length + y.2.1.dom.length))
    (hy : y.2.2 = x.1.drop (y.1.length + y.2.1.dom.length) ++ x.2.1.cod ++ x.2.2) :
    dg RD k μ s t L = dg RD k μ s t (L.take n ++ swapRL x y ++ rest) := by
  rw [congrArg (dg RD k μ s t) (list_split_at L n x y rest hL)]
  obtain ⟨p, h, b⟩ := x
  obtain ⟨a, g, r⟩ := y
  simp only [swapRL] at hx hy ⊢
  generalize p.drop (a.length + g.dom.length) = m at hx hy ⊢
  subst hx hy
  exact dg_congr_ctx (fun s t => (sChain_swap_iff a m b g h s t).2)
    (fun s t => (sChain_swap_iff a m b g h s t).1)
    (fun s t _ => (dg_swap RD k μ s t a m b g h).symm) s t _ _

/-! ## Local rewriting at a position -/

theorem list_split_at' (L : List (LayerData I)) (n l : ℕ) :
    L = L.take n ++ (L.drop n).take l ++ L.drop (n + l) := by
  rw [List.append_assoc, ← List.drop_drop, List.take_append_drop, List.take_append_drop]

/-- **One step of a certificate chain at a position**: if `dg ν s t A = dg ν s t B`
(`ν = μ + v_X`) and the layers `n, …, n + |A| - 1` of `L` are `A` placed between the strands `u`
and `v`, these layers may be replaced by `B` placed between `u` and `v`. -/
theorem dg_step_at {μ : X} {s₀ t₀ : List (Letter I)} (L : List (LayerData I)) (n : ℕ)
    (u v : List (Letter I)) {s t : List (Letter I)} {A B : List (LayerData I)}
    (E : dg RD k (wt RD μ v) s t A = dg RD k (wt RD μ v) s t B)
    (hpre : SChain s₀ (L.take n) (u ++ s ++ v))
    (hpost : SChain (u ++ t ++ v) (L.drop (n + A.length)) t₀)
    (hL : (L.drop n).take A.length = A.map (whL u v)) :
    dg RD k μ s₀ t₀ L =
      dg RD k μ s₀ t₀ (L.take n ++ B.map (whL u v) ++ L.drop (n + A.length)) :=
  dg_step RD k μ _ _ u v E hpre hpost (by rw [← hL]; exact list_split_at' L n A.length) rfl

/-- One step of a certificate chain at a position, with a linear combination on the right-hand
side (`dg_stepL`). -/
theorem dg_stepL_at {μ : X} {s₀ t₀ : List (Letter I)} (L : List (LayerData I)) (n : ℕ)
    (u v : List (Letter I)) {s t : List (Letter I)} {A : List (LayerData I)}
    {F : (pres RD k).obj (ob RD (wt RD μ v) s) ⟶ (pres RD k).obj (ob RD (wt RD μ v) t)}
    (E : dg RD k (wt RD μ v) s t A = F)
    (hpre : SChain s₀ (L.take n) (u ++ s ++ v))
    (hpost : SChain (u ++ t ++ v) (L.drop (n + A.length)) t₀)
    (hL : (L.drop n).take A.length = A.map (whL u v)) :
    dg RD k μ s₀ t₀ L =
      ctxL RD k μ s₀ t₀ (L.take n) u v (L.drop (n + A.length)) s t F :=
  dg_stepL RD k μ _ _ u v E hpre hpost (by rw [← hL]; exact list_split_at' L n A.length)

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

/-- `dswap n`: exchange the layers `n` and `n + 1` of the left-hand side `dg μ s t L` of the
goal by the interchange law. -/
macro "dswap " n:term:max : tactic => `(tactic| (
  first
    | refine Eq.trans (dg_swapLR_at _ $n _ _ _ (by exact rfl) (by exact rfl) (by exact rfl)) ?_
    | refine Eq.trans (dg_swapRL_at _ $n _ _ _ (by exact rfl) (by exact rfl) (by exact rfl)) ?_
  try dnorm))

/-- `dat n u v E`: rewrite the left-hand side `dg μ s₀ t₀ L` of the goal with the local
equation `E : dg ν s t A = dg ν s t B` placed between the strands `u` and `v`, `A` starting at
the layer `n` of `L`. -/
macro "dat " n:term:max u:term:max v:term:max E:term:max : tactic => `(tactic| (
  refine Eq.trans (dg_step_at _ $n $u $v $E (by (try dnorm); schain) (by (try dnorm); schain)
    (by dnorm)) ?_
  try dnorm))

/-! ## The braid relation on upward strands -/

variable (RD k) in
/-- **KL III `eq_r3_easy-gen`, `eq_r3_hard-gen`** (the cases without correction term, i.e.
unless `c = e ≠ d`): the braid relation `ψ₀ ψ₁ ψ₀ = ψ₁ ψ₀ ψ₁` on upward strands `E_c E_d E_e`,
in normal form (bottom to top). -/
theorem dg_braid (μ : X) (c d e : I) (h : ¬ (c = e ∧ c ≠ d)) :
    dg RD k μ [up c, up d, up e] [up e, up d, up c]
        [([], .cross true c d, [up e]), ([up d], .cross true c e, []),
          ([], .cross true d e, [up c])] =
      dg RD k μ [up c, up d, up e] [up e, up d, up c]
        [([up c], .cross true d e, []), ([], .cross true c e, [up d]),
          ([up e], .cross true c d, [])] := by
  have key := (KLR.Diagram.pres k (KLR.klQ2 k C)).diag_eq_of_rel (.braid c d e h) rfl
  have key' := congrArg (upFunctor RD k μ).map key
  rw [upFunctor_diag, upFunctor_diag, upDiag_eq_dg, upDiag_eq_dg] at key'
  exact key'

/-! ## The interchange law for blocks of layers -/

/-- A layer `(a, g, b)` on the left slides past a list of layers `B` on the strands to its right
(interchange law, in any context). -/
theorem dg_interchange_one {μ : X} {S T : List (Letter I)} (pre post : List (LayerData I))
    (a b : List (Letter I)) (g : Shape I) {t₀ t₁ : List (Letter I)} {B : List (LayerData I)}
    (hB : SChain t₀ B t₁) :
    dg RD k μ S T (pre ++ [(a, g, b ++ t₀)] ++ B.map (whL (a ++ g.cod ++ b) []) ++ post) =
      dg RD k μ S T (pre ++ B.map (whL (a ++ g.dom ++ b) []) ++ [(a, g, b ++ t₁)] ++ post) := by
  induction B generalizing pre t₀ with
  | nil =>
    cases hB
    simp
  | cons y B ih =>
    obtain ⟨c, h, d⟩ := y
    obtain ⟨rfl, hB'⟩ := hB
    have e₁ : pre ++ [(a, g, b ++ (c ++ h.dom ++ d))] ++
        List.map (whL (a ++ g.cod ++ b) []) ((c, h, d) :: B) ++ post =
        pre ++ [(a, g, (b ++ c) ++ h.dom ++ d), (a ++ g.cod ++ (b ++ c), h, d)] ++
          (List.map (whL (a ++ g.cod ++ b) []) B ++ post) := by
      simp [whL, List.append_assoc]
    have e₂ : pre ++ [(a ++ g.dom ++ (b ++ c), h, d), (a, g, (b ++ c) ++ h.cod ++ d)] ++
        (List.map (whL (a ++ g.cod ++ b) []) B ++ post) =
        (pre ++ [(a ++ g.dom ++ b ++ c, h, d)]) ++ [(a, g, b ++ (c ++ h.cod ++ d))] ++
          List.map (whL (a ++ g.cod ++ b) []) B ++ post := by
      simp [List.append_assoc]
    rw [e₁, dg_congr_ctx (fun s t => (sChain_swap_iff a (b ++ c) d g h s t).1)
      (fun s t => (sChain_swap_iff a (b ++ c) d g h s t).2)
      (fun s t _ => dg_swap RD k μ s t a (b ++ c) d g h) S T pre _, e₂, ih _ hB']
    simp [whL, List.append_assoc]

/-- **The interchange law for blocks of layers**: a diagram `A` (from `s` to `s'`) on the left
and a diagram `B` (from `t` to `t'`) on the right can be exchanged, in any context. -/
theorem dg_interchange {μ : X} {S T : List (Letter I)} (pre post : List (LayerData I))
    {s s' t t' : List (Letter I)} {A B : List (LayerData I)} (hA : SChain s A s')
    (hB : SChain t B t') :
    dg RD k μ S T (pre ++ A.map (whL [] t) ++ B.map (whL s' []) ++ post) =
      dg RD k μ S T (pre ++ B.map (whL s []) ++ A.map (whL [] t') ++ post) := by
  induction A generalizing pre s with
  | nil =>
    cases hA
    simp
  | cons x A ih =>
    obtain ⟨a, g, b⟩ := x
    obtain ⟨rfl, hA'⟩ := hA
    have e₁ : pre ++ List.map (whL [] t) ((a, g, b) :: A) ++ B.map (whL s' []) ++ post =
        (pre ++ [(a, g, b ++ t)]) ++ A.map (whL [] t) ++ B.map (whL s' []) ++ post := by
      simp [whL, List.append_assoc]
    have e₂ : (pre ++ [(a, g, b ++ t)]) ++ B.map (whL (a ++ g.cod ++ b) []) ++
        A.map (whL [] t') ++ post =
        pre ++ [(a, g, b ++ t)] ++ B.map (whL (a ++ g.cod ++ b) []) ++
          (A.map (whL [] t') ++ post) := by
      simp [List.append_assoc]
    rw [e₁, ih _ hA', e₂, dg_interchange_one _ _ a b g hB]
    simp [whL, List.append_assoc]

end Categorification.KL3.Diagram

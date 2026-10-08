/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.ChordLettered
import Categorification.Diagrams.KL3.SortedSpanProof
import StringDiagrams.Chord.PresentedRegions

/-!
# Chord diagrams in `U`: the moves hold modulo lower terms

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.2.3, proof
of Proposition 3.11 ("Relations on 2-morphisms in `U(E_ν 1_λ)` allow arbitrary homotopies of
colored dotted diagrams modulo lower order terms, i.e., terms with fewer crossings", TeX lines
4568–4580), following A. Lauda, arXiv:0803.3652v3, §8.

A diagram of cups and crossings in the sense of `StringDiagrams.Chord`
(`Chord.Move`, letters the signed letters `Letter I` with the dual letter `Letter.dual`) gives a
normal-form diagram of `U` (`chL`): a cup `cup g a` is the cup `1 ⟶ E_a E_{a*}` between the
first `g` strands and the others, a crossing `cross p` the crossing `xLay` of the strands `p`,
`p + 1`. We show that the generating moves of `Chord.Equiv` hold in `U` modulo diagrams with
fewer crossings (`rw_sound`), and that reducible diagrams are themselves lower terms
(`chL_mem_lo_of_reducible`):

* moves at disjoint places: exactly, by the interchange law, through the multi-region chord
  interface `StringDiagrams.Chord.RegionChordGens` of string-diagrams-lean (`chGens`,
  `dg_chL_congr`);
* the braid move: Reidemeister 3 modulo lower terms (`r3`);
* the pitchfork move: `cupPF`;
* a double crossing: Reidemeister 2 modulo lower terms (`r2`); a curl: `cupCurl`.

## Main results

* `chL`, `sChain_chL`, `ccnt_chL`: the diagram of a chord diagram.
* `chLetters`, `chGens`, `layList_chL`: `U` as an instance of the multi-region chord interface;
  the layers of `chL l D` are those of the interpretation of `D` there.
* `rw_sound`, `equiv_sound`: equivalent chord diagrams agree in `U` modulo lower terms.
* `chL_mem_lo_of_reducible`: reducible chord diagrams are lower terms.
* `chL_normal_form`: every chord diagram is, modulo lower terms, `0` or the canonical diagram of
  its pairing.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation
open StringDiagrams.Chord (Move Step Rw Fits lstep canon run)

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {k : Type w} [CommRing k]

/-! ## The diagram of a chord diagram -/

section Layers

/-- The layers of a move of a chord diagram applied to the letters `l`. -/
def mvL (l : List (Letter I)) : Move (Letter I) → List (LayerData I)
  | .cup g a => [(l.take g, .cup a, l.drop g)]
  | .cross p => match l.drop p with
    | x :: y :: r => (xLay x y).map (whL (l.take p) r)
    | _ => []

/-- The effect of a move on the letters. -/
abbrev lst (l : List (Letter I)) (m : Move (Letter I)) : List (Letter I) := lstep Letter.dual l m

/-- **The layers of a chord diagram** (moves read from the bottom) starting from the letters
`l`. -/
def chL : List (Letter I) → List (Move (Letter I)) → List (LayerData I)
  | _, [] => []
  | l, m :: D => mvL l m ++ chL (lst l m) D

/-- The number of crossings of a chord diagram. -/
def ncr (D : List (Move (Letter I))) : ℕ := D.countP fun m => match m with
  | .cross _ => true
  | .cup _ _ => false

@[simp] theorem ncr_nil : ncr ([] : List (Move (Letter I))) = 0 := rfl

theorem ncr_append (D E : List (Move (Letter I))) : ncr (D ++ E) = ncr D + ncr E := by
  simp [ncr, List.countP_append]

@[simp] theorem ncr_cons_cross (p : ℕ) (D : List (Move (Letter I))) :
    ncr (.cross p :: D) = ncr D + 1 := by simp [ncr]

@[simp] theorem ncr_cons_cup (g : ℕ) (a : Letter I) (D : List (Move (Letter I))) :
    ncr (.cup g a :: D) = ncr D := by simp [ncr]

theorem swapAt_mid {β : Type*} (u w : List β) (x y : β) :
    Chord.swapAt (u ++ x :: y :: w) u.length = u ++ y :: x :: w := by
  have hp : u.length + 1 < (u ++ x :: y :: w).length := by simp
  apply List.ext_getElem?; intro i
  rw [Chord.getElem?_swapAt _ hp]
  rcases (show i < u.length ∨ i = u.length ∨ i = u.length + 1 ∨ u.length + 1 < i by omega) with
    h | rfl | rfl | h
  · rw [Chord.tau_of_ne (by omega) (by omega), List.getElem?_append_left h,
      List.getElem?_append_left h]
  · simp [Chord.tau_left]
  · simp [Chord.tau_right]
  · rw [Chord.tau_of_ne (by omega) (by omega), List.getElem?_append_right (by omega),
      List.getElem?_append_right (by omega)]
    obtain ⟨m, rfl⟩ : ∃ m, i = u.length + 2 + m := ⟨i - u.length - 2, by omega⟩
    simp [show u.length + 2 + m - u.length = m + 2 by omega]

@[simp] theorem mvL_cup (u w : List (Letter I)) (a : Letter I) :
    mvL (u ++ w) (.cup u.length a) = [(u, .cup a, w)] := by
  simp [mvL]

@[simp] theorem mvL_cross (u w : List (Letter I)) (x y : Letter I) :
    mvL (u ++ x :: y :: w) (.cross u.length) = (xLay x y).map (whL u w) := by
  simp [mvL]

@[simp] theorem lst_cup (u w : List (Letter I)) (a : Letter I) :
    lst (u ++ w) (.cup u.length a) = u ++ a :: a.dual :: w := by
  simp [lst, lstep, Chord.insAt]

@[simp] theorem lst_cross (u w : List (Letter I)) (x y : Letter I) :
    lst (u ++ x :: y :: w) (.cross u.length) = u ++ y :: x :: w := by
  simp only [lst, lstep]; exact swapAt_mid u w x y

theorem exists_split_cup {l : List (Letter I)} {g : ℕ} (h : g ≤ l.length) :
    ∃ u w, l = u ++ w ∧ u.length = g :=
  ⟨l.take g, l.drop g, (List.take_append_drop g l).symm, by simp; omega⟩

theorem exists_split_cross {l : List (Letter I)} {p : ℕ} (h : p + 1 < l.length) :
    ∃ u x y w, l = u ++ x :: y :: w ∧ u.length = p := by
  obtain ⟨u, w', rfl, hu⟩ := exists_split_cup (l := l) (g := p) (by omega)
  match w', h with
  | x :: y :: w, _ => exact ⟨u, x, y, w, rfl, hu⟩
  | [], h => simp at h; omega
  | [x], h => simp at h; omega

theorem exists_cons2 {l : List (Letter I)} (h : 2 ≤ l.length) : ∃ x y w, l = x :: y :: w := by
  match l, h with
  | x :: y :: w, _ => exact ⟨x, y, w, rfl⟩
  | [], h => simp at h
  | [x], h => simp at h

theorem sChain_mvL {l : List (Letter I)} {m : Move (Letter I)} (h : m.Ok l.length) :
    SChain l (mvL l m) (lst l m) := by
  cases m with
  | cup g a =>
    obtain ⟨u, w, rfl, rfl⟩ := exists_split_cup (l := l) h
    rw [mvL_cup, lst_cup]
    exact ⟨by simp, by simp⟩
  | cross p =>
    obtain ⟨u, x, y, w, rfl, rfl⟩ := exists_split_cross (l := l) h
    rw [mvL_cross, lst_cross]
    simpa using (sChain_xLay x y).whisk u w

theorem ccnt_mvL {l : List (Letter I)} {m : Move (Letter I)} (h : m.Ok l.length) :
    ccnt (mvL l m) = ncr [m] := by
  cases m with
  | cup g a =>
    obtain ⟨u, w, rfl, rfl⟩ := exists_split_cup (l := l) h
    rw [mvL_cup]; rfl
  | cross p =>
    obtain ⟨u, x, y, w, rfl, rfl⟩ := exists_split_cross (l := l) h
    rw [mvL_cross, ccnt_map_whL, ccnt_xLay]; rfl

theorem chL_append : ∀ (l : List (Letter I)) (D E : List (Move (Letter I))),
    chL l (D ++ E) = chL l D ++ chL (D.foldl lst l) E
  | l, [], E => rfl
  | l, m :: D, E => by
    simp only [List.cons_append, chL, List.foldl_cons, chL_append _ D E, List.append_assoc]

theorem sChain_chL : ∀ {l : List (Letter I)} {D : List (Move (Letter I))},
    Fits l.length D → SChain l (chL l D) (D.foldl lst l)
  | l, [], _ => rfl
  | l, m :: D, h => by
    have h2 : Fits (lst l m).length D := by
      rw [Chord.length_lstep]; exact h.2
    exact (sChain_mvL h.1).append (sChain_chL h2)

theorem ccnt_chL : ∀ {l : List (Letter I)} {D : List (Move (Letter I))},
    Fits l.length D → ccnt (chL l D) = ncr D
  | l, [], _ => rfl
  | l, m :: D, h => by
    have h2 : Fits (lst l m).length D := by
      rw [Chord.length_lstep]; exact h.2
    rw [chL, ccnt_append, ccnt_mvL h.1, ccnt_chL h2, ← ncr_append]; rfl

theorem mvL_cup_eq {l u w : List (Letter I)} {g : ℕ} (a : Letter I) (hl : l = u ++ w)
    (hg : g = u.length) : mvL l (.cup g a) = [(u, .cup a, w)] := by
  subst hl hg; exact mvL_cup u w a

theorem lst_cup_eq {l u w : List (Letter I)} {g : ℕ} (a : Letter I) (hl : l = u ++ w)
    (hg : g = u.length) : lst l (.cup g a) = u ++ a :: a.dual :: w := by
  subst hl hg; exact lst_cup u w a

theorem mvL_cross_eq {l u w : List (Letter I)} {x y : Letter I} {p : ℕ}
    (hl : l = u ++ x :: y :: w) (hp : p = u.length) :
    mvL l (.cross p) = (xLay x y).map (whL u w) := by
  subst hl hp; exact mvL_cross u w x y

theorem lst_cross_eq {l u w : List (Letter I)} {x y : Letter I} {p : ℕ}
    (hl : l = u ++ x :: y :: w) (hp : p = u.length) : lst l (.cross p) = u ++ y :: x :: w := by
  subst hl hp; exact lst_cross u w x y

theorem chL_pair (l : List (Letter I)) (m₁ m₂ : Move (Letter I)) :
    chL l [m₁, m₂] = mvL l m₁ ++ mvL (lst l m₁) m₂ := by simp [chL]

theorem chL_triple (l : List (Letter I)) (m₁ m₂ m₃ : Move (Letter I)) :
    chL l [m₁, m₂, m₃] = mvL l m₁ ++ mvL (lst l m₁) m₂ ++ mvL (lst (lst l m₁) m₂) m₃ := by
  simp [chL]

theorem foldl_len_eq (l : List (Letter I)) (D : List (Move (Letter I))) :
    D.foldl Move.len l.length = (D.foldl lst l).length :=
  (Chord.foldl_lstep_len l D).symm

theorem chL_mid (A L B : List (Move (Letter I))) :
    chL [] (A ++ L ++ B) = chL [] A ++ chL (A.foldl lst []) L ++
      chL (L.foldl lst (A.foldl lst [])) B := by
  rw [chL_append, chL_append, List.foldl_append, List.append_assoc]

theorem fits_mid {A L B : List (Move (Letter I))} (h : Fits 0 (A ++ L ++ B)) :
    Fits (A.foldl lst []).length L := by
  rw [Chord.fits_append, Chord.fits_append] at h
  have := h.1.2
  rwa [show (0 : ℕ) = ([] : List (Letter I)).length from rfl, foldl_len_eq] at this

theorem chL_ne_nil {l : List (Letter I)} {D : List (Move (Letter I))} (hf : Fits l.length D)
    (hD : D ≠ []) : chL l D ≠ [] := by
  obtain ⟨m, D, rfl⟩ := List.exists_cons_of_ne_nil hD
  have hm : mvL l m ≠ [] := by
    cases m with
    | cup g a =>
      obtain ⟨u, w, rfl, rfl⟩ := exists_split_cup (l := l) hf.1
      simp
    | cross p =>
      obtain ⟨u, x, y, w, rfl, rfl⟩ := exists_split_cross (l := l) hf.1
      simp [xLay_ne_nil]
  simp [chL, hm]

theorem SChain.eq_ends {s t s' t' : List (Letter I)} {A : List (LayerData I)} (hA : A ≠ [])
    (h : SChain s A t) (h' : SChain s' A t') : s = s' ∧ t = t' := by
  obtain ⟨x, A', rfl⟩ := List.exists_cons_of_ne_nil hA
  obtain rfl : s = s' := h.1.trans h'.1.symm
  exact ⟨rfl, SChain.eq_target h h'⟩

end Layers

/-! ## The multi-region chord interface

The signed letters label the strands of the signature `psig RD` of `U`, the letter `a` with the
region `μ` on its right being the colour `⟨a, μ⟩` (`chLetters`); the cups `1 ⟶ E_a E_{a*}` and
the crossings `xLay` in every region are cups and crossings in the sense of
`StringDiagrams.Chord.RegionChordGens` (`chGens`). The layers of a chord diagram are those of
its interpretation there (`layList_chL`), so the distant commutations of moves, which hold there
exactly by the interchange law, hold for the normal-form diagrams in any context
(`dg_chL_congr`). -/

section Regions

variable (RD) in
/-- The signed letters as letters of the signature of `U`: the letter `a` with the region `μ` on
its right is the colour `⟨a, μ⟩`. -/
def chLetters : Chord.Letters (psig RD) (Letter I) where
  col a μ := ⟨a, μ⟩
  col_tgt _ _ := rfl

@[simp] theorem chLetters_lreg (μ : X) (l : List (Letter I)) :
    (chLetters RD).lreg μ l = wt RD μ l := by
  induction l with
  | nil => rfl
  | cons a l ih => exact congrArg (sh RD a + ·) ih

@[simp] theorem chLetters_word (μ : X) (l : List (Letter I)) :
    (chLetters RD).word μ l = wd RD μ l := by
  induction l with
  | nil => rfl
  | cons a l ih => exact congrArg₂ List.cons (congrArg (Col.mk a) (chLetters_lreg μ l)) ih

@[simp] theorem chLetters_obj (μ : X) (l : List (Letter I)) :
    (chLetters RD).obj μ l = ob RD μ l :=
  Obj.ext (chLetters_lreg μ l) (chLetters_word μ l)

variable (RD) in
/-- The cups `1 ⟶ E_a E_{a*}` and the crossings `xLay` of `U`, in every region, as cups and
crossings of the multi-region chord interface. -/
def chGens : Chord.RegionChordGens (chLetters RD) Letter.dual where
  cup μ a := layList RD μ [([], .cup a, [])]
  cross μ a b := layList RD μ (xLay a b)
  chain_cup := fun (μ : X) a => by
    rw [chLetters_obj, chLetters_obj]
    exact SChain.chain RD μ (show SChain [] [([], Shape.cup a, [])] [a, a.dual] from
      ⟨by simp, by simp⟩)
  chain_cross := fun (μ : X) a b => by
    rw [chLetters_obj, chLetters_obj]
    exact (sChain_xLay a b).chain RD μ
  cup_even _ _ _ _ := Signature.IsEven.odd_eq_false _
  cross_even _ _ _ _ _ := Signature.IsEven.odd_eq_false _

/-- The layers of a move are those of its interpretation in the chord interface. -/
theorem layList_mvL (μ : X) (l : List (Letter I)) (m : Move (Letter I)) :
    layList RD μ (mvL l m) = (chGens RD).moveLayers μ l m := by
  cases m with
  | cup g a =>
    have h := layList_whisker RD μ (l.take g) (l.drop g)
      (show SChain [] [([], Shape.cup a, [])] [a, a.dual] from ⟨by simp, by simp⟩)
    simp only [wt_nil] at h
    simp only [Chord.RegionChordGens.moveLayers, chGens, chLetters_obj, chLetters_lreg,
      chLetters_word]
    rw [h]
    simp [mvL, whL]
  | cross p =>
    by_cases hp : p + 1 < l.length
    · obtain ⟨u, x, y, w, rfl, rfl⟩ := exists_split_cross (l := l) hp
      rw [mvL_cross, (chGens RD).moveLayers_cross μ u x y w rfl]
      have h := layList_whisker RD μ u w (sChain_xLay x y)
      simp only [chGens, chLetters_obj, chLetters_lreg, chLetters_word]
      rw [← h]
      rfl
    · simp only [Chord.RegionChordGens.moveLayers, dite_eq_right hp]
      rcases hd : l.drop p with _ | ⟨x, _ | ⟨y, r⟩⟩
      · simp [mvL, hd]
      · simp [mvL, hd]
      · have := congrArg List.length hd
        simp at this
        omega

/-- **The layers of a chord diagram are those of its interpretation** in the chord interface. -/
theorem layList_chL (μ : X) (l : List (Letter I)) (D : List (Move (Letter I))) :
    layList RD μ (chL l D) = (chGens RD).layersOf μ l D := by
  induction D generalizing l with
  | nil => rfl
  | cons m D ih =>
    simp only [chL, Chord.RegionChordGens.layersOf, layList_append, layList_mvL, ih]

/-- **Chord diagrams with equal images in the presented category give equal normal-form diagrams
in any context**: if the images of `L` and `R` under the interpretation of the chord interface
(region `μ`) agree exactly, then so do `pre ++ chL l L ++ post` and `pre ++ chL l R ++ post`. -/
theorem dg_chL_congr {μ : X} {s₀ t₀ l : List (Letter I)} {L R : List (Move (Letter I))}
    (hL : Fits l.length L) (hR : Fits l.length R) (hLR : L.foldl lst l = R.foldl lst l)
    (hL0 : L ≠ []) (hR0 : R ≠ [])
    (h : (Chord.MoveInterp.Filtration.bot ((chGens RD).interp (pres RD k) μ)).Near 0 l L R)
    (pre post : List (LayerData I)) :
    dg RD k μ s₀ t₀ (pre ++ chL l L ++ post) = dg RD k μ s₀ t₀ (pre ++ chL l R ++ post) := by
  have cL := sChain_chL (l := l) hL
  have cR : SChain l (chL l R) (L.foldl lst l) := by rw [hLR]; exact sChain_chL hR
  have nL := chL_ne_nil hL hL0
  have nR := chL_ne_nil hR hR0
  refine dg_congr_ctx (fun s t hs => ?_) (fun s t hs => ?_) (fun s t hs => ?_) s₀ t₀ pre post
  · obtain ⟨e₁, e₂⟩ := hs.eq_ends nL cL; rw [e₁, e₂]; exact cR
  · obtain ⟨e₁, e₂⟩ := hs.eq_ends nR cR; rw [e₁, e₂]; exact cL
  · obtain ⟨e₁, e₂⟩ := hs.eq_ends nL cL
    rw [e₁, e₂]
    have key := (Chord.MoveInterp.Filtration.near_bot_iff).1 h hLR
    rw [(chGens RD).eval_comp_eqToHom_eq (pres RD k) μ hLR
      ⟨(chGens RD).layersOf μ l L, hLR ▸ (chGens RD).chain_layersOf μ l L⟩ rfl] at key
    replace key := key.trans ((chGens RD).eval_interp (pres RD k) μ l R)
    rw [dg_of cL, dg_of cR]
    exact (pres RD k).diag_eq_of_diag_eq_of_layers _ _ _ _ (chLetters_obj μ l).symm
      (by rw [hLR, chLetters_obj]) (by rw [layers_mkD, layList_chL]; rfl) (by rw [layers_mkD, layList_chL]; rfl) key

end Regions

/-! ## The moves hold modulo lower terms -/

section Sound

variable [DecidableEq I]

omit [DecidableEq I] in
theorem lo_of_eq {μ : X} {s t : List (Letter I)} {n : ℕ} {a b} (h : a = b) :
    a - b ∈ Lo RD k μ s t n := by
  rw [h, sub_self]; exact Submodule.zero_mem _

/-- **Each generating move holds in `U` modulo lower terms**, in any context. -/
theorem step_sound {L R : List (Move (Letter I))} (hs : Step L R) (l : List (Letter I))
    (hL : Fits l.length L) (pre post : List (LayerData I)) (μ : X) (s₀ t₀ : List (Letter I)) :
    dg RD k μ s₀ t₀ (pre ++ chL l L ++ post) - dg RD k μ s₀ t₀ (pre ++ chL l R ++ post) ∈
      Lo RD k μ s₀ t₀ (ccnt pre + ncr L + ccnt post) := by
  have hR : Fits l.length R := ((hs.fits_letters (d := Letter.dual) l).1).1 hL
  have hLR : L.foldl lst l = R.foldl lst l := (hs.fits_letters (d := Letter.dual) l).2 hL
  -- moves at disjoint places: exactly, by the interchange law in the chord interface
  have sep : (Chord.MoveInterp.Filtration.bot ((chGens RD).interp (pres RD k) μ)).Near 0 l L R →
      dg RD k μ s₀ t₀ (pre ++ chL l L ++ post) - dg RD k μ s₀ t₀ (pre ++ chL l R ++ post) ∈
        Lo RD k μ s₀ t₀ (ccnt pre + ncr L + ccnt post) := fun h =>
    lo_of_eq (dg_chL_congr hL hR hLR (by cases hs <;> simp) (by cases hs <;> simp) h pre post)
  cases hs with
  | xx h => exact sep ((chGens RD).near_xx (pres RD k) μ _ h hL)
  | xuL a h => exact sep ((chGens RD).near_xuL (pres RD k) μ _ a h hL)
  | xuR a h => exact sep ((chGens RD).near_xuR (pres RD k) μ _ a h hL)
  | uu a b h => exact sep ((chGens RD).near_uu (pres RD k) μ _ a b h hL)
  | braid p =>
    simp only [Fits, Chord.Move.Ok, Chord.Move.len] at hL
    obtain ⟨u, x, y, w, rfl, rfl⟩ := exists_split_cross (l := l) (p := p) (by omega)
    obtain ⟨z', Q, rfl⟩ : ∃ z' Q, w = z' :: Q := by
      match w, hL with
      | z' :: Q, _ => exact ⟨z', Q, rfl⟩
      | [], hL => simp at hL
    have e1 : chL (u ++ x :: y :: z' :: Q) [.cross u.length, .cross (u.length + 1),
        .cross u.length] = (r3L x y z').map (whL u Q) := by
      rw [chL_triple, mvL_cross_eq rfl rfl, lst_cross_eq rfl rfl,
        mvL_cross_eq (u := u ++ [y]) (x := x) (y := z') (w := Q) (by simp) (by simp),
        lst_cross_eq (u := u ++ [y]) (x := x) (y := z') (w := Q) (by simp) (by simp),
        mvL_cross_eq (u := u) (x := y) (y := z') (w := x :: Q) (by simp) rfl]
      simp only [r3L]; wnf
    have e2 : chL (u ++ x :: y :: z' :: Q) [.cross (u.length + 1), .cross u.length,
        .cross (u.length + 1)] = (r3R x y z').map (whL u Q) := by
      rw [chL_triple, mvL_cross_eq (u := u ++ [x]) (x := y) (y := z') (w := Q) (by simp) (by simp),
        lst_cross_eq (u := u ++ [x]) (x := y) (y := z') (w := Q) (by simp) (by simp),
        mvL_cross_eq (u := u) (x := x) (y := z') (w := y :: Q) (by simp) rfl,
        lst_cross_eq (u := u) (x := x) (y := z') (w := y :: Q) (by simp) rfl,
        mvL_cross_eq (u := u ++ [z']) (x := x) (y := y) (w := Q) (by simp) (by simp)]
      simp only [r3R]; wnf
    rw [e1, e2]
    refine leL_le_lo (c := ccnt pre + 2 + ccnt post) (by simp [ncr]) ?_
    exact dg_mod_free pre post u Q (r3 (RD := RD) (k := k) _ x y z') (sChain_r3L x y z')
      (sChain_r3R x y z') (by simp [r3L, xLay_ne_nil]) (by simp [r3R, xLay_ne_nil]) rfl rfl le_rfl
  | pitch g a =>
    simp only [Fits, Chord.Move.Ok, Chord.Move.len] at hL
    obtain ⟨u, w, rfl, rfl⟩ := exists_split_cup (l := l) (g := g) (by omega)
    obtain ⟨m', Q, rfl⟩ : ∃ m' Q, w = m' :: Q := by
      match w, hL with
      | m' :: Q, _ => exact ⟨m', Q, rfl⟩
      | [], hL => simp at hL
    have e1 : chL (u ++ m' :: Q) [.cup u.length a, .cross (u.length + 1)] =
        ([([], Shape.cup a, [m'])] ++ (xLay a.dual m').map (whL [a] [])).map (whL u Q) := by
      rw [chL_pair, mvL_cup_eq a rfl rfl, lst_cup_eq a rfl rfl,
        mvL_cross_eq (u := u ++ [a]) (x := a.dual) (y := m') (w := Q) (by simp) (by simp)]
      wnf
    have e2 : chL (u ++ m' :: Q) [.cup (u.length + 1) a, .cross u.length] =
        ([([m'], Shape.cup a, [])] ++ (xLay m' a).map (whL [] [a.dual])).map (whL u Q) := by
      rw [chL_pair, mvL_cup_eq (u := u ++ [m']) (w := Q) a (by simp) (by simp),
        lst_cup_eq (u := u ++ [m']) (w := Q) a (by simp) (by simp),
        mvL_cross_eq (u := u) (x := m') (y := a) (w := a.dual :: Q) (by simp) rfl]
      wnf
    rw [e1, e2]
    refine leL_le_lo (c := ccnt pre + 0 + ccnt post) (by simp [ncr]) ?_
    refine dg_mod_free pre post u Q (cupPF (RD := RD) (k := k) _ a m') ?_ ?_
      (by simp) (by simp) rfl rfl le_rfl
    · exact (show SChain [m'] [([], .cup a, [m'])] [a, a.dual, m'] from
        ⟨by simp, by simp⟩).append (by simpa using (sChain_xLay a.dual m').whisk [a] [])
    · exact (show SChain [m'] [([m'], .cup a, [])] [m', a, a.dual] from
        ⟨by simp, by simp⟩).append (by simpa using (sChain_xLay m' a).whisk [] [a.dual])

omit [DecidableEq I] in
theorem ncr_step {L R : List (Move (Letter I))} (hs : Step L R) : ncr L = ncr R := by
  cases hs <;> simp [ncr]

omit [DecidableEq I] in
theorem fits_parts {A L B : List (Move (Letter I))} (h : Fits 0 (A ++ L ++ B)) :
    Fits 0 A ∧ Fits (A.foldl lst []).length L ∧ Fits (L.foldl lst (A.foldl lst [])).length B := by
  have h' := h
  rw [Chord.fits_append, Chord.fits_append] at h'
  refine ⟨h'.1.1, fits_mid h, ?_⟩
  have := h'.2
  rwa [List.foldl_append, show (0 : ℕ) = ([] : List (Letter I)).length from rfl, foldl_len_eq,
    foldl_len_eq] at this

omit [DecidableEq I] in
theorem ccnt_chL_mid {A L B : List (Move (Letter I))} (h : Fits 0 (A ++ L ++ B)) :
    ccnt (chL [] A) + ncr L + ccnt (chL (L.foldl lst (A.foldl lst [])) B) = ncr (A ++ L ++ B) := by
  obtain ⟨hA, -, hB⟩ := fits_parts h
  rw [ccnt_chL (l := []) hA, ccnt_chL hB, ncr_append, ncr_append]

/-- **A generating move in context holds in `U` modulo lower terms.** -/
theorem rw_sound {D D' : List (Move (Letter I))} (h : Rw D D') (hf : Fits 0 D) (μ : X)
    (v : List (Letter I)) :
    ncr D = ncr D' ∧ dg RD k μ [] v (chL [] D) - dg RD k μ [] v (chL [] D') ∈ Lo RD k μ [] v (ncr D) := by
  obtain ⟨A, B, L, R, hs, rfl, rfl⟩ := h
  refine ⟨by rw [ncr_append, ncr_append, ncr_append, ncr_append, ncr_step hs], ?_⟩
  obtain ⟨-, hL, -⟩ := fits_parts hf
  have hlet := ((hs.fits_letters (d := Letter.dual) (A.foldl lst [])).2 hL)
  rw [chL_mid, chL_mid, ← hlet, ← ccnt_chL_mid hf]
  exact step_sound hs _ hL _ _ μ [] v

/-- **Equivalent chord diagrams agree in `U` modulo lower terms.** -/
theorem equiv_sound {D D' : List (Move (Letter I))} (h : Chord.Equiv D D') (hf : Fits 0 D) :
    ncr D = ncr D' ∧ ∀ (μ : X) (v : List (Letter I)),
      dg RD k μ [] v (chL [] D) - dg RD k μ [] v (chL [] D') ∈ Lo RD k μ [] v (ncr D) := by
  induction h with
  | rel D D' h => exact ⟨(rw_sound (RD := RD) (k := k) h hf 0 []).1, fun μ v => (rw_sound h hf μ v).2⟩
  | refl D => exact ⟨rfl, fun μ v => lo_of_eq rfl⟩
  | symm D D' h ih =>
    have hf' : Fits 0 D := ((Chord.Equiv.fits_letters (d := Letter.dual) h []).1).2 hf
    obtain ⟨e, ih⟩ := ih hf'
    refine ⟨e.symm, fun μ v => ?_⟩
    rw [← e, ← neg_sub]; exact Submodule.neg_mem _ (ih μ v)
  | trans D D' D'' h h' ih ih' =>
    have hf' : Fits 0 D' := ((Chord.Equiv.fits_letters (d := Letter.dual) h []).1).1 hf
    obtain ⟨e, ih⟩ := ih hf
    obtain ⟨e', ih'⟩ := ih' hf'
    refine ⟨e.trans e', fun μ v => lo_sub_trans (ih μ v) ?_⟩
    rw [e]; exact ih' μ v

/-- **Reducible chord diagrams are lower terms** (a double crossing: Reidemeister 2; a curl:
`cupCurl`). -/
theorem chL_mem_lo_of_reducible {D : List (Move (Letter I))} (h : Chord.Reducible D)
    (hf : Fits 0 D) (μ : X) (v : List (Letter I)) :
    dg RD k μ [] v (chL [] D) ∈ Lo RD k μ [] v (ncr D) := by
  obtain ⟨A, B, p, h⟩ := h
  suffices H : ∀ E, Chord.Equiv D E → (∀ hE : Fits 0 E,
      dg RD k μ [] v (chL [] E) ∈ Lo RD k μ [] v (ncr E)) →
      dg RD k μ [] v (chL [] D) ∈ Lo RD k μ [] v (ncr D) by
    rcases h with h | ⟨a, h⟩
    · refine H _ h fun hE => ?_
      obtain ⟨-, hL, -⟩ := fits_parts hE
      simp only [Fits, Chord.Move.Ok, Chord.Move.len] at hL
      obtain ⟨u, x, y, Q, hl, rfl⟩ := exists_split_cross (l := A.foldl lst []) (p := p) (by omega)
      rw [chL_mid, ← ccnt_chL_mid hE, hl]
      have e : chL (u ++ x :: y :: Q) [.cross u.length, .cross u.length] =
          (xLay x y ++ xLay y x).map (whL u Q) := by
        rw [chL_pair, mvL_cross_eq rfl rfl, lst_cross_eq rfl rfl, mvL_cross_eq rfl rfl,
          List.map_append]
      rw [e]
      refine leL_le_lo (c := ccnt (chL [] A) + 1 + ccnt (chL (List.foldl lst (u ++ x :: y :: Q)
        [.cross u.length, .cross u.length]) B)) (by simp [ncr]) ?_
      exact dg_mem_free _ _ u Q (r2 (RD := RD) (k := k) _ x y)
        ((sChain_xLay x y).append (sChain_xLay y x)) (by simp [xLay_ne_nil]) rfl le_rfl
    · refine H _ h fun hE => ?_
      obtain ⟨-, hL, -⟩ := fits_parts hE
      simp only [Fits, Chord.Move.Ok, Chord.Move.len] at hL
      obtain ⟨u, Q, hl, rfl⟩ := exists_split_cup (l := A.foldl lst []) (g := p) (by omega)
      rw [chL_mid, ← ccnt_chL_mid hE, hl]
      have e : chL (u ++ Q) [.cup u.length a, .cross u.length] =
          ([([], Shape.cup a, [])] ++ xLay a a.dual).map (whL u Q) := by
        rw [chL_pair, mvL_cup_eq a rfl rfl, lst_cup_eq a rfl rfl,
          mvL_cross_eq (u := u) (x := a) (y := a.dual) (w := Q) rfl rfl]
        wnf
      rw [e]
      refine leL_le_lo (c := ccnt (chL [] A) + 0 + ccnt (chL (List.foldl lst (u ++ Q)
        [.cup u.length a, .cross u.length]) B)) (by simp [ncr]) ?_
      exact dg_mem_free _ _ u Q (cupCurl (RD := RD) (k := k) _ a)
        ((show SChain [] [([], Shape.cup a, [])] [a, a.dual] from ⟨by simp, by simp⟩).append
          (sChain_xLay a a.dual)) (by simp) rfl le_rfl
  intro E hDE hE
  have hfE : Fits 0 E := ((Chord.Equiv.fits_letters (d := Letter.dual) hDE []).1).1 hf
  obtain ⟨e, hs⟩ := equiv_sound (RD := RD) (k := k) hDE hf
  have := Submodule.add_mem _ (hs μ v) (show dg RD k μ [] v (chL [] E) ∈ Lo RD k μ [] v (ncr D)
    from e ▸ hE hfE)
  rwa [sub_add_cancel] at this

/-- **Normal form of chord diagrams in `U`**: a chord diagram is, modulo diagrams with fewer
crossings, either `0` or the canonical diagram of its final pairing (which has as many
crossings). -/
theorem chL_normal_form {D : List (Move (Letter I))} (hf : Fits 0 D) (μ : X) (v : List (Letter I)) :
    dg RD k μ [] v (chL [] D) ∈ Lo RD k μ [] v (ncr D) ∨
      (Fits 0 (canon (run Letter.dual D)) ∧ ncr (canon (run Letter.dual D)) = ncr D ∧
        dg RD k μ [] v (chL [] D) - dg RD k μ [] v (chL [] (canon (run Letter.dual D))) ∈
          Lo RD k μ [] v (ncr D)) := by
  rcases Chord.equiv_canon_or_reducible (d := Letter.dual) hf with h | h
  · exact Or.inl (chL_mem_lo_of_reducible h hf μ v)
  · obtain ⟨e, hs⟩ := equiv_sound (RD := RD) (k := k) h hf
    exact Or.inr ⟨((Chord.Equiv.fits_letters (d := Letter.dual) h []).1).1 hf, e.symm, hs μ v⟩

end Sound

/-! ## Dots -/

section Dots

/-- A dot on the strand at position `i` of the letters `t` (no layer if `i` is out of range). -/
def dotAt (t : List (Letter I)) (i : ℕ) : List (LayerData I) :=
  match t.drop i with
  | l :: w => [(t.take i, .dot l, w)]
  | [] => []

/-- Dots on the strands at the positions `is` (from the bottom). -/
def dotsL (t : List (Letter I)) (is : List ℕ) : List (LayerData I) := (is.map (dotAt t)).flatten

/-- The new position of the strand at position `i` after a move. -/
def mvPos : Move (Letter I) → ℕ → ℕ
  | .cup g _, i => if i < g then i else i + 2
  | .cross p, i => Chord.tau p i

@[simp] theorem dotAt_eq (u w : List (Letter I)) (l : Letter I) :
    dotAt (u ++ l :: w) u.length = [(u, .dot l, w)] := by
  simp [dotAt]

theorem dotAt_eq' {t u w : List (Letter I)} {l : Letter I} {i : ℕ} (ht : t = u ++ l :: w)
    (hi : i = u.length) : dotAt t i = [(u, .dot l, w)] := by
  subst ht hi; exact dotAt_eq u w l

theorem exists_split_dot {t : List (Letter I)} {i : ℕ} (h : i < t.length) :
    ∃ u l w, t = u ++ l :: w ∧ u.length = i := by
  obtain ⟨u, w', rfl, hu⟩ := exists_split_cup (l := t) (g := i) h.le
  match w', h with
  | l :: w, _ => exact ⟨u, l, w, rfl, hu⟩
  | [], h => simp at h; omega

theorem sChain_dotAt {t : List (Letter I)} {i : ℕ} (h : i < t.length) :
    SChain t (dotAt t i) t := by
  obtain ⟨u, l, w, rfl, rfl⟩ := exists_split_dot h
  rw [dotAt_eq]; exact ⟨by simp, by simp⟩

@[simp] theorem ccnt_dotAt (t : List (Letter I)) (i : ℕ) : ccnt (dotAt t i) = 0 := by
  unfold dotAt; split <;> rfl

@[simp] theorem dotsL_nil (t : List (Letter I)) : dotsL t [] = [] := rfl

@[simp] theorem dotsL_cons (t : List (Letter I)) (i : ℕ) (is : List ℕ) :
    dotsL t (i :: is) = dotAt t i ++ dotsL t is := rfl

theorem dotsL_append (t : List (Letter I)) (is js : List ℕ) :
    dotsL t (is ++ js) = dotsL t is ++ dotsL t js := by
  simp [dotsL]

@[simp] theorem ccnt_dotsL (t : List (Letter I)) (is : List ℕ) : ccnt (dotsL t is) = 0 := by
  induction is with
  | nil => rfl
  | cons i is ih => rw [dotsL_cons, ccnt_append, ccnt_dotAt, ih]

theorem sChain_dotsL {t : List (Letter I)} : ∀ {is : List ℕ}, (∀ i ∈ is, i < t.length) →
    SChain t (dotsL t is) t
  | [], _ => rfl
  | i :: _, h => (sChain_dotAt (h i List.mem_cons_self)).append
      (sChain_dotsL fun j hj => h j (List.mem_cons_of_mem _ hj))

theorem dotAt_of_mem {t : List (Letter I)} {x : LayerData I} (hx : x.2.1.isDot = true)
    (hc : SChain t [x] t) : x.1.length < t.length ∧ [x] = dotAt t x.1.length := by
  obtain ⟨a, g, b⟩ := x
  cases g with
  | dot l =>
    have e : t = a ++ l :: b := by simpa using hc.1
    subst e
    exact ⟨by simp, (dotAt_eq a b l).symm⟩
  | _ => simp [Shape.isDot] at hx

/-- Every list of dots is `dotsL` of the list of their positions. -/
theorem exists_dotsL {t : List (Letter I)} : ∀ {Dt : List (LayerData I)}, AllSh Shape.isDot Dt →
    SChain t Dt t → ∃ is : List ℕ, (∀ i ∈ is, i < t.length) ∧ Dt = dotsL t is
  | [], _, _ => ⟨[], by simp, rfl⟩
  | x :: Dt, hD, hc => by
    have hx : x.2.1.isDot = true := hD x List.mem_cons_self
    have hxc : SChain t [x] t := by
      obtain ⟨a, g, b⟩ := x
      cases g with
      | dot l => exact ⟨hc.1, by simpa using hc.1.symm⟩
      | _ => simp [Shape.isDot] at hx
    have hDc : SChain t Dt t := by
      have h2 := hc.2
      have e : x.1 ++ x.2.1.cod ++ x.2.2 = t := hxc.2
      rwa [e] at h2
    obtain ⟨is, his, rfl⟩ := exists_dotsL (fun y hy => hD y (List.mem_cons_of_mem _ hy)) hDc
    obtain ⟨hl, e⟩ := dotAt_of_mem hx hxc
    refine ⟨x.1.length :: is, ?_, ?_⟩
    · intro i hi
      rcases List.mem_cons.1 hi with rfl | hi
      · exact hl
      · exact his i hi
    · rw [dotsL_cons, ← e]; rfl

theorem allSh_dotsL (t : List (Letter I)) (is : List ℕ) : AllSh Shape.isDot (dotsL t is) := by
  intro x hx
  simp only [dotsL, List.mem_flatten, List.mem_map] at hx
  obtain ⟨_, ⟨i, -, rfl⟩, hx⟩ := hx
  unfold dotAt at hx
  split at hx
  · rw [List.mem_singleton.1 hx]; rfl
  · simp at hx

variable [DecidableEq I]

set_option maxHeartbeats 1600000 in
/-- **A dot passes a move** (exactly for a cup or a crossing of other strands, modulo diagrams
with fewer crossings if the dot is on a strand of the crossing). -/
theorem dot_move {t : List (Letter I)} {m : Move (Letter I)} (hm : m.Ok t.length) {i : ℕ}
    (hi : i < t.length) (P Q : List (LayerData I)) (μ : X) (s₀ t₀ : List (Letter I)) :
    dg RD k μ s₀ t₀ (P ++ dotAt t i ++ mvL t m ++ Q) -
        dg RD k μ s₀ t₀ (P ++ mvL t m ++ dotAt (lst t m) (mvPos m i) ++ Q) ∈
      Lo RD k μ s₀ t₀ (ccnt P + ncr [m] + ccnt Q) := by
  suffices H : dg RD k μ s₀ t₀ (P ++ dotAt t i ++ mvL t m ++ Q) -
        dg RD k μ s₀ t₀ (P ++ mvL t m ++ dotAt (lst t m) (mvPos m i) ++ Q) ∈
      LeL RD k μ s₀ t₀ (ccnt P + ccnt Q) ∧ (ncr [m] = 0 → dg RD k μ s₀ t₀ (P ++ dotAt t i ++ mvL t m ++ Q) =
        dg RD k μ s₀ t₀ (P ++ mvL t m ++ dotAt (lst t m) (mvPos m i) ++ Q)) by
    by_cases h0 : ncr [m] = 0
    · exact lo_of_eq (H.2 h0)
    · exact leL_le_lo (by omega) H.1
  cases m with
  | cup g a =>
    simp only [Chord.Move.Ok] at hm
    obtain ⟨u, w, rfl, rfl⟩ := exists_split_cup (l := t) hm
    rw [mvL_cup, lst_cup]
    simp only [mvPos]
    split_ifs with hig
    · obtain ⟨u1, l, M, rfl, rfl⟩ := exists_split_dot (t := u) hig
      rw [dotAt_eq' (u := u1) (l := l) (w := M ++ w) (by simp) rfl,
        dotAt_eq' (u := u1) (l := l) (w := M ++ a :: a.dual :: w) (by simp) rfl]
      have E := dg_ichg (RD := RD) (k := k) (μ := μ) (s₀ := s₀) (t₀ := t₀) P Q u1 w
        (A := [([], .dot l, [])]) (B := [(M, .cup a, [])]) (s := [l]) (s' := [l]) (t := M)
        (t' := M ++ [a, a.dual]) ⟨by simp, by simp⟩ ⟨by simp, by simp⟩
      wnf at E ⊢
      exact ⟨leL_sub_of_eq E, fun _ => E⟩
    · obtain ⟨M, l, w1, rfl, hM⟩ := exists_split_dot (t := w) (i := i - u.length)
        (by simp at hi; omega)
      rw [dotAt_eq' (u := u ++ M) (l := l) (w := w1) (by simp) (by simp; omega),
        dotAt_eq' (u := u ++ a :: a.dual :: M) (l := l) (w := w1) (by simp) (by simp; omega)]
      have E := dg_ichg (RD := RD) (k := k) (μ := μ) (s₀ := s₀) (t₀ := t₀) P Q u w1
        (A := [([], .cup a, [])]) (B := [(M, .dot l, [])]) (s := []) (s' := [a, a.dual])
        (t := M ++ [l]) (t' := M ++ [l]) ⟨by simp, by simp⟩ ⟨by simp, by simp⟩
      wnf at E ⊢
      exact ⟨leL_sub_of_eq E.symm, fun _ => E.symm⟩
  | cross p =>
    simp only [Chord.Move.Ok] at hm
    obtain ⟨u, x, y, w, rfl, rfl⟩ := exists_split_cross (l := t) hm
    rw [mvL_cross, lst_cross]
    simp only [mvPos]
    rcases (show i < u.length ∨ i = u.length ∨ i = u.length + 1 ∨ u.length + 1 < i by omega) with
      h | rfl | rfl | h
    · obtain ⟨u1, l, M, rfl, rfl⟩ := exists_split_dot (t := u) h
      rw [Chord.tau_of_ne (by simp) (by simp; omega),
        dotAt_eq' (u := u1) (l := l) (w := M ++ x :: y :: w) (by simp) rfl,
        dotAt_eq' (u := u1) (l := l) (w := M ++ y :: x :: w) (by simp) rfl]
      refine ⟨leL_sub_of_eq ?_, fun h => by simp [ncr] at h⟩
      have E := dg_ichg (RD := RD) (k := k) (μ := μ) (s₀ := s₀) (t₀ := t₀) P Q u1 w
        (A := [([], .dot l, [])]) (B := (xLay x y).map (whL M [])) (s := [l]) (s' := [l])
        ⟨by simp, by simp⟩ ((sChain_xLay x y).whisk M [])
      wnf at E ⊢
      exact E
    · rw [Chord.tau_left, dotAt_eq' (u := u) (l := x) (w := y :: w) rfl rfl,
        dotAt_eq' (u := u ++ [y]) (l := x) (w := w) (by simp) (by simp)]
      refine ⟨?_, fun h => by simp [ncr] at h⟩
      refine dg_mod_free P Q u w (leL_sub_comm (ds1 (RD := RD) (k := k) _ x y))
        (A := [([], .dot x, [y])] ++ xLay x y) (B := xLay x y ++ [([y], .dot x, [])])
        ((show SChain [x, y] [([], .dot x, [y])] [x, y] from ⟨rfl, rfl⟩).append (sChain_xLay x y))
        ((sChain_xLay x y).append ⟨rfl, rfl⟩) (by simp) (by simp) ?_ ?_ (by simp)
      · wnf
      · wnf
    · rw [Chord.tau_right, dotAt_eq' (u := u ++ [x]) (l := y) (w := w) (by simp) (by simp),
        dotAt_eq' (u := u) (l := y) (w := x :: w) rfl rfl]
      refine ⟨?_, fun h => by simp [ncr] at h⟩
      refine dg_mod_free P Q u w (leL_sub_comm (ds0 (RD := RD) (k := k) _ x y))
        (A := [([x], .dot y, [])] ++ xLay x y) (B := xLay x y ++ [([], .dot y, [x])])
        ((show SChain [x, y] [([x], .dot y, [])] [x, y] from ⟨rfl, rfl⟩).append (sChain_xLay x y))
        ((sChain_xLay x y).append ⟨rfl, rfl⟩) (by simp) (by simp) ?_ ?_ (by simp)
      · wnf
      · wnf
    · obtain ⟨M, l, w1, rfl, hM⟩ := exists_split_dot (t := w) (i := i - u.length - 2)
        (by simp at hi; omega)
      rw [Chord.tau_of_ne (by omega) (by omega),
        dotAt_eq' (u := u ++ x :: y :: M) (l := l) (w := w1) (by simp) (by simp; omega),
        dotAt_eq' (u := u ++ y :: x :: M) (l := l) (w := w1) (by simp) (by simp; omega)]
      refine ⟨leL_sub_of_eq ?_, fun h => by simp [ncr] at h⟩
      have E := dg_ichg (RD := RD) (k := k) (μ := μ) (s₀ := s₀) (t₀ := t₀) P Q u w1
        (A := xLay x y) (B := [(M, .dot l, [])]) (t := M ++ [l]) (t' := M ++ [l])
        (sChain_xLay x y) ⟨by simp, by simp⟩
      wnf at E ⊢
      exact E.symm

/-- **Dots pass a move.** -/
theorem dots_move {t : List (Letter I)} {m : Move (Letter I)} (hm : m.Ok t.length) :
    ∀ {is : List ℕ}, (∀ i ∈ is, i < t.length) → ∀ (P Q : List (LayerData I)) (μ : X)
      (s₀ t₀ : List (Letter I)),
    dg RD k μ s₀ t₀ (P ++ dotsL t is ++ mvL t m ++ Q) -
        dg RD k μ s₀ t₀ (P ++ mvL t m ++ dotsL (lst t m) (is.map (mvPos m)) ++ Q) ∈
      Lo RD k μ s₀ t₀ (ccnt P + ncr [m] + ccnt Q)
  | [], _, P, Q, μ, s₀, t₀ => lo_of_eq (by simp)
  | i :: is, h, P, Q, μ, s₀, t₀ => by
    have h1 := dots_move hm (fun j hj => h j (List.mem_cons_of_mem _ hj)) (P ++ dotAt t i) Q μ s₀ t₀
    have h2 := dot_move (RD := RD) (k := k) hm (h i List.mem_cons_self) P
      (dotsL (lst t m) (is.map (mvPos m)) ++ Q) μ s₀ t₀
    simp only [ccnt_append, ccnt_dotAt, ccnt_dotsL, add_zero, zero_add] at h1 h2
    simp only [dotsL_cons, List.map_cons, List.append_assoc] at h1 h2 ⊢
    exact lo_sub_trans h1 h2

omit [DecidableEq I] in
theorem dg_sub_comp {μ : X} {s m t : List (Letter I)} {A B : List (LayerData I)}
    (hA : SChain s A m) (hB : SChain s B m) (M : List (LayerData I)) :
    dg RD k μ s t (A ++ M) - dg RD k μ s t (B ++ M) =
      (dg RD k μ s m A - dg RD k μ s m B) ≫ dg RD k μ m t M := by
  rw [Preadditive.sub_comp, ← dg_append_of_left hA, ← dg_append_of_left hB]

/-- **Move diagrams as chord diagrams with dots on top**: a move diagram from `1_μ` (dots, cups
and crossings) is, modulo diagrams with fewer crossings, a chord diagram followed by dots on its
top strands. -/
theorem mv_to_chord (μ : X) : ∀ (ms : List (Mv I)) {v : List (Letter I)}, MvChain [] ms v →
    ∃ (D : List (Move (Letter I))) (is : List ℕ), Fits 0 D ∧ D.foldl lst [] = v ∧
      ncr D = ccnt (mvLay ms) ∧ (∀ i ∈ is, i < v.length) ∧
      dg RD k μ [] v (mvLay ms) - dg RD k μ [] v (chL [] D ++ dotsL v is) ∈
        Lo RD k μ [] v (ccnt (mvLay ms)) := by
  intro ms
  induction ms using List.reverseRecOn with
  | nil =>
    intro v h
    have hv : [] = v := h
    subst hv
    exact ⟨[], [], trivial, rfl, rfl, by simp, lo_of_eq (by simp [chL])⟩
  | append_singleton ms m ih =>
    intro v h
    obtain ⟨h1, h2⟩ := MvChain.of_snoc h
    obtain ⟨D, is, hD, hlet, hn, his, hdiff⟩ := ih h1
    have hA : SChain [] (mvLay ms) m.src := h1.sChain
    have hB : SChain [] (chL [] D ++ dotsL m.src is) m.src := by
      have := sChain_chL (l := []) hD
      rw [hlet] at this
      exact this.append (sChain_dotsL his)
    have Δ1 := lo_comp_dg (RD := RD) (k := k) (r := v) hdiff m.lay
    rw [← dg_sub_comp hA hB] at Δ1
    rw [mvLay_append, mvLay_singleton, ccnt_append]
    subst h2
    cases m with
    | dot u l w =>
      refine ⟨D, is ++ [u.length], hD, hlet, by rw [hn, Mv.ccnt_lay, add_zero], ?_, ?_⟩
      · intro i hi
        rcases List.mem_append.1 hi with hi | hi
        · have := his i hi; simpa [Mv.src, Mv.tgt] using this
        · simp at hi; simp [Mv.tgt, hi]
      · have e : chL [] D ++ dotsL (Mv.dot u l w).tgt (is ++ [u.length]) =
            chL [] D ++ dotsL (Mv.dot u l w).src is ++ (Mv.dot u l w).lay := by
          simp only [Mv.tgt, Mv.src, Mv.lay, dotsL_append, dotsL_cons, dotsL_nil, List.append_nil,
            List.append_assoc]
          congr 2
          simp
        rw [e]; exact Δ1
    | cup u a w =>
      have hlay : (Mv.cup u a w).lay = mvL (u ++ w) (.cup u.length a) := by
        rw [mvL_cup]; rfl
      have hsrc : (Mv.cup u a w).src = u ++ w := by simp [Mv.src]
      have htgt : (Mv.cup u a w).tgt = lst (u ++ w) (.cup u.length a) := by
        rw [lst_cup]; simp [Mv.tgt]
      rw [hsrc] at hlet his Δ1
      rw [hlay, htgt] at Δ1 ⊢
      have hm : (Move.cup u.length a : Move (Letter I)).Ok (u ++ w).length := by
        simp [Chord.Move.Ok]
      refine ⟨D ++ [.cup u.length a], is.map (mvPos (.cup u.length a)), ?_, ?_, ?_, ?_, ?_⟩
      · rw [Chord.fits_append]
        refine ⟨hD, ?_, trivial⟩
        rw [show (0 : ℕ) = ([] : List (Letter I)).length from rfl, foldl_len_eq, hlet]
        exact hm
      · rw [List.foldl_append, hlet]; rfl
      · rw [ncr_append, hn, ccnt_mvL hm]
      · intro j hj
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hj
        have := his i hi
        simp only [mvPos, Chord.lstep, lst, Chord.length_insAt (u ++ w) (by simp : u.length ≤ _)]
        split_ifs <;> omega
      · have Δ2 := dots_move (RD := RD) (k := k) hm his (chL [] D) [] μ []
          (lst (u ++ w) (.cup u.length a))
        simp only [List.append_nil, ccnt_nil, add_zero] at Δ2
        rw [ccnt_chL (l := []) hD] at Δ2
        rw [ccnt_mvL hm, ← hn] at Δ1 ⊢
        rw [chL_append, hlet]
        simp only [chL, List.append_nil]
        exact lo_sub_trans Δ1 (by simpa [List.append_assoc] using Δ2)
    | cross u x y w =>
      have hlay : (Mv.cross u x y w).lay = mvL (u ++ x :: y :: w) (.cross u.length) := by
        rw [mvL_cross]; rfl
      have hsrc : (Mv.cross u x y w).src = u ++ x :: y :: w := by simp [Mv.src]
      have htgt : (Mv.cross u x y w).tgt = lst (u ++ x :: y :: w) (.cross u.length) := by
        rw [lst_cross]; simp [Mv.tgt]
      rw [hsrc] at hlet his Δ1
      rw [hlay, htgt] at Δ1 ⊢
      have hm : (Move.cross u.length : Move (Letter I)).Ok (u ++ x :: y :: w).length := by
        simp [Chord.Move.Ok]
      refine ⟨D ++ [.cross u.length], is.map (mvPos (I := I) (.cross u.length)), ?_, ?_, ?_, ?_, ?_⟩
      · rw [Chord.fits_append]
        refine ⟨hD, ?_, trivial⟩
        rw [show (0 : ℕ) = ([] : List (Letter I)).length from rfl, foldl_len_eq, hlet]
        exact hm
      · rw [List.foldl_append, hlet]; rfl
      · rw [ncr_append, hn, ccnt_mvL hm]
      · intro j hj
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hj
        have := his i hi
        simp only [mvPos, lst, Chord.lstep, Chord.length_swapAt]
        simp only [List.length_append, List.length_cons] at this ⊢
        unfold Chord.tau; split_ifs <;> omega
      · have Δ2 := dots_move (RD := RD) (k := k) hm his (chL [] D) [] μ []
          (lst (u ++ x :: y :: w) (.cross u.length))
        simp only [List.append_nil, ccnt_nil, add_zero] at Δ2
        rw [ccnt_chL (l := []) hD] at Δ2
        rw [ccnt_mvL hm, ← hn] at Δ1 ⊢
        rw [chL_append, hlet]
        simp only [chL, List.append_nil]
        exact lo_sub_trans Δ1 (by simpa [List.append_assoc] using Δ2)

end Dots

/-! ## Dots on the canonical diagram -/

section CanonDots

open StringDiagrams.Chord (Same Valid Lettered Iso)

variable [DecidableEq I]

omit [DecidableEq I] in
theorem lo_sub_symm {μ : X} {s t : List (Letter I)} {n : ℕ} {a b}
    (h : a - b ∈ Lo RD k μ s t n) : b - a ∈ Lo RD k μ s t n := by
  rw [← neg_sub]; exact Submodule.neg_mem _ h

omit [DecidableEq I] in
/-- A dot on the right leg of a cup equals a dot on its left leg. -/
theorem dotCup (ν : X) (x : Letter I) :
    dg RD k ν [] [x, x.dual] [([], .cup x, []), ([x], .dot x.dual, [])] =
      dg RD k ν [] [x, x.dual] [([], .cup x, []), ([], .dot x, [x.dual])] := by
  obtain ⟨_ | _, i⟩ := x
  · exact dg_dot_cupDn RD k i ν
  · exact dg_dot_cupUp RD k i ν

omit [DecidableEq I] in
theorem dotAt_comm_lt {t : List (Letter I)} {i j : ℕ} (hij : i < j) (hj : j < t.length)
    (P Q : List (LayerData I)) (μ : X) (s₀ t₀ : List (Letter I)) :
    dg RD k μ s₀ t₀ (P ++ dotAt t i ++ dotAt t j ++ Q) =
      dg RD k μ s₀ t₀ (P ++ dotAt t j ++ dotAt t i ++ Q) := by
  obtain ⟨u, l, w, rfl, rfl⟩ := exists_split_dot (t := t) (i := i) (by omega)
  obtain ⟨M, l', w', rfl, hM⟩ := exists_split_dot (t := w) (i := j - u.length - 1)
    (by simp at hj; omega)
  rw [dotAt_eq, dotAt_eq' (u := u ++ l :: M) (l := l') (w := w') (by simp) (by simp; omega)]
  have E := dg_ichg (RD := RD) (k := k) (μ := μ) (s₀ := s₀) (t₀ := t₀) P Q u w'
    (A := [([], .dot l, [])]) (B := [(M, .dot l', [])]) (s := [l]) (s' := [l]) (t := M ++ [l'])
    (t' := M ++ [l']) ⟨by simp, by simp⟩ ⟨by simp, by simp⟩
  wnf at E ⊢
  exact E

omit [DecidableEq I] in
theorem dotAt_comm {t : List (Letter I)} {i j : ℕ} (hi : i < t.length) (hj : j < t.length)
    (P Q : List (LayerData I)) (μ : X) (s₀ t₀ : List (Letter I)) :
    dg RD k μ s₀ t₀ (P ++ dotAt t i ++ dotAt t j ++ Q) =
      dg RD k μ s₀ t₀ (P ++ dotAt t j ++ dotAt t i ++ Q) := by
  rcases lt_trichotomy i j with h | rfl | h
  · exact dotAt_comm_lt h hj P Q μ s₀ t₀
  · rfl
  · exact (dotAt_comm_lt h hi P Q μ s₀ t₀).symm

omit [DecidableEq I] in
/-- **Dots on distinct strands commute.** -/
theorem dotsL_perm {t : List (Letter I)} {is js : List ℕ} (h : is.Perm js) :
    (∀ i ∈ is, i < t.length) → ∀ (P Q : List (LayerData I)) (μ : X) (s₀ t₀ : List (Letter I)),
    dg RD k μ s₀ t₀ (P ++ dotsL t is ++ Q) = dg RD k μ s₀ t₀ (P ++ dotsL t js ++ Q) := by
  induction h with
  | nil => intros; rfl
  | cons x h ih =>
    intro hb P Q μ s₀ t₀
    simp only [dotsL_cons, ← List.append_assoc]
    exact ih (fun i hi => hb i (List.mem_cons_of_mem _ hi)) _ Q μ s₀ t₀
  | swap x y l =>
    intro hb P Q μ s₀ t₀
    simp only [dotsL_cons]
    have := dotAt_comm (RD := RD) (k := k) (t := t) (hb y List.mem_cons_self)
      (hb x (List.mem_cons_of_mem _ List.mem_cons_self)) P (dotsL t l ++ Q) μ s₀ t₀
    simpa [List.append_assoc] using this
  | trans h1 h2 ih1 ih2 =>
    intro hb P Q μ s₀ t₀
    exact (ih1 hb P Q μ s₀ t₀).trans (ih2 (fun i hi => hb i (h1.symm.subset hi)) P Q μ s₀ t₀)

omit [DecidableEq I] in
theorem canon_letters {s : List (ℕ × Letter I)} (hv : Valid s) (hl : Lettered Letter.dual s) :
    Fits 0 (canon s) ∧ (canon s).foldl lst [] = s.map Prod.snd := by
  obtain ⟨hf, hiso⟩ := Chord.run_canon (d := Letter.dual) _ (Nat.lt_succ_self _) hv hl
  refine ⟨hf, ?_⟩
  rw [← hiso.1, Chord.snd_run]

omit [DecidableEq I] in
theorem snd_adj {s : List (ℕ × Letter I)} (hl : Lettered Letter.dual s) {r : ℕ}
    (hr : Same s r (r + 1)) :
    (s[r + 1]'hr.lt_right).2 = (s[r]'hr.lt_left).2.dual := by
  have := hl r (r + 1) hr (by omega)
  rw [List.getElem?_eq_getElem hr.lt_left, List.getElem?_eq_getElem hr.lt_right] at this
  simpa using this

omit [DecidableEq I] in
theorem map_snd_adj {s : List (ℕ × Letter I)} (hl : Lettered Letter.dual s) {r : ℕ}
    (hr : Same s r (r + 1)) :
    s.map Prod.snd = lst ((Chord.rmAt s r).map Prod.snd) (.cup r (s[r]'hr.lt_left).2) := by
  have e := Chord.insAt_rmAt s (show r + 1 < s.length from hr.lt_right)
  conv_lhs => rw [← e]
  rw [Chord.map_insAt, snd_adj hl hr]
  rfl

/-- **A dot slides along an arc of the canonical diagram** (from one end to the other), modulo
diagrams with fewer crossings. -/
theorem arc_dot (μ : X) : ∀ (n : ℕ) {s : List (ℕ × Letter I)}, s.length + Chord.cr s < n →
    Valid s → Lettered Letter.dual s → ∀ {a c : ℕ}, Same s a c → ∀ (Q : List (LayerData I))
    (t₀ : List (Letter I)),
    dg RD k μ [] t₀ (chL [] (canon s) ++ dotAt (s.map Prod.snd) c ++ Q) -
        dg RD k μ [] t₀ (chL [] (canon s) ++ dotAt (s.map Prod.snd) a ++ Q) ∈
      Lo RD k μ [] t₀ (ncr (canon s) + ccnt Q) := by
  intro n
  induction n with
  | zero => intro s h; omega
  | succ n ih =>
  intro s hn hv hl a c hac Q t₀
  by_cases hadj : ∃ r, Same s r (r + 1)
  · classical
    obtain ⟨r, hr, hmin⟩ : ∃ r, Same s r (r + 1) ∧ ∀ r' < r, ¬ Same s r' (r' + 1) :=
      ⟨Nat.find hadj, Nat.find_spec hadj, fun _ => Nat.find_min hadj⟩
    have hl2 : r + 2 ≤ s.length := hr.lt_right
    obtain ⟨x, hx⟩ : ∃ x, x = (s[r]'hr.lt_left).2 := ⟨_, rfl⟩
    obtain ⟨t, ht⟩ : ∃ t, t = Chord.rmAt s r := ⟨_, rfl⟩
    have hvt : Valid t := ht ▸ hv.rmAt hr
    have hlt : Lettered Letter.dual t := ht ▸ hl.rmAt hl2
    obtain ⟨hft, hct⟩ := canon_letters hvt hlt
    have hmeas : t.length + Chord.cr t < n := by
      rw [ht, Chord.length_rmAt s hl2]; have := Chord.cr_rmAt_le (s := s) hl2; omega
    have hv' : s.map Prod.snd = lst (t.map Prod.snd) (.cup r x) := by
      rw [ht, hx]; exact map_snd_adj hl hr
    have hm : (Move.cup r x : Move (Letter I)).Ok (t.map Prod.snd).length := by
      simp [Chord.Move.Ok, ht, Chord.length_rmAt s hl2]; omega
    have hch : chL [] (canon s) = chL [] (canon t) ++ mvL (t.map Prod.snd) (.cup r x) := by
      rw [Chord.canon_adj hv hr hmin, ← ht, ← hx, chL_append, hct]; simp [chL]
    have hncr : ncr (canon s) = ncr (canon t) := by
      rw [Chord.canon_adj hv hr hmin, ← ht, ncr_append]; simp [ncr]
    rw [hch, hncr, hv']
    have hP := ccnt_chL (l := []) hft
    obtain ⟨u, w, huw, hu⟩ := exists_split_cup (l := t.map Prod.snd) (g := r) hm
    by_cases hc : c = r ∨ c = r + 1
    · -- the dot is on the cup created last
      have key : dg RD k μ [] t₀ (chL [] (canon t) ++ mvL (t.map Prod.snd) (.cup r x) ++
            dotAt (lst (t.map Prod.snd) (.cup r x)) (r + 1) ++ Q) =
          dg RD k μ [] t₀ (chL [] (canon t) ++ mvL (t.map Prod.snd) (.cup r x) ++
            dotAt (lst (t.map Prod.snd) (.cup r x)) r ++ Q) := by
        rw [huw, ← hu, mvL_cup, lst_cup,
          dotAt_eq' (u := u ++ [x]) (l := x.dual) (w := w) (by simp) (by simp), dotAt_eq]
        refine dg_step_free (chL [] (canon t)) Q u w (dotCup (RD := RD) (k := k) _ x)
          ⟨by simp, by simp⟩ ⟨by simp, by simp⟩ (by simp) (by simp) ?_ ?_
        · wnf
        · wnf
      rcases hc with rfl | rfl
      · have ha : a = c + 1 := hv.unique hac.symm hr
        subst ha
        exact lo_of_eq key.symm
      · have ha : a = r := hv.unique hac.symm hr.symm
        subst ha
        exact lo_of_eq key
    · have ha : ¬ (a = r ∨ a = r + 1) := by
        rintro (rfl | rfl)
        · exact hc (Or.inr (hv.unique hac hr))
        · exact hc (Or.inl (hv.unique hac hr.symm))
      set c' := if c < r then c else c - 2 with hc'
      set a' := if a < r then a else a - 2 with ha'
      have ec : mvPos (.cup r x) c' = c := by simp only [mvPos, hc']; split_ifs <;> omega
      have ea : mvPos (.cup r x) a' = a := by simp only [mvPos, ha']; split_ifs <;> omega
      have hac' : Same t a' c' := by
        rw [ht, Chord.same_rmAt hl2]
        have e1 : Chord.rmIdx r a' = a := by simp only [Chord.rmIdx, ha']; split_ifs <;> omega
        have e2 : Chord.rmIdx r c' = c := by simp only [Chord.rmIdx, hc']; split_ifs <;> omega
        rw [e1, e2]; exact hac
      have hcl : c' < (t.map Prod.snd).length := by simpa using hac'.lt_right
      have hal : a' < (t.map Prod.snd).length := by simpa using hac'.lt_left
      have h1 := dot_move (RD := RD) (k := k) hm hcl (chL [] (canon t)) Q μ [] t₀
      have h2 := ih hmeas hvt hlt hac' (mvL (t.map Prod.snd) (.cup r x) ++ Q) t₀
      have h3 := dot_move (RD := RD) (k := k) hm hal (chL [] (canon t)) Q μ [] t₀
      rw [ec] at h1
      rw [ea] at h3
      simp only [ccnt_append, ccnt_mvL hm, hP] at h1 h2 h3
      simp only [List.append_assoc] at h1 h2 h3 ⊢
      have := lo_sub_trans (lo_sub_symm h1) (lo_sub_trans (by simpa [ncr] using h2) h3)
      simpa [ncr] using this
  · have hno : ∀ r, ¬ Same s r (r + 1) := fun r hr => hadj ⟨r, hr⟩
    have hne : s ≠ [] := by rintro rfl; have := hac.lt_left; simp at this
    obtain ⟨q, ho, hcl, hq, -⟩ := Chord.canon_cross hv hno hne
    have hilv := Chord.ilv_of_opn_cls hv (hno q) ho hcl
    have hql := hilv.lt
    set t := Chord.swapAt s q with ht
    have hvt : Valid t := hv.swapAt hql
    have hlt : Lettered Letter.dual t := hl.swapAt hql (hno q)
    obtain ⟨hft, hct⟩ := canon_letters hvt hlt
    have hmeas : t.length + Chord.cr t < n := by
      rw [ht, Chord.length_swapAt]; have := Chord.cr_swapAt_lt hv hilv; omega
    have hv' : s.map Prod.snd = lst (t.map Prod.snd) (.cross q) := by
      simp only [lst, Chord.lstep, ht, ← Chord.map_swapAt, Chord.swapAt_swapAt]
    have hm : (Move.cross q : Move (Letter I)).Ok (t.map Prod.snd).length := by
      simpa [Chord.Move.Ok, ht] using hql
    have hch : chL [] (canon s) = chL [] (canon t) ++ mvL (t.map Prod.snd) (.cross q) := by
      rw [hq, chL_append, hct]; simp [chL]
    have hncr : ncr (canon s) = ncr (canon t) + 1 := by
      rw [hq, ncr_append]; simp [ncr]
    rw [hch, hncr, hv']
    have hP := ccnt_chL (l := []) hft
    have hac' : Same t (Chord.tau q a) (Chord.tau q c) := by
      rw [ht, Chord.same_swapAt hql, Chord.tau_tau, Chord.tau_tau]; exact hac
    have hcl' : Chord.tau q c < (t.map Prod.snd).length := by simpa using hac'.lt_right
    have hal' : Chord.tau q a < (t.map Prod.snd).length := by simpa using hac'.lt_left
    have h1 := dot_move (RD := RD) (k := k) hm hcl' (chL [] (canon t)) Q μ [] t₀
    have h2 := ih hmeas hvt hlt hac' (mvL (t.map Prod.snd) (.cross q) ++ Q) t₀
    have h3 := dot_move (RD := RD) (k := k) hm hal' (chL [] (canon t)) Q μ [] t₀
    simp only [mvPos, Chord.tau_tau] at h1 h3
    simp only [ccnt_append, ccnt_mvL hm, hP] at h1 h2 h3
    simp only [List.append_assoc] at h1 h2 h3 ⊢
    rw [← add_assoc] at h2
    exact lo_sub_trans (lo_sub_symm h1) (lo_sub_trans h2 h3)

/-- The left end of the arc through the position `i`. -/
noncomputable def lEnd (s : List (ℕ × Letter I)) (i : ℕ) : ℕ := by
  classical
  exact if h : ∃ j, j < i ∧ Same s i j then Nat.find h else i

omit [DecidableEq I] in
theorem lEnd_spec (s : List (ℕ × Letter I)) (i : ℕ) :
    (lEnd s i = i ∧ ¬ ∃ j, j < i ∧ Same s i j) ∨ (lEnd s i < i ∧ Same s i (lEnd s i)) := by
  classical
  unfold lEnd
  split_ifs with h
  · exact Or.inr ⟨(Nat.find_spec h).1, (Nat.find_spec h).2⟩
  · exact Or.inl ⟨rfl, h⟩

omit [DecidableEq I] in
theorem lEnd_isLeft {s : List (ℕ × Letter I)} (hv : Valid s) (i : ℕ) :
    ¬ ∃ j, j < lEnd s i ∧ Same s (lEnd s i) j := by
  rcases lEnd_spec s i with ⟨e, h⟩ | ⟨hlt, h⟩
  · rwa [e]
  · rintro ⟨j, hj, hs⟩
    have := hv.unique h.symm hs
    omega

omit [DecidableEq I] in
theorem lEnd_lt {s : List (ℕ × Letter I)} {i : ℕ} (hi : i < s.length) : lEnd s i < s.length := by
  rcases lEnd_spec s i with ⟨e, -⟩ | ⟨hlt, -⟩ <;> omega

/-- **Dots move to the left ends of their arcs**, modulo diagrams with fewer crossings. -/
theorem dots_left (μ : X) {s : List (ℕ × Letter I)} (hv : Valid s) (hl : Lettered Letter.dual s) :
    ∀ (is : List ℕ), (∀ i ∈ is, i < s.length) → ∀ (Q : List (LayerData I)) (t₀ : List (Letter I)),
    dg RD k μ [] t₀ (chL [] (canon s) ++ dotsL (s.map Prod.snd) is ++ Q) -
        dg RD k μ [] t₀ (chL [] (canon s) ++ dotsL (s.map Prod.snd) (is.map (lEnd s)) ++ Q) ∈
      Lo RD k μ [] t₀ (ncr (canon s) + ccnt Q)
  | [], _, Q, t₀ => lo_of_eq rfl
  | i :: is, h, Q, t₀ => by
    have hi : i < s.length := h i List.mem_cons_self
    have his : ∀ j ∈ is, j < s.length := fun j hj => h j (List.mem_cons_of_mem _ hj)
    have hb : ∀ j ∈ is, j < (s.map Prod.snd).length := by simpa using his
    have hL : lEnd s i < (s.map Prod.snd).length := by simpa using lEnd_lt hi
    have hbm : ∀ j ∈ is.map (lEnd s), j < (s.map Prod.snd).length := by
      intro j hj
      obtain ⟨j', hj', rfl⟩ := List.mem_map.1 hj
      simpa using lEnd_lt (his j' hj')
    -- the first dot moves to the left end of its arc
    have step1 : dg RD k μ [] t₀ (chL [] (canon s) ++ dotAt (s.map Prod.snd) i ++
          (dotsL (s.map Prod.snd) is ++ Q)) -
        dg RD k μ [] t₀ (chL [] (canon s) ++ dotAt (s.map Prod.snd) (lEnd s i) ++
          (dotsL (s.map Prod.snd) is ++ Q)) ∈ Lo RD k μ [] t₀ (ncr (canon s) + ccnt Q) := by
      rcases lEnd_spec s i with ⟨e, -⟩ | ⟨-, hs⟩
      · rw [e]; exact lo_of_eq rfl
      · have := arc_dot (RD := RD) (k := k) μ _ (Nat.lt_succ_self _) hv hl hs.symm
          (dotsL (s.map Prod.snd) is ++ Q) t₀
        simpa [ccnt_append] using this
    -- the other dots, by induction
    have step2 := dots_left μ hv hl is his (dotAt (s.map Prod.snd) (lEnd s i) ++ Q) t₀
    have p1 := dotsL_perm (RD := RD) (k := k) (t := s.map Prod.snd)
      (List.perm_middle (a := lEnd s i) (l₁ := is) (l₂ := []))
      (by intro j hj; simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hj
          rcases hj with hj | rfl; exacts [hb j hj, hL])
      (chL [] (canon s)) Q μ [] t₀
    have p2 := dotsL_perm (RD := RD) (k := k) (t := s.map Prod.snd)
      (List.perm_middle (a := lEnd s i) (l₁ := is.map (lEnd s)) (l₂ := []))
      (by intro j hj; simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hj
          rcases hj with hj | rfl; exacts [hbm j hj, hL])
      (chL [] (canon s)) Q μ [] t₀
    simp only [dotsL_append, dotsL_cons, dotsL_nil, List.append_nil, List.append_assoc] at p1 p2
    simp only [ccnt_append, ccnt_dotAt, zero_add] at step1 step2
    simp only [dotsL_cons, List.map_cons, List.append_assoc] at step1 step2 ⊢
    rw [← p1] at step1
    rw [p2] at step2
    exact lo_sub_trans step1 step2

end CanonDots

/-! ## Spanning -/

section Span

open StringDiagrams.Chord (Same Valid Lettered)

variable [DecidableEq I]

variable (RD k) in
/-- The span of the canonical diagrams with dots at the left ends of their arcs, followed by
elements of the image of `Π_μ` on the far right. -/
def CanonSpan (μ : X) (v : List (Letter I)) :
    Submodule k ((pres RD k).obj (ob RD μ []) ⟶ (pres RD k).obj (ob RD μ v)) :=
  Submodule.span k {f | ∃ (s : List (ℕ × Letter I)) (is : List ℕ)
    (β : End ((pres RD k).obj (ob RD μ []))), Valid s ∧ Lettered Letter.dual s ∧
      s.map Prod.snd = v ∧ (∀ i ∈ is, i < s.length ∧ ¬ ∃ j, j < i ∧ Same s i j) ∧
      IsBub RD k μ β ∧ f = dg RD k μ [] v (chL [] (canon s) ++ dotsL v is) ≫ bubAt RD k μ v β}

omit [DecidableEq I] in
theorem thruShort_nil (μ : X) (v : List (Letter I)) : thruShort RD k μ [] v = ⊥ := by
  rw [thruShort, Submodule.span_eq_bot]
  rintro _ ⟨u, g, h, hu, rfl⟩
  simp at hu

omit [DecidableEq I] in
theorem dual_involutive : Function.Involutive (Letter.dual (I := I)) := Letter.dual_dual

omit [DecidableEq I] in
/-- Composing with bubbles on the far right preserves lower terms (any source and target; the
endomorphism version is `lo_comp_bubAt_mem`). -/
theorem lo_comp_bubAt_mem_of {μ : X} {s t : List (Letter I)} {n : ℕ} {f}
    (hf : f ∈ Lo RD k μ s t n) {β : End ((pres RD k).obj (ob RD μ []))} (hβ : IsBub RD k μ β) :
    f ≫ bubAt RD k μ t β ∈ Lo RD k μ s t n := by
  have hb : bubAt RD k μ t β ∈ LeL RD k μ t t 0 := by
    have := ctxL_leL (RD := RD) (k := k) (μ := μ) (s₀ := t) (t₀ := t) (pre := []) (post := [])
      (u := t) (v := []) (s := []) (t := []) (isBub_mem_leL hβ)
    convert this using 1 <;> rfl
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨L, hL, rfl⟩ := hf
    have := leL_comp (dg_mem_leL (s := s) (t := t) (le_refl (ccnt L))) hb
    exact leL_le_lo (by omega) this
  | zero => rw [Limits.zero_comp]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Preadditive.add_comp]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [Linear.smul_comp]; exact Submodule.smul_mem _ r hx

/-- **A move diagram with bubbles lies in the canonical span modulo lower terms.** -/
theorem mvSp_gen_mem (μ : X) {v : List (Letter I)} {ms : List (Mv I)} (hch : MvChain [] ms v)
    {β : End ((pres RD k).obj (ob RD μ []))} (hβ : IsBub RD k μ β) :
    dg RD k μ [] v (mvLay ms) ≫ bubAt RD k μ v β ∈
      CanonSpan RD k μ v ⊔ Lo RD k μ [] v (ccnt (mvLay ms)) := by
  obtain ⟨D, is, hD, hlet, hn, his, hdiff⟩ := mv_to_chord (RD := RD) (k := k) μ ms hch
  have hsD : SChain [] (chL [] D) v := by
    have := sChain_chL (l := []) hD; rwa [hlet] at this
  -- the dots can be taken on top
  have e1 : dg RD k μ [] v (mvLay ms) ≫ bubAt RD k μ v β =
      (dg RD k μ [] v (mvLay ms) - dg RD k μ [] v (chL [] D ++ dotsL v is)) ≫ bubAt RD k μ v β +
        dg RD k μ [] v (chL [] D) ≫ dg RD k μ v v (dotsL v is) ≫ bubAt RD k μ v β := by
    rw [Preadditive.sub_comp, dg_append_of_left hsD, Category.assoc, sub_add_cancel]
  rw [e1]
  refine Submodule.add_mem _ (Submodule.mem_sup_right (lo_comp_bubAt_mem_of hdiff hβ)) ?_
  rcases chL_normal_form (RD := RD) (k := k) hD μ v with h | ⟨hfc, hnc, hdc⟩
  · refine Submodule.mem_sup_right ?_
    rw [← Category.assoc]
    have := lo_comp_bubAt_mem_of (lo_comp_dg (r := v) h (dotsL v is)) hβ
    rwa [ccnt_dotsL, add_zero, hn] at this
  · obtain ⟨s, hs⟩ : ∃ s, s = run Letter.dual D := ⟨_, rfl⟩
    rw [← hs] at hfc hnc hdc
    have hvs : Valid s := hs ▸ (Chord.inv_run hD).1
    have hls : Lettered Letter.dual s := hs ▸ Chord.lettered_run dual_involutive hD
    have hsv : s.map Prod.snd = v := by rw [hs, Chord.snd_run, ← hlet]
    have hsc : SChain [] (chL [] (canon s)) v := by
      have := sChain_chL (l := []) hfc
      rwa [(canon_letters hvs hls).2, hsv] at this
    have e2 : dg RD k μ [] v (chL [] D) ≫ dg RD k μ v v (dotsL v is) ≫ bubAt RD k μ v β =
        ((dg RD k μ [] v (chL [] D) - dg RD k μ [] v (chL [] (canon s))) ≫
          dg RD k μ v v (dotsL v is)) ≫ bubAt RD k μ v β +
        ((dg RD k μ [] v (chL [] (canon s) ++ dotsL v is) -
          dg RD k μ [] v (chL [] (canon s) ++ dotsL v (is.map (lEnd s)))) ≫ bubAt RD k μ v β +
        dg RD k μ [] v (chL [] (canon s) ++ dotsL v (is.map (lEnd s))) ≫ bubAt RD k μ v β) := by
      rw [dg_append_of_left hsc]
      simp only [Preadditive.sub_comp, Category.assoc]
      abel
    rw [e2]
    refine Submodule.add_mem _ (Submodule.mem_sup_right ?_) (Submodule.add_mem _
      (Submodule.mem_sup_right ?_) (Submodule.mem_sup_left (Submodule.subset_span ?_)))
    · have := lo_comp_bubAt_mem_of (lo_comp_dg (r := v) hdc (dotsL v is)) hβ
      rwa [ccnt_dotsL, add_zero, hn] at this
    · have his' : ∀ i ∈ is, i < s.length := by rw [← hsv] at his; simpa using his
      have := dots_left (RD := RD) (k := k) μ hvs hls is his' [] v
      rw [hsv] at this
      simp only [List.append_nil, ccnt_nil, add_zero, hnc, hn] at this
      exact lo_comp_bubAt_mem_of this hβ
    · refine ⟨s, is.map (lEnd s), β, hvs, hls, hsv, fun i hi => ?_, hβ, rfl⟩
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hi
      have hj' : j < s.length := by rw [← hsv] at his; simpa using his j hj
      exact ⟨lEnd_lt hj', lEnd_isLeft hvs j⟩

variable {k : Type w} [Field k]

/-- **The canonical diagrams span** `HOM_U(1_μ, E_v 1_μ)` (any Cartan datum): every 2-morphism
`1_μ ⟶ E_v 1_μ` is a linear combination of canonical diagrams of pairings of `v`, with dots at
the left ends of their arcs, followed by elements of the image of `Π_μ`. -/
theorem mem_canonSpan (μ : X) (v : List (Letter I))
    (f : (pres RD k).obj (ob RD μ []) ⟶ (pres RD k).obj (ob RD μ v)) :
    f ∈ CanonSpan RD k μ v := by
  have key : ∀ c (L : List (LayerData I)), ccnt L ≤ c → dg RD k μ [] v L ∈ CanonSpan RD k μ v := by
    intro c
    induction c using Nat.strong_induction_on with
    | _ c ihc =>
    intro L hL
    have hlo : ∀ n ≤ c, Lo RD k μ [] v n ≤ CanonSpan RD k μ v := by
      intro n hn
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨L', hL', rfl⟩
      exact ihc (ccnt L') (by omega) L' le_rfl
    have hcap := capElim (RD := RD) (k := k) (μ := μ) (w₀ := []) c v L hL
    rw [CapTarget, thruShort_nil, sup_bot_eq, MvSp] at hcap
    generalize dg RD k μ [] v L = x at hcap
    induction hcap using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨ms, β, hch, hcc, hβ, rfl⟩ := hx
      have h := mvSp_gen_mem (RD := RD) (k := k) μ hch hβ
      exact (sup_le le_rfl (hlo _ hcc)) h
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul r x _ hx => exact Submodule.smul_mem _ r hx
  have hf := mem_span_dg (RD := RD) (k := k) μ f
  refine (Submodule.span_le.mpr ?_) hf
  rintro _ ⟨L, -, rfl⟩
  exact key _ L le_rfl

end Span

end Categorification.KL3.Diagram

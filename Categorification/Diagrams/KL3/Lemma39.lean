/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.SortDecomp
import Categorification.Diagrams.KL3.EndOneGraded

/-!
# KL III Lemma 3.9, Proposition 3.10 and Proposition 3.6

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.2.1
(Proposition 3.6, label `prop_bubbles_same_orient`) and §3.2.2 (Lemma 3.9, label
`lem_surjective`; Proposition 3.10). TeX locators `sources/klr/kl3/0807.3250v1.txt`, lines
1690–1790.

KL III prove Lemma 3.9 ("`ϕ_{i,j,λ}` is surjective") by a reduction of crossings following
A. Lauda, arXiv:0803.3652v3, §8, which uses a theorem on planar 4-valent graphs (Carpentier's
triangle moves). We give a different proof, which uses no planar topology: every 2-morphism
between upward sequences is processed one layer at a time, and the intermediate 1-morphisms are
sorted by the decompositions of `E_i F_j` and `F_j E_i` (`decR`, `decL`).

## The argument

Fix an upward sequence `s` and the rightmost region `μ`. Call a 2-morphism
`f : E_s 1_μ → E_a F_b 1_μ` (target sorted to the right) **good** (`GoodR`) if it is obtained
from an element of `upSpan` (upward diagrams followed by bubble monomials) by unbending the
downward strands `F_b` on the right (`unbendR`), times a bubble monomial; and similarly
`g : E_s 1_μ → F_d E_c 1_μ` (sorted to the left) is **good** (`GoodL`) if it is obtained from an
element of `upSpan` by unbending on the left.

* **R → L.** If `f` is good and `m : E_a F_b → F_d E_c` is a *monotone* diagram of type `RL`
  (cups `1 → F E`, caps `E F → 1`, dots, crossings), then `f ≫ m` is good (`goodR_comp`):
  bending the downward strands of `m` at its bottom right up and those at its top left down
  gives a monotone diagram `m♯` between upward sequences (`sharpL`), which is an upward diagram
  (`straightenRL`); `f ≫ m` is then the left unbending of the right partial trace of
  `(1 ⊗ f♭) ≫ m♯` (interchange law and zigzag relations, `dg_unbend_sharp`), which lies in
  `upSpan` by the Markov lemma for blocks (`ptrRL_mem_upSpan`).
* **L → R.** Symmetrically with monotone diagrams of type `LR` and the left partial trace
  (`goodL_comp`).
* **One layer.** If `f : E_s → E_w` is such that `f ≫ p` is good for every monotone
  `p : E_w → E_a F_b` of type `LR` (`LayerInv`), then so is `f ≫ L` for every layer `L`
  (`inv_step`): write `1_{E_w}` by `decR` as a sum of `p ≫ q` (`q` monotone of type `RL`), and
  `1` at the source or target of `L` by `decL`; every layer is a dot, a crossing, or a cup or cap
  of one of the two monotone types, so that `f ≫ p ≫ q ≫ L ≫ …` is processed by one step
  `R → L` and one step `L → R`.
* Every normal-form diagram between upward sequences is thus good, i.e. lies in `upSpan`.

The bubble slides (KL III Propositions 3.3, 3.4) and the Markov lemmas use simply-laced Cartan
data; accordingly the results assume `SimplyLaced C`.

## Main results

* `upSpanDiag_of_simplyLaced`: **KL III Lemma 3.9 in diagrammatic form** (`UpSpanDiag RD k μ`,
  for every `μ`).
* `endUpSpan_of_simplyLaced`: its one-strand case.
* `prop310_of_simplyLaced`: **KL III Proposition 3.10**:
  `ϕ_{ν,λ} : R(ν) ⊗ Π_λ → END_U(E_ν 1_λ)` is surjective.
* `prop36_of_simplyLaced`: **KL III Proposition 3.6**: `Π_λ → END_U(1_λ)` is surjective.
* `cor37_gdim_le_pi_of_simplyLaced`, `cor37_finrank_le_of_simplyLaced`,
  `cor37_HDe_neg_of_simplyLaced`, `cor37_HDe_zero_of_simplyLaced`, `cor37_isUnit_of_simplyLaced`:
  **KL III Corollary 3.7** (`gdim HOM_U(1_λ, 1_λ) ≤ π`, nonnegatively graded with degree-zero part
  `k · 1`, "local graded ring"), from the conditional versions of
  `Categorification.Diagrams.KL3.EndOneGraded`.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {k : Type w} [CommRing k]

/-! ## Good 2-morphisms -/

variable (RD k) in
/-- 2-morphisms `E_s 1_μ → E_a F_b 1_μ` obtained from `upSpan` by unbending the downward strands
on the right, times a bubble monomial. -/
def GoodR (μ : X) (s : List (Letter I)) (a b : List I) :
    Submodule k ((pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ (ups a ++ dns b))) :=
  Submodule.span k {f | ∃ (δ : End ((pres RD k).obj (ob RD μ [])))
    (x : (pres RD k).obj (ob RD (wt RD μ (dns b)) (s ++ rd (dns b))) ⟶
      (pres RD k).obj (ob RD (wt RD μ (dns b)) (ups a))),
    IsBub RD k μ δ ∧ x ∈ upSpan RD k (wt RD μ (dns b)) (s ++ rd (dns b)) (ups a) ∧
      f = bubAt RD k μ s δ ≫ unbendR RD k μ b s (ups a) x}

variable (RD k) in
/-- 2-morphisms `E_s 1_μ → F_d E_c 1_μ` obtained from `upSpan` by unbending the downward strands
on the left, times a bubble monomial. -/
def GoodL (μ : X) (s : List (Letter I)) (d c : List I) :
    Submodule k ((pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ (dns d ++ ups c))) :=
  Submodule.span k {f | ∃ (δ : End ((pres RD k).obj (ob RD μ [])))
    (y : (pres RD k).obj (ob RD (wt RD μ []) (rd (dns d) ++ s)) ⟶
      (pres RD k).obj (ob RD (wt RD μ []) (ups c))),
    IsBub RD k μ δ ∧ y ∈ upSpan RD k (wt RD μ []) (rd (dns d) ++ s) (ups c) ∧
      f = bubAt RD k μ s δ ≫ unbendL RD k μ d s (ups c) y}

theorem goodR_bub {μ : X} {s : List (Letter I)} {a b : List I}
    {δ : End ((pres RD k).obj (ob RD μ []))} (hδ : IsBub RD k μ δ) {f}
    (hf : f ∈ GoodR RD k μ s a b) : bubAt RD k μ s δ ≫ f ∈ GoodR RD k μ s a b := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨δ', x, hδ', hx, rfl⟩ := hf
    exact Submodule.subset_span ⟨δ ≫ δ', x, hδ.comp hδ', hx, by rw [bubAt_comp, Category.assoc]⟩
  | zero => rw [Limits.comp_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Preadditive.comp_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [Linear.comp_smul]; exact Submodule.smul_mem _ r hx

theorem goodL_bub {μ : X} {s : List (Letter I)} {d c : List I}
    {δ : End ((pres RD k).obj (ob RD μ []))} (hδ : IsBub RD k μ δ) {f}
    (hf : f ∈ GoodL RD k μ s d c) : bubAt RD k μ s δ ≫ f ∈ GoodL RD k μ s d c := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨δ', y, hδ', hy, rfl⟩ := hf
    exact Submodule.subset_span ⟨δ ≫ δ', y, hδ.comp hδ', hy, by rw [bubAt_comp, Category.assoc]⟩
  | zero => rw [Limits.comp_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Preadditive.comp_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [Linear.comp_smul]; exact Submodule.smul_mem _ r hx

/-! ## The exchange identities -/

/-- **R → L at the level of diagrams**: an unbent upward diagram (with a closed diagram `B`
inserted to the right of it) followed by `M` is the left unbending of the right partial trace of
the bent diagram, with `M` replaced by its bent form `A'` (interchange law, zigzags). -/
theorem core_RL_dg (μ : X) {s : List (Letter I)} {a b d c : List I}
    {A M A' B : List (LayerData I)} (hA : SChain (s ++ rd (dns b)) A (ups a))
    (hM : SChain (ups a ++ dns b) M (dns d ++ ups c))
    (hE : dg RD k (wt RD μ (dns b)) (rd (dns d) ++ ups a) (ups c ++ rd (dns b))
      (sharpL (dns d) (dns b) (ups a) (ups c) M) =
        dg RD k (wt RD μ (dns b)) (rd (dns d) ++ ups a) (ups c ++ rd (dns b)) A')
    (hB : SChain [] B []) :
    dg RD k μ s (dns d ++ ups c) ((cupA (rd (dns b))).map (whL s []) ++
        (A ++ B.map (whL (ups a) [])).map (whL [] (dns b)) ++ M) =
      dg RD k μ s (dns d ++ ups c) ((cupA (dns d)).map (whL [] s) ++
        ((cupA (rd (dns b))).map (whL (rd (dns d) ++ s) []) ++
          (A.map (whL (rd (dns d)) []) ++ A' ++ B.map (whL (ups c ++ rd (dns b)) [])).map
            (whL [] (dns b)) ++ (capA (dns b)).map (whL (ups c) [])).map (whL (dns d) [])) := by
  set D := dns d
  set E := dns b
  set d' := rd D
  set b' := rd E
  have hcD : SChain s ((cupA D).map (whL [] s)) (D ++ d' ++ s) := by
    simpa using (sChain_cupA D).whisk [] s
  have hcb : SChain (D ++ d' ++ s) ((cupA b').map (whL (D ++ d' ++ s) []))
      (D ++ d' ++ s ++ b' ++ E) := by
    have := (sChain_cupA b').whisk (D ++ d' ++ s) []
    simp only [rd_rd, b'] at this ⊢
    simpa using this
  have hAw : SChain (D ++ d' ++ s ++ b' ++ E) (A.map (whL (D ++ d') E))
      (D ++ d' ++ ups a ++ E) := by
    simpa using hA.whisk (D ++ d') E
  have hsh := sChain_sharpL (p := D) (q := E) (x := ups a) (y := ups c) hM
  have hsh' : SChain (D ++ d' ++ ups a ++ E) ((sharpL D E (ups a) (ups c) M).map (whL D E))
      (D ++ ups c ++ b' ++ E) := by simpa using hsh.whisk D E
  have hBw : SChain (D ++ ups c ++ b' ++ E) (B.map (whL (D ++ ups c ++ b') E))
      (D ++ ups c ++ b' ++ E) := by simpa using hB.whisk (D ++ ups c ++ b') E
  have hcap : SChain (D ++ ups c ++ b' ++ E) ((capA E).map (whL (D ++ ups c) [])) (D ++ ups c) := by
    simpa using (sChain_capA E).whisk (D ++ ups c) []
  -- (i) the upward diagram `A'` is the bent form of `M`
  have h1 := dg_step RD k μ (s₀ := s) (t₀ := D ++ ups c)
    ((cupA D).map (whL [] s) ++ (cupA b').map (whL (D ++ d' ++ s) []) ++ A.map (whL (D ++ d') E))
    (B.map (whL (D ++ ups c ++ b') E) ++ (capA E).map (whL (D ++ ups c) [])) D E hE.symm
    (by simpa using (hcD.append hcb).append hAw) (by simpa using hBw.append hcap) rfl rfl
  -- (ii) the closed diagram `B` moves below the bent form of `M`
  have h2 := dg_closed_left (RD := RD) (k := k) μ (S := s) (T := D ++ ups c)
    ((cupA D).map (whL [] s) ++ (cupA b').map (whL (D ++ d' ++ s) []) ++ A.map (whL (D ++ d') E))
    ((capA E).map (whL (D ++ ups c) [])) (s := D ++ d' ++ ups a) (s' := D ++ ups c ++ b') E hB
    (A := (sharpL D E (ups a) (ups c) M).map (whL D [])) (by simpa using hsh.whisk D [])
  -- (iii) the cups on the left move above the unbent upward diagram
  have hX : SChain s ((cupA b').map (whL s []) ++ A.map (whL [] E) ++ B.map (whL (ups a) E))
      (ups a ++ E) := by
    have x1 : SChain s ((cupA b').map (whL s [])) (s ++ b' ++ E) := by
      simpa [b', rd_rd] using (sChain_cupA b').whisk s []
    have x2 : SChain (s ++ b' ++ E) (A.map (whL [] E)) (ups a ++ E) := by
      simpa using hA.whisk [] E
    have x3 : SChain (ups a ++ E) (B.map (whL (ups a) E)) (ups a ++ E) := by
      simpa using hB.whisk (ups a) E
    exact (x1.append x2).append x3
  have h3 := dg_interchange (RD := RD) (k := k) (μ := μ) (S := s) (T := D ++ ups c) []
    ((sharpL D E (ups a) (ups c) M).map (whL D E) ++ (capA E).map (whL (D ++ ups c) []))
    (sChain_cupA D) hX
  -- (iv) unbending the bent form of `M` gives `M`
  have h4 := dg_step RD k μ (s₀ := s) (t₀ := D ++ ups c)
    ((cupA b').map (whL s []) ++ A.map (whL [] E) ++ B.map (whL (ups a) E)) [] [] []
    (dg_unbend_sharp D E (ups a) (ups c) hM (wt RD μ [])) (by simpa using hX) (by simp) rfl rfl
  symm
  calc dg RD k μ s (D ++ ups c) ((cupA D).map (whL [] s) ++ ((cupA b').map (whL (d' ++ s) []) ++
        (A.map (whL d' []) ++ A' ++ B.map (whL (ups c ++ b') [])).map (whL [] E) ++
          (capA E).map (whL (ups c) [])).map (whL D []))
      = dg RD k μ s (D ++ ups c) (((cupA D).map (whL [] s) ++
          (cupA b').map (whL (D ++ d' ++ s) []) ++ A.map (whL (D ++ d') E)) ++ A'.map (whL D E) ++
            (B.map (whL (D ++ ups c ++ b') E) ++ (capA E).map (whL (D ++ ups c) []))) :=
        dg_list_eq (by laysimp)
    _ = _ := h1
    _ = dg RD k μ s (D ++ ups c) (((cupA D).map (whL [] s) ++
          (cupA b').map (whL (D ++ d' ++ s) []) ++ A.map (whL (D ++ d') E)) ++
          ((sharpL D E (ups a) (ups c) M).map (whL D [])).map (whL [] E) ++
            B.map (whL (D ++ ups c ++ b') E) ++ (capA E).map (whL (D ++ ups c) [])) :=
        dg_list_eq (by laysimp)
    _ = _ := h2
    _ = dg RD k μ s (D ++ ups c) ([] ++ (cupA D).map (whL [] s) ++
          ((cupA b').map (whL s []) ++ A.map (whL [] E) ++ B.map (whL (ups a) E)).map
            (whL (D ++ d') []) ++ ((sharpL D E (ups a) (ups c) M).map (whL D E) ++
              (capA E).map (whL (D ++ ups c) []))) := dg_list_eq (by laysimp)
    _ = _ := h3
    _ = dg RD k μ s (D ++ ups c) (((cupA b').map (whL s []) ++ A.map (whL [] E) ++
          B.map (whL (ups a) E)) ++ ((cupA D).map (whL [] (ups a ++ E)) ++
            (sharpL D E (ups a) (ups c) M).map (whL D E) ++ (capA E).map (whL (D ++ ups c) [])).map
              (whL [] []) ++ []) := dg_list_eq (by laysimp)
    _ = _ := h4
    _ = dg RD k μ s (D ++ ups c) ((cupA b').map (whL s []) ++
          (A ++ B.map (whL (ups a) [])).map (whL [] E) ++ M) := dg_list_eq (by laysimp)

/-- **L → R at the level of diagrams**: a diagram unbent on the left followed by `M` is the right
unbending of the left partial trace of the bent diagram, with `M` replaced by its bent form
`A''` (interchange law, zigzags). -/
theorem core_LR_dg (μ : X) {s : List (Letter I)} {d a c b : List I}
    {B M A'' : List (LayerData I)} (hB : SChain (rd (dns d) ++ s) B (ups a))
    (hM : SChain (dns d ++ ups a) M (ups c ++ dns b))
    (hE : dg RD k (wt RD μ (dns b)) (ups a ++ rd (dns b)) (rd (dns d) ++ ups c)
      (flatL (rd (dns d)) (rd (dns b)) (ups a) (ups c) M) =
        dg RD k (wt RD μ (dns b)) (ups a ++ rd (dns b)) (rd (dns d) ++ ups c) A'') :
    dg RD k μ s (ups c ++ dns b) ((cupA (dns d)).map (whL [] s) ++ B.map (whL (dns d) []) ++ M) =
      dg RD k μ s (ups c ++ dns b) ((cupA (rd (dns b))).map (whL s []) ++
        ((cupA (dns d)).map (whL [] (s ++ rd (dns b))) ++
          (B.map (whL [] (rd (dns b))) ++ A'').map (whL (dns d) []) ++
            (capA (rd (dns d))).map (whL [] (ups c))).map (whL [] (dns b))) := by
  set D := dns d
  set E := dns b
  have hcb : SChain s ((cupA (rd E)).map (whL s [])) (s ++ rd E ++ E) := by
    simpa [rd_rd] using (sChain_cupA (rd E)).whisk s []
  have hcD : SChain (s ++ rd E ++ E) ((cupA D).map (whL [] (s ++ rd E ++ E)))
      (D ++ rd D ++ s ++ rd E ++ E) := by
    simpa using (sChain_cupA D).whisk [] (s ++ rd E ++ E)
  have hBw : SChain (D ++ rd D ++ s ++ rd E ++ E) (B.map (whL D (rd E ++ E)))
      (D ++ ups a ++ rd E ++ E) := by simpa using hB.whisk D (rd E ++ E)
  have hM' : SChain (rd (rd D) ++ ups a) M (ups c ++ rd (rd E)) := by
    simpa [rd_rd] using hM
  have hfl := sChain_flatL (p := rd D) (q := rd E) (x := ups a) (y := ups c) hM'
  have hflw : SChain (D ++ ups a ++ rd E ++ E)
      ((flatL (rd D) (rd E) (ups a) (ups c) M).map (whL D E)) (D ++ rd D ++ ups c ++ E) := by
    simpa using hfl.whisk D E
  have hcap : SChain (D ++ rd D ++ ups c ++ E) ((capA (rd D)).map (whL [] (ups c ++ E)))
      (ups c ++ E) := by
    simpa [rd_rd] using (sChain_capA (rd D)).whisk [] (ups c ++ E)
  -- (i) the upward diagram `A''` is the bent form of `M`
  have h1 := dg_step RD k μ (s₀ := s) (t₀ := ups c ++ E)
    ((cupA (rd E)).map (whL s []) ++ (cupA D).map (whL [] (s ++ rd E ++ E)) ++
      B.map (whL D (rd E ++ E))) ((capA (rd D)).map (whL [] (ups c ++ E))) D E hE.symm
    (by simpa using (hcb.append hcD).append hBw) (by simpa using hcap) rfl rfl
  -- (ii) the cups on the right move above the diagram unbent on the left
  have hY : SChain s ((cupA D).map (whL [] s) ++ B.map (whL D [])) (D ++ ups a) := by
    have y1 : SChain s ((cupA D).map (whL [] s)) (D ++ rd D ++ s) := by
      simpa using (sChain_cupA D).whisk [] s
    have y2 : SChain (D ++ rd D ++ s) (B.map (whL D [])) (D ++ ups a) := by
      simpa using hB.whisk D []
    exact y1.append y2
  have h2 := dg_interchange (RD := RD) (k := k) (μ := μ) (S := s) (T := ups c ++ E) []
    ((flatL (rd D) (rd E) (ups a) (ups c) M).map (whL D E) ++
      (capA (rd D)).map (whL [] (ups c ++ E))) hY (B := cupA (rd E)) (t := []) (t' := rd E ++ E)
    (by simpa [rd_rd] using sChain_cupA (rd E))
  -- (iii) unbending the bent form of `M` gives `M`
  have hf := dg_unbend_flat (RD := RD) (k := k) (rd D) (rd E) (ups a) (ups c) hM' (wt RD μ [])
  rw [rd_rd, rd_rd] at hf
  have h3 := dg_step RD k μ (s₀ := s) (t₀ := ups c ++ E)
    ((cupA D).map (whL [] s) ++ B.map (whL D [])) [] [] [] hf (by simpa using hY) (by simp) rfl rfl
  symm
  calc dg RD k μ s (ups c ++ E) ((cupA (rd E)).map (whL s []) ++
        ((cupA D).map (whL [] (s ++ rd E)) ++ (B.map (whL [] (rd E)) ++ A'').map (whL D []) ++
          (capA (rd D)).map (whL [] (ups c))).map (whL [] E))
      = dg RD k μ s (ups c ++ E) (((cupA (rd E)).map (whL s []) ++
          (cupA D).map (whL [] (s ++ rd E ++ E)) ++ B.map (whL D (rd E ++ E))) ++
            A''.map (whL D E) ++ (capA (rd D)).map (whL [] (ups c ++ E))) :=
        dg_list_eq (by laysimp)
    _ = _ := h1
    _ = dg RD k μ s (ups c ++ E) ([] ++ (cupA (rd E)).map (whL s []) ++
          ((cupA D).map (whL [] s) ++ B.map (whL D [])).map (whL [] (rd E ++ E)) ++
            ((flatL (rd D) (rd E) (ups a) (ups c) M).map (whL D E) ++
              (capA (rd D)).map (whL [] (ups c ++ E)))) := dg_list_eq (by laysimp)
    _ = _ := h2.symm
    _ = dg RD k μ s (ups c ++ E) (((cupA D).map (whL [] s) ++ B.map (whL D [])) ++
          ((cupA (rd E)).map (whL (D ++ ups a) []) ++
            (flatL (rd D) (rd E) (ups a) (ups c) M).map (whL D E) ++
              (capA (rd D)).map (whL [] (ups c ++ E))).map (whL [] []) ++ []) :=
        dg_list_eq (by laysimp)
    _ = _ := h3
    _ = dg RD k μ s (ups c ++ E) ((cupA D).map (whL [] s) ++ B.map (whL D []) ++ M) :=
        dg_list_eq (by laysimp)

/-! ## Monotone diagrams of the two types -/

theorem allSh_sharpL {p q x y : List (Letter I)} {M : List (LayerData I)}
    (hM : AllSh Shape.isRL M) (hp : ∀ l ∈ p, l.1 = false) (hq : ∀ l ∈ q, l.1 = false) :
    AllSh Shape.isRL (sharpL p q x y M) := by
  refine ((allSh_cupA q (fun l hl => ?_)).map_whL _ _).append (hM.map_whL _ _) |>.append
    ((allSh_capA p (fun l hl => ?_)).map_whL _ _)
  · simp [Shape.isRL, hq l hl]
  · simp [Shape.isRL, hp l hl]

theorem allSh_flatL {p q x y : List (Letter I)} {M : List (LayerData I)}
    (hM : AllSh Shape.isLR M) (hp : ∀ l ∈ p, l.1 = true) (hq : ∀ l ∈ q, l.1 = true) :
    AllSh Shape.isLR (flatL p q x y M) := by
  refine ((allSh_cupA p (fun l hl => ?_)).map_whL _ _).append (hM.map_whL _ _) |>.append
    ((allSh_capA q (fun l hl => ?_)).map_whL _ _)
  · simp [Shape.isLR, hp l hl]
  · simp [Shape.isLR, hq l hl]

theorem dns_fst (b : List I) : ∀ l ∈ dns b, l.1 = false := by
  intro l hl
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hl
  rfl

theorem Upward.map_whL {A : List (LayerData I)} (h : Upward A) (u v : List (Letter I)) :
    Upward (A.map (whL u v)) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  exact h y hy

/-! ## Good 2-morphisms are preserved by monotone diagrams -/

/-- **R → L**: a good 2-morphism into a word sorted to the right, followed by a monotone diagram of
type `RL` into a word sorted to the left, is good (simply-laced). -/
theorem goodR_comp (hSL : SimplyLaced C) [DecidableEq I] {μ : X} {s : List (Letter I)}
    (hs : Positive s) {a b d c : List I} {M : List (LayerData I)} (hM : AllSh Shape.isRL M)
    (hMc : SChain (ups a ++ dns b) M (dns d ++ ups c)) {f} (hf : f ∈ GoodR RD k μ s a b) :
    f ≫ dg RD k μ (ups a ++ dns b) (dns d ++ ups c) M ∈ GoodL RD k μ s d c := by
  obtain ⟨A', hA'u, hA'c, hE⟩ := straightenRL (RD := RD) (k := k)
    (s := rd (dns d) ++ ups a) (t := ups c ++ rd (dns b))
    (positive_append.2 ⟨positive_rd_dns d, positive_ups a⟩)
    (positive_append.2 ⟨positive_ups c, positive_rd_dns b⟩)
    (allSh_sharpL hM (dns_fst d) (dns_fst b)) (sChain_sharpL hMc)
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨δ, x, hδ, hx, rfl⟩ := hf
    rw [Category.assoc]
    refine goodL_bub hδ ?_
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨A, γ, hAu, hAc, hγ, rfl⟩ := hx
      have hA2 : SChain ((rd (dns d) ++ s) ++ rd (dns b)) (A.map (whL (rd (dns d)) []) ++ A')
          (ups c ++ rd (dns b)) := by
        refine (show SChain ((rd (dns d) ++ s) ++ rd (dns b)) (A.map (whL (rd (dns d)) []))
          (rd (dns d) ++ ups a) by simpa using hAc.whisk (rd (dns d)) []).append hA'c
      have key := hom_ext_dg RD k (wt RD μ (dns b)) (s := []) (t := [])
        ((Linear.rightComp k _ (dg RD k μ (ups a ++ dns b) (dns d ++ ups c) M)).comp
          ((unbendR RD k μ b s (ups a)).comp
            ((Linear.leftComp k _ (dg RD k (wt RD μ (dns b)) (s ++ rd (dns b)) (ups a) A)).comp
              (bubAt RD k (wt RD μ (dns b)) (ups a)))))
        ((unbendL RD k μ d s (ups c)).comp
          ((ptrRL RD k μ b (rd (dns d) ++ s) (ups c) ((rd (dns d) ++ s) ++ rd (dns b))
            (ups c ++ rd (dns b))).comp
            ((Linear.leftComp k _ (dg RD k (wt RD μ (dns b)) ((rd (dns d) ++ s) ++ rd (dns b))
              (ups c ++ rd (dns b)) (A.map (whL (rd (dns d)) []) ++ A'))).comp
              (bubAt RD k (wt RD μ (dns b)) (ups c ++ rd (dns b))))))
        (fun B hB => ?_)
      · have e := LinearMap.congr_fun key γ
        change unbendR RD k μ b s (ups a) (dg RD k (wt RD μ (dns b)) (s ++ rd (dns b)) (ups a) A ≫
            bubAt RD k (wt RD μ (dns b)) (ups a) γ) ≫
              dg RD k μ (ups a ++ dns b) (dns d ++ ups c) M =
          unbendL RD k μ d s (ups c) (ptrRL RD k μ b (rd (dns d) ++ s) (ups c)
            ((rd (dns d) ++ s) ++ rd (dns b)) (ups c ++ rd (dns b))
            (dg RD k (wt RD μ (dns b)) ((rd (dns d) ++ s) ++ rd (dns b)) (ups c ++ rd (dns b))
              (A.map (whL (rd (dns d)) []) ++ A') ≫
                bubAt RD k (wt RD μ (dns b)) (ups c ++ rd (dns b)) γ)) at e
        rw [e]
        refine Submodule.subset_span ⟨𝟙 _, _, IsBub.id, ?_, by rw [bubAt_id, Category.id_comp]⟩
        exact ptrRL_mem_upSpan hSL b μ (positive_append.2 ⟨positive_rd_dns d, hs⟩) (positive_ups c)
          rfl rfl (Submodule.subset_span ⟨_, γ, (hAu.map_whL _ _).append hA'u, hA2, hγ, rfl⟩)
      change unbendR RD k μ b s (ups a) (dg RD k (wt RD μ (dns b)) (s ++ rd (dns b)) (ups a) A ≫
            bubAt RD k (wt RD μ (dns b)) (ups a) (dg RD k (wt RD μ (dns b)) [] [] B)) ≫
            dg RD k μ (ups a ++ dns b) (dns d ++ ups c) M =
          unbendL RD k μ d s (ups c) (ptrRL RD k μ b (rd (dns d) ++ s) (ups c)
            ((rd (dns d) ++ s) ++ rd (dns b)) (ups c ++ rd (dns b))
            (dg RD k (wt RD μ (dns b)) ((rd (dns d) ++ s) ++ rd (dns b)) (ups c ++ rd (dns b))
              (A.map (whL (rd (dns d)) []) ++ A') ≫
                bubAt RD k (wt RD μ (dns b)) (ups c ++ rd (dns b))
                  (dg RD k (wt RD μ (dns b)) [] [] B)))
      have hBa : SChain (ups a) (B.map (whL (ups a) [])) (ups a) := by
        simpa using hB.whisk (ups a) []
      have hBc : SChain (ups c ++ rd (dns b)) (B.map (whL (ups c ++ rd (dns b)) []))
          (ups c ++ rd (dns b)) := by simpa using hB.whisk (ups c ++ rd (dns b)) []
      have hU : SChain s ((cupA (rd (dns b))).map (whL s []) ++
          (A ++ B.map (whL (ups a) [])).map (whL [] (dns b))) (ups a ++ dns b) := by
        refine (show SChain s ((cupA (rd (dns b))).map (whL s [])) (s ++ rd (dns b) ++ dns b) by
          simpa [rd_rd] using (sChain_cupA (rd (dns b))).whisk s []).append ?_
        simpa using (hAc.append hBa).whisk [] (dns b)
      rw [bubAt_dg, bubAt_dg, dg_comp hAc hBa, dg_comp hA2 hBc, unbendR_dg, dg_comp hU hMc,
        ptrRL_dg μ b rfl rfl]
      erw [unbendL_dg]
      exact (core_RL_dg μ hAc hMc (hE (wt RD μ (dns b))) hB).trans
        (dg_list_eq (by simp only [List.append_assoc]))
    | zero => rw [map_zero, Limits.zero_comp]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add, Preadditive.add_comp]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [map_smul, Linear.smul_comp]; exact Submodule.smul_mem _ r hx
  | zero => rw [Limits.zero_comp]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Preadditive.add_comp]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [Linear.smul_comp]; exact Submodule.smul_mem _ r hx

/-- Unbending on the left commutes with bubble monomials on the far right. -/
theorem unbendL_dg_bubAt (μ : X) (d : List I) (s c : List (Letter I)) {B : List (LayerData I)}
    (hBc : SChain (rd (dns d) ++ s) B c) (γ : End ((pres RD k).obj (ob RD (wt RD μ []) []))) :
    unbendL RD k μ d s c (dg RD k (wt RD μ []) (rd (dns d) ++ s) c B ≫
        bubAt RD k (wt RD μ []) c γ) =
      unbendL RD k μ d s c (dg RD k (wt RD μ []) (rd (dns d) ++ s) c B) ≫
        bubAt RD k μ (dns d ++ c) γ := by
  have key := hom_ext_dg RD k (wt RD μ []) (s := []) (t := [])
    ((unbendL RD k μ d s c).comp ((Linear.leftComp k _ (dg RD k (wt RD μ []) (rd (dns d) ++ s) c
      B)).comp (bubAt RD k (wt RD μ []) c)))
    ((Linear.leftComp k _ (unbendL RD k μ d s c (dg RD k (wt RD μ []) (rd (dns d) ++ s) c B))).comp
      (bubAt RD k μ (dns d ++ c))) (fun Bb hBb => ?_)
  · exact LinearMap.congr_fun key γ
  change unbendL RD k μ d s c (dg RD k (wt RD μ []) (rd (dns d) ++ s) c B ≫
      bubAt RD k (wt RD μ []) c (dg RD k (wt RD μ []) [] [] Bb)) =
    unbendL RD k μ d s c (dg RD k (wt RD μ []) (rd (dns d) ++ s) c B) ≫
      bubAt RD k μ (dns d ++ c) (dg RD k μ [] [] Bb)
  have h1 : SChain c (Bb.map (whL c [])) c := by simpa using hBb.whisk c []
  have h2 : SChain (dns d ++ c) (Bb.map (whL (dns d ++ c) [])) (dns d ++ c) := by
    simpa using hBb.whisk (dns d ++ c) []
  have h3 : SChain s ((cupA (dns d)).map (whL [] s) ++ B.map (whL (dns d) [])) (dns d ++ c) := by
    refine (show SChain s ((cupA (dns d)).map (whL [] s)) (dns d ++ (rd (dns d) ++ s)) by
      simpa using (sChain_cupA (dns d)).whisk [] s).append ?_
    simpa using hBc.whisk (dns d) []
  rw [bubAt_dg, bubAt_dg, dg_comp hBc h1, unbendL_dg, unbendL_dg, dg_comp h3 h2]
  exact dg_list_eq (by laysimp)

/-- **L → R**: a good 2-morphism into a word sorted to the left, followed by a monotone diagram of
type `LR` into a word sorted to the right, is good (simply-laced). -/
theorem goodL_comp (hSL : SimplyLaced C) [DecidableEq I] {μ : X} {s : List (Letter I)}
    (hs : Positive s) {d a c b : List I} {M : List (LayerData I)} (hM : AllSh Shape.isLR M)
    (hMc : SChain (dns d ++ ups a) M (ups c ++ dns b)) {g} (hg : g ∈ GoodL RD k μ s d a) :
    g ≫ dg RD k μ (dns d ++ ups a) (ups c ++ dns b) M ∈ GoodR RD k μ s c b := by
  have hM' : SChain (rd (rd (dns d)) ++ ups a) M (ups c ++ rd (rd (dns b))) := by
    simpa [rd_rd] using hMc
  obtain ⟨A'', hA''u, hA''c, hE⟩ := straightenLR (RD := RD) (k := k)
    (s := ups a ++ rd (dns b)) (t := rd (dns d) ++ ups c)
    (positive_append.2 ⟨positive_ups a, positive_rd_dns b⟩)
    (positive_append.2 ⟨positive_rd_dns d, positive_ups c⟩)
    (allSh_flatL hM (positive_rd_dns d) (positive_rd_dns b)) (sChain_flatL hM')
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨δ, y, hδ, hy, rfl⟩ := hg
    rw [Category.assoc]
    refine goodR_bub hδ ?_
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨B, γ, hBu, hBc, hγ, rfl⟩ := hy
      rw [unbendL_dg_bubAt μ d s (ups a) hBc γ, ← bubAt_comm, Category.assoc]
      refine goodR_bub (μ := μ) (δ := γ) hγ ?_
      have hB2 : SChain (rd (dns d) ++ (s ++ rd (dns b))) (B.map (whL [] (rd (dns b))) ++ A'')
          (rd (dns d) ++ ups c) := by
        refine (show SChain (rd (dns d) ++ (s ++ rd (dns b))) (B.map (whL [] (rd (dns b))))
          (ups a ++ rd (dns b)) by simpa using hBc.whisk [] (rd (dns b))).append hA''c
      have e : unbendL RD k μ d s (ups a) (dg RD k (wt RD μ []) (rd (dns d) ++ s) (ups a) B) ≫
          dg RD k μ (dns d ++ ups a) (ups c ++ dns b) M =
          unbendR RD k μ b s (ups c) (ptrLL RD k (wt RD μ (dns b)) d (s ++ rd (dns b)) (ups c)
            (rd (dns d) ++ (s ++ rd (dns b))) (rd (dns d) ++ ups c)
            (dg RD k (wt RD (wt RD μ (dns b)) []) (rd (dns d) ++ (s ++ rd (dns b)))
              (rd (dns d) ++ ups c) (B.map (whL [] (rd (dns b))) ++ A''))) := by
        have hU : SChain s ((cupA (dns d)).map (whL [] s) ++ B.map (whL (dns d) []))
            (dns d ++ ups a) := by
          refine (show SChain s ((cupA (dns d)).map (whL [] s)) (dns d ++ (rd (dns d) ++ s)) by
            simpa using (sChain_cupA (dns d)).whisk [] s).append ?_
          simpa using hBc.whisk (dns d) []
        rw [unbendL_dg, dg_comp hU hMc, ptrLL_dg (wt RD μ (dns b)) d rfl rfl]
        erw [unbendR_dg]
        exact core_LR_dg μ hBc hMc (hE (wt RD μ (dns b)))
      rw [e]
      refine Submodule.subset_span ⟨𝟙 _, _, IsBub.id, ?_, by rw [bubAt_id, Category.id_comp]⟩
      exact ptrLL_mem_upSpan hSL d (wt RD μ (dns b))
        (positive_append.2 ⟨hs, positive_rd_dns b⟩) (positive_ups c) rfl rfl
        (Submodule.subset_span ⟨_, 𝟙 _, (hBu.map_whL _ _).append hA''u, hB2, IsBub.id,
          by rw [bubAt_id, Category.comp_id]⟩)
    | zero => rw [map_zero, Limits.zero_comp]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add, Preadditive.add_comp]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [map_smul, Linear.smul_comp]; exact Submodule.smul_mem _ r hx
  | zero => rw [Limits.zero_comp]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Preadditive.add_comp]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [Linear.smul_comp]; exact Submodule.smul_mem _ r hx

/-! ## The base case and the end -/

/-- **Base case**: a monotone diagram of type `LR` from an upward sequence to a word sorted to the
right is good. -/
theorem good_base {μ : X} {s : List (Letter I)} (hs : Positive s) {a b : List I}
    {P : List (LayerData I)} (hP : AllSh Shape.isLR P) (hPc : SChain s P (ups a ++ dns b)) :
    dg RD k μ s (ups a ++ dns b) P ∈ GoodR RD k μ s a b := by
  have hZ : SChain (s ++ rd (dns b)) (P.map (whL [] (rd (dns b))) ++
      (capA (rd (dns b))).map (whL (ups a) [])) (ups a) := by
    refine (show SChain (s ++ rd (dns b)) (P.map (whL [] (rd (dns b))))
      (ups a ++ dns b ++ rd (dns b)) by simpa using hPc.whisk [] (rd (dns b))).append ?_
    simpa [rd_rd] using (sChain_capA (rd (dns b))).whisk (ups a) []
  have hZs : AllSh Shape.isLR (P.map (whL [] (rd (dns b))) ++
      (capA (rd (dns b))).map (whL (ups a) [])) :=
    (hP.map_whL _ _).append ((allSh_capA _ (fun l hl => by
      simp [Shape.isLR, positive_rd_dns b l hl])).map_whL _ _)
  obtain ⟨A, hAu, hAc, hE⟩ := straightenLR (RD := RD) (k := k) (s := s ++ rd (dns b))
    (t := ups a) (positive_append.2 ⟨hs, positive_rd_dns b⟩) (positive_ups a) hZs hZ
  have h := dg_unbendR_bendR (RD := RD) (k := k) (rd (dns b)) s (ups a) (P := P)
    (by simpa [rd_rd] using hPc) μ
  rw [rd_rd] at h
  have key : dg RD k μ s (ups a ++ dns b) P = unbendR RD k μ b s (ups a)
      (dg RD k (wt RD μ (dns b)) (s ++ rd (dns b)) (ups a) (P.map (whL [] (rd (dns b))) ++
        (capA (rd (dns b))).map (whL (ups a) []))) := by
    rw [unbendR_dg]
    exact h.symm
  rw [key]
  refine Submodule.subset_span ⟨𝟙 _, _, IsBub.id, ?_, by rw [bubAt_id, Category.id_comp]⟩
  rw [hE]
  exact dg_upward_mem_upSpan hAu hAc

theorem upSpan_bub {μ : X} {S T : List (Letter I)} {δ : End ((pres RD k).obj (ob RD μ []))}
    (hδ : IsBub RD k μ δ) {x} (hx : x ∈ upSpan RD k μ S T) :
    bubAt RD k μ S δ ≫ x ∈ upSpan RD k μ S T := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨A, γ, hA, hc, hγ, rfl⟩ := hx
    refine Submodule.subset_span ⟨A, δ ≫ γ, hA, hc, hδ.comp hγ, ?_⟩
    rw [← Category.assoc, bubAt_comm, Category.assoc, bubAt_comp]
  | zero => rw [Limits.comp_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Preadditive.comp_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [Linear.comp_smul]; exact Submodule.smul_mem _ r hx

/-- Good 2-morphisms into an upward sequence lie in `upSpan`. -/
theorem goodR_nil_le (μ : X) (s : List (Letter I)) (a : List I) :
    GoodR RD k μ s a [] ≤ upSpan RD k μ s (ups a ++ dns []) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨δ, x, hδ, hx, rfl⟩
  refine upSpan_bub hδ ?_
  exact upSpan_ctxL (fun y hy => by simp [cupA] at hy) (fun y hy => by simp at hy)
    (by simp [cupA]) (by simp) hx

/-! ## One layer at a time -/

variable (RD k) in
/-- The invariant: `f ≫ p` is good for every monotone diagram `p` of type `LR` into a word sorted
to the right. -/
def LayerInv (μ : X) (s w : List (Letter I))
    (f : (pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ w)) : Prop :=
  ∀ (a b : List I) (P : List (LayerData I)), AllSh Shape.isLR P → SChain w P (ups a ++ dns b) →
    f ≫ dg RD k μ w (ups a ++ dns b) P ∈ GoodR RD k μ s a b

theorem Shape.isRL_or_isLR (g : Shape I) : g.isRL = true ∨ g.isLR = true := by
  cases g with
  | dot l => exact Or.inl rfl
  | cross ε a b => exact Or.inl rfl
  | cup l => obtain ⟨b, i⟩ := l; cases b <;> simp [Shape.isRL, Shape.isLR]
  | cap l => obtain ⟨b, i⟩ := l; cases b <;> simp [Shape.isRL, Shape.isLR]

/-- **One layer**: the invariant is preserved by composing with any layer (simply-laced). -/
theorem inv_step (hSL : SimplyLaced C) [DecidableEq I] {μ : X} {s : List (Letter I)}
    (hs : Positive s) {w w' : List (Letter I)} {f} (hf : LayerInv RD k μ s w f) {x : LayerData I}
    (hx : SChain w [x] w') : LayerInv RD k μ s w' (f ≫ dg RD k μ w w' [x]) := by
  intro a' b' P' hP' hcP'
  have hΦ : ∀ e ∈ decRSet RD k μ w, f ≫ e ≫ dg RD k μ w w' [x] ≫
      dg RD k μ w' (ups a' ++ dns b') P' ∈ GoodR RD k μ s a' b' := by
    intro e he
    induction he using Submodule.span_induction with
    | mem e he =>
      obtain ⟨a, b, P, Q, δ, hP, hcP, hQ, hcQ, hδ, rfl⟩ := he
      have hg := hf a b P hP hcP
      have hxs : x.2.1.isRL = true ∨ x.2.1.isLR = true := Shape.isRL_or_isLR _
      rcases hxs with hxs | hxs
      · -- the layer is of type `RL`: sort its target to the left
        have hΨ : ∀ e' ∈ decLSet RD k μ w', f ≫ bubAt RD k μ w δ ≫
            dg RD k μ w (ups a ++ dns b) P ≫ dg RD k μ (ups a ++ dns b) w Q ≫
              dg RD k μ w w' [x] ≫ e' ≫ dg RD k μ w' (ups a' ++ dns b') P' ∈
                GoodR RD k μ s a' b' := by
          intro e' he'
          induction he' using Submodule.span_induction with
          | mem e' he' =>
            obtain ⟨d, c, P'', Q'', δ', hP'', hcP'', hQ'', hcQ'', hδ', rfl⟩ := he'
            have h1 := goodR_comp hSL hs (M := Q ++ [x] ++ P'')
              ((hQ.append (fun y hy => by rw [List.mem_singleton.1 hy]; exact hxs)).append hP'')
              ((hcQ.append hx).append hcP'') hg
            have h2 := goodL_comp hSL hs (M := Q'' ++ P') (hQ''.append hP') (hcQ''.append hcP') h1
            have h3 := goodR_bub hδ (goodR_bub hδ' h2)
            convert h3 using 1
            rw [← dg_comp (hcQ.append hx) hcP'', ← dg_comp hcQ hx, ← dg_comp hcQ'' hcP']
            have hb := bubAt_comm RD k μ δ' (f ≫ dg RD k μ w (ups a ++ dns b) P ≫
              dg RD k μ (ups a ++ dns b) w Q ≫ dg RD k μ w w' [x])
            have hb' := bubAt_comm RD k μ δ f
            simp only [Category.assoc] at hb hb' ⊢
            rw [← reassoc_of% hb', ← reassoc_of% hb]
          | zero => simp
          | add e₁ e₂ _ _ h₁ h₂ =>
            simp only [Preadditive.add_comp, Preadditive.comp_add]; exact Submodule.add_mem _ h₁ h₂
          | smul r e _ h =>
            simp only [Linear.smul_comp, Linear.comp_smul]; exact Submodule.smul_mem _ r h
        have := hΨ _ (decL (RD := RD) (k := k) hSL μ _ w' (Nat.lt_succ_self _))
        simpa only [Category.id_comp, Category.assoc] using this
      · -- the layer is of type `LR`: sort its source to the left
        have hΨ : ∀ e' ∈ decLSet RD k μ w, f ≫ bubAt RD k μ w δ ≫
            dg RD k μ w (ups a ++ dns b) P ≫ dg RD k μ (ups a ++ dns b) w Q ≫ e' ≫
              dg RD k μ w w' [x] ≫ dg RD k μ w' (ups a' ++ dns b') P' ∈
                GoodR RD k μ s a' b' := by
          intro e' he'
          induction he' using Submodule.span_induction with
          | mem e' he' =>
            obtain ⟨d, c, P'', Q'', δ', hP'', hcP'', hQ'', hcQ'', hδ', rfl⟩ := he'
            have h1 := goodR_comp hSL hs (M := Q ++ P'') (hQ.append hP'') (hcQ.append hcP'') hg
            have h2 := goodL_comp hSL hs (M := Q'' ++ [x] ++ P')
              ((hQ''.append (fun y hy => by rw [List.mem_singleton.1 hy]; exact hxs)).append hP')
              ((hcQ''.append hx).append hcP') h1
            have h3 := goodR_bub hδ (goodR_bub hδ' h2)
            convert h3 using 1
            rw [← dg_comp hcQ hcP'', ← dg_comp (hcQ''.append hx) hcP', ← dg_comp hcQ'' hx]
            have hb := bubAt_comm RD k μ δ' (f ≫ dg RD k μ w (ups a ++ dns b) P ≫
              dg RD k μ (ups a ++ dns b) w Q)
            have hb' := bubAt_comm RD k μ δ f
            simp only [Category.assoc] at hb hb' ⊢
            rw [← reassoc_of% hb', ← reassoc_of% hb]
          | zero => simp
          | add e₁ e₂ _ _ h₁ h₂ =>
            simp only [Preadditive.add_comp, Preadditive.comp_add]; exact Submodule.add_mem _ h₁ h₂
          | smul r e _ h =>
            simp only [Linear.smul_comp, Linear.comp_smul]; exact Submodule.smul_mem _ r h
        have := hΨ _ (decL (RD := RD) (k := k) hSL μ _ w (Nat.lt_succ_self _))
        simpa only [Category.id_comp, Category.assoc] using this
    | zero => simp
    | add e₁ e₂ _ _ h₁ h₂ =>
      simp only [Preadditive.add_comp, Preadditive.comp_add]; exact Submodule.add_mem _ h₁ h₂
    | smul r e _ h =>
      simp only [Linear.smul_comp, Linear.comp_smul]; exact Submodule.smul_mem _ r h
  have := hΦ _ (decR (RD := RD) (k := k) hSL μ _ w (Nat.lt_succ_self _))
  simpa only [Category.id_comp, Category.assoc] using this

/-! ## Main results -/

/-- **KL III Lemma 3.9, diagrammatic form** (simply-laced Cartan data): every normal-form diagram
of `U` from an upward sequence to an upward sequence is a linear combination of upward diagrams
followed by bubble monomials on the far right. -/
theorem upSpanDiag_of_simplyLaced (hSL : SimplyLaced C) [DecidableEq I] (μ : X) :
    UpSpanDiag RD k μ := by
  intro s t ls hs ht h
  have hbase : LayerInv RD k μ s s (𝟙 _) := fun a b P hP hPc => by
    rw [Category.id_comp]; exact good_base hs hP hPc
  have hall : ∀ (ls : List (LayerData I)) {w₀ w : List (Letter I)}
      (f : (pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ w₀)),
      LayerInv RD k μ s w₀ f → SChain w₀ ls w → LayerInv RD k μ s w (f ≫ dg RD k μ w₀ w ls) := by
    intro ls
    induction ls with
    | nil =>
      intro w₀ w f hf hc
      obtain rfl : w₀ = w := hc
      rw [dg_nil, Category.comp_id]
      exact hf
    | cons x ls ih =>
      intro w₀ w f hf hc
      have hx : SChain w₀ [x] (x.1 ++ x.2.1.cod ++ x.2.2) := ⟨hc.1, rfl⟩
      have := ih _ (inv_step hSL hs hf hx) hc.2
      rw [Category.assoc, dg_comp hx hc.2] at this
      exact this
  have hI := hall ls (𝟙 _) hbase h
  obtain ⟨a, rfl⟩ : ∃ a, t = ups a ++ dns [] := ⟨t.map Prod.snd, by simp [ups_map_snd ht]⟩
  have hm := hI a [] [] (fun x hx => by simp at hx) rfl
  rw [dg_nil, Category.comp_id, Category.id_comp] at hm
  exact goodR_nil_le μ s a hm

/-- **The one-strand case of KL III Lemma 3.9** (simply-laced): every endomorphism of `E_i 1_μ`
is a linear combination of dots times bubble monomials. -/
theorem endUpSpan_of_simplyLaced (hSL : SimplyLaced C) (μ : X) (i : I) :
    EndUpSpan RD k μ i := by
  classical
  exact endUpSpan_of_upSpanDiag RD k (upSpanDiag_of_simplyLaced hSL μ) i

/-- **KL III Proposition 3.10** (simply-laced): `ϕ_{ν,λ} : R(ν) ⊗ Π_λ → END_U(E_ν 1_λ)` is
surjective. -/
theorem prop310_of_simplyLaced (hSL : SimplyLaced C) [DecidableEq I] (μ : X) (ν : Multiset I) :
    Prop310 RD k μ ν :=
  prop310_of_upSpanDiag RD k μ ν (upSpanDiag_of_simplyLaced hSL μ)

/-- **KL III Proposition 3.6** (simply-laced): `Π_λ → END_U(1_λ)` is surjective. -/
theorem prop36_of_simplyLaced (hSL : SimplyLaced C) (lam : X) : Prop36 RD k lam := by
  classical
  exact prop36_of_upSpanDiag RD k hSL (fun μ => upSpanDiag_of_simplyLaced hSL μ) lam

/-! ## Corollary 3.7 -/

/-- **KL III Corollary 3.7**, nonnegativity of degrees (simply-laced): `HOM_U(1_λ, 1_λ)` has no
nonzero elements of negative degree. -/
theorem cor37_HDe_neg_of_simplyLaced (hSL : SimplyLaced C) (lam : X) {d : ℤ} (hd : d < 0) :
    HDe RD k lam d = ⊥ :=
  cor37_HDe_neg lam (prop36_of_simplyLaced hSL lam) hd

/-- **KL III Corollary 3.7**, the degree-zero part (simply-laced): the degree-zero part of
`HOM_U(1_λ, 1_λ)` is `k · 1`. -/
theorem cor37_HDe_zero_of_simplyLaced (hSL : SimplyLaced C) (lam : X) :
    HDe RD k lam 0 = Submodule.span k {𝟙 _} :=
  cor37_HDe_zero lam (prop36_of_simplyLaced hSL lam)

/-- **KL III Corollary 3.7** (simply-laced, `I` finite, `k` with the strong rank condition):
`dim_k HOM_U(1_λ, 1_λ)_d` is at most the number of monomials of degree `d` in `Π_λ`. -/
theorem cor37_finrank_le_of_simplyLaced [StrongRankCondition k] [Finite I] (hSL : SimplyLaced C)
    (lam : X) (d : ℤ) : Module.finrank k (HDe RD k lam d) ≤ (monDeg C d).ncard :=
  cor37_finrank_le lam (prop36_of_simplyLaced hSL lam) d

/-- **KL III Corollary 3.7**, `gdim HOM_U(1_λ, 1_λ) ≤ π` (simply-laced, `I` finite, `k` with the
strong rank condition): the dimension in degree `d` is at most the coefficient of `q^d` in `π`. -/
theorem cor37_gdim_le_pi_of_simplyLaced [StrongRankCondition k] [Fintype I]
    (hSL : SimplyLaced C) (lam : X) (N d : ℕ) (hd : d ≤ N) :
    (Module.finrank k (HDe RD k lam d) : ℤ) ≤ (piTrunc C N).coeff d :=
  cor37_gdim_le_pi lam (prop36_of_simplyLaced hSL lam) N d hd

/-- **KL III Corollary 3.7**, "local graded ring" (simply-laced, `k` a field): a homogeneous element
of `END_U(1_λ)` of degree `≤ 0` which is nonzero is a unit. -/
theorem cor37_isUnit_of_simplyLaced {K : Type w} [Field K] {RD : RootDatum C X Y}
    (hSL : SimplyLaced C) (lam : X) {x : EndOne RD K lam} {d : ℤ} (hx : x ∈ HDo RD K lam d)
    (hd : d ≤ 0) (hx0 : x ≠ 0) : IsUnit x :=
  cor37_isUnit lam (prop36_of_simplyLaced hSL lam) hx hd hx0

end Categorification.KL3.Diagram

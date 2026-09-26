/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.KrullSchmidtU

/-!
# Indecomposable 1-morphisms of `U̇` are summands of sorted words (KL III Lemma 3.38)

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.8.4
(TeX `\subsubsection{Idempotents in $\UcatD$}`), Lemma 3.38 and its proof:

> If `P` has width `m` then `P` is isomorphic to a direct summand of `E_{ν,-ν'} 1_λ {t}` for some
> `ν, ν'`, `‖ν‖ + ‖ν'‖ = m` […] Moving all positive terms of `i` to the left of all negative
> terms produces a sequence `j (-j')` with `j, j'` positive, `‖j‖ + ‖j'‖ = m` and `P` being a
> summand of `E_{j(-j')} 1_λ {t}`.

Here the *width* of an indecomposable `P` is the smallest length of a signed sequence `w` such
that `P` is a direct summand of `E_w 1_λ {t}`.

## Main results

* `one_mem_thru_sorted`: in `U`, the identity of `E_w 1_μ` is a linear combination of composites
  `E_w 1_μ → E_u 1_μ → E_w 1_μ` of homogeneous 2-morphisms of opposite degrees through **sorted**
  words `u = (+a)(-b)` (all upward letters to the left) with `|u| ≤ |w|`, `|u| ≡ |w| mod 2`
  (the relations `eq_downup_ij-gen` and `eq_ident_decomp` of Definition 3.1; no bubble slides).
* `exists_retract_nfObj`: every indecomposable object of `U̇(λ, ρ)` is a retract (direct
  summand) of some `E_w 1_λ {t}`.
* `exists_retract_sorted_of_retract`: **KL III Lemma 3.38, module level**: an indecomposable
  direct summand of `E_w 1_λ {t}` is a direct summand of `E_{+a} E_{-b} 1_λ {t'}` for sorted
  `(+a)(-b)` with `|a| + |b| ≤ |w|`, `|a| + |b| ≡ |w| mod 2`; `exists_retract_sorted`: every
  indecomposable of `U̇(λ, ρ)` is a summand of such a sorted `E_{+a} E_{-b} 1_λ {t'}`.
* `K0Kar_span_sorted_summands`: `K₀(U̇(λ, ρ))` is spanned over `ℤ[q, q⁻¹]` by the classes of the
  indecomposable direct summands of the sorted `E_{+a} E_{-b} 1_λ {t}`.

(simply-laced Cartan data, `I` finite, `k` a field: the Krull–Schmidt property of
`Categorification.Diagrams.KL3.KrullSchmidtU` is used.)

## What remains for the surjectivity of `γ`

KL III's proof of surjectivity (Theorem 1.1) continues by analysing the minimal idempotents of
`END(E_{ν,-ν'} 1_λ)` through `R(ν) ⊗ R(ν') ⊗ Π_λ` (Propositions 3.32–3.36, Corollary 3.37):
the ideal `I_{ν,-ν',λ}` of 2-morphisms factoring through shorter sequences, the surjection
`βα : R(ν) ⊗ R(ν') ⊗ Π_λ → R_{ν,-ν',λ}`, virtually nilpotent ideals, and the identification
`K₀(R(ν) ⊗ R(ν') ⊗ Π_λ) ≅ _𝒜f_ν ⊗ _𝒜f_{ν'}`. These are not formalized here, so the statement
"`[P]` lies in the image of `γ` for every indecomposable `P`" remains open; the results above
reduce it to the indecomposable summands of the sorted 1-morphisms `E_{+a} E_{-b} 1_λ`.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents StringDiagrams QuantumGroup
  UDot Presentation GradedBicat KrullSchmidtCat

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {k : Type w} [Field k]

/-! ## Identities factoring through sets of words -/

section Thru

variable (RD k) in
/-- Composites `E_w 1_μ → E_u 1_μ → E_w 1_μ` (`u ∈ S`, of the weight of `w`) of homogeneous
2-morphisms of opposite degrees. -/
def thruGen (μ : X) (w : List (Letter I)) (S : Set (List (Letter I))) :
    Set (End ((pres RD k).obj (ob RD μ w))) :=
  {x | ∃ u ∈ S, wt RD μ u = wt RD μ w ∧ ∃ (α : ℤ)
    (a : (pres RD k).obj (ob RD μ w) ⟶ (pres RD k).obj (ob RD μ u))
    (b : (pres RD k).obj (ob RD μ u) ⟶ (pres RD k).obj (ob RD μ w)),
    a ∈ HomD RD k μ w u α ∧ b ∈ HomD RD k μ u w (-α) ∧ x = a ≫ b}

variable (RD k) in
/-- The span of `thruGen`. -/
def thru (μ : X) (w : List (Letter I)) (S : Set (List (Letter I))) :
    Submodule k (End ((pres RD k).obj (ob RD μ w))) :=
  Submodule.span k (thruGen RD k μ w S)

variable (RD k) in
/-- Composites through `u ∈ S` of homogeneous 2-morphisms of arbitrary degrees. -/
def homGen (μ : X) (w : List (Letter I)) (S : Set (List (Letter I))) :
    Set (End ((pres RD k).obj (ob RD μ w))) :=
  {x | ∃ u ∈ S, wt RD μ u = wt RD μ w ∧ ∃ (α β : ℤ)
    (a : (pres RD k).obj (ob RD μ w) ⟶ (pres RD k).obj (ob RD μ u))
    (b : (pres RD k).obj (ob RD μ u) ⟶ (pres RD k).obj (ob RD μ w)),
    a ∈ HomD RD k μ w u α ∧ b ∈ HomD RD k μ u w β ∧ x = a ≫ b}

/-- Taking degree-zero components: if the identity is a linear combination of composites of
homogeneous 2-morphisms, it is one of composites of opposite degrees. -/
theorem one_mem_thru_of_homGen {μ : X} {w : List (Letter I)} {S : Set (List (Letter I))}
    (h : 𝟙 _ ∈ Submodule.span k (homGen RD k μ w S)) : 𝟙 _ ∈ thru RD k μ w S := by
  have hP := pres_isHomogeneous (RD := RD) (k := k)
  have key : ∀ x ∈ Submodule.span k (homGen RD k μ w S),
      Presentation.homogeneousComponent hP 0 x ∈ thru RD k μ w S := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, hu, hw, α, β, a, b, ha, hb, rfl⟩ := hx
      have hab := Presentation.comp_mem_homDeg ha hb
      by_cases h0 : α + β = 0
      · rw [Presentation.homogeneousComponent_of_mem hP (mem_homDeg_of_eq hab h0)]
        exact Submodule.subset_span ⟨u, hu, hw, α, a, b, ha,
          mem_homDeg_of_eq hb (by omega), rfl⟩
      · rw [Presentation.homogeneousComponent_of_mem_of_ne hP hab h0]
        exact Submodule.zero_mem _
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx
  have := key _ h
  rwa [Presentation.homogeneousComponent_of_mem hP ((pres RD k).id_mem_homDeg (deg RD) _)] at this

theorem thru_mono {μ : X} {w : List (Letter I)} {S S' : Set (List (Letter I))} (h : S ⊆ S') :
    thru RD k μ w S ≤ thru RD k μ w S' := by
  refine Submodule.span_mono ?_
  rintro _ ⟨u, hu, hw, α, a, b, ha, hb, rfl⟩
  exact ⟨u, h hu, hw, α, a, b, ha, hb, rfl⟩

/-- **Transitivity**: factorizations through `S` of the identities of the words of `S` compose. -/
theorem thru_le {μ : X} {w : List (Letter I)} {S S' : Set (List (Letter I))}
    (h : ∀ u ∈ S, wt RD μ u = wt RD μ w → 𝟙 _ ∈ thru RD k μ u S') :
    thru RD k μ w S ≤ thru RD k μ w S' := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨u, hu, hw, α, a, b, ha, hb, rfl⟩
  let L : ((pres RD k).obj (ob RD μ u) ⟶ (pres RD k).obj (ob RD μ u)) →ₗ[k]
      ((pres RD k).obj (ob RD μ w) ⟶ (pres RD k).obj (ob RD μ w)) :=
    Linear.leftComp k _ a ∘ₗ Linear.rightComp k _ b
  have hL : thru RD k μ u S' ≤ (thru RD k μ w S').comap L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u', hu', hw', α', a', b', ha', hb', rfl⟩
    refine Submodule.subset_span ⟨u', hu', hw'.trans hw, α + α', a ≫ a', b' ≫ b,
      Presentation.comp_mem_homDeg ha ha',
      mem_homDeg_of_eq (Presentation.comp_mem_homDeg hb' hb) (by ring), ?_⟩
    change a ≫ ((a' ≫ b') ≫ b) = _
    simp only [Category.assoc]
  have := Submodule.mem_comap.1 (hL (h u hu hw))
  have e : L (𝟙 _) = a ≫ b := by
    change a ≫ (𝟙 _ ≫ b) = _
    rw [Category.id_comp]
  convert this using 1
  exact e.symm

theorem plcL_mem (μ : X) (u v s t : List (Letter I)) {d : ℤ}
    {f : (pres RD k).obj (ob RD (wt RD μ v) s) ⟶ (pres RD k).obj (ob RD (wt RD μ v) t)}
    (hf : f ∈ HomD RD k (wt RD μ v) s t d) :
    plcL RD k μ u v s t f ∈ HomD RD k μ (u ++ s ++ v) (u ++ t ++ v) d := by
  have := map_homD_le (plcL RD k μ u v s t) 0 (fun ls _ => by
    rw [plcL_dg]
    exact dg_mem_homD (by rw [sdegSum_map_whL, add_zero])) d ⟨f, hf, rfl⟩
  rwa [add_zero] at this

/-- **Whiskering** a factorization of the identity of `E_s` by words `u`, `v`. -/
theorem one_mem_thru_whisker {μ : X} (u v s : List (Letter I)) {S : Set (List (Letter I))}
    (h : 𝟙 _ ∈ thru RD k (wt RD μ v) s S) :
    𝟙 _ ∈ thru RD k μ (u ++ s ++ v) ((fun s' => u ++ s' ++ v) '' S) := by
  have h1 : plcL RD k μ u v s s (𝟙 _) = 𝟙 _ := by
    have := plcL_dg (RD := RD) (k := k) μ u v s s []
    rw [dg_nil] at this
    rw [this, List.map_nil, dg_nil]
  rw [← h1]
  have hL : thru RD k (wt RD μ v) s S ≤
      (thru RD k μ (u ++ s ++ v) ((fun s' => u ++ s' ++ v) '' S)).comap (plcL RD k μ u v s s) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨s', hs', hw, α, a, b, ha, hb, rfl⟩
    refine Submodule.subset_span ⟨u ++ s' ++ v, ⟨s', hs', rfl⟩, by simp only [wt_append, hw], α,
      plcL RD k μ u v s s' a, plcL RD k μ u v s' s b, plcL_mem μ u v s s' ha,
      plcL_mem μ u v s' s hb, ?_⟩
    exact (plcL_comp RD k μ u v hw hw.symm a b).symm
  exact hL h

theorem wt_up_dn_swap (ν : X) (i j : I) : wt RD ν [up i, dn j] = wt RD ν [dn j, up i] := by
  simp only [wt_cons, wt_nil]; abel

theorem wt_nil_dn_up (ν : X) (i : I) : wt RD ν [] = wt RD ν [dn i, up i] := by
  simp only [wt_cons, wt_nil, sh, up, dn, sgn]; simp

/-- For `i ≠ j`, the sideways crossings are inverse isomorphisms `F_j E_i ≅ E_i F_j`
(eq. `eq_downup_ij-gen`). -/
theorem one_mem_thru_swap (ν : X) {i j : I} (h : i ≠ j) :
    𝟙 _ ∈ thru RD k ν [dn j, up i] {[up i, dn j]} := by
  refine Submodule.subset_span ⟨[up i, dn j], rfl, wt_up_dn_swap ν i j, 0,
    dg RD k ν _ _ (crossrL i j), dg RD k ν _ _ (crosslL i j), crossrL_mem i j ν,
    mem_homDeg_of_eq (crosslL_mem i j ν) neg_zero.symm, ?_⟩
  rw [dg_comp (by schain) (by schain), dg_downupFE RD k j i (Ne.symm h) ν, dg_nil]

/-- The decomposition of the identity of `F_i E_i 1_ν` (eq. `eq_ident_decomp`): it factors
through `E_i F_i 1_ν` and through `1_ν`. -/
theorem one_mem_thru_decomp (ν : X) (i : I) :
    𝟙 _ ∈ thru RD k ν [dn i, up i] {[up i, dn i], []} := by
  apply one_mem_thru_of_homGen
  rw [← dg_nil (RD := RD) (k := k) ν [dn i, up i], dg_decompFE]
  refine Submodule.add_mem _ (Submodule.neg_mem _ (Submodule.subset_span ?_))
    (Submodule.sum_mem _ fun f _ => Submodule.sum_mem _ fun g _ => ?_)
  · exact ⟨[up i, dn i], Set.mem_insert _ _, wt_up_dn_swap ν i i, 0, 0, dg RD k ν _ _ (crossrL i i),
      dg RD k ν _ _ (crosslL i i), crossrL_mem i i ν, crosslL_mem i i ν,
      (dg_comp (by schain) (by schain)).symm⟩
  · set P := dotCapFELs i (f - g)
    set Q := cupDotFELs i ((-ip RD i ν).toNat - 1 - f)
    let Ψ : ((pres RD k).obj (ob RD ν []) ⟶ (pres RD k).obj (ob RD ν [])) →ₗ[k]
        ((pres RD k).obj (ob RD ν [dn i, up i]) ⟶ (pres RD k).obj (ob RD ν [dn i, up i])) :=
      Linear.leftComp k _ (dg RD k ν [dn i, up i] [] P) ∘ₗ
        Linear.rightComp k _ (dg RD k ν [] [dn i, up i] Q)
    have hΨ : Submodule.span k (Set.range (bubMon RD k ν)) ≤
        (Submodule.span k (homGen RD k ν [dn i, up i] {[up i, dn i], []})).comap Ψ := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨m, rfl⟩
      exact Submodule.subset_span ⟨[], Set.mem_insert_of_mem _ rfl, wt_nil_dn_up ν i,
        sdegSum RD ν P, Finsupp.weight (wPi C) m + sdegSum RD ν Q, dg RD k ν _ _ P,
        bubMon RD k ν m ≫ dg RD k ν _ _ Q, dg_mem_homD rfl,
        Presentation.comp_mem_homDeg (bubMon_mem ν m) (dg_mem_homD rfl), rfl⟩
    exact hΨ (isBub_mem_span (cwU_isBub (RD := RD) (k := k) (lam := ν) i _))

/-- Sorted words (all upward letters to the left) of length at most, and of the parity of, the
length of `w`. -/
def SortedLe (w : List (Letter I)) : Set (List (Letter I)) :=
  {u | (∃ a b : List I, u = ups a ++ dns b) ∧ u.length ≤ w.length ∧ u.length % 2 = w.length % 2}

theorem sortedLe_mono {w w' : List (Letter I)} (h₁ : w'.length ≤ w.length)
    (h₂ : w'.length % 2 = w.length % 2) : SortedLe w' ⊆ SortedLe w := by
  rintro u ⟨hs, hl, hp⟩
  exact ⟨hs, hl.trans h₁, hp.trans h₂⟩

/-- **Sorting** (the module-level content of KL III Lemma 3.38): the identity of `E_w 1_μ`
factors, as a linear combination of composites of homogeneous 2-morphisms of opposite degrees,
through sorted words `E_{+a} E_{-b} 1_μ` of length at most, and of the parity of, `|w|`. -/
theorem one_mem_thru_sorted (μ : X) :
    ∀ (n : ℕ) (w : List (Letter I)), invR w < n → 𝟙 _ ∈ thru RD k μ w (SortedLe w)
  | 0 => fun w h => absurd h (Nat.not_lt_zero _)
  | n + 1 => fun w hw => by
    by_cases h0 : invR w = 0
    · obtain ⟨a, b, rfl⟩ := invR_eq_zero w h0
      refine Submodule.subset_span ⟨_, ⟨⟨a, b, rfl⟩, le_rfl, rfl⟩, rfl, 0, 𝟙 _, 𝟙 _,
        (pres RD k).id_mem_homDeg (deg RD) _,
        mem_homDeg_of_eq ((pres RD k).id_mem_homDeg (deg RD) _) neg_zero.symm,
        (Category.id_comp _).symm⟩
    obtain ⟨u, v, j, i, rfl⟩ := invR_pos w h0
    have hlen₁ : (u ++ up i :: dn j :: v).length = (u ++ dn j :: up i :: v).length := by simp
    have hlen₂ : (u ++ v).length + 2 = (u ++ dn j :: up i :: v).length := by simp; omega
    by_cases hij : i = j
    · subst hij
      have h1 := one_mem_thru_whisker (RD := RD) (k := k) (μ := μ) u v [dn i, up i]
        (one_mem_thru_decomp (wt RD μ v) i)
      rw [show u ++ [dn i, up i] ++ v = u ++ dn i :: up i :: v by simp] at h1
      refine thru_le (fun w' hw' _ => ?_) h1
      obtain ⟨s', hs', rfl⟩ := hw'
      rcases hs' with rfl | rfl
      · dsimp only
        have e : u ++ [up i, dn i] ++ v = u ++ up i :: dn i :: v := by simp
        rw [e]
        refine thru_mono (sortedLe_mono hlen₁.le (by rw [hlen₁])) ?_
        exact one_mem_thru_sorted μ n (u ++ up i :: dn i :: v) (by have := invR_swap i i v u; omega)
      · dsimp only
        have e : u ++ [] ++ v = u ++ v := by simp
        rw [e]
        refine thru_mono (sortedLe_mono (w' := u ++ v) (by omega) (by omega)) ?_
        exact one_mem_thru_sorted μ n (u ++ v) (by have := invR_del i i v u; omega)
    · have h1 := one_mem_thru_whisker (RD := RD) (k := k) (μ := μ) u v [dn j, up i]
        (one_mem_thru_swap (wt RD μ v) hij)
      rw [show u ++ [dn j, up i] ++ v = u ++ dn j :: up i :: v by simp] at h1
      refine thru_le (fun w' hw' _ => ?_) h1
      obtain ⟨s', rfl, rfl⟩ := hw'
      dsimp only
      have e : u ++ [up i, dn j] ++ v = u ++ up i :: dn j :: v := by simp
      rw [e]
      refine thru_mono (sortedLe_mono hlen₁.le (by rw [hlen₁])) ?_
      exact one_mem_thru_sorted μ n (u ++ up i :: dn j :: v) (by have := invR_swap i j v u; omega)

end Thru

/-! ## Direct summands in `U̇(λ, ρ)` -/

section Retracts

variable [DecidableEq I] [Finite I] (hSL : SimplyLaced C)
include hSL

/-- A factorization of the identity of `E_w 1_λ` through words `u ∈ S`: every indecomposable
direct summand of `E_w 1_λ {n}` is a direct summand of some `E_u 1_λ {n'}`, `u ∈ S`. -/
theorem exists_retract_of_thru {ρ lam : X} {w : List (Letter I)} {h : wt RD lam w = ρ} {n : ℤ}
    {S : Set (List (Letter I))} (hS : 𝟙 _ ∈ thru RD k lam w S) {Z : UKar RD k ρ lam}
    (hZ : IsIndec Z) (f : Z ⟶ nfObj RD k ρ lam w h n) (g : nfObj RD k ρ lam w h n ⟶ Z)
    (hfg : f ≫ g = 𝟙 Z) :
    ∃ u ∈ S, ∃ (hu : wt RD lam u = ρ) (n' : ℤ) (f' : Z ⟶ nfObj RD k ρ lam u hu n')
      (g' : nfObj RD k ρ lam u hu n' ⟶ Z), f' ≫ g' = 𝟙 Z := by
  haveI := homFinite_UDot (RD := RD) (k := k) hSL ρ lam
  obtain ⟨N, c, x, hx⟩ := Submodule.mem_span_set'.1 hS
  have hgen : ∀ i, (x i).1 ∈ thruGen RD k lam w S := fun i => (x i).2
  choose u hu hw α a b ha hb he using hgen
  have hu' : ∀ i, wt RD lam (u i) = ρ := fun i => (hw i).trans h
  let V : Fin N → UKar RD k ρ lam := fun i => nfObj RD k ρ lam (u i) (hu' i) (n - α i)
  let A : ∀ i, nfObj RD k ρ lam w h n ⟶ V i := fun i =>
    homOf (c i • a i) (mem_homDeg_of_eq (Submodule.smul_mem _ _ (ha i)) (by ring))
  let B : ∀ i, V i ⟶ nfObj RD k ρ lam w h n := fun i =>
    homOf (b i) (mem_homDeg_of_eq (hb i) (by ring))
  have htot : ∑ i ∈ Finset.univ, A i ≫ B i = 𝟙 _ := by
    simp only [A, B, homOf_comp]
    rw [sum_homOf]
    refine homOf_eq_id ?_ _
    rw [← hx]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [he i, Linear.smul_comp]
  obtain ⟨i, -, f', g', hfg'⟩ := hZ.exists_retract_of_sum k f g hfg Finset.univ V A B htot
  exact ⟨u i, hu i, hu' i, n - α i, f', g', hfg'⟩

omit hSL [DecidableEq I] [Finite I] in
/-- Every 1-morphism of `U` from `ρ` to `λ` is `E_w 1_λ` for a signed sequence `w`. -/
theorem exists_eq_nfHom {ρ lam : X} (x : Bicat.Hom (wtObj RD k ρ) (wtObj RD k lam)) :
    ∃ (w : List (Letter I)) (h : wt RD lam w = ρ), x = nfHom RD k ρ lam w h := by
  have hx := obj_eq_ob_endR lam x.obj x.wf x.endR_eq
  have hs : wt RD lam (x.obj.word.map Col.l) = ρ := by
    have := x.start_eq
    rw [hx] at this
    exact this
  exact ⟨_, hs, Bicat.Hom.ext hx⟩

/-- **Every indecomposable object of `U̇(λ, ρ)` is a direct summand of some `E_w 1_λ {n}`.** -/
theorem exists_retract_nfObj {ρ lam : X} {Z : UKar RD k ρ lam} (hZ : IsIndec Z) :
    ∃ (w : List (Letter I)) (h : wt RD lam w = ρ) (n : ℤ) (f : Z ⟶ nfObj RD k ρ lam w h n)
      (g : nfObj RD k ρ lam w h n ⟶ Z), f ≫ g = 𝟙 Z := by
  haveI := homFinite_UDot (RD := RD) (k := k) hSL ρ lam
  obtain ⟨M, p, hp⟩ := Z
  let f₀ : (⟨M, p, hp⟩ : UKar RD k ρ lam) ⟶ (toKaroubi _).obj M :=
    ⟨p, by simp [hp]⟩
  let g₀ : (toKaroubi _).obj M ⟶ (⟨M, p, hp⟩ : UKar RD k ρ lam) :=
    ⟨p, by simp [hp]⟩
  have h₀ : f₀ ≫ g₀ = 𝟙 _ := Karoubi.hom_ext _ _ (by simp [f₀, g₀, hp])
  let e := Mat_.isoBiproductEmbedding M
  let V : M.ι → UKar RD k ρ lam := fun i =>
    (toKaroubi _).obj ((Mat_.embedding _).obj (M.X i))
  let A : ∀ i, (toKaroubi _).obj M ⟶ V i := fun i =>
    (toKaroubi _).map (e.hom ≫ biproduct.π (fun j => (Mat_.embedding _).obj (M.X j)) i)
  let B : ∀ i, V i ⟶ (toKaroubi _).obj M := fun i =>
    (toKaroubi _).map (biproduct.ι (fun j => (Mat_.embedding _).obj (M.X j)) i ≫ e.inv)
  have htot : ∑ i ∈ Finset.univ, A i ≫ B i = 𝟙 _ := by
    simp only [A, B, ← Functor.map_comp, ← Functor.map_sum]
    have hs : (∑ j, (e.hom ≫ biproduct.π (fun j => (Mat_.embedding _).obj (M.X j)) j) ≫
        biproduct.ι (fun j => (Mat_.embedding _).obj (M.X j)) j ≫ e.inv) = 𝟙 M := by
      simp only [Category.assoc, ← Preadditive.comp_sum]
      rw [show (∑ j, biproduct.π (fun j => (Mat_.embedding _).obj (M.X j)) j ≫
          biproduct.ι (fun j => (Mat_.embedding _).obj (M.X j)) j ≫ e.inv) =
          (∑ j, biproduct.π (fun j => (Mat_.embedding _).obj (M.X j)) j ≫
            biproduct.ι (fun j => (Mat_.embedding _).obj (M.X j)) j) ≫ e.inv by
          rw [Preadditive.sum_comp]; simp only [Category.assoc],
        biproduct.total, Category.id_comp, e.hom_inv_id]
    rw [hs, CategoryTheory.Functor.map_id]
  obtain ⟨i, -, f', g', h'⟩ := hZ.exists_retract_of_sum k f₀ g₀ h₀ Finset.univ V A B htot
  obtain ⟨w, h, hx⟩ := exists_eq_nfHom (RD := RD) (k := k) (M.X i).x
  refine ⟨w, h, (M.X i).t, ?_⟩
  have hV : V i = nfObj RD k ρ lam w h (M.X i).t := by
    have hX : M.X i = ⟨nfHom RD k ρ lam w h, (M.X i).t⟩ := GrObj.ext hx rfl
    simp only [V]
    rw [hX]
    rfl
  rw [← hV]
  exact ⟨f', g', h'⟩

/-- **KL III Lemma 3.38, module level**: an indecomposable direct summand of `E_w 1_λ {n}` is a
direct summand of `E_{+a} E_{-b} 1_λ {n'}` for a sorted sequence `(+a)(-b)` with
`|a| + |b| ≤ |w|` and `|a| + |b| ≡ |w| mod 2`. -/
theorem exists_retract_sorted_of_retract {ρ lam : X} {w : List (Letter I)}
    {h : wt RD lam w = ρ} {n : ℤ} {Z : UKar RD k ρ lam} (hZ : IsIndec Z)
    (f : Z ⟶ nfObj RD k ρ lam w h n) (g : nfObj RD k ρ lam w h n ⟶ Z) (hfg : f ≫ g = 𝟙 Z) :
    ∃ (a b : List I) (hab : wt RD lam (ups a ++ dns b) = ρ) (n' : ℤ),
      a.length + b.length ≤ w.length ∧ (a.length + b.length) % 2 = w.length % 2 ∧
      ∃ (f' : Z ⟶ nfObj RD k ρ lam (ups a ++ dns b) hab n')
        (g' : nfObj RD k ρ lam (ups a ++ dns b) hab n' ⟶ Z), f' ≫ g' = 𝟙 Z := by
  obtain ⟨u, ⟨⟨a, b, rfl⟩, hl, hp⟩, hu, n', f', g', h'⟩ := exists_retract_of_thru hSL
    (one_mem_thru_sorted (RD := RD) (k := k) lam (invR w + 1) w (Nat.lt_succ_self _)) hZ f g hfg
  have hlen : (ups a ++ dns b).length = a.length + b.length := by simp [ups, dns]
  exact ⟨a, b, hu, n', hlen ▸ hl, hlen ▸ hp, f', g', h'⟩

/-- **Every indecomposable 1-morphism of `U̇(λ, ρ)` is a direct summand of a sorted
`E_{+a} E_{-b} 1_λ {n}`** (KL III §3.8.4). -/
theorem exists_retract_sorted {ρ lam : X} {Z : UKar RD k ρ lam} (hZ : IsIndec Z) :
    ∃ (a b : List I) (hab : wt RD lam (ups a ++ dns b) = ρ) (n : ℤ)
      (f : Z ⟶ nfObj RD k ρ lam (ups a ++ dns b) hab n)
      (g : nfObj RD k ρ lam (ups a ++ dns b) hab n ⟶ Z), f ≫ g = 𝟙 Z := by
  obtain ⟨w, h, n, f, g, hfg⟩ := exists_retract_nfObj hSL hZ
  obtain ⟨a, b, hab, n', -, -, f', g', h'⟩ := exists_retract_sorted_of_retract hSL hZ f g hfg
  exact ⟨a, b, hab, n', f', g', h'⟩

/-- **`K₀(U̇(λ, ρ))` is spanned by the classes of the indecomposable direct summands of the
sorted 1-morphisms `E_{+a} E_{-b} 1_λ {n}`.** -/
theorem K0Kar_span_sorted_summands (ρ lam : X) :
    Submodule.span (LaurentPolynomial ℤ) {x : K0Kar RD k ρ lam | ∃ Z : UKar RD k ρ lam,
      IsIndec Z ∧ (∃ (a b : List I) (hab : wt RD lam (ups a ++ dns b) = ρ) (n : ℤ)
        (f : Z ⟶ nfObj RD k ρ lam (ups a ++ dns b) hab n)
        (g : nfObj RD k ρ lam (ups a ++ dns b) hab n ⟶ Z), f ≫ g = 𝟙 Z) ∧ x = K0U.cl Z} = ⊤ := by
  rw [eq_top_iff, ← (indecBasisU (k := k) hSL ρ lam).span_eq, Submodule.span_le]
  rintro _ ⟨b, rfl⟩
  rw [indecBasisU_apply]
  exact Submodule.subset_span ⟨b.rep, b.isIndec_rep, exists_retract_sorted hSL b.isIndec_rep, rfl⟩

end Retracts

end Categorification.KL3.Diagram

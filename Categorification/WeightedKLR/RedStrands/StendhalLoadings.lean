/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.RedStrands.CrawleyBoeveyIn
import Categorification.WeightedKLR.RedStrands.Stendhal
import Categorification.WeightedKLR.KLR.SpacedCrossing

/-!
# Stendhal loadings

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, proof of
Theorem 3.5: the loadings of the Crawley-Boevey graph `Γ_λ` (new edges directed into the new
vertex, of weights `ϖ_1 < ⋯ < ϖ_ℓ`, old edges of weight `0`) attached to Stendhal sequences.

Webster turns the ghosts of the `0`-labelled strand into the red strands of a Stendhal diagram.
Conversely, a sequence `i` of black and red termini of a Stendhal diagram, with red strands in
the order `λ_1, …, λ_ℓ`, gives a loading: the `0`-strand at `0`, so that its ghost for the new
edges of `λ_j` is at `ϖ_j`, and the black strands at increasing points, each lying between the
ghosts `ϖ_j` with the same red strands on its left as in `i`.

We place the black strand at position `p` (among `M` positions, `g` of the red positions being
smaller than `p`) at `stPt ϖ M ρ p`, a point strictly between the `g`-th and `(g + 1)`-st entry of
the sequence `ϖ_1 - 1 < ϖ_1 < ⋯ < ϖ_ℓ < ⋯` (`lowB`). These points increase with `p`, and lie
right of the ghost `ϖ_j` exactly when the `j`-th red position is smaller than `p`
(`ghost_lt_stPt_iff`).

## Main definitions

* `Stendhal.stPt`: the points of the black strands.
* `Stendhal.toTilde`: the strands of a Stendhal sequence as strands of `ν̃ = ν + α_0`, the red
  strands becoming the `0`-strand.
* `Stendhal.stCfg`: the loading of a position function on the strands of a Stendhal sequence.

## Main results

* `Stendhal.stPt_lt_stPt`, `Stendhal.ghost_lt_stPt_iff`.
* `Stendhal.oldWall_pos_iff`, `Stendhal.newWall_pos_iff`, `Stendhal.diag_pos_iff`: the side of
  each hyperplane on which `stCfg` lies.
* `Stendhal.isGeneric_stCfg`.
* `Stendhal.separates_stCfg_swap_black`, `Stendhal.separates_stCfg_swap_red`: the hyperplanes
  crossed by exchanging two neighbouring black strands, or a black and a red strand.
-/

namespace Categorification.Stendhal

open Categorification.WeightedKLR Equiv

section Points

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {ℓ : ℕ}
  (ϖ : Fin ℓ → 𝕜)

/-- The weights `ϖ_j`, continued past `ℓ` by an increasing sequence. -/
def extW (n : ℕ) : 𝕜 :=
  if h : n < ℓ then ϖ ⟨n, h⟩ else (1 + ∑ r, |ϖ r|) + n

variable {ϖ}

omit [IsStrictOrderedRing 𝕜] in
theorem extW_of_lt {n : ℕ} (h : n < ℓ) : extW ϖ n = ϖ ⟨n, h⟩ := by simp [extW, h]

omit [IsStrictOrderedRing 𝕜] in
theorem extW_of_not_lt {n : ℕ} (h : ¬ n < ℓ) : extW ϖ n = (1 + ∑ r, |ϖ r|) + n := by
  simp [extW, h]

omit [IsStrictOrderedRing 𝕜] in
theorem extW_fin (r : Fin ℓ) : extW ϖ r = ϖ r := extW_of_lt r.2

theorem extW_strictMono (hϖ : StrictMono ϖ) : StrictMono (extW ϖ) := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  by_cases h1 : n + 1 < ℓ
  · rw [extW_of_lt h1, extW_of_lt (by omega)]
    exact hϖ (Fin.mk_lt_mk.2 (Nat.lt_succ_self n))
  · rw [extW_of_not_lt h1]
    by_cases h0 : n < ℓ
    · rw [extW_of_lt h0]
      have h2 := Finset.single_le_sum (fun r (_ : r ∈ Finset.univ) => abs_nonneg (ϖ r))
        (Finset.mem_univ ⟨n, h0⟩)
      have h3 := le_abs_self (ϖ ⟨n, h0⟩)
      have h4 : (0 : 𝕜) ≤ ((n + 1 : ℕ) : 𝕜) := Nat.cast_nonneg _
      linarith
    · rw [extW_of_not_lt h0]
      push_cast
      linarith

variable (ϖ) in
/-- The bounds of the intervals of black strands: `ϖ_1 - 1, ϖ_1, ϖ_2, …`. -/
def lowB : ℕ → 𝕜
  | 0 => extW ϖ 0 - 1
  | n + 1 => extW ϖ n

theorem lowB_strictMono (hϖ : StrictMono ϖ) : StrictMono (lowB ϖ) := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  cases n with
  | zero => show extW ϖ 0 - 1 < extW ϖ 0; linarith
  | succ n => exact extW_strictMono hϖ (Nat.lt_succ_self n)

/-- The number of red positions smaller than `p`. -/
def gap (ρ : Fin ℓ → ℕ) (p : ℕ) : ℕ := (Finset.univ.filter fun r => ρ r < p).card

theorem gap_mono (ρ : Fin ℓ → ℕ) {p p' : ℕ} (h : p ≤ p') : gap ρ p ≤ gap ρ p' :=
  Finset.card_le_card fun r hr => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
    omega

theorem succ_le_gap {ρ : Fin ℓ → ℕ} (hρ : StrictMono ρ) {p : ℕ} {r : Fin ℓ} (h : ρ r < p) :
    r.val + 1 ≤ gap ρ p := by
  rw [← Fin.card_Iic]
  refine Finset.card_le_card fun r' hr' => ?_
  simp only [Finset.mem_Iic] at hr'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact lt_of_le_of_lt (hρ.monotone hr') h

theorem gap_le {ρ : Fin ℓ → ℕ} (hρ : StrictMono ρ) {p : ℕ} {r : Fin ℓ} (h : p < ρ r) :
    gap ρ p ≤ r.val := by
  conv_rhs => rw [← Fin.card_Iio r]
  refine Finset.card_le_card fun r' hr' => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr'
  simp only [Finset.mem_Iio]
  exact hρ.lt_iff_lt.1 (by omega)

variable (ϖ) in
/-- The point of the black strand at position `p < M`, when the red strands are at the
positions `ρ`: a point strictly between `lowB (gap ρ p)` and `lowB (gap ρ p + 1)`, increasing
with `p`. -/
def stPt (M : ℕ) (ρ : Fin ℓ → ℕ) (p : ℕ) : 𝕜 :=
  lowB ϖ (gap ρ p) + (lowB ϖ (gap ρ p + 1) - lowB ϖ (gap ρ p)) * ((p + 1) / (M + 1))

theorem frac_pos_lt_one {M p : ℕ} (h : p < M) :
    (0 : 𝕜) < ((p : 𝕜) + 1) / ((M : 𝕜) + 1) ∧ ((p : 𝕜) + 1) / ((M : 𝕜) + 1) < 1 := by
  have hM : (0 : 𝕜) < (M : 𝕜) + 1 := by positivity
  have hp : (p : 𝕜) + 1 < (M : 𝕜) + 1 := by exact_mod_cast Nat.succ_lt_succ h
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one hM]
  exact hp

theorem lowB_lt_stPt (hϖ : StrictMono ϖ) {M : ℕ} (ρ : Fin ℓ → ℕ) {p : ℕ} (h : p < M) :
    lowB ϖ (gap ρ p) < stPt ϖ M ρ p := by
  have hd := sub_pos.2 (lowB_strictMono hϖ (Nat.lt_succ_self (gap ρ p)))
  have ht := (frac_pos_lt_one (𝕜 := 𝕜) h).1
  unfold stPt
  nlinarith

theorem stPt_lt_lowB (hϖ : StrictMono ϖ) {M : ℕ} (ρ : Fin ℓ → ℕ) {p : ℕ} (h : p < M) :
    stPt ϖ M ρ p < lowB ϖ (gap ρ p + 1) := by
  have hd := sub_pos.2 (lowB_strictMono hϖ (Nat.lt_succ_self (gap ρ p)))
  have ht := (frac_pos_lt_one (𝕜 := 𝕜) h).2
  unfold stPt
  nlinarith

/-- The points of the black strands increase with their positions. -/
theorem stPt_lt_stPt (hϖ : StrictMono ϖ) {M : ℕ} (ρ : Fin ℓ → ℕ) {p p' : ℕ} (hp : p < p')
    (hp' : p' < M) : stPt ϖ M ρ p < stPt ϖ M ρ p' := by
  have hg := gap_mono ρ hp.le
  rcases hg.lt_or_eq with hg | hg
  · calc stPt ϖ M ρ p < lowB ϖ (gap ρ p + 1) := stPt_lt_lowB hϖ ρ (hp.trans hp')
      _ ≤ lowB ϖ (gap ρ p') := (lowB_strictMono hϖ).monotone hg
      _ < stPt ϖ M ρ p' := lowB_lt_stPt hϖ ρ hp'
  · have hd := sub_pos.2 (lowB_strictMono hϖ (Nat.lt_succ_self (gap ρ p)))
    have hM : (0 : 𝕜) < (M : 𝕜) + 1 := by positivity
    have hpp : ((p : 𝕜) + 1) / ((M : 𝕜) + 1) < ((p' : 𝕜) + 1) / ((M : 𝕜) + 1) := by
      rw [div_lt_div_iff_of_pos_right hM]
      exact_mod_cast Nat.succ_lt_succ hp
    unfold stPt
    rw [← hg]
    nlinarith

theorem stPt_injOn (hϖ : StrictMono ϖ) {M : ℕ} (ρ : Fin ℓ → ℕ) {p p' : ℕ} (hp : p < M)
    (hp' : p' < M) (h : stPt ϖ M ρ p = stPt ϖ M ρ p') : p = p' := by
  rcases lt_trichotomy p p' with hl | rfl | hl
  · exact absurd h (stPt_lt_stPt hϖ ρ hl hp').ne
  · rfl
  · exact absurd h (stPt_lt_stPt hϖ ρ hl hp).ne'

theorem stPt_lt_ghost (hϖ : StrictMono ϖ) {M : ℕ} {ρ : Fin ℓ → ℕ} (hρ : StrictMono ρ)
    {p : ℕ} (hp : p < M) {r : Fin ℓ} (hlt : p < ρ r) : stPt ϖ M ρ p < ϖ r :=
  calc stPt ϖ M ρ p < lowB ϖ (gap ρ p + 1) := stPt_lt_lowB hϖ ρ hp
    _ ≤ lowB ϖ (r.val + 1) := (lowB_strictMono hϖ).monotone (by have := gap_le hρ hlt; omega)
    _ = ϖ r := extW_fin r

theorem stPt_lt_stPt_iff (hϖ : StrictMono ϖ) {M : ℕ} (ρ : Fin ℓ → ℕ) {p p' : ℕ} (hp : p < M)
    (hp' : p' < M) : stPt ϖ M ρ p < stPt ϖ M ρ p' ↔ p < p' := by
  refine ⟨fun h => ?_, fun h => stPt_lt_stPt hϖ ρ h hp'⟩
  by_contra h'
  rcases (not_lt.1 h').lt_or_eq with h'' | h''
  · exact absurd h (not_lt.2 (stPt_lt_stPt hϖ ρ h'' hp).le)
  · subst h''; exact lt_irrefl _ h

/-- **The ghosts of the `0`-strand are the red strands**: the black strand at position `p`, not
a red position, lies right of `ϖ_j` exactly when the `j`-th red strand is left of it. -/
theorem ghost_lt_stPt_iff (hϖ : StrictMono ϖ) {M : ℕ} {ρ : Fin ℓ → ℕ} (hρ : StrictMono ρ)
    {p : ℕ} (hp : p < M) (hpr : ∀ r, ρ r ≠ p) (r : Fin ℓ) :
    ϖ r < stPt ϖ M ρ p ↔ ρ r < p := by
  constructor
  · intro h
    by_contra h'
    have hlt : p < ρ r := lt_of_le_of_ne (not_lt.1 h') (hpr r).symm
    exact absurd h (not_lt.2 (stPt_lt_ghost hϖ hρ hp hlt).le)
  · intro h
    calc ϖ r = lowB ϖ (r.val + 1) := (extW_fin r).symm
      _ ≤ lowB ϖ (gap ρ p) := (lowB_strictMono hϖ).monotone (succ_le_gap hρ h)
      _ < stPt ϖ M ρ p := lowB_lt_stPt hϖ ρ hp

end Points

section Strands

variable {I : Type} [DecidableEq I] {ℓ : ℕ} {ν : Multiset I}

local notation "μ" => Multiset.toFinsupp (stendhalWeight ℓ ν)
local notation "ν̃" => WeightedGraph.redWeight (Multiset.toFinsupp ν)

theorem stendhalWeight_inl (a : I) :
    Multiset.toFinsupp (stendhalWeight ℓ ν) (.inl a) = ν.count a := by
  rw [Multiset.toFinsupp_apply, stendhalWeight, Multiset.count_add,
    Multiset.count_map_eq_count' _ _ Sum.inl_injective]
  simp

theorem stendhalWeight_inr (r : Fin ℓ) :
    Multiset.toFinsupp (stendhalWeight ℓ ν) (.inr r) = 1 := by
  rw [Multiset.toFinsupp_apply, stendhalWeight, Multiset.count_add,
    Multiset.count_map_eq_count' _ _ Sum.inr_injective]
  simp

theorem redWeight_toFinsupp_some (a : I) : ν̃ (some a) = ν.count a := by
  rw [WeightedGraph.redWeight_some, Multiset.toFinsupp_apply]

variable (ν) in
/-- The red strand labelled `λ_r` of a Stendhal sequence. -/
def redStrand (r : Fin ℓ) : Strand μ :=
  ⟨⟨.inr r, Finsupp.mem_support_iff.2 (by rw [stendhalWeight_inr]; exact one_ne_zero)⟩,
    ⟨0, by rw [stendhalWeight_inr]; exact Nat.one_pos⟩⟩

theorem redStrand_injective : Function.Injective (redStrand (ℓ := ℓ) ν) := by
  intro r r' h
  have := congrArg (fun s : Strand μ => s.1.1) h
  exact Sum.inr_injective this

/-- The strands of a Stendhal sequence as strands of `ν̃ = ν + α_0`: the black strands are the
strands of `ν`, and the red strands all become the `0`-strand. -/
def toTilde : Strand μ → Strand ν̃
  | ⟨⟨.inl a, ha⟩, r⟩ => ⟨⟨some a, Finsupp.mem_support_iff.2 (by
      rw [redWeight_toFinsupp_some, ← stendhalWeight_inl (ℓ := ℓ)]
      exact Finsupp.mem_support_iff.1 ha)⟩,
      ⟨r.val, by rw [redWeight_toFinsupp_some, ← stendhalWeight_inl (ℓ := ℓ)]; exact r.2⟩⟩
  | ⟨⟨.inr _, _⟩, _⟩ => GalleryAlgebra.zeroStrand _

/-- The black strand of a Stendhal sequence corresponding to a strand of `ν̃` other than the
`0`-strand. -/
def ofTilde : Strand ν̃ → Option (Strand μ)
  | ⟨⟨none, _⟩, _⟩ => none
  | ⟨⟨some a, ha⟩, r⟩ => some ⟨⟨.inl a, Finsupp.mem_support_iff.2 (by
      rw [stendhalWeight_inl, ← redWeight_toFinsupp_some]
      exact Finsupp.mem_support_iff.1 ha)⟩,
      ⟨r.val, by rw [stendhalWeight_inl, ← redWeight_toFinsupp_some]; exact r.2⟩⟩

theorem ofTilde_toTilde_inl {s : Strand μ} (hs : s.1.1.isLeft) : ofTilde (toTilde s) = some s := by
  obtain ⟨⟨a | r, ha⟩, n⟩ := s
  · rfl
  · simp at hs

theorem toTilde_of_ofTilde {t : Strand ν̃} {s : Strand μ} (h : ofTilde t = some s) :
    toTilde s = t := by
  obtain ⟨⟨_ | a, ha⟩, n⟩ := t
  · simp [ofTilde] at h
  · simp only [ofTilde, Option.some.injEq] at h
    subst h
    rfl

theorem isLeft_of_ofTilde {t : Strand ν̃} {s : Strand μ} (h : ofTilde t = some s) :
    s.1.1.isLeft := by
  obtain ⟨⟨_ | a, ha⟩, n⟩ := t
  · simp [ofTilde] at h
  · simp only [ofTilde, Option.some.injEq] at h
    subst h
    rfl

theorem exists_ofTilde {t : Strand ν̃} (h : t.1.1 ≠ none) :
    ∃ s : Strand μ, ofTilde t = some s := by
  obtain ⟨⟨_ | a, ha⟩, n⟩ := t
  · exact absurd rfl h
  · exact ⟨_, rfl⟩

theorem ofTilde_zeroStrand : ofTilde (GalleryAlgebra.zeroStrand (Multiset.toFinsupp ν)) =
    (none : Option (Strand μ)) := rfl

theorem toTilde_ne_zeroStrand {s : Strand μ} (hs : s.1.1.isLeft) :
    toTilde s ≠ GalleryAlgebra.zeroStrand (Multiset.toFinsupp ν) := by
  intro h
  have := ofTilde_toTilde_inl hs
  rw [h, ofTilde_zeroStrand] at this
  simp at this

theorem toTilde_inj {s s' : Strand μ} (hs : s.1.1.isLeft) (hs' : s'.1.1.isLeft) :
    toTilde s = toTilde s' ↔ s = s' := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  have h1 := ofTilde_toTilde_inl hs
  rw [h, ofTilde_toTilde_inl hs'] at h1
  exact (Option.some_injective _ h1).symm

theorem not_isLeft_redStrand (r : Fin ℓ) : ¬ (redStrand ν r).1.1.isLeft := by
  simp [redStrand]

theorem ofTilde_eq_none {t : Strand ν̃} (h : t.1.1 = none) : ofTilde t = (none : Option (Strand μ)) := by
  obtain ⟨⟨_ | a, ha⟩, n⟩ := t
  · rfl
  · simp at h

theorem exists_ofTilde_of_ne {t : Strand ν̃} (h : t ≠ GalleryAlgebra.zeroStrand _) :
    ∃ s : Strand μ, ofTilde t = some s := by
  refine exists_ofTilde fun h' => h ?_
  exact GalleryAlgebra.eq_of_fst_eq (GalleryAlgebra.redWeight_zeroStrand _) (Subtype.ext h')

end Strands

section Config

variable {I : Type} [DecidableEq I] {ℓ : ℕ} {ν : Multiset I}
  {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k]
  {Γ : WeightedGraph I 𝕜 k} {Λ : Fin ℓ → I →₀ ℕ} {ϖ : Fin ℓ → 𝕜}

local notation "μ" => Multiset.toFinsupp (stendhalWeight ℓ ν)
local notation "ν̃" => WeightedGraph.redWeight (Multiset.toFinsupp ν)
local notation "Γλ" => WeightedGraph.crawleyBoeveyIn Γ Λ ϖ

variable (ν) in
/-- The positions of the red strands. -/
def redPosOf (π : Strand μ → ℕ) (r : Fin ℓ) : ℕ := π (redStrand ν r)

variable (ϖ) in
/-- **The loading of a Stendhal position function** `π` (positions `< M`): the `0`-strand at
`0`, and the black strand `s` at `stPt ϖ M ρ (π s)`, `ρ` the positions of the red strands. -/
def stCfg (M : ℕ) (π : Strand μ → ℕ) (t : Strand ν̃) : 𝕜 :=
  (ofTilde t).elim 0 fun s => stPt ϖ M (redPosOf ν π) (π s)

omit [IsStrictOrderedRing 𝕜] in
theorem stCfg_some {M : ℕ} {π : Strand μ → ℕ} {t : Strand ν̃} {s : Strand μ}
    (h : ofTilde t = some s) : stCfg ϖ M π t = stPt ϖ M (redPosOf ν π) (π s) := by
  rw [stCfg, h, Option.elim_some]

omit [IsStrictOrderedRing 𝕜] in
theorem stCfg_none {M : ℕ} {π : Strand μ → ℕ} {t : Strand ν̃} (h : t.1.1 = none) :
    stCfg ϖ M π t = 0 := by
  rw [stCfg, ofTilde_eq_none h, Option.elim_none]

variable (ν) in
/-- An admissible position function: injective, with values `< M`, and with the red strands in
the order `λ_1, …, λ_ℓ`. -/
structure IsAdm (M : ℕ) (π : Strand μ → ℕ) : Prop where
  inj : Function.Injective π
  lt : ∀ s, π s < M
  red : StrictMono (redPosOf ν π)

theorem IsAdm.ne_red {M : ℕ} {π : Strand μ → ℕ} (hπ : IsAdm ν M π) {s : Strand μ}
    (hs : s.1.1.isLeft) (r : Fin ℓ) : redPosOf ν π r ≠ π s := fun h =>
  not_isLeft_redStrand (ν := ν) r (hπ.inj h ▸ hs)

/-- The side of an old wall: `x_b > x_a` exactly when `π a < π b`. -/
theorem oldWall_pos_iff (hϖ : StrictMono ϖ) (hw0 : ∀ e, Γ.weight e = 0) {M : ℕ}
    {π : Strand μ → ℕ} (hπ : IsAdm ν M π) (w : Wall Γλ ν̃) {e : Γ.E} (he : w.edge = .inl e)
    {a b : Strand μ} (ha : ofTilde w.src = some a) (hb : ofTilde w.tgt = some b) :
    0 < w.val (stCfg ϖ M π) ↔ π a < π b := by
  have hw : Γλ.weight w.edge = 0 := by rw [he]; exact hw0 e
  rw [Wall.val, hw, sub_zero, stCfg_some ha, stCfg_some hb, sub_pos,
    stPt_lt_stPt_iff hϖ _ (hπ.lt a) (hπ.lt b)]

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem src_none_of_edge_inr (w : Wall Γλ ν̃) {c : WeightedGraph.RedEdge Λ}
    (he : w.edge = .inr c) : w.src.1.1 = none := by
  have := w.2.1
  rw [show w.1.1 = w.edge from rfl, he] at this
  exact this

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem tgt_label_of_edge_inr (w : Wall Γλ ν̃) {c : WeightedGraph.RedEdge Λ}
    (he : w.edge = .inr c) : w.tgt.1.1 = some c.2.1 := by
  have := w.2.2.1
  rw [show w.1.1 = w.edge from rfl, he] at this
  exact this

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem label_of_edge_inl (w : Wall Γλ ν̃) {e : Γ.E} (he : w.edge = .inl e) :
    w.src.1.1 = some (Γ.head e) ∧ w.tgt.1.1 = some (Γ.tail e) := by
  have h1 := w.2.1
  have h2 := w.2.2.1
  rw [show w.1.1 = w.edge from rfl, he] at h1 h2
  exact ⟨h1, h2⟩

/-- The side of a new wall `x_b - x_0 = ϖ_j`: `b` lies right of the ghost `ϖ_j` exactly when
the red strand `λ_j` is left of it. -/
theorem newWall_pos_iff (hϖ : StrictMono ϖ) {M : ℕ} {π : Strand μ → ℕ} (hπ : IsAdm ν M π)
    (w : Wall Γλ ν̃) {c : WeightedGraph.RedEdge Λ} (he : w.edge = .inr c) {b : Strand μ}
    (hb : ofTilde w.tgt = some b) :
    0 < w.val (stCfg ϖ M π) ↔ π (redStrand ν c.1) < π b := by
  have hw : Γλ.weight w.edge = ϖ c.1 := by rw [he]; rfl
  rw [Wall.val, hw, stCfg_none (src_none_of_edge_inr w he), stCfg_some hb, sub_zero, sub_pos]
  exact ghost_lt_stPt_iff hϖ hπ.red (hπ.lt b) (hπ.ne_red (isLeft_of_ofTilde hb)) c.1

theorem diag_pos_iff (hϖ : StrictMono ϖ) {M : ℕ} {π : Strand μ → ℕ} (hπ : IsAdm ν M π)
    (d : Diag ν̃) {a b : Strand μ} (ha : ofTilde d.fst = some a) (hb : ofTilde d.snd = some b) :
    0 < d.val (stCfg ϖ M π) ↔ π a < π b := by
  rw [Diag.val, stCfg_some ha, stCfg_some hb, sub_pos,
    stPt_lt_stPt_iff hϖ _ (hπ.lt a) (hπ.lt b)]

theorem exists_ofTilde_diag (d : Diag ν̃) :
    (∃ a : Strand μ, ofTilde d.fst = some a) ∧ ∃ b : Strand μ, ofTilde d.snd = some b :=
  ⟨exists_ofTilde_of_ne (GalleryAlgebra.diag_ne (GalleryAlgebra.redWeight_zeroStrand _) d).1,
    exists_ofTilde_of_ne (GalleryAlgebra.diag_ne (GalleryAlgebra.redWeight_zeroStrand _) d).2⟩

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem exists_ofTilde_wall_inl (w : Wall Γλ ν̃) {e : Γ.E} (he : w.edge = .inl e) :
    (∃ a : Strand μ, ofTilde w.src = some a) ∧ ∃ b : Strand μ, ofTilde w.tgt = some b :=
  ⟨exists_ofTilde (by rw [(label_of_edge_inl w he).1]; exact Option.some_ne_none _),
    exists_ofTilde (by rw [(label_of_edge_inl w he).2]; exact Option.some_ne_none _)⟩

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem exists_ofTilde_wall_inr (w : Wall Γλ ν̃) {c : WeightedGraph.RedEdge Λ}
    (he : w.edge = .inr c) : ∃ b : Strand μ, ofTilde w.tgt = some b :=
  exists_ofTilde (by rw [tgt_label_of_edge_inr w he]; exact Option.some_ne_none _)

theorem ne_of_ofTilde {t t' : Strand ν̃} (h : t ≠ t') {a b : Strand μ} (ha : ofTilde t = some a)
    (hb : ofTilde t' = some b) : a ≠ b := by
  rintro rfl
  exact h ((toTilde_of_ofTilde ha).symm.trans (toTilde_of_ofTilde hb))

/-- **The Stendhal loading is generic.** -/
theorem isGeneric_stCfg (hϖ : StrictMono ϖ) (hw0 : ∀ e, Γ.weight e = 0) {M : ℕ}
    {π : Strand μ → ℕ} (hπ : IsAdm ν M π) : IsGeneric Γλ (stCfg ϖ M π) := by
  intro h
  rcases h with w | d
  · rw [Hyp.val_inl]
    rcases he : w.edge with e | c
    · obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := exists_ofTilde_wall_inl w he
      have hab := ne_of_ofTilde w.2.2.2 ha hb
      have hab' : π a ≠ π b := fun h => hab (hπ.inj h)
      rw [Wall.val, show Γλ.weight w.edge = 0 by rw [he]; exact hw0 e, sub_zero,
        stCfg_some ha, stCfg_some hb, sub_ne_zero]
      exact fun h => hab' (stPt_injOn hϖ _ (hπ.lt a) (hπ.lt b) h.symm)
    · obtain ⟨b, hb⟩ := exists_ofTilde_wall_inr w he
      have hw : Γλ.weight w.edge = ϖ c.1 := by rw [he]; rfl
      rw [Wall.val, hw, stCfg_none (src_none_of_edge_inr w he), stCfg_some hb, sub_zero,
        sub_ne_zero]
      intro h
      rcases lt_or_gt_of_ne (hπ.ne_red (isLeft_of_ofTilde hb) c.1) with hl | hl
      · exact (ne_of_gt ((ghost_lt_stPt_iff hϖ hπ.red (hπ.lt b)
          (hπ.ne_red (isLeft_of_ofTilde hb)) c.1).2 hl)) h
      · exact (stPt_lt_ghost hϖ hπ.red (hπ.lt b) hl).ne h
  · rw [Hyp.val_inr]
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := exists_ofTilde_diag (ℓ := ℓ) d
    have hne : d.fst ≠ d.snd := fun h => by
      have h2 : d.fst.2.val < d.snd.2.val := d.2.2
      rw [h] at h2
      exact lt_irrefl _ h2
    have hab := ne_of_ofTilde hne ha hb
    have hab' : π a ≠ π b := fun h => hab (hπ.inj h)
    rw [Diag.val, stCfg_some ha, stCfg_some hb, sub_ne_zero]
    exact fun h => hab' (stPt_injOn hϖ _ (hπ.lt a) (hπ.lt b) h.symm)

end Config

end Categorification.Stendhal

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidCornerFactor
import Categorification.WeightedKLR.Rigidity.CupCapMidCornerTopBasis
import Categorification.WeightedKLR.Rigidity.CupCapEndIndex

/-!
# Indices of the basis of `T̃^{λ⁺}` adapted to the window before `λ_{j+1}`

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17, for the cap after the red strand `λ_j`.
For a term of the basis of `T̃^{λ⁺}` whose top is a loading `midSeq j hj s t` with the window at
`c = midPos j s`, write its permutation as `w = b u` with `b` a permutation of the window and `u` a
window shuffle (`winEquiv`), and choose the reduced word `(c + ρ₂(b)) ρ₃(u)` (`midWordAt`). This
word depends on the loading through `c`, so the basis is the one with words chosen per loading
(`topBasisSeq`, word `midWord`). Its terms with top in `midSet` are indexed by pairs
(`MidPair`, `midPairIdx`): a generator `g = (s, t, d, u)` (`MidGen`: red-ordered loadings `s` of
`λ` and `t` at the maximum, dots `d` on the black strands of `s` and a window shuffle `u`), and a
term of the basis of `T̃^{(μ,μ*)}` with dots on top and bottom `t`.

## Main definitions

* `CupCap.midWordAt`, `CupCap.midWord`: the reduced words adapted to the window.
* `CupCap.MidGen`, `CupCap.MidPair`, `CupCap.midPairIdx`: the indices.

## Main results

* `CupCap.midWord_spec`: the words are reduced.
* `CupCap.midPairIdx_injective`, `CupCap.exists_midPairIdx`: the pairs index exactly the basis
  terms whose top lies in `midSet`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA Equiv MvPolynomial

variable {I : Type} [DecidableEq I] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ} {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))

section Words

variable (ρ₂ : Perm (Fin (Multiset.card (stendhalWeight 2 ν₀))) → List ℕ)
  (ρ₃ : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀)))) → List ℕ)

variable (j) in
/-- The word `(c + ρ₂(b)) ρ₃(u)` attached to `w = b u`, for the window at `c = midPos j s`. -/
def midWordAt (s : Seq (stendhalWeight ℓ ν)) (w : Perm (Fin M)) : List ℕ :=
  shiftWord (midPos j s) (ρ₂ ((winEquiv (midPos_add_N_le j ν₀ s)).symm w).1) ++
    ρ₃ ((winEquiv (midPos_add_N_le j ν₀ s)).symm w).2.1

omit [DecidableEq I] in
theorem midWordAt_winPerm_mul (s : Seq (stendhalWeight ℓ ν)) (b : Perm (Fin N))
    (u : WinShuffle (midPos_add_N_le j ν₀ s)) :
    midWordAt j ρ₂ ρ₃ s (winPerm (midPos_add_N_le j ν₀ s) b * u.1) =
      shiftWord (midPos j s) (ρ₂ b) ++ ρ₃ u.1 := by
  have : (winEquiv (midPos_add_N_le j ν₀ s)).symm (winPerm (midPos_add_N_le j ν₀ s) b * u.1) =
      (b, u) := (winEquiv _).symm_apply_apply (b, u)
  rw [midWordAt, this]

variable {ρ₂ ρ₃}

omit [DecidableEq I] in
theorem midWordAt_spec (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w) (s : Seq (stendhalWeight ℓ ν))
    (w : Perm (Fin M)) :
    IsReduced M (midWordAt j ρ₂ ρ₃ s w) ∧ wordProd M (midWordAt j ρ₂ ρ₃ s w) = w := by
  obtain ⟨⟨b, u⟩, rfl⟩ := (winEquiv (midPos_add_N_le j ν₀ s)).surjective w
  rw [winEquiv_apply, midWordAt_winPerm_mul]
  have hu : IsWinShuffle (midPos_add_N_le j ν₀ s) (wordProd M (ρ₃ u.1)) := by
    rw [(hρ₃ u.1).2]; exact u.2
  obtain ⟨h1, h2⟩ := IsReduced.window _ (hρ₂ b).1 (hρ₃ u.1).1 hu
  exact ⟨h1, by rw [h2, (hρ₂ b).2, (hρ₃ u.1).2]⟩

variable (j hj ρ₂ ρ₃) in
/-- **The reduced words adapted to the window**: for a bottom loading `i` and `w` with
`w • i = midSeq j hj s t`, the word `midWordAt j ρ₂ ρ₃ s w`; otherwise `ρ₃ w`. -/
def midWord (i : Seq (stendhalWeight (ℓ + 2) (ν + ν₀))) (w : Perm (Fin M)) : List ℕ :=
  if h : w • i ∈ midSet j hj ν ν₀ then midWordAt j ρ₂ ρ₃ (exists_midSeq_of_mem h).choose w
  else ρ₃ w

theorem midWord_eq {i : Seq (stendhalWeight (ℓ + 2) (ν + ν₀))} {w : Perm (Fin M)}
    {s : Seq (stendhalWeight ℓ ν)} {t : Seq (stendhalWeight 2 ν₀)}
    (hi : w • i = midSeq j hj s t) : midWord j hj ρ₂ ρ₃ i w = midWordAt j ρ₂ ρ₃ s w := by
  have hm : w • i ∈ midSet j hj ν ν₀ := hi ▸ midSeq_mem_midSet s t
  simp only [midWord, hm, ↓reduceDIte]
  obtain ⟨t', ht'⟩ := (exists_midSeq_of_mem hm).choose_spec
  rw [(midSeq_injective (ht'.trans hi)).1]

theorem midWord_spec (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    (i : Seq (stendhalWeight (ℓ + 2) (ν + ν₀))) (w : Perm (Fin M)) :
    IsReduced M (midWord j hj ρ₂ ρ₃ i w) ∧ wordProd M (midWord j hj ρ₂ ρ₃ i w) = w := by
  unfold midWord
  split_ifs
  · exact midWordAt_spec hρ₂ hρ₃ _ w
  · exact hρ₃ w

end Words

section Index

variable (j hj ν ν₀) in
/-- **The generators of the corner at the window before `λ_{j+1}`**: a red-ordered loading `s`
of `λ`, a red-ordered loading `t` at the maximum, dots `d` on the black strands of `s` and a
window shuffle `u` for the window at `midPos j s`, such that the bottom `u⁻¹ (midSeq s t)` is
red-ordered. -/
@[ext]
structure MidGen where
  /-- The loading of `λ` at the top. -/
  s : Seq (stendhalWeight ℓ ν)
  /-- The loading at the maximum. -/
  t : Seq (stendhalWeight 2 ν₀)
  /-- The dots on the strands of `λ`, at the top. -/
  d : Fin m →₀ ℕ
  /-- The window shuffle. -/
  u : Perm (Fin M)
  hs : IsRedOrdered s
  ht : IsRedOrdered t
  hd : ∀ a ∈ d.support, (s.lbl a).isLeft
  hu : IsWinShuffle (midPos_add_N_le j ν₀ s) u
  hbot : IsRedOrdered (u⁻¹ • midSeq j hj s t)

/-- The bottom `u⁻¹ (midSeq s t)` of a generator. -/
def MidGen.bot (g : MidGen j hj ν ν₀) : Seq (stendhalWeight (ℓ + 2) (ν + ν₀)) :=
  g.u⁻¹ • midSeq j hj g.s g.t

omit [DecidableEq I] in
theorem MidGen.smul_bot (g : MidGen j hj ν ν₀) : g.u • g.bot = midSeq j hj g.s g.t := by
  rw [MidGen.bot, smul_inv_smul]

variable (ρ₂ : Perm (Fin (Multiset.card (stendhalWeight 2 ν₀))) → List ℕ)
  (ρ₃ : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀)))) → List ℕ)

variable (j hj ν) in
/-- **The pairs**: a generator and a term of the basis of `T̃^{(μ,μ*)}` with dots on top whose
bottom is the loading `t` of the generator. -/
abbrev MidPair : Type :=
  {p : MidGen j hj ν ν₀ × {y // IsTopTerm (ℓ := 2) (ν := ν₀) ρ₂ y} // p.2.1.1 = p.1.t}

variable {ρ₂ ρ₃}

/-- The index `(u⁻¹ (midSeq s t), b u, (d, d'))` of `T̃^{λ⁺}` attached to a pair. -/
def midPairRaw (p : MidPair j hj ν ρ₂) :
    Seq (stendhalWeight (ℓ + 2) (ν + ν₀)) × Perm (Fin M) × (Fin M →₀ ℕ) :=
  (p.1.1.bot, winPerm (midPos_add_N_le j ν₀ p.1.1.s) p.1.2.1.2.1 * p.1.1.u,
    midExp j ν₀ p.1.1.s (p.1.1.d, p.1.2.1.2.2))

omit [DecidableEq I] in
theorem midPairRaw_top (p : MidPair j hj ν ρ₂) :
    (midPairRaw p).2.1 • (midPairRaw p).1 =
      midSeq j hj p.1.1.s (p.1.2.1.2.1 • p.1.2.1.1) := by
  simp only [midPairRaw]
  rw [mul_smul, MidGen.smul_bot, winPerm_smul_midSeq, p.2]

variable (ρ₃) in
theorem isTopTermSeq_midPairRaw (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w) (p : MidPair j hj ν ρ₂) :
    IsTopTermSeq (midWord j hj ρ₂ ρ₃) (midPairRaw p) := by
  obtain ⟨⟨g, y⟩, hp⟩ := p
  have hy := y.2
  have htop : IsRedOrdered ((midPairRaw ⟨⟨g, y⟩, hp⟩).2.1 • (midPairRaw ⟨⟨g, y⟩, hp⟩).1) := by
    rw [midPairRaw_top, isRedOrdered_midSeq]
    exact ⟨g.hs, hy.2.1⟩
  refine ⟨g.hbot, htop, fun c hc => ?_, ?_⟩
  · rw [midPairRaw_top]
    obtain ⟨z, rfl⟩ := (midPosEquiv j ν₀ g.s).surjective c
    rcases z with a | b
    · have ha : a ∈ g.d.support := by
        rw [Finsupp.mem_support_iff] at hc ⊢
        have := midExp_outPos (j := j) (ν₀ := ν₀) g.s (g.d, y.1.2.2) a
        simp only [midPairRaw] at hc
        rw [show midPosEquiv j ν₀ g.s (.inl a) = outPos j ν₀ g.s a from rfl, this] at hc
        exact hc
      change ((midSeq j hj _ _).lbl (outPos j ν₀ g.s a)).isLeft
      rw [midSeq_lbl_outPos]
      simpa using g.hd a ha
    · have hb : b ∈ y.1.2.2.support := by
        rw [Finsupp.mem_support_iff] at hc ⊢
        simp only [midPairRaw] at hc
        rw [midPosEquiv_inr, midExp_winPos] at hc
        exact hc
      rw [midPosEquiv_inr]
      change ((midSeq j hj _ _).lbl _).isLeft
      rw [midSeq_lbl_winPos]
      simpa using hy.2.2.1 b hb
  · exact noRedCross_of_isRedOrdered (midWord_spec hρ₂ hρ₃ _ _).1 g.hbot
      (by rw [(midWord_spec hρ₂ hρ₃ _ _).2]; exact htop)

variable (ρ₃) in
/-- The index of `T̃^{λ⁺}` attached to a pair. -/
def midPairIdx (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w) (p : MidPair j hj ν ρ₂) :
    {b // IsTopTermSeq (midWord j hj ρ₂ ρ₃) b} :=
  ⟨midPairRaw p, isTopTermSeq_midPairRaw ρ₃ hρ₂ hρ₃ p⟩

theorem midPairRaw_injective :
    Function.Injective (midPairRaw (j := j) (hj := hj) (ν := ν) (ν₀ := ν₀) (ρ₂ := ρ₂)) := by
  rintro ⟨⟨⟨s, t, d, u, h1s, h1t, h1d, h1u, h1b⟩, ⟨⟨t₁, b, e⟩, hy⟩⟩, hp⟩
    ⟨⟨⟨s', t', d₁, u', h2s, h2t, h2d, h2u, h2b⟩, ⟨⟨t₁', b', e'⟩, hy'⟩⟩, hp'⟩ h
  have htop := congrArg (fun r : Seq (stendhalWeight (ℓ + 2) (ν + ν₀)) × Perm (Fin M) ×
    (Fin M →₀ ℕ) => r.2.1 • r.1) h
  rw [midPairRaw_top, midPairRaw_top] at htop
  obtain ⟨rfl, -⟩ := midSeq_injective htop
  simp only [midPairRaw, MidGen.bot, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨rfl, rfl⟩ := winPerm_mul_injective _ h1u h2u h2
  obtain ⟨-, rfl⟩ := midSeq_injective (smul_left_cancel _ h1)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj ((midExp j ν₀ s).injective h3)
  have ht : t₁ = t₁' := hp.trans hp'.symm
  subst ht
  rfl

theorem midPairIdx_injective (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w) :
    Function.Injective (midPairIdx (j := j) (hj := hj) (ν := ν) ρ₃ hρ₂ hρ₃) :=
  fun _ _ h => midPairRaw_injective (congrArg Subtype.val h)

theorem midPairIdx_top_mem (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w) (p : MidPair j hj ν ρ₂) :
    (midPairIdx ρ₃ hρ₂ hρ₃ p).1.2.1 • (midPairIdx ρ₃ hρ₂ hρ₃ p).1.1 ∈ midSet j hj ν ν₀ := by
  change (midPairRaw p).2.1 • (midPairRaw p).1 ∈ _
  rw [midPairRaw_top]
  exact midSeq_mem_midSet _ _

variable (ρ₂ ρ₃) in
/-- **Every term of the basis of `T̃^{λ⁺}` whose top lies in `midSet` comes from a pair.** -/
theorem exists_midPairIdx (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    (b : {b // IsTopTermSeq (midWord j hj ρ₂ ρ₃) b}) (hb : b.1.2.1 • b.1.1 ∈ midSet j hj ν ν₀) :
    ∃ p, midPairIdx ρ₃ hρ₂ hρ₃ p = b := by
  obtain ⟨⟨i, w, dd⟩, hi, htop, hdot, hcross⟩ := b
  obtain ⟨s, t', hst⟩ := exists_midSeq_of_mem hb
  obtain ⟨⟨bb, u⟩, rfl⟩ := (winEquiv (midPos_add_N_le j ν₀ s)).surjective w
  obtain ⟨⟨d, d'⟩, rfl⟩ := (midExp j ν₀ s).surjective dd
  simp only [winEquiv_apply] at hst htop hdot hcross ⊢
  have hmid : u.1 • i = midSeq j hj s (bb⁻¹ • t') := by
    rw [← winPerm_smul_midSeq, hst, ← mul_smul, ← mul_assoc, winPerm_mul, inv_mul_cancel,
      winPerm_one, one_mul]
  rw [midWord_eq hst.symm, midWordAt_winPerm_mul] at hcross
  have hmidRO : IsRedOrdered (u.1 • i) := by
    have h3 := ((SplitRed.noRedCross_append _ _ _).1 hcross).2
    have := isRedOrdered_wordProd_smul hi (hρ₃ u.1).1.1 h3
    rwa [(hρ₃ u.1).2] at this
  rw [hmid, isRedOrdered_midSeq] at hmidRO
  rw [← hst, isRedOrdered_midSeq] at htop
  let g : MidGen j hj ν ν₀ :=
    { s := s, t := bb⁻¹ • t', d := d, u := u.1, hs := htop.1, ht := hmidRO.2
      hd := fun a ha => by
        have hc : outPos j ν₀ s a ∈ (midExp j ν₀ s (d, d')).support := by
          rw [Finsupp.mem_support_iff, midExp_outPos]; exact Finsupp.mem_support_iff.1 ha
        have := hdot _ hc
        rw [← hst] at this
        change ((midSeq j hj _ _).lbl _).isLeft at this
        rw [midSeq_lbl_outPos] at this
        simpa using this
      hu := u.2
      hbot := by rw [← hmid, inv_smul_smul]; exact hi }
  have hy : IsTopTerm (ℓ := 2) (ν := ν₀) ρ₂ (bb⁻¹ • t', bb, d') := by
    refine ⟨hmidRO.2, by simpa using htop.2, fun b' hb' => ?_, ?_⟩
    · have hc : winPos (midPos_add_N_le j ν₀ s) b' ∈ (midExp j ν₀ s (d, d')).support := by
        rw [Finsupp.mem_support_iff, midExp_winPos]; exact Finsupp.mem_support_iff.1 hb'
      have := hdot _ hc
      rw [← hst] at this
      change ((midSeq j hj _ _).lbl _).isLeft at this
      rw [midSeq_lbl_winPos] at this
      simpa using this
    · exact noRedCross_of_isRedOrdered (hρ₂ bb).1 hmidRO.2
        (by rw [(hρ₂ bb).2, smul_inv_smul]; exact htop.2)
  refine ⟨⟨(g, ⟨_, hy⟩), rfl⟩, Subtype.ext ?_⟩
  change (g.bot, _, _) = _
  simp only [MidGen.bot, g, Prod.mk.injEq, and_true]
  rw [← hmid, inv_smul_smul]

end Index

end Categorification.Stendhal.CupCap

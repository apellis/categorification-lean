/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapEndWords
import Categorification.WeightedKLR.RedStrands.BraidedIdentity
import Categorification.WeightedKLR.RedStrands.SplitRedWords

/-!
# Indices of the basis of `T̃^{λ⁺}` adapted to the two blocks at the right end

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17, in the case `j = ℓ`. Choose reduced words
`ρ₁`, `ρ₂`, `ρ₃` for the permutations of the strands of `λ`, of the strands at the maximum and of
all strands of `λ⁺`, and write a permutation of `λ⁺` as `w = (a × b) u` with `u` a shuffle. The
reduced word `ρ₁(a) (m + ρ₂(b)) ρ₃(u)` (`endWord`) gives a basis of `T̃^{λ⁺}` with dots on top
(`topBasis`), whose terms with top in the end block are indexed by pairs: a term `x` of the basis of
`T̃^λ`, a red-ordered loading `j` of the strands at the maximum and a shuffle `u` (the generator
`EndGen`), and a term of the basis of `T̃^{(μ,μ*)}` with bottom `j` (`EndPair`, `endPairIdx`).
This is the indexing of Webster's basis `B″` (the triples of (7.36)).

## Main definitions

* `endWord`: the reduced word adapted to the blocks.
* `endExp`: exponents of `λ⁺` split along the two blocks.
* `EndGen`, `EndPair`, `endPairIdx`: the indices.

## Main results

* `endPairIdx_injective`, `exists_endPairIdx`: the pairs index exactly the basis terms whose top
  lies in the end block.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA Equiv MvPolynomial

variable {I : Type} {ℓ : ℕ} {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "hM" => m_add_N_end (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)

section Words

variable (ρ₁ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ)
  (ρ₂ : Perm (Fin (Multiset.card (stendhalWeight 2 ν₀))) → List ℕ)
  (ρ₃ : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀)))) → List ℕ)

/-- The word `ρ₁(a) (m + ρ₂(b)) ρ₃(u)` attached to `w = (a × b) u`. -/
def endWord (w : Perm (Fin M)) : List ℕ :=
  ρ₁ ((parabolicEquiv hM).symm w).1 ++ shiftWord m (ρ₂ ((parabolicEquiv hM).symm w).2.1) ++
    ρ₃ ((parabolicEquiv hM).symm w).2.2.1

theorem endWord_blockPerm_mul (a : Perm (Fin m)) (b : Perm (Fin N)) (u : Shuffle hM) :
    endWord ρ₁ ρ₂ ρ₃ (blockPerm hM a b * u.1) = ρ₁ a ++ shiftWord m (ρ₂ b) ++ ρ₃ u.1 := by
  have : (parabolicEquiv hM).symm (blockPerm hM a b * u.1) = (a, b, u) :=
    (parabolicEquiv hM).symm_apply_apply (a, b, u)
  rw [endWord, this]

variable {ρ₁ ρ₂ ρ₃}

theorem endWord_spec (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w) (w : Perm (Fin M)) :
    IsReduced M (endWord ρ₁ ρ₂ ρ₃ w) ∧ wordProd M (endWord ρ₁ ρ₂ ρ₃ w) = w := by
  obtain ⟨⟨a, b, u⟩, rfl⟩ := (parabolicEquiv hM).surjective w
  rw [parabolicEquiv_apply, endWord_blockPerm_mul]
  have hu : IsShuffle hM (wordProd M (ρ₃ u.1)) := by rw [(hρ₃ u.1).2]; exact u.2
  obtain ⟨h1, h2⟩ := IsReduced.parabolic hM (hρ₁ a).1 (hρ₂ b).1 (hρ₃ u.1).1 hu
  exact ⟨h1, by rw [h2, (hρ₁ a).2, (hρ₂ b).2, (hρ₃ u.1).2]⟩

end Words

section Exponents

variable (ν ν₀) in
/-- Exponent vectors of `λ⁺` split along the two blocks. -/
def endExp : (Fin m →₀ ℕ) × (Fin N →₀ ℕ) ≃ (Fin M →₀ ℕ) :=
  Finsupp.sumFinsuppEquivProdFinsupp.symm.trans (Finsupp.domCongr (blockEquiv hM)).toEquiv

theorem blockEquiv_inl_end (a : Fin m) : blockEquiv hM (Sum.inl a) = posL ν₀ a := rfl

theorem blockEquiv_inr_end (b : Fin N) : blockEquiv hM (Sum.inr b) = posR ν b := rfl

theorem endExp_posL (d : (Fin m →₀ ℕ) × (Fin N →₀ ℕ)) (a : Fin m) :
    endExp ν ν₀ d (posL ν₀ a) = d.1 a := by
  rw [← blockEquiv_inl_end]
  simp [endExp]

theorem endExp_posR (d : (Fin m →₀ ℕ) × (Fin N →₀ ℕ)) (b : Fin N) :
    endExp ν ν₀ d (posR ν b) = d.2 b := by
  rw [← blockEquiv_inr_end]
  simp [endExp]

theorem posL_injective : Function.Injective (posL (I := I) (ℓ := ℓ) (ν := ν) ν₀) :=
  fun a a' h => Fin.ext (by simpa using congrArg Fin.val h)

theorem posR_injective : Function.Injective (posR (I := I) (ℓ := ℓ) (ν₀ := ν₀) ν) :=
  fun b b' h => Fin.ext (by simpa using congrArg Fin.val h)

theorem endExp_eq (d : (Fin m →₀ ℕ) × (Fin N →₀ ℕ)) :
    endExp ν ν₀ d = d.1.mapDomain (posL ν₀) + d.2.mapDomain (posR ν) := by
  ext c
  obtain ⟨x, rfl⟩ := (blockEquiv hM).surjective c
  rcases x with a | b
  · rw [blockEquiv_inl_end, endExp_posL, Finsupp.coe_add, Pi.add_apply,
      Finsupp.mapDomain_apply_of_injective posL_injective, Finsupp.mapDomain_of_notMem_range]
    · simp
    · rintro ⟨b, hb⟩
      have := congrArg Fin.val hb
      simp at this
      omega
  · rw [blockEquiv_inr_end, endExp_posR, Finsupp.coe_add, Pi.add_apply,
      Finsupp.mapDomain_apply_of_injective posR_injective, Finsupp.mapDomain_of_notMem_range]
    · simp
    · rintro ⟨a, ha⟩
      have := congrArg Fin.val ha
      simp at this
      omega

theorem monomial_endExp {k : Type*} [CommRing k] (d : (Fin m →₀ ℕ) × (Fin N →₀ ℕ)) :
    (monomial (endExp ν ν₀ d) 1 : MvPolynomial (Fin M) k) =
      rename (posL ν₀) (monomial d.1 1) * rename (posR ν) (monomial d.2 1) := by
  rw [rename_monomial, rename_monomial, monomial_mul_monomial, one_mul, endExp_eq]

end Exponents

section Index

variable (ρ₁ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ)
  (ρ₂ : Perm (Fin (Multiset.card (stendhalWeight 2 ν₀))) → List ℕ)
  (ρ₃ : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀)))) → List ℕ)

variable (ν₀) in
/-- **The generators**: a term `x` of the basis of `T̃^λ` with dots on top, a red-ordered loading
`j` of the strands at the maximum and a shuffle `u`, such that the bottom `u⁻¹ (i j)` (`i` the
bottom of `x`) is red-ordered. -/
abbrev EndGen : Type :=
  {g : {x // IsTopTerm (ℓ := ℓ) (ν := ν) ρ₁ x} × Seq (stendhalWeight 2 ν₀) × Shuffle hM //
    IsRedOrdered g.2.1 ∧ IsRedOrdered (g.2.2.1⁻¹ • endSeq g.1.1.1 g.2.1)}

variable {ρ₁}

/-- The bottom `u⁻¹ (i j)` of a generator. -/
def EndGen.bot (g : EndGen ν₀ ρ₁) : Seq (stendhalWeight (ℓ + 2) (ν + ν₀)) :=
  g.1.2.2.1⁻¹ • endSeq g.1.1.1.1 g.1.2.1

variable (ρ₁) in
/-- **The pairs**: a generator and a term of the basis of `T̃^{(μ,μ*)}` with dots on top whose
bottom is the loading `j` of the generator. -/
abbrev EndPair : Type :=
  {p : EndGen ν₀ ρ₁ × {y // IsTopTerm (ℓ := 2) (ν := ν₀) ρ₂ y} // p.2.1.1 = p.1.1.2.1}

variable {ρ₂ ρ₃}

/-- The index `(u⁻¹ (i j), (a × b) u, (d, d'))` of `T̃^{λ⁺}` attached to a pair. -/
def endPairRaw (p : EndPair ρ₁ ρ₂) :
    Seq (stendhalWeight (ℓ + 2) (ν + ν₀)) × Perm (Fin M) × (Fin M →₀ ℕ) :=
  (p.1.1.bot, blockPerm hM p.1.1.1.1.1.2.1 p.1.2.1.2.1 * p.1.1.1.2.2.1,
    endExp ν ν₀ (p.1.1.1.1.1.2.2, p.1.2.1.2.2))

theorem smul_bot (g : EndGen ν₀ ρ₁) : g.1.2.2.1 • g.bot = endSeq g.1.1.1.1 g.1.2.1 := by
  rw [EndGen.bot, smul_inv_smul]

theorem endPairRaw_top (p : EndPair ρ₁ ρ₂) :
    (endPairRaw p).2.1 • (endPairRaw p).1 =
      endSeq (p.1.1.1.1.1.2.1 • p.1.1.1.1.1.1) (p.1.2.1.2.1 • p.1.2.1.1) := by
  simp only [endPairRaw]
  rw [mul_smul, smul_bot, blockPerm_smul_endSeq, p.2]

variable (ρ₁ ρ₂ ρ₃) in
theorem isTopTerm_endPairRaw (hρ : ∀ w, IsReduced M (endWord ρ₁ ρ₂ ρ₃ w) ∧
      wordProd M (endWord ρ₁ ρ₂ ρ₃ w) = w) (p : EndPair ρ₁ ρ₂) :
    IsTopTerm (endWord ρ₁ ρ₂ ρ₃) (endPairRaw p) := by
  have hM' := card_plus_end (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  obtain ⟨⟨g, y⟩, hp⟩ := p
  have hx := g.1.1.2
  have hy := y.2
  have htop : IsRedOrdered ((endPairRaw ⟨⟨g, y⟩, hp⟩).2.1 • (endPairRaw ⟨⟨g, y⟩, hp⟩).1) := by
    rw [endPairRaw_top, isRedOrdered_endSeq]
    exact ⟨hx.2.1, hy.2.1⟩
  refine ⟨g.2.2, htop, fun c hc => ?_, ?_⟩
  · rw [endPairRaw_top]
    obtain ⟨z, rfl⟩ := (blockEquiv hM).surjective c
    rcases z with a | b
    · rw [blockEquiv_inl_end] at hc ⊢
      have ha : a ∈ g.1.1.1.2.2.support := by
        rw [Finsupp.mem_support_iff] at hc ⊢
        simpa [endPairRaw, endExp_posL] using hc
      have := hx.2.2.1 a ha
      change ((endSeq _ _).lbl _).isLeft
      rw [endSeq_lbl_lt _ _ _ (by simp)]
      simpa using this
    · rw [blockEquiv_inr_end] at hc ⊢
      have hb : b ∈ y.1.2.2.support := by
        rw [Finsupp.mem_support_iff] at hc ⊢
        simpa [endPairRaw, endExp_posR] using hc
      have := hy.2.2.1 b hb
      change ((endSeq _ _).lbl _).isLeft
      rw [endSeq_lbl_ge _ _ _ (by simp)]
      simpa using this
  · exact noRedCross_of_isRedOrdered (hρ _).1 g.2.2 (by rw [(hρ _).2]; exact htop)

variable (ρ₁ ρ₂ ρ₃) in
/-- The index of `T̃^{λ⁺}` attached to a pair. -/
def endPairIdx (hρ : ∀ w, IsReduced M (endWord ρ₁ ρ₂ ρ₃ w) ∧ wordProd M (endWord ρ₁ ρ₂ ρ₃ w) = w)
    (p : EndPair ρ₁ ρ₂) : {b // IsTopTerm (endWord ρ₁ ρ₂ ρ₃) b} :=
  ⟨endPairRaw p, isTopTerm_endPairRaw ρ₁ ρ₂ ρ₃ hρ p⟩

theorem endPairRaw_injective : Function.Injective (endPairRaw (ρ₁ := ρ₁) (ρ₂ := ρ₂)) := by
  rintro ⟨⟨g, y⟩, hp⟩ ⟨⟨g', y'⟩, hp'⟩ h
  simp only [endPairRaw, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨ha, hb, hu⟩ := blockPerm_mul_injective hM g.1.2.2.2 g'.1.2.2.2 h2
  obtain ⟨hd, hd'⟩ := Prod.mk.inj ((endExp ν ν₀).injective h3)
  have hbot : endSeq g.1.1.1.1 g.1.2.1 = endSeq g'.1.1.1.1 g'.1.2.1 := by
    rw [← smul_bot, ← smul_bot, h1, hu]
  obtain ⟨hi, hj⟩ := endSeq_injective hbot
  have hg : g = g' := by
    obtain ⟨⟨⟨⟨i, a, d⟩, _⟩, j, u⟩, _⟩ := g
    obtain ⟨⟨⟨⟨i', a', d'⟩, _⟩, j', u'⟩, _⟩ := g'
    simp only at ha hb hu hd hd' hi hj
    subst ha hd hi hj
    obtain rfl : u = u' := Subtype.ext hu
    rfl
  subst hg
  have hy : y = y' := by
    obtain ⟨⟨j, b, d⟩, _⟩ := y
    obtain ⟨⟨j', b', d'⟩, _⟩ := y'
    simp only at hp hp' hb hd'
    subst hb hd'
    obtain rfl : j = j' := hp.trans hp'.symm
    rfl
  subst hy
  rfl

theorem endPairIdx_injective (hρ : ∀ w, IsReduced M (endWord ρ₁ ρ₂ ρ₃ w) ∧
      wordProd M (endWord ρ₁ ρ₂ ρ₃ w) = w) :
    Function.Injective (endPairIdx ρ₁ ρ₂ ρ₃ hρ) :=
  fun _ _ h => endPairRaw_injective (congrArg Subtype.val h)

theorem endPairIdx_top_mem [DecidableEq I] (hρ : ∀ w, IsReduced M (endWord ρ₁ ρ₂ ρ₃ w) ∧
      wordProd M (endWord ρ₁ ρ₂ ρ₃ w) = w) (p : EndPair ρ₁ ρ₂) :
    (endPairIdx ρ₁ ρ₂ ρ₃ hρ p).1.2.1 • (endPairIdx ρ₁ ρ₂ ρ₃ hρ p).1.1 ∈ endSet ν ν₀ := by
  change (endPairRaw p).2.1 • (endPairRaw p).1 ∈ _
  rw [endPairRaw_top]
  exact endSeq_mem_endSet _ _

variable (ρ₁ ρ₂ ρ₃) in
/-- **Every term of the basis of `T̃^{λ⁺}` whose top lies in the end block comes from a pair.** -/
theorem exists_endPairIdx [DecidableEq I] (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    (b : {b // IsTopTerm (endWord ρ₁ ρ₂ ρ₃) b}) (hb : b.1.2.1 • b.1.1 ∈ endSet ν ν₀) :
    ∃ p, endPairIdx ρ₁ ρ₂ ρ₃ (endWord_spec hρ₁ hρ₂ hρ₃) p = b := by
  have hM' := card_plus_end (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  obtain ⟨⟨i, w, d⟩, hi, htop, hdot, hcross⟩ := b
  obtain ⟨⟨a, bb, u⟩, rfl⟩ := (parabolicEquiv hM).surjective w
  obtain ⟨⟨d₁, d₂⟩, rfl⟩ := (endExp ν ν₀).surjective d
  obtain ⟨s, t, hst⟩ := exists_endSeq_of_mem hb
  simp only [parabolicEquiv_apply] at hst htop hdot hcross ⊢
  -- the middle loading `u • i`
  have hmid : u.1 • i = endSeq (a⁻¹ • s) (bb⁻¹ • t) := by
    rw [← blockPerm_smul_endSeq, hst, ← mul_smul, ← mul_assoc, blockPerm_mul, inv_mul_cancel,
      inv_mul_cancel, blockPerm_one, one_mul]
  rw [endWord_blockPerm_mul] at hcross
  have hmidRO : IsRedOrdered (u.1 • i) := by
    have h3 := ((SplitRed.noRedCross_append _ _ _).1 hcross).2
    have := isRedOrdered_wordProd_smul hi (hρ₃ u.1).1.1 h3
    rwa [(hρ₃ u.1).2] at this
  rw [hmid, isRedOrdered_endSeq] at hmidRO
  rw [← hst, isRedOrdered_endSeq] at htop
  have hx : IsTopTerm (ℓ := ℓ) (ν := ν) ρ₁ (a⁻¹ • s, a, d₁) := by
    refine ⟨hmidRO.1, by simpa using htop.1, fun a' ha' => ?_, ?_⟩
    · have hc : posL ν₀ a' ∈ (endExp ν ν₀ (d₁, d₂)).support := by
        rw [Finsupp.mem_support_iff, endExp_posL]; exact Finsupp.mem_support_iff.1 ha'
      have := hdot _ hc
      rw [← hst] at this
      change ((endSeq _ _).lbl _).isLeft at this
      rw [endSeq_lbl_lt _ _ _ (by simp)] at this
      simpa using this
    · exact noRedCross_of_isRedOrdered (hρ₁ a).1 hmidRO.1 (by rw [(hρ₁ a).2]; simpa using htop.1)
  have hy : IsTopTerm (ℓ := 2) (ν := ν₀) ρ₂ (bb⁻¹ • t, bb, d₂) := by
    refine ⟨hmidRO.2, by simpa using htop.2, fun b' hb' => ?_, ?_⟩
    · have hc : posR ν b' ∈ (endExp ν ν₀ (d₁, d₂)).support := by
        rw [Finsupp.mem_support_iff, endExp_posR]; exact Finsupp.mem_support_iff.1 hb'
      have := hdot _ hc
      rw [← hst] at this
      change ((endSeq _ _).lbl _).isLeft at this
      rw [endSeq_lbl_ge _ _ _ (by simp)] at this
      simpa using this
    · exact noRedCross_of_isRedOrdered (hρ₂ bb).1 hmidRO.2 (by rw [(hρ₂ bb).2]; simpa using htop.2)
  let g : EndGen ν₀ ρ₁ := ⟨(⟨_, hx⟩, bb⁻¹ • t, u), hmidRO.2, by
    change IsRedOrdered (u.1⁻¹ • endSeq (a⁻¹ • s) (bb⁻¹ • t))
    rw [← hmid, inv_smul_smul]; exact hi⟩
  refine ⟨⟨(g, ⟨_, hy⟩), rfl⟩, Subtype.ext ?_⟩
  change (g.bot, _, _) = _
  simp only [EndGen.bot, g, Prod.mk.injEq, and_true]
  rw [← hmid, inv_smul_smul]

end Index

end Categorification.Stendhal.CupCap

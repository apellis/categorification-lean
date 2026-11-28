/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FrontWindowFactor

/-!
# Indices of the basis of `T̃^{λ⁺}` adapted to the two blocks with the maximum at the left end

Webster, arXiv:1309.3796v3, proof of Lemma 7.19, the block decomposition (B3) with the black
block at the right end, steps 1 and 2 of the paper argument. Choose reduced words `ρ₁`, `ρ₂`,
`ρ₃` for the permutations of the strands of `λ`, of the strands at the maximum and of all strands
of `λ⁺`, and write a permutation of `λ⁺` as `w = (b × a) u` with `b` permuting the first `N`
strands, `a` the last `m` and `u` a shuffle. The reduced word `ρ₂(b) (N + ρ₁(a)) ρ₃(u)`
(`frontWord`) gives a basis of `T̃^{λ⁺}` with dots on top (`topBasis`), whose terms with top in
`frontSet` are indexed by triples (`FrontTriple`, `frontIdx`): a base generator `c = (i, j, u)`
of red-ordered loadings `i` of `λ` and `j` of the strands at the maximum and a shuffle `u` with
red-ordered bottom `u⁻¹ (j i)` (`FrontGen`), a basis term `y` of `T̃^{(μ,μ*)}` with bottom `j`
and a basis term `x` of `T̃^λ` with bottom `i`.

## Main definitions

* `CupCap.frontWord`: the reduced word adapted to the blocks.
* `CupCap.frontExp`: exponents of `λ⁺` split along the two blocks.
* `CupCap.FrontGen`, `CupCap.FrontTriple`, `CupCap.frontIdx`: the indices.

## Main results

* `CupCap.frontIdx_injective`, `CupCap.exists_frontIdx`: the triples index exactly the basis
  terms whose top lies in `frontSet`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA Equiv MvPolynomial

variable {I : Type} {ℓ : ℕ} {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "hF" => N_add_m_front (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)

section Words

variable (ρ₁ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ)
  (ρ₂ : Perm (Fin (Multiset.card (stendhalWeight 2 ν₀))) → List ℕ)
  (ρ₃ : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀)))) → List ℕ)

/-- The word `ρ₂(b) (N + ρ₁(a)) ρ₃(u)` attached to `w = (b × a) u`. -/
def frontWord (w : Perm (Fin M)) : List ℕ :=
  ρ₂ ((parabolicEquiv hF).symm w).1 ++ shiftWord N (ρ₁ ((parabolicEquiv hF).symm w).2.1) ++
    ρ₃ ((parabolicEquiv hF).symm w).2.2.1

theorem frontWord_blockPerm_mul (b : Perm (Fin N)) (a : Perm (Fin m)) (u : Shuffle hF) :
    frontWord ρ₁ ρ₂ ρ₃ (blockPerm hF b a * u.1) = ρ₂ b ++ shiftWord N (ρ₁ a) ++ ρ₃ u.1 := by
  have : (parabolicEquiv hF).symm (blockPerm hF b a * u.1) = (b, a, u) :=
    (parabolicEquiv hF).symm_apply_apply (b, a, u)
  rw [frontWord, this]

variable {ρ₁ ρ₂ ρ₃}

theorem frontWord_spec (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w) (w : Perm (Fin M)) :
    IsReduced M (frontWord ρ₁ ρ₂ ρ₃ w) ∧ wordProd M (frontWord ρ₁ ρ₂ ρ₃ w) = w := by
  obtain ⟨⟨b, a, u⟩, rfl⟩ := (parabolicEquiv hF).surjective w
  rw [parabolicEquiv_apply, frontWord_blockPerm_mul]
  have hu : IsShuffle hF (wordProd M (ρ₃ u.1)) := by rw [(hρ₃ u.1).2]; exact u.2
  obtain ⟨h1, h2⟩ := IsReduced.parabolic hF (hρ₂ b).1 (hρ₁ a).1 (hρ₃ u.1).1 hu
  exact ⟨h1, by rw [h2, (hρ₂ b).2, (hρ₁ a).2, (hρ₃ u.1).2]⟩

end Words

section Exponents

variable (ν ν₀) in
/-- Exponent vectors of `λ⁺` split along the two blocks. -/
def frontExp : (Fin N →₀ ℕ) × (Fin m →₀ ℕ) ≃ (Fin M →₀ ℕ) :=
  Finsupp.sumFinsuppEquivProdFinsupp.symm.trans (Finsupp.domCongr (blockEquiv hF)).toEquiv

theorem blockEquiv_inl_front (b : Fin N) : blockEquiv hF (Sum.inl b) = frontPos ν b := rfl

theorem blockEquiv_inr_front (a : Fin m) : blockEquiv hF (Sum.inr a) = suffixPos ν₀ a := rfl

theorem frontExp_frontPos (d : (Fin N →₀ ℕ) × (Fin m →₀ ℕ)) (b : Fin N) :
    frontExp ν ν₀ d (frontPos ν b) = d.1 b := by
  rw [← blockEquiv_inl_front]
  simp [frontExp]

theorem frontExp_suffixPos (d : (Fin N →₀ ℕ) × (Fin m →₀ ℕ)) (a : Fin m) :
    frontExp ν ν₀ d (suffixPos ν₀ a) = d.2 a := by
  rw [← blockEquiv_inr_front]
  simp [frontExp]

theorem frontPos_injective : Function.Injective (frontPos (I := I) (ℓ := ℓ) (ν₀ := ν₀) ν) :=
  fun a a' h => Fin.ext (by simpa using congrArg Fin.val h)

theorem suffixPos_injective : Function.Injective (suffixPos (I := I) (ℓ := ℓ) (ν := ν) ν₀) :=
  fun b b' h => Fin.ext (by simpa using congrArg Fin.val h)

theorem frontExp_eq (d : (Fin N →₀ ℕ) × (Fin m →₀ ℕ)) :
    frontExp ν ν₀ d = d.1.mapDomain (frontPos ν) + d.2.mapDomain (suffixPos ν₀) := by
  ext c
  obtain ⟨x, rfl⟩ := (blockEquiv hF).surjective c
  rcases x with b | a
  · rw [blockEquiv_inl_front, frontExp_frontPos, Finsupp.coe_add, Pi.add_apply,
      Finsupp.mapDomain_apply_of_injective frontPos_injective, Finsupp.mapDomain_of_notMem_range]
    · simp
    · rintro ⟨a, ha⟩
      have := congrArg Fin.val ha
      simp at this
      omega
  · rw [blockEquiv_inr_front, frontExp_suffixPos, Finsupp.coe_add, Pi.add_apply,
      Finsupp.mapDomain_apply_of_injective suffixPos_injective, Finsupp.mapDomain_of_notMem_range]
    · simp
    · rintro ⟨b, hb⟩
      have := congrArg Fin.val hb
      simp at this
      omega

theorem monomial_frontExp {k : Type*} [CommRing k] (d : (Fin N →₀ ℕ) × (Fin m →₀ ℕ)) :
    (monomial (frontExp ν ν₀ d) 1 : MvPolynomial (Fin M) k) =
      rename (frontPos ν) (monomial d.1 1) * rename (suffixPos ν₀) (monomial d.2 1) := by
  rw [rename_monomial, rename_monomial, monomial_mul_monomial, one_mul, frontExp_eq]

end Exponents

section Index

variable (ρ₁ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ)
  (ρ₂ : Perm (Fin (Multiset.card (stendhalWeight 2 ν₀))) → List ℕ)
  (ρ₃ : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀)))) → List ℕ)

variable (ℓ ν ν₀) in
/-- **The base generators**: red-ordered loadings `i` of `λ` and `j` of the strands at the maximum
and a shuffle `u`, such that the bottom `u⁻¹ (j i)` is red-ordered. -/
abbrev FrontGen : Type :=
  {c : Seq (stendhalWeight ℓ ν) × Seq (stendhalWeight 2 ν₀) × Shuffle hF //
    IsRedOrdered c.1 ∧ IsRedOrdered c.2.1 ∧ IsRedOrdered (c.2.2.1⁻¹ • frontSeq c.1 c.2.1)}

/-- The bottom `u⁻¹ (j i)` of a base generator. -/
def FrontGen.bot (c : FrontGen ℓ ν ν₀) : Seq (stendhalWeight (ℓ + 2) (ν + ν₀)) :=
  c.1.2.2.1⁻¹ • frontSeq c.1.1 c.1.2.1

/-- **The triples**: a base generator `c = (i, j, u)`, a basis term `y` of `T̃^{(μ,μ*)}` with
bottom `j` and a basis term `x` of `T̃^λ` with bottom `i`. -/
abbrev FrontTriple : Type :=
  {p : FrontGen ℓ ν ν₀ × {y // IsTopTerm (ℓ := 2) (ν := ν₀) ρ₂ y} ×
      {x // IsTopTerm (ℓ := ℓ) (ν := ν) ρ₁ x} //
    p.2.1.1.1 = p.1.1.2.1 ∧ p.2.2.1.1 = p.1.1.1}

variable {ρ₁ ρ₂ ρ₃}

/-- The index `(u⁻¹ (j i), (b × a) u, (d, d'))` of `T̃^{λ⁺}` attached to a triple. -/
def frontRaw (p : FrontTriple ρ₁ ρ₂) :
    Seq (stendhalWeight (ℓ + 2) (ν + ν₀)) × Perm (Fin M) × (Fin M →₀ ℕ) :=
  (p.1.1.bot, blockPerm hF p.1.2.1.1.2.1 p.1.2.2.1.2.1 * p.1.1.1.2.2.1,
    frontExp ν ν₀ (p.1.2.1.1.2.2, p.1.2.2.1.2.2))

theorem smul_frontBot (c : FrontGen ℓ ν ν₀) : c.1.2.2.1 • c.bot = frontSeq c.1.1 c.1.2.1 := by
  rw [FrontGen.bot, smul_inv_smul]

theorem frontRaw_top (p : FrontTriple ρ₁ ρ₂) :
    (frontRaw p).2.1 • (frontRaw p).1 =
      frontSeq (p.1.2.2.1.2.1 • p.1.2.2.1.1) (p.1.2.1.1.2.1 • p.1.2.1.1.1) := by
  simp only [frontRaw]
  rw [mul_smul, smul_frontBot, blockPerm_smul_frontSeq, p.2.1, p.2.2]

variable (ρ₁ ρ₂ ρ₃) in
theorem isTopTerm_frontRaw (hρ : ∀ w, IsReduced M (frontWord ρ₁ ρ₂ ρ₃ w) ∧
      wordProd M (frontWord ρ₁ ρ₂ ρ₃ w) = w) (p : FrontTriple ρ₁ ρ₂) :
    IsTopTerm (frontWord ρ₁ ρ₂ ρ₃) (frontRaw p) := by
  obtain ⟨⟨c, y, x⟩, hp⟩ := p
  have hx := x.2
  have hy := y.2
  have htop : IsRedOrdered ((frontRaw ⟨⟨c, y, x⟩, hp⟩).2.1 • (frontRaw ⟨⟨c, y, x⟩, hp⟩).1) := by
    rw [frontRaw_top, isRedOrdered_frontSeq]
    exact ⟨hx.2.1, hy.2.1⟩
  refine ⟨c.2.2.2, htop, fun z hz => ?_, ?_⟩
  · rw [frontRaw_top]
    obtain ⟨w, rfl⟩ := (blockEquiv hF).surjective z
    rcases w with b | a
    · rw [blockEquiv_inl_front] at hz ⊢
      have hb : b ∈ y.1.2.2.support := by
        rw [Finsupp.mem_support_iff] at hz ⊢
        simpa [frontRaw, frontExp_frontPos] using hz
      have := hy.2.2.1 b hb
      change ((frontSeq _ _).lbl _).isLeft
      rw [frontSeq_lbl_lt _ _ _ (by simp)]
      simpa using this
    · rw [blockEquiv_inr_front] at hz ⊢
      have ha : a ∈ x.1.2.2.support := by
        rw [Finsupp.mem_support_iff] at hz ⊢
        simpa [frontRaw, frontExp_suffixPos] using hz
      have := hx.2.2.1 a ha
      change ((frontSeq _ _).lbl _).isLeft
      rw [frontSeq_lbl_ge _ _ _ (by simp)]
      simpa using this
  · exact noRedCross_of_isRedOrdered (hρ _).1 c.2.2.2 (by rw [(hρ _).2]; exact htop)

variable (ρ₁ ρ₂ ρ₃) in
/-- The index of `T̃^{λ⁺}` attached to a triple. -/
def frontIdx (hρ : ∀ w, IsReduced M (frontWord ρ₁ ρ₂ ρ₃ w) ∧ wordProd M (frontWord ρ₁ ρ₂ ρ₃ w) = w)
    (p : FrontTriple ρ₁ ρ₂) : {b // IsTopTerm (frontWord ρ₁ ρ₂ ρ₃) b} :=
  ⟨frontRaw p, isTopTerm_frontRaw ρ₁ ρ₂ ρ₃ hρ p⟩

theorem frontRaw_injective : Function.Injective (frontRaw (ρ₁ := ρ₁) (ρ₂ := ρ₂)) := by
  rintro ⟨⟨c, y, x⟩, hp⟩ ⟨⟨c', y', x'⟩, hp'⟩ h
  simp only [frontRaw, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨hb, ha, hu⟩ := blockPerm_mul_injective hF c.1.2.2.2 c'.1.2.2.2 h2
  obtain ⟨hd, hd'⟩ := Prod.mk.inj ((frontExp ν ν₀).injective h3)
  have hbot : frontSeq c.1.1 c.1.2.1 = frontSeq c'.1.1 c'.1.2.1 := by
    rw [← smul_frontBot, ← smul_frontBot, h1, hu]
  obtain ⟨hi, hj⟩ := frontSeq_injective hbot
  have hc : c = c' := by
    obtain ⟨⟨i, j, u⟩, _⟩ := c
    obtain ⟨⟨i', j', u'⟩, _⟩ := c'
    simp only at hu hi hj
    subst hi hj
    obtain rfl : u = u' := Subtype.ext hu
    rfl
  subst hc
  have hy : y = y' := by
    obtain ⟨⟨j, b, d⟩, _⟩ := y
    obtain ⟨⟨j', b', d'⟩, _⟩ := y'
    simp only at hp hp' hb hd
    subst hb hd
    obtain rfl : j = j' := hp.1.trans hp'.1.symm
    rfl
  have hx : x = x' := by
    obtain ⟨⟨i, a, d⟩, _⟩ := x
    obtain ⟨⟨i', a', d'⟩, _⟩ := x'
    simp only at hp hp' ha hd'
    subst ha hd'
    obtain rfl : i = i' := hp.2.trans hp'.2.symm
    rfl
  subst hy hx
  rfl

theorem frontIdx_injective (hρ : ∀ w, IsReduced M (frontWord ρ₁ ρ₂ ρ₃ w) ∧
      wordProd M (frontWord ρ₁ ρ₂ ρ₃ w) = w) :
    Function.Injective (frontIdx ρ₁ ρ₂ ρ₃ hρ) :=
  fun _ _ h => frontRaw_injective (congrArg Subtype.val h)

theorem frontIdx_top_mem [DecidableEq I] (hρ : ∀ w, IsReduced M (frontWord ρ₁ ρ₂ ρ₃ w) ∧
      wordProd M (frontWord ρ₁ ρ₂ ρ₃ w) = w) (p : FrontTriple ρ₁ ρ₂) :
    (frontIdx ρ₁ ρ₂ ρ₃ hρ p).1.2.1 • (frontIdx ρ₁ ρ₂ ρ₃ hρ p).1.1 ∈ frontSet ν ν₀ := by
  change (frontRaw p).2.1 • (frontRaw p).1 ∈ _
  rw [frontRaw_top]
  exact frontSeq_mem_frontSet _ _

variable (ρ₁ ρ₂ ρ₃) in
/-- **Every term of the basis of `T̃^{λ⁺}` whose top lies in `frontSet` comes from a triple.** -/
theorem exists_frontIdx [DecidableEq I] (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w)
    (b : {b // IsTopTerm (frontWord ρ₁ ρ₂ ρ₃) b}) (hb : b.1.2.1 • b.1.1 ∈ frontSet ν ν₀) :
    ∃ p, frontIdx ρ₁ ρ₂ ρ₃ (frontWord_spec hρ₁ hρ₂ hρ₃) p = b := by
  obtain ⟨⟨i, w, d⟩, hi, htop, hdot, hcross⟩ := b
  obtain ⟨⟨bb, a, u⟩, rfl⟩ := (parabolicEquiv hF).surjective w
  obtain ⟨⟨d₁, d₂⟩, rfl⟩ := (frontExp ν ν₀).surjective d
  obtain ⟨s, t, hst⟩ := exists_frontSeq_of_mem hb
  simp only [parabolicEquiv_apply] at hst htop hdot hcross ⊢
  -- the middle loading `u • i`
  have hmid : u.1 • i = frontSeq (a⁻¹ • s) (bb⁻¹ • t) := by
    rw [← blockPerm_smul_frontSeq, hst, ← mul_smul, ← mul_assoc, blockPerm_mul, inv_mul_cancel,
      inv_mul_cancel, blockPerm_one, one_mul]
  rw [frontWord_blockPerm_mul] at hcross
  have hmidRO : IsRedOrdered (u.1 • i) := by
    have h3 := ((SplitRed.noRedCross_append _ _ _).1 hcross).2
    have := isRedOrdered_wordProd_smul hi (hρ₃ u.1).1.1 h3
    rwa [(hρ₃ u.1).2] at this
  rw [hmid, isRedOrdered_frontSeq] at hmidRO
  rw [← hst, isRedOrdered_frontSeq] at htop
  have hx : IsTopTerm (ℓ := ℓ) (ν := ν) ρ₁ (a⁻¹ • s, a, d₂) := by
    refine ⟨hmidRO.1, by simpa using htop.1, fun a' ha' => ?_, ?_⟩
    · have hc : suffixPos ν₀ a' ∈ (frontExp ν ν₀ (d₁, d₂)).support := by
        rw [Finsupp.mem_support_iff, frontExp_suffixPos]; exact Finsupp.mem_support_iff.1 ha'
      have := hdot _ hc
      rw [← hst] at this
      change ((frontSeq _ _).lbl _).isLeft at this
      rw [frontSeq_lbl_ge _ _ _ (by simp)] at this
      simpa using this
    · exact noRedCross_of_isRedOrdered (hρ₁ a).1 hmidRO.1 (by rw [(hρ₁ a).2]; simpa using htop.1)
  have hy : IsTopTerm (ℓ := 2) (ν := ν₀) ρ₂ (bb⁻¹ • t, bb, d₁) := by
    refine ⟨hmidRO.2, by simpa using htop.2, fun b' hb' => ?_, ?_⟩
    · have hc : frontPos ν b' ∈ (frontExp ν ν₀ (d₁, d₂)).support := by
        rw [Finsupp.mem_support_iff, frontExp_frontPos]; exact Finsupp.mem_support_iff.1 hb'
      have := hdot _ hc
      rw [← hst] at this
      change ((frontSeq _ _).lbl _).isLeft at this
      rw [frontSeq_lbl_lt _ _ _ (by simp)] at this
      simpa using this
    · exact noRedCross_of_isRedOrdered (hρ₂ bb).1 hmidRO.2 (by rw [(hρ₂ bb).2]; simpa using htop.2)
  let c : FrontGen ℓ ν ν₀ := ⟨(a⁻¹ • s, bb⁻¹ • t, u), hmidRO.1, hmidRO.2, by
    change IsRedOrdered (u.1⁻¹ • frontSeq (a⁻¹ • s) (bb⁻¹ • t))
    rw [← hmid, inv_smul_smul]; exact hi⟩
  refine ⟨⟨(c, ⟨_, hy⟩, ⟨_, hx⟩), rfl, rfl⟩, Subtype.ext ?_⟩
  change (c.bot, _, _) = _
  simp only [FrontGen.bot, c, Prod.mk.injEq, and_true]
  rw [← hmid, inv_smul_smul]

end Index

end Categorification.Stendhal.CupCap

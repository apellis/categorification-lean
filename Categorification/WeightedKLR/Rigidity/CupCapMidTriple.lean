/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidCornerIndex

/-!
# Webster's triples for the cap after `λ_j`

Webster, arXiv:1309.3796v3, §7.3, Lemma 7.17, for the cap after the red strand `λ_j`. The set
`B″` is indexed by triples: an element `b` of the basis `B` of `T̃^λ`, an element `b′` of a basis
`B′` of `L`, and a shuffle of the bottom of `b′` with the black block of the bottom of `b`
between `λ_j` and `λ_{j+1}`. Here `b` is a term `x^d ψ_w e(i)` of the basis of Proposition 4.16
with dots on top (bottom `i`, top `w • i`), recorded by `(i, w, d)`; its word plays no role,
since a reduced word between red-ordered loadings never crosses two red strands. The bottom of
`b′` is a loading `t` at the maximum, with `μ` first and `μ*` last (`IsCapGood`).

A shuffle of `t` with the `j`-th black block of `i` is recorded as the positions of all strands
at the bottom of `λ⁺` (`IsBlockShuffle`): a bijection `Fin m ⊕ Fin N ≃ Fin M`, increasing on the
strands of `i` and on those of `t`, with the red strands `λ_1, …, λ_j` left of all strands of `t`
and `λ_{j+1}, …, λ_ℓ` right of them. The strands of `t` thus lie among the strands of the black
block between `λ_j` and `λ_{j+1}`, and the other strands of `i` keep their places.

The triples are in bijection with the generators `(s, t, d, u)` of the corner of the maximum
(`MidGen`) whose loading `t` is cap-good (`midTripleEquiv`): `s = w • i`, and the window shuffle
`u` sends the bottom position of the strand `a` of `i` to the top position of the strand `w a`
of `s`, and the bottom position of the strand `q` of `t` to the window.

## Main definitions

* `CupCap.IsBlockShuffle`: a shuffle of the strands at the maximum with the black block.
* `CupCap.MidTriple`: Webster's triples, without the element of `B′`.
* `CupCap.midTripleEquiv`: the bijection with the cap-good generators.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA Equiv

variable {I : Type} {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ} {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))

section Red

theorem oldRed_val_ite (r : Fin ℓ) :
    (oldRed j hj r).val = if r.val < j then r.val else r.val + 2 :=
  insertPos_inl_val _ r

theorem oldColour_eq_inr {c : I ⊕ Fin ℓ} {r : Fin (ℓ + 2)} (h : oldColour j hj c = .inr r) :
    ∃ r₀, c = .inr r₀ ∧ oldRed j hj r₀ = r := by
  rcases c with c | c
  · simp at h
  · exact ⟨c, rfl, by simpa using h⟩

end Red

section Shuffle

variable (j ν₀) in
/-- **A shuffle of the strands at the maximum with the `j`-th black block of `i`**, recorded as
the bottom positions of all strands of `λ⁺`: increasing on the strands of `i` and on those at the
maximum, with the red strands `λ_1, …, λ_j` of `i` left of every strand at the maximum and the
others right of them. -/
def IsBlockShuffle (i : Seq (stendhalWeight ℓ ν)) (ε : Fin m ⊕ Fin N ≃ Fin M) : Prop :=
  StrictMono (fun a => ε (.inl a)) ∧ StrictMono (fun q => ε (.inr q)) ∧
    ∀ a q (r : Fin ℓ), i.lbl a = .inr r → (r.val < j ↔ ε (.inl a) < ε (.inr q))

/-- A loading of `λ⁺` whose strands are those of a red-ordered `i` and a red-ordered `t`, placed
by a shuffle with the `j`-th black block, is red-ordered. -/
theorem isRedOrdered_of_isBlockShuffle {β : Seq (stendhalWeight (ℓ + 2) (ν + ν₀))}
    {i : Seq (stendhalWeight ℓ ν)} {t : Seq (stendhalWeight 2 ν₀)} {ε : Fin m ⊕ Fin N ≃ Fin M}
    (hε : IsBlockShuffle j ν₀ i ε) (hi : IsRedOrdered i) (ht : IsRedOrdered t)
    (h₁ : ∀ a, β.lbl (ε (.inl a)) = oldColour j hj (i.lbl a))
    (h₂ : ∀ q, β.lbl (ε (.inr q)) = cupColour j hj (t.lbl q)) : IsRedOrdered β := by
  obtain ⟨hl, hr, hb⟩ := hε
  intro x y r r' hxy hx hy
  obtain ⟨p, rfl⟩ := ε.surjective x
  obtain ⟨p', rfl⟩ := ε.surjective y
  rcases p with a | q <;> rcases p' with a' | q'
  · rw [h₁] at hx hy
    obtain ⟨r₀, h0, rfl⟩ := oldColour_eq_inr hx
    obtain ⟨r₁, h1, rfl⟩ := oldColour_eq_inr hy
    have hlt := hi a a' r₀ r₁ (hl.lt_iff_lt.1 hxy) h0 h1
    rw [Fin.lt_def, oldRed_val_ite, oldRed_val_ite]
    rw [Fin.lt_def] at hlt
    split_ifs <;> omega
  · rw [h₁] at hx
    rw [h₂] at hy
    obtain ⟨r₀, h0, rfl⟩ := oldColour_eq_inr hx
    rcases hc : t.lbl q' with c | c <;> rw [hc] at hy
    · simp at hy
    · simp only [Sum.map_inr, Sum.inr.injEq] at hy
      subst hy
      have := (hb a q' r₀ h0).2 hxy
      rw [Fin.lt_def, oldRed_val_ite, cupRed_val]
      split_ifs
      omega
  · rw [h₂] at hx
    rw [h₁] at hy
    obtain ⟨r₁, h1, rfl⟩ := oldColour_eq_inr hy
    rcases hc : t.lbl q with c | c <;> rw [hc] at hx
    · simp at hx
    · simp only [Sum.map_inr, Sum.inr.injEq] at hx
      subst hx
      have := mt (hb a' q r₁ h1).1 (not_lt.2 hxy.le)
      rw [Fin.lt_def, oldRed_val_ite, cupRed_val]
      have hc2 := c.isLt
      split_ifs
      omega
  · rw [h₂] at hx hy
    rcases hc : t.lbl q with c | c <;> rw [hc] at hx
    · simp at hx
    rcases hc' : t.lbl q' with c' | c' <;> rw [hc'] at hy
    · simp at hy
    simp only [Sum.map_inr, Sum.inr.injEq] at hx hy
    subst hx hy
    have := ht q q' c c' (hr.lt_iff_lt.1 hxy) hc hc'
    rw [Fin.lt_def, cupRed_val, cupRed_val]
    rw [Fin.lt_def] at this
    omega

/-- Conversely, if such a loading is red-ordered and `t` has `μ` first and `μ*` last, then `i` is
red-ordered and the strands at the maximum lie in the `j`-th black block of `i`. -/
theorem isBlockShuffle_of_isRedOrdered {β : Seq (stendhalWeight (ℓ + 2) (ν + ν₀))}
    {i : Seq (stendhalWeight ℓ ν)} {t : Seq (stendhalWeight 2 ν₀)} {ε : Fin m ⊕ Fin N ≃ Fin M}
    (hl : StrictMono (fun a => ε (.inl a))) (hr : StrictMono (fun q => ε (.inr q)))
    (hβ : IsRedOrdered β) (hcap : IsCapGood ν₀ t)
    (h₁ : ∀ a, β.lbl (ε (.inl a)) = oldColour j hj (i.lbl a))
    (h₂ : ∀ q, β.lbl (ε (.inr q)) = cupColour j hj (t.lbl q)) :
    IsRedOrdered i ∧ IsBlockShuffle j ν₀ i ε := by
  have hN := two_le_card_stendhalWeight ν₀
  refine ⟨fun a a' r r' haa' ha ha' => ?_, hl, hr, fun a q r ha => ?_⟩
  · have := hβ _ _ _ _ (hl haa') (by rw [h₁, ha]; rfl) (by rw [h₁, ha']; rfl)
    rw [Fin.lt_def, oldRed_val_ite, oldRed_val_ite] at this
    rw [Fin.lt_def]
    split_ifs at this <;> omega
  · have hne : ε (.inl a) ≠ ε (.inr q) := fun h => Sum.inl_ne_inr (ε.injective h)
    have hx : β.lbl (ε (.inl a)) = .inr (oldRed j hj r) := by rw [h₁, ha]; rfl
    constructor
    · intro hrj
      by_contra hc
      have hgt : ε (.inr q) < ε (.inl a) := lt_of_le_of_ne (not_lt.1 hc) hne.symm
      have h0 : ε (.inr ⟨0, by omega⟩) ≤ ε (.inr q) :=
        hr.monotone (Fin.mk_le_mk.2 (Nat.zero_le _))
      have := hβ _ _ _ _ (lt_of_le_of_lt h0 hgt)
        (by rw [h₂, hcap.1]; rfl) hx
      rw [Fin.lt_def, oldRed_val_ite, cupRed_val] at this
      simp only [hrj, ↓reduceIte] at this
      omega
    · intro hlt
      have h1 : ε (.inr q) ≤ ε (.inr ⟨N - 1, by omega⟩) :=
        hr.monotone (Fin.mk_le_mk.2 (by omega))
      have := hβ _ _ _ _ (lt_of_lt_of_le hlt h1) hx (by rw [h₂, hcap.2]; rfl)
      rw [Fin.lt_def, oldRed_val_ite, cupRed_val] at this
      split_ifs at this with h
      · exact h
      · simp at this; omega

end Shuffle

section Triples

variable (ℓ j ν ν₀) in
/-- **Webster's triples** (arXiv:1309.3796v3, §7.3, before Lemma 7.17), without the element of
`B′`: a term `x^d ψ_w e(i)` of the basis `B` of `T̃^λ` with dots on top (`i` and `w • i`
red-ordered, dots on black strands of `w • i`), a red-ordered loading `t` at the maximum with
`μ` first and `μ*` last (the bottom of an element of `B′`), and a shuffle of `t` with the `j`-th
black block of the bottom `i` of `b`. -/
structure MidTriple where
  /-- The bottom of `b`. -/
  i : Seq (stendhalWeight ℓ ν)
  /-- The permutation of `b`. -/
  w : Perm (Fin m)
  /-- The dots of `b`, at the top. -/
  d : Fin m →₀ ℕ
  /-- The bottom of `b′`. -/
  t : Seq (stendhalWeight 2 ν₀)
  /-- The shuffle of `t` with the `j`-th black block of `i`. -/
  ε : Fin m ⊕ Fin N ≃ Fin M
  hi : IsRedOrdered i
  hwi : IsRedOrdered (w • i)
  hd : ∀ a ∈ d.support, ((w • i).lbl a).isLeft
  ht : IsRedOrdered t
  hcap : IsCapGood ν₀ t
  hε : IsBlockShuffle j ν₀ i ε

theorem MidTriple.ext' {τ τ' : MidTriple ℓ j ν ν₀} (hi : τ.i = τ'.i) (hw : τ.w = τ'.w)
    (hd : τ.d = τ'.d) (ht : τ.t = τ'.t) (hε : τ.ε = τ'.ε) : τ = τ' := by
  cases τ; cases τ'
  simp only at hi hw hd ht hε
  subst hi hw hd ht hε
  rfl

theorem MidGen.ext' {g g' : MidGen j hj ν ν₀} (hs : g.s = g'.s) (ht : g.t = g'.t)
    (hd : g.d = g'.d) (hu : g.u = g'.u) : g = g' := by
  cases g; cases g'
  simp only at hs ht hd hu
  subst hs ht hd hu
  rfl

/-- The window shuffle of a triple: the strand `a` of `i` goes from its bottom position to the
top position of the strand `w a` of `s = w • i`, and the strand `q` of `t` to the window. -/
def MidTriple.u (τ : MidTriple ℓ j ν ν₀) : Perm (Fin M) :=
  τ.ε.symm.trans ((Equiv.sumCongr τ.w (Equiv.refl _)).trans (midPosEquiv j ν₀ (τ.w • τ.i)))

theorem MidTriple.u_inl (τ : MidTriple ℓ j ν ν₀) (a : Fin m) :
    τ.u (τ.ε (.inl a)) = outPos j ν₀ (τ.w • τ.i) (τ.w a) := by
  simp [MidTriple.u, outPos]

theorem MidTriple.u_inr (τ : MidTriple ℓ j ν ν₀) (q : Fin N) :
    τ.u (τ.ε (.inr q)) = winPos (midPos_add_N_le j ν₀ (τ.w • τ.i)) q := by
  simp [MidTriple.u, midPosEquiv_inr]

/-- The bottom labels below a window shuffle `u` with `u (ε (inl a)) = outPos s (w a)`. -/
theorem bot_lbl_inl {s : Seq (stendhalWeight ℓ ν)} {t : Seq (stendhalWeight 2 ν₀)}
    {u : Perm (Fin M)} {w : Perm (Fin m)} {ε : Fin m ⊕ Fin N ≃ Fin M}
    (hu : ∀ a, u (ε (.inl a)) = outPos j ν₀ s (w a)) (a : Fin m) :
    (u⁻¹ • midSeq j hj s t).lbl (ε (.inl a)) = oldColour j hj ((w⁻¹ • s).lbl a) := by
  change (midSeq j hj s t).1 ((u⁻¹).symm (ε (.inl a))) = _
  rw [Perm.inv_def, Equiv.symm_symm, hu]
  change (midSeq j hj s t).lbl _ = _
  rw [midSeq_lbl_outPos]
  simp [Seq.lbl, Perm.inv_def]

theorem bot_lbl_inr {s : Seq (stendhalWeight ℓ ν)} {t : Seq (stendhalWeight 2 ν₀)}
    {u : Perm (Fin M)} {ε : Fin m ⊕ Fin N ≃ Fin M}
    (hu : ∀ q, u (ε (.inr q)) = winPos (midPos_add_N_le j ν₀ s) q) (q : Fin N) :
    (u⁻¹ • midSeq j hj s t).lbl (ε (.inr q)) = cupColour j hj (t.lbl q) := by
  change (midSeq j hj s t).1 ((u⁻¹).symm (ε (.inr q))) = _
  rw [Perm.inv_def, Equiv.symm_symm, hu]
  exact midSeq_lbl_winPos s t q

/-- The cap-good generator of a triple. -/
def MidTriple.toGen (τ : MidTriple ℓ j ν ν₀) : {g : MidGen j hj ν ν₀ // IsCapGood ν₀ g.t} :=
  ⟨{ s := τ.w • τ.i
     t := τ.t
     d := τ.d
     u := τ.u
     hs := τ.hwi
     ht := τ.ht
     hd := τ.hd
     hu := by
       intro q q' hqq'
       have h := fun q => (Perm.inv_eq_iff_eq (f := τ.u)).2 (τ.u_inr q).symm
       simp only [h]
       exact τ.hε.2.1 hqq'
     hbot := by
       refine isRedOrdered_of_isBlockShuffle τ.hε τ.hi τ.ht (fun a => ?_)
         (bot_lbl_inr τ.u_inr)
       rw [bot_lbl_inl τ.u_inl, inv_smul_smul] }, τ.hcap⟩

theorem MidTriple.toGen_injective : Function.Injective (MidTriple.toGen (j := j) (hj := hj)
    (ν := ν) (ν₀ := ν₀)) := by
  intro τ τ' h
  have hs : τ.w • τ.i = τ'.w • τ'.i := congrArg (fun g => g.1.s) h
  have ht : τ.t = τ'.t := congrArg (fun g => g.1.t) h
  have hd : τ.d = τ'.d := congrArg (fun g => g.1.d) h
  have hu : τ.u = τ'.u := congrArg (fun g => g.1.u) h
  -- the bottom positions agree
  have key : ∀ x, Sum.map τ.w id (τ.ε.symm x) = Sum.map τ'.w id (τ'.ε.symm x) := by
    intro x
    have := congrArg (fun v : Perm (Fin M) => v x) hu
    simp only [MidTriple.u, Equiv.trans_apply, Equiv.sumCongr_apply, Equiv.coe_refl] at this
    rw [hs] at this
    exact (midPosEquiv j ν₀ _).injective this
  have hinr : ∀ q, τ.ε (.inr q) = τ'.ε (.inr q) := by
    intro q
    have := key (τ.ε (.inr q))
    rw [Equiv.symm_apply_apply] at this
    rcases hc : τ'.ε.symm (τ.ε (.inr q)) with b | q'
    · rw [hc] at this; simp at this
    · rw [hc] at this
      simp only [Sum.map_inr, id_eq, Sum.inr.injEq] at this
      subst this
      exact (τ'.ε.symm_apply_eq.1 hc).symm ▸ rfl
  have hrange : ∀ (σ σ' : MidTriple ℓ j ν ν₀),
      (∀ x, Sum.map σ.w id (σ.ε.symm x) = Sum.map σ'.w id (σ'.ε.symm x)) →
      Set.range (fun a => σ.ε (.inl a)) ⊆ Set.range (fun a => σ'.ε (.inl a)) := by
    rintro σ σ' hk _ ⟨a, rfl⟩
    have := hk (σ.ε (.inl a))
    rw [Equiv.symm_apply_apply] at this
    rcases hc : σ'.ε.symm (σ.ε (.inl a)) with b | q'
    · exact ⟨b, (σ'.ε.symm_apply_eq.1 hc).symm⟩
    · rw [hc] at this; simp at this
  have hinl : (fun a => τ.ε (.inl a)) = fun a => τ'.ε (.inl a) :=
    (StrictMono.range_inj_of_wellFoundedLT τ.hε.1 τ'.hε.1).1
      ((hrange τ τ' key).antisymm (hrange τ' τ fun x => (key x).symm))
  have hε : τ.ε = τ'.ε := by
    ext p
    rcases p with a | q
    · exact congrArg Fin.val (congrFun hinl a)
    · exact congrArg Fin.val (hinr q)
  have hw : τ.w = τ'.w := by
    ext a
    have := key (τ.ε (.inl a))
    rw [Equiv.symm_apply_apply, hε, Equiv.symm_apply_apply] at this
    simpa using congrArg Fin.val (Sum.inl_injective this)
  refine MidTriple.ext' ?_ hw hd ht hε
  rw [hw] at hs
  exact smul_left_cancel _ hs

section Surjective

variable (g : MidGen j hj ν ν₀)

/-- The bottom positions of the strands of a generator. -/
def MidGen.botEquiv : Fin m ⊕ Fin N ≃ Fin M := (midPosEquiv j ν₀ g.s).trans g.u.symm

theorem MidGen.botEquiv_inr (q : Fin N) :
    g.botEquiv (.inr q) = g.u⁻¹ (winPos (midPos_add_N_le j ν₀ g.s) q) := by
  simp [MidGen.botEquiv, midPosEquiv_inr, Perm.inv_def]

/-- The bottom positions of the strands of `λ`, in increasing order. -/
def MidGen.botSet : Finset (Fin M) :=
  Finset.univ.map ⟨fun a => g.botEquiv (.inl a), fun _ _ h => Sum.inl_injective
    (g.botEquiv.injective h)⟩

theorem MidGen.card_botSet : g.botSet.card = m := by simp [MidGen.botSet]

/-- The increasing enumeration of the bottom positions of the strands of `λ`. -/
def MidGen.botOrd : Fin m ↪o Fin M := g.botSet.orderEmbOfFin g.card_botSet

theorem MidGen.exists_botOrd (b : Fin m) : ∃ a, g.botEquiv (.inl a) = g.botOrd b := by
  obtain ⟨a, -, ha⟩ := Finset.mem_map.1 (g.botSet.orderEmbOfFin_mem g.card_botSet b)
  exact ⟨a, ha⟩

/-- The permutation of the strands of `λ`: the strand at the `b`-th bottom position of `λ` is the
strand `perm b` of `s` at the top. -/
def MidGen.perm : Perm (Fin m) :=
  Equiv.ofBijective (fun b => (g.exists_botOrd b).choose)
    (Finite.injective_iff_bijective.1 fun b b' h => by
      have h1 := (g.exists_botOrd b).choose_spec
      have h2 := (g.exists_botOrd b').choose_spec
      exact g.botOrd.injective (h1.symm.trans ((congrArg _ (congrArg Sum.inl h)).trans h2)))

theorem MidGen.botEquiv_perm (b : Fin m) : g.botEquiv (.inl (g.perm b)) = g.botOrd b :=
  (g.exists_botOrd b).choose_spec

/-- The shuffle of a generator. -/
def MidGen.shuffle : Fin m ⊕ Fin N ≃ Fin M :=
  (Equiv.sumCongr g.perm (Equiv.refl _)).trans g.botEquiv

theorem MidGen.shuffle_inl (b : Fin m) : g.shuffle (.inl b) = g.botOrd b := by
  simp [MidGen.shuffle, MidGen.botEquiv_perm]

theorem MidGen.u_shuffle_inl (b : Fin m) :
    g.u (g.shuffle (.inl b)) = outPos j ν₀ g.s (g.perm b) := by
  simp [MidGen.shuffle, MidGen.botEquiv, outPos]

theorem MidGen.u_shuffle_inr (q : Fin N) :
    g.u (g.shuffle (.inr q)) = winPos (midPos_add_N_le j ν₀ g.s) q := by
  simp [MidGen.shuffle, MidGen.botEquiv, midPosEquiv_inr]

theorem MidGen.shuffle_inr (q : Fin N) :
    g.shuffle (.inr q) = g.u⁻¹ (winPos (midPos_add_N_le j ν₀ g.s) q) := by
  exact ((Perm.inv_eq_iff_eq).2 (g.u_shuffle_inr q).symm).symm

end Surjective

theorem MidTriple.toGen_surjective : Function.Surjective (MidTriple.toGen (j := j) (hj := hj)
    (ν := ν) (ν₀ := ν₀)) := by
  rintro ⟨g, hcap⟩
  have hl : StrictMono (fun a => g.shuffle (.inl a)) := by
    simp only [MidGen.shuffle_inl]; exact g.botOrd.strictMono
  have hr : StrictMono (fun q => g.shuffle (.inr q)) := by
    simp only [MidGen.shuffle_inr]; exact g.hu
  obtain ⟨hi, hε⟩ := isBlockShuffle_of_isRedOrdered (i := g.perm⁻¹ • g.s) hl hr g.hbot hcap
    (bot_lbl_inl g.u_shuffle_inl) (bot_lbl_inr g.u_shuffle_inr)
  have hs : g.perm • (g.perm⁻¹ • g.s) = g.s := smul_inv_smul _ _
  refine ⟨⟨g.perm⁻¹ • g.s, g.perm, g.d, g.t, g.shuffle, hi, by rw [hs]; exact g.hs,
    by rw [hs]; exact g.hd, g.ht, hcap, hε⟩, Subtype.ext (MidGen.ext' hs rfl rfl ?_)⟩
  refine Equiv.ext fun x => ?_
  obtain ⟨p, rfl⟩ := g.shuffle.surjective x
  change (midPosEquiv j ν₀ (g.perm • (g.perm⁻¹ • g.s)))
    (Sum.map g.perm id (g.shuffle.symm (g.shuffle p))) = g.u (g.shuffle p)
  rw [Equiv.symm_apply_apply, hs]
  rcases p with b | q
  · rw [g.u_shuffle_inl]; rfl
  · rw [g.u_shuffle_inr, ← midPosEquiv_inr]; rfl

variable (j hj ν ν₀) in
/-- **Webster's triples are the cap-good generators** of the corner of the maximum
(arXiv:1309.3796v3, §7.3, Lemma 7.17). -/
def midTripleEquiv : MidTriple ℓ j ν ν₀ ≃ {g : MidGen j hj ν ν₀ // IsCapGood ν₀ g.t} :=
  Equiv.ofBijective MidTriple.toGen ⟨MidTriple.toGen_injective, MidTriple.toGen_surjective⟩

theorem midTripleEquiv_apply_t (τ : MidTriple ℓ j ν ν₀) :
    (midTripleEquiv j hj ν ν₀ τ).1.t = τ.t := rfl

end Triples

end Categorification.Stendhal.CupCap

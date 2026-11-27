/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidLeftFreeSurj
import Categorification.WeightedKLR.Rigidity.CupCapMidTriple

/-!
# The dots of `λ` acting on the model of `K̃^{λ⁺}_λ`

Webster, arXiv:1309.3796v3, §7.3, the assertion after Lemma 7.19 that `coe^{λ⁺}_λ` is projective
as a left `T^λ`-module, for a cap after the red strand `λ_j`. The polynomial ring
`P = k[x_1, …, x_m]` in the dots of `λ` acts on `T̃^λ` through `x^d ↦ x^d · 1`. It is
commutative, and every left `T̃^λ`-module is a `P`-module through it.

On the model, `x^e` sends the element `v γ_g` of a generator `g` to `v γ_{g + e}`, the generator
with the dots `e` added, when `e` puts no dot on a red strand of the top of `g`, and to zero
otherwise (`midLeftAlg_polT_tmul_midGenCorner`). The permutation of the strands of `λ` of the
generator of a triple is the permutation of the triple (`MidTriple.perm_toGen`).

## Main definitions

* `polT`: the dots of `λ` in `T̃^λ`, `p ↦ p · 1`.
* `MidGen.addDots`: the generator with dots added.
* `MidTriple.blockShuffle`: the block shuffle of a triple, with its permutation of `λ` and its
  dots removed.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA Equiv MulOpposite InductionAlong MvPolynomial

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "T" => StendhalAlgebra k Q Λ ν
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)
local notation "bot" => botMap k Q Λ Λc j hj ν ν₀

/-! ### The permutation of the generator of a triple -/

omit [DecidableEq I] in
/-- The permutation of the strands of `λ` of the generator of a triple is its permutation `w`. -/
theorem MidTriple.perm_toGen (τ : MidTriple ℓ j ν ν₀) :
    (MidTriple.toGen (hj := hj) τ).1.perm = τ.w := by
  set g := (MidTriple.toGen (hj := hj) τ).1
  have hbe : ∀ a, g.botEquiv (.inl (τ.w a)) = τ.ε (.inl a) := by
    intro a
    have h := τ.u_inl a
    change g.u.symm (outPos j ν₀ (τ.w • τ.i) (τ.w a)) = _
    rw [← h]
    exact g.u.symm_apply_apply _
  have hbo : (fun b => τ.ε (.inl b)) = g.botOrd :=
    Finset.orderEmbOfFin_unique g.card_botSet
      (fun b => by rw [← hbe]; exact Finset.mem_map_of_mem _ (Finset.mem_univ _)) τ.hε.1
  ext b
  have h1 := g.botEquiv_perm b
  rw [← hbo] at h1
  dsimp only at h1
  rw [← hbe] at h1
  exact congrArg Fin.val (Sum.inl_injective (g.botEquiv.injective h1))

/-- The triple with its permutation of `λ` and its dots removed. -/
def MidTriple.block (τ : MidTriple ℓ j ν ν₀) : MidTriple ℓ j ν ν₀ :=
  { τ with w := 1, d := 0, hwi := by rw [one_smul]; exact τ.hi, hd := by simp }

variable (hj) in
/-- **The block shuffle of a triple**: its generator with the permutation of `λ` and the dots
removed. -/
def MidTriple.blockShuffle (τ : MidTriple ℓ j ν ν₀) : MidBlockShuffle j hj ν ν₀ :=
  ⟨⟨(MidTriple.toGen (hj := hj) τ.block).1, rfl⟩, MidTriple.perm_toGen _⟩

omit [DecidableEq I] in
theorem MidTriple.blockShuffle_s (τ : MidTriple ℓ j ν ν₀) :
    (τ.blockShuffle hj).1.1.s = τ.i := one_smul _ _

/-! ### Adding dots to a generator -/

omit [DecidableEq I] in
theorem support_add_isLeft {s : Seq (stendhalWeight ℓ ν)} {d e : Fin m →₀ ℕ}
    (hd : ∀ a ∈ d.support, (s.lbl a).isLeft) (he : ∀ a ∈ e.support, (s.lbl a).isLeft) :
    ∀ a ∈ (d + e).support, (s.lbl a).isLeft := fun a ha => by
  rcases Finset.mem_union.1 (Finsupp.support_add ha) with h | h
  exacts [hd a h, he a h]

/-- The generator `g` with the dots `e` added on top. -/
def MidGen.addDots (g : MidGen j hj ν ν₀) (e : Fin m →₀ ℕ)
    (he : ∀ a ∈ e.support, (g.s.lbl a).isLeft) : MidGen j hj ν ν₀ :=
  { g with d := g.d + e, hd := support_add_isLeft g.hd he }

variable {ρ₃ : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀)))) → List ℕ}

theorem pol_mul_midGenKLR_of_isLeft (g : MidGen j hj ν ν₀) (e : Fin m →₀ ℕ)
    (he : ∀ a ∈ e.support, (g.s.lbl a).isLeft) :
    pol (rename (outPos j ν₀ g.s) (monomial e 1)) * midGenKLR Q Λ Λc ρ₃ g =
      midGenKLR Q Λ Λc ρ₃ (g.addDots e he) := by
  simp only [midGenKLR, MidGen.addDots, MidGen.bot]
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc (pol _) (KLRAlgebra.e _), ← (e_commute_pol _ _).eq,
    mul_assoc (KLRAlgebra.e _) (pol _) (pol _), ← map_mul, ← map_mul, monomial_mul_monomial,
    mul_one, add_comm e]

theorem bot_pol_mul_midGenKLR_of_not (g : MidGen j hj ν ν₀) (e : Fin m →₀ ℕ)
    (he : ¬ ∀ a ∈ e.support, (g.s.lbl a).isLeft) :
    bot (pol (rename (outPos j ν₀ g.s) (monomial e 1)) * midGenKLR Q Λ Λc ρ₃ g) = 0 := by
  push Not at he
  obtain ⟨a, ha, hr⟩ := he
  have hX : (monomial e 1 : MvPolynomial (Fin m) k) =
      X a * monomial (e - Finsupp.single a 1) 1 := by
    rw [X, monomial_mul_monomial, one_mul, add_tsub_cancel_of_le
      (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 ha)))]
  have hred : ((midSeq j hj g.s g.t).lbl (outPos j ν₀ g.s a)).isRight := by
    rw [midSeq_lbl_outPos]
    cases h : g.s.lbl a with
    | inl i => rw [h] at hr; exact absurd rfl hr
    | inr r => rfl
  have hmg : KLRAlgebra.e (midSeq j hj g.s g.t) * midGenKLR Q Λ Λc ρ₃ g =
      midGenKLR Q Λ Λc ρ₃ g := by
    simp only [midGenKLR, ← mul_assoc, e_mul_self]
  have h1 : pol (rename (outPos j ν₀ g.s) (monomial e 1)) * midGenKLR Q Λ Λc ρ₃ g =
      (KLRAlgebra.x (outPos j ν₀ g.s a) * KLRAlgebra.e (midSeq j hj g.s g.t)) *
        (pol (rename (outPos j ν₀ g.s) (monomial (e - Finsupp.single a 1) 1)) *
          midGenKLR Q Λ Λc ρ₃ g) := by
    rw [hX, map_mul, map_mul, rename_X, pol_X, mul_assoc (KLRAlgebra.x _),
      mul_assoc (KLRAlgebra.x _) (KLRAlgebra.e _)]
    congr 1
    rw [← mul_assoc, (e_commute_pol _ _).eq, mul_assoc, hmg]
  rw [h1, map_mul, bot_x_mul_e_of_red _ _ hred, zero_mul]

/-! ### The dots of `λ` in `T̃^λ` -/

variable (Q Λ ν) in
/-- **The dots of `λ` in `T̃^λ`**, `p ↦ p · 1`. -/
abbrev polT : MvPolynomial (Fin m) k →ₐ[k] T := (topMap k Q Λ ν).comp pol

/-- A dot on a red strand vanishes in `T̃^λ`. -/
theorem topMap_x_mul_e_of_red (a : Fin m) (i : Seq (stendhalWeight ℓ ν))
    (h : (i.lbl a).isRight) :
    topMap k Q Λ ν (KLRAlgebra.x a * KLRAlgebra.e i) = 0 := by
  rw [AlgHom.comp_apply, map_mul]
  change orderProjection _ _ _ (StendhalAlgebraAllOrders.x _ * StendhalAlgebraAllOrders.e _) = 0
  rw [StendhalAlgebraAllOrders.x_mul_e_of_red _ _ h, map_zero]

/-- **The dots `x^e` act on `v γ_g`** by adding `e` to the dots of `g`, or by zero when `e` puts a
dot on a red strand. -/
theorem midLeftAlg_polT_tmul_midGenCorner {L : Type*} [AddCommGroup L]
    [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
    {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}
    (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (g : MidGen j hj ν ν₀) (e : Fin m →₀ ℕ) (v : L) :
    midLeftAlg L hL hR (polT Q Λ ν (monomial e 1)) (Ind.tmul (midGenCorner Q Λ Λc ρ₃ g) v) =
      if he : ∀ a ∈ e.support, (g.s.lbl a).isLeft then
        Ind.tmul (midGenCorner Q Λ Λc ρ₃ (g.addDots e he)) v else 0 := by
  rw [AlgHom.comp_apply, midLeftAlg_topMap, midGenCorner_eq_midGen, midGenElt,
    midKLRAct_pol_tmul_midGen hR g.s _ _ (midIdem_mul_midGenKLR g)]
  split_ifs with he
  · rw [pol_mul_midGenKLR_of_isLeft g e he, midGenCorner_eq_midGen, midGenElt]
  · rw [bot_pol_mul_midGenKLR_of_not g e he, tmul_midGen_zero]

/-! ### The diagrams of the triples in `T̃^λ` -/

/-- The triple `τ` with the dots `e` added. -/
def MidTriple.addDots (τ : MidTriple ℓ j ν ν₀) (e : Fin m →₀ ℕ)
    (he : ∀ a ∈ e.support, ((τ.w • τ.i).lbl a).isLeft) : MidTriple ℓ j ν ν₀ :=
  { τ with d := τ.d + e, hd := support_add_isLeft τ.hd he }

omit [DecidableEq I] in
theorem MidTriple.toGen_addDots (τ : MidTriple ℓ j ν ν₀) (e : Fin m →₀ ℕ)
    (he : ∀ a ∈ e.support, ((τ.w • τ.i).lbl a).isLeft) :
    (MidTriple.toGen (hj := hj) (τ.addDots e he)).1 =
      (MidTriple.toGen (hj := hj) τ).1.addDots e he :=
  rfl

variable (ρ₁ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ)

variable (Q Λ) in
/-- **The diagram `x^d ψ_{ρ w} e(i)` of a triple** `(i, w, d, t, ε)`, in the KLR algebra of
`λ`. -/
def MidTriple.elt (τ : MidTriple ℓ j ν ν₀) : R :=
  pol (monomial τ.d 1) * ψw (ρ₁ τ.w) * KLRAlgebra.e τ.i

theorem MidTriple.elt_mul_e (τ : MidTriple ℓ j ν ν₀) :
    τ.elt Q Λ ρ₁ * KLRAlgebra.e τ.i = τ.elt Q Λ ρ₁ := by
  rw [MidTriple.elt, mul_assoc, e_mul_self]

theorem MidTriple.e_mul_elt (hρ₁ : ∀ w, wordProd m (ρ₁ w) = w) (τ : MidTriple ℓ j ν ν₀) :
    KLRAlgebra.e (τ.w • τ.i) * τ.elt Q Λ ρ₁ = τ.elt Q Λ ρ₁ := by
  rw [MidTriple.elt, ← mul_assoc, ← mul_assoc, (e_commute_pol _ _).eq, mul_assoc (pol _),
    e_mul_ψw, hρ₁, inv_smul_smul, mul_assoc, mul_assoc, e_mul_self, ← mul_assoc]

/-- **The dots `x^e` act on the diagram of a triple** by adding `e` to its dots, or by zero when
`e` puts a dot on a red strand at the top. -/
theorem polT_mul_topMap_elt (hρ₁ : ∀ w, wordProd m (ρ₁ w) = w) (τ : MidTriple ℓ j ν ν₀)
    (e : Fin m →₀ ℕ) :
    polT Q Λ ν (monomial e 1) * topMap k Q Λ ν (τ.elt Q Λ ρ₁) =
      if he : ∀ a ∈ e.support, ((τ.w • τ.i).lbl a).isLeft then
        topMap k Q Λ ν ((τ.addDots e he).elt Q Λ ρ₁) else 0 := by
  rw [AlgHom.comp_apply, ← map_mul]
  split_ifs with he
  · congr 1
    simp only [MidTriple.elt, MidTriple.addDots]
    rw [← mul_assoc, ← mul_assoc, ← map_mul, monomial_mul_monomial, mul_one, add_comm e]
  · push Not at he
    obtain ⟨a, ha, hr⟩ := he
    have hX : (monomial e 1 : MvPolynomial (Fin m) k) =
        X a * monomial (e - Finsupp.single a 1) 1 := by
      rw [X, monomial_mul_monomial, one_mul, add_tsub_cancel_of_le
        (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 ha)))]
    have hred : ((τ.w • τ.i).lbl a).isRight := by
      cases h : (τ.w • τ.i).lbl a with
      | inl i => rw [h] at hr; exact absurd rfl hr
      | inr r => rfl
    have key : pol (monomial e 1) * τ.elt Q Λ ρ₁ =
        (KLRAlgebra.x a * KLRAlgebra.e (τ.w • τ.i)) *
          (pol (monomial (e - Finsupp.single a 1) 1) * τ.elt Q Λ ρ₁) := by
      rw [hX, map_mul, pol_X, mul_assoc, mul_assoc (KLRAlgebra.x a) (KLRAlgebra.e _)]
      congr 1
      rw [← mul_assoc, (e_commute_pol _ _).eq, mul_assoc, τ.e_mul_elt (Q := Q) (Λ := Λ) ρ₁ hρ₁]
    rw [key, map_mul, topMap_x_mul_e_of_red a _ hred, zero_mul]

end Categorification.Stendhal.CupCap

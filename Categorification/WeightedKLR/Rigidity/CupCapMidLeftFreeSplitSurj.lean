/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidLeftFreeSplit

/-!
# Surjectivity of the splitting map

Webster, arXiv:1309.3796v3, §7.3, the assertion after Lemma 7.19 that `coe^{λ⁺}_λ` is projective
as a left `T^λ`-module, for a cap after the red strand `λ_j`. The splitting map
`Φ : K̃^{λ⁺}_λ → ⨁_g T̃^λ e(s_g) ⊗_k L e(t_g)` is surjective (`midLeftSplit_surjective`): the
summand `T̃^λ e(s) ⊗_k L e(t)` of a block shuffle is spanned by the `x^u ψ_{ρ w} e(s) ⊗ v`
(KL I, Theorem 2.5, spanning half, dots on top), each of which is zero or the image of the
element `v γ_g` of the generator of the triple `(s, w, u, t, ε)` (`midTripleEquiv`, Lemma 7.17).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA Equiv MulOpposite InductionAlong MvPolynomial TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "T" => StendhalAlgebra k Q Λ ν
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)

/-! ### Diagrams that vanish in `T̃^λ` -/

theorem e_smul_mul_pol_ψw (ρ₁ : Perm (Fin m) → List ℕ) (hρ₁ : ∀ w, wordProd m (ρ₁ w) = w)
    (w : Perm (Fin m)) (q : MvPolynomial (Fin m) k) (i : Seq (stendhalWeight ℓ ν)) :
    (KLRAlgebra.e (w • i) * (pol q * ψw (ρ₁ w) * KLRAlgebra.e i) : R) =
      pol q * ψw (ρ₁ w) * KLRAlgebra.e i := by
  rw [← mul_assoc, ← mul_assoc, (e_commute_pol _ _).eq, mul_assoc (pol _), e_mul_ψw, hρ₁,
    inv_smul_smul, mul_assoc, mul_assoc, e_mul_self, ← mul_assoc]

/-- A diagram with a dot on a red strand at its top vanishes in `T̃^λ`. -/
theorem topMap_pol_mul_of_not (u : Fin m →₀ ℕ) {i : Seq (stendhalWeight ℓ ν)} {Y : R}
    (hY : KLRAlgebra.e i * Y = Y) (hu : ¬ ∀ a ∈ u.support, (i.lbl a).isLeft) :
    topMap k Q Λ ν (pol (monomial u 1) * Y) = 0 := by
  push Not at hu
  obtain ⟨a, ha, hr⟩ := hu
  have hX : (monomial u 1 : MvPolynomial (Fin m) k) =
      X a * monomial (u - Finsupp.single a 1) 1 := by
    rw [X, monomial_mul_monomial, one_mul, add_tsub_cancel_of_le
      (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 ha)))]
  have hred : (i.lbl a).isRight := by
    cases h : i.lbl a with
    | inl i => rw [h] at hr; exact absurd rfl hr
    | inr r => rfl
  have key : pol (monomial u 1) * Y =
      (KLRAlgebra.x a * KLRAlgebra.e i) * (pol (monomial (u - Finsupp.single a 1) 1) * Y) := by
    rw [hX, map_mul, pol_X, mul_assoc, mul_assoc (KLRAlgebra.x a) (KLRAlgebra.e _)]
    congr 1
    rw [← mul_assoc, (e_commute_pol _ _).eq, mul_assoc, hY]
  rw [key, map_mul, topMap_x_mul_e_of_red a _ hred, zero_mul]

theorem topMap_e_mul_of_not {i : Seq (stendhalWeight ℓ ν)} (hi : ¬ IsRedOrdered i) (Y : R) :
    topMap k Q Λ ν (KLRAlgebra.e i * Y) = 0 := by
  rw [map_mul, AlgHom.comp_apply, orderProjection_e_of_not hi, zero_mul]

variable {L : Type*} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

local notation "Src" => MidBlockSrc j hj Q Λ Λc ν ν₀ L

theorem lof_tmul_congr [DecidableEq (MidBlockShuffle j hj ν ν₀)]
    {b b' : MidBlockShuffle j hj ν ν₀} (hb : b = b') {a a' : T} (haa : a = a')
    (ha : a ∈ Submodule.span T {StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λ) b.1.1.s b.1.1.hs})
    (ha' : a' ∈ Submodule.span T
      {StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λ) b'.1.1.s b'.1.1.hs}) (x : L)
    (hx : x ∈ BalancedTensor.idemPart k L (midGenIdem (k := k) Q Λc b.1.1))
    (hx' : x ∈ BalancedTensor.idemPart k L (midGenIdem (k := k) Q Λc b'.1.1)) :
    (DirectSum.lof k _ (fun g : MidBlockShuffle j hj ν ν₀ => MidLeftSummand Q Λ Λc L g.1) b
      (⟨a, ha⟩ ⊗ₜ ⟨x, hx⟩) : Src) =
    DirectSum.lof k _ (fun g : MidBlockShuffle j hj ν ν₀ => MidLeftSummand Q Λ Λc L g.1) b'
      (⟨a', ha'⟩ ⊗ₜ ⟨x, hx'⟩) := by
  subst hb haa; rfl

variable (ρ₁ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ)
  {ρ₂ : Perm (Fin (Multiset.card (stendhalWeight 2 ν₀))) → List ℕ}
  {ρ₃ : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀)))) → List ℕ}

omit [DecidableEq I] in
/-- The triple of a cap-good block shuffle has trivial permutation and no dots, bottom the top
of the block shuffle, and the block shuffle as its block shuffle. -/
theorem midTripleEquiv_symm_block (b : MidBlockShuffle j hj ν ν₀) (hcap : IsCapGood ν₀ b.1.1.t) :
    ((midTripleEquiv j hj ν ν₀).symm ⟨b.1.1, hcap⟩).i = b.1.1.s ∧
      ((midTripleEquiv j hj ν ν₀).symm ⟨b.1.1, hcap⟩).w = 1 ∧
      ((midTripleEquiv j hj ν ν₀).symm ⟨b.1.1, hcap⟩).d = 0 ∧
      ((midTripleEquiv j hj ν ν₀).symm ⟨b.1.1, hcap⟩).blockShuffle hj = b := by
  set τ := (midTripleEquiv j hj ν ν₀).symm ⟨b.1.1, hcap⟩
  have hg : (MidTriple.toGen (hj := hj) τ).1 = b.1.1 :=
    congrArg Subtype.val ((midTripleEquiv j hj ν ν₀).apply_symm_apply ⟨b.1.1, hcap⟩)
  have hw : τ.w = 1 := by rw [← MidTriple.perm_toGen (hj := hj) τ, hg]; exact b.2
  have hs : τ.w • τ.i = b.1.1.s := congrArg MidGen.s hg
  have hd : τ.d = 0 := (congrArg MidGen.d hg).trans b.1.2
  refine ⟨by rwa [hw, one_smul] at hs, hw, hd, Subtype.ext (Subtype.ext ?_)⟩
  change (MidTriple.toGen (hj := hj) τ.block).1 = b.1.1
  rw [← hg]
  exact congrArg (fun x => (MidTriple.toGen (hj := hj) x).1)
    (MidTriple.ext' rfl hw.symm hd.symm rfl rfl)

/-- The element `x^u ψ_{ρ w} e(i) ⊗ v` of the summand of a cap-good block shuffle is in the
image of the splitting map. -/
theorem lof_pol_ψw_mem_range [DecidableEq (MidGen j hj ν ν₀)]
    [DecidableEq (MidBlockShuffle j hj ν ν₀)] (hρ₁ : ∀ w, wordProd m (ρ₁ w) = w)
    (hQ : KLRSymm Q) (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w) (b : MidBlockShuffle j hj ν ν₀)
    (hcap : IsCapGood ν₀ b.1.1.t)
    (v : BalancedTensor.idemPart k L (midGenIdem (k := k) Q Λc b.1.1))
    (w : Perm (Fin m)) (u : Fin m →₀ ℕ) (i : Seq (stendhalWeight ℓ ν)) :
    (DirectSum.lof k _ (fun g : MidBlockShuffle j hj ν ν₀ => MidLeftSummand Q Λ Λc L g.1) b
      (⟨topMap k Q Λ ν (pol (monomial u 1) * ψw (ρ₁ w) * KLRAlgebra.e i) *
          StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λ) b.1.1.s b.1.1.hs,
        Submodule.mem_span_singleton.2 ⟨_, rfl⟩⟩ ⊗ₜ v) : Src) ∈
      LinearMap.range (midLeftSplit (Q := Q) (Λ := Λ) L ρ₁ hQ hρ₂ hρ₃) := by
  obtain ⟨hib, hw1, hd0, hbτ⟩ := midTripleEquiv_symm_block b hcap
  set τb := (midTripleEquiv j hj ν ν₀).symm ⟨b.1.1, hcap⟩
  set r : R := pol (monomial u 1) * ψw (ρ₁ w) * KLRAlgebra.e i with hr
  have hre : topMap k Q Λ ν r * StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λ) b.1.1.s b.1.1.hs =
      topMap k Q Λ ν (r * KLRAlgebra.e b.1.1.s) := by
    rw [map_mul (topMap k Q Λ ν) r, topMap_e_of_isRedOrdered _ b.1.1.hs]
  have hzero : ∀ h : topMap k Q Λ ν r *
      StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λ) b.1.1.s b.1.1.hs = 0,
      (DirectSum.lof k _ (fun g : MidBlockShuffle j hj ν ν₀ => MidLeftSummand Q Λ Λc L g.1) b
        (⟨topMap k Q Λ ν r * StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λ) b.1.1.s b.1.1.hs,
          Submodule.mem_span_singleton.2 ⟨_, rfl⟩⟩ ⊗ₜ v) : Src) ∈
        LinearMap.range (midLeftSplit (Q := Q) (Λ := Λ) L ρ₁ hQ hρ₂ hρ₃) := fun h => by
    have h0 : (⟨topMap k Q Λ ν r * StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λ) b.1.1.s b.1.1.hs,
        Submodule.mem_span_singleton.2 ⟨_, rfl⟩⟩ : Submodule.span T
          {StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λ) b.1.1.s b.1.1.hs}) = 0 := Subtype.ext h
    rw [h0, TensorProduct.zero_tmul, map_zero]
    exact zero_mem _
  by_cases hi : i = b.1.1.s
  swap
  · refine hzero ?_
    rw [hre, hr, mul_assoc, e_mul_e, ite_eq_right_iff.2 (fun h => absurd h hi), mul_zero,
      map_zero]
  subst hi
  have hY : KLRAlgebra.e (w • b.1.1.s) * (ψw (ρ₁ w) * KLRAlgebra.e b.1.1.s) =
      (ψw (ρ₁ w) * KLRAlgebra.e b.1.1.s : R) := by
    rw [← mul_assoc, e_mul_ψw, hρ₁, inv_smul_smul, mul_assoc, e_mul_self]
  by_cases hws : IsRedOrdered (w • b.1.1.s)
  swap
  · refine hzero ?_
    rw [hre, hr, mul_assoc, e_mul_self, ← e_smul_mul_pol_ψw ρ₁ hρ₁, topMap_e_mul_of_not hws]
  by_cases hu : ∀ a ∈ u.support, ((w • b.1.1.s).lbl a).isLeft
  swap
  · refine hzero ?_
    rw [hre, hr, mul_assoc, e_mul_self, mul_assoc, topMap_pol_mul_of_not u hY hu]
  let τ : MidTriple ℓ j ν ν₀ :=
    { τb with w := w, d := u, hwi := by rw [hib]; exact hws, hd := by rw [hib]; exact hu }
  let g := (MidTriple.toGen (hj := hj) τ).1
  have hcap' : IsCapGood ν₀ g.t := τb.hcap
  have hvmem : (v : L) ∈ BalancedTensor.idemPart k L (midGenIdem (k := k) Q Λc g) :=
    (idemPart_e_congr (midTripleEquiv_symm_t b.1.1 hcap).symm _ _).le v.2
  refine ⟨Ind.tmul (midGenCorner Q Λ Λc ρ₃ g) (v : L), ?_⟩
  have hτ : (midTripleEquiv j hj ν ν₀).symm ⟨g, hcap'⟩ = τ :=
    (midTripleEquiv j hj ν ν₀).symm_apply_apply τ
  rw [midLeftSplit_tmul ρ₁ hQ hρ₂ hρ₃ g
    (⟨(v : L), hvmem⟩ : BalancedTensor.idemPart k L (midGenIdem (k := k) Q Λc g)),
    midSplitGen_of_capGood ρ₁ g hcap',
    midSplitTriple_congr ρ₁ hτ]
  have hbτ' : τ.blockShuffle hj = b := by
    rw [← hbτ]
    exact Subtype.ext (Subtype.ext (congrArg (fun x => (MidTriple.toGen (hj := hj) x).1)
      (MidTriple.ext' rfl rfl rfl rfl rfl)))
  refine lof_tmul_congr hbτ' ?_ _ _ _ _ _
  rw [hre, hr, mul_assoc, e_mul_self, MidTriple.elt]
  change topMap k Q Λ ν (pol (monomial u 1) * ψw (ρ₁ w) * KLRAlgebra.e τb.i) = _
  rw [hib, mul_assoc]

/-- **The splitting map is surjective.** -/
theorem midLeftSplit_surjective [DecidableEq (MidGen j hj ν ν₀)]
    [DecidableEq (MidBlockShuffle j hj ν ν₀)]
    (hρ₁ : ∀ w, IsReduced m (ρ₁ w) ∧ wordProd m (ρ₁ w) = w)
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (hQ : KLRSymm Q) (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w) :
    Function.Surjective (midLeftSplit (Q := Q) (Λ := Λ) (Λc := Λc) (hj := hj) L ρ₁ hQ hρ₂ hρ₃) := by
  intro z
  change z ∈ LinearMap.range (midLeftSplit (Q := Q) (Λ := Λ) L ρ₁ hQ hρ₂ hρ₃)
  induction z using DirectSum.induction_on with
  | zero => exact zero_mem _
  | add x y hx hy => exact add_mem hx hy
  | of b x =>
    rw [← DirectSum.lof_eq_of k]
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
    | tmul a v =>
      by_cases hcap : IsCapGood ν₀ b.1.1.t
      swap
      · have hv : v = 0 := by
          refine Subtype.ext ?_
          have h := hL _ (v : L) hcap
          rw [topMap_e_of_isRedOrdered _ b.1.1.ht] at h
          exact (v.2.symm.trans h)
        rw [hv, TensorProduct.tmul_zero, map_zero]
        exact zero_mem _
      obtain ⟨a', ha'⟩ := Submodule.mem_span_singleton.1 a.2
      obtain ⟨r, rfl⟩ := topMap_surjective' (k := k) (Q := Q) (Λ := Λ) (ν := ν) a'
      have ha : a = ⟨topMap k Q Λ ν r *
          StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λ) b.1.1.s b.1.1.hs,
          Submodule.mem_span_singleton.2 ⟨_, rfl⟩⟩ := Subtype.ext ha'.symm
      rw [ha]
      obtain ⟨n, hn⟩ := exists_mem_filt r
      have hspan := KLRAlgebra.mem_span_dotsTop_of_mem_filt ρ₁ hρ₁ hn
      clear hn ha ha' a
      induction hspan using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨w, u, i, -, rfl⟩ := hy
        exact lof_pol_ψw_mem_range ρ₁ (fun w => (hρ₁ w).2) hQ hρ₂ hρ₃ b hcap v w u i
      | zero =>
        have h0 : (⟨topMap k Q Λ ν 0 *
            StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λ) b.1.1.s b.1.1.hs,
            Submodule.mem_span_singleton.2 ⟨_, rfl⟩⟩ : Submodule.span T
              {StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λ) b.1.1.s b.1.1.hs}) = 0 :=
          Subtype.ext (by
            change topMap k Q Λ ν 0 * _ = 0
            rw [map_zero, zero_mul])
        rw [h0, TensorProduct.zero_tmul, map_zero]
        exact zero_mem _
      | add y y' _ _ h h' =>
        have hadd : (⟨topMap k Q Λ ν (y + y') *
            StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λ) b.1.1.s b.1.1.hs,
            Submodule.mem_span_singleton.2 ⟨_, rfl⟩⟩ : Submodule.span T
              {StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λ) b.1.1.s b.1.1.hs}) =
            ⟨_, Submodule.mem_span_singleton.2 ⟨topMap k Q Λ ν y, rfl⟩⟩ +
              ⟨_, Submodule.mem_span_singleton.2 ⟨topMap k Q Λ ν y', rfl⟩⟩ :=
          Subtype.ext (by
            change topMap k Q Λ ν (y + y') * _ = topMap k Q Λ ν y * _ + topMap k Q Λ ν y' * _
            rw [map_add, add_mul])
        rw [hadd, TensorProduct.add_tmul, map_add]
        exact add_mem h h'
      | smul c y _ h =>
        have hsm : (⟨topMap k Q Λ ν (c • y) *
            StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λ) b.1.1.s b.1.1.hs,
            Submodule.mem_span_singleton.2 ⟨_, rfl⟩⟩ : Submodule.span T
              {StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λ) b.1.1.s b.1.1.hs}) =
            c • ⟨_, Submodule.mem_span_singleton.2 ⟨topMap k Q Λ ν y, rfl⟩⟩ :=
          Subtype.ext (by
            change topMap k Q Λ ν (c • y) * _ = c • (topMap k Q Λ ν y * _)
            rw [map_smul, smul_mul_assoc])
        rw [hsm, ← TensorProduct.smul_tmul', map_smul]
        exact Submodule.smul_mem _ c h

end Categorification.Stendhal.CupCap

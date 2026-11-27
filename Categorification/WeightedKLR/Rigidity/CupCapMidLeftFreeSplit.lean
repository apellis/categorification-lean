/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidLeftFreePoly

/-!
# The splitting map of the model of `K̃^{λ⁺}_λ` onto the block shuffles

Webster, arXiv:1309.3796v3, §7.3, the assertion after Lemma 7.19 that `coe^{λ⁺}_λ` is projective
as a left `T^λ`-module, for a cap after the red strand `λ_j`. Through the basis of the model
(`midModelEquivₖ`) and Webster's triples (`midTripleEquiv`, Lemma 7.17), the map

  `Φ : K̃^{λ⁺}_λ → ⨁_g T̃^λ e(s_g) ⊗_k L e(t_g)`, `v γ_{(i, w, d, t, ε)} ↦ x^d ψ_{ρ w} e(i) ⊗ v`,

sends the element of a cap-good generator to the diagram of its triple in the summand of its
block shuffle, and is zero on the other generators. It commutes with the dots of `λ`
(`midLeftSplit_polT_smul`).

## Main definitions

* `midLeftSplit`: the map `Φ`, `k`-linear.
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

variable {L : Type*} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

variable (j hj Q Λ Λc ν ν₀ L) in
/-- The source `⨁_g T̃^λ e(s_g) ⊗_k L e(t_g)` of the comparison map over the block shuffles. -/
abbrev MidBlockSrc : Type _ :=
  DirectSum (MidBlockShuffle j hj ν ν₀) fun g => MidLeftSummand Q Λ Λc L g.1

local notation "Src" => MidBlockSrc j hj Q Λ Λc ν ν₀ L

theorem idemPart_e_congr {t t' : Seq (stendhalWeight 2 ν₀)} (h : t = t') (ht : IsRedOrdered t)
    (ht' : IsRedOrdered t') :
    BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht)) =
      BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t' ht')) := by
  subst h; rfl

variable (ρ₁ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ)

theorem topMap_elt_mem (τ : MidTriple ℓ j ν ν₀) :
    topMap k Q Λ ν (τ.elt Q Λ ρ₁) ∈ Submodule.span T
      {StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λ) (τ.blockShuffle hj).1.1.s
        (τ.blockShuffle hj).1.1.hs} := by
  refine Submodule.mem_span_singleton.2 ⟨topMap k Q Λ ν (τ.elt Q Λ ρ₁), ?_⟩
  have he : StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λ) (τ.blockShuffle hj).1.1.s
      (τ.blockShuffle hj).1.1.hs = topMap k Q Λ ν (KLRAlgebra.e τ.i) := by
    rw [topMap_e_of_isRedOrdered τ.i τ.hi]
    congr 1
  rw [smul_eq_mul, he, ← map_mul, MidTriple.elt_mul_e]

variable (L) in
/-- The summand map of a triple: `v ↦ x^d ψ_{ρ w} e(i) ⊗ v` in the summand of its block
shuffle. -/
def midSplitTriple [DecidableEq (MidBlockShuffle j hj ν ν₀)] (τ : MidTriple ℓ j ν ν₀) :
    BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) τ.t τ.ht))
      →ₗ[k] Src :=
  (DirectSum.lof k _ (fun g : MidBlockShuffle j hj ν ν₀ => MidLeftSummand Q Λ Λc L g.1)
    (τ.blockShuffle hj)).comp
    (TensorProduct.mk k _ _ ⟨topMap k Q Λ ν (τ.elt Q Λ ρ₁), topMap_elt_mem ρ₁ τ⟩)

omit [DecidableEq I] in
theorem midTripleEquiv_symm_t (g : MidGen j hj ν ν₀) (hcap : IsCapGood ν₀ g.t) :
    ((midTripleEquiv j hj ν ν₀).symm ⟨g, hcap⟩).t = g.t :=
  congrArg (fun x => x.1.t) ((midTripleEquiv j hj ν ν₀).apply_symm_apply ⟨g, hcap⟩)

theorem mem_idemPart_symm (g : MidGen j hj ν ν₀) (hcap : IsCapGood ν₀ g.t)
    (v : BalancedTensor.idemPart k L (midGenIdem (k := k) Q Λc g)) :
    (v : L) ∈ BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc)
      ((midTripleEquiv j hj ν ν₀).symm ⟨g, hcap⟩).t
      ((midTripleEquiv j hj ν ν₀).symm ⟨g, hcap⟩).ht)) :=
  (idemPart_e_congr (midTripleEquiv_symm_t g hcap).symm _ _).le v.2

variable (L) in
/-- The summand map of a generator: through its triple when it is cap-good, zero otherwise. -/
def midSplitGen [DecidableEq (MidBlockShuffle j hj ν ν₀)] (g : MidGen j hj ν ν₀) :
    BalancedTensor.idemPart k L (midGenIdem (k := k) Q Λc g) →ₗ[k] Src where
  toFun v := if hcap : IsCapGood ν₀ g.t then
    midSplitTriple (Q := Q) (Λ := Λ) L ρ₁ ((midTripleEquiv j hj ν ν₀).symm ⟨g, hcap⟩)
      ⟨v, mem_idemPart_symm g hcap v⟩ else 0
  map_add' v v' := by
    split_ifs with hcap
    · rw [← map_add]; rfl
    · rw [add_zero]
  map_smul' c v := by
    split_ifs with hcap
    · rw [RingHom.id_apply, ← map_smul]; rfl
    · rw [smul_zero]

theorem midSplitGen_of_capGood [DecidableEq (MidBlockShuffle j hj ν ν₀)]
    (g : MidGen j hj ν ν₀) (hcap : IsCapGood ν₀ g.t)
    (v : BalancedTensor.idemPart k L (midGenIdem (k := k) Q Λc g)) :
    midSplitGen (Q := Q) (Λ := Λ) L ρ₁ g v =
      midSplitTriple (Q := Q) (Λ := Λ) L ρ₁ ((midTripleEquiv j hj ν ν₀).symm ⟨g, hcap⟩)
        ⟨v, mem_idemPart_symm g hcap v⟩ := by
  simp only [midSplitGen, LinearMap.coe_mk, AddHom.coe_mk, hcap, dite_true]

theorem midSplitGen_of_not [DecidableEq (MidBlockShuffle j hj ν ν₀)]
    (g : MidGen j hj ν ν₀) (hcap : ¬ IsCapGood ν₀ g.t)
    (v : BalancedTensor.idemPart k L (midGenIdem (k := k) Q Λc g)) :
    midSplitGen (Q := Q) (Λ := Λ) L ρ₁ g v = 0 := by
  simp only [midSplitGen, LinearMap.coe_mk, AddHom.coe_mk, hcap, dite_false]

variable {ρ₂ : Perm (Fin (Multiset.card (stendhalWeight 2 ν₀))) → List ℕ}
  {ρ₃ : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀)))) → List ℕ}

variable (L) in
/-- **The splitting map** `Φ : K̃^{λ⁺}_λ → ⨁_g T̃^λ e(s_g) ⊗_k L e(t_g)`,
`v γ_{(i, w, d, t, ε)} ↦ x^d ψ_{ρ w} e(i) ⊗ v`, through the basis of the model. -/
def midLeftSplit [DecidableEq (MidGen j hj ν ν₀)] [DecidableEq (MidBlockShuffle j hj ν ν₀)]
    (hQ : KLRSymm Q) (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w) :
    MidModel j hj Q Λ Λc ν ν₀ L →ₗ[k] Src :=
  (DFinsupp.lsum ℕ fun g => midSplitGen (Q := Q) (Λ := Λ) L ρ₁ g) ∘ₗ
    (midModelEquivₖ j hj Q Λ Λc ν ν₀ L ρ₃ hQ hρ₂ hρ₃).toLinearMap

theorem midModelEquivₖ_tmul [DecidableEq (MidGen j hj ν ν₀)] (hQ : KLRSymm Q)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w) (g : MidGen j hj ν ν₀)
    (v : BalancedTensor.idemPart k L (midGenIdem (k := k) Q Λc g)) :
    midModelEquivₖ j hj Q Λ Λc ν ν₀ L ρ₃ hQ hρ₂ hρ₃ (Ind.tmul (midGenCorner Q Λ Λc ρ₃ g) (v : L)) =
      (DFinsupp.single g v :
        Π₀ g, BalancedTensor.idemPart k L (midGenIdem (k := k) Q Λc g)) := by
  have h := midModelEquiv_symm_single (Λ := Λ) (L := L) hQ hρ₂ hρ₃ g ⟨(v : L), v.2⟩
  refine DFinsupp.ext fun g' => Subtype.ext ?_
  change ((midModelEquiv j hj Q Λ Λc ν ν₀ ρ₃ L hQ hρ₂ hρ₃ (Ind.tmul _ (v : L)) g' : L)) = _
  rw [← h, LinearEquiv.apply_symm_apply]
  by_cases hg : g = g'
  · subst hg; simp only [DFinsupp.single_eq_same]
  · simp only [DFinsupp.single_apply, hg, dite_false, ZeroMemClass.coe_zero]

theorem midLeftSplit_tmul [DecidableEq (MidGen j hj ν ν₀)]
    [DecidableEq (MidBlockShuffle j hj ν ν₀)] (hQ : KLRSymm Q)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w) (g : MidGen j hj ν ν₀)
    (v : BalancedTensor.idemPart k L (midGenIdem (k := k) Q Λc g)) :
    midLeftSplit (Q := Q) (Λ := Λ) L ρ₁ hQ hρ₂ hρ₃ (Ind.tmul (midGenCorner Q Λ Λc ρ₃ g) (v : L)) =
      midSplitGen (Q := Q) (Λ := Λ) L ρ₁ g v := by
  rw [midLeftSplit, LinearMap.comp_apply, LinearEquiv.coe_coe, midModelEquivₖ_tmul,
    DFinsupp.lsum_single]

/-! ### The splitting map commutes with the dots of `λ` -/

omit [DecidableEq I] in
theorem MidGen.addDots_congr {g g' : MidGen j hj ν ν₀} (h : g = g') (e : Fin m →₀ ℕ)
    (he : ∀ a ∈ e.support, (g.s.lbl a).isLeft) (he' : ∀ a ∈ e.support, (g'.s.lbl a).isLeft) :
    g.addDots e he = g'.addDots e he' := by
  subst h; rfl

omit [DecidableEq I] in
/-- The triple of a generator with dots added is the triple with the dots added. -/
theorem midTripleEquiv_symm_addDots (g : MidGen j hj ν ν₀) (hcap : IsCapGood ν₀ g.t)
    (e : Fin m →₀ ℕ) (he : ∀ a ∈ e.support, (g.s.lbl a).isLeft) :
    ∃ he' : ∀ a ∈ e.support,
        ((((midTripleEquiv j hj ν ν₀).symm ⟨g, hcap⟩).w •
          ((midTripleEquiv j hj ν ν₀).symm ⟨g, hcap⟩).i).lbl a).isLeft,
      (midTripleEquiv j hj ν ν₀).symm ⟨g.addDots e he, hcap⟩ =
        ((midTripleEquiv j hj ν ν₀).symm ⟨g, hcap⟩).addDots e he' := by
  set τ := (midTripleEquiv j hj ν ν₀).symm ⟨g, hcap⟩
  have hg : (MidTriple.toGen (hj := hj) τ).1 = g :=
    congrArg Subtype.val ((midTripleEquiv j hj ν ν₀).apply_symm_apply ⟨g, hcap⟩)
  have hs : τ.w • τ.i = g.s := congrArg MidGen.s hg
  refine ⟨fun a ha => hs ▸ he a ha, ?_⟩
  rw [Equiv.symm_apply_eq]
  refine Subtype.ext ?_
  change g.addDots e he = (MidTriple.toGen (hj := hj) (τ.addDots e _)).1
  rw [MidTriple.toGen_addDots]
  exact MidGen.addDots_congr hg.symm e _ _

theorem midSplitTriple_congr [DecidableEq (MidBlockShuffle j hj ν ν₀)]
    {τ τ' : MidTriple ℓ j ν ν₀} (h : τ = τ') (x : L)
    (hx : x ∈ BalancedTensor.idemPart k L
      (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) τ.t τ.ht))) :
    midSplitTriple (Q := Q) (Λ := Λ) (hj := hj) L ρ₁ τ ⟨x, hx⟩ =
      midSplitTriple (Q := Q) (Λ := Λ) (hj := hj) L ρ₁ τ' ⟨x, h ▸ hx⟩ := by
  subst h; rfl

theorem smul_midSplitTriple [DecidableEq (MidBlockShuffle j hj ν ν₀)] (a : T)
    (τ : MidTriple ℓ j ν ν₀)
    (x : BalancedTensor.idemPart k L
      (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) τ.t τ.ht))) :
    a • midSplitTriple (Q := Q) (Λ := Λ) (hj := hj) L ρ₁ τ x =
      DirectSum.lof T _ (fun g : MidBlockShuffle j hj ν ν₀ => MidLeftSummand Q Λ Λc L g.1)
        (τ.blockShuffle hj)
        ((a • (⟨topMap k Q Λ ν (τ.elt Q Λ ρ₁), topMap_elt_mem ρ₁ τ⟩ :
          Submodule.span T {StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λ)
            (τ.blockShuffle hj).1.1.s (τ.blockShuffle hj).1.1.hs})) ⊗ₜ x) := by
  change a • DirectSum.lof T _ (fun g : MidBlockShuffle j hj ν ν₀ => MidLeftSummand Q Λ Λc L g.1)
    (τ.blockShuffle hj) (_ ⊗ₜ x) = _
  rw [← LinearMap.map_smul]
  congr 1

/-- **The splitting map commutes with the dots on a generator.** -/
theorem midLeftSplit_polT_tmul [DecidableEq (MidGen j hj ν ν₀)]
    [DecidableEq (MidBlockShuffle j hj ν ν₀)] (hρ₁ : ∀ w, wordProd m (ρ₁ w) = w)
    {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}
    (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (hQ : KLRSymm Q)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w) (g : MidGen j hj ν ν₀)
    (e : Fin m →₀ ℕ) (v : BalancedTensor.idemPart k L (midGenIdem (k := k) Q Λc g)) :
    midLeftSplit (Q := Q) (Λ := Λ) L ρ₁ hQ hρ₂ hρ₃
        (midLeftAlg L hL hR (polT Q Λ ν (monomial e 1))
          (Ind.tmul (midGenCorner Q Λ Λc ρ₃ g) (v : L))) =
      polT Q Λ ν (monomial e 1) • midSplitGen (Q := Q) (Λ := Λ) L ρ₁ g v := by
  rw [midLeftAlg_polT_tmul_midGenCorner]
  by_cases hcap : IsCapGood ν₀ g.t
  swap
  · rw [midSplitGen_of_not ρ₁ g hcap, smul_zero]
    split_ifs with he
    · exact midLeftSplit_tmul (g := g.addDots e he) ρ₁ hQ hρ₂ hρ₃ v ▸
        midSplitGen_of_not ρ₁ (g.addDots e he) hcap v
    · exact map_zero _
  set τ := (midTripleEquiv j hj ν ν₀).symm ⟨g, hcap⟩ with hτdef
  have hg : (MidTriple.toGen (hj := hj) τ).1 = g :=
    congrArg Subtype.val ((midTripleEquiv j hj ν ν₀).apply_symm_apply ⟨g, hcap⟩)
  have hs : τ.w • τ.i = g.s := congrArg MidGen.s hg
  rw [midSplitGen_of_capGood ρ₁ g hcap, smul_midSplitTriple]
  have hsm : ∀ he : ∀ a ∈ e.support, ((τ.w • τ.i).lbl a).isLeft,
      (polT Q Λ ν (monomial e 1) • (⟨topMap k Q Λ ν (τ.elt Q Λ ρ₁), topMap_elt_mem ρ₁ τ⟩ :
        Submodule.span T {StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λ)
          (τ.blockShuffle hj).1.1.s (τ.blockShuffle hj).1.1.hs})) =
        ⟨topMap k Q Λ ν ((τ.addDots e he).elt Q Λ ρ₁), topMap_elt_mem ρ₁ (τ.addDots e he)⟩ :=
    fun he => Subtype.ext (by
      rw [Submodule.coe_smul, smul_eq_mul, polT_mul_topMap_elt ρ₁ hρ₁,
        dite_eq_left_of_eq_true (eq_true he)])
  split_ifs with he
  · rw [midLeftSplit_tmul (g := g.addDots e he) ρ₁ hQ hρ₂ hρ₃ v,
      midSplitGen_of_capGood ρ₁ (g.addDots e he) hcap]
    obtain ⟨he', hτ⟩ := midTripleEquiv_symm_addDots g hcap e he
    rw [midSplitTriple_congr ρ₁ hτ, hsm he']
    rfl
  · have he' : ¬ ∀ a ∈ e.support, ((τ.w • τ.i).lbl a).isLeft := fun h => he (hs ▸ h)
    have h0 : (polT Q Λ ν (monomial e 1) • (⟨topMap k Q Λ ν (τ.elt Q Λ ρ₁),
        topMap_elt_mem ρ₁ τ⟩ : Submodule.span T {StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λ)
          (τ.blockShuffle hj).1.1.s (τ.blockShuffle hj).1.1.hs})) = 0 :=
      Subtype.ext (by
        rw [Submodule.coe_smul, smul_eq_mul, polT_mul_topMap_elt ρ₁ hρ₁,
          dite_eq_right_of_eq_false (eq_false he')]; rfl)
    rw [h0, TensorProduct.zero_tmul, map_zero, map_zero]

/-- **The splitting map commutes with the dots of `λ`**. -/
theorem midLeftSplit_polT_smul [DecidableEq (MidGen j hj ν ν₀)]
    [DecidableEq (MidBlockShuffle j hj ν ν₀)] (hρ₁ : ∀ w, wordProd m (ρ₁ w) = w)
    {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}
    (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (hQ : KLRSymm Q)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w) (p : MvPolynomial (Fin m) k)
    (y : MidModel j hj Q Λ Λc ν ν₀ L) :
    midLeftSplit (Q := Q) (Λ := Λ) L ρ₁ hQ hρ₂ hρ₃ (midLeftAlg L hL hR (polT Q Λ ν p) y) =
      polT Q Λ ν p • midLeftSplit (Q := Q) (Λ := Λ) L ρ₁ hQ hρ₂ hρ₃ y := by
  have hmono : ∀ (e : Fin m →₀ ℕ) (y : MidModel j hj Q Λ Λc ν ν₀ L),
      midLeftSplit (Q := Q) (Λ := Λ) L ρ₁ hQ hρ₂ hρ₃
        (midLeftAlg L hL hR (polT Q Λ ν (monomial e 1)) y) =
      polT Q Λ ν (monomial e 1) • midLeftSplit (Q := Q) (Λ := Λ) L ρ₁ hQ hρ₂ hρ₃ y := by
    intro e y
    obtain ⟨f, rfl⟩ := (midModelEquivₖ j hj Q Λ Λc ν ν₀ L ρ₃ hQ hρ₂ hρ₃).symm.surjective y
    induction f using DFinsupp.induction with
    | h0 => rw [map_zero, map_zero, map_zero, smul_zero]
    | ha g v f _ _ ih =>
      have hsymm : (midModelEquivₖ j hj Q Λ Λc ν ν₀ L ρ₃ hQ hρ₂ hρ₃).symm (DFinsupp.single g v) =
          Ind.tmul (midGenCorner Q Λ Λc ρ₃ g) (v : L) :=
        (LinearEquiv.symm_apply_eq _).2 (midModelEquivₖ_tmul hQ hρ₂ hρ₃ g v).symm
      simp only [map_add, smul_add]
      rw [ih, hsymm, midLeftSplit_polT_tmul ρ₁ hρ₁ hR, midLeftSplit_tmul]
  induction p using MvPolynomial.induction_on' with
  | monomial e c =>
    rw [show (monomial e c : MvPolynomial (Fin m) k) = c • monomial e 1 by
      rw [smul_monomial, smul_eq_mul, mul_one], map_smul, map_smul, LinearMap.smul_apply,
      map_smul, hmono, smul_assoc]
  | add p q hp hq =>
    rw [map_add, map_add, LinearMap.add_apply, map_add, hp, hq, add_smul]

end Categorification.Stendhal.CupCap

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendIotaGen
import Categorification.WeightedKLR.Rigidity.CupCapMidLeftFreeBijective
import Categorification.Algebra.InductionAlongTensor

/-!
# `T̃^λ_{{i} + ν} e' ⊗_{T̃^λ_ν} K̃_ν → K̃_{{i} + ν}` is injective

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the part for `𝔈_i`, for `j < ℓ`, at the level of the models. The
multiplication

  `μ : T̃^λ_{{i} + ν} e' ⊗_{T̃^λ_ν} K̃_ν → K̃_{{i} + ν}`, `a ⊗ y ↦ a · ι(y)`,

(`CupCap.appendIotaMul`, the induction along appending the black strand `i` on the right) is
injective (`CupCap.appendIotaMul_injective`). Its image is `K̃_{{i} + ν} e'⁺`
(`CupCap.appendBlackPlusOp_one_smul_mem_span_appendIota`).

The argument goes through the left freeness of the models (`CupCap.midThetaBlock_bijective`):
the induced module is spanned by the elements `a ⊗ v γ_g` over the block generators `g` at `ν`,
with `a ∈ T̃^λ_{{i} + ν} e(s_g i)`, and `μ` sends them to `a · v γ_{g i}`, the basis of
`K̃_{{i} + ν}` over the block generators `g i`, which are pairwise distinct.

Route hypotheses (tracked): each piece `L e(t)` is finitely generated over `k`, `Q` is
symmetric, the cup scalars are units and `L` satisfies the pull-off identity, as for
`CupCap.midThetaBlock_bijective`. The tilde coset filtration of `K̃_{{i} + ν} e'⁺` would
remove the finite generation.

## Main definitions

* `CupCap.appendIotaMul`, `CupCap.appendBlock`.

## Main results

* `CupCap.appendIotaMul_tmul`, `CupCap.appendBlock_injective`.
* `CupCap.appendIotaMul_injective`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA Equiv MulOpposite InductionAlong TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} (ν : Multiset I) {ν₀ : Multiset I} (i : I)

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "T" => StendhalAlgebra k Q Λ ν
local notation "Tᵢ" => StendhalAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν)
local notation "aB" => (appendBlackStendhal Q Λ i ν : StendhalAlgebra k Q Λ ν →ₙ+*
  StendhalAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν))

/-! ### The block generators `g i` -/

variable (h : j < ℓ)

/-- **The appended block generator** `g i` at `{i} + ν` of a block generator `g` at `ν`. -/
def appendBlock (g : MidBlockShuffle j hj ν ν₀) : MidBlockShuffle j hj νᵢ ν₀ :=
  ⟨⟨g.1.1.appendExt ν i h, rfl⟩, g.1.1.appendExt_perm ν i h g.2⟩

omit [DecidableEq I] in
theorem appendBlackLoading_inj {s s' : Seq (stendhalWeight ℓ ν)}
    (hs : appendBlackLoading i ν s = appendBlackLoading i ν s') : s = s' :=
  Subtype.ext (funext fun a => by
    have hm := card_appendBlackWeight (ℓ := ℓ) (ν := ν) (i := i)
    have h1 := appendBlackLoading_lbl_of_lt i ν s ⟨a.val, by omega⟩ a.2
    have h2 := appendBlackLoading_lbl_of_lt i ν s' ⟨a.val, by omega⟩ a.2
    rw [hs, h2] at h1
    exact h1.symm)

/-- The appended block generators are pairwise distinct. -/
theorem appendBlock_injective : Function.Injective (appendBlock (ν₀ := ν₀) (hj := hj) ν i h) := by
  intro g g' hg
  have h1 := congrArg (fun g => g.1.1) hg
  simp only [appendBlock] at h1
  have hs : g.1.1.s = g'.1.1.s := appendBlackLoading_inj ν i (congrArg MidGen.s h1)
  have ht : g.1.1.t = g'.1.1.t := congrArg (fun x => x.t) h1
  have hu : g.1.1.u = g'.1.1.u := extPerm_injective (card_plus_appendBlack (ℓ := ℓ)
    (ν₀ := ν₀) ν i) (congrArg MidGen.u h1)
  exact Subtype.ext (Subtype.ext (MidGen.ext' hs ht (g.1.2.trans g'.1.2.symm) hu))

/-! ### The multiplication map -/

variable {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}
  (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
  (hR' : MidKLRRel j hj Q Λ Λc ((Singleton.singleton i : Multiset I) + ν) ν₀ L hL)

/-- **The multiplication** `T̃^λ_{{i} + ν} e' ⊗_{T̃^λ_ν} K̃_ν → K̃_{{i} + ν}`,
`a ⊗ y ↦ a · ι(y)`, in the models, for `j < ℓ`. -/
def appendIotaMul : IndK k (MidLeftModel L hL hR) aB →ₗ[Tᵢ] MidLeftModel L hL hR' :=
  Ind.lift (fun z y => (midLeftAlg L hL hR' z.1 (appendIota ν i L h y) :
      MidLeftModel L hL hR'))
    (fun z z' y => by rw [Submodule.coe_add, map_add, LinearMap.add_apply]; rfl)
    (fun z y y' => (congrArg (midLeftAlg L hL hR' z.1) (appendIota_add ν i h y y')).trans
      (map_add _ _ _))
    (fun z a y => by
      change midLeftAlg L hL hR' (z.1 * aB a) (appendIota ν i L h y) =
        midLeftAlg L hL hR' z.1 (appendIota ν i L h (midLeftAlg L hL hR a y))
      rw [map_mul, Module.End.mul_apply]
      exact congrArg _ (appendIota_midLeftAlg ν i h hR hR' a y).symm)
    (fun b z y => by
      change midLeftAlg L hL hR' (b * z.1) (appendIota ν i L h y) =
        midLeftAlg L hL hR' b (midLeftAlg L hL hR' z.1 (appendIota ν i L h y))
      rw [map_mul, Module.End.mul_apply])

omit [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
theorem appendIotaMul_tmul (z : Corner aB) (y : MidLeftModel L hL hR) :
    appendIotaMul ν i h hR hR' (IndK.tmul z y) =
      (midLeftAlg L hL hR' z.1 (appendIota ν i L h y) : MidLeftModel L hL hR') :=
  rfl

/-! ### The spanning map of the induced module -/

theorem appendIndK_add_tmul {N : Type} [AddCommGroup N] [Module T N] (z z' : Corner aB) (n : N) :
    (IndK.tmul (k := k) (z + z') n : IndK k N aB) = IndK.tmul z n + IndK.tmul z' n :=
  Ind.add_tmul z z' n

theorem appendIndK_smul_tmul {N : Type} [AddCommGroup N] [Module T N] (b : Tᵢ) (z : Corner aB)
    (n : N) : (IndK.tmul (k := k) (b • z) n : IndK k N aB) = b • IndK.tmul z n :=
  (Ind.smul_tmul b z n).symm

theorem mem_corner_of_mem_span (g : MidBlockShuffle j hj ν ν₀)
    (a : Submodule.span Tᵢ {StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λ)
      (appendBlock ν i h g).1.1.s (appendBlock ν i h g).1.1.hs}) :
    (a : Tᵢ) ∈ lIdeal (aB 1) := by
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 a.2
  change (a : Tᵢ) * aB 1 = a
  rw [← hb, smul_eq_mul, mul_assoc]
  congr 1
  have he : StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λ) (appendBlock ν i h g).1.1.s
      (appendBlock ν i h g).1.1.hs =
      appendBlackStendhal Q Λ i ν (StendhalAlgebra.e g.1.1.s g.1.1.hs) :=
    (appendBlackStendhal_e Q Λ i ν g.1.1.s g.1.1.hs).symm
  rw [he]
  exact (map_mul (appendBlackStendhal Q Λ i ν) _ _).symm.trans (by rw [mul_one])

/-- The element `v γ_g` of the model at `ν`, for `v ∈ L e(t_{g i})`. -/
def appendGenLin (g : MidBlockShuffle j hj ν ν₀) :
    BalancedTensor.idemPart k L (midGenIdem (k := k) Q Λc (appendBlock ν i h g).1.1) →ₗ[k]
      MidLeftModel L hL hR where
  toFun v := (Ind.tmul (midGenCorner Q Λ Λc (canWord M) g.1.1) (v : L) :
    MidModel j hj Q Λ Λc ν ν₀ L)
  map_add' v v' := by
    rw [Submodule.coe_add, Ind.tmul_add]
    rfl
  map_smul' c v := by
    rw [Submodule.coe_smul, ← smul_tmul_midModel]
    rfl

/-- The bilinear map `(a, v) ↦ a ⊗ v γ_g` of a summand. -/
def appendSpanBil (g : MidBlockShuffle j hj ν ν₀) :
    Submodule.span Tᵢ {StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λ)
        (appendBlock ν i h g).1.1.s (appendBlock ν i h g).1.1.hs} →ₗ[Tᵢ]
      BalancedTensor.idemPart k L (midGenIdem (k := k) Q Λc (appendBlock ν i h g).1.1) →ₗ[k]
        IndK k (MidLeftModel L hL hR) aB :=
  LinearMap.mk₂' Tᵢ k
    (fun a v => IndK.tmul ⟨a, mem_corner_of_mem_span ν i h g a⟩
      (appendGenLin ν i h hR g v))
    (fun a a' v => by
      have := appendIndK_add_tmul ν i (k := k) (⟨a, mem_corner_of_mem_span ν i h g a⟩ : Corner aB)
        ⟨a', mem_corner_of_mem_span ν i h g a'⟩ (appendGenLin ν i h hR g v)
      exact this)
    (fun c a v => by
      have := appendIndK_smul_tmul ν i (k := k) c
        (⟨a, mem_corner_of_mem_span ν i h g a⟩ : Corner aB)
        (appendGenLin ν i h hR g v)
      exact this)
    (fun a v v' => by rw [map_add]; exact Ind.tmul_add _ _ _)
    (fun c a v => by
      rw [map_smul]
      exact Ind.tmul_algebraMap_smul k (fun c t => map_smul (appendBlackStendhal Q Λ i ν) c t)
        _ c _)

variable (L hL) in
/-- **The spanning map** `⨁_g T̃^λ_{{i} + ν} e(s_g i) ⊗_k L e(t_g) → T̃^λ_{{i} + ν} e' ⊗ K̃_ν`,
`a ⊗ v ↦ a ⊗ v γ_g`, over the block generators `g` at `ν`. -/
def appendSpan [DecidableEq (MidBlockShuffle j hj ν ν₀)] :
    (DirectSum (MidBlockShuffle j hj ν ν₀) fun g =>
        MidLeftSummand Q Λ Λc L (appendBlock ν i h g).1) →ₗ[Tᵢ]
      IndK k (MidLeftModel L hL hR) aB :=
  DirectSum.toModule Tᵢ _ _ fun g => AlgebraTensorModule.lift (appendSpanBil ν i h hR g)

variable (L) in
/-- The inclusion of the summands of the block generators `g i`. -/
def appendBlockIncl [DecidableEq (MidBlockShuffle j hj ν ν₀)]
    [DecidableEq (MidBlockShuffle j hj νᵢ ν₀)] :
    (DirectSum (MidBlockShuffle j hj ν ν₀) fun g =>
        MidLeftSummand Q Λ Λc L (appendBlock ν i h g).1) →ₗ[Tᵢ]
      DirectSum (MidBlockShuffle j hj νᵢ ν₀) fun g => MidLeftSummand Q Λ Λc L g.1 :=
  DirectSum.toModule Tᵢ (MidBlockShuffle j hj ν ν₀)
    (DirectSum (MidBlockShuffle j hj νᵢ ν₀) fun g => MidLeftSummand Q Λ Λc L g.1) fun g =>
      DirectSum.lof Tᵢ (MidBlockShuffle j hj νᵢ ν₀) (fun g => MidLeftSummand Q Λ Λc L g.1)
        (appendBlock ν i h g)

theorem appendBlockIncl_injective [DecidableEq (MidBlockShuffle j hj ν ν₀)]
    [DecidableEq (MidBlockShuffle j hj νᵢ ν₀)] :
    Function.Injective
      (appendBlockIncl (Q := Q) (Λ := Λ) (Λc := Λc) (hj := hj) (ν₀ := ν₀) ν i h L) := by
  have key : ∀ (x : DirectSum (MidBlockShuffle j hj ν ν₀) fun g =>
      MidLeftSummand Q Λ Λc L (appendBlock ν i h g).1) (g : MidBlockShuffle j hj ν ν₀),
      DirectSum.component Tᵢ _ (fun g => MidLeftSummand Q Λ Λc L g.1) (appendBlock ν i h g)
          (appendBlockIncl ν i h L x) = DirectSum.component Tᵢ _ _ g x := by
    intro x g
    induction x using DirectSum.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | of g' y =>
      rw [← DirectSum.lof_eq_of Tᵢ, appendBlockIncl, DirectSum.toModule_lof]
      by_cases hg : g' = g
      · subst hg
        rw [DirectSum.component.lof_self, DirectSum.component.lof_self]
      · have hg' : appendBlock ν i h g' ≠ appendBlock ν i h g :=
          fun he => hg (appendBlock_injective ν i h he)
        rw [DirectSum.component.of, DirectSum.component.of]
        simp only [hg, hg', ↓reduceDIte]
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  intro x x' hxx'
  refine DirectSum.ext_component Tᵢ fun g => ?_
  rw [← key, ← key, hxx']

/-! ### Surjectivity of the spanning map -/

theorem tmul_midGenCorner_mem_range_appendSpan [DecidableEq (MidBlockShuffle j hj ν ν₀)]
    (z : Corner aB) (g : MidBlockShuffle j hj ν ν₀)
    (v : BalancedTensor.idemPart k L (midGenIdem (k := k) Q Λc (appendBlock ν i h g).1.1)) :
    (IndK.tmul z (Ind.tmul (midGenCorner Q Λ Λc (canWord M) g.1.1) (v : L) :
        MidLeftModel L hL hR) : IndK k (MidLeftModel L hL hR) aB) ∈
      LinearMap.range (appendSpan ν i h L hL hR) := by
  have hmem : z.1 * StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λ)
      (appendBlock ν i h g).1.1.s (appendBlock ν i h g).1.1.hs ∈
        Submodule.span Tᵢ {StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λ)
          (appendBlock ν i h g).1.1.s (appendBlock ν i h g).1.1.hs} :=
    Submodule.smul_mem _ z.1 (Submodule.mem_span_singleton_self _)
  refine ⟨DirectSum.lof Tᵢ _ (fun g => MidLeftSummand Q Λ Λc L (appendBlock ν i h g).1) g
    (⟨_, hmem⟩ ⊗ₜ v), ?_⟩
  rw [appendSpan, DirectSum.toModule_lof, AlgebraTensorModule.lift_tmul]
  change (Ind.tmul _ (Ind.tmul (midGenCorner Q Λ Λc (canWord M) g.1.1) (v : L) :
      MidModel j hj Q Λ Λc ν ν₀ L) : Ind (MidLeftModel L hL hR) aB) = _
  conv_rhs => rw [← midLeftAlg_e_tmul_midGenCorner hR g.1.1 (v : L)]
  refine Eq.trans ?_ (Ind.op_smul_tmul (N := MidLeftModel L hL hR) z
    (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λ) g.1.1.s g.1.1.hs) _)
  congr 1
  apply Subtype.ext
  change z.1 * StendhalAlgebra.e _ _ =
    z.1 * appendBlackStendhal Q Λ i ν (StendhalAlgebra.e g.1.1.s g.1.1.hs)
  rw [appendBlackStendhal_e]
  rfl

/-- **The spanning map is surjective**: `T̃^λ_{{i} + ν} e' ⊗ K̃_ν` is spanned by the elements
`a ⊗ v γ_g`, `a ∈ T̃^λ_{{i} + ν} e(s_g i)`, over the block generators `g` at `ν`, when the cup
scalars are units and `L` satisfies the pull-off identity. -/
theorem appendSpan_surjective [DecidableEq (MidBlockShuffle j hj ν ν₀)]
    (hP : PullOff k Q Λc ν₀ L) (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i')) :
    Function.Surjective (appendSpan ν i h L hL hR) := by
  have hρ : ∀ w, IsReduced M (canWord M w) ∧ wordProd M (canWord M w) = w :=
    fun w => ⟨isReduced_canWord M w, wordProd_canWord M w⟩
  have hΘ := midThetaBlock_surjective hR (canWord M) hρ hP hκ
  intro x
  refine Ind.induction_on (motive := fun x : Ind (MidLeftModel L hL hR) aB =>
    (x : IndK k (MidLeftModel L hL hR) aB) ∈ LinearMap.range (appendSpan ν i h L hL hR)) x
    (zero_mem _) (fun z y => ?_) (fun _ _ h h' => add_mem h h')
  obtain ⟨w, rfl⟩ := hΘ y
  induction w using DirectSum.induction_on with
  | zero =>
    rw [map_zero]
    exact (congrArg (· ∈ LinearMap.range (appendSpan ν i h L hL hR))
      (Ind.tmul_zero (N := MidLeftModel L hL hR) z)).mpr (zero_mem _)
  | add w w' hw hw' =>
    rw [map_add]
    exact (congrArg (· ∈ LinearMap.range (appendSpan ν i h L hL hR))
      (Ind.tmul_add (N := MidLeftModel L hL hR) z _ _)).mpr (add_mem hw hw')
  | of g t =>
    induction t using TensorProduct.inductionOn with
    | add t t' ht ht' =>
      rw [map_add, map_add]
      exact (congrArg (· ∈ LinearMap.range (appendSpan ν i h L hL hR))
        (Ind.tmul_add (N := MidLeftModel L hL hR) z _ _)).mpr (add_mem ht ht')
    | tmul a v =>
      have he : midThetaBlock L hL (canWord M) hR (DirectSum.of _ g (a ⊗ₜ v)) =
          (midLeftAlg L hL hR (a : T)
            (Ind.tmul (midGenCorner Q Λ Λc (canWord M) g.1.1) (v : L)) :
            MidLeftModel L hL hR) := by
        rw [← DirectSum.lof_eq_of T, midThetaBlock, DirectSum.toModule_lof,
          AlgebraTensorModule.lift_tmul]
        rfl
      rw [he]
      have h2 := (Ind.op_smul_tmul (N := MidLeftModel L hL hR) z (a : T)
        (Ind.tmul (midGenCorner Q Λ Λc (canWord M) g.1.1) (v : L) :
          MidModel j hj Q Λ Λc ν ν₀ L)).symm
      exact (congrArg (· ∈ LinearMap.range (appendSpan ν i h L hL hR)) h2).mpr
        (tmul_midGenCorner_mem_range_appendSpan ν i h hR _ g v)

/-! ### Injectivity -/

/-- `μ` on the spanning set is the comparison map at `{i} + ν` on the summands of the block
generators `g i`. -/
theorem appendIotaMul_comp_appendSpan [DecidableEq (MidBlockShuffle j hj ν ν₀)]
    [DecidableEq (MidBlockShuffle j hj νᵢ ν₀)] :
    appendIotaMul ν i h hR hR' ∘ₗ appendSpan ν i h L hL hR =
      midThetaBlock L hL (appendWords ν i) hR' ∘ₗ appendBlockIncl ν i h L := by
  refine DirectSum.linearMap_ext Tᵢ fun g => AlgebraTensorModule.ext fun a v => ?_
  simp only [LinearMap.comp_apply]
  rw [appendSpan, DirectSum.toModule_lof, AlgebraTensorModule.lift_tmul, appendBlockIncl,
    DirectSum.toModule_lof, midThetaBlock, DirectSum.toModule_lof,
    AlgebraTensorModule.lift_tmul]
  change (midLeftAlg L hL hR' (a : Tᵢ)
      (appendIota ν i L h (Ind.tmul (midGenCorner Q Λ Λc (canWord M) g.1.1) (v : L))) :
      MidLeftModel L hL hR') = midLeftAlg L hL hR' (a : Tᵢ)
      (Ind.tmul (midGenCorner Q Λ Λc (appendWords ν i) (g.1.1.appendExt ν i h)) (v : L))
  rw [appendIota_tmul_midGenCorner ν i h g.1.1 g.1.2]

/-- **`T̃^λ_{{i} + ν} e' ⊗_{T̃^λ_ν} K̃_ν → K̃_{{i} + ν}` is injective** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21, the part for `𝔈_i`), for `j < ℓ`, in the
models.

Route hypotheses (tracked): each piece `L e(t)` finitely generated over `k` (`hfin`), `Q`
symmetric, the cup scalars units and the pull-off identity, as for
`midThetaBlock_bijective`. -/
theorem appendIotaMul_injective (hQ : KLRSymm Q) (hP : PullOff k Q Λc ν₀ L)
    (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i'))
    (hfin : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Finite k
      (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht)))) :
    Function.Injective (appendIotaMul ν i h hR hR') := by
  classical
  intro x x' hxx'
  obtain ⟨w, rfl⟩ := appendSpan_surjective ν i h hR hP hκ x
  obtain ⟨w', rfl⟩ := appendSpan_surjective ν i h hR hP hκ x'
  have hc := LinearMap.congr_fun (appendIotaMul_comp_appendSpan ν i h hR hR')
  have e1 := hc w
  have e2 := hc w'
  simp only [LinearMap.comp_apply] at e1 e2
  rw [e1, e2] at hxx'
  exact congrArg _ (appendBlockIncl_injective ν i h
    ((midThetaBlock_bijective hR' hQ (appendWords_spec ν i) hP hκ hfin).1 hxx'))

end Categorification.Stendhal.CupCap

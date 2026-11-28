/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendTopIotaInj

/-!
# The violated parts under `T̃^λ_{{i} + ν} e' ⊗ K̃_ν ≅ K̃_{{i} + ν} e'⁺`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the part for `𝔈_i`. The multiplication `μ : T̃^λ_{{i} + ν} e' ⊗ K̃_ν →
K̃_{{i} + ν}`, `a ⊗ y ↦ a · ι(y)`, is injective with image `K̃_{{i} + ν} e'⁺`. Under it, the
elements sent into the bottom-violated part `K̃_{{i} + ν} · V_{λ⁺}` are exactly the span of the
`a · x` with `a` in the violating ideal of `T̃^λ_{{i} + ν}`
(`CupCap.appendIotaMul_mem_midBotViolSub_iff` for `j < ℓ`,
`CupCap.appendTopIotaMul_mem_midBotViolSub_iff` for `j = ℓ`). Passing to the quotients
`K = K̃ / K̃ · V_{λ⁺}` and `T^λ = T̃^λ / V_λ`, this is the injectivity of
`T^λ_{{i} + ν} e' ⊗ K_ν → K_{{i} + ν} e'⁺`.

The argument is general (`CupCap.mem_midBotViolSub_iff_mem_leftViolSub`): the bottom-violated
part of the model is its top-violated part (`CupCap.midLeftAlg_mem_midBotViolSub`,
`CupCap.op_smul_mem_midViolatedSub`), the actions on the two sides commute, and an injective
left linear map onto the `e'⁺`-part identifies the top-violated parts.

Route hypotheses (tracked), as for the injectivity of `μ` (`CupCap.appendIotaMul_injective`):
each piece `L e(t)` finitely generated over `k`, `Q` symmetric, the cup scalars units and the
pull-off identities.

## Main definitions

* `CupCap.leftViolSub`: the span of the `a · x`, `a` in the violating ideal of `T̃^λ`.

## Main results

* `CupCap.mem_midBotViolSub_iff_mem_leftViolSub`.
* `CupCap.appendIotaMul_mem_midBotViolSub_iff`, `CupCap.appendTopIotaMul_mem_midBotViolSub_iff`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA Equiv MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ}

section General

variable {ν ν₀ : Multiset I}

local notation "T" => StendhalAlgebra k Q Λ ν
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))

variable (k Q Λ ν) in
/-- **The violated part of a left `T̃^λ`-module**: the span of the `a · x` with `a` in the
violating ideal of `T̃^λ`. -/
def leftViolSub (X : Type*) [AddCommGroup X] [Module T X] : Submodule T X :=
  Submodule.span T {x | ∃ a ∈ StendhalAlgebra.violatedIdeal k Q Λ ν, ∃ y : X, x = a • y}

theorem smul_mem_leftViolSub {X : Type*} [AddCommGroup X] [Module T X] {a : T}
    (ha : a ∈ StendhalAlgebra.violatedIdeal k Q Λ ν) (y : X) :
    a • y ∈ leftViolSub k Q Λ ν X :=
  Submodule.subset_span ⟨a, ha, y, rfl⟩

variable {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}

/-- **An injective left linear map onto the `e`-part identifies the violated parts**: for `μ`
injective, with image fixed by the right action of `e` and containing every `y · e`, an element
`μ(x)` lies in the bottom-violated part of the model iff `x` lies in the violated part. -/
theorem mem_midBotViolSub_iff_mem_leftViolSub (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
    (hP : PullOff k Q Λc ν₀ L) (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))
    {X : Type*} [AddCommGroup X] [Module T X] (μ : X →ₗ[T] MidLeftModel L hL hR)
    (hμ : Function.Injective μ) (e : Tpᵐᵒᵖ) (hfix : ∀ x, e • μ x = μ x)
    (hsurj : ∀ y : MidLeftModel L hL hR, ∃ x, μ x = e • y) (x : X) :
    (μ x : MidModel j hj Q Λ Λc ν ν₀ L) ∈ midBotViolSub Q Λ Λc j hj ν ν₀ L ↔
      x ∈ leftViolSub k Q Λ ν X := by
  classical
  constructor
  · intro hx
    have hBV : ∀ z ∈ midBotViolSub Q Λ Λc j hj ν ν₀ L,
        (show MidLeftModel L hL hR from z) ∈ midViolatedSub L hL hR := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨b, hb, w, rfl⟩ := hz
        exact op_smul_mem_midViolatedSub hR
          (fun w => ⟨isReduced_canWord M w, wordProd_canWord M w⟩) hP hκ hb w
      | zero => exact zero_mem _
      | add z z' _ _ hz hz' => exact add_mem hz hz'
      | smul c z _ hz => exact midRightLin_mem_midViolatedSub hR c hz
    have key : ∀ z ∈ midViolatedSub L hL hR,
        ∃ x' ∈ leftViolSub k Q Λ ν X, μ x' = e • z := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨a, ha, y, rfl⟩ := hz
        obtain ⟨x₀, hx₀⟩ := hsurj y
        refine ⟨a • x₀, smul_mem_leftViolSub ha x₀, ?_⟩
        rw [map_smul, hx₀]
        exact ((midRightLin L hL hR e).map_smul a y).symm
      | zero => exact ⟨0, zero_mem _, by rw [map_zero, smul_zero]⟩
      | add z z' _ _ hz hz' =>
        obtain ⟨x₁, hx₁, h₁⟩ := hz
        obtain ⟨x₂, hx₂, h₂⟩ := hz'
        exact ⟨x₁ + x₂, add_mem hx₁ hx₂, by rw [map_add, h₁, h₂, smul_add]⟩
      | smul c z _ hz =>
        obtain ⟨x₁, hx₁, h₁⟩ := hz
        refine ⟨c • x₁, Submodule.smul_mem _ c hx₁, ?_⟩
        rw [map_smul, h₁]
        exact ((midRightLin L hL hR e).map_smul c z).symm
    obtain ⟨x', hx', he⟩ := key _ (hBV _ hx)
    rw [hfix] at he
    rwa [← hμ he]
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, y, rfl⟩ := hx
      rw [map_smul]
      exact midLeftAlg_mem_midBotViolSub ν hL hR ha (μ y)
    | zero => rw [map_zero]; exact zero_mem _
    | add x x' _ _ hx hx' => rw [map_add]; exact add_mem hx hx'
    | smul c x _ hx =>
      rw [map_smul]
      exact midLeftAlg_mem_midBotViolSub_of_mem hR c hx

end General

variable (ν : Multiset I) {ν₀ : Multiset I} (i : I)

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "Tᵢ" => StendhalAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν)
local notation "aB" => (appendBlackStendhal Q Λ i ν : StendhalAlgebra k Q Λ ν →ₙ+*
  StendhalAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν))
local notation "φ⁺" => appendBlackPlusOp Q Λ Λc j hj ν ν₀ i

variable {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}
  (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
  (hR' : MidKLRRel j hj Q Λ Λc ((Singleton.singleton i : Multiset I) + ν) ν₀ L hL)

section Mid

variable (h : j < ℓ)

omit [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
/-- The image of `μ` is fixed by `e'⁺`, for `j < ℓ`. -/
theorem appendIotaMul_fix (x : IndK k (MidLeftModel L hL hR) aB) :
    φ⁺ 1 • appendIotaMul ν i h hR hR' x = appendIotaMul ν i h hR hR' x := by
  refine Ind.induction_on (motive := fun x : Ind (MidLeftModel L hL hR) aB =>
    φ⁺ 1 • appendIotaMul ν i h hR hR' (x : IndK k (MidLeftModel L hL hR) aB) =
      appendIotaMul ν i h hR hR' x) x ?_ (fun z y => ?_) (fun s t hs ht => ?_)
  · change φ⁺ 1 • appendIotaMul ν i h hR hR' 0 = appendIotaMul ν i h hR hR' 0
    rw [map_zero, smul_zero]
  · change φ⁺ 1 • midLeftAlg L hL hR' z.1 (appendIota ν i L h y) =
      midLeftAlg L hL hR' z.1 (appendIota ν i L h y)
    rw [← midLeftAlg_smul]
    exact congrArg _ ((appendIota_smul ν i h 1 y).symm.trans (congrArg _ (one_smul _ y)))
  · exact (congrArg (φ⁺ 1 • ·) (map_add (appendIotaMul ν i h hR hR') s t)).trans
      ((smul_add _ _ _).trans ((congrArg₂ (· + ·) hs ht).trans (map_add _ s t).symm))

/-- Every `y e'⁺` is in the image of `μ`, for `j < ℓ`. -/
theorem appendIotaMul_surj (hP : PullOff k Q Λc ν₀ L) (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i'))
    (y : MidLeftModel L hL hR') :
    ∃ x, appendIotaMul ν i h hR hR' x = φ⁺ 1 • y := by
  have hy := appendBlackPlusOp_one_smul_mem_span_appendIota ν i h hR' hP hκ y
  have hle : Submodule.span Tᵢ (Set.range fun x : MidModel j hj Q Λ Λc ν ν₀ L =>
      toMidLeftModel ν i hR' (appendIota ν i L h x)) ≤
        LinearMap.range (appendIotaMul ν i h hR hR') := by
    rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    refine ⟨IndK.tmul (unitGen aB) x, ?_⟩
    change midLeftAlg L hL hR' (aB 1) (appendIota ν i L h x) = appendIota ν i L h x
    exact (appendIota_midLeftAlg ν i h hR hR' 1 x).symm.trans (by rw [map_one]; rfl)
  exact hle hy

/-- **The violated parts under `T̃^λ_{{i} + ν} e' ⊗ K̃_ν ≅ K̃_{{i} + ν} e'⁺`** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21, the part for `𝔈_i`), for `j < ℓ`: `μ(x)`
lies in the bottom-violated part `K̃_{{i} + ν} · V_{λ⁺}` iff `x` lies in the span of the `a · x'`
with `a` in the violating ideal of `T̃^λ_{{i} + ν}`.

Route hypotheses (tracked), as for `CupCap.appendIotaMul_injective`: each piece `L e(t)`
finitely generated over `k` (`hfin`), `Q` symmetric, the cup scalars units and the pull-off
identity. -/
theorem appendIotaMul_mem_midBotViolSub_iff (hQ : KLRSymm Q) (hP : PullOff k Q Λc ν₀ L)
    (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i'))
    (hfin : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Finite k
      (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht))))
    (x : IndK k (MidLeftModel L hL hR) aB) :
    (appendIotaMul ν i h hR hR' x : MidModel j hj Q Λ Λc νᵢ ν₀ L) ∈
        midBotViolSub Q Λ Λc j hj νᵢ ν₀ L ↔
      x ∈ leftViolSub k Q Λ νᵢ (IndK k (MidLeftModel L hL hR) aB) :=
  mem_midBotViolSub_iff_mem_leftViolSub hR' hP hκ (appendIotaMul ν i h hR hR')
    (appendIotaMul_injective ν i h hR hR' hQ hP hκ hfin) (φ⁺ 1)
    (appendIotaMul_fix ν i hR hR' h) (appendIotaMul_surj ν i hR hR' h hP hκ) x

end Mid

section Top

variable (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
  (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i')) (h : ¬ j < ℓ)

omit [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
/-- The image of `μ` is fixed by `e'⁺`, for `j = ℓ`. -/
theorem appendTopIotaMul_fix (x : IndK k (MidLeftModel L hL hR) aB) :
    φ⁺ 1 • appendTopIotaMul ν i h hR hR' hP hPL hκ x =
      appendTopIotaMul ν i h hR hR' hP hPL hκ x := by
  refine Ind.induction_on (motive := fun x : Ind (MidLeftModel L hL hR) aB =>
    φ⁺ 1 • appendTopIotaMul ν i h hR hR' hP hPL hκ (x : IndK k (MidLeftModel L hL hR) aB) =
      appendTopIotaMul ν i h hR hR' hP hPL hκ x) x ?_ (fun z y => ?_) (fun s t hs ht => ?_)
  · change φ⁺ 1 • appendTopIotaMul ν i h hR hR' hP hPL hκ 0 =
      appendTopIotaMul ν i h hR hR' hP hPL hκ 0
    rw [map_zero, smul_zero]
  · change φ⁺ 1 • midLeftAlg L hL hR' z.1 (appendTopIota ν i hP hPL hL hκ h y) =
      midLeftAlg L hL hR' z.1 (appendTopIota ν i hP hPL hL hκ h y)
    rw [← midLeftAlg_smul]
    exact congrArg _ ((appendTopIota_smul ν i hP hPL hL hκ h 1 y).symm.trans
      (congrArg _ (one_smul _ y)))
  · exact (congrArg (φ⁺ 1 • ·) (map_add (appendTopIotaMul ν i h hR hR' hP hPL hκ) s t)).trans
      ((smul_add _ _ _).trans ((congrArg₂ (· + ·) hs ht).trans (map_add _ s t).symm))

/-- Every `y e'⁺` is in the image of `μ`, for `j = ℓ`. -/
theorem appendTopIotaMul_surj (y : MidLeftModel L hL hR') :
    ∃ x, appendTopIotaMul ν i h hR hR' hP hPL hκ x = φ⁺ 1 • y := by
  have hy := appendBlackPlusOp_one_smul_mem_span_appendTopIota ν i hP hPL hL hκ h hR' y
  have hle : Submodule.span Tᵢ (Set.range fun x : MidModel j hj Q Λ Λc ν ν₀ L =>
      toMidLeftModel ν i hR' (appendTopIota ν i hP hPL hL hκ h x)) ≤
        LinearMap.range (appendTopIotaMul ν i h hR hR' hP hPL hκ) := by
    rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    refine ⟨IndK.tmul (unitGen aB) x, ?_⟩
    change midLeftAlg L hL hR' (aB 1) (appendTopIota ν i hP hPL hL hκ h x) =
      appendTopIota ν i hP hPL hL hκ h x
    exact (appendTopIota_midLeftAlg ν i hP hPL hL hκ h hR hR' 1 x).symm.trans
      (by rw [map_one]; rfl)
  exact hle hy

/-- **The violated parts under `T̃^λ_{{i} + ν} e' ⊗ K̃_ν ≅ K̃_{{i} + ν} e'⁺`** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21, the part for `𝔈_i`), for `j = ℓ`: `μ(x)`
lies in the bottom-violated part `K̃_{{i} + ν} · V_{λ⁺}` iff `x` lies in the span of the `a · x'`
with `a` in the violating ideal of `T̃^λ_{{i} + ν}`.

Route hypotheses (tracked), as for `CupCap.appendTopIotaMul_injective`: each piece `L e(t)`
finitely generated over `k` (`hfin`), `Q` symmetric, the cup scalars units and the pull-off
identities. -/
theorem appendTopIotaMul_mem_midBotViolSub_iff (hQ : KLRSymm Q)
    (hfin : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Finite k
      (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht))))
    (x : IndK k (MidLeftModel L hL hR) aB) :
    (appendTopIotaMul ν i h hR hR' hP hPL hκ x : MidModel j hj Q Λ Λc νᵢ ν₀ L) ∈
        midBotViolSub Q Λ Λc j hj νᵢ ν₀ L ↔
      x ∈ leftViolSub k Q Λ νᵢ (IndK k (MidLeftModel L hL hR) aB) :=
  mem_midBotViolSub_iff_mem_leftViolSub hR' hP hκ (appendTopIotaMul ν i h hR hR' hP hPL hκ)
    (appendTopIotaMul_injective ν i h hR hR' hP hPL hκ hQ hfin) (φ⁺ 1)
    (appendTopIotaMul_fix ν i hR hR' hP hPL hκ h)
    (appendTopIotaMul_surj ν i hR hR' hP hPL hκ h) x

end Top

end Categorification.Stendhal.CupCap

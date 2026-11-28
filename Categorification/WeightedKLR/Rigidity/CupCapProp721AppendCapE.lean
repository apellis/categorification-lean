/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendViolKer
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapInd
import Categorification.Algebra.InductionAlongQuotient

/-!
# `T^λ_{{i} + ν} e' ⊗_{T^λ_ν} K_ν ≅ K_{{i} + ν} e'⁺` as bimodules

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the part for `𝔈_i`. For right modules, `K ∘ 𝔈_i` is the tensor product with
`B₁ = T^λ_{{i} + ν} e' ⊗_{T^λ_ν} K_ν` (induction along `appendBlack`) and `𝔈_i ∘ K` is the
tensor product with `B₂ = K_{{i} + ν} e'⁺`, a right `T^{λ⁺}_{ν + ν₀}`-module through
`appendBlackTPAOp`. The multiplication `a ⊗ c ↦ a · ι(c)` is an isomorphism `B₁ ≅ B₂` of left
`T^λ_{{i} + ν}`-modules (`CupCap.capEEquiv`), compatible with the right actions of
`T^{λ⁺}_{ν + ν₀}` (`CupCap.capEEquiv_rightAct`).

The argument is the same for every `ι : K_ν → K_{{i} + ν}` with the properties of
`CupCap.capIota` (`j < ℓ`) and `CupCap.capTopIota` (`j = ℓ`), given the model-level
statements: surjectivity (`CupCap.appendBlackPlusOp_one_smul_mem_closure_capIota`) and the
matching of the violated parts under the injective model map
(`CupCap.appendIotaMul_mem_midBotViolSub_iff`). The induced module over `T̃^λ` maps onto `B₁`
(`InductionAlong.indQuotHom`), and the violated part maps to zero.

Route hypotheses (tracked), as for `CupCap.appendIotaMul_injective`: each piece `L e(t)`
finitely generated over `k`, `Q` symmetric, the cup scalars units and the pull-off identities.

## Main definitions

* `CupCap.capModelProj`: the projection of the model onto `K^{λ⁺}_λ`.
* `CupCap.capEMul`: `B₁ → K_{{i} + ν}`, `a ⊗ c ↦ a · ι(c)`.
* `CupCap.capERight`: the right action of `e'⁺` on `K_{{i} + ν}`.
* `CupCap.capEEquiv`: `B₁ ≅ B₂`, for any `ι` with the properties of appending a strand.
* `CupCap.capEEquivMid` (`j < ℓ`), `CupCap.capEEquivTop` (`j = ℓ`): the two cases.

## Main results

* `CupCap.capEMul_injective`, `CupCap.range_capEMul`, `CupCap.capEEquiv_rightAct`.
* `CupCap.capEEquivMid_rightAct`, `CupCap.capEEquivTop_rightAct`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν₀ : Multiset I}
  {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}

theorem mk_eq_zero_iff_mem_violatedIdeal {ν : Multiset I}
    (x : StendhalAlgebra k Q Λ ν) :
    TensorProductAlgebra.mk Q Λ ν x = 0 ↔ x ∈ StendhalAlgebra.violatedIdeal k Q Λ ν := by
  change (StendhalAlgebra.violatedIdeal k Q Λ ν).ringCon.mk' x = 0 ↔ _
  rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']

section Proj

variable {ν : Multiset I}

local notation "CB" => CapBimodule k Q Λ Λc j hj ν ν₀ L

variable (L) in
/-- `K^{λ⁺}_λ` as a left `T̃^λ`-module, through the quotient map. -/
abbrev capStendhalLeftModule : Module (StendhalAlgebra k Q Λ ν) CB :=
  Module.compHom CB (TensorProductAlgebra.mk Q Λ ν).toRingHom

attribute [local instance] capStendhalLeftModule

variable (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (hP : PullOff k Q Λc ν₀ L)
  (hPL : PullOffLeft k Q Λc ν₀ L) (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))

/-- **The projection of the model onto `K^{λ⁺}_λ`**, a left `T̃^λ`-linear map. -/
def capModelProj : MidLeftModel L hL hR →ₗ[StendhalAlgebra k Q Λ ν] CB where
  toFun y := (capModelRightEquiv hR hP hPL hκ).symm
    (Submodule.Quotient.mk (y : MidModel j hj Q Λ Λc ν ν₀ L))
  map_add' y y' := by rw [← map_add]; rfl
  map_smul' a y := by
    apply (capModelRightEquiv hR hP hPL hκ).injective
    rw [LinearEquiv.apply_symm_apply]
    exact (capModelRightEquiv_capLeftLin hR hP hPL hκ a _ y
      (LinearEquiv.apply_symm_apply _ _)).symm

theorem capModelRightEquiv_capModelProj (y : MidLeftModel L hL hR) :
    capModelRightEquiv hR hP hPL hκ (capModelProj hR hP hPL hκ y) =
      Submodule.Quotient.mk (y : MidModel j hj Q Λ Λc ν ν₀ L) :=
  LinearEquiv.apply_symm_apply _ _

theorem capModelProj_surjective : Function.Surjective (capModelProj hR hP hPL hκ) := by
  intro c
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (capModelRightEquiv hR hP hPL hκ c)
  exact ⟨y, (capModelRightEquiv hR hP hPL hκ).injective
    ((capModelRightEquiv_capModelProj hR hP hPL hκ y).trans hy)⟩

theorem capModelProj_eq_zero_iff (y : MidLeftModel L hL hR) :
    capModelProj hR hP hPL hκ y = 0 ↔
      (y : MidModel j hj Q Λ Λc ν ν₀ L) ∈ midBotViolSub Q Λ Λc j hj ν ν₀ L := by
  change (capModelRightEquiv hR hP hPL hκ).symm
    (Submodule.Quotient.mk (y : MidModel j hj Q Λ Λc ν ν₀ L)) = 0 ↔ _
  rw [LinearEquiv.map_eq_zero_iff]
  exact Submodule.Quotient.mk_eq_zero _

end Proj

attribute [local instance] capStendhalLeftModule

variable (ν : Multiset I) (i : I)

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "T" => StendhalAlgebra k Q Λ ν
local notation "Tᵢ" => StendhalAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν)
local notation "TA" => TensorProductAlgebra k Q Λ ν
local notation "TAᵢ" => TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν)
local notation "TPp" => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
local notation "CB" => CapBimodule k Q Λ Λc j hj ν ν₀ L
local notation "CBᵢ" => CapBimodule k Q Λ Λc j hj ((Singleton.singleton i : Multiset I) + ν) ν₀ L
local notation "aB" => (appendBlackStendhal Q Λ i ν : StendhalAlgebra k Q Λ ν →ₙ+*
  StendhalAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν))
local notation "aBl" => (appendBlack Q Λ i ν : TensorProductAlgebra k Q Λ ν →ₙ+*
  TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν))
local notation "φ⁺" => appendBlackPlusOp Q Λ Λc j hj ν ν₀ i
local notation "eP" => appendBlackTPAOp k Q Λ Λc j hj ν ν₀ i 1

/-! ### The multiplication map on `K` -/

section Mul

theorem capIotaK_smul_left (ιK : CB →+ CBᵢ)
    (hιl : ∀ (z : StendhalAlgebra k Q Λ ν) (c : CB),
      ιK (capLeftLin L z c) = capLeftLin L (aB z) (ιK c))
    (a : TA) (c : CB) : ιK (a • c) = (aBl a • ιK c : CBᵢ) := by
  obtain ⟨a, rfl⟩ := (StendhalAlgebra.violatedIdeal k Q Λ ν).ringCon.mkₐ_surjective (α := k) a
  have h := hιl a c
  change ιK (TensorProductAlgebra.mk Q Λ ν a • c) =
    (aBl (TensorProductAlgebra.mk Q Λ ν a) • ιK c : CBᵢ)
  have hm : aBl (TensorProductAlgebra.mk Q Λ ν a) = TensorProductAlgebra.mk Q Λ νᵢ (aB a) :=
    appendBlack_mk Q Λ i ν a
  rw [hm]
  exact h

/-- **The multiplication** `T^λ_{{i} + ν} e' ⊗_{T^λ_ν} K_ν → K_{{i} + ν}`, `a ⊗ c ↦ a · ι(c)`. -/
def capEMul (ιK : CB →+ CBᵢ)
    (hιl : ∀ (z : StendhalAlgebra k Q Λ ν) (c : CB),
      ιK (capLeftLin L z c) = capLeftLin L (aB z) (ιK c)) :
    Ind CB aBl →ₗ[TAᵢ] CBᵢ :=
  Ind.lift (fun z c => z.1 • ιK c)
    (fun z z' c => by rw [Submodule.coe_add, add_smul])
    (fun z c c' => by rw [map_add, smul_add])
    (fun z a c => by
      rw [capIotaK_smul_left ν i ιK hιl, op_smul_val, mul_smul])
    (fun b z c => by rw [Submodule.coe_smul, smul_eq_mul, mul_smul])

theorem capEMul_tmul (ιK : CB →+ CBᵢ)
    (hιl : ∀ (z : StendhalAlgebra k Q Λ ν) (c : CB),
      ιK (capLeftLin L z c) = capLeftLin L (aB z) (ιK c))
    (z : Corner aBl) (c : CB) :
    capEMul ν i ιK hιl (Ind.tmul z c) = z.1 • ιK c :=
  rfl

theorem capBimodule_smul_comm {μ : Multiset I}
    (a : TensorProductAlgebra k Q Λ μ)
    (b : (TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (μ + ν₀))ᵐᵒᵖ)
    (c : CapBimodule k Q Λ Λc j hj μ ν₀ L) : a • b • c = b • a • c :=
  SMulCommClass.smul_comm a b c

variable (L) in
/-- **The right action of `e'⁺` on `K_{{i} + ν}`**, a left `T^λ_{{i} + ν}`-linear map. -/
def capERight : CBᵢ →ₗ[TAᵢ] CBᵢ where
  toFun c := eP • c
  map_add' c c' := smul_add _ c c'
  map_smul' a c := (capBimodule_smul_comm a eP c).symm

theorem capERight_apply (c : CBᵢ) : capERight L ν i c = eP • c := rfl

theorem appendBlackTPAOp_one_smul (c : CBᵢ) : eP • c = φ⁺ 1 • c := by
  have h1 : appendBlackTPAOp k Q Λ Λc j hj ν ν₀ i 1 =
      appendBlackTPAOp k Q Λ Λc j hj ν ν₀ i (plusQuotOp k Q Λ Λc j hj ν ν₀ 1) := by
    rw [RingHom.map_one]
  rw [h1, appendBlackTPAOp_plusQuotOp]
  exact (capStendhal_smul _ _).symm

theorem capERight_capEMul (ιK : CB →+ CBᵢ)
    (hιl : ∀ (z : StendhalAlgebra k Q Λ ν) (c : CB),
      ιK (capLeftLin L z c) = capLeftLin L (aB z) (ιK c))
    (hιs : ∀ (b : Tpᵐᵒᵖ) (c : CB), ιK (b • c) = φ⁺ b • ιK c) (x : Ind CB aBl) :
    capERight L ν i (capEMul ν i ιK hιl x) = capEMul ν i ιK hιl x := by
  induction x using Ind.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul z c =>
    change eP • (z.1 • ιK c) = z.1 • ιK c
    rw [← capBimodule_smul_comm, appendBlackTPAOp_one_smul, ← hιs, one_smul]
  | add x x' hx hx' => rw [map_add, map_add, hx, hx']

end Mul

/-! ### Comparison with the models -/

section Model

variable (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
  (hR' : MidKLRRel j hj Q Λ Λc ((Singleton.singleton i : Multiset I) + ν) ν₀ L hL)
  (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
  (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i'))

theorem appendBlack_comp_mk (a : T) :
    aBl ((TensorProductAlgebra.mk Q Λ ν).toRingHom a) =
      (TensorProductAlgebra.mk Q Λ νᵢ).toRingHom (aB a) :=
  appendBlack_mk Q Λ i ν a

/-- The map from the induced module of the model over `T̃^λ` to `T^λ_{{i} + ν} e' ⊗ K_ν`,
`z ⊗ y ↦ π(z) ⊗ π(y)`. -/
def capEMulLift : Ind (MidLeftModel L hL hR) aB →+ Ind CB aBl :=
  (indQuotHom (appendBlack_comp_mk ν i) (N := CB) (fun _ _ => rfl)).comp
    (Ind.map (φ := aB) (capModelProj hR hP hPL hκ)).toAddMonoidHom

theorem capEMulLift_tmul (z : Corner aB) (y : MidLeftModel L hL hR) :
    capEMulLift ν i hR hP hPL hκ (Ind.tmul z y) =
      Ind.tmul (quotCorner (appendBlack_comp_mk ν i) z) (capModelProj hR hP hPL hκ y) := by
  change indQuotHom (appendBlack_comp_mk ν i) (N := CB) (fun _ _ => rfl)
    (Ind.map (φ := aB) (capModelProj hR hP hPL hκ) (Ind.tmul z y)) = _
  rw [Ind.map_tmul, indQuotHom_tmul]

theorem capEMulLift_surjective : Function.Surjective (capEMulLift ν i hR hP hPL hκ) := by
  have hmap : Function.Surjective (Ind.map (φ := aB) (capModelProj hR hP hPL hκ)) := by
    intro w
    induction w using Ind.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul z c =>
      obtain ⟨y, rfl⟩ := capModelProj_surjective hR hP hPL hκ c
      exact ⟨Ind.tmul z y, Ind.map_tmul _ z y⟩
    | add w w' hw hw' =>
      obtain ⟨x, rfl⟩ := hw
      obtain ⟨x', rfl⟩ := hw'
      exact ⟨x + x', map_add _ x x'⟩
  exact (indQuotHom_surjective
    (fun b => (StendhalAlgebra.violatedIdeal k Q Λ νᵢ).ringCon.mkₐ_surjective (α := k) b)
    (appendBlack_comp_mk ν i) (N := CB) (fun _ _ => rfl)).comp hmap

theorem capEMulLift_leftViolSub {x : IndK k (MidLeftModel L hL hR) aB}
    (hx : x ∈ leftViolSub k Q Λ νᵢ (IndK k (MidLeftModel L hL hR) aB)) :
    capEMulLift ν i hR hP hPL hκ x = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, y, rfl⟩ := hx
    change indQuotHom (appendBlack_comp_mk ν i) (N := CB) (fun _ _ => rfl)
      (Ind.map (φ := aB) (capModelProj hR hP hPL hκ) (a • y)) = 0
    have e1 : Ind.map (φ := aB) (capModelProj hR hP hPL hκ) (a • y) =
        a • Ind.map (φ := aB) (capModelProj hR hP hPL hκ)
          (show Ind (MidLeftModel L hL hR) aB from y) := map_smul _ a _
    rw [e1, indQuotHom_smul]
    change TensorProductAlgebra.mk Q Λ νᵢ a • _ = 0
    rw [(mk_eq_zero_iff_mem_violatedIdeal a).2 ha, zero_smul]
  | zero => exact map_zero _
  | add x y _ _ hx hy =>
    exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (add_zero 0))
  | smul c x _ hx =>
    change indQuotHom (appendBlack_comp_mk ν i) (N := CB) (fun _ _ => rfl)
      (Ind.map (φ := aB) (capModelProj hR hP hPL hκ) (c • x)) = 0
    have e1 : Ind.map (φ := aB) (capModelProj hR hP hPL hκ) (c • x) =
        c • Ind.map (φ := aB) (capModelProj hR hP hPL hκ)
          (show Ind (MidLeftModel L hL hR) aB from x) := map_smul _ c _
    rw [e1, indQuotHom_smul]
    exact (congrArg _ hx).trans (smul_zero _)

/-- **The square with the model**: `μ_K ∘ π = π ∘ μ`. -/
theorem capEMul_capEMulLift (ιK : CB →+ CBᵢ)
    (hιl : ∀ (z : StendhalAlgebra k Q Λ ν) (c : CB),
      ιK (capLeftLin L z c) = capLeftLin L (aB z) (ιK c))
    (μ : IndK k (MidLeftModel L hL hR) aB →ₗ[Tᵢ] MidLeftModel L hL hR')
    (hsq : ∀ (z : Corner aB) (y : MidLeftModel L hL hR),
      capModelProj hR' hP hPL hκ (μ (IndK.tmul z y)) =
        capLeftLin L z.1 (ιK (capModelProj hR hP hPL hκ y)))
    (x : IndK k (MidLeftModel L hL hR) aB) :
    capEMul ν i ιK hιl (capEMulLift ν i hR hP hPL hκ x) = capModelProj hR' hP hPL hκ (μ x) := by
  refine Ind.induction_on (motive := fun x : Ind (MidLeftModel L hL hR) aB =>
    capEMul ν i ιK hιl (capEMulLift ν i hR hP hPL hκ x) =
      capModelProj hR' hP hPL hκ (μ (x : IndK k (MidLeftModel L hL hR) aB))) x ?_
    (fun z y => ?_) (fun s t hs ht => ?_)
  · change capEMul ν i ιK hιl (capEMulLift ν i hR hP hPL hκ 0) =
      capModelProj hR' hP hPL hκ (μ 0)
    rw [map_zero, map_zero, map_zero, map_zero]
  · rw [capEMulLift_tmul, capEMul_tmul, quotCorner_val]
    exact (hsq z y).symm
  · exact (congrArg (capEMul ν i ιK hιl) (map_add _ s t)).trans ((map_add _ _ _).trans
      ((congrArg₂ (· + ·) hs ht).trans ((map_add _ _ _).symm.trans
        (congrArg _ (map_add μ s t).symm))))

/-- **`T^λ_{{i} + ν} e' ⊗_{T^λ_ν} K_ν → K_{{i} + ν}` is injective**, given the matching of the
violated parts under an injective model map. -/
theorem capEMul_injective (ιK : CB →+ CBᵢ)
    (hιl : ∀ (z : StendhalAlgebra k Q Λ ν) (c : CB),
      ιK (capLeftLin L z c) = capLeftLin L (aB z) (ιK c))
    (μ : IndK k (MidLeftModel L hL hR) aB →ₗ[Tᵢ] MidLeftModel L hL hR')
    (hsq : ∀ (z : Corner aB) (y : MidLeftModel L hL hR),
      capModelProj hR' hP hPL hκ (μ (IndK.tmul z y)) =
        capLeftLin L z.1 (ιK (capModelProj hR hP hPL hκ y)))
    (hker : ∀ x, (μ x : MidModel j hj Q Λ Λc νᵢ ν₀ L) ∈ midBotViolSub Q Λ Λc j hj νᵢ ν₀ L ↔
      x ∈ leftViolSub k Q Λ νᵢ (IndK k (MidLeftModel L hL hR) aB)) :
    Function.Injective (capEMul ν i ιK hιl) := by
  rw [injective_iff_map_eq_zero]
  intro w hw
  obtain ⟨x, rfl⟩ := capEMulLift_surjective ν i hR hP hPL hκ w
  have hx := (capEMul_capEMulLift ν i hR hR' hP hPL hκ ιK hιl μ hsq
    (show IndK k (MidLeftModel L hL hR) aB from x)).symm.trans hw
  rw [capModelProj_eq_zero_iff, hker] at hx
  exact capEMulLift_leftViolSub ν i hR hP hPL hκ hx

end Model

section Range

/-- **The image of `T^λ_{{i} + ν} e' ⊗_{T^λ_ν} K_ν → K_{{i} + ν}` is `K_{{i} + ν} e'⁺`**. -/
theorem range_capEMul (ιK : CB →+ CBᵢ)
    (hιl : ∀ (z : StendhalAlgebra k Q Λ ν) (c : CB),
      ιK (capLeftLin L z c) = capLeftLin L (aB z) (ιK c))
    (hιs : ∀ (b : Tpᵐᵒᵖ) (c : CB), ιK (b • c) = φ⁺ b • ιK c)
    (hcl : ∀ c : CBᵢ, φ⁺ 1 • c ∈ AddSubmonoid.closure
      (Set.range fun p : Tᵢ × CB => capLeftLin L p.1 (ιK p.2))) :
    LinearMap.range (capEMul ν i ιK hιl) = LinearMap.range (capERight L ν i) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact ⟨_, capERight_capEMul ν i ιK hιl hιs x⟩
  · rintro _ ⟨c, rfl⟩
    rw [capERight_apply, appendBlackTPAOp_one_smul]
    refine (AddSubmonoid.closure_le
      (S := (LinearMap.range (capEMul ν i ιK hιl)).toAddSubmonoid)).2 ?_ (hcl c)
    rintro _ ⟨⟨a, c'⟩, rfl⟩
    refine ⟨Ind.tmul ⟨TensorProductAlgebra.mk Q Λ νᵢ a * aBl 1, mul_mem_corner aBl _ 1⟩ c', ?_⟩
    rw [capEMul_tmul]
    change (TensorProductAlgebra.mk Q Λ νᵢ a * aBl 1) • ιK c' =
      TensorProductAlgebra.mk Q Λ νᵢ a • ιK c'
    rw [mul_smul, ← capIotaK_smul_left ν i ιK hιl, one_smul]

end Range

section Right

variable (L) in
/-- The right action of `b ∈ T^{λ⁺}_{ν + ν₀}` on `K_ν`, a left `T^λ_ν`-linear map. -/
def capRightActLin (b : TPpᵐᵒᵖ) : CB →ₗ[TA] CB where
  toFun c := b • c
  map_add' c c' := smul_add b c c'
  map_smul' a c := (capBimodule_smul_comm a b c).symm

theorem capRightActLin_apply (b : TPpᵐᵒᵖ) (c : CB) : capRightActLin L ν b c = b • c := rfl

theorem capIotaK_smul_right (ιK : CB →+ CBᵢ)
    (hιs : ∀ (b : Tpᵐᵒᵖ) (c : CB), ιK (b • c) = φ⁺ b • ιK c)
    (b : TPpᵐᵒᵖ) (c : CB) :
    ιK (b • c) = (appendBlackTPAOp k Q Λ Λc j hj ν ν₀ i b • ιK c : CBᵢ) := by
  obtain ⟨b, rfl⟩ := plusQuotOp_surjective (k := k) (Q := Q) (Λ := Λ) (Λc := Λc) (j := j)
    (hj := hj) (ν := ν) (ν₀ := ν₀) b
  rw [appendBlackTPAOp_plusQuotOp, ← capStendhal_smul, ← capStendhal_smul]
  exact hιs b c

/-- **`T^λ_{{i} + ν} e' ⊗_{T^λ_ν} K_ν → K_{{i} + ν}` carries the right action of `b` to the
right action of `appendBlack(b)`**. -/
theorem capEMul_rightAct (ιK : CB →+ CBᵢ)
    (hιl : ∀ (z : StendhalAlgebra k Q Λ ν) (c : CB),
      ιK (capLeftLin L z c) = capLeftLin L (aB z) (ιK c))
    (hιs : ∀ (b : Tpᵐᵒᵖ) (c : CB), ιK (b • c) = φ⁺ b • ιK c)
    (b : TPpᵐᵒᵖ) (x : Ind CB aBl) :
    capEMul ν i ιK hιl (Ind.map (capRightActLin L ν b) x) =
      appendBlackTPAOp k Q Λ Λc j hj ν ν₀ i b • capEMul ν i ιK hιl x := by
  induction x using Ind.induction_on with
  | zero => rw [map_zero, map_zero, smul_zero]
  | tmul z c =>
    rw [Ind.map_tmul, capEMul_tmul, capEMul_tmul, capRightActLin_apply,
      capIotaK_smul_right ν i ιK hιs, capBimodule_smul_comm]
  | add x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, smul_add]

end Right

section Equiv

variable (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
  (hR' : MidKLRRel j hj Q Λ Λc ((Singleton.singleton i : Multiset I) + ν) ν₀ L hL)
  (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
  (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i'))

/-- **`T^λ_{{i} + ν} e' ⊗_{T^λ_ν} K_ν ≅ K_{{i} + ν} e'⁺`** as left `T^λ_{{i} + ν}`-modules, for a
map `ι` with the properties of appending a black strand, given the model-level surjectivity and
matching of the violated parts. -/
def capEEquiv (ιK : CB →+ CBᵢ)
    (hιl : ∀ (z : StendhalAlgebra k Q Λ ν) (c : CB),
      ιK (capLeftLin L z c) = capLeftLin L (aB z) (ιK c))
    (hιs : ∀ (b : Tpᵐᵒᵖ) (c : CB), ιK (b • c) = φ⁺ b • ιK c)
    (μ : IndK k (MidLeftModel L hL hR) aB →ₗ[Tᵢ] MidLeftModel L hL hR')
    (hsq : ∀ (z : Corner aB) (y : MidLeftModel L hL hR),
      capModelProj hR' hP hPL hκ (μ (IndK.tmul z y)) =
        capLeftLin L z.1 (ιK (capModelProj hR hP hPL hκ y)))
    (hker : ∀ x, (μ x : MidModel j hj Q Λ Λc νᵢ ν₀ L) ∈ midBotViolSub Q Λ Λc j hj νᵢ ν₀ L ↔
      x ∈ leftViolSub k Q Λ νᵢ (IndK k (MidLeftModel L hL hR) aB))
    (hcl : ∀ c : CBᵢ, φ⁺ 1 • c ∈ AddSubmonoid.closure
      (Set.range fun p : Tᵢ × CB => capLeftLin L p.1 (ιK p.2))) :
    Ind CB aBl ≃ₗ[TAᵢ] LinearMap.range (capERight L ν i : CBᵢ →ₗ[TAᵢ] CBᵢ) :=
  (LinearEquiv.ofInjective _ (capEMul_injective ν i hR hR' hP hPL hκ ιK hιl μ hsq hker)).trans
    (LinearEquiv.ofEq _ _ (range_capEMul ν i ιK hιl hιs hcl))

theorem capEEquiv_apply (ιK : CB →+ CBᵢ)
    (hιl : ∀ (z : StendhalAlgebra k Q Λ ν) (c : CB),
      ιK (capLeftLin L z c) = capLeftLin L (aB z) (ιK c))
    (hιs : ∀ (b : Tpᵐᵒᵖ) (c : CB), ιK (b • c) = φ⁺ b • ιK c)
    (μ : IndK k (MidLeftModel L hL hR) aB →ₗ[Tᵢ] MidLeftModel L hL hR')
    (hsq : ∀ (z : Corner aB) (y : MidLeftModel L hL hR),
      capModelProj hR' hP hPL hκ (μ (IndK.tmul z y)) =
        capLeftLin L z.1 (ιK (capModelProj hR hP hPL hκ y)))
    (hker : ∀ x, (μ x : MidModel j hj Q Λ Λc νᵢ ν₀ L) ∈ midBotViolSub Q Λ Λc j hj νᵢ ν₀ L ↔
      x ∈ leftViolSub k Q Λ νᵢ (IndK k (MidLeftModel L hL hR) aB))
    (hcl : ∀ c : CBᵢ, φ⁺ 1 • c ∈ AddSubmonoid.closure
      (Set.range fun p : Tᵢ × CB => capLeftLin L p.1 (ιK p.2)))
    (x : Ind CB aBl) :
    (capEEquiv ν i hR hR' hP hPL hκ ιK hιl hιs μ hsq hker hcl x : CBᵢ) =
      capEMul ν i ιK hιl x :=
  rfl

/-- **The isomorphism `T^λ_{{i} + ν} e' ⊗_{T^λ_ν} K_ν ≅ K_{{i} + ν} e'⁺` is one of bimodules**: it
carries the right action of `b ∈ T^{λ⁺}_{ν + ν₀}` to the right action of `appendBlack(b)`. -/
theorem capEEquiv_rightAct (ιK : CB →+ CBᵢ)
    (hιl : ∀ (z : StendhalAlgebra k Q Λ ν) (c : CB),
      ιK (capLeftLin L z c) = capLeftLin L (aB z) (ιK c))
    (hιs : ∀ (b : Tpᵐᵒᵖ) (c : CB), ιK (b • c) = φ⁺ b • ιK c)
    (μ : IndK k (MidLeftModel L hL hR) aB →ₗ[Tᵢ] MidLeftModel L hL hR')
    (hsq : ∀ (z : Corner aB) (y : MidLeftModel L hL hR),
      capModelProj hR' hP hPL hκ (μ (IndK.tmul z y)) =
        capLeftLin L z.1 (ιK (capModelProj hR hP hPL hκ y)))
    (hker : ∀ x, (μ x : MidModel j hj Q Λ Λc νᵢ ν₀ L) ∈ midBotViolSub Q Λ Λc j hj νᵢ ν₀ L ↔
      x ∈ leftViolSub k Q Λ νᵢ (IndK k (MidLeftModel L hL hR) aB))
    (hcl : ∀ c : CBᵢ, φ⁺ 1 • c ∈ AddSubmonoid.closure
      (Set.range fun p : Tᵢ × CB => capLeftLin L p.1 (ιK p.2)))
    (b : TPpᵐᵒᵖ) (x : Ind CB aBl) :
    (capEEquiv ν i hR hR' hP hPL hκ ιK hιl hιs μ hsq hker hcl
        (Ind.map (capRightActLin L ν b) x) : CBᵢ) =
      appendBlackTPAOp k Q Λ Λc j hj ν ν₀ i b •
        (capEEquiv ν i hR hR' hP hPL hκ ιK hιl hιs μ hsq hker hcl x : CBᵢ) :=
  capEMul_rightAct ν i ιK hιl hιs b x

end Equiv

/-! ### The two cases -/

section Cases

variable [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
  (hR' : MidKLRRel j hj Q Λ Λc ((Singleton.singleton i : Multiset I) + ν) ν₀ L hL)
  (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
  (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i')) (hQ : KLRSymm Q)
  (hfin : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Finite k
    (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht))))

omit [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
theorem capModelProj_appendIota (h : j < ℓ) (y : MidLeftModel L hL hR) :
    capIota ν i hR hR' hP hPL hκ h (capModelProj hR hP hPL hκ y) =
      capModelProj hR' hP hPL hκ (appendIota ν i L h y) :=
  (capModelRightEquiv hR' hP hPL hκ).injective
    ((capModelRightEquiv_capIota ν i hR hR' hP hPL hκ h _ y
      (capModelRightEquiv_capModelProj hR hP hPL hκ y)).trans
      (capModelRightEquiv_capModelProj hR' hP hPL hκ _).symm)

omit [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
theorem capModelProj_appendTopIota (h : ¬ j < ℓ) (y : MidLeftModel L hL hR) :
    capTopIota ν i hR hR' hP hPL hκ h (capModelProj hR hP hPL hκ y) =
      capModelProj hR' hP hPL hκ (appendTopIota ν i hP hPL hL hκ h y) :=
  (capModelRightEquiv hR' hP hPL hκ).injective
    ((capModelRightEquiv_capTopIota ν i hR hR' hP hPL hκ h _ y
      (capModelRightEquiv_capModelProj hR hP hPL hκ y)).trans
      (capModelRightEquiv_capModelProj hR' hP hPL hκ _).symm)

/-- **`T^λ_{{i} + ν} e' ⊗_{T^λ_ν} K_ν ≅ K_{{i} + ν} e'⁺` as bimodules** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21, the part for `𝔈_i`), for `j < ℓ`:
`a ⊗ c ↦ a · ι(c)` is an isomorphism of left `T^λ_{{i} + ν}`-modules
(`CupCap.capEEquiv_apply`), compatible with the right actions (`CupCap.capEEquivMid_rightAct`).

Route hypotheses (tracked), as for `CupCap.appendIotaMul_injective`: each piece `L e(t)`
finitely generated over `k` (`hfin`), `Q` symmetric, the cup scalars units and the pull-off
identities. -/
def capEEquivMid (h : j < ℓ) :
    Ind CB aBl ≃ₗ[TAᵢ] LinearMap.range (capERight L ν i : CBᵢ →ₗ[TAᵢ] CBᵢ) :=
  capEEquiv ν i hR hR' hP hPL hκ (capIota ν i hR hR' hP hPL hκ h)
    (capIota_capLeftLin ν i hR hR' hP hPL hκ h) (capIota_smul ν i hR hR' hP hPL hκ h)
    (appendIotaMul ν i h hR hR')
    (fun z y => by
      rw [capModelProj_appendIota ν i hR hR' hP hPL hκ h y]
      exact (capModelProj hR' hP hPL hκ).map_smul z.1 (appendIota ν i L h y))
    (appendIotaMul_mem_midBotViolSub_iff ν i hR hR' h hQ hP hκ hfin)
    (appendBlackPlusOp_one_smul_mem_closure_capIota ν i hR hR' hP hPL hκ h)

theorem capEEquivMid_apply (h : j < ℓ) (z : Corner aBl) (c : CB) :
    (capEEquivMid ν i hR hR' hP hPL hκ hQ hfin h (Ind.tmul z c) : CBᵢ) =
      z.1 • capIota ν i hR hR' hP hPL hκ h c :=
  rfl

theorem capEEquivMid_rightAct (h : j < ℓ) (b : TPpᵐᵒᵖ) (x : Ind CB aBl) :
    (capEEquivMid ν i hR hR' hP hPL hκ hQ hfin h (Ind.map (capRightActLin L ν b) x) : CBᵢ) =
      appendBlackTPAOp k Q Λ Λc j hj ν ν₀ i b •
        (capEEquivMid ν i hR hR' hP hPL hκ hQ hfin h x : CBᵢ) :=
  capEMul_rightAct ν i _ (capIota_capLeftLin ν i hR hR' hP hPL hκ h)
    (capIota_smul ν i hR hR' hP hPL hκ h) b x

/-- **`T^λ_{{i} + ν} e' ⊗_{T^λ_ν} K_ν ≅ K_{{i} + ν} e'⁺` as bimodules** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21, the part for `𝔈_i`), for `j = ℓ`:
`a ⊗ c ↦ a · ι(c)` is an isomorphism of left `T^λ_{{i} + ν}`-modules
(`CupCap.capEEquivTop_apply`), compatible with the right actions (`CupCap.capEEquivTop_rightAct`).

Route hypotheses (tracked), as for `CupCap.appendTopIotaMul_injective`: each piece `L e(t)`
finitely generated over `k` (`hfin`), `Q` symmetric, the cup scalars units and the pull-off
identities. -/
def capEEquivTop (h : ¬ j < ℓ) :
    Ind CB aBl ≃ₗ[TAᵢ] LinearMap.range (capERight L ν i : CBᵢ →ₗ[TAᵢ] CBᵢ) :=
  capEEquiv ν i hR hR' hP hPL hκ (capTopIota ν i hR hR' hP hPL hκ h)
    (capTopIota_capLeftLin ν i hR hR' hP hPL hκ h) (capTopIota_smul ν i hR hR' hP hPL hκ h)
    (appendTopIotaMul ν i h hR hR' hP hPL hκ)
    (fun z y => by
      rw [capModelProj_appendTopIota ν i hR hR' hP hPL hκ h y]
      exact (capModelProj hR' hP hPL hκ).map_smul z.1 (appendTopIota ν i hP hPL hL hκ h y))
    (appendTopIotaMul_mem_midBotViolSub_iff ν i hR hR' hP hPL hκ h hQ hfin)
    (appendBlackPlusOp_one_smul_mem_closure_capTopIota ν i hR hR' hP hPL hκ h)

theorem capEEquivTop_apply (h : ¬ j < ℓ) (z : Corner aBl) (c : CB) :
    (capEEquivTop ν i hR hR' hP hPL hκ hQ hfin h (Ind.tmul z c) : CBᵢ) =
      z.1 • capTopIota ν i hR hR' hP hPL hκ h c :=
  rfl

theorem capEEquivTop_rightAct (h : ¬ j < ℓ) (b : TPpᵐᵒᵖ) (x : Ind CB aBl) :
    (capEEquivTop ν i hR hR' hP hPL hκ hQ hfin h (Ind.map (capRightActLin L ν b) x) : CBᵢ) =
      appendBlackTPAOp k Q Λ Λc j hj ν ν₀ i b •
        (capEEquivTop ν i hR hR' hP hPL hκ hQ hfin h x : CBᵢ) :=
  capEMul_rightAct ν i _ (capTopIota_capLeftLin ν i hR hR' hP hPL hκ h)
    (capTopIota_smul ν i hR hR' hP hPL hκ h) b x

end Cases

end Categorification.Stendhal.CupCap

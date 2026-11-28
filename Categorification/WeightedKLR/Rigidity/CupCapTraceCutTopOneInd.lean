/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.MackeyBotCorner

/-!
# The identity-shuffle part of a Mackey layer as an induced module

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half, step L5; Khovanov–Lauda I
(arXiv:0803.4121v2), §2.6, Propositions 2.16 and 2.18.

Let `q` be a Mackey datum and `BotN = MackeyBot_λ ⊗_{R''} N` the bottom factor of its layer.
The algebra `R(γ) ⊗ R(δ)` acts on `BotN` through `c ↦ 1 ⊗ c ∈ R'` (`botNModuleRight`, a local
instance). The map

  `Ind_{γ,δ} BotN = R(γ + δ) 1_{γ,δ} ⊗_{R(γ) ⊗ R(δ)} BotN → MackeyTop_λ ⊗_{R'} BotN`,
  `b ⊗ y ↦ (1 ⊗ b) · (1_λ ⊗ y)`

(`topOneIndMap`, with `R(γ + δ) = R(ν')` along `q.h₂`) has image the identity-shuffle span
`mackeyTopOneSpan` and is injective (`topOneIndMap_injective`). The left inverse
(`topOneIndRetract`) takes the identity-shuffle coordinate of the first factor in Proposition
2.16 (right-module form, `rightFreeEquiv`): this coordinate is right `R(α) ⊗ R(β)`-linear, so
it passes to the balanced tensor product. Hence
`mackeyTopOneSpan q N ≅ Ind_{γ,δ} BotN` (`topOneIndEquiv`), compatibly with the action of
`R(ν')` (`topOneIndMap_smul`).

Webster's proof does not spell this out. Symmetric `Q` (`KLRSymm Q`) for the injectivity, any
commutative ring `k`. No new hypothesis.

## Main results

* `KLR.KLRAlgebra.botNModuleRight`, `KLR.KLRAlgebra.topOneIndMap`,
  `KLR.KLRAlgebra.topOneIndMap_tmul`, `KLR.KLRAlgebra.topOneIndMap_smul`.
* `KLR.KLRAlgebra.topOneIndRetract`, `KLR.KLRAlgebra.topOneIndRetract_topOneIndMap`,
  `KLR.KLRAlgebra.topOneIndMap_injective`, `KLR.KLRAlgebra.range_topOneIndMap`.
* `KLR.KLRAlgebra.topOneIndEquiv`: `Ind_{γ,δ} BotN ≃ mackeyTopOneSpan q N`.
-/

noncomputable section

namespace Categorification.KLR

open Equiv TypeA MulOpposite
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k}

namespace KLRAlgebra

variable {ν ν' ν'' ν''' : Multiset I} (q : MackeyQuad ν ν' ν'' ν''')
  (N : Type*) [AddCommGroup N] [Module k N] [Module (TensorKLR Q ν'' ν''') N]

/-- `MackeyBot_λ ⊗_{R''} N`, the right factor of a Mackey layer. -/
local notation "BotN" => BalancedTensor k (QuadAlg Q q) (TensorKLR Q ν'' ν''') (MackeyBot Q q) N

/-- `R(γ) ⊗ R(δ)` acts on `MackeyBot_λ ⊗_{R''} N` through `c ↦ 1 ⊗ c ∈ R'`. -/
@[instance_reducible]
def botNModuleRight : Module (TensorKLR Q q.γ q.δ) BotN :=
  Module.compHom BotN
    (Algebra.TensorProduct.includeRight (R := k) (A := TensorKLR Q q.α q.β)
      (B := TensorKLR Q q.γ q.δ)).toRingHom

attribute [local instance] botNModuleRight

theorem botNModuleRight_smul (c : TensorKLR Q q.γ q.δ) (y : BotN) :
    c • y = (((1 : TensorKLR Q q.α q.β) ⊗ₜ c : QuadAlg Q q) • y) := rfl

variable {q}

/-- `ι_{α,β} ⊗ ι_{γ,δ}` on `1 ⊗ c`. -/
theorem quadTop_one_tmul (c : TensorKLR Q q.γ q.δ) :
    quadTop q ((1 : TensorKLR Q q.α q.β) ⊗ₜ c) =
      castAlg Q q.h₁ (oneConcat Q q.α q.β) ⊗ₜ castAlg Q q.h₂ (concat Q q.γ q.δ c) := by
  rw [quadTop, TensorProduct.map_tmul]
  simp only [LinearMap.coe_comp, Function.comp_apply, AlgEquiv.toLinearMap_apply, concat_one]

/-- `ι_{α,β} ⊗ ι_{γ,δ}` on a pure tensor `X ⊗ c`. -/
theorem quadTop_tmul_concat (X : TensorKLR Q q.α q.β) (c : TensorKLR Q q.γ q.δ) :
    quadTop q (X ⊗ₜ c) =
      castAlg Q q.h₁ (concat Q q.α q.β X) ⊗ₜ castAlg Q q.h₂ (concat Q q.γ q.δ c) := by
  rw [quadTop, TensorProduct.map_tmul]
  simp only [LinearMap.coe_comp, Function.comp_apply, AlgEquiv.toLinearMap_apply]

/-- `(1 ⊗ b) · 1_λ = 1_{α,β} ⊗ b 1_{γ,δ}`. -/
theorem one_tmul_mul_quadTop_one (b : KLRAlgebra k Q ν') :
    (((1 : KLRAlgebra k Q ν) ⊗ₜ b : TensorKLR Q ν ν') * quadTop q 1) =
      castAlg Q q.h₁ (oneConcat Q q.α q.β) ⊗ₜ (b * castAlg Q q.h₂ (oneConcat Q q.γ q.δ)) := by
  rw [quadTop_one_eq_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

variable (q)

/-- The bilinear form of `b ⊗ y ↦ (1 ⊗ b) · (1_λ ⊗ y)`. -/
def topOneIndBil : IndBimod Q q.γ q.δ →ₗ[k] BotN →ₗ[k] MackeyLeftInd Q N q :=
  LinearMap.mk₂ k
    (fun b y => (((1 : KLRAlgebra k Q ν) ⊗ₜ castAlg Q q.h₂ (b : KLRAlgebra k Q (q.γ + q.δ)) :
      TensorKLR Q ν ν') • (BalancedTensor.tmul (mackeyTopOne q) y : MackeyLeftInd Q N q)))
    (fun b b' y => by
      rw [Submodule.coe_add, map_add, TensorProduct.tmul_add, add_smul])
    (fun c b y => by
      rw [Submodule.coe_smul_of_tower, map_smul, TensorProduct.tmul_smul, smul_assoc])
    (fun b y y' => by rw [BalancedTensor.tmul_add, smul_add])
    (fun c b y => by rw [BalancedTensor.tmul_smul, smul_comm])

theorem topOneIndBil_apply (b : IndBimod Q q.γ q.δ) (y : BotN) :
    topOneIndBil q N b y = (((1 : KLRAlgebra k Q ν) ⊗ₜ
      castAlg Q q.h₂ (b : KLRAlgebra k Q (q.γ + q.δ)) : TensorKLR Q ν ν') •
        (BalancedTensor.tmul (mackeyTopOne q) y : MackeyLeftInd Q N q)) := rfl

theorem topOneIndBil_balanced (b : IndBimod Q q.γ q.δ) (c : TensorKLR Q q.γ q.δ) (y : BotN) :
    topOneIndBil q N (op c • b) y = topOneIndBil q N b (c • y) := by
  rw [topOneIndBil_apply, topOneIndBil_apply, botNModuleRight_smul,
    ← BalancedTensor.op_smul_tmul, BalancedTensor.smul_tmul', BalancedTensor.smul_tmul']
  congr 1
  apply Subtype.ext
  change ((1 : KLRAlgebra k Q ν) ⊗ₜ castAlg Q q.h₂ ((b : KLRAlgebra k Q (q.γ + q.δ)) *
      concat Q q.γ q.δ c) : TensorKLR Q ν ν') * quadTop q 1 =
    ((1 : KLRAlgebra k Q ν) ⊗ₜ castAlg Q q.h₂ (b : KLRAlgebra k Q (q.γ + q.δ)) :
      TensorKLR Q ν ν') * (quadTop q 1 * quadTop q ((1 : TensorKLR Q q.α q.β) ⊗ₜ c))
  rw [quadTop_one_mul, quadTop_one_tmul, one_tmul_mul_quadTop_one,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  congr 1
  rw [← map_mul, ← map_mul, mul_assoc, concat_mul_oneConcat]

/-- **The map `Ind_{γ,δ} BotN → MackeyTop_λ ⊗_{R'} BotN`**, `b ⊗ y ↦ (1 ⊗ b) · (1_λ ⊗ y)`,
with `R(γ + δ) = R(ν')` along `q.h₂`. -/
def topOneIndMap : Ind Q q.γ q.δ BotN →ₗ[k] MackeyLeftInd Q N q :=
  BalancedTensor.lift (topOneIndBil q N) (topOneIndBil_balanced q N)

theorem topOneIndMap_tmul (b : IndBimod Q q.γ q.δ) (y : BotN) :
    topOneIndMap q N (BalancedTensor.tmul b y) = (((1 : KLRAlgebra k Q ν) ⊗ₜ
      castAlg Q q.h₂ (b : KLRAlgebra k Q (q.γ + q.δ)) : TensorKLR Q ν ν') •
        (BalancedTensor.tmul (mackeyTopOne q) y : MackeyLeftInd Q N q)) := rfl

/-- **`R(ν')` acts through `R(γ + δ)`**: `Φ(r x) = (1 ⊗ r) Φ(x)`. -/
theorem topOneIndMap_smul (r : KLRAlgebra k Q (q.γ + q.δ)) (x : Ind Q q.γ q.δ BotN) :
    topOneIndMap q N (r • x) =
      (((1 : KLRAlgebra k Q ν) ⊗ₜ castAlg Q q.h₂ r : TensorKLR Q ν ν') •
        topOneIndMap q N x) := by
  induction x using BalancedTensor.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add x x' hx hx' => rw [smul_add, map_add, hx, hx', map_add, smul_add]
  | tmul b y =>
    rw [BalancedTensor.smul_tmul', topOneIndMap_tmul, topOneIndMap_tmul, smul_smul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, Submodule.coe_smul, smul_eq_mul, map_mul]

theorem topOneIndMap_mem (x : Ind Q q.γ q.δ BotN) :
    topOneIndMap q N x ∈ mackeyTopOneSpan q N := by
  induction x using BalancedTensor.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | add x x' hx hx' => rw [map_add]; exact add_mem hx hx'
  | tmul b y => exact smul_tmul_mackeyTopOne_mem q _ y

/-! ### The identity-shuffle coordinate -/

variable {q}

/-- The projection `R(ν') → R(γ + δ) 1_{γ,δ}`, `b ↦ b 1_{γ,δ}` along `q.h₂`. -/
def topSecondProj : KLRAlgebra k Q ν' →ₗ[k] IndBimod Q q.γ q.δ :=
  ((Graded.leftIdealProj (oneConcat_idem (Q := Q) (ν := q.γ) (ν' := q.δ))).restrictScalars k)
    ∘ₗ (castAlg Q q.h₂.symm).toLinearMap

theorem coe_topSecondProj (b : KLRAlgebra k Q ν') :
    (topSecondProj (q := q) b : KLRAlgebra k Q (q.γ + q.δ)) =
      castAlg Q q.h₂.symm b * oneConcat Q q.γ q.δ := rfl

theorem topSecondProj_mul (b : KLRAlgebra k Q ν') (c : TensorKLR Q q.γ q.δ) :
    topSecondProj (q := q) (b * castAlg Q q.h₂ (concat Q q.γ q.δ c)) =
      op c • topSecondProj (q := q) b := by
  apply Subtype.ext
  rw [coe_topSecondProj, coe_op_smul, coe_topSecondProj, unop_op, map_mul,
    castAlg_symm_castAlg, mul_assoc, concat_mul_oneConcat, mul_assoc, oneConcat_mul_concat]

theorem topSecondProj_castAlg (b : IndBimod Q q.γ q.δ) :
    topSecondProj (q := q) (castAlg Q q.h₂ (b : KLRAlgebra k Q (q.γ + q.δ))) = b := by
  apply Subtype.ext
  rw [coe_topSecondProj, castAlg_symm_castAlg]
  exact b.2

variable (q) (hsym : KLRSymm Q)

/-- The identity-shuffle coordinate `R(ν) → R(α) ⊗ R(β)` of Proposition 2.16 (right-module
form), applied to `r 1_{α,β}` along `q.h₁`. -/
def topFirstCoord : KLRAlgebra k Q ν →ₗ[k] TensorKLR Q q.α q.β :=
  Finsupp.lapply (shufOne : Shuffle (Seq.card_add' q.α q.β)) ∘ₗ
    (rightFreeEquiv q.α q.β hsym).symm.toLinearMap ∘ₗ
    ((Graded.leftIdealProj (oneConcat_idem (Q := Q) (ν := q.α) (ν' := q.β))).restrictScalars k)
    ∘ₗ (castAlg Q q.h₁.symm).toLinearMap

theorem topFirstCoord_apply (a : KLRAlgebra k Q ν) :
    topFirstCoord q hsym a = (rightFreeEquiv q.α q.β hsym).symm
      (Graded.leftIdealProj oneConcat_idem (castAlg Q q.h₁.symm a)) shufOne := rfl

theorem topFirstCoord_mul (a : KLRAlgebra k Q ν) (X : TensorKLR Q q.α q.β) :
    topFirstCoord q hsym (a * castAlg Q q.h₁ (concat Q q.α q.β X)) =
      topFirstCoord q hsym a * X := by
  have h : Graded.leftIdealProj oneConcat_idem
      (castAlg Q q.h₁.symm (a * castAlg Q q.h₁ (concat Q q.α q.β X))) =
      op X • Graded.leftIdealProj (oneConcat_idem (Q := Q) (ν := q.α) (ν' := q.β))
        (castAlg Q q.h₁.symm a) := by
    apply Subtype.ext
    rw [Graded.leftIdealProj_apply, coe_op_smul, Graded.leftIdealProj_apply, unop_op, map_mul,
      castAlg_symm_castAlg, mul_assoc, concat_mul_oneConcat, mul_assoc, oneConcat_mul_concat]
  rw [topFirstCoord_apply, h, rightFreeEquiv, rightFreeEquivOf_symm_op_smul,
    Finsupp.mapRange_apply]
  rfl

theorem topFirstCoord_oneConcat :
    topFirstCoord q hsym (castAlg Q q.h₁ (oneConcat Q q.α q.β)) = 1 := by
  have h : Graded.leftIdealProj oneConcat_idem
      (castAlg Q q.h₁.symm (castAlg Q q.h₁ (oneConcat Q q.α q.β))) =
      rightFreeEquiv q.α q.β hsym (Finsupp.single shufOne 1) := by
    apply Subtype.ext
    rw [Graded.leftIdealProj_apply, castAlg_symm_castAlg, oneConcat_idem.eq, rightFreeEquiv,
      rightFreeEquivOf_single_one, coe_hatWRevSubOf, hatWRevOf_one shufWord_spec]
  rw [topFirstCoord_apply, h, LinearEquiv.symm_apply_apply, Finsupp.single_eq_same]

/-- The trilinear map `X ⊗ b ↦ (y ↦ b ⊗ (X ⊗ 1) y)`. -/
def topOneIndCoordBil :
    TensorKLR Q q.α q.β →ₗ[k] IndBimod Q q.γ q.δ →ₗ[k] BotN →ₗ[k] Ind Q q.γ q.δ BotN :=
  LinearMap.mk₂ k
    (fun X b =>
      { toFun := fun y => BalancedTensor.tmul b
          ((X ⊗ₜ (1 : TensorKLR Q q.γ q.δ) : QuadAlg Q q) • y)
        map_add' := fun y y' => by rw [smul_add, BalancedTensor.tmul_add]
        map_smul' := fun c y => by
          rw [smul_algebra_smul_comm, BalancedTensor.tmul_smul]; rfl })
    (fun X X' b => by
      ext y
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, TensorProduct.add_tmul,
        add_smul, BalancedTensor.tmul_add])
    (fun c X b => by
      ext y
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
        ← TensorProduct.smul_tmul', smul_assoc, BalancedTensor.tmul_smul])
    (fun X b b' => by
      ext y
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, BalancedTensor.add_tmul])
    (fun c X b => by
      ext y
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, BalancedTensor.smul_tmul])

theorem topOneIndCoordBil_apply (X : TensorKLR Q q.α q.β) (b : IndBimod Q q.γ q.δ) (y : BotN) :
    topOneIndCoordBil q N X b y =
      BalancedTensor.tmul b ((X ⊗ₜ (1 : TensorKLR Q q.γ q.δ) : QuadAlg Q q) • y) := rfl

/-- The bilinear map `w, y ↦ ∑ π₂(w₂) ⊗ (π₁(w₁) ⊗ 1) y` on `(R(ν) ⊗ R(ν')) × BotN`, with `π₁`
the identity-shuffle coordinate and `π₂` the projection to `R(γ + δ) 1_{γ,δ}`. -/
def topOneIndCoord : TensorKLR Q ν ν' →ₗ[k] BotN →ₗ[k] Ind Q q.γ q.δ BotN :=
  TensorProduct.lift (topOneIndCoordBil q N) ∘ₗ
    TensorProduct.map (topFirstCoord q hsym) (topSecondProj (q := q))

theorem topOneIndCoord_tmul (a : KLRAlgebra k Q ν) (b : KLRAlgebra k Q ν') (y : BotN) :
    topOneIndCoord q N hsym (a ⊗ₜ b) y = BalancedTensor.tmul (topSecondProj (q := q) b)
      ((topFirstCoord q hsym a ⊗ₜ (1 : TensorKLR Q q.γ q.δ) : QuadAlg Q q) • y) := rfl

theorem topOneIndCoord_mul (w : TensorKLR Q ν ν') (r : QuadAlg Q q) (y : BotN) :
    topOneIndCoord q N hsym (w * quadTop q r) y = topOneIndCoord q N hsym w (r • y) := by
  induction r using TensorProduct.inductionOn with
  | add r r' hr hr' => rw [map_add, mul_add, map_add, LinearMap.add_apply, hr, hr', add_smul,
      map_add]
  | tmul X c =>
    induction w using TensorProduct.inductionOn with
    | add w w' hw hw' => rw [add_mul, map_add, LinearMap.add_apply, hw, hw', map_add,
        LinearMap.add_apply]
    | tmul a b =>
      rw [quadTop_tmul_concat, Algebra.TensorProduct.tmul_mul_tmul, topOneIndCoord_tmul,
        topOneIndCoord_tmul, topFirstCoord_mul, topSecondProj_mul, BalancedTensor.op_smul_tmul,
        botNModuleRight_smul, smul_smul, smul_smul, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, one_mul]

/-- **The left inverse `MackeyTop_λ ⊗_{R'} BotN → Ind_{γ,δ} BotN`** of `topOneIndMap`. -/
def topOneIndRetract : MackeyLeftInd Q N q →ₗ[k] Ind Q q.γ q.δ BotN :=
  BalancedTensor.lift
    (topOneIndCoord q N hsym ∘ₗ
      ((Graded.leftIdeal (quadTop (Q := Q) q 1)).subtype.restrictScalars k))
    (fun m r y => topOneIndCoord_mul q N hsym (m : TensorKLR Q ν ν') r y)

theorem topOneIndRetract_topOneIndMap (x : Ind Q q.γ q.δ BotN) :
    topOneIndRetract q N hsym (topOneIndMap q N x) = x := by
  induction x using BalancedTensor.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x x' hx hx' => rw [map_add, map_add, hx, hx']
  | tmul b y =>
    rw [topOneIndMap_tmul, BalancedTensor.smul_tmul']
    change topOneIndCoord q N hsym (((1 : KLRAlgebra k Q ν) ⊗ₜ
      castAlg Q q.h₂ (b : KLRAlgebra k Q (q.γ + q.δ)) : TensorKLR Q ν ν') * quadTop q 1) y = _
    rw [one_tmul_mul_quadTop_one, ← map_mul, show (b : KLRAlgebra k Q (q.γ + q.δ)) *
      oneConcat Q q.γ q.δ = b from b.2, topOneIndCoord_tmul, topFirstCoord_oneConcat,
      topSecondProj_castAlg, Algebra.TensorProduct.one_def.symm, one_smul]

include hsym in
/-- **`topOneIndMap` is injective.** -/
theorem topOneIndMap_injective : Function.Injective (topOneIndMap (Q := Q) q N) :=
  Function.LeftInverse.injective (topOneIndRetract_topOneIndMap q N hsym)

/-- The generators of `mackeyTopOneSpan` lie in the image: `(1 ⊗ b) · (1_λ ⊗ y)` is the image
of `b 1_{γ,δ} ⊗ y`. -/
theorem topOneIndMap_topSecondProj (b : KLRAlgebra k Q ν') (y : BotN) :
    topOneIndMap q N (BalancedTensor.tmul (topSecondProj (q := q) b) y) =
      (((1 : KLRAlgebra k Q ν) ⊗ₜ b : TensorKLR Q ν ν') •
        (BalancedTensor.tmul (mackeyTopOne q) y : MackeyLeftInd Q N q)) := by
  rw [topOneIndMap_tmul, BalancedTensor.smul_tmul', BalancedTensor.smul_tmul']
  congr 1
  apply Subtype.ext
  change ((1 : KLRAlgebra k Q ν) ⊗ₜ castAlg Q q.h₂
      ((topSecondProj (q := q) b : KLRAlgebra k Q (q.γ + q.δ))) : TensorKLR Q ν ν') *
      quadTop q 1 = ((1 : KLRAlgebra k Q ν) ⊗ₜ b : TensorKLR Q ν ν') * quadTop q 1
  rw [one_tmul_mul_quadTop_one, one_tmul_mul_quadTop_one, coe_topSecondProj, map_mul,
    castAlg_castAlg_symm, mul_assoc, ← map_mul, oneConcat_idem.eq]

theorem range_topOneIndMap :
    LinearMap.range (topOneIndMap (Q := Q) q N) = mackeyTopOneSpan q N := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact topOneIndMap_mem q N x
  · rw [mackeyTopOneSpan, Submodule.span_le]
    rintro _ ⟨⟨b, y⟩, rfl⟩
    exact ⟨_, topOneIndMap_topSecondProj q N b y⟩

/-- **`mackeyTopOneSpan q N ≅ R(γ + δ) 1_{γ,δ} ⊗_{R(γ) ⊗ R(δ)} BotN`.** -/
def topOneIndEquiv : Ind Q q.γ q.δ BotN ≃ₗ[k] mackeyTopOneSpan (Q := Q) q N :=
  (LinearEquiv.ofInjective (topOneIndMap (Q := Q) q N) (topOneIndMap_injective q N hsym)).trans
    (LinearEquiv.ofEq _ _ (range_topOneIndMap (Q := Q) q N))

theorem coe_topOneIndEquiv (x : Ind Q q.γ q.δ BotN) :
    (topOneIndEquiv q N hsym x : MackeyLeftInd Q N q) = topOneIndMap q N x := rfl

end KLRAlgebra

end Categorification.KLR

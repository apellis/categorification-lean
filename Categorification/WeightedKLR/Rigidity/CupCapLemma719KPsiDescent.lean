/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KPsiModel
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KModelViolated

/-!
# The inverse on the model kills the violated part

Webster, arXiv:1309.3796v3, Lemma 7.19 (K), proof of the inverse `Ψ`: the map `f_y` on the
model of `K̃^{λ⁺}_λ` vanishes on `V_λ K̃`, the part violated above the cap. A violated diagram of
`T̃^λ` acts on a generator `v ⊗ e Z` through a violated diagram `W` of `T̃^{λ⁺}`
(`midLeftAlg_tmul_midGen_violated`), and the reflection of `e W Z` vanishes in `T^{λ⁺}`.

## Main results

* `Stendhal.CupCap.plusFlip_of_mem_violated`: the reflection kills the violated diagrams.
* `Stendhal.CupCap.kModelMap_of_mem_midViolatedSub`: `f_y` vanishes on `V_λ K̃`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite InductionAlong
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Flip

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

/-- **The reflection kills the violated diagrams.** -/
theorem plusFlip_of_mem_violated {W : StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)}
    (hW : W ∈ StendhalAlgebra.violatedIdeal k Q (plusLabels Λ Λc j hj) (ν + ν₀)) :
    plusFlip j hj Q Λ Λc ν ν₀ W = 0 := by
  have h : TensorProductAlgebra.mk Q (plusLabels Λ Λc j hj) (ν + ν₀) W = 0 := by
    rw [← map_zero (TensorProductAlgebra.mk Q (plusLabels Λ Λc j hj) (ν + ν₀))]
    exact (RingCon.eq _).2 (((StendhalAlgebra.violatedIdeal k Q (plusLabels Λ Λc j hj)
      (ν + ν₀)).rel_iff _ 0).2 (by rw [sub_zero]; exact hW))
  rw [plusFlip, h, op_zero, map_zero]

end Flip

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} (j : ℕ) (hj : j ≤ ℓ)
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  (θ γ ν₀ : Multiset I)
  (Y : Type) [AddCommGroup Y] [Module k Y]
  [Module (cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) Y]
  [IsScalarTower k (cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) Y] (hQ : KLRSymm Q)
  (L' : Type) [AddCommGroup L'] [Module k L']
  [Module (TensorProductAlgebra k Q Λc ν₀) L'] [IsScalarTower k (TensorProductAlgebra k Q Λc ν₀) L']

set_option hygiene false in
local notation "Lc" => CapCoef Q Λc ν₀ L'
set_option hygiene false in
local notation "fM" => kModelMap j hj Q Λ Λc θ γ ν₀ Y hQ L'

variable {j hj Q Λ Λc θ γ ν₀ L'}
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : Lc), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}

/-- Every element of the corner of the maximum is a generator `e Z`. -/
theorem midGen_unop_val (z : Corner (midOp j hj Q Λ Λc (θ + γ) ν₀)) :
    midGen j hj Q Λ Λc (θ + γ) ν₀ z.1.unop = z := by
  refine Subtype.ext ?_
  rw [midGen_val]
  have h : z.1 * op (midStendhal j hj Q Λ Λc (θ + γ) ν₀ 1) = z.1 := z.2
  rw [op_mul, op_unop]
  exact h

variable (hR : MidKLRRel j hj Q Λ Λc (θ + γ) ν₀ Lc hL)

/-- **`f_y` vanishes on a violated diagram of `T̃^λ` acting on the model.** -/
theorem kModelMap_midLeftAlg_of_mem_violated (y : Y) {a : StendhalAlgebra k Q Λ (θ + γ)}
    (ha : a ∈ StendhalAlgebra.violatedIdeal k Q Λ (θ + γ))
    (t : MidModel j hj Q Λ Λc (θ + γ) ν₀ Lc) :
    fM y (midLeftAlg Lc hL hR a t) = 0 := by
  obtain ⟨W, hW, h⟩ := midLeftAlg_tmul_midGen_violated hR ha
  induction t using Ind.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul z v =>
    rw [← midGen_unop_val z, h, kModelMap_tmul, midGen_val, unop_op,
      plusFlip_of_mem_violated (TwoSidedIdeal.mul_mem_left _ _ _
        (TwoSidedIdeal.mul_mem_right _ _ _ hW)), zero_smul]
  | add s t hs ht => rw [map_add, map_add, hs, ht, add_zero]

/-- **`f_y` vanishes on `V_λ K̃`.** -/
theorem kModelMap_of_mem_midViolatedSub (y : Y) {w : MidLeftModel Lc hL hR}
    (hw : w ∈ midViolatedSub Lc hL hR) :
    fM y (show MidModel j hj Q Λ Λc (θ + γ) ν₀ Lc from w) = 0 := by
  suffices h : ∀ t : StendhalAlgebra k Q Λ (θ + γ),
      fM y (show MidModel j hj Q Λ Λc (θ + γ) ν₀ Lc from t • w) = 0 by
    simpa only [one_smul] using h 1
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, u, rfl⟩ := hx
    intro t
    rw [smul_smul]
    exact kModelMap_midLeftAlg_of_mem_violated Y hQ hR y
      (TwoSidedIdeal.mul_mem_left _ _ _ ha) u
  | zero => intro t; rw [smul_zero]; exact map_zero _
  | add x x' _ _ hx hx' =>
    intro t
    rw [smul_add]
    exact (map_add (fM y) _ _).trans (by rw [hx t, hx' t, add_zero])
  | smul c x _ hx =>
    intro t
    rw [smul_smul]
    exact hx (t * c)

variable (hP : PullOff k Q Λc ν₀ Lc) (hPL : PullOffLeft k Q Λc ν₀ Lc)
  (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))

/-- **`f_y` on `K̃^{λ⁺}_λ`**, through its model. -/
def kTildeMap (y : Y) :
    CapTilde k Q Λ Λc j hj (θ + γ) ν₀ Lc →+ KCutSrc j hj Q Λ Λc θ γ ν₀ Y hQ L' where
  toFun c := fM y (ofMidBimod Lc hL hR (midCapModelEquiv hP hPL hκ hR c))
  map_zero' := by rw [map_zero]; exact map_zero (fM y)
  map_add' c c' := by rw [map_add]; exact map_add (fM y) _ _

/-- **`f_y` vanishes on the violated diagrams of `K̃^{λ⁺}_λ`.** -/
theorem kTildeMap_of_mem_violated (y : Y) {c : CapTilde k Q Λ Λc j hj (θ + γ) ν₀ Lc}
    (hc : c ∈ violated k Q Λ Λc j hj (θ + γ) ν₀ Lc) :
    kTildeMap Y hQ hR hP hPL hκ y c = 0 := by
  classical
  choose ρ₃ hρ₃ using fun w => exists_reduced (Multiset.card (stendhalWeight (ℓ + 2)
    ((θ + γ) + ν₀))) w
  exact kModelMap_of_mem_midViolatedSub Y hQ hR y
    (midCapModelEquiv_mem_of_mem_violated hP hPL hκ hR hρ₃ hc)

/-- **`f_y` on `K^{λ⁺}_λ`**: it descends from `K̃^{λ⁺}_λ`. -/
def kCapMap (y : Y) :
    ReflectedCap j hj Q Λ Λc (θ + γ) ν₀ Lc →+ KCutSrc j hj Q Λ Λc θ γ ν₀ Y hQ L' :=
  QuotientAddGroup.lift (violated k Q Λ Λc j hj (θ + γ) ν₀ Lc).toAddSubgroup
    (kTildeMap Y hQ hR hP hPL hκ y) fun _ hc => kTildeMap_of_mem_violated Y hQ hR hP hPL hκ y hc

theorem kCapMap_toRefl (y : Y) (c : CapTilde k Q Λ Λc j hj (θ + γ) ν₀ Lc) :
    kCapMap Y hQ hR hP hPL hκ y (toRefl c) = kTildeMap Y hQ hR hP hPL hκ y c :=
  rfl

/-- **`f_y` is `T^{λ⁺}`-linear** on the reflection of `K^{λ⁺}_λ`. -/
theorem kCapMap_smul (y : Y)
    (s : TensorProductAlgebra k Q (plusLabels Λ Λc j hj) ((θ + γ) + ν₀))
    (r : ReflectedCap j hj Q Λ Λc (θ + γ) ν₀ Lc) :
    kCapMap Y hQ hR hP hPL hκ y (s • r) = s • kCapMap Y hQ hR hP hPL hκ y r := by
  obtain ⟨c, rfl⟩ := toRefl_surjective r
  obtain ⟨b, rfl⟩ := RingCon.mk'_surjective _ s
  obtain ⟨a, rfl⟩ := topMap_surjective' (k := k) (Q := Q) (Λ := plusLabels Λ Λc j hj)
    (ν := (θ + γ) + ν₀) b
  change kCapMap Y hQ hR hP hPL hκ y (TensorProductAlgebra.mk Q (plusLabels Λ Λc j hj)
    ((θ + γ) + ν₀) (botMap k Q Λ Λc j hj (θ + γ) ν₀ a) • toRefl c) = _
  rw [mk_smul_toRefl, kCapMap_toRefl, kCapMap_toRefl]
  change fM y (ofMidBimod Lc hL hR (midCapModelEquiv hP hPL hκ hR (_ • c))) = _
  rw [map_smul, ofMidBimod, midBimod_smul, midEnvAlg_mk, map_one, Module.End.one_apply,
    kModelMap_smul, unop_op, plusFlip_botMap, hflip_hflip]
  rfl

/-- **`f_y` as a `T^{λ⁺}`-linear map** out of the reflection of `K^{λ⁺}_λ`. -/
def kCapLin (y : Y) :
    ReflectedCap j hj Q Λ Λc (θ + γ) ν₀ Lc →ₗ[TensorProductAlgebra k Q (plusLabels Λ Λc j hj)
      ((θ + γ) + ν₀)] KCutSrc j hj Q Λ Λc θ γ ν₀ Y hQ L' where
  toFun := kCapMap Y hQ hR hP hPL hκ y
  map_add' := map_add _
  map_smul' := kCapMap_smul Y hQ hR hP hPL hκ y

end Categorification.Stendhal.CupCap

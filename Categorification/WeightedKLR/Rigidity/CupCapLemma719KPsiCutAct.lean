/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KPsiCut

/-!
# The right action of `T^λ` on the maps `f_y`

Webster, arXiv:1309.3796v3, Lemma 7.19 (K), proof of the inverse `Ψ`: a diagram `a` of `T^λ`
acts on the reflection of `K^{λ⁺}_λ` from the right as its mirror image acts on the model from
the left (`kCapLin_op_mk_smul`). When the mirror image slides through the model as a diagram
`Y₀` of `T̃^{λ⁺}`, the intertwining condition of `y ↦ f_y` at `a` reduces to an identity on the
unit of `S_+(Y ⊠ L')` (`kCapLin_op_mk_smul_of_slide`).

## Main results

* `Stendhal.CupCap.kCapLin_op_mk_smul`: the right action through the model.
* `Stendhal.CupCap.kCapLin_op_mk_smul_of_slide`: the reduction to the unit.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite InductionAlong
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {θ γ ν₀ : Multiset I}
  (Y : Type) [AddCommGroup Y] [Module k Y]
  [Module (cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) Y]
  [IsScalarTower k (cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) Y] (hQ : KLRSymm Q)
  {L' : Type} [AddCommGroup L'] [Module k L']
  [Module (TensorProductAlgebra k Q Λc ν₀) L'] [IsScalarTower k (TensorProductAlgebra k Q Λc ν₀) L']

set_option hygiene false in
local notation "Np" => BlocksOneStepInput Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ
  (PlusInput Q Λ Λc j hj θ ν₀ γ (MidSpect (k := k) Y L'))
set_option hygiene false in
local notation "U" y:max v:max =>
  kSrcUnit j hj Q Λ Λc θ γ ν₀ Y hQ L' (show Np from midSpectTmul (k := k) y v)
set_option hygiene false in
local notation "Lc" => CapCoef Q Λc ν₀ L'
set_option hygiene false in
local notation "fM" => kModelMap j hj Q Λ Λc θ γ ν₀ Y hQ L'
set_option hygiene false in
local notation "mkp" => TensorProductAlgebra.mk Q (plusLabels Λ Λc j hj) ((θ + γ) + ν₀)
set_option hygiene false in
local notation "botp" => botMap k Q Λ Λc j hj (θ + γ) ν₀
set_option hygiene false in
local notation "Rp" => KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj))
  (stendhalWeight (ℓ + 2) ((θ + γ) + ν₀))
set_option hygiene false in
local notation "Rλ" => KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ (θ + γ))
set_option hygiene false in
local notation "fl" => plusFlip j hj Q Λ Λc (θ + γ) ν₀

variable {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : Lc), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}
  (hR : MidKLRRel j hj Q Λ Λc (θ + γ) ν₀ Lc hL)
  (hP : PullOff k Q Λc ν₀ Lc) (hPL : PullOffLeft k Q Λc ν₀ Lc)
  (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))

/-- **A diagram of `T^λ` acts on the reflection from the right as its mirror image acts on the
model.** -/
theorem kCapLin_op_mk_smul (y : Y) (a : Rλ) (c : CapTilde k Q Λ Λc j hj (θ + γ) ν₀ Lc) :
    kCapLin Y hQ hR hP hPL hκ y (op (TensorProductAlgebra.mk Q Λ (θ + γ)
        (topMap k Q Λ (θ + γ) a)) • toRefl c) =
      fM y (midKLRAct hR (hflip a)
        (ofMidBimod Lc hL hR (midCapModelEquiv hP hPL hκ hR c))) := by
  rw [op_mk_smul_toRefl]
  change fM y (ofMidBimod Lc hL hR (midCapModelEquiv hP hPL hκ hR (_ • c))) = _
  rw [map_smul, ofMidBimod, midBimod_smul, midEnvAlg_mk, op_one, one_smul, midLeftAlg_topMap]
  rfl

/-- **The reduction to the unit**: if the mirror image of `a` slides through the model as `Y₀`,
and the mirror image of `Y₀` takes the unit at `y` to the unit at `y'`, then
`f_{y'} = f_y(· a)`. -/
theorem kCapLin_op_mk_smul_of_slide (y y' : Y) (a : Rλ) (Y₀ : Rp)
    (ha : ∀ (Z : Rp) (v : Lc), midKLRAct hR (hflip a)
        (Ind.tmul (midGen j hj Q Λ Λc (θ + γ) ν₀ (botp Z)) v) =
      Ind.tmul (midGen j hj Q Λ Λc (θ + γ) ν₀ (botp (Y₀ * Z))) v)
    (hU : ∀ v : L', U y' v = mkp (botp (hflip Y₀)) • U y v)
    (r : ReflectedCap j hj Q Λ Λc (θ + γ) ν₀ Lc) :
    kCapLin Y hQ hR hP hPL hκ y' r = kCapLin Y hQ hR hP hPL hκ y
      (op (TensorProductAlgebra.mk Q Λ (θ + γ) (topMap k Q Λ (θ + γ) a)) • r) := by
  obtain ⟨c, rfl⟩ := toRefl_surjective r
  rw [kCapLin_op_mk_smul]
  change fM y' (ofMidBimod Lc hL hR (midCapModelEquiv hP hPL hκ hR c)) = _
  generalize ofMidBimod Lc hL hR (midCapModelEquiv hP hPL hκ hR c) = w
  induction w using Ind.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul z v =>
    obtain ⟨Z, hZ⟩ := topMap_surjective' (k := k) (Q := Q) (Λ := plusLabels Λ Λc j hj)
      (ν := (θ + γ) + ν₀) z.1.unop
    have hz : z = midGen j hj Q Λ Λc (θ + γ) ν₀ (botp Z) := by
      rw [← midGen_unop_val z]
      exact congrArg _ hZ.symm
    rw [hz, ha, kModelMap_tmul, kModelMap_tmul, midGen_val, midGen_val, unop_op, unop_op,
      plusFlip_mul, plusFlip_mul, mul_smul, mul_smul, kSrc_flip_midStendhal_one_smul_unit,
      kSrc_flip_midStendhal_one_smul_unit, map_mul, plusFlip_mul, mul_smul, plusFlip_botMap
        (a := Y₀), hU]
  | add s t hs ht => rw [map_add, map_add, map_add, hs, ht]

end Categorification.Stendhal.CupCap

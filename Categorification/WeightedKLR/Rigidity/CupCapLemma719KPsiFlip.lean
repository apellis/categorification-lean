/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KSrcMid
import Categorification.WeightedKLR.Rigidity.CupCapMidNull

/-!
# The mirror image of the diagrams at the maximum

Webster, arXiv:1309.3796v3, Lemma 7.19 (K), proof of the inverse `Ψ`: the model of `K̃^{λ⁺}_λ`
is a right `T̃^{λ⁺}`-module, while the right side `S_+(Y ⊠ L')` is a left one; the inverse
passes between them by the horizontal reflection. Placing a diagram at the maximum commutes
with the reflection (`hflip_insertMap`, `hflip_midMapKLR`), so the reflection of a diagram at
the maximum acts on the unit of the right side as its mirror image acts on `L'`
(`kSrc_flip_midBot_smul_unit`). In particular the reflection of the unit of the maximum fixes the
unit (`kSrc_flip_midStendhal_one_smul_unit`).

## Main definitions

* `Stendhal.CupCap.plusFlip`: the reflection `T̃^{λ⁺} → T^{λ⁺}`, an anti-homomorphism.

## Main results

* `Stendhal.CupCap.hflip_insertMap`: a diagram placed in a window, reflected.
* `Stendhal.CupCap.plusFlip_midBot`: the reflection of a diagram at the maximum.
* `Stendhal.CupCap.kSrc_flip_midBot_smul_unit`,
  `Stendhal.CupCap.kSrc_flip_midStendhal_one_smul_unit`: their action on the unit.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Insert

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "Rc" => KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)
local notation "ι" => insertMap (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc
local notation "E" s:max n:max hn:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s n hn)

theorem hflip_eSum_insertSet (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m) :
    hflip (E s n hn) = E s n hn := by
  simp only [KLRAlgebra.eSum, hflip_sum, hflip_e]

theorem eSum_insertSet_mul_x (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m)
    (a : Fin (Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀)))) :
    E s n hn * KLRAlgebra.x a = KLRAlgebra.x a * E s n hn := by
  simp only [KLRAlgebra.eSum, Finset.sum_mul, Finset.mul_sum, e_mul_x]

/-- **Placing a diagram in a window commutes with the reflection.** -/
theorem hflip_insertMap (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m) (g : Rc) :
    hflip (ι s n hn g) = ι s n hn (hflip g) := by
  let S : Subalgebra k Rc :=
    { carrier := {g | hflip (ι s n hn g) = ι s n hn (hflip g)}
      mul_mem' := fun {a b} (ha : hflip (ι s n hn a) = _) (hb : hflip (ι s n hn b) = _) => by
        change hflip (ι s n hn (a * b)) = ι s n hn (hflip (a * b))
        rw [insertMap_mul, hflip_mul, hflip_mul, insertMap_mul, ha, hb]
      add_mem' := fun {a b} (ha : hflip (ι s n hn a) = _) (hb : hflip (ι s n hn b) = _) => by
        change hflip (ι s n hn (a + b)) = ι s n hn (hflip (a + b))
        rw [insertMap_add, hflip_add, hflip_add, insertMap_add, ha, hb]
      algebraMap_mem' := fun c => by
        change hflip (ι s n hn (algebraMap k Rc c)) = ι s n hn (hflip (algebraMap k Rc c))
        rw [hflip_algebraMap, insertMap_algebraMap, hflip_smul, hflip_eSum_insertSet] }
  refine mem_of_gens (AlgHom.id k Rc) S (fun w => ?_) (fun b => ?_) (fun q => ?_) g
  · change hflip (ι s n hn (e w)) = ι s n hn (hflip (e w))
    rw [hflip_e, insertMap_e, hflip_e]
  · change hflip (ι s n hn (x b)) = ι s n hn (hflip (x b))
    rw [hflip_x, insertMap_x, hflip_mul, hflip_x, hflip_eSum_insertSet, eSum_insertSet_mul_x]
  · change hflip (ι s n hn (ψ q)) = ι s n hn (hflip (ψ q))
    rw [hflip_ψ]
    by_cases hq : q + 1 < Multiset.card (stendhalWeight 2 ν₀)
    · rw [insertMap_ψ s hn hq, hflip_mul, hflip_ψ, hflip_eSum_insertSet,
        eSum_insertSet_mul_ψ s hn hq]
    · rw [ψ_eq_zero q (by omega)]
      simp [insertMap]

/-- **Placing a diagram at the maximum commutes with the reflection.** -/
theorem hflip_midMapKLR (g : Rc) :
    hflip (midMapKLR j hj Q Λ Λc ν ν₀ g) = midMapKLR j hj Q Λ Λc ν ν₀ (hflip g) := by
  simp only [midMapKLR, hflip_sum, hflip_insertMap]

end Insert

section Order

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}
  {ℓ' : ℕ} (Λ' : Fin ℓ' → I →₀ ℕ) (ν' : Multiset I)

theorem orderProjection_redOrderedIdem :
    orderProjection Q Λ' ν' (StendhalAlgebraAllOrders.redOrderedIdem k Q Λ' ν') = 1 :=
  Subtype.ext StendhalAlgebraAllOrders.isIdempotentElem_redOrderedIdem.eq

/-- The red-ordered idempotent is the unit of `T^λ`. -/
theorem tensorOfKLR_redOrderedKLR : tensorOfKLR Q Λ' ν' (redOrderedKLR k Q Λ' ν') = 1 := by
  rw [tensorOfKLR, ofKLR_redOrderedKLR, orderProjection_redOrderedIdem, map_one]

theorem hflip_redOrderedKLR : hflip (redOrderedKLR k Q Λ' ν') = redOrderedKLR k Q Λ' ν' := by
  simp only [redOrderedKLR, hflip_sum, hflip_e]

end Order

section Flip

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} (j : ℕ) (hj : j ≤ ℓ)
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  (ν ν₀ : Multiset I)

local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
local notation "mkP" => TensorProductAlgebra.mk Q (plusLabels Λ Λc j hj) (ν + ν₀)

/-- **The reflection `T̃^{λ⁺} → T^{λ⁺}`**: the image of a diagram, reflected horizontally. It
reverses products. -/
def plusFlip (Z : Tp) : TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀) :=
  (tensorFlipRingEquiv (Q := Q) (Λ := plusLabels Λ Λc j hj) (ν + ν₀)).symm (op (mkP Z))

variable {j hj Q Λ Λc ν ν₀}

theorem plusFlip_mul (a b : Tp) :
    plusFlip j hj Q Λ Λc ν ν₀ (a * b) =
      plusFlip j hj Q Λ Λc ν ν₀ b * plusFlip j hj Q Λ Λc ν ν₀ a := by
  simp only [plusFlip, map_mul, op_mul]

theorem plusFlip_add (a b : Tp) :
    plusFlip j hj Q Λ Λc ν ν₀ (a + b) =
      plusFlip j hj Q Λ Λc ν ν₀ a + plusFlip j hj Q Λ Λc ν ν₀ b := by
  simp only [plusFlip, map_add, op_add]

theorem plusFlip_zero : plusFlip j hj Q Λ Λc ν ν₀ 0 = 0 := by
  simp only [plusFlip, map_zero, op_zero]

/-- The reflection of the image of a diagram is the image of its mirror image. -/
theorem plusFlip_botMap
    (a : KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))) :
    plusFlip j hj Q Λ Λc ν ν₀ (botMap k Q Λ Λc j hj ν ν₀ a) =
      mkP (botMap k Q Λ Λc j hj ν ν₀ (hflip a)) :=
  tensorFlipRingEquiv_symm_op_mk a

/-- **The reflection of a diagram at the maximum** is the image of its mirror image at the
maximum. -/
theorem plusFlip_midBot (g : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) :
    plusFlip j hj Q Λ Λc ν ν₀ (midBot j hj Q Λ Λc ν ν₀ g) =
      mkP (midBot j hj Q Λ Λc ν ν₀ (hflip g)) := by
  rw [midBot_apply, plusFlip_botMap, hflip_midMapKLR]
  rfl

end Flip

section Unit

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} (j : ℕ) (hj : j ≤ ℓ)
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  (θ γ ν₀ : Multiset I)
  (Y : Type) [AddCommGroup Y] [Module k Y]
  [Module (cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) Y]
  [IsScalarTower k (cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) Y] (hQ : KLRSymm Q)
  (L' : Type) [AddCommGroup L'] [Module k L']
  [Module (TensorProductAlgebra k Q Λc ν₀) L'] [IsScalarTower k (TensorProductAlgebra k Q Λc ν₀) L']

set_option hygiene false in
local notation "Np" => BlocksOneStepInput Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ
  (PlusInput Q Λ Λc j hj θ ν₀ γ (MidSpect (k := k) Y L'))
set_option hygiene false in
local notation "U" y:max v:max =>
  kSrcUnit j hj Q Λ Λc θ γ ν₀ Y hQ L' (show Np from midSpectTmul (k := k) y v)

/-- **The reflection of a diagram at the maximum acts on the unit** as its mirror image acts on
`L'`. -/
theorem kSrc_flip_midBot_smul_unit (g : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀))
    (y : Y) (v : L') :
    plusFlip j hj Q Λ Λc (θ + γ) ν₀ (midBot j hj Q Λ Λc (θ + γ) ν₀ g) • U y v =
      U y (tensorOfKLR Q Λc ν₀ (hflip g) • v) := by
  rw [plusFlip_midBot]
  exact kSrc_midBot_smul_unit j hj Q Λ Λc θ γ ν₀ Y hQ L' (hflip g) y v

/-- **The reflection of the unit of the maximum fixes the unit.** -/
theorem kSrc_flip_midStendhal_one_smul_unit (y : Y) (v : L') :
    plusFlip j hj Q Λ Λc (θ + γ) ν₀ (midStendhal j hj Q Λ Λc (θ + γ) ν₀ 1) • U y v = U y v := by
  rw [midStendhal_one_eq_midBot, kSrc_flip_midBot_smul_unit, hflip_redOrderedKLR,
    tensorOfKLR_redOrderedKLR, one_smul]

end Unit

end Categorification.Stendhal.CupCap

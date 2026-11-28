/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationPlusOuterCut
import Categorification.WeightedKLR.RedStrands.PartialStandardizationSpectatorTensorNatural

/-!
# Naturality of the outer standardizations of `S_+`

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3 (the
computation of `S_+(Z ⊠ L)` in the proof of Lemma 7.19), toward the derived form of
Lemma 7.19 (K). The identifications `plusOuterPair Z ⊠ L ≅ plusOuterStd (Z ⊠ L)`
(`plusOuterTensorEquiv`) and `singOuter (Z) ≅ plusOuterPair Z` over the two blocks at the cut
(`cutPairEquiv`) are natural in the module `Z` over the outer singleton blocks.

## Main definitions

* `Stendhal.CupCap.plusTensorInputMap`: `g ⊠ L : Z ⊠ L → Z' ⊠ L`.
* `Stendhal.CupCap.plusOuterPairFunctor`: `plusOuterPair` as a functor.

## Main results

* `Stendhal.CupCap.plusOuterTensorEquiv_natural`: naturality of `plusOuterTensorEquiv`.
* `Stendhal.CupCap.cutPairEquiv_natural`: naturality of `cutPairEquiv`.
-/

set_option backward.isDefEq.respectTransparency false

universe u

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory KLR KLRAlgebra TypeA
open scoped TensorProduct

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

variable {I k : Type u} [DecidableEq I] [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q)

section Tensor

variable {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ) (j : ℕ) (hj : j ≤ ℓ)
  (β : Multiset I) (θh : Fin j → Multiset I) (θt : Fin (ℓ - j) → Multiset I)

set_option hygiene false in
local notation "Hd" => TensorProductAlgebra k Q (Λ ∘ Fin.castLE hj) (singWeight j θh)
set_option hygiene false in
local notation "Tl" => TensorProductAlgebra k Q (plusTailLabels Λ j hj) (singWeight (ℓ - j) θt)
set_option hygiene false in
local notation "Cp" => TensorProductAlgebra k Q Λc β
set_option hygiene false in
local notation "Sh" => singAlg Q j (Λ ∘ Fin.castLE hj) θh
set_option hygiene false in
local notation "St" => singAlg Q (ℓ - j) (plusTailLabels Λ j hj) θt

variable {Z Z' : ModuleCat.{u} (Sh ⊗[k] St)} (g : Z ⟶ Z') (L : Type u) [AddCommGroup L]
  [Module k L] [Module Cp L] [IsScalarTower k Cp L]

/-- `g ⊠ L : Z ⊠ L → Z' ⊠ L`. -/
def plusTensorInputMap :
    plusTensorInput Q Λ Λc j hj β θh θt Z L ⟶ plusTensorInput Q Λ Λc j hj β θh θt Z' L :=
  ModuleCat.ofHom (midSpectMap (B := Cp) g.hom)

/-- `plusOuterPair` as a functor. -/
abbrev plusOuterPairFunctor : ModuleCat.{u} (Sh ⊗[k] St) ⥤ ModuleCat.{u} (Hd ⊗[k] Tl) :=
  singStd Q hQ j (Λ ∘ Fin.castLE hj) θh St ⋙
    ModuleCat.restrictScalars.{u} (plusTensorRotIn Q Λ j hj θh θt).toRingHom ⋙
    singStd Q hQ (ℓ - j) (plusTailLabels Λ j hj) θt (AlgCat.of k Hd) ⋙
    ModuleCat.restrictScalars.{u} (plusTensorRotOut Q Λ j hj θh θt).toRingHom

/-- The standardization of the first block of `Z ⊠ L` is natural. -/
theorem plusTensorFirst_natural (x : (singStd Q hQ j (Λ ∘ Fin.castLE hj) θh St).obj Z) (v : L) :
    (plusTensorFirst Q hQ Λ Λc j hj β θh θt Z' L).equiv
        (((singStd Q hQ j (Λ ∘ Fin.castLE hj) θh St).map g).hom x ⊗ₜ[k] v) =
      ((singStd Q hQ j (Λ ∘ Fin.castLE hj) θh (AlgCat.of k (Cp ⊗[k] St))).map
        (plusTensorInputMap Q Λ Λc j hj β θh θt g L)).hom
        ((plusTensorFirst Q hQ Λ Λc j hj β θh θt Z L).equiv (x ⊗ₜ[k] v)) :=
  singStdTensorEquiv_natural Q hQ j (Λ ∘ Fin.castLE hj) θh (plusTensorSwap Q Λ Λc j hj β θt)
    (plusTensorFirstIn Q Λ Λc j hj β θh θt Z L) (plusTensorFirstIn Q Λ Λc j hj β θh θt Z' L)
    g (plusTensorInputMap Q Λ Λc j hj β θh θt g L) (fun _ _ => rfl) x v

/-- The standardization of the last block of `Z ⊠ L` is natural. -/
theorem plusTensorSecond_natural
    (x : (singStd Q hQ (ℓ - j) (plusTailLabels Λ j hj) θt (AlgCat.of k Hd)).obj
      ((ModuleCat.restrictScalars.{u} (plusTensorRotIn Q Λ j hj θh θt).toRingHom).obj
        ((singStd Q hQ j (Λ ∘ Fin.castLE hj) θh St).obj Z))) (v : L) :
    (plusTensorSecond Q hQ Λ Λc j hj β θh θt Z' L).equiv
        (((singStd Q hQ (ℓ - j) (plusTailLabels Λ j hj) θt (AlgCat.of k Hd)).map
          ((ModuleCat.restrictScalars.{u} (plusTensorRotIn Q Λ j hj θh θt).toRingHom).map
            ((singStd Q hQ j (Λ ∘ Fin.castLE hj) θh St).map g))).hom x ⊗ₜ[k] v) =
      ((singStd Q hQ (ℓ - j) (plusTailLabels Λ j hj) θt (AlgCat.of k (Hd ⊗[k] Cp))).map
        ((ModuleCat.restrictScalars.{u}
          (R := St ⊗[k] (AlgCat.of k (Hd ⊗[k] Cp) : AlgCat.{u} k))
          (plusTensorRotP Q Λ Λc j hj β θh θt)).map
          ((singStd Q hQ j (Λ ∘ Fin.castLE hj) θh (AlgCat.of k (Cp ⊗[k] St))).map
            (plusTensorInputMap Q Λ Λc j hj β θh θt g L)))).hom
        ((plusTensorSecond Q hQ Λ Λc j hj β θh θt Z L).equiv (x ⊗ₜ[k] v)) := by
  have hm : ∀ m w, (plusTensorSecondIn Q hQ Λ Λc j hj β θh θt Z' L).equiv
      (((ModuleCat.restrictScalars.{u} (plusTensorRotIn Q Λ j hj θh θt).toRingHom).map
        ((singStd Q hQ j (Λ ∘ Fin.castLE hj) θh St).map g)).hom m ⊗ₜ[k] w) =
      ((ModuleCat.restrictScalars.{u} (R := St ⊗[k] (AlgCat.of k (Hd ⊗[k] Cp) : AlgCat.{u} k))
        (plusTensorRotP Q Λ Λc j hj β θh θt)).map
        ((singStd Q hQ j (Λ ∘ Fin.castLE hj) θh (AlgCat.of k (Cp ⊗[k] St))).map
          (plusTensorInputMap Q Λ Λc j hj β θh θt g L))).hom
        ((plusTensorSecondIn Q hQ Λ Λc j hj β θh θt Z L).equiv (m ⊗ₜ[k] w)) :=
    fun m w => plusTensorFirst_natural Q hQ Λ Λc j hj β θh θt g L m w
  have key := singStdTensorEquiv_natural Q hQ (ℓ - j) (plusTailLabels Λ j hj) θt
    (plusTensorMid Q Λ Λc j hj β θh) (plusTensorSecondIn Q hQ Λ Λc j hj β θh θt Z L)
    (plusTensorSecondIn Q hQ Λ Λc j hj β θh θt Z' L) _ _ hm x v
  exact key

/-- `plusOuterTensorEquiv` is natural on pure tensors. -/
theorem plusOuterTensorEquiv_natural_tmul (y : plusOuterPair Q hQ Λ j hj θh θt Z) (v : L) :
    plusOuterTensorEquiv Q hQ Λ Λc j hj β θh θt Z' L
        (midSpectTmul (k := k) (((plusOuterPairFunctor Q hQ Λ j hj θh θt).map g).hom y) v) =
      ((plusOuterStd Q hQ Λ Λc j hj β θh θt).map
        (plusTensorInputMap Q Λ Λc j hj β θh θt g L)).hom
        (plusOuterTensorEquiv Q hQ Λ Λc j hj β θh θt Z L (midSpectTmul (k := k) y v)) :=
  plusTensorSecond_natural Q hQ Λ Λc j hj β θh θt g L y v

/-- **`plusOuterPair Z ⊠ L ≅ plusOuterStd (Z ⊠ L)` is natural in `Z`.** -/
theorem plusOuterTensorEquiv_natural (z : MidSpect (k := k) (plusOuterPair Q hQ Λ j hj θh θt Z) L) :
    plusOuterTensorEquiv Q hQ Λ Λc j hj β θh θt Z' L
        (midSpectMap (B := Cp) ((plusOuterPairFunctor Q hQ Λ j hj θh θt).map g).hom z) =
      ((plusOuterStd Q hQ Λ Λc j hj β θh θt).map
        (plusTensorInputMap Q Λ Λc j hj β θh θt g L)).hom
        (plusOuterTensorEquiv Q hQ Λ Λc j hj β θh θt Z L z) := by
  induction (show plusOuterPair Q hQ Λ j hj θh θt Z ⊗[k] L from z) using
    TensorProduct.inductionOn with
  | tmul y v => exact plusOuterTensorEquiv_natural_tmul Q hQ Λ Λc j hj β θh θt g L y v
  | add x y hx hy =>
    exact ((congrArg (plusOuterTensorEquiv Q hQ Λ Λc j hj β θh θt Z' L) (map_add _ x y)).trans
      (map_add _ _ _)).trans ((congrArg₂ (· + ·) hx hy).trans
        ((map_add _ _ _).symm.trans (congrArg _ (map_add _ x y).symm)))

end Tensor

section Cut

variable {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (j : ℕ) (hj : j ≤ ℓ) (θ : Fin (j + (ℓ - j)) → Multiset I)

set_option hygiene false in
local notation "Λ'" => Λ ∘ Fin.cast (Nat.add_sub_of_le hj)
set_option hygiene false in
local notation "Sh" => singAlg Q j (Λ' ∘ Fin.castAdd (ℓ - j)) (θ ∘ Fin.castAdd (ℓ - j))
set_option hygiene false in
local notation "St" => singAlg Q (ℓ - j) (Λ' ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j)
set_option hygiene false in
local notation "w₁" => singWeight j (θ ∘ Fin.castAdd (ℓ - j))
set_option hygiene false in
local notation "w₂" => singWeight (ℓ - j) (θ ∘ Fin.natAdd j)
set_option hygiene false in
local notation "Kk" => (AlgCat.of k k : AlgCat.{u} k)
set_option hygiene false in
local notation "Hd" => TensorProductAlgebra k Q (Λ' ∘ Fin.castAdd (ℓ - j)) w₁

variable {Z Z' : ModuleCat.{u} (Sh ⊗[k] St)} (g : Z ⟶ Z')

/-- `cutPairZ` on maps. -/
def cutPairZMap : cutPairZ Q Λ j hj θ Z ⟶ cutPairZ Q Λ j hj θ Z' :=
  (ModuleCat.restrictScalars.{u} (Algebra.TensorProduct.map (AlgHom.id k _)
    (Algebra.TensorProduct.rid k k St).toAlgHom).toRingHom).map g

/-- `CutPairSource` on maps. -/
def cutPairSourceMap :
    CutPairSource Q hQ Λ j hj θ Z →ₗ[cutFactorAlgebra Q Λ' w₁ w₂] CutPairSource Q hQ Λ j hj θ Z' :=
  cutSpectInputHom (a := j) (r := ℓ - j) Q Λ' w₁ w₂
    ((singOuter Q hQ j (ℓ - j) Λ' θ Kk).map (cutPairZMap Q Λ j hj θ g)).hom

/-- `cutPairTarget` on maps. -/
def cutPairTargetMap : cutPairTarget Q hQ Λ j hj θ Z ⟶ cutPairTarget Q hQ Λ j hj θ Z' :=
  (ModuleCat.restrictScalars.{u} (cutPairIdent Q Λ j hj θ).toRingHom).map
    ((plusOuterPairFunctor Q hQ Λ j hj (θ ∘ Fin.castAdd (ℓ - j)) (θ ∘ Fin.natAdd j)).map g)

/-- The change of spectator of the last block is natural. -/
theorem cutPairMid_natural
    (z : cutPairMidL Q hQ Λ j hj θ Z) :
    (cutPairMid Q hQ Λ j hj θ Z').equiv
        (((ModuleCat.restrictScalars.{u}
          (Algebra.TensorProduct.leftComm k St Hd Kk).toAlgHom.toRingHom).map
          ((singStd Q hQ j (Λ' ∘ Fin.castAdd (ℓ - j)) (θ ∘ Fin.castAdd (ℓ - j))
            (AlgCat.of k (St ⊗[k] Kk))).map (cutPairZMap Q Λ j hj θ g))).hom z) =
      ((ModuleCat.restrictScalars.{u}
        (plusTensorRotIn Q Λ j hj (θ ∘ Fin.castAdd (ℓ - j)) (θ ∘ Fin.natAdd j)).toRingHom).map
        ((singStd Q hQ j (Λ' ∘ Fin.castAdd (ℓ - j)) (θ ∘ Fin.castAdd (ℓ - j)) St).map g)).hom
        ((cutPairMid Q hQ Λ j hj θ Z).equiv z) :=
  singStdSpectatorEquiv_natural Q hQ j (Λ' ∘ Fin.castAdd (ℓ - j)) (θ ∘ Fin.castAdd (ℓ - j))
    (cutPairRidLast Q Λ j hj θ)
    (⟨AddEquiv.refl _, fun _ _ => rfl⟩ :
      SpectatorEquiv Sh (cutPairRidLast Q Λ j hj θ) (cutPairZ Q Λ j hj θ Z) Z)
    (⟨AddEquiv.refl _, fun _ _ => rfl⟩ :
      SpectatorEquiv Sh (cutPairRidLast Q Λ j hj θ) (cutPairZ Q Λ j hj θ Z') Z')
    (cutPairZMap Q Λ j hj θ g) g (fun _ => rfl) z

/-- **The standardizations of the two blocks at the cut are naturally `plusOuterPair`.** -/
theorem cutPairEquiv_natural (x : CutPairSource Q hQ Λ j hj θ Z) :
    cutPairEquiv Q hQ Λ j hj θ Z' (cutPairSourceMap Q hQ Λ j hj θ g x) =
      (cutPairTargetMap Q hQ Λ j hj θ g).hom (cutPairEquiv Q hQ Λ j hj θ Z x) := by
  have key := singStdSpectatorEquiv_natural Q hQ (ℓ - j) (Λ' ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j)
    (cutPairRidHead Q Λ j hj θ) (cutPairMid Q hQ Λ j hj θ Z) (cutPairMid Q hQ Λ j hj θ Z')
    ((ModuleCat.restrictScalars.{u}
      (Algebra.TensorProduct.leftComm k St Hd Kk).toAlgHom.toRingHom).map
      ((singStd Q hQ j (Λ' ∘ Fin.castAdd (ℓ - j)) (θ ∘ Fin.castAdd (ℓ - j))
        (AlgCat.of k (St ⊗[k] Kk))).map (cutPairZMap Q Λ j hj θ g)))
    ((ModuleCat.restrictScalars.{u}
      (plusTensorRotIn Q Λ j hj (θ ∘ Fin.castAdd (ℓ - j)) (θ ∘ Fin.natAdd j)).toRingHom).map
      ((singStd Q hQ j (Λ' ∘ Fin.castAdd (ℓ - j)) (θ ∘ Fin.castAdd (ℓ - j)) St).map g))
    (cutPairMid_natural Q hQ Λ j hj θ g) x
  exact key

end Cut

end Categorification.Stendhal.CupCap

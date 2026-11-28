/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationSpectatorTensorStages
import Categorification.WeightedKLR.RedStrands.PartialStandardizationPlusStaged
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KSpectator


/-!
# The outer standardizations of `S_+` commute with tensoring the middle block

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3 (proof of
Lemma 7.19, where `S_+(Z ⊠ L)` is computed). For a module `Z` over the outer singleton blocks
`T^{λ_1}(θ_1) ⊗ ⋯ ⊗ T^{λ_j}(θ_j) ⊗ (T^{λ_{j+1}}(θ'_1) ⊗ ⋯)` and a module `L` over the middle
block `T^{μ μ*}(β)`, the input `Z ⊠ L` of `S_+` is `Z ⊗_k L` (`plusTensorInput`). The
standardizations of the first and of the last block (`plusOuterStd`) act on the outer blocks
only: `plusOuterStd (Z ⊠ L)` is `plusOuterPair Z ⊠ L`, where `plusOuterPair` standardizes the
first block with the last block in the spectator and then the last block with the first block
in the spectator (`plusOuterTensorEquiv`). Both stages are `singStdTensorEquiv`.

## Main definitions

* `Stendhal.CupCap.plusTensorInput`: the input `Z ⊠ L` of `S_+`.
* `Stendhal.CupCap.plusOuterPair`: the standardizations of the two outer blocks of `Z`.
* `Stendhal.CupCap.plusOuterTensorEquiv`, `Stendhal.CupCap.plusOuterTensorIso`:
  `plusOuterPair Z ⊠ L ≅ plusOuterStd (Z ⊠ L)`.

## Main results

* `Stendhal.CupCap.plusOuterTensorAddEquiv_smul`: the identification intertwines the actions of
  the three blocks.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR KLRAlgebra TypeA
open scoped TensorProduct

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

variable {I k : Type u} [DecidableEq I] [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q)

namespace CupCap

variable {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ) (j : ℕ) (hj : j ≤ ℓ)
  (β : Multiset I) (θh : Fin j → Multiset I) (θt : Fin (ℓ - j) → Multiset I)

/-- The semiring structure of the bundled algebra of the three blocks of `λ⁺`, through its ring
structure (so that linear maps over it elaborate). -/
private abbrev plusFactorAlgCatNonAssocSemiring (θ γ : Multiset I) :
    NonAssocSemiring (plusFactorAlgCat Q Λ Λc j hj θ β γ) :=
  Semiring.toNonAssocSemiring

attribute [local instance high] plusFactorAlgCatNonAssocSemiring

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

variable (Z : ModuleCat.{u} (Sh ⊗[k] St)) (L : Type u) [AddCommGroup L] [Module k L]
  [Module Cp L] [IsScalarTower k Cp L]

/-- **The input `Z ⊠ L` of `S_+`**: a module over the outer singleton blocks, tensored with a
module over the middle block. -/
abbrev plusTensorInput : ModuleCat.{u} (plusSingAlg Q Λ Λc j hj β θh θt) :=
  ModuleCat.of _ (MidSpect (k := k) Z L)

/-- The spectator map `T^{λ_{j+1}…} ⊗ T^{μμ*} → T^{μμ*} ⊗ T^{λ_{j+1}…}` of the first stage. -/
def plusTensorSwap :
    St ⊗[k] (AlgCat.of k Cp : AlgCat.{u} k) →ₐ[k] (AlgCat.of k (Cp ⊗[k] St) : AlgCat.{u} k) :=
  (Algebra.TensorProduct.comm k St Cp).toAlgHom

/-- `Z ⊠ L` as a tensor isomorphism for the first block. -/
def plusTensorFirstIn : TensorSpectatorEquiv Sh St (AlgCat.of k Cp : AlgCat.{u} k)
    (AlgCat.of k (Cp ⊗[k] St) : AlgCat.{u} k)
    (plusTensorSwap Q Λ Λc j hj β θt) Z L (plusTensorInput Q Λ Λc j hj β θh θt Z L) where
  equiv := AddEquiv.refl _
  map_smul a c b m v := (midSpect_tmul_smul (k := k) (A := Sh) (B := Cp) (C := St)
    a b c m v).symm

/-- The standardization of the first block of `Z ⊠ L`. -/
def plusTensorFirst :=
  singStdTensorEquiv Q hQ (B := AlgCat.of k Cp) (L := L) j (Λ ∘ Fin.castLE hj) θh
  (plusTensorSwap Q Λ Λc j hj β θt) (plusTensorFirstIn Q Λ Λc j hj β θh θt Z L)

/-- The rotation `T^{λ_{j+1}…} ⊗ T^A → T^A ⊗ T^{λ_{j+1}…}` after the first stage. -/
def plusTensorRotIn : St ⊗[k] (AlgCat.of k Hd : AlgCat.{u} k) →ₐ[k] Hd ⊗[k] St :=
  (Algebra.TensorProduct.comm k St Hd).toAlgHom

/-- The rotation `A ⊗ (B ⊗ C) → B ⊗ (C ⊗ A)` of the first stage of `plusOuterStd`. -/
def plusTensorRotP : St ⊗[k] (AlgCat.of k (Hd ⊗[k] Cp) : AlgCat.{u} k) →+*
    Hd ⊗[k] (AlgCat.of k (Cp ⊗[k] St) : AlgCat.{u} k) :=
  (tensorRotate (k := k) St Hd Cp).toAlgHom.toRingHom

/-- The spectator map of the second stage. -/
def plusTensorMid : (AlgCat.of k Hd : AlgCat.{u} k) ⊗[k] (AlgCat.of k Cp : AlgCat.{u} k) →ₐ[k]
    (AlgCat.of k (Hd ⊗[k] Cp) : AlgCat.{u} k) := AlgHom.id k _

/-- The first stage of `Z ⊠ L`, as a tensor isomorphism for the last block. -/
def plusTensorSecondIn : TensorSpectatorEquiv St (AlgCat.of k Hd : AlgCat.{u} k)
    (AlgCat.of k Cp : AlgCat.{u} k) (AlgCat.of k (Hd ⊗[k] Cp) : AlgCat.{u} k)
    (plusTensorMid Q Λ Λc j hj β θh)
    ((ModuleCat.restrictScalars.{u} (plusTensorRotIn Q Λ j hj θh θt).toRingHom).obj
      ((singStd Q hQ j (Λ ∘ Fin.castLE hj) θh St).obj Z)) L
    ((ModuleCat.restrictScalars.{u}
      (R := St ⊗[k] (AlgCat.of k (Hd ⊗[k] Cp) : AlgCat.{u} k))
      (plusTensorRotP Q Λ Λc j hj β θh θt)).obj
      ((singStd Q hQ j (Λ ∘ Fin.castLE hj) θh (AlgCat.of k (Cp ⊗[k] St))).obj
        (plusTensorInput Q Λ Λc j hj β θh θt Z L))) where
  equiv := AddEquiv.trans
    (M := (ModuleCat.restrictScalars.{u} (plusTensorRotIn Q Λ j hj θh θt).toRingHom).obj
      ((singStd Q hQ j (Λ ∘ Fin.castLE hj) θh St).obj Z) ⊗[k] L)
    (N := (singStd Q hQ j (Λ ∘ Fin.castLE hj) θh St).obj Z ⊗[k] L)
    (tensorCongrOf
      (X := (ModuleCat.restrictScalars.{u} (plusTensorRotIn Q Λ j hj θh θt).toRingHom).obj
        ((singStd Q hQ j (Λ ∘ Fin.castLE hj) θh St).obj Z))
      (Y := (singStd Q hQ j (Λ ∘ Fin.castLE hj) θh St).obj Z) L (AddEquiv.refl _)
      (restrictScalars_algebraMap_smul (plusTensorRotIn Q Λ j hj θh θt)
        ((singStd Q hQ j (Λ ∘ Fin.castLE hj) θh St).obj Z)))
    (plusTensorFirst Q hQ Λ Λc j hj β θh θt Z L).equiv
  map_smul a c b m v := (plusTensorFirst Q hQ Λ Λc j hj β θh θt Z L).map_smul c a b m v

/-- The standardization of the last block of `Z ⊠ L`. -/
def plusTensorSecond := singStdTensorEquiv Q hQ (B := AlgCat.of k Cp) (L := L) (ℓ - j)
  (plusTailLabels Λ j hj) θt (plusTensorMid Q Λ Λc j hj β θh)
  (plusTensorSecondIn Q hQ Λ Λc j hj β θh θt Z L)

/-- The rotation `T^A ⊗ T^B → T^B ⊗ T^A` after the second stage. -/
def plusTensorRotOut : Hd ⊗[k] Tl →ₐ[k] Tl ⊗[k] (AlgCat.of k Hd : AlgCat.{u} k) :=
  (Algebra.TensorProduct.comm k Hd Tl).toAlgHom

/-- **The standardizations of the first and of the last block**, in stages, of a module over the
outer singleton blocks of `λ⁺`: the first block with the last block in the spectator, then the
last block with the first block in the spectator. -/
abbrev plusOuterPair : ModuleCat.{u} (Hd ⊗[k] Tl) :=
  (ModuleCat.restrictScalars.{u} (plusTensorRotOut Q Λ j hj θh θt).toRingHom).obj
    ((singStd Q hQ (ℓ - j) (plusTailLabels Λ j hj) θt (AlgCat.of k Hd)).obj
      ((ModuleCat.restrictScalars.{u} (plusTensorRotIn Q Λ j hj θh θt).toRingHom).obj
        ((singStd Q hQ j (Λ ∘ Fin.castLE hj) θh St).obj Z)))

/-- The additive isomorphism `plusOuterPair Z ⊠ L ≅ plusOuterStd (Z ⊠ L)`. -/
def plusOuterTensorAddEquiv : MidSpect (k := k) (plusOuterPair Q hQ Λ j hj θh θt Z) L ≃+
    (plusOuterStd Q hQ Λ Λc j hj β θh θt).obj (plusTensorInput Q Λ Λc j hj β θh θt Z L) :=
  AddEquiv.trans
    (M := MidSpect (k := k) (plusOuterPair Q hQ Λ j hj θh θt Z) L)
    (N := (singStd Q hQ (ℓ - j) (plusTailLabels Λ j hj) θt (AlgCat.of k Hd)).obj
      ((ModuleCat.restrictScalars.{u} (plusTensorRotIn Q Λ j hj θh θt).toRingHom).obj
        ((singStd Q hQ j (Λ ∘ Fin.castLE hj) θh St).obj Z)) ⊗[k] L)
    (tensorCongrOf (X := plusOuterPair Q hQ Λ j hj θh θt Z)
      (Y := (singStd Q hQ (ℓ - j) (plusTailLabels Λ j hj) θt (AlgCat.of k Hd)).obj
        ((ModuleCat.restrictScalars.{u} (plusTensorRotIn Q Λ j hj θh θt).toRingHom).obj
          ((singStd Q hQ j (Λ ∘ Fin.castLE hj) θh St).obj Z))) L (AddEquiv.refl _)
      (restrictScalars_algebraMap_smul (plusTensorRotOut Q Λ j hj θh θt) _))
    (plusTensorSecond Q hQ Λ Λc j hj β θh θt Z L).equiv

/-- `plusOuterTensorAddEquiv` intertwines the actions of pure tensors. -/
theorem plusOuterTensorAddEquiv_smul_tmul (a : Hd) (b : Cp) (c : Tl)
    (y : plusOuterPair Q hQ Λ j hj θh θt Z) (v : L) :
    plusOuterTensorAddEquiv Q hQ Λ Λc j hj β θh θt Z L
        ((a ⊗ₜ[k] (b ⊗ₜ[k] c) : Hd ⊗[k] (Cp ⊗[k] Tl)) • midSpectTmul (k := k) y v) =
      (show plusFactorAlgCat Q Λ Λc j hj (singWeight j θh) β (singWeight (ℓ - j) θt) from
        a ⊗ₜ[k] (b ⊗ₜ[k] c)) •
        plusOuterTensorAddEquiv Q hQ Λ Λc j hj β θh θt Z L (midSpectTmul (k := k) y v) :=
  (congrArg (plusOuterTensorAddEquiv Q hQ Λ Λc j hj β θh θt Z L)
    (midSpect_tmul_smul (k := k) a b c y v)).trans
    ((plusTensorSecond Q hQ Λ Λc j hj β θh θt Z L).map_smul c a b y v)

/-- `plusOuterTensorAddEquiv` intertwines the actions of the three blocks. -/
theorem plusOuterTensorAddEquiv_smul (x : Hd ⊗[k] (Cp ⊗[k] Tl))
    (z : MidSpect (k := k) (plusOuterPair Q hQ Λ j hj θh θt Z) L) :
    plusOuterTensorAddEquiv Q hQ Λ Λc j hj β θh θt Z L (x • z) =
      (show plusFactorAlgCat Q Λ Λc j hj (singWeight j θh) β (singWeight (ℓ - j) θt) from x) •
        plusOuterTensorAddEquiv Q hQ Λ Λc j hj β θh θt Z L z := by
  induction x using TensorProduct.inductionOn with
  | tmul a bc =>
    induction bc using TensorProduct.inductionOn with
    | tmul b c =>
      refine TensorProduct.inductionOn
        (motive := fun w : plusOuterPair Q hQ Λ j hj θh θt Z ⊗[k] L =>
          plusOuterTensorAddEquiv Q hQ Λ Λc j hj β θh θt Z L
              ((a ⊗ₜ[k] (b ⊗ₜ[k] c) : Hd ⊗[k] (Cp ⊗[k] Tl)) •
                (show MidSpect (k := k) (plusOuterPair Q hQ Λ j hj θh θt Z) L from w)) =
            (show plusFactorAlgCat Q Λ Λc j hj (singWeight j θh) β (singWeight (ℓ - j) θt) from
              a ⊗ₜ[k] (b ⊗ₜ[k] c)) •
              plusOuterTensorAddEquiv Q hQ Λ Λc j hj β θh θt Z L
                (show MidSpect (k := k) (plusOuterPair Q hQ Λ j hj θh θt Z) L from w))
        z ?_ ?_
      · exact fun y v => plusOuterTensorAddEquiv_smul_tmul Q hQ Λ Λc j hj β θh θt Z L a b c y v
      · intro w w' hw hw'
        exact (congrArg _ (smul_add _ _ _)).trans ((map_add _ _ _).trans
          ((congrArg₂ (· + ·) hw hw').trans ((smul_add _ _ _).symm.trans
            (congrArg (_ • ·) (map_add _ _ _).symm))))
    | add bc bc' hb hb' =>
      exact (congrArg (plusOuterTensorAddEquiv Q hQ Λ Λc j hj β θh θt Z L)
        ((congrArg (· • z) (TensorProduct.tmul_add a bc bc')).trans
          (add_smul (a ⊗ₜ[k] bc) (a ⊗ₜ[k] bc') z))).trans
        ((map_add _ _ _).trans ((congrArg₂ (· + ·) hb hb').trans
          ((add_smul _ _ _).symm.trans (congrArg (· • _) (TensorProduct.tmul_add a bc bc').symm))))
  | add x x' hx hx' =>
    exact (congrArg (plusOuterTensorAddEquiv Q hQ Λ Λc j hj β θh θt Z L)
      (add_smul x x' z)).trans ((map_add _ _ _).trans ((congrArg₂ (· + ·) hx hx').trans
        (add_smul _ _ _).symm))

/-- **The standardizations of the outer blocks of `S_+` commute with tensoring the middle
block**: `plusOuterPair Z ⊠ L ≅ plusOuterStd (Z ⊠ L)` as modules over the three blocks. -/
def plusOuterTensorEquiv :
    MidSpect (k := k) (plusOuterPair Q hQ Λ j hj θh θt Z) L ≃ₗ[
      plusFactorAlgCat Q Λ Λc j hj (singWeight j θh) β (singWeight (ℓ - j) θt)]
      (plusOuterStd Q hQ Λ Λc j hj β θh θt).obj (plusTensorInput Q Λ Λc j hj β θh θt Z L) where
  toFun := plusOuterTensorAddEquiv Q hQ Λ Λc j hj β θh θt Z L
  invFun := (plusOuterTensorAddEquiv Q hQ Λ Λc j hj β θh θt Z L).symm
  left_inv := (plusOuterTensorAddEquiv Q hQ Λ Λc j hj β θh θt Z L).left_inv
  right_inv := (plusOuterTensorAddEquiv Q hQ Λ Λc j hj β θh θt Z L).right_inv
  map_add' := map_add _
  map_smul' := plusOuterTensorAddEquiv_smul Q hQ Λ Λc j hj β θh θt Z L

/-- `plusOuterTensorEquiv` on pure tensors. -/
theorem plusOuterTensorEquiv_tmul (y : plusOuterPair Q hQ Λ j hj θh θt Z) (v : L) :
    plusOuterTensorEquiv Q hQ Λ Λc j hj β θh θt Z L (midSpectTmul (k := k) y v) =
      plusOuterTensorAddEquiv Q hQ Λ Λc j hj β θh θt Z L (midSpectTmul (k := k) y v) := rfl

/-- `plusOuterTensorEquiv` as an isomorphism in the category of modules over the three
blocks. -/
def plusOuterTensorIso :
    ModuleCat.of (plusFactorAlgCat Q Λ Λc j hj (singWeight j θh) β (singWeight (ℓ - j) θt))
        (MidSpect (k := k) (plusOuterPair Q hQ Λ j hj θh θt Z) L) ≅
      (plusOuterStd Q hQ Λ Λc j hj β θh θt).obj (plusTensorInput Q Λ Λc j hj β θh θt Z L) :=
  (plusOuterTensorEquiv Q hQ Λ Λc j hj β θh θt Z L).toModuleIso

end CupCap

end Categorification.Stendhal

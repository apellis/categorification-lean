/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationSingSplit
import Categorification.WeightedKLR.RedStrands.PartialStandardizationPlusOuterTensor


/-!
# The standardizations of the two blocks at the cut are the outer standardizations of `S_+`

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3 (proof of
Lemma 7.19). For a module `Z` over the singleton blocks of `λ`, split at the cut after the
`j`-th red strand and labelled by `λ ∘ Fin.cast`, the standardizations of the two blocks at the
cut (`singOuter` with the trivial spectator `k`, restricted to the two blocks) are the
standardizations of the outer blocks of `λ⁺` without a spectator (`plusOuterPair`), as modules
over the algebra of the two blocks (`cutPairEquiv`). The trivial spectator is dropped by
changes of spectator along `T ⊗ k ≅ T` (`singStdSpectatorEquiv`).

## Main definitions

* `Stendhal.CupCap.cutPairZ`: `Z` with the trivial spectator.
* `Stendhal.CupCap.CutPairSource`: `singOuter` of `cutPairZ`, over the two blocks.
* `Stendhal.CupCap.cutPairEquiv`: `CutPairSource ≅ plusOuterPair Z`.

## Main results

* `Stendhal.tensorTripleRight_addHom_ext`: additive maps on `M ⊗ (N ⊗ P)` agreeing on pure
  tensors agree.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR KLRAlgebra TypeA
open scoped TensorProduct

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

variable {I k : Type u} [DecidableEq I] [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q)

/-- Additive maps on `M ⊗ (N ⊗ P)` agreeing on pure tensors agree. -/
theorem tensorTripleRight_addHom_ext {M N P S : Type*} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] [AddCommGroup P] [Module k P] [AddCommGroup S]
    (F G : M ⊗[k] (N ⊗[k] P) →+ S) (h : ∀ m n p, F (m ⊗ₜ (n ⊗ₜ p)) = G (m ⊗ₜ (n ⊗ₜ p)))
    (x : M ⊗[k] (N ⊗[k] P)) : F x = G x := by
  induction x using TensorProduct.inductionOn with
  | tmul m y =>
    induction y using TensorProduct.inductionOn with
    | tmul n p => exact h m n p
    | add y y' hy hy' => rw [TensorProduct.tmul_add, map_add, map_add, hy, hy']
  | add x y hx hy => rw [map_add, map_add, hx, hy]

namespace CupCap

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
set_option hygiene false in
local notation "Tl" => TensorProductAlgebra k Q (Λ' ∘ Fin.natAdd j) w₂

variable (Z : ModuleCat.{u} (Sh ⊗[k] St))

/-- Dropping the trivial spectator of the last block. -/
def cutPairRidLast : (AlgCat.of k (St ⊗[k] k) : AlgCat.{u} k) →ₐ[k] St :=
  (Algebra.TensorProduct.rid k k St).toAlgHom

/-- `Z` with the trivial spectator. -/
abbrev cutPairZ : ModuleCat.{u} (Sh ⊗[k] (AlgCat.of k (St ⊗[k] k) : AlgCat.{u} k)) :=
  (ModuleCat.restrictScalars.{u} (Algebra.TensorProduct.map (AlgHom.id k _)
    (Algebra.TensorProduct.rid k k St).toAlgHom).toRingHom).obj Z

/-- The first stage, dropping the trivial spectator. -/
def cutPairFirst := singStdSpectatorEquiv Q hQ j (Λ' ∘ Fin.castAdd (ℓ - j))
  (θ ∘ Fin.castAdd (ℓ - j)) (cutPairRidLast Q Λ j hj θ) (Z := cutPairZ Q Λ j hj θ Z) (Z' := Z)
  ⟨AddEquiv.refl _, fun _ _ => rfl⟩

/-- Dropping the trivial spectator of the first block. -/
def cutPairRidHead :
    (AlgCat.of k (Hd ⊗[k] k) : AlgCat.{u} k) →ₐ[k] (AlgCat.of k Hd : AlgCat.{u} k) :=
  (Algebra.TensorProduct.rid k k Hd).toAlgHom

/-- The first stage of `singOuter`, as a module over the last block. -/
abbrev cutPairMidL : ModuleCat.{u} (St ⊗[k] (AlgCat.of k (Hd ⊗[k] k) : AlgCat.{u} k)) :=
  (ModuleCat.restrictScalars.{u} (Algebra.TensorProduct.leftComm k St Hd Kk).toAlgHom.toRingHom).obj
    ((singStd Q hQ j (Λ' ∘ Fin.castAdd (ℓ - j)) (θ ∘ Fin.castAdd (ℓ - j))
      (AlgCat.of k (St ⊗[k] Kk))).obj (cutPairZ Q Λ j hj θ Z))

/-- The first stage of `plusOuterPair`, as a module over the last block. -/
abbrev cutPairMidR : ModuleCat.{u} (St ⊗[k] (AlgCat.of k Hd : AlgCat.{u} k)) :=
  (ModuleCat.restrictScalars.{u}
    (plusTensorRotIn Q Λ j hj (θ ∘ Fin.castAdd (ℓ - j)) (θ ∘ Fin.natAdd j)).toRingHom).obj
    ((singStd Q hQ j (Λ' ∘ Fin.castAdd (ℓ - j)) (θ ∘ Fin.castAdd (ℓ - j)) St).obj Z)

/-- The algebra maps of the change of spectator of the last block agree. -/
theorem cutPairMid_apply (x : St ⊗[k] (AlgCat.of k (Hd ⊗[k] k) : AlgCat.{u} k)) :
    Algebra.TensorProduct.map (AlgHom.id k Hd) (cutPairRidLast Q Λ j hj θ)
        (Algebra.TensorProduct.leftComm k St Hd Kk x) =
      plusTensorRotIn Q Λ j hj (θ ∘ Fin.castAdd (ℓ - j)) (θ ∘ Fin.natAdd j)
        (Algebra.TensorProduct.map (AlgHom.id k St) (cutPairRidHead Q Λ j hj θ) x) :=
  tensorTripleRight_addHom_ext (k := k)
    ((Algebra.TensorProduct.map (AlgHom.id k Hd)
        (cutPairRidLast Q Λ j hj θ)).toRingHom.toAddMonoidHom.comp
      (Algebra.TensorProduct.leftComm k St Hd Kk).toRingHom.toAddMonoidHom)
    ((plusTensorRotIn Q Λ j hj (θ ∘ Fin.castAdd (ℓ - j))
        (θ ∘ Fin.natAdd j)).toRingHom.toAddMonoidHom.comp
      (Algebra.TensorProduct.map (AlgHom.id k St)
        (cutPairRidHead Q Λ j hj θ)).toRingHom.toAddMonoidHom)
    (fun s h c => (TensorProduct.smul_tmul c h s).symm) x

/-- The change of spectator of the last block. -/
def cutPairMid : SpectatorEquiv St (cutPairRidHead Q Λ j hj θ) (cutPairMidL Q hQ Λ j hj θ Z)
    (cutPairMidR Q hQ Λ j hj θ Z) where
  equiv := (cutPairFirst Q hQ Λ j hj θ Z).equiv
  map_smul x m := ((cutPairFirst Q hQ Λ j hj θ Z).map_smul
      (Algebra.TensorProduct.leftComm k St Hd Kk x) m).trans
    (congrArg (· • (cutPairFirst Q hQ Λ j hj θ Z).equiv m) (cutPairMid_apply Q Λ j hj θ x))

/-- The standardization of the last block, dropping the trivial spectator. -/
def cutPairLast := singStdSpectatorEquiv Q hQ (ℓ - j) (Λ' ∘ Fin.natAdd j) (θ ∘ Fin.natAdd j)
  (cutPairRidHead Q Λ j hj θ) (Z := cutPairMidL Q hQ Λ j hj θ Z)
  (Z' := cutPairMidR Q hQ Λ j hj θ Z) (cutPairMid Q hQ Λ j hj θ Z)

/-- The identification of the algebra of the two blocks at the cut with that of the outer blocks
of `λ⁺`. -/
def cutPairIdent : cutFactorAlgebra Q Λ' w₁ w₂ →ₐ[k]
    TensorProductAlgebra k Q (Λ ∘ Fin.castLE hj) w₁ ⊗[k]
      TensorProductAlgebra k Q (plusTailLabels Λ j hj) w₂ :=
  AlgHom.id k _

/-- The algebra maps of the last stage agree. -/
theorem cutPairOut_apply (x : cutFactorAlgebra Q Λ' w₁ w₂) :
    Algebra.TensorProduct.map (AlgHom.id k Tl) (cutPairRidHead Q Λ j hj θ)
        (singRotOut Q j (ℓ - j) Λ' w₁ w₂ Kk (x ⊗ₜ[k] (1 : k))) =
      plusTensorRotOut Q Λ j hj (θ ∘ Fin.castAdd (ℓ - j)) (θ ∘ Fin.natAdd j)
        (cutPairIdent Q Λ j hj θ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul h t => exact congrArg (t ⊗ₜ[k] ·) (one_smul k h)
  | add x y hx hy =>
    exact (congrArg (fun z => Algebra.TensorProduct.map (AlgHom.id k Tl)
        (cutPairRidHead Q Λ j hj θ) (singRotOut Q j (ℓ - j) Λ' w₁ w₂ Kk z))
        (TensorProduct.add_tmul x y (1 : k))).trans
      ((congrArg (Algebra.TensorProduct.map (AlgHom.id k Tl) (cutPairRidHead Q Λ j hj θ))
        (map_add _ _ _)).trans ((map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans
          (map_add _ _ _).symm)))

/-- The standardizations of the two blocks of `Z` at the cut, from `singOuter` with the trivial
spectator. -/
abbrev CutPairSource : Type u :=
  CutSpectInput (a := j) (r := ℓ - j) Q Λ' w₁ w₂ Kk
    ((singOuter Q hQ j (ℓ - j) Λ' θ Kk).obj (cutPairZ Q Λ j hj θ Z))

/-- `plusOuterPair Z`, as a module over the algebra of the two blocks at the cut. -/
abbrev cutPairTarget : ModuleCat.{u} (cutFactorAlgebra Q Λ' w₁ w₂) :=
  (ModuleCat.restrictScalars.{u} (cutPairIdent Q Λ j hj θ).toRingHom).obj
    (plusOuterPair Q hQ Λ j hj (θ ∘ Fin.castAdd (ℓ - j)) (θ ∘ Fin.natAdd j) Z)

/-- **The standardizations of the two blocks at the cut are `plusOuterPair`**: `singOuter` with
the trivial spectator, restricted to the two blocks, is `plusOuterPair`. -/
def cutPairEquiv : CutPairSource Q hQ Λ j hj θ Z ≃ₗ[cutFactorAlgebra Q Λ' w₁ w₂]
    cutPairTarget Q hQ Λ j hj θ Z where
  toFun := (cutPairLast Q hQ Λ j hj θ Z).equiv
  invFun := (cutPairLast Q hQ Λ j hj θ Z).equiv.symm
  left_inv := (cutPairLast Q hQ Λ j hj θ Z).equiv.left_inv
  right_inv := (cutPairLast Q hQ Λ j hj θ Z).equiv.right_inv
  map_add' := map_add _
  map_smul' x n := ((cutPairLast Q hQ Λ j hj θ Z).map_smul
      (singRotOut Q j (ℓ - j) Λ' w₁ w₂ Kk (x ⊗ₜ[k] (1 : k))) n).trans
    (congrArg (· • (cutPairLast Q hQ Λ j hj θ Z).equiv n) (cutPairOut_apply Q Λ j hj θ x))

end CupCap

end Categorification.Stendhal

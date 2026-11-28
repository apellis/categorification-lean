/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.SMoveEmptyCorner
import Categorification.WeightedKLR.Rigidity.SMoveModules
import Categorification.WeightedKLR.RedStrands.SingStdStandardBasis

/-!
# The diagonal corner of the S-move

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22, the `Tor_0` term on the diagonal. For the three red strands of the S-move
and a loading `s = (red₁ red₂ 𝐮 red₃)` with all black strands between the second and third red
strands, the vectors fixed by `e(s)` in `𝕊^{λ_1, λ_2; λ_3}(𝕊^{λ_1; λ_2}(P_∅ ⊠ Z) ⊠ P_∅)` are
the vectors of the one-red module `Z` fixed by the loading idempotent of `(red₂ 𝐮)`.

Both reductions are `cutStandardLoadingFixedEquiv` at a cut whose outer block is `P_∅`
(`emptyLeftCornerInputEquiv`, `emptyRightCornerInputEquiv`); here they are stated for the
module structures over `T^λ` (`fixSub`) and composed. The loading idempotent of a
concatenation is written in the coordinates of the cut (`cutLoad`); for the composite, the
prefix loading of the outer cut is chosen so that its idempotent is the loading idempotent of
the inner cut (`cutPrefixProjection_e_innerLoading`).

## Main definitions

* `Stendhal.cutLoad`: the loading idempotent of `T^λ(ν)` at a loading of the cut coordinates.
* `Stendhal.emptyLeftStd`, `Stendhal.emptyRightStd`: `𝕊(P_∅ ⊠ −)`, `𝕊(− ⊠ P_∅)` for any
  number of red strands in the inner block (`SMove.leftStd`, `SMove.rightStd` are instances).
* `Stendhal.emptyLeftStdCornerEquiv`, `Stendhal.emptyRightStdCornerEquiv`: the fixed vectors.
* `Stendhal.SMove.innerLoading`: the prefix loading `(red₁ 𝐣)` of the outer cut.
* `Stendhal.SMove.diagonalCornerEquiv`: the composite three-strand reduction.
-/

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR KLRAlgebra
open scoped TensorProduct

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

theorem castTensorProductAlgebra_symm_cast {I k : Type*} [DecidableEq I] [CommRing k]
    {Q : I → I → MvPolynomial (Fin 2) k} {m : ℕ} (Λ' : Fin m → I →₀ ℕ) {ν ν' : Multiset I}
    (h : ν = ν') (x : TensorProductAlgebra k Q Λ' ν) :
    castTensorProductAlgebra Q Λ' h.symm (castTensorProductAlgebra Q Λ' h x) = x := by
  subst h; rfl

/-! ### Loading idempotents in cut coordinates -/

section Cut

variable {I k : Type} [DecidableEq I] [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q) {a r : ℕ} (Λ : Fin (a + r) → I →₀ ℕ) {θ β ν : Multiset I} (h : θ + β = ν)

local notation "α" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd r)) (stendhalWeight a θ)
local notation "δ" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd a)) (stendhalWeight r β)

/-- The loading idempotent of `T^λ(ν)` at a loading `s` of the cut coordinates, transported
along the split `θ + β = ν`. -/
def cutLoad (s : Seq (α + δ)) : TensorProductAlgebra k Q Λ ν :=
  castTensorProductAlgebra Q Λ h (affineToTensor Q Λ θ β (e s))

variable (M : ModuleCat.{0} (cutFactorAlgebra Q Λ θ β))

/-- The partial standardization `𝕊(M)` as a module over `T^λ(ν)`. -/
abbrev cutStdObj : ModuleCat.{0} (TensorProductAlgebra k Q Λ ν) :=
  (cutStandardFunctor Q hQ Λ θ β (castTensorProductAlgebra Q Λ h.symm).toAlgHom).obj M

theorem cutLoad_smul (s : Seq (α + δ)) (z : cutStdObj Q hQ Λ h M) :
    cutLoad Q Λ h s • z = cutLoadingEnd Q Λ θ β M hQ s z := by
  change cutStandardAction Q Λ θ β M hQ
    (castTensorProductAlgebra Q Λ h.symm (castTensorProductAlgebra Q Λ h _)) z = _
  rw [castTensorProductAlgebra_symm_cast]

theorem algebraMap_smul_cutStandardFunctor (c : k) (z : CutStandard Q Λ θ β M) :
    (algebraMap k (TensorProductAlgebra k Q Λ ν) c) • (@id (cutStdObj Q hQ Λ h M) z) =
      c • z := by
  change cutStandardAction Q Λ θ β M hQ (castTensorProductAlgebra Q Λ h.symm _) z = _
  rw [AlgEquiv.commutes, AlgHom.commutes]
  rfl

theorem mem_fixSub_cutLoad_iff (s : Seq (α + δ)) (z : CutStandard Q Λ θ β M) :
    @id (cutStdObj Q hQ Λ h M) z ∈ fixSub k (cutStdObj Q hQ Λ h M) (cutLoad Q Λ h s) ↔
      z ∈ LinearMap.ker (cutLoadingEnd Q Λ θ β M hQ s - 1) := by
  rw [mem_ker_sub_one_iff, mem_fixSub]
  exact Eq.congr_left (cutLoad_smul Q hQ Λ h M s z)

/-- The fixed vectors of `e(s)` on `𝕊(M)`, in the `T^λ`-module structure of the functor. -/
def fixSubCutLoadEquiv (s : Seq (α + δ)) :
    fixSub k (cutStdObj Q hQ Λ h M) (cutLoad Q Λ h s) ≃ₗ[k]
      LinearMap.ker (cutLoadingEnd Q Λ θ β M hQ s - 1) where
  toFun z := ⟨@id (CutStandard Q Λ θ β M) z.1,
    (mem_fixSub_cutLoad_iff Q hQ Λ h M s _).mp z.2⟩
  invFun z := ⟨@id (cutStdObj Q hQ Λ h M) z.1,
    (mem_fixSub_cutLoad_iff Q hQ Λ h M s _).mpr z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c z := Subtype.ext (algebraMap_smul_cutStandardFunctor Q hQ Λ h M c z.1)

end Cut

/-- On `A ⊠ X` over `A ⊗ B`, the scalars of `k` through `algebraMap` are the tensor scalars. -/
theorem algebraMap_smul_extTensor {k A B P X : Type*} [CommRing k] [Ring A] [Algebra k A]
    [Ring B] [Algebra k B] [AddCommGroup P] [Module k P] [Module A P] [IsScalarTower k A P]
    [AddCommGroup X] [Module k X] [Module B X] [IsScalarTower k B X] (c : k)
    (x : ExtTensor k P X) : (algebraMap k (A ⊗[k] B) c) • x = c • x := by
  rw [ExtTensor.smul_def, AlgHom.commutes]
  rfl

/-! ### The outer block `P_∅` on the left -/

section EmptyLeft

variable {I k : Type} [DecidableEq I] [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q) {r : ℕ} (Λ : Fin (1 + r) → I →₀ ℕ) (β : Multiset I)

local notation "α" =>
  Multiset.map (Sum.map (id : I → I) (Fin.castAdd r)) (stendhalWeight 1 (0 : Multiset I))
local notation "δ" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd 1)) (stendhalWeight r β)

/-- `𝕊^{λ_1; λ_2, …}(P_∅ ⊠ −)` for an inner block of `r` red strands (Webster,
arXiv:1309.3796v3, §5.1); `SMove.leftStd` is the case `r = 1 + 1`. -/
def emptyLeftStd :
    ModuleCat.{0} (TensorProductAlgebra k Q (Λ ∘ Fin.natAdd 1) β) ⥤
      ModuleCat.{0} (TensorProductAlgebra k Q Λ β) :=
  SMove.regularLeftTensor (TensorProductAlgebra k Q (Λ ∘ Fin.castAdd r) 0) ⋙
    cutStandardFunctor Q hQ Λ 0 β (castTensorProductAlgebra Q Λ (zero_add β).symm).toAlgHom

variable (Z : ModuleCat.{0} (TensorProductAlgebra k Q (Λ ∘ Fin.natAdd 1) β))

local notation "L" => TensorProductAlgebra k Q (Λ ∘ Fin.castAdd r) 0

/-- `T^{λ_1}(0) ⊠ Z ≅ Z` (`tensorProductAlgebraZeroEquiv`). -/
def emptyLeftScalarEquiv : L ⊗[k] Z ≃ₗ[k] Z :=
  (TensorProduct.congr (tensorProductAlgebraZeroEquiv Q (Λ ∘ Fin.castAdd r)).toLinearEquiv
    (LinearEquiv.refl k Z)).trans (TensorProduct.lid k Z)

theorem emptyLeftScalarEquiv_lTensor (p : TensorProductAlgebra k Q (Λ ∘ Fin.natAdd 1) β)
    (x : L ⊗[k] Z) :
    emptyLeftScalarEquiv Q Λ β Z ((Algebra.lsmul k k Z p).lTensor L x) =
      p • emptyLeftScalarEquiv Q Λ β Z x := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, smul_add]
  | tmul l z =>
    rw [LinearMap.lTensor_tmul, Algebra.lsmul_coe]
    simp only [emptyLeftScalarEquiv, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
      TensorProduct.lid_tmul, LinearEquiv.refl_apply]
    exact smul_comm _ p z

/-- `P_∅ ⊠ Z`, the input of the cut. -/
abbrev emptyLeftInput := (SMove.regularLeftTensor (k := k) L).obj Z

theorem cutInputIdemEnd_regularLeft (i : Seq α) (j : Seq δ) (x : L ⊗[k] Z) :
    emptyLeftScalarEquiv Q Λ β Z (@id (L ⊗[k] Z) (cutInputIdemEnd Q Λ 0 β
      (emptyLeftInput Q Λ β Z) (i.append j) (@id (CutInput Q Λ 0 β (emptyLeftInput Q Λ β Z)) x))) =
      cutSuffixProjection Q Λ β (e j) • emptyLeftScalarEquiv Q Λ β Z x :=
  (congrArg (emptyLeftScalarEquiv Q Λ β Z)
    (LinearMap.congr_fun (cutInputIdemEnd_emptyLeft Q Λ β Z i j) x)).trans
    (emptyLeftScalarEquiv_lTensor Q Λ β Z _ x)

theorem cutInputIdemEnd_regularLeft_symm (i : Seq α) (j : Seq δ)
    (y : fixSub k Z (cutSuffixProjection Q Λ β (e j))) :
    @id (L ⊗[k] Z) (cutInputIdemEnd Q Λ 0 β (emptyLeftInput Q Λ β Z) (i.append j)
      (@id (CutInput Q Λ 0 β (emptyLeftInput Q Λ β Z))
        ((emptyLeftScalarEquiv Q Λ β Z).symm y.1))) =
      (emptyLeftScalarEquiv Q Λ β Z).symm y.1 := by
  apply (emptyLeftScalarEquiv Q Λ β Z).injective
  rw [cutInputIdemEnd_regularLeft, LinearEquiv.apply_symm_apply]
  exact y.2

/-- The input corner of `P_∅ ⊠ Z` at `(red₁ 𝐣)` is the fixed space of `e(𝐣)` on `Z`. -/
def emptyLeftInputFixedEquiv (i : Seq α) (j : Seq δ) :
    LinearMap.ker (cutInputIdemEnd Q Λ 0 β (emptyLeftInput Q Λ β Z) (i.append j) - 1) ≃ₗ[k]
      fixSub k Z (cutSuffixProjection Q Λ β (e j)) where
  toFun x := ⟨emptyLeftScalarEquiv Q Λ β Z (@id (L ⊗[k] Z) x.1),
    (cutInputIdemEnd_regularLeft Q Λ β Z i j x.1).symm.trans
      (congrArg (fun z => emptyLeftScalarEquiv Q Λ β Z (@id (L ⊗[k] Z) z))
        ((mem_ker_sub_one_iff (cutInputIdemEnd Q Λ 0 β (emptyLeftInput Q Λ β Z) (i.append j))
          x.1).mp x.2))⟩
  invFun y := ⟨@id (CutInput Q Λ 0 β (emptyLeftInput Q Λ β Z))
      ((emptyLeftScalarEquiv Q Λ β Z).symm y.1),
    (mem_ker_sub_one_iff (cutInputIdemEnd Q Λ 0 β (emptyLeftInput Q Λ β Z) (i.append j))
      _).mpr (cutInputIdemEnd_regularLeft_symm Q Λ β Z i j y)⟩
  left_inv x := Subtype.ext ((emptyLeftScalarEquiv Q Λ β Z).symm_apply_apply x.1)
  right_inv y := Subtype.ext ((emptyLeftScalarEquiv Q Λ β Z).apply_symm_apply y.1)
  map_add' x x' := Subtype.ext (map_add (emptyLeftScalarEquiv Q Λ β Z) x.1 x'.1)
  map_smul' c x := Subtype.ext (by
    refine Eq.trans ?_ (map_smul (emptyLeftScalarEquiv Q Λ β Z) c (@id (L ⊗[k] Z) x.1))
    exact congrArg (emptyLeftScalarEquiv Q Λ β Z) (algebraMap_smul_extTensor (A := L)
      (B := TensorProductAlgebra k Q (Λ ∘ Fin.natAdd 1) β) c (@id (ExtTensor k L Z) x.1)))

/-- **The loading corner of `𝕊(P_∅ ⊠ Z)`** (Webster, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.22): the vectors fixed by the loading idempotent of `(red₁ 𝐣)` are the vectors of
`Z` fixed by that of `𝐣`. -/
def emptyLeftStdCornerEquiv (i : Seq α) (j : Seq δ) :
    fixSub k ((emptyLeftStd Q hQ Λ β).obj Z) (cutLoad Q Λ (zero_add β) (i.append j)) ≃ₗ[k]
      fixSub k Z (cutSuffixProjection Q Λ β (e j)) :=
  (fixSubCutLoadEquiv Q hQ Λ (zero_add β) (emptyLeftInput Q Λ β Z) (i.append j)).trans
    ((cutStandardLoadingFixedEquiv Q Λ 0 β (emptyLeftInput Q Λ β Z) hQ
      (isUnshuffledLoading_append_emptyLeft Q Λ β i j)).trans
      (emptyLeftInputFixedEquiv Q Λ β Z i j))

end EmptyLeft

/-! ### The outer block `P_∅` on the right -/

section EmptyRight

variable {I k : Type} [DecidableEq I] [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q) {a : ℕ} (Λ : Fin (a + 1) → I →₀ ℕ) (θ : Multiset I)

local notation "α" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd 1)) (stendhalWeight a θ)
local notation "δ" =>
  Multiset.map (Sum.map (id : I → I) (Fin.natAdd a)) (stendhalWeight 1 (0 : Multiset I))

/-- `𝕊^{…, λ_a; λ_{a+1}}(− ⊠ P_∅)` for an inner block of `a` red strands (Webster,
arXiv:1309.3796v3, §5.1); `SMove.rightStd` is the case `a = 2`. -/
def emptyRightStd :
    ModuleCat.{0} (TensorProductAlgebra k Q (Λ ∘ Fin.castAdd 1) θ) ⥤
      ModuleCat.{0} (TensorProductAlgebra k Q Λ θ) :=
  SMove.regularRightTensor (TensorProductAlgebra k Q (Λ ∘ Fin.natAdd a) 0) ⋙
    cutStandardFunctor Q hQ Λ θ 0 (castTensorProductAlgebra Q Λ (add_zero θ).symm).toAlgHom

variable (W : ModuleCat.{0} (TensorProductAlgebra k Q (Λ ∘ Fin.castAdd 1) θ))

local notation "C" => TensorProductAlgebra k Q (Λ ∘ Fin.natAdd a) 0

/-- `W ⊠ T^{λ_{a+1}}(0) ≅ W` (`tensorProductAlgebraZeroEquiv`). -/
def emptyRightScalarEquiv : W ⊗[k] C ≃ₗ[k] W :=
  (TensorProduct.congr (LinearEquiv.refl k W)
    (tensorProductAlgebraZeroEquiv Q (Λ ∘ Fin.natAdd a)).toLinearEquiv).trans
    (TensorProduct.rid k W)

theorem emptyRightScalarEquiv_rTensor (p : TensorProductAlgebra k Q (Λ ∘ Fin.castAdd 1) θ)
    (x : W ⊗[k] C) :
    emptyRightScalarEquiv Q Λ θ W ((Algebra.lsmul k k W p).rTensor C x) =
      p • emptyRightScalarEquiv Q Λ θ W x := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, smul_add]
  | tmul w c =>
    rw [LinearMap.rTensor_tmul, Algebra.lsmul_coe]
    simp only [emptyRightScalarEquiv, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
      TensorProduct.rid_tmul, LinearEquiv.refl_apply]
    exact smul_comm _ p w

/-- `W ⊠ P_∅`, the input of the cut. -/
abbrev emptyRightInput := (SMove.regularRightTensor (k := k) C).obj W

theorem cutInputIdemEnd_regularRight (i : Seq α) (j : Seq δ) (x : W ⊗[k] C) :
    emptyRightScalarEquiv Q Λ θ W (@id (W ⊗[k] C) (cutInputIdemEnd Q Λ θ 0
      (emptyRightInput Q Λ θ W) (i.append j)
        (@id (CutInput Q Λ θ 0 (emptyRightInput Q Λ θ W)) x))) =
      cutPrefixProjection Q Λ θ (e i) • emptyRightScalarEquiv Q Λ θ W x :=
  (congrArg (emptyRightScalarEquiv Q Λ θ W)
    (LinearMap.congr_fun (cutInputIdemEnd_emptyRight Q Λ θ W i j) x)).trans
    (emptyRightScalarEquiv_rTensor Q Λ θ W _ x)

theorem cutInputIdemEnd_regularRight_symm (i : Seq α) (j : Seq δ)
    (y : fixSub k W (cutPrefixProjection Q Λ θ (e i))) :
    @id (W ⊗[k] C) (cutInputIdemEnd Q Λ θ 0 (emptyRightInput Q Λ θ W) (i.append j)
      (@id (CutInput Q Λ θ 0 (emptyRightInput Q Λ θ W))
        ((emptyRightScalarEquiv Q Λ θ W).symm y.1))) =
      (emptyRightScalarEquiv Q Λ θ W).symm y.1 := by
  apply (emptyRightScalarEquiv Q Λ θ W).injective
  rw [cutInputIdemEnd_regularRight, LinearEquiv.apply_symm_apply]
  exact y.2

/-- The input corner of `W ⊠ P_∅` at `(𝐢 red)` is the fixed space of `e(𝐢)` on `W`. -/
def emptyRightInputFixedEquiv (i : Seq α) (j : Seq δ) :
    LinearMap.ker (cutInputIdemEnd Q Λ θ 0 (emptyRightInput Q Λ θ W) (i.append j) - 1) ≃ₗ[k]
      fixSub k W (cutPrefixProjection Q Λ θ (e i)) where
  toFun x := ⟨emptyRightScalarEquiv Q Λ θ W (@id (W ⊗[k] C) x.1),
    (cutInputIdemEnd_regularRight Q Λ θ W i j x.1).symm.trans
      (congrArg (fun z => emptyRightScalarEquiv Q Λ θ W (@id (W ⊗[k] C) z))
        ((mem_ker_sub_one_iff (cutInputIdemEnd Q Λ θ 0 (emptyRightInput Q Λ θ W) (i.append j))
          x.1).mp x.2))⟩
  invFun y := ⟨@id (CutInput Q Λ θ 0 (emptyRightInput Q Λ θ W))
      ((emptyRightScalarEquiv Q Λ θ W).symm y.1),
    (mem_ker_sub_one_iff (cutInputIdemEnd Q Λ θ 0 (emptyRightInput Q Λ θ W) (i.append j))
      _).mpr (cutInputIdemEnd_regularRight_symm Q Λ θ W i j y)⟩
  left_inv x := Subtype.ext ((emptyRightScalarEquiv Q Λ θ W).symm_apply_apply x.1)
  right_inv y := Subtype.ext ((emptyRightScalarEquiv Q Λ θ W).apply_symm_apply y.1)
  map_add' x x' := Subtype.ext (map_add (emptyRightScalarEquiv Q Λ θ W) x.1 x'.1)
  map_smul' c x := Subtype.ext (by
    refine Eq.trans ?_ (map_smul (emptyRightScalarEquiv Q Λ θ W) c (@id (W ⊗[k] C) x.1))
    exact congrArg (emptyRightScalarEquiv Q Λ θ W) (algebraMap_smul_extTensor
      (A := TensorProductAlgebra k Q (Λ ∘ Fin.castAdd 1) θ) (B := C) c
      (@id (ExtTensor k W C) x.1)))

/-- **The loading corner of `𝕊(W ⊠ P_∅)`** (Webster, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.22): the vectors fixed by the loading idempotent of `(𝐢 red)` are the vectors of
`W` fixed by that of `𝐢`. -/
def emptyRightStdCornerEquiv (i : Seq α) (j : Seq δ) :
    fixSub k ((emptyRightStd Q hQ Λ θ).obj W) (cutLoad Q Λ (add_zero θ) (i.append j)) ≃ₗ[k]
      fixSub k W (cutPrefixProjection Q Λ θ (e i)) :=
  (fixSubCutLoadEquiv Q hQ Λ (add_zero θ) (emptyRightInput Q Λ θ W) (i.append j)).trans
    ((cutStandardLoadingFixedEquiv Q Λ θ 0 (emptyRightInput Q Λ θ W) hQ
      (isUnshuffledLoading_append_emptyRight Q Λ θ i j)).trans
      (emptyRightInputFixedEquiv Q Λ θ W i j))

end EmptyRight

/-! ### The three-strand composite -/

namespace SMove

variable {I k : Type} [DecidableEq I] [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q) (Λ : Fin (2 + 1) → I →₀ ℕ) (β : Multiset I)

theorem rightStd_eq_emptyRightStd : rightStd Q hQ Λ β = emptyRightStd Q hQ Λ β := rfl

theorem leftStd_eq_emptyLeftStd (Λ' : Fin (1 + (1 + 1)) → I →₀ ℕ) :
    leftStd Q hQ Λ' β = emptyLeftStd Q hQ Λ' β := rfl

local notation "Λ₂" => (Λ ∘ Fin.castAdd 1 : Fin (1 + 1) → I →₀ ℕ)
local notation "α₂" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd 1))
  (stendhalWeight 1 (0 : Multiset I))
local notation "δ₂" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd 1)) (stendhalWeight 1 β)

/-- The prefix loading `(red₁ 𝐣)` of the outer cut `{1, 2} | {3}`, for a loading `𝐣` of the
inner cut `{1} | {2}`. -/
def innerLoading (i : Seq α₂) (j : Seq δ₂) :
    Seq (Multiset.map (Sum.map (id : I → I) (Fin.castAdd 1)) (stendhalWeight 2 β)) :=
  (redSubfamilyRelabel Q Λ (Fin.castAdd 1) (Fin.castAdd_injective 2 1) β).equiv
    (Seq.cast (congrArg (stendhalWeight (1 + 1)) (zero_add β))
      (Seq.cast (cutInputWeights_add (a := 1) (r := 1) (0 : Multiset I) β) (i.append j)))

theorem cast_tensorLoad {m : ℕ} (Λ' : Fin m → I →₀ ℕ) {ν ν' : Multiset I} (h : ν = ν')
    (c : Seq (stendhalWeight m ν)) :
    castTensorProductAlgebra Q Λ' h (tensorLoad Q Λ' ν c) =
      tensorLoad Q Λ' ν' (Seq.cast (congrArg (stendhalWeight m) h) c) := by
  subst h; rfl

omit [DecidableEq I] in
theorem seq_cast_symm_cast {J : Type*} {μ μ' : Multiset J} (h : μ = μ') (c : Seq μ) :
    Seq.cast h.symm (Seq.cast h c) = c := by
  subst h; rfl

/-- The idempotent of the prefix loading `innerLoading i j` is the loading idempotent of the
inner cut at `i.append j`. -/
theorem cutPrefixProjection_e_innerLoading (i : Seq α₂) (j : Seq δ₂) :
    cutPrefixProjection Q Λ β (e (innerLoading Q Λ β i j)) =
      cutLoad Q Λ₂ (zero_add β) (i.append j) := by
  rw [cutPrefixProjection_e, innerLoading, Equiv.symm_apply_apply, cutLoad,
    ← cast_tensorLoad Q _ (zero_add β),
    tensorLoad_eq_affineToTensor (a := 1) (r := 1), seq_cast_symm_cast]

variable (Z : ModuleCat.{0}
  (TensorProductAlgebra k Q ((Λ ∘ Fin.castAdd 1 : Fin (1 + 1) → I →₀ ℕ) ∘ Fin.natAdd 1) β))

local notation "α₃" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd 1)) (stendhalWeight 2 β)
local notation "δ₃" =>
  Multiset.map (Sum.map (id : I → I) (Fin.natAdd 2)) (stendhalWeight 1 (0 : Multiset I))

/-- **The diagonal corner of the S-move** (Webster, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.22, `Tor_0` on the diagonal): for the loading `(red₁ 𝐣 red₃)`, `𝐣` a loading of
the one-red block `{2}`, the vectors of
`𝕊^{λ_1, λ_2; λ_3}(𝕊^{λ_1; λ_2}(P_∅ ⊠ Z) ⊠ P_∅)` fixed by its loading idempotent are the
vectors of `Z` fixed by the loading idempotent of `𝐣`. No route hypotheses. -/
def diagonalCornerEquiv (i : Seq α₂) (j : Seq δ₂) (j₃ : Seq δ₃) :
    fixSub k ((rightStd Q hQ Λ β).obj ((emptyLeftStd Q hQ Λ₂ β).obj Z))
        (cutLoad Q Λ (add_zero β) ((innerLoading Q Λ β i j).append j₃)) ≃ₗ[k]
      fixSub k Z (cutSuffixProjection Q Λ₂ β (e j)) :=
  (emptyRightStdCornerEquiv Q hQ Λ β _ _ j₃).trans
    ((LinearEquiv.ofEq _ _ (by rw [cutPrefixProjection_e_innerLoading])).trans
      (emptyLeftStdCornerEquiv Q hQ Λ₂ β Z i j))

end SMove

end Categorification.Stendhal

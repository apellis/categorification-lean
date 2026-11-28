/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.WindowBlackBlockIC

/-!
# `A e_R` is a finitely generated projective right `D_R`-module

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, consequence of (B3-R) used for the
module form of (IC), at `ℓ = 0`. Let `A = T̃^{λ⁺}` and `D_R = T̃^{(μ,μ*)} ⊗ T̃^λ`. The corner
`A e_R = {y | y e_R = y}` (`frontRightCorner`) is a right `D_R`-module by `y · d' = y ι_R(d')`,
i.e. a module over `D_Rᵐᵒᵖ` (`frontRightAct`). By (B3-R) it is `⨁_{c'} flip(γ_{c'}) ι_R(1_{c'} D_R)`
over the finitely many front generators `c'`, so it is a direct summand of the finite free
module on the generators `flip(γ_{c'})`:

* `Module.Finite` and `Module.Projective` over `D_Rᵐᵒᵖ` (`frontRightCorner_finite`,
  `frontRightCorner_projective`).

The coordinates `κ(y)` of `y ∈ A e_R` in this decomposition (`frontRightCoord`) satisfy
`κ(y ι_R(d')) = κ(y) d'` and `κ(flip(γ_{c'})) = 1_{c'}` at `c'`; they are used for the module form
of (IC) in `WindowBlackBlockIndCoind`.

Symmetric `Q` (`KLRSymm Q`), any commutative ring `k`, `ℓ = 0`.

## Main definitions

* `CupCap.frontRightCorner`, `CupCap.frontRightAct` (and the module instance),
  `CupCap.frontRightGen`, `CupCap.frontRightCoord`.

## Main results

* `CupCap.frontRightCorner_finite`, `CupCap.frontRightCorner_projective`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA Equiv MvPolynomial MulOpposite
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin 0 → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "T" => StendhalAlgebra k Q Λ ν
local notation "Tc" => StendhalAlgebra k Q Λc ν₀
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc 0 le_rfl) (ν + ν₀)

/-! ### The right `D_R`-module `A e_R` -/

variable (Q Λ Λc ν ν₀) in
/-- The corner `A e_R = {y | y e_R = y}`, as a `k`-submodule. -/
def frontRightCorner : Submodule k Tp where
  carrier := {y | y * frontStendhal Q Λ Λc ν ν₀ 1 = y}
  add_mem' {y y'} hy hy' := by
    change (y + y') * _ = y + y'
    rw [add_mul, hy, hy']
  zero_mem' := zero_mul _
  smul_mem' r y hy := by
    change (r • y) * _ = r • y
    rw [smul_mul_assoc, hy]

theorem mem_frontRightCorner {y : Tp} :
    y ∈ frontRightCorner Q Λ Λc ν ν₀ ↔ y * frontStendhal Q Λ Λc ν ν₀ 1 = y := Iff.rfl

theorem mul_blockTensorR_mem_frontRightCorner (y : Tp) (d' : Tc ⊗[k] T) :
    y * blockTensorR Q Λ Λc ν ν₀ d' ∈ frontRightCorner Q Λ Λc ν ν₀ := by
  rw [mem_frontRightCorner, mul_assoc, blockTensorR_mul_frontStendhal_one]

variable (Q Λ Λc ν ν₀) in
/-- The right action of `D_R` on `A e_R`, `y · d' = y ι_R(d')`, as a ring map from `D_Rᵐᵒᵖ`. -/
def frontRightAct : (Tc ⊗[k] T)ᵐᵒᵖ →+* Module.End k (frontRightCorner Q Λ Λc ν ν₀) where
  toFun d :=
    { toFun := fun y => ⟨y.1 * blockTensorR Q Λ Λc ν ν₀ d.unop,
        mul_blockTensorR_mem_frontRightCorner _ _⟩
      map_add' := fun y y' => Subtype.ext (add_mul _ _ _)
      map_smul' := fun r y => Subtype.ext (smul_mul_assoc _ _ _) }
  map_one' := LinearMap.ext fun y => Subtype.ext (by
    change y.1 * blockTensorR Q Λ Λc ν ν₀ (unop 1) = y.1
    rw [unop_one, blockTensorR_one]
    exact y.2)
  map_mul' a b := LinearMap.ext fun y => Subtype.ext (by
    change y.1 * blockTensorR Q Λ Λc ν ν₀ (unop (a * b)) =
      y.1 * blockTensorR Q Λ Λc ν ν₀ (unop b) * blockTensorR Q Λ Λc ν ν₀ (unop a)
    rw [unop_mul, blockTensorR_mul, mul_assoc])
  map_zero' := LinearMap.ext fun y => Subtype.ext (by
    change y.1 * blockTensorR Q Λ Λc ν ν₀ (unop 0) = 0
    rw [unop_zero, map_zero, mul_zero])
  map_add' a b := LinearMap.ext fun y => Subtype.ext (by
    change y.1 * blockTensorR Q Λ Λc ν ν₀ (unop (a + b)) =
      y.1 * blockTensorR Q Λ Λc ν ν₀ (unop a) + y.1 * blockTensorR Q Λ Λc ν ν₀ (unop b)
    rw [unop_add, map_add, mul_add])

/-- `A e_R` as a right `D_R`-module. -/
instance : Module (Tc ⊗[k] T)ᵐᵒᵖ (frontRightCorner Q Λ Λc ν ν₀) :=
  Module.compHom _ (frontRightAct Q Λ Λc ν ν₀)

theorem op_smul_frontRightCorner (d' : Tc ⊗[k] T) (y : frontRightCorner Q Λ Λc ν ν₀) :
    ((op d' • y : frontRightCorner Q Λ Λc ν ν₀) : Tp) = y.1 * blockTensorR Q Λ Λc ν ν₀ d' :=
  rfl

/-! ### The generators and the coordinates -/

variable {ρ₁ : Perm (Fin (Multiset.card (stendhalWeight 0 ν))) → List ℕ}
  {ρ₂ : Perm (Fin (Multiset.card (stendhalWeight 2 ν₀))) → List ℕ}
  {ρ₃ : Perm (Fin (Multiset.card (stendhalWeight (0 + 2) (ν + ν₀)))) → List ℕ}

/-- `flip(γ_{c'}) ι_R(1_{c'}) = flip(γ_{c'})`. -/
theorem flip_genEltF_mul_blockTensorR_blockIdemF (c' : FrontGen 0 ν ν₀) :
    StendhalAlgebra.flip (genEltF Q Λ Λc ρ₃ c') *
        blockTensorR Q Λ Λc ν ν₀ (blockIdemF Q Λ Λc c') =
      StendhalAlgebra.flip (genEltF Q Λ Λc ρ₃ c') := by
  have h1 : blockTensorR Q Λ Λc ν ν₀ (blockIdemF Q Λ Λc c') * genEltF Q Λ Λc ρ₃ c' =
      genEltF Q Λ Λc ρ₃ c' := by
    rw [blockIdemF, blockTensorR_tmul, mul_assoc, suffixStendhal_e_mul_genEltF,
      frontStendhal_e_mul_genEltF]
  have h2 := congrArg StendhalAlgebra.flip h1
  rwa [StendhalAlgebra.flip_mul, flip_blockTensorR, flipDF_blockIdemF] at h2

variable (Q Λ Λc ρ₃) in
/-- The generator `flip(γ_{c'})` of `A e_R`. -/
def frontRightGen (c' : FrontGen 0 ν ν₀) : frontRightCorner Q Λ Λc ν ν₀ :=
  ⟨StendhalAlgebra.flip (genEltF Q Λ Λc ρ₃ c'), by
    rw [mem_frontRightCorner, ← flip_genEltF_mul_blockTensorR_blockIdemF, mul_assoc,
      blockTensorR_mul_frontStendhal_one]⟩

/-- `∑_{c'} flip(γ_{c'}) ι_R(b_{c'})` as a sum over all front generators. -/
theorem blockSumRF_eq_sum [DecidableEq (FrontGen 0 ν ν₀)] [Fintype (FrontGen 0 ν ν₀)]
    (b : Π₀ c' : FrontGen 0 ν ν₀, blockRightF Q Λ Λc c') :
    blockSumRF Q Λ Λc ρ₃ b = ∑ c', StendhalAlgebra.flip (genEltF Q Λ Λc ρ₃ c') *
      blockTensorR Q Λ Λc ν ν₀ (b c') := by
  induction b using DFinsupp.induction with
  | h0 => simp
  | ha c x f _ _ ih =>
    have hs : ∑ c', StendhalAlgebra.flip (genEltF Q Λ Λc ρ₃ c') *
        blockTensorR Q Λ Λc ν ν₀
          ((DFinsupp.single c x : Π₀ c', blockRightF Q Λ Λc c') c' : Tc ⊗[k] T) =
          StendhalAlgebra.flip (genEltF Q Λ Λc ρ₃ c) * blockTensorR Q Λ Λc ν ν₀ x := by
      rw [Finset.sum_eq_single c (fun c' _ hc' => by
          rw [DFinsupp.single_eq_of_ne hc', Submodule.coe_zero, map_zero, mul_zero])
        (by simp), DFinsupp.single_eq_same]
    simp only [DFinsupp.add_apply, Submodule.coe_add, map_add, mul_add, Finset.sum_add_distrib,
      hs, ih, blockSumRF_single]

private theorem stendhalE_mul_self' {ℓ' : ℕ} {Λ' : Fin ℓ' → I →₀ ℕ} {ν' : Multiset I}
    (s : Seq (stendhalWeight ℓ' ν')) (hs : IsRedOrdered s) :
    (StendhalAlgebra.e s hs * StendhalAlgebra.e s hs : StendhalAlgebra k Q Λ' ν') =
      StendhalAlgebra.e s hs := by
  apply Subtype.ext
  change StendhalAlgebraAllOrders.e s * StendhalAlgebraAllOrders.e s = _
  rw [StendhalAlgebraAllOrders.e_mul_e, ite_eq_left rfl]
  rfl

theorem blockIdemF_mem_blockRightF (c' : FrontGen 0 ν ν₀) :
    blockIdemF Q Λ Λc c' ∈ blockRightF Q Λ Λc c' := by
  rw [mem_blockRightF, blockIdemF, Algebra.TensorProduct.tmul_mul_tmul, stendhalE_mul_self',
    stendhalE_mul_self']

omit [DecidableEq I] in
private theorem equivFunOnFinite_symm_apply' {α M : Type*} [Zero M] [Finite α] (g : α → M)
    (a : α) : Finsupp.equivFunOnFinite.symm g a = g a :=
  congrFun (Finsupp.equivFunOnFinite.apply_symm_apply g) a

section Coord

variable [DecidableEq (FrontGen 0 ν ν₀)] (hQ : KLRSymm Q)
  (hρ₁ : ∀ a, IsReduced (Multiset.card (stendhalWeight 0 ν)) (ρ₁ a) ∧
    wordProd (Multiset.card (stendhalWeight 0 ν)) (ρ₁ a) = a)
  (hρ₂ : ∀ b, IsReduced (Multiset.card (stendhalWeight 2 ν₀)) (ρ₂ b) ∧
    wordProd (Multiset.card (stendhalWeight 2 ν₀)) (ρ₂ b) = b)
  (hρ₃ : ∀ w, IsReduced (Multiset.card (stendhalWeight (0 + 2) (ν + ν₀))) (ρ₃ w) ∧
    wordProd (Multiset.card (stendhalWeight (0 + 2) (ν + ν₀))) (ρ₃ w) = w)

include hQ hρ₁ hρ₂ hρ₃

theorem frontRightCorner_le_range :
    frontRightCorner Q Λ Λc ν ν₀ ≤ LinearMap.range (blockSumRF Q Λ Λc ρ₃) :=
  fun y hy => (mem_range_blockSumRF_iff (ρ₁ := ρ₁) hQ hρ₁ hρ₂ hρ₃ y).2 hy

variable (Q Λ Λc ρ₃) in
/-- **The coordinates** of `y ∈ A e_R` in `⨁_{c'} 1_{c'} D_R` (inverse of (B3-R)). -/
def frontRightCoord :
    frontRightCorner Q Λ Λc ν ν₀ →ₗ[k] Π₀ c' : FrontGen 0 ν ν₀, blockRightF Q Λ Λc c' :=
  (LinearEquiv.ofInjective (blockSumRF Q Λ Λc ρ₃)
      (blockSumRF_injective (ρ₁ := ρ₁) hQ hρ₁ hρ₂ hρ₃)).symm.toLinearMap ∘ₗ
    Submodule.inclusion (frontRightCorner_le_range hQ hρ₁ hρ₂ hρ₃)

theorem blockSumRF_frontRightCoord (y : frontRightCorner Q Λ Λc ν ν₀) :
    blockSumRF Q Λ Λc ρ₃ (frontRightCoord Q Λ Λc ρ₃ hQ hρ₁ hρ₂ hρ₃ y) = y.1 :=
  congrArg Subtype.val ((LinearEquiv.ofInjective (blockSumRF Q Λ Λc ρ₃)
    (blockSumRF_injective (ρ₁ := ρ₁) hQ hρ₁ hρ₂ hρ₃)).apply_symm_apply
      (Submodule.inclusion (frontRightCorner_le_range hQ hρ₁ hρ₂ hρ₃) y))

theorem frontRightCoord_eq {y : frontRightCorner Q Λ Λc ν ν₀}
    {b : Π₀ c' : FrontGen 0 ν ν₀, blockRightF Q Λ Λc c'} (h : blockSumRF Q Λ Λc ρ₃ b = y.1) :
    frontRightCoord Q Λ Λc ρ₃ hQ hρ₁ hρ₂ hρ₃ y = b :=
  blockSumRF_injective (ρ₁ := ρ₁) hQ hρ₁ hρ₂ hρ₃ (by rw [blockSumRF_frontRightCoord, h])

/-- The coordinates are right `D_R`-linear. -/
theorem frontRightCoord_op_smul (d' : Tc ⊗[k] T) (y : frontRightCorner Q Λ Λc ν ν₀) :
    frontRightCoord Q Λ Λc ρ₃ hQ hρ₁ hρ₂ hρ₃ (op d' • y) =
      blockRightMulF Q Λ Λc d' (frontRightCoord Q Λ Λc ρ₃ hQ hρ₁ hρ₂ hρ₃ y) :=
  frontRightCoord_eq hQ hρ₁ hρ₂ hρ₃ (by
    rw [blockSumRF_blockRightMulF, blockSumRF_frontRightCoord]
    rfl)

/-- The coordinates of the generator `flip(γ_{c'})`: `1_{c'}` at `c'`. -/
theorem frontRightCoord_gen (c' : FrontGen 0 ν ν₀) :
    frontRightCoord Q Λ Λc ρ₃ hQ hρ₁ hρ₂ hρ₃ (frontRightGen Q Λ Λc ρ₃ c') =
      DFinsupp.single c' ⟨blockIdemF Q Λ Λc c', blockIdemF_mem_blockRightF c'⟩ :=
  frontRightCoord_eq hQ hρ₁ hρ₂ hρ₃ (by
    rw [blockSumRF_single]
    exact flip_genEltF_mul_blockTensorR_blockIdemF c')

variable (Q Λ Λc ρ₃) in
/-- The combination map `(c' ↦ r_{c'}) ↦ ∑ flip(γ_{c'}) · r_{c'}` from the free module. -/
def frontRightComb :
    (FrontGen 0 ν ν₀ →₀ (Tc ⊗[k] T)ᵐᵒᵖ) →ₗ[(Tc ⊗[k] T)ᵐᵒᵖ] frontRightCorner Q Λ Λc ν ν₀ :=
  Finsupp.linearCombination _ (frontRightGen Q Λ Λc ρ₃)

variable (Q Λ Λc ρ₃) in
/-- The coordinates as a right `D_R`-linear map into the free module. -/
def frontRightCoordFree :
    frontRightCorner Q Λ Λc ν ν₀ →ₗ[(Tc ⊗[k] T)ᵐᵒᵖ] (FrontGen 0 ν ν₀ →₀ (Tc ⊗[k] T)ᵐᵒᵖ) where
  toFun y := Finsupp.equivFunOnFinite.symm fun c' =>
    op ((frontRightCoord Q Λ Λc ρ₃ hQ hρ₁ hρ₂ hρ₃ y c' : Tc ⊗[k] T))
  map_add' y y' := by
    ext c'
    simp only [map_add, DFinsupp.add_apply, Submodule.coe_add, op_add,
      equivFunOnFinite_symm_apply', Finsupp.add_apply]
  map_smul' r y := by
    induction r using MulOpposite.rec' with
    | h d' =>
      ext c'
      simp only [frontRightCoord_op_smul, equivFunOnFinite_symm_apply',
        RingHom.id_apply, Finsupp.smul_apply, smul_eq_mul, blockRightMulF,
        DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_apply, LinearMap.coe_mk,
        AddHom.coe_mk, op_mul]

theorem frontRightComb_comp_coordFree :
    (frontRightComb Q Λ Λc ρ₃).comp (frontRightCoordFree Q Λ Λc ρ₃ hQ hρ₁ hρ₂ hρ₃) =
      LinearMap.id := by
  classical
  let _ : Fintype (FrontGen 0 ν ν₀) := Fintype.ofFinite _
  refine LinearMap.ext fun y => Subtype.ext ?_
  rw [LinearMap.comp_apply, frontRightComb, Finsupp.linearCombination_apply,
    Finsupp.sum_fintype _ _ (fun _ => by simp), LinearMap.id_apply,
    Submodule.coe_sum]
  conv_rhs => rw [← blockSumRF_frontRightCoord hQ hρ₁ hρ₂ hρ₃ y, blockSumRF_eq_sum]
  rfl

/-- **`A e_R` is projective over `D_R`.** -/
theorem frontRightCorner_projective :
    Module.Projective (Tc ⊗[k] T)ᵐᵒᵖ (frontRightCorner Q Λ Λc ν ν₀) :=
  Module.Projective.of_split (frontRightCoordFree Q Λ Λc ρ₃ hQ hρ₁ hρ₂ hρ₃)
    (frontRightComb Q Λ Λc ρ₃) (frontRightComb_comp_coordFree hQ hρ₁ hρ₂ hρ₃)

/-- **`A e_R` is finitely generated over `D_R`.** -/
theorem frontRightCorner_finite :
    Module.Finite (Tc ⊗[k] T)ᵐᵒᵖ (frontRightCorner Q Λ Λc ν ν₀) :=
  Module.Finite.of_surjective (frontRightComb Q Λ Λc ρ₃) fun y =>
    ⟨frontRightCoordFree Q Λ Λc ρ₃ hQ hρ₁ hρ₂ hρ₃ y,
      LinearMap.congr_fun (frontRightComb_comp_coordFree hQ hρ₁ hρ₂ hρ₃) y⟩

end Coord

end Categorification.Stendhal.CupCap

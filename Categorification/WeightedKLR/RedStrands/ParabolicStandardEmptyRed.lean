/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastKernel
import Categorification.KLR.CyclotomicAbsentColour

/-!
# Standardization with an empty last block

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5. When the last block is empty (`β = ∅`), the factor algebra is
`T^{λ'} ⊗ R^{λ_ℓ}_0 ≅ T^{λ'}`, and standardization of a module `N` is a quotient of the induction
of `N` along the map `T^{λ'} → T^λ` adding a red strand on the right
(`Prop 4.18`). This file constructs the surjection.

## Main definitions

* `emptyFactorToOld`: the factor algebra at `β = ∅` is `T^{λ'}`.
* `EmptyRedInd`: the induction of `N` along `appendRed`.
* `emptyRedStandard`: the map `S(N) → EmptyRedInd N`.

## Main results

* `emptyRedStandard_surjective`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra InductionAlong MulOpposite
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} {k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (θ : Multiset I)

local notation "old" => Λ ∘ Fin.castSucc
local notation "S" => stendhalQ Q Λ
local notation "Aₚ" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ)
local notation "A₀" => Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ))
  (stendhalWeight 1 (0 : Multiset I))
local notation "L₀" => TensorProductAlgebra k Q (old) (θ + 0)
local notation "T₀" => TensorProductAlgebra k Q Λ (θ + 0)
local notation "λf" => (fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i)

/-- The factor algebra with an empty last block is `T^{λ'}`. -/
def emptyFactorEquiv :
    parabolicFactorAlgebra Q Λ θ 0 ≃ₐ[k] TensorProductAlgebra k Q (old) θ :=
  (Algebra.TensorProduct.congr AlgEquiv.refl (cyclotomicZeroEquiv Q λf)).trans
    (Algebra.TensorProduct.rid k k _)

/-- The factor algebra with an empty last block, as `T^{λ'}` on the weight `θ + 0`. -/
def emptyFactorToOld : parabolicFactorAlgebra Q Λ θ 0 ≃ₐ[k] L₀ :=
  (emptyFactorEquiv Q Λ θ).trans (castTensorProductAlgebra Q (old) (add_zero θ).symm)

/-- Appending the last red strand, as a nonunital map `T^{λ'} → T^λ`. -/
def emptyRedHom : L₀ →ₙ+* T₀ :=
  (KLR.cornerVal (TensorProductAlgebra.isIdempotentElem_lastRedIdem Q Λ (θ + 0))).comp
    (appendRed Q Λ (θ + 0)).toRingHom.toNonUnitalRingHom

theorem emptyRedHom_apply (x : L₀) : emptyRedHom Q Λ θ x = (appendRed Q Λ (θ + 0) x).val := rfl

theorem appendRed_castTensorProductAlgebra {θ θ' : Multiset I} (h : θ = θ')
    (x : TensorProductAlgebra k Q (old) θ) :
    (appendRed Q Λ θ' (castTensorProductAlgebra Q (old) h x)).val =
      castTensorProductAlgebra Q Λ h (appendRed Q Λ θ x).val := by
  subst h; rfl

omit [DecidableEq I] in
theorem emptyRed_mem (a : I ⊕ Fin (ℓ + 1)) (ha : a ∈ A₀) : a = Sum.inr (Fin.last ℓ) := by
  simpa [stendhalWeight] using ha

omit [DecidableEq I] in
theorem emptyRed_eq : A₀ = ({Sum.inr (Fin.last ℓ)} : Multiset (I ⊕ Fin (ℓ + 1))) := by
  simp [stendhalWeight]

/-- `parabolicAffine` at `β = ∅`, bundled. -/
def emptyAffine : KLRAlgebra k S (Aₚ + A₀) →ₐ[k] T₀ :=
  (TensorProductAlgebra.mk Q Λ (θ + 0)).comp ((orderProjection Q Λ (θ + 0)).comp
    ((StendhalAlgebraAllOrders.ofKLR k Q Λ (θ + 0)).comp
      (castKLR S (parabolicInputWeights_add (ℓ := ℓ) θ 0)).toAlgHom))

theorem emptyAffine_apply (a : KLRAlgebra k S (Aₚ + A₀)) :
    emptyAffine Q Λ θ a = parabolicAffine Q Λ θ 0 a := rfl

/-- The element of `T^λ` represented by a diagram on the parabolic weight with no black strands
in the last block. -/
def emptyF : TensorKLR S Aₚ A₀ →ₗ[k] T₀ := (emptyAffine Q Λ θ).toLinearMap ∘ₗ concat S Aₚ A₀

theorem emptyF_apply (t : TensorKLR S Aₚ A₀) :
    emptyF Q Λ θ t = parabolicAffine Q Λ θ 0 (concat S Aₚ A₀ t) := rfl

/-- `appendRed` as a `k`-linear map into `T^λ`. -/
def emptyRedLin : L₀ →ₗ[k] T₀ where
  toFun := emptyRedHom Q Λ θ
  map_add' := map_add _
  map_smul' c y := by
    rw [emptyRedHom_apply, emptyRedHom_apply, map_smul, RingHom.id_apply]
    generalize appendRed Q Λ (θ + 0) y = a
    have hx := (Subsemigroup.mem_corner_iff
      (TensorProductAlgebra.isIdempotentElem_lastRedIdem Q Λ (θ + 0))).1 a.2
    rw [Algebra.smul_def c a, Algebra.smul_def c a.val]
    change (algebraMap k (TensorProductAlgebra.lastRedCorner Q Λ (θ + 0)) c).1 * a.1 =
      algebraMap k T₀ c * a.1
    change algebraMap k T₀ c * _ * a.1 = _
    rw [mul_assoc, hx.1]

/-- The same element computed through the factor algebra and `appendRed`. -/
def emptyG : TensorKLR S Aₚ A₀ →ₗ[k] T₀ :=
  emptyRedLin Q Λ θ ∘ₗ (emptyFactorToOld Q Λ θ).toLinearMap ∘ₗ
    (parabolicInputMap Q Λ θ 0).toLinearMap

theorem emptyG_apply (t : TensorKLR S Aₚ A₀) :
    emptyG Q Λ θ t = emptyRedHom Q Λ θ (emptyFactorToOld Q Λ θ (parabolicInputMap Q Λ θ 0 t)) :=
  rfl

theorem emptyF_mul (s t : TensorKLR S Aₚ A₀) :
    emptyF Q Λ θ (s * t) = emptyF Q Λ θ s * emptyF Q Λ θ t := by
  simp only [emptyF_apply, concat_mul, ← emptyAffine_apply, map_mul]

theorem emptyG_mul (s t : TensorKLR S Aₚ A₀) :
    emptyG Q Λ θ (s * t) = emptyG Q Λ θ s * emptyG Q Λ θ t := by
  simp only [emptyG_apply, map_mul]

private theorem emptyConcat_one_tmul_x_mul (b : Fin (A₀).card) (t : Seq (A₀)) :
    concat S Aₚ A₀ (1 ⊗ₜ (x b * e t)) = x (Seq.posR Aₚ b) * concat S Aₚ A₀ (1 ⊗ₜ e t) := by
  rw [show (1 : KLRAlgebra k S Aₚ) ⊗ₜ[k] (x b * e t) =
      ((1 : KLRAlgebra k S Aₚ) ⊗ₜ[k] (x b : KLRAlgebra k S A₀)) * (1 ⊗ₜ[k] e t) by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul],
    concat_mul, concat_one_tmul_x, mul_assoc, oneConcat_mul_concat]

theorem emptyF_one_tmul (v : KLRAlgebra k S A₀) :
    emptyF Q Λ θ (1 ⊗ₜ v) =
      cyclotomicZeroEquiv Q λf (parabolicLastCyclotomic Q Λ 0 v) • emptyF Q Λ θ (1 ⊗ₜ 1) := by
  let := Seq.uniqueOfForall (emptyRed_mem (I := I) (ℓ := ℓ))
  induction v using klr_induction with
  | hadd u v hu hv => rw [TensorProduct.tmul_add, map_add, hu, hv, map_add, map_add, add_smul]
  | hmul u v hu hv =>
    rw [show (1 : KLRAlgebra k S Aₚ) ⊗ₜ[k] (u * v) =
      ((1 : KLRAlgebra k S Aₚ) ⊗ₜ[k] u) * (1 ⊗ₜ[k] v) by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul], emptyF_mul, hu, hv, smul_mul_smul_comm,
      ← emptyF_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul, map_mul, map_mul]
  | hr r =>
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, map_smul, map_smul, map_smul,
      map_one, map_one, smul_eq_mul, mul_one]
  | he s => rw [e_eq_one, map_one, map_one, one_smul]
  | hx b =>
    have hb : ((default : Seq (A₀)).lbl b).isRight := by
      rw [Seq.lbl, emptyRed_mem _ ((default : Seq (A₀)).mem b)]; rfl
    have h1 : (x b : KLRAlgebra k S A₀) = x b * e default := by rw [e_eq_one, mul_one]
    rw [h1, parabolicLastCyclotomic, AlgHom.comp_apply,
      parabolicLastProjection_red_dot _ _ _ _ _ hb, map_zero, map_zero, zero_smul, emptyF_apply,
      emptyConcat_one_tmul_x_mul, concat_one_tmul_e, Finset.mul_sum, ← emptyAffine_apply,
      map_sum, Finset.sum_eq_zero fun i _ => ?_]
    rw [emptyAffine_apply]
    change TensorProductAlgebra.mk Q Λ (θ + 0) (orderProjection Q Λ (θ + 0)
      (StendhalAlgebraAllOrders.ofKLR k Q Λ (θ + 0) (castKLR S _ _))) = 0
    rw [map_mul, castKLR_x, castKLR_e, map_mul]
    refine (congrArg (fun z => TensorProductAlgebra.mk Q Λ (θ + 0) (orderProjection Q Λ (θ + 0) z))
      (StendhalAlgebraAllOrders.x_mul_e_of_red _ _ ?_)).trans (by simp)
    simp only [Seq.lbl] at hb ⊢
    simpa using hb
  | hψ j =>
    rw [ψ_eq_zero j (by simp [emptyRed_eq]), TensorProduct.tmul_zero, map_zero, map_zero,
      map_zero, zero_smul]

theorem cyclotomicZero_eq_smul_one (w : CycKLR k Q λf (0 : Multiset I)) :
    w = cyclotomicZeroEquiv Q λf w • (1 : CycKLR k Q λf (0 : Multiset I)) := by
  conv_lhs => rw [← (cyclotomicZeroEquiv Q λf).symm_apply_apply w]
  rw [← Algebra.algebraMap_eq_smul_one, ← AlgEquiv.commutes (cyclotomicZeroEquiv Q λf).symm,
    Algebra.algebraMap_self, RingHom.id_apply]

theorem parabolicInputMap_one_tmul (v : KLRAlgebra k S A₀) :
    parabolicInputMap Q Λ θ 0 (1 ⊗ₜ v) =
      cyclotomicZeroEquiv Q λf (parabolicLastCyclotomic Q Λ 0 v) •
        parabolicInputMap Q Λ θ 0 (1 ⊗ₜ 1) := by
  rw [parabolicInputMap, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
    map_one, map_one]
  conv_lhs => rw [cyclotomicZero_eq_smul_one Q Λ (parabolicLastCyclotomic Q Λ 0 v)]
  rw [TensorProduct.tmul_smul]

theorem emptyG_one_tmul (v : KLRAlgebra k S A₀) :
    emptyG Q Λ θ (1 ⊗ₜ v) =
      cyclotomicZeroEquiv Q λf (parabolicLastCyclotomic Q Λ 0 v) • emptyG Q Λ θ (1 ⊗ₜ 1) := by
  simp only [emptyG, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    AlgEquiv.toLinearMap_apply]
  rw [parabolicInputMap_one_tmul, map_smul, map_smul]

theorem castKLR_concat_tmul_one {d d' : Multiset (I ⊕ Fin (ℓ + 1))} (hd : d = d')
    {T : Multiset (I ⊕ Fin (ℓ + 1))} (h₁ : Aₚ + d = T) (h₂ : Aₚ + d' = T)
    (u : KLRAlgebra k S Aₚ) :
    castKLR S h₁ (concat S Aₚ d (u ⊗ₜ 1)) = castKLR S h₂ (concat S Aₚ d' (u ⊗ₜ 1)) := by
  subst hd; rfl

theorem emptyG_tmul_one (u : KLRAlgebra k S Aₚ) :
    emptyG Q Λ θ (u ⊗ₜ 1) =
      (appendRed Q Λ (θ + 0) (castTensorProductAlgebra Q (old) (add_zero θ).symm
        (parabolicPrefixProjection Q Λ θ u))).val := by
  rw [emptyG_apply, emptyRedHom_apply, parabolicInputMap, Algebra.TensorProduct.map_tmul,
    map_one]
  congr 2
  simp [emptyFactorToOld, emptyFactorEquiv]

theorem emptyF_tmul_one (u : KLRAlgebra k S Aₚ) :
    emptyF Q Λ θ (u ⊗ₜ 1) = emptyG Q Λ θ (u ⊗ₜ 1) := by
  rw [emptyG_tmul_one, appendRed_castTensorProductAlgebra,
    ← tensorOfKLR_concat_one_eq_appendRed, castTensorProductAlgebra_mk, castKLR_castKLR,
    emptyF_apply]
  exact congrArg (tensorOfKLR Q Λ (θ + 0)) (castKLR_concat_tmul_one Q Λ θ (emptyRed_eq) _ _ u)

theorem emptyF_eq_emptyG : emptyF Q Λ θ = emptyG Q Λ θ := by
  refine TensorProduct.ext' fun u v => ?_
  rw [show u ⊗ₜ[k] v = (u ⊗ₜ[k] (1 : KLRAlgebra k S A₀)) * (1 ⊗ₜ v) by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul], emptyF_mul, emptyG_mul,
    emptyF_tmul_one, emptyF_one_tmul, emptyG_one_tmul, emptyF_tmul_one, ← emptyF_tmul_one]

end Categorification.Stendhal

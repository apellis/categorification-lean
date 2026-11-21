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
`T^{λ'} ⊗ R^{λ_ℓ}_0 ≅ T^{λ'}`, and standardization of a module `N` is the induction of `N`
along the map `T^{λ'} → T^λ` adding a red strand on the right (`Prop 4.18`). The inverse is
`z ⊗ n ↦ z · (1 ⊗ n)`, so in this case no dimension count is needed.

## Main definitions

* `emptyFactorToOld`: the factor algebra at `β = ∅` is `T^{λ'}`.
* `EmptyRedInd`: the induction of `N` along `appendRed`.
* `emptyRedStandard`: the map `S(N) → EmptyRedInd N`, and `emptyRedInv` its inverse.
* `emptyRedStandardEquiv`: `S(N) ≅ EmptyRedInd N` as `T^λ`-modules.

## Main results

* `emptyRedStandard_surjective`, `emptyRedStandard_injective`.
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


/-! ### The induced module and the map from standardization -/

/-- A module of the factor algebra at `β = ∅`, viewed as a `T^{λ'}`-module. -/
def EmptyRedInput (N : Type*) [AddCommGroup N] [Module (parabolicFactorAlgebra Q Λ θ 0) N] :=
  N

section Induced

variable (N : Type*) [AddCommGroup N] [Module k N] [Module (parabolicFactorAlgebra Q Λ θ 0) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ 0) N] (hQ : KLRSymm Q)

local notation "N₁" => EmptyRedInput Q Λ θ N

instance : AddCommGroup N₁ := inferInstanceAs (AddCommGroup N)
instance : Module k N₁ := inferInstanceAs (Module k N)
instance : Module L₀ N₁ :=
  Module.compHom N (emptyFactorToOld Q Λ θ).symm.toAlgHom.toRingHom
instance : IsScalarTower k L₀ N₁ := ⟨fun c t n => by
  change ((emptyFactorToOld Q Λ θ).symm (c • t)) • (show N from n) =
    c • (((emptyFactorToOld Q Λ θ).symm t) • (show N from n))
  rw [map_smul, smul_assoc]⟩

/-- **The induction of `N` along `T^{λ'} → T^λ`**, adding the last red strand
(Webster, arXiv:1309.3796v3, Prop 4.18). -/
abbrev EmptyRedInd := InductionAlong.IndK k N₁ (emptyRedHom Q Λ θ)

local notation "J" => EmptyRedInd Q Λ θ N

instance : SMulCommClass T₀ k J := ⟨fun a c x => by
  change a • (algebraMap k T₀ c • x) = algebraMap k T₀ c • (a • x)
  rw [← mul_smul, ← mul_smul, Algebra.commutes]⟩

theorem emptyRedHom_smul (c : k) (t : L₀) :
    emptyRedHom Q Λ θ (c • t) = c • emptyRedHom Q Λ θ t :=
  (emptyRedLin Q Λ θ).map_smul c t

/-- `N` as a `T^{λ'}`-module. -/
def emptyIn (n : ParabolicInput Q Λ θ 0 N) : N₁ := n

omit [Module k N] [IsScalarTower k (parabolicFactorAlgebra Q Λ θ 0) N] in
theorem emptyIn_smul (t : TensorKLR S Aₚ A₀) (y : ParabolicInput Q Λ θ 0 N) :
    emptyIn Q Λ θ N (t • y) =
      (emptyFactorToOld Q Λ θ (parabolicInputMap Q Λ θ 0 t)) • emptyIn Q Λ θ N y := by
  change _ = (emptyFactorToOld Q Λ θ).symm (emptyFactorToOld Q Λ θ _) • (show N from y)
  rw [AlgEquiv.symm_apply_apply]
  rfl

/-- The generator map `n ↦ 1 ⊗ n`. -/
def emptyRedGen : ParabolicInput Q Λ θ 0 N →ₗ[k] J where
  toFun n := InductionAlong.IndK.tmul (unitGen (emptyRedHom Q Λ θ)) (emptyIn Q Λ θ N n)
  map_add' n n' := Ind.tmul_add _ (emptyIn Q Λ θ N n) (emptyIn Q Λ θ N n')
  map_smul' c n :=
    Ind.tmul_algebraMap_smul k (emptyRedHom_smul Q Λ θ) (unitGen _) c (emptyIn Q Λ θ N n)

theorem emptyRedGen_apply (n : ParabolicInput Q Λ θ 0 N) :
    emptyRedGen Q Λ θ N n = Ind.tmul (unitGen (emptyRedHom Q Λ θ)) (emptyIn Q Λ θ N n) := rfl

theorem emptyRedGen_smul (t : TensorKLR S Aₚ A₀) (y : ParabolicInput Q Λ θ 0 N) :
    emptyRedGen Q Λ θ N (t • y) = emptyF Q Λ θ t • emptyRedGen Q Λ θ N y := by
  rw [emptyRedGen_apply, emptyRedGen_apply, emptyIn_smul, ← Ind.op_smul_tmul, emptyF_eq_emptyG]
  refine (congrArg (fun w => Ind.tmul w (emptyIn Q Λ θ N y)) ?_).trans
    (Ind.smul_tmul (emptyG Q Λ θ t) _ _).symm
  apply Subtype.ext
  change emptyRedHom Q Λ θ 1 * emptyRedHom Q Λ θ _ = emptyG Q Λ θ t * emptyRedHom Q Λ θ 1
  rw [emptyG_apply, ← map_mul, ← map_mul, one_mul, mul_one]
  rfl

/-- The bilinear map `(r, y) ↦ r · (1 ⊗ y)`. -/
def emptyStdBil : IndBimod S Aₚ A₀ →ₗ[k] ParabolicInput Q Λ θ 0 N →ₗ[k] J :=
  LinearMap.mk₂ k (fun r y => emptyAffine Q Λ θ r.1 • emptyRedGen Q Λ θ N y)
    (fun r r' y => by rw [Submodule.coe_add, map_add, add_smul])
    (fun c r y => by
      change emptyAffine Q Λ θ (c • r.1) • _ = _
      rw [map_smul, smul_assoc])
    (fun r y y' => by rw [map_add, smul_add])
    (fun c r y => by rw [map_smul, smul_comm])

/-- The map from the shuffle module, `r ⊗ y ↦ r · (1 ⊗ y)`. -/
def emptyStdShuffle : ParabolicShuffle Q Λ θ 0 N →ₗ[k] J :=
  BalancedTensor.lift (emptyStdBil Q Λ θ N) (fun r a y => by
    change emptyAffine Q Λ θ (r.1 * concat S Aₚ A₀ a) • _ =
      emptyAffine Q Λ θ r.1 • emptyRedGen Q Λ θ N (a • y)
    rw [emptyRedGen_smul, map_mul, mul_smul]
    rfl)

theorem emptyStdShuffle_tmul (r : IndBimod S Aₚ A₀) (y : ParabolicInput Q Λ θ 0 N) :
    emptyStdShuffle Q Λ θ N (BalancedTensor.tmul r y) =
      emptyAffine Q Λ θ r.1 • emptyRedGen Q Λ θ N y := rfl

theorem emptyStdShuffle_smul (b : KLRAlgebra k S (Aₚ + A₀)) (x : ParabolicShuffle Q Λ θ 0 N) :
    emptyStdShuffle Q Λ θ N (b • x) = emptyAffine Q Λ θ b • emptyStdShuffle Q Λ θ N x := by
  induction x using BalancedTensor.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul r y =>
    rw [BalancedTensor.smul_tmul', emptyStdShuffle_tmul, emptyStdShuffle_tmul]
    change emptyAffine Q Λ θ (b * r.1) • _ = _
    rw [map_mul, mul_smul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

theorem emptyAffine_eSum :
    emptyAffine Q Λ θ (eSum S (parabolicOrderedLoadings (ℓ := ℓ) θ 0)) = 1 := by
  rw [emptyAffine_apply, parabolicOrderedLoadings_eq_redOrderedSet, parabolicAffine,
    castKLR_eSum_redOrderedSet, orderProjection_ofKLR_eSum_redOrderedSet, map_one]

/-- **The map `S(N) → Ind N`** from standardization to the induction along the last red
strand, for an empty last block. -/
def emptyRedStandard : ParabolicStandardT Q Λ θ 0 N hQ →ₗ[k] J :=
  (excludedSpace (parabolicShuffleAction Q Λ θ 0 N)
    (parabolicOrderedLoadings (ℓ := ℓ) θ 0)).liftQ
    (emptyStdShuffle Q Λ θ N) (fun x hx => by
      rw [LinearMap.mem_ker]
      have hx' : eSum S (parabolicOrderedLoadings (ℓ := ℓ) θ 0) • x = 0 := hx
      rw [← one_smul T₀ (emptyStdShuffle Q Λ θ N x), ← emptyAffine_eSum,
        ← emptyStdShuffle_smul, hx', map_zero])

/-- The class of `x` in `S(N)`. -/
def emptyStdMk (x : ParabolicShuffle Q Λ θ 0 N) : ParabolicStandardT Q Λ θ 0 N hQ :=
  Submodule.mkQ _ x

theorem emptyRedStandard_mk (x : ParabolicShuffle Q Λ θ 0 N) :
    emptyRedStandard Q Λ θ N hQ (emptyStdMk Q Λ θ N hQ x) = emptyStdShuffle Q Λ θ N x := rfl

theorem emptyStdMk_smul (a : KLRAlgebra k S (Aₚ + A₀)) (x : ParabolicShuffle Q Λ θ 0 N) :
    emptyAffine Q Λ θ a • emptyStdMk Q Λ θ N hQ x = emptyStdMk Q Λ θ N hQ (a • x) := by
  change parabolicStandardAction Q Λ θ 0 N hQ _ _ = _
  rw [emptyAffine_apply, parabolicAffine, parabolicStandardAction_affine]
  rfl

/-- `emptyRedStandard` is `T^λ`-linear. -/
theorem emptyRedStandard_smul (t : T₀) (m : ParabolicStandardT Q Λ θ 0 N hQ) :
    emptyRedStandard Q Λ θ N hQ (t • m) = t • emptyRedStandard Q Λ θ N hQ m := by
  obtain ⟨a, rfl⟩ := parabolicAffine_surjective Q Λ θ 0 t
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (excludedSpace
    (parabolicShuffleAction Q Λ θ 0 N) (parabolicOrderedLoadings (ℓ := ℓ) θ 0)) m
  change emptyRedStandard Q Λ θ N hQ (emptyAffine Q Λ θ a • emptyStdMk Q Λ θ N hQ x) =
    emptyAffine Q Λ θ a • emptyRedStandard Q Λ θ N hQ (emptyStdMk Q Λ θ N hQ x)
  rw [emptyStdMk_smul, emptyRedStandard_mk, emptyRedStandard_mk, emptyStdShuffle_smul]

/-- `emptyRedStandard` as a map of `T^λ`-modules. -/
def emptyRedStandardT : ParabolicStandardT Q Λ θ 0 N hQ →ₗ[T₀] J where
  toFun := emptyRedStandard Q Λ θ N hQ
  map_add' := map_add _
  map_smul' := emptyRedStandard_smul Q Λ θ N hQ

theorem emptyRedStandard_mk_one (n : ParabolicInput Q Λ θ 0 N) :
    emptyRedStandard Q Λ θ N hQ
        (emptyStdMk Q Λ θ N hQ (BalancedTensor.tmul (oneBimod S Aₚ A₀) n)) =
      emptyRedGen Q Λ θ N n := by
  rw [emptyRedStandard_mk, emptyStdShuffle_tmul]
  change emptyAffine Q Λ θ (oneConcat S Aₚ A₀) • _ = _
  rw [← concat_one]
  change emptyF Q Λ θ 1 • _ = _
  rw [emptyF_eq_emptyG, emptyG_apply, map_one, map_one, emptyRedGen_apply]
  exact (Ind.smul_tmul _ _ _).trans
    (congrArg (fun w => Ind.tmul w _) (Subtype.ext (unit_mul_unit (emptyRedHom Q Λ θ))))

/-- **`S(N)` maps onto the induction of `N` along the last red strand** (Webster,
arXiv:1309.3796v3, proof of Prop 5.5, `β = ∅`). -/
theorem emptyRedStandard_surjective : Function.Surjective (emptyRedStandard Q Λ θ N hQ) := by
  intro y
  refine Ind.induction_on (motive := fun y : J => ∃ m, emptyRedStandard Q Λ θ N hQ m = y) y
    ⟨0, map_zero _⟩ (fun z n => ?_) (fun s t hs ht => ?_)
  · refine ⟨z.1 • emptyStdMk Q Λ θ N hQ
      (BalancedTensor.tmul (oneBimod S Aₚ A₀) (show ParabolicInput Q Λ θ 0 N from n)), ?_⟩
    rw [emptyRedStandard_smul, emptyRedStandard_mk_one]
    exact (Ind.smul_tmul _ _ _).trans (congrArg (fun w => Ind.tmul w n) (Subtype.ext z.2))
  · obtain ⟨a, rfl⟩ := hs
    obtain ⟨b, rfl⟩ := ht
    exact ⟨a + b, map_add _ _ _⟩

/-- `N` as a module of the factor algebra again. -/
def emptyOut (n : N₁) : ParabolicInput Q Λ θ 0 N := n

omit [Module k N] [IsScalarTower k (parabolicFactorAlgebra Q Λ θ 0) N] in
theorem emptyOut_add (n n' : N₁) :
    emptyOut Q Λ θ N (n + n') = emptyOut Q Λ θ N n + emptyOut Q Λ θ N n' := rfl

/-- The generator `1 ⊗ n` of `S(N)`. -/
def emptyStdGen (n : N₁) : ParabolicStandardT Q Λ θ 0 N hQ :=
  emptyStdMk Q Λ θ N hQ (BalancedTensor.tmul (oneBimod S Aₚ A₀) (emptyOut Q Λ θ N n))

omit [IsScalarTower k (parabolicFactorAlgebra Q Λ θ 0) N] in
theorem emptyStdGen_add (n n' : N₁) :
    emptyStdGen Q Λ θ N hQ (n + n') = emptyStdGen Q Λ θ N hQ n + emptyStdGen Q Λ θ N hQ n' := by
  rw [emptyStdGen, emptyStdGen, emptyStdGen, emptyOut_add, BalancedTensor.tmul_add]
  exact map_add (Submodule.mkQ _) _ _

/-- Adding the last red strand to `a ∈ T^{λ'}` acts on the generator through `a`. -/
theorem emptyStdGen_smul (a : L₀) (n : N₁) :
    emptyRedHom Q Λ θ a • emptyStdGen Q Λ θ N hQ n = emptyStdGen Q Λ θ N hQ (a • n) := by
  obtain ⟨t, ht⟩ := parabolicInputMap_surjective Q Λ θ 0 ((emptyFactorToOld Q Λ θ).symm a)
  have ha : a = emptyFactorToOld Q Λ θ (parabolicInputMap Q Λ θ 0 t) := by
    rw [ht, AlgEquiv.apply_symm_apply]
  subst ha
  have h1 : emptyFactorToOld Q Λ θ (parabolicInputMap Q Λ θ 0 t) • n =
      emptyIn Q Λ θ N (t • emptyOut Q Λ θ N n) :=
    (emptyIn_smul Q Λ θ N t (emptyOut Q Λ θ N n)).symm
  rw [h1, ← emptyG_apply, ← emptyF_eq_emptyG]
  change emptyAffine Q Λ θ (concat S Aₚ A₀ t) • _ = _
  rw [emptyStdGen, emptyStdMk_smul, BalancedTensor.smul_tmul', concat_smul_oneBimod,
    BalancedTensor.op_smul_tmul]
  rfl

/-- **The inverse map `Ind N → S(N)`**, `z ⊗ n ↦ z · (1 ⊗ n)`. -/
def emptyRedInv : J →ₗ[T₀] ParabolicStandardT Q Λ θ 0 N hQ :=
  Ind.lift (fun z n => z.1 • emptyStdGen Q Λ θ N hQ n)
    (fun z z' n => by rw [Submodule.coe_add, add_smul])
    (fun z n n' => by rw [emptyStdGen_add, smul_add])
    (fun z a n => by
      change (z.1 * emptyRedHom Q Λ θ a) • _ = _
      rw [mul_smul, emptyStdGen_smul])
    (fun b z n => by
      change (b * z.1) • _ = _
      rw [mul_smul])

theorem emptyRedInv_tmul (z : InductionAlong.Corner (emptyRedHom Q Λ θ)) (n : N₁) :
    emptyRedInv Q Λ θ N hQ (Ind.tmul z n) = z.1 • emptyStdGen Q Λ θ N hQ n := rfl

theorem emptyRedStandard_emptyRedInv (y : J) :
    emptyRedStandardT Q Λ θ N hQ (emptyRedInv Q Λ θ N hQ y) = y := by
  refine Ind.induction_on (motive := fun y : J =>
    emptyRedStandardT Q Λ θ N hQ (emptyRedInv Q Λ θ N hQ y) = y) y
    (by erw [map_zero]; rfl) (fun z n => ?_) (fun s t hs ht => by
      erw [map_add, map_add, hs, ht]; rfl)
  rw [emptyRedInv_tmul, map_smul]
  change z.1 • emptyRedStandard Q Λ θ N hQ (emptyStdMk Q Λ θ N hQ
    (BalancedTensor.tmul (oneBimod S Aₚ A₀) (emptyOut Q Λ θ N n))) = _
  rw [emptyRedStandard_mk_one]
  exact (Ind.smul_tmul _ _ _).trans (congrArg (fun w => Ind.tmul w n) (Subtype.ext z.2))

omit [IsScalarTower k (parabolicFactorAlgebra Q Λ θ 0) N] in
theorem emptyStdMk_zero : emptyStdMk Q Λ θ N hQ 0 = 0 := map_zero (Submodule.mkQ _)

omit [IsScalarTower k (parabolicFactorAlgebra Q Λ θ 0) N] in
theorem emptyStdMk_add (x y : ParabolicShuffle Q Λ θ 0 N) :
    emptyStdMk Q Λ θ N hQ (x + y) = emptyStdMk Q Λ θ N hQ x + emptyStdMk Q Λ θ N hQ y :=
  map_add (Submodule.mkQ _) x y

theorem emptyRedInv_emptyRedStandard (m : ParabolicStandardT Q Λ θ 0 N hQ) :
    emptyRedInv Q Λ θ N hQ (emptyRedStandardT Q Λ θ N hQ m) = m := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (excludedSpace
    (parabolicShuffleAction Q Λ θ 0 N) (parabolicOrderedLoadings (ℓ := ℓ) θ 0)) m
  change emptyRedInv Q Λ θ N hQ (emptyRedStandard Q Λ θ N hQ (emptyStdMk Q Λ θ N hQ x)) =
    emptyStdMk Q Λ θ N hQ x
  induction x using BalancedTensor.induction_on with
  | zero => rw [emptyStdMk_zero, map_zero, map_zero]
  | tmul r y =>
    rw [emptyRedStandard_mk, emptyStdShuffle_tmul, map_smul, emptyRedGen_apply]
    change emptyAffine Q Λ θ r.1 • ((unitGen (emptyRedHom Q Λ θ)).1 •
      emptyStdGen Q Λ θ N hQ (emptyIn Q Λ θ N y)) = _
    rw [unitGen, emptyStdGen_smul, one_smul, emptyStdGen, emptyStdMk_smul,
      BalancedTensor.smul_tmul']
    congr 2
    exact Subtype.ext r.2
  | add x y hx hy =>
    rw [emptyStdMk_add, map_add, map_add, hx, hy]

/-- **`S(N) ≅ Ind N`**: for an empty last block, standardization is the induction of `N`
along `T^{λ'} → T^λ`, adding the last red strand (Webster, arXiv:1309.3796v3, proof of
Prop 5.5, `β = ∅`). -/
def emptyRedStandardEquiv : ParabolicStandardT Q Λ θ 0 N hQ ≃ₗ[T₀] J :=
  LinearEquiv.ofLinearMap (emptyRedStandardT Q Λ θ N hQ) (emptyRedInv Q Λ θ N hQ)
    (LinearMap.ext (emptyRedStandard_emptyRedInv Q Λ θ N hQ))
    (LinearMap.ext (emptyRedInv_emptyRedStandard Q Λ θ N hQ))

theorem emptyRedStandard_injective : Function.Injective (emptyRedStandard Q Λ θ N hQ) :=
  (emptyRedStandardEquiv Q Λ θ N hQ).injective

end Induced

end Categorification.Stendhal

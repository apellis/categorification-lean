/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.SingleBlackLattice
import Mathlib.LinearAlgebra.PiTensorProduct.DirectSum
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The first lowering weight of the integral tensor product

Webster, arXiv:1309.3796v2, §1.2 and §4.7, especially Theorem 4.38.
For a finite tuple of dominant weights, the first lowering component of
the integral tensor product is spanned by pure tensors with one lowered
factor. These give coordinates for the prefix-lowering vectors defined
before Lemma 4.36.
-/

noncomputable section

namespace Categorification.Stendhal.FirstWeight

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop
open LusztigF DirectSum PiTensorProduct
open scoped DirectSum TensorProduct

local notation "𝕍" => (RatFunc.X : RatFunc ℚ)
local notation "𝕂" => RatFunc ℚ
local notation "LP" => LaurentPolynomial ℤ
local notation "hvt" => transcendental_ratFunc_X
local instance : NeZero 𝕍 := ⟨RatFunc.X_ne_zero⟩

variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y]
    {D : LusztigCartanDatum I} {R : D.RootDatum Y} {ℓ : ℕ}
    (weights : Fin ℓ → Dom R)

local notation "V" => fun j : Fin ℓ => IrreducibleModule R 𝕍 (Subtype.val (weights j))

/-- The rational tensor product of the irreducible highest-weight modules. -/
abbrev TensorSpace := ⨂[𝕂] j, V j

instance tensorLaurentModule : Module LP (TensorSpace weights) :=
  Module.compHom _ integralLaurentEval

omit [Finite I] in
theorem tensor_laurent_smul (a : LP) (x : TensorSpace weights) :
    a • x = integralLaurentEval a • x := rfl

/-- The image of the tensor product of the integral highest-weight lattices in
the rational tensor product. -/
def integralTensor : Submodule LP (TensorSpace weights) :=
  Submodule.span LP {x | ∃ z : ∀ j, V j,
    (∀ j, z j ∈ hwIntegral (weights j)) ∧ x = PiTensorProduct.tprod 𝕂 z}

local notation "W" => Y →+ ℤ
local notation "WS" => fun j : Fin ℓ => weightSpace R 𝕍 (V j)

private def factorSplit (hR : R.IsXRegular) (j : Fin ℓ) :
    V j ≃ₗ[𝕂] ⨁ μ : W, WS j μ := by
  classical
  exact (LinearEquiv.ofBijective (DirectSum.coeLinearMap (WS j))
    (isInternal_weightSpace hvn_ratFunc (isInt hvt hR (weights j)))).symm

open Classical in
omit [Finite I] in
private theorem factorSplit_apply (hR : R.IsXRegular) (j : Fin ℓ)
    {μ : W} {x : V j} (hx : x ∈ WS j μ) :
    factorSplit weights hR j x = DirectSum.lof 𝕂 _ _ μ ⟨x, hx⟩ := by
  apply (factorSplit weights hR j).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  exact (DirectSum.coeLinearMap_of (WS j) μ ⟨x, hx⟩).symm

private def splitWeights (hR : R.IsXRegular) :
    TensorSpace weights ≃ₗ[𝕂] ⨁ μ : (Fin ℓ → W), ⨂[𝕂] j, WS j (μ j) :=
  (PiTensorProduct.congr (factorSplit weights hR)).trans PiTensorProduct.ofDirectSumEquiv

open Classical in
omit [Finite I] in
private theorem splitWeights_tprod (hR : R.IsXRegular) (μ : Fin ℓ → W)
    (x : ∀ j, V j) (hx : ∀ j, x j ∈ WS j (μ j)) :
    splitWeights weights hR (PiTensorProduct.tprod 𝕂 x) =
      DirectSum.lof 𝕂 _ _ μ (PiTensorProduct.tprod 𝕂 (fun j => ⟨x j, hx j⟩)) := by
  classical
  rw [splitWeights, LinearEquiv.trans_apply, PiTensorProduct.congr_tprod]
  simp_rw [factorSplit_apply weights hR _ (hx _)]
  rw [PiTensorProduct.ofDirectSumEquiv_tprod_lof]

/-- Projection onto the total weight `μ` in the coproduct weight decomposition. -/
def tensorWeightProj (hR : R.IsXRegular) (μ : W) : Module.End 𝕂 (TensorSpace weights) := by
  classical
  let e := splitWeights weights hR
  exact e.symm.toLinearMap ∘ₗ DFinsupp.filterLinearMap 𝕂
    (fun wt : Fin ℓ → W => ⨂[𝕂] j, WS j (wt j)) (fun wt => ∑ j, wt j = μ) ∘ₗ e.toLinearMap

open Classical in
omit [Finite I] in
theorem tensorWeightProj_tprod (hR : R.IsXRegular) (μ : W) (wt : Fin ℓ → W)
    (x : ∀ j, V j) (hx : ∀ j, x j ∈ WS j (wt j)) :
    tensorWeightProj weights hR μ (PiTensorProduct.tprod 𝕂 x) =
      if ∑ j, wt j = μ then PiTensorProduct.tprod 𝕂 x else 0 := by
  classical
  simp only [tensorWeightProj, LinearMap.comp_apply, LinearEquiv.coe_coe,
    splitWeights_tprod weights hR wt x hx]
  change (splitWeights weights hR).symm ((DFinsupp.single wt
    (PiTensorProduct.tprod 𝕂 (fun j => ⟨x j, hx j⟩))).filter (fun wt => ∑ j, wt j = μ)) = _
  by_cases h : ∑ j, wt j = μ
  · rw [DFinsupp.filter_single_pos (p := fun z : Fin ℓ → W => ∑ r, z r = μ) wt _ h, ite_eq_left h,
      ← show splitWeights weights hR (PiTensorProduct.tprod 𝕂 x) = DFinsupp.single wt _ from
        splitWeights_tprod weights hR wt x hx, LinearEquiv.symm_apply_apply]
  · rw [DFinsupp.filter_single_neg (p := fun z : Fin ℓ → W => ∑ r, z r = μ) wt _ h, ite_eq_right h, map_zero]

/-- The group-like action of `Kₐ` on the tensor product, as in Webster §1.2. -/
def tensorTorus (a : Y) : Module.End 𝕂 (TensorSpace weights) :=
  PiTensorProduct.map (fun j => DistribSMul.toLinearMap 𝕂 (V j) (K R 𝕍 a))

omit [Finite I] in
private theorem tensorTorus_tprod (a : Y) (wt : Fin ℓ → W) (x : ∀ j, V j)
    (hx : ∀ j, x j ∈ WS j (wt j)) :
    tensorTorus weights a (PiTensorProduct.tprod 𝕂 x) = 𝕍 ^ ((∑ j, wt j) a) •
      PiTensorProduct.tprod 𝕂 x := by
  rw [tensorTorus, PiTensorProduct.map_tprod]
  have he (j : Fin ℓ) : K R 𝕍 a • x j = 𝕍 ^ (wt j) a • x j := hx j a
  simp_rw [DistribSMul.toLinearMap_apply, he]
  rw [MultilinearMap.map_smul_univ]
  congr 1
  rw [AddMonoidHom.finsetSum_apply]
  generalize (Finset.univ : Finset (Fin ℓ)) = s
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih =>
    rw [Finset.prod_insert hb, Finset.sum_insert hb, ih, zpow_add₀ RatFunc.X_ne_zero]

omit [Finite I] in
private theorem splitWeights_tensorTorus_apply (hR : R.IsXRegular) (a : Y)
    (x : TensorSpace weights) (wt : Fin ℓ → W) :
    splitWeights weights hR (tensorTorus weights a x) wt =
      𝕍 ^ ((∑ j, wt j) a) • splitWeights weights hR x wt := by
  classical
  obtain ⟨y, rfl⟩ := (splitWeights weights hR).symm.surjective x
  simp only [LinearEquiv.apply_symm_apply]
  induction y using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simp [map_add, smul_add, hx, hy]
  | of w y =>
    induction y using PiTensorProduct.induction_on with
    | add x y hx hy => simp [map_add, smul_add, hx, hy]
    | smul_tprod c u =>
      have hw : splitWeights weights hR (PiTensorProduct.tprod 𝕂 (fun j => (u j : V j))) =
          DirectSum.of _ w (PiTensorProduct.tprod 𝕂 u) :=
        splitWeights_tprod weights hR w _ (fun j => (u j).2)
      rw [show DirectSum.of (fun w : Fin ℓ → W => ⨂[𝕂] j, WS j (w j)) w
          (c • PiTensorProduct.tprod 𝕂 u) = c • DirectSum.of _ w (PiTensorProduct.tprod 𝕂 u)
        from (DirectSum.lof 𝕂 _ _ w).map_smul _ _]
      rw [← hw, ← map_smul, LinearEquiv.symm_apply_apply, map_smul, tensorTorus_tprod weights a w _
        (fun j => (u j).2)]
      simp only [map_smul, hw]
      let z := (DirectSum.of (fun w : Fin ℓ → W => ⨂[𝕂] j, WS j (w j)) w
        (PiTensorProduct.tprod 𝕂 u)) wt
      change c • (𝕍 ^ ((∑ j, w j) a) • z) = 𝕍 ^ ((∑ j, wt j) a) • (c • z)
      by_cases h : wt = w
      · subst wt
        exact smul_comm c (𝕍 ^ ((∑ j, w j) a)) z
      · have hz : z = 0 := DFinsupp.single_eq_of_ne h
        simp [hz]

omit [Finite I] in
/-- The projection's fixed vectors are precisely the weight vectors for the
group-like toral action of Webster §1.2. -/
theorem tensorWeightProj_eq_self_iff (hR : R.IsXRegular) (μ : W) (x : TensorSpace weights) :
    tensorWeightProj weights hR μ x = x ↔ ∀ a, tensorTorus weights a x = 𝕍 ^ (μ a) • x := by
  classical
  let e := splitWeights weights hR
  have hp : e (tensorWeightProj weights hR μ x) =
      (e x).filter (fun wt => ∑ j, wt j = μ) := e.apply_symm_apply _
  constructor
  · intro h a
    apply e.injective
    apply DFinsupp.ext
    intro wt
    rw [splitWeights_tensorTorus_apply weights hR a, map_smul, DFinsupp.smul_apply]
    by_cases ht : ∑ j, wt j = μ
    · rw [ht]
    · have hz : e x wt = 0 := by
        have he := congrArg (fun u => u wt) (hp.symm.trans (congrArg e h))
        rwa [DFinsupp.filter_apply_neg (p := fun w : Fin ℓ → W => ∑ j, w j = μ) _ ht, eq_comm] at he
      change 𝕍 ^ ((∑ j, wt j) a) • e x wt = 𝕍 ^ (μ a) • e x wt
      simp [hz]
  · intro h
    apply e.injective
    rw [hp]
    apply DFinsupp.ext
    intro wt
    by_cases ht : ∑ j, wt j = μ
    · exact DFinsupp.filter_apply_pos (p := fun w : Fin ℓ → W => ∑ j, w j = μ) _ ht
    · rw [DFinsupp.filter_apply_neg (p := fun w : Fin ℓ → W => ∑ j, w j = μ) _ ht]
      obtain ⟨a, ha⟩ := DFunLike.ne_iff.mp ht
      have he := congrArg (fun z => e z wt) (h a)
      change splitWeights weights hR (tensorTorus weights a x) wt =
        (e (𝕍 ^ (μ a) • x)) wt at he
      rw [splitWeights_tensorTorus_apply weights hR a, map_smul, DFinsupp.smul_apply] at he
      change 𝕍 ^ ((∑ j, wt j) a) • e x wt = 𝕍 ^ (μ a) • e x wt at he
      by_contra hz
      exact ha (zpow_injective_of_not_root RatFunc.X_ne_zero hvn_ratFunc
        (smul_left_injective 𝕂 (Ne.symm hz) he))

variable (i : I)

private def highestVector (j : Fin ℓ) : V j :=
  IrreducibleModule.hwv R 𝕍 (weights j).1

private def loweredVector (j : Fin ℓ) : V j :=
  F R 𝕍 i • highestVector weights j

private def loweredFactors (j : Fin ℓ) : ∀ r, V r :=
  Function.update (highestVector weights) j (loweredVector weights i j)

private def loweredWeights (j : Fin ℓ) : Fin ℓ → W :=
  Function.update (fun r => (weights r).1) j ((weights j).1 - R.root i)

/-- The pure tensor with the `j`-th factor lowered once. -/
def loweredPure (j : Fin ℓ) : TensorSpace weights :=
  PiTensorProduct.tprod 𝕂 (loweredFactors weights i j)

omit [Finite I] in
private theorem loweredFactors_weight (j r : Fin ℓ) :
    loweredFactors weights i j r ∈ WS r (loweredWeights weights i j r) := by
  by_cases h : r = j
  · subst r
    simp only [loweredFactors, loweredWeights, Function.update_self, loweredVector, highestVector]
    exact F_smul_mem_weightSpace IrreducibleModule.hwv_mem_weightSpace i
  · simp only [loweredFactors, loweredWeights, Function.update_of_ne h, highestVector]
    exact IrreducibleModule.hwv_mem_weightSpace

omit [Finite I] [DecidableEq I] in
private theorem sum_loweredWeights (j : Fin ℓ) :
    ∑ r, loweredWeights weights i j r = (∑ r, (weights r).1) - R.root i := by
  rw [loweredWeights, Finset.sum_update_of_mem (Finset.mem_univ j)]
  have e := Finset.sum_erase_add Finset.univ (fun r => (weights r).1) (Finset.mem_univ j)
  rw [← e, Finset.sdiff_singleton_eq_erase]
  abel

/-- The component of the integral tensor lattice in weight
`(∑ⱼ λⱼ) − αᵢ`. -/
def tensorFirstLattice (hR : R.IsXRegular) : Submodule LP (TensorSpace weights) where
  carrier := {x | x ∈ integralTensor weights ∧
    tensorWeightProj weights hR ((∑ r, (weights r).1) - R.root i) x = x}
  add_mem' hx hy := ⟨add_mem hx.1 hy.1, by rw [map_add, hx.2, hy.2]⟩
  zero_mem' := ⟨zero_mem _, map_zero _⟩
  smul_mem' a _ hx := ⟨Submodule.smul_mem _ _ hx.1, by
    rw [tensor_laurent_smul, map_smul, hx.2]⟩

/-- Membership in the integral tensor product and the toral eigenspace of
`(∑ⱼ λⱼ) − αᵢ` characterizes the first lowering lattice. -/
theorem mem_tensorFirstLattice (hR : R.IsXRegular) (x : TensorSpace weights) :
    x ∈ tensorFirstLattice weights i hR ↔ x ∈ integralTensor weights ∧
      ∀ a, tensorTorus weights a x = 𝕍 ^ (((∑ r, (weights r).1) - R.root i) a) • x :=
  and_congr_right (fun _ => tensorWeightProj_eq_self_iff weights hR _ x)

theorem loweredPure_mem (hR : R.IsXRegular) (j : Fin ℓ) :
    loweredPure weights i j ∈ tensorFirstLattice weights i hR := by
  refine ⟨Submodule.subset_span ⟨loweredFactors weights i j, ?_, rfl⟩, ?_⟩
  · intro r
    by_cases h : r = j
    · subst r
      simp only [loweredFactors, Function.update_self, loweredVector, highestVector]
      exact (show loweredVector weights i j ∈ SingleBlack.firstLoweringLattice (weights j) i from
        SingleBlack.lower_mem_lattice (weights j) i).1
    · simp only [loweredFactors, Function.update_of_ne h, highestVector]
      exact hwv_mem_hwIntegral (weights r)
  · rw [loweredPure, tensorWeightProj_tprod weights hR _ _ _ (loweredFactors_weight weights i j),
      sum_loweredWeights, ite_eq_left rfl]

omit [Finite I] in
private theorem map_tprod_mem_span_factors (P : Module.End 𝕂 (TensorSpace weights))
    (A : ∀ r, Set (V r)) (L : Submodule LP (TensorSpace weights))
    (hA : ∀ x : ∀ r, V r, (∀ r, x r ∈ A r) → P (PiTensorProduct.tprod 𝕂 x) ∈ L)
    (x : ∀ r, V r) (hx : ∀ r, x r ∈ Submodule.span LP (A r)) :
    P (PiTensorProduct.tprod 𝕂 x) ∈ L := by
  classical
  have aux (s : Finset (Fin ℓ)) (x : ∀ r, V r)
      (hs : ∀ r ∈ s, x r ∈ Submodule.span LP (A r))
      (hr : ∀ r ∉ s, x r ∈ A r) : P (PiTensorProduct.tprod 𝕂 x) ∈ L := by
    induction s using Finset.induction_on generalizing x with
    | empty => exact hA x (fun r => hr r (by simp))
    | insert j s hj ih =>
      have hJ (z : V j) (hz : z ∈ Submodule.span LP (A j)) :
          P (PiTensorProduct.tprod 𝕂 (Function.update x j z)) ∈ L := by
        induction hz using Submodule.span_induction with
        | mem z hz =>
          refine ih (Function.update x j z) (fun r hrs => ?_) (fun r hrs => ?_)
          · rw [Function.update_of_ne (fun h : r = j => hj (h ▸ hrs))]
            exact hs r (Finset.mem_insert_of_mem hrs)
          · by_cases h : r = j
            · subst r
              simpa using hz
            · rw [Function.update_of_ne h]
              exact hr r (by simp [h, hrs])
        | zero => rw [MultilinearMap.map_update_zero, map_zero]; exact zero_mem _
        | add _ _ _ _ h₁ h₂ =>
          rw [MultilinearMap.map_update_add, map_add]
          exact add_mem h₁ h₂
        | smul a z _ hz =>
          rw [hw_laurent_smul_eq, MultilinearMap.map_update_smul, map_smul, ← tensor_laurent_smul]
          exact Submodule.smul_mem _ a hz
      simpa only [Function.update_eq_self] using hJ (x j) (hs j (Finset.mem_insert_self _ _))
  exact aux Finset.univ x (fun r _ => hx r) (fun r hr => (hr (Finset.mem_univ r)).elim)

omit [Finite I] in
private theorem depth_sum_single (depth : Fin ℓ → I →₀ ℕ)
    (h : ∑ r, depth r = Finsupp.single i 1) :
    ∃ j, depth j = Finsupp.single i 1 ∧ ∀ r, r ≠ j → depth r = 0 := by
  have hc (u : I) : (∑ r, depth r u) = Finsupp.single i 1 u := by
    simpa only [Finsupp.finsetSum_apply] using congrArg (fun x : I →₀ ℕ => x u) h
  have hci : (∑ r, depth r i) = 1 := by simpa using hc i
  have hcine : (∑ r, depth r i) ≠ 0 := by omega
  obtain ⟨j, hj, hji⟩ := Finset.exists_ne_zero_of_sum_ne_zero hcine
  have hle (r : Fin ℓ) (u : I) : depth r u ≤ Finsupp.single i 1 u :=
    (Finset.single_le_sum (fun a _ => Nat.zero_le (depth a u)) (Finset.mem_univ r)).trans_eq (hc u)
  have hji' : depth j i = 1 := by
    have hb := hle j i
    rw [Finsupp.single_eq_same] at hb
    omega
  refine ⟨j, ?_, ?_⟩
  · ext u
    by_cases hu : u = i
    · subst u; simpa using hji'
    · have := hle j u
      rw [Finsupp.single_eq_of_ne hu] at this ⊢
      omega
  · intro r hr
    ext u
    by_cases hu : u = i
    · subst u
      have hsplit := Finset.sum_erase_add Finset.univ (fun a => depth a i) hj
      have hle' := Finset.single_le_sum (fun a _ => Nat.zero_le (depth a i))
        (Finset.mem_erase.2 ⟨hr, Finset.mem_univ r⟩)
      simp only [Finsupp.zero_apply]
      omega
    · have := hle r u
      rw [Finsupp.single_eq_of_ne hu] at this
      simp only [Finsupp.zero_apply]
      omega

omit [Finite I] [DecidableEq I] in
private theorem rootSum_finsetSum (s : Finset (Fin ℓ)) (depth : Fin ℓ → I →₀ ℕ) :
    R.rootSum (∑ r ∈ s, depth r) = ∑ r ∈ s, R.rootSum (depth r) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert r s h ih => rw [Finset.sum_insert h, Finset.sum_insert h, R.rootSum_add, ih]

private theorem tensorWeightProj_mem_span_loweredPure (hR : R.IsXRegular)
    (x : ∀ r, V r)
    (hx : ∀ r, x r ∈ hwIntegral (weights r)) :
    tensorWeightProj weights hR ((∑ r, (weights r).1) - R.root i)
        (PiTensorProduct.tprod 𝕂 x) ∈ Submodule.span LP (Set.range (loweredPure weights i)) := by
  classical
  refine map_tprod_mem_span_factors weights _ (fun r => {y | ∃ d : I →₀ ℕ,
    y ∈ wsp (weights r) d ∧ y ∈ hwIntegral (weights r)}) _ ?_ x
    (fun r => SingleBlack.hwIntegral_le_span_homogeneous (weights r) hR (hx r))
  intro y hy
  choose depth hdepth hint using hy
  rw [tensorWeightProj_tprod weights hR _ (fun r => (weights r).1 - R.rootSum (depth r)) _ hdepth]
  split_ifs with hwt
  · rw [Finset.sum_sub_distrib, ← rootSum_finsetSum (R := R) Finset.univ] at hwt
    have hdep : ∑ r, depth r = Finsupp.single i 1 :=
      LusztigCartanDatum.RootDatum.rootSum_injective hR (by
        simpa only [R.rootSum_single, one_smul] using sub_right_injective hwt)
    obtain ⟨j, hj, hr⟩ := depth_sum_single (i := i) depth hdep
    have hcoeff (r : Fin ℓ) : ∃ a : LP, y r = a • loweredFactors weights i j r := by
      by_cases h : r = j
      · subst r
        have hw : y j ∈ SingleBlack.firstLoweringLattice (weights j) i := by
          exact ⟨hint j, by simpa only [wsp, hj, R.rootSum_single, one_smul] using hdepth j⟩
        have hs := SingleBlack.lattice_le_span (weights j) i hR hw
        rw [Submodule.mem_span_singleton] at hs
        obtain ⟨a, ha⟩ := hs
        exact ⟨a, by simpa only [loweredFactors, Function.update_self, loweredVector,
          highestVector] using ha.symm⟩
      · have hw : y r ∈ wsp (weights r) 0 := (hr r h) ▸ hdepth r
        have hs := SingleBlack.hwIntegral_weight_zero_mem_span (weights r) hR (hint r) hw
        rw [Submodule.mem_span_singleton] at hs
        obtain ⟨a, ha⟩ := hs
        exact ⟨a, by simpa only [loweredFactors, Function.update_of_ne h, highestVector] using ha.symm⟩
    choose a ha using hcoeff
    have heq : y = fun r => integralLaurentEval (a r) • loweredFactors weights i j r := by
      funext r
      rw [ha r, hw_laurent_smul_eq]
    rw [heq, MultilinearMap.map_smul_univ, ← map_prod, ← tensor_laurent_smul, ← loweredPure]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · exact zero_mem _

/-- The one-lowered pure tensors span precisely the first total weight of the
integral tensor product in Webster's Theorem 4.38. -/
theorem span_loweredPure_eq (hR : R.IsXRegular) :
    Submodule.span LP (Set.range (loweredPure weights i)) = tensorFirstLattice weights i hR := by
  refine le_antisymm (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨j, rfl⟩
    exact loweredPure_mem weights i hR j
  · rintro x ⟨hx, hproj⟩
    rw [← hproj]
    clear hproj
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      exact tensorWeightProj_mem_span_loweredPure weights i hR y hy
    | zero => simp
    | add _ _ _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx =>
      rw [tensor_laurent_smul, map_smul, ← tensor_laurent_smul]
      exact Submodule.smul_mem _ a hx

omit [Finite I] in
omit [DecidableEq I] in
private theorem loweredWeights_injective : Function.Injective (loweredWeights weights i) := by
  intro r s h
  by_contra hne
  have he := congrFun h r
  simp only [loweredWeights, Function.update_self, Function.update_of_ne hne] at he
  have hz : R.root i = 0 := by
    have hdiff := congrArg (fun u : W => (weights r).1 - u) he
    simpa using hdiff
  have hz' := congrArg (fun u : W => u (R.coroot i)) hz
  simp [R.root_coroot, D.cartanMatrix_self] at hz'

omit [Finite I] in
private theorem loweredFactors_ne_zero (hR : R.IsXRegular)
    (hpos : ∀ r, 0 < (weights r).1 (R.coroot i)) (j r : Fin ℓ) :
    loweredFactors weights i j r ≠ 0 := by
  by_cases hr : r = j
  · subst r
    simpa only [loweredFactors, Function.update_self, loweredVector, highestVector] using
      SingleBlack.lower_ne_zero (weights j) i hR (hpos j)
  · simpa only [loweredFactors, Function.update_of_ne hr, highestVector] using
      hwv_ne_zero hR hvn_ratFunc (weights r).1

private theorem tprod_ne_zero {J : Type*} [Fintype J] {M : J → Type*}
    [∀ j, AddCommGroup (M j)] [∀ j, Module 𝕂 (M j)] (x : ∀ j, M j)
    (hx : ∀ j, x j ≠ 0) : PiTensorProduct.tprod 𝕂 x ≠ 0 := by
  choose f hf using fun j => Module.Projective.exists_dual_eq_one 𝕂 (hx j)
  let Ψ := PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra 𝕂 J 𝕂).compLinearMap f)
  intro h
  have he := congrArg Ψ h
  simp [Ψ, hf] at he

omit [Finite I] in
/-- When each multiplicity at the lowering colour is positive, the corresponding
one-lowered pure tensors are linearly independent over the integral Laurent ring. -/
theorem loweredPure_linearIndependent (hR : R.IsXRegular)
    (hpos : ∀ r, 0 < (weights r).1 (R.coroot i)) :
    LinearIndependent LP (loweredPure weights i) := by
  classical
  refine Fintype.linearIndependent_iff.2 fun a ha j => ?_
  let c := (DirectSum.component 𝕂 _ _ (loweredWeights weights i j)).comp
    (splitWeights weights hR).toLinearMap
  have h := congrArg c ha
  simp only [map_sum, tensor_laurent_smul, map_smul, map_zero] at h
  rw [Finset.sum_eq_single j] at h
  · have hc : c (loweredPure weights i j) =
        PiTensorProduct.tprod 𝕂 (fun r => ⟨loweredFactors weights i j r, loweredFactors_weight weights i j r⟩) := by
      rw [show c (loweredPure weights i j) = DirectSum.component 𝕂 _ _ (loweredWeights weights i j)
          (splitWeights weights hR (loweredPure weights i j)) from rfl,
        loweredPure, splitWeights_tprod weights hR _ _ (loweredFactors_weight weights i j),
        DirectSum.component.lof_self]
    apply integralLaurentEval_injective
    rw [map_zero]
    refine (smul_eq_zero.mp h).resolve_right ?_
    rw [hc]
    apply tprod_ne_zero
    intro r hr
    exact loweredFactors_ne_zero weights i hR hpos j r
      (congrArg Subtype.val hr)
  · intro r _ hr
    have hc : c (loweredPure weights i r) = 0 := by
      rw [show c (loweredPure weights i r) = DirectSum.component 𝕂 _ _ (loweredWeights weights i j)
          (splitWeights weights hR (loweredPure weights i r)) from rfl,
        loweredPure, splitWeights_tprod weights hR _ _ (loweredFactors_weight weights i r),
        DirectSum.component.of, dite_eq_right (fun hh => hr (loweredWeights_injective weights i hh))]
    rw [hc, smul_zero]
  · simp

/-- The pure-tensor basis of the first lowering component, under positive
multiplicity at each factor. -/
def loweredPureBasis (hR : R.IsXRegular) (hpos : ∀ r, 0 < (weights r).1 (R.coroot i)) :
    Module.Basis (Fin ℓ) LP (tensorFirstLattice weights i hR) :=
  (Module.Basis.span (loweredPure_linearIndependent weights i hR hpos)).map
    (LinearEquiv.ofEq _ _ (span_loweredPure_eq weights i hR))

@[simp] theorem loweredPureBasis_apply (hR : R.IsXRegular)
    (hpos : ∀ r, 0 < (weights r).1 (R.coroot i)) (j : Fin ℓ) :
    (loweredPureBasis weights i hR hpos j : TensorSpace weights) = loweredPure weights i j := by
  simp [loweredPureBasis]

private def prefixExponent (r j s : Fin ℓ) : ℤ :=
  if j < s ∧ s ≤ r then -(D.d i : ℤ) * (weights s).1 (R.coroot i) else 0

/-- The Laurent coefficient of the pure tensor lowered at `j` in the prefix
ending at `r`. The factors strictly between `j` and the end of the prefix
carry the `K̃ᵢ⁻¹` from Webster's coproduct (5.10). -/
def prefixCoefficient (r j : Fin ℓ) : LP :=
  ∏ s, LaurentPolynomial.T (prefixExponent weights i r j s)

omit [Finite I] [DecidableEq I] in
private theorem prefixCoefficient_diag (r : Fin ℓ) : prefixCoefficient weights i r r = 1 := by
  have h (s : Fin ℓ) : ¬ (r < s ∧ s ≤ r) := fun ht => (not_lt_of_ge ht.2) ht.1
  simp [prefixCoefficient, prefixExponent, h]

private def prefixSummand (r j s : Fin ℓ) : Module.End 𝕂 (V s) :=
  if s = j then DistribSMul.toLinearMap 𝕂 (V s) (F R 𝕍 i)
  else if j < s ∧ s ≤ r then DistribSMul.toLinearMap 𝕂 (V s) (K R 𝕍 (-ktilde R i))
  else LinearMap.id

/-- The operator from Webster, arXiv:1309.3796v2, equation (5.10) applied on
the prefix ending at `r`, with identity operators on the remaining factors. -/
def prefixLowering (r : Fin ℓ) : Module.End 𝕂 (TensorSpace weights) :=
  ∑ j ∈ Finset.Iic r, PiTensorProduct.map (prefixSummand weights i r j)

/-- Webster's vector `pᵢ^κ` for the single black strand immediately after red
strand `r`, as defined before Lemma 4.36. -/
def pVector (r : Fin ℓ) : TensorSpace weights :=
  prefixLowering weights i r (PiTensorProduct.tprod 𝕂 (highestVector weights))

omit [Finite I] in
private theorem prefixSummand_highest (r j s : Fin ℓ) :
    prefixSummand weights i r j s (highestVector weights s) =
      𝕍 ^ prefixExponent weights i r j s • loweredFactors weights i j s := by
  by_cases h : s = j
  · subst s
    simp [prefixSummand, prefixExponent, loweredFactors, loweredVector]
  · by_cases h' : j < s ∧ s ≤ r
    · rw [prefixSummand, ite_eq_right h, ite_eq_left h', DistribSMul.toLinearMap_apply,
        prefixExponent, ite_eq_left h', loweredFactors, Function.update_of_ne h]
      change K R 𝕍 (-ktilde R i) • highestVector weights s =
        𝕍 ^ (-(D.d i : ℤ) * (weights s).1 (R.coroot i)) • highestVector weights s
      rw [K_neg_ktilde_smul_of_mem_weightSpace
        (show highestVector weights s ∈ WS s ((weights s).1) from IrreducibleModule.hwv_mem_weightSpace),
        ← zpow_natCast, ← zpow_mul, mul_neg]
      rw [neg_mul]
    · simp [prefixSummand, prefixExponent, h, h', loweredFactors]

omit [Finite I] in
/-- Expansion of Webster's `pᵢ^κ` in the pure tensors of the first weight. -/
theorem pVector_eq_sum (r : Fin ℓ) : pVector weights i r =
    ∑ j ∈ Finset.Iic r, prefixCoefficient weights i r j • loweredPure weights i j := by
  rw [pVector, prefixLowering, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [PiTensorProduct.map_tprod]
  simp_rw [prefixSummand_highest weights i r j]
  rw [MultilinearMap.map_smul_univ, ← loweredPure, tensor_laurent_smul,
    prefixCoefficient, map_prod]
  simp_rw [integralLaurentEval_T]

private def prefixMatrix : Matrix (Fin ℓ) (Fin ℓ) LP :=
  fun j r => if j ≤ r then prefixCoefficient weights i r j else 0

omit [Finite I] [DecidableEq I] in
private theorem prefixMatrix_det : (prefixMatrix weights i).det = 1 := by
  have htri : (prefixMatrix weights i).IsUpperTriangular := by
    intro j r h
    exact ite_eq_right (not_le_of_gt h)
  rw [Matrix.det_of_isUpperTriangular htri]
  simp [prefixMatrix, prefixCoefficient_diag]

private def prefixCoordinates : (Fin ℓ → LP) ≃ₗ[LP] (Fin ℓ → LP) := by
  let A := prefixMatrix weights i
  have hA : IsUnit A.det := by rw [prefixMatrix_det]; exact isUnit_one
  refine {
    toFun := A.mulVec
    invFun := A⁻¹.mulVec
    left_inv := ?_
    right_inv := ?_
    map_add' := Matrix.mulVec_add A
    map_smul' := Matrix.mulVec_smul A }
  · intro x
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hA, Matrix.one_mulVec]
  · intro x
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hA, Matrix.one_mulVec]

/-- The basis of the first integral tensor weight consisting of Webster's
`pᵢ^κ` for positive multiplicity in every factor. -/
def pVectorBasis (hR : R.IsXRegular) (hpos : ∀ r, 0 < (weights r).1 (R.coroot i)) :
    Module.Basis (Fin ℓ) LP (tensorFirstLattice weights i hR) :=
  let b := loweredPureBasis weights i hR hpos
  b.map ((b.equivFun.trans (prefixCoordinates weights i)).trans b.equivFun.symm)

@[simp] theorem pVectorBasis_apply (hR : R.IsXRegular)
    (hpos : ∀ r, 0 < (weights r).1 (R.coroot i)) (r : Fin ℓ) :
    (pVectorBasis weights i hR hpos r : TensorSpace weights) = pVector weights i r := by
  let b := loweredPureBasis weights i hR hpos
  rw [pVectorBasis, Module.Basis.map_apply]
  change ((b.equivFun.symm ((prefixMatrix weights i).mulVec (b.equivFun (b r)))) :
    TensorSpace weights) = _
  have hb : b.equivFun (b r) = Pi.single r 1 := by
    funext j
    rw [Module.Basis.equivFun_self, Pi.single_apply]
    by_cases h : r = j
    · subst j; simp
    · simp [h, Ne.symm h]
  rw [hb, Matrix.mulVec_single_one, Module.Basis.equivFun_symm_apply]
  change (tensorFirstLattice weights i hR).subtype (∑ j, prefixMatrix weights i j r • b j) = _
  rw [map_sum]
  simp only [map_smul]
  change ∑ j, prefixMatrix weights i j r • (b j : TensorSpace weights) = _
  simp only [b, loweredPureBasis_apply]
  simp_rw [prefixMatrix, ite_smul, zero_smul]
  rw [← Finset.sum_filter, pVector_eq_sum]
  have he : Finset.univ.filter (fun j : Fin ℓ => j ≤ r) = Finset.Iic r := by
    ext j
    simp
  rw [he]

end Categorification.Stendhal.FirstWeight

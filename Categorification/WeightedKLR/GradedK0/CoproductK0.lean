/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.GradedK0.ResIndTwist
import Categorification.WeightedKLR.GradedK0.TensorK0
import Categorification.WeightedKLR.Mackey.CoproductK0

/-!
# The graded coproduct on `K₀ ⊗ K₀` of weighted KLR algebras

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, Theorem 2.19: the
graded Grothendieck groups of the weighted KLR algebras form a twisted bialgebra, with product
given by induction and coproduct by restriction. This is the graded form of
`Mackey/CoproductK0.lean`.

## Main results

* `Juxtapose.middleIndExtIndEquiv`: `(W_{a+c} ⊗ W_{b+d}) e' ⊗_{W'} ((P_a ⊠ P_b) ⊠ (Q_c ⊠ Q_d))
  ≅ Ind(P_a ⊠ Q_c) ⊠ Ind(P_b ⊠ Q_d)` for the graded inductions `W_{ν'+ν''} e_{ν';ν''} ⊗ -` of
  `GradedK0/Induction.lean`, over any commutative ring;
  `GradingDatum.middleIndGProjExtIndIso`: it is an isomorphism of graded modules, with no shift.
* `GradingDatum.middleIndK0_extTensor`: on graded `K₀`,
  `middleInd ((x_a ⊠ x_b) ⊠ (y_c ⊠ y_d)) = (x_a · y_c) ⊠ (x_b · y_d)`.
* `GradingDatum.coproductK0`: `Δ_{ν₁,ν₂} : K₀(W_{ν₁+ν₂}) → K₀(W_{ν₁}) ⊗_{ℤ[q,q⁻¹]} K₀(W_{ν₂})`,
  the restriction followed by the inverse of `GradingDatum.k0TensorEquiv`.
* `ShuffleLayout.twistedMulK0Graded`: `(x_a ⊗ x_b) ⊗ (y_c ⊗ y_d) ↦ (x_a · y_c) ⊗ (x_b · y_d)`,
  and `ShuffleLayout.k0TensorEquiv_twistedMulK0Graded` comparing it with
  `ResIndPiece.twistK0Graded`.
* `exists_coproductK0_indK0_eq_sum_graded`: **the graded Mackey formula**
  `Δ_{ν₁,ν₂}(x · y) = ∑ᵢ q^{sᵢ} T_{Lᵢ}(Δ_{a,b} x ⊗ Δ_{c,d} y)`, over a field.

## Route hypothesis

`coproductK0` and the Mackey formula assume `TensorK0Hyp` (see `GradedK0/TensorK0.lean`): the
identification `K₀(W_μ ⊗ W_{μ'}) ≅ K₀(W_μ) ⊗ K₀(W_{μ'})`, used without justification in the
proof of Webster's Theorem 2.19. It is not proved here for weighted KLR algebras.
-/

noncomputable section

namespace Categorification.WeightedKLR

open FullChamber GalleryAlgebra Juxtapose MulOpposite Categorification.Graded DirectSum
open scoped TensorProduct

universe u v w

variable {I : Type u} [DecidableEq I] {𝕜 : Type v} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜]

namespace Juxtapose

section Along

variable {k : Type*} [CommRing k] {P Q A B C Z : Type*} [AddCommGroup P] [Module k P]
  [AddCommGroup Q] [Module k Q] [Ring A] [Algebra k A] [Ring B] [Algebra k B]
  [Module A P] [IsScalarTower k A P] [Module B Q] [IsScalarTower k B Q] [Ring C]
  [AddCommGroup Z] [Module C Z]

/-- A map out of `P ⊠ Q` that is additive and intertwines the action of `A ⊗ B` with that of
`C` along an additive map `φ : A ⊗ B → C` on generators intertwines it everywhere. -/
theorem extTensor_smul_eq_along (φ : A ⊗[k] B →+ C) {F : ExtTensor k P Q → Z}
    (hadd : ∀ x y, F (x + y) = F x + F y) (h0 : F 0 = 0)
    (htmul : ∀ (a : A) (b : B) (p : P) (q : Q),
      F ((a ⊗ₜ[k] b) • ExtTensor.tmul p q) = φ (a ⊗ₜ[k] b) • F (ExtTensor.tmul p q))
    (t : A ⊗[k] B) (x : ExtTensor k P Q) : F (t • x) = φ t • F x := by
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    induction x using ExtTensor.induction_on with
    | zero => rw [smul_zero, h0, smul_zero]
    | tmul p q => exact htmul a b p q
    | add x y hx hy => rw [smul_add, hadd, hx, hy, hadd, smul_add]
  | add s t hs ht => rw [add_smul, hadd, hs, ht, map_add, add_smul]

end Along

section Generators

variable {k : Type*} [CommRing k] {A₁ R₁ A₂ R₂ Y : Type*} [Ring A₁] [Algebra k A₁] [Ring R₁]
  [Ring A₂] [Algebra k A₂] [Ring R₂]
  {M₁ U₁ M₂ U₂ : Type*} [AddCommGroup M₁] [Module k M₁] [Module A₁ M₁]
  [IsScalarTower k A₁ M₁] [Module R₁ᵐᵒᵖ M₁] [AddCommGroup U₁] [Module k U₁] [Module R₁ U₁]
  [AddCommGroup M₂] [Module k M₂] [Module A₂ M₂]
  [IsScalarTower k A₂ M₂] [Module R₂ᵐᵒᵖ M₂] [AddCommGroup U₂] [Module k U₂] [Module R₂ U₂]
  [AddCommGroup Y]

/-- An additive map `G` that undoes an additive map `F` on the generators `m ⊗ u` of a balanced
tensor product undoes it everywhere. -/
theorem balancedTensor_leftInverse (F : BalancedTensor k A₁ R₁ M₁ U₁ →+ Y)
    (G : Y →+ BalancedTensor k A₁ R₁ M₁ U₁)
    (h : ∀ m u, G (F (BalancedTensor.tmul m u)) = BalancedTensor.tmul m u)
    (x : BalancedTensor k A₁ R₁ M₁ U₁) : G (F x) = x := by
  induction x using BalancedTensor.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul m u => exact h m u
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- An additive map `G` that undoes an additive map `F` on the generators
`(m ⊗ u) ⊠ (m' ⊗ u')` of an external tensor product of balanced tensor products undoes it
everywhere. -/
theorem extBalancedTensor_leftInverse
    (F : ExtTensor k (BalancedTensor k A₁ R₁ M₁ U₁) (BalancedTensor k A₂ R₂ M₂ U₂) →+ Y)
    (G : Y →+ ExtTensor k (BalancedTensor k A₁ R₁ M₁ U₁) (BalancedTensor k A₂ R₂ M₂ U₂))
    (h : ∀ m u m' u', G (F (ExtTensor.tmul (BalancedTensor.tmul m u)
      (BalancedTensor.tmul m' u'))) =
        ExtTensor.tmul (BalancedTensor.tmul m u) (BalancedTensor.tmul m' u'))
    (y : ExtTensor k (BalancedTensor k A₁ R₁ M₁ U₁) (BalancedTensor k A₂ R₂ M₂ U₂)) :
    G (F y) = y := by
  induction y using ExtTensor.induction_on with
  | zero => rw [map_zero, map_zero]
  | add y y' hy hy' => rw [map_add, map_add, hy, hy']
  | tmul x x' =>
    induction x using BalancedTensor.induction_on with
    | zero => rw [ExtTensor.zero_tmul, map_zero, map_zero]
    | add x₁ x₂ h₁ h₂ => rw [ExtTensor.add_tmul, map_add, map_add, h₁, h₂]
    | tmul m u =>
      induction x' using BalancedTensor.induction_on with
      | zero => rw [ExtTensor.tmul_zero, map_zero, map_zero]
      | add x₁ x₂ h₁ h₂ => rw [ExtTensor.tmul_add, map_add, map_add, h₁, h₂]
      | tmul m' u' => exact h m u m' u'

/-- An additive map out of `(M₁ ⊗ U₁) ⊠ (M₂ ⊗ U₂)` intertwining the actions of `A₁ ⊗ A₂` on
the generators `(m ⊗ u) ⊠ (m' ⊗ u')` intertwines them everywhere. -/
theorem extBalancedTensor_smul_eq [Module (A₁ ⊗[k] A₂) Y]
    (F : ExtTensor k (BalancedTensor k A₁ R₁ M₁ U₁) (BalancedTensor k A₂ R₂ M₂ U₂) →+ Y)
    (h : ∀ (s : A₁) (s' : A₂) m u m' u',
      F (ExtTensor.tmul (BalancedTensor.tmul (s • m) u) (BalancedTensor.tmul (s' • m') u')) =
        (s ⊗ₜ[k] s') • F (ExtTensor.tmul (BalancedTensor.tmul m u) (BalancedTensor.tmul m' u')))
    (t : A₁ ⊗[k] A₂)
    (y : ExtTensor k (BalancedTensor k A₁ R₁ M₁ U₁) (BalancedTensor k A₂ R₂ M₂ U₂)) :
    F (t • y) = t • F y := by
  refine extTensor_smul_eq_along (AddMonoidHom.id _) (map_add F) (map_zero F) (fun s s' x x' => ?_)
    t y
  rw [ExtTensor.smul_tmul, AddMonoidHom.id_apply]
  induction x using BalancedTensor.induction_on with
  | zero => rw [smul_zero, ExtTensor.zero_tmul, ExtTensor.zero_tmul, map_zero, smul_zero]
  | add x₁ x₂ h₁ h₂ => rw [smul_add, ExtTensor.add_tmul, ExtTensor.add_tmul, map_add, map_add,
      h₁, h₂, smul_add]
  | tmul m u =>
    induction x' using BalancedTensor.induction_on with
    | zero => rw [smul_zero, ExtTensor.tmul_zero, ExtTensor.tmul_zero, map_zero, smul_zero]
    | add x₁ x₂ h₁ h₂ => rw [smul_add, ExtTensor.tmul_add, ExtTensor.tmul_add, map_add, map_add,
        h₁, h₂, smul_add]
    | tmul m' u' =>
      rw [BalancedTensor.smul_tmul', BalancedTensor.smul_tmul']
      exact h s s' m u m' u'

/-- The exchange of the middle factors `(M₁ ⊠ M₂) ⊠ (M₃ ⊠ M₄) ≅ (M₁ ⊠ M₃) ⊠ (M₂ ⊠ M₄)` is
degree-preserving for the tensor product gradings. -/
theorem middleComm_mem_grading {ι : Type*} [AddCommMonoid ι] {M₁ M₂ M₃ M₄ : Type*}
    [AddCommGroup M₁] [Module k M₁] [AddCommGroup M₂] [Module k M₂] [AddCommGroup M₃] [Module k M₃]
    [AddCommGroup M₄] [Module k M₄] {𝒰₁ : ι → Submodule k M₁} {𝒰₂ : ι → Submodule k M₂}
    {𝒰₃ : ι → Submodule k M₃} {𝒰₄ : ι → Submodule k M₄} {d : ι}
    {n : ExtTensor k (ExtTensor k M₁ M₂) (ExtTensor k M₃ M₄)}
    (hn : n ∈ ExtTensor.grading (ExtTensor.grading 𝒰₁ 𝒰₂) (ExtTensor.grading 𝒰₃ 𝒰₄) d) :
    ExtTensor.middleComm n ∈
      ExtTensor.grading (ExtTensor.grading 𝒰₁ 𝒰₃) (ExtTensor.grading 𝒰₂ 𝒰₄) d := by
  refine ExtTensor.grading_map_mem _ _ _ (ExtTensor.middleComm (k := k) (M₁ := M₁) (M₂ := M₂)
    (M₃ := M₃) (M₄ := M₄)).toLinearMap (fun i j p q hp hq => ?_) hn
  refine ExtTensor.grading_map_mem 𝒰₁ 𝒰₂
    (fun i' => ExtTensor.grading (ExtTensor.grading 𝒰₁ 𝒰₃) (ExtTensor.grading 𝒰₂ 𝒰₄) (i' + j))
    ((ExtTensor.middleComm (k := k) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) (M₄ := M₄)).toLinearMap ∘ₗ
      (TensorProduct.mk k (ExtTensor k M₁ M₂) (ExtTensor k M₃ M₄)).flip q)
    (fun i₁ i₂ m₁ m₂ h₁ h₂ => ?_) hp
  refine ExtTensor.grading_map_mem 𝒰₃ 𝒰₄
    (fun j' => ExtTensor.grading (ExtTensor.grading 𝒰₁ 𝒰₃) (ExtTensor.grading 𝒰₂ 𝒰₄)
      (i₁ + i₂ + j'))
    ((ExtTensor.middleComm (k := k) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) (M₄ := M₄)).toLinearMap ∘ₗ
      TensorProduct.mk k (ExtTensor k M₁ M₂) (ExtTensor k M₃ M₄) (ExtTensor.tmul m₁ m₂))
    (fun j₁ j₂ m₃ m₄ h₃ h₄ => ?_) hq
  have h := ExtTensor.tmul_mem_grading (ExtTensor.tmul_mem_grading h₁ h₃)
    (ExtTensor.tmul_mem_grading h₂ h₄)
  rw [add_add_add_comm] at h
  exact h

end Generators

/-! ### Product of two graded inductions as induction from the middle parabolic -/

section MiddleExt

variable {k : Type w} [CommRing k] {Γ : WeightedGraph I 𝕜 k}

variable (k Γ) in
/-- The generator `e_{ν';ν''} = ι_{ν';ν''}(1)` of `W_{ν'+ν''} e_{ν';ν''}`. -/
def gradedIndUnit (ν' ν'' : I →₀ ℕ) : GradedIndBimod k Γ ν' ν'' :=
  ⟨inductionMap k Γ ν' ν'' 1, Graded.mem_leftIdeal.2 isIdempotentElem_inductionMap_one.eq⟩

theorem coe_gradedIndUnit (ν' ν'' : I →₀ ℕ) :
    (gradedIndUnit k Γ ν' ν'' : WeightedKLRAlgebra k Γ (ν' + ν'')) =
      inductionMap k Γ ν' ν'' 1 := rfl

theorem op_smul_gradedIndUnit {ν' ν'' : I →₀ ℕ} (t : TensorW k Γ ν' ν'') :
    (op t • gradedIndUnit k Γ ν' ν'' : GradedIndBimod k Γ ν' ν'') =
      inductionMap k Γ ν' ν'' t • gradedIndUnit k Γ ν' ν'' := by
  apply Subtype.ext
  rw [coe_op_smul, unop_op, Submodule.coe_smul, smul_eq_mul, coe_gradedIndUnit, ← map_mul,
    one_mul, inductionMap_mul_one]

theorem smul_gradedIndUnit {ν' ν'' : I →₀ ℕ} (m : GradedIndBimod k Γ ν' ν'') :
    ((m : WeightedKLRAlgebra k Γ (ν' + ν'')) • gradedIndUnit k Γ ν' ν'' :
      GradedIndBimod k Γ ν' ν'') = m := by
  apply Subtype.ext
  rw [Submodule.coe_smul, smul_eq_mul, coe_gradedIndUnit]
  exact Graded.mem_leftIdeal.1 m.2

variable {a b c d : I →₀ ℕ}

variable (k Γ a b c d) in
/-- `(m, m') ↦ m ⊗ m' : W_{a+c} e_{a;c} × W_{b+d} e_{b;d} → (W_{a+c} ⊗ W_{b+d}) e'`. -/
def bimodPair :
    GradedIndBimod k Γ a c →ₗ[k] GradedIndBimod k Γ b d →ₗ[k] MiddleTop k Γ a b c d :=
  LinearMap.mk₂ k
    (fun m m' => ⟨(m : WeightedKLRAlgebra k Γ (a + c)) ⊗ₜ (m' : WeightedKLRAlgebra k Γ (b + d)),
      by
        rw [mem_middleTopSub, middleTop_one, Algebra.TensorProduct.tmul_mul_tmul,
          Graded.mem_leftIdeal.1 m.2, Graded.mem_leftIdeal.1 m'.2]⟩)
    (fun m₁ m₂ m' => Subtype.ext (TensorProduct.add_tmul _ _ _))
    (fun r m m' => Subtype.ext (TensorProduct.smul_tmul' _ _ _).symm)
    (fun m m₁ m₂ => Subtype.ext (TensorProduct.tmul_add _ _ _))
    (fun r m m' => Subtype.ext (TensorProduct.tmul_smul _ _ _))

theorem coe_bimodPair (m : GradedIndBimod k Γ a c) (m' : GradedIndBimod k Γ b d) :
    (bimodPair k Γ a b c d m m' : WeightedKLRAlgebra k Γ (a + c) ⊗[k]
      WeightedKLRAlgebra k Γ (b + d)) =
      (m : WeightedKLRAlgebra k Γ (a + c)) ⊗ₜ (m' : WeightedKLRAlgebra k Γ (b + d)) := rfl

theorem op_smul_bimodPair (t : TensorW k Γ a c) (t' : TensorW k Γ b d)
    (m : GradedIndBimod k Γ a c) (m' : GradedIndBimod k Γ b d) :
    op ((middleAlgComm k Γ a b c d).symm (t ⊗ₜ t')) • bimodPair k Γ a b c d m m' =
      bimodPair k Γ a b c d (op t • m) (op t' • m') := by
  apply Subtype.ext
  rw [coe_op_smul_middleTop, unop_op, ← pairInd_middleAlgComm, AlgEquiv.apply_symm_apply,
    pairInd_apply, TensorProduct.map_tmul, coe_bimodPair, coe_bimodPair, coe_op_smul,
    coe_op_smul, unop_op, unop_op]
  exact Algebra.TensorProduct.tmul_mul_tmul _ _ _ _

theorem smul_bimodPair (s : WeightedKLRAlgebra k Γ (a + c)) (s' : WeightedKLRAlgebra k Γ (b + d))
    (m : GradedIndBimod k Γ a c) (m' : GradedIndBimod k Γ b d) :
    (s ⊗ₜ s' : WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d)) •
        bimodPair k Γ a b c d m m' = bimodPair k Γ a b c d (s • m) (s' • m') := by
  apply Subtype.ext
  rw [Submodule.coe_smul, smul_eq_mul, coe_bimodPair, coe_bimodPair, Submodule.coe_smul,
    Submodule.coe_smul, smul_eq_mul, smul_eq_mul]
  exact Algebra.TensorProduct.tmul_mul_tmul _ _ _ _

theorem bimodPair_gradedIndUnit_smul
    (t : MiddleTop k Γ a b c d) :
    ((t : WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d)) •
      bimodPair k Γ a b c d (gradedIndUnit k Γ a c) (gradedIndUnit k Γ b d) :
        MiddleTop k Γ a b c d) = t := by
  apply Subtype.ext
  rw [Submodule.coe_smul, smul_eq_mul, coe_bimodPair, coe_gradedIndUnit, coe_gradedIndUnit,
    ← middleTop_one]
  exact t.2

variable {Pa Pb Qc Qd : Type*}
  [AddCommGroup Pa] [Module k Pa] [Module (WeightedKLRAlgebra k Γ a) Pa]
  [IsScalarTower k (WeightedKLRAlgebra k Γ a) Pa]
  [AddCommGroup Pb] [Module k Pb] [Module (WeightedKLRAlgebra k Γ b) Pb]
  [IsScalarTower k (WeightedKLRAlgebra k Γ b) Pb]
  [AddCommGroup Qc] [Module k Qc] [Module (WeightedKLRAlgebra k Γ c) Qc]
  [IsScalarTower k (WeightedKLRAlgebra k Γ c) Qc]
  [AddCommGroup Qd] [Module k Qd] [Module (WeightedKLRAlgebra k Γ d) Qd]
  [IsScalarTower k (WeightedKLRAlgebra k Γ d) Qd]

variable (k Γ) in
/-- `n ↦ e_{ν';ν''} ⊗ n : N → W_{ν'+ν''} e_{ν';ν''} ⊗ N`. -/
def gradedIndUnitMap (ν' ν'' : I →₀ ℕ) (N : Type*) [AddCommGroup N] [Module k N]
    [Module (TensorW k Γ ν' ν'') N] : N →ₗ[k] GradedInd k Γ ν' ν'' N :=
  BalancedTensor.mkBil k _ _ _ N (gradedIndUnit k Γ ν' ν'')

theorem gradedIndUnitMap_apply {ν' ν'' : I →₀ ℕ} {N : Type*} [AddCommGroup N] [Module k N]
    [Module (TensorW k Γ ν' ν'') N] (n : N) :
    gradedIndUnitMap k Γ ν' ν'' N n = BalancedTensor.tmul (gradedIndUnit k Γ ν' ν'') n := rfl

theorem gradedIndUnitMap_smul {ν' ν'' : I →₀ ℕ} {N : Type*} [AddCommGroup N] [Module k N]
    [Module (TensorW k Γ ν' ν'') N] (t : TensorW k Γ ν' ν'') (n : N) :
    gradedIndUnitMap k Γ ν' ν'' N (t • n) =
      inductionMap k Γ ν' ν'' t • gradedIndUnitMap k Γ ν' ν'' N n := by
  rw [gradedIndUnitMap_apply, gradedIndUnitMap_apply, ← BalancedTensor.op_smul_tmul,
    op_smul_gradedIndUnit, BalancedTensor.smul_tmul']

variable (k Γ a b c d Pa Pb Qc Qd) in
/-- `(u ⊠ u') ↦ (e_{a;c} ⊗ u) ⊠ (e_{b;d} ⊗ u')`. -/
def extIndUnit :
    ExtTensor k (ExtTensor k Pa Qc) (ExtTensor k Pb Qd) →ₗ[k]
      ExtTensor k (GradedInd k Γ a c (ExtTensor k Pa Qc)) (GradedInd k Γ b d (ExtTensor k Pb Qd)) :=
  TensorProduct.map (gradedIndUnitMap k Γ a c _) (gradedIndUnitMap k Γ b d _)

theorem extIndUnit_tmul (u : ExtTensor k Pa Qc) (u' : ExtTensor k Pb Qd) :
    extIndUnit k Γ a b c d Pa Pb Qc Qd (ExtTensor.tmul u u') =
      ExtTensor.tmul (gradedIndUnitMap k Γ a c _ u) (gradedIndUnitMap k Γ b d _ u') := rfl

theorem pairInd_tmul (s : TensorW k Γ a c) (s' : TensorW k Γ b d) :
    pairInd k Γ a b c d (s ⊗ₜ s') = inductionMap k Γ a c s ⊗ₜ inductionMap k Γ b d s' := rfl

theorem extIndUnit_smul
    (y : TensorW k Γ a c ⊗[k] TensorW k Γ b d)
    (w : ExtTensor k (ExtTensor k Pa Qc) (ExtTensor k Pb Qd)) :
    extIndUnit k Γ a b c d Pa Pb Qc Qd (y • w) =
      pairInd k Γ a b c d y • extIndUnit k Γ a b c d Pa Pb Qc Qd w :=
  extTensor_smul_eq_along (pairInd k Γ a b c d).toAddMonoidHom (map_add _)
    (map_zero _) (fun s s' u u' => by
      rw [ExtTensor.smul_tmul, extIndUnit_tmul, extIndUnit_tmul, gradedIndUnitMap_smul,
        gradedIndUnitMap_smul]
      exact (ExtTensor.smul_tmul _ _ _ _).symm) y w

/-- The map `(t, n) ↦ t · ((e_{a;c} ⊗ (p_a ⊗ q_c)) ⊠ (e_{b;d} ⊗ (p_b ⊗ q_d)))`. -/
def middleIndToExtIndFun (t : MiddleTop k Γ a b c d)
    (n : ExtTensor k (ExtTensor k Pa Pb) (ExtTensor k Qc Qd)) :
    ExtTensor k (GradedInd k Γ a c (ExtTensor k Pa Qc)) (GradedInd k Γ b d (ExtTensor k Pb Qd)) :=
  (t : WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d)) •
    extIndUnit k Γ a b c d Pa Pb Qc Qd (ExtTensor.middleComm n)

variable (k Γ a b c d Pa Pb Qc Qd) in
/-- `middleIndToExtIndFun` as a `k`-bilinear map. -/
def middleIndToExtIndBil :
    MiddleTop k Γ a b c d →ₗ[k] ExtTensor k (ExtTensor k Pa Pb) (ExtTensor k Qc Qd) →ₗ[k]
      ExtTensor k (GradedInd k Γ a c (ExtTensor k Pa Qc))
        (GradedInd k Γ b d (ExtTensor k Pb Qd)) :=
  (Algebra.lsmul k k (ExtTensor k (GradedInd k Γ a c (ExtTensor k Pa Qc))
      (GradedInd k Γ b d (ExtTensor k Pb Qd)))).toLinearMap.compl₁₂
    ((middleTopSub k Γ a b c d).subtype.restrictScalars k)
    ((extIndUnit k Γ a b c d Pa Pb Qc Qd).comp
      (ExtTensor.middleComm (k := k) (M₁ := Pa) (M₂ := Pb) (M₃ := Qc) (M₄ := Qd)).toLinearMap)

theorem middleIndToExtIndBil_apply (t : MiddleTop k Γ a b c d)
    (n : ExtTensor k (ExtTensor k Pa Pb) (ExtTensor k Qc Qd)) :
    middleIndToExtIndBil k Γ a b c d Pa Pb Qc Qd t n = middleIndToExtIndFun t n := rfl

theorem middleIndToExtIndFun_op_smul (t : MiddleTop k Γ a b c d) (m : MiddleAlg k Γ a b c d)
    (n : ExtTensor k (ExtTensor k Pa Pb) (ExtTensor k Qc Qd)) :
    middleIndToExtIndFun (op m • t) n = middleIndToExtIndFun t (m • n) := by
  have h : extIndUnit k Γ a b c d Pa Pb Qc Qd (ExtTensor.middleComm (m • n)) =
      middleTop k Γ a b c d m • extIndUnit k Γ a b c d Pa Pb Qc Qd (ExtTensor.middleComm n) :=
    (congrArg (extIndUnit k Γ a b c d Pa Pb Qc Qd) (ExtTensor.middleComm_smul m n)).trans
      ((extIndUnit_smul _ _).trans (congrArg (· • _) (pairInd_middleAlgComm m)))
  exact (mul_smul (t : WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d))
    (middleTop k Γ a b c d m) _).trans (congrArg _ h.symm)

theorem middleIndToExtIndFun_smul
    (z : WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d))
    (t : MiddleTop k Γ a b c d) (n : ExtTensor k (ExtTensor k Pa Pb) (ExtTensor k Qc Qd)) :
    middleIndToExtIndFun (z • t) n = z • middleIndToExtIndFun t n :=
  mul_smul z (t : WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d)) _

variable (k Γ a b c d Pa Pb Qc Qd) in
/-- `t ⊗ ((p_a ⊠ p_b) ⊠ (q_c ⊠ q_d)) ↦ t · ((e_{a;c} ⊗ (p_a ⊠ q_c)) ⊠ (e_{b;d} ⊗ (p_b ⊠ q_d)))`. -/
def middleIndToExtInd :
    BalancedTensor k (WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d))
        (MiddleAlg k Γ a b c d) (MiddleTop k Γ a b c d)
        (ExtTensor k (ExtTensor k Pa Pb) (ExtTensor k Qc Qd)) →ₗ[
      WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d)]
      ExtTensor k (GradedInd k Γ a c (ExtTensor k Pa Qc))
        (GradedInd k Γ b d (ExtTensor k Pb Qd)) :=
  BalancedTensor.liftB (middleIndToExtIndBil k Γ a b c d Pa Pb Qc Qd)
    (fun t m n => middleIndToExtIndFun_op_smul t m n)
    (fun z t n => middleIndToExtIndFun_smul z t n)

theorem middleIndToExtInd_tmul (t : MiddleTop k Γ a b c d)
    (n : ExtTensor k (ExtTensor k Pa Pb) (ExtTensor k Qc Qd)) :
    middleIndToExtInd k Γ a b c d Pa Pb Qc Qd (BalancedTensor.tmul t n) =
      middleIndToExtIndFun t n := rfl

variable (Pa Pb Qc Qd) in
/-- The exchange `(P_a ⊠ Q_c) ⊠ (P_b ⊠ Q_d) → (P_a ⊠ P_b) ⊠ (Q_c ⊠ Q_d)`. -/
def gradedMiddleCommInv : ExtTensor k (ExtTensor k Pa Qc) (ExtTensor k Pb Qd) ≃ₗ[k]
    ExtTensor k (ExtTensor k Pa Pb) (ExtTensor k Qc Qd) :=
  (ExtTensor.middleComm (k := k) (M₁ := Pa) (M₂ := Pb) (M₃ := Qc) (M₄ := Qd)).symm

variable (k Γ a b c d) in
/-- The inverse of `middleAlgComm`, as an algebra map. -/
def middleAlgCommInv : TensorW k Γ a c ⊗[k] TensorW k Γ b d →ₐ[k] MiddleAlg k Γ a b c d :=
  (middleAlgComm k Γ a b c d).symm.toAlgHom

theorem middleAlgComm_middleAlgCommInv (y : TensorW k Γ a c ⊗[k] TensorW k Γ b d) :
    middleAlgComm k Γ a b c d (middleAlgCommInv k Γ a b c d y) = y :=
  AlgEquiv.apply_symm_apply _ _

theorem op_smul_bimodPair_inv (t : TensorW k Γ a c) (t' : TensorW k Γ b d)
    (m : GradedIndBimod k Γ a c) (m' : GradedIndBimod k Γ b d) :
    op (middleAlgCommInv k Γ a b c d (t ⊗ₜ[k] t' : TensorW k Γ a c ⊗[k] TensorW k Γ b d)) •
        bimodPair k Γ a b c d m m' =
      bimodPair k Γ a b c d (op t • m) (op t' • m') := by
  apply Subtype.ext
  rw [coe_op_smul_middleTop, unop_op, ← pairInd_middleAlgComm, middleAlgComm_middleAlgCommInv,
    pairInd_apply, TensorProduct.map_tmul, coe_bimodPair, coe_bimodPair, coe_op_smul,
    coe_op_smul, unop_op, unop_op]
  exact Algebra.TensorProduct.tmul_mul_tmul _ _ _ _

theorem gradedMiddleCommInv_smul (y : TensorW k Γ a c ⊗[k] TensorW k Γ b d)
    (w : ExtTensor k (ExtTensor k Pa Qc) (ExtTensor k Pb Qd)) :
    gradedMiddleCommInv Pa Pb Qc Qd (y • w) =
      middleAlgCommInv k Γ a b c d y • gradedMiddleCommInv Pa Pb Qc Qd w :=
  ExtTensor.middleComm_symm_smul y w

theorem gradedMiddleCommInv_symm_apply (n : ExtTensor k (ExtTensor k Pa Pb) (ExtTensor k Qc Qd)) :
    (gradedMiddleCommInv Pa Pb Qc Qd).symm n = ExtTensor.middleComm n := rfl

variable (Pa Pb Qc Qd) in
/-- `(m, u, m', u') ↦ (m ⊗ m') ⊗ ((p_a ⊠ p_b) ⊠ (q_c ⊠ q_d))` for `u = p_a ⊠ q_c`,
`u' = p_b ⊠ q_d`. -/
def extIndPairFun (m : GradedIndBimod k Γ a c) (u : ExtTensor k Pa Qc)
    (m' : GradedIndBimod k Γ b d) (u' : ExtTensor k Pb Qd) :
    BalancedTensor k (WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d))
      (MiddleAlg k Γ a b c d) (MiddleTop k Γ a b c d)
      (ExtTensor k (ExtTensor k Pa Pb) (ExtTensor k Qc Qd)) :=
  BalancedTensor.tmul (bimodPair k Γ a b c d m m')
    (gradedMiddleCommInv Pa Pb Qc Qd (ExtTensor.tmul u u'))

variable (Pa Pb Qc Qd) in
/-- `extIndPairFun` as a `k`-bilinear map in its last two arguments. -/
def extIndPairBil (m : GradedIndBimod k Γ a c) (u : ExtTensor k Pa Qc) :
    GradedIndBimod k Γ b d →ₗ[k] ExtTensor k Pb Qd →ₗ[k]
      BalancedTensor k (WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d))
        (MiddleAlg k Γ a b c d) (MiddleTop k Γ a b c d)
        (ExtTensor k (ExtTensor k Pa Pb) (ExtTensor k Qc Qd)) :=
  (BalancedTensor.mkBil k _ _ _ _).compl₁₂ (bimodPair k Γ a b c d m)
    ((gradedMiddleCommInv Pa Pb Qc Qd).toLinearMap.comp
      (TensorProduct.mk k (ExtTensor k Pa Qc) (ExtTensor k Pb Qd) u))

theorem extIndPairFun_smul (m : GradedIndBimod k Γ a c) (u : ExtTensor k Pa Qc)
    (m' : GradedIndBimod k Γ b d) (u' : ExtTensor k Pb Qd) (t : TensorW k Γ a c)
    (t' : TensorW k Γ b d) :
    extIndPairFun Pa Pb Qc Qd m (t • u) m' (t' • u') =
      extIndPairFun Pa Pb Qc Qd (op t • m) u (op t' • m') u' := by
  have h1 : gradedMiddleCommInv Pa Pb Qc Qd (ExtTensor.tmul (t • u) (t' • u')) =
      middleAlgCommInv k Γ a b c d (t ⊗ₜ[k] t' : TensorW k Γ a c ⊗[k] TensorW k Γ b d) •
        gradedMiddleCommInv Pa Pb Qc Qd (ExtTensor.tmul u u') :=
    (congrArg (gradedMiddleCommInv Pa Pb Qc Qd) (ExtTensor.smul_tmul t t' u u').symm).trans
      (gradedMiddleCommInv_smul _ _)
  rw [extIndPairFun, extIndPairFun, h1, ← BalancedTensor.op_smul_tmul, op_smul_bimodPair_inv]

theorem extIndPairFun_op_smul_right (m : GradedIndBimod k Γ a c) (u : ExtTensor k Pa Qc)
    (m' : GradedIndBimod k Γ b d) (t' : TensorW k Γ b d) (u' : ExtTensor k Pb Qd) :
    extIndPairFun Pa Pb Qc Qd m u (op t' • m') u' =
      extIndPairFun Pa Pb Qc Qd m u m' (t' • u') := by
  have h := extIndPairFun_smul m u m' u' 1 t'
  rw [op_one, one_smul, one_smul] at h
  exact h.symm

theorem extIndPairFun_op_smul_left (m : GradedIndBimod k Γ a c) (t : TensorW k Γ a c)
    (u : ExtTensor k Pa Qc) (m' : GradedIndBimod k Γ b d) (u' : ExtTensor k Pb Qd) :
    extIndPairFun Pa Pb Qc Qd (op t • m) u m' u' =
      extIndPairFun Pa Pb Qc Qd m (t • u) m' u' := by
  have h := extIndPairFun_smul m u m' u' t 1
  rw [op_one, one_smul, one_smul] at h
  exact h.symm

variable (Pa Pb Qc Qd) in
/-- For fixed `m ⊗ u ∈ Ind(P_a ⊠ Q_c)`, the map `Ind(P_b ⊠ Q_d) → (W_{a+c} ⊗ W_{b+d}) e' ⊗ ...`. -/
def extIndInner (m : GradedIndBimod k Γ a c) (u : ExtTensor k Pa Qc) :
    GradedInd k Γ b d (ExtTensor k Pb Qd) →ₗ[k] BalancedTensor k (WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d))
        (MiddleAlg k Γ a b c d) (MiddleTop k Γ a b c d)
        (ExtTensor k (ExtTensor k Pa Pb) (ExtTensor k Qc Qd)) :=
  BalancedTensor.lift (extIndPairBil Pa Pb Qc Qd m u) fun m' t' u' =>
    extIndPairFun_op_smul_right m u m' t' u'

theorem extIndInner_tmul (m : GradedIndBimod k Γ a c) (u : ExtTensor k Pa Qc)
    (m' : GradedIndBimod k Γ b d) (u' : ExtTensor k Pb Qd) :
    extIndInner Pa Pb Qc Qd m u (BalancedTensor.tmul m' u') =
      extIndPairFun Pa Pb Qc Qd m u m' u' := rfl

theorem extIndInner_add_left (m₁ m₂ : GradedIndBimod k Γ a c) (u : ExtTensor k Pa Qc) :
    extIndInner Pa Pb Qc Qd (b := b) (d := d) (m₁ + m₂) u =
      extIndInner Pa Pb Qc Qd (b := b) (d := d) m₁ u + extIndInner Pa Pb Qc Qd (b := b) (d := d) m₂ u :=
  BalancedTensor.ext fun m' u' =>
    (congrArg (fun z => BalancedTensor.tmul z (gradedMiddleCommInv Pa Pb Qc Qd
      (ExtTensor.tmul u u'))) (LinearMap.map_add₂ (bimodPair k Γ a b c d) m₁ m₂ m')).trans
      (BalancedTensor.add_tmul _ _ _)

theorem extIndInner_smul_left (r : k) (m : GradedIndBimod k Γ a c) (u : ExtTensor k Pa Qc) :
    extIndInner Pa Pb Qc Qd (b := b) (d := d) (r • m) u = r • extIndInner Pa Pb Qc Qd (b := b) (d := d) m u :=
  BalancedTensor.ext fun m' u' =>
    (congrArg (fun z => BalancedTensor.tmul z (gradedMiddleCommInv Pa Pb Qc Qd
      (ExtTensor.tmul u u'))) (LinearMap.map_smul₂ (bimodPair k Γ a b c d) r m m')).trans
      (BalancedTensor.smul_tmul _ _ _)

theorem extIndInner_add_right (m : GradedIndBimod k Γ a c) (u₁ u₂ : ExtTensor k Pa Qc) :
    extIndInner Pa Pb Qc Qd (b := b) (d := d) m (u₁ + u₂) =
      extIndInner Pa Pb Qc Qd (b := b) (d := d) m u₁ + extIndInner Pa Pb Qc Qd (b := b) (d := d) m u₂ :=
  BalancedTensor.ext fun m' u' =>
    (congrArg (BalancedTensor.tmul (bimodPair k Γ a b c d m m'))
      ((congrArg (gradedMiddleCommInv Pa Pb Qc Qd) (ExtTensor.add_tmul u₁ u₂ u')).trans
        (map_add (gradedMiddleCommInv Pa Pb Qc Qd) _ _))).trans
      (BalancedTensor.tmul_add _ _ _)

theorem extIndInner_smul_right (r : k) (m : GradedIndBimod k Γ a c) (u : ExtTensor k Pa Qc) :
    extIndInner Pa Pb Qc Qd (b := b) (d := d) m (r • u) = r • extIndInner Pa Pb Qc Qd (b := b) (d := d) m u :=
  BalancedTensor.ext fun m' u' =>
    (congrArg (BalancedTensor.tmul (bimodPair k Γ a b c d m m'))
      ((congrArg (gradedMiddleCommInv Pa Pb Qc Qd) (ExtTensor.smul_tmul' r u u').symm).trans
        (map_smul (gradedMiddleCommInv Pa Pb Qc Qd) _ _))).trans
      (BalancedTensor.tmul_smul _ _ _)

theorem extIndInner_op_smul (m : GradedIndBimod k Γ a c) (t : TensorW k Γ a c)
    (u : ExtTensor k Pa Qc) :
    extIndInner Pa Pb Qc Qd (b := b) (d := d) (op t • m) u =
      extIndInner Pa Pb Qc Qd (b := b) (d := d) m (t • u) :=
  BalancedTensor.ext fun m' u' => extIndPairFun_op_smul_left m t u m' u'

variable (k Γ a b c d Pa Pb Qc Qd) in
/-- The inverse of `middleIndToExtInd`, as a `k`-linear map:
`(m ⊗ (p_a ⊠ q_c)) ⊠ (m' ⊗ (p_b ⊠ q_d)) ↦ (m ⊗ m') ⊗ ((p_a ⊠ p_b) ⊠ (q_c ⊠ q_d))`. -/
def extIndToMiddleInd :
    ExtTensor k (GradedInd k Γ a c (ExtTensor k Pa Qc)) (GradedInd k Γ b d (ExtTensor k Pb Qd))
      →ₗ[k] BalancedTensor k (WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d))
        (MiddleAlg k Γ a b c d) (MiddleTop k Γ a b c d)
        (ExtTensor k (ExtTensor k Pa Pb) (ExtTensor k Qc Qd)) :=
  ExtTensor.lift (BalancedTensor.lift
    (LinearMap.mk₂ k (extIndInner Pa Pb Qc Qd) extIndInner_add_left extIndInner_smul_left
      extIndInner_add_right extIndInner_smul_right) extIndInner_op_smul)

theorem extIndToMiddleInd_tmul (m : GradedIndBimod k Γ a c) (u : ExtTensor k Pa Qc)
    (m' : GradedIndBimod k Γ b d) (u' : ExtTensor k Pb Qd) :
    extIndToMiddleInd k Γ a b c d Pa Pb Qc Qd
        (ExtTensor.tmul (BalancedTensor.tmul m u) (BalancedTensor.tmul m' u')) =
      extIndPairFun Pa Pb Qc Qd m u m' u' := rfl

theorem extIndToMiddleInd_smul
    (s : WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d))
    (y : ExtTensor k (GradedInd k Γ a c (ExtTensor k Pa Qc))
      (GradedInd k Γ b d (ExtTensor k Pb Qd))) :
    extIndToMiddleInd k Γ a b c d Pa Pb Qc Qd (s • y) =
      s • extIndToMiddleInd k Γ a b c d Pa Pb Qc Qd y :=
  extBalancedTensor_smul_eq (extIndToMiddleInd k Γ a b c d Pa Pb Qc Qd).toAddMonoidHom
    (fun s s' m u m' u' =>
      (congrArg (fun z => BalancedTensor.tmul z
          (gradedMiddleCommInv Pa Pb Qc Qd (ExtTensor.tmul u u')))
        (smul_bimodPair s s' m m').symm).trans (BalancedTensor.smul_tmul' _ _ _).symm) s y

theorem extIndToMiddleInd_extIndUnit (w : ExtTensor k (ExtTensor k Pa Qc) (ExtTensor k Pb Qd)) :
    extIndToMiddleInd k Γ a b c d Pa Pb Qc Qd (extIndUnit k Γ a b c d Pa Pb Qc Qd w) =
      BalancedTensor.tmul (bimodPair k Γ a b c d (gradedIndUnit k Γ a c) (gradedIndUnit k Γ b d))
        (gradedMiddleCommInv Pa Pb Qc Qd w) :=
  LinearMap.congr_fun (f := (extIndToMiddleInd k Γ a b c d Pa Pb Qc Qd).comp
      (extIndUnit k Γ a b c d Pa Pb Qc Qd))
    (g := (BalancedTensor.mkBil k _ _ _ _ (bimodPair k Γ a b c d (gradedIndUnit k Γ a c)
      (gradedIndUnit k Γ b d))).comp (gradedMiddleCommInv Pa Pb Qc Qd).toLinearMap)
    (TensorProduct.ext' fun _ _ => rfl) w

theorem gradedMiddleCommInv_middleComm
    (n : ExtTensor k (ExtTensor k Pa Pb) (ExtTensor k Qc Qd)) :
    gradedMiddleCommInv Pa Pb Qc Qd (ExtTensor.middleComm n) = n :=
  LinearEquiv.symm_apply_apply _ n

theorem middleComm_gradedMiddleCommInv
    (w : ExtTensor k (ExtTensor k Pa Qc) (ExtTensor k Pb Qd)) :
    ExtTensor.middleComm (gradedMiddleCommInv Pa Pb Qc Qd w) = w :=
  LinearEquiv.apply_symm_apply _ w

theorem extIndToMiddleInd_middleIndToExtInd_tmul (t : MiddleTop k Γ a b c d)
    (n : ExtTensor k (ExtTensor k Pa Pb) (ExtTensor k Qc Qd)) :
    extIndToMiddleInd k Γ a b c d Pa Pb Qc Qd
        (middleIndToExtInd k Γ a b c d Pa Pb Qc Qd (BalancedTensor.tmul t n)) =
      BalancedTensor.tmul t n := by
  have h1 := extIndToMiddleInd_smul (Pa := Pa) (Pb := Pb) (Qc := Qc) (Qd := Qd)
    (t : WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d))
    (extIndUnit k Γ a b c d Pa Pb Qc Qd (ExtTensor.middleComm n))
  have h2 := extIndToMiddleInd_extIndUnit (Γ := Γ) (a := a) (b := b) (c := c) (d := d)
    (ExtTensor.middleComm (k := k) (M₁ := Pa) (M₂ := Pb) (M₃ := Qc) (M₄ := Qd) n)
  rw [gradedMiddleCommInv_middleComm] at h2
  rw [middleIndToExtInd_tmul, middleIndToExtIndFun, h1, h2, BalancedTensor.smul_tmul',
    bimodPair_gradedIndUnit_smul]

theorem extIndToMiddleInd_middleIndToExtInd
    (x : BalancedTensor k (WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d))
      (MiddleAlg k Γ a b c d) (MiddleTop k Γ a b c d)
      (ExtTensor k (ExtTensor k Pa Pb) (ExtTensor k Qc Qd))) :
    extIndToMiddleInd k Γ a b c d Pa Pb Qc Qd (middleIndToExtInd k Γ a b c d Pa Pb Qc Qd x) =
      x :=
  balancedTensor_leftInverse (middleIndToExtInd k Γ a b c d Pa Pb Qc Qd).toAddMonoidHom
    (extIndToMiddleInd k Γ a b c d Pa Pb Qc Qd).toAddMonoidHom
    extIndToMiddleInd_middleIndToExtInd_tmul x

theorem middleIndToExtInd_extIndToMiddleInd
    (y : ExtTensor k (GradedInd k Γ a c (ExtTensor k Pa Qc))
      (GradedInd k Γ b d (ExtTensor k Pb Qd))) :
    middleIndToExtInd k Γ a b c d Pa Pb Qc Qd (extIndToMiddleInd k Γ a b c d Pa Pb Qc Qd y) =
      y :=
  extBalancedTensor_leftInverse (extIndToMiddleInd k Γ a b c d Pa Pb Qc Qd).toAddMonoidHom
    (middleIndToExtInd k Γ a b c d Pa Pb Qc Qd).toAddMonoidHom (fun m u m' u' =>
      (congrArg (middleIndToExtInd k Γ a b c d Pa Pb Qc Qd) (extIndToMiddleInd_tmul m u m' u')).trans <|
      (middleIndToExtInd_tmul _ _).trans <|
      (congrArg (fun z => ((m : WeightedKLRAlgebra k Γ (a + c)) ⊗ₜ[k]
          (m' : WeightedKLRAlgebra k Γ (b + d))) • extIndUnit k Γ a b c d Pa Pb Qc Qd z)
        (middleComm_gradedMiddleCommInv (ExtTensor.tmul u u'))).trans <|
      (congrArg (((m : WeightedKLRAlgebra k Γ (a + c)) ⊗ₜ[k]
          (m' : WeightedKLRAlgebra k Γ (b + d))) • ·) (extIndUnit_tmul u u')).trans <|
      (ExtTensor.smul_tmul _ _ _ _).trans <|
        congrArg₂ ExtTensor.tmul
          ((BalancedTensor.smul_tmul' _ _ _).trans
            (congrArg (fun z => BalancedTensor.tmul z u) (smul_gradedIndUnit m)))
          ((BalancedTensor.smul_tmul' _ _ _).trans
            (congrArg (fun z => BalancedTensor.tmul z u') (smul_gradedIndUnit m')))) y

variable (k Γ a b c d Pa Pb Qc Qd) in
/-- **The product of two graded inductions is induction from the middle parabolic**:
`(W_{a+c} ⊗ W_{b+d}) e' ⊗_{W'} ((P_a ⊠ P_b) ⊠ (Q_c ⊠ Q_d)) ≅ Ind(P_a ⊠ Q_c) ⊠ Ind(P_b ⊠ Q_d)`
as `W_{a+c} ⊗ W_{b+d}`-modules, for the inductions `W_{ν'+ν''} e_{ν';ν''} ⊗ -` of Webster,
arXiv:1209.2463v4, Definition 2.17, over any commutative ring. This is the module-level step
behind the multiplicativity of the coproduct in Theorem 2.19; the ungraded form is
`Juxtapose.extIndIndEquiv`. -/
def middleIndExtIndEquiv :
    BalancedTensor k (WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d))
        (MiddleAlg k Γ a b c d) (MiddleTop k Γ a b c d)
        (ExtTensor k (ExtTensor k Pa Pb) (ExtTensor k Qc Qd)) ≃ₗ[
      WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d)]
      ExtTensor k (GradedInd k Γ a c (ExtTensor k Pa Qc))
        (GradedInd k Γ b d (ExtTensor k Pb Qd)) :=
  { middleIndToExtInd k Γ a b c d Pa Pb Qc Qd with
    invFun := extIndToMiddleInd k Γ a b c d Pa Pb Qc Qd
    left_inv := extIndToMiddleInd_middleIndToExtInd
    right_inv := middleIndToExtInd_extIndToMiddleInd }

end MiddleExt

end Juxtapose

namespace GradingDatum

section Field

variable {k : Type w} [Field k] {Γ : WeightedGraph I 𝕜 k} (G : GradingDatum Γ)
  {a b c d : I →₀ ℕ}

/-- `n ↦ e_{ν';ν''} ⊗ n` is degree-preserving. -/
theorem gradedIndUnitMap_mem {ν' ν'' : I →₀ ℕ} {N : Type*} [AddCommGroup N] [Module k N]
    [Module (TensorW k Γ ν' ν'') N] {𝒩 : ℤ → Submodule k N} {i : ℤ} {n : N} (hn : n ∈ 𝒩 i) :
    gradedIndUnitMap k Γ ν' ν'' N n ∈ G.gradedIndGrading ν' ν'' 𝒩 i := by
  have h := tmul_mem_balancedGrading (B := WeightedKLRAlgebra k Γ (ν' + ν''))
    (A := TensorW k Γ ν' ν'') (ℳ := G.indBimodGrading ν' ν'') (𝒩 := 𝒩)
    (m := gradedIndUnit k Γ ν' ν'') (G.inductionMap_one_mem_klrGrade (ν' := ν') (ν'' := ν'')) hn
  rw [zero_add] at h
  exact h

variable (a b c d) in
/-- **The product of two graded inductions is graded induction from the middle parabolic**
(the graded form of `Juxtapose.extIndIndEquiv`):
`(W_{a+c} ⊗ W_{b+d}) e' ⊗_{W'} ((P_a ⊠ P_b) ⊠ (Q_c ⊠ Q_d)) ≅ Ind(P_a ⊠ Q_c) ⊠ Ind(P_b ⊠ Q_d)` as
graded `W_{a+c} ⊗ W_{b+d}`-modules, with no grading shift, for the inductions of Webster,
arXiv:1209.2463v4, Definition 2.17. -/
def middleIndGProjExtIndIso (Pa : GProj (G.klrGrade a)) (Pb : GProj (G.klrGrade b))
    (Qc : GProj (G.klrGrade c)) (Qd : GProj (G.klrGrade d)) :
    (G.middleIndGProj a b c d ((Pa.extTensor Pb).extTensor (Qc.extTensor Qd))).Iso
      ((G.indProj Pa Qc).extTensor (G.indProj Pb Qd)) :=
  GradedEquiv.ofPreserves
    (middleIndExtIndEquiv k Γ a b c d Pa.carrier Pb.carrier Qc.carrier Qd.carrier)
    fun _ _ hy => balancedGrading_map_mem
      (B := WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d))
      (A := MiddleAlg k Γ a b c d) _
      ((middleIndExtIndEquiv k Γ a b c d Pa.carrier Pb.carrier Qc.carrier
        Qd.carrier).toLinearMap.restrictScalars k)
      (fun _ _ _ _ ht hn => SetLike.GradedSMul.smul_mem
        (self := ((G.indProj Pa Qc).extTensor (G.indProj Pb Qd)).gradedSMul) ht
        (ExtTensor.grading_map_mem _ _ _ (extIndUnit k Γ a b c d Pa.carrier Pb.carrier Qc.carrier
            Qd.carrier)
          (fun _ _ _ _ hu hu' => ExtTensor.tmul_mem_grading (G.gradedIndUnitMap_mem hu)
            (G.gradedIndUnitMap_mem hu'))
          (middleComm_mem_grading hn))) hy

theorem middleIndK0_extTensor_of (Pa : GProj (G.klrGrade a)) (Pb : GProj (G.klrGrade b))
    (Qc : GProj (G.klrGrade c)) (Qd : GProj (G.klrGrade d)) :
    G.middleIndK0 a b c d (K0.of ((Pa.extTensor Pb).extTensor (Qc.extTensor Qd))) =
      K0.of ((G.indProj Pa Qc).extTensor (G.indProj Pb Qd)) := by
  rw [middleIndK0_of]
  exact K0.of_eq_of_iso (G.middleIndGProjExtIndIso a b c d Pa Pb Qc Qd)

variable (a b c d) in
/-- **Graded induction from the middle parabolic of an external product of external
products**: `middleInd ((x_a ⊠ x_b) ⊠ (y_c ⊠ y_d)) = (x_a · y_c) ⊠ (x_b · y_d)` in the graded
`K₀(W_{a+c} ⊗ W_{b+d})`, over any field (Webster, arXiv:1209.2463v4, Theorem 2.19). -/
theorem middleIndK0_extTensor (xa : K0 (G.klrGrade a)) (xb : K0 (G.klrGrade b))
    (yc : K0 (G.klrGrade c)) (yd : K0 (G.klrGrade d)) :
    G.middleIndK0 a b c d (K0.extTensor _ _ (K0.extTensor _ _ xa xb) (K0.extTensor _ _ yc yd)) =
      K0.extTensor _ _ (G.indK0 a c xa yc) (G.indK0 b d xb yd) := by
  induction xa using K0.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | neg x hx => simp only [map_neg, LinearMap.neg_apply, hx]
  | of Pa =>
    induction xb using K0.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
    | neg x hx => simp only [map_neg, LinearMap.neg_apply, hx]
    | of Pb =>
      induction yc using K0.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
      | neg x hx => simp only [map_neg, LinearMap.neg_apply, hx]
      | of Qc =>
        induction yd using K0.induction_on with
        | zero => simp
        | add x y hx hy => simp only [map_add, hx, hy]
        | neg x hx => simp only [map_neg, hx]
        | of Qd =>
          rw [K0.extTensor_of, K0.extTensor_of, K0.extTensor_of, indK0_of, indK0_of,
            K0.extTensor_of]
          exact G.middleIndK0_extTensor_of Pa Pb Qc Qd

end Field

end GradingDatum

end Categorification.WeightedKLR

/-! ### Transport of external products, the graded coproduct and the Mackey formula -/

namespace Categorification.Graded

namespace K0

open scoped TensorProduct

variable {k : Type v} [Field k] {A B A' B' : Type u} [Ring A] [Algebra k A] [Ring B]
  [Algebra k B] [Ring A'] [Algebra k A'] [Ring B'] [Algebra k B']
  {𝒜 : ℤ → Submodule k A} {ℬ : ℤ → Submodule k B} {𝒜' : ℤ → Submodule k A'}
  {ℬ' : ℤ → Submodule k B'}

/-- Transport of external products of graded projective modules along graded isomorphisms of
both factors. -/
theorem map_congr_extTensor (σ : A ≃ₐ[k] A') (τ : B ≃ₐ[k] B')
    (hσ : ∀ ⦃d : ℤ⦄ ⦃a : A'⦄, a ∈ 𝒜' d → σ.symm a ∈ 𝒜 d)
    (hτ : ∀ ⦃d : ℤ⦄ ⦃b : B'⦄, b ∈ ℬ' d → τ.symm b ∈ ℬ d)
    (hστ : ∀ ⦃d : ℤ⦄ ⦃t : A' ⊗[k] B'⦄, t ∈ tensorGrading 𝒜' ℬ' d →
      (Algebra.TensorProduct.congr σ τ).symm t ∈ tensorGrading 𝒜 ℬ d)
    (x : K0 𝒜) (y : K0 ℬ) :
    map (Algebra.TensorProduct.congr σ τ) hστ (extTensor 𝒜 ℬ x y) =
      extTensor 𝒜' ℬ' (map σ hσ x) (map τ hτ y) := by
  induction x using induction_on with
  | of P =>
    induction y using induction_on with
    | of Q =>
      rw [extTensor_of, map_of σ hσ P, map_of τ hτ Q, extTensor_of]
      refine map_of_semilinear _ _ _ ((GProj.restrict σ hσ P).extTensor (GProj.restrict τ hτ Q))
        (AddEquiv.refl (ExtTensor k P.carrier Q.carrier)) (fun t x => ?_) (fun _ _ h => h)
        (fun _ _ h => h)
      induction t using TensorProduct.inductionOn with
      | add t t' ht ht' =>
        show ((t + t') • x : ExtTensor k P.carrier Q.carrier) =
          (Algebra.TensorProduct.congr σ τ (t + t') • (show ExtTensor k (GProj.restrict σ hσ P).carrier
            (GProj.restrict τ hτ Q).carrier from x))
        rw [add_smul, map_add, add_smul]
        exact congrArg₂ (· + ·) ht ht'
      | tmul a b =>
        show ((a ⊗ₜ[k] b) • x : ExtTensor k P.carrier Q.carrier) =
          (Algebra.TensorProduct.congr σ τ (a ⊗ₜ[k] b) • (show ExtTensor k
            (GProj.restrict σ hσ P).carrier (GProj.restrict τ hτ Q).carrier from x))
        rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
        induction x using ExtTensor.induction_on with
        | zero =>
          show ((a ⊗ₜ[k] b) • (0 : ExtTensor k P.carrier Q.carrier) :
              ExtTensor k P.carrier Q.carrier) = ((σ a ⊗ₜ[k] τ b) •
            (0 : ExtTensor k (GProj.restrict σ hσ P).carrier (GProj.restrict τ hτ Q).carrier))
          rw [smul_zero, smul_zero]; rfl
        | tmul p q =>
          show ExtTensor.tmul (a • p) (b • q) =
            ExtTensor.tmul (σ.symm (σ a) • p) (τ.symm (τ b) • q)
          rw [AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply]
        | add x x' hx hx' =>
          show ((a ⊗ₜ[k] b) • (x + x' : ExtTensor k P.carrier Q.carrier) :
              ExtTensor k P.carrier Q.carrier) = ((σ a ⊗ₜ[k] τ b) •
            ((show ExtTensor k (GProj.restrict σ hσ P).carrier (GProj.restrict τ hτ Q).carrier from x) +
              (show ExtTensor k (GProj.restrict σ hσ P).carrier (GProj.restrict τ hτ Q).carrier from x')))
          rw [smul_add, smul_add]
          exact congrArg₂ (· + ·) hx hx'
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | neg y hy => simp only [map_neg, hy]
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | neg x hx => simp only [map_neg, LinearMap.neg_apply, hx]

end K0

end Categorification.Graded

namespace Categorification.WeightedKLR

open Categorification.Graded Juxtapose
open scoped TensorProduct

variable {I : Type u} [DecidableEq I] {𝕜 : Type v} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜]

namespace GradingDatum

section Coproduct

variable {k : Type w} [Field k] {Γ : WeightedGraph I 𝕜 k} (G : GradingDatum Γ)

/-- The product of Webster's Theorem 2.19 on `K₀(W_μ) ⊗_{ℤ[q,q⁻¹]} K₀(W_{μ'})`, landing in
`K₀(W_ν)` for `μ + μ' = ν` through `castW` (Webster, arXiv:1209.2463v4, §2.4). -/
def indK0TensorCast (μ μ' ν : I →₀ ℕ) (h : μ + μ' = ν) :
    K0 (G.klrGrade μ) ⊗[LaurentPolynomial ℤ] K0 (G.klrGrade μ') →ₗ[LaurentPolynomial ℤ]
      K0 (G.klrGrade ν) :=
  K0.map (castW k Γ h) (fun _ _ hx => G.castW_symm_mem_klrGrade h hx) ∘ₗ G.indK0Tensor μ μ'

theorem indK0TensorCast_tmul {μ μ' ν : I →₀ ℕ} (h : μ + μ' = ν) (x : K0 (G.klrGrade μ))
    (y : K0 (G.klrGrade μ')) :
    G.indK0TensorCast μ μ' ν h (x ⊗ₜ y) =
      K0.map (castW k Γ h) (fun _ _ hx => G.castW_symm_mem_klrGrade h hx) (G.indK0 μ μ' x y) := by
  rw [indK0TensorCast, LinearMap.comp_apply, indK0Tensor_tmul]

section Def

variable (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hS : Γ.Standing) (ν₁ ν₂ : I →₀ ℕ)
  [HasGdim (G.klrGrade ν₁)] [HasGdim (G.klrGrade ν₂)]

/-- **The graded coproduct of Webster's Theorem 2.19 on `K₀ ⊗ K₀`** (arXiv:1209.2463v4, §2.4):
`Δ_{ν₁,ν₂} : K₀(W_{ν₁+ν₂}) → K₀(W_{ν₁}) ⊗_{ℤ[q,q⁻¹]} K₀(W_{ν₂})`, `[L] ↦ [Res_{ν₁;ν₂} L]`
followed by the inverse of `k0TensorEquiv`. It is defined under the route hypothesis
`TensorK0Hyp (G.klrGrade ν₁) (G.klrGrade ν₂)`, which Webster's paper does not supply and which
is not proved here for weighted KLR algebras (see `GradedK0/TensorK0.lean`). -/
def coproductK0 (H : TensorK0Hyp (G.klrGrade ν₁) (G.klrGrade ν₂)) :
    K0 (G.klrGrade (ν₁ + ν₂)) →ₗ[LaurentPolynomial ℤ]
      K0 (G.klrGrade ν₁) ⊗[LaurentPolynomial ℤ] K0 (G.klrGrade ν₂) :=
  (G.k0TensorEquiv ν₁ ν₂ H).symm.toLinearMap ∘ₗ G.resK0 ν₁ ν₂ hD hZ hS

theorem k0TensorEquiv_coproductK0 (H : TensorK0Hyp (G.klrGrade ν₁) (G.klrGrade ν₂))
    (x : K0 (G.klrGrade (ν₁ + ν₂))) :
    G.k0TensorEquiv ν₁ ν₂ H (G.coproductK0 hD hZ hS ν₁ ν₂ H x) = G.resK0 ν₁ ν₂ hD hZ hS x :=
  (G.k0TensorEquiv ν₁ ν₂ H).apply_symm_apply _

end Def

end Coproduct

end GradingDatum

namespace ShuffleLayout

variable {k : Type w} [Field k] {Γ : WeightedGraph I 𝕜 k} (G : GradingDatum Γ)
  {ν' ν'' ν₁ ν₂ : I →₀ ℕ} (L : ShuffleLayout ν' ν'' ν₁ ν₂)

/-- **The graded twisted product of a shuffle layout** on `K₀ ⊗ K₀`:
`(x_a ⊗ x_b) ⊗ (y_c ⊗ y_d) ↦ (x_a · y_c) ⊗ (x_b · y_d)`, from
`(K₀(W_a) ⊗ K₀(W_b)) ⊗ (K₀(W_c) ⊗ K₀(W_d))` to `K₀(W_{ν₁}) ⊗ K₀(W_{ν₂})`, tensor products
over `ℤ[q,q⁻¹]` (Webster, arXiv:1209.2463v4, Theorem 2.19). The power of `q` of the Mackey
formula is not part of this map. -/
def twistedMulK0Graded :
    (K0 (G.klrGrade L.a) ⊗[LaurentPolynomial ℤ] K0 (G.klrGrade L.b)) ⊗[LaurentPolynomial ℤ]
        (K0 (G.klrGrade L.c) ⊗[LaurentPolynomial ℤ] K0 (G.klrGrade L.d)) →ₗ[LaurentPolynomial ℤ]
      K0 (G.klrGrade ν₁) ⊗[LaurentPolynomial ℤ] K0 (G.klrGrade ν₂) :=
  TensorProduct.map (G.indK0TensorCast L.a L.c ν₁ L.hac) (G.indK0TensorCast L.b L.d ν₂ L.hbd) ∘ₗ
    (TensorProduct.tensorTensorTensorComm (LaurentPolynomial ℤ) _ _ _ _).toLinearMap

theorem twistedMulK0Graded_tmul (xa : K0 (G.klrGrade L.a)) (xb : K0 (G.klrGrade L.b))
    (yc : K0 (G.klrGrade L.c)) (yd : K0 (G.klrGrade L.d)) :
    L.twistedMulK0Graded G ((xa ⊗ₜ xb) ⊗ₜ (yc ⊗ₜ yd)) =
      G.indK0TensorCast L.a L.c ν₁ L.hac (xa ⊗ₜ yc) ⊗ₜ
        G.indK0TensorCast L.b L.d ν₂ L.hbd (xb ⊗ₜ yd) :=
  rfl

/-- The graded twisted product under the comparisons `k0TensorEquiv` is the twisted
`Ind ∘ Res` of `ResIndPiece.twistK0Graded`: `[T_L (u ⊗ w)] =
(Ind_{a;c} ⊗ Ind_{b;d}) ∘ (exchange) ([u] ⊠ [w])`, under `TensorK0Hyp` for the four pairs of
factors (Webster, arXiv:1209.2463v4, Theorem 2.19). -/
theorem k0TensorEquiv_twistedMulK0Graded
    [HasGdim (G.klrGrade L.a)] [HasGdim (G.klrGrade L.b)] [HasGdim (G.klrGrade L.c)]
    [HasGdim (G.klrGrade L.d)] [HasGdim (G.klrGrade ν₁)] [HasGdim (G.klrGrade ν₂)]
    (Hab : TensorK0Hyp (G.klrGrade L.a) (G.klrGrade L.b))
    (Hcd : TensorK0Hyp (G.klrGrade L.c) (G.klrGrade L.d))
    (H₁₂ : TensorK0Hyp (G.klrGrade ν₁) (G.klrGrade ν₂))
    (u : K0 (G.klrGrade L.a) ⊗[LaurentPolynomial ℤ] K0 (G.klrGrade L.b))
    (w : K0 (G.klrGrade L.c) ⊗[LaurentPolynomial ℤ] K0 (G.klrGrade L.d)) :
    G.k0TensorEquiv ν₁ ν₂ H₁₂ (L.twistedMulK0Graded G (u ⊗ₜ w)) =
      K0.map (L.leftEquiv k Γ) (fun _ _ h => L.leftEquiv_symm_mem G h)
        (G.middleIndK0 L.a L.b L.c L.d (K0.extTensor _ _ (G.k0TensorEquiv L.a L.b Hab u)
          (G.k0TensorEquiv L.c L.d Hcd w))) := by
  induction u using TensorProduct.inductionOn with
  | add u u' hu hu' => simp only [TensorProduct.add_tmul, map_add, LinearMap.add_apply, hu, hu']
  | tmul xa xb =>
    induction w using TensorProduct.inductionOn with
    | add w w' hw hw' => simp only [TensorProduct.tmul_add, map_add, hw, hw']
    | tmul yc yd =>
      rw [twistedMulK0Graded_tmul, GradingDatum.k0TensorEquiv_tmul,
        GradingDatum.k0TensorEquiv_tmul, GradingDatum.k0TensorEquiv_tmul,
        G.middleIndK0_extTensor, GradingDatum.indK0TensorCast_tmul,
        GradingDatum.indK0TensorCast_tmul]
      exact (K0.map_congr_extTensor (castW k Γ L.hac) (castW k Γ L.hbd)
        (fun _ _ h => G.castW_symm_mem_klrGrade L.hac h)
        (fun _ _ h => G.castW_symm_mem_klrGrade L.hbd h)
        (fun _ _ h => L.leftEquiv_symm_mem G h) _ _).symm

end ShuffleLayout

section GradedMackey

variable {k : Type w} [Field k] {Γ : WeightedGraph I 𝕜 k} {ν' ν'' ν₁ ν₂ : I →₀ ℕ}

/-- **The graded Mackey formula for the coproduct on `K₀ ⊗ K₀`** (Webster, arXiv:1209.2463v4,
Theorem 2.19). Over a field `k`, under Webster's standing hypothesis, for `ν₁ + ν₂ = ν' + ν''`
there are shuffle layouts `L i`, one for each shuffle type of `(ν', ν''; ν₁, ν₂)`, with
`Δ_{ν₁,ν₂}(x · y) = ∑ᵢ q^{sᵢ} T_{L i}(Δ_{a,b} x ⊗ Δ_{c,d} y)` for all `x ∈ K₀(W_{ν'})`,
`y ∈ K₀(W_{ν''})`, where `sᵢ = middleShift G a b c d` for the blocks of `L i`, `T_L` is
`ShuffleLayout.twistedMulK0Graded` and algebras of equal dimension vectors are identified by
`castW`. **Route hypothesis:** `hT`, `TensorK0Hyp` for every pair of weighted KLR algebras
(the identification `K₀(W_μ ⊗ W_{μ'}) ≅ K₀(W_μ) ⊗ K₀(W_{μ'})` that Webster uses without
justification), not proved here for weighted KLR algebras (its conditions `endA`, `endB` are
open); the graded dimensions of the `W_μ` are supplied for the grading of the standing
hypothesis by `GalleryAlgebra.hasGdim_klrGrade`. -/
theorem exists_coproductK0_indK0_eq_sum_graded (G : GradingDatum Γ) (hD : Γ.Dagger)
    (hZ : Γ.NoZeroLoops) (hS : Γ.Standing) (hν : ν₁ + ν₂ = ν' + ν'')
    [∀ μ : I →₀ ℕ, HasGdim (G.klrGrade μ)]
    (hT : ∀ μ μ' : I →₀ ℕ, TensorK0Hyp (G.klrGrade μ) (G.klrGrade μ')) :
    ∃ (n : ℕ) (L : Fin n → ShuffleLayout ν' ν'' ν₁ ν₂),
      Function.Injective (fun i => ⇑(L i).c) ∧
      Set.range (fun i => ⇑(L i).c) = Set.range (shuffleType (ν := ν' + ν'') ν' ν₁) ∧
      ∀ (x : K0 (G.klrGrade ν')) (y : K0 (G.klrGrade ν'')),
        G.coproductK0 hD hZ hS ν₁ ν₂ (hT ν₁ ν₂) (K0.map (castW k Γ hν.symm)
            (fun _ _ h => G.castW_symm_mem_klrGrade hν.symm h) (G.indK0 ν' ν'' x y)) =
          ∑ i, (LaurentPolynomial.T (middleShift G (L i).a (L i).b (L i).c (L i).d) :
              LaurentPolynomial ℤ) •
            (L i).twistedMulK0Graded G
              (G.coproductK0 hD hZ hS (L i).a (L i).b (hT _ _)
                  (K0.map (castW k Γ (L i).hab).symm
                    (fun _ _ h => G.castW_mem_klrGrade (L i).hab h) x) ⊗ₜ
                G.coproductK0 hD hZ hS (L i).c (L i).d (hT _ _)
                  (K0.map (castW k Γ (L i).hcd).symm
                    (fun _ _ h => G.castW_mem_klrGrade (L i).hcd h) y)) := by
  obtain ⟨n, L, hinj, hrange, h⟩ :=
    exists_resK0_indK0_eq_sum_twistK0Graded (k := k) G hD hZ hS hν
  refine ⟨n, L, hinj, hrange, fun x y => (G.k0TensorEquiv ν₁ ν₂ (hT ν₁ ν₂)).injective ?_⟩
  rw [GradingDatum.k0TensorEquiv_coproductK0, h, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, ShuffleLayout.k0TensorEquiv_twistedMulK0Graded G (L i) (hT _ _) (hT _ _),
    GradingDatum.k0TensorEquiv_coproductK0, GradingDatum.k0TensorEquiv_coproductK0]
  rfl

end GradedMackey

end Categorification.WeightedKLR

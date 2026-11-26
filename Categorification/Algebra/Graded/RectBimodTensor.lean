/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.CornerBimoduleGrading
import Categorification.Algebra.CornerTensor
import Categorification.Algebra.BalancedTensorAssoc
import Categorification.Algebra.BalancedTensorExact

/-!
# Tensor products of rectangular corners

Let `φ : A' ≃ A` be an isomorphism of `k`-algebras, and let `α : T → A`, `β : T' → A`,
`γ : T'' → A`, `β' : T' → A'`, `γ' : T'' → A'` be multiplicative maps with `φ ∘ β' = β` and
`φ ∘ γ' = γ`. Multiplication `y ⊗ x ↦ x φ(y)` is a map of `(T, T'')`-bimodules
`α(1) A β(1) ⊗_{T'} β'(1) A' γ'(1) → α(1) A γ(1)`, of degree zero for gradings preserved by
`φ` (`RectBimod.tensorMul`). If `β` maps onto the corner `β(1) A β(1)` and multiplication
`α(1) A β(1) ⊗_{β(1) A β(1)} β(1) A γ(1) → A` is injective with image `α(1) A γ(1)`, it is an
isomorphism (`RectBimod.tensorMulEquiv`).

In B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §6.1,
this compares the composite of two braiding functors with a single one: Lemma 6.5 gives the
bijectivity of the corner multiplication, and `φ` relabels the red strands.
-/

noncomputable section

namespace Categorification.Graded.RectBimod

open MulOpposite BalancedTensor

variable {k : Type*} [Field k] {A A' : Type*} [Ring A] [Algebra k A] [Ring A'] [Algebra k A']
  {T T' T'' : Type*} [Ring T] [Algebra k T] [Ring T'] [Algebra k T'] [Ring T''] [Algebra k T'']
  (φ : A' ≃ₐ[k] A) {α : T →ₙₐ[k] A} {β : T' →ₙₐ[k] A} {γ : T'' →ₙₐ[k] A}
  {β' : T' →ₙₐ[k] A'} {γ' : T'' →ₙₐ[k] A'}

theorem isIdempotentElem_one {S : Type*} [Ring S] [Algebra k S] (f : S →ₙₐ[k] A) :
    IsIdempotentElem (f 1) := by
  rw [IsIdempotentElem, ← map_mul, one_mul]

variable (hβ : ∀ t, φ (β' t) = β t) (hγ : ∀ u, φ (γ' u) = γ u)

include hγ in
theorem mul_map_mem (y : RectBimod β' γ') (x : RectBimod α β) :
    α 1 * (val α β x * φ (val β' γ' y)) = val α β x * φ (val β' γ' y) ∧
      (val α β x * φ (val β' γ' y)) * γ 1 = val α β x * φ (val β' γ' y) := by
  refine ⟨by rw [← mul_assoc, (mem x).1], ?_⟩
  rw [mul_assoc, ← hγ 1, ← map_mul, (mem y).2]

/-- The bilinear map `y, x ↦ x φ(y)`. -/
def tensorMulBil : RectBimod β' γ' →ₗ[k] RectBimod α β →ₗ[k] RectBimod α γ :=
  LinearMap.mk₂ k (fun y x => mk (val α β x * φ (val β' γ' y)) (mul_map_mem φ hγ y x))
    (fun y y' x => ext (by
      change val α β x * φ (val β' γ' y + val β' γ' y') = _
      rw [map_add, mul_add]; rfl))
    (fun c y x => ext (by
      change val α β x * φ (c • val β' γ' y) = c • (val α β x * φ (val β' γ' y))
      rw [map_smul, mul_smul_comm]))
    (fun y x x' => ext (by
      change (val α β x + val α β x') * φ (val β' γ' y) = _
      rw [add_mul]; rfl))
    (fun c y x => ext (by
      change (c • val α β x) * φ (val β' γ' y) = c • (val α β x * φ (val β' γ' y))
      rw [smul_mul_assoc]))

include hβ in
theorem tensorMulBil_balanced (y : RectBimod β' γ') (a : T'ᵐᵒᵖ) (x : RectBimod α β) :
    tensorMulBil φ hγ (op a • y) x = tensorMulBil φ hγ y (a • x) := ext (by
  change val α β x * φ (β' a.unop * val β' γ' y) = val α β x * β a.unop * φ (val β' γ' y)
  rw [map_mul, hβ, mul_assoc])

/-- **Multiplication of rectangular corners**, `y ⊗ x ↦ x φ(y)`, a map of `(T, T'')`-bimodules
`α(1) A β(1) ⊗_{T'} β'(1) A' γ'(1) → α(1) A γ(1)` (written as left `T''ᵐᵒᵖ`-modules). -/
def tensorMul :
    BalancedTensor k T''ᵐᵒᵖ T'ᵐᵒᵖ (RectBimod β' γ') (RectBimod α β) →ₗ[T''ᵐᵒᵖ]
      RectBimod α γ :=
  liftB (tensorMulBil φ hγ) (tensorMulBil_balanced φ hβ hγ) fun b y x => ext (by
    change val α β x * φ (val β' γ' y * γ' b.unop) = val α β x * φ (val β' γ' y) * γ b.unop
    rw [map_mul, hγ, mul_assoc])

theorem val_tensorMul_tmul (y : RectBimod β' γ') (x : RectBimod α β) :
    val α γ (tensorMul φ hβ hγ (tmul y x)) = val α β x * φ (val β' γ' y) := rfl

/-- Multiplication commutes with the left `T`-actions. -/
theorem isBimoduleHom_tensorMul :
    IsBimoduleHom (B := T''ᵐᵒᵖ) (A := Tᵐᵒᵖ) (tensorMul (α := α) φ hβ hγ) := by
  intro a t
  induction t using BalancedTensor.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul y x =>
    refine ext ?_
    change val α β (op a • x) * φ (val β' γ' y) = α (op a).unop.unop * (val α β x * φ (val β' γ' y))
    change α (op a).unop.unop * val α β x * φ (val β' γ' y) = _
    rw [mul_assoc]
  | add s t hs ht => rw [smul_add, map_add, hs, ht, map_add, smul_add]

/-- Multiplication has degree zero for gradings preserved by `φ`. -/
theorem tensorMul_mem_grading (𝒢 : ℤ → Submodule k A) (𝒢' : ℤ → Submodule k A')
    [SetLike.GradedMonoid 𝒢] (hφ : ∀ ⦃d : ℤ⦄ ⦃y : A'⦄, y ∈ 𝒢' d → φ y ∈ 𝒢 d) ⦃d : ℤ⦄
    ⦃t : BalancedTensor k T''ᵐᵒᵖ T'ᵐᵒᵖ (RectBimod β' γ') (RectBimod α β)⦄
    (ht : t ∈ balancedGrading T''ᵐᵒᵖ T'ᵐᵒᵖ (grading 𝒢' β' γ') (grading 𝒢 α β) d) :
    tensorMul φ hβ hγ t ∈ grading 𝒢 α γ d :=
  balancedGrading_map_mem _ ((tensorMul φ hβ hγ).restrictScalars k) (fun i j y x hy hx => by
    change val α β x * φ (val β' γ' y) ∈ 𝒢 (i + j)
    rw [add_comm]
    exact SetLike.GradedMul.mul_mem hx (hφ hy)) ht

/-! ### Bijectivity -/

local notation "CT" => CornerTensor k A (α 1) (β 1) (γ 1)

include hβ hγ in
/-- The comparison with the corner tensor product, `y ⊗ x ↦ x ⊗ φ(y)`. -/
private def toCorner :
    BalancedTensor k T''ᵐᵒᵖ T'ᵐᵒᵖ (RectBimod β' γ') (RectBimod α β) →ₗ[k] CT :=
  lift (LinearMap.mk₂ k (fun y x => CornerTensor.tmul (val α β x) (φ (val β' γ' y)))
      (fun y y' x => by
        change CornerTensor.tmul _ (φ (val β' γ' y + val β' γ' y')) = _
        rw [map_add, CornerTensor.tmul_add_right])
      (fun c y x => by
        change CornerTensor.tmul _ (φ (c • val β' γ' y)) = _
        rw [map_smul, CornerTensor.tmul_smul_right])
      (fun y x x' => by
        change CornerTensor.tmul (val α β x + val α β x') _ = _
        rw [CornerTensor.tmul_add_left])
      (fun c y x => by
        change CornerTensor.tmul (c • val α β x) _ = _
        rw [CornerTensor.tmul_smul_left]))
    fun y a x => by
      change CornerTensor.tmul (val α β x) (φ (β' a.unop * val β' γ' y)) =
        CornerTensor.tmul (val α β x * β a.unop) (φ (val β' γ' y))
      have hc : β 1 * β a.unop * β 1 = β a.unop := by
        rw [← map_mul, ← map_mul, one_mul, mul_one]
      rw [map_mul, hβ, CornerTensor.tmul_balance_of hc]

private theorem toCorner_tmul (y : RectBimod β' γ') (x : RectBimod α β) :
    toCorner (γ := γ) φ hβ (tmul y x) = CornerTensor.tmul (val α β x) (φ (val β' γ' y)) := rfl

include hβ hγ in
private theorem symm_mem (z : A) :
    β' 1 * φ.symm (β 1 * z * γ 1) = φ.symm (β 1 * z * γ 1) ∧
      φ.symm (β 1 * z * γ 1) * γ' 1 = φ.symm (β 1 * z * γ 1) := by
  constructor
  · apply φ.injective
    rw [map_mul, AlgEquiv.apply_symm_apply, hβ, ← mul_assoc, ← mul_assoc,
      (isIdempotentElem_one β).eq]
  · apply φ.injective
    rw [map_mul, AlgEquiv.apply_symm_apply, hγ, mul_assoc, (isIdempotentElem_one γ).eq]

private theorem corner_mem (x : A) :
    α 1 * (α 1 * x * β 1) = α 1 * x * β 1 ∧ (α 1 * x * β 1) * β 1 = α 1 * x * β 1 := by
  constructor
  · rw [← mul_assoc, ← mul_assoc, (isIdempotentElem_one α).eq]
  · rw [mul_assoc, (isIdempotentElem_one β).eq]

/-- The bilinear map `x, z ↦ φ⁻¹(β(1) z γ(1)) ⊗ α(1) x β(1)`. -/
private def fromCornerBil :
    A →ₗ[k] A →ₗ[k] BalancedTensor k T''ᵐᵒᵖ T'ᵐᵒᵖ (RectBimod β' γ') (RectBimod α β) :=
  LinearMap.mk₂ k (fun x z => tmul (mk (φ.symm (β 1 * z * γ 1)) (symm_mem φ hβ hγ z))
      (mk (α 1 * x * β 1) (corner_mem x)))
    (fun x x' z => by
      rw [← tmul_add]
      congr 1
      exact ext (by simp only [val_mk, mul_add, add_mul]; rfl))
    (fun c x z => by
      rw [← tmul_smul]
      congr 1
      exact ext (by simp only [val_mk, mul_smul_comm, smul_mul_assoc]; rfl))
    (fun x z z' => by
      rw [← add_tmul]
      congr 1
      exact ext (by simp only [val_mk, mul_add, add_mul, map_add]))
    (fun c x z => by
      rw [← smul_tmul]
      congr 1
      exact ext (by simp only [val_mk, mul_smul_comm, smul_mul_assoc, map_smul]))

variable (hsurj : ∀ c, β 1 * c = c ∧ c * β 1 = c → ∃ t, β t = c)

include hsurj in
/-- The inverse comparison with the corner tensor product. -/
private def fromCorner :
    CT →ₗ[k] BalancedTensor k T''ᵐᵒᵖ T'ᵐᵒᵖ (RectBimod β' γ') (RectBimod α β) :=
  (CornerTensor.rel k A (α 1) (β 1) (γ 1)).liftQ (TensorProduct.lift (fromCornerBil φ hβ hγ)) <| by
    rw [CornerTensor.rel, Submodule.span_le]
    rintro t (⟨x, z, rfl⟩ | ⟨x, c, z, rfl⟩) <;>
      simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, TensorProduct.lift.tmul,
        sub_eq_zero]
    · change tmul _ _ = tmul _ _
      congr 1
      · exact ext (by
          simp only [val_mk]
          congr 1
          simp only [← mul_assoc, (isIdempotentElem_one β).eq]
          rw [mul_assoc _ (γ 1), (isIdempotentElem_one γ).eq])
      · exact ext (by
          simp only [val_mk]
          simp only [← mul_assoc, (isIdempotentElem_one α).eq]
          rw [mul_assoc _ (β 1), (isIdempotentElem_one β).eq])
    · obtain ⟨t, ht⟩ := hsurj (β 1 * c * β 1)
        ⟨by rw [← mul_assoc, ← mul_assoc, (isIdempotentElem_one β).eq],
         by rw [mul_assoc, (isIdempotentElem_one β).eq]⟩
      change tmul _ _ = tmul _ _
      have h1 : β 1 * β t = β t := by rw [← map_mul, one_mul]
      have h2 : β t * β 1 = β t := by rw [← map_mul, mul_one]
      have hx : (mk (α 1 * (x * (β 1 * c * β 1)) * β 1) (corner_mem _) : RectBimod α β) =
          op t • (mk (α 1 * x * β 1) (corner_mem x) : RectBimod α β) := ext (by
        change α 1 * (x * (β 1 * c * β 1)) * β 1 = α 1 * x * β 1 * β (op t).unop
        rw [← ht, unop_op, mul_assoc (α 1 * x) (β 1) (β t), h1, mul_assoc (α 1) (x * β t),
          mul_assoc x (β t), h2, ← mul_assoc])
      have hz : (mk (φ.symm (β 1 * (β 1 * c * β 1 * z) * γ 1)) (symm_mem φ hβ hγ _) :
          RectBimod β' γ') = op (op t) • (mk (φ.symm (β 1 * z * γ 1)) (symm_mem φ hβ hγ z) :
            RectBimod β' γ') := ext (by
        change φ.symm (β 1 * (β 1 * c * β 1 * z) * γ 1) =
          β' (op (op t)).unop.unop * φ.symm (β 1 * z * γ 1)
        apply φ.injective
        have r : ∀ a : A, a * β 1 * β 1 = a * β 1 := fun a => by
          rw [mul_assoc, (isIdempotentElem_one β).eq]
        simp only [map_mul, AlgEquiv.apply_symm_apply, unop_op, hβ]
        rw [ht]
        simp only [← mul_assoc, (isIdempotentElem_one β).eq, r])
      rw [hx, hz, op_smul_tmul]

private theorem fromCorner_tmul (x z : A) :
    fromCorner φ hβ hγ hsurj (CornerTensor.tmul x z) =
      tmul (mk (φ.symm (β 1 * z * γ 1)) (symm_mem φ hβ hγ z)) (mk (α 1 * x * β 1) (corner_mem x)) :=
  rfl

private theorem fromCorner_toCorner (t : BalancedTensor k T''ᵐᵒᵖ T'ᵐᵒᵖ (RectBimod β' γ')
    (RectBimod α β)) : fromCorner φ hβ hγ hsurj (toCorner (γ := γ) φ hβ t) = t := by
  induction t using BalancedTensor.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul y x =>
    rw [toCorner_tmul, fromCorner_tmul]
    congr 1
    · refine ext ?_
      change φ.symm (β 1 * φ (val β' γ' y) * γ 1) = val β' γ' y
      apply φ.injective
      rw [AlgEquiv.apply_symm_apply, ← hβ, ← hγ, ← map_mul, ← map_mul, (mem y).1, (mem y).2]
    · refine ext ?_
      change α 1 * val α β x * β 1 = val α β x
      rw [(mem x).1, (mem x).2]
  | add s t hs ht => rw [map_add, map_add, hs, ht]

private theorem toCorner_fromCorner (t : CT) : toCorner (γ := γ) φ hβ (fromCorner φ hβ hγ hsurj t) = t := by
  induction t using CornerTensor.induction_on with
  | tmul x z =>
    rw [fromCorner_tmul, toCorner_tmul]
    change CornerTensor.tmul (α 1 * x * β 1) (φ (φ.symm (β 1 * z * γ 1))) = _
    rw [AlgEquiv.apply_symm_apply, ← CornerTensor.tmul_corner]
  | add s t hs ht => rw [map_add, map_add, hs, ht]

variable (hinj : Function.Injective (CornerTensor.mult (isIdempotentElem_one α)
    (isIdempotentElem_one β) (isIdempotentElem_one γ) :
      CornerTensor k A (α 1) (β 1) (γ 1) →ₗ[k] A))
  (hmul : ∀ z, ∃ t : CornerTensor k A (α 1) (β 1) (γ 1), CornerTensor.mult (isIdempotentElem_one α) (isIdempotentElem_one β)
    (isIdempotentElem_one γ) t = α 1 * z * γ 1)

private theorem mult_toCorner (t : BalancedTensor k T''ᵐᵒᵖ T'ᵐᵒᵖ (RectBimod β' γ')
    (RectBimod α β)) :
    CornerTensor.mult (isIdempotentElem_one α) (isIdempotentElem_one β)
      (isIdempotentElem_one γ) (toCorner (γ := γ) φ hβ t) = val α γ (tensorMul φ hβ hγ t) := by
  induction t using BalancedTensor.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul y x =>
    rw [toCorner_tmul, CornerTensor.mult_tmul, val_tensorMul_tmul, (mem x).1, (mem x).2, ← hγ,
      mul_assoc, ← map_mul, (mem y).2]
  | add s t hs ht => rw [map_add, map_add, hs, ht, map_add, map_add]

include hsurj hinj hmul in
theorem tensorMul_bijective : Function.Bijective (tensorMul (α := α) φ hβ hγ) := by
  constructor
  · intro s t hst
    rw [← fromCorner_toCorner (γ := γ) φ hβ hγ hsurj s, ← fromCorner_toCorner (γ := γ) φ hβ hγ hsurj t]
    congr 1
    apply hinj
    rw [mult_toCorner φ hβ hγ, mult_toCorner φ hβ hγ, hst]
  · intro z
    obtain ⟨t, ht⟩ := hmul (val α γ z)
    refine ⟨fromCorner φ hβ hγ hsurj t, ext ?_⟩
    rw [← mult_toCorner φ hβ hγ, toCorner_fromCorner, ht, (mem z).1, (mem z).2]

/-- **Multiplication of rectangular corners as an isomorphism**, when `β` maps onto its corner
and the corner multiplication is injective onto `α(1) A γ(1)`. -/
def tensorMulEquiv :
    BalancedTensor k T''ᵐᵒᵖ T'ᵐᵒᵖ (RectBimod β' γ') (RectBimod α β) ≃ₗ[T''ᵐᵒᵖ] RectBimod α γ :=
  LinearEquiv.ofBijective (tensorMul φ hβ hγ) (tensorMul_bijective φ hβ hγ hsurj hinj hmul)

theorem tensorMulEquiv_apply (t : BalancedTensor k T''ᵐᵒᵖ T'ᵐᵒᵖ (RectBimod β' γ')
    (RectBimod α β)) : tensorMulEquiv φ hβ hγ hsurj hinj hmul t = tensorMul φ hβ hγ t := rfl

end Categorification.Graded.RectBimod

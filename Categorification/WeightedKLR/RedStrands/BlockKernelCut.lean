/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockKernelTensor
import Categorification.WeightedKLR.RedStrands.BraidedStandardInjective

/-!
# Cutting the violated relations in the tensor of the higher submodule

Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8, paragraph after (6.21).
Work in the braided algebra of Proposition 6.4 (red dots removed, no global
violations imposed). A marked pair consists of a lift of an element of the higher
ideal above the seam and an arbitrary lower diagram. Pushing a global violation to
the source order gives a marking with the same stack and zero upper factor in `K`.
Subtracting these markings reduces the degree-one kernel to relations whose stacks
already vanish before the violated quotient. No assertion that all such changes
of marking are balanced relations is used here.
-/
noncomputable section
namespace Categorification.Stendhal.BraidedStendhalAlgebra
open KLR TypeA
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
variable {I : Type} {k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ} {ν : Multiset I}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
    (t : KLR.Seq (stendhalWeight ℓ ν)) (a b : Fin ℓ) (κ' : List (Fin ℓ))
local notation "A" => BraidedStendhalAlgebra k Q Λ ν
local notation "V" => ViolQuotient k Q Λ ν
local notation "mk" => violMk k Q Λ ν
local notation "e" => fun i => ofKLR k Q Λ ν (KLRAlgebra.e i)
local notation "κ" => redWord t
local notation "E" => redProj k Q Λ ν κ
local notation "F" => redProj k Q Λ ν κ'
local notation "J" => blockUpperIdeal k Q Λ ν a b (adjacentBlockRoot a b t) κ
local notation "K" => blockLoadingKernel Q Λ t a b
local notation "B" => RedBlock.crossingSpace (k := k) (mk E) (mk F)
local notation "T" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν κ)
local notation "inc" => blockKernelTensorInclusion Q Λ t a b κ'
local notation "stack" => blockLoadingTensorStack Q Λ t κ'

/-- Allowed upper representatives before imposing global violations. On compressing
the two ends these project onto the higher submodule, not the standard quotient. -/
def blockKernelUpper : Submodule k A :=
  ((TwoSidedIdeal.asIdeal (J)).restrictScalars k).comap (mk).toLinearMap
local notation "U" => blockKernelUpper Q Λ t a b

/-- Upper half of a marked pair as a diagram in the higher submodule. -/
def blockKernelUpperClass : U →ₗ[k] K where
  toFun x := ⟨blockLoadingRep Q Λ t (mk x.1), by
    change (blockLoadingRep Q Λ t (mk x.1)).1.1 ∈ J
    rw [blockLoadingRep_val]
    exact (J).mul_mem_right _ _ ((J).mul_mem_left _ _ x.2)⟩
  map_add' x y := by
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    change (blockLoadingRep Q Λ t (mk (x.1+y.1))).1.1 =
      (blockLoadingRep Q Λ t (mk x.1)).1.1 + (blockLoadingRep Q Λ t (mk y.1)).1.1
    simp only [blockLoadingRep_val, map_add, mul_add, add_mul]
  map_smul' c x := by
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    change (blockLoadingRep Q Λ t (mk (c • x.1))).1.1 = c • (blockLoadingRep Q Λ t (mk x.1)).1.1
    simp only [blockLoadingRep_val, map_smul, mul_smul_comm, smul_mul_assoc]

/-- Lower half of a marked pair, with both red-order projectors imposed. -/
def blockKernelLowerClass : A →ₗ[k] B :=
  ((mk).toLinearMap ∘ₗ LinearMap.mulRight k F ∘ₗ LinearMap.mulLeft k E).codRestrict B fun z => by
    change mk E * mk (E*z*F) = mk (E*z*F) ∧ mk (E*z*F) * mk F = mk (E*z*F)
    simp only [← map_mul]; constructor <;> congr 1
    · rw [← mul_assoc, ← mul_assoc, (isIdempotentElem_redProj κ).eq]
    · rw [mul_assoc _ F F, (isIdempotentElem_redProj κ').eq]

/-- A marked representative evaluated in the independently defined balanced kernel tensor. -/
def blockKernelCut : U ⊗[k] A →ₗ[k] BalancedTensor k k T K B :=
  BalancedTensor.mk k k T K B ∘ₗ TensorProduct.map (blockKernelUpperClass Q Λ t a b) (blockKernelLowerClass Q Λ t κ')

/-- Forget the seam *before* passing to `V`. Both external projectors and the source
order at the seam are retained. -/
def blockKernelCutStack : U ⊗[k] A →ₗ[k] A :=
  LinearMap.mul' k A ∘ₗ TensorProduct.map ((LinearMap.mulRight k E).comp
    ((LinearMap.mulLeft k (e t)).comp (U).subtype)) (LinearMap.mulRight k F)

local notation "cl" => blockKernelCut Q Λ t a b κ'
local notation "mult" => blockKernelCutStack Q Λ t a b κ'

theorem blockKernelCutStack_tmul (x : U) (y : A) : mult (x ⊗ₜ y) = e t * x.1 * E * (y * F) := rfl

private theorem stack_cut (z : U ⊗[k] A) : stack (inc (cl z)) = mk (mult z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
    change (blockLoadingRep Q Λ t (mk x.1)).1.1 * mk (E*y*F) = mk (e t * x.1 * E * (y*F))
    rw [blockLoadingRep_val]; simp only [← map_mul, ← mul_assoc]
    rw [mul_assoc _ E E, (isIdempotentElem_redProj κ).eq]

private theorem blockKernelUpperClass_surjective : Function.Surjective (blockKernelUpperClass Q Λ t a b) := by
  intro x
  obtain ⟨y,hy⟩ := violMk_surjective x.1.1.1
  have hu : y ∈ U := by change mk y ∈ J; rw [hy]; exact x.2
  refine ⟨⟨y,hu⟩, Subtype.ext ?_⟩
  change blockLoadingRep Q Λ t (mk y) = x.1
  rw [hy, blockLoadingRep_self]

private theorem blockKernelLowerClass_surjective : Function.Surjective (blockKernelLowerClass Q Λ t κ') := by
  intro x
  obtain ⟨y,hy⟩ := violMk_surjective x.1
  refine ⟨y, Subtype.ext ?_⟩
  change mk (E*y*F) = x.1
  rw [map_mul, map_mul, hy, x.2.1, x.2.2]

/-- All balanced kernel tensors have marked representatives, independently of equality
after stacking (Webster v2, §6.1, proof following (6.21)). -/
theorem blockKernelCut_surjective : Function.Surjective cl :=
  BalancedTensor.mk_surjective.comp (TensorProduct.map_surjective (blockKernelUpperClass_surjective Q Λ t a b)
    (blockKernelLowerClass_surjective Q Λ t κ'))

local notation "Z" => Submodule.map mult (LinearMap.ker cl)

private theorem violated_mark (u v : A) {i : KLR.Seq (stendhalWeight ℓ ν)} (hi : redWord i = κ)
    (hv : IsViolated i) : e t * (u * e i * v) * F ∈ Z := by
  have hz : mk (u * e i) = 0 := by rw [map_mul, violMk_e hv, mul_zero]
  let x : U := ⟨u * e i, by change mk (u * e i) ∈ J; rw [hz]; exact (J).zero_mem⟩
  have hx : blockKernelUpperClass Q Λ t a b x = 0 := by
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    change (blockLoadingRep Q Λ t (mk (u * e i))).1.1 = 0
    rw [blockLoadingRep_val, hz, mul_zero, zero_mul]
  refine ⟨x ⊗ₜ v, ?_, ?_⟩
  · change BalancedTensor.tmul (blockKernelUpperClass Q Λ t a b x) (blockKernelLowerClass Q Λ t κ' v) = 0
    rw [hx, BalancedTensor.zero_tmul]
  · rw [blockKernelCutStack_tmul]
    change e t * (u * e i) * E * (v * F) = _
    simp only [mul_assoc, e_mul_redProj κ i, ite_eq_left hi]

/-- **Interior violations have zero kernel-tensor lifts** (Webster v2, Lemma 6.8,
paragraph following (6.21)). No higher quotient is taken in the hypothesis. The new
marking has an equal stack in the algebra of Proposition 6.4, not just in its quotient. -/
theorem exists_zero_blockKernelCut (hQ : KLRSymm Q) {x : A} (hx : mk x = 0) :
    ∃ z, mult z = e t * x * F ∧ cl z = 0 := by
  have hw : IsReducedChoice (canWord (stendhalWeight ℓ ν).card) :=
    fun w => ⟨isReduced_canWord _ w, wordProd_canWord _ w⟩
  have hh := redProj_mul_mem_violSpan hw hQ κ ((violMk_eq_zero_iff _).mp hx)
  let cut := (LinearMap.mulRight k F).comp (LinearMap.mulLeft k (e t))
  have H : cut (E*x) ∈ Z := by
    apply (show violSpan k Q Λ ν κ ≤ (Z).comap cut from Submodule.span_le.2 ?_) hh
    rintro _ ⟨u,i,v,hv,hi,rfl⟩; exact violated_mark Q Λ t a b κ' u v hi hv
  change e t * (E*x) * F ∈ Z at H
  rw [← mul_assoc, e_mul_redProj, ite_eq_left rfl] at H
  obtain ⟨z,hz,he⟩ := H
  exact ⟨z,he,hz⟩

private theorem normalize_stack (z : U ⊗[k] A) : e t * mult z * F = mult z := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, mul_add, add_mul, hx, hy]
  | tmul x y =>
    have he : e t * e t = e t := by rw [← map_mul, KLRAlgebra.e_mul_self]
    simp only [blockKernelCutStack_tmul, ← mul_assoc, he]
    rw [mul_assoc _ F F, (isIdempotentElem_redProj κ').eq]

private theorem ker_eq_image_of_zero_lifts {M N D C : Type*} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] [AddCommGroup D] [Module k D] [AddCommGroup C] [Module k C]
    (c : M →ₗ[k] N) (d : M →ₗ[k] D) (i : N →ₗ[k] C) (hs : Function.Surjective c)
    (hl : ∀ v, i (c v) = 0 → ∃ w, d w = d v ∧ c w = 0)
    (hr : ∀ v, d v = 0 → i (c v) = 0) : LinearMap.ker i = (LinearMap.ker d).map c := by
  apply le_antisymm
  · rintro z hz; obtain ⟨v,rfl⟩ := hs z
    obtain ⟨w,hw,hc⟩ := hl v hz
    exact ⟨v-w, by change d (v-w) = 0; rw [map_sub, hw, sub_self], by rw [map_sub,hc,sub_zero]⟩
  · rintro _ ⟨v,hv,rfl⟩; exact hr v hv

private theorem lift_zero_stack (hQ : KLRSymm Q) (v : U ⊗[k] A) (hz : inc (cl v) = 0) :
    ∃ w, mult w = mult v ∧ cl w = 0 := by
  have hv : mk (mult v) = 0 := (stack_cut Q Λ t a b κ' v).symm.trans
    ((blockKernelTensorInclusion_eq_zero_iff Q Λ t a b κ' (cl v)).1 hz)
  have H : ∃ w : U ⊗[k] A, mult w = e t * mult v * F ∧ cl w = 0 :=
    exists_zero_blockKernelCut Q Λ t a b κ' hQ (x := mult v) hv
  exact H.imp fun _ hw => ⟨hw.1.trans (normalize_stack Q Λ t a b κ' v), hw.2⟩

private theorem cut_of_zero_stack (v : U ⊗[k] A) (hv : mult v = 0) : inc (cl v) = 0 :=
  (blockKernelTensorInclusion_eq_zero_iff Q Λ t a b κ' (cl v)).2
    ((stack_cut Q Λ t a b κ' v).trans ((congrArg mk hv).trans (map_zero mk)))

/-- **Reduction of the kernel in (6.21) to affine relations** (Webster v2, Lemma 6.8).
Every class killed by the inclusion after tensoring is the class of a sum of marked
pairs with zero stack before imposing violations. The remaining injectivity assertion
is that these affine relations are already zero as balanced classes with upper factor in `K`. -/
theorem ker_blockKernelTensorInclusion_eq_map (hQ : KLRSymm Q) :
    LinearMap.ker inc = (LinearMap.ker mult).map cl := by
  refine ker_eq_image_of_zero_lifts (k := k) (M := U ⊗[k] A) (N := BalancedTensor k k T K B)
    (D := A) (C := BalancedTensor k k T (rIdeal (orderedLoadingIdem Q Λ t)) B)
    cl mult inc (blockKernelCut_surjective Q Λ t a b κ') (lift_zero_stack Q Λ t a b κ' hQ)
    (cut_of_zero_stack Q Λ t a b κ')

end Categorification.Stendhal.BraidedStendhalAlgebra

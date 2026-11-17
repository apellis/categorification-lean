/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LastRedLayerTensor
import Categorification.WeightedKLR.RedStrands.SingleRedGrading

/-!
# Grading on the last-red layer presentation

Webster, arXiv:1309.3796v2, Definitions 4.4–4.7 and the rank argument in
Theorem 4.38. The smaller-suffix ideal is generated in degree zero. The
fixed-weight layer corner has the quotient grading, and its presentation by
the shorter tensor product algebra and the cyclotomic algebra preserves
degrees.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR KLRAlgebra Categorification.Graded
open scoped TensorProduct DirectSum
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ+1) → I →₀ ℕ)
  {ν θ β : Multiset I}
variable (G : GradingDatum (stendhalQ Q Λ)) (p : Fin (stendhalWeight (ℓ+1) ν).card)
  (h : stendhalWeight (ℓ+1) θ + β.map (Sum.inl : I → I ⊕ Fin (ℓ+1)) = stendhalWeight (ℓ+1) ν)
  (ha : (stendhalWeight (ℓ+1) θ).card = p.val+1)

local notation "ι" => (Sum.inl : I → I ⊕ Fin (ℓ+1))
local notation "M" => stendhalWeight (ℓ+1) ν
local notation "PWeight" => stendhalWeight (ℓ+1) θ
local notation "B" => β.map ι
local notation "S" => stendhalQ Q Λ
local notation "π" => StendhalAlgebraAllOrders.ofKLR k Q Λ ν
local notation "π₀" => StendhalAlgebraAllOrders.ofKLR k Q Λ θ
local notation "τ" => TensorProductAlgebra.mk Q Λ ν
local notation "q" => RingCon.mkₐ k (TwoSidedIdeal.ringCon (smallerSuffixIdeal Q Λ p))
local notation "J" => smallerSuffixIdeal Q Λ p
local notation "F" => suffixConcat Q Λ p h
local notation "C" => RingCon.Quotient (TwoSidedIdeal.ringCon (smallerSuffixIdeal Q Λ p))
local notation "λf" => (fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i)
local notation "L" => TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) θ
local notation "R" => CycKLR k Q λf β

/-- The quotient grading by diagrams through smaller suffixes. -/
def lastRedLayerGrade : ℤ → Submodule k C := Graded.map (tensorProductGrade G ν) (q).toLinearMap

/-- The smaller-suffix ideal is homogeneous, since all of its generating
boundary idempotents have degree zero. -/
theorem smallerSuffixIdeal_decompose_mem (x : TensorProductAlgebra k Q Λ ν)
    (hx : x ∈ J) (d : ℤ) : (DirectSum.decompose (tensorProductGrade G ν) x d).val ∈ J := by
  apply Graded.decompose_mem_twoSidedSpan (tensorProductGrade G ν) _ hx d
  rintro _ ⟨s,hs,_,_,_,rfl⟩
  exact ⟨0,mk_e_mem_tensorProductGrade G ν s hs⟩

instance lastRedLayerGradedAlgebra : GradedAlgebra (lastRedLayerGrade Q Λ G p) :=
  Graded.mapGradedAlgebra _ q (RingCon.mkₐ_surjective _) fun x hx d => by
    change (J).ringCon.mk' _ = 0 at hx ⊢
    rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk'] at hx ⊢
    exact smallerSuffixIdeal_decompose_mem Q Λ G p x hx d

private theorem raw_mem_layer_grade {d : ℤ} {x : KLRAlgebra k S M} (hx : x ∈ G.grade M d) :
    lastRedLayerProjection Q Λ p (π x) ∈ lastRedLayerGrade Q Λ G p d := by
  apply Graded.mem_map_of_mem (tensorProductGrade G ν) (q).toLinearMap
  apply Graded.mem_map_of_mem (stendhalGrade G ν) (τ).toLinearMap
  change π x * StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν ∈ allOrdersGrade G ν d
  have he : StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν ∈ allOrdersGrade G ν 0 :=
    Submodule.sum_mem _ fun a _ => Graded.mem_map_of_mem _ (π).toLinearMap (G.e_mem_grade a)
  have hπ : π x ∈ allOrdersGrade G ν d := Graded.mem_map_of_mem _ (π).toLinearMap hx
  simpa only [add_zero] using SetLike.GradedMul.mul_mem (A := allOrdersGrade G ν) hπ he

theorem suffixConcat_tmul_mem_grade {i j : ℤ} {a : KLRAlgebra k S PWeight} {b : KLRAlgebra k S B}
    (h₁ : a ∈ G.grade PWeight i) (h₂ : b ∈ G.grade B j) :
    F (a ⊗ₜ b) ∈ lastRedLayerGrade Q Λ G p (i+j) :=
  raw_mem_layer_grade Q Λ G p (G.castKLR_mem_grade h (G.concat_tmul_mem_grade h₁ h₂))

theorem prefixTensor_mem_grade {i : ℤ} {x : TensorProductAlgebra k Q Λ θ}
    (hx : x ∈ tensorProductGrade G θ i) :
    prefixTensor Q Λ p h x ∈ lastRedLayerGrade Q Λ G p i := by
  obtain ⟨z,hz,rfl⟩ := Submodule.mem_map.mp hx
  obtain ⟨a,ha,he⟩ := Submodule.mem_map.mp (show z.val ∈ allOrdersGrade G θ i from hz)
  have hp : orderProjection Q Λ θ (π₀ a) = z := by
    apply Subtype.ext
    change π₀ a * _ = z.val
    change π₀ a = z.val at he
    rw [he]
    exact KLR.Corner.val_mul_E z
  change prefixTensor Q Λ p h (TensorProductAlgebra.mk Q Λ θ z) ∈ _
  rw [← hp,prefixTensor_projection]
  simpa only [add_zero] using suffixConcat_tmul_mem_grade Q Λ G p h ha
    (SetLike.GradedOne.one_mem : (1 : KLRAlgebra k S B) ∈ G.grade B 0)

theorem lastRedLayerIdem_mem_grade : lastRedLayerIdem Q Λ p h ∈ lastRedLayerGrade Q Λ G p 0 :=
  prefixTensor_mem_grade Q Λ G p h (TensorProductAlgebra.lastRedIdem_mem_grade Q Λ θ G)

/-- The graded algebra in the specified layer corner. -/
def lastRedLayerCornerGrade : ℤ → Submodule k (lastRedLayerIdem_idem Q Λ p h).Corner :=
  Graded.cornerGrading (lastRedLayerGrade Q Λ G p) (lastRedLayerIdem_idem Q Λ p h)

instance lastRedLayerCornerGradedAlgebra : GradedAlgebra (lastRedLayerCornerGrade Q Λ G p h) :=
  Graded.cornerGradedAlgebra _ _ (lastRedLayerIdem_mem_grade Q Λ G p h)

/-- Restriction of the augmented grading to the pure black labels. -/
def restrictBlackGrading : GradingDatum Q where
  degX i := G.degX (.inl i)
  degΨ i j := G.degΨ (.inl i) (.inl j)
  degΨ_self i := G.degΨ_self (.inl i)
  isWeightedHomogeneous i j hij := G.isWeightedHomogeneous (.inl i) (.inl j) (fun he => hij (Sum.inl_injective he))

local notation "Black" => restrictBlackGrading Q Λ G
local notation "Earlier" => tensorProductGrade (restrictRedGrading Q Λ G) θ
local notation "Final" => CycKLR.grade Black (Λ (Fin.last ℓ)) β

/-- The surjective layer homomorphism is graded for the tensor product
grading on its source and the quotient corner grading on its target. -/
theorem lastRedLayerTensor_mem_grade {d : ℤ} {z : L ⊗[k] R}
    (hz : z ∈ tensorGrading Earlier Final d) :
    lastRedLayerTensor Q Λ p h ha z ∈ lastRedLayerCornerGrade Q Λ G p h d := by
  classical
  induction hz using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨i,j,x,y,rfl,hx,hy,rfl⟩ := ht
    obtain ⟨v,hv,rfl⟩ := Submodule.mem_map.mp hy
    change (lastRedLayerTensor Q Λ p h ha (x ⊗ₜ CycKLR.mk k Q λf β v)).val ∈
      lastRedLayerGrade Q Λ G p (i+j)
    rw [lastRedLayerTensor_tmul_mk]
    apply SetLike.GradedMul.mul_mem (A := lastRedLayerGrade Q Λ G p)
    · exact prefixTensor_mem_grade Q Λ G p h (appendRed_mem_grade Q Λ θ G hx)
    · have hE : eSum S (Finset.univ.filter (HasLastRed (ν := θ) (ℓ := ℓ))) ∈ G.grade PWeight 0 :=
        Submodule.sum_mem _ fun a _ => G.e_mem_grade a
      have hv' : blackSuffixReindex Q Λ β v ∈ G.grade B j :=
        SingleRed.reindex_mem_grade β Sum.inl_injective G Black (fun _ => rfl) (fun _ _ => rfl) hv
      simpa only [zero_add] using suffixConcat_tmul_mem_grade Q Λ G p h hE hv'
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [AlgHom.map_smul_of_tower]
    exact Submodule.smul_mem _ c hx

end Categorification.Stendhal

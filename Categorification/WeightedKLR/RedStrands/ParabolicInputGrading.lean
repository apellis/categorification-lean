/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicShuffleAction
import Categorification.WeightedKLR.RedStrands.StendhalTensorGrading
import Categorification.WeightedKLR.RedStrands.LastRedLayerGrading
import Categorification.Algebra.Graded.G0

/-!
# The graded affine input to standardization

Webster, arXiv:1309.3796v2, §5, standardization and Theorem 5.8.
The earlier red family and the final cyclotomic factor give a finite
graded module for the affine parabolic subalgebra, in the grading induced
from the common augmented KLR algebra.
-/

noncomputable section
namespace Categorification.Stendhal
open KLR KLRAlgebra Categorification.Graded DirectSum
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} {k : Type*} [DecidableEq I] [CommRing k] {n m : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin n → I →₀ ℕ) (f : Fin m → Fin n)
  (hf : Function.Injective f) (G : GradingDatum (stendhalQ Q Λ)) (ν : Multiset I)
local notation "c" => Sum.map (id : I → I) f
local notation "μ" => stendhalWeight m ν
local notation "F" => redSubfamilyRelabel Q Λ f hf ν

/-- Restriction of diagram degrees along an inclusion of red labels. -/
def redSubfamilyGrading : GradingDatum (stendhalQ Q (Λ ∘ f)) where
  degX s := G.degX ((c) s)
  degΨ s t := G.degΨ ((c) s) ((c) t)
  degΨ_self s := G.degΨ_self _
  isWeightedHomogeneous s t h := by
    have H := G.isWeightedHomogeneous ((c) s) ((c) t)
      (fun he => h (Sum.map_injective.mpr ⟨Function.injective_id,hf⟩ he))
    cases s <;> cases t <;> exact H
local notation "H" => redSubfamilyGrading Λ f hf G

private theorem subfamilyRelabel_coaction (z : KLRAlgebra k (stendhalQ Q (Λ ∘ f)) μ) :
    G.coaction (relabelHom (F) z) =
      AddMonoidAlgebra.mapAlgHom ℤ (relabelHom (F)) ((H).coaction z) := by
  classical
  induction z using klr_induction with
  | hr r => simp only [AlgHom.commutes]
  | hadd x y hx hy => simp only [map_add,hx,hy]
  | hmul x y hx hy => simp only [map_mul,hx,hy]
  | he s => simp only [relabelHom_e,GradingDatum.coaction_e,AddMonoidAlgebra.mapAlgHom_single]
  | hx a =>
    simp only [relabelHom_x,GradingDatum.coaction_x,map_sum,AddMonoidAlgebra.mapAlgHom_single,
      map_mul,relabelHom_e]
    symm
    apply Fintype.sum_equiv (F).equiv
    intro s
    rfl
  | hψ j =>
    simp only [relabelHom_ψ,GradingDatum.coaction_ψ,map_sum,AddMonoidAlgebra.mapAlgHom_single,
      map_mul,relabelHom_e]
    symm
    apply Fintype.sum_equiv (F).equiv
    intro s
    congr 1
    by_cases hj : j+1 < (μ).card
    · have hj' : j+1 < ((μ).map (c)).card := by simpa using hj
      rw [(H).dψ_of_lt hj,G.dψ_of_lt hj']
      rfl
    · simp [GradingDatum.dψ,hj]

/-- Relabelling along an inclusion of red labels preserves the affine degree. -/
theorem redSubfamilyRelabel_mem_grade {d : ℤ} {z : KLRAlgebra k (stendhalQ Q (Λ ∘ f)) μ}
    (hz : z ∈ (H).grade μ d) : relabelHom (F) z ∈ G.grade ((μ).map (c)) d := by
  rw [GradingDatum.mem_grade, subfamilyRelabel_coaction, (H).mem_grade.mp hz,
    AddMonoidAlgebra.mapAlgHom_single]

/-- Projection to a red subfamily preserves the affine degree. -/
theorem redSubfamilyProjection_mem_grade {d : ℤ} {x}
    (hx : x ∈ G.grade ((μ).map (c)) d) :
    redSubfamilyProjection Q Λ f hf ν x ∈ tensorProductGrade (H) ν d := by
  have Hhom : PreservesGrading ((H).grade μ) (G.grade ((μ).map (c))) (relabelEquiv (F)).toLinearMap := by
    intro i t ht
    change relabelHom (F) t ∈ G.grade _ i
    rw [GradingDatum.mem_grade,subfamilyRelabel_coaction,(H).mem_grade.mp ht,
      AddMonoidAlgebra.mapAlgHom_single]
  have hback := (GradedEquiv.ofPreserves (relabelEquiv (F)).toLinearEquiv Hhom).symm_map_mem' hx
  exact stendhalTensorProjection_mem_grade (Λ ∘ f) (H) ν hback

section Last
variable {ℓ : ℕ} (wt : Fin (ℓ+1) → I →₀ ℕ) (G' : GradingDatum (stendhalQ Q wt))
    (θ β : Multiset I)
local notation "α" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ)
local notation "δ" => Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ)) (stendhalWeight 1 β)
local notation "Earlier" => tensorProductGrade (restrictRedGrading Q wt G') θ
local notation "Black" => restrictBlackGrading Q wt G'
local notation "Final" => CycKLR.grade (Black) (wt (Fin.last ℓ)) β

/-- The final affine projection to the cyclotomic algebra preserves degrees. -/
theorem parabolicLastCyclotomic_mem_grade {d : ℤ} {r} (hr : r ∈ G'.grade δ d) :
    parabolicLastCyclotomic Q wt β r ∈ Final d := by
  let wt₁ := fun _ : Fin 1 => wt (Fin.last ℓ)
  let oneRed := fun _ : Fin 1 => Fin.last ℓ
  have hinj : Function.Injective oneRed := fun _ _ _ => Subsingleton.elim _ _
  let J := redSubfamilyGrading wt oneRed hinj G'
  let σ := SingleRed.cyclotomicEquiv Q wt₁ β
  have hσ : PreservesGrading (Final) (tensorProductGrade J β) σ.toLinearMap := by
    rintro i y ⟨a,ha,rfl⟩
    change SingleRed.cyclotomicProjection Q wt₁ β (CycKLR.mk k Q _ β a) ∈ tensorProductGrade J β i
    rw [SingleRed.cyclotomicProjection,CycKLR.lift_mk]
    apply Graded.mem_map_of_mem
    change StendhalAlgebraAllOrders.ofKLR k Q wt₁ β _ ∈ allOrdersGrade J β i
    apply Graded.mem_map_of_mem
    apply J.castKLR_mem_grade
    apply (blockR _ _).valHom_mem_grade
    exact SingleRed.reindex_mem_grade β Sum.inl_injective J (Black) (fun _ => rfl) (fun _ _ => rfl) ha
  exact (GradedEquiv.ofPreserves σ.toLinearEquiv hσ).symm_map_mem'
    (redSubfamilyProjection_mem_grade wt oneRed hinj G' β hr)

local notation "In" => tensorGrading (G'.grade α) (G'.grade δ)
local notation "Out" => tensorGrading (Earlier) (Final)

/-- The map defining the affine parabolic action on a factor module is graded. -/
theorem parabolicInputMap_mem_grade {d : ℤ} {z} (hz : z ∈ In d) :
    parabolicInputMap Q wt θ β z ∈ Out d := by
  induction hz using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨i,j,x,y,rfl,hx,hy,rfl⟩ := ht
    exact tmul_mem_tensorGrading (redSubfamilyProjection_mem_grade wt Fin.castSucc (Fin.castSucc_injective ℓ) G' θ hx)
      (parabolicLastCyclotomic_mem_grade wt G' β hy)
  | zero => simp
  | add a b _ _ ha hb => simpa using add_mem ha hb
  | smul scalar a _ ha =>
    rw [AlgHom.map_smul_of_tower]
    exact Submodule.smul_mem _ scalar ha

end Last
section Finite
universe w
variable {J : Type} [DecidableEq J] {K : Type w} [Field K] {ℓ : ℕ}
  {P : J → J → MvPolynomial (Fin 2) K} (wt : Fin (ℓ+1) → J →₀ ℕ)
  (D : GradingDatum (stendhalQ P wt)) (θ β : Multiset J)
local notation "leftWeight" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ)
local notation "rightWeight" => Multiset.map (Sum.map (id : J → J) (fun _ : Fin 1 => Fin.last ℓ)) (stendhalWeight 1 β)
local notation "𝓡" => tensorGrading (D.grade leftWeight) (D.grade rightWeight)
local notation "𝓣" => tensorGrading (tensorProductGrade (restrictRedGrading P wt D) θ)
  (CycKLR.grade (restrictBlackGrading P wt D) (wt (Fin.last ℓ)) β)

/-- Restriction of a finite graded factor module along the affine parabolic
input map. Its carrier and graded pieces are those of the factor module. -/
def parabolicInputGFin (N : GFin 𝓣) : GFin 𝓡 := by
  let V := ParabolicInput P wt θ β N.carrier
  let ℳ : ℤ → Submodule K V := N.grading
  let : DirectSum.Decomposition ℳ := N.decomposition
  let : SetLike.GradedSMul 𝓡 ℳ := ⟨fun i j a x ha hx => by
    change parabolicInputMap P wt θ β a • (x : N.carrier) ∈ N.grading (i+j)
    exact N.gradedSMul.smul_mem (parabolicInputMap_mem_grade wt D θ β ha) hx⟩
  let : FiniteDimensional K V := N.finiteDimensional
  exact {carrier := V,grading := ℳ}

end Finite
end Categorification.Stendhal

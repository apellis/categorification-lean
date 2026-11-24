import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleDotDegree
import Categorification.WeightedKLR.RedStrands.LabelTwoExteriorComplexExact
import Categorification.WeightedKLR.RedStrands.LabelTwoOutgoingRows
import Categorification.Algebra.Graded.Idempotent

namespace Categorification.Stendhal.LabelTwo

open KLR KLRAlgebra TypeA Categorification.Graded DirectSum
noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable (k : Type) [Field k]

local notation "ν" => (({()} : Multiset Unit) + {()})
local notation "rawν" => Multiset.replicate 2 ()
local notation "rawW" => fun (_ : Fin 2) => Finsupp.single () 2
local notation "μ" => stendhalWeight 2 ν
local notation "m" => Multiset.card μ
local notation "G" => labelTwoGradingDatum k
local notation "S" => stendhalQ (parameter k) weights
local notation "H" => KLRAlgebra k S μ
local notation "rawH" => KLRAlgebra k (stendhalQ (parameter k) rawW) (stendhalWeight 2 rawν)
local notation "𝒜" => middleTensorGrade k (G)
local notation "πT" => stendhalTensorProjection (Q := parameter k) weights ν
local notation "X₁" => (x (⟨1, by decide⟩ : Fin m) : H)

private def leftCut : Seq μ := labelTwoExteriorLeftLoading
private def rightCut : Seq μ := labelTwoExteriorRightLoading

private def qword : H := e leftCut - X₁ * (ψ 1 : H) * e leftCut

private theorem left_cut_projector_affine_degree_zero : qword k ∈ (G).grade μ 0 := by
  have hc : IsConstOn leftCut 1 2 := by unfold IsConstOn; decide +kernel
  have h := blockIdem_mem_grade (G) (by decide : 1 + 2 ≤ m) hc
  rw [blockIdem, blockElt_two (by decide : 1 + 1 < m)] at h
  exact Submodule.sub_mem _ ((G).e_mem_grade leftCut) h

/-- The complementary exterior idempotent has degree zero in the diagram
algebra's usual type A₁ grading. -/
theorem labelTwoLeftExteriorProjector_degree_zero :
    labelTwoLeftExteriorProjector (parameter k) ∈ 𝒜 0 := by
  change πT (qword k) ∈ 𝒜 0
  exact stendhalTensorProjection_mem_grade weights (G) ν (left_cut_projector_affine_degree_zero k)

/-- The right exterior divided-power projector also has degree zero. -/
theorem labelTwoRightExteriorProjector_affine_degree_zero :
    ((x (⟨2, by decide⟩ : Fin m) : H) * (ψ 2 : H) * e rightCut) ∈ (G).grade μ 0 := by
  have hc : IsConstOn rightCut 2 2 := by unfold IsConstOn; decide +kernel
  have h := blockIdem_mem_grade (G) (by decide : 2 + 2 ≤ m) hc
  rw [blockIdem, blockElt_two (by decide : 2 + 1 < m)] at h
  exact h

/-- The mixed return from the left exterior loading has degree two. -/
theorem labelTwoOutgoingCrossing_affine_degree_two :
    ((ψ 2 : H) * e leftCut) ∈ (G).grade μ 2 := by
  have h := (G).ψ_mul_e_mem_grade' 2 leftCut
  have hd : (G).dψ 2 leftCut = 2 := by
    rw [(G).dψ_of_lt (by decide : 2 + 1 < m) leftCut]
    have h₂ : leftCut.lbl ⟨2, by decide⟩ = .inl () := rfl
    have h₃ : leftCut.lbl ⟨3, by decide⟩ = .inr 1 := rfl
    rw [h₂,h₃]
    change (1 : ℤ) * (weights 1 ()) = 2
    simp [weights]
  exact hd ▸ h

private theorem orderedRawMiddle : IsRedOrdered labelTwoMiddleLoading := by
  unfold IsRedOrdered
  decide +kernel

local notation "rawS" => leftStandard (parameter k) rawW labelTwoMiddleLoading orderedRawMiddle
local notation "rawV" => rawS ⧸ LinearMap.range (labelTwoMiddleDotSumEnd (parameter k))
local notation "rawGen" => leftStandardUnit (parameter k) rawW labelTwoMiddleLoading orderedRawMiddle
local notation "gbar" => (Submodule.Quotient.mk rawGen : rawV)
local notation "d" => labelTwoMiddleExteriorDifferential (parameter k)

/-- The outgoing map sends the middle quotient generator to degree two in the
actual complementary exterior projective. -/
theorem labelTwoOutgoingGenerator_degree_two :
    (d gbar).val ∈ 𝒜 2 := by
  have h := labelTwo_outgoing_applyRaw (parameter k) (1 : rawH)
  simp only [tensorOfKLR, map_one, one_smul, one_mul] at h
  have hg : (d gbar).val = πT ((ψ 2 * e leftCut) * qword k : H) := h
  have hp := SetLike.mul_mem_graded (labelTwoOutgoingCrossing_affine_degree_two k)
    (left_cut_projector_affine_degree_zero k)
  have hp' : ((ψ 2 * e leftCut) * qword k : H) ∈ (G).grade μ 2 := by
    simpa only [add_zero] using hp
  exact hg.symm ▸ stendhalTensorProjection_mem_grade weights (G) ν hp'

local notation "A" => TensorProductAlgebra k (parameter k) weights ν
local notation "M" => Standard k
local notation "𝓜" => middleStandardGrade k (G)
local notation "QPlus" => LinearMap.range (diagramPlus k)
local notation "E" => exteriorMiddleQuotientEquiv k
local notation "g" => leftStandardUnit (parameter k) weights loading loading_ordered

private theorem normalizedOutgoing_generator_mem_grade :
    (normalizedOutgoing k ((QPlus).mkQ g)).val ∈ 𝒜 2 := by
  have h : (E).symm ((QPlus).mkQ g) = gbar :=
    (E).symm_apply_eq.mpr (exteriorMiddleQuotientEquiv_mk_unit k).symm
  change (d ((E).symm ((QPlus).mkQ g))).val ∈ 𝒜 2
  rw [h]
  exact labelTwoOutgoingGenerator_degree_two k

set_option maxHeartbeats 1200000 in
/-- The actual outgoing crossing, applied to the class of any homogeneous
middle-standard vector, raises its degree by two in the exterior ideal. -/
theorem labelTwoOutgoing_mem_grade {i : ℤ} {z : M} (hz : z ∈ 𝓜 i) :
    (normalizedOutgoing k ((QPlus).mkQ z)).val ∈ 𝒜 (i + 2) := by
  let eval : A →ₗ[k] M :=
    { toFun := fun a => a • g
      map_add' := fun a b => add_smul a b g
      map_smul' := fun c a => smul_assoc c a g }
  let Gm := middleStandardGFin k (G)
  let : Decomposition 𝓜 := Gm.decomposition
  have heval : PreservesGrading 𝒜 𝓜 eval := by
    intro j a ha
    change a • g ∈ 𝓜 j
    have h : a • g ∈ 𝓜 (j + 0) :=
      Gm.gradedSMul.smul_mem ha (middleStandardGenerator_mem_grade k)
    simpa only [add_zero] using h
  obtain ⟨a,ha⟩ := leftStandard_exists_smul_unit (Q := parameter k) (Λ := weights)
    loading loading_ordered z
  have h₀ : (decompose 𝓜 (eval a) i).val = eval (decompose 𝒜 a i) :=
    decompose_map heval a i
  have h₁ : (decompose 𝓜 (eval a) i).val = z := by
    rw [show eval a = z from ha.symm, decompose_of_mem_same _ hz]
  have hza : z = (decompose 𝒜 a i).val • g := h₁.symm.trans h₀
  have hmul : (normalizedOutgoing k ((QPlus).mkQ z)).val =
      (decompose 𝒜 a i).val * (normalizedOutgoing k ((QPlus).mkQ g)).val := by
    rw [hza, (QPlus).mkQ.map_smul, (normalizedOutgoing k).map_smul]
    rfl
  exact hmul.symm ▸ SetLike.mul_mem_graded (decompose 𝒜 a i).property
      (normalizedOutgoing_generator_mem_grade k)

local notation "V" => StandardDotSumQuotient k
private abbrev exteriorProjector : A := labelTwoLeftExteriorProjector (parameter k)
local notation "P" => lIdeal (exteriorProjector k)
private abbrev middleMkQ : M →ₗ[A] V := (QPlus).mkQ
local notation "q" => middleMkQ k

/-- The actual middle quotient carries the quotient grading of the standard. -/
def labelTwoMiddleQuotientGrade : ℤ → Submodule k V :=
  Graded.map 𝓜 ((q).restrictScalars k)

local instance : Decomposition 𝓜 := (middleStandardGFin k (G)).decomposition

/-- The dot-sum image is homogeneous because the dot-sum map has degree two. -/
theorem labelTwoDotSumImage_isHomogeneous :
    (QPlus : Submodule A M).IsHomogeneous 𝓜 := by
  apply Graded.isHomogeneous_range (ℳ := Graded.shift 𝓜 2)
  intro i x hx
  change x ∈ 𝓜 (i - 2) at hx
  simpa only [sub_add_cancel] using (mem_homGrade.mp (diagramPlus_degree_two k) hx)

/-- The homogeneous quotient grading gives a direct-sum decomposition. -/
@[instance_reducible] def labelTwoMiddleQuotientDecomposition : Decomposition (labelTwoMiddleQuotientGrade k) := by
  apply Graded.mapDecomposition (π := (q).restrictScalars k) (QPlus).mkQ_surjective
  intro x hx i
  change q x = 0 at hx
  change q _ = 0
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (labelTwoDotSumImage_isHomogeneous k i ((Submodule.Quotient.mk_eq_zero _).mp hx))

/-- The quotient grading is compatible with the action of the diagram algebra. -/
instance labelTwoMiddleQuotient_gradedSMul :
    SetLike.GradedSMul 𝒜 (labelTwoMiddleQuotientGrade k) := by
  let : SetLike.GradedSMul 𝒜 𝓜 := (middleStandardGFin k (G)).gradedSMul
  exact Graded.gradedSMul_map 𝒜 (fun a x => (q).map_smul a x)

/-- The exterior projective has the inherited grading of its regular ideal. -/
def labelTwoLeftExteriorGrade : ℤ → Submodule k P :=
  Graded.submodule 𝒜 P

/-- The homogeneous exterior idempotent gives a graded projective ideal. -/
@[instance_reducible] def labelTwoLeftExteriorDecomposition : Decomposition (labelTwoLeftExteriorGrade k) := by
  apply Graded.submoduleDecomposition
  exact Graded.leftIdeal_isHomogeneous (labelTwoLeftExteriorProjector_degree_zero k)

/-- The outgoing crossing between the actual quotient and projective has internal degree two. -/
theorem labelTwoOutgoing_degree_two :
    normalizedOutgoing k ∈ homGrade A (labelTwoMiddleQuotientGrade k)
      (labelTwoLeftExteriorGrade k) 2 := by
  intro i y hy
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
  exact labelTwoOutgoing_mem_grade k hx

end
end Categorification.Stendhal.LabelTwo

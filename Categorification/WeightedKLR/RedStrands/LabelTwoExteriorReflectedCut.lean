/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoExteriorProjectiveSpan
import Categorification.WeightedKLR.RedStrands.LabelTwoEndpointFlagDetection
import Categorification.WeightedKLR.RedStrands.BoundaryHomReflection
import Categorification.WeightedKLR.RedStrands.LabelTwoExteriorDegrees

/-!
# The reflected cut of the label-two exterior projective

The complementary exterior projector is degree zero. Horizontal reflection
selects its first-dot translate, which spans a nonzero line in diagram degree two.
-/

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA MulOpposite
noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {k : Type} [Field k] (param : Unit → Unit → MvPolynomial (Fin 2) k)
local notation "ν" => Multiset.replicate 2 ()
local notation "μ" => stendhalWeight 2 ν
local notation "m" => Multiset.card μ
local notation "wt" => fun (_ : Fin 2) => Finsupp.single () 2
local notation "H" => KLRAlgebra k (stendhalQ param wt) μ
local notation "T" => TensorProductAlgebra k param wt ν
local notation "π" => tensorOfKLR param wt ν
local notation "C" => labelTwoExteriorLeftLoading
local notation "X₁" => (x (⟨1, by decide⟩ : Fin m) : H)
local notation "X₂" => (x (⟨2, by decide⟩ : Fin m) : H)
local notation "p" => labelTwoLeftExteriorProjector param
local notation "u" => (π X₁ * p)
local notation "γ" => (ψ 1 : H)
local notation "E" => π (e C : H)
private abbrev reflection : T →ₐ[k] Tᵐᵒᵖ := tensorReflect
local notation "R" => reflection param

private theorem proj_mul (a b : H) : π (a * b) = π a * π b := by
  simp only [tensorOfKLR, map_mul]

private theorem proj_add (a b : H) : π (a + b) = π a + π b := by
  simp only [tensorOfKLR,map_add]

private theorem proj_dot₂_eq_neg : π X₂ * p = -u := by
  have h := congrArg (· * p) (labelTwo_leftExterior_dot_relations param).1
  rw [proj_mul, proj_add, zero_mul, mul_assoc, labelTwoLeftExteriorProjector_fixed, add_mul, add_comm] at h
  exact eq_neg_iff_add_eq_zero.mpr h

private theorem proj_dot₁_sq : π X₁ * u = 0 := by
  have h := congrArg (· * p) (labelTwo_leftExterior_dot_relations param).2
  rw [proj_mul, proj_mul, zero_mul, mul_assoc, labelTwoLeftExteriorProjector_fixed] at h
  rw [mul_assoc (π X₂), proj_dot₂_eq_neg param, mul_neg, neg_eq_zero] at h
  have h' : π X₁ * (π X₂ * p) = 0 := by
    rw [← mul_assoc, ← proj_mul, x_mul_x, proj_mul, mul_assoc, h]
  rwa [proj_dot₂_eq_neg param, mul_neg, neg_eq_zero] at h'

private theorem e_cross_comm : E * π γ = π γ * E := by
  rw [← proj_mul, ← proj_mul, ψ_mul_e]
  have hc : sadj m 1 • C = C := by decide +kernel
  rw [hc]

private theorem e_dot_comm : E * π X₁ = π X₁ * E := by
  rw [← proj_mul, ← proj_mul, e_mul_x]

private theorem e_dot_fixed : E * u = u := by
  rw [← mul_assoc, e_dot_comm param, mul_assoc, labelTwoLeftExteriorProjector_fixed]

private theorem refined_reflect : (R p).unop = E - E * (π γ * π X₁) := by
  let word : H := e C - X₁ * γ * e C
  have h := congrArg unop
    (tensorReflect_projection (Q := param) (Λ := wt) («ν» := ν) word)
  change (R p).unop = π (hflip word) at h
  unfold word at h
  rw [h]
  simp only [hflip_sub, hflip_mul, hflip_e, hflip_ψ, hflip_x, tensorOfKLR, map_sub, map_mul]

private theorem reflected_support : (R p).unop * E = (R p).unop := by
  rw [refined_reflect param, sub_mul]
  have he : E * E = E := by rw [← proj_mul, e_mul_self]
  rw [he]
  congr 1
  rw [mul_assoc, mul_assoc, ← e_dot_comm param, ← mul_assoc (π γ),
    ← e_cross_comm param]
  simp only [← mul_assoc, he]

private theorem reflected_kills_unit : (R p).unop * p = 0 := by
  rw [refined_reflect param, sub_mul, labelTwoLeftExteriorProjector_fixed,
    mul_assoc E, mul_assoc (π γ), labelTwoLeftExteriorProjector_cross_dot,
    labelTwoLeftExteriorProjector_fixed, sub_self]

private theorem reflected_fixes_dot : (R p).unop * u = u := by
  rw [refined_reflect param, sub_mul, e_dot_fixed param, mul_assoc E,
    mul_assoc (π γ), proj_dot₁_sq param,mul_zero,mul_zero,sub_zero]

private theorem cut_ordered : IsRedOrdered C := by
  unfold IsRedOrdered
  decide +kernel

/-- The reflected exterior idempotent selects the first-dot line of the actual
complementary exterior projective. -/
theorem labelTwoExterior_reflectedProjector_image (z : lIdeal p) :
    ∃ b : k, (R p).unop * z.val = b • u := by
  obtain ⟨a,b,h⟩ := exterior_projector_cut_span param C cut_ordered cut_ordered []
    (fun w hw => labelTwoExteriorPBWChoice_left w hw) z
  have he : E = seqIdem param wt C cut_ordered := by
    exact stendhalTensorProjection_e wt ν C cut_ordered
  rw [← he, ψw_nil] at h
  simp only [tensorOfKLR, map_one, one_mul] at h
  refine ⟨b,?_⟩
  calc
    _ = (R p).unop * (E * z.val) := by rw [← mul_assoc, reflected_support param]
    _ = _ := by rw [h, mul_add, mul_smul_comm, mul_smul_comm, reflected_kills_unit param,
      reflected_fixes_dot param, smul_zero, zero_add]

private theorem first_dot_ne_zero : u ≠ 0 := by
  intro h
  have hp := labelTwoLeftExteriorProjector_cross_dot param
  rw [h, mul_zero] at hp
  have hz : π ((1 : k) • (e C - X₁ * ψ 1 * e C) +
      (0 : k) • (X₁ * (e C - X₁ * ψ 1 * e C)) : H) = 0 := by
    simp only [one_smul, zero_smul, add_zero]
    exact hp.symm
  exact one_ne_zero (LabelTwoEndpointFlag.outgoing_exterior_coefficients_eq_zero param hz).1

/-- The fixed subspace of the reflected complementary exterior projector. -/
abbrev labelTwoExteriorReflectedLine : Submodule k (lIdeal p) :=
  Graded.idemSubspace k (lIdeal p) ((R p).unop)

/-- The first-dot generator of the reflected exterior line. -/
def labelTwoExteriorReflectedLineGenerator : ↥(labelTwoExteriorReflectedLine param) :=
  ⟨⟨u, by
    change (π X₁ * p) * p = π X₁ * p
    rw [mul_assoc, (isIdempotentElem_labelTwoLeftExteriorProjector param).eq]⟩,
    Subtype.ext (reflected_fixes_dot param)⟩

/-- The reflected complementary exterior projector cuts out an actual
one-dimensional subspace with first-dot generator. -/
def labelTwoExteriorReflectedLineEquiv :
    k ≃ₗ[k] ↥(labelTwoExteriorReflectedLine param) := by
  let f := LinearMap.toSpanSingleton k ↥(labelTwoExteriorReflectedLine param) (labelTwoExteriorReflectedLineGenerator param)
  refine LinearEquiv.ofBijective f ⟨?_,?_⟩
  · apply (injective_iff_map_eq_zero (f := f)).mpr
    intro a h
    have hv : a • u = 0 :=
      congrArg (fun z : ↥(labelTwoExteriorReflectedLine param) => z.val.val) h
    exact (smul_eq_zero.mp hv).resolve_right (first_dot_ne_zero param)
  · intro v
    obtain ⟨a,ha⟩ := labelTwoExterior_reflectedProjector_image param v.val
    refine ⟨a,Subtype.ext (Subtype.ext ?_)⟩
    have h : (R p).unop * v.val.val = v.val.val :=
      congrArg Subtype.val v.property
    exact ha.symm.trans h

open Categorification.Graded LabelTwo

/-- The first-dot line has raw diagram degree two. -/
theorem labelTwoExteriorReflectedLineGenerator_degree_two (k : Type) [Field k] :
    (labelTwoExteriorReflectedLineGenerator (parameter k)).val.val ∈
      middleTensorGrade k (labelTwoGradingDatum k) 2 := by
  let ν' := (({()} : Multiset Unit) + {()})
  let μ' := stendhalWeight 2 ν'
  let H' := KLRAlgebra k (stendhalQ (parameter k) weights) μ'
  let C' : Seq μ' := labelTwoExteriorLeftLoading
  let X : H' := x ⟨1, by decide⟩
  let word : H' := e C' - X * ψ 1 * e C'
  have hc : IsConstOn C' 1 2 := by unfold IsConstOn; decide +kernel
  have hBlock := blockIdem_mem_grade (labelTwoGradingDatum k) (by decide : 1 + 2 ≤ μ'.card) hc
  rw [blockIdem, blockElt_two (by decide : 1 + 1 < μ'.card)] at hBlock
  have hp : word ∈ (labelTwoGradingDatum k).grade μ' 0 :=
    Submodule.sub_mem _ ((labelTwoGradingDatum k).e_mem_grade C') hBlock
  have hdeg : ∀ c : Unit ⊕ Fin 2, (labelTwoGradingDatum k).degX c = 2 := by
    rintro (c | c) <;> rfl
  have hx : X * e C' ∈ (labelTwoGradingDatum k).grade μ' 2 := by
    have hx₀ := (labelTwoGradingDatum k).x_mul_e_mem_grade ⟨1, by decide⟩ C'
    rw [hdeg] at hx₀
    exact hx₀
  have h := SetLike.mul_mem_graded hx hp
  have hh : (X * e C') * word ∈ (labelTwoGradingDatum k).grade μ' 2 := by
    simpa only [add_zero] using h
  let Pj := stendhalTensorProjection (Q := parameter k) weights ν'
  have ht := stendhalTensorProjection_mem_grade weights (labelTwoGradingDatum k) ν' hh
  change Pj ((X * e C') * word) ∈ middleTensorGrade k (labelTwoGradingDatum k) 2 at ht
  have hs : Pj (e C') * Pj word = Pj word :=
    labelTwoLeftExteriorProjector_fixed (parameter k)
  rw [map_mul, map_mul, mul_assoc, hs] at ht
  exact ht

end
end Categorification.Stendhal

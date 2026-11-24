/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoExteriorProjectiveSpan
import Categorification.WeightedKLR.RedStrands.LabelTwoExteriorCokernel
import Categorification.WeightedKLR.RedStrands.LabelTwoEndpointFlagDetection
import Mathlib.Algebra.Category.ModuleCat.Simple

/-!
# The simple augmentation of the label-two exterior complex

Webster, arXiv:1309.3796v2, §8.2, printed page 80. The outgoing image
contains the middle and terminal cuts of the complementary exterior
projective. The quotient is supported at the exterior loading. Its two
spanning vectors are exchanged by the first dot and the black crossing,
which proves that the quotient is simple.
-/

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA
noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {k : Type} [Field k]
variable (param : Unit → Unit → MvPolynomial (Fin 2) k)
local notation "ν" => Multiset.replicate 2 ()
local notation "μ" => stendhalWeight 2 (Multiset.replicate 2 ())
local notation "m" => Multiset.card μ
local notation "wt" => fun (_ : Fin 2) => Finsupp.single () 2
local notation "S" => stendhalQ param wt
local notation "H" => KLRAlgebra k S μ
local notation "T" => TensorProductAlgebra k param wt ν
local notation "π" => tensorOfKLR param wt ν
local notation "A" => labelTwoExteriorRightLoading
local notation "B" => labelTwoMiddleLoading
local notation "C" => labelTwoExteriorLeftLoading
local notation "X₁" => (x (⟨1, by decide⟩ : Fin m) : H)
local notation "qword" => (e C - X₁ * ψ 1 * e C : H)
local notation "p" => labelTwoLeftExteriorProjector param
local notation "u" => (π X₁ * p)
local notation "P" => lIdeal p
local notation "d" => labelTwoMiddleExteriorDifferential param
local notation "aug" => labelTwoExteriorAugmentation param
local notation "K" => labelTwoExteriorCokernel param

private theorem orderedA : IsRedOrdered A := by unfold IsRedOrdered; decide +kernel
private theorem orderedB : IsRedOrdered B := by unfold IsRedOrdered; decide +kernel
private theorem orderedC : IsRedOrdered C := by unfold IsRedOrdered; decide +kernel

local notation "M" => leftStandard param wt B orderedB
local notation "g" => leftStandardUnit param wt B orderedB
local notation "MQ" => M ⧸ LinearMap.range (labelTwoMiddleDotSumEnd param)
local notation "gbar" => (Submodule.Quotient.mk g : MQ)
local notation "W" => (ψ 1 * (ψ 2 * e C) : H)

private theorem proj_mul (a b : H) : π (a * b) = π a * π b := by
  simp only [tensorOfKLR, map_mul]

private theorem projected_loading (s : Seq μ) (hs : IsRedOrdered s) :
    π (e s : H) = seqIdem param wt s hs := by
  apply congrArg (TensorProductAlgebra.mk param wt ν)
  apply Subtype.ext
  exact (StendhalAlgebraAllOrders.e_mul_redOrderedIdem s).trans (ite_eq_left hs)

private theorem projected_unordered (s : Seq μ) (hs : ¬ IsRedOrdered s) :
    π (e s : H) = 0 := by
  have h : orderProjection param wt ν
      (StendhalAlgebraAllOrders.ofKLR k param wt ν (e s)) = 0 := by
    apply Subtype.ext
    exact (StendhalAlgebraAllOrders.e_mul_redOrderedIdem s).trans (ite_eq_right hs)
  rw [tensorOfKLR, h]
  exact (TensorProductAlgebra.mk param wt ν).map_zero

private theorem projected_violated (s : Seq μ) (ho : IsRedOrdered s) (hv : IsViolated s) :
    seqIdem param wt s ho = 0 := by
  change (StendhalAlgebra.violatedIdeal k param wt ν).ringCon.mk' _ = 0
  rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']
  exact TwoSidedIdeal.subset_span ⟨s,ho,hv,rfl⟩

private theorem ordered_nonviolated_loading (s : Seq μ) (ho : IsRedOrdered s)
    (hv : ¬ IsViolated s) : s = A ∨ s = B ∨ s = C := by
  have hb : (s.lbl ⟨0,by decide⟩).isLeft = false := by
    cases h : (s.lbl ⟨0,by decide⟩).isLeft
    · rfl
    · exact (hv ⟨by decide,h⟩).elim
  obtain ⟨w,rfl⟩ := Seq.exists_smul_eq A s
  have h : ∀ w : Equiv.Perm (Fin m), ((w • A).lbl ⟨0,by decide⟩).isLeft = false →
      IsRedOrdered (w • A) → w • A = A ∨ w • A = B ∨ w • A = C := by
    unfold IsRedOrdered
    decide +kernel
  exact h w hb ho

private theorem projected_exterior_dot_fixed :
    π (e C : H) * u = u := by
  rw [← mul_assoc, ← proj_mul, e_mul_x, proj_mul, mul_assoc, labelTwoLeftExteriorProjector_fixed]

private theorem projected_terminal_slide : π W = π (ψw [1,2] : H) * π (e C : H) := by
  simp only [ψw_cons,ψw_nil,mul_one,proj_mul,mul_assoc]

private theorem terminal_output_columns :
    (d (π (ψ 1 * e B : H) • gbar)).val = π (ψw [1,2] : H) * p ∧
    (d (π (ψ 1 * (X₁ * e B) : H) • gbar)).val = π (ψw [1,2] : H) * u := by
  have h := labelTwo_outgoing_terminal_diagram_columns param
  constructor
  · rw [h.1,proj_mul,projected_terminal_slide,mul_assoc]
    exact congrArg (π (ψw [1,2] : H) * ·) (labelTwoLeftExteriorProjector_fixed param)
  · rw [h.2.2.1,proj_mul,projected_terminal_slide,mul_assoc]
    have hx : π (X₁ * qword : H) = u := proj_mul param _ _
    rw [hx]
    exact congrArg (π (ψw [1,2] : H) * ·) (projected_exterior_dot_fixed param)

private theorem middle_output_columns :
    (d gbar).val = π (ψw [2] : H) * p ∧
    (d (π X₁ • gbar)).val = π (ψw [2] : H) * u := by
  constructor
  · have h := labelTwo_outgoing_applyRaw param (1 : H)
    have h' : (d gbar).val = π ((ψ 2 * e C) * qword : H) := by
      simpa only [tensorOfKLR, map_one, one_smul, one_mul] using h
    rw [h',proj_mul,proj_mul,mul_assoc]
    change π (ψ 2 : H) * (π (e C : H) * p) = _
    rw [labelTwoLeftExteriorProjector_fixed]
    simp only [ψw_cons,ψw_nil,mul_one]
  · rw [labelTwo_outgoing_applyRaw]
    have h : (X₁ * (ψ 2 * e C) * qword : H) = (ψ 2 * e C) * (X₁ * qword) := by
      rw [← mul_assoc X₁, x_mul_ψ _ _ (by decide) (by decide)]
      calc
        _ = (ψ 2 : H) * (X₁ * e C) * qword := by simp only [mul_assoc]
        _ = _ := by rw [x_mul_e]; simp only [mul_assoc]
    rw [h,proj_mul,proj_mul,proj_mul,mul_assoc]
    change π (ψ 2 : H) * (π (e C : H) * u) = _
    rw [projected_exterior_dot_fixed param]
    simp only [ψw_cons,ψw_nil,mul_one]

private theorem outgoing_range_of_two_columns (z : P) (a b : k) (x y : MQ)
    (h : z.val = a • (d x).val + b • (d y).val) : z ∈ LinearMap.range (d) := by
  let f := (d).restrictScalars k
  refine ⟨a • x + b • y, Subtype.ext ?_⟩
  have h' : f (a • x + b • y) = a • f x + b • f y :=
    (f.map_add _ _).trans (congrArg₂ (· + ·) (f.map_smul a x) (f.map_smul b y))
  exact (congrArg Subtype.val h').trans h.symm

private theorem outgoing_range_at_middle (z : P) :
    seqIdem param wt B orderedB • z ∈ LinearMap.range (d) := by
  obtain ⟨a,b,h⟩ := exterior_projector_cut_span param B orderedB orderedC [2]
    (fun w hw => labelTwoExteriorPBWChoice_middle w hw) z
  have hh : (seqIdem param wt B orderedB • z).val =
      a • (π (ψw [2] : H) * p) + b • (π (ψw [2] : H) * u) := h
  rw [← (middle_output_columns param).1, ← (middle_output_columns param).2] at hh
  exact outgoing_range_of_two_columns param _ a b gbar (π X₁ • gbar) hh

private theorem outgoing_range_at_terminal (z : P) :
    seqIdem param wt A orderedA • z ∈ LinearMap.range (d) := by
  obtain ⟨a,b,h⟩ := exterior_projector_cut_span param A orderedA orderedC [1,2]
    (fun w hw => labelTwoExteriorPBWChoice_terminal w hw) z
  have hh : (seqIdem param wt A orderedA • z).val =
      a • (π (ψw [1,2] : H) * p) + b • (π (ψw [1,2] : H) * u) := h
  rw [← (terminal_output_columns param).1, ← (terminal_output_columns param).2] at hh
  exact outgoing_range_of_two_columns param _ a b
    (π (ψ 1 * e B : H) • gbar) (π (ψ 1 * (X₁ * e B) : H) • gbar) hh

private theorem exterior_augmentation_off_loading (s : Seq μ) (hs : s ≠ C) (z : P) :
    aug (π (e s : H) • z) = 0 := by
  by_cases ho : IsRedOrdered s
  · rw [projected_loading param s ho]
    by_cases hv : IsViolated s
    · rw [projected_violated param s ho hv, zero_smul, map_zero]
    · rcases ordered_nonviolated_loading s ho hv with h | h | h
      · subst s
        exact (Submodule.Quotient.mk_eq_zero _).mpr (outgoing_range_at_terminal param z)
      · subst s
        exact (Submodule.Quotient.mk_eq_zero _).mpr (outgoing_range_at_middle param z)
      · exact (hs h).elim
  · rw [projected_unordered param s ho,zero_smul,map_zero]

/-- The augmentation is supported at the left exterior loading. -/
theorem labelTwoExteriorAugmentation_loading_project (z : P) :
    aug (π (e C : H) • z) = aug z := by
  classical
  have hsum : (∑ s : Seq μ, π (e s : H)) = (1 : T) := by
    simp only [tensorOfKLR, ← map_sum, sum_e, map_one]
  calc
    _ = ∑ s : Seq μ, aug (π (e s : H) • z) := by
      symm
      apply Finset.sum_eq_single C
      · intro s _ hs
        exact exterior_augmentation_off_loading param s hs z
      · intro h
        exact (h (Finset.mem_univ C)).elim
    _ = _ := by rw [← map_sum, ← Finset.sum_smul, hsum, one_smul]

private def exteriorUnit : P := ⟨p, (isIdempotentElem_labelTwoLeftExteriorProjector param).eq⟩
private def exteriorFirstDot : P := π X₁ • exteriorUnit param

/-- The actual cokernel has the exterior undotted generator and its first dot
as a spanning pair. -/
theorem labelTwoExteriorCokernel_span (v : K) :
    ∃ a b : k, v = a • aug (exteriorUnit param) + b • aug (exteriorFirstDot param) := by
  obtain ⟨z,rfl⟩ := labelTwoExteriorAugmentation_surjective param v
  obtain ⟨a,b,h⟩ := exterior_projector_cut_span param C orderedC orderedC []
    (fun w hw => labelTwoExteriorPBWChoice_left w hw) z
  have h' : (π (e C : H) • z : P) = a • exteriorUnit param + b • exteriorFirstDot param := by
    apply Subtype.ext
    change π (e C : H) * z.val = a • p + b • u
    rw [projected_loading param C orderedC]
    simp only [ψw_nil, tensorOfKLR, map_one, one_mul] at h
    exact h
  refine ⟨a,b,?_⟩
  let f := (aug).restrictScalars k
  exact (labelTwoExteriorAugmentation_loading_project param z).symm.trans <|
    (congrArg (aug) h').trans ((f.map_add _ _).trans
      (congrArg₂ (· + ·) (f.map_smul a _) (f.map_smul b _)))

private theorem middleQuotient_leftExterior_smul_zero (z : MQ) :
    π (e C : H) • z = 0 := by
  let f := (LinearMap.range (labelTwoMiddleDotSumEnd param)).mkQ
  obtain ⟨x,hx⟩ := (LinearMap.range (labelTwoMiddleDotSumEnd param)).mkQ_surjective z
  have hlt : StendhalLT B C := by unfold StendhalLT StendhalLE; decide +kernel
  have hx' : π (e C : H) • x = 0 := by
    rw [projected_loading param C orderedC]
    exact seqIdem_smul_leftStandard_eq_zero param wt orderedB orderedC hlt x
  rw [← hx, ← f.map_smul, hx', f.map_zero]

private theorem exteriorProjector_ne_zero : p ≠ 0 := by
  intro h
  have h' : π ((1 : k) • qword + (0 : k) • (X₁ * qword) : H) = 0 := by
    simp only [one_smul, zero_smul, add_zero]
    exact h
  exact one_ne_zero (LabelTwoEndpointFlag.outgoing_exterior_coefficients_eq_zero param h').1

private theorem exterior_cokernel_unit_ne_zero : aug (exteriorUnit param) ≠ 0 := by
  intro h
  obtain ⟨z,hz⟩ := (Submodule.Quotient.mk_eq_zero _).mp h
  have hc : π (e C : H) • exteriorUnit param = exteriorUnit param :=
    Subtype.ext (labelTwoLeftExteriorProjector_fixed param)
  have hp : exteriorUnit param = 0 := by
    calc
      _ = π (e C : H) • exteriorUnit param := hc.symm
      _ = π (e C : H) • d z := congrArg (π (e C : H) • ·) hz.symm
      _ = d (π (e C : H) • z) := ((d).map_smul _ _).symm
      _ = _ := by rw [middleQuotient_leftExterior_smul_zero, map_zero]
  exact exteriorProjector_ne_zero param (congrArg Subtype.val hp)

private theorem exterior_cokernel_generated (z : K) :
    ∃ t : T, t • aug (exteriorUnit param) = z := by
  obtain ⟨x,rfl⟩ := labelTwoExteriorAugmentation_surjective param z
  refine ⟨x.val, ((aug).map_smul _ _).symm.trans ?_⟩
  exact congrArg (aug) (Subtype.ext x.property)

private theorem exterior_cokernel_black_cross_zero :
    π (ψ 1 : H) • aug (exteriorUnit param) = 0 := by
  have h : π (ψ 1 : H) • exteriorUnit param = 0 :=
    Subtype.ext (labelTwoLeftExteriorProjector_cross_zero param)
  exact ((aug).map_smul _ _).symm.trans ((congrArg (aug) h).trans (aug).map_zero)

private theorem exterior_cokernel_black_cross_dot :
    π (ψ 1 : H) • aug (exteriorFirstDot param) = aug (exteriorUnit param) := by
  have h : π (ψ 1 : H) • exteriorFirstDot param = exteriorUnit param :=
    Subtype.ext (labelTwoLeftExteriorProjector_cross_dot param)
  exact ((aug).map_smul _ _).symm.trans (congrArg (aug) h)

/-- A two-vector span is simple when a crossing extracts the cyclic vector. -/
theorem simple_of_two_vector_span {R L : Type*}
    [Ring R] [Algebra k R] [AddCommGroup L] [Module k L] [Module R L]
    [IsScalarTower k R L] (g₀ g₁ : L) (hunit : g₀ ≠ 0) (cross : R)
    (h₀ : cross • g₀ = 0) (h₁ : cross • g₁ = g₀)
    (hspan : ∀ z : L, ∃ a b : k, z = a • g₀ + b • g₁)
    (hcyclic : ∀ z : L, ∃ r : R, r • g₀ = z) : IsSimpleModule R L := by
  have commute (r : R) (a : k) (x : L) : r • (a • x) = a • (r • x) := by
    rw [← IsScalarTower.algebraMap_smul R a x, ← mul_smul,
      ← Algebra.commutes a r, mul_smul, IsScalarTower.algebraMap_smul]
  have undo (a : k) (ha : a ≠ 0) (x : L) :
      algebraMap k R a⁻¹ • (a • x) = x := by
    rw [IsScalarTower.algebraMap_smul, smul_smul, inv_mul_cancel₀ ha, one_smul]
  apply isSimpleModule_iff_toSpanSingleton_surjective.mpr
  refine ⟨⟨⟨g₀,0,hunit⟩⟩,?_⟩
  intro x hx z
  obtain ⟨a,b,hx'⟩ := hspan x
  have hgen : ∃ s : R, s • x = g₀ := by
    by_cases hb : b = 0
    · have hx₀ : x = a • g₀ := by simpa only [hb,zero_smul,add_zero] using hx'
      have ha : a ≠ 0 := by
        intro h
        exact hx (by simpa only [h,zero_smul] using hx₀)
      refine ⟨algebraMap k R a⁻¹, ?_⟩
      rw [hx₀,undo a ha]
    · have hcross : cross • x = b • g₀ := by
        rw [hx', smul_add, commute, commute, h₀, h₁, smul_zero, zero_add]
      refine ⟨algebraMap k R b⁻¹ * cross, ?_⟩
      rw [mul_smul,hcross,undo b hb]
  obtain ⟨s,hs⟩ := hgen
  obtain ⟨r,hr⟩ := hcyclic z
  refine ⟨r*s,?_⟩
  change (r*s) • x = z
  rw [mul_smul,hs,hr]

set_option maxHeartbeats 750000 in
/-- The augmentation of the actual exterior complex is a simple module,
supported on the left exterior loading. -/
theorem labelTwoExteriorCokernel_simple :
    CategoryTheory.Simple (ModuleCat.of T K) := by
  apply simple_iff_isSimpleModule.mpr
  exact simple_of_two_vector_span (k := k) (R := T) (L := K)
    (aug (exteriorUnit param)) (aug (exteriorFirstDot param))
    (exterior_cokernel_unit_ne_zero param) (π (ψ 1 : H))
    (exterior_cokernel_black_cross_zero param) (exterior_cokernel_black_cross_dot param)
    (labelTwoExteriorCokernel_span param) (exterior_cokernel_generated param)

end
end Categorification.Stendhal

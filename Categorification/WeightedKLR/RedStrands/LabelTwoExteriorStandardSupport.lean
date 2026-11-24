/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoExteriorMiddleMap
import Categorification.WeightedKLR.RedStrands.LoadingCutPBW
import Categorification.WeightedKLR.RedStrands.RedBlackCrossingInjective
import Categorification.WeightedKLR.RedStrands.BoundaryHomReflection

/-!
# The right exterior divided standard at label two

Webster, arXiv:1309.3796v2, §8.2, printed page 80. Only the terminal
loading acts on this standard. Its divided-power summand is spanned by
the projected generator and the translate by the black crossing.
-/

namespace Categorification.Stendhal
open KLR KLRAlgebra TypeA

noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {k : Type} [Field k] (param : Unit → Unit → MvPolynomial (Fin 2) k)
local notation "ν" => Multiset.replicate 2 ()
local notation "μ" => stendhalWeight 2 (Multiset.replicate 2 ())
local notation "wt" => fun (_ : Fin 2) => Finsupp.single () 2
local notation "S" => stendhalQ param wt
local notation "H" => KLRAlgebra k S μ
local notation "T" => TensorProductAlgebra k param wt ν
local notation "π" => tensorOfKLR param wt ν
local notation "A" => labelTwoExteriorRightLoading
local notation "B" => labelTwoMiddleLoading
local notation "m" => Multiset.card μ
local notation "X₂" => (x (⟨2, by decide⟩ : Fin m) : H)
local notation "X₃" => (x (⟨3, by decide⟩ : Fin m) : H)

private theorem a_ordered : IsRedOrdered A := by unfold IsRedOrdered; decide +kernel
private theorem b_ordered : IsRedOrdered B := by unfold IsRedOrdered; decide +kernel
local notation "start" => leftStandard param wt A a_ordered

private theorem strict_of_ne (s : KLR.Seq μ) (hs : IsRedOrdered s) (hv : ¬ IsViolated s)
    (hne : s ≠ A) : StendhalLT A s := by
  have firstRed : (s.lbl ⟨0, by decide⟩).isLeft = false := by
    cases he : (s.lbl ⟨0, by decide⟩).isLeft
    · rfl
    · exact (hv ⟨by decide, he⟩).elim
  obtain ⟨w, rfl⟩ := KLR.Seq.exists_smul_eq A s
  have cases : ∀ v : Equiv.Perm (Fin m), ((v • A).lbl ⟨0, by decide⟩).isLeft = false →
      IsRedOrdered (v • A) → v • A = A ∨ StendhalLT A (v • A) := by
    unfold IsRedOrdered StendhalLT StendhalLE
    decide +kernel
  exact (cases w firstRed hs).resolve_left hne

private theorem project_loading (s : KLR.Seq μ) (hs : IsRedOrdered s) :
    π (e s) = seqIdem param wt s hs := by
  apply congrArg (TensorProductAlgebra.mk param wt ν)
  apply Subtype.ext
  exact (StendhalAlgebraAllOrders.e_mul_redOrderedIdem s).trans (ite_eq_left hs)

private theorem project_unordered (s : KLR.Seq μ) (hs : ¬ IsRedOrdered s) :
    π (e s) = 0 := by
  rw [tensorOfKLR, ← map_zero (TensorProductAlgebra.mk param wt ν)]
  apply congrArg (TensorProductAlgebra.mk param wt ν)
  apply Subtype.ext
  exact (StendhalAlgebraAllOrders.e_mul_redOrderedIdem s).trans (ite_eq_right hs)

/-- The right exterior standard is supported at its own loading. -/
theorem labelTwo_rightStandard_loading_annihilation (s : KLR.Seq μ) (hne : s ≠ A) (z : start) :
    π (e s) • z = 0 := by
  by_cases hs : IsRedOrdered s
  · rw [project_loading param s hs]
    by_cases hv : IsViolated s
    · have hzero : seqIdem param wt s hs = 0 := by
        change (StendhalAlgebra.violatedIdeal k param wt ν).ringCon.mk' _ = 0
        rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']
        exact TwoSidedIdeal.subset_span ⟨s, hs, hv, rfl⟩
      rw [hzero, zero_smul]
    · exact seqIdem_smul_leftStandard_eq_zero param wt a_ordered hs (strict_of_ne s hs hv hne) z
  · rw [project_unordered param s hs, zero_smul]

/-- Every vector of the right exterior standard is fixed by its loading. -/
theorem labelTwo_rightStandard_loading_fixed (z : start) : π (e A) • z = z := by
  classical
  have hsum : (∑ s : KLR.Seq μ, π (e s)) = (1 : T) := by
    simp only [tensorOfKLR, ← map_sum, sum_e, map_one]
  calc
    _ = ∑ s : KLR.Seq μ, π (e s) • z := by
      symm
      apply Finset.sum_eq_single A
      · intro s _ hs
        exact labelTwo_rightStandard_loading_annihilation param s hs z
      · intro h
        exact (h (Finset.mem_univ A)).elim
    _ = z := by rw [← Finset.sum_smul, hsum, one_smul]

private def startAffineAction : H →ₐ[k] Module.End k start :=
  (Algebra.lsmul k k start).comp ((TensorProductAlgebra.mk param wt ν).comp
    ((orderProjection param wt ν).comp (StendhalAlgebraAllOrders.ofKLR k param wt ν)))

local notation "act" => startAffineAction param

private theorem startAffineAction_mul (u v : H) :
    act (u * v) = act u * act v :=
  map_mul (act) u v

private theorem startAffineAction_add (u v : H) :
    act (u + v) = act u + act v :=
  map_add (act) u v

private theorem startAffineAction_loading :
    act (e A) = 1 := by
  apply LinearMap.ext
  exact labelTwo_rightStandard_loading_fixed param

private theorem startAffineAction_middle :
    act (e B) = 0 := by
  apply LinearMap.ext
  exact labelTwo_rightStandard_loading_annihilation param B (by decide)

private theorem start_first_dot_sq_zero :
    act X₂ * act X₂ = 0 := by
  have hsq := ψ_sq (Q := S) 1 (by decide : 2 < m) A
  have hl : (A).lbl ⟨1, by decide⟩ = .inr 1 := rfl
  have hr : (A).lbl ⟨2, by decide⟩ = .inl () := rfl
  simp only [hl, hr, reduceCtorEq, ↓reduceIte, stendhalQ_inr_inl, Finsupp.single_eq_same] at hsq
  have h : (ψ 1 * ψ 1 * e A : H) = X₂ * X₂ * e A := by
    simpa only [ncEval_x2, pow_two, map_mul, MvPolynomial.rename_X, Matrix.cons_val_one,
      Matrix.cons_val_zero, pol_X] using hsq
  have hs : sadj m 1 • A = B := by decide
  have hfactor : (X₂ * X₂ * e A : H) = (ψ 1 * e B) * ψ 1 := by
    rw [← h, ← e_mul_ψ_mul_ψ, ← mul_assoc, e_mul_ψ, hs]
  have hzero : act ((ψ 1 * e B) * ψ 1) = 0 := by
    rw [startAffineAction_mul param, startAffineAction_mul param, startAffineAction_middle param, mul_zero, zero_mul]
  have hresult : act (X₂ * X₂ * e A) = 0 := (congrArg (act) hfactor).trans hzero
  simpa only [startAffineAction_mul param, startAffineAction_loading param, mul_one] using hresult

set_option maxHeartbeats 500000 in
/-- The two black dots and the black crossing on the right exterior standard
satisfy the saturated weight-two nilHecke relations. -/
theorem labelTwo_rightStandard_terminalOperators :
    act X₂ * act X₂ = 0 ∧ act X₃ * act X₃ = 0 ∧
      act X₂ + act X₃ = 0 ∧
      act (ψ 2) * act (ψ 2) = 0 ∧
      act (ψ 2) * act X₂ + act X₂ * act (ψ 2) = 1 := by
  have heq : (A).lbl ⟨2, by decide⟩ = (A).lbl ⟨3, by decide⟩ := rfl
  have dd : act (ψ 2) * act (ψ 2) = 0 := by
    have h := ψ_sq (Q := S) 2 (by decide : 3 < m) A
    simp only [heq, ↓reduceIte] at h
    have hp := congrArg (act) h
    simpa only [map_mul, map_zero, startAffineAction_loading, mul_one] using hp
  have right : act (ψ 2) * act X₂ - act X₃ * act (ψ 2) = 1 := by
    have h := dot_cross_right (Q := S) 2 (by decide : 3 < m) A
    simp only [heq, ↓reduceIte] at h
    have hp := congrArg (act) h
    simpa only [map_mul, map_sub, startAffineAction_loading, mul_one] using hp
  have commute : act X₂ * act X₃ = act X₃ * act X₂ := by
    rw [← map_mul, ← map_mul, x_mul_x]
  have pp := start_first_dot_sq_zero param
  obtain ⟨hsum, hq, hslide⟩ := CycKLR.terminalTwoBlack_relations_of_first_dot_sq_zero
    («S» := Module.End k start) (act X₂) (act X₃) (act (ψ 2)) pp dd right commute
  exact ⟨pp, hq, hsum, dd, hslide⟩

private theorem start_red_dot_zero (a : Fin m) (h : ((A).lbl a).isRight) :
    act (x a) = 0 := by
  have he := StendhalAlgebraAllOrders.x_mul_e_of_red
    (k := k) (Q := param) (Λ := wt) («ν» := ν) a A h
  let proj := (Algebra.lsmul k k start).comp
    ((TensorProductAlgebra.mk param wt ν).comp (orderProjection param wt ν))
  have he' := congrArg (fun a => proj a) he
  have hz : act (x a * e A) = 0 := by
    simpa only [proj, AlgHom.comp_apply, StendhalAlgebraAllOrders.x, StendhalAlgebraAllOrders.e,
      map_mul, map_zero, startAffineAction] using he'
  rwa [map_mul, startAffineAction_loading, mul_one] at hz

local notation "gA" => leftStandardUnit param wt A a_ordered
local notation "v₀" => (act (X₂ * ψ 2 * e A) gA : start)

private theorem start_firstDot_projected_zero :
    act X₂ v₀ = 0 := by
  have hsq := (labelTwo_rightStandard_terminalOperators param).1
  have hh : act X₂ * act (X₂ * ψ 2 * e A) = 0 := by
    rw [startAffineAction_mul param, startAffineAction_mul param, startAffineAction_loading param,
      mul_one, ← mul_assoc, hsq, zero_mul]
  exact congrArg (fun f : Module.End k start => f gA) hh

private theorem start_secondDot_projected_zero :
    act X₃ v₀ = 0 := by
  have hsum := (labelTwo_rightStandard_terminalOperators param).2.2.1
  have hthree : act X₃ = -act X₂ :=
    eq_neg_iff_add_eq_zero.mpr (by rw [add_comm, hsum])
  rw [hthree, LinearMap.neg_apply, start_firstDot_projected_zero, neg_zero]

set_option maxHeartbeats 400000 in
private theorem start_dot_annihilates_projected_gen (a : Fin m) :
    act (x a) v₀ = 0 := by
  fin_cases a
  · rw [start_red_dot_zero param _ (by decide), LinearMap.zero_apply]
  · rw [start_red_dot_zero param _ (by decide), LinearMap.zero_apply]
  · exact start_firstDot_projected_zero param
  · exact start_secondDot_projected_zero param

private theorem scalar_of_dot_action_zero {n : ℕ} {M : Type*}
    [AddCommGroup M] [Module k M] (ev : MvPolynomial (Fin n) k →ₐ[k] Module.End k M)
    (v : M) (hdot : ∀ j : Fin n, ev (MvPolynomial.X j) v = 0)
    (f : MvPolynomial (Fin n) k) :
    ∃ t : k, ev f v = t • v := by
  induction f using MvPolynomial.induction_on with
  | C t =>
      refine ⟨t, ?_⟩
      change ev (algebraMap k (MvPolynomial (Fin n) k) t) v = t • v
      rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply]
      rfl
  | add u v' hu hv =>
      obtain ⟨a,ha⟩ := hu
      obtain ⟨b,hb⟩ := hv
      exact ⟨a+b, by rw [map_add ev, LinearMap.add_apply, ha, hb, add_smul]⟩
  | mul_X u j _ =>
      refine ⟨0, ?_⟩
      rw [map_mul ev, Module.End.mul_apply, hdot, map_zero, zero_smul]

/-- On the exterior projected generator every dot polynomial acts by a scalar. -/
theorem labelTwo_rightStandard_polynomial_scalar (f : MvPolynomial (Fin m) k) :
    ∃ t : k, act (pol f) v₀ = t • v₀ := by
  let ev : MvPolynomial (Fin m) k →ₐ[k] Module.End k start := (act).comp pol
  change ∃ t : k, ev f v₀ = t • v₀
  apply scalar_of_dot_action_zero ev v₀ _ f
  intro j
  change act (pol (MvPolynomial.X j)) v₀ = 0
  rw [pol_X, start_dot_annihilates_projected_gen]

local notation "v₁" => (act (ψ 2) v₀ : start)

private theorem rightExterior_stabilizer (w : Equiv.Perm (Fin m)) (hw : w • A = A) :
    w = 1 ∨ w = wordProd m [2] := by
  have h : ∀ v : Equiv.Perm (Fin m), v • A = A → v = 1 ∨ v = wordProd m [2] := by decide +kernel
  exact h w hw

private theorem startStandard_loading_fixed (z : start) :
    seqIdem param wt A a_ordered • z = z :=
  (congrArg (· • z) (project_loading param A a_ordered).symm).trans
    (labelTwo_rightStandard_loading_fixed param z)


private theorem start_projector_generator :
    labelTwoRightExteriorProjection param gA = v₀ :=
  labelTwoRightExteriorProjection_generator param

set_option maxHeartbeats 700000 in
/-- The actual right exterior divided standard is spanned by its projected
generator and its black-crossing translate. -/
theorem labelTwo_rightExteriorDividedStandard_span
    (z : labelTwoRightExteriorDividedStandard param) :
    ∃ a b : k, z.val = a • v₀ + b • v₁ := by
  let D : Submodule k start := Submodule.span k {v₀, v₁}
  have hz : z.val ∈ D := by
    obtain ⟨v, hv⟩ := z.property
    change labelTwoRightExteriorProjection param v = z.val at hv
    obtain ⟨d, rfl⟩ := leftStandard_exists_smul_unit A a_ordered v
    rw [← hv, map_smul, start_projector_generator]
    have hcut : (seqIdem param wt A a_ordered * d) • v₀ ∈ D := by
      apply loading_mul_smul_mem_of_projected_PBW (M := start) param wt
        (fun w => ⟨isReduced_canWord m w,wordProd_canWord m w⟩)
        a_ordered a_ordered v₀ (startStandard_loading_fixed param v₀) D _ d
      intro w hw f
      obtain ⟨t,ht⟩ := labelTwo_rightStandard_polynomial_scalar param f
      have hfixed : act (e A) v₀ = v₀ := labelTwo_rightStandard_loading_fixed param v₀
      change act (ψw (canWord m w) * pol f * e A) v₀ ∈ D
      rw [startAffineAction_mul param, startAffineAction_mul param, Module.End.mul_apply,
        Module.End.mul_apply, hfixed, ht, map_smul]
      rcases rightExterior_stabilizer w hw with h | h
      · have hw' : canWord m w = [] := by rw [h, canWord_one]
        rw [hw',ψw_nil,map_one]
        change t • v₀ ∈ D
        exact D.smul_mem t (Submodule.subset_span (Set.mem_insert _ _))
      · have hw' : canWord m w = [2] := by
          rw [h, wordProd_singleton, canWord_sadj («m» := m) (a := 2) (by decide)]
        rw [hw',ψw_cons,ψw_nil,mul_one]
        exact D.smul_mem t (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    rwa [mul_smul, startStandard_loading_fixed] at hcut
  change z.val ∈ Submodule.span k ({v₀, v₁} : Set start) at hz
  rw [Submodule.mem_span_pair] at hz
  obtain ⟨a, b, hab⟩ := hz
  exact ⟨a, b, hab.symm⟩

private abbrev rightExteriorReflection : T →ₐ[k] Tᵐᵒᵖ := tensorReflect

local notation "D" => act (ψ 2 : H)
local notation "Y" => act X₂

private theorem projected_operator : act (X₂ * ψ 2 * e A) = Y * D := by
  rw [map_mul, map_mul, startAffineAction_loading, mul_one]

private theorem reflected_operator :
    act (hflip (X₂ * ψ 2 * e A)) = D * Y := by
  simp only [hflip_mul, hflip_e, hflip_ψ, hflip_x, map_mul, startAffineAction_loading, one_mul]

private theorem reflected_kills_projected_unit :
    act (hflip (X₂ * ψ 2 * e A)) v₀ = 0 := by
  have hY : Y * Y = 0 := (labelTwo_rightStandard_terminalOperators param).1
  have h : (D * Y) * (Y * D) = 0 := by
    rw [← mul_assoc (D * Y), mul_assoc D Y Y, hY, mul_zero, zero_mul]
  rw [reflected_operator, projected_operator, ← Module.End.mul_apply, h, LinearMap.zero_apply]

set_option maxHeartbeats 850000 in
private theorem reflected_fixes_projected_translate :
    act (hflip (X₂ * ψ 2 * e A)) v₁ = v₁ := by
  have hD : D * D = 0 := (labelTwo_rightStandard_terminalOperators param).2.2.2.1
  have hmix : D * Y + Y * D = 1 := (labelTwo_rightStandard_terminalOperators param).2.2.2.2
  have h : (D * Y) * D = D := calc
    (D * Y) * D = (D * Y + Y * D) * D := by
      rw [add_mul, mul_assoc Y D D, hD, mul_zero, add_zero]
    _ = D := by rw [hmix, one_mul]
  rw [reflected_operator, ← Module.End.mul_apply (D * Y) D v₀, h]


private theorem reflected_projector_formula :
    (rightExteriorReflection param (π (X₂ * ψ 2 * e A))).unop =
      π (hflip (X₂ * ψ 2 * e A : H)) :=
  congrArg MulOpposite.unop
    (tensorReflect_projection (Q := param) (Λ := wt) («ν» := ν) (X₂ * ψ 2 * e A))

/-- The reflected incoming projector fixes the black-crossing translate. -/
theorem labelTwoRightExterior_reflectedProjector_fixes_translate :
    (rightExteriorReflection param (π (X₂ * ψ 2 * e A))).unop • v₁ = v₁ :=
  (congrArg (· • v₁) (reflected_projector_formula param)).trans
    (reflected_fixes_projected_translate param)

set_option maxHeartbeats 850000 in
/-- The reflected right exterior projector acts on the actual divided standard
with image spanned by the black-crossing translate. -/
theorem labelTwoRightExterior_reflectedProjector_image (z : labelTwoRightExteriorDividedStandard param) :
    ∃ b : k, (rightExteriorReflection param (π (X₂ * ψ 2 * e A))).unop • z.val = b • v₁ := by
  obtain ⟨a,b,h⟩ := labelTwo_rightExteriorDividedStandard_span param z
  refine ⟨b,?_⟩
  rw [reflected_projector_formula param]
  change act (hflip (X₂ * ψ 2 * e A)) z.val = _
  have hs : z.val = a • v₀ + b • v₁ := h
  rw [hs, map_add, map_smul, map_smul, reflected_kills_projected_unit,
    reflected_fixes_projected_translate, smul_zero, zero_add]


end
end Categorification.Stendhal

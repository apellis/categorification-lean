/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorLatticeCoordinates
import Categorification.WeightedKLR.RedStrands.OrdinaryShuffleSum
import Categorification.WeightedKLR.RedStrands.LastRedLayerClasses
import Categorification.KLR.CyclotomicWordRestriction

/-!
# Cyclotomic simple characters as rational highest-weight functionals

Webster, arXiv:1309.3796v2, Proposition 3.21 and §4.7, Theorem 4.38.
The one-factor integral comparison extends graded Hom into each simple top
to a rational functional on the highest-weight module. On lowering words
these functionals read the graded dimensions of their loading spaces.
-/

noncomputable section
namespace Categorification.Stendhal.FirstWeight

open KLR KLRAlgebra QuantumGroup QuantumGroup.UDot Categorification.Graded GProj
open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF
open scoped TensorProduct

local notation "LP" => LaurentPolynomial ℤ
local notation "L" => RatFunc ℚ
local notation "v" => (RatFunc.X : L)
private local instance cyclotomicX_neZero : NeZero v := ⟨RatFunc.X_ne_zero⟩
private abbrev inversion := (LaurentPolynomial.invert (R := ℤ)).toRingEquiv
private local instance cyclotomicInversionPair : RingHomInvPair inversion.toRingHom inversion.toRingHom := RingHomInvPair.of_ringEquiv inversion
private local instance cyclotomicVAlgebra : Algebra LP L := KLGamma.vAlgebra
private local instance cyclotomicFractionRing : IsFractionRing LP L := KLGamma.isFractionRing_vAlgebra

variable {I : Type} [DecidableEq I] [Finite I] {k Y : Type*} [Field k] [AddCommGroup Y]
    (C : CartanDatum I) {Q : I → I → MvPolynomial (Fin 2) k} (μ : I →₀ ℕ)
    (hQ : IsRouquierQ C Q) {R : C.toLusztig.RootDatum Y} (wt : Dom R)
    (hwt : ∀ i, (μ i : ℤ) = wt.1 (R.coroot i)) (hR : R.IsXRegular)
local notation "G" => hQ.gradingDatum
local notation "A" => CycKLR k Q (fun i => (Polynomial.X : Polynomial k) ^ μ i)
local notation "D" => CycKLR.grade G μ
local notation "J" => Σ γ : Multiset I, IndecClass (D γ)
local notation "V" => IrreducibleModule R v (Subtype.val wt)
local notation "ι" => DirectSum.lof LP _ (fun γ => K0 (D γ))

/-- The weight datum on the coroot lattice: weights are additive maps on `Y`. -/
def cyclotomicWeightDatum : WeightDatum C (Y →+ ℤ) Y where
  pair := (AddMonoidHom.id (Y →+ ℤ)).flip
  iX := R.root
  iY := R.coroot
  pair_iY_iX := R.root_coroot

local notation "RD" => cyclotomicWeightDatum C (R := R)

/-- The one-factor integral comparison for a dominant weight given on the coroot lattice. -/
abbrev cyclotomicLatticeEquiv : CycKLR.projectiveK0 G μ ≃ₛₗ[inversion.toRingHom] hwIntegral wt :=
  CycKLR.projectiveIntegralEquiv hQ μ RD wt.1 hwt hR

local notation "E" => cyclotomicLatticeEquiv C μ hQ wt hwt hR

private local instance gradedBlock (γ : Multiset I) : HasGdim (D γ) := by
  let := lastRedFinal_finite hQ μ γ
  exact HasGdim.of_finiteDimensional _

omit [Finite I] in
private theorem finiteTop (γ : Multiset I) (b : IndecClass (D γ)) : Module.Finite k b.top := by
  let := lastRedFinal_finite hQ μ γ
  exact (IndecClass.isGradedSimple_top b).finiteDimensional (⊥ : Submodule k (A γ))
    (fun x hx y => by rw [(Submodule.mem_bot _).mp hx,zero_smul])

/-- The finite graded simple top of the projective indexed by a cyclotomic shift class. -/
abbrev cyclotomicSimpleTop (γ : Multiset I) (b : IndecClass (D γ)) : GFin (D γ) :=
  IndecClass.topFin (finiteTop C μ hQ γ) b

omit [Finite I] in
private theorem scalarTop (γ : Multiset I) (b : IndecClass (D γ)) :
    Module.finrank k (endZero (A γ) b.top.grading) = 1 := by
  let := finiteTop C μ hQ γ b
  let := (IndecClass.isGradedSimple_top b).isSimpleModule
  let := (IndecClass.isGradedSimple_top b).nontrivial
  apply finrank_endZero_eq_one_of_forall
  intro f
  obtain ⟨c,hc⟩ := lastRedFinal_scalar hQ μ γ f
  exact ⟨c, LinearMap.ext hc⟩

private theorem eval_eq (c : LP) : algebraMap LP L c = integralLaurentEval c := by
  obtain ⟨d,rfl⟩ := (LaurentPolynomial.invert (R := ℤ)).surjective c
  exact (KLGamma.laurentEval_vQ_invert d).trans (CycKLR.integralEval_invert d).symm

/-- The cyclotomic projective Hom polynomial into the selected simple top. -/
def cyclotomicTopPolynomial (γ : Multiset I) (j : IndecClass (D γ)) : K0 (D γ) →+ LP := by
  let := lastRedFinal_finite hQ μ γ
  exact projectiveHomPolynomial (D γ) (cyclotomicSimpleTop C μ hQ γ j)

private theorem exists_finalTests :
    ∃ t : J → V →ₗ[L] L, (∀ γ j x, t ⟨γ,j⟩ (E x) =
      integralLaurentEval (cyclotomicTopPolynomial C μ hQ γ j (x γ))) ∧
      Function.Injective (fun x : hwIntegral wt => fun j => t j x) := by
  let finite : ∀ γ : Multiset I, Module.Finite k (A γ) := lastRedFinal_finite hQ μ
  let : SMul LP V := (hwLaurentModule wt).toDistribMulAction.toDistribSMul.toSMul
  let : IsScalarTower LP L V := ⟨fun c a x => by
    rw [Algebra.smul_def, mul_smul]
    exact (congrArg (fun z : L => z • (a • x)) (eval_eq c)).trans (hw_laurent_smul_eq wt c (a • x)).symm⟩
  obtain ⟨t,ht,hi⟩ := exists_totalTopTests (s := D) E (finiteTop C μ hQ) (scalarTop C μ hQ)
  exact ⟨t,fun γ j x => (ht γ j x).trans (eval_eq _), hi⟩

/-- The rational functional extending the cyclotomic graded simple character.
Its restriction to the integral lattice is canonical. -/
def cyclotomicTopTest : J → V →ₗ[L] L := (exists_finalTests C μ hQ wt hwt hR).choose

local notation "test" => cyclotomicTopTest C μ hQ wt hwt hR

/-- The value on an integral class is the Laurent evaluation of its Hom polynomial
in the component indexed by the simple. -/
theorem cyclotomicTopTest_hom (γ : Multiset I) (j : IndecClass (D γ)) (x : CycKLR.projectiveK0 G μ) :
    test ⟨γ,j⟩ (E x) =
      integralLaurentEval (cyclotomicTopPolynomial C μ hQ γ j (x γ)) :=
  (exists_finalTests C μ hQ wt hwt hR).choose_spec.1 γ j x

/-- The family of simple characters separates the points of the integral highest-weight lattice. -/
theorem cyclotomicTopTest_separates : Function.Injective (fun x : hwIntegral wt => fun j => test j x) :=
  (exists_finalTests C μ hQ wt hwt hR).choose_spec.2

/-- Highest-weight vector corresponding to one indecomposable projective in a specified block. -/
def cyclotomicBasisPoint (j : J) : V := (E (ι j.1 (K0.of j.2.rep))).val

private theorem span_lattice_image {P U Z : Type*} [AddCommGroup P] [Module LP P]
    [AddCommGroup U] [Module LP U] {W : Submodule LP U} (e : P ≃ₛₗ[inversion.toRingHom] W)
    (B : Module.Basis Z LP P) : Submodule.span LP (Set.range (fun j => (e (B j)).val)) = W := by
  let g := W.subtype.comp e.toLinearMap
  calc
    _ = Submodule.map g (Submodule.span LP (Set.range B)) := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    _ = W := by rw [B.span_eq, Submodule.map_top, LinearMap.range_comp, e.range,
      Submodule.map_top, W.range_subtype]

/-- The images of the cyclotomic projective basis in all black contents span
the one-factor integral highest-weight lattice. -/
theorem span_cyclotomicBasisPoint :
    Submodule.span LP (Set.range (cyclotomicBasisPoint C μ hQ wt hwt hR)) = hwIntegral wt := by
  have hu : ∀ i j, i ≠ j → IsUnit (polyInY (Q i j)).leadingCoeff := fun i j hij => by
    obtain ⟨c,hc,he⟩ := hQ.polyInY_leading i j hij
    rw [he]
    exact hc.map Polynomial.C
  have he := span_lattice_image (E) (CycKLR.projectiveK0Basis G μ hu)
  have hpoints : (fun j : J => (E (CycKLR.projectiveK0Basis G μ hu j)).val) =
      cyclotomicBasisPoint C μ hQ wt hwt hR := by
    funext ⟨γ,j⟩
    rw [CycKLR.projectiveK0Basis_apply]
    rfl
  rwa [hpoints] at he

open scoped Classical in
/-- Projective basis vectors and simple characters are dual over all black contents. -/
theorem cyclotomicTopTest_point (j j' : J) :
    test j (cyclotomicBasisPoint C μ hQ wt hwt hR j') = if j = j' then 1 else 0 := by
  classical
  rcases j with ⟨γ,j⟩
  rcases j' with ⟨δ,b⟩
  rw [cyclotomicBasisPoint, cyclotomicTopTest_hom]
  let := lastRedFinal_finite hQ μ γ
  unfold cyclotomicTopPolynomial
  by_cases h : δ = γ
  · subst δ
    simp only [DirectSum.lof_eq_of, DirectSum.of_eq_same]
    have hp := projectiveCharacter_topFin (D γ) (finiteTop C μ hQ γ) (scalarTop C μ hQ γ)
      j (K0.of b.rep)
    change LaurentPolynomial.invert (projectiveHomPolynomial _ _ _) = _ at hp
    apply_fun (LaurentPolynomial.invert (R := ℤ)).symm at hp
    rw [LaurentPolynomial.invert.symm_apply_apply] at hp
    rw [hp, ← K0.indecBasis_apply, Module.Basis.repr_self]
    by_cases hb : j = b <;> simp [hb]
  · rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ (Ne.symm h), map_zero, map_zero, ite_eq_right]
    exact fun e => h (congrArg Sigma.fst e).symm

local notation "act" => fun i => Algebra.lsmul L L V (F R v i)
local notation "highest" => IrreducibleModule.hwv R v (Subtype.val wt)
local notation "word" => CycKLR.sequenceClass hQ μ
local notation "π" => CycKLR.mk k Q (fun i => (Polynomial.X : Polynomial k) ^ μ i)

omit [DecidableEq I] [Finite I] in
private theorem suffixOp_snoc {M : Type*} [AddCommGroup M] [Module L M]
    (a : I → Module.End L M) (s : List I) (i : I) :
    ordinarySuffixOp a (s ++ [i]) = a i * ordinarySuffixOp a s := by
  induction s with
  | nil => simp [ordinarySuffixOp]
  | cons _ s ih => simp only [List.cons_append, ordinarySuffixOp, ih, mul_assoc]

/-- The integral comparison sends an ordinary word class to the lowered highest-weight vector. -/
theorem cyclotomicWord_image (s : List I) : (E (word s)).val = ordinarySuffixOp act s highest := by
  induction s using List.reverseRecOn with
  | nil =>
    have hv := CycKLR.projectiveIntegralEquiv_val hQ μ RD wt.1 hwt hR (word [])
    rw [CycKLR.sequenceClass, (G).clsW_nil] at hv
    rw [CycKLR.sequenceClass, (G).clsW_nil]
    exact hv.trans (CycKLR.projectiveHighestWeightEquiv_vacuum μ RD wt.1 hwt hQ hR)
  | append_singleton s i ih =>
    rw [CycKLR.sequenceClass_append, suffixOp_snoc]
    exact (CycKLR.projectiveIntegralEquiv_lower hQ μ RD wt.1 hwt hR i (word s)).trans
      (congrArg (fun x : V => F R v i • x) ih)

/-- The cyclotomic projective of a sequence idempotent. -/
abbrev cyclotomicWordProjective {γ : Multiset I} (s : Seq γ) : GProj (D γ) :=
  GProj.ofIdempotent (π γ (e s)) ((show IsIdempotentElem (e (Q := Q) s) from e_mul_self s).map (π γ))
    (Graded.mem_map_of_mem _ (π γ).toLinearMap ((G).e_mem_grade s))

omit [Finite I] in
/-- The ordinary word class is the class of the cyclotomic word projective in its block. -/
theorem cyclotomicSequenceClass_at (s : List I) {γ : Multiset I} (h : (s : Multiset I) = γ) :
    word s = ι γ (K0.of (cyclotomicWordProjective C μ hQ (Seq.ofList s h))) := by
  subst γ
  change CycKLR.totalQuotientK0 G μ ((G).clsW s) = _
  rw [show CycKLR.totalQuotientK0 G μ ((G).clsW s) =
    ι (s : Multiset I) (CycKLR.quotientK0 G μ _ (K0.of ((G).projP (Seq.ofList s rfl)))) from
    CycKLR.totalQuotientK0_lof ..]
  exact congrArg _ (CycKLR.quotientK0_ofIdempotent G μ _ _ _)

/-- At an ordinary lowering word of its black content, the rational test is
the Laurent evaluation of the graded dimension of the simple's loading space. -/
theorem cyclotomicTopTest_word (s : List I) {γ : Multiset I} (h : (s : Multiset I) = γ)
    (j : IndecClass (D γ)) :
    test ⟨γ,j⟩ (ordinarySuffixOp act s highest) =
      integralLaurentEval (gdimPoly (idem j.top.grading (π γ (e (Seq.ofList s h))))) := by
  let := lastRedFinal_finite hQ μ γ
  rw [← cyclotomicWord_image C μ hQ wt hwt hR, cyclotomicTopTest_hom, cyclotomicTopPolynomial,
    cyclotomicSequenceClass_at C μ hQ s h,
    DirectSum.lof_eq_of, DirectSum.of_eq_same]
  apply congrArg integralLaurentEval
  exact projectiveHomPolynomial_ofIdempotent (D γ) (cyclotomicSimpleTop C μ hQ γ j)
    ((show IsIdempotentElem (e (Q := Q) (Seq.ofList s h)) from e_mul_self _).map (π γ))
    (Graded.mem_map_of_mem _ (π γ).toLinearMap ((G).e_mem_grade _))

/-- Every ordinary lowering word from a different black content pairs to zero. -/
theorem cyclotomicTopTest_word_of_ne (s : List I) {γ : Multiset I} (h : (s : Multiset I) ≠ γ)
    (j : IndecClass (D γ)) : test ⟨γ,j⟩ (ordinarySuffixOp act s highest) = 0 := by
  rw [← cyclotomicWord_image C μ hQ wt hwt hR, cyclotomicTopTest_hom,
    cyclotomicSequenceClass_at C μ hQ s rfl,
    DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ (Ne.symm h), map_zero, map_zero]

end Categorification.Stendhal.FirstWeight

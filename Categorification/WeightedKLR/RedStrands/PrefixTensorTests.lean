/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorLatticeCoordinates
import Categorification.WeightedKLR.RedStrands.TensorShuffleCriterion
import Categorification.WeightedKLR.RedStrands.AbsoluteSimple

/-!
# Simple-top tests on the preceding tensor factors

Webster, arXiv:1309.3796v2, §4.7, Theorem 4.38. In the induction on the
number of red factors, an identification of the earlier projective
lattice supplies rational tests of each earlier content. Under the change
to the bar coproduct, each test evaluates on the ordinary tensor word as
the graded dimension of its loading in the corresponding simple top.
-/

noncomputable section
namespace Categorification.Stendhal.FirstWeight
open KLR QuantumGroup LieLean LieLean.QuantumGroup.GrandLoop LusztigF Categorification.Graded GProj
local notation "LP" => LaurentPolynomial ℤ
local notation "L" => RatFunc ℚ
private abbrev inversion := (LaurentPolynomial.invert (R := ℤ)).toRingEquiv
local instance : RingHomInvPair inversion.toRingHom inversion.toRingHom := RingHomInvPair.of_ringEquiv inversion

variable {I k Y : Type*} [Field k] [DecidableEq I] [Finite I] [AddCommGroup Y] {ℓ : ℕ}
    {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin ℓ → I →₀ ℕ) (C : CartanDatum I)
    (hQ : IsRouquierQ C Q) {R : C.toLusztig.RootDatum Y} (wt : Fin ℓ → Dom R) (hR : R.IsXRegular)
local notation "G" => stendhalGradingDatum Λ hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)
local notation "s" => tensorProductGrade G
local notation "Ps" => fun β : Multiset I => K0 (s β)
local notation "J" => Σ β : Multiset I, IndecClass (s β)

private local instance blockGdim (β : Multiset I) : HasGdim (s β) := by
  let := tensorProductAlgebra_finite Λ β hQ
  exact HasGdim.of_finiteDimensional _

omit [Finite I] in
private theorem prefixTopFinite (β : Multiset I) (b : IndecClass (s β)) : Module.Finite k b.top := by
  let := tensorProductAlgebra_finite Λ β hQ
  exact (IndecClass.isGradedSimple_top b).finiteDimensional (⊥ : Submodule k (TensorProductAlgebra k Q Λ β))
    (fun a ha m => by rw [(Submodule.mem_bot k).mp ha, zero_smul])

omit [Finite I] in
private theorem prefixEnd (i : Multiset I) (b : IndecClass (s i)) : Module.finrank k (endZero (TensorProductAlgebra k Q Λ i) b.top.grading) = 1 := by
    let := tensorProductAlgebra_finite Λ i hQ
    let := prefixTopFinite Λ C hQ i b
    let := (IndecClass.isGradedSimple_top b).isSimpleModule
    let := (IndecClass.isGradedSimple_top b).nontrivial
    apply finrank_endZero_eq_one_of_forall
    intro f
    obtain ⟨c,hc⟩ := exists_scalar_of_simple Λ i hQ f
    exact ⟨c,LinearMap.ext hc⟩

/-- Simple top at one black content of the preceding tensor factors. -/
def prefixSimpleTop (j : J) : GFin (s j.1) := IndecClass.topFin (prefixTopFinite Λ C hQ j.1) j.2

private theorem coeffEval (c : LP) : laurentEval vQ c = integralLaurentEval c := by
  obtain ⟨d,rfl⟩ := (LaurentPolynomial.invert (R := ℤ)).surjective c
  rw [KLGamma.laurentEval_vQ_invert, CycKLR.integralEval_invert]

/-- Graded Hom polynomial into a chosen earlier simple top. -/
def prefixHom (j : J) (x : K0 (s j.1)) : LP := by
  let := tensorProductAlgebra_finite Λ j.1 hQ
  exact projectiveHomPolynomial (s j.1) (prefixSimpleTop Λ C hQ j) x

attribute [local instance] KLGamma.vAlgebra

private theorem testTower {M : Type*} [AddCommGroup M] [Module L M] [Module LP M]
    (h : ∀ (c : LP) (x : M), c • x = integralLaurentEval c • x) : IsScalarTower LP L M := by
  refine ⟨fun c a x => ?_⟩
  rw [Algebra.smul_def, mul_smul, h]
  exact congrArg (fun z : L => z • (a • x)) (coeffEval c)

variable (e : DirectSum (Multiset I) (fun β => K0 (tensorProductGrade
  (stendhalGradingDatum Λ hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)) β)) ≃ₛₗ[inversion.toRingHom] integralTensor wt)

/-- Rational simple-top coordinates after conjugating the tensor coproduct. -/
theorem exists_prefixTopTests :
    ∃ t : J → TensorSpace wt →ₗ[L] L, ∀ j x,
      t j ((tensorCoproductEquiv hR wt).symm (e x)) =
        integralLaurentEval (prefixHom Λ C hQ j (x j.1)) := by
  let := testTower (tensor_laurent_smul wt)
  let (i : Multiset I) := tensorProductAlgebra_finite Λ i hQ
  obtain ⟨t,ht,_⟩ := exists_totalTopTests s e (prefixTopFinite Λ C hQ) (prefixEnd Λ C hQ)
  refine ⟨fun j => (t j).comp (tensorCoproductEquiv hR wt).toLinearMap,?_⟩
  rintro ⟨i,j⟩ x
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, ht]
  exact coeffEval _

/-- The rational coordinate indexed by an earlier factor simple. -/
def prefixTopTest := (exists_prefixTopTests Λ C hQ wt hR e).choose

theorem prefixTopTest_apply (j : J) (x : DirectSum (Multiset I) Ps) :
    prefixTopTest Λ C hQ wt hR e j ((tensorCoproductEquiv hR wt).symm (e x)) =
      integralLaurentEval (prefixHom Λ C hQ j (x j.1)) :=
  (exists_prefixTopTests Λ C hQ wt hR e).choose_spec j x

local notation "ι" => DirectSum.lof LP _ Ps

variable (he : ∀ w, e (tensorWordProjectiveClass Λ C hQ w) = integralWordVector (C := C) wt w)

private abbrev earlierOrdinary (w : TensorWord I ℓ) :=
  K0.of (sequenceProj G w.loading w.blocks_redOrdered)

include he
private theorem prefixOrdinaryImage (w : TensorWord I ℓ) :
    barOrdinaryWord w wt = (tensorCoproductEquiv hR wt).symm (e ((ι) _ (earlierOrdinary Λ C hQ w))) := by
  apply (tensorCoproductEquiv hR wt).injective
  rw [tensorCoproductEquiv_ordinary, LinearEquiv.apply_symm_apply, tensorWordVector_factorial]
  change _ = ((e ((ι) _ (K0.of (sequenceProj G (KLRAlgebra.Seq.ofList _ w.blocks_weight) w.blocks_redOrdered)))) : TensorSpace wt)
  rw [tensorWordProjective_factorial Λ C hQ w, map_smul, e.map_smulₛₗ]
  change _ = ((inversion _ • e (tensorWordProjectiveClass Λ C hQ w) : integralTensor wt) : TensorSpace wt)
  rw [he, Submodule.coe_smul, tensor_laurent_smul]
  exact congrArg (fun a : L => a • tensorWordVector w wt) (CycKLR.integralEval_invert _).symm

/-- On the ordinary word of the earlier tensor, its simple-top coordinate
is the graded dimension of the corresponding loading in that simple. -/
theorem prefixTopTest_word (w : TensorWord I ℓ) (b : IndecClass (s w.content.toMultiset)) :
    prefixTopTest Λ C hQ wt hR e ⟨_,b⟩ (barOrdinaryWord w wt) =
      integralLaurentEval (gdimPoly (idem (prefixSimpleTop Λ C hQ ⟨_,b⟩).grading
        (TensorProductAlgebra.mk Q Λ _ (StendhalAlgebra.e w.loading w.blocks_redOrdered)))) := by
  rw [prefixOrdinaryImage Λ C hQ wt hR e he, prefixTopTest_apply]
  apply congrArg integralLaurentEval
  change prefixHom Λ C hQ _ ((DirectSum.of Ps _ (earlierOrdinary Λ C hQ w)) _) = _
  rw [DirectSum.of_eq_same]
  let := tensorProductAlgebra_finite Λ w.content.toMultiset hQ
  exact projectiveHomPolynomial_ofIdempotent _ _ (isIdempotentElem_mk_e w.loading w.blocks_redOrdered)
    (mk_e_mem_tensorProductGrade G _ w.loading w.blocks_redOrdered)

/-- A simple top of another earlier content has zero coordinate on the word. -/
theorem prefixTopTest_word_of_ne (j : J) (w : TensorWord I ℓ) (h : j.1 ≠ w.content.toMultiset) :
    prefixTopTest Λ C hQ wt hR e j (barOrdinaryWord w wt) = 0 := by
  rw [prefixOrdinaryImage Λ C hQ wt hR e he, prefixTopTest_apply]
  change integralLaurentEval (prefixHom Λ C hQ j ((DirectSum.of Ps _ (earlierOrdinary Λ C hQ w)) j.1)) = _
  rw [DirectSum.of_eq_of_ne _ _ _ h]
  let := tensorProductAlgebra_finite Λ j.1 hQ
  change integralLaurentEval (projectiveHomPolynomial (s j.1) _ 0) = _
  rw [map_zero, map_zero]

omit he in
/-- A projective basis point in the preceding bar tensor representation. -/
def prefixBasisPoint (j : J) : TensorSpace wt :=
  (tensorCoproductEquiv hR wt).symm (e ((ι) j.1 (K0.of j.2.rep)))

omit he in
open scoped Classical in
theorem prefixTopTest_point (i j : J) :
    prefixTopTest Λ C hQ wt hR e i (prefixBasisPoint Λ C hQ wt hR e j) = if i = j then 1 else 0 := by
  classical
  rcases i with ⟨a,b⟩
  rcases j with ⟨a',b'⟩
  rw [prefixBasisPoint, prefixTopTest_apply]
  change integralLaurentEval (prefixHom Λ C hQ ⟨a,b⟩ ((DirectSum.of Ps a' (K0.of b'.rep)) a)) = _
  by_cases ha : a = a'
  · subst a'
    rw [DirectSum.of_eq_same]
    let := tensorProductAlgebra_finite Λ a hQ
    have ht := projectiveCharacter_topFin (s a) (prefixTopFinite Λ C hQ a) (prefixEnd Λ C hQ a) b (K0.indecBasis (s a) b')
    rw [Module.Basis.repr_self, K0.indecBasis_apply] at ht
    have ht' := congrArg (LaurentPolynomial.invert (R := ℤ)) ht
    change LaurentPolynomial.invert (LaurentPolynomial.invert (prefixHom Λ C hQ ⟨a,b⟩ (K0.of b'.rep))) = _ at ht'
    have hinv (v : LP) : LaurentPolynomial.invert (LaurentPolynomial.invert v) = v := LaurentPolynomial.invert.symm_apply_apply v
    rw [hinv] at ht'
    rw [ht']
    by_cases hb : b = b'
    · subst b'
      simp
    · simp [hb]
  · rw [DirectSum.of_eq_of_ne _ _ _ ha]
    let := tensorProductAlgebra_finite Λ a hQ
    change integralLaurentEval (projectiveHomPolynomial (s a) _ 0) = _
    have hne : (⟨a,b⟩ : J) ≠ ⟨a',b'⟩ := fun h => ha (congrArg Sigma.fst h)
    rw [map_zero,map_zero,ite_eq_right hne]

omit he in
/-- The rational span of the preceding projective basis points contains the
bar-coproduct image of the whole integral tensor lattice. -/
theorem prefixBasisPoint_span (x : integralTensor wt) :
    (tensorCoproductEquiv hR wt).symm (x : TensorSpace wt) ∈
      Submodule.span L (Set.range (prefixBasisPoint Λ C hQ wt hR e)) := by
  classical
  obtain ⟨y,rfl⟩ := e.surjective x
  let B := DFinsupp.basis (fun i : Multiset I => K0.indecBasis (s i))
  have h := B.mem_span y
  induction h using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨⟨i,j⟩,rfl⟩ := hz
    apply Submodule.subset_span
    refine ⟨⟨i,j⟩,?_⟩
    unfold prefixBasisPoint
    congr 3
    simp [B,DFinsupp.basis,Module.Basis.coe_ofRepr,DirectSum.lof]
    rfl
  | zero => rw [e.map_zero, Submodule.coe_zero, map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb =>
    rw [map_add, Submodule.coe_add, map_add]
    exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    rw [e.map_smulₛₗ, Submodule.coe_smul, tensor_laurent_smul, map_smul]
    exact Submodule.smul_mem _ _ ha

end Categorification.Stendhal.FirstWeight

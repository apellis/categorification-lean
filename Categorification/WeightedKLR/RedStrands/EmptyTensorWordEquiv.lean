/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.EmptyTensor
import Categorification.WeightedKLR.RedStrands.TensorWordRelations

/-!
# The empty tensor word comparison

For the initial case of Webster, arXiv:1309.3796v2, Theorem 4.38, the
empty projective corresponds to the generator of the empty tensor product.
Positive black content vanishes on both sides, and black blocks of
multiplicity zero act by the identity.
-/
noncomputable section
namespace Categorification.Stendhal.FirstWeight

open KLR KLRAlgebra QuantumGroup Categorification.Graded LieLean LieLean.QuantumGroup
  LieLean.QuantumGroup.GrandLoop LusztigF
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

local notation "LP" => LaurentPolynomial ℤ
local notation "L" => RatFunc ℚ
local notation "v" => (RatFunc.X : L)
private local instance emptyWordNeZero : NeZero v := ⟨RatFunc.X_ne_zero⟩
private abbrev invLP := (LaurentPolynomial.invert (R := ℤ)).toRingEquiv
private local instance emptyWordInvPair : RingHomInvPair invLP.toRingHom invLP.toRingHom := RingHomInvPair.of_ringEquiv invLP

variable {I k Y : Type*} [DecidableEq I] [Field k] [AddCommGroup Y]
    {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I)
    (hQ : IsRouquierQ C Q) {R : C.toLusztig.RootDatum Y} [Finite I]
    (wt : Fin 0 → Dom R)

private abbrev vacuumLine := LinearMap.toSpanSingleton LP (integralTensor wt)
  (integralWordVector (C := C) wt .empty)

private theorem vacuumLine_bijective : Function.Bijective (vacuumLine C wt) := by
  constructor
  · intro a b h
    have he := congrArg (fun x : integralTensor wt => PiTensorProduct.isEmptyEquiv (Fin 0)
      (x : TensorSpace wt)) h
    change PiTensorProduct.isEmptyEquiv _ (a • tensorWordVector .empty wt) =
      PiTensorProduct.isEmptyEquiv _ (b • tensorWordVector .empty wt) at he
    rw [tensor_laurent_smul,tensor_laurent_smul,map_smul,map_smul,tensorWordVector,
        PiTensorProduct.isEmptyEquiv_apply_tprod] at he
    exact integralLaurentEval_injective (by simpa using he)
  · rintro ⟨x,hx⟩
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z,_,rfl⟩ := hx
      refine ⟨1,Subtype.ext ?_⟩
      change (1 : LP) • tensorWordVector .empty wt = _
      rw [one_smul,tensorWordVector]
      exact congrArg (PiTensorProduct.tprod L) (Subsingleton.elim _ _)
    | zero => exact ⟨0,map_zero _⟩
    | add a b _ _ ha hb =>
      obtain ⟨r,hr⟩ := ha
      obtain ⟨s,hs⟩ := hb
      exact ⟨r+s,by rw [map_add,hr,hs]; rfl⟩
    | smul a b _ hb =>
      obtain ⟨s,hs⟩ := hb
      exact ⟨a • s,by rw [map_smul,hs]; rfl⟩

local notation "Λ₀" => (Fin.elim0 : Fin 0 → I →₀ ℕ)
local notation "G" => stendhalGradingDatum Λ₀ hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)
local notation "Ps" => fun γ : Multiset I => K0 (tensorProductGrade G γ)

private def emptyComparison : DirectSum (Multiset I) Ps ≃ₛₗ[invLP.toRingHom] integralTensor wt :=
  by
    let σ : LP ≃ₛₗ[invLP.toRingHom] LP := invLP.toSemilinearEquiv
    exact ((emptyTensorK0Equiv Q G).trans σ).trans
      (LinearEquiv.ofBijective (vacuumLine C wt) (vacuumLine_bijective C wt))

omit [Finite I] in
private theorem emptyProjective_regular :
    K0.of (tensorWordProjective Λ₀ C hQ (.empty : TensorWord I 0)) =
      K0.of (GProj.regular (tensorProductGrade G 0)) := by
  classical
  have hf := tensorWordProjective_factorial Λ₀ C hQ (.empty : TensorWord I 0)
  simp only [TensorWord.blackBlocks,KL2.divQFact2,List.map_nil,List.prod_nil,one_smul] at hf
  rw [← hf]
  let s : Seq (stendhalWeight 0 (0 : Multiset I)) := (TensorWord.empty : TensorWord I 0).loading
  have hs : IsRedOrdered s := (TensorWord.empty : TensorWord I 0).blocks_redOrdered
  have huniq (t : Seq (stendhalWeight 0 (0 : Multiset I))) : t = s := by
    apply Subtype.ext
    funext j
    have hj := j.isLt
    simp [stendhalWeight] at hj
  have he : (StendhalAlgebra.e s hs : StendhalAlgebra k Q Λ₀ 0) = 1 := by
    apply KLR.Corner.ext
    change StendhalAlgebraAllOrders.e s = StendhalAlgebraAllOrders.redOrderedIdem k Q Λ₀ 0
    unfold StendhalAlgebraAllOrders.redOrderedIdem
    symm
    refine Finset.sum_eq_single s (fun t _ h => (h (huniq t)).elim) (fun h => ?_)
    apply False.elim
    apply h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs⟩
  have hb := congrArg (TensorProductAlgebra.mk Q Λ₀ (0 : Multiset I)) he
  rw [map_one] at hb
  exact (K0.of_ofIdempotent_congr (𝒜 := tensorProductGrade G 0) hb
    (isIdempotentElem_mk_e s hs) _ (mk_e_mem_tensorProductGrade G 0 s hs) _).trans
      (K0.of_eq_of_iso GProj.ofIdempotentOneIso)

private theorem emptyComparison_word : ∀ w : TensorWord I 0,
    emptyComparison C hQ wt (tensorWordProjectiveClass Λ₀ C hQ w) =
      integralWordVector (C := C) wt w
  | .empty => by
    change vacuumLine C wt (invLP ((tensorProductVacuumK0Equiv G)
      ((DirectSum.component LP _ Ps 0) ((DirectSum.lof LP _ Ps 0)
        (K0.of (tensorWordProjective Λ₀ C hQ .empty)))))) = _
    rw [DirectSum.component.lof_self]
    have hp := congrArg (tensorProductVacuumK0Equiv G) (emptyProjective_regular C hQ)
    rw [tensorProductVacuumK0Equiv_regular] at hp
    erw [hp,map_one]
    exact one_smul _ _
  | .black w i 0 => by
    have hz := blackLower_pow_eq_qfact_smul Λ₀ C hQ i 0
    simp at hz
    rw [← blackDividedLower_tensorWordProjectiveClass,← hz,Module.End.one_apply,
      emptyComparison_word w]
    apply Subtype.ext
    simp [integralWordVector,tensorWordVector,qDivPow_zero']
  | .black w i (n+1) => by
    have hn : (w.black i (n+1)).content.toMultiset ≠ 0 := by
      simp [TensorWord.content,Finsupp.toMultiset_single,Multiset.nsmul_singleton]
    have hz : (emptyTensorK0Equiv Q G) (tensorWordProjectiveClass Λ₀ C hQ (w.black i (n+1))) = 0 := by
      change tensorProductVacuumK0Equiv G ((DirectSum.component LP _ Ps 0)
        ((DirectSum.lof LP _ Ps _) _)) = _
      rw [DirectSum.component.of, dite_eq_right hn,map_zero]
    change vacuumLine C wt (invLP ((emptyTensorK0Equiv Q G) _)) = _
    rw [hz,map_zero,map_zero]
    apply Subtype.ext
    change (0 : TensorSpace wt) = tensorRepresentation wt
      (qDivPow (v ^ C.toLusztig.d i) (n+1) (F R v i)) _
    have hzero : tensorRepresentation wt (qDivPow (v ^ C.toLusztig.d i) (n+1) (F R v i)) = 0 := by
      change (Algebra.ofId L _) (counit R v _) = 0
      simp [qDivPow]
    rw [hzero,LinearMap.zero_apply]

/-- **Webster, arXiv:1309.3796v2, Theorem 4.38**, empty red family: the
Laurent-semilinear identification of the total projective Grothendieck group
with the empty integral tensor sends every divided projective to its tensor word. -/
theorem exists_emptyTensorWordEquiv (Λ : Fin 0 → I →₀ ℕ) :
    ∃ e : DirectSum (Multiset I) (fun β => K0 (tensorProductGrade
      (stendhalGradingDatum Λ hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)) β))
        ≃ₛₗ[invLP.toRingHom] integralTensor wt,
      ∀ w, e (tensorWordProjectiveClass Λ C hQ w) = integralWordVector (C := C) wt w := by
  obtain rfl : Λ = Λ₀ := Subsingleton.elim _ _
  exact ⟨emptyComparison C hQ wt,emptyComparison_word C hQ wt⟩

end Categorification.Stendhal.FirstWeight

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorClassFunctional
import Categorification.WeightedKLR.RedStrands.RightBlackInduction
import Categorification.WeightedKLR.RedStrands.BlackInductionExact
import Categorification.WeightedKLR.RedStrands.TensorFormUnique

/-!
# The lowering functor on class functionals

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §4.6, §4.7,
Theorem 4.38, and Corollary 6.10. The functor `Fᵢ = - ⊗ e' T^λ_{ν+i}` on finite-dimensional
graded right modules (`rightBlackInd`) acts on class functionals by the adjoint of `Fᵢ` for the
form of Proposition 4.33:
`classFunctional (Fᵢ N) = classFunctional N ∘ τ(Fᵢ)` (`classFunctional_rightBlackInd`).

The proof does not use that `N` is projective. Cutting `Fᵢ N` by a loading idempotent `e(t)`
gives `HOM(X_t, N)`, for the dual `X_t` of the projective cut corner `e' T^λ_{ν+i} e(t)`
(`gdimPoly_rightBlackInd_cut`). The class of `X_t` is identified by testing against right
sequence projectives: on those `Fᵢ` is computed by Lemma 4.37 (`rightBlackIndPrincipalIso`),
and the form is nondegenerate (Proposition 4.33).

## Main results

* `classFunctional_congr` : class functionals of isomorphic modules agree.
* `rightTensorModuleEquiv_rightSequence` : `η' [e(s) T^λ] = η [T^λ e(s)]`.
* `ext_rightSequence` : functionals agreeing on all right sequence projectives agree.
* `tau_F_rightSequence` : `τ(Fᵢ) η' [e(t) T^λ] = η' [X_t]`.
* `classFunctional_rightBlackInd` : `classFunctional (Fᵢ N) = classFunctional N ∘ τ(Fᵢ)`.
-/

noncomputable section

namespace Categorification.Stendhal.FirstWeight

open KLR KLRAlgebra KLGamma Categorification.Graded QuantumGroup QuantumGroup.UDot
open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF MulOpposite
open scoped RatFunc

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
local notation "LP" => LaurentPolynomial ℤ
local notation "𝕂" => RatFunc ℚ
local notation "v" => (RatFunc.X : 𝕂)
local notation "ev" => integralLaurentEval
private abbrev invRing : LP ≃+* LP := (LaurentPolynomial.invert (R := ℤ)).toRingEquiv
local instance : NeZero (RatFunc.X : 𝕂) := ⟨RatFunc.X_ne_zero⟩
local instance : RingHomInvPair invRing.toRingHom invRing.toRingHom :=
  RingHomInvPair.of_ringEquiv invRing

variable {I : Type} {k Y : Type*} [DecidableEq I] [Field k] [AddCommGroup Y] [Finite I]
    {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)
    {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular) {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ)
    (wt : Fin ℓ → Dom R) (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i))

local notation "G" => stendhalGradingDatum Λ hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)
local notation "K" => tensorProjectiveGroup C hQ Λ
local notation "Kr" => rightTensorProjectiveGroup C hQ Λ
local notation "η" => tensorModuleEquiv C hQ hR Λ wt hwt
local notation "η'" => rightTensorModuleEquiv C hQ hR Λ wt hwt
local notation "B" => TensorPairing.orderedForm hR wt
local notation "𝒜" ν => oppositeGrade (tensorProductGrade G ν)
local notation "cf" => classFunctional C hQ hR Λ wt hwt
local notation "rseq" => rightSequenceProj G
local notation "τF" i => tensorRepresentation wt (barHom R (rho R v (F R v i)))

variable [∀ ν : Multiset I, Module.Finite k (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ]

/-- Class functionals of isomorphic modules agree. -/
theorem classFunctional_congr (ν : Multiset I) {N N' : GFin (𝒜 ν)} (e : N.Iso N') :
    cf ν N = cf ν N' := by
  refine Lattice.ext_of_lattice (isLattice_integralTensor C hR wt) fun z hz ↦ ?_
  obtain ⟨x, hx⟩ := (η').surjective ⟨z, hz⟩
  have hzx : z = (η' x : TensorSpace wt) := by rw [hx]
  rw [hzx, classFunctional_eta, classFunctional_eta]
  congr 1
  apply toLaurentSeries_injective
  rw [toLaurentSeries_projectiveHomPolynomial, toLaurentSeries_projectiveHomPolynomial,
    pairingRight_hiso e]

/-- A class functional vanishes on the classes of other black contents. -/
theorem classFunctional_lof_of_ne {ν β : Multiset I} (N : GFin (𝒜 ν)) (x : Kr β) (h : β ≠ ν) :
    cf ν N (η' (DirectSum.lof LP _ Kr β x)) = 0 := by
  rw [classFunctional_eta, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne (h := Ne.symm h), map_zero,
    map_zero]

/-- The class functional at a right sequence projective is the graded dimension of the cut. -/
theorem classFunctional_rightSequence (ν : Multiset I) (N : GFin (𝒜 ν))
    (s : Seq (stendhalWeight ℓ ν)) (hs : IsRedOrdered s) :
    cf ν N (η' (DirectSum.lof LP _ Kr ν (K0.of (rseq s hs)))) =
      ev (gdimPoly (idem N.grading (op (TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e s hs))))) := by
  rw [classFunctional_eta, DirectSum.lof_apply]
  exact congrArg ev (projectiveHomPolynomial_ofIdempotent _ N _ _)

omit [∀ ν : Multiset I, Module.Finite k (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ] in
/-- Webster, Lemma 4.35 and Theorem 4.38: the class of the right sequence projective is that of
the left one. -/
theorem rightTensorModuleEquiv_rightSequence (ν : Multiset I) (s : Seq (stendhalWeight ℓ ν))
    (hs : IsRedOrdered s) :
    η' (DirectSum.lof LP _ Kr ν (K0.of (rseq s hs))) =
      η (DirectSum.lof LP _ K ν (K0.of (sequenceProj G s hs))) := by
  rw [rightTensorModuleEquiv, LinearEquiv.trans_apply]
  congr 1
  rw [LinearEquiv.symm_apply_eq, tensorReflectionK0_lof, K0.rightTwistEquiv_of]
  exact congrArg _ (K0.of_eq_of_iso (sequenceProj_rightEquiv G
    (stendhalGradingDatum_degΨ_symm C hQ Λ) s hs)).symm

omit [∀ ν : Multiset I, Module.Finite k (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ] in
/-- **Functionals agreeing on right sequence projectives agree** (Webster, Lemma 4.37 and
Theorem 4.38). A semilinear functional on `V_λ` vanishing at every `η' [e(s) T^λ]` is zero: the
sequence projectives are nonzero multiples of the word projectives, which span the lattice. -/
theorem ext_rightSequence {σ : 𝕂 →+* 𝕂} (f : TensorSpace wt →ₛₗ[σ] 𝕂)
    (h : ∀ (β : Multiset I) (s : Seq (stendhalWeight ℓ β)) (hs : IsRedOrdered s),
      f (η' (DirectSum.lof LP _ Kr β (K0.of (rseq s hs)))) = 0) : f = 0 := by
  have hlat : ∀ z ∈ integralTensor wt, f z = 0 := by
    intro z hz
    obtain ⟨x, hx⟩ := (η).surjective ⟨z, hz⟩
    have hzx : z = (η x : TensorSpace wt) := by rw [hx]
    rw [hzx]
    have hx' : x ∈ Submodule.span LP (Set.range (tensorWordProjectiveClass Λ C hQ)) := by
      rw [span_tensorWordProjectiveClass Λ C hQ]; trivial
    clear hx hzx
    induction hx' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, rfl⟩ := hy
      have hw := h _ (Seq.ofList _ w.blocks_weight) w.blocks_redOrdered
      rw [rightTensorModuleEquiv_rightSequence, tensorWordProjective_factorial, map_smul,
        LinearEquiv.map_smulₛₗ, Submodule.coe_smul] at hw
      change f (ev (invRing (KL2.divQFact2 C w.blackBlocks)) •
        (η (tensorWordProjectiveClass Λ C hQ w) : TensorSpace wt)) = 0 at hw
      rw [map_smulₛₗ, smul_eq_mul] at hw
      have hc : KL2.divQFact2 C w.blackBlocks ≠ 0 := fun h0 =>
        KL2Gamma.qToV_divQFact2_ne_zero C w.blackBlocks (by rw [h0, map_zero])
      have hc' : σ (ev (invRing (KL2.divQFact2 C w.blackBlocks))) ≠ 0 :=
        (map_ne_zero σ).mpr (Lattice.eval_ne_zero fun h0 => hc (invRing.injective (by rw [h0, map_zero])))
      exact (mul_eq_zero.mp hw).resolve_left hc'
    | zero => rw [map_zero, ZeroMemClass.coe_zero, map_zero]
    | add a b _ _ ha hb => rw [map_add, Submodule.coe_add, map_add, ha, hb, add_zero]
    | smul a y _ hy =>
      rw [LinearEquiv.map_smulₛₗ, Submodule.coe_smul]
      change f (ev _ • (η y : TensorSpace wt)) = 0
      rw [map_smulₛₗ, hy, smul_zero]
  ext z
  have hz : z ∈ Submodule.span 𝕂 (integralTensor wt : Set (TensorSpace wt)) := by
    have h := (isLattice_integralTensor C hR wt).span_eq
    change Submodule.span 𝕂 (integralTensor wt : Set (TensorSpace wt)) = ⊤ at h
    rw [h]; trivial
  rw [LinearMap.zero_apply]
  induction hz using Submodule.span_induction with
  | mem y hy => exact hlat y hy
  | zero => exact map_zero f
  | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
  | smul c y _ hy => rw [map_smulₛₗ, hy, smul_zero]

omit [∀ ν : Multiset I, Module.Finite k (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ] in
/-- Webster, §4.6 and Theorem 4.38: on right sequence projectives, `Fᵢ` appends a black strand. -/
theorem F_rightSequence (i : I) (γ : Multiset I) (s : Seq (stendhalWeight ℓ γ))
    (hs : IsRedOrdered s) :
    tensorRepresentation wt (F R v i) (η' (DirectSum.lof LP _ Kr γ (K0.of (rseq s hs)))) =
      (η' (DirectSum.lof LP _ Kr ({i} + γ) (K0.of (rseq (appendBlackLoading i γ s)
        (appendBlackLoading_ordered i γ s hs)))) : TensorSpace wt) := by
  rw [rightTensorModuleEquiv_rightSequence, rightTensorModuleEquiv_rightSequence,
    ← tensorModuleEquiv_F, blackLower_lof, blackIndK0_sequenceProj]

/-- The adjoint of `Fᵢ` against a right sequence projective. -/
theorem orderedForm_rightSequence_tauF (i : I) (γ : Multiset I) (s : Seq (stendhalWeight ℓ γ))
    (hs : IsRedOrdered s) (y : TensorSpace wt) :
    B (η' (DirectSum.lof LP _ Kr γ (K0.of (rseq s hs)))) ((τF i) y) =
      cf ({i} + γ) (rseq (appendBlackLoading i γ s) (appendBlackLoading_ordered i γ s hs)).toGFin
        y := by
  rw [← TensorPairing.orderedForm_adjoint, F_rightSequence, classFunctional_projective]

omit [Finite I] [∀ ν : Multiset I, Module.Finite k (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ] in
private theorem appendBlackOp_rightSequence (i : I) (γ : Multiset I)
    (s : Seq (stendhalWeight ℓ γ)) (hs : IsRedOrdered s) :
    appendBlackOp Q Λ i γ (op (TensorProductAlgebra.mk Q Λ γ (StendhalAlgebra.e s hs))) =
      op (TensorProductAlgebra.mk Q Λ ({i} + γ) (StendhalAlgebra.e (appendBlackLoading i γ s)
        (appendBlackLoading_ordered i γ s hs))) :=
  (appendBlackOp_op Q Λ i γ _).trans (congrArg op (appendBlack_mk_e Q Λ i γ s hs))

private theorem classFunctional_ofIdempotent_congr (ν : Multiset I)
    {e e' : (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ} (h : e = e') (he : IsIdempotentElem e)
    (he0 : e ∈ (𝒜 ν) 0) (he' : IsIdempotentElem e') (he0' : e' ∈ (𝒜 ν) 0) :
    cf ν (GProj.ofIdempotent e he he0).toGFin = cf ν (GProj.ofIdempotent e' he' he0').toGFin := by
  subst h; rfl

/-- **Lemma 4.37 for right modules, on class functionals**: `Fᵢ (e(s) T^λ) ≅ e(s i) T^λ`. -/
theorem classFunctional_rightBlackInd_rightSequence (i : I) (γ : Multiset I)
    (s : Seq (stendhalWeight ℓ γ)) (hs : IsRedOrdered s) :
    cf ({i} + γ) (rightBlackInd G i γ (rseq s hs).toGFin) =
      cf ({i} + γ) (rseq (appendBlackLoading i γ s) (appendBlackLoading_ordered i γ s hs)).toGFin :=
  (classFunctional_congr C hQ hR Λ wt hwt _ (rightBlackIndPrincipalIso G i γ
    (e := op (TensorProductAlgebra.mk Q Λ γ (StendhalAlgebra.e s hs)))
    (congrArg op (isIdempotentElem_mk_e s hs)) (mk_e_mem_tensorProductGrade G γ s hs))).trans
    (classFunctional_ofIdempotent_congr C hQ hR Λ wt hwt _ (appendBlackOp_rightSequence Λ i γ s hs)
      _ _ _ _)

/-- The dual `X_t` of the cut corner `e' T^λ_{ν+i} e(t)`. -/
def cutDual (i : I) (ν : Multiset I) (t : Seq (stendhalWeight ℓ ({i} + ν)))
    (ht : IsRedOrdered t) : GProj (𝒜 ν) :=
  haveI := projective_blackCorner (Q := Q) (Λ := Λ) i ν C hQ
  cornerCutDual G i ν (congrArg op (isIdempotentElem_mk_e t ht))
    (mk_e_mem_tensorProductGrade G _ t ht)

/-- `classFunctional (Fᵢ N) (η' [e(t) T^λ]) = classFunctional N (η' [X_t])`. -/
theorem classFunctional_rightBlackInd_cut (i : I) (ν : Multiset I) (N : GFin (𝒜 ν))
    (t : Seq (stendhalWeight ℓ ({i} + ν))) (ht : IsRedOrdered t) :
    cf ({i} + ν) (rightBlackInd G i ν N) (η' (DirectSum.lof LP _ Kr ({i} + ν) (K0.of (rseq t ht)))) =
      cf ν N (η' (DirectSum.lof LP _ Kr ν (K0.of (cutDual C hQ Λ i ν t ht)))) := by
  have := projective_blackCorner (Q := Q) (Λ := Λ) i ν C hQ
  rw [classFunctional_rightSequence, gdimPoly_rightBlackInd_cut, classFunctional_of]
  rfl

/-- **The class of `X_t`** (Webster, Proposition 4.33 and Lemma 4.37):
`τ(Fᵢ) η' [e(t) T^λ] = η' [X_t]`. -/
theorem tauF_rightSequence (i : I) (ν : Multiset I) (t : Seq (stendhalWeight ℓ ({i} + ν)))
    (ht : IsRedOrdered t) :
    (τF i) (η' (DirectSum.lof LP _ Kr ({i} + ν) (K0.of (rseq t ht)))) =
      (η' (DirectSum.lof LP _ Kr ν (K0.of (cutDual C hQ Λ i ν t ht))) : TensorSpace wt) := by
  rw [← sub_eq_zero]
  refine (TensorPairing.orderedForm_nondegenerate hR wt).2 _ fun x => ?_
  have hf := ext_rightSequence C hQ hR Λ wt hwt ((B).flip ((τF i)
    (η' (DirectSum.lof LP _ Kr ({i} + ν) (K0.of (rseq t ht)))) -
      (η' (DirectSum.lof LP _ Kr ν (K0.of (cutDual C hQ Λ i ν t ht))) : TensorSpace wt)))
    fun γ s hs => by
      rw [LinearMap.flip_apply, map_sub, orderedForm_rightSequence_tauF,
        ← classFunctional_projective,
        ← classFunctional_rightBlackInd_rightSequence C hQ hR Λ wt hwt i γ s hs]
      by_cases hγ : γ = ν
      · subst hγ
        rw [classFunctional_rightBlackInd_cut, sub_self]
      · have h1 : ({i} + ν : Multiset I) ≠ {i} + γ := fun h' => hγ (add_left_cancel h').symm
        rw [classFunctional_lof_of_ne C hQ hR Λ wt hwt _ _ h1,
          classFunctional_lof_of_ne C hQ hR Λ wt hwt _ _ (Ne.symm hγ), sub_self]
  exact LinearMap.congr_fun hf x

/-- `τ(Fᵢ)` kills the classes of black contents without `i`. -/
theorem tauF_rightSequence_of_not_mem (i : I) {β : Multiset I} (hi : i ∉ β)
    (t : Seq (stendhalWeight ℓ β)) (ht : IsRedOrdered t) :
    (τF i) (η' (DirectSum.lof LP _ Kr β (K0.of (rseq t ht)))) = 0 := by
  refine (TensorPairing.orderedForm_nondegenerate hR wt).2 _ fun x => ?_
  have hf := ext_rightSequence C hQ hR Λ wt hwt ((B).flip ((τF i)
    (η' (DirectSum.lof LP _ Kr β (K0.of (rseq t ht))))))
    fun γ s hs => by
      rw [LinearMap.flip_apply, orderedForm_rightSequence_tauF, classFunctional_lof_of_ne]
      rintro rfl
      exact hi (Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton_self i)))
  exact LinearMap.congr_fun hf x

/-- **`Fᵢ` on class functionals** (Webster, arXiv:1309.3796v2, §4.6, Proposition 4.33 and
Theorem 4.38): for every finite-dimensional graded right module `N`,
`classFunctional (Fᵢ N) = classFunctional N ∘ τ(Fᵢ)`, where `τ(Fᵢ)` is the adjoint of `Fᵢ` for the
form of Proposition 4.33. -/
theorem classFunctional_rightBlackInd (i : I) (ν : Multiset I) (N : GFin (𝒜 ν)) :
    cf ({i} + ν) (rightBlackInd G i ν N) = (cf ν N).comp (τF i) := by
  rw [← sub_eq_zero]
  refine ext_rightSequence C hQ hR Λ wt hwt _ fun β t ht => ?_
  rw [LinearMap.sub_apply, LinearMap.comp_apply, sub_eq_zero]
  by_cases hi : i ∈ β
  · obtain ⟨ν', rfl⟩ : ∃ ν', β = {i} + ν' :=
      ⟨β.erase i, by rw [Multiset.singleton_add, Multiset.cons_erase hi]⟩
    rw [tauF_rightSequence]
    by_cases h : ν' = ν
    · subst h
      exact classFunctional_rightBlackInd_cut C hQ hR Λ wt hwt i ν' N t ht
    · have h1 : ({i} + ν' : Multiset I) ≠ {i} + ν := fun h' => h (add_left_cancel h')
      rw [classFunctional_lof_of_ne C hQ hR Λ wt hwt _ _ h1,
        classFunctional_lof_of_ne C hQ hR Λ wt hwt _ _ h]
  · rw [tauF_rightSequence_of_not_mem C hQ hR Λ wt hwt i hi, map_zero,
      classFunctional_lof_of_ne]
    rintro rfl
    exact hi (Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton_self i)))

end Categorification.Stendhal.FirstWeight

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapSpanning
import Categorification.WeightedKLR.Rigidity.RigidityExtHead
import Categorification.WeightedKLR.RedStrands.RepresentationLift

/-!
# The cap bimodule at Webster's coefficient module `L_μ`

Webster, arXiv:1309.3796v3, §7.3, Definition 7.15 and Lemma 7.17. The cap bimodule `K̃^{λ⁺}_λ`
is built from a right module `L` over `T̃^{(μ, μ*)}`; Webster takes `L = L_μ`, the simple head of
the coevaluation projective (Lemma 7.3, `Stendhal.coevaluationHead`), which is a module over the
quotient `T^{(μ, μ*)}`.

We view a right `T^{(μ, μ*)}`-module as a right `T̃^{(μ, μ*)}`-module along the quotient map
(`CupCap.ViaQuotient`), and show that a module on which every cut idempotent acts by zero is
supported on the loadings with `μ` first and `μ*` last
(`CupCap.smul_e_eq_zero_of_not_isCapGood`). The idempotents of the other loadings are either
violated (a black strand left of `μ`), have the red strands in the wrong order, or are cuts
(`μ*` is not the last strand). The head `L_μ` has this property because the cut projectives span
the submodule it is the quotient by (`CupCap.coevaluationHead_smul_cutIdem`). Hence the spanning
step of Lemma 7.17 holds for Webster's `L_μ` with the support hypothesis discharged
(`CupCap.span_canonical_coevaluationHead`).
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR MulOpposite

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section ViaQuotient

variable {I : Type} [DecidableEq I] (k : Type*) [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)
  (Λc : Fin 2 → I →₀ ℕ) (ν₀ : Multiset I) (M : Type*)

/-- A right `T^{(μ, μ*)}`-module, viewed as a right `T̃^{(μ, μ*)}`-module along the quotient map
`T̃^{(μ, μ*)} → T^{(μ, μ*)}`. -/
@[nolint unusedArguments]
def ViaQuotient (k : Type*) [CommRing k] (_Q : I → I → MvPolynomial (Fin 2) k)
    (_Λc : Fin 2 → I →₀ ℕ) (_ν₀ : Multiset I) (M : Type*) : Type _ := M

instance [AddCommGroup M] : AddCommGroup (ViaQuotient k Q Λc ν₀ M) := ‹AddCommGroup M›

instance [AddCommGroup M] [Module (TensorProductAlgebra k Q Λc ν₀)ᵐᵒᵖ M] :
    Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ (ViaQuotient k Q Λc ν₀ M) :=
  Module.compHom M (TensorProductAlgebra.mk Q Λc ν₀).toRingHom.op

variable {k Q Λc ν₀ M} [AddCommGroup M] [Module (TensorProductAlgebra k Q Λc ν₀)ᵐᵒᵖ M]

/-- An element of `M` as an element of `ViaQuotient`. -/
def ViaQuotient.of (v : M) : ViaQuotient k Q Λc ν₀ M := v

theorem ViaQuotient.smul_def (a : StendhalAlgebra k Q Λc ν₀) (v : ViaQuotient k Q Λc ν₀ M) :
    op a • v = (op (TensorProductAlgebra.mk Q Λc ν₀ a) • (show M from v) : M) :=
  rfl

/-- The idempotent of a loading of `(μ, μ*)` that is not of the form `μ ⋯ μ*` is zero in
`T^{(μ, μ*)}` unless the loading is red-ordered and its last strand is not `μ*`; in that case it
is a cut idempotent. -/
theorem mk_cupMap_e_of_not_isCapGood (w : Seq (stendhalWeight 2 ν₀)) (hw : ¬ IsCapGood ν₀ w) :
    TensorProductAlgebra.mk Q Λc ν₀ (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) = 0 ∨
      ∃ s : TwoRedErase.CutLoading ν₀,
        TensorProductAlgebra.mk Q Λc ν₀ (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) =
          TwoRedErase.cutIdem Q Λc ν₀ s := by
  have hRel := tensorRepresentationRelations_projection (k := k) (Q := Q) (Λ := Λc) (ν := ν₀)
  by_cases ho : IsRedOrdered w
  swap
  · exact Or.inl (hRel.unordered w ho)
  have h0 : 0 < Multiset.card (stendhalWeight 2 ν₀) :=
    lt_of_lt_of_le (by norm_num) (two_le_card_stendhalWeight ν₀)
  by_cases hv : IsViolated w
  · exact Or.inl (hRel.violated w ho hv)
  have hfirst : w.lbl ⟨0, h0⟩ = .inr 0 := by
    rcases hl : w.lbl ⟨0, h0⟩ with b | r
    · exact absurd ⟨h0, by rw [hl]; rfl⟩ hv
    · congr 1
      by_contra hr
      have hr1 : r = 1 := by omega
      obtain ⟨a, ha⟩ := exists_lbl_eq_inr w 0
      have ha0 : (⟨0, h0⟩ : Fin _) ≠ a := by
        rintro rfl
        rw [hl, hr1] at ha
        exact absurd (Sum.inr.inj ha) (by decide)
      have hlt : (⟨0, h0⟩ : Fin _) < a := lt_of_le_of_ne (Fin.mk_le_mk.2 (Nat.zero_le _)) ha0
      have := ho _ _ r 0 hlt hl ha
      omega
  have hlast : ¬ HasLastRed (ℓ := 1) w := by
    intro hlr
    apply hw
    refine ⟨hfirst, ?_⟩
    have hc : Multiset.card (stendhalWeight 2 ν₀) - 1 = Multiset.card ν₀ + 1 := by
      simp [stendhalWeight]
    have := hlr
    unfold HasLastRed lastRedPosition at this
    convert this using 2
    · exact Fin.ext hc
    · rfl
  refine Or.inr ⟨⟨⟨w, ho⟩, hlast⟩, ?_⟩
  show _ = TensorProductAlgebra.mk Q Λc ν₀ (StendhalAlgebra.e w ho)
  congr 1
  exact Subtype.ext ((StendhalAlgebraAllOrders.e_mul_redOrderedIdem w).trans (ite_eq_left ho))

/-- **Support of `L` at the ends of the maximum.** A right `T^{(μ, μ*)}`-module on which every cut
idempotent acts by zero, viewed as a `T̃^{(μ, μ*)}`-module, is supported on the loadings whose
first strand is `μ` and whose last strand is `μ*`. -/
theorem smul_e_eq_zero_of_not_isCapGood
    (hcut : ∀ (s : TwoRedErase.CutLoading ν₀) (v : M), op (TwoRedErase.cutIdem Q Λc ν₀ s) • v = 0)
    (w : Seq (stendhalWeight 2 ν₀)) (v : ViaQuotient k Q Λc ν₀ M) (hw : ¬ IsCapGood ν₀ w) :
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0 := by
  rw [ViaQuotient.smul_def]
  rcases mk_cupMap_e_of_not_isCapGood (k := k) (Q := Q) (Λc := Λc) w hw with h | ⟨s, h⟩
  · rw [h, op_zero, zero_smul]
    rfl
  · rw [h]
    exact hcut s v

end ViaQuotient

section Coevaluation

open CycKLR KLRAlgebra QuantumGroup QuantumGroup.UDot

variable {I : Type} [Fintype I] [DecidableEq I] {k : Type*} [Field k] {C : CartanDatum I}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : I → ℕ)
  {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (highest : X)
  (d : List (I × ℕ))

/-- Every cut idempotent acts by zero on the head `L_μ` of the coevaluation projective: the image
of a cut projective lies in the submodule that `L_μ` is the quotient by. -/
theorem coevaluationHead_smul_cutIdem
    (s : TwoRedErase.CutLoading (expandDiv d : Multiset I))
    (v : coevaluationHead Q Λ RD highest d) :
    op (TwoRedErase.cutIdem Q (coevaluationLabels Λ RD highest (expandDiv d)) (expandDiv d) s) •
      v = 0 := by
  induction v using Submodule.Quotient.induction_on with
  | H x =>
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    refine Submodule.subset_span ⟨s, ?_⟩
    change x.val * _ * _ = x.val * _
    rw [unop_op, mul_assoc, (TwoRedErase.isIdempotentElem_cutIdem Q _ _ s).eq]

variable {ℓ : ℕ} (Λ' : Fin ℓ → I →₀ ℕ) (j : ℕ) (hj : j ≤ ℓ) (ν : Multiset I)

/-- **Lemma 7.17, spanning step, at Webster's `L_μ`.** For the head `L_μ` of the coevaluation
projective (Lemma 7.3), if the scalars of (max1) are units, `K̃^{λ⁺}_λ` is spanned by the
canonical generators `a · cap(s, capPos s, v) · z`, `z` a diagram on the strands left of
`λ_{j+1}`. -/
theorem span_canonical_coevaluationHead
    (hκ : ∀ i, IsUnit (cupScalar Q (expandDiv d : Multiset I) i)) :
    canonicalSpan k Q Λ' (coevaluationLabels Λ RD highest (expandDiv d)) j hj ν
      (expandDiv d)
      (ViaQuotient k Q (coevaluationLabels Λ RD highest (expandDiv d)) (expandDiv d)
        (coevaluationHead Q Λ RD highest d)) = ⊤ :=
  span_canonical hκ fun w v hw =>
    smul_e_eq_zero_of_not_isCapGood (coevaluationHead_smul_cutIdem Q Λ RD highest d) w v hw

end Coevaluation

end Categorification.Stendhal.CupCap

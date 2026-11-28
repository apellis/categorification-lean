/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.RigidityExtLastTermExt
import Categorification.WeightedKLR.Rigidity.RigidityExtDualBlock
import Categorification.WeightedKLR.Rigidity.RigidityExtCoevaluationHeadExt
import Categorification.WeightedKLR.RedStrands.TensorFinite

/-!
# Proposition 7.8 for the simple head `L_λ`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.1,
Proposition 7.8: the simple head `L_λ` of the coevaluation wrap projective has a resolution
`0 → M_N → ⋯ → M_1 → M_0 → L_λ → 0`, `N = 2ρ^∨(λ)`, with `M_{N-j}` in the subcategory generated
by the standard modules of level `j` and `M_N ≅ M_λ`. In the repaired reading of
`exists_stdResolution`, `M_n` is a sum of standardizations of finite-dimensional factor modules
at level `N - n`; the last term is `M_λ` by `exists_stdResolution_last`, from Corollary 7.7 and
the semisimplicity of the dual-weight block (`exists_linearEquiv_pi_cycDivProj_coevaluation`).
Corollary 7.9 follows: `Extⁱ(L_λ, M_λ)` is one-dimensional for `i = 2ρ^∨(λ)` and zero otherwise
(`ext_coevaluationHead`, from `ext_stdResolution_last`).
Ungraded; `L_λ` is a left module through the horizontal reflection (`flipLeft`).
-/

universe w

noncomputable section

open CategoryTheory Abelian Limits MulOpposite

namespace Categorification.Stendhal

open KLR

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance] ModuleCat.moduleOfAlgebraModule
  ModuleCat.isScalarTower_of_algebra_moduleCat

variable {I : Type} {k : Type} [DecidableEq I] [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I)

/-- A quotient of a right ideal `e T`, as a left module through the horizontal reflection, is
finite-dimensional when `T` is. -/
theorem finiteDimensional_flipLeft_quotient [Module.Finite k (TensorProductAlgebra k Q Λ ν)]
    {e : TensorProductAlgebra k Q Λ ν} (he : IsIdempotentElem e)
    (N : Submodule (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ (rIdeal e)) :
    FiniteDimensional k (flipLeft Q Λ ν (rIdeal e ⧸ N)) := by
  have : Module.Finite (TensorProductAlgebra k Q Λ ν) (flipLeft Q Λ ν (rIdeal e ⧸ N)) := by
    refine Module.Finite.of_surjective (LinearMap.toSpanSingleton _ _
      (show flipLeft Q Λ ν (rIdeal e ⧸ N) from
        Submodule.Quotient.mk (⟨e, he.eq⟩ : rIdeal e))) fun y => ?_
    induction (show rIdeal e ⧸ N from y) using Submodule.Quotient.induction_on with
    | H x =>
      refine ⟨tensorFlip x.val, ?_⟩
      rw [LinearMap.toSpanSingleton_apply, flipLeft_smul, tensorFlip_tensorFlip]
      change Submodule.Quotient.mk (op x.val • (⟨e, he.eq⟩ : rIdeal e)) = _
      congr 1
      exact Subtype.ext x.2
  exact Module.Finite.trans (TensorProductAlgebra k Q Λ ν) _

end Categorification.Stendhal

namespace Categorification.KLR.CycKLR

open KLRAlgebra Categorification.Graded QuantumGroup QuantumGroup.UDot _root_.Module

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance] ModuleCat.moduleOfAlgebraModule
  ModuleCat.isScalarTower_of_algebra_moduleCat

variable {I : Type} {k : Type} [Fintype I] [DecidableEq I] [Field k] {C : CartanDatum I}
    {Q : I → I → MvPolynomial (Fin 2) k} (hP : IsRouquierQ C Q) (Λ : I → ℕ)
    {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y)
    (highest : X) (hΛ : ∀ i, (Λ i : ℤ) = RD.pair (RD.iY i) highest)
    (hR : (projectiveRootDatum RD).IsXRegular)
    {K H : Type*} [Field K] [ConditionallyCompleteLinearOrder K] [IsStrictOrderedRing K]
    [AddCommGroup H] [Module K H] (P : Matrix.Realization C.toLusztig.cartanMatrix K H)

local notation "Dc" => P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix
local notation "cs" => P.coxeterSystem C.toLusztig.isGeneralizedCartan_cartanMatrix

omit [Fintype I] [DecidableEq I] in
/-- The only loading of a single red strand with no black strands is the vacuum loading. -/
theorem eq_vacuumSeq_one (t : Seq (Stendhal.stendhalWeight 1 (0 : Multiset I))) :
    t = Stendhal.vacuumSeq := by
  apply Seq.word_injective
  rw [Stendhal.word_eq_of_stendhalWeight_one_zero, Stendhal.word_eq_of_stendhalWeight_one_zero]

include hP hΛ hR in
/-- **Webster, arXiv:1309.3796v3, §7.1, Proposition 7.8**, ungraded, in the repaired reading.
Let `w` be a reduced expression of the longest element, `d` the divided coevaluation word of
Definition 7.1, `N = |d̂| = 2ρ^∨(λ)`. The simple head `L_λ` (`coevaluationHead d`, Lemma 7.3)
has a resolution `0 → M_N → ⋯ → M_1 → M_0 → L_λ → 0`, given by short exact sequences
`0 → K_{n+1} → M_n → K_n → 0` with `K_0 = L_λ`, in which `M_n` is a finite sum of
standardizations of finite-dimensional factor modules at the split with `n` black strands right
of the last red strand, `M_n = 0` for `n > N`, and the last term is
`M_N ≅ M_λ = S(T^{λ} e(t) ⊠ R^{λ*} 1_{d̄})`.

Webster states that `M_{N-j}` lies in the subcategory generated by the standards `S^{κ_j}_i`;
here `M_n` is a sum of standardizations of arbitrary finite-dimensional factor modules, which lie
in that subcategory. Under the route hypothesis `hall` of Proposition 7.6. -/
theorem _root_.Categorification.Stendhal.exists_stdResolution_coevaluationHead
    [FiniteDimensional K H] (weight : P.integralWeights)
    (hweight : P.IsDominantIntegral (weight : Module.Dual K H))
    (match_weight : ∀ i, (weight : Module.Dual K H) (P.coroot i) =
      (RD.pair.flip highest ((projectiveRootDatum RD).coroot i) : K))
    (w : List I) (hw : (cs).IsReduced w.reverse)
    (hlong : ∀ i, (cs).IsLeftDescent ((cs).wordProd w.reverse) i)
    (hQ : KLRSymm Q)
    (hall : Stendhal.AllFiniteDeltaInjective Q (coevaluationLabels Λ RD highest
      (expandDiv (Stendhal.coevaluationDividedWord Dc weight w))) hQ)
    (t : Seq (Stendhal.stendhalWeight 1 (0 : Multiset I))) (ht : Stendhal.IsRedOrdered t)
    (h : 0 + Stendhal.wordWt (expandDiv (Stendhal.coevaluationDividedWord Dc weight w)) 0 =
      expandDiv (Stendhal.coevaluationDividedWord Dc weight w))
    [HasExt.{w} (ModuleCat.{0} (Stendhal.TensorProductAlgebra k Q
      (coevaluationLabels Λ RD highest (expandDiv (Stendhal.coevaluationDividedWord Dc weight w)))
      (expandDiv (Stendhal.coevaluationDividedWord Dc weight w))))] :
    ∃ S : ℕ → ShortComplex (ModuleCat.{0} (Stendhal.TensorProductAlgebra k Q
        (coevaluationLabels Λ RD highest (expandDiv (Stendhal.coevaluationDividedWord Dc weight w)))
        (expandDiv (Stendhal.coevaluationDividedWord Dc weight w)))),
      Nonempty ((S 0).X₃ ≅ Stendhal.flipLeft Q _ _ (Stendhal.coevaluationHead Q Λ RD highest
        (Stendhal.coevaluationDividedWord Dc weight w))) ∧
      (∀ n, Nonempty ((S (n + 1)).X₃ ≅ (S n).X₁)) ∧ (∀ n, (S n).ShortExact) ∧
      (∀ n ≤ (expandDiv (Stendhal.coevaluationDividedWord Dc weight w)).length,
        Stendhal.StdSum Q _ hQ
          ((expandDiv (Stendhal.coevaluationDividedWord Dc weight w)).length + 1 - n) (S n).X₂) ∧
      (∀ n, (expandDiv (Stendhal.coevaluationDividedWord Dc weight w)).length < n →
        IsZero (S n).X₂) ∧
      Nonempty ((S (expandDiv (Stendhal.coevaluationDividedWord Dc weight w)).length).X₂ ≅
        Stendhal.tensorStd Q _ hQ h (Stendhal.oldProj Q _ 0 t ht)
          (Stendhal.cycDivProj Q _ (Stendhal.coevaluationDividedWord Dc weight w))) := by
  let d := Stendhal.coevaluationDividedWord Dc weight w
  let Λ' := coevaluationLabels Λ RD highest (expandDiv d)
  obtain rfl := eq_vacuumSeq_one t
  have het : Stendhal.TensorProductAlgebra.mk Q (Λ' ∘ Fin.castSucc) 0
      (Stendhal.StendhalAlgebra.e Stendhal.vacuumSeq ht) = 1 :=
    Stendhal.vacuumSeq_mk_e Q (Λ' ∘ Fin.castSucc)
  have := Stendhal.tensorProductAlgebra_finite Λ' (expandDiv d : Multiset I) hP
  have hz : IsIdempotentElem (Stendhal.TwoRedErase.wrapIdem Q Λ' (expandDiv d)
      (dividedIdem Λ (Q := Q) d)) :=
    (Stendhal.TwoRedErase.wrapIdem_mul Q Λ' _ _ _).trans
      (congrArg _ (isIdempotentElem_dividedIdem Λ d).eq)
  have := Stendhal.finiteDimensional_flipLeft_quotient Q Λ' _ hz
    (Stendhal.coevaluationTrace (Stendhal.TwoRedErase.cutIdem Q Λ' (expandDiv d)))
  obtain ⟨J, _, _, ι, π, hιπ, htot, hcard⟩ := Stendhal.exists_bicone_cycWord_cycDivProj Q Λ' d
  have : Nonempty J := Fintype.card_pos_iff.1 (hcard ▸ Stendhal.prod_factorial_pos d)
  have htop := Stendhal.finrank_ext_standard_coevaluationHead hP Λ RD highest hΛ hR P weight
    hweight match_weight w hw hlong hQ hall _ ht h
  rw [← Multiset.coe_card] at htop
  have hS := Stendhal.exists_stdResolution_last Q Λ' hQ hP hall
    (Stendhal.flipLeft Q Λ' _ (Stendhal.coevaluationHead Q Λ RD highest d))
    (fun s hs hcut y => by
      rw [Stendhal.flipLeft_smul, Stendhal.loadingIdem, Stendhal.tensorFlip_mk_e]
      exact Stendhal.coevaluationHead_cut Q Λ RD highest d s hs hcut _)
    (expandDiv d) h Stendhal.vacuumSeq ht het (Stendhal.cycDivProj Q Λ' d)
    (fun M _ _ _ => exists_linearEquiv_pi_cycDivProj_coevaluation hP RD Λ highest hR P weight
      hweight match_weight w hw hlong M) ι π hιπ htot htop
  obtain ⟨S, h0, hs, he, hstd, hz, hlast, -⟩ := hS
  simp only [Multiset.coe_card] at hstd hz hlast
  exact ⟨S, h0, hs, he, hstd, hz, hlast⟩

include hP hΛ hR in
/-- **Webster, arXiv:1309.3796v3, §7.1, Corollary 7.9**, ungraded. With the notation of
`exists_stdResolution_coevaluationHead`, `Extⁱ(L_λ, M_λ)` is one-dimensional for
`i = N = 2ρ^∨(λ)` and zero otherwise, `M_λ = S(T^{λ} e(t) ⊠ R^{λ*} 1_{d̄})`. Under the route
hypothesis `hall` of Proposition 7.6. -/
theorem _root_.Categorification.Stendhal.ext_coevaluationHead
    [FiniteDimensional K H] (weight : P.integralWeights)
    (hweight : P.IsDominantIntegral (weight : Module.Dual K H))
    (match_weight : ∀ i, (weight : Module.Dual K H) (P.coroot i) =
      (RD.pair.flip highest ((projectiveRootDatum RD).coroot i) : K))
    (w : List I) (hw : (cs).IsReduced w.reverse)
    (hlong : ∀ i, (cs).IsLeftDescent ((cs).wordProd w.reverse) i)
    (hQ : KLRSymm Q)
    (hall : Stendhal.AllFiniteDeltaInjective Q (coevaluationLabels Λ RD highest
      (expandDiv (Stendhal.coevaluationDividedWord Dc weight w))) hQ)
    (t : Seq (Stendhal.stendhalWeight 1 (0 : Multiset I))) (ht : Stendhal.IsRedOrdered t)
    (h : 0 + Stendhal.wordWt (expandDiv (Stendhal.coevaluationDividedWord Dc weight w)) 0 =
      expandDiv (Stendhal.coevaluationDividedWord Dc weight w))
    [HasExt.{w} (ModuleCat.{0} (Stendhal.TensorProductAlgebra k Q
      (coevaluationLabels Λ RD highest (expandDiv (Stendhal.coevaluationDividedWord Dc weight w)))
      (expandDiv (Stendhal.coevaluationDividedWord Dc weight w))))] :
    Module.finrank k (Ext.{w} (Stendhal.flipLeft Q
        (coevaluationLabels Λ RD highest (expandDiv (Stendhal.coevaluationDividedWord Dc weight w))) _ (Stendhal.coevaluationHead Q Λ RD highest
        (Stendhal.coevaluationDividedWord Dc weight w)))
      (Stendhal.tensorStd Q _ hQ h (Stendhal.oldProj Q _ 0 t ht)
        (Stendhal.cycDivProj Q _ (Stendhal.coevaluationDividedWord Dc weight w)))
      (expandDiv (Stendhal.coevaluationDividedWord Dc weight w)).length) = 1 ∧
    ∀ i ≠ (expandDiv (Stendhal.coevaluationDividedWord Dc weight w)).length,
      Subsingleton (Ext.{w} (Stendhal.flipLeft Q
        (coevaluationLabels Λ RD highest (expandDiv (Stendhal.coevaluationDividedWord Dc weight w))) _ (Stendhal.coevaluationHead Q Λ RD highest
          (Stendhal.coevaluationDividedWord Dc weight w)))
        (Stendhal.tensorStd Q _ hQ h (Stendhal.oldProj Q _ 0 t ht)
          (Stendhal.cycDivProj Q _ (Stendhal.coevaluationDividedWord Dc weight w))) i) := by
  let d := Stendhal.coevaluationDividedWord Dc weight w
  let Λ' := coevaluationLabels Λ RD highest (expandDiv d)
  obtain rfl := eq_vacuumSeq_one t
  have het : Stendhal.TensorProductAlgebra.mk Q (Λ' ∘ Fin.castSucc) 0
      (Stendhal.StendhalAlgebra.e Stendhal.vacuumSeq ht) = 1 :=
    Stendhal.vacuumSeq_mk_e Q (Λ' ∘ Fin.castSucc)
  have := Stendhal.tensorProductAlgebra_finite Λ' (expandDiv d : Multiset I) hP
  have hz : IsIdempotentElem (Stendhal.TwoRedErase.wrapIdem Q Λ' (expandDiv d)
      (dividedIdem Λ (Q := Q) d)) :=
    (Stendhal.TwoRedErase.wrapIdem_mul Q Λ' _ _ _).trans
      (congrArg _ (isIdempotentElem_dividedIdem Λ d).eq)
  have := Stendhal.finiteDimensional_flipLeft_quotient Q Λ' _ hz
    (Stendhal.coevaluationTrace (Stendhal.TwoRedErase.cutIdem Q Λ' (expandDiv d)))
  obtain ⟨J, _, _, ι, π, hιπ, htot, hcard⟩ := Stendhal.exists_bicone_cycWord_cycDivProj Q Λ' d
  have : Nonempty J := Fintype.card_pos_iff.1 (hcard ▸ Stendhal.prod_factorial_pos d)
  have htop := Stendhal.finrank_ext_standard_coevaluationHead hP Λ RD highest hΛ hR P weight
    hweight match_weight w hw hlong hQ hall _ ht h
  rw [← Multiset.coe_card] at htop
  have hE := Stendhal.ext_stdResolution_last Q Λ' hQ hP hall (expandDiv d) h Stendhal.vacuumSeq
    ht ι π hιπ htot
    (Stendhal.flipLeft Q Λ' _ (Stendhal.coevaluationHead Q Λ RD highest d))
    (fun s hs hcut y => by
      rw [Stendhal.flipLeft_smul, Stendhal.loadingIdem, Stendhal.tensorFlip_mk_e]
      exact Stendhal.coevaluationHead_cut Q Λ RD highest d s hs hcut _)
    het
    (fun M _ _ _ => exists_linearEquiv_pi_cycDivProj_coevaluation hP RD Λ highest hR P weight
      hweight match_weight w hw hlong M) htop
  obtain ⟨h1, h2⟩ := hE
  rw [Multiset.coe_card] at h1
  exact ⟨h1, fun i hi => h2 i (by rwa [Multiset.coe_card])⟩

local notation "QK" =>
  KL3.Diagram.CL.qCL (KL3.Diagram.CL.CLScalars.kl : KL3.Diagram.CL.CLScalars C k)

include hΛ hR in
/-- **Webster, arXiv:1309.3796v3, §7.1, Proposition 7.8**, ungraded, in the repaired reading, at
the standard Khovanov–Lauda parameters, with no route hypothesis. -/
theorem _root_.Categorification.Stendhal.exists_stdResolution_coevaluationHead_std
    (hP' : IsRouquierQ C QK) (hQs : KLRSymm QK)
    [FiniteDimensional K H] (weight : P.integralWeights)
    (hweight : P.IsDominantIntegral (weight : Module.Dual K H))
    (match_weight : ∀ i, (weight : Module.Dual K H) (P.coroot i) =
      (RD.pair.flip highest ((projectiveRootDatum RD).coroot i) : K))
    (w : List I) (hw : (cs).IsReduced w.reverse)
    (hlong : ∀ i, (cs).IsLeftDescent ((cs).wordProd w.reverse) i)
    (t : Seq (Stendhal.stendhalWeight 1 (0 : Multiset I))) (ht : Stendhal.IsRedOrdered t)
    (h : 0 + Stendhal.wordWt (expandDiv (Stendhal.coevaluationDividedWord Dc weight w)) 0 =
      expandDiv (Stendhal.coevaluationDividedWord Dc weight w))
    [HasExt.{w} (ModuleCat.{0} (Stendhal.TensorProductAlgebra k QK
      (coevaluationLabels Λ RD highest (expandDiv (Stendhal.coevaluationDividedWord Dc weight w)))
      (expandDiv (Stendhal.coevaluationDividedWord Dc weight w))))] :
    ∃ S : ℕ → ShortComplex (ModuleCat.{0} (Stendhal.TensorProductAlgebra k QK
        (coevaluationLabels Λ RD highest (expandDiv (Stendhal.coevaluationDividedWord Dc weight w)))
        (expandDiv (Stendhal.coevaluationDividedWord Dc weight w)))),
      Nonempty ((S 0).X₃ ≅ Stendhal.flipLeft QK _ _ (Stendhal.coevaluationHead QK Λ RD highest
        (Stendhal.coevaluationDividedWord Dc weight w))) ∧
      (∀ n, Nonempty ((S (n + 1)).X₃ ≅ (S n).X₁)) ∧ (∀ n, (S n).ShortExact) ∧
      (∀ n ≤ (expandDiv (Stendhal.coevaluationDividedWord Dc weight w)).length,
        Stendhal.StdSum QK _ hQs
          ((expandDiv (Stendhal.coevaluationDividedWord Dc weight w)).length + 1 - n) (S n).X₂) ∧
      (∀ n, (expandDiv (Stendhal.coevaluationDividedWord Dc weight w)).length < n →
        IsZero (S n).X₂) ∧
      Nonempty ((S (expandDiv (Stendhal.coevaluationDividedWord Dc weight w)).length).X₂ ≅
        Stendhal.tensorStd QK _ hQs h (Stendhal.oldProj QK _ 0 t ht)
          (Stendhal.cycDivProj QK _ (Stendhal.coevaluationDividedWord Dc weight w))) :=
  Stendhal.exists_stdResolution_coevaluationHead hP' Λ RD highest hΛ hR P weight hweight match_weight w hw hlong hQs
    (by
      convert Stendhal.allFiniteDeltaInjective_std
        (Λ := coevaluationLabels Λ RD highest (expandDiv (Stendhal.coevaluationDividedWord Dc
          weight w))) hP' hQs) t ht h

include hΛ hR in
/-- **Webster, arXiv:1309.3796v3, §7.1, Corollary 7.9**, ungraded, at the standard
Khovanov–Lauda parameters, with no route hypothesis. -/
theorem _root_.Categorification.Stendhal.ext_coevaluationHead_std
    (hP' : IsRouquierQ C QK) (hQs : KLRSymm QK)
    [FiniteDimensional K H] (weight : P.integralWeights)
    (hweight : P.IsDominantIntegral (weight : Module.Dual K H))
    (match_weight : ∀ i, (weight : Module.Dual K H) (P.coroot i) =
      (RD.pair.flip highest ((projectiveRootDatum RD).coroot i) : K))
    (w : List I) (hw : (cs).IsReduced w.reverse)
    (hlong : ∀ i, (cs).IsLeftDescent ((cs).wordProd w.reverse) i)
    (t : Seq (Stendhal.stendhalWeight 1 (0 : Multiset I))) (ht : Stendhal.IsRedOrdered t)
    (h : 0 + Stendhal.wordWt (expandDiv (Stendhal.coevaluationDividedWord Dc weight w)) 0 =
      expandDiv (Stendhal.coevaluationDividedWord Dc weight w))
    [HasExt.{w} (ModuleCat.{0} (Stendhal.TensorProductAlgebra k QK
      (coevaluationLabels Λ RD highest (expandDiv (Stendhal.coevaluationDividedWord Dc weight w)))
      (expandDiv (Stendhal.coevaluationDividedWord Dc weight w))))] :
    Module.finrank k (Ext.{w} (Stendhal.flipLeft QK
        (coevaluationLabels Λ RD highest (expandDiv (Stendhal.coevaluationDividedWord Dc weight w))) _ (Stendhal.coevaluationHead QK Λ RD highest
        (Stendhal.coevaluationDividedWord Dc weight w)))
      (Stendhal.tensorStd QK _ hQs h (Stendhal.oldProj QK _ 0 t ht)
        (Stendhal.cycDivProj QK _ (Stendhal.coevaluationDividedWord Dc weight w)))
      (expandDiv (Stendhal.coevaluationDividedWord Dc weight w)).length) = 1 ∧
    ∀ i ≠ (expandDiv (Stendhal.coevaluationDividedWord Dc weight w)).length,
      Subsingleton (Ext.{w} (Stendhal.flipLeft QK
        (coevaluationLabels Λ RD highest (expandDiv (Stendhal.coevaluationDividedWord Dc weight w))) _ (Stendhal.coevaluationHead QK Λ RD highest
          (Stendhal.coevaluationDividedWord Dc weight w)))
        (Stendhal.tensorStd QK _ hQs h (Stendhal.oldProj QK _ 0 t ht)
          (Stendhal.cycDivProj QK _ (Stendhal.coevaluationDividedWord Dc weight w))) i) :=
  Stendhal.ext_coevaluationHead hP' Λ RD highest hΛ hR P weight hweight match_weight w hw hlong hQs
    (by
      convert Stendhal.allFiniteDeltaInjective_std
        (Λ := coevaluationLabels Λ RD highest (expandDiv (Stendhal.coevaluationDividedWord Dc
          weight w))) hP' hQs) t ht h

end Categorification.KLR.CycKLR

end

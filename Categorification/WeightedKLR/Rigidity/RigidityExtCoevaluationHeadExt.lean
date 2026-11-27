/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.RigidityExtCoevaluationExt
import Categorification.WeightedKLR.Rigidity.RigidityExtHead
import Categorification.WeightedKLR.Rigidity.RigidityExtStandardResolutionStd

/-!
# Corollary 7.7, vanishing part, for the simple head `L_λ`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.1,
Corollary 7.7: `Extⁱ(M_λ, L_λ) = 0` for `i ≠ 2ρ^∨(λ)`. Here `L_λ` is the head
`coevaluationHead` of Lemma 7.3, the quotient of the wrap projective by the images of the cut
projectives, so it is killed by the cut idempotents (`coevaluationHead_cut`). The standard module
`M_λ = S^{κ₀}_{i}` has every black strand right of the second red strand; it is
`S(T^{λ} e(t) ⊠ R^{λ*} e(u))` with `t` the loading of the first red strand alone. The statement
holds for every black word `u` of the weight of `L_λ` and every `t`
(`subsingleton_ext_standard_coevaluationHead`), and `|u| = 2ρ^∨(λ)` for the coevaluation word.

Ext is computed for left modules, with `L_λ` a left module through the horizontal reflection
(`flipLeft`); the grading shift of the printed statement is not recorded (ungraded).
-/

universe v

open CategoryTheory Abelian MulOpposite

namespace Categorification.Stendhal

open KLR KLR.CycKLR KLRAlgebra QuantumGroup.UDot

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} {k : Type} [Fintype I] [DecidableEq I] [Field k]
  {C : QuantumGroup.CartanDatum I}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : I → ℕ)
  {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (highest : X)

/-- **The head `L_λ` of Lemma 7.3 is killed by the cuts**: `L_λ e(s) = 0` for every red-ordered
loading `s` whose last strand is not the second red strand. -/
theorem coevaluationHead_cut (d : List (I × ℕ))
    (s : Seq (stendhalWeight 2 (expandDiv d : Multiset I))) (hs : IsRedOrdered s)
    (hcut : ¬HasLastRed s) (y : coevaluationHead Q Λ RD highest d) :
    op (loadingIdem Q (coevaluationLabels Λ RD highest (expandDiv d)) s hs) • y = 0 := by
  induction y using Submodule.Quotient.induction_on with
  | H x =>
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    refine Submodule.subset_span ⟨⟨⟨s, hs⟩, hcut⟩, ?_⟩
    change x.val * loadingIdem Q _ s hs * loadingIdem Q _ s hs =
      x.val * loadingIdem Q _ s hs
    rw [mul_assoc, (isIdempotentElem_mk_e s hs).eq]

variable {Q} (hQ : KLRSymm Q) (hR : IsRouquierQ C Q) (d : List (I × ℕ))
  (hall : AllFiniteDeltaInjective Q (coevaluationLabels Λ RD highest (expandDiv d)) hQ)
  {θ : Multiset I} (t : Seq (stendhalWeight 1 θ)) (ht : IsRedOrdered t) (u : List I)
  (h : θ + wordWt u 0 = expandDiv d)
  [HasExt.{v} (ModuleCat.{0} (TensorProductAlgebra k Q (coevaluationLabels Λ RD highest
    (expandDiv d)) (expandDiv d)))]

include hR hall in
/-- **Webster, arXiv:1309.3796v3, §7.1, Corollary 7.7 (vanishing part)**, ungraded:
`Extⁱ(S(T^{λ} e(t) ⊠ R^{λ*} e(u)), L_λ) = 0` for `i ≠ |u|`, where `L_λ = coevaluationHead d`.
For `θ = 0` this standard is `M_λ`, and for the coevaluation word `|u| = 2ρ^∨(λ)`. Under the route
hypothesis `hall` of Proposition 7.6 (discharged for Rouquier parameters in
`subsingleton_ext_standard_coevaluationHead_of_rouquier`). -/
theorem subsingleton_ext_standard_coevaluationHead (n : ℕ) (hn : n ≠ u.length) :
    Subsingleton (Ext (tensorStd Q (coevaluationLabels Λ RD highest (expandDiv d)) hQ h
      (oldProj Q _ θ t ht) (cycWord Q _ u))
      (flipLeft Q (coevaluationLabels Λ RD highest (expandDiv d)) (expandDiv d)
        (coevaluationHead Q Λ RD highest d)) n) :=
  subsingleton_ext_standard_of_cut Q _ hQ hR hall t ht u h _
    (fun s hs hcut y => coevaluationHead_cut Q Λ RD highest d s hs hcut y) n hn

include hR in
/-- **Webster, arXiv:1309.3796v3, §7.1, Corollary 7.7 (vanishing part)**, ungraded, for Rouquier
parameters `Q`, with no route hypothesis. -/
theorem subsingleton_ext_standard_coevaluationHead_of_rouquier (n : ℕ) (hn : n ≠ u.length) :
    Subsingleton (Ext (tensorStd Q (coevaluationLabels Λ RD highest (expandDiv d)) hQ h
      (oldProj Q _ θ t ht) (cycWord Q _ u))
      (flipLeft Q (coevaluationLabels Λ RD highest (expandDiv d)) (expandDiv d)
        (coevaluationHead Q Λ RD highest d)) n) := by
  refine subsingleton_ext_standard_coevaluationHead Λ RD highest hQ hR d ?_ t ht u h n hn
  convert allFiniteDeltaInjective_of_rouquier
    (Λ := coevaluationLabels Λ RD highest (expandDiv d)) hR hQ

end Categorification.Stendhal

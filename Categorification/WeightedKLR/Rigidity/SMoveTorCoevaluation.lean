/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.SMoveTorWrapHeadCast
import Categorification.WeightedKLR.Rigidity.RigidityExtCoevaluationWrapHyp

/-!
# Proposition 7.22 (c) for the coevaluation heads

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22, gap (c). Let `w` be a reduced expression of the longest element, `d` the
divided coevaluation word of `λ` (Definition 7.1), `ν = d̂` its black weight and `λ* = -w₀λ`.
The S-move has red labels `(λ, λ*, λ)`. Its right module `L'` over `(λ, λ*)` is the coevaluation
head `L_λ` of Lemma 7.3 and its left module `L` over `(λ*, λ)` is the coevaluation head `L_{λ*}`
at the dual highest weight `ν - λ`, for the divided word `d̄ = d.reverse` of `λ*` along the
reversed expression. Then `(SMove.leftStd L)^r ⊗ᴸ SMove.rightStd L'` is `k` in degree `-|ν|`
and zero elsewhere: `SMove.derivedTensorHomology_reflect_coevaluationHead_one_dimensional`.

The library constructs `L_{λ*}` over the black weight `d̄̂` and the coevaluation labels at `ν - λ`,
which agree with the S-move's black weight `d̂` and labels only propositionally
(`coe_expandDiv_dualCoevaluationDividedWord`, `sMoveCoevaluationLabels_natAdd`,
`rightLabels_sMoveCoevaluationLabels`); the modules are transported along these equalities by
`castTensorModule`.

## Main results

* `SMove.coe_expandDiv_dualCoevaluationDividedWord`, `SMove.expandDiv_eq_reverse_dual`.
* `SMove.sMoveCoevaluationLabels`: the labels `(λ, λ*, λ)`, with
  `SMove.sMoveCoevaluationLabels_natAdd` and `SMove.rightLabels_sMoveCoevaluationLabels`.
* `SMove.derivedTensorHomology_reflect_coevaluationHead_one_dimensional`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.SMove

open CategoryTheory CategoryTheory.Limits Abelian Equiv MulOpposite
open Categorification.KLR.KLRAlgebra Categorification.Graded QuantumGroup QuantumGroup.UDot
open Categorification.KLR Categorification.KLR.CycKLR Categorification.Stendhal.TwoRedErase
open DG DG.DerivedCategory
open scoped DG.DegreeZero

universe w v

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
    (weight : P.integralWeights) (w : List I)

local notation "Dc" => P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix
local notation "cs" => P.coxeterSystem C.toLusztig.isGeneralizedCartan_cartanMatrix
local notation "dL" => Stendhal.coevaluationDividedWord Dc weight w
set_option quotPrecheck false in
local notation "dX" => Stendhal.coevaluationDividedWord Dc
  (-(w.foldl (fun μ j =>
  (P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix).reflection j μ) weight)) w.reverse
local notation "Λs" => (fun j => coevaluationLabels Λ RD highest (expandDiv dL) (Fin.last 1) j)
local notation "ΦX" => coevaluationLabels Λs RD (dualHighest RD highest (expandDiv dL))
  (expandDiv dX)
local notation "ΦY" => coevaluationLabels Λ RD highest (expandDiv dL)

omit [DecidableEq I] in
/-- The divided word of `λ*` along the reversed expression is `d.reverse`. -/
theorem dualCoevaluationDividedWord_eq :
    dX = (dL).reverse :=
  Stendhal.coevaluationDividedWord_reverse Dc weight w

omit [DecidableEq I] in
/-- The black weights of the two coevaluation words agree. -/
theorem coe_expandDiv_dualCoevaluationDividedWord :
    (expandDiv dL : Multiset I) = (expandDiv dX : Multiset I) := by
  rw [Stendhal.SMove.dualCoevaluationDividedWord_eq, Stendhal.expandDiv_reverse,
    Multiset.coe_reverse]

omit [DecidableEq I] in
/-- The word `𝐮` of the right module is the reverse of the expanded dual word. -/
theorem expandDiv_eq_reverse_dual :
    expandDiv dL = (expandDiv dX).reverse := by
  rw [Stendhal.SMove.dualCoevaluationDividedWord_eq, Stendhal.expandDiv_reverse,
    List.reverse_reverse]

/-- The red labels `(λ, λ*, λ)` of the S-move for the coevaluation at `λ`. -/
def sMoveCoevaluationLabels (ν : Multiset I) :
    Fin (1 + (1 + 1)) → I →₀ ℕ :=
  ![Finsupp.equivFunOnFinite.symm Λ, dualRedLabel RD highest ν, Finsupp.equivFunOnFinite.symm Λ]

omit [DecidableEq I] in
include hΛ in
/-- The labels of the last two red strands of `(λ, λ*, λ)` are the coevaluation labels
`(λ*, λ)` at the dual highest weight. -/
theorem sMoveCoevaluationLabels_natAdd
    (ν ν' : Multiset I) (hν : ν = ν') :
    sMoveCoevaluationLabels Λ RD highest ν ∘ Fin.natAdd 1 =
      coevaluationLabels (fun j => coevaluationLabels Λ RD highest ν (Fin.last 1) j) RD
        (dualHighest RD highest ν) ν' := by
  subst hν
  have h := coevaluationLabels_dualHighest Λ RD highest hΛ ν
  have h2 : (fun j => coevaluationLabels Λ RD highest ν (Fin.last 1) j) =
      fun i => dualRedLabel RD highest ν i := rfl
  rw [h2, h]
  funext i
  fin_cases i
  · ext j; rfl
  · rfl

omit [DecidableEq I] in
/-- The labels of the first two red strands of `(λ, λ*, λ)` are the coevaluation labels
`(λ, λ*)`. -/
theorem rightLabels_sMoveCoevaluationLabels
    (ν : Multiset I) :
    rightLabels (sMoveCoevaluationLabels Λ RD highest ν) = coevaluationLabels Λ RD highest ν := by
  funext i
  fin_cases i <;> rfl

variable (Ξ : Fin (1 + (1 + 1)) → I →₀ ℕ)

local notation "Ξ₃" => (Ξ ∘ Fin.cast (Nat.add_assoc 1 1 1) : Fin (1 + 1 + 1) → I →₀ ℕ)
local notation "νL" => (expandDiv dL : Multiset I)

variable {ρ : Perm (Fin (Multiset.card (stendhalWeight (1 + 1 + 1)
    (expandDiv (Stendhal.coevaluationDividedWord
      (P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix) weight w) :
        Multiset I)))) → List ℕ}
    (hρ : TypeA.IsReducedChoice ρ)

variable [HasDerivedCategory.{w, 0}
    (BraidedStendhalAlgebra.ViolOrderCorner (k := k) (Q := Q)
      (Λ := Ξ ∘ Fin.cast (Nat.add_assoc 1 1 1))
      (ν := (expandDiv (Stendhal.coevaluationDividedWord
      (P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix) weight w) : Multiset I))
      (List.map (1 : Perm (Fin (1 + 1 + 1))) (List.finRange (1 + 1 + 1))))]
  [HasDerivedCategory.{w, 0} (Stendhal.TensorProductAlgebra k Q
    (Ξ ∘ Fin.cast (Nat.add_assoc 1 1 1)) (expandDiv (Stendhal.coevaluationDividedWord
      (P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix) weight w) : Multiset I))]
  [HasDerivedCategory.{w, 0} ℤ]
  [HasExt.{v} (ModuleCat.{0} (Stendhal.TensorProductAlgebra k Q (Ξ ∘ Fin.natAdd 1)
    (expandDiv (Stendhal.coevaluationDividedWord
      (P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix) weight w) : Multiset I)))]
  [HasExt.{v} (ModuleCat.{0} (Stendhal.TensorProductAlgebra k Q
    (coevaluationLabels Λ RD highest (expandDiv (Stendhal.coevaluationDividedWord
      (P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix) weight w)))
    (expandDiv (Stendhal.coevaluationDividedWord
      (P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix) weight w) : Multiset I)))]

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

include hP hΛ hR hρ in
/-- **Proposition 7.22 (c) for the coevaluation heads** (Webster, arXiv:1309.3796v3, §7.3,
Proposition 7.22, gap (c) of its proof). Let `w` be a reduced expression of the longest element
of a finite Weyl group, `d` the divided coevaluation word of `λ` (Definition 7.1), `ν = d̂`, and
let the S-move have red labels `Ξ = (λ, λ*, λ)` (`hX`, `hY`; for example
`sMoveCoevaluationLabels`). With `L` the coevaluation head `L_{λ*}` of Lemma 7.3 at the dual
highest weight `ν - λ` for the divided word `d̄ = d.reverse` of `λ*` (over `(λ*, λ)`), and `L'`
the coevaluation head `L_λ` (over `(λ, λ*)`), both transported to the S-move's labels and black
weight by `castTensorModule`, the Tor `(SMove.leftStd L)^r ⊗ᴸ SMove.rightStd L'` is `k` in
degree `-|ν|` and zero in every other degree.

Comparison with Webster v3, Proposition 7.22, hypothesis by hypothesis:
* Webster's setting: `𝔤` of finite type, `λ` dominant, `w₀` the longest element. Here: a
  realization `P` with finite Weyl group, `weight` dominant integral and matching `λ`
  (`hweight`, `match_weight`, `hΛ`), `w` a reduced expression (`hw`) of an element with every
  simple reflection a left descent (`hlong`), i.e. of `w₀`; X-regularity `hR` of the projective
  root datum (as in Proposition 7.2 in the library).
* Webster's `L` and `L'` are the simple coevaluation heads at `λ*` and `λ` (Lemma 7.3); here they
  are exactly these modules (`coevaluationHead`), up to the transport along the equalities of
  labels and black weights.
* Webster's statement is graded; here it is ungraded, with Tor over `ℤ` and the degree `-|ν|`
  term identified with `k` additively.
* Route hypothesis: a Rouquier choice of `Q` (`hP`; Webster allows any `Q` with his
  nondegeneracy hypotheses). No other route hypothesis remains: the normalization, the
  semisimplicity of the dual block, the top Ext and the hypotheses of Lemma 7.3 are proved
  (`wrapHeadHypotheses_dualCoevaluation`, `exists_bicone_cycWord_cycDivProj`,
  `exists_linearEquiv_pi_cycDivProj_coevaluation`,
  `finrank_ext_standard_coevaluationHead_of_rouquier`). -/
theorem derivedTensorHomology_reflect_coevaluationHead_one_dimensional
    (hQ : KLRSymm Q) (hX : Ξ ∘ Fin.natAdd 1 = ΦX) (hY : rightLabels Ξ = ΦY)
    [FiniteDimensional K H]
    [Finite (P.weylGroup C.toLusztig.isGeneralizedCartan_cartanMatrix)]
    (hweight : P.IsDominantIntegral (weight : Module.Dual K H))
    (match_weight : ∀ i, (weight : Module.Dual K H) (P.coroot i) =
      (RD.pair.flip highest ((projectiveRootDatum RD).coroot i) : K))
    (hw : (cs).IsReduced w.reverse)
    (hlong : ∀ i, (cs).IsLeftDescent ((cs).wordProd w.reverse) i) :
    Nonempty ((homologyFunctor (A := ℤ) ℤ (-(Multiset.card νL : ℤ))).obj
        ((derivedTensor.{w} ℤ (Stendhal.TensorProductAlgebra k Q Ξ₃ νL)
          ((reflectOne Q Ξ₃ hQ hρ).obj ((leftStd Q hQ Ξ νL).obj
            (castTensorModule Q hX (coe_expandDiv_dualCoevaluationDividedWord P weight w)
              (Stendhal.flipLeft Q ΦX _ (Stendhal.coevaluationHead Q Λs RD
                (dualHighest RD highest (expandDiv dL)) dX)))))).obj
          (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor _).obj
            ((rightStd Q hQ Ξ₃ νL).obj (castTensorModule Q hY rfl
              (Stendhal.flipLeft Q ΦY _ (Stendhal.coevaluationHead Q Λ RD highest dL))))))) ≃+
          k) ∧
      ∀ n : ℤ, n ≠ -(Multiset.card νL : ℤ) → IsZero ((homologyFunctor (A := ℤ) ℤ n).obj
        ((derivedTensor.{w} ℤ (Stendhal.TensorProductAlgebra k Q Ξ₃ νL)
          ((reflectOne Q Ξ₃ hQ hρ).obj ((leftStd Q hQ Ξ νL).obj
            (castTensorModule Q hX (coe_expandDiv_dualCoevaluationDividedWord P weight w)
              (Stendhal.flipLeft Q ΦX _ (Stendhal.coevaluationHead Q Λs RD
                (dualHighest RD highest (expandDiv dL)) dX)))))).obj
          (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor _).obj
            ((rightStd Q hQ Ξ₃ νL).obj (castTensorModule Q hY rfl
              (Stendhal.flipLeft Q ΦY _ (Stendhal.coevaluationHead Q Λ RD highest dL)))))))) := by
  have hH := Stendhal.wrapHeadHypotheses_dualCoevaluation (Q := Q) hP Λ RD
    highest hR P weight hweight match_weight w hw hlong
  have het : Stendhal.TensorProductAlgebra.mk Q (ΦY ∘ Fin.castSucc) 0
      (Stendhal.StendhalAlgebra.e Stendhal.vacuumSeq Stendhal.vacuumSeq_ordered) = 1 :=
    Stendhal.vacuumSeq_mk_e Q (ΦY ∘ Fin.castSucc)
  have h₀ : 0 + Stendhal.wordWt (expandDiv dL) 0 = νL := by
    rw [zero_add, ← Stendhal.coe_reverse_eq_wordWt, Multiset.coe_reverse]
  have := Stendhal.tensorProductAlgebra_finite ΦY νL hP
  have hz : IsIdempotentElem (Stendhal.TwoRedErase.wrapIdem Q ΦY νL
      (dividedIdem Λ (Q := Q) dL)) :=
    (Stendhal.TwoRedErase.wrapIdem_mul Q ΦY _ _ _).trans
      (congrArg _ (isIdempotentElem_dividedIdem Λ dL).eq)
  have := Stendhal.finiteDimensional_flipLeft_quotient Q ΦY _ hz
    (Stendhal.coevaluationTrace (Stendhal.TwoRedErase.cutIdem Q ΦY νL))
  have hB := Stendhal.exists_bicone_cycWord_cycDivProj Q ΦY dL
  obtain ⟨J, _, _, ι, π, hιπ, htot, hcard⟩ := hB
  have : Nonempty J := Fintype.card_pos_iff.1 (hcard ▸ Stendhal.prod_factorial_pos dL)
  have htop := Stendhal.finrank_ext_standard_coevaluationHead_of_rouquier Λ RD highest hΛ hR hP
    hQ P weight hweight match_weight w hw hlong Stendhal.vacuumSeq Stendhal.vacuumSeq_ordered h₀
  rw [← Multiset.coe_card] at htop
  have hJ : Fintype.card J = ((dX).map fun q => q.2.factorial).prod := by
    rw [hcard, Stendhal.SMove.dualCoevaluationDividedWord_eq, List.map_reverse,
      List.prod_reverse]
  exact derivedTensorHomology_reflect_wrapHead_rightStd_one_dimensional_of_eq.{w, v}
    Q hQ Ξ dX hX hY (coe_expandDiv_dualCoevaluationDividedWord P weight w) hρ hP hH.1 hH.2.1
    hH.2.2.1
    hH.2.2.2 (Stendhal.flipLeft Q ΦY _ (Stendhal.coevaluationHead Q Λ RD highest dL))
    (fun s hs hcut y => by
      rw [Stendhal.flipLeft_smul, Stendhal.loadingIdem, Stendhal.tensorFlip_mk_e]
      exact Stendhal.coevaluationHead_cut Q Λ RD highest dL s hs hcut _)
    (expandDiv dL) (expandDiv_eq_reverse_dual P weight w) h₀ Stendhal.vacuumSeq
    Stendhal.vacuumSeq_ordered het (Stendhal.cycDivProj Q ΦY dL)
    (fun M _ _ _ => exists_linearEquiv_pi_cycDivProj_coevaluation hP RD Λ highest hR P weight
      hweight match_weight w hw hlong M) ι π hιπ htot htop hJ

end Categorification.Stendhal.SMove

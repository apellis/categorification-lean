/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.SingleRedInduction
import Categorification.WeightedKLR.RedStrands.SingleRedDerivedTensorIsoId
import Categorification.WeightedKLR.RedStrands.BlackRouqData
import Categorification.WeightedKLR.Induction.Generation

set_option backward.isDefEq.respectTransparency false

/-!
# Black induction of the projectives `e(𝐢) T^λ`, one red strand

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.6 (the
functor `F_i` of Theorem 4.31 adds a black strand on the right) and Theorem 4.20 (`T^λ ≅ R^λ`
for one red strand, `SingleRed.insertRed`). For one red strand:

* `SingleRed.appendBlack_insertRed_e`: adding a black strand of colour `i` on the right sends
  the idempotent `e(𝐢)` (red strand on the left) to `e(𝐢 i)`;
* `SingleRed.blackFOfEqRedFirstIdealIso`: **`F_i (e(𝐢) T^λ_μ) ≅ e(𝐢 i) T^λ_β`** as right
  modules, for `{i} + μ = β` (induction of a cyclic projective, `InductionAlong.indLIdealEquiv`);
* `SingleRed.derivedFOfEqSingleRedFirstIdealIso`: the same in the derived category, in degree `0`
  (derived induction of a single module is the single of the induced module, Mathlib's
  `Functor.mapDerivedCategorySingleFunctor`).

This is the step of the computation of the derived action on `F_𝐢 T^λ_∅` (the input `W` of
`SingleRed.blackVacuumDerivedTensorIsoId`) that adds one black strand.
-/

noncomputable section

namespace Categorification.Stendhal.SingleRed

open CategoryTheory MulOpposite KLR KLRAlgebra KLRAlgebra.AbsentColour InductionAlong
  QuantumGroup

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  (Λ : Fin 1 → I →₀ ℕ)

/-- **Adding a black strand on the right to `e(𝐢)`** (red strand on the left) gives `e(𝐢 i)`
(Webster, arXiv:1309.3796v3, §4.6, Theorem 4.20). -/
theorem appendBlack_insertRed_e (i : I) (ν : Multiset I) (s : Seq ν) :
    appendBlack Q Λ i ν (insertRed Q Λ ν (KLRAlgebra.e s)) =
      insertRed Q Λ ({i} + ν) (KLRAlgebra.e (Seq.cast (add_comm ν {i}) (s.append default))) := by
  rw [insertRed_e, insertRed_e]
  exact (appendBlack_mk_e Q Λ i ν _ (ordered ν _)).trans
    (congrArg (fun s => mk Q Λ ({i} + ν) (StendhalAlgebraAllOrders.e s))
      (appendBlackLoading_insertWord i ν s))

/-- The sequence `𝐢 i` of content `β`, for `{i} + μ = β`. -/
def appendSeq (i : I) {μ β : Multiset I} (h : ({i} : Multiset I) + μ = β) (s : Seq μ) : Seq β :=
  Seq.cast ((add_comm μ {i}).trans h) (s.append default)

theorem appendBlackOpOfEq_redFirstIdem (i : I) {μ β : Multiset I}
    (h : ({i} : Multiset I) + μ = β) (s : Seq μ) :
    appendBlackOpOfEq Q Λ i h (redFirstIdem Q Λ μ s) = redFirstIdem Q Λ β (appendSeq i h s) := by
  subst h
  rw [appendBlackOpOfEq_apply]
  change op (appendBlack Q Λ i μ (insertRed Q Λ μ (KLRAlgebra.e s))) = _
  rw [appendBlack_insertRed_e]
  rfl

/-- The ideal `T e` of `idemLeftIdeal` is the left ideal `lIdeal e`. -/
theorem idemLeftIdeal_eq_lIdeal {T : Type} [Ring T] (e : T) : idemLeftIdeal e = lIdeal e :=
  Submodule.ext fun _ => Iff.rfl

/-- **`F_i (e(𝐢) T^λ_μ) ≅ e(𝐢 i) T^λ_β`** (Webster, arXiv:1309.3796v3, §4.6, one red strand):
induction of the cyclic projective right module `e(𝐢) T^λ_μ` along the black-strand map. -/
def blackFOfEqRedFirstIdealIso (i : I) {μ β : Multiset I} (h : ({i} : Multiset I) + μ = β)
    (s : Seq μ) :
    (blackFOfEq Q Λ i h).obj
        (ModuleCat.of (TensorProductAlgebra k Q Λ μ)ᵐᵒᵖ (idemLeftIdeal (redFirstIdem Q Λ μ s))) ≅
      ModuleCat.of (TensorProductAlgebra k Q Λ β)ᵐᵒᵖ
        (idemLeftIdeal (redFirstIdem Q Λ β (appendSeq i h s))) :=
  LinearEquiv.toModuleIso
    ((Ind.congr (LinearEquiv.ofEq _ _ (idemLeftIdeal_eq_lIdeal _))).trans
      ((indLIdealEquiv (appendBlackOpOfEq Q Λ i h) (redFirstIdem_isIdempotentElem Q Λ μ s)).trans
        (LinearEquiv.ofEq _ _ (by
          rw [appendBlackOpOfEq_redFirstIdem, idemLeftIdeal_eq_lIdeal]))))

theorem blackFOfEqRedFirstIdealIso_hom_tmul (i : I) {μ β : Multiset I}
    (h : ({i} : Multiset I) + μ = β) (s : Seq μ) (z : Corner (appendBlackOpOfEq Q Λ i h))
    (a : idemLeftIdeal (redFirstIdem Q Λ μ s)) :
    ((blackFOfEqRedFirstIdealIso Q Λ i h s).hom.hom (Ind.tmul z a) : _) =
      z.1 * appendBlackOpOfEq Q Λ i h a.1 :=
  rfl

variable [∀ β : Multiset I,
  HasDerivedCategory.{0} (ModuleCat.{0} (TensorProductAlgebra k Q Λ β)ᵐᵒᵖ)]
  {C : CartanDatum I} (hQ : IsRouquierQ C Q)

/-- **Derived induction of `e(𝐢) T^λ_μ` in degree `0`** is `e(𝐢 i) T^λ_β` in degree `0`
(Webster, arXiv:1309.3796v3, §4.6, one red strand; Mathlib's
`Functor.mapDerivedCategorySingleFunctor`). -/
def derivedFOfEqSingleRedFirstIdealIso (i : I) {μ β : Multiset I}
    (h : ({i} : Multiset I) + μ = β) (s : Seq μ) :
    (derivedFOfEq Λ hQ i h).obj ((DerivedCategory.singleFunctor _ 0).obj
        (ModuleCat.of (TensorProductAlgebra k Q Λ μ)ᵐᵒᵖ (idemLeftIdeal (redFirstIdem Q Λ μ s)))) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (ModuleCat.of (TensorProductAlgebra k Q Λ β)ᵐᵒᵖ
          (idemLeftIdeal (redFirstIdem Q Λ β (appendSeq i h s)))) :=
  haveI := blackFOfEq_preservesFiniteLimits Λ hQ i h
  haveI := blackFOfEq_preservesFiniteColimits Λ hQ i h
  ((blackFOfEq Q Λ i h).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (blackFOfEqRedFirstIdealIso Q Λ i h s)

end Categorification.Stendhal.SingleRed

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorClassLowering
import Categorification.WeightedKLR.RedStrands.TensorRestrictionAdjoint

/-!
# Class functionals killed by the lowering operators

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 7.5. Webster shows that `[L_λ]` is invariant by checking `Hom(F_i P, L_λ) = 0` for
every projective `P` (Lemma 7.3: `L_λ` is killed by the idempotents of the loadings with a black
strand to the right of the last red strand) and that `L_λ` has weight `0`. This file proves both
inputs for the class functional `classFunctional N` of an arbitrary finite-dimensional graded
right module `N` over `T^λ` (Webster, Corollary 6.10):

* `classFunctional_comp_F_eq_zero`: if every idempotent `e(t)` of a red-ordered loading `t`
  whose last strand is black kills `N`, then `classFunctional N ∘ F_i = 0` for all `i`. On a right
  sequence projective, `F_i` appends a black strand on the right (`F_rightSequence`), and the
  class functional there is the graded dimension of the cut `N e(t)`.
* `classFunctional_K`: if the black content `ν` of `N` has the total weight of the red strands,
  `Σ_r λ_r = Σ_{i ∈ ν} α_i`, then `classFunctional N (K_μ x) = classFunctional N x`
  (the class of a black content `β` has weight `Σ_r λ_r - Σ_{i ∈ β} α_i`,
  `tensorModuleEquiv_torus_block`).

The argument is Webster's ("`Hom(P, E_i L) = Hom(F_i P, L) = 0`"), read on class functionals:
no restriction functor is needed, since `F_i` on right sequence projectives is explicit.
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
local instance classFunctionalInvarianceInst : NeZero (RatFunc.X : 𝕂) := ⟨RatFunc.X_ne_zero⟩
private abbrev invRing : LP ≃+* LP := (LaurentPolynomial.invert (R := ℤ)).toRingEquiv
local instance classFunctionalInvarianceInst2 :
    RingHomInvPair invRing.toRingHom invRing.toRingHom :=
  RingHomInvPair.of_ringEquiv invRing

variable {I : Type} {k Y : Type*} [DecidableEq I] [Field k] [AddCommGroup Y] [Finite I]
    {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)
    {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular) {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ)
    (wt : Fin ℓ → Dom R) (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i))

local notation "G" =>
  stendhalGradingDatum Λ hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)
local notation "K" => tensorProjectiveGroup C hQ Λ
local notation "Kr" => rightTensorProjectiveGroup C hQ Λ
local notation "η" => tensorModuleEquiv C hQ hR Λ wt hwt
local notation "η'" => rightTensorModuleEquiv C hQ hR Λ wt hwt
local notation "𝒜" ν => oppositeGrade (tensorProductGrade G ν)
local notation "cf" => classFunctional C hQ hR Λ wt hwt
local notation "ρ" => tensorRepresentation wt

variable [∀ ν : Multiset I, Module.Finite k (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ]

/-- A red-ordered loading whose last strand is black (the loadings `κ` with a black strand to
the right of the last red strand). -/
def IsLastBlack {ν : Multiset I} (t : Seq (stendhalWeight ℓ ν)) : Prop :=
  ∃ a : Fin (Multiset.card (stendhalWeight ℓ ν)),
    a.val + 1 = Multiset.card (stendhalWeight ℓ ν) ∧ (t.lbl a).isLeft

omit [DecidableEq I] [Finite I] in
/-- Appending a black strand on the right gives a loading whose last strand is black. -/
theorem isLastBlack_appendBlackLoading (i : I) (β : Multiset I)
    (s : Seq (stendhalWeight ℓ β)) : IsLastBlack (appendBlackLoading i β s) := by
  have hc : Multiset.card (stendhalWeight ℓ ({i} + β)) =
      Multiset.card (stendhalWeight ℓ β) + 1 := by
    simp [stendhalWeight]
  refine ⟨⟨Multiset.card (stendhalWeight ℓ β), by omega⟩, hc.symm, ?_⟩
  rw [appendBlackLoading_lbl_of_eq i β s _ rfl]
  rfl

omit [Finite I] in
private theorem gdimPoly_eq_zero_of_forall {M : Type*} [AddCommGroup M] [Module k M]
    (ℳ : ℤ → Submodule k M) (h : ∀ d, ℳ d = ⊥) : gdimPoly ℳ = 0 := by
  have h0 : (fun d => (Module.finrank k (ℳ d) : ℤ)) = 0 := by
    funext d; rw [h d, finrank_bot]; rfl
  ext d
  simp [gdimPoly, h0]

/-- **The class functional is killed by the lowering operators** (Webster, arXiv:1309.3796v3,
proof of Proposition 7.5 from Lemma 7.3): if `N e(t) = 0` for every red-ordered loading `t`
whose last strand is black, then `classFunctional N (F_i x) = 0` for all `i` and `x`. -/
theorem classFunctional_comp_F_eq_zero (ν : Multiset I) (N : GFin (𝒜 ν))
    (hN : ∀ (t : Seq (stendhalWeight ℓ ν)) (ht : IsRedOrdered t), IsLastBlack t →
      ∀ x : N.carrier, op (TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e t ht)) • x = 0)
    (i : I) : (cf ν N).comp (ρ (F R v i)) = 0 := by
  refine ext_rightSequence C hQ hR Λ wt hwt _ fun β s hs => ?_
  rw [LinearMap.comp_apply, F_rightSequence]
  by_cases h : {i} + β = ν
  · subst h
    rw [classFunctional_rightSequence]
    have hbot : ∀ d, idem N.grading
        (op (TensorProductAlgebra.mk Q Λ ({i} + β) (StendhalAlgebra.e
          (appendBlackLoading i β s) (appendBlackLoading_ordered i β s hs)))) d = ⊥ := by
      intro d
      refine (Submodule.eq_bot_iff _).2 fun x _ => ?_
      apply Subtype.ext
      have hx := x.2
      rw [mem_idemSubspace, hN _ _ (isLastBlack_appendBlackLoading i β s)] at hx
      exact hx.symm
    rw [gdimPoly_eq_zero_of_forall _ hbot, map_zero]
  · exact classFunctional_lof_of_ne C hQ hR Λ wt hwt N _ h

omit [∀ ν : Multiset I, Module.Finite k (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ] in
/-- The toral action on the image of a right projective class in a single black content. -/
theorem rightTensorModuleEquiv_torus_block (β : Multiset I) (x : Kr β) (a : Y) :
    ρ (QuantumGroup.K R v a) (η' (DirectSum.lof LP _ Kr β x) : TensorSpace wt) =
      v ^ (((∑ r, (wt r).1) - R.rootSum β.toFinsupp) a) •
        (η' (DirectSum.lof LP _ Kr β x) : TensorSpace wt) := by
  have hx : (tensorReflectionK0 C hQ Λ).symm (DirectSum.lof LP _ Kr β x) =
      DirectSum.lof LP _ K β ((K0.rightTwistEquiv (tensorReflectionG C hQ Λ β)).symm x) := by
    rw [LinearEquiv.symm_apply_eq, tensorReflectionK0_lof, LinearEquiv.apply_symm_apply]
  rw [rightTensorModuleEquiv, LinearEquiv.trans_apply, hx]
  exact tensorModuleEquiv_torus_block C hQ hR Λ wt hwt β _ a

/-- **The class functional of a module of weight `0` is `K`-invariant**: if the black content
`ν` carries the total weight of the red strands, `Σ_r λ_r = Σ_{i ∈ ν} α_i`, then
`classFunctional N (K_μ x) = classFunctional N x`. -/
theorem classFunctional_K (ν : Multiset I) (N : GFin (𝒜 ν))
    (hν : ∑ r, (wt r).1 = R.rootSum ν.toFinsupp) (a : Y) (x : TensorSpace wt) :
    cf ν N (ρ (QuantumGroup.K R v a) x) = cf ν N x := by
  have h := Lattice.ext_of_lattice (isLattice_integralTensor C hR wt)
    (f := (cf ν N).comp (ρ (QuantumGroup.K R v a))) (f' := cf ν N) fun z hz => by
      obtain ⟨y, hy⟩ := (η').surjective ⟨z, hz⟩
      have hzy : z = (η' y : TensorSpace wt) := by rw [hy]
      rw [hzy, LinearMap.comp_apply]
      clear hy hzy
      induction y using DirectSum.induction_on with
      | zero => rw [map_zero, ZeroMemClass.coe_zero, map_zero, map_zero]
      | add y y' hy hy' =>
        rw [map_add, Submodule.coe_add, map_add, map_add, hy, hy', map_add]
      | of β y =>
        rw [← DirectSum.lof_eq_of LP, rightTensorModuleEquiv_torus_block, map_smul]
        by_cases h : β = ν
        · subst h
          rw [hν, sub_self, AddMonoidHom.zero_apply, zpow_zero, one_smul]
        · rw [classFunctional_lof_of_ne C hQ hR Λ wt hwt N _ h, smul_zero]
  exact LinearMap.congr_fun h x

end Categorification.Stendhal.FirstWeight

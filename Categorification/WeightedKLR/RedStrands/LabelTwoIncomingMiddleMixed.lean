/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoIncomingExteriorAcyclic

/-!
# Mixed tensor with the label-two middle standard

The incoming exterior coefficient is supported at its exterior loading.
It kills the generator of the middle standard and the higher loading
idempotents in its supported resolution.
-/

open CategoryTheory CategoryTheory.Limits DG DG.DerivedCategory MulOpposite
open scoped DG.DegreeZero

set_option backward.isDefEq.respectTransparency false

namespace Categorification.Stendhal.LabelTwo

open KLR KLRAlgebra

noncomputable section

universe w

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable (k : Type) [Field k]
local notation "ν" => (({()} : Multiset Unit) + {()})
local notation "wt" => weights
local notation "μ" => stendhalWeight 2 ν
local notation "T" => TensorProductAlgebra k (parameter k) wt ν
local notation "S" => Standard k
local notation "N" => IncomingExteriorCoefficient k
local notation "P" => labelTwoRightExteriorDividedStandard (parameter k)
local notation "E" => seqIdem (parameter k) wt loading loading_ordered
local notation "A₀" => labelTwoExteriorRightLoading
local notation "reflection" => (tensorReflect : T →ₐ[k] Tᵐᵒᵖ)
local notation "TRaw" => TensorProductAlgebra k (parameter k)
  (fun (_ : Fin 2) => Finsupp.single () 2) (Multiset.replicate 2 ())

local instance : Module T P := inferInstanceAs (Module TRaw P)
local instance : Module Tᵐᵒᵖ N := inferInstanceAs (Module TRawᵐᵒᵖ N)
local instance : SMulCommClass k Tᵐᵒᵖ N := inferInstanceAs (SMulCommClass k TRawᵐᵒᵖ N)

private theorem incomingCoefficient_action (a : T) (z : N) :
    (op a • z : N) = ((reflection a).unop • (show P from z) : P) := rfl

private theorem incomingCoefficient_kills_other (s : Seq μ) (hs : IsRedOrdered s)
    (hne : s ≠ A₀) (z : N) : op (seqIdem (parameter k) wt s hs) • z = 0 := by
  rw [incomingCoefficient_action, unop_tensorReflect_e]
  have h : seqIdem (parameter k) wt s hs = tensorOfKLR (parameter k) wt ν (e s) :=
    (stendhalTensorProjection_e wt ν s hs).symm
  let y : P := z
  apply Subtype.ext
  change seqIdem (parameter k) wt s hs • y.val = 0
  exact (congrArg (fun a : T => a • y.val) h).trans
    (labelTwo_rightStandard_loading_annihilation (parameter k) s hne y.val)

private theorem right_not_higher : ¬ StendhalLT loading A₀ := by
  unfold StendhalLT StendhalLE
  decide +kernel

private theorem incomingCoefficient_kills_above_middle (s : Seq μ) (hs : IsRedOrdered s)
    (h : StendhalLT loading s) (z : N) : op (seqIdem (parameter k) wt s hs) • z = 0 :=
  incomingCoefficient_kills_other k s hs (fun he => right_not_higher (he ▸ h)) z

variable [DG.HasDerivedCategory.{w,0} k]
  [DG.HasDerivedCategory.{w,0} (TensorProductAlgebra k (parameter k)
    weights (({()} : Multiset Unit) + {()}))]

/-- The ambient mixed tensor of the reflected incoming exterior with the actual middle standard. -/
abbrev incomingMiddleStandardHomology (n : ℤ) : ModuleCat k :=
  (homologyFunctor k n).obj ((derivedTensor k T N).obj (Q.obj (DGModuleCat.of T (InDegreeZero S))))

/-- The ordinary mixed tensor is zero because the incoming exterior is
killed by the middle idempotent. -/
theorem incomingMiddleStandardHomology_zero_isZero :
    IsZero (incomingMiddleStandardHomology k 0) := by
  let e₀ : incomingMiddleStandardHomology k 0 ≃ₗ[k] TensorProductOver T N S :=
    ambientDerivedTensorH0Equiv (k := k) (A := T) («N» := N) S
  have h : loading ≠ A₀ := by
    intro he
    have hh := congrArg (fun s : Seq μ => s.lbl ⟨2, by decide⟩) he
    change (Sum.inr (1 : Fin 2) : Unit ⊕ Fin 2) = Sum.inl () at hh
    cases hh
  let g : S := leftStandardUnit (parameter k) wt loading loading_ordered
  have hg : E • g = g := by
    have he := (middleToFixed k (1 : Categorification.Webster.LabelTwo.Middle k)).property
    change E • (middleToFixed k (1 : Categorification.Webster.LabelTwo.Middle k)).val = _ at he
    simpa only [middleToFixed_one_val] using he
  have hz (z : TensorProductOver T N S) : z = 0 := by
    induction z using TensorProductOver.induction_on with
    | zero => rfl
    | tmul m s =>
      obtain ⟨a,rfl⟩ := leftStandard_exists_smul_unit (Q := parameter k) (Λ := wt) loading loading_ordered s
      change TensorProductOver.tmul T m (a • g) = 0
      rw [← TensorProductOver.op_smul_tmul, ← hg,
        ← TensorProductOver.op_smul_tmul, incomingCoefficient_kills_other k loading loading_ordered h,
        TensorProductOver.zero_tmul]
    | add x y hx hy => rw [hx,hy,add_zero]
  have : Subsingleton (TensorProductOver T N S) := ⟨fun x y => (hz x).trans (hz y).symm⟩
  exact ModuleCat.isZero_iff_subsingleton.mpr e₀.injective.subsingleton

/-- A projective resolution supported above the middle loading makes the
mixed incoming-exterior and middle-standard tensor vanish in every degree. -/
theorem incomingMiddleStandardHomology_isZero_of_support
    (R : ProjectiveResolution (ModuleCat.of T S))
    (hR : ∀ n : ℕ, ∃ (J : Type) (label : J → {s : Seq μ // IsRedOrdered s})
      (inc : ∀ j, lIdeal (seqIdem (parameter k) wt (label j).1 (label j).2) →ₗ[T]
        R.complex.X (n+1)),
      (∀ j, StendhalLT loading (label j).1) ∧ ∀ x : R.complex.X (n+1),
        x ∈ Submodule.span T {y | ∃ j z, inc j z = y})
    (n : ℤ) : IsZero (incomingMiddleStandardHomology k n) := by
  by_cases hn : n = 0
  · subst n
    exact incomingMiddleStandardHomology_zero_isZero k
  · apply isZero_homology_of_isZero_intHomology k
    refine isZero_derivedTensorHomology_of_projectiveResolution_loading_support
      (M := N) R (fun s : {s : Seq μ // IsRedOrdered s} =>
        seqIdem (parameter k) wt s.1 s.2) (fun s => StendhalLT loading s.1)
      (fun s => seqIdem_mul_self (parameter k) wt s.1 s.2) hR ?_ n hn
    intro s hs z
    exact incomingCoefficient_kills_above_middle k s.1 s.2 hs z

end
end Categorification.Stendhal.LabelTwo

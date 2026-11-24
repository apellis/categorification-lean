/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicTerminalProjective
import Categorification.WeightedKLR.RedStrands.EraseRed
import Categorification.WeightedKLR.Induction.Restriction

/-!
# The terminal projective of the one-red Webster algebra

The cyclotomic equivalence transports the weight-two divided-power idempotent
and the simplicity of its right projective to the Webster diagram algebra.
-/

noncomputable section

namespace Categorification.Stendhal.SingleRed

open KLR KLR.CycKLR MulOpposite

variable {k : Type*} [Field k] (Q : Unit → Unit → MvPolynomial (Fin 2) k)

local notation "ν" => Multiset.replicate 2 ()
local notation "Λ" => fun (_ : Fin 1) => Finsupp.single () 2
local notation "A" => TensorProductAlgebra k Q Λ ν
local notation "powers" => fun _ : Unit => (Polynomial.X ^ 2 : Polynomial k)
local notation "R" => CycKLR k Q powers ν

private def terminalEquiv : R ≃ₐ[k] A := by
  have hp : (fun i : Unit => (Polynomial.X : Polynomial k) ^ Finsupp.single () 2 i) = powers := by
    funext i
    cases i
    rw [Finsupp.single_eq_same]
  exact hp ▸ cyclotomicEquiv (k := k) Q Λ ν

/-- The terminal weight-two projector as a diagram in the one-red Webster algebra. -/
def twoBlackTerminalWebsterIdem : A :=
  terminalEquiv Q (twoBlackTerminalIdem Q)

theorem twoBlackTerminalWebsterIdem_idempotent :
    IsIdempotentElem (twoBlackTerminalWebsterIdem Q) :=
  (twoBlackTerminalIdem_idempotent Q).map (terminalEquiv Q)

/-- The right ideal cut out by the terminal Webster projector is projective. -/
theorem twoBlackTerminalWebsterProjective_projective :
    Module.Projective Aᵐᵒᵖ (rIdeal (twoBlackTerminalWebsterIdem Q)) :=
  rIdeal_projective (twoBlackTerminalWebsterIdem_idempotent Q)

/-- The terminal divided-power right ideal in the one-red Webster algebra is simple. -/
theorem twoBlackTerminalWebsterProjective_simple :
    CategoryTheory.Simple (ModuleCat.of Aᵐᵒᵖ (rIdeal (twoBlackTerminalWebsterIdem Q))) := by
  let e := terminalEquiv Q
  let σ := e.op.toRingHom
  let _ : RingHomSurjective σ := ⟨e.op.surjective⟩
  let f : rIdeal (twoBlackTerminalIdem Q) →ₛₗ[σ] rIdeal (twoBlackTerminalWebsterIdem Q) :=
    { toFun := fun x => ⟨e x.val, by
        change e (twoBlackTerminalIdem Q) * e x.val = e x.val
        rw [← map_mul, mem_rIdeal.mp x.property]⟩
      map_add' := fun x y => Subtype.ext (map_add e x.val y.val)
      map_smul' := fun a x => Subtype.ext (map_mul e x.val (unop a)) }
  have hf : Function.Bijective f := by
    refine ⟨fun x y h => Subtype.ext (e.injective (congrArg Subtype.val h)), ?_⟩
    intro y
    obtain ⟨x, hx⟩ := e.surjective y.val
    refine ⟨⟨x, mem_rIdeal.mpr (e.injective ?_)⟩, Subtype.ext hx⟩
    rw [map_mul, hx]
    exact mem_rIdeal.mp y.property
  exact simple_iff_isSimpleModule.mpr
    ((f.isSimpleModule_iff_of_bijective hf).mp
      (simple_iff_isSimpleModule.mp (twoBlackTerminalProjective_simple Q)))


attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

/-- The outer divided-power factor in the label-two unknot calculation,
Webster v2, §8.2, has scalar corner algebra. -/
def twoBlackTerminalWebsterCornerEquiv :
    (twoBlackTerminalWebsterIdem_idempotent Q).Corner ≃ₐ[k] k := by
  let e := terminalEquiv Q
  let P := twoBlackTerminalWebsterIdem Q
  let C := (twoBlackTerminalWebsterIdem_idempotent Q).Corner
  let f : k →ₐ[k] C := Algebra.ofId k C
  refine (AlgEquiv.ofBijective f ⟨?_,?_⟩).symm
  · have hn : P ≠ 0 := fun h => twoBlackTerminalIdem_ne_zero Q
      (e.injective (h.trans (map_zero e).symm))
    apply (injective_iff_map_eq_zero f).mpr
    intro c hc
    have hz : c • P = 0 := congrArg Subtype.val hc
    exact (smul_eq_zero.mp hz).resolve_right hn
  · intro z
    obtain ⟨hl,hr⟩ := (Subsemigroup.mem_corner_iff
      (twoBlackTerminalWebsterIdem_idempotent Q)).mp z.property
    have support : twoBlackTerminalIdem Q * e.symm z.val = e.symm z.val ∧
        e.symm z.val * twoBlackTerminalIdem Q = e.symm z.val := by
      constructor
      · apply e.injective
        rw [map_mul,AlgEquiv.apply_symm_apply]; exact hl
      · apply e.injective
        rw [map_mul,AlgEquiv.apply_symm_apply]; exact hr
    obtain ⟨c,hc⟩ := twoBlackTerminal_corner_span Q
      ⟨e.symm z.val,(Subsemigroup.mem_corner_iff (twoBlackTerminalIdem_idempotent Q)).mpr support⟩
    refine ⟨c,Subtype.ext ?_⟩
    change c • P = z.val
    have h := congrArg e hc
    rw [map_smul,AlgEquiv.apply_symm_apply] at h
    exact h

end Categorification.Stendhal.SingleRed

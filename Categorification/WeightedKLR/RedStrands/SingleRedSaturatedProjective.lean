/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicSaturatedProjective
import Categorification.WeightedKLR.RedStrands.SingleRedGrading
import Categorification.WeightedKLR.Induction.Restriction

/-!
# Saturated divided powers in the one-red Webster algebra

This is the one-colour step in Webster, arXiv:1309.3796v2, Proposition 7.2.
Inserting one red strand identifies the saturated divided-power projector
with the homogeneous full-loading block idempotent in the Webster algebra.
Its right ideal is simple and projective.
-/

noncomputable section

namespace Categorification.Stendhal.SingleRed

open KLR KLR.CycKLR KLRAlgebra MulOpposite

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {k I : Type*} [Field k] [DecidableEq I]
  {ν : Multiset I} {i : I} (same : ∀ j ∈ ν, j = i)
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin 1 → I →₀ ℕ)

local notation "n" => Multiset.card ν
local notation "A" => TensorProductAlgebra k Q Λ ν
local notation "powers" => fun _ : I => (Polynomial.X ^ n : Polynomial k)
local notation "actual" => fun j : I => (Polynomial.X ^ Λ 0 j : Polynomial k)
local notation "R" => CycKLR k Q powers ν

include same in
private theorem terminal_cycElt (sat : Λ 0 i = n) (s : Seq ν) :
    cycElt Q powers s = cycElt Q actual s := by
  by_cases h : 0 < n
  · rw [cycElt_of_pos _ _ _ h, cycElt_of_pos _ _ _ h]
    have hlabel : s.lbl ⟨0,h⟩ = i := same _ (s.mem ⟨0,h⟩)
    simp only [hlabel,sat]
  · simp [cycElt,h]

private def terminalEquiv (sat : Λ 0 i = n) : R ≃ₐ[k] A := by
  let f : R →ₐ[k] CycKLR k Q actual ν := CycKLR.lift (CycKLR.mk k Q actual ν) fun s => by
    rw [terminal_cycElt same Q Λ sat, mk_cycElt]
  let g : CycKLR k Q actual ν →ₐ[k] R := CycKLR.lift (CycKLR.mk k Q powers ν) fun s => by
    rw [← terminal_cycElt same Q Λ sat, mk_cycElt]
  refine (AlgEquiv.ofAlgHom f g ?_ ?_).trans (cyclotomicEquiv Q Λ ν)
  · apply AlgHom.ext
    intro z
    obtain ⟨w,rfl⟩ := CycKLR.mk_surjective z
    simp only [AlgHom.comp_apply, AlgHom.id_apply, f, g, lift_mk]
  · apply AlgHom.ext
    intro z
    obtain ⟨w,rfl⟩ := CycKLR.mk_surjective z
    simp only [AlgHom.comp_apply, AlgHom.id_apply, f, g, lift_mk]

/-- The saturated divided-power projector in the one-red Webster algebra. -/
def saturatedWebsterIdem : A :=
  cyclotomicProjection Q Λ ν (CycKLR.mk k Q actual ν
    (pol (NilHecke.xDelta n) * ψw (NilHecke.w0Word n)))

include same in
/-- The saturated projector is the inserted full-loading block idempotent. -/
theorem saturatedWebsterIdem_eq_blockIdem (s : Seq ν) :
    saturatedWebsterIdem (ν := ν) Q Λ =
      cyclotomicProjection Q Λ ν (CycKLR.mk k Q actual ν (blockIdem s 0 n)) := by
  unfold saturatedWebsterIdem
  have he : (pol (NilHecke.xDelta n) * ψw (NilHecke.w0Word n) : KLRAlgebra k Q ν) =
      blockIdem s 0 n := by
    apply toNH_injective same Q
    rw [map_mul, toNH_pol, toNH_ψw, toNH_blockIdem]
    rfl
  rw [he]

include same in
/-- The saturated Webster projector has degree zero for the diagram grading. -/
theorem saturatedWebsterIdem_mem_grade (s : Seq ν)
    (G : GradingDatum Q) (d : I → ℤ) (hd : ∀ j, G.degX j = 2 * d j) :
    saturatedWebsterIdem (ν := ν) Q Λ ∈
      tensorProductGrade (stendhalGradingDatum Λ G d hd) ν 0 := by
  rw [saturatedWebsterIdem_eq_blockIdem same Q Λ s]
  apply cyclotomicEquiv_mem_grade Λ G d hd ν
  apply Submodule.mem_map_of_mem
  apply blockIdem_mem_grade G (by simp)
  intro a b _ _ _ _
  exact (same _ (s.mem a)).trans (same _ (s.mem b)).symm

include same in
private theorem terminalEquiv_idem (sat : Λ 0 i = n) :
    terminalEquiv same Q Λ sat (terminalDividedIdem (ν := ν) Q) = saturatedWebsterIdem (ν := ν) Q Λ := by
  simp only [terminalEquiv, terminalDividedIdem, saturatedWebsterIdem, AlgEquiv.trans_apply,
    AlgEquiv.ofAlgHom_apply, lift_mk, cyclotomicEquiv]

include same in
theorem saturatedWebsterIdem_idempotent (sat : Λ 0 i = n) :
    IsIdempotentElem (saturatedWebsterIdem (ν := ν) Q Λ) :=
  terminalEquiv_idem same Q Λ sat ▸ (terminalDividedIdem_idempotent same Q).map (terminalEquiv same Q Λ sat)

include same in
/-- Webster, arXiv:1309.3796v2, Proposition 7.2 for a one-colour divided-power word.
The divided-power summand of the one-red Webster algebra is a simple projective. -/
theorem saturatedWebsterProjective_simple (sat : Λ 0 i = n) :
    CategoryTheory.Simple (ModuleCat.of Aᵐᵒᵖ (rIdeal (saturatedWebsterIdem (ν := ν) Q Λ))) := by
  let e := terminalEquiv same Q Λ sat
  have he : e (terminalDividedIdem (ν := ν) Q) = saturatedWebsterIdem (ν := ν) Q Λ :=
    terminalEquiv_idem same Q Λ sat
  let σ := e.op.toRingHom
  let _ : RingHomSurjective σ := ⟨e.op.surjective⟩
  let f : rIdeal (terminalDividedIdem (ν := ν) Q) →ₛₗ[σ] rIdeal (saturatedWebsterIdem (ν := ν) Q Λ) :=
    { toFun := fun x => ⟨e x.val, by
        rw [mem_rIdeal, ← he, ← map_mul, mem_rIdeal.mp x.property]⟩
      map_add' := fun x y => Subtype.ext (map_add e x.val y.val)
      map_smul' := fun a x => Subtype.ext (map_mul e x.val (unop a)) }
  have hf : Function.Bijective f := by
    refine ⟨fun x y h => Subtype.ext (e.injective (congrArg Subtype.val h)), ?_⟩
    intro y
    obtain ⟨x, hx⟩ := e.surjective y.val
    refine ⟨⟨x, mem_rIdeal.mpr (e.injective ?_)⟩, Subtype.ext hx⟩
    rw [map_mul, he, hx]
    exact mem_rIdeal.mp y.property
  exact simple_iff_isSimpleModule.mpr
    ((f.isSimpleModule_iff_of_bijective hf).mp
      (simple_iff_isSimpleModule.mp (terminalDividedProjective_simple same Q)))

include same in
theorem saturatedWebsterProjective_projective (sat : Λ 0 i = n) :
    Module.Projective Aᵐᵒᵖ (rIdeal (saturatedWebsterIdem (ν := ν) Q Λ)) :=
  rIdeal_projective (saturatedWebsterIdem_idempotent same Q Λ sat)


end Categorification.Stendhal.SingleRed

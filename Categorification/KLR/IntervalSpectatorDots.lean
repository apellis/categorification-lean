/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Mackey
import Categorification.KLR.IntervalConcat
import Categorification.KLR.IntervalPBWCoordinates

/-!
# Multiplication by interval diagrams with exterior dots

The ambient interval PBW span remains stable under multiplication on the
right by diagrams embedded between fixed exterior loadings.
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra

open MvPolynomial TypeA
open scoped TensorProduct

variable {I k : Type} [DecidableEq I] [CommRing k]
    (Q : I → I → MvPolynomial (Fin 2) k) {α β γ : Multiset I}

local notation "K" => KLRAlgebra k Q
local notation "A" => K (α + (β + γ))
local notation "M" => intervalPBWSpan Q (ν := α + (β + γ)) (p := α.card) (n := β.card)

private theorem concat_interval_spectator_polynomials
    (f : MvPolynomial (Fin α.card) k) (g : MvPolynomial (Fin β.card) k)
    (h : MvPolynomial (Fin γ.card) k) {w : List ℕ}
    (hw : ValidWord β.card w) (l : Seq α) (s : Seq β) (r : Seq γ) :
    concat Q α (β + γ) ((pol f * e l) ⊗ₜ[k]
      concat Q β γ ((ψw w * pol g * e s) ⊗ₜ[k] (pol h * e r))) =
    ψw (shiftWord α.card w) *
      pol (rename (Seq.posL (β + γ)) f *
        rename (Seq.posR α) (rename (Seq.posL γ) g * rename (Seq.posR β) h)) *
      e (l.append (s.append r)) := by
  have hw' : ValidWord (β + γ).card w := by
    intro j hj
    have h := hw j hj
    rw [Multiset.card_add]
    omega
  have inner := concat_ψw_pol_e (Q := Q) hw (validWord_nil γ.card) g h s r
  simp only [shiftWord, List.map_nil, List.append_nil, ψw_nil, one_mul] at inner
  rw [inner]
  simpa only [ψw_nil, one_mul, List.nil_append] using
    (concat_ψw_pol_e (Q := Q) (validWord_nil α.card) hw' f (rename (Seq.posL γ) g * rename (Seq.posR β) h)
      l (s.append r))

private theorem concat_spectators_mem_intervalPBWSpan (hQ : KLRSymm Q)
    (l : Seq α) (r : Seq γ) (f : MvPolynomial (Fin α.card) k)
    (h : MvPolynomial (Fin γ.card) k) (z : K β) :
    concat Q α (β + γ) ((pol f * e l) ⊗ₜ[k]
      concat Q β γ (z ⊗ₜ[k] (pol h * e r))) ∈ M := by
  let F : K β →ₗ[k] A := (concat Q α (β + γ)).comp
    (((TensorProduct.mk k _ _) (pol f * e l)).comp
      ((concat Q β γ).comp ((TensorProduct.mk k _ _).flip (pol h * e r))))
  let B := basisOfSymm hQ (canWord β.card)
    (fun w => ⟨isReduced_canWord _ w, wordProd_canWord _ w⟩)
  change z ∈ (M).comap F
  have hs : ⊤ ≤ (M).comap F := by
    rw [← B.span_eq, Submodule.span_le]
    rintro _ ⟨⟨s, v, d⟩, rfl⟩
    change concat Q α (β + γ) ((pol f * e l) ⊗ₜ[k]
      concat Q β γ (B (s,v,d) ⊗ₜ[k] (pol h * e r))) ∈ M
    rw [show B (s,v,d) = _ from basisOfSymm_apply ..,
      concat_interval_spectator_polynomials Q f _ h (validWord_canWord _ v) l s r]
    exact intervalPBWSpan_polynomial Q _ v _
  exact hs (Submodule.mem_top (x := z))

/-- Multiplying an ambient interval coefficient by a local interval diagram
preserves the interval span, including arbitrary dots on the exterior.
This is used in the kernel test following (6.21) in Webster v2, Lemma 6.8. -/
theorem intervalPBWSpan_mul_intervalConcat (hQ : KLRSymm Q) (l : Seq α) (r : Seq γ)
    (x : M) (y : K β) : x.val * intervalConcat Q l r y ∈ M := by
  classical
  obtain ⟨x, hx⟩ := x
  induction hx using Submodule.span_induction with
  | zero => simp
  | add x z hx hz hx' hz' => rw [add_mul]; exact add_mem hx' hz'
  | smul c x hx hx' => rw [smul_mul_assoc]; exact (M).smul_mem c hx'
  | mem x hx =>
    obtain ⟨s, v, d, rfl⟩ := hx
    change (ψw (shiftWord α.card (canWord β.card v)) * pol (monomial d 1) * e s : A) *
      intervalConcat Q l r y ∈ M
    by_cases hs : ∃ t : Seq β, s = l.append (t.append r)
    · obtain ⟨t, rfl⟩ := hs
      obtain ⟨⟨a, bc⟩, rfl⟩ := (expEquiv α (β + γ)).surjective d
      obtain ⟨⟨b, c⟩, rfl⟩ := (expEquiv β γ).surjective bc
      rw [monomial_expEquiv, monomial_expEquiv,
        ← concat_interval_spectator_polynomials Q _ _ _ (validWord_canWord _ v) l t r,
        intervalConcat_apply, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul]
      rw [mul_assoc, e_mul_self, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul,
        mul_assoc (pol (monomial c 1) : K γ) (e r) (e r), e_mul_self]
      exact concat_spectators_mem_intervalPBWSpan Q hQ l r _ _ _
    · have hf (t : Seq β) : intervalConcat Q l r (e t : K β) = e (l.append (t.append r)) := by
        rw [intervalConcat_apply, concat_e_tmul_e, concat_e_tmul_e]
      have hfix : intervalConcat Q l r y =
          (∑ t : Seq β, e (l.append (t.append r))) * intervalConcat Q l r y := by
        have hu : (∑ t : Seq β, e (l.append (t.append r)) : A) =
            intervalConcat Q l r (1 : K β) := by
          simp_rw [← hf]
          rw [← map_sum, sum_e]
        rw [hu, ← intervalConcat_mul, one_mul]
      have hz : (e s : A) * intervalConcat Q l r y = 0 := by
        conv_lhs => arg 2; rw [hfix]
        rw [← mul_assoc, Finset.mul_sum, Finset.sum_eq_zero, zero_mul]
        intro t _
        rw [e_mul_e, ite_eq_right (fun he => hs ⟨t, he⟩)]
      rw [mul_assoc, hz, mul_zero]
      exact zero_mem _


end Categorification.KLR.KLRAlgebra

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.BasisTheoremGeneral
import Categorification.KLR.Concat


/-!
# Concatenating a KLR interval with fixed exterior loadings

For Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8 after (6.21), the
middle KLR diagram in a marked interval can be inserted between the left and
right loading idempotents. Its crossing word and dots shift by the left
weight, while its image has the corresponding shifted PBW spanning set.
-/

namespace Categorification.KLR.KLRAlgebra

open MvPolynomial TypeA
open scoped TensorProduct

variable {I k : Type*} [DecidableEq I] [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {α β γ : Multiset I}

private theorem concat_ψw_pol_e (p : MvPolynomial (Fin β.card) k)
    (q : MvPolynomial (Fin γ.card) k) {w₁ w₂ : List ℕ}
    (hw₁ : ValidWord β.card w₁) (hw₂ : ValidWord γ.card w₂) (s : Seq β) (r : Seq γ) :
    concat Q β γ ((ψw w₁ * pol p * e s) ⊗ₜ[k] (ψw w₂ * pol q * e r)) =
      ψw (w₁ ++ shiftWord β.card w₂) *
        pol (rename (Seq.posL γ) p * rename (Seq.posR β) q) * e (s.append r) := by
  have he : concat Q β γ ((pol p * e s) ⊗ₜ[k] (pol q * e r)) =
      pol (rename (Seq.posL γ) p * rename (Seq.posR β) q) * e (s.append r) := by
    simpa only [ψw_nil, mul_one, shiftWord, List.map_nil, List.nil_append] using
      (concat_pol_ψw_e (Q := Q) p q (validWord_nil β.card) (validWord_nil γ.card) s r)
  rw [mul_assoc (ψw w₁), mul_assoc (ψw w₂), ← Algebra.TensorProduct.tmul_mul_tmul,
    concat_mul, concat_ψw_tmul_ψw hw₁ hw₂, mul_assoc, oneConcat_mul_concat, he, ← mul_assoc]

/-- The local crossing word with bottom dots is shifted by the left exterior weight.
The right exterior weight changes only the positions available for concatenation. -/
theorem concat_interval_ψw_pol_e (p : MvPolynomial (Fin β.card) k) {w : List ℕ}
    (hw : ValidWord β.card w) (l : Seq α) (s : Seq β) (r : Seq γ) :
    concat Q α (β + γ) (e l ⊗ₜ[k] concat Q β γ ((ψw w * pol p * e s) ⊗ₜ[k] e r)) =
      ψw (shiftWord α.card w) * pol (rename (Seq.posR α ∘ Seq.posL γ) p) *
        e (l.append (s.append r)) := by
  classical
  let a : MvPolynomial (Fin (β + γ).card) k := rename (Seq.posL γ) p
  have inner :
      concat Q β γ ((ψw w * pol p * e s) ⊗ₜ[k] e r) =
        ψw w * pol a * e (s.append r) := by
    simpa only [shiftWord, List.map_nil, List.append_nil, ψw_nil, map_one, one_mul, mul_one] using
      (concat_ψw_pol_e (Q := Q) p 1 hw (validWord_nil γ.card) s r)
  rw [inner]
  have hw' : ValidWord (β + γ).card w := by
    intro j hj
    have := hw j hj
    rw [Multiset.card_add]
    omega
  simpa only [a, rename_rename, map_one, one_mul, ψw_nil, List.nil_append] using
    (concat_ψw_pol_e (Q := Q) 1 a (validWord_nil α.card) hw' l (s.append r))

open Equiv PolyRep

variable (Q)

/-- Concatenation of a local KLR element with fixed exterior loading idempotents. -/
noncomputable def intervalConcat (l : Seq α) (r : Seq γ) :
    KLRAlgebra k Q β →ₗ[k] KLRAlgebra k Q (α + (β + γ)) :=
  (concat Q α (β + γ)).comp
    (((TensorProduct.mk k _ _) (e l)).comp
      ((concat Q β γ).comp ((TensorProduct.mk k _ _).flip (e r))))

theorem intervalConcat_apply (l : Seq α) (r : Seq γ) (y : KLRAlgebra k Q β) :
    intervalConcat Q l r y =
      concat Q α (β + γ) (e l ⊗ₜ[k] concat Q β γ (y ⊗ₜ[k] e r)) := rfl

/-- An interval concatenation transports products, since the exterior diagrams
are loading idempotents. -/
theorem intervalConcat_mul (l : Seq α) (r : Seq γ) (x y : KLRAlgebra k Q β) :
    intervalConcat Q l r (x * y) = intervalConcat Q l r x * intervalConcat Q l r y := by
  simp only [intervalConcat_apply]
  rw [← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, e_mul_self, ← concat_mul,
    Algebra.TensorProduct.tmul_mul_tmul, e_mul_self]

/-- For any reduced-word choice on the interval, its shifted PBW vectors with
fixed exterior idempotents span the image of interval concatenation. -/
theorem range_intervalConcat_eq_span (hsym : KLRSymm Q) (l : Seq α) (r : Seq γ)
    (ρ : Perm (Fin β.card) → List ℕ)
    (hρ : ∀ w, IsReduced β.card (ρ w) ∧ wordProd β.card (ρ w) = w) :
    LinearMap.range (intervalConcat (β := β) Q l r) =
      Submodule.span k (Set.range fun (b : Seq β × Perm (Fin β.card) × (Fin β.card →₀ ℕ)) =>
        ψw (shiftWord α.card (ρ b.2.1)) *
          pol (rename (Seq.posR α ∘ Seq.posL γ) (monomial b.2.2 1)) *
          e (l.append (b.1.append r))) := by
  let B := basisOfSymm hsym ρ hρ
  rw [← Submodule.map_top, ← B.span_eq, Submodule.map_span, ← Set.range_comp]
  apply congrArg (Submodule.span k)
  apply congrArg Set.range
  funext b
  rw [Function.comp_apply, intervalConcat_apply, show B b = _ from basisOfSymm_apply _ _ _ _,
    concat_interval_ψw_pol_e _ ((hρ b.2.1).1.1) l b.1 r]

end Categorification.KLR.KLRAlgebra

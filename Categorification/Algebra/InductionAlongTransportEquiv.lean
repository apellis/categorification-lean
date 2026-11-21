/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongAssoc

/-!
# Transporting a restriction–induction decomposition along ring isomorphisms

Given ring isomorphisms `A₀ ≃ A₀'`, `A ≃ A'`, `B ≃ B'` intertwining nonunital maps
`φ₂ : A₀ → A`, `φ₁ : A → B` with `φ₂'`, `φ₁'`, and a semilinear isomorphism `M ≃ M'`, a linear
isomorphism `Res Ind M' ≃ Ind Res M' × M'^ι` over `A'` transports to one over `A`
(`resIndEquivTransport`), and dually (`indResEquivTransport`). This is the formal step that
moves the commutation relation of `Eᵢ` and `Fᵢ` from the all-down matrix ring to the tensor
product algebra through the repaired Webster Lemma 4.29 (Webster, arXiv:1309.3796v3,
proof of Proposition 5.5).
-/

noncomputable section

namespace Categorification.InductionAlong

universe u w

section

variable {A₀ A B A₀' A' B' : Type u} [Ring A₀] [Ring A] [Ring B] [Ring A₀'] [Ring A'] [Ring B']
  {φ₂ : A₀ →ₙ+* A} {φ₁ : A →ₙ+* B} {φ₂' : A₀' →ₙ+* A'} {φ₁' : A' →ₙ+* B'}
  (a₀ : A₀ ≃+* A₀') (a : A ≃+* A') (b : B ≃+* B')
  (h₂ : ∀ t, φ₂' (a₀ t) = a (φ₂ t)) (h₁ : ∀ t, φ₁' (a t) = b (φ₁ t))
  {M M' : Type w} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A' M']
  (e : M ≃+ M') (he : ∀ (t : A) m, e (t • m) = a t • e m)

omit [Ring A₀] [Ring A₀'] in
theorem symm_smul_of_semilinear {N N' : Type*} [AddCommGroup N] [Module A N] [AddCommGroup N']
    [Module A' N'] (f : N ≃+ N') (hf : ∀ (t : A) n, f (t • n) = a t • f n) (t : A) (y : N') :
    f.symm (a t • y) = t • f.symm y := by
  apply f.injective
  rw [f.apply_symm_apply, hf, f.apply_symm_apply]

/-- The transport `Res Ind M ≃ Res Ind M'` (restriction after induction along `φ₁`). -/
def resIndTransport : Res φ₁ (Ind M φ₁) ≃+ Res φ₁' (Ind M' φ₁') :=
  Res.transport a b h₁ (Ind.transport a b h₁ e he) (Ind.transport_smul a b h₁ e he)

theorem resIndTransport_smul (t : A) (x : Res φ₁ (Ind M φ₁)) :
    resIndTransport a b h₁ e he (t • x) = a t • resIndTransport a b h₁ e he x :=
  Res.transport_smul a b h₁ _ _ t x

/-- The transport `Ind Res M ≃ Ind Res M'` (induction after restriction along `φ₂`). -/
def indResTransport : Ind (Res φ₂ M) φ₂ ≃+ Ind (Res φ₂' M') φ₂' :=
  Ind.transport a₀ a h₂ (Res.transport a₀ a h₂ e he) (Res.transport_smul a₀ a h₂ e he)

theorem indResTransport_smul (t : A) (x : Ind (Res φ₂ M) φ₂) :
    indResTransport a₀ a h₂ e he (t • x) = a t • indResTransport a₀ a h₂ e he x :=
  Ind.transport_smul a₀ a h₂ _ _ t x

/-- **Transport of `Res Ind M ≃ Ind Res M ⊕ M^ι`** along ring isomorphisms intertwining the
two nonunital maps and a semilinear isomorphism `M ≃ M'`. -/
def resIndEquivTransport (ι : Type*)
    (L : Res φ₁' (Ind M' φ₁') ≃ₗ[A'] Ind (Res φ₂' M') φ₂' × (ι → M')) :
    Res φ₁ (Ind M φ₁) ≃ₗ[A] Ind (Res φ₂ M) φ₂ × (ι → M) :=
  { ((resIndTransport a b h₁ e he).trans L.toAddEquiv).trans
      ((indResTransport a₀ a h₂ e he).prodCongr (AddEquiv.piCongrRight fun _ => e)).symm with
    map_smul' := fun t x => by
      change ((indResTransport a₀ a h₂ e he).prodCongr _).symm
          (L (resIndTransport a b h₁ e he (t • x))) =
        t • ((indResTransport a₀ a h₂ e he).prodCongr _).symm
          (L (resIndTransport a b h₁ e he x))
      rw [resIndTransport_smul, L.map_smul]
      refine symm_smul_of_semilinear a _ (fun s y => ?_) t _
      refine Prod.ext (indResTransport_smul a₀ a h₂ e he s y.1) (funext fun j => he s (y.2 j)) }

/-- **Transport of `Ind Res M ≃ Res Ind M ⊕ M^ι`** along ring isomorphisms intertwining the
two nonunital maps and a semilinear isomorphism `M ≃ M'`. -/
def indResEquivTransport (ι : Type*)
    (L : Ind (Res φ₂' M') φ₂' ≃ₗ[A'] Res φ₁' (Ind M' φ₁') × (ι → M')) :
    Ind (Res φ₂ M) φ₂ ≃ₗ[A] Res φ₁ (Ind M φ₁) × (ι → M) :=
  { ((indResTransport a₀ a h₂ e he).trans L.toAddEquiv).trans
      ((resIndTransport a b h₁ e he).prodCongr (AddEquiv.piCongrRight fun _ => e)).symm with
    map_smul' := fun t x => by
      change ((resIndTransport a b h₁ e he).prodCongr _).symm
          (L (indResTransport a₀ a h₂ e he (t • x))) =
        t • ((resIndTransport a b h₁ e he).prodCongr _).symm
          (L (indResTransport a₀ a h₂ e he x))
      rw [indResTransport_smul, L.map_smul]
      refine symm_smul_of_semilinear a _ (fun s y => ?_) t _
      refine Prod.ext (resIndTransport_smul a b h₁ e he s y.1) (funext fun j => he s (y.2 j)) }

end

end Categorification.InductionAlong

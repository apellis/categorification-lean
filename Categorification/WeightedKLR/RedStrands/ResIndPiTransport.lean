/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongTransportNaturality
import Categorification.Algebra.InductionAlongTensorFactorLiftRight

/-!
# Transporting and lifting `Res Ind M ≅ M^ι`

The case of the commutation relation `Eᵢ Fᵢ ≅ Fᵢ Eᵢ ⊕ 1^{⊕ n}` in which `Eᵢ` vanishes on the
source (Webster, arXiv:1309.3796v3, Theorem 4.31, used in the proof of Proposition 5.5 for a
colour outside the black content) is an isomorphism `Res_φ Ind_φ M ≅ M^ι`, natural in `M`.
This file provides the formal steps that move it from the all-down matrix ring to the tensor
product algebra and to the factor algebras of the last red strand:

* `resIndPiEquivTransport`, `resIndPiEquivTransport_map`: transport along ring isomorphisms
  intertwining the maps, with its naturality;
* `liftResIndPiEquiv`, `liftResIndPiEquivRight`: lifts of a natural isomorphism to modules over
  a tensor product, on the left and on the right tensor factor.
-/

namespace Categorification

open scoped TensorProduct

noncomputable section

namespace InductionAlong

universe u w

section Transport

variable {A B A' B' : Type u} [Ring A] [Ring B] [Ring A'] [Ring B']
  {φ₁ : A →ₙ+* B} {φ₁' : A' →ₙ+* B'} (a : A ≃+* A') (b : B ≃+* B')
  (h₁ : ∀ t, φ₁' (a t) = b (φ₁ t))
  {M M' M₂ M₂' : Type w} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A' M']
  [AddCommGroup M₂] [Module A M₂] [AddCommGroup M₂'] [Module A' M₂']
  (e : M ≃+ M') (he : ∀ (t : A) m, e (t • m) = a t • e m)

/-- **Transport of `Res Ind M ≃ M^ι`** along ring isomorphisms intertwining the maps and a
semilinear isomorphism `M ≃ M'`. -/
def resIndPiEquivTransport (ι : Type*) (L : Res φ₁' (Ind M' φ₁') ≃ₗ[A'] (ι → M')) :
    Res φ₁ (Ind M φ₁) ≃ₗ[A] (ι → M) :=
  { ((resIndTransport a b h₁ e he).trans L.toAddEquiv).trans
      (AddEquiv.piCongrRight fun _ => e).symm with
    map_smul' := fun t x => by
      change (AddEquiv.piCongrRight fun _ => e).symm (L (resIndTransport a b h₁ e he (t • x))) =
        t • (AddEquiv.piCongrRight fun _ => e).symm (L (resIndTransport a b h₁ e he x))
      rw [resIndTransport_smul, L.map_smul]
      exact symm_smul_of_semilinear a _ (fun s y => funext fun j => he s (y j)) t _ }

variable (e₂ : M₂ ≃+ M₂') (he₂ : ∀ (t : A) m, e₂ (t • m) = a t • e₂ m)
  (g : M →ₗ[A] M₂) (g' : M' →ₗ[A'] M₂') (hg : ∀ m, e₂ (g m) = g' (e m))

include hg in
/-- **Naturality of `resIndPiEquivTransport`**: if `L`, `L₂` carry `Res (Ind g')` to `g'^ι`, the
transports carry `Res (Ind g)` to `g^ι`. -/
theorem resIndPiEquivTransport_map (ι : Type*) (L : Res φ₁' (Ind M' φ₁') ≃ₗ[A'] (ι → M'))
    (L₂ : Res φ₁' (Ind M₂' φ₁') ≃ₗ[A'] (ι → M₂'))
    (hL : ∀ y, L₂ (Res.map (Ind.map g') y) = fun s => g' (L y s))
    (x : Res φ₁ (Ind M φ₁)) :
    resIndPiEquivTransport a b h₁ e₂ he₂ ι L₂ (Res.map (Ind.map g) x) =
      fun s => g (resIndPiEquivTransport a b h₁ e he ι L x s) := by
  funext s
  apply e₂.injective
  change e₂ (e₂.symm (L₂ (resIndTransport a b h₁ e₂ he₂ (Res.map (Ind.map g) x)) s)) =
    e₂ (g (e.symm (L (resIndTransport a b h₁ e he x) s)))
  rw [AddEquiv.apply_symm_apply, resIndTransport_map a b h₁ e he e₂ he₂ g g' hg, hL, hg,
    AddEquiv.apply_symm_apply]

end Transport

section LeftPi

variable {k : Type*} [CommRing k] {C : Type u} [Ring C] [Algebra k C] {A : Type u} [Ring A]
  [Algebra k A] (n : ℕ)

/-- The first factor of `N^n` is `(N|_A)^n`. -/
def leftFactorPiEquiv (N : Type w) [AddCommGroup N] [Module (A ⊗[k] C) N] :
    LeftFactorRes k A C (Fin n → N) ≃ₗ[A] (Fin n → LeftFactorRes k A C N) where
  toFun x := (show Fin n → N from x)
  invFun y := (show LeftFactorRes k A C (Fin n → N) from y)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem leftFactorPiEquiv_cAct (N : Type w) [AddCommGroup N] [Module (A ⊗[k] C) N] (c : C)
    (x : LeftFactorRes k A C (Fin n → N)) :
    leftFactorPiEquiv n N (leftFactorCAct c x) =
      fun s => leftFactorCAct c (leftFactorPiEquiv n N x s) := rfl

variable {B₁ : Type u} [Ring B₁] [Algebra k B₁]
  (α : A →ₙ+* B₁) (ψα : A ⊗[k] C →ₙ+* B₁ ⊗[k] C)
  (hψα : ∀ (a : A) (c : C), ψα (a ⊗ₜ c) = α a ⊗ₜ c)
  (β : A →ₙ+* B₁) (hβ : ∀ (c : k) (t : A), β (c • t) = c • β t)
  (ψβ : A ⊗[k] C →ₙ+* B₁ ⊗[k] C) (hψβ : ∀ (a : A) (c : C), ψβ (a ⊗ₜ c) = β a ⊗ₜ c)

/-- **Lifting a natural isomorphism `Res_α Ind_β ≅ id^n`** to modules over the tensor product
with `C`. -/
def liftResIndPiEquiv
    (Φ : ∀ (M : Type u) [AddCommGroup M] [Module A M], Res α (Ind M β) ≃ₗ[A] (Fin n → M))
    (hΦ : ∀ (M M' : Type u) [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
      (f : M →ₗ[A] M') (x : Res α (Ind M β)),
      Φ M' (Res.map (Ind.map f) x) = fun s => f (Φ M x s))
    (N : Type u) [AddCommGroup N] [Module k N] [Module (A ⊗[k] C) N]
    [IsScalarTower k (A ⊗[k] C) N] :
    Res ψα (IndK k N ψβ) ≃ₗ[A ⊗[k] C] (Fin n → N) :=
  linearEquivOfLeftFactor
    (((resIndLeftFactorEquiv α ψα hψα β hβ ψβ hψβ N).trans (Φ (LeftFactorRes k A C N))).trans
      (leftFactorPiEquiv (k := k) (A := A) (C := C) n N).symm)
    (fun c x => by
      apply (leftFactorPiEquiv (k := k) (A := A) (C := C) n N).injective
      simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
      rw [leftFactorPiEquiv_cAct, LinearEquiv.apply_symm_apply, resIndLeftFactorEquiv_cAct, hΦ])

end LeftPi

section RightPi

variable {k : Type*} [CommRing k] {C : Type u} [Ring C] [Algebra k C] {A : Type u} [Ring A]
  [Algebra k A] (n : ℕ)

/-- The second factor of `N^n` is `(N|_A)^n`. -/
def rightFactorPiEquiv (N : Type w) [AddCommGroup N] [Module (C ⊗[k] A) N] :
    RightFactorRes k A C (Fin n → N) ≃ₗ[A] (Fin n → RightFactorRes k A C N) where
  toFun x := (show Fin n → N from x)
  invFun y := (show RightFactorRes k A C (Fin n → N) from y)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem rightFactorPiEquiv_cAct (N : Type w) [AddCommGroup N] [Module (C ⊗[k] A) N] (c : C)
    (x : RightFactorRes k A C (Fin n → N)) :
    rightFactorPiEquiv n N (rightFactorCAct c x) =
      fun s => rightFactorCAct c (rightFactorPiEquiv n N x s) := rfl

variable {B₁ : Type u} [Ring B₁] [Algebra k B₁]
  (α : A →ₙ+* B₁) (ψα : C ⊗[k] A →ₙ+* C ⊗[k] B₁)
  (hψα : ∀ (c : C) (a : A), ψα (c ⊗ₜ a) = c ⊗ₜ α a)
  (β : A →ₙ+* B₁) (hβ : ∀ (c : k) (t : A), β (c • t) = c • β t)
  (ψβ : C ⊗[k] A →ₙ+* C ⊗[k] B₁) (hψβ : ∀ (c : C) (a : A), ψβ (c ⊗ₜ a) = c ⊗ₜ β a)

/-- **Lifting a natural isomorphism `Res_α Ind_β ≅ id^n`** to modules over the tensor product
`C ⊗ A`. -/
def liftResIndPiEquivRight
    (Φ : ∀ (M : Type u) [AddCommGroup M] [Module A M], Res α (Ind M β) ≃ₗ[A] (Fin n → M))
    (hΦ : ∀ (M M' : Type u) [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
      (f : M →ₗ[A] M') (x : Res α (Ind M β)),
      Φ M' (Res.map (Ind.map f) x) = fun s => f (Φ M x s))
    (N : Type u) [AddCommGroup N] [Module k N] [Module (C ⊗[k] A) N]
    [IsScalarTower k (C ⊗[k] A) N] :
    Res ψα (IndK k N ψβ) ≃ₗ[C ⊗[k] A] (Fin n → N) :=
  linearEquivOfRightFactor
    (((resIndRightFactorEquiv α ψα hψα β hβ ψβ hψβ N).trans (Φ (RightFactorRes k A C N))).trans
      (rightFactorPiEquiv (k := k) (A := A) (C := C) n N).symm)
    (fun c x => by
      apply (rightFactorPiEquiv (k := k) (A := A) (C := C) n N).injective
      simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
      rw [rightFactorPiEquiv_cAct, LinearEquiv.apply_symm_apply, resIndRightFactorEquiv_cAct,
        hΦ])

end RightPi

end InductionAlong

end

end Categorification

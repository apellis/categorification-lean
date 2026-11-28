/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongSigmaTransport
import Categorification.TwoRep.SumInvModuleTransfer

/-!
# Transporting Brundan's inversion relations along ring isomorphisms

Given ring isomorphisms intertwining nonunital maps `φ₂ : A₀ → A`, `φ₁ : A → B` with `φ₂'`,
`φ₁'`, and a semilinear isomorphism `M ≃ M'`, an explicit inverse of Rouquier's rightward
crossing together with the dotted counits `z ⊗ m ↦ z d^m m` (Brundan, arXiv:1501.00350v1, (1.8)),
or with the dotted units `m ↦ φ₁(1) d^m ⊗ m` ((1.9)), on `M'` gives one on `M`
(`InductionAlong.sumInvTo_transport`, `InductionAlong.sumInvFrom_transport`).

This moves the inversion relations of Webster's functors from the all-down matrix ring to the
tensor product algebra through the repaired Lemma 4.29 (arXiv:1309.3796v3).
-/

noncomputable section

namespace Categorification.InductionAlong

open CategoryTheory MulOpposite TwoRep

universe u

variable {A₀ A B A₀' A' B' : Type u} [Ring A₀] [Ring A] [Ring B] [Ring A₀'] [Ring A'] [Ring B']
  {φ₂ : A₀ →ₙ+* A} {φ₁ : A →ₙ+* B} {φ₂' : A₀' →ₙ+* A'} {φ₁' : A' →ₙ+* B'}
  (a₀ : A₀ ≃+* A₀') (a : A ≃+* A') (b : B ≃+* B')
  (h₂ : ∀ t, φ₂' (a₀ t) = a (φ₂ t)) (h₁ : ∀ t, φ₁' (a t) = b (φ₁ t))
  (M : ModuleCat.{u} A) (M' : ModuleCat.{u} A')
  (e : M ≃+ M') (he : ∀ (t : A) m, e (t • m) = a t • e m)
  {c : B} (hc : ∀ t, c * φ₁ (φ₂ t) = φ₁ (φ₂ t) * c) {c' : B'}
  (hc' : ∀ t, c' * φ₁' (φ₂' t) = φ₁' (φ₂' t) * c') (hcc : b c = c') {n : ℕ}

omit [Ring B] [Ring B'] in
theorem indResTransport_natMap_pow {d : A} (hd : Intertwines φ₂ φ₂ d) {d' : A'}
    (hd' : Intertwines φ₂' φ₂' d') (hdd : a d = d') (m : ℕ) (x : Ind (Res φ₂ M) φ₂) :
    indResTransport a₀ a h₂ e he ((natMap hd ^ m : Module.End _ _) x) =
      (natMap hd' ^ m : Module.End _ _) (indResTransport a₀ a h₂ e he x) := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, indResTransport_natMap a₀ a h₂ e he hd hd' hdd, ih,
      pow_succ', Module.End.mul_apply]

omit [Ring A₀] [Ring A₀'] in
theorem resIndTransport_resMap_natMap_pow {d : B} (hd : Intertwines φ₁ φ₁ d) {d' : B'}
    (hd' : Intertwines φ₁' φ₁' d') (hdd : b d = d') (m : ℕ) (x : Res φ₁ (Ind M φ₁)) :
    resIndTransport a b h₁ e he (Res.map (natMap hd ^ m : Module.End _ _) x) =
      Res.map (natMap hd' ^ m : Module.End _ _) (resIndTransport a b h₁ e he x) := by
  induction m generalizing x with
  | zero => exact Res.ext rfl
  | succ m ih =>
    have e₁ : ∀ {N : Type u} [AddCommGroup N] [Module B N] (f : N →ₗ[B] N) (y : Res φ₁ N),
        Res.map (φ := φ₁) (f ^ (m + 1) : Module.End _ _) y = Res.map f (Res.map (f ^ m) y) :=
      fun f y => Res.ext (by rw [Res.val_map, Res.val_map, Res.val_map, pow_succ',
        Module.End.mul_apply])
    have e₂ : ∀ {N : Type u} [AddCommGroup N] [Module B' N] (f : N →ₗ[B'] N) (y : Res φ₁' N),
        Res.map (φ := φ₁') (f ^ (m + 1) : Module.End _ _) y = Res.map f (Res.map (f ^ m) y) :=
      fun f y => Res.ext (by rw [Res.val_map, Res.val_map, Res.val_map, pow_succ',
        Module.End.mul_apply])
    rw [e₁, resIndTransport_resMap_natMap a b h₁ e he hd hd' hdd, ih, e₂]

/-- **Brundan (1.8), transported along ring isomorphisms**: an explicit inverse of
`(sigmaLin, z ⊗ m ↦ z d'^m m)` on `M'` gives one of `(sigmaLin, z ⊗ m ↦ z d^m m)` on `M`. -/
def sumInvTo_transport {d : A} (hd : Intertwines φ₂ φ₂ d) {d' : A'}
    (hd' : Intertwines φ₂' φ₂' d') (hdd : a d = d')
    (S : SumInvTo (X := ModuleCat.of A' (Ind (Res φ₂' M') φ₂'))
      (Y := ModuleCat.of A' (Res φ₁' (Ind M' φ₁'))) (Z := M')
      (ModuleCat.ofHom (sigmaLin φ₂' φ₁' hc' M'))
      (fun m => ModuleCat.ofHom (counitMap (φ := φ₂') M' ∘ₗ (natMap hd' ^ m : Module.End _ _)))
      n) :
    SumInvTo (X := ModuleCat.of A (Ind (Res φ₂ M) φ₂)) (Y := ModuleCat.of A (Res φ₁ (Ind M φ₁)))
      (Z := M) (ModuleCat.ofHom (sigmaLin φ₂ φ₁ hc M))
      (fun m => ModuleCat.ofHom (counitMap (φ := φ₂) M ∘ₗ (natMap hd ^ m : Module.End _ _))) n :=
  S.transferAdd (indResTransport a₀ a h₂ e he) (resIndTransport a b h₁ e he) e
    (fun x => resIndTransport_sigmaLin a₀ a b h₂ h₁ e he hc hc' hcc x)
    (fun m x => by
      change e (counitMap M ((natMap hd ^ m : Module.End _ _) x)) =
        counitMap M' ((natMap hd' ^ m : Module.End _ _) (indResTransport a₀ a h₂ e he x))
      rw [← indResTransport_natMap_pow a₀ a h₂ M M' e he hd hd' hdd m x,
        counitMap_indResTransport])

/-- **Brundan (1.9), transported along ring isomorphisms**: an explicit inverse of
`(sigmaLin, m ↦ φ₁'(1) d'^m ⊗ m)` on `M'` gives one of `(sigmaLin, m ↦ φ₁(1) d^m ⊗ m)` on
`M`. -/
def sumInvFrom_transport {d : B} (hd : Intertwines φ₁ φ₁ d) {d' : B'}
    (hd' : Intertwines φ₁' φ₁' d') (hdd : b d = d')
    (S : SumInvFrom (X := ModuleCat.of A' (Res φ₁' (Ind M' φ₁')))
      (Y := ModuleCat.of A' (Ind (Res φ₂' M') φ₂')) (Z := M')
      (ModuleCat.ofHom (sigmaLin φ₂' φ₁' hc' M'))
      (fun m => ModuleCat.ofHom (Res.map (natMap hd' ^ m : Module.End _ _) ∘ₗ
        unitMap (φ := φ₁') M')) n) :
    SumInvFrom (X := ModuleCat.of A (Res φ₁ (Ind M φ₁))) (Y := ModuleCat.of A (Ind (Res φ₂ M) φ₂))
      (Z := M) (ModuleCat.ofHom (sigmaLin φ₂ φ₁ hc M))
      (fun m => ModuleCat.ofHom (Res.map (natMap hd ^ m : Module.End _ _) ∘ₗ
        unitMap (φ := φ₁) M)) n :=
  S.transferAdd (resIndTransport a b h₁ e he) (indResTransport a₀ a h₂ e he) e
    (fun x => resIndTransport_sigmaLin a₀ a b h₂ h₁ e he hc hc' hcc x)
    (fun m z => by
      change resIndTransport a b h₁ e he (Res.map (natMap hd ^ m : Module.End _ _)
          (unitMap M z)) = Res.map (natMap hd' ^ m : Module.End _ _) (unitMap M' (e z))
      rw [resIndTransport_resMap_natMap_pow a b h₁ M M' e he hd hd' hdd m,
        resIndTransport_unitMap])

end Categorification.InductionAlong

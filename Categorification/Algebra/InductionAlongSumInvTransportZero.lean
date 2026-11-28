/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongSumInvTransport

/-!
# Transporting the dotted units along ring isomorphisms, with zero crossing

The case of `InductionAlong.sumInvFrom_transport` in which the crossing has zero source:
an explicit inverse of `(0, m ↦ φ₁'(1) d'^m ⊗ m) : 0 ⊕ M'^n ⟶ Res (Ind M')` gives one of
`(0, m ↦ φ₁(1) d^m ⊗ m)` on `M` (`InductionAlong.sumInvFrom_transportOfZero`). This is
Brundan's (1.9) (arXiv:1501.00350v1) at weights where `Eᵢ` vanishes, moved from the all-down
matrix ring to the tensor product algebra through the repaired Lemma 4.29 of Webster
(arXiv:1309.3796v3).
-/

noncomputable section

namespace Categorification.InductionAlong

open CategoryTheory MulOpposite TwoRep

universe u

variable {A B A' B' : Type u} [Ring A] [Ring B] [Ring A'] [Ring B']
  {φ₁ : A →ₙ+* B} {φ₁' : A' →ₙ+* B'} (a : A ≃+* A') (b : B ≃+* B')
  (h₁ : ∀ t, φ₁' (a t) = b (φ₁ t))
  (M : ModuleCat.{u} A) (M' : ModuleCat.{u} A')
  (e : M ≃+ M') (he : ∀ (t : A) m, e (t • m) = a t • e m) {n : ℕ}

/-- **Brundan (1.9) with zero crossing, transported along ring isomorphisms**: an explicit
inverse of `(0, m ↦ φ₁'(1) d'^m ⊗ m)` on `M'` gives one of `(0, m ↦ φ₁(1) d^m ⊗ m)` on `M`. -/
def sumInvFrom_transportOfZero {d : B} (hd : Intertwines φ₁ φ₁ d) {d' : B'}
    (hd' : Intertwines φ₁' φ₁' d') (hdd : b d = d')
    (S : SumInvFrom (X := ModuleCat.of A' (Res φ₁' (Ind M' φ₁')))
      (Y := ModuleCat.of A' PUnit.{u + 1}) (Z := M') 0
      (fun m => ModuleCat.ofHom (Res.map (natMap hd' ^ m : Module.End _ _) ∘ₗ
        unitMap (φ := φ₁') M')) n) :
    SumInvFrom (X := ModuleCat.of A (Res φ₁ (Ind M φ₁))) (Y := ModuleCat.of A PUnit.{u + 1})
      (Z := M) 0
      (fun m => ModuleCat.ofHom (Res.map (natMap hd ^ m : Module.End _ _) ∘ₗ
        unitMap (φ := φ₁) M)) n :=
  S.transferAdd (resIndTransport a b h₁ e he) (AddEquiv.refl _) e
    (fun _ => (map_zero _).trans rfl)
    (fun m z => by
      change resIndTransport a b h₁ e he (Res.map (natMap hd ^ m : Module.End _ _)
          (unitMap M z)) = Res.map (natMap hd' ^ m : Module.End _ _) (unitMap M' (e z))
      rw [resIndTransport_resMap_natMap_pow a b h₁ M M' e he hd hd' hdd m,
        resIndTransport_unitMap])

end Categorification.InductionAlong

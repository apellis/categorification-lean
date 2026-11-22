/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongTransportNaturality
import Categorification.Algebra.InductionAlongRes
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Transporting restriction–induction adjunctions along ring isomorphisms

For ring isomorphisms `a : A ≃+* A'`, `c : B ≃+* B'` intertwining nonunital ring maps
`φ : A → B` and `φ' : A' → B'`, restriction and induction along `φ` are those along `φ'`
conjugated by the equivalences of module categories given by restriction of scalars along `a`
and `c` (`resFunctorTransportIso`, `functorTransportIso`). Hence an adjunction
`Res_{φ'} ⊣ Ind_{φ'}` transports to an adjunction `Res_φ ⊣ Ind_φ`
(`resIndAdjunctionTransport`).

This moves the adjunction `Eᵢ ⊣ Fᵢ` of Webster, arXiv:1309.3796v3, Theorem 4.31, from the
all-down matrix rings of the categorical action to the tensor product algebras `T^λ` through the
ring isomorphisms of Lemma 4.29.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.InductionAlong

open CategoryTheory

universe u w

variable {A B A' B' : Type u} [Ring A] [Ring B] [Ring A'] [Ring B'] {φ : A →ₙ+* B}
  {φ' : A' →ₙ+* B'} (a : A ≃+* A') (c : B ≃+* B') (h : ∀ t, φ' (a t) = c (φ t))

include h

/-- Restriction along `φ` is restriction along `φ'` conjugated by restriction of scalars
along the ring isomorphisms. -/
def resFunctorTransportIso :
    ModuleCat.restrictScalars.{max u w} c.symm.toRingHom ⋙ resFunctor.{u, w} φ' ⋙
        ModuleCat.restrictScalars.{max u w} a.toRingHom ≅ resFunctor.{u, w} φ :=
  (NatIso.ofComponents
    (fun (M : ModuleCat.{max u w} B) => LinearEquiv.toModuleIso
      { Res.transport (M' := (ModuleCat.restrictScalars.{max u w} c.symm.toRingHom).obj M)
          a c h (AddEquiv.refl (M : Type (max u w))) (fun b m => by
            change b • m = c.symm (c b) • m
            rw [RingEquiv.symm_apply_apply]) with
        map_smul' := fun t x => Res.transport_smul a c h _ _ t x })
    (fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => Res.ext rfl))).symm

/-- Induction along `φ` is induction along `φ'` conjugated by restriction of scalars along the
ring isomorphisms. -/
def functorTransportIso :
    ModuleCat.restrictScalars.{max u w} a.symm.toRingHom ⋙ functor.{u, w} φ' ⋙
        ModuleCat.restrictScalars.{max u w} c.toRingHom ≅ functor.{u, w} φ :=
  (NatIso.ofComponents
    (fun (N : ModuleCat.{max u w} A) => LinearEquiv.toModuleIso
      { Ind.transport (N' := (ModuleCat.restrictScalars.{max u w} a.symm.toRingHom).obj N)
          a c h (AddEquiv.refl (N : Type (max u w))) (fun t n => by
            change t • n = a.symm (a t) • n
            rw [RingEquiv.symm_apply_apply]) with
        map_smul' := fun b x => Ind.transport_smul a c h _ _ b x })
    (fun {N N' : ModuleCat.{max u w} A} (g : N ⟶ N') => ModuleCat.hom_ext (LinearMap.ext fun x =>
      Ind.transport_map a c h _ _ _ _ g.hom
        ((ModuleCat.restrictScalars.{max u w} a.symm.toRingHom).map g).hom (fun _ => rfl) x))).symm

/-- **Transport of `Res ⊣ Ind`** along ring isomorphisms intertwining `φ` and `φ'`. -/
def resIndAdjunctionTransport (adj : resFunctor.{u, w} φ' ⊣ functor.{u, w} φ') :
    resFunctor.{u, w} φ ⊣ functor.{u, w} φ :=
  (((ModuleCat.restrictScalarsEquivalenceOfRingEquiv c).symm.toAdjunction.comp
      (adj.comp (ModuleCat.restrictScalarsEquivalenceOfRingEquiv a).toAdjunction)).ofNatIsoLeft
    (resFunctorTransportIso a c h)).ofNatIsoRight (functorTransportIso a c h)

end Categorification.InductionAlong

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.Algebra.Algebra.Equiv

/-!
# The Grothendieck group `K₀` of finitely generated projective modules

For an algebra `A` over a commutative ring `k`, `ProjK0 k A` is the Grothendieck group of the
category of finitely generated projective left `A`-modules: the free abelian group on
isomorphism classes modulo `[P ⊕ Q] = [P] + [Q]` (this split category has the same `K₀` for
short exact sequences). This is the ungraded counterpart of `Categorification.Graded.K0`, used
for the Grothendieck groups of B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, Theorem 2.19, whose induced modules are not yet graded.

The modules carry their `k`-module structure (compatible with the `A`-action), so that external
tensor products over `k` can be formed. Isomorphisms are `A`-linear equivalences.

## Main definitions and results

* `FGProj k A`: bundled finitely generated projective `A`-modules, with `FGProj.prod` and
  `FGProj.regular`.
* `ProjK0 k A`, `ProjK0.of P = [P]`; `of_eq_of_iso`, `of_prod`, `hom_ext`, `induction_on`, and
  the universal properties `lift`, `lift₂`.
* `FGProj.restrict σ P`: `P` as a module over `A'` through an isomorphism `σ : A ≃ₐ[k] A'`;
  `ProjK0.map σ`, and `ProjK0.map_of_semilinear`: a `σ`-semilinear isomorphism `X ≅ Y` gives
  `map σ [X] = [Y]`. This is the transport used for isomorphisms of modules over identified
  algebras (for example along `castW` or the associator of a triple tensor product).
-/

universe u v

noncomputable section

namespace Categorification

variable (k : Type v) [CommRing k] (A : Type u) [Ring A] [Algebra k A]

/-- A finitely generated projective left `A`-module (bundled), with a compatible `k`-module
structure. The carrier lives in the universe of `A`. -/
structure FGProj where
  /-- The underlying type. -/
  carrier : Type u
  [addCommGroup : AddCommGroup carrier]
  [module : Module A carrier]
  [moduleK : Module k carrier]
  [isScalarTower : IsScalarTower k A carrier]
  [finite : Module.Finite A carrier]
  [projective : Module.Projective A carrier]

namespace FGProj

attribute [instance] addCommGroup module moduleK isScalarTower finite projective

variable {k A}

instance : CoeSort (FGProj k A) (Type u) := ⟨carrier⟩

/-- Bundle a finitely generated projective module. -/
def of (M : Type u) [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    [Module.Finite A M] [Module.Projective A M] : FGProj k A := ⟨M⟩

/-- The direct sum `P ⊕ Q`. -/
def prod (P Q : FGProj k A) : FGProj k A := of (P.carrier × Q.carrier)

variable (k A) in
/-- The regular module `A`. -/
def regular : FGProj k A := of A

/-- Isomorphisms: `A`-linear equivalences. -/
abbrev Iso (P Q : FGProj k A) : Type u := P.carrier ≃ₗ[A] Q.carrier

variable (k A) in
/-- The setoid of isomorphism classes. -/
def isoSetoid : Setoid (FGProj k A) where
  r P Q := Nonempty (Iso P Q)
  iseqv := ⟨fun _ => ⟨LinearEquiv.refl _ _⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

variable (k A) in
/-- Isomorphism classes of finitely generated projective modules. -/
def IsoClass : Type (max v (u + 1)) := Quotient (isoSetoid k A)

/-- The isomorphism class of `P`. -/
def isoClass (P : FGProj k A) : IsoClass k A := Quotient.mk (isoSetoid k A) P

theorem isoClass_eq {P Q : FGProj k A} (e : Iso P Q) : isoClass P = isoClass Q :=
  Quotient.sound ⟨e⟩

theorem isoClass_surjective : Function.Surjective (isoClass (k := k) (A := A)) :=
  Quotient.mk_surjective

/-! ### Restriction along an isomorphism of algebras -/

variable {A' : Type u} [Ring A'] [Algebra k A']

/-- The module structure over `A'` of `P` through `σ⁻¹`. -/
abbrev restrictModule (σ : A ≃ₐ[k] A') (P : FGProj k A) : Module A' P.carrier :=
  Module.compHom P.carrier (σ.symm : A' →+* A)

/-- `P` as a module over `A'`, through an isomorphism of algebras `σ : A ≃ₐ[k] A'`. -/
def restrict (σ : A ≃ₐ[k] A') (P : FGProj k A) : FGProj k A' :=
  letI := restrictModule σ P
  haveI := RingHomInvPair.of_ringEquiv σ.toRingEquiv
  haveI := RingHomInvPair.of_ringEquiv_symm σ.toRingEquiv
  let e : P.carrier ≃ₛₗ[(σ.toRingEquiv : A →+* A')] P.carrier :=
    { AddEquiv.refl P.carrier with
      map_smul' := fun a x => by
        show a • x = σ.symm (σ a) • x
        rw [AlgEquiv.symm_apply_apply] }
  { carrier := P.carrier
    module := restrictModule σ P
    isScalarTower := ⟨fun c a x => by
      show σ.symm (c • a) • x = c • (σ.symm a • x)
      rw [map_smul, smul_assoc]⟩
    finite := Module.Finite.of_surjective e.toLinearMap e.surjective
    projective := Module.Projective.of_equiv e }

/-- A `σ`-semilinear isomorphism `X ≅ Y` is an isomorphism `restrict σ X ≅ Y`. -/
def restrictIsoOfSemilinear (σ : A ≃ₐ[k] A') (X : FGProj k A) (Y : FGProj k A')
    (e : X.carrier ≃+ Y.carrier) (he : ∀ (a : A) (x : X.carrier), e (a • x) = σ a • e x) :
    Iso (restrict σ X) Y :=
  { e with
    map_smul' := fun a x =>
      (he (σ.symm a) x).trans (congrArg (· • e x) (σ.apply_symm_apply a)) }

/-- Restriction respects isomorphisms. -/
def restrictCongr (σ : A ≃ₐ[k] A') {P Q : FGProj k A} (f : Iso P Q) :
    Iso (restrict σ P) (restrict σ Q) :=
  { f.toAddEquiv with
    map_smul' := fun a x => f.map_smul (σ.symm a) x }

/-- Restriction respects direct sums. -/
def restrictProd (σ : A ≃ₐ[k] A') (P Q : FGProj k A) :
    Iso (restrict σ (P.prod Q)) ((restrict σ P).prod (restrict σ Q)) :=
  { AddEquiv.refl (P.carrier × Q.carrier) with
    map_smul' := fun _ _ => rfl }

end FGProj

open FGProj

/-- The defining relations `[P ⊕ Q] - [P] - [Q]` of `K₀`. -/
def ProjK0.relations : Set (FreeAbelianGroup (FGProj.IsoClass k A)) :=
  {x | ∃ P Q : FGProj k A, x = .of (isoClass (P.prod Q)) - .of (isoClass P) - .of (isoClass Q)}

/-- The subgroup generated by the relations of `K₀`. -/
def ProjK0.relSubgroup : AddSubgroup (FreeAbelianGroup (FGProj.IsoClass k A)) :=
  AddSubgroup.closure (ProjK0.relations k A)

/-- **The Grothendieck group `K₀(A)`** of finitely generated projective left `A`-modules: the free
abelian group on isomorphism classes modulo `[P ⊕ Q] = [P] + [Q]`. -/
def ProjK0 : Type (max v (u + 1)) := FreeAbelianGroup (FGProj.IsoClass k A) ⧸ ProjK0.relSubgroup k A

namespace ProjK0

instance : AddCommGroup (ProjK0 k A) :=
  inferInstanceAs (AddCommGroup (FreeAbelianGroup (FGProj.IsoClass k A) ⧸ relSubgroup k A))

/-- The quotient map from the free abelian group on isomorphism classes. -/
def mk : FreeAbelianGroup (FGProj.IsoClass k A) →+ ProjK0 k A := QuotientAddGroup.mk' _

variable {k A}

theorem mk_surjective : Function.Surjective (mk k A) := QuotientAddGroup.mk'_surjective _

/-- The class `[P] ∈ K₀(A)`. -/
def of (P : FGProj k A) : ProjK0 k A := mk k A (FreeAbelianGroup.of (isoClass P))

/-- Isomorphic modules have the same class. -/
theorem of_eq_of_iso {P Q : FGProj k A} (e : P.Iso Q) : of P = of Q := by
  rw [of, of, isoClass_eq e]

/-- `[P ⊕ Q] = [P] + [Q]`. -/
theorem of_prod (P Q : FGProj k A) : of (P.prod Q) = of P + of Q := by
  have h : FreeAbelianGroup.of (isoClass (P.prod Q)) - FreeAbelianGroup.of (isoClass P) -
      FreeAbelianGroup.of (isoClass Q) ∈ relSubgroup k A :=
    AddSubgroup.subset_closure ⟨P, Q, rfl⟩
  rw [← QuotientAddGroup.eq_zero_iff] at h
  change mk k A _ = 0 at h
  rw [map_sub, map_sub, sub_sub, sub_eq_zero] at h
  exact h

/-- Additive maps out of `K₀` are determined by their values on classes `[P]`. -/
theorem hom_ext {G : Type*} [AddCommGroup G] {f g : ProjK0 k A →+ G}
    (h : ∀ P : FGProj k A, f (of P) = g (of P)) : f = g := by
  refine QuotientAddGroup.addMonoidHom_ext _ (FreeAbelianGroup.lift_ext _ _ fun c => ?_)
  obtain ⟨P, rfl⟩ := isoClass_surjective c
  exact h P

/-- Induction principle: a property of `K₀` holding on classes and closed under `0`, `+`, `-`
holds everywhere. -/
@[elab_as_elim]
theorem induction_on {motive : ProjK0 k A → Prop} (x : ProjK0 k A) (of : ∀ P, motive (of P))
    (zero : motive 0) (add : ∀ x y, motive x → motive y → motive (x + y))
    (neg : ∀ x, motive x → motive (-x)) : motive x := by
  obtain ⟨y, rfl⟩ := mk_surjective x
  induction y using FreeAbelianGroup.induction_on with
  | zero => simpa using zero
  | of c =>
    obtain ⟨P, rfl⟩ := isoClass_surjective c
    exact of P
  | neg c h => simpa using neg _ h
  | add y z hy hz => simpa using add _ _ hy hz

variable {k' : Type v} [CommRing k'] {A' : Type u} [Ring A'] [Algebra k' A']
  {G : Type*} [AddCommGroup G]

/-- The universal property of `K₀`: an isomorphism-invariant function on finitely generated
projective modules, additive on direct sums, induces an additive map on `K₀`. -/
def lift (f : FGProj k A → G) (hiso : ∀ P Q : FGProj k A, P.Iso Q → f P = f Q)
    (hadd : ∀ P Q : FGProj k A, f (P.prod Q) = f P + f Q) : ProjK0 k A →+ G :=
  QuotientAddGroup.lift (relSubgroup k A)
    (FreeAbelianGroup.lift (fun x : FGProj.IsoClass k A =>
      Quotient.lift (s := FGProj.isoSetoid k A) f (fun P Q ⟨e⟩ => hiso P Q e) x)) (by
      rw [relSubgroup, AddSubgroup.closure_le]
      rintro _ ⟨P, Q, rfl⟩
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, FreeAbelianGroup.lift_apply_of]
      show f (P.prod Q) - f P - f Q = 0
      rw [hadd]; abel)

@[simp] theorem lift_of (f : FGProj k A → G) (hiso : ∀ P Q : FGProj k A, P.Iso Q → f P = f Q)
    (hadd : ∀ P Q : FGProj k A, f (P.prod Q) = f P + f Q) (P : FGProj k A) :
    lift f hiso hadd (of P) = f P := by
  show FreeAbelianGroup.lift _ (FreeAbelianGroup.of _) = _
  rw [FreeAbelianGroup.lift_apply_of]
  rfl

/-- A biadditive map `K₀(A) × K₀(A') → G` from a function on pairs of modules which is
isomorphism-invariant and additive in each variable. -/
def lift₂ (f : FGProj k A → FGProj k' A' → G)
    (hiso₁ : ∀ (P₁ P₂ : FGProj k A) (Q : FGProj k' A'), P₁.Iso P₂ → f P₁ Q = f P₂ Q)
    (hiso₂ : ∀ (P : FGProj k A) (Q₁ Q₂ : FGProj k' A'), Q₁.Iso Q₂ → f P Q₁ = f P Q₂)
    (hadd₁ : ∀ (P₁ P₂ : FGProj k A) (Q : FGProj k' A'), f (P₁.prod P₂) Q = f P₁ Q + f P₂ Q)
    (hadd₂ : ∀ (P : FGProj k A) (Q₁ Q₂ : FGProj k' A'), f P (Q₁.prod Q₂) = f P Q₁ + f P Q₂) :
    ProjK0 k A →+ ProjK0 k' A' →+ G :=
  lift (fun P => lift (f P) (hiso₂ P) (hadd₂ P))
    (fun P₁ P₂ e => hom_ext fun Q => by rw [lift_of, lift_of, hiso₁ P₁ P₂ Q e])
    (fun P₁ P₂ => hom_ext fun Q => by rw [AddMonoidHom.add_apply, lift_of, lift_of, lift_of,
      hadd₁])

@[simp] theorem lift₂_of (f : FGProj k A → FGProj k' A' → G)
    (hiso₁ : ∀ (P₁ P₂ : FGProj k A) (Q : FGProj k' A'), P₁.Iso P₂ → f P₁ Q = f P₂ Q)
    (hiso₂ : ∀ (P : FGProj k A) (Q₁ Q₂ : FGProj k' A'), Q₁.Iso Q₂ → f P Q₁ = f P Q₂)
    (hadd₁ : ∀ (P₁ P₂ : FGProj k A) (Q : FGProj k' A'), f (P₁.prod P₂) Q = f P₁ Q + f P₂ Q)
    (hadd₂ : ∀ (P : FGProj k A) (Q₁ Q₂ : FGProj k' A'), f P (Q₁.prod Q₂) = f P Q₁ + f P Q₂)
    (P : FGProj k A) (Q : FGProj k' A') :
    lift₂ f hiso₁ hiso₂ hadd₁ hadd₂ (of P) (of Q) = f P Q := by
  rw [lift₂, lift_of, lift_of]

/-! ### Transport along an isomorphism of algebras -/

section Map

variable {A' A'' : Type u} [Ring A'] [Algebra k A'] [Ring A''] [Algebra k A'']

/-- The isomorphism `K₀(A) ≅ K₀(A')` induced by an isomorphism of algebras `σ : A ≃ₐ[k] A'`
(restriction of scalars along `σ⁻¹`). -/
def map (σ : A ≃ₐ[k] A') : ProjK0 k A →+ ProjK0 k A' :=
  lift (fun P => of (restrict σ P)) (fun _ _ e => of_eq_of_iso (restrictCongr σ e))
    (fun P Q => by rw [of_eq_of_iso (restrictProd σ P Q), of_prod])

theorem map_of (σ : A ≃ₐ[k] A') (P : FGProj k A) : map σ (of P) = of (restrict σ P) :=
  lift_of _ _ _ P

/-- **Transport of classes along a semilinear isomorphism**: an additive isomorphism `X ≅ Y`
which is semilinear along `σ : A ≃ₐ[k] A'` identifies `map σ [X]` with `[Y]`. -/
theorem map_of_semilinear (σ : A ≃ₐ[k] A') (X : FGProj k A) (Y : FGProj k A')
    (e : X.carrier ≃+ Y.carrier) (he : ∀ (a : A) (x : X.carrier), e (a • x) = σ a • e x) :
    map σ (of X) = of Y := by
  rw [map_of]
  exact of_eq_of_iso (restrictIsoOfSemilinear σ X Y e he)

theorem map_refl (x : ProjK0 k A) : map (AlgEquiv.refl : A ≃ₐ[k] A) x = x := by
  have : map (AlgEquiv.refl : A ≃ₐ[k] A) = AddMonoidHom.id _ := hom_ext fun P =>
    map_of_semilinear _ P P (AddEquiv.refl _) fun _ _ => rfl
  rw [this, AddMonoidHom.id_apply]

theorem map_trans (σ : A ≃ₐ[k] A') (τ : A' ≃ₐ[k] A'') (x : ProjK0 k A) :
    map τ (map σ x) = map (σ.trans τ) x := by
  have : (map τ).comp (map σ) = map (σ.trans τ) := hom_ext fun P => by
    rw [AddMonoidHom.comp_apply, map_of, map_of_semilinear τ (restrict σ P)
      (restrict (σ.trans τ) P) (AddEquiv.refl _) fun a x =>
        congrArg (fun b : A => b • (show P.carrier from x))
          (show σ.symm a = (σ.trans τ).symm (τ a) by
            rw [AlgEquiv.symm_trans_apply, AlgEquiv.symm_apply_apply]), map_of]
  rw [← this, AddMonoidHom.comp_apply]

theorem map_symm_map (σ : A ≃ₐ[k] A') (x : ProjK0 k A) : map σ.symm (map σ x) = x := by
  rw [map_trans, AlgEquiv.self_trans_symm, map_refl]

end Map

end ProjK0

end Categorification

end

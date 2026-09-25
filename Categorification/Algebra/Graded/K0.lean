/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.Module

/-!
# The Grothendieck group `K₀` of graded projective modules

Let `A` be a `k`-algebra graded by `𝒜 : ℤ → Submodule k A`. Following Khovanov–Lauda I
(arXiv:0803.4121v2, §2.5), `K₀(A)` is the Grothendieck group of the category `A-pmod` of
finitely generated graded projective left `A`-modules with degree-preserving morphisms, a
`ℤ[q, q⁻¹]`-module with `q` acting by the grading shift `{1}`.

## Definitions

* `GMod 𝒜` : bundled graded left `A`-modules (carrier in the universe of `A`), with the
  constructions `GMod.shift` (`M{a}`), `GMod.prod` (`M ⊕ N`), and `GMod.regular` (`A` itself).
* `GProj 𝒜` : bundled graded modules which are finitely generated and projective as `A`-modules.
* `GProj.IsoClass 𝒜` : isomorphism classes under degree-preserving isomorphisms.
* `K0 𝒜` : the free abelian group on isomorphism classes modulo `[P ⊕ Q] = [P] + [Q]`;
  `K0.of P` is the class `[P]`.
* `Module (LaurentPolynomial ℤ) (K0 𝒜)` with `T a • [P] = [P{a}]` (`K0.T_smul_of`).

## Design decisions

* **Projectivity.** An object of `A-pmod` is a graded module which is finitely generated and
  projective as an (ungraded) `A`-module. For `ℤ`-graded rings this agrees with being projective
  in the category of graded modules and degree-preserving maps, and with being finitely
  generated there (a standard fact of graded ring theory, which we do not formalize here). We use
  Mathlib's `Module.Finite` and `Module.Projective`.
* **Size.** Isomorphism classes of modules in `Type u` form a type in `Type (u + 1)`; we take
  the modules in the universe of `A` (every finitely generated projective module is isomorphic to
  one there) and accept that `K0 𝒜 : Type (max (u + 1) v)` for `A : Type u`, `k : Type v`.
  This is the literal definition, so no comparison theorem is needed.
* **Relations.** Since `A-pmod` is split (every short exact sequence of projectives splits),
  the relations `[P ⊕ Q] = [P] + [Q]` define the same group as short exact sequences would.
* **Shift convention.** `M{a}` is `M` with the grading shifted up by `a`
  (`(M{a})_d = M_{d-a}`, see `Graded.shift`), and `q^a [P] = [P{a}]`.
-/

universe u v

noncomputable section

namespace Categorification.Graded

open DirectSum

variable {k : Type v} [CommRing k] {A : Type u} [Ring A] [Algebra k A] (𝒜 : ℤ → Submodule k A)

/-- A graded left `A`-module (bundled): an `A`-module with a `ℤ`-grading `grading`
compatible with `𝒜`. The carrier lives in the universe of `A`. -/
structure GMod where
  /-- The underlying type. -/
  carrier : Type u
  [addCommGroup : AddCommGroup carrier]
  [module : Module A carrier]
  [moduleK : Module k carrier]
  [isScalarTower : IsScalarTower k A carrier]
  /-- The grading. -/
  grading : ℤ → Submodule k carrier
  [decomposition : Decomposition grading]
  [gradedSMul : SetLike.GradedSMul 𝒜 grading]

namespace GMod

attribute [instance] addCommGroup module moduleK isScalarTower decomposition gradedSMul

variable {𝒜}

instance : CoeSort (GMod 𝒜) (Type u) := ⟨carrier⟩

/-- Bundle a graded module. -/
def of (M : Type u) [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    (ℳ : ℤ → Submodule k M) [Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ] : GMod 𝒜 :=
  ⟨M, ℳ⟩

/-- The grading shift `M{a}` (grading shifted up by `a`). -/
def shift (M : GMod 𝒜) (a : ℤ) : GMod 𝒜 := of M (Graded.shift M.grading a)

/-- The direct sum `M ⊕ N`. -/
def prod (M N : GMod 𝒜) : GMod 𝒜 := of (M × N) (Graded.prod M.grading N.grading)

variable (𝒜) in
/-- The regular module `A`, graded by `𝒜`. -/
def regular [GradedAlgebra 𝒜] : GMod 𝒜 := of A 𝒜

/-- Degree-preserving isomorphisms. -/
abbrev Iso (M N : GMod 𝒜) : Type u := M.grading ≃ᵍ[A] N.grading

/-- `M{a}{b} ≅ M{a + b}`. -/
def shiftShiftIso (M : GMod 𝒜) (a b : ℤ) : Iso ((M.shift a).shift b) (M.shift (a + b)) :=
  GradedEquiv.ofEq (shift_shift M.grading a b)

/-- `M{0} ≅ M`. -/
def shiftZeroIso (M : GMod 𝒜) : Iso (M.shift 0) M :=
  GradedEquiv.ofEq (shift_zero M.grading)

/-- `(M ⊕ N){a} ≅ M{a} ⊕ N{a}`. -/
def prodShiftIso (M N : GMod 𝒜) (a : ℤ) : Iso ((M.prod N).shift a) ((M.shift a).prod (N.shift a))
    := GradedEquiv.ofEq (M := M × N) (shift_prod M.grading N.grading a)

end GMod

/-- A finitely generated graded projective left `A`-module (an object of KL I's `A-pmod`). -/
structure GProj extends GMod 𝒜 where
  [finite : Module.Finite A carrier]
  [projective : Module.Projective A carrier]

namespace GProj

attribute [instance] finite projective

variable {𝒜}

/-- The grading shift `P{a}`. -/
def shift (P : GProj 𝒜) (a : ℤ) : GProj 𝒜 :=
  { toGMod := P.toGMod.shift a
    finite := P.finite
    projective := P.projective }

/-- The direct sum `P ⊕ Q`. -/
def prod (P Q : GProj 𝒜) : GProj 𝒜 :=
  { toGMod := P.toGMod.prod Q.toGMod
    finite := inferInstanceAs (Module.Finite A (P.carrier × Q.carrier))
    projective := inferInstanceAs (Module.Projective A (P.carrier × Q.carrier)) }

variable (𝒜) in
/-- The regular module `A` as a graded projective module. -/
def regular [GradedAlgebra 𝒜] : GProj 𝒜 :=
  { toGMod := GMod.regular 𝒜
    finite := inferInstanceAs (Module.Finite A A)
    projective := inferInstanceAs (Module.Projective A A) }

/-- Degree-preserving isomorphisms. -/
abbrev Iso (P Q : GProj 𝒜) : Type u := P.toGMod.Iso Q.toGMod

variable (𝒜) in
/-- The setoid of isomorphism classes. -/
def isoSetoid : Setoid (GProj 𝒜) where
  r P Q := Nonempty (Iso P Q)
  iseqv := ⟨fun _ => ⟨GradedEquiv.refl _⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

variable (𝒜) in
/-- Isomorphism classes of finitely generated graded projective modules. -/
def IsoClass : Type _ := Quotient (isoSetoid 𝒜)

/-- The isomorphism class of `P`. -/
def isoClass (P : GProj 𝒜) : IsoClass 𝒜 := Quotient.mk (isoSetoid 𝒜) P

theorem isoClass_eq_iff {P Q : GProj 𝒜} : isoClass P = isoClass Q ↔ Nonempty (Iso P Q) :=
  Quotient.eq (r := isoSetoid 𝒜)

theorem isoClass_eq {P Q : GProj 𝒜} (e : Iso P Q) : isoClass P = isoClass Q :=
  isoClass_eq_iff.2 ⟨e⟩

theorem isoClass_surjective : Function.Surjective (isoClass (𝒜 := 𝒜)) :=
  Quotient.mk_surjective

/-- Shifting is well defined on isomorphism classes. -/
def IsoClass.shift (a : ℤ) : IsoClass 𝒜 → IsoClass 𝒜 :=
  Quotient.map (fun P => P.shift a) fun _ _ ⟨e⟩ => ⟨e.shift a⟩

@[simp] theorem IsoClass.shift_isoClass (a : ℤ) (P : GProj 𝒜) :
    IsoClass.shift a (isoClass P) = isoClass (P.shift a) := rfl

end GProj

open GProj FreeAbelianGroup

/-- The defining relations `[P ⊕ Q] - [P] - [Q]` of `K₀`. -/
def K0.relations : Set (FreeAbelianGroup (GProj.IsoClass 𝒜)) :=
  {x | ∃ P Q : GProj 𝒜, x = of (isoClass (P.prod Q)) - of (isoClass P) - of (isoClass Q)}

/-- The subgroup generated by the relations of `K₀`. -/
def K0.relSubgroup : AddSubgroup (FreeAbelianGroup (GProj.IsoClass 𝒜)) :=
  AddSubgroup.closure (K0.relations 𝒜)

/-- The Grothendieck group `K₀(A)` of finitely generated graded projective `A`-modules: the free
abelian group on isomorphism classes modulo `[P ⊕ Q] = [P] + [Q]`. -/
def K0 : Type _ := FreeAbelianGroup (GProj.IsoClass 𝒜) ⧸ K0.relSubgroup 𝒜

namespace K0

instance : AddCommGroup (K0 𝒜) :=
  inferInstanceAs (AddCommGroup (FreeAbelianGroup (GProj.IsoClass 𝒜) ⧸ K0.relSubgroup 𝒜))

/-- The quotient map from the free abelian group on isomorphism classes. -/
def mk : FreeAbelianGroup (GProj.IsoClass 𝒜) →+ K0 𝒜 := QuotientAddGroup.mk' _

variable {𝒜}

theorem mk_surjective : Function.Surjective (mk 𝒜) := QuotientAddGroup.mk'_surjective _

/-- The class `[P] ∈ K₀(A)`. -/
def of (P : GProj 𝒜) : K0 𝒜 := mk 𝒜 (FreeAbelianGroup.of (isoClass P))

/-- Isomorphic modules have the same class. -/
theorem of_eq_of_iso {P Q : GProj 𝒜} (e : P.Iso Q) : of P = of Q := by
  rw [of, of, isoClass_eq e]

/-- `[P ⊕ Q] = [P] + [Q]`. -/
theorem of_prod (P Q : GProj 𝒜) : of (P.prod Q) = of P + of Q := by
  have h : FreeAbelianGroup.of (isoClass (P.prod Q)) - FreeAbelianGroup.of (isoClass P) -
      FreeAbelianGroup.of (isoClass Q) ∈ relSubgroup 𝒜 :=
    AddSubgroup.subset_closure ⟨P, Q, rfl⟩
  rw [← QuotientAddGroup.eq_zero_iff] at h
  change mk 𝒜 _ = 0 at h
  rw [map_sub, map_sub, sub_sub, sub_eq_zero] at h
  exact h

/-- Additive maps out of `K₀` are determined by their values on classes `[P]`. -/
theorem hom_ext {G : Type*} [AddCommGroup G] {f g : K0 𝒜 →+ G}
    (h : ∀ P : GProj 𝒜, f (of P) = g (of P)) : f = g := by
  refine QuotientAddGroup.addMonoidHom_ext _ (FreeAbelianGroup.lift.ext _ _ fun c => ?_)
  obtain ⟨P, rfl⟩ := isoClass_surjective c
  exact h P

/-- Induction principle: a property of `K₀` holding on classes and closed under `0`, `+`, `-`
holds everywhere. -/
@[elab_as_elim]
theorem induction_on {motive : K0 𝒜 → Prop} (x : K0 𝒜) (of : ∀ P, motive (of P))
    (zero : motive 0) (add : ∀ x y, motive x → motive y → motive (x + y))
    (neg : ∀ x, motive x → motive (-x)) : motive x := by
  obtain ⟨y, rfl⟩ := mk_surjective x
  induction y using FreeAbelianGroup.induction_on with
  | C0 => simpa using zero
  | C1 c =>
    obtain ⟨P, rfl⟩ := isoClass_surjective c
    exact of P
  | Cn c h => simpa using neg _ h
  | Cp y z hy hz => simpa using add _ _ hy hz

/-! ### The grading shift and the `ℤ[q, q⁻¹]`-module structure -/

/-- The grading shift `{a}` on `K₀`. -/
def shiftHom (a : ℤ) : K0 𝒜 →+ K0 𝒜 :=
  QuotientAddGroup.map _ _ (FreeAbelianGroup.map (GProj.IsoClass.shift a)) <| by
    rw [relSubgroup, AddSubgroup.closure_le]
    rintro _ ⟨P, Q, rfl⟩
    apply AddSubgroup.subset_closure
    refine ⟨P.shift a, Q.shift a, ?_⟩
    simp only [map_sub, FreeAbelianGroup.map_of_apply, GProj.IsoClass.shift_isoClass]
    have e : GProj.Iso ((P.prod Q).shift a) ((P.shift a).prod (Q.shift a)) :=
      GMod.prodShiftIso P.toGMod Q.toGMod a
    rw [isoClass_eq e]

@[simp] theorem shiftHom_of (a : ℤ) (P : GProj 𝒜) : shiftHom a (of P) = of (P.shift a) := rfl

theorem shiftHom_zero : shiftHom (0 : ℤ) = AddMonoidHom.id (K0 𝒜) :=
  hom_ext fun P => by
    rw [shiftHom_of, AddMonoidHom.id_apply]
    exact of_eq_of_iso (GMod.shiftZeroIso P.toGMod)

theorem shiftHom_add (a b : ℤ) : shiftHom (a + b) = (shiftHom b).comp (shiftHom (𝒜 := 𝒜) a) :=
  hom_ext fun P => by
    rw [AddMonoidHom.comp_apply, shiftHom_of, shiftHom_of, shiftHom_of]
    exact (of_eq_of_iso (GMod.shiftShiftIso P.toGMod a b)).symm

/-- The action of `q^a` as an element of `End(K₀)`. -/
def qPow : Multiplicative ℤ →* Module.End ℤ (K0 𝒜) where
  toFun a := (shiftHom (Multiplicative.toAdd a)).toIntLinearMap
  map_one' := by
    ext x
    simp [shiftHom_zero]
  map_mul' a b := by
    ext x
    simp only [toAdd_mul, AddMonoidHom.coe_toIntLinearMap, Module.End.mul_apply]
    rw [add_comm, shiftHom_add]
    rfl

/-- `K₀(A)` is a `ℤ[q, q⁻¹]`-module, `q` acting by the grading shift `{1}`. -/
noncomputable instance : Module (LaurentPolynomial ℤ) (K0 𝒜) :=
  Module.compHom (K0 𝒜) (AddMonoidAlgebra.lift ℤ ℤ (Module.End ℤ (K0 𝒜)) qPow).toRingHom

theorem smul_def (p : LaurentPolynomial ℤ) (x : K0 𝒜) :
    p • x = AddMonoidAlgebra.lift ℤ ℤ (Module.End ℤ (K0 𝒜)) qPow p x := rfl

/-- `q^a • x = x{a}`. -/
theorem T_smul (a : ℤ) (x : K0 𝒜) : (LaurentPolynomial.T a : LaurentPolynomial ℤ) • x =
    shiftHom a x := by
  rw [smul_def, LaurentPolynomial.T, AddMonoidAlgebra.lift_single, one_smul]
  rfl

/-- `q^a [P] = [P{a}]`. -/
theorem T_smul_of (a : ℤ) (P : GProj 𝒜) :
    (LaurentPolynomial.T a : LaurentPolynomial ℤ) • of P = of (P.shift a) := by
  rw [T_smul, shiftHom_of]

end K0

end Categorification.Graded

end

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.K0

/-!
# Transport of graded `K₀` along a graded isomorphism of algebras

For a `k`-algebra isomorphism `σ : A ≃ₐ[k] A'` whose inverse is degree-preserving for gradings
`𝒜` of `A` and `𝒜'` of `A'`, a graded `A`-module `P` is a graded `A'`-module through `σ⁻¹`
(`GProj.restrict`), with the same grading. This gives a `ℤ[q, q⁻¹]`-linear map
`K0.map σ : K₀(A) → K₀(A')`, the graded analogue of `ProjK0.map`.

## Main definitions and results

* `GProj.restrict σ hσ P`: `P` as a graded `A'`-module.
* `K0.map σ hσ`: `[P] ↦ [restrict σ P]`, `ℤ[q, q⁻¹]`-linear.
* `K0.map_of_semilinear`: a degree-preserving additive isomorphism `X ≅ Y`, semilinear along `σ`,
  gives `map σ [X] = [Y]`.
-/

universe u v

noncomputable section

namespace Categorification.Graded

open DirectSum GProj

variable {k : Type v} [CommRing k] {A A' : Type u} [Ring A] [Algebra k A] [Ring A']
  [Algebra k A'] {𝒜 : ℤ → Submodule k A} {𝒜' : ℤ → Submodule k A'}
  (σ : A ≃ₐ[k] A') (hσ : ∀ ⦃d : ℤ⦄ ⦃a : A'⦄, a ∈ 𝒜' d → σ.symm a ∈ 𝒜 d)

namespace GProj

/-- `P` as a finitely generated graded projective `A'`-module, through `σ⁻¹`, with the same
grading. -/
def restrict (P : GProj 𝒜) : GProj 𝒜' :=
  letI : Module A' P.carrier := Module.compHom P.carrier (σ.symm : A' →+* A)
  haveI := RingHomInvPair.of_ringEquiv σ.toRingEquiv
  haveI := RingHomInvPair.of_ringEquiv_symm σ.toRingEquiv
  let e : P.carrier ≃ₛₗ[(σ.toRingEquiv : A →+* A')] P.carrier :=
    { AddEquiv.refl P.carrier with
      map_smul' := fun a x => by
        show a • x = σ.symm (σ a) • x
        rw [AlgEquiv.symm_apply_apply] }
  { carrier := P.carrier
    module := Module.compHom P.carrier (σ.symm : A' →+* A)
    isScalarTower := ⟨fun c a x => by
      show σ.symm (c • a) • x = c • (σ.symm a • x)
      rw [map_smul, smul_assoc]⟩
    grading := P.grading
    decomposition := P.decomposition
    gradedSMul := ⟨fun _ _ _ _ ha hx => P.gradedSMul.smul_mem (hσ ha) hx⟩
    finite := Module.Finite.of_surjective e.toLinearMap e.surjective
    projective := Module.Projective.of_equiv e }

theorem restrict_carrier (P : GProj 𝒜) : (restrict σ hσ P).carrier = P.carrier := rfl

theorem restrict_smul (P : GProj 𝒜) (a : A') (x : (restrict σ hσ P).carrier) :
    a • x = (σ.symm a • (show P.carrier from x) : P.carrier) := rfl

/-- A degree-preserving `σ`-semilinear isomorphism `X ≅ Y` is an isomorphism
`restrict σ X ≅ Y`. -/
def restrictIsoOfSemilinear (X : GProj 𝒜) (Y : GProj 𝒜') (e : X.carrier ≃+ Y.carrier)
    (he : ∀ (a : A) (x : X.carrier), e (a • x) = σ a • e x)
    (hg : ∀ ⦃d : ℤ⦄ ⦃x : X.carrier⦄, x ∈ X.grading d → e x ∈ Y.grading d)
    (hg' : ∀ ⦃d : ℤ⦄ ⦃y : Y.carrier⦄, y ∈ Y.grading d → e.symm y ∈ X.grading d) :
    (restrict σ hσ X).Iso Y where
  toLinearEquiv :=
    { e with
      map_smul' := fun a x =>
        (he (σ.symm a) x).trans (congrArg (· • e x) (σ.apply_symm_apply a)) }
  map_mem' _ _ hx := hg hx
  symm_map_mem' _ _ hy := hg' hy

/-- Restriction respects isomorphisms. -/
def restrictCongr {P Q : GProj 𝒜} (f : P.Iso Q) : (restrict σ hσ P).Iso (restrict σ hσ Q) where
  toLinearEquiv :=
    { f.toLinearEquiv.toAddEquiv with
      map_smul' := fun a x => f.toLinearEquiv.map_smul (σ.symm a) x }
  map_mem' _ _ hx := f.map_mem' hx
  symm_map_mem' _ _ hy := f.symm_map_mem' hy

/-- Restriction respects direct sums. -/
def restrictProd (P Q : GProj 𝒜) :
    (restrict σ hσ (P.prod Q)).Iso ((restrict σ hσ P).prod (restrict σ hσ Q)) where
  toLinearEquiv :=
    { AddEquiv.refl (P.carrier × Q.carrier) with
      map_smul' := fun _ _ => rfl }
  map_mem' _ _ hx := hx
  symm_map_mem' _ _ hy := hy

/-- Restriction respects grading shifts. -/
def restrictShift (P : GProj 𝒜) (a : ℤ) :
    (restrict σ hσ (P.shift a)).Iso ((restrict σ hσ P).shift a) where
  toLinearEquiv :=
    { AddEquiv.refl P.carrier with
      map_smul' := fun _ _ => rfl }
  map_mem' _ _ hx := hx
  symm_map_mem' _ _ hy := hy

end GProj

namespace K0

/-- The additive map `K₀(A) → K₀(A')`, `[P] ↦ [restrict σ P]`. -/
def mapAdd : K0 𝒜 →+ K0 𝒜' :=
  QuotientAddGroup.lift (relSubgroup 𝒜)
    ((mk 𝒜').comp (FreeAbelianGroup.lift (fun x : GProj.IsoClass 𝒜 =>
      FreeAbelianGroup.of (Quotient.map (sa := isoSetoid 𝒜) (sb := isoSetoid 𝒜')
        (restrict σ hσ) (fun _ _ ⟨e⟩ => ⟨restrictCongr σ hσ e⟩) x)))) (by
      rw [relSubgroup, AddSubgroup.closure_le]
      rintro _ ⟨P, Q, rfl⟩
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, FreeAbelianGroup.lift_apply_of,
        AddMonoidHom.comp_apply]
      change of (restrict σ hσ (P.prod Q)) - of (restrict σ hσ P) - of (restrict σ hσ Q) = 0
      rw [of_eq_of_iso (restrictProd σ hσ P Q), of_prod]
      abel)

@[simp] theorem mapAdd_of (P : GProj 𝒜) : mapAdd σ hσ (of P) = of (restrict σ hσ P) := by
  show mk 𝒜' (FreeAbelianGroup.lift _ (FreeAbelianGroup.of _)) = _
  rw [FreeAbelianGroup.lift_apply_of]
  rfl

theorem mapAdd_shiftHom (a : ℤ) (x : K0 𝒜) :
    mapAdd σ hσ (shiftHom a x) = shiftHom a (mapAdd σ hσ x) := by
  induction x using induction_on with
  | of P =>
    rw [shiftHom_of, mapAdd_of, mapAdd_of, shiftHom_of]
    exact of_eq_of_iso (restrictShift σ hσ P a)
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | neg x hx => simp only [map_neg, hx]

theorem mapAdd_smul (p : LaurentPolynomial ℤ) (x : K0 𝒜) :
    mapAdd σ hσ (p • x) = p • mapAdd σ hσ x := by
  induction p using LaurentPolynomial.induction_on' with
  | add p p' hp hp' => rw [add_smul, add_smul, map_add, hp, hp']
  | C_mul_T a c =>
    rw [mul_smul, mul_smul, T_smul, T_smul, LaurentPolynomial.C_eq_algebraMap, algebraMap_smul,
      algebraMap_smul, map_zsmul, mapAdd_shiftHom]

/-- **Transport of graded `K₀` along a graded isomorphism of algebras**: the
`ℤ[q, q⁻¹]`-linear map `K₀(A) → K₀(A')`, `[P] ↦ [P]` with `A'` acting through `σ⁻¹`. -/
def map : K0 𝒜 →ₗ[LaurentPolynomial ℤ] K0 𝒜' where
  toFun := mapAdd σ hσ
  map_add' := map_add _
  map_smul' := mapAdd_smul σ hσ

theorem map_of (P : GProj 𝒜) : map σ hσ (of P) = of (restrict σ hσ P) := mapAdd_of σ hσ P

/-- **Transport of classes along a semilinear isomorphism**: a degree-preserving additive
isomorphism `X ≅ Y`, semilinear along `σ`, identifies `map σ [X]` with `[Y]`. -/
theorem map_of_semilinear (X : GProj 𝒜) (Y : GProj 𝒜') (e : X.carrier ≃+ Y.carrier)
    (he : ∀ (a : A) (x : X.carrier), e (a • x) = σ a • e x)
    (hg : ∀ ⦃d : ℤ⦄ ⦃x : X.carrier⦄, x ∈ X.grading d → e x ∈ Y.grading d)
    (hg' : ∀ ⦃d : ℤ⦄ ⦃y : Y.carrier⦄, y ∈ Y.grading d → e.symm y ∈ X.grading d) :
    map σ hσ (of X) = of Y := by
  rw [map_of]
  exact of_eq_of_iso (restrictIsoOfSemilinear σ hσ X Y e he hg hg')

end K0

end Categorification.Graded

end

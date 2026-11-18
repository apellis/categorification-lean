/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.HomForm

/-!
# Restriction of graded modules along a graded algebra isomorphism

Let `σ : B ≃ₐ[k] A` be an isomorphism of `k`-algebras which preserves the gradings
`ℬ` and `𝒜`. Restricting the action along `σ` turns a graded `A`-module into a graded
`B`-module with the same underlying graded vector space. This preserves finitely generated
projectives, direct sums, grading shifts and degree-preserving isomorphisms, so it induces an
isomorphism of graded Grothendieck groups `K₀(A) ≅ K₀(B)` of `ℤ[q, q⁻¹]`-modules, and it
preserves the graded Hom spaces, hence the Euler form `([P], [Q]) ↦ gdim HOM(P, Q)`.

This is the formal device behind the passage between graded left and graded right projectives
along a graded antiinvolution (Webster, arXiv:1309.3796v2, §4.7, which works with right
modules), see `K0.rightTwistEquiv`.

## Main definitions and results

* `Restrict σ M`, `GMod.restrict`, `GProj.restrict` : restriction along `σ`.
* `K0.map` : the additive map on `K₀` induced by an operation on graded projectives that
  respects isomorphisms and direct sums; `K0.mapₗ` when it also respects shifts.
* `K0.restrictEquiv` : `K₀(A) ≃ K₀(B)` as `ℤ[q, q⁻¹]`-modules, `[P] ↦ [P|_σ]`.
* `GProj.homGdim_restrict`, `K0.homForm_restrictEquiv` : restriction preserves the Euler form.
-/

universe u v

noncomputable section

namespace Categorification.Graded

open DirectSum

/-! ### Restriction of graded modules -/

section Restrict

variable {k : Type v} [CommRing k] {A B : Type u} [Ring A] [Algebra k A] [Ring B] [Algebra k B]

/-- A module over `A` regarded as a module over `B` through `σ : B ≃ₐ[k] A`. A type synonym. -/
def Restrict (_σ : B ≃ₐ[k] A) (M : Type*) : Type _ := M

namespace Restrict

variable (σ : B ≃ₐ[k] A) (M : Type*) [AddCommGroup M] [Module A M] [Module k M]

instance : AddCommGroup (Restrict σ M) := inferInstanceAs (AddCommGroup M)
instance : Module k (Restrict σ M) := inferInstanceAs (Module k M)

instance : Module B (Restrict σ M) :=
  letI : Module A (Restrict σ M) := inferInstanceAs (Module A M)
  Module.compHom (Restrict σ M) (σ : B →+* A)

variable {σ M}

omit [Module k M] in
/-- `b · m = σ(b) m`. -/
theorem smul_def (b : B) (m : Restrict σ M) :
    b • m = (show Restrict σ M from (σ b • (show M from m) : M)) := rfl

variable (σ M) in
instance [IsScalarTower k A M] : IsScalarTower k B (Restrict σ M) where
  smul_assoc c b m := by
    change (σ (c • b) • (show M from m) : M) = c • (σ b • (show M from m))
    rw [map_smul, smul_assoc]

end Restrict

variable (σ : B ≃ₐ[k] A) {M : Type*} [AddCommGroup M] [Module A M] [Module k M]

/-- The grading of a restricted module: that of `M`. -/
def restrictGrading (ℳ : ℤ → Submodule k M) : ℤ → Submodule k (Restrict σ M) := ℳ

instance (ℳ : ℤ → Submodule k M) [Decomposition ℳ] : Decomposition (restrictGrading σ ℳ) :=
  inferInstanceAs (Decomposition ℳ)

variable {𝒜 : ℤ → Submodule k A} {ℬ : ℤ → Submodule k B}

/-- `σ` preserves the gradings. -/
def IsGradedAlgEquiv (σ : B ≃ₐ[k] A) (ℬ : ℤ → Submodule k B) (𝒜 : ℤ → Submodule k A) : Prop :=
  ∀ ⦃d : ℤ⦄ (b : B), σ b ∈ 𝒜 d ↔ b ∈ ℬ d

variable {σ}

theorem IsGradedAlgEquiv.symm (hσ : IsGradedAlgEquiv σ ℬ 𝒜) : IsGradedAlgEquiv σ.symm 𝒜 ℬ :=
  fun d a => by rw [← hσ, σ.apply_symm_apply]

/-- The restricted action is graded. -/
theorem restrict_gradedSMul (hσ : IsGradedAlgEquiv σ ℬ 𝒜) (ℳ : ℤ → Submodule k M)
    [SetLike.GradedSMul 𝒜 ℳ] : SetLike.GradedSMul ℬ (restrictGrading σ ℳ) where
  smul_mem {_ _} {b m} hb hm := by
    have h := SetLike.GradedSMul.smul_mem (A := 𝒜) (B := ℳ) ((hσ b).2 hb)
      (show (show M from m) ∈ ℳ _ from hm)
    exact h

/-- Restriction of a graded `A`-module along `σ`. -/
def GMod.restrict (hσ : IsGradedAlgEquiv σ ℬ 𝒜) (M : GMod 𝒜) : GMod ℬ :=
  letI := restrict_gradedSMul hσ M.grading
  GMod.of (Restrict σ M) (restrictGrading σ M.grading)

/-- Restriction of a finitely generated graded projective along `σ`. -/
def GProj.restrict (hσ : IsGradedAlgEquiv σ ℬ 𝒜) (P : GProj 𝒜) : GProj ℬ := by
  let R : A ≃+* B := σ.symm.toRingEquiv
  letI : RingHomInvPair (R : A →+* B) (R.symm : B →+* A) := .of_ringEquiv R
  letI : RingHomInvPair (R.symm : B →+* A) (R : A →+* B) := .of_ringEquiv_symm R
  letI : RingHomSurjective (R : A →+* B) := ⟨R.surjective⟩
  let e : P.carrier ≃ₛₗ[(R : A →+* B)] (P.toGMod.restrict hσ).carrier :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun a x => by
        change a • x = σ (σ.symm a) • x
        rw [σ.apply_symm_apply] }
  exact
    { toGMod := P.toGMod.restrict hσ
      finite := Module.Finite.of_surjective e.toLinearMap e.surjective
      projective := Module.Projective.of_equiv e }

variable (hσ : IsGradedAlgEquiv σ ℬ 𝒜)

/-- Isomorphisms restrict to isomorphisms. -/
def GMod.restrictIso {M N : GMod 𝒜} (f : M.Iso N) :
    (M.restrict hσ).Iso (N.restrict hσ) where
  toLinearEquiv :=
    { toFun := fun m => f (show M from m)
      invFun := fun n => f.symm (show N from n)
      left_inv := f.toLinearEquiv.left_inv
      right_inv := f.toLinearEquiv.right_inv
      map_add' := f.toLinearEquiv.map_add
      map_smul' := fun b m => f.toLinearEquiv.map_smul (σ b) m }
  map_mem' := fun _ _ h => f.map_mem h
  symm_map_mem' := fun _ _ h => f.symm_map_mem' h

/-- Restriction commutes with grading shifts. -/
def GMod.restrictShiftIso (M : GMod 𝒜) (a : ℤ) :
    ((M.shift a).restrict hσ).Iso ((M.restrict hσ).shift a) :=
  GradedEquiv.refl _

/-- Restriction commutes with direct sums. -/
def GMod.restrictProdIso (M N : GMod 𝒜) :
    ((M.prod N).restrict hσ).Iso ((M.restrict hσ).prod (N.restrict hσ)) where
  toLinearEquiv :=
    { toFun := fun x => ((show M × N from x).1, (show M × N from x).2)
      invFun := fun x => (show M from x.1, show N from x.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_mem' := fun _ _ h => h
  symm_map_mem' := fun _ _ h => h

/-- Restricting along `σ` and then along `σ⁻¹` gives back the original module. -/
def GMod.restrictRestrictIso (M : GMod 𝒜) : ((M.restrict hσ).restrict hσ.symm).Iso M where
  toLinearEquiv :=
    { toFun := fun m => (show M from m)
      invFun := fun m => m
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun a m => by
        change σ (σ.symm a) • (show M from m) = a • (show M from m)
        rw [σ.apply_symm_apply] }
  map_mem' := fun _ _ h => h
  symm_map_mem' := fun _ _ h => h

end Restrict

/-! ### Induced maps on `K₀` -/

section K0Map

variable {k : Type v} [CommRing k] {A B : Type u} [Ring A] [Algebra k A] [Ring B] [Algebra k B]
  {𝒜 : ℤ → Submodule k A} {ℬ : ℤ → Submodule k B}

namespace K0

open GProj FreeAbelianGroup

/-- The additive map on `K₀` induced by an operation on graded projectives which respects
isomorphisms and binary direct sums. -/
def map (F : GProj 𝒜 → GProj ℬ) (hF : ∀ {P Q : GProj 𝒜}, P.Iso Q → Nonempty ((F P).Iso (F Q)))
    (hprod : ∀ P Q : GProj 𝒜, Nonempty ((F (P.prod Q)).Iso ((F P).prod (F Q)))) :
    K0 𝒜 →+ K0 ℬ :=
  QuotientAddGroup.map _ _ (FreeAbelianGroup.map (Quotient.map F fun _ _ ⟨e⟩ => hF e)) <| by
    rw [relSubgroup, AddSubgroup.closure_le]
    rintro _ ⟨P, Q, rfl⟩
    apply AddSubgroup.subset_closure
    refine ⟨F P, F Q, ?_⟩
    simp only [map_sub]
    change FreeAbelianGroup.of (isoClass (F (P.prod Q))) - FreeAbelianGroup.of (isoClass (F P)) -
      FreeAbelianGroup.of (isoClass (F Q)) = _
    rw [isoClass_eq (hprod P Q).some]

@[simp] theorem map_of (F : GProj 𝒜 → GProj ℬ) (hF) (hprod) (P : GProj 𝒜) :
    map F hF hprod (of P) = of (F P) := rfl

/-- An operation on graded projectives which moreover commutes with grading shifts induces a
`ℤ[q, q⁻¹]`-linear map on `K₀`. -/
def mapₗ (F : GProj 𝒜 → GProj ℬ)
    (hF : ∀ {P Q : GProj 𝒜}, P.Iso Q → Nonempty ((F P).Iso (F Q)))
    (hprod : ∀ P Q : GProj 𝒜, Nonempty ((F (P.prod Q)).Iso ((F P).prod (F Q))))
    (hshift : ∀ (P : GProj 𝒜) (a : ℤ), Nonempty ((F (P.shift a)).Iso ((F P).shift a))) :
    K0 𝒜 →ₗ[LaurentPolynomial ℤ] K0 ℬ where
  toFun := map F hF hprod
  map_add' := map_add _
  map_smul' p x := by
    have hcomm (a : ℤ) : (map F hF hprod).comp (shiftHom a) = (shiftHom a).comp (map F hF hprod) :=
      hom_ext fun P => by
        simp only [AddMonoidHom.comp_apply, shiftHom_of, map_of]
        exact of_eq_of_iso (hshift P a).some
    simp only [RingHom.id_apply, smul_def]
    induction p using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
    | single a n =>
      rw [AddMonoidAlgebra.lift_single, AddMonoidAlgebra.lift_single]
      change map F hF hprod (n • shiftHom a x) = n • shiftHom a (map F hF hprod x)
      rw [map_zsmul]
      exact congrArg (n • ·) (DFunLike.congr_fun (hcomm a) x)

@[simp] theorem mapₗ_of (F : GProj 𝒜 → GProj ℬ) (hF) (hprod) (hshift) (P : GProj 𝒜) :
    mapₗ F hF hprod hshift (of P) = of (F P) := rfl

end K0

end K0Map

/-! ### Restriction on `K₀` -/

section K0Restrict

variable {k : Type v} [CommRing k] {A B : Type u} [Ring A] [Algebra k A] [Ring B] [Algebra k B]
  {𝒜 : ℤ → Submodule k A} {ℬ : ℤ → Submodule k B} {σ : B ≃ₐ[k] A}
  (hσ : IsGradedAlgEquiv σ ℬ 𝒜)

namespace K0

/-- Restriction along `σ` on `K₀`, as a map of `ℤ[q, q⁻¹]`-modules. -/
def restrict : K0 𝒜 →ₗ[LaurentPolynomial ℤ] K0 ℬ :=
  mapₗ (GProj.restrict hσ) (fun e => ⟨GMod.restrictIso hσ e⟩)
    (fun P Q => ⟨GMod.restrictProdIso hσ P.toGMod Q.toGMod⟩)
    (fun P a => ⟨GMod.restrictShiftIso hσ P.toGMod a⟩)

@[simp] theorem restrict_of (P : GProj 𝒜) : restrict hσ (of P) = of (P.restrict hσ) := rfl

theorem restrict_restrict (x : K0 𝒜) : restrict hσ.symm (restrict hσ x) = x := by
  induction x using induction_on with
  | of P => exact of_eq_of_iso (GMod.restrictRestrictIso hσ P.toGMod)
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | neg x hx => simp [hx]

/-- **Restriction along a graded algebra isomorphism identifies the graded Grothendieck
groups** as `ℤ[q, q⁻¹]`-modules. -/
def restrictEquiv : K0 𝒜 ≃ₗ[LaurentPolynomial ℤ] K0 ℬ :=
  { restrict hσ with
    invFun := restrict hσ.symm
    left_inv := restrict_restrict hσ
    right_inv := restrict_restrict hσ.symm }

@[simp] theorem restrictEquiv_of (P : GProj 𝒜) :
    restrictEquiv hσ (of P) = of (P.restrict hσ) := rfl

end K0

end K0Restrict

/-! ### Restriction preserves graded Hom spaces -/

section HomRestrict

variable {k : Type v} [Field k] {A B : Type u} [Ring A] [Algebra k A] [Ring B] [Algebra k B]
  {𝒜 : ℤ → Submodule k A} {ℬ : ℤ → Submodule k B} {σ : B ≃ₐ[k] A}
  (hσ : IsGradedAlgEquiv σ ℬ 𝒜)

/-- A `B`-linear map between restrictions is an `A`-linear map. -/
def restrictHomEquiv (M N : Type*) [AddCommGroup M] [Module A M] [Module k M]
    [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N] :
    (Restrict σ M →ₗ[B] Restrict σ N) ≃ₗ[k] (M →ₗ[A] N) where
  toFun f :=
    { toFun := fun x => f x
      map_add' := f.map_add
      map_smul' := fun a x => by
        have h := f.map_smul (σ.symm a) x
        change f (show Restrict σ M from (σ (σ.symm a) • x : M)) =
          (show N from (σ (σ.symm a) • (show N from f x) : N)) at h
        rwa [σ.apply_symm_apply] at h }
  invFun g :=
    { toFun := fun x => g x
      map_add' := g.map_add
      map_smul' := fun b x => g.map_smul (σ b) x }
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The graded Hom spaces of restricted modules are those of the original modules. -/
def homGradeRestrictEquiv (M N : GMod 𝒜) (d : ℤ) :
    homGrade B (M.restrict hσ).grading (N.restrict hσ).grading d ≃ₗ[k]
      homGrade A M.grading N.grading d :=
  (restrictHomEquiv (σ := σ) M N).ofSubmodules _ _ (by
    ext f
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact fun _ _ hx => hg hx
    · intro hf
      refine ⟨(restrictHomEquiv (σ := σ) M N).symm f, fun _ _ hx => hf hx, rfl⟩)

/-- `gdim HOM(P|_σ, Q|_σ) = gdim HOM(P, Q)`. -/
theorem GProj.homGdim_restrict (P Q : GProj 𝒜) :
    (P.restrict hσ).homGdim (Q.restrict hσ) = P.homGdim Q :=
  gdim_eq_of_finrank_eq fun d => (homGradeRestrictEquiv hσ P.toGMod Q.toGMod d).finrank_eq

/-- **Restriction preserves the Euler form** `([P], [Q]) ↦ gdim HOM(P, Q)` on `K₀`. -/
theorem K0.homForm_restrictEquiv [GradedAlgebra 𝒜] [HasGdim 𝒜] [GradedAlgebra ℬ] [HasGdim ℬ]
    (x y : K0 𝒜) :
    K0.homForm ℬ (K0.restrictEquiv hσ x) (K0.restrictEquiv hσ y) = K0.homForm 𝒜 x y := by
  induction x using K0.induction_on with
  | of P =>
    induction y using K0.induction_on with
    | of Q => simp only [K0.restrictEquiv_of, K0.homForm_of, GProj.homGdim_restrict]
    | zero => simp
    | add y z hy hz => rw [map_add, map_add, map_add, hy, hz]
    | neg y hy => rw [map_neg, map_neg, map_neg, hy]
  | zero => simp
  | add x z hx hz => simp only [map_add, AddMonoidHom.add_apply, hx, hz]
  | neg x hx => simp only [map_neg, AddMonoidHom.neg_apply, hx]

end HomRestrict

end Categorification.Graded

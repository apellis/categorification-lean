/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.TensorRepresentedIso
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.StdBasis

/-!
# Finitely generated projective representing bimodules

For a functor `F : ModuleCat B ⥤ ModuleCat A` represented by tensoring with `F(B)`
(`IsTensorRepresented`), we record when the representing bimodule `F(B)` is finitely generated
and projective as a right `B`-module (`TensorRepresented.IsFinProj`). This is closed under
composition of represented functors (`IsFinProj.comp`), because a tensor product `M ⊗_A N` of a
finitely generated projective right `A`-module `M` with an `(A, B)`-bimodule `N` that is finitely
generated projective over `B` is finitely generated projective over `B`
(`projective_tensorProductOver`, `finite_tensorProductOver`). It holds
for restriction of scalars and for the identity, and is invariant under natural isomorphism.

Used for the standard bimodules of B. Webster, *Knot invariants and higher representation
theory*, arXiv:1309.3796v3, §5, which are finitely generated projective over the block algebras;
this is the projectivity needed to identify the standardization functors on derived categories
with derived tensor products in the proof of Lemma 7.19.
-/

noncomputable section

namespace Categorification

open CategoryTheory DG MulOpposite
open scoped DG.TensorProductOver.RightAction

universe u

namespace TensorRepresented

variable {A B : Type*} [Ring A] [Ring B] {M M' : Type*} [AddCommGroup M] [Module Aᵐᵒᵖ M]
  [AddCommGroup M'] [Module Aᵐᵒᵖ M'] (N : Type*) [AddCommGroup N] [Module A N]
  [Module Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N]

/-- `f ⊗ 1 : M ⊗_A N → M' ⊗_A N`, as a map of right `B`-modules. -/
def tensorMapLeft (f : M →ₗ[Aᵐᵒᵖ] M') :
    TensorProductOver A M N →ₗ[Bᵐᵒᵖ] TensorProductOver A M' N where
  toFun := TensorProductOver.map f LinearMap.id
  map_add' := map_add _
  map_smul' b t := by
    induction t using TensorProductOver.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | tmul m n => rfl
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

theorem tensorMapLeft_tmul (f : M →ₗ[Aᵐᵒᵖ] M') (m : M) (n : N) :
    tensorMapLeft (B := B) N f (TensorProductOver.tmul A m n) =
      TensorProductOver.tmul A (f m) n := rfl

theorem tensorMapLeft_comp {M'' : Type*} [AddCommGroup M''] [Module Aᵐᵒᵖ M''] (f : M →ₗ[Aᵐᵒᵖ] M')
    (f' : M' →ₗ[Aᵐᵒᵖ] M'') :
    (tensorMapLeft (B := B) N f').comp (tensorMapLeft N f) = tensorMapLeft N (f'.comp f) :=
  LinearMap.ext fun t => by
    induction t using TensorProductOver.induction_on with
    | zero => simp only [map_zero]
    | tmul m n => rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem tensorMapLeft_id : tensorMapLeft (B := B) N (LinearMap.id : M →ₗ[Aᵐᵒᵖ] M) = LinearMap.id :=
  LinearMap.ext fun t => by
    induction t using TensorProductOver.induction_on with
    | zero => simp only [map_zero]
    | tmul m n => rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]

variable (n : ℕ)

/-- The bi-additive map `(x, m) ↦ (x_i m)_i`. -/
def piTensorBil : (Fin n → A) →+ N →+ (Fin n → N) where
  toFun x :=
    { toFun := fun m i => x i • m
      map_zero' := funext fun _ => smul_zero _
      map_add' := fun m m' => funext fun _ => smul_add _ m m' }
  map_zero' := by ext m i; exact zero_smul A m
  map_add' x y := by ext m i; exact add_smul (x i) (y i) m

/-- The `i`-th standard basis vector of `A^n`. -/
def basisVec (i : Fin n) : Fin n → A := Pi.single i 1

theorem basisVec_apply (i j : Fin n) : basisVec (A := A) n i j = if j = i then 1 else 0 := by
  by_cases h : j = i
  · subst h; simp [basisVec]
  · simp [basisVec, h]

theorem sum_op_smul_basisVec (x : Fin n → A) : ∑ i, op (x i) • basisVec n i = x := by
  funext j
  rw [Finset.sum_apply]
  change ∑ i, basisVec n i j * x i = x j
  simp [basisVec_apply]

/-- `A^n ⊗_A N → N^n`, `x ⊗ m ↦ (x_i m)_i`. -/
def piTensorMap : TensorProductOver A (Fin n → A) N →+ (Fin n → N) :=
  TensorProductOver.lift (piTensorBil N n) fun a x m => funext fun i => by
    change (x i * a) • m = x i • a • m
    exact mul_smul _ _ _

theorem piTensorMap_tmul (x : Fin n → A) (m : N) :
    piTensorMap N n (TensorProductOver.tmul A x m) = fun i => x i • m := rfl

/-- `N^n → A^n ⊗_A N`, `g ↦ ∑_i e_i ⊗ g_i`. -/
def piTensorInv : (Fin n → N) →+ TensorProductOver A (Fin n → A) N where
  toFun g := ∑ i, TensorProductOver.tmul A (basisVec n i) (g i)
  map_zero' := by simp only [Pi.zero_apply, TensorProductOver.tmul_zero, Finset.sum_const_zero]
  map_add' g g' := by
    simp only [Pi.add_apply, TensorProductOver.tmul_add, Finset.sum_add_distrib]

theorem piTensorInv_map (t : TensorProductOver A (Fin n → A) N) :
    piTensorInv N n (piTensorMap N n t) = t := by
  induction t using TensorProductOver.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul x m =>
    change ∑ i, TensorProductOver.tmul A (basisVec n i) (x i • m) = _
    simp only [← TensorProductOver.op_smul_tmul]
    conv_rhs => rw [← sum_op_smul_basisVec n x]
    rw [← TensorProductOver.tmulAddHom_apply, map_sum, AddMonoidHom.finsetSum_apply]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem piTensorMap_inv (g : Fin n → N) :
    piTensorMap N n (piTensorInv (A := A) N n g) = g := by
  change piTensorMap N n (∑ i, TensorProductOver.tmul A (basisVec n i) (g i)) = g
  rw [map_sum]
  funext j
  rw [Finset.sum_apply]
  change ∑ i, basisVec (A := A) n i j • g i = g j
  simp [basisVec_apply]

theorem piTensorMap_smul (b : Bᵐᵒᵖ) (t : TensorProductOver A (Fin n → A) N) :
    piTensorMap N n (b • t) = b • piTensorMap N n t := by
  induction t using TensorProductOver.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul x m =>
    funext i
    exact smul_comm (x i) b m
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- `A^n ⊗_A N ≅ N^n`, `x ⊗ m ↦ (x_i m)_i`, as right `B`-modules. -/
def piTensorEquiv : TensorProductOver A (Fin n → A) N ≃ₗ[Bᵐᵒᵖ] (Fin n → N) where
  toFun := piTensorMap N n
  invFun := piTensorInv (A := A) N n
  map_add' := map_add _
  map_smul' := piTensorMap_smul N n
  left_inv := piTensorInv_map N n
  right_inv := piTensorMap_inv N n

/-- A finitely generated right `A`-module is a quotient of `A^n` for some `n`. -/
theorem exists_surjective_pi [Module.Finite Aᵐᵒᵖ M] :
    ∃ (n : ℕ) (σ : (Fin n → A) →ₗ[Aᵐᵒᵖ] M), Function.Surjective σ := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := Aᵐᵒᵖ) (M := M)
  refine ⟨n, { toFun := fun x => ∑ i, op (x i) • s i
               map_add' := fun x y => by simp [add_smul, Finset.sum_add_distrib]
               map_smul' := fun a x => by
                 simp only [RingHom.id_apply, Finset.smul_sum, ← mul_smul]
                 rfl }, ?_⟩
  rw [← LinearMap.range_eq_top, eq_top_iff, ← hs, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  refine ⟨basisVec n i, ?_⟩
  change ∑ j, op (basisVec n i j) • s j = s i
  simp [basisVec_apply, apply_ite op]

/-- `M ⊗_A N` is a retract of `N^n` as a right `B`-module, for `M` finitely generated projective
over `A`. -/
theorem tensor_exists_retract_pi [Module.Projective Aᵐᵒᵖ M] [Module.Finite Aᵐᵒᵖ M] :
    ∃ (n : ℕ) (i : TensorProductOver A M N →ₗ[Bᵐᵒᵖ] (Fin n → N))
      (s : (Fin n → N) →ₗ[Bᵐᵒᵖ] TensorProductOver A M N), s.comp i = LinearMap.id := by
  obtain ⟨n, σ, hσ⟩ := exists_surjective_pi (A := A) (M := M)
  obtain ⟨h, hh⟩ := Module.projective_lifting_property σ LinearMap.id hσ
  refine ⟨n, (piTensorEquiv (B := B) N n).toLinearMap.comp (tensorMapLeft N h),
    (tensorMapLeft N σ).comp (piTensorEquiv N n).symm.toLinearMap, ?_⟩
  rw [LinearMap.comp_assoc, ← LinearMap.comp_assoc (tensorMapLeft N h),
    LinearEquiv.symm_comp, LinearMap.id_comp, tensorMapLeft_comp, hh, tensorMapLeft_id]

/-- **`M ⊗_A N` is projective over `B`** for `M` finitely generated projective over `A` and `N`
projective over `B`. -/
theorem projective_tensorProductOver [Module.Projective Aᵐᵒᵖ M] [Module.Finite Aᵐᵒᵖ M]
    [Module.Projective Bᵐᵒᵖ N] : Module.Projective Bᵐᵒᵖ (TensorProductOver A M N) := by
  obtain ⟨n, i, s, h⟩ := tensor_exists_retract_pi (A := A) (B := B) (M := M) N
  have : Module.Projective Bᵐᵒᵖ (Fin n → N) :=
    Module.Projective.of_equiv (DFinsupp.linearEquivFunOnFintype (R := Bᵐᵒᵖ)
      (M := fun _ : Fin n => N))
  exact Module.Projective.of_split i s h

/-- **`M ⊗_A N` is finitely generated over `B`** for `M` finitely generated projective over `A`
and `N` finitely generated over `B`. -/
theorem finite_tensorProductOver [Module.Projective Aᵐᵒᵖ M] [Module.Finite Aᵐᵒᵖ M]
    [Module.Finite Bᵐᵒᵖ N] : Module.Finite Bᵐᵒᵖ (TensorProductOver A M N) := by
  obtain ⟨n, i, s, h⟩ := tensor_exists_retract_pi (A := A) (B := B) (M := M) N
  exact Module.Finite.of_surjective s fun t => ⟨i t, LinearMap.congr_fun h t⟩


section IdemCoords

variable (R : Type*) [Ring R] {ι : Type*} (e : ι → R)

/-- The families `(g_i)` with `g_i ∈ e_i R`, as a right `R`-submodule of `R^ι`. -/
def idemCoords : Submodule Rᵐᵒᵖ (ι → R) where
  carrier := {g | ∀ i, e i * g i = g i}
  add_mem' {g g'} hg hg' i := by
    change e i * (g i + g' i) = g i + g' i
    rw [mul_add, hg i, hg' i]
  zero_mem' i := mul_zero (e i)
  smul_mem' b g hg i := by
    change e i * (g i * b.unop) = g i * b.unop
    rw [← mul_assoc, hg i]

/-- `R^ι ≅ (Rᵐᵒᵖ)^ι` as right `R`-modules. -/
def piOpEquiv : (ι → R) ≃ₗ[Rᵐᵒᵖ] (ι → Rᵐᵒᵖ) where
  toFun g i := op (g i)
  invFun g i := (g i).unop
  map_add' _ _ := rfl
  map_smul' b g := funext fun i => by
    change op (g i * b.unop) = b * op (g i)
    rw [op_mul, op_unop]
  left_inv _ := rfl
  right_inv _ := rfl

variable {e}

/-- The projection `g ↦ (e_i g_i)_i` onto `idemCoords`. -/
def idemCoordsProj (he : ∀ i, IsIdempotentElem (e i)) : (ι → R) →ₗ[Rᵐᵒᵖ] idemCoords R e where
  toFun g := ⟨fun i => e i * g i, fun i => by rw [← mul_assoc, (he i).eq]⟩
  map_add' g g' := Subtype.ext (funext fun i => mul_add (e i) (g i) (g' i))
  map_smul' b g := Subtype.ext (funext fun i => (mul_assoc (e i) (g i) b.unop).symm)

theorem idemCoordsProj_comp_subtype (he : ∀ i, IsIdempotentElem (e i)) :
    (idemCoordsProj R he).comp (idemCoords R e).subtype = LinearMap.id :=
  LinearMap.ext fun g => Subtype.ext (funext fun i => g.2 i)

/-- **A sum of right ideals `e_i R` for idempotents `e_i` is projective.** -/
theorem projective_idemCoords [Finite ι] (he : ∀ i, IsIdempotentElem (e i)) :
    Module.Projective Rᵐᵒᵖ (idemCoords R e) :=
  have : Module.Projective Rᵐᵒᵖ (ι → Rᵐᵒᵖ) := Module.Projective.of_basis (Pi.basisFun Rᵐᵒᵖ ι)
  have : Module.Projective Rᵐᵒᵖ (ι → R) := Module.Projective.of_equiv (piOpEquiv R).symm
  Module.Projective.of_split _ _ (idemCoordsProj_comp_subtype R he)

/-- **A finite sum of right ideals `e_i R` for idempotents `e_i` is finitely generated.** -/
theorem finite_idemCoords [Finite ι] (he : ∀ i, IsIdempotentElem (e i)) :
    Module.Finite Rᵐᵒᵖ (idemCoords R e) :=
  have : Module.Finite Rᵐᵒᵖ (ι → R) := Module.Finite.equiv (piOpEquiv R).symm
  Module.Finite.of_surjective (idemCoordsProj R he) fun g =>
    ⟨g.1, LinearMap.congr_fun (idemCoordsProj_comp_subtype R he) g⟩

end IdemCoords

section IsFinProj

variable {A B C : Type u} [Ring A] [Ring B] [Ring C]

/-- The representing bimodule `F(B)` is **finitely generated projective as a right `B`-module**.
-/
structure IsFinProj (F : ModuleCat.{u} B ⥤ ModuleCat.{u} A) [F.Additive] : Prop where
  projective : Module.Projective Bᵐᵒᵖ (Bimod F)
  finite : Module.Finite Bᵐᵒᵖ (Bimod F)

theorem IsFinProj.of_equiv {F : ModuleCat.{u} B ⥤ ModuleCat.{u} A} [F.Additive]
    {M : Type u} [AddCommGroup M] [Module Bᵐᵒᵖ M] [Module.Projective Bᵐᵒᵖ M]
    [Module.Finite Bᵐᵒᵖ M] (e : M ≃ₗ[Bᵐᵒᵖ] Bimod F) : IsFinProj F :=
  ⟨Module.Projective.of_equiv e, Module.Finite.equiv e⟩

/-- Finite projectivity of the representing bimodule is invariant under natural isomorphism. -/
theorem IsFinProj.of_iso {F G : ModuleCat.{u} B ⥤ ModuleCat.{u} A} [F.Additive] [G.Additive]
    (e : F ≅ G) (hF : IsFinProj F) : IsFinProj G :=
  have := hF.projective
  have := hF.finite
  IsFinProj.of_equiv (bimodEquivOfIso e)

/-- **Finite projectivity of representing bimodules is closed under composition.** -/
theorem IsFinProj.comp {F : ModuleCat.{u} B ⥤ ModuleCat.{u} A} {G : ModuleCat.{u} A ⥤
    ModuleCat.{u} C} [F.Additive] [G.Additive] (hG : IsTensorRepresented G) (hFp : IsFinProj F)
    (hGp : IsFinProj G) : IsFinProj (F ⋙ G) :=
  have := hFp.projective
  have := hFp.finite
  have := hGp.projective
  have := hGp.finite
  have := projective_tensorProductOver (A := A) (B := B) (M := Bimod G) (Bimod F)
  have := finite_tensorProductOver (A := A) (B := B) (M := Bimod G) (Bimod F)
  IsFinProj.of_equiv (compBimodEquiv F G hG)

/-- The representing bimodule of a restriction of scalars along `φ : B → B'` is `B'`. -/
def restrictScalarsBimodEquiv {B' : Type u} [Ring B'] (φ : B →+* B') :
    B'ᵐᵒᵖ ≃ₗ[B'ᵐᵒᵖ] Bimod (ModuleCat.restrictScalars.{u} φ) where
  toFun b := (show B' from b.unop)
  invFun p := op (show B' from p)
  map_add' _ _ := rfl
  map_smul' b c := by
    change unop (b * c) = (show B' from unop c) • unop b
    rw [unop_mul, smul_eq_mul]
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The representing bimodule of a restriction of scalars is free of rank one.** -/
theorem isFinProj_restrictScalars {B' : Type u} [Ring B'] (φ : B →+* B') :
    IsFinProj (ModuleCat.restrictScalars.{u} φ) :=
  IsFinProj.of_equiv (restrictScalarsBimodEquiv φ)

/-- The representing bimodule of the identity functor is free of rank one. -/
theorem isFinProj_id : IsFinProj (𝟭 (ModuleCat.{u} B)) :=
  IsFinProj.of_iso (ModuleCat.restrictScalarsId' (RingHom.id B) rfl)
    (isFinProj_restrictScalars (RingHom.id B))

end IsFinProj

end TensorRepresented

end Categorification

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.ResTowerNilHecke

/-!
# Rouquier's rightward crossing for induction along a tower of rings

Let `φ₁ : A₀ → A₁` and `φ₂ : A₁ → A₂` be nonunital ring maps, and let `c ∈ A₂` commute with the
image of `φ₂ ∘ φ₁` and satisfy `φ₂(1) c = c`. Left multiplication by `c` on `Res_{φ₁} Res_{φ₂}`
(`resAct₂`) is a crossing on restriction; its mate `τ` through `Ind ⊣ Res` is a crossing on
induction. Rouquier's rightward crossing (Brundan, arXiv:1501.00350v1, (1.6))

`σ : Ind_{φ₁} Res_{φ₁} ⟶ Res_{φ₂} Ind_{φ₂}`,  `σ = (η₂ on the right) · τ · (ε₁ on the left)`,

is then the explicit map `z ⊗ m ↦ φ₂(z) c φ₂(1) ⊗ m` (`InductionAlong.sigma_app`, with the map
`sigmaLin`). This describes the rightward crossing of Webster's induction and restriction
functors on modules over `T^λ` (arXiv:1309.3796v3, §4.6, Theorem 4.31).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.InductionAlong

open CategoryTheory MulOpposite

universe u

variable {A₀ A₁ A₂ : Type u} [Ring A₀] [Ring A₁] [Ring A₂] (φ₁ : A₀ →ₙ+* A₁) (φ₂ : A₁ →ₙ+* A₂)
  {c : A₂} (hc : ∀ a, c * φ₂ (φ₁ a) = φ₂ (φ₁ a) * c)

/-- The corner element `φ₂(z) c φ₂(1)` of `z ∈ A₁ φ₁(1)`. -/
def sigmaElt (c : A₂) (z : Corner φ₁) : Corner φ₂ :=
  ⟨φ₂ z.1 * (c * φ₂ 1), by
    change φ₂ z.1 * (c * φ₂ 1) * φ₂ 1 = φ₂ z.1 * (c * φ₂ 1)
    rw [mul_assoc, mul_assoc, ← map_mul, one_mul]⟩

@[simp] theorem sigmaElt_val (c : A₂) (z : Corner φ₁) :
    (sigmaElt φ₁ φ₂ c z).1 = φ₂ z.1 * (c * φ₂ 1) := rfl

include hc in
theorem sigmaElt_op_smul (z : Corner φ₁) (a : A₀) :
    sigmaElt φ₁ φ₂ c (op a • z) = op (φ₁ a) • sigmaElt φ₁ φ₂ c z := by
  apply Subtype.ext
  change φ₂ (z.1 * φ₁ a) * (c * φ₂ 1) = φ₂ z.1 * (c * φ₂ 1) * φ₂ (φ₁ a)
  have h1 : φ₂ (φ₁ a) * φ₂ 1 = φ₂ (φ₁ a) := by rw [← map_mul, mul_one]
  have h2 : φ₂ 1 * φ₂ (φ₁ a) = φ₂ (φ₁ a) := by rw [← map_mul, one_mul]
  rw [map_mul, mul_assoc, ← mul_assoc (φ₂ (φ₁ a)), ← hc, mul_assoc, mul_assoc, mul_assoc,
    h1, h2]

/-- **Rouquier's rightward crossing**, `Ind_{φ₁} Res_{φ₁} M → Res_{φ₂} Ind_{φ₂} M`,
`z ⊗ m ↦ φ₂(z) c φ₂(1) ⊗ m`. -/
def sigmaLin (M : Type u) [AddCommGroup M] [Module A₁ M] :
    Ind (Res φ₁ M) φ₁ →ₗ[A₁] Res φ₂ (Ind M φ₂) :=
  Ind.lift (fun z m => Res.mk (Ind.tmul (sigmaElt φ₁ φ₂ c z) m.val) (by
      rw [Ind.smul_tmul]
      congr 1
      apply Subtype.ext
      change φ₂ 1 * (φ₂ z.1 * (c * φ₂ 1)) = φ₂ z.1 * (c * φ₂ 1)
      rw [← mul_assoc, ← map_mul, one_mul]))
    (fun z z' m => Res.ext ((congrArg (Ind.tmul · m.val) (Subtype.ext (by
        change φ₂ (z.1 + z'.1) * (c * φ₂ 1) = φ₂ z.1 * (c * φ₂ 1) + φ₂ z'.1 * (c * φ₂ 1)
        rw [map_add, add_mul]))).trans (Ind.add_tmul _ _ _)))
    (fun z m m' => Res.ext (Ind.tmul_add (sigmaElt φ₁ φ₂ c z) m.val m'.val))
    (fun z a m => Res.ext (by
      rw [Res.val_mk, Res.val_mk, Res.val_smul, sigmaElt_op_smul φ₁ φ₂ hc, Ind.op_smul_tmul]))
    (fun b z m => Res.ext (by
      rw [Res.val_mk, Res.val_smul, Res.val_mk, Ind.smul_tmul]
      congr 1
      exact Subtype.ext (by
        change φ₂ (b * z.1) * (c * φ₂ 1) = φ₂ b * (φ₂ z.1 * (c * φ₂ 1))
        rw [map_mul, mul_assoc])))

@[simp] theorem sigmaLin_tmul (M : Type u) [AddCommGroup M] [Module A₁ M] (z : Corner φ₁)
    (m : Res φ₁ M) :
    (sigmaLin φ₁ φ₂ hc M (Ind.tmul z m)).val = Ind.tmul (sigmaElt φ₁ φ₂ c z) m.val :=
  rfl

omit [Ring A₀] [Ring A₁] [Ring A₂] in
theorem resFunctor_map_val {A B : Type u} [Ring A] [Ring B] {φ : A →ₙ+* B}
    {M M' : ModuleCat.{u} B} (f : M ⟶ M') (x : Res φ M) :
    (((resFunctor.{u, u} φ).map f).hom x).val = f.hom x.val :=
  rfl

omit [Ring A₀] [Ring A₁] [Ring A₂] in
theorem functor_map_tmul {A B : Type u} [Ring A] [Ring B] {φ : A →ₙ+* B}
    {N N' : ModuleCat.{u} A} (g : N ⟶ N') (z : Corner φ) (n : N) :
    ((functor.{u, u} φ).map g).hom (Ind.tmul z n) = Ind.tmul z (g.hom n) :=
  rfl

omit [Ring A₀] [Ring A₁] [Ring A₂] in
theorem adjunction_unit_app_hom_val {A B : Type u} [Ring A] [Ring B] (φ : A →ₙ+* B)
    (N : ModuleCat.{u} A) (n : N) :
    (((adjunction.{u, u} φ).unit.app N).hom n).val = Ind.tmul (unitGen φ) n :=
  rfl

omit [Ring A₀] [Ring A₁] [Ring A₂] in
theorem adjunction_counit_app_hom_tmul {A B : Type u} [Ring A] [Ring B] (φ : A →ₙ+* B)
    (M : ModuleCat.{u} B) (z : Corner φ) (m : Res φ M) :
    ((adjunction.{u, u} φ).counit.app M).hom (Ind.tmul z m) = z.1 • m.val :=
  rfl

variable (hfix : φ₂ 1 * c = c)
  (τ : resFunctor.{u, u} φ₂ ⋙ resFunctor.{u, u} φ₁ ⟶ resFunctor φ₂ ⋙ resFunctor φ₁)
  (hτ : ∀ M, τ.app M = ModuleCat.ofHom (resAct₂ c hfix hc M))

include hτ in
/-- The mate of `resAct₂ c` on a pure tensor `φ₂(1) ⊗ (z ⊗ n)`. -/
theorem conjugateEquiv_symm_resAct₂_tmul (N : ModuleCat.{u} A₀) (z : Corner φ₁) (n : N) :
    (((conjugateEquiv ((adjunction.{u, u} φ₁).comp (adjunction.{u, u} φ₂))
        ((adjunction φ₁).comp (adjunction φ₂))).symm τ).app N).hom
        (Ind.tmul (unitGen φ₂) (Ind.tmul z n)) =
      Ind.tmul (sigmaElt φ₁ φ₂ c z) (Ind.tmul (unitGen φ₁) n) := by
  set τ' := ((conjugateEquiv ((adjunction.{u, u} φ₁).comp (adjunction.{u, u} φ₂))
    ((adjunction φ₁).comp (adjunction φ₂))).symm τ)
  have key := congrArg (fun f => (f.hom n).val.val)
    (unit_conjugateEquiv_symm ((adjunction.{u, u} φ₁).comp (adjunction.{u, u} φ₂))
      ((adjunction φ₁).comp (adjunction φ₂)) τ N)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, hτ] at key
  change Ind.tmul (c • unitGen φ₂) (Ind.tmul (unitGen φ₁) n) =
    τ'.app N (Ind.tmul (unitGen φ₂) (Ind.tmul (unitGen φ₁) n)) at key
  have hz : Ind.tmul (φ := φ₂) (unitGen φ₂) (Ind.tmul z n) =
      φ₂ z.1 • Ind.tmul (unitGen φ₂) (Ind.tmul (unitGen φ₁) n) := by
    have : Ind.tmul (φ := φ₁) z n = z.1 • Ind.tmul (unitGen φ₁) n := by
      rw [Ind.smul_tmul]
      exact congrArg (Ind.tmul · n) (Subtype.ext z.2.symm)
    rw [this, ← Ind.op_smul_tmul, Ind.smul_tmul]
    congr 1
    exact Subtype.ext (by
      change φ₂ 1 * φ₂ z.1 = φ₂ z.1 * φ₂ 1
      rw [← map_mul, ← map_mul, one_mul, mul_one])
  rw [hz, (τ'.app N).hom.map_smul, ← key, Ind.smul_tmul]
  exact congrArg (Ind.tmul · _) (Subtype.ext rfl)

include hτ in
/-- **Rouquier's rightward crossing for induction along `φ₁`, `φ₂`**: `η₂ · τ · ε₁` is
`sigmaLin`, for `τ` the mate of `resAct₂ c`. -/
theorem sigma_app (M : ModuleCat.{u} A₁) :
    (Functor.whiskerLeft (resFunctor φ₁ ⋙ functor φ₁) (adjunction.{u, u} φ₂).unit ≫
      Functor.whiskerRight (Functor.whiskerLeft (resFunctor φ₁)
        ((conjugateEquiv ((adjunction.{u, u} φ₁).comp (adjunction.{u, u} φ₂))
          ((adjunction φ₁).comp (adjunction φ₂))).symm τ)) (resFunctor φ₂) ≫
      Functor.whiskerRight (adjunction.{u, u} φ₁).counit (functor φ₂ ⋙ resFunctor φ₂)).app M =
      ModuleCat.ofHom (sigmaLin φ₁ φ₂ hc M) := by
  ext x
  induction x using Ind.induction_on with
  | zero => rw [map_zero, map_zero]
  | add s t hs ht => rw [map_add, map_add, hs, ht]
  | tmul z m =>
    apply Res.ext
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      ModuleCat.hom_comp, LinearMap.comp_apply, Functor.comp_map]
    erw [resFunctor_map_val, resFunctor_map_val, adjunction_unit_app_hom_val,
      conjugateEquiv_symm_resAct₂_tmul φ₁ φ₂ hc hfix τ hτ, functor_map_tmul,
      adjunction_counit_app_hom_tmul]
    exact congrArg (Ind.tmul _) m.prop

end Categorification.InductionAlong

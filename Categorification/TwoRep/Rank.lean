/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.KrullSchmidt

/-!
# The rank calculus of CL §3.1

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, §3.1: "Choose (non-canonical) direct sum decompositions `X = A ⊗ V ⊕ B` and
`Y = A ⊗ V' ⊕ B'` where [...] `B, B'` do not contain `A` as a direct summand. Then one of the
matrix coefficients of `f` is a map `A ⊗ V → A ⊗ V'`, which (since `A` is a brick) is equivalent
to a linear map `V → V'`. The `A`-rank of `f` equals the rank of this linear map."

The `A`-rank `rk0 k A f` is defined (`KrullSchmidt.lean`) as the rank of the pairing
`Hom(A, X) × Hom(Y, A) → End(A)`, `(g, h) ↦ g ≫ f ≫ h`. Here:

* `rk0_biprod_map` (**additivity**): `rk_A(f₁ ⊕ f₂) = rk_A(f₁) + rk_A(f₂)`;
* `rk0_eq_zero_of_not_retract_left/right`: for a brick `A`, if `A` is not a retract of the
  source (or of the target), then `rk_A(f) = 0` (a nonzero element of `End(A) = k` is invertible);
* `rk0_iso_of_brick`: `rk_A(e) = 1` for an isomorphism `e : A ≅ A'` out of a brick `A`;
* `rk0_biprod_map_of_not_retract` (**CL's second description**): if `f = g ⊕ f'` is block
  diagonal with respect to decompositions `X = X₁ ⊕ X₂`, `Y = Y₁ ⊕ Y₂` where `A` is not a retract
  of `X₂`, then `rk_A(f) = rk_A(g)`.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits Module
open KrullSchmidtCat

universe v u

variable (k : Type*) [Field k] {𝒞 : Type u} [Category.{v} 𝒞] [Preadditive 𝒞] [Linear k 𝒞]
  [HomFinite k 𝒞] [HasBinaryBiproducts 𝒞]

omit [HomFinite k 𝒞] [HasBinaryBiproducts 𝒞] in
theorem range_prodMap {R M₁ M₂ N₁ N₂ : Type*} [Semiring R] [AddCommMonoid M₁]
    [AddCommMonoid M₂] [AddCommMonoid N₁] [AddCommMonoid N₂] [Module R M₁] [Module R M₂]
    [Module R N₁] [Module R N₂] (f : M₁ →ₗ[R] N₁) (g : M₂ →ₗ[R] N₂) :
    LinearMap.range (f.prodMap g) = (LinearMap.range f).prod (LinearMap.range g) := by
  ext ⟨a, b⟩
  simp only [LinearMap.mem_range, LinearMap.prodMap_apply, Prod.exists, Prod.mk.injEq,
    Submodule.mem_prod]
  constructor
  · rintro ⟨x, y, rfl, rfl⟩; exact ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩
  · rintro ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩; exact ⟨x, y, rfl, rfl⟩

/-- **Additivity of the `A`-rank** over block diagonal maps: `rk_A(f₁ ⊕ f₂) = rk_A(f₁) + rk_A(f₂)`. -/
theorem rk0_biprod_map (A : 𝒞) {X₁ X₂ Y₁ Y₂ : 𝒞} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) :
    rk0 k A (biprod.map f₁ f₂) = rk0 k A f₁ + rk0 k A f₂ := by
  let U := KrullSchmidtCat.biprodEquiv k A X₁ X₂
  let V := biprodLeftEquiv k Y₁ Y₂ A
  let L := LinearMap.coprodEquiv (M₃ := (A ⟶ A)) k ≪≫ₗ
      LinearEquiv.arrowCongr V.symm (LinearEquiv.refl k (A ⟶ A))
  have hΦ : rankPairing k A (biprod.map f₁ f₂) =
      L.toLinearMap ∘ₗ ((rankPairing k A f₁).prodMap (rankPairing k A f₂)) ∘ₗ U.toLinearMap := by
    ext g h
    simp only [rankPairing, LinearMap.mk₂_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, LinearMap.prodMap_apply, L, LinearEquiv.trans_apply,
      LinearEquiv.arrowCongr_apply, LinearEquiv.symm_symm, LinearEquiv.refl_apply,
      LinearMap.coprodEquiv_apply, LinearMap.coprod_apply, U, V,
      KrullSchmidtCat.biprodEquiv_apply, biprodLeftEquiv_apply]
    have hg : g = biprod.lift (g ≫ biprod.fst) (g ≫ biprod.snd) := by
      apply biprod.hom_ext <;> simp
    have hh : h = biprod.desc (biprod.inl ≫ h) (biprod.inr ≫ h) := by
      apply biprod.hom_ext' <;> simp
    conv_lhs => rw [hg, hh]
    have : biprod.lift (g ≫ biprod.fst) (g ≫ biprod.snd) ≫ biprod.map f₁ f₂ =
        biprod.lift (g ≫ biprod.fst ≫ f₁) (g ≫ biprod.snd ≫ f₂) := by
      apply biprod.hom_ext <;> simp
    rw [← Category.assoc, this, biprod.lift_desc]
    simp only [Category.assoc]
  rw [rk0, rk0, rk0, hΦ, LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top _
      (LinearEquiv.range U), LinearEquiv.finrank_map_eq, range_prodMap,
    finrank_submodule_prod]

omit [HasBinaryBiproducts 𝒞] in
/-- For a brick `A`, a nonzero value `g ≫ f ≫ h` of the pairing makes `A` a retract of the
source; so if `A` is not a retract of the source, `rk_A(f) = 0`. -/
theorem rk0_eq_zero_of_not_retract_left {A : 𝒞} (hA : IsBrick k A) {X Y : 𝒞} (f : X ⟶ Y)
    (hX : ¬ ∃ (i : A ⟶ X) (p : X ⟶ A), i ≫ p = 𝟙 A) : rk0 k A f = 0 := by
  rw [rk0, Submodule.finrank_eq_zero, LinearMap.range_eq_bot]
  ext g h
  simp only [rankPairing, LinearMap.mk₂_apply, LinearMap.zero_apply]
  have h1 : (𝟙 A : A ⟶ A) ≠ 0 := fun h0 => hA.1.1 ((IsZero.iff_id_eq_zero A).2 h0)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (𝟙 A) h1).1 hA.2 (g ≫ f ≫ h)
  by_contra hne
  have hc0 : c ≠ 0 := by rintro rfl; exact hne (by rw [← hc, zero_smul])
  refine hX ⟨g, c⁻¹ • (f ≫ h), ?_⟩
  rw [Linear.comp_smul, ← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]

omit [HasBinaryBiproducts 𝒞] in
/-- For a brick `A`, if `A` is not a retract of the target, `rk_A(f) = 0`. -/
theorem rk0_eq_zero_of_not_retract_right {A : 𝒞} (hA : IsBrick k A) {X Y : 𝒞} (f : X ⟶ Y)
    (hY : ¬ ∃ (i : A ⟶ Y) (p : Y ⟶ A), i ≫ p = 𝟙 A) : rk0 k A f = 0 := by
  rw [rk0, Submodule.finrank_eq_zero, LinearMap.range_eq_bot]
  ext g h
  simp only [rankPairing, LinearMap.mk₂_apply, LinearMap.zero_apply]
  have h1 : (𝟙 A : A ⟶ A) ≠ 0 := fun h0 => hA.1.1 ((IsZero.iff_id_eq_zero A).2 h0)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (𝟙 A) h1).1 hA.2 (g ≫ f ≫ h)
  by_contra hne
  have hc0 : c ≠ 0 := by rintro rfl; exact hne (by rw [← hc, zero_smul])
  refine hY ⟨c⁻¹ • (g ≫ f), h, ?_⟩
  rw [Linear.smul_comp, Category.assoc, ← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]

/-- **CL's second description of the `A`-rank**: if `f = g ⊕ f'` is block diagonal and `A` is not a
retract of `X₂` (the source of `f'`), then `rk_A(f) = rk_A(g)`. -/
theorem rk0_biprod_map_of_not_retract {A : 𝒞} (hA : IsBrick k A) {X₁ X₂ Y₁ Y₂ : 𝒞}
    (g : X₁ ⟶ Y₁) (f' : X₂ ⟶ Y₂) (hX : ¬ ∃ (i : A ⟶ X₂) (p : X₂ ⟶ A), i ≫ p = 𝟙 A) :
    rk0 k A (biprod.map g f') = rk0 k A g := by
  rw [rk0_biprod_map, rk0_eq_zero_of_not_retract_left k hA f' hX, add_zero]

omit [HasBinaryBiproducts 𝒞] in
/-- For a brick `A` and an isomorphism `e : A ≅ A'`, `rk_A(e) = 1`. -/
theorem rk0_iso_of_brick {A A' : 𝒞} (hA : IsBrick k A) (e : A ≅ A') : rk0 k A e.hom = 1 := by
  have : e.hom = 𝟙 A ≫ e.hom := (Category.id_comp _).symm
  rw [this, rk0_comp_iso, rk0_id k hA]

end Categorification.TwoRep

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqSl2
import Categorification.Algebra.HomTensorDecomp

/-!
# Moving explicit inverses between module categories

Brundan's invertibility conditions (arXiv:1501.00350v1, (1.8) and (1.9)) ask for an explicit
inverse of `(f, g 0, …, g (n-1))` (`TwoRep.SumInvTo`, `TwoRep.SumInvFrom`). This file moves
such inverses between categories of modules.

* `SumInvTo.transferAdd`, `SumInvFrom.transferAdd`: an explicit inverse in `ModuleCat R'`
  gives one in `ModuleCat R`, along additive bijections intertwining the maps. The inverse
  components are linear, since they are the components of the inverse of the linear bijection
  `(f, g 0, …, g (n-1))`; the rings `R` and `R'` need not be related.
* `HomTensor.sumInvToModule`, `HomTensor.sumInvFromModule`: an explicit inverse of natural
  transformations between additive functors gives one between their module functors
  `M ↦ (O' ⟶ F O) ⊗_{End O} M` (`HomTensor.natModuleHom`).

These pass the inversion relations of a categorical action on categories of projectives to the
action on all modules, as in Webster, arXiv:1309.3796v3, §4.6 and Proposition 5.5.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory

universe u u' v v'

section Transfer

variable {R : Type u} [Ring R] {R' : Type u'} [Ring R'] {X Y Z : ModuleCat.{v} R}
  {X' Y' Z' : ModuleCat.{v'} R'} {n : ℕ}

/-- **An explicit inverse `Y ⊕ Z^n → X`, transferred along additive bijections**: if the maps of
`ModuleCat R` correspond to maps of `ModuleCat R'` with an explicit inverse, they have one. -/
def SumInvTo.transferAdd {f : X ⟶ Y} {g : ℕ → (X ⟶ Z)} {f₂ : X' ⟶ Y'} {g₂ : ℕ → (X' ⟶ Z')}
    (S : SumInvTo f₂ g₂ n) (eX : X ≃+ X') (eY : Y ≃+ Y') (eZ : Z ≃+ Z')
    (hf : ∀ x, eY (f x) = f₂ (eX x)) (hg : ∀ m x, eZ (g m x) = g₂ m (eX x)) :
    SumInvTo f g n :=
  let a : Y → X := fun y => eX.symm (S.f' (eY y))
  let b : ℕ → Z → X := fun m z => eX.symm (S.g' m (eZ z))
  have total : ∀ x, a (f x) + ∑ m ∈ Finset.range n, b m (g m x) = x := fun x => by
    apply eX.injective
    have h := congrArg (fun t => t.hom (eX x)) S.total
    simp only [ModuleCat.hom_add, ModuleCat.hom_comp, ModuleCat.hom_sum, LinearMap.add_apply,
      LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, ModuleCat.hom_id,
      LinearMap.id_apply] at h
    simp only [a, b, map_add, map_sum, AddEquiv.apply_symm_apply, hf, hg]
    exact h
  have ff : ∀ y, f (a y) = y := fun y => by
    apply eY.injective
    rw [hf, AddEquiv.apply_symm_apply]
    exact congrArg (fun t => t.hom (eY y)) S.ff
  have fg : ∀ m, m < n → ∀ y, g m (a y) = 0 := fun m hm y => by
    apply eZ.injective
    rw [hg, AddEquiv.apply_symm_apply, map_zero]
    exact congrArg (fun t => t.hom (eY y)) (S.fg m hm)
  have gf : ∀ m, m < n → ∀ z, f (b m z) = 0 := fun m hm z => by
    apply eY.injective
    rw [hf, AddEquiv.apply_symm_apply, map_zero]
    exact congrArg (fun t => t.hom (eZ z)) (S.gf m hm)
  have gg : ∀ m m', m < n → m' < n → ∀ z, g m' (b m z) = if m = m' then z else 0 :=
    fun m m' hm hm' z => by
    apply eZ.injective
    rw [hg, AddEquiv.apply_symm_apply]
    have h := congrArg (fun t => t.hom (eZ z)) (S.gg m m' hm hm')
    split_ifs at h ⊢ with hmm
    · exact h
    · rw [map_zero]; exact h
  have a0 : a 0 = 0 := by simp only [a, map_zero]
  have b0 : ∀ m, b m 0 = 0 := fun m => by simp only [b, map_zero]
  have la : ∀ (r : R) y, a (r • y) = r • a y := fun r y => by
    have e := total (r • a y)
    rw [Finset.sum_eq_zero (fun m hm => by
      rw [(g m).hom.map_smul, fg m (Finset.mem_range.1 hm), smul_zero, b0]), add_zero,
      f.hom.map_smul, ff] at e
    exact e
  have lb : ∀ m, m < n → ∀ (r : R) z, b m (r • z) = r • b m z := fun m hm r z => by
    have hz : r • z = g m (r • b m z) := by
      rw [(g m).hom.map_smul, gg m m hm hm z, ite_eq_left rfl]
    have e := total (r • b m z)
    rw [f.hom.map_smul, gf m hm z, smul_zero, a0, zero_add,
      Finset.sum_eq_single m (fun m' hm' hne => by
        rw [(g m').hom.map_smul, gg m m' hm (Finset.mem_range.1 hm'),
          ite_eq_right (Ne.symm hne), smul_zero, b0])
      (fun h => absurd (Finset.mem_range.2 hm) h)] at e
    rw [hz]
    exact e
  { f' := ModuleCat.ofHom
      { toFun := a
        map_add' := fun y y' => by simp only [a, map_add]
        map_smul' := la }
    g' := fun m => ModuleCat.ofHom
      { toFun := fun z => if m < n then b m z else 0
        map_add' := fun z z' => by split_ifs <;> simp [b]
        map_smul' := fun r z => by
          split_ifs with hm
          · exact lb m hm r z
          · simp }
    total := by
      ext x
      simp only [ModuleCat.hom_add, ModuleCat.hom_comp, ModuleCat.hom_sum, LinearMap.add_apply,
        LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, ModuleCat.hom_id,
        LinearMap.id_apply, ModuleCat.hom_ofHom, LinearMap.coe_mk, AddHom.coe_mk]
      rw [Finset.sum_congr rfl (fun m hm => by rw [ite_eq_left (Finset.mem_range.1 hm)])]
      exact total x
    ff := by
      ext y
      exact ff y
    fg := fun m hm => by
      ext y
      exact fg m hm y
    gf := fun m hm => by
      ext z
      change f (if m < n then b m z else 0) = 0
      rw [ite_eq_left hm]
      exact gf m hm z
    gg := fun m m' hm hm' => by
      ext z
      change g m' (if m < n then b m z else 0) = _
      rw [ite_eq_left hm, gg m m' hm hm' z]
      split_ifs <;> rfl }

/-- **An explicit inverse `X → Y ⊕ Z^n`, transferred along additive bijections**: if the maps of
`ModuleCat R` correspond to maps of `ModuleCat R'` with an explicit inverse, they have one. -/
def SumInvFrom.transferAdd {f : Y ⟶ X} {g : ℕ → (Z ⟶ X)} {f₂ : Y' ⟶ X'} {g₂ : ℕ → (Z' ⟶ X')}
    (S : SumInvFrom f₂ g₂ n) (eX : X ≃+ X') (eY : Y ≃+ Y') (eZ : Z ≃+ Z')
    (hf : ∀ y, eX (f y) = f₂ (eY y)) (hg : ∀ m z, eX (g m z) = g₂ m (eZ z)) :
    SumInvFrom f g n :=
  let a : X →+ Y := eY.symm.toAddMonoidHom.comp
    ((S.f'.hom.toAddMonoidHom).comp eX.toAddMonoidHom)
  let b : ℕ → X →+ Z := fun m => eZ.symm.toAddMonoidHom.comp
    (((S.g' m).hom.toAddMonoidHom).comp eX.toAddMonoidHom)
  have total : ∀ x, f (a x) + ∑ m ∈ Finset.range n, g m (b m x) = x := fun x => by
    apply eX.injective
    have h := congrArg (fun t => t.hom (eX x)) S.total
    simp only [ModuleCat.hom_add, ModuleCat.hom_comp, ModuleCat.hom_sum, LinearMap.add_apply,
      LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, ModuleCat.hom_id,
      LinearMap.id_apply] at h
    simp only [a, b, AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
      LinearMap.toAddMonoidHom_coe, map_add, map_sum, hf, hg, AddEquiv.apply_symm_apply]
    exact h
  have ff : ∀ y, a (f y) = y := fun y => by
    apply eY.injective
    simp only [a, AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
      LinearMap.toAddMonoidHom_coe, hf, AddEquiv.apply_symm_apply]
    exact congrArg (fun t => t.hom (eY y)) S.ff
  have fg : ∀ m, m < n → ∀ y, b m (f y) = 0 := fun m hm y => by
    apply eZ.injective
    simp only [b, AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
      LinearMap.toAddMonoidHom_coe, hf, AddEquiv.apply_symm_apply, map_zero]
    exact congrArg (fun t => t.hom (eY y)) (S.fg m hm)
  have gf : ∀ m, m < n → ∀ z, a (g m z) = 0 := fun m hm z => by
    apply eY.injective
    simp only [a, AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
      LinearMap.toAddMonoidHom_coe, hg, AddEquiv.apply_symm_apply, map_zero]
    exact congrArg (fun t => t.hom (eZ z)) (S.gf m hm)
  have gg : ∀ m m', m < n → m' < n → ∀ z, b m' (g m z) = if m = m' then z else 0 :=
    fun m m' hm hm' z => by
    apply eZ.injective
    simp only [b, AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
      LinearMap.toAddMonoidHom_coe, hg, AddEquiv.apply_symm_apply]
    have h := congrArg (fun t => t.hom (eZ z)) (S.gg m m' hm hm')
    split_ifs at h ⊢ with hmm
    · exact h
    · rw [map_zero]; exact h
  have la : ∀ (r : R) x, a (r • x) = r • a x := fun r x => by
    conv_lhs => rw [← total x, smul_add, Finset.smul_sum]
    rw [map_add, ← f.hom.map_smul, ff, map_sum, Finset.sum_eq_zero (fun m hm => by
      rw [← (g m).hom.map_smul, gf m (Finset.mem_range.1 hm)]), add_zero]
  have lb : ∀ m, m < n → ∀ (r : R) x, b m (r • x) = r • b m x := fun m hm r x => by
    conv_lhs => rw [← total x, smul_add, Finset.smul_sum]
    rw [map_add, ← f.hom.map_smul, fg m hm, zero_add, map_sum,
      Finset.sum_eq_single m (fun m' hm' hne => by
        rw [← (g m').hom.map_smul, gg m' m (Finset.mem_range.1 hm') hm, ite_eq_right hne])
      (fun h => absurd (Finset.mem_range.2 hm) h), ← (g m).hom.map_smul, gg m m hm hm,
      ite_eq_left rfl]
  { f' := ModuleCat.ofHom
      { toFun := a
        map_add' := fun x x' => by simp only [a, map_add]
        map_smul' := la }
    g' := fun m => ModuleCat.ofHom
      { toFun := fun x => if m < n then b m x else 0
        map_add' := fun x x' => by split_ifs <;> simp [b]
        map_smul' := fun r x => by
          split_ifs with hm
          · exact lb m hm r x
          · simp }
    total := by
      ext x
      simp only [ModuleCat.hom_add, ModuleCat.hom_comp, ModuleCat.hom_sum, LinearMap.add_apply,
        LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, ModuleCat.hom_id,
        LinearMap.id_apply, ModuleCat.hom_ofHom, LinearMap.coe_mk, AddHom.coe_mk]
      rw [Finset.sum_congr rfl (fun m hm => by rw [ite_eq_left (Finset.mem_range.1 hm)])]
      exact total x
    ff := by
      ext y
      exact ff y
    fg := fun m hm => by
      ext y
      change (if m < n then b m (f y) else 0) = 0
      rw [ite_eq_left hm]
      exact fg m hm y
    gf := fun m hm => by
      ext z
      exact gf m hm z
    gg := fun m m' hm hm' => by
      ext z
      change (if m' < n then b m' (g m z) else 0) = _
      rw [ite_eq_left hm', gg m m' hm hm' z]
      split_ifs <;> rfl }

end Transfer

end Categorification.TwoRep

namespace Categorification.HomTensor

open CategoryTheory TwoRep

universe v₁ v₂ u₁ u₂ w

attribute [local instance] bimodule

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] {D : Type u₂} [Category.{v₂} D]
  [Preadditive D] (O : C) (O' : D) (M : Type w) [AddCommGroup M] [Module (End O)ᵐᵒᵖ M]
  {F G H : C ⥤ D} [F.Additive] [G.Additive] [H.Additive] {n : ℕ}

/-- **An explicit inverse of natural transformations gives one of their module maps**: an
explicit inverse of `(f, g 0, …, g (n-1)) : F ⟶ G ⊕ H^n` among additive functors gives one of
the module maps `(O' ⟶ F O) ⊗ M ⟶ (O' ⟶ G O) ⊗ M ⊕ ((O' ⟶ H O) ⊗ M)^n`. -/
def sumInvToModule {f : F ⟶ G} {g : ℕ → (F ⟶ H)} (S : SumInvTo f g n) :
    SumInvTo (natModuleHom O O' M f) (fun m => natModuleHom O O' M (g m)) n where
  f' := natModuleHom O O' M S.f'
  g' m := natModuleHom O O' M (S.g' m)
  total := by
    rw [← natModuleHom_id, ← S.total, natModuleHom_add, natModuleHom_comp, natModuleHom_sum]
    simp only [natModuleHom_comp]
  ff := by rw [← natModuleHom_comp, S.ff, natModuleHom_id]
  fg m hm := by rw [← natModuleHom_comp, S.fg m hm, natModuleHom_zero]
  gf m hm := by rw [← natModuleHom_comp, S.gf m hm, natModuleHom_zero]
  gg m m' hm hm' := by
    rw [← natModuleHom_comp, S.gg m m' hm hm']
    split_ifs
    · exact natModuleHom_id O O' M
    · exact natModuleHom_zero O O' M

/-- **An explicit inverse of natural transformations gives one of their module maps**, for
`(f, g 0, …, g (n-1)) : G ⊕ H^n ⟶ F`. -/
def sumInvFromModule {f : G ⟶ F} {g : ℕ → (H ⟶ F)} (S : SumInvFrom f g n) :
    SumInvFrom (natModuleHom O O' M f) (fun m => natModuleHom O O' M (g m)) n where
  f' := natModuleHom O O' M S.f'
  g' m := natModuleHom O O' M (S.g' m)
  total := by
    rw [← natModuleHom_id, ← S.total, natModuleHom_add, natModuleHom_comp, natModuleHom_sum]
    simp only [natModuleHom_comp]
  ff := by rw [← natModuleHom_comp, S.ff, natModuleHom_id]
  fg m hm := by rw [← natModuleHom_comp, S.fg m hm, natModuleHom_zero]
  gf m hm := by rw [← natModuleHom_comp, S.gf m hm, natModuleHom_zero]
  gg m m' hm hm' := by
    rw [← natModuleHom_comp, S.gg m m' hm hm']
    split_ifs
    · exact natModuleHom_id O O' M
    · exact natModuleHom_zero O O' M

end Categorification.HomTensor

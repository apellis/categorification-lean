/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensorFiltration
import Categorification.Algebra.IdempotentEquiv
import DG.Derived.Perfect

set_option backward.isDefEq.respectTransparency false

/-!
# Right ideals of a complete family of idempotents generate the derived category

For a ring `A` and a finite family of orthogonal idempotents `f i` with `∑ f i = 1`, the right
ideals `f i A`, in degree `0`, compactly generate the derived category of right `A`-modules
(`compactlyGenerates_rIdeal`): `A = ⊕ f i A`, and `A` compactly generates. This is the
generation of `D(T^λ)` by the projectives `e(t) T^λ` used in Webster, arXiv:1309.3796v3, proof
of Theorem 6.15.
-/

noncomputable section

namespace Categorification

open CategoryTheory MulOpposite DG
open scoped DG.DegreeZero

variable {A : Type} [Ring A] [DG.HasDerivedCategory.{0, 0} Aᵐᵒᵖ]
  {ι : Type} [Fintype ι] (f : ι → A) (hf : ∀ i, IsIdempotentElem (f i))

/-- The right ideal `f A` as an object of the derived category of right `A`-modules. -/
abbrev rIdealObj (e : A) : DG.DerivedCategory.{0} Aᵐᵒᵖ :=
  DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor Aᵐᵒᵖ).obj (ModuleCat.of Aᵐᵒᵖ (rIdeal e)))

/-- The regular module in degree `0`. -/
abbrev regularObj : DG.DerivedCategory.{0} Aᵐᵒᵖ :=
  DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor Aᵐᵒᵖ).obj (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ))

variable (A) in
/-- The regular module in degree `0` is the regular dg module. -/
def regularObjIso : DG.DerivedCategory.Q.obj (DGModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ) ≅ regularObj (A := A) :=
  DG.DerivedCategory.Q.mapIso (DGModuleCat.isoOfDGModuleEquiv
    { toLinearEquiv := LinearEquiv.refl Aᵐᵒᵖ Aᵐᵒᵖ
      map_mem' := fun hx => hx
      map_d' := fun _ => rfl })

/-- Left multiplication by `e`, `A → e A`, as a map of right `A`-modules. -/
def rIdealGenProj {e : A} (he : IsIdempotentElem e) :
    ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ ⟶ ModuleCat.of Aᵐᵒᵖ (rIdeal e) :=
  ModuleCat.ofHom
    { toFun := fun a => ⟨e * a.unop, by
        change e * (e * a.unop) = e * a.unop
        rw [← mul_assoc, he.eq]⟩
      map_add' := fun a b => Subtype.ext (by
        change e * (a + b).unop = e * a.unop + e * b.unop
        rw [MulOpposite.unop_add, mul_add])
      map_smul' := fun c a => Subtype.ext (by
        change e * (a.unop * c.unop) = e * a.unop * c.unop
        rw [mul_assoc]) }

/-- The inclusion `e A → A` of right `A`-modules. -/
def rIdealGenIncl (e : A) : ModuleCat.of Aᵐᵒᵖ (rIdeal e) ⟶ ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ :=
  ModuleCat.ofHom
    { toFun := fun y => op y.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

omit [DG.HasDerivedCategory.{0, 0} Aᵐᵒᵖ] in
theorem rIdealGenIncl_rIdealGenProj {e : A} (he : IsIdempotentElem e) :
    rIdealGenIncl e ≫ rIdealGenProj he = 𝟙 _ := by
  refine ModuleCat.hom_ext (LinearMap.ext fun y => Subtype.ext ?_)
  change e * y.1 = y.1
  exact (mem_rIdeal (A := A)).1 y.2

omit [DG.HasDerivedCategory.{0, 0} Aᵐᵒᵖ] in
include hf in
theorem sum_rIdealGenProj_rIdealGenIncl (hsum : ∑ i, f i = 1) :
    ∑ i, rIdealGenProj (hf i) ≫ rIdealGenIncl (f i) = 𝟙 (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun a => ?_)
  change (∑ i, (rIdealGenProj (hf i) ≫ rIdealGenIncl (f i))).hom a = a
  rw [ModuleCat.hom_sum, LinearMap.sum_apply]
  change ∑ i, op (f i * a.unop) = a
  rw [show (∑ i, op (f i * a.unop)) = op (∑ i, f i * a.unop) from
    (map_sum (MulOpposite.opAddEquiv : A ≃+ Aᵐᵒᵖ) _ _).symm, ← Finset.sum_mul, hsum, one_mul,
    op_unop]

include hf in
/-- **The right ideals of a complete family of idempotents compactly generate** the derived
category of right modules. -/
theorem compactlyGenerates_rIdeal (hsum : ∑ i, f i = 1) :
    CompactlyGenerates (fun i => rIdealObj (f i)) := by
  let Φ := degreeZeroModuleFunctor Aᵐᵒᵖ ⋙ DG.DerivedCategory.Q
  have hG := DG.DerivedCategory.compactlyGenerates (A := Aᵐᵒᵖ)
  have hreg : IsCompact.{0} (regularObj (A := A)) :=
    (hG.isCompact ()).of_iso (regularObjIso A).symm
  refine ⟨fun i => IsCompact.of_retract
    ⟨Φ.map (rIdealGenIncl (f i)), Φ.map (rIdealGenProj (hf i)), by
      rw [← Φ.map_comp, rIdealGenIncl_rIdealGenProj, Φ.map_id]; rfl⟩ hreg, fun Y h => ?_⟩
  refine hG.isZero_of_forall_eq_zero Y fun _ n φ => ?_
  have hψ : ((regularObjIso A).inv)⟦n⟧' ≫ φ = 0 := by
    have e : 𝟙 ((regularObj (A := A))⟦n⟧) =
        ∑ i, (Φ.map (rIdealGenProj (hf i)))⟦n⟧' ≫ (Φ.map (rIdealGenIncl (f i)))⟦n⟧' := by
      have e0 : Φ.map (𝟙 (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ)) =
          ∑ i, Φ.map (rIdealGenProj (hf i)) ≫ Φ.map (rIdealGenIncl (f i)) := by
        rw [← sum_rIdealGenProj_rIdealGenIncl f hf hsum, Functor.map_sum]
        simp only [Functor.map_comp]
      have e1 : 𝟙 (regularObj (A := A)) = Φ.map (𝟙 (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ)) :=
        (Φ.map_id _).symm
      rw [← (shiftFunctor _ n).map_id, e1, e0, Functor.map_sum]
      simp only [Functor.map_comp]
    rw [← Category.id_comp (((regularObjIso A).inv)⟦n⟧' ≫ φ), e, Preadditive.sum_comp]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Category.assoc, h i n (_ ≫ _), Limits.comp_zero]
  have : φ = ((regularObjIso A).hom)⟦n⟧' ≫ ((regularObjIso A).inv)⟦n⟧' ≫ φ := by
    rw [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id]
    simp
  rw [this, hψ, Limits.comp_zero]

end Categorification

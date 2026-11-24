/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DG.Category.Derived.Basic

/-!
# Exact triangles for pointwise exact sequences of diagram-weight modules

The cone of the first arrow maps quasi-isomorphically to the quotient. This
applies in particular to the two short exact sequences of the fundamental
middle resolution in Webster, arXiv:1309.3796v2, §7.1.
-/

noncomputable section
namespace Categorification.Stendhal.FundamentalCorner
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated DG DG.CatModule
universe v
variable {C : Type} [Category.{0} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C]
    {A B E : CatModule.{0} C} (f : A ⟶ B) (g : B ⟶ E) (fg : f ≫ g = 0)

private def coneDescent : cone f ⟶ E where
  app X := (g.app X).comp (cone.sndAddHom f X)
  map_mem' h := g.map_mem (cone.sndAddHom_mem h)
  map_d' {X} z := by
    change g.app X (cone.sndAddHom f X (d z)) = d (g.app X (cone.sndAddHom f X z))
    rw [cone.sndAddHom_d, map_add, g.map_d]
    have h := congrArg (fun a : A ⟶ E => a.app X (shift.unmk 1 ((cone.fstHom f).app X z))) fg
    change g.app X (f.app X _) = 0 at h
    rw [h, zero_add]
  map_smul' h z := g.map_smul h (cone.sndAddHom f _ z)

local notation "H" => coneDescent f g fg

private def pack {X : C} (a : A.obj X) (b : B.obj X) (e : E.obj X) : (cone H).obj X :=
  (shift.mk 1 (show (cone f).obj X from (shift.mk 1 a, b)), e)

private theorem pack_mem {X : C} {n : ℤ} (a : A.obj X) (b : B.obj X) (e : E.obj X) :
    pack f g fg a b e ∈ DG.grading n ↔
      a ∈ DG.grading (n+1+1) ∧ b ∈ DG.grading (n+1) ∧ e ∈ DG.grading n := by
  change (_ ∧ _) ↔ _
  exact and_assoc

private theorem d_pack {X : C} (a : A.obj X) (b : B.obj X) (e : E.obj X) :
    d (pack f g fg a b e) = pack f g fg (d a) (-(f.app X a + d b)) (g.app X b + d e) := by
  refine Prod.ext (Prod.ext ?_ ?_) rfl
  · change koszulSign 1 • (koszulSign 1 • d a) = d a
    simp [Units.smul_def]
  · change koszulSign 1 • (f.app X a + d b) = -(f.app X a + d b)
    simp [Units.smul_def, add_comm]

omit [DGCategory C] in
private theorem homogeneous_preimage {M N : CatModule.{0} C} (a : M ⟶ N) (X : C) {n : ℤ} {x : N.obj X}
    (hx : x ∈ DG.grading n) (h : ∃ y, a.app X y = x) :
    ∃ y ∈ DG.grading n, a.app X y = x := by
  obtain ⟨y, hy⟩ := h
  refine ⟨(DirectSum.decompose DG.grading y n).val, (DirectSum.decompose DG.grading y n).property, ?_⟩
  rw [← coe_decompose_map_of_map_mem (a.app X) (fun h => a.map_mem h), hy, DirectSum.decompose_of_mem_same _ hx]

private theorem coneDescent_quasiIso
    (hinj : ∀ X, Function.Injective (f.app X)) (hex : ∀ X, Function.Exact (f.app X) (g.app X))
    (hsur : ∀ X, Function.Surjective (g.app X)) : IsQuasiIso H := by
  apply (isQuasiIso_iff_isAcyclic_cone H).mpr
  intro X
  refine DG.isAcyclic_iff.mpr fun n y hy hdy => ?_
  let a := shift.unmk 1 ((cone.fstHom f).app X (shift.unmk 1 ((cone.fstHom H).app X y)))
  let b := cone.sndAddHom f X (shift.unmk 1 ((cone.fstHom H).app X y))
  let e := cone.sndAddHom H X y
  change pack f g fg a b e ∈ DG.grading n at hy
  change d (pack f g fg a b e) = 0 at hdy
  rw [d_pack] at hdy
  have hb := (pack_mem f g fg a b e).mp hy
  have hba : -(f.app X a + d b) = 0 := congrArg (fun z : (cone H).obj X =>
    cone.sndAddHom f X (shift.unmk 1 ((cone.fstHom H).app X z))) hdy
  have hbe : g.app X b + d e = 0 := congrArg (cone.sndAddHom H X) hdy
  obtain ⟨b', hb', hgb⟩ := homogeneous_preimage g X hb.2.2 (hsur X e)
  have hb0 : g.app X (-(b + d b')) = 0 := by rw [map_neg, map_add, g.map_d, hgb, hbe, neg_zero]
  obtain ⟨a', ha', hfa⟩ := homogeneous_preimage f X
    (neg_mem (add_mem hb.2.1 (DG.d_mem hb'))) ((hex X _).mp hb0)
  have hda : d a' = a := by
    apply hinj X
    rw [f.map_d, hfa, d_neg, d_add, d_d, add_zero]
    have h := neg_eq_zero.mp hba
    exact (eq_neg_of_add_eq_zero_left h).symm
  refine ⟨pack f g fg a' b' 0, ?_, ?_⟩
  · apply (pack_mem f g fg a' b' 0).mpr
    simpa only [sub_add_cancel] using (show a' ∈ DG.grading (n+1) ∧ b' ∈ DG.grading n ∧ (0 : E.obj X) ∈ DG.grading (n-1) from ⟨ha', hb', zero_mem _⟩)
  · have h : -(f.app X a' + d b') = b := by rw [hfa]; abel
    rw [d_pack, hda, h, hgb, d_zero, add_zero]
    rfl

variable [CatModule.HasDerivedCategory.{v,0} C]

include fg in
/-- A pointwise short exact sequence gives a distinguished triangle with these three objects. -/
theorem exists_weight_triangle_of_exact
    (hinj : ∀ X, Function.Injective (f.app X)) (hex : ∀ X, Function.Exact (f.app X) (g.app X))
    (hsur : ∀ X, Function.Surjective (g.app X)) :
    ∃ D : Triangle (CatModule.DerivedCategory.{v,0} C), D ∈ distTriang _ ∧
      Nonempty (D.obj₁ ≅ CatModule.DerivedCategory.Q.obj A) ∧
      Nonempty (D.obj₂ ≅ CatModule.DerivedCategory.Q.obj B) ∧ Nonempty (D.obj₃ ≅ CatModule.DerivedCategory.Q.obj E) := by
  let qC : CatModule.{0} C ⥤ CatModule.DerivedCategory.{v,0} C := CatModule.DerivedCategory.Q
  have hIso : IsIso (qC.map H) := (CatModule.DerivedCategory.isIso_Q_map_iff H).mpr (coneDescent_quasiIso f g fg hinj hex hsur)
  let D : Triangle (CatModule.DerivedCategory.{v,0} C) := CatModule.DerivedCategory.Q.mapTriangle.obj (cone.triangle f)
  have hD : D ∈ distTriang _ := (CatModule.DerivedCategory.mem_distTriang_iff _).mpr ⟨_, _, f, ⟨Iso.refl _⟩⟩
  exact ⟨D, hD, ⟨Iso.refl _⟩, ⟨Iso.refl _⟩, ⟨@asIso _ _ _ _ (qC.map H) hIso⟩⟩

end Categorification.Stendhal.FundamentalCorner

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.DotExtension

/-!
# Extending graded structure to the additive Karoubi envelope

A *left shift structure* on a bicategory (`LeftShift`) consists of endofunctors `S` of the hom
categories with isomorphisms `S(f) ≫ g ≅ S(f ≫ g)`, natural in `f` and `g`; a *right shift
structure* (`RightShift`) has `f ≫ S(g) ≅ S(f ≫ g)` instead. For the grading shift `⟨1⟩` of a
graded 2-category (S. Cautis, A. D. Lauda, arXiv:1111.1431v3, §2.1.2) these are
`x⟨1⟩ y ≅ (x y)⟨1⟩` and `x (y⟨1⟩) ≅ (x y)⟨1⟩`. A pseudofunctor commutes with shift structures
(`LeftShiftCompat`, `RightShiftCompat`) if it comes with isomorphisms `F(S f) ≅ T(F f)`, natural
in `f`, compatible with the composition constraints; they are then also compatible with the
identity constraints (`LeftShiftCompat.mapId`, `RightShiftCompat.mapId`).

This file shows that these structures extend to the additive Karoubi envelope
`Kar A = KarBicat (MatBicat A)` (J. Brundan, A. P. Ellis, arXiv:1603.05928v3, §1.5):

* `LeftShift.kar`, `RightShift.kar`: the induced shift structures of `Kar A` (`S` applied
  entrywise to matrices and idempotents; the isomorphisms are diagonal matrices);
* `LeftShiftCompat.ext`, `RightShiftCompat.ext`: if `F` commutes with shift structures, so does its
  extension `DotExt.ext F hF : Kar A ⥤ᵖ B`, with the isomorphisms `DotExt.extShiftIso`
  (`DotExt.extNatIso`).

The proof reduces to the objects of `A` (`DotExt.lhs_eq_rhs_incl`, using that `ext F hF` restricts
to `F` as a pseudofunctor, `DotExt.inclIso_mapComp`): natural transformations between additive
functors out of `Karoubi (Mat_ E)` are determined by their components at the objects of `E`
(`KarMatExt.natTrans_ext`), and the isomorphisms `KarMatExt.ext γ` restrict to `γ`
(`KarMatExt.ext_hom_app_incl`).
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Categorification

open CategoryTheory CategoryTheory.Limits Idempotents

namespace MatExtGen

open Mat_

universe v₁ v₂ u₂ u₃

variable {C : Type u₂} [Category.{v₁} C] [Preadditive C] {D : Type u₃} [Category.{v₂} D]
  [Preadditive D] [HasFiniteBiproducts D]

theorem isoBiproductEmbedding_hom_π_embedding (x : C) :
    ((embedding C).obj x).isoBiproductEmbedding.hom ≫
      biproduct.π (fun i => (embedding C).obj (((embedding C).obj x).X i)) PUnit.unit = 𝟙 _ := by
  rw [isoBiproductEmbedding_hom]
  erw [biproduct.lift_π]
  ext ⟨⟩ ⟨⟩
  rfl

theorem ι_isoBiproductEmbedding_inv_embedding (x : C) :
    biproduct.ι (fun i => (embedding C).obj (((embedding C).obj x).X i)) PUnit.unit ≫
      ((embedding C).obj x).isoBiproductEmbedding.inv = 𝟙 _ := by
  have : Unique ((embedding C).obj x).ι := inferInstanceAs (Unique PUnit)
  have h := isoBiproductEmbedding_hom_π_embedding x
  have hu : biproduct.π (fun i => (embedding C).obj (((embedding C).obj x).X i)) PUnit.unit ≫
      biproduct.ι (fun i => (embedding C).obj (((embedding C).obj x).X i)) PUnit.unit = 𝟙 _ := by
    rw [← biproduct.total, Fintype.sum_unique]
    rfl
  calc _ = (((embedding C).obj x).isoBiproductEmbedding.hom ≫
        biproduct.π (fun i => (embedding C).obj (((embedding C).obj x).X i)) PUnit.unit) ≫
        biproduct.ι (fun i => (embedding C).obj (((embedding C).obj x).X i)) PUnit.unit ≫
          ((embedding C).obj x).isoBiproductEmbedding.inv := by
          rw [h]; exact (Category.id_comp _).symm
    _ = 𝟙 _ := by rw [Category.assoc, reassoc_of% hu, Iso.hom_inv_id]

/-- **The isomorphism `ext γ` restricts to `γ`.** -/
theorem ext_hom_app_embedding {F G : Mat_ C ⥤ D} [F.Additive] [G.Additive]
    (γ : embedding C ⋙ F ≅ embedding C ⋙ G) (x : C) :
    (ext γ).hom.app ((embedding C).obj x) = γ.hom.app x := by
  have : Unique ((embedding C).obj x).ι := inferInstanceAs (Unique PUnit)
  simp only [ext, NatIso.ofComponents_hom_app, Iso.trans_hom, Iso.symm_hom, biproduct.mapIso_hom]
  rw [← Category.comp_id (addIso F _).hom,
    ← TwoRep.biproduct_π_ι_unique (fun i => F.obj ((embedding C).obj (((embedding C).obj x).X i))),
    Category.assoc, Category.assoc, biproduct.ι_map_assoc]
  erw [ι_addIso_inv]
  rw [← Category.assoc, addIso_hom_π]
  erw [isoBiproductEmbedding_hom_π_embedding, ι_isoBiproductEmbedding_inv_embedding]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.comp_id]
  rfl

end MatExtGen

namespace KarMatExt

variable {E : Type*} [Category E] [Preadditive E] {D : Type*} [Category D] [Preadditive D]

/-- The projection of `P` onto its `i`-th summand. -/
abbrev retrI (P : Karoubi (Mat_ E)) (i : P.X.ι) : P ⟶ (incl E).obj (P.X.X i) :=
  P.decompId_i ≫ (toKaroubi _).map
    (P.X.isoBiproductEmbedding.hom ≫ biproduct.π (fun j => (Mat_.embedding E).obj (P.X.X j)) i)

/-- The inclusion of the `i`-th summand of `P`. -/
abbrev retrP (P : Karoubi (Mat_ E)) (i : P.X.ι) : (incl E).obj (P.X.X i) ⟶ P :=
  (toKaroubi _).map (biproduct.ι (fun j => (Mat_.embedding E).obj (P.X.X j)) i ≫
    P.X.isoBiproductEmbedding.inv) ≫ P.decompId_p

/-- Every object of `Karoubi (Mat_ E)` is a retract of a finite direct sum of objects of `E`:
the identity is a sum of morphisms factoring through objects in the image of `incl E`. -/
theorem id_eq_sum (P : Karoubi (Mat_ E)) : 𝟙 P = ∑ i, retrI P i ≫ retrP P i := by
  have h : ∑ i, P.X.isoBiproductEmbedding.hom ≫
      biproduct.π (fun j => (Mat_.embedding E).obj (P.X.X j)) i ≫
        biproduct.ι (fun j => (Mat_.embedding E).obj (P.X.X j)) i ≫
          P.X.isoBiproductEmbedding.inv = 𝟙 P.X := by
    rw [← Preadditive.comp_sum]
    simp only [← Category.assoc (biproduct.π _ _)]
    rw [← Preadditive.sum_comp, biproduct.total, Category.id_comp, Iso.hom_inv_id]
  simp only [retrI, retrP, Category.assoc, ← Preadditive.comp_sum]
  simp only [← Category.assoc, ← Preadditive.sum_comp]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [← Functor.map_sum, h, CategoryTheory.Functor.map_id]
  erw [Category.id_comp]
  exact P.decompId

/-- **Natural transformations out of an additive functor on `Karoubi (Mat_ E)` are determined by
their components at the objects of `E`.** -/
theorem natTrans_ext {G₁ G₂ : Karoubi (Mat_ E) ⥤ D} [G₁.Additive] {α β : G₁ ⟶ G₂}
    (h : ∀ x : E, α.app ((incl E).obj x) = β.app ((incl E).obj x)) : α = β := by
  have key : ∀ γ : G₁ ⟶ G₂, ∀ P, γ.app P = ∑ i, G₁.map (retrI P i) ≫
      γ.app ((incl E).obj (P.X.X i)) ≫ G₂.map (retrP P i) := by
    intro γ P
    conv_lhs => rw [← Category.id_comp (γ.app P), ← CategoryTheory.Functor.map_id, id_eq_sum P,
      Functor.map_sum, Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Functor.map_comp, Category.assoc, γ.naturality]
  ext P
  rw [key α P, key β P]
  exact Finset.sum_congr rfl fun i _ => by rw [h]

/-- **The isomorphism `ext γ` restricts to `γ`.** -/
theorem ext_hom_app_incl {G₁ G₂ : Karoubi (Mat_ E) ⥤ D} [HasFiniteBiproducts D] [G₁.Additive]
    [G₂.Additive] (γ : incl E ⋙ G₁ ≅ incl E ⋙ G₂) (x : E) :
    (ext γ).hom.app ((incl E).obj x) = γ.hom.app x := by
  let e : toKaroubi (Mat_ E) ⋙ G₁ ≅ toKaroubi (Mat_ E) ⋙ G₂ := MatExtGen.ext γ
  have h := congr_app ((whiskeringLeftObjToKaroubiFullyFaithful (C := Mat_ E) (D := D)).map_preimage
    (X := G₁) (Y := G₂) e.hom) ((Mat_.embedding E).obj x)
  exact h.trans (MatExtGen.ext_hom_app_embedding (F := toKaroubi (Mat_ E) ⋙ G₁)
    (G := toKaroubi (Mat_ E) ⋙ G₂) γ x)

end KarMatExt

/-! ## Diagonal matrices -/

namespace DiagMat

open StringDiagrams.Mat_

variable {D : Type*} [Category D] [Preadditive D]

theorem comp_diagMat_apply {M : Mat_ D} {ι : Type} [Fintype ι] {X Y : ι → D}
    (f : M ⟶ (⟨ι, X⟩ : Mat_ D)) (φ : ∀ i, X i ⟶ Y i) (i : M.ι) (j : ι) :
    (f ≫ diagMat (D := D) φ : M ⟶ (⟨ι, Y⟩ : Mat_ D)) i j = f i j ≫ φ j := by
  classical
  rw [Mat_.comp_apply, Finset.sum_eq_single j]
  · exact congrArg (f i j ≫ ·) (permMat_apply_self (Equiv.refl ι) φ j)
  · intro b _ hb
    exact (congrArg (f i b ≫ ·) (permMat_apply_of_ne (Equiv.refl ι) φ hb)).trans Limits.comp_zero
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem diagMat_comp_apply {ι : Type} [Fintype ι] {X Y : ι → D} {M : Mat_ D}
    (φ : ∀ i, X i ⟶ Y i) (f : (⟨ι, Y⟩ : Mat_ D) ⟶ M) (i : ι) (j : M.ι) :
    (diagMat (D := D) φ ≫ f : (⟨ι, X⟩ : Mat_ D) ⟶ M) i j = φ i ≫ f i j := by
  classical
  rw [Mat_.comp_apply, Finset.sum_eq_single i]
  · exact congrArg (· ≫ f i j) (permMat_apply_self (Equiv.refl ι) φ i)
  · intro b _ hb
    exact (congrArg (· ≫ f b j) (permMat_apply_of_ne (Equiv.refl ι) φ (Ne.symm hb))).trans
      Limits.zero_comp
  · intro h
    exact absurd (Finset.mem_univ i) h

end DiagMat

/-! ## Shift structures -/

namespace TwoRep

open Bicategory StringDiagrams

universe w v u

/-- **A left shift structure** on a bicategory: endofunctors `S` of the hom categories with
isomorphisms `S(f) ≫ g ≅ S(f ≫ g)`, natural in `f` and `g` (e.g. the grading shift `⟨1⟩` of a
graded 2-category, CL §2.1.2, with `x⟨1⟩ y ≅ (x y)⟨1⟩`). -/
structure LeftShift (A : Type u) [Bicategory.{w, v} A] [∀ a b : A, Preadditive (a ⟶ b)] where
  /-- The shift on the hom category `a ⟶ b`. -/
  S : ∀ a b : A, (a ⟶ b) ⥤ (a ⟶ b)
  additive : ∀ a b : A, (S a b).Additive := by infer_instance
  /-- `S(f) ≫ g ≅ S(f ≫ g)`. -/
  iso : ∀ {a b c : A} (f : a ⟶ b) (g : b ⟶ c), (S a b).obj f ≫ g ≅ (S a c).obj (f ≫ g)
  iso_naturality_left : ∀ {a b c : A} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c),
    (S a b).map η ▷ g ≫ (iso f' g).hom = (iso f g).hom ≫ (S a c).map (η ▷ g)
  iso_naturality_right : ∀ {a b c : A} (f : a ⟶ b) {g g' : b ⟶ c} (θ : g ⟶ g'),
    (S a b).obj f ◁ θ ≫ (iso f g').hom = (iso f g).hom ≫ (S a c).map (f ◁ θ)

attribute [instance] LeftShift.additive

namespace LeftShift

variable {A : Type u} [Bicategory.{w, v} A] [∀ a b : A, Preadditive (a ⟶ b)]
  [PreadditiveBicategory A] (L : LeftShift A)

theorem matHcomp₂_eq {a b c : StringDiagrams.MatBicat A} {M M' : a ⟶ b} {N N' : b ⟶ c}
    (η : M ⟶ M') (θ : N ⟶ N') : hcomp₂ η θ = StringDiagrams.MatBicat.hcomp η θ := by
  show StringDiagrams.MatBicat.hcomp η (𝟙 N) ≫ StringDiagrams.MatBicat.hcomp (𝟙 M') θ = _
  rw [← StringDiagrams.MatBicat.hcomp_comp, Category.comp_id, Category.id_comp]

/-- The diagonal matrix of the isomorphisms `S(f) ≫ g ≅ S(f ≫ g)`. -/
abbrev diag {a b c : StringDiagrams.MatBicat A} (M : a ⟶ b) (N : b ⟶ c) :
    (L.S a.obj b.obj).mapMat_.obj M ≫ N ≅ (L.S a.obj c.obj).mapMat_.obj (M ≫ N) :=
  MatBicat.diagIso fun x : M.ι × N.ι => L.iso (M.X x.1) (N.X x.2)

theorem diag_comm {a b c : StringDiagrams.MatBicat A} {M M' : a ⟶ b} {N N' : b ⟶ c}
    (u : M ⟶ M') (q : N ⟶ N') :
    hcomp₂ ((L.S a.obj b.obj).mapMat_.map u) q ≫ (L.diag M' N').hom =
      (L.diag M N).hom ≫ (L.S a.obj c.obj).mapMat_.map (hcomp₂ u q) := by
  apply CategoryTheory.Mat_.hom_ext
  intro i j
  rw [matHcomp₂_eq]
  erw [matHcomp₂_eq]
  erw [DiagMat.comp_diagMat_apply, DiagMat.diagMat_comp_apply]
  show hcomp₂ ((L.S _ _).map (u i.1 j.1)) (q i.2 j.2) ≫ (L.iso _ _).hom =
    (L.iso _ _).hom ≫ (L.S _ _).map (hcomp₂ (u i.1 j.1) (q i.2 j.2))
  simp only [hcomp₂, Category.assoc, L.iso_naturality_right, reassoc_of% L.iso_naturality_left,
    Functor.map_comp]

/-- The shift of `Kar A`: `S` applied entrywise to matrices and idempotents. -/
abbrev karS (a b : Kar A) : (a ⟶ b) ⥤ (a ⟶ b) :=
  mapKaroubi (L.S a.obj.obj b.obj.obj).mapMat_

/-- `S(P) ≫ Q ≅ S(P ≫ Q)` in `Kar A`: the diagonal matrix of the isomorphisms of `L`. -/
def karIso {a b c : Kar A} (P : a ⟶ b) (Q : b ⟶ c) :
    (L.karS a b).obj P ≫ Q ≅ (L.karS a c).obj (P ≫ Q) :=
  StringDiagrams.Karoubi.mkIso (L.diag P.X Q.X) (L.diag_comm P.p Q.p)

/-- **The shift structure of `Kar A`** induced by a shift structure of `A`. -/
def kar : LeftShift (Kar A) where
  S := L.karS
  additive a b := by
    have := mapMat_additive (L.S a.obj.obj b.obj.obj)
    exact mapKaroubi_additive _
  iso P Q := L.karIso P Q
  iso_naturality_left {a b c P P'} u Q := Idempotents.Karoubi.hom_ext _ _ (by
    show hcomp₂ ((L.S _ _).mapMat_.map u.f) Q.p ≫ ((L.diag P'.X Q.X).hom ≫
        (L.S _ _).mapMat_.map (hcomp₂ P'.p Q.p)) =
      ((L.diag P.X Q.X).hom ≫ (L.S _ _).mapMat_.map (hcomp₂ P.p Q.p)) ≫
        (L.S _ _).mapMat_.map (hcomp₂ u.f Q.p)
    rw [← Category.assoc, L.diag_comm u.f Q.p, Category.assoc, Category.assoc, ← Functor.map_comp,
      ← Functor.map_comp,
      ← hcomp₂_comp, ← hcomp₂_comp, Idempotents.Karoubi.comp_p, Idempotents.Karoubi.p_comp,
      Q.idem])
  iso_naturality_right {a b c} P {Q Q'} v := Idempotents.Karoubi.hom_ext _ _ (by
    show hcomp₂ ((L.S _ _).mapMat_.map P.p) v.f ≫ ((L.diag P.X Q'.X).hom ≫
        (L.S _ _).mapMat_.map (hcomp₂ P.p Q'.p)) =
      ((L.diag P.X Q.X).hom ≫ (L.S _ _).mapMat_.map (hcomp₂ P.p Q.p)) ≫
        (L.S _ _).mapMat_.map (hcomp₂ P.p v.f)
    rw [← Category.assoc, L.diag_comm P.p v.f, Category.assoc, Category.assoc, ← Functor.map_comp,
      ← Functor.map_comp,
      ← hcomp₂_comp, ← hcomp₂_comp, Idempotents.Karoubi.comp_p, Idempotents.Karoubi.p_comp,
      P.idem])

end LeftShift

namespace DotExt

variable {B : Type u} [Bicategory.{w, v} B]

/-- The pasting argument behind the compatibility of the extended shift with the composition
constraints, at the inclusions of 1-morphisms of `A` (all 1-morphisms have the same objects). -/
theorem shift_incl_aux {P₀ P₁ P₂ : B} (T₀₁ : (P₀ ⟶ P₁) ⥤ (P₀ ⟶ P₁))
    (T₀₂ : (P₀ ⟶ P₂) ⥤ (P₀ ⟶ P₂)) {Ex Fx ESx EiSx FSx : P₀ ⟶ P₁} {Ey Fy : P₁ ⟶ P₂}
    {ESxy EiSxy EiSxy' FSxy EiSxyS FSxyS ESixy ESixy' Exy Eixy Fxy : P₀ ⟶ P₂}
    (mcSx_y : ESxy ⟶ ESx ≫ Ey) (ψx : ESx ⟶ T₀₁.obj Ex) (τE : T₀₁.obj Ex ≫ Ey ≅ T₀₂.obj (Ex ≫ Ey))
    (eLt : ESxy ⟶ ESixy) (ψxy : ESixy ⟶ T₀₂.obj Exy) (mcx_y : Exy ⟶ Ex ≫ Ey)
    (eεy : ESxy ⟶ EiSxy) (mcSxy' : EiSxy ⟶ EiSx ≫ Ey) (eε : ESx ⟶ EiSx)
    (h1 : eεy ≫ mcSxy' = mcSx_y ≫ eε ▷ Ey)
    (ιSx : EiSx ⟶ FSx) (φx : FSx ⟶ T₀₁.obj Fx) (ιx : Ex ≅ Fx)
    (h2 : ψx = eε ≫ ιSx ≫ φx ≫ T₀₁.map ιx.inv)
    (ιy : Ey ≅ Fy) (eMcSxy : EiSxy ⟶ EiSxy') (ιSxy : EiSxy' ⟶ FSxy) (FmcSxy : FSxy ⟶ FSx ≫ Fy)
    (h3 : mcSxy' ≫ ιSx ▷ Ey ≫ FSx ◁ ιy.hom = eMcSxy ≫ ιSxy ≫ FmcSxy)
    (τF : T₀₁.obj Fx ≫ Fy ≅ T₀₂.obj (Fx ≫ Fy)) (FL : FSxy ⟶ FSxyS) (φxy : FSxyS ⟶ T₀₂.obj Fxy)
    (Fmcxy : Fxy ⟶ Fx ≫ Fy)
    (h4 : FmcSxy ≫ φx ▷ Fy ≫ τF.hom = FL ≫ φxy ≫ T₀₂.map Fmcxy)
    (τFE : T₀₁.obj Fx ≫ Ey ≅ T₀₂.obj (Fx ≫ Ey))
    (h5a : T₀₁.map ιx.inv ▷ Ey ≫ τE.hom = τFE.hom ≫ T₀₂.map (ιx.inv ▷ Ey))
    (h5b : T₀₁.obj Fx ◁ ιy.inv ≫ τFE.hom = τF.hom ≫ T₀₂.map (Fx ◁ ιy.inv))
    (ιxy : Eixy ≅ Fxy) (eMcxy : Eixy ≅ Exy)
    (h6 : mcx_y ≫ ιx.hom ▷ Ey ≫ Fx ◁ ιy.hom = eMcxy.inv ≫ ιxy.hom ≫ Fmcxy)
    (eiL : EiSxy' ⟶ EiSxyS) (ιS_xy : EiSxyS ⟶ FSxyS) (h7 : eiL ≫ ιS_xy = ιSxy ≫ FL)
    (eSw : ESixy' ≅ ESixy) (ψixy : ESixy' ⟶ T₀₂.obj Eixy)
    (h8 : eSw.hom ≫ ψxy = ψixy ≫ T₀₂.map eMcxy.hom)
    (eεxy : ESixy' ⟶ EiSxyS) (h9 : ψixy = eεxy ≫ ιS_xy ≫ φxy ≫ T₀₂.map ιxy.inv)
    (h10 : eεy ≫ eMcSxy ≫ eiL = eLt ≫ eSw.inv ≫ eεxy) :
    mcSx_y ≫ ψx ▷ Ey ≫ τE.hom = eLt ≫ ψxy ≫ T₀₂.map mcx_y := by
  have hm : mcx_y = eMcxy.inv ≫ ιxy.hom ≫ Fmcxy ≫ Fx ◁ ιy.inv ≫ ιx.inv ▷ Ey := by
    calc mcx_y = mcx_y ≫ (ιx.hom ▷ Ey ≫ Fx ◁ ιy.hom) ≫ (Fx ◁ ιy.inv ≫ ιx.inv ▷ Ey) := by
          simp only [Category.assoc, whiskerLeft_hom_inv_assoc, hom_inv_whiskerRight,
            Category.comp_id]
      _ = _ := by simp only [Category.assoc]; rw [reassoc_of% h6]
  have h6' : Fmcxy ≫ Fx ◁ ιy.inv ≫ ιx.inv ▷ Ey = ιxy.inv ≫ eMcxy.hom ≫ mcx_y := by
    rw [hm]; simp
  have h8' : ψxy = eSw.inv ≫ ψixy ≫ T₀₂.map eMcxy.hom := by
    rw [← h8, Iso.inv_hom_id_assoc]
  rw [h2, h8', h9]
  simp only [comp_whiskerRight, Category.assoc]
  rw [← reassoc_of% h1]
  -- insert `ιy ≫ ιy⁻¹` after `ιSx ▷ Ey`
  rw [show ∀ {Z} (h : _ ⟶ Z), ιSx ▷ Ey ≫ φx ▷ Ey ≫ h =
      ιSx ▷ Ey ≫ FSx ◁ ιy.hom ≫ FSx ◁ ιy.inv ≫ φx ▷ Ey ≫ h from fun h => by
    rw [whiskerLeft_hom_inv_assoc]]
  rw [reassoc_of% h3, whisker_exchange_assoc, h5a, reassoc_of% h5b,
    reassoc_of% h4, ← reassoc_of% h7, reassoc_of% h10, ← Functor.map_comp, ← Functor.map_comp, h6',
    Functor.map_comp, Functor.map_comp]

end DotExt

/-- **A pseudofunctor commuting with left shift structures**: isomorphisms
`S(f) ↦ F(S f) ≅ T(F f)` on the hom categories, compatible with the composition constraints of `F`
and the isomorphisms `S(f) ≫ g ≅ S(f ≫ g)`, `T(u) ≫ v ≅ T(u ≫ v)` (CL §2.1.2: a graded 2-functor
commutes with the grading shift compatibly with horizontal composition). -/
structure LeftShiftCompat {A : Type u} [Bicategory.{w, v} A] [∀ a b : A, Preadditive (a ⟶ b)]
    {B : Type*} [Bicategory B] [∀ a b : B, Preadditive (a ⟶ b)] (F : Pseudofunctor A B)
    (L : LeftShift A) (M : LeftShift B) where
  /-- `F(S f) ≅ T(F f)`, naturally in `f`. -/
  φ : ∀ a b : A, L.S a b ⋙ F.mapFunctor a b ≅ F.mapFunctor a b ⋙ M.S (F.obj a) (F.obj b)
  coh : ∀ {a b c : A} (f : a ⟶ b) (g : b ⟶ c),
    (F.mapComp ((L.S a b).obj f) g).hom ≫ (φ a b).hom.app f ▷ F.map g ≫
        (M.iso (F.map f) (F.map g)).hom =
      F.map₂ (L.iso f g).hom ≫ (φ a c).hom.app (f ≫ g) ≫ (M.S _ _).map (F.mapComp f g).hom

namespace DotExt

variable {A : Type u} [Bicategory.{w, v} A] [∀ a b : A, Preadditive (a ⟶ b)]
  [PreadditiveBicategory A] {B : Type*} [Bicategory B]
  [∀ a b : B, Preadditive (a ⟶ b)] [PreadditiveBicategory B]
  [∀ a b : B, HasFiniteBiproducts (a ⟶ b)] [∀ a b : B, IsIdempotentComplete (a ⟶ b)]
  (F : Pseudofunctor A B) (hF : AddHyp F) {L : LeftShift A} {M : LeftShift B}
  (C : LeftShiftCompat F L M)

/-- The extension of `C.φ` to the additive Karoubi envelope. -/
def extShiftIso (a b : Kar A) :
    L.kar.S a b ⋙ (ext F hF).mapFunctor a b ≅
      (ext F hF).mapFunctor a b ⋙ M.S ((ext F hF).obj a) ((ext F hF).obj b) :=
  extNatIso F hF a b (L.S a.obj.obj b.obj.obj) (M.S _ _) (C.φ a.obj.obj b.obj.obj)

theorem extShiftIso_hom_app_incl {a b : A} (x : a ⟶ b) :
    (extShiftIso F hF C ((incl A).obj a) ((incl A).obj b)).hom.app ((incl A).map x) =
      (ext F hF).map₂ ((KarMatExt.inclShift (L.S a b)).hom.app x) ≫
        (inclIso F hF ((L.S a b).obj x)).hom ≫ (C.φ a b).hom.app x ≫
          (M.S _ _).map (inclIso F hF x).inv := by
  have : (mapKaroubi (L.S a b).mapMat_).Additive := by
    have := mapMat_additive (L.S a b)
    exact mapKaroubi_additive _
  have := mapFunctor_additive F hF ((incl A).obj a) ((incl A).obj b)
  have h1 : (L.kar.S ((incl A).obj a) ((incl A).obj b)).Additive := L.kar.additive _ _
  have i1 : (L.kar.S ((incl A).obj a) ((incl A).obj b) ⋙
    (ext F hF).mapFunctor ((incl A).obj a) ((incl A).obj b)).Additive := inferInstance
  have i2 : ((ext F hF).mapFunctor ((incl A).obj a) ((incl A).obj b) ⋙
    M.S ((ext F hF).obj ((incl A).obj a)) ((ext F hF).obj ((incl A).obj b))).Additive :=
    inferInstance
  exact @KarMatExt.ext_hom_app_incl _ _ _ _ _ _ _ _ _ i1 i2 _ x

attribute [local instance] MatBicat.uniqueSingleι MatBicat.uniqueCompι MatBicat.uniqueIdι

/-- At the inclusions of 1-morphisms of `A`, the isomorphism `S(P) ≫ Q ≅ S(P ≫ Q)` of `Kar A` is
that of `A`. -/
theorem karIso_incl {a b c : A} (x : a ⟶ b) (y : b ⟶ c) :
    (((KarMatExt.inclShift (L.S a b)).hom.app x :
        (L.kar.S _ _).obj ((incl A).map x) ⟶ (incl A).map ((L.S a b).obj x)) ▷ (incl A).map y) ≫
      ((incl A).mapComp ((L.S a b).obj x) y).inv ≫ (incl A).map₂ (L.iso x y).hom =
    (L.kar.iso ((incl A).map x) ((incl A).map y)).hom ≫
      (L.kar.S _ _).map ((incl A).mapComp x y).inv ≫
        ((KarMatExt.inclShift (L.S a c)).hom.app (x ≫ y) :
          (L.kar.S _ _).obj ((incl A).map (x ≫ y)) ⟶ (incl A).map ((L.S a c).obj (x ≫ y))) := by
  apply Idempotents.Karoubi.hom_ext
  apply CategoryTheory.Mat_.hom_ext
  intro i j
  show (hcomp₂ (𝟙 _ ≫ 𝟙 _) (𝟙 _) ≫ ((𝟙 _ ≫ 𝟙 _) ≫ MatBicat.singleCompInv ((L.S a b).obj x) y) ≫
      MatBicat.mat1 (L.iso x y).hom) i j =
    (((L.diag _ _).hom ≫ (L.S a c).mapMat_.map (hcomp₂ (𝟙 _) (𝟙 _))) ≫
      (L.S a c).mapMat_.map ((𝟙 _ ≫ 𝟙 _) ≫ MatBicat.singleCompInv x y) ≫ (𝟙 _ ≫ 𝟙 _)) i j
  simp only [Category.id_comp, Category.comp_id, hcomp₂_id_id, CategoryTheory.Functor.map_id]
  erw [MatBicat.comp_apply_unique, DiagMat.diagMat_comp_apply]
  show 𝟙 _ ≫ (L.iso x y).hom = (L.iso x y).hom ≫ (L.S a c).map (𝟙 _)
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

theorem mapComp_naturality_left' {𝒳 𝒴 : Type*} [Bicategory 𝒳] [Bicategory 𝒴]
    (G : Pseudofunctor 𝒳 𝒴) {a b c : 𝒳} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) :
    G.map₂ (η ▷ g) ≫ (G.mapComp f' g).hom = (G.mapComp f g).hom ≫ G.map₂ η ▷ G.map g := by
  rw [G.map₂_whisker_right]
  simp

theorem mapComp_naturality_right' {𝒳 𝒴 : Type*} [Bicategory 𝒳] [Bicategory 𝒴]
    (G : Pseudofunctor 𝒳 𝒴) {a b c : 𝒳} (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') :
    G.map₂ (f ◁ η) ≫ (G.mapComp f g').hom = (G.mapComp f g).hom ≫ G.map f ◁ G.map₂ η := by
  rw [G.map₂_whisker_left]
  simp

theorem map₂_comp₃_eq {𝒳 𝒴 : Type*} [Bicategory 𝒳] [Bicategory 𝒴] (G : Pseudofunctor 𝒳 𝒴)
    {a b : 𝒳} {f₀ f₁ f₂ f₃ f₁' f₂' : a ⟶ b} {p : f₀ ⟶ f₁} {q : f₁ ⟶ f₂} {r : f₂ ⟶ f₃}
    {p' : f₀ ⟶ f₁'} {q' : f₁' ⟶ f₂'} {r' : f₂' ⟶ f₃} (h : p ≫ q ≫ r = p' ≫ q' ≫ r') :
    G.map₂ p ≫ G.map₂ q ≫ G.map₂ r = G.map₂ p' ≫ G.map₂ q' ≫ G.map₂ r' := by
  simp only [← PrelaxFunctor.map₂_comp, h]

/-- The composite `ext(S X ≫ Y) → ext(S X) ext Y → T(ext X) ext Y → T(ext X ext Y)`. -/
abbrev lhs {a b c : Kar A} (X : a ⟶ b) (Y : b ⟶ c) :
    (ext F hF).map ((L.kar.S a b).obj X ≫ Y) ⟶
      (M.S ((ext F hF).obj a) ((ext F hF).obj c)).obj ((ext F hF).map X ≫ (ext F hF).map Y) :=
  ((ext F hF).mapComp ((L.kar.S a b).obj X) Y).hom ≫
    (extShiftIso F hF C a b).hom.app X ▷ (ext F hF).map Y ≫
      (M.iso ((ext F hF).map X) ((ext F hF).map Y)).hom

/-- The composite `ext(S X ≫ Y) → ext(S(X ≫ Y)) → T(ext(X ≫ Y)) → T(ext X ext Y)`. -/
abbrev rhs {a b c : Kar A} (X : a ⟶ b) (Y : b ⟶ c) :
    (ext F hF).map ((L.kar.S a b).obj X ≫ Y) ⟶
      (M.S ((ext F hF).obj a) ((ext F hF).obj c)).obj ((ext F hF).map X ≫ (ext F hF).map Y) :=
  (ext F hF).map₂ (L.kar.iso X Y).hom ≫ (extShiftIso F hF C a c).hom.app (X ≫ Y) ≫
    (M.S _ _).map ((ext F hF).mapComp X Y).hom

theorem lhs_eq_rhs_incl {a b c : A} (x : a ⟶ b) (y : b ⟶ c) :
    lhs F hF C ((incl A).map x) ((incl A).map y) =
      rhs F hF C ((incl A).map x) ((incl A).map y) := by
  have h1 := mapComp_naturality_left' (ext F hF)
      (show (L.kar.S ((incl A).obj a) ((incl A).obj b)).obj ((incl A).map x) ⟶
        (incl A).map ((L.S a b).obj x) from (KarMatExt.inclShift (L.S a b)).hom.app x)
      ((incl A).map y)
  have h2 := extShiftIso_hom_app_incl F hF C x
  have h3 := inclIso_mapComp F hF ((L.S a b).obj x) y
  have h4 := C.coh x y
  have h5a := M.iso_naturality_left (inclIso F hF x).inv ((ext F hF).map ((incl A).map y))
  have h5b := M.iso_naturality_right (F.map x) (inclIso F hF y).inv
  have h6 := inclIso_mapComp F hF x y
  have h7 := inclIso_naturality F hF (L.iso x y).hom
  have h8 := (extShiftIso F hF C ((incl A).obj a) ((incl A).obj c)).hom.naturality
    ((incl A).mapComp x y).hom
  have h9 := extShiftIso_hom_app_incl F hF C (x ≫ y)
  have h10 := map₂_comp₃_eq (ext F hF) (karIso_incl (L := L) x y)
  exact shift_incl_aux _ _ _ _ _ _ _ _ _ _ _ h1 _ _ _ h2 (inclIso F hF y) _ _ _ h3 _ _ _ _ h4 _ h5a
    h5b (inclIso F hF (x ≫ y)) ((ext F hF).map₂Iso ((incl A).mapComp x y)) h6 _ _ h7
    ((ext F hF).map₂Iso ((L.kar.S _ _).mapIso ((incl A).mapComp x y))) _ h8 _ h9 h10

theorem lhs_nat_aux {P₀ P₁ P₂ : B} (T₀₁ : (P₀ ⟶ P₁) ⥤ (P₀ ⟶ P₁)) (T₀₂ : (P₀ ⟶ P₂) ⥤ (P₀ ⟶ P₂))
    {E₁ E₁' : P₀ ⟶ P₂} {E₂ E₂' Ex Ex' : P₀ ⟶ P₁} {Ey : P₁ ⟶ P₂} (m : E₁ ⟶ E₂ ≫ Ey)
    (m' : E₁' ⟶ E₂' ≫ Ey) (a₁ : E₁ ⟶ E₁') (a₂ : E₂ ⟶ E₂') (ψ : E₂ ⟶ T₀₁.obj Ex)
    (ψ' : E₂' ⟶ T₀₁.obj Ex') (b : Ex ⟶ Ex') (τ : T₀₁.obj Ex ≫ Ey ⟶ T₀₂.obj (Ex ≫ Ey))
    (τ' : T₀₁.obj Ex' ≫ Ey ⟶ T₀₂.obj (Ex' ≫ Ey)) (h₁ : a₁ ≫ m' = m ≫ a₂ ▷ Ey)
    (h₂ : a₂ ≫ ψ' = ψ ≫ T₀₁.map b) (h₃ : T₀₁.map b ▷ Ey ≫ τ' = τ ≫ T₀₂.map (b ▷ Ey)) :
    a₁ ≫ m' ≫ ψ' ▷ Ey ≫ τ' = (m ≫ ψ ▷ Ey ≫ τ) ≫ T₀₂.map (b ▷ Ey) := by
  rw [reassoc_of% h₁, ← comp_whiskerRight_assoc, h₂, comp_whiskerRight_assoc, h₃]
  simp only [Category.assoc]

theorem rhs_nat_aux {P₀ P₂ : B} (T₀₂ : (P₀ ⟶ P₂) ⥤ (P₀ ⟶ P₂))
    {E₁ E₁' E₃ E₃' Exy Exy' G G' : P₀ ⟶ P₂}
    (eL : E₁ ⟶ E₃) (eL' : E₁' ⟶ E₃') (ψ : E₃ ⟶ T₀₂.obj Exy) (ψ' : E₃' ⟶ T₀₂.obj Exy')
    (mc : Exy ⟶ G) (mc' : Exy' ⟶ G') (a₁ : E₁ ⟶ E₁') (a₃ : E₃ ⟶ E₃') (c : Exy ⟶ Exy')
    (d : G ⟶ G') (h₁ : a₁ ≫ eL' = eL ≫ a₃) (h₂ : a₃ ≫ ψ' = ψ ≫ T₀₂.map c)
    (h₃ : c ≫ mc' = mc ≫ d) :
    a₁ ≫ eL' ≫ ψ' ≫ T₀₂.map mc' = (eL ≫ ψ ≫ T₀₂.map mc) ≫ T₀₂.map d := by
  rw [reassoc_of% h₁, reassoc_of% h₂, ← Functor.map_comp, h₃, Functor.map_comp]
  simp only [Category.assoc]

theorem map₂_comp₂_eq {𝒳 𝒴 : Type*} [Bicategory 𝒳] [Bicategory 𝒴] (G : Pseudofunctor 𝒳 𝒴)
    {a b : 𝒳} {f₀ f₁ f₂ f₁' : a ⟶ b} {p : f₀ ⟶ f₁} {q : f₁ ⟶ f₂} {p' : f₀ ⟶ f₁'}
    {q' : f₁' ⟶ f₂} (h : p ≫ q = p' ≫ q') : G.map₂ p ≫ G.map₂ q = G.map₂ p' ≫ G.map₂ q' := by
  simp only [← PrelaxFunctor.map₂_comp, h]

/-- `lhs`, as a natural transformation in the first variable. -/
def lhsNatLeft {a b c : Kar A} (Y : b ⟶ c) :
    L.kar.S a b ⋙ postcomp a Y ⋙ (ext F hF).mapFunctor a c ⟶
      (ext F hF).mapFunctor a b ⋙ postcomp ((ext F hF).obj a) ((ext F hF).map Y) ⋙
        M.S ((ext F hF).obj a) ((ext F hF).obj c) where
  app X := lhs F hF C X Y
  naturality {_ _} u :=
    lhs_nat_aux _ _ _ _ _ _ _ _ _ _ _ (mapComp_naturality_left' (ext F hF) _ Y)
      ((extShiftIso F hF C a b).hom.naturality u) (M.iso_naturality_left _ _)

/-- `rhs`, as a natural transformation in the first variable. -/
def rhsNatLeft {a b c : Kar A} (Y : b ⟶ c) :
    L.kar.S a b ⋙ postcomp a Y ⋙ (ext F hF).mapFunctor a c ⟶
      (ext F hF).mapFunctor a b ⋙ postcomp ((ext F hF).obj a) ((ext F hF).map Y) ⋙
        M.S ((ext F hF).obj a) ((ext F hF).obj c) where
  app X := rhs F hF C X Y
  naturality {_ _} u :=
    rhs_nat_aux _ _ _ _ _ _ _ _ _ _ _
      (map₂_comp₂_eq (ext F hF) (L.kar.iso_naturality_left u Y))
      ((extShiftIso F hF C a c).hom.naturality (u ▷ Y)) (mapComp_naturality_left' (ext F hF) u Y)

theorem lhs_nat_aux_right {P₀ P₁ P₂ : B} (T₀₁ : (P₀ ⟶ P₁) ⥤ (P₀ ⟶ P₁))
    (T₀₂ : (P₀ ⟶ P₂) ⥤ (P₀ ⟶ P₂)) {E₁ E₁' : P₀ ⟶ P₂} {E₂ Ex : P₀ ⟶ P₁} {Ey Ey' : P₁ ⟶ P₂}
    (m : E₁ ⟶ E₂ ≫ Ey) (m' : E₁' ⟶ E₂ ≫ Ey') (a₁ : E₁ ⟶ E₁') (bv : Ey ⟶ Ey')
    (ψ : E₂ ⟶ T₀₁.obj Ex) (τ : T₀₁.obj Ex ≫ Ey ⟶ T₀₂.obj (Ex ≫ Ey))
    (τ' : T₀₁.obj Ex ≫ Ey' ⟶ T₀₂.obj (Ex ≫ Ey')) (h₁ : a₁ ≫ m' = m ≫ E₂ ◁ bv)
    (h₃ : T₀₁.obj Ex ◁ bv ≫ τ' = τ ≫ T₀₂.map (Ex ◁ bv)) :
    a₁ ≫ m' ≫ ψ ▷ Ey' ≫ τ' = (m ≫ ψ ▷ Ey ≫ τ) ≫ T₀₂.map (Ex ◁ bv) := by
  rw [reassoc_of% h₁, whisker_exchange_assoc, h₃]
  simp only [Category.assoc]

/-- `lhs`, as a natural transformation in the second variable. -/
def lhsNatRight {a b c : Kar A} (X : a ⟶ b) :
    precomp c ((L.kar.S a b).obj X) ⋙ (ext F hF).mapFunctor a c ⟶
      (ext F hF).mapFunctor b c ⋙ precomp ((ext F hF).obj c) ((ext F hF).map X) ⋙
        M.S ((ext F hF).obj a) ((ext F hF).obj c) where
  app Y := lhs F hF C X Y
  naturality {_ _} v :=
    lhs_nat_aux_right _ _ _ _ _ _ _ _ _ (mapComp_naturality_right' (ext F hF) _ v)
      (M.iso_naturality_right _ _)

/-- `rhs`, as a natural transformation in the second variable. -/
def rhsNatRight {a b c : Kar A} (X : a ⟶ b) :
    precomp c ((L.kar.S a b).obj X) ⋙ (ext F hF).mapFunctor a c ⟶
      (ext F hF).mapFunctor b c ⋙ precomp ((ext F hF).obj c) ((ext F hF).map X) ⋙
        M.S ((ext F hF).obj a) ((ext F hF).obj c) where
  app Y := rhs F hF C X Y
  naturality {_ _} v :=
    rhs_nat_aux _ _ _ _ _ _ _ _ _ _ _
      (map₂_comp₂_eq (ext F hF) (L.kar.iso_naturality_right X v))
      ((extShiftIso F hF C a c).hom.naturality (X ◁ v)) (mapComp_naturality_right' (ext F hF) X v)

theorem lhs_eq_rhs_inclRight {a b c : A} (x : a ⟶ b) (Y : (incl A).obj b ⟶ (incl A).obj c) :
    lhs F hF C ((incl A).map x) Y = rhs F hF C ((incl A).map x) Y := by
  have i₁ : (precomp ((incl A).obj c) ((L.kar.S _ _).obj ((incl A).map x)) ⋙
      (ext F hF).mapFunctor ((incl A).obj a) ((incl A).obj c)).Additive := inferInstance
  have h := @KarMatExt.natTrans_ext _ _ _ _ _ _ _ _ i₁ (lhsNatRight F hF C ((incl A).map x))
    (rhsNatRight F hF C ((incl A).map x)) (fun y => lhs_eq_rhs_incl F hF C x y)
  exact congr_app h Y


theorem lhs_eq_rhs_inclObj {a b c : A} (X : (incl A).obj a ⟶ (incl A).obj b)
    (Y : (incl A).obj b ⟶ (incl A).obj c) : lhs F hF C X Y = rhs F hF C X Y := by
  have i₁ : (L.kar.S ((incl A).obj a) ((incl A).obj b) ⋙ postcomp ((incl A).obj a) Y ⋙
      (ext F hF).mapFunctor ((incl A).obj a) ((incl A).obj c)).Additive := inferInstance
  have h := @KarMatExt.natTrans_ext _ _ _ _ _ _ _ _ i₁ (lhsNatLeft F hF C Y)
    (rhsNatLeft F hF C Y) (fun x => lhs_eq_rhs_inclRight F hF C x Y)
  exact congr_app h X

/-- **The extension of a pseudofunctor commuting with left shift structures commutes with the
induced shift structures**, compatibly with the composition constraints, on the whole additive
Karoubi envelope. -/
theorem lhs_eq_rhs {a b c : Kar A} (X : a ⟶ b) (Y : b ⟶ c) :
    lhs F hF C X Y = rhs F hF C X Y := by
  obtain ⟨⟨a⟩⟩ := a
  obtain ⟨⟨b⟩⟩ := b
  obtain ⟨⟨c⟩⟩ := c
  exact lhs_eq_rhs_inclObj F hF C X Y

/-- **The extension of a pseudofunctor commuting with left shift structures commutes with the
induced left shift structure of the additive Karoubi envelope.** -/
def _root_.Categorification.TwoRep.LeftShiftCompat.ext : LeftShiftCompat (ext F hF) L.kar M where
  φ := extShiftIso F hF C
  coh X Y := lhs_eq_rhs F hF C X Y

end DotExt

namespace LeftShiftCompat

variable {A : Type u} [Bicategory.{w, v} A] [∀ a b : A, Preadditive (a ⟶ b)] {B : Type*}
  [Bicategory B] [∀ a b : B, Preadditive (a ⟶ b)] {G : Pseudofunctor A B} {L : LeftShift A}
  {M : LeftShift B} (C : LeftShiftCompat G L M)

/-- The component `G(S f) ⟶ T(G f)` of `C.φ`. -/
def app {a b : A} (f : a ⟶ b) : G.map ((L.S a b).obj f) ⟶ (M.S _ _).obj (G.map f) :=
  (C.φ a b).hom.app f

theorem app_naturality {a b : A} {f g : a ⟶ b} (η : f ⟶ g) :
    G.map₂ ((L.S a b).map η) ≫ C.app g = C.app f ≫ (M.S _ _).map (G.map₂ η) :=
  (C.φ a b).hom.naturality η

theorem coh' {a b c : A} (f : a ⟶ b) (g : b ⟶ c) :
    (G.mapComp ((L.S a b).obj f) g).hom ≫ C.app f ▷ G.map g ≫ (M.iso (G.map f) (G.map g)).hom =
      G.map₂ (L.iso f g).hom ≫ C.app (f ≫ g) ≫ (M.S _ _).map (G.mapComp f g).hom :=
  C.coh f g

/-- **Compatibility with the identity constraints**: under `S(1) ≫ f ≅ S(1 ≫ f) ≅ S f` and
`T(1) ≫ v ≅ T(1 ≫ v) ≅ T v`, the isomorphism `G(S f) ≅ T(G f)` is the composite of the
composition constraint at `(S 1, f)`, `G(S 1) ≅ T(G 1)` and the identity constraint. -/
theorem mapId {a b : A} (f : a ⟶ b) :
    (G.mapComp ((L.S a a).obj (𝟙 a)) f).hom ≫ C.app (𝟙 a) ▷ G.map f ≫
        (M.S _ _).map (G.mapId a).hom ▷ G.map f ≫ (M.iso (𝟙 _) (G.map f)).hom ≫
          (M.S _ _).map (λ_ (G.map f)).hom =
      G.map₂ ((L.iso (𝟙 a) f).hom ≫ (L.S a b).map (λ_ f).hom) ≫ C.app f := by
  rw [reassoc_of% M.iso_naturality_left, reassoc_of% C.coh', ← Functor.map_comp,
    ← Functor.map_comp, ← G.map₂_left_unitor, ← C.app_naturality, PrelaxFunctor.map₂_comp,
    Category.assoc]

end LeftShiftCompat

/-! ## Right shift structures -/

/-- **A right shift structure** on a bicategory: endofunctors `S` of the hom categories with
isomorphisms `f ≫ S(g) ≅ S(f ≫ g)`, natural in `f` and `g` (e.g. the grading shift `⟨1⟩` of a
graded 2-category, CL §2.1.2, with `x (y⟨1⟩) ≅ (x y)⟨1⟩`). -/
structure RightShift (A : Type u) [Bicategory.{w, v} A] [∀ a b : A, Preadditive (a ⟶ b)] where
  /-- The shift on the hom category `a ⟶ b`. -/
  S : ∀ a b : A, (a ⟶ b) ⥤ (a ⟶ b)
  additive : ∀ a b : A, (S a b).Additive := by infer_instance
  /-- `f ≫ S(g) ≅ S(f ≫ g)`. -/
  iso : ∀ {a b c : A} (f : a ⟶ b) (g : b ⟶ c), f ≫ (S b c).obj g ≅ (S a c).obj (f ≫ g)
  iso_naturality_left : ∀ {a b c : A} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c),
    η ▷ (S b c).obj g ≫ (iso f' g).hom = (iso f g).hom ≫ (S a c).map (η ▷ g)
  iso_naturality_right : ∀ {a b c : A} (f : a ⟶ b) {g g' : b ⟶ c} (θ : g ⟶ g'),
    f ◁ (S b c).map θ ≫ (iso f g').hom = (iso f g).hom ≫ (S a c).map (f ◁ θ)

attribute [instance] RightShift.additive

namespace RightShift

variable {A : Type u} [Bicategory.{w, v} A] [∀ a b : A, Preadditive (a ⟶ b)]
  [PreadditiveBicategory A] (L : RightShift A)

/-- The diagonal matrix of the isomorphisms `f ≫ S(g) ≅ S(f ≫ g)`. -/
abbrev diag {a b c : StringDiagrams.MatBicat A} (M : a ⟶ b) (N : b ⟶ c) :
    M ≫ (L.S b.obj c.obj).mapMat_.obj N ≅ (L.S a.obj c.obj).mapMat_.obj (M ≫ N) :=
  MatBicat.diagIso fun x : M.ι × N.ι => L.iso (M.X x.1) (N.X x.2)

theorem diag_comm {a b c : StringDiagrams.MatBicat A} {M M' : a ⟶ b} {N N' : b ⟶ c}
    (u : M ⟶ M') (q : N ⟶ N') :
    hcomp₂ u ((L.S b.obj c.obj).mapMat_.map q) ≫ (L.diag M' N').hom =
      (L.diag M N).hom ≫ (L.S a.obj c.obj).mapMat_.map (hcomp₂ u q) := by
  apply CategoryTheory.Mat_.hom_ext
  intro i j
  rw [LeftShift.matHcomp₂_eq]
  erw [LeftShift.matHcomp₂_eq]
  erw [DiagMat.comp_diagMat_apply, DiagMat.diagMat_comp_apply]
  show hcomp₂ (u i.1 j.1) ((L.S _ _).map (q i.2 j.2)) ≫ (L.iso _ _).hom =
    (L.iso _ _).hom ≫ (L.S _ _).map (hcomp₂ (u i.1 j.1) (q i.2 j.2))
  simp only [hcomp₂, Category.assoc, L.iso_naturality_right, reassoc_of% L.iso_naturality_left,
    Functor.map_comp]

/-- The shift of `Kar A`: `S` applied entrywise to matrices and idempotents. -/
abbrev karS (a b : Kar A) : (a ⟶ b) ⥤ (a ⟶ b) :=
  mapKaroubi (L.S a.obj.obj b.obj.obj).mapMat_

/-- `P ≫ S(Q) ≅ S(P ≫ Q)` in `Kar A`: the diagonal matrix of the isomorphisms of `L`. -/
def karIso {a b c : Kar A} (P : a ⟶ b) (Q : b ⟶ c) :
    P ≫ (L.karS b c).obj Q ≅ (L.karS a c).obj (P ≫ Q) :=
  StringDiagrams.Karoubi.mkIso (L.diag P.X Q.X) (L.diag_comm P.p Q.p)

/-- **The right shift structure of `Kar A`** induced by a right shift structure of `A`. -/
def kar : RightShift (Kar A) where
  S := L.karS
  additive a b := by
    have := mapMat_additive (L.S a.obj.obj b.obj.obj)
    exact mapKaroubi_additive _
  iso P Q := L.karIso P Q
  iso_naturality_left {a b c P P'} u Q := Idempotents.Karoubi.hom_ext _ _ (by
    show hcomp₂ u.f ((L.S _ _).mapMat_.map Q.p) ≫ ((L.diag P'.X Q.X).hom ≫
        (L.S _ _).mapMat_.map (hcomp₂ P'.p Q.p)) =
      ((L.diag P.X Q.X).hom ≫ (L.S _ _).mapMat_.map (hcomp₂ P.p Q.p)) ≫
        (L.S _ _).mapMat_.map (hcomp₂ u.f Q.p)
    rw [← Category.assoc, L.diag_comm u.f Q.p, Category.assoc, Category.assoc, ← Functor.map_comp,
      ← Functor.map_comp, ← hcomp₂_comp, ← hcomp₂_comp, Idempotents.Karoubi.comp_p,
      Idempotents.Karoubi.p_comp, Q.idem])
  iso_naturality_right {a b c} P {Q Q'} v := Idempotents.Karoubi.hom_ext _ _ (by
    show hcomp₂ P.p ((L.S _ _).mapMat_.map v.f) ≫ ((L.diag P.X Q'.X).hom ≫
        (L.S _ _).mapMat_.map (hcomp₂ P.p Q'.p)) =
      ((L.diag P.X Q.X).hom ≫ (L.S _ _).mapMat_.map (hcomp₂ P.p Q.p)) ≫
        (L.S _ _).mapMat_.map (hcomp₂ P.p v.f)
    rw [← Category.assoc, L.diag_comm P.p v.f, Category.assoc, Category.assoc, ← Functor.map_comp,
      ← Functor.map_comp, ← hcomp₂_comp, ← hcomp₂_comp, Idempotents.Karoubi.comp_p,
      Idempotents.Karoubi.p_comp, P.idem])

end RightShift

/-- **A pseudofunctor commuting with right shift structures** (see `LeftShiftCompat`). -/
structure RightShiftCompat {A : Type u} [Bicategory.{w, v} A] [∀ a b : A, Preadditive (a ⟶ b)]
    {B : Type*} [Bicategory B] [∀ a b : B, Preadditive (a ⟶ b)] (F : Pseudofunctor A B)
    (L : RightShift A) (M : RightShift B) where
  /-- `F(S g) ≅ T(F g)`, naturally in `g`. -/
  φ : ∀ a b : A, L.S a b ⋙ F.mapFunctor a b ≅ F.mapFunctor a b ⋙ M.S (F.obj a) (F.obj b)
  coh : ∀ {a b c : A} (f : a ⟶ b) (g : b ⟶ c),
    (F.mapComp f ((L.S b c).obj g)).hom ≫ F.map f ◁ (φ b c).hom.app g ≫
        (M.iso (F.map f) (F.map g)).hom =
      F.map₂ (L.iso f g).hom ≫ (φ a c).hom.app (f ≫ g) ≫ (M.S _ _).map (F.mapComp f g).hom

namespace DotExt

variable {B : Type u} [Bicategory.{w, v} B]

/-- The pasting argument behind `lhsR_eq_rhsR_incl` (see `shift_incl_aux`). -/
theorem shift_incl_auxR {P₀ P₁ P₂ : B} (T₁₂ : (P₁ ⟶ P₂) ⥤ (P₁ ⟶ P₂))
    (T₀₂ : (P₀ ⟶ P₂) ⥤ (P₀ ⟶ P₂)) {Ex Fx : P₀ ⟶ P₁} {Ey Fy ESy EiSy FSy : P₁ ⟶ P₂}
    {ExSy EixSy EixSy' FxSy EiSxyS FSxyS ESixy ESixy' Exy Eixy Fxy : P₀ ⟶ P₂}
    (mcx_Sy : ExSy ⟶ Ex ≫ ESy) (ψy : ESy ⟶ T₁₂.obj Ey) (τE : Ex ≫ T₁₂.obj Ey ≅ T₀₂.obj (Ex ≫ Ey))
    (eLt : ExSy ⟶ ESixy) (ψxy : ESixy ⟶ T₀₂.obj Exy) (mcx_y : Exy ⟶ Ex ≫ Ey)
    (eεy : ExSy ⟶ EixSy) (mcx_Sy' : EixSy ⟶ Ex ≫ EiSy) (eε : ESy ⟶ EiSy)
    (h1 : eεy ≫ mcx_Sy' = mcx_Sy ≫ Ex ◁ eε)
    (ιSy : EiSy ⟶ FSy) (φy : FSy ⟶ T₁₂.obj Fy) (ιy : Ey ≅ Fy)
    (h2 : ψy = eε ≫ ιSy ≫ φy ≫ T₁₂.map ιy.inv)
    (ιx : Ex ≅ Fx) (eMc : EixSy ⟶ EixSy') (ιxSy : EixSy' ⟶ FxSy) (FmcxSy : FxSy ⟶ Fx ≫ FSy)
    (h3 : mcx_Sy' ≫ ιx.hom ▷ EiSy ≫ Fx ◁ ιSy = eMc ≫ ιxSy ≫ FmcxSy)
    (τF : Fx ≫ T₁₂.obj Fy ≅ T₀₂.obj (Fx ≫ Fy)) (FL : FxSy ⟶ FSxyS) (φxy : FSxyS ⟶ T₀₂.obj Fxy)
    (Fmcxy : Fxy ⟶ Fx ≫ Fy)
    (h4 : FmcxSy ≫ Fx ◁ φy ≫ τF.hom = FL ≫ φxy ≫ T₀₂.map Fmcxy)
    (τEF : Ex ≫ T₁₂.obj Fy ≅ T₀₂.obj (Ex ≫ Fy))
    (h5a : ιx.inv ▷ T₁₂.obj Fy ≫ τEF.hom = τF.hom ≫ T₀₂.map (ιx.inv ▷ Fy))
    (h5b : Ex ◁ T₁₂.map ιy.inv ≫ τE.hom = τEF.hom ≫ T₀₂.map (Ex ◁ ιy.inv))
    (ιxy : Eixy ≅ Fxy) (eMcxy : Eixy ≅ Exy)
    (h6 : mcx_y ≫ ιx.hom ▷ Ey ≫ Fx ◁ ιy.hom = eMcxy.inv ≫ ιxy.hom ≫ Fmcxy)
    (eiL : EixSy' ⟶ EiSxyS) (ιS_xy : EiSxyS ⟶ FSxyS) (h7 : eiL ≫ ιS_xy = ιxSy ≫ FL)
    (eSw : ESixy' ≅ ESixy) (ψixy : ESixy' ⟶ T₀₂.obj Eixy)
    (h8 : eSw.hom ≫ ψxy = ψixy ≫ T₀₂.map eMcxy.hom)
    (eεxy : ESixy' ⟶ EiSxyS) (h9 : ψixy = eεxy ≫ ιS_xy ≫ φxy ≫ T₀₂.map ιxy.inv)
    (h10 : eεy ≫ eMc ≫ eiL = eLt ≫ eSw.inv ≫ eεxy) :
    mcx_Sy ≫ Ex ◁ ψy ≫ τE.hom = eLt ≫ ψxy ≫ T₀₂.map mcx_y := by
  have hm : mcx_y = eMcxy.inv ≫ ιxy.hom ≫ Fmcxy ≫ ιx.inv ▷ Fy ≫ Ex ◁ ιy.inv := by
    calc mcx_y = mcx_y ≫ (ιx.hom ▷ Ey ≫ Fx ◁ ιy.hom) ≫ (ιx.inv ▷ Fy ≫ Ex ◁ ιy.inv) := by
          simp only [Category.assoc]
          rw [whisker_exchange_assoc, hom_inv_whiskerRight_assoc, whiskerLeft_hom_inv,
            Category.comp_id]
      _ = _ := by simp only [Category.assoc]; rw [reassoc_of% h6]
  have h6' : Fmcxy ≫ ιx.inv ▷ Fy ≫ Ex ◁ ιy.inv = ιxy.inv ≫ eMcxy.hom ≫ mcx_y := by
    rw [hm]; simp
  have h8' : ψxy = eSw.inv ≫ ψixy ≫ T₀₂.map eMcxy.hom := by
    rw [← h8, Iso.inv_hom_id_assoc]
  rw [h2, h8', h9]
  simp only [Bicategory.whiskerLeft_comp, Category.assoc]
  rw [← reassoc_of% h1]
  rw [show ∀ {Z} (h : _ ⟶ Z), Ex ◁ ιSy ≫ Ex ◁ φy ≫ h =
      ιx.hom ▷ EiSy ≫ Fx ◁ ιSy ≫ ιx.inv ▷ FSy ≫ Ex ◁ φy ≫ h from fun h => by
    rw [← whisker_exchange_assoc, hom_inv_whiskerRight_assoc]]
  rw [reassoc_of% h3, ← whisker_exchange_assoc, h5b, reassoc_of% h5a, reassoc_of% h4,
    ← reassoc_of% h7, reassoc_of% h10, ← Functor.map_comp, ← Functor.map_comp, h6',
    Functor.map_comp, Functor.map_comp]

end DotExt

namespace DotExt

variable {A : Type u} [Bicategory.{w, v} A] [∀ a b : A, Preadditive (a ⟶ b)]
  [PreadditiveBicategory A] {B : Type*} [Bicategory B]
  [∀ a b : B, Preadditive (a ⟶ b)] [PreadditiveBicategory B]
  [∀ a b : B, HasFiniteBiproducts (a ⟶ b)] [∀ a b : B, IsIdempotentComplete (a ⟶ b)]
  (F : Pseudofunctor A B) (hF : AddHyp F) {L : RightShift A} {M : RightShift B}
  (C : RightShiftCompat F L M)

/-- The extension of `C.φ` to the additive Karoubi envelope. -/
def extShiftIsoR (a b : Kar A) :
    L.kar.S a b ⋙ (ext F hF).mapFunctor a b ≅
      (ext F hF).mapFunctor a b ⋙ M.S ((ext F hF).obj a) ((ext F hF).obj b) :=
  extNatIso F hF a b (L.S a.obj.obj b.obj.obj) (M.S _ _) (C.φ a.obj.obj b.obj.obj)

theorem extShiftIsoR_hom_app_incl {a b : A} (x : a ⟶ b) :
    (extShiftIsoR F hF C ((incl A).obj a) ((incl A).obj b)).hom.app ((incl A).map x) =
      (ext F hF).map₂ ((KarMatExt.inclShift (L.S a b)).hom.app x) ≫
        (inclIso F hF ((L.S a b).obj x)).hom ≫ (C.φ a b).hom.app x ≫
          (M.S _ _).map (inclIso F hF x).inv := by
  have : (mapKaroubi (L.S a b).mapMat_).Additive := by
    have := mapMat_additive (L.S a b)
    exact mapKaroubi_additive _
  have := mapFunctor_additive F hF ((incl A).obj a) ((incl A).obj b)
  have h1 : (L.kar.S ((incl A).obj a) ((incl A).obj b)).Additive := L.kar.additive _ _
  have i1 : (L.kar.S ((incl A).obj a) ((incl A).obj b) ⋙
    (ext F hF).mapFunctor ((incl A).obj a) ((incl A).obj b)).Additive := inferInstance
  have i2 : ((ext F hF).mapFunctor ((incl A).obj a) ((incl A).obj b) ⋙
    M.S ((ext F hF).obj ((incl A).obj a)) ((ext F hF).obj ((incl A).obj b))).Additive :=
    inferInstance
  exact @KarMatExt.ext_hom_app_incl _ _ _ _ _ _ _ _ _ i1 i2 _ x

attribute [local instance] MatBicat.uniqueSingleι MatBicat.uniqueCompι MatBicat.uniqueIdι

/-- At the inclusions of 1-morphisms of `A`, the isomorphism `P ≫ S(Q) ≅ S(P ≫ Q)` of `Kar A` is
that of `A`. -/
theorem karIsoR_incl {a b c : A} (x : a ⟶ b) (y : b ⟶ c) :
    ((incl A).map x ◁ (show (L.kar.S _ _).obj ((incl A).map y) ⟶ (incl A).map ((L.S b c).obj y)
        from (KarMatExt.inclShift (L.S b c)).hom.app y)) ≫
      ((incl A).mapComp x ((L.S b c).obj y)).inv ≫ (incl A).map₂ (L.iso x y).hom =
    (L.kar.iso ((incl A).map x) ((incl A).map y)).hom ≫
      (L.kar.S _ _).map ((incl A).mapComp x y).inv ≫
        (show (L.kar.S _ _).obj ((incl A).map (x ≫ y)) ⟶ (incl A).map ((L.S a c).obj (x ≫ y))
          from (KarMatExt.inclShift (L.S a c)).hom.app (x ≫ y)) := by
  apply Idempotents.Karoubi.hom_ext
  apply CategoryTheory.Mat_.hom_ext
  intro i j
  show (hcomp₂ (𝟙 _) (𝟙 _ ≫ 𝟙 _) ≫ ((𝟙 _ ≫ 𝟙 _) ≫ MatBicat.singleCompInv x ((L.S b c).obj y)) ≫
      MatBicat.mat1 (L.iso x y).hom) i j =
    (((L.diag _ _).hom ≫ (L.S a c).mapMat_.map (hcomp₂ (𝟙 _) (𝟙 _))) ≫
      (L.S a c).mapMat_.map ((𝟙 _ ≫ 𝟙 _) ≫ MatBicat.singleCompInv x y) ≫ (𝟙 _ ≫ 𝟙 _)) i j
  simp only [Category.id_comp, Category.comp_id, hcomp₂_id_id, CategoryTheory.Functor.map_id]
  erw [MatBicat.comp_apply_unique, DiagMat.diagMat_comp_apply]
  show 𝟙 _ ≫ (L.iso x y).hom = (L.iso x y).hom ≫ (L.S a c).map (𝟙 _)
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

/-- The composite `ext(X ≫ S Y) → ext X ext(S Y) → ext X T(ext Y) → T(ext X ext Y)`. -/
abbrev lhsR {a b c : Kar A} (X : a ⟶ b) (Y : b ⟶ c) :
    (ext F hF).map (X ≫ (L.kar.S b c).obj Y) ⟶
      (M.S ((ext F hF).obj a) ((ext F hF).obj c)).obj ((ext F hF).map X ≫ (ext F hF).map Y) :=
  ((ext F hF).mapComp X ((L.kar.S b c).obj Y)).hom ≫
    (ext F hF).map X ◁ (extShiftIsoR F hF C b c).hom.app Y ≫
      (M.iso ((ext F hF).map X) ((ext F hF).map Y)).hom

/-- The composite `ext(X ≫ S Y) → ext(S(X ≫ Y)) → T(ext(X ≫ Y)) → T(ext X ext Y)`. -/
abbrev rhsR {a b c : Kar A} (X : a ⟶ b) (Y : b ⟶ c) :
    (ext F hF).map (X ≫ (L.kar.S b c).obj Y) ⟶
      (M.S ((ext F hF).obj a) ((ext F hF).obj c)).obj ((ext F hF).map X ≫ (ext F hF).map Y) :=
  (ext F hF).map₂ (L.kar.iso X Y).hom ≫ (extShiftIsoR F hF C a c).hom.app (X ≫ Y) ≫
    (M.S _ _).map ((ext F hF).mapComp X Y).hom

theorem lhsR_eq_rhsR_incl {a b c : A} (x : a ⟶ b) (y : b ⟶ c) :
    lhsR F hF C ((incl A).map x) ((incl A).map y) =
      rhsR F hF C ((incl A).map x) ((incl A).map y) := by
  have h1 := mapComp_naturality_right' (ext F hF) ((incl A).map x)
      (show (L.kar.S ((incl A).obj b) ((incl A).obj c)).obj ((incl A).map y) ⟶
        (incl A).map ((L.S b c).obj y) from (KarMatExt.inclShift (L.S b c)).hom.app y)
  have h2 := extShiftIsoR_hom_app_incl F hF C y
  have h3 := inclIso_mapComp F hF x ((L.S b c).obj y)
  have h4 := C.coh x y
  have h5a := M.iso_naturality_left (inclIso F hF x).inv (F.map y)
  have h5b := M.iso_naturality_right ((ext F hF).map ((incl A).map x)) (inclIso F hF y).inv
  have h6 := inclIso_mapComp F hF x y
  have h7 := inclIso_naturality F hF (L.iso x y).hom
  have h8 := (extShiftIsoR F hF C ((incl A).obj a) ((incl A).obj c)).hom.naturality
    ((incl A).mapComp x y).hom
  have h9 := extShiftIsoR_hom_app_incl F hF C (x ≫ y)
  have h10 := map₂_comp₃_eq (ext F hF) (karIsoR_incl (L := L) x y)
  exact shift_incl_auxR _ _ _ _ _ _ _ _ _ _ _ h1 _ _ (inclIso F hF y) h2 (inclIso F hF x) _ _ _ h3
    _ _ _ _ h4 _ h5a h5b (inclIso F hF (x ≫ y)) ((ext F hF).map₂Iso ((incl A).mapComp x y)) h6 _ _
    h7 ((ext F hF).map₂Iso ((L.kar.S _ _).mapIso ((incl A).mapComp x y))) _ h8 _ h9 h10

theorem lhsR_nat_aux_left {P₀ P₁ P₂ : B} (T₁₂ : (P₁ ⟶ P₂) ⥤ (P₁ ⟶ P₂))
    (T₀₂ : (P₀ ⟶ P₂) ⥤ (P₀ ⟶ P₂)) {E₁ E₁' : P₀ ⟶ P₂} {Ex Ex' : P₀ ⟶ P₁} {E₂ Ey : P₁ ⟶ P₂}
    (m : E₁ ⟶ Ex ≫ E₂) (m' : E₁' ⟶ Ex' ≫ E₂) (a₁ : E₁ ⟶ E₁') (bu : Ex ⟶ Ex')
    (ψ : E₂ ⟶ T₁₂.obj Ey) (τ : Ex ≫ T₁₂.obj Ey ⟶ T₀₂.obj (Ex ≫ Ey))
    (τ' : Ex' ≫ T₁₂.obj Ey ⟶ T₀₂.obj (Ex' ≫ Ey)) (h₁ : a₁ ≫ m' = m ≫ bu ▷ E₂)
    (h₃ : bu ▷ T₁₂.obj Ey ≫ τ' = τ ≫ T₀₂.map (bu ▷ Ey)) :
    a₁ ≫ m' ≫ Ex' ◁ ψ ≫ τ' = (m ≫ Ex ◁ ψ ≫ τ) ≫ T₀₂.map (bu ▷ Ey) := by
  rw [reassoc_of% h₁, ← whisker_exchange_assoc, h₃]
  simp only [Category.assoc]

theorem lhsR_nat_aux_right {P₀ P₁ P₂ : B} (T₁₂ : (P₁ ⟶ P₂) ⥤ (P₁ ⟶ P₂))
    (T₀₂ : (P₀ ⟶ P₂) ⥤ (P₀ ⟶ P₂)) {E₁ E₁' : P₀ ⟶ P₂} {Ex : P₀ ⟶ P₁} {E₂ E₂' Ey Ey' : P₁ ⟶ P₂}
    (m : E₁ ⟶ Ex ≫ E₂) (m' : E₁' ⟶ Ex ≫ E₂') (a₁ : E₁ ⟶ E₁') (a₂ : E₂ ⟶ E₂')
    (ψ : E₂ ⟶ T₁₂.obj Ey) (ψ' : E₂' ⟶ T₁₂.obj Ey') (b : Ey ⟶ Ey')
    (τ : Ex ≫ T₁₂.obj Ey ⟶ T₀₂.obj (Ex ≫ Ey)) (τ' : Ex ≫ T₁₂.obj Ey' ⟶ T₀₂.obj (Ex ≫ Ey'))
    (h₁ : a₁ ≫ m' = m ≫ Ex ◁ a₂) (h₂ : a₂ ≫ ψ' = ψ ≫ T₁₂.map b)
    (h₃ : Ex ◁ T₁₂.map b ≫ τ' = τ ≫ T₀₂.map (Ex ◁ b)) :
    a₁ ≫ m' ≫ Ex ◁ ψ' ≫ τ' = (m ≫ Ex ◁ ψ ≫ τ) ≫ T₀₂.map (Ex ◁ b) := by
  rw [reassoc_of% h₁, ← Bicategory.whiskerLeft_comp_assoc, h₂, Bicategory.whiskerLeft_comp_assoc,
    h₃]
  simp only [Category.assoc]

/-- `lhsR`, as a natural transformation in the first variable. -/
def lhsRNatLeft {a b c : Kar A} (Y : b ⟶ c) :
    postcomp a ((L.kar.S b c).obj Y) ⋙ (ext F hF).mapFunctor a c ⟶
      (ext F hF).mapFunctor a b ⋙ postcomp ((ext F hF).obj a) ((ext F hF).map Y) ⋙
        M.S ((ext F hF).obj a) ((ext F hF).obj c) where
  app X := lhsR F hF C X Y
  naturality {_ _} u :=
    lhsR_nat_aux_left _ _ _ _ _ _ _ _ _ (mapComp_naturality_left' (ext F hF) u _)
      (M.iso_naturality_left _ _)

/-- `rhsR`, as a natural transformation in the first variable. -/
def rhsRNatLeft {a b c : Kar A} (Y : b ⟶ c) :
    postcomp a ((L.kar.S b c).obj Y) ⋙ (ext F hF).mapFunctor a c ⟶
      (ext F hF).mapFunctor a b ⋙ postcomp ((ext F hF).obj a) ((ext F hF).map Y) ⋙
        M.S ((ext F hF).obj a) ((ext F hF).obj c) where
  app X := rhsR F hF C X Y
  naturality {_ _} u :=
    rhs_nat_aux _ _ _ _ _ _ _ _ _ _ _
      (map₂_comp₂_eq (ext F hF) (L.kar.iso_naturality_left u Y))
      ((extShiftIsoR F hF C a c).hom.naturality (u ▷ Y)) (mapComp_naturality_left' (ext F hF) u Y)

/-- `lhsR`, as a natural transformation in the second variable. -/
def lhsRNatRight {a b c : Kar A} (X : a ⟶ b) :
    L.kar.S b c ⋙ precomp c X ⋙ (ext F hF).mapFunctor a c ⟶
      (ext F hF).mapFunctor b c ⋙ precomp ((ext F hF).obj c) ((ext F hF).map X) ⋙
        M.S ((ext F hF).obj a) ((ext F hF).obj c) where
  app Y := lhsR F hF C X Y
  naturality {_ _} v :=
    lhsR_nat_aux_right _ _ _ _ _ _ _ _ _ _ _ (mapComp_naturality_right' (ext F hF) X _)
      ((extShiftIsoR F hF C b c).hom.naturality v) (M.iso_naturality_right _ _)

/-- `rhsR`, as a natural transformation in the second variable. -/
def rhsRNatRight {a b c : Kar A} (X : a ⟶ b) :
    L.kar.S b c ⋙ precomp c X ⋙ (ext F hF).mapFunctor a c ⟶
      (ext F hF).mapFunctor b c ⋙ precomp ((ext F hF).obj c) ((ext F hF).map X) ⋙
        M.S ((ext F hF).obj a) ((ext F hF).obj c) where
  app Y := rhsR F hF C X Y
  naturality {_ _} v :=
    rhs_nat_aux _ _ _ _ _ _ _ _ _ _ _
      (map₂_comp₂_eq (ext F hF) (L.kar.iso_naturality_right X v))
      ((extShiftIsoR F hF C a c).hom.naturality (X ◁ v)) (mapComp_naturality_right' (ext F hF) X v)

theorem lhsR_eq_rhsR_inclRight {a b c : A} (x : a ⟶ b) (Y : (incl A).obj b ⟶ (incl A).obj c) :
    lhsR F hF C ((incl A).map x) Y = rhsR F hF C ((incl A).map x) Y := by
  have i₁ : (L.kar.S ((incl A).obj b) ((incl A).obj c) ⋙ precomp ((incl A).obj c) ((incl A).map x) ⋙
      (ext F hF).mapFunctor ((incl A).obj a) ((incl A).obj c)).Additive := inferInstance
  have h := @KarMatExt.natTrans_ext _ _ _ _ _ _ _ _ i₁ (lhsRNatRight F hF C ((incl A).map x))
    (rhsRNatRight F hF C ((incl A).map x)) (fun y => lhsR_eq_rhsR_incl F hF C x y)
  exact congr_app h Y

theorem lhsR_eq_rhsR_inclObj {a b c : A} (X : (incl A).obj a ⟶ (incl A).obj b)
    (Y : (incl A).obj b ⟶ (incl A).obj c) : lhsR F hF C X Y = rhsR F hF C X Y := by
  have i₁ : (postcomp ((incl A).obj a) ((L.kar.S ((incl A).obj b) ((incl A).obj c)).obj Y) ⋙
      (ext F hF).mapFunctor ((incl A).obj a) ((incl A).obj c)).Additive := inferInstance
  have h := @KarMatExt.natTrans_ext _ _ _ _ _ _ _ _ i₁ (lhsRNatLeft F hF C Y)
    (rhsRNatLeft F hF C Y) (fun x => lhsR_eq_rhsR_inclRight F hF C x Y)
  exact congr_app h X

/-- **The extension of a pseudofunctor commuting with right shift structures commutes with the
induced shift structures**, compatibly with the composition constraints, on the whole additive
Karoubi envelope. -/
theorem lhsR_eq_rhsR {a b c : Kar A} (X : a ⟶ b) (Y : b ⟶ c) :
    lhsR F hF C X Y = rhsR F hF C X Y := by
  obtain ⟨⟨a⟩⟩ := a
  obtain ⟨⟨b⟩⟩ := b
  obtain ⟨⟨c⟩⟩ := c
  exact lhsR_eq_rhsR_inclObj F hF C X Y

/-- **The extension of a pseudofunctor commuting with right shift structures commutes with the
induced right shift structure of the additive Karoubi envelope.** -/
def _root_.Categorification.TwoRep.RightShiftCompat.ext :
    RightShiftCompat (ext F hF) L.kar M where
  φ := extShiftIsoR F hF C
  coh X Y := lhsR_eq_rhsR F hF C X Y

end DotExt

namespace RightShiftCompat

variable {A : Type u} [Bicategory.{w, v} A] [∀ a b : A, Preadditive (a ⟶ b)] {B : Type*}
  [Bicategory B] [∀ a b : B, Preadditive (a ⟶ b)] {G : Pseudofunctor A B} {L : RightShift A}
  {M : RightShift B} (C : RightShiftCompat G L M)

/-- The component `G(S g) ⟶ T(G g)` of `C.φ`. -/
def app {a b : A} (g : a ⟶ b) : G.map ((L.S a b).obj g) ⟶ (M.S _ _).obj (G.map g) :=
  (C.φ a b).hom.app g

theorem app_naturality {a b : A} {f g : a ⟶ b} (η : f ⟶ g) :
    G.map₂ ((L.S a b).map η) ≫ C.app g = C.app f ≫ (M.S _ _).map (G.map₂ η) :=
  (C.φ a b).hom.naturality η

theorem coh' {a b c : A} (f : a ⟶ b) (g : b ⟶ c) :
    (G.mapComp f ((L.S b c).obj g)).hom ≫ G.map f ◁ C.app g ≫ (M.iso (G.map f) (G.map g)).hom =
      G.map₂ (L.iso f g).hom ≫ C.app (f ≫ g) ≫ (M.S _ _).map (G.mapComp f g).hom :=
  C.coh f g

/-- **Compatibility with the identity constraints** (see `LeftShiftCompat.mapId`). -/
theorem mapId {a b : A} (f : a ⟶ b) :
    (G.mapComp f ((L.S b b).obj (𝟙 b))).hom ≫ G.map f ◁ C.app (𝟙 b) ≫
        G.map f ◁ (M.S _ _).map (G.mapId b).hom ≫ (M.iso (G.map f) (𝟙 _)).hom ≫
          (M.S _ _).map (ρ_ (G.map f)).hom =
      G.map₂ ((L.iso f (𝟙 b)).hom ≫ (L.S a b).map (ρ_ f).hom) ≫ C.app f := by
  rw [reassoc_of% M.iso_naturality_right, reassoc_of% C.coh', ← Functor.map_comp,
    ← Functor.map_comp, ← G.map₂_right_unitor, ← C.app_naturality, PrelaxFunctor.map₂_comp,
    Category.assoc]

end RightShiftCompat

end TwoRep

end Categorification

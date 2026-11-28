/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721TraceCyclic
import Categorification.WeightedKLR.Rigidity.CupCapProp721ResIndTrace
import Categorification.Diagrams.KLR.MatEndModuleDot
import Categorification.Diagrams.KLR.MatEndNatEmb

/-!
# Symmetry of the trace of `Res ⊣ Ind` along a matrix map against a cyclic 2-morphism

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, Theorem 4.31,
as used in §7.3, proof of Proposition 7.21. The adjunction `Res_φ ⊣ Ind_φ` along the matrix map
of a functor `F` (`KLR.Diagram.MatEnd.resIndAdjunction`) is built from `F' ⊣ E` and `E ⊣ F'` on
completed additive envelopes, and its trace closes a diagram on the right: `z ↦ η ≫ E z ≫ ε'`
(`KLR.Diagram.MatEnd.resIndAdjunction_counit_app_mk_tmul`). This is Webster's description of the
action of the 2-morphisms after Theorem 4.31 (attachment at the right, the closing loop drawn as
a double Stendhal diagram).

If a natural endomorphism `θ` of `F` is cyclic, that is its conjugate along `F' ⊣ E` is also its
conjugate along `E ⊣ F'` (`TwoRep.IsCyclic` in functor form), then the trace is symmetric
against the diagonal matrix `natEmb θ`: `τ (c z) = τ (z c)`
(`KLR.Diagram.MatEnd.resIndTrace_cyclic`). The proof slides `θ` around the closing loop:
through the unit by the conjugate along `F' ⊣ E`, past the diagram by naturality, and through
the counit by the conjugate along `E ⊣ F'` (`CupCap.unit_map_counit_comm_of_cyclic`).

## Main results

* `CupCap.unit_map_counit_comm_of_cyclic`: the closing trace of a cyclic `θ` is symmetric, at
  each object.
* `KLR.Diagram.MatEnd.resIndTrace_cyclic`: the trace of the matrix adjunction is symmetric
  against `natEmb θ` for cyclic `θ`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CategoryTheory.Idempotents MulOpposite Categorification.InductionAlong

namespace Categorification.Stendhal.CupCap

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] {L : C ⥤ D}
  {R : D ⥤ C} (adj : L ⊣ R) (adj' : R ⊣ L)

/-- **The closing trace is symmetric against a cyclic 2-morphism**, at an object: if the
conjugate of `θ : L ⟶ L` along `L ⊣ R` is also its conjugate along `R ⊣ L`, then for every
`w : L X ⟶ L X`, closing `θ ≫ w` and `w ≫ θ` on the right (the unit of `L ⊣ R`, then `R`, then
the counit of `R ⊣ L`) gives the same endomorphism of `X` (cf. `TwoRep.closeTrace_comp_comm`). -/
theorem unit_map_counit_comm_of_cyclic (θ : L ⟶ L)
    (hθ : conjugateEquiv adj' adj' (conjugateEquiv adj adj θ) = θ) (X : C)
    (w : L.obj X ⟶ L.obj X) :
    adj.unit.app X ≫ R.map (θ.app X ≫ w) ≫ adj'.counit.app X =
      adj.unit.app X ≫ R.map (w ≫ θ.app X) ≫ adj'.counit.app X := by
  have hu := unit_conjugateEquiv adj adj θ X
  have hc := conjugateEquiv_counit adj' adj' (conjugateEquiv adj adj θ) X
  rw [hθ] at hc
  have hn := (conjugateEquiv adj adj θ).naturality w
  rw [R.map_comp, R.map_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% hu, ← reassoc_of% hn, hc]

end Categorification.Stendhal.CupCap

namespace Categorification.KLR.Diagram.MatEnd

open Categorification.Stendhal.CupCap

variable {C : Type} [Category.{0} C] [Preadditive C] {D : Type} [Category.{0} D]
  [Preadditive D] {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {X : ι → C} {Y : κ → D} (F : C ⥤ D) [F.Additive] {e : ι → κ}
  (he : Function.Injective e) (h : ∀ i, F.obj (X i) = Y (e i))
  {E : Karoubi (Mat_ D) ⥤ Karoubi (Mat_ C)} [E.Additive] (adj : mapKaroubi F.mapMat_ ⊣ E)
  (adj' : E ⊣ mapKaroubi F.mapMat_)
  {J : Type} [Fintype J]
  (π : J → (E.obj ((toKaroubi _).obj (familySum Y)) ⟶ (toKaroubi _).obj (familySum X)))
  (ι' : J → ((toKaroubi _).obj (familySum X) ⟶ E.obj ((toKaroubi _).obj (familySum Y))))
  (hπ : ∑ j, π j ≫ ι' j = 𝟙 _)

attribute [local instance] HomTensor.bimodule

/-- The closing morphism of the trace of `resIndAdjunction` at a corner element. -/
abbrev resIndClose (z : Corner (mapEmbOp F he h)) :
    (toKaroubi _).obj (familySum X) ⟶ (toKaroubi _).obj (familySum X) :=
  resRegularHom F he h adj (resUnit _) ≫ E.map (karoubiCorner F he h z) ≫
    adj'.counit.app ((toKaroubi _).obj (familySum X))

/-- The trace of `resIndAdjunction` at `z` is the closing morphism `resIndClose z`, acting on the
unit of the regular module. -/
theorem resIndTrace_eq (z : Corner (mapEmbOp F he h)) (hz : mapEmbOp F he h 1 * z.1 = z.1) :
    letI := HomTensor.transferModule (karoubiMatrixOp X) (MatEnd X)ᵐᵒᵖ
    resIndTrace (resIndAdjunction F he h adj adj' π ι' hπ) z hz =
      (op (resIndClose F he h adj adj' z) : (End ((toKaroubi _).obj (familySum X)))ᵐᵒᵖ) •
        (1 : (MatEnd X)ᵐᵒᵖ) :=
  resIndAdjunction_counit_app_mk_tmul F he h adj adj' π ι' hπ
    (ModuleCat.of _ (MatEnd X)ᵐᵒᵖ) z 1 _

omit [E.Additive] in
/-- On a corner element fixed by `φ(1)`, the generator `β = (F' ⊣ E)(sect)` of the trace may be
replaced by the unit of `F' ⊣ E` followed by the section. -/
theorem resIndClose_eq_unit (z : Corner (mapEmbOp F he h)) (hz : mapEmbOp F he h 1 * z.1 = z.1) :
    resIndClose F he h adj adj' z =
      adj.unit.app _ ≫ E.map (karoubiSect F h ≫ karoubiCorner F he h z) ≫
        adj'.counit.app ((toKaroubi _).obj (familySum X)) := by
  have hfix : (karoubiMatrixOpY Y (mapEmbOp F he h 1)).unop ≫ karoubiCorner F he h z =
      karoubiCorner F he h z := by
    rw [← karoubiCorner_smul]
    exact congrArg _ (Subtype.ext hz)
  simp only [resIndClose, resRegularHom_apply, resUnit, Res.val_mk, Adjunction.homEquiv_unit,
    Category.assoc]
  rw [← E.map_comp_assoc, Category.assoc, hfix]

variable (θ : F ⟶ F)

/-- The diagonal matrix of `θ`, as an element of the opposite matrix ring, commutes with the image
of the matrix map. -/
theorem natEmb_commute (a : (MatEnd X)ᵐᵒᵖ) :
    op (natEmb F h θ) * mapEmbOp F he h a = mapEmbOp F he h a * op (natEmb F h θ) :=
  (intertwines_natEmb F he h θ a).symm

/-- `sect ≫ natEmb θ ≫ Z = θ̂ ≫ sect ≫ Z` for a corner morphism `Z` fixed by `φ(1)`. -/
theorem karoubiSect_natEmb_corner (z : Corner (mapEmbOp F he h))
    (hz : mapEmbOp F he h 1 * z.1 = z.1) :
    karoubiSect F h ≫ karoubiCorner F he h (op (natEmb F h θ) • z) =
      (completionMap₂ θ).app ((toKaroubi _).obj (familySum X)) ≫ karoubiSect F h ≫
        karoubiCorner F he h z := by
  have hfix : (karoubiMatrixOpY Y (mapEmbOp F he h 1)).unop ≫ karoubiCorner F he h z =
      karoubiCorner F he h z := by
    rw [← karoubiCorner_smul]
    exact congrArg _ (Subtype.ext hz)
  have hgen : op (natEmb F h θ) • unitGen (mapEmbOp F he h) =
      cornerMul (intertwines_natEmb F he h θ) (unitGen (mapEmbOp F he h)) :=
    Subtype.ext (natEmb_commute F he h θ 1)
  have hc : (karoubiMatrixOpY Y (op (natEmb F h θ))).unop ≫ karoubiGen F he h =
      karoubiGen F he h ≫ (completionMap₂ θ).app ((toKaroubi _).obj (familySum X)) := by
    rw [← karoubiCorner_smul, hgen, karoubiCorner_cornerMul_natEmb]
  rw [karoubiCorner_smul, ← hfix, ← karoubiGen_sect F he h, Category.assoc,
    reassoc_of% hc, ← Category.assoc (karoubiSect F h), karoubiSect_gen, Category.id_comp,
    ← Category.assoc (karoubiSect F h) (karoubiGen F he h), karoubiSect_gen, Category.id_comp]

/-- **The trace of `Res ⊣ Ind` along a matrix map is symmetric against a cyclic 2-morphism**
(Webster, arXiv:1309.3796v3, Theorem 4.31, with the action of the 2-morphisms by attachment at
the right): if `θ : F ⟶ F` is cyclic for the completed adjunctions `F' ⊣ E` and `E ⊣ F'`, then
`τ (natEmb θ · z) = τ (z · natEmb θ)` for every corner element `z` fixed by `φ(1)`. -/
theorem resIndTrace_cyclic
    (hθ : conjugateEquiv adj' adj' (conjugateEquiv adj adj (completionMap₂ θ)) =
      completionMap₂ θ)
    (z : Corner (mapEmbOp F he h)) (hz : mapEmbOp F he h 1 * z.1 = z.1) :
    resIndTrace (resIndAdjunction F he h adj adj' π ι' hπ) (op (natEmb F h θ) • z)
        (smul_corner_fixed (natEmb_commute F he h θ) z hz) =
      resIndTrace (resIndAdjunction F he h adj adj' π ι' hπ)
        (cornerMul (intertwines_of_commute (natEmb_commute F he h θ)) z)
        (cornerMul_fixed (intertwines_of_commute (natEmb_commute F he h θ)) z hz) := by
  rw [resIndTrace_eq, resIndTrace_eq]
  congr 2
  rw [resIndClose_eq_unit F he h adj adj' _ (smul_corner_fixed (natEmb_commute F he h θ) z hz),
    resIndClose_eq_unit F he h adj adj' _
      (cornerMul_fixed (intertwines_of_commute (natEmb_commute F he h θ)) z hz),
    karoubiSect_natEmb_corner F he h θ z hz,
    karoubiCorner_cornerMul F he h (intertwines_of_commute (natEmb_commute F he h θ))
      (karoubiCorner_cornerMul_natEmb F he h θ) z, ← Category.assoc (karoubiSect F h)]
  exact unit_map_counit_comm_of_cyclic adj adj' (completionMap₂ θ) hθ _ _

end Categorification.KLR.Diagram.MatEnd

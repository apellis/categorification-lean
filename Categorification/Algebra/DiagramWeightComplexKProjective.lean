/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DiagramWeightComplex
import DG.Category.Tensor.GradedFiltration
import DG.Category.SubQuotient
import Mathlib.Algebra.Homology.Single
import DG.Category.Resolution.SemiFree

/-!
# K-projective weight complexes

The realization of a bounded-above weight complex is K-projective if its
individual terms, placed in their cohomological degrees, are K-projective.
This is the dg step for the standard resolutions in Webster,
arXiv:1309.3796v2, Lemma 6.11.
-/

noncomputable section

namespace Categorification

open CategoryTheory DG DirectSum
open scoped DG.DegreeZero CatModule

universe u v
variable {R : Type u} [Ring R] [InternalGrading R] [BigradedDGRing R]
  {S : Type v} [Ring S]

private theorem complexComponent_map {K L : CochainComplex (ModuleCat.{v} S) ℤ}
    (f : K ⟶ L) (j : ℤ) (x : ComplexSum K) :
    ComplexSum.component L j (ComplexSum.map f x) = f.f j (ComplexSum.component K j x) := by
  induction x using ComplexSum.induction_on with
  | zero => simp
  | of i x =>
    by_cases hij : i = j
    · subst j
      rw [ComplexSum.map_of, ComplexSum.component_of_same, ComplexSum.component_of_same]
    · rw [ComplexSum.map_of, ComplexSum.component_of_ne hij, ComplexSum.component_of_ne hij, map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem complexComponent_d {K : CochainComplex (ModuleCat.{v} S) ℤ}
    (j : ℤ) (x : ComplexSum K) :
    ComplexSum.component K j (d x) = K.d (j - 1) j (ComplexSum.component K (j - 1) x) := by
  induction x using ComplexSum.induction_on with
  | zero => simp
  | of i x =>
    by_cases hij : i + 1 = j
    · subst j
      rw [ComplexSum.d_of, add_sub_cancel_right, ComplexSum.component_of_same, ComplexSum.component_of_same]
    · rw [ComplexSum.d_of, ComplexSum.component_of_ne hij,
        ComplexSum.component_of_ne (show i ≠ j - 1 by omega), map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem complexDecompose_eq {K : CochainComplex (ModuleCat.{v} S) ℤ}
    (j : ℤ) (x : ComplexSum K) :
    (DirectSum.decompose (DG.grading (M := ComplexSum K)) x j).val =
      ComplexSum.of K j (ComplexSum.component K j x) := by
  induction x using ComplexSum.induction_on with
  | zero => simp
  | of i x =>
    by_cases hij : i = j
    · subst j
      rw [DirectSum.decompose_of_mem_same _ (ComplexSum.of_mem_grading _ _), ComplexSum.component_of_same]
    · rw [DirectSum.decompose_of_mem_ne _ (ComplexSum.of_mem_grading _ _) hij,
        ComplexSum.component_of_ne hij, map_zero]
  | add x y hx hy =>
    rw [DirectSum.decompose_add, DirectSum.add_apply]
    exact (congrArg₂ (· + ·) hx hy).trans (by rw [map_add, map_add])

variable (F : WeightComplexDiagram R S) [F.Additive]

/-- The dg submodule of the realization supported in cohomological degrees at least b. -/
def diagramWeightComplexTruncation (b : ℤ) : CatSubmodule (diagramWeightModuleOfComplex F) where
  carrier X := {
    carrier := {x | ∀ j < b, ComplexSum.component (F.obj X) j x = 0}
    zero_mem' := fun _ _ => map_zero _
    add_mem' := fun hx hy j hj => by erw [map_add, hx j hj, hy j hj, add_zero]
    neg_mem' := fun hx j hj => by erw [map_neg, hx j hj, neg_zero] }
  decompose_mem' {X x} hx j i hi := by
    change ComplexSum.component (F.obj X) i (DirectSum.decompose
      (DG.grading (M := ComplexSum (F.obj X))) x j).val = 0
    erw [complexDecompose_eq]
    by_cases hji : j = i
    · subst i
      rw [ComplexSum.component_of_same]
      exact hx j hi
    · exact ComplexSum.component_of_ne hji _
  d_mem' {X x} hx j hj := by
    change ComplexSum.component (F.obj X) j (d x) = 0
    erw [complexComponent_d, hx (j - 1) (by omega), map_zero]
  smul_mem' {X Y} f {x} hx j hj := by
    change ComplexSum.component (F.obj Y) j (ComplexSum.map (F.map f) x) = 0
    erw [complexComponent_map, hx j hj, map_zero]

private theorem complexComponent_ext {K : CochainComplex (ModuleCat.{v} S) ℤ}
    {x y : ComplexSum K} (h : ∀ j, ComplexSum.component K j x = ComplexSum.component K j y) :
    x = y := by
  apply (DirectSum.decompose (DG.grading (M := ComplexSum K))).injective
  ext j
  rw [complexDecompose_eq, complexDecompose_eq, h j]

/-- The weight components of a complex in one cohomological degree,
with zero differential. -/
def weightComplexPieceDiagram (b : ℤ) : WeightComplexDiagram R S :=
  F ⋙ HomologicalComplex.eval (ModuleCat S) (ComplexShape.up ℤ) b ⋙
    HomologicalComplex.single (ModuleCat S) (ComplexShape.up ℤ) b

instance (b : ℤ) : (weightComplexPieceDiagram F b).Additive := by
  unfold weightComplexPieceDiagram
  infer_instance

abbrev weightComplexPiece (b : ℤ) := diagramWeightModuleOfComplex (weightComplexPieceDiagram F b)

private abbrev pieceIso (b : ℤ) (X : WeightCategory R) :=
  HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) b ((F.obj X).X b)

private def pieceProjectionAdd (b : ℤ) (X : WeightCategory R) :
    (diagramWeightComplexTruncation F b).toCatModule.obj X →+
      (weightComplexPiece F b).obj X :=
  ((ComplexSum.of ((weightComplexPieceDiagram F b).obj X) b).toAddMonoidHom.comp
    ((pieceIso F b X).inv.hom.toAddMonoidHom.comp
      (ComplexSum.component (F.obj X) b).toAddMonoidHom)).comp
        (AddSubgroupClass.subtype ((diagramWeightComplexTruncation F b).carrier X))

/-- From the truncation below degree b, take the component in degree b.
There is no incoming differential to this component. -/
def diagramWeightComplexTruncationProjection (b : ℤ) :
    (diagramWeightComplexTruncation F b).toCatModule ⟶ weightComplexPiece F b where
  app := pieceProjectionAdd F b
  map_mem' {X n x} hx := by
    let K := F.obj X
    let L := (weightComplexPieceDiagram F b).obj X
    change (x.val : ComplexSum K) ∈ DG.grading n at hx
    change ComplexSum.of L b ((pieceIso F b X).inv (ComplexSum.component K b x.val)) ∈ DG.grading (M := ComplexSum L) n
    by_cases hn : n = b
    · subst n
      exact ComplexSum.of_mem_grading _ _
    · obtain ⟨y, hy⟩ := ComplexSum.mem_grading_iff.mp hx
      have hz : ComplexSum.component K b x.val = 0 :=
        (congrArg (ComplexSum.component K b) hy.symm).trans (ComplexSum.component_of_ne hn y)
      erw [hz, map_zero, map_zero]
      exact zero_mem _
  map_d' {X} x := by
    let K := F.obj X
    let L := (weightComplexPieceDiagram F b).obj X
    change ComplexSum.of L b ((pieceIso F b X).inv (ComplexSum.component K b (d x.val))) =
      d (ComplexSum.of L b ((pieceIso F b X).inv (ComplexSum.component K b x.val)))
    have hz : ComplexSum.component K (b - 1) x.val = 0 := x.property _ (by omega)
    erw [complexComponent_d, hz, map_zero, map_zero, map_zero, ComplexSum.d_of]
    have h : L.d b (b+1) = 0 :=
      HomologicalComplex.single_obj_d (ComplexShape.up ℤ) b ((F.obj X).X b) b (b+1)
    erw [h]
    change 0 = ComplexSum.of L (b+1) 0
    exact (map_zero _).symm
  map_smul' {X Y} a x := by
    let K := F.obj X
    let L := F.obj Y
    let K' := (weightComplexPieceDiagram F b).obj X
    let L' := (weightComplexPieceDiagram F b).obj Y
    change ComplexSum.of L' b ((pieceIso F b Y).inv
      (ComplexSum.component L b (ComplexSum.map (F.map a) x.val))) =
      ComplexSum.map ((weightComplexPieceDiagram F b).map a)
        (ComplexSum.of K' b ((pieceIso F b X).inv (ComplexSum.component K b x.val)))
    erw [complexComponent_map, ComplexSum.map_of]
    apply congrArg (ComplexSum.of L' b)
    change _ = ((HomologicalComplex.single (ModuleCat S) (ComplexShape.up ℤ) b).map
      ((F.map a).f b)).f b ((pieceIso F b X).inv (ComplexSum.component K b x.val))
    rw [HomologicalComplex.single_map_f_self]
    erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]

omit [F.Additive] in
private theorem single_component_zero (b : ℤ) (X : WeightCategory R) {j : ℤ}
    (hj : j ≠ b) (x : ComplexSum ((weightComplexPieceDiagram F b).obj X)) :
    ComplexSum.component _ j x = 0 := by
  have h : CategoryTheory.Limits.IsZero (((weightComplexPieceDiagram F b).obj X).X j) :=
    HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) b ((F.obj X).X b) j hj
  exact (ModuleCat.isZero_iff_subsingleton.mp h).elim _ _

omit [F.Additive] in
private theorem single_reconstruct (b : ℤ) (X : WeightCategory R)
    (x : ComplexSum ((weightComplexPieceDiagram F b).obj X)) :
    ComplexSum.of _ b (ComplexSum.component _ b x) = x := by
  apply complexComponent_ext
  intro j
  by_cases hj : j = b
  · subst j
    exact ComplexSum.component_of_same _ _
  · rw [ComplexSum.component_of_ne (Ne.symm hj), single_component_zero F b X hj x]

/-- The unique nonzero cochain coordinate of a single-degree weight model. -/
def weightComplexPieceAddEquiv (b : ℤ) (X : WeightCategory R) :
    (weightComplexPiece F b).obj X ≃+ (F.obj X).X b :=
  let L := (weightComplexPieceDiagram F b).obj X
  let p := ComplexSum.component L b
  AddEquiv.ofBijective (((pieceIso F b X).hom.hom.toAddMonoidHom).comp p.toAddMonoidHom)
    ((show Function.Bijective (pieceIso F b X).hom from
      ⟨(ModuleCat.mono_iff_injective _).mp inferInstance, (ModuleCat.epi_iff_surjective _).mp inferInstance⟩).comp
      (show Function.Bijective p from
        ⟨fun x y h => (single_reconstruct F b X x).symm.trans
            ((congrArg (ComplexSum.of L b) h).trans (single_reconstruct F b X y)),
          fun y => ⟨ComplexSum.of L b y, ComplexSum.component_of_same _ _⟩⟩))

/-- The unique coordinate of a single-degree weight model carries the
ordinary action of the corresponding chain term. -/
theorem weightComplexPieceAddEquiv_act (b : ℤ) {X Y : WeightCategory R} (a : X ⟶ Y)
    (x : (weightComplexPiece F b).obj X) :
    weightComplexPieceAddEquiv F b Y ((weightComplexPiece F b).act a x) =
      (F.map a).f b (weightComplexPieceAddEquiv F b X x) := by
  let K := (weightComplexPieceDiagram F b).obj X
  let L := (weightComplexPieceDiagram F b).obj Y
  change (pieceIso F b Y).hom (ComplexSum.component L b
      (ComplexSum.map ((weightComplexPieceDiagram F b).map a) x)) =
    (F.map a).f b ((pieceIso F b X).hom (ComplexSum.component K b x))
  erw [complexComponent_map]
  change (pieceIso F b Y).hom (((HomologicalComplex.single (ModuleCat S) (ComplexShape.up ℤ) b).map
    ((F.map a).f b)).f b (ComplexSum.component K b x)) = _
  rw [HomologicalComplex.single_map_f_self]
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]

theorem weightComplexPiece_mem_grading_iff (b n : ℤ) (X : WeightCategory R)
    (x : (weightComplexPiece F b).obj X) :
    x ∈ DG.grading n ↔ n = b ∨ x = 0 := by
  let L := (weightComplexPieceDiagram F b).obj X
  change (x : ComplexSum L) ∈ DG.grading (M := ComplexSum L) n ↔ n = b ∨ x = 0
  constructor
  · intro hx
    by_cases h : n = b
    · exact Or.inl h
    · obtain ⟨y, hy⟩ := ComplexSum.mem_grading_iff.mp hx
      have hz : ComplexSum.component L b x = 0 :=
        (congrArg (ComplexSum.component L b) hy.symm).trans (ComplexSum.component_of_ne h y)
      exact Or.inr ((single_reconstruct F b X x).symm.trans (by erw [hz, map_zero]; rfl))
  · intro h
    rcases h with h | h
    · subst n
      exact ComplexSum.mem_grading_iff.mpr ⟨_, single_reconstruct F b X x⟩
    · rw [h]
      exact zero_mem _

theorem weightComplexPiece_d_eq_zero (b : ℤ) (X : WeightCategory R)
    (x : (weightComplexPiece F b).obj X) : d x = 0 := by
  let L := (weightComplexPieceDiagram F b).obj X
  let y : ComplexSum L := x
  have hd : L.d b (b + 1) = 0 :=
    HomologicalComplex.single_obj_d (ComplexShape.up ℤ) b ((F.obj X).X b) b (b+1)
  change d y = 0
  rw [← single_reconstruct F b X y, ComplexSum.d_of, hd]
  change ComplexSum.of L (b+1) 0 = 0
  exact map_zero _

private def pieceSectionAdd (b : ℤ) (X : WeightCategory R) :
    (weightComplexPiece F b).obj X →+ (diagramWeightComplexTruncation F b).toCatModule.obj X :=
  ((ComplexSum.of (F.obj X) b).toAddMonoidHom.comp
    ((pieceIso F b X).hom.hom.toAddMonoidHom.comp
      (ComplexSum.component ((weightComplexPieceDiagram F b).obj X) b).toAddMonoidHom)).codRestrict _
      (fun x j hj => ComplexSum.component_of_ne (by omega) _)

private def diagramWeightComplexTruncationSection (b : ℤ) :
    CatModule.Cochain (weightComplexPiece F b) (diagramWeightComplexTruncation F b).toCatModule 0 :=
  CatModule.Cochain.ofHoms (pieceSectionAdd F b)
    (by
      intro X n x hx
      let L := (weightComplexPieceDiagram F b).obj X
      change (x : ComplexSum L) ∈ DG.grading n at hx
      change ComplexSum.of (F.obj X) b ((pieceIso F b X).hom (ComplexSum.component L b x)) ∈ DG.grading n
      by_cases hn : n = b
      · subst n
        exact ComplexSum.of_mem_grading _ _
      · obtain ⟨z, hz⟩ := ComplexSum.mem_grading_iff.mp hx
        have he := (congrArg (ComplexSum.component L b) hz.symm).trans (ComplexSum.component_of_ne hn z)
        erw [he, map_zero, map_zero]
        exact zero_mem _)
    (by
      intro X Y a x
      apply Subtype.ext
      let K := (weightComplexPieceDiagram F b).obj X
      let L := (weightComplexPieceDiagram F b).obj Y
      change ComplexSum.of (F.obj Y) b ((pieceIso F b Y).hom (ComplexSum.component L b
        (ComplexSum.map ((weightComplexPieceDiagram F b).map a) x))) =
        ComplexSum.map (F.map a) (ComplexSum.of (F.obj X) b
          ((pieceIso F b X).hom (ComplexSum.component K b x)))
      erw [complexComponent_map, ComplexSum.map_of]
      apply congrArg (ComplexSum.of (F.obj Y) b)
      change (pieceIso F b Y).hom (((HomologicalComplex.single (ModuleCat S) (ComplexShape.up ℤ) b).map
        ((F.map a).f b)).f b (ComplexSum.component K b x)) = _
      rw [HomologicalComplex.single_map_f_self]
      erw [ModuleCat.comp_apply, ModuleCat.comp_apply]
      erw [Iso.inv_hom_id_apply]
      rfl)

theorem diagramWeightComplexTruncation_step (b : ℤ) (X : WeightCategory R) :
    (diagramWeightComplexTruncation F (b+1)).carrier X ≤ (diagramWeightComplexTruncation F b).carrier X :=
  fun _ hx j hj => hx j (by omega)

private theorem pieceProjection_eq_zero (b : ℤ) (X : WeightCategory R)
    (x : (diagramWeightComplexTruncation F b).toCatModule.obj X) :
    (diagramWeightComplexTruncationProjection F b).app X x = 0 ↔
      x.val ∈ (diagramWeightComplexTruncation F (b+1)).carrier X := by
  let K := F.obj X
  let L := (weightComplexPieceDiagram F b).obj X
  change ComplexSum.of L b ((pieceIso F b X).inv (ComplexSum.component K b x.val)) = 0 ↔
    ∀ j < b+1, ComplexSum.component K j x.val = 0
  constructor
  · intro hx j hj
    by_cases h : j = b
    · subst j
      have hh : ComplexSum.of L b ((pieceIso F b X).inv (ComplexSum.component K b x.val)) =
          ComplexSum.of L b 0 := hx.trans (map_zero _).symm
      have hz := ComplexSum.of_injective b hh
      exact (ModuleCat.mono_iff_injective (pieceIso F b X).inv).mp inferInstance
        (hz.trans (map_zero _).symm)
    · exact x.property j (by omega)
  · intro hx
    erw [hx b (by omega), map_zero, map_zero]

/-- Adjacent truncations are graded split, with the lowest remaining degree as their quotient. -/
def diagramWeightComplexTruncationSplitting (b : ℤ) :
    CatModule.GradedSplitting (CatSubmodule.inclusion (diagramWeightComplexTruncation_step F b))
      (diagramWeightComplexTruncationProjection F b) :=
  CatModule.GradedSplitting.ofSection (diagramWeightComplexTruncation_step F b)
    (diagramWeightComplexTruncationProjection F b) (pieceProjection_eq_zero F b)
    (diagramWeightComplexTruncationSection F b) (by
      intro X y
      let K := F.obj X
      let L := (weightComplexPieceDiagram F b).obj X
      change ComplexSum.of L b ((pieceIso F b X).inv (ComplexSum.component K b
        (ComplexSum.of K b ((pieceIso F b X).hom (ComplexSum.component L b y))))) = y
      erw [ComplexSum.component_of_same]
      erw [Iso.hom_inv_id_apply]
      exact single_reconstruct F b X y)

section Filtration

universe a b c
variable {C : Type a} [Category.{b} C] [Preadditive C]
  [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  {P : CatModule.{c} C}

/-- An exhaustive filtration by graded-split dg submodules with K-projective
successive quotients is K-projective when its initial term is. -/
theorem isKProjective_of_gradedSplitFiltration
    (F : ℕ → CatSubmodule P)
    (hstep : ∀ i X, (F i).carrier X ≤ (F (i + 1)).carrier X)
    (hexh : ∀ X (x : P.obj X), ∃ i, x ∈ (F i).carrier X)
    (h₀ : CatModule.IsKProjective (F 0).toCatModule)
    (Q : ℕ → CatModule.{c} C)
    (π : ∀ i, (F (i + 1)).toCatModule ⟶ Q i)
    (split : ∀ i, CatModule.GradedSplitting (CatSubmodule.inclusion (hstep i)) (π i))
    (hQ : ∀ i, CatModule.IsKProjective (Q i)) :
    CatModule.IsKProjective P := by
  intro N hN f
  obtain ⟨h, hh⟩ := CatModule.Cochain.exists_of_filtration hstep hexh
    (fun i => {h : CatModule.Cochain (F i).toCatModule N (-1) |
      CatModule.Cochain.ofHom ((F i).subtype ≫ f) = CatModule.δ (-1) 0 h})
    (CatModule.homotopic_zero_iff_exists.mp (h₀ N hN ((F 0).subtype ≫ f)))
    (fun i h hh => (split i).exists_extension (hQ i N hN)
      ((F (i + 1)).subtype ≫ f) h hh)
  refine CatModule.homotopic_zero_iff_exists.mpr ⟨h, CatModule.Cochain.ext fun X x => ?_⟩
  obtain ⟨i, hi⟩ := hexh X x
  have h1 := congrArg (fun z : CatModule.Cochain (F i).toCatModule N 0 => z.app X ⟨x, hi⟩) (hh i)
  have h2 := congrArg (fun z : CatModule.Cochain (F i).toCatModule N 0 => z.app X ⟨x, hi⟩)
    (CatModule.δ_ofHom_comp (F i).subtype h 0)
  exact h1.trans h2

end Filtration

private theorem diagramWeightComplexTruncation_exhaustive (X : WeightCategory R)
    (x : (diagramWeightModuleOfComplex F).obj X) :
    ∃ k : ℕ, x ∈ (diagramWeightComplexTruncation F (1 - (k : ℤ))).carrier X := by
  let K := F.obj X
  let y : ComplexSum K := x
  change ∃ k : ℕ, ∀ j < 1 - (k : ℤ), ComplexSum.component K j y = 0
  induction y using ComplexSum.induction_on with
  | zero => exact ⟨0, fun _ _ => map_zero _⟩
  | of n z =>
    refine ⟨(1 - n).toNat, fun j hj => ComplexSum.component_of_ne ?_ z⟩
    omega
  | add y z hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨max m n, fun j hj => ?_⟩
    rw [map_add, hm j (by push_cast at hj; omega), hn j (by push_cast at hj; omega), add_zero]

private theorem diagramWeightComplexTruncation_initial_kProjective
    (hzero : ∀ X (n : ℤ), 0 < n → CategoryTheory.Limits.IsZero ((F.obj X).X n)) :
    CatModule.IsKProjective (diagramWeightComplexTruncation F 1).toCatModule := by
  intro N hN f
  refine CatModule.homotopic_zero_iff_exists.mpr ⟨0, CatModule.Cochain.ext fun X x => ?_⟩
  have hx : x = 0 := by
    apply Subtype.ext
    apply complexComponent_ext
    intro j
    change ComplexSum.component (F.obj X) j x.val = 0
    by_cases hj : 0 < j
    · let _ := ModuleCat.isZero_iff_subsingleton.mp (hzero X j hj)
      exact Subsingleton.elim _ _
    · exact x.property j (by omega)
  rw [hx]
  simp

private theorem truncationSplitting_exists (b a : ℤ) (h : a = b+1)
    (step : ∀ X, (diagramWeightComplexTruncation F a).carrier X ≤
      (diagramWeightComplexTruncation F b).carrier X) :
    ∃ p : (diagramWeightComplexTruncation F b).toCatModule ⟶ weightComplexPiece F b,
      Nonempty (CatModule.GradedSplitting (CatSubmodule.inclusion step) p) := by
  subst a
  exact ⟨_, ⟨diagramWeightComplexTruncationSplitting F b⟩⟩

/-- A bounded-above weight complex is K-projective if its individual terms,
placed in their cohomological degrees with zero differential, are K-projective. -/
theorem diagramWeightModuleOfComplex_isKProjective
    (hzero : ∀ X (n : ℤ), 0 < n → CategoryTheory.Limits.IsZero ((F.obj X).X n))
    (hterm : ∀ n : ℕ, CatModule.IsKProjective (weightComplexPiece F (-(n : ℤ)))) :
    CatModule.IsKProjective (diagramWeightModuleOfComplex F) := by
  let cut (n : ℕ) : ℤ := 1 - (n : ℤ)
  let trunc (n : ℕ) := diagramWeightComplexTruncation F (cut n)
  have hb (n : ℕ) : cut (n+1) = -(n : ℤ) := by dsimp [cut]; omega
  have hc (n : ℕ) : cut n = cut (n+1) + 1 := by dsimp [cut]; omega
  let step (n : ℕ) (X : WeightCategory R) : (trunc n).carrier X ≤ (trunc (n + 1)).carrier X := by
    intro x hx j hj
    exact hx j (by rw [hc n]; omega)
  have hs (n : ℕ) := truncationSplitting_exists F (cut (n+1)) (cut n) (hc n) (step n)
  choose proj split using hs
  exact isKProjective_of_gradedSplitFiltration trunc step
    (diagramWeightComplexTruncation_exhaustive F) (diagramWeightComplexTruncation_initial_kProjective F hzero)
    (fun n => weightComplexPiece F (cut (n+1))) proj (fun n => (split n).some)
    (fun n => by rw [hb n]; exact hterm n)

private def cutProjection (b : ℤ) (X : WeightCategory R) :
    ComplexSum (F.obj X) →+ ComplexSum (F.obj X) :=
  DirectSum.toAddMonoid fun n =>
    if b ≤ n then (ComplexSum.of (F.obj X) n).toAddMonoidHom else 0

omit [F.Additive] in
private theorem cutProjection_of (b : ℤ) (X : WeightCategory R) (n : ℤ) (x : (F.obj X).X n) :
    cutProjection F b X (ComplexSum.of (F.obj X) n x) =
      if b ≤ n then ComplexSum.of (F.obj X) n x else 0 := by
  classical
  change (DirectSum.toAddMonoid (β := fun n => (F.obj X).X n) (fun n =>
    if b ≤ n then (ComplexSum.of (F.obj X) n).toAddMonoidHom else 0))
      (DirectSum.of (fun n => (F.obj X).X n) n x) = _
  rw [DirectSum.toAddMonoid_of]
  split <;> rfl

omit [F.Additive] in
private theorem cutProjection_component (b : ℤ) (X : WeightCategory R) (n : ℤ)
    (x : ComplexSum (F.obj X)) :
    ComplexSum.component (F.obj X) n (cutProjection F b X x) =
      if b ≤ n then ComplexSum.component (F.obj X) n x else 0 := by
  induction x using ComplexSum.induction_on with
  | zero => simp
  | of j y =>
    rw [cutProjection_of]
    by_cases h : j = n
    · subst j
      split <;> simp
    · rw [ComplexSum.component_of_ne h]
      split <;> simp [ComplexSum.component_of_ne h]
  | add x y hx hy =>
    rw [map_add (cutProjection F b X), map_add, hx, hy, map_add]
    split <;> simp

/-- Keeping the coordinates above the cut gives a graded retraction of the truncation. -/
def diagramWeightComplexTruncationRetraction (b : ℤ) :
    CatModule.Cochain (diagramWeightModuleOfComplex F)
      (diagramWeightComplexTruncation F b).toCatModule 0 where
  app X := (cutProjection F b X).codRestrict ((diagramWeightComplexTruncation F b).carrier X)
    (fun x n hn => by rw [cutProjection_component, ite_eq_right (by omega)])
  map_mem' {X n x} hx := by
    change (x : ComplexSum (F.obj X)) ∈ DG.grading n at hx
    change cutProjection F b X x ∈ DG.grading (n + 0)
    obtain ⟨y, rfl⟩ := ComplexSum.mem_grading_iff.mp hx
    rw [add_zero, cutProjection_of]
    split
    · exact ComplexSum.of_mem_grading n y
    · exact zero_mem _
  map_smul' {X Y n f} _ x := by
    rw [zero_mul, koszulSign_zero, one_smul]
    apply Subtype.ext
    change cutProjection F b Y (ComplexSum.map (F.map f) x) =
      ComplexSum.map (F.map f) (cutProjection F b X x)
    induction x using ComplexSum.induction_on with
    | zero => simp
    | of i y =>
      rw [ComplexSum.map_of, cutProjection_of, cutProjection_of]
      split
      · exact (ComplexSum.map_of (F.map f) i y).symm
      · exact (map_zero _).symm
    | add x y hx hy => simp only [map_add, hx, hy]

/-- The graded projection fixes every element supported above the cut. -/
theorem diagramWeightComplexTruncationRetraction_subtype (b : ℤ) (X : WeightCategory R)
    (x : (diagramWeightComplexTruncation F b).toCatModule.obj X) :
    (diagramWeightComplexTruncationRetraction F b).app X
      ((diagramWeightComplexTruncation F b).subtype.app X x) = x := by
  apply Subtype.ext
  let z : (diagramWeightComplexTruncation F b).carrier X := x
  let a : ComplexSum (F.obj X) := z.val
  change cutProjection F b X a = a
  apply complexComponent_ext
  intro n
  rw [cutProjection_component F b X n a]
  split
  · rfl
  · exact (z.property n (by omega)).symm

/-- Tensoring a bounded-above weight complex with the fixed coefficient gives an
acyclic coend when the coend of each of its single-degree pieces is acyclic. -/
theorem diagramWeightModuleOfComplex_tensor_acyclic
    (N : CatModule (DGOpposite (WeightCategory R)))
    (hdeg : ∀ {X Y : WeightCategory R} (f : X ⟶ Y), f ∈ DG.grading (0 : ℤ))
    (hzero : ∀ X (n : ℤ), 0 < n → Limits.IsZero ((F.obj X).X n))
    (hterm : ∀ n : ℕ, DG.IsAcyclic
      (CatTensorProduct N (weightComplexPiece F (-(n : ℤ))))) :
    DG.IsAcyclic (CatTensorProduct N (diagramWeightModuleOfComplex F)) := by
  let cut (n : ℕ) : ℤ := 1 - (n : ℤ)
  let trunc (n : ℕ) := diagramWeightComplexTruncation F (cut n)
  let stages (n : ℕ) := (trunc n).toCatModule
  have hsteps (m n : ℕ) (hmn : m ≤ n) (X : WeightCategory R) :
      (trunc m).carrier X ≤ (trunc n).carrier X := by
    intro x hx j hj
    exact hx j (by change j < cut n at hj; dsimp [cut] at *; omega)
  have hstages (n : ℕ) : DG.IsAcyclic (CatTensorProduct N (stages n)) := by
    induction n with
    | zero =>
      have hobj (X : WeightCategory R) (x : (stages 0).obj X) : x = 0 := by
        apply Subtype.ext
        apply complexComponent_ext
        intro j
        change ComplexSum.component (F.obj X) j x.val = 0
        by_cases hj : 0 < j
        · let _ := ModuleCat.isZero_iff_subsingleton.mp (hzero X j hj)
          exact Subsingleton.elim _ _
        · exact x.property j (by dsimp [cut]; omega)
      refine DG.isAcyclic_iff.mpr fun j z hz _ => ⟨0, zero_mem _, ?_⟩
      have hzer (x : CatTensorProduct N (stages 0)) : x = 0 := by
        induction x using CatTensorProduct.induction_on with
        | zero => rfl
        | tmul X a b => rw [hobj X b, CatTensorProduct.tmul_zero]
        | add a b ha hb => rw [ha, hb, add_zero]
      rw [hzer z, d_zero]
    | succ n ih =>
      have hc : cut n = cut (n+1) + 1 := by dsimp [cut]; omega
      have hb : cut (n+1) = -(n : ℤ) := by dsimp [cut]; omega
      obtain ⟨p, ⟨split⟩⟩ := truncationSplitting_exists F (cut (n+1)) (cut n) hc
        (hsteps n (n+1) (Nat.le_succ _))
      let i := CatSubmodule.inclusion (hsteps n (n+1) (Nat.le_succ _))
      let I := CatTensorProduct.map (𝟙 N) i
      let P := CatTensorProduct.map (𝟙 N) p
      obtain ⟨hi, hex, hp⟩ := CatTensorProduct.exact_of_graded_split N hdeg i p
        split.r split.s (fun _ => split.r_i) (fun _ => split.p_s) (fun _ => split.p_i)
        (fun _ => split.i_r_add_s_p)
      have hq : DG.IsAcyclic (CatTensorProduct N (weightComplexPiece F (cut (n+1)))) := by
        rw [hb]
        exact hterm n
      exact isAcyclic_of_shortExact_addHom I P
        (fun h => CatTensorProduct.map_mem _ _ h) (fun h => CatTensorProduct.map_mem _ _ h)
        (CatTensorProduct.map_d _ _) (CatTensorProduct.map_d _ _) hi hex hp ih hq
  exact CatTensorProduct.isAcyclic_of_graded_split_union N hdeg stages (fun n => (trunc n).subtype)
    (fun n => diagramWeightComplexTruncationRetraction F (cut n))
    (fun n => diagramWeightComplexTruncationRetraction_subtype F (cut n))
    (fun m n h => CatSubmodule.inclusion (hsteps m n h))
    (fun _ _ _ => CatModule.hom_ext fun _ _ => rfl)
    (fun X x => by
      obtain ⟨n, hx⟩ := diagramWeightComplexTruncation_exhaustive F X x
      exact ⟨n, ⟨x, hx⟩, rfl⟩)
    hstages

end Categorification

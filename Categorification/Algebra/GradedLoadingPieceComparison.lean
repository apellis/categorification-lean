/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.GradedLoadingWeightCorners
import Categorification.Algebra.GradedChainWeightDG
import Categorification.Algebra.DiagramWeightComplexKProjective

/-!
# Representable corner models of graded resolution pieces

The cohomological piece of a graded loading resolution is the corresponding
ordinary diagram grade, with its cohomological shift. A degree-zero
representable corner model of that grade identifies the piece as a dg module.
-/

noncomputable section

namespace Categorification.ModuleFiltration

open CategoryTheory DG DirectSum
open scoped DG.DegreeZero Classical CatModule

variable {R : Type} [Ring R] [InternalGrading R] [BigradedDGRing R]
local notation "W" => WeightCategory R

/-- A degree-zero scalar idempotent yields a representable corner at each weight. -/
def loadingWeightIdempotent (a : R) (ha : a ∈ wgrading (M := R) 0)
    (hi : IsIdempotentElem a) (X : W) : DGCategory.Idempotent X where
  val := ⟨a, by simpa only [sub_self] using ha⟩
  mem_cocycles := ⟨WeightCategory.mem_grading_iff.mpr
    ((InDegreeZero.ring_mem_grading_iff (R := R)).mpr (Or.inl rfl)),
    WeightCategory.hom_ext (InDegreeZero.ring_d_apply a)⟩
  comp_self := WeightCategory.hom_ext hi.eq

theorem corner_mem_zero_iff {V X : W} (p : DGCategory.Idempotent V)
    (i : ℤ) (x : (CatModule.corner p).obj X) : x ∈ grading i ↔ i = 0 ∨ x = 0 := by
  let y : (CatModule.cornerSubmodule p).carrier X := x
  change y.val.val ∈ grading (M := R) i ↔ i = 0 ∨ y = 0
  rw [InDegreeZero.ring_mem_grading_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (Subtype.ext (WeightCategory.hom_ext h))
  · rintro (h | rfl)
    · exact Or.inl h
    · exact Or.inr rfl

theorem corner_d_zero {V X : W} (p : DGCategory.Idempotent V)
    (x : (CatModule.corner p).obj X) : d x = 0 :=
  Subtype.ext (WeightCategory.hom_ext (InDegreeZero.ring_d_apply x.val.val))

theorem cornerSum_mem_zero_iff {J : Type} {V : J → W}
    (p : ∀ j, DGCategory.Idempotent (V j)) (X : W) (i : ℤ)
    (x : (CatModule.directSum (fun j => CatModule.corner (p j))).obj X) :
    x ∈ grading i ↔ i = 0 ∨ x = 0 := by
  classical
  let y : ⨁ j : J, (CatModule.corner (p j)).obj X := x
  change (∀ j, y j ∈ grading i) ↔ i = 0 ∨ y = 0
  constructor
  · intro h
    by_cases hi : i = 0
    · exact Or.inl hi
    · exact Or.inr (DFinsupp.ext fun j => ((corner_mem_zero_iff (p j) i (y j)).mp (h j)).resolve_left hi)
  · rintro (h | rfl) j
    · exact (corner_mem_zero_iff (p j) i (y j)).mpr (Or.inl h)
    · exact zero_mem _

theorem cornerSum_d_zero {J : Type} {V : J → W}
    (p : ∀ j, DGCategory.Idempotent (V j)) (X : W)
    (x : (CatModule.directSum (fun j => CatModule.corner (p j))).obj X) : d x = 0 := by
  let y : ⨁ j : J, (CatModule.corner (p j)).obj X := x
  change d y = 0
  apply DFinsupp.ext
  intro j
  rw [DG.DirectSum.coe_d_apply, DirectSum.zero_apply]
  exact corner_d_zero (p j) (y j)

private def isoOfSingleDegreeCoords {M N : CatModule W} (b : ℤ)
    (E : ∀ X, M.obj X ≃+ N.obj X)
    (hM : ∀ X i (x : M.obj X), x ∈ grading i ↔ i = b ∨ x = 0)
    (hN : ∀ X i (x : N.obj X), x ∈ grading i ↔ i = b ∨ x = 0)
    (hdM : ∀ X (x : M.obj X), d x = 0)
    (hdN : ∀ X (x : N.obj X), d x = 0)
    (hact : ∀ {X Y : W} (f : X ⟶ Y) (x : M.obj X), E Y (M.act f x) = N.act f (E X x)) :
    M ≅ N where
  hom := {
    app := fun X => (E X).toAddMonoidHom
    map_mem' := by
      intro X i x hx
      rw [hN]
      rcases (hM X i x).mp hx with h | rfl
      · exact Or.inl h
      · exact Or.inr (map_zero _)
    map_d' := by intro X x; simp [hdM, hdN]
    map_smul' := hact }
  inv := {
    app := fun X => (E X).symm.toAddMonoidHom
    map_mem' := by
      intro X i x hx
      rw [hM]
      rcases (hN X i x).mp hx with h | rfl
      · exact Or.inl h
      · exact Or.inr (map_zero _)
    map_d' := by intro X x; simp [hdM, hdN]
    map_smul' := by
      intro X Y f x
      change (E Y).symm (N.act f x) = M.act f ((E X).symm x)
      apply (E Y).injective
      rw [AddEquiv.apply_symm_apply, hact, AddEquiv.apply_symm_apply] }
  hom_inv_id := CatModule.hom_ext fun X x => (E X).symm_apply_apply x
  inv_hom_id := CatModule.hom_ext fun X x => (E X).apply_symm_apply x

private theorem weightShift_mem_iff {K : CatModule W}
    (h : ∀ X i (x : K.obj X), x ∈ grading i ↔ i = 0 ∨ x = 0)
    (n : ℕ) (X : W) (i : ℤ) (x : (CatModule.shift (n : ℤ) K).obj X) :
    x ∈ grading i ↔ i = -(n : ℤ) ∨ x = 0 := by
  rw [CatModule.shift.mem_grading_iff', h]
  have hz : CatModule.shift.unmk (n : ℤ) x = 0 ↔ x = 0 := by
    rw [← map_zero (CatModule.shift.unmk (n : ℤ) (M := K) (X := X)),
      (CatModule.shift.unmk (n : ℤ) (M := K) (X := X)).injective.eq_iff]
  rw [hz]
  have hzero : i + (n : ℤ) = 0 ↔ i = -(n : ℤ) := by omega
  rw [hzero]

private theorem weightShift_d_zero {K : CatModule W}
    (h : ∀ X (x : K.obj X), d x = 0)
    (n : ℕ) (X : W) (x : (CatModule.shift (n : ℤ) K).obj X) : d x = 0 := by
  apply (CatModule.shift.unmk (n : ℤ)).injective
  rw [CatModule.shift.unmk_d, h, smul_zero, map_zero]

private theorem weightShift_act {K : CatModule W} (n : ℕ)
    {X Y : W} (a : X ⟶ Y) (x : K.obj X) :
    (CatModule.shift.mk (n : ℤ) (K.act a x)) =
      (CatModule.shift (n : ℤ) K).act a (CatModule.shift.mk (n : ℤ) x) := by
  have ha : a ∈ grading 0 := WeightCategory.mem_grading_iff.mpr
    ((InDegreeZero.ring_mem_grading_iff (R := R)).mpr (Or.inl rfl))
  change CatModule.shift.mk (M := K) (n : ℤ) (a • x) = a • CatModule.shift.mk (M := K) (n : ℤ) x
  simpa only [Int.mul_zero, koszulSign_zero, one_smul] using
    (CatModule.shift.smul_mk (n := (n : ℤ)) (M := K) ha x).symm


section Piece

variable (P : ℕ → WeightGradedTerm R)
  (δ : ∀ n, (P (n+1)).obj →ₗ[R] (P n).obj)
  (hδ : ∀ n j {x : (P (n+1)).obj}, x ∈ (P (n+1)).grade j → δ n x ∈ (P n).grade j)
  (hc : ∀ n (x : (P (n+2)).obj), δ n (δ (n+1) x) = 0)

private abbrev cochain := weightCochainOfGradedChain P δ hδ hc

/-- The coordinate of a single cohomological piece of the actual graded chain. -/
private def pieceCoordinate (n : ℕ) (X : W) :
    (weightComplexPiece (cochain P δ hδ hc) (-(n : ℤ))).obj X ≃+ (P n).grade X.as :=
  (weightComplexPieceAddEquiv (cochain P δ hδ hc) (-(n : ℤ)) X).trans
    (weightCochainOfGradedChain_coordinate P δ hδ hc X n).toLinearEquiv.toAddEquiv

private theorem pieceCoordinate_act (n : ℕ) {X Y : W} (a : X ⟶ Y)
    (x : (weightComplexPiece (cochain P δ hδ hc) (-(n : ℤ))).obj X) :
    (pieceCoordinate P δ hδ hc n Y
      ((weightComplexPiece (cochain P δ hδ hc) (-(n : ℤ))).act a x)).val =
      a.val • (pieceCoordinate P δ hδ hc n X x).val := by
  change ((weightCochainOfGradedChain_coordinate P δ hδ hc Y n).hom
    (weightComplexPieceAddEquiv (cochain P δ hδ hc) (-(n : ℤ)) Y
      ((weightComplexPiece (cochain P δ hδ hc) (-(n : ℤ))).act a x))).val = _
  rw [weightComplexPieceAddEquiv_act]
  exact congrArg Subtype.val (weightCochainOfGradedChain_coordinate_act P δ hδ hc a n
    (weightComplexPieceAddEquiv (cochain P δ hδ hc) (-(n : ℤ)) X x))

/-- A chain term with the same weight action as a degree-zero projective
model gives the corresponding shifted cohomological piece. -/
def weightComplexPieceIsoOfGradeCoords (n : ℕ) (K : CatModule W)
    (E : ∀ X : W, (P n).grade X.as ≃+ K.obj X)
    (hK : ∀ X i (x : K.obj X), x ∈ grading i ↔ i = 0 ∨ x = 0)
    (hdK : ∀ X (x : K.obj X), d x = 0)
    (hE : ∀ {X Y : W} (a : X ⟶ Y) (x : (P n).grade X.as) (y : (P n).grade Y.as),
      y.val = a.val • x.val → E Y y = K.act a (E X x)) :
    weightComplexPiece (cochain P δ hδ hc) (-(n : ℤ)) ≅ CatModule.shift (n : ℤ) K := by
  apply isoOfSingleDegreeCoords (-(n : ℤ))
    (fun X => ((pieceCoordinate P δ hδ hc n X).trans (E X)).trans (CatModule.shift.mk (n : ℤ)))
    (fun X i => weightComplexPiece_mem_grading_iff (cochain P δ hδ hc) (-(n : ℤ)) i X)
    (weightShift_mem_iff hK n)
    (weightComplexPiece_d_eq_zero (cochain P δ hδ hc) (-(n : ℤ)))
    (weightShift_d_zero hdK n)
  intro X Y a x
  change CatModule.shift.mk (n : ℤ) (E Y (pieceCoordinate P δ hδ hc n Y _)) =
    (CatModule.shift (n : ℤ) K).act a
      (CatModule.shift.mk (n : ℤ) (E X (pieceCoordinate P δ hδ hc n X x)))
  rw [hE a _ _ (pieceCoordinate_act P δ hδ hc n a x)]
  exact weightShift_act n a _

end Piece

end Categorification.ModuleFiltration

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.NumericalAdjunction
import Categorification.TwoRep.LemXind
import Categorification.TwoRep.BBwProof

/-!
# The numerical shadow of (3.2) at every weight

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, §3.2: the adjoint induction hypothesis (3.2) (`eq:ind_hyp`) at the weight `n`
says `(E 1_n)_L ≅ 1_n F ⟨-n-1⟩`. The dimension counts of §3.2 use it only through the equalities
of Hom-dimensions that such an adjunction gives (`StrongSl2.NumAdj`, `WordBounded.lean`).

Since the boundedness condition (BB_w) (`StrongSl2.BBw`) holds (`StrongSl2.bbw`), these
equalities hold **at every weight**, for word-generated test 1-morphisms (`numAdj`): apply the
abstract numerical adjunction (`Sl2CatData.finrank_f_eq`, `NumericalAdjunction.lean`) to

* the Hom categories `Hom(obj c, obj t)`, `t ∈ ℤ`, with `e = (- ≫ E)`, `f = (- ≫ F)`
  (`leftData`): this gives `dim Hom(x ≫ F, y) = dim Hom(x, y ≫ E⟨-n-1⟩)`;
* the Hom categories `Hom(obj t, obj c)`, `t ∈ ℤ`, with `e = (F ≫ -)`, `f = (E ≫ -)`
  (`rightData`): this gives `dim Hom(x, F ≫ y) = dim Hom(E⟨-n-1⟩ ≫ x, y)`.

In both cases condition (3) of CL Definition 1.2 gives the commutation relation, the formal
adjunction `E 1_n ⊣ 1_n F ⟨n+1⟩` gives the adjunction of Hom-dimensions in one direction, the test
objects are the word-generated 1-morphisms, and (BB_w) is the boundedness of their Hom spaces.

Consequently CL Lemma 3.6 (`DotNondeg`) follows from (BB_w) without the adjoint induction
hypothesis, retaining the ambient graded linear, Hom-finite and idempotent-complete hypotheses,
the range `n ≥ 2`, and the nonzero top identity (`dotNondeg`). This is a numerical route to
dot nondegeneracy, not a construction of an actual adjunction or full Proposition 3.9.
-/

noncomputable section

namespace Categorification.TwoRep.StrongSl2

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Module
open KrullSchmidtCat (HomFinite)

universe w v u

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [∀ a b : B, HomFinite k (a ⟶ b)] {S : StrongSl2 k B}

variable (S) in
/-- The categories `Hom(obj c, obj t)`, `t ∈ ℤ`, with the functors `- ≫ E`, `- ≫ F` and the
word-generated 1-morphisms as test objects. -/
def leftData (c : ℤ) : Sl2CatData k (fun t : ℤ => (S.obj c ⟶ S.obj t)) where
  n₀ := S.n₀
  e t := postcomp (S.obj c) (S.E t)
  f t := postcomp (S.obj c) (S.F t)
  eBiprod t X Y := whiskerRightBiprodIso X Y (S.E t)
  fBiprod t X Y := whiskerRightBiprodIso X Y (S.F t)
  eShift t X a := whiskerRightShiftIso X (S.E t) a
  fShift t X a := whiskerRightShiftIso X (S.F t) a
  EF t X h := by
    obtain ⟨e⟩ := S.EF t h
    exact ⟨α_ _ _ _ ≪≫ whiskerLeftIso X e ≪≫ whiskerLeftBiprodIso _ _ _ ≪≫
      biprod.mapIso (α_ _ _ _).symm (compQsumIso _ _ _)⟩
  FE t X h := by
    obtain ⟨e⟩ := S.FE t h
    exact ⟨α_ _ _ _ ≪≫ whiskerLeftIso X e ≪≫ whiskerLeftBiprodIso _ _ _ ≪≫
      biprod.mapIso (α_ _ _ _).symm (compQsumIso _ _ _)⟩
  adj t X Z d := by
    change finrank k (X ≫ S.E t ⟶ Z⟦d⟧) = finrank k (X ⟶ (Z ≫ S.F t)⟦d + (S.n₀ + 2 * t + 1)⟧)
    rw [(S.dimAdj t).left, finrank_hom_congr_right k X
      (shiftCompShiftIso Z (S.F t) (p := d) (q := S.wt t + 1) (s := d + (S.n₀ + 2 * t + 1))
        (by dsimp [wt]; ring))]
  bdd := by
    obtain ⟨N, hN⟩ := S.integrable
    exact ⟨N, fun t ht X => isZero_of_isZero_id_tgt (hN t ht) X⟩
  P t X := S.WordGen c t X
  P_zero t := .zero _ _
  P_biprod t _ _ hX hY := .biprod hX hY
  P_shift t _ a hX := .shift a hX
  P_iso t _ _ hX e := hX.of_iso e
  P_e t _ hX := hX.comp (.E t)
  P_f t _ hX := hX.comp (.F t)
  bb t _ _ hX hZ := S.homBddBelow_wordGen hX hZ

variable (S) in
/-- The categories `Hom(obj t, obj c)`, `t ∈ ℤ`, with the functors `F ≫ -`, `E ≫ -` and the
word-generated 1-morphisms as test objects. -/
def rightData (c : ℤ) : Sl2CatData k (fun t : ℤ => (S.obj t ⟶ S.obj c)) where
  n₀ := S.n₀
  e t := precomp (S.obj c) (S.F t)
  f t := precomp (S.obj c) (S.E t)
  eBiprod t X Y := whiskerLeftBiprodIso (S.F t) X Y
  fBiprod t X Y := whiskerLeftBiprodIso (S.E t) X Y
  eShift t X a := whiskerLeftShiftIso (S.F t) X a
  fShift t X a := whiskerLeftShiftIso (S.E t) X a
  EF t X h := by
    obtain ⟨e⟩ := S.EF t h
    exact ⟨(α_ _ _ _).symm ≪≫ whiskerRightIso e X ≪≫ whiskerRightBiprodIso _ _ _ ≪≫
      biprod.mapIso (α_ _ _ _) (qsumCompIso _ _ _)⟩
  FE t X h := by
    obtain ⟨e⟩ := S.FE t h
    exact ⟨(α_ _ _ _).symm ≪≫ whiskerRightIso e X ≪≫ whiskerRightBiprodIso _ _ _ ≪≫
      biprod.mapIso (α_ _ _ _) (qsumCompIso _ _ _)⟩
  adj t X Z d := by
    change finrank k (S.F t ≫ X ⟶ Z⟦d⟧) = finrank k (X ⟶ (S.E t ≫ Z)⟦d + (S.n₀ + 2 * t + 1)⟧)
    rw [finrank_hom_congr_right k X (whiskerLeftShiftIso (S.E t) Z _).symm, (S.dimAdj t).right,
      finrank_hom_congr_left k (whiskerRightShiftIso (S.F t) X _),
      finrank_hom_shift_shift k _ _ (c := d) (by rfl)]
  bdd := by
    obtain ⟨N, hN⟩ := S.integrable
    exact ⟨N, fun t ht X => isZero_of_isZero_id_src (hN t ht) X⟩
  P t X := S.WordGen t c X
  P_zero t := .zero _ _
  P_biprod t _ _ hX hY := .biprod hX hY
  P_shift t _ a hX := .shift a hX
  P_iso t _ _ hX e := hX.of_iso e
  P_e t _ hX := (WordGen.F t).comp hX
  P_f t _ hX := (WordGen.E t).comp hX
  bb t _ _ hX hZ := S.homBddBelow_wordGen hX hZ

variable (S) in
/-- **The numerical shadow of (3.2) holds at every weight**: for word-generated
test 1-morphisms `x`, `y`, `dim Hom(x ≫ F, y) = dim Hom(x, y ≫ E⟨-n-1⟩)` and
`dim Hom(x, F ≫ y) = dim Hom(E⟨-n-1⟩ ≫ x, y)`, `n = wt r`. -/
theorem numAdj (r : ℤ) : S.NumAdj r where
  left c x y hx hy := by
    have h := (leftData S c).finrank_f_eq (t := r) (X := x) (Z := y) hx hy 0
    change finrank k (x ≫ S.F r ⟶ y⟦(0 : ℤ)⟧) =
      finrank k (x ⟶ (y ≫ S.E r)⟦0 - (S.n₀ + 2 * r + 1)⟧) at h
    rw [finrank_hom_shift_zero k _ _ rfl] at h
    rw [h, finrank_hom_congr_right k x (whiskerLeftShiftIso y (S.E r) _)]
    exact finrank_hom_shift_congr k _ _ (by dsimp [wt]; ring)
  right c x y hx hy := by
    have h := (rightData S c).finrank_f_eq (t := r) (X := x) (Z := y) hx hy (S.wt r + 1)
    change finrank k (S.E r ≫ x ⟶ y⟦S.wt r + 1⟧) =
      finrank k (x ⟶ (S.F r ≫ y)⟦S.wt r + 1 - (S.n₀ + 2 * r + 1)⟧) at h
    rw [finrank_hom_shift_zero k x (S.F r ≫ y) (by dsimp [wt]; ring)] at h
    rw [← h, finrank_hom_congr_left k (whiskerRightShiftIso (S.E r) x _),
      finrank_hom_shift_left k _ _ (b := S.wt r + 1) (by ring)]

variable (S) in
/-- **CL Lemma 3.6**: at a weight `n = wt (r + 1 + 1) ≥ 2` with `1_n ≠ 0`, every
decomposition datum of `E F 1_n` has nondegenerate subdiagonal dot entries. No adjoint induction
hypothesis is needed. -/
theorem dotNondeg [∀ a b : B, IsIdempotentComplete (a ⟶ b)] {r : ℤ}
    (hn : 0 ≤ S.wt (r + 1)) (h2 : ¬ IsZero (𝟙 (S.obj (r + 1 + 1)))) (e : S.EFDecomp (r + 1)) :
    DotNondeg e :=
  lemXind_of_numAdj hn (fun r' _ => S.numAdj r') h2 e

end Categorification.TwoRep.StrongSl2

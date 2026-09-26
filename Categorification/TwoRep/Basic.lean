/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Bicategory.Adjunction.Mate
import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Shift.ShiftedHom
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Categorification.Diagrams.KL3.KrullSchmidtCat

/-!
# Graded additive `k`-linear 2-categories (framework for Cautis–Lauda)

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, §2.1.2 (`sec:categories`): "By a graded category we will mean a category
equipped with an auto-equivalence `⟨1⟩` [...] `Hom^l(A, B)` will be short-hand for
`Hom(A, B⟨l⟩)`. A graded additive `k`-linear 2-category is [...] a 2-category `K` such that the Hom
categories [...] are graded additive `k`-linear categories and the composition maps [...] form
graded additive `k`-linear functor[s]."

This file is the base of the `Categorification.TwoRep` development (CL §3 and, later, the proof of
CL Theorem 1.1). Files: `Basic` (this), `KrullSchmidt` (§3.1), `Sl2` (Definition 1.2 for `sl₂`
along a weight string, the adjoint induction), `AdjointInduction` (§3.2 for `n ≥ 0`),
`AdjointInductionNeg` (Lemma 3.1 for `n ≤ 0`, Remark 3.11), `Biadjoint` (§3.4–3.5, dimension
counts), `EndE` (§3.6, dimension count), `QStrong` (Definition 1.2 in general).

## Design

* **The 2-category** is a Mathlib `Bicategory B` (weak, as in CL's "(weak) 2-functor"). Its Hom
  categories carry instances `[∀ a b : B, Preadditive (a ⟶ b)]`, `[∀ a b, Linear k (a ⟶ b)]`,
  `[∀ a b, HasZeroObject (a ⟶ b)]`, `[∀ a b, HasBinaryBiproducts (a ⟶ b)]` (additivity) and
  `[∀ a b, HasShift (a ⟶ b) ℤ]` (the grading shift `⟨1⟩` with its iterates `⟨l⟩`, and the
  coherence isomorphisms `⟨a⟩⟨b⟩ ≅ ⟨a + b⟩`, `⟨0⟩ ≅ 𝟭` of Mathlib's `HasShift`). The mixin
  `GradedBicategory B` says that whiskering by any 1-morphism, on either side, is an additive
  functor commuting with the shift (`Functor.CommShift`) — CL's "composition is a graded additive
  functor" — and that the shift functors are additive; `GradedBicategory.IsLinear B k` adds
  `k`-linearity. Idempotent completeness and finite-dimensionality of 2-Hom spaces are the
  separate instances `[∀ a b, IsIdempotentComplete (a ⟶ b)]` (Mathlib) and
  `[∀ a b, KrullSchmidtCat.HomFinite k (a ⟶ b)]`, assumed only where used.
* **Why a shift functor rather than `ℤ`-graded Hom spaces.** CL's arguments constantly form
  direct sums of shifted objects (`E F 1_n ≅ F E 1_n ⊕_{[n]} 1_n`, `qsum`) and compare dimensions
  of `Hom(X, Y⟨l⟩)`; with a shift functor these are ordinary objects and Hom spaces. Degree-`d`
  2-morphisms `X → Y⟨d⟩` are Mathlib's `ShiftedHom X Y d`, with composition `ShiftedHom.comp` and
  whiskering `shWhiskerLeft`/`shWhiskerRight` (`ShiftedHom.map` along the `CommShift` whiskering
  functors). No compatibility between the left and right whiskering shift isomorphisms, or with
  the associator, is assumed: nothing in §3 needs it (see `DimAdj`), and it can be added as a
  further mixin when a later stage (e.g. cyclicity, §4) needs coherent grading shifts of
  adjunctions.
* **Adjunctions** are Mathlib's `Bicategory.Adjunction` (`u ⊣ v`). The adjunction isomorphisms of
  CL §3.2, `Hom(u x, y) ≅ Hom(x, u_R y)` etc., are the `k`-linear equivalences
  `Adj.homEquivLeft`/`Adj.homEquivRight`, built from Mathlib's mate bijection. The dimension
  arguments of CL §3.2–3.6 use only the dimension-level shadow `DimAdj k u v` of an adjunction,
  which is stable under grading shifts (`DimAdj.shift`: `u ⊣ v ⇒ u⟨n⟩ ⊣ v⟨-n⟩`) and isomorphisms
  without any coherence.
* **Direct sums over quantum integers** (`sec:categories`): `lsum` is the direct sum of a list and
  `qsum d n X = ⊕_{[n]_q^{d}} X = ⊕_{j<n} X⟨d(n-1-2j)⟩`, with dimension formulas
  `finrank_hom_qsum_left/right` and whiskering isomorphisms `qsumCompIso`, `compQsumIso`.
* **Composition order.** Mathlib writes `f ≫ g` for "first `f`, then `g`"; CL's `E F 1_n` (first
  `F`) is `F ≫ E`. All docstrings give both.
* **Zero objects.** CL's "Important convention" (after Definition 1.2) — a weight `λ` is zero when
  `1_λ` is isomorphic to the zero 1-morphism — is `IsZero (𝟙 (obj λ))` in the Hom category;
  `isZero_of_isZero_id_src/tgt` show every 1-morphism out of or into such an object is zero.

## Main declarations

* `GradedBicategory`, `GradedBicategory.IsLinear`;
* `finrank_hom_congr`, `finrank_hom_biprod_left/right`, `finrank_hom_shift_*`: Hom-dimension
  calculus in a `k`-linear category with shift;
* `Adj.homEquivLeft`, `Adj.homEquivRight`, `DimAdj`, `Adj.dimAdj`, `DimAdj.shift`,
  `DimAdj.of_iso`, `adjunctionOfIsZero`;
* `lsum`, `qsum`, `whiskerLeftShiftIso`, `whiskerRightShiftIso`, `shiftCompShiftIso`,
  `whiskerLeftBiprodIso`, `whiskerRightBiprodIso`;
* `shId`, `shPow`, `homogEval2`, `homogEval3`: degree bookkeeping and homogeneous polynomial
  evaluation for shifted 2-morphisms (used to state the KLR relations in `QStrong`).
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Module
open KrullSchmidtCat (HomFinite)

universe w v u

/-! ## Dimensions of Hom spaces in a `k`-linear category -/

section HomDim

variable (k : Type*) [Field k] {C : Type*} [Category C] [Preadditive C] [Linear k C]

/-- Isomorphic objects have Hom spaces of the same dimension. -/
theorem finrank_hom_congr {X X' Y Y' : C} (e : X ≅ X') (f : Y ≅ Y') :
    finrank k (X ⟶ Y) = finrank k (X' ⟶ Y') :=
  (Linear.homCongr k e f).finrank_eq

theorem finrank_hom_congr_left {X X' : C} (e : X ≅ X') (Y : C) :
    finrank k (X ⟶ Y) = finrank k (X' ⟶ Y) :=
  finrank_hom_congr k e (Iso.refl Y)

theorem finrank_hom_congr_right (X : C) {Y Y' : C} (f : Y ≅ Y') :
    finrank k (X ⟶ Y) = finrank k (X ⟶ Y') :=
  finrank_hom_congr k (Iso.refl X) f

theorem finrank_hom_of_isZero_left {X : C} (h : IsZero X) (Y : C) : finrank k (X ⟶ Y) = 0 := by
  haveI : Subsingleton (X ⟶ Y) := ⟨fun f g => h.eq_of_src f g⟩
  exact finrank_zero_of_subsingleton

theorem finrank_hom_of_isZero_right (X : C) {Y : C} (h : IsZero Y) : finrank k (X ⟶ Y) = 0 := by
  haveI : Subsingleton (X ⟶ Y) := ⟨fun f g => h.eq_of_tgt f g⟩
  exact finrank_zero_of_subsingleton

section Biprod

variable [HasBinaryBiproducts C]

/-- `Hom(X ⊞ X', Y) ≅ Hom(X, Y) × Hom(X', Y)`. -/
@[simps]
def biprodLeftEquiv (X X' Y : C) : (X ⊞ X' ⟶ Y) ≃ₗ[k] (X ⟶ Y) × (X' ⟶ Y) where
  toFun f := (biprod.inl ≫ f, biprod.inr ≫ f)
  invFun ab := biprod.desc ab.1 ab.2
  map_add' f g := by simp
  map_smul' c f := by simp
  left_inv f := by apply biprod.hom_ext' <;> simp
  right_inv ab := by simp

variable [HomFinite k C]

theorem finrank_hom_biprod_left (X X' Y : C) :
    finrank k (X ⊞ X' ⟶ Y) = finrank k (X ⟶ Y) + finrank k (X' ⟶ Y) := by
  rw [(biprodLeftEquiv k X X' Y).finrank_eq, Module.finrank_prod]

theorem finrank_hom_biprod_right (X Y Y' : C) :
    finrank k (X ⟶ Y ⊞ Y') = finrank k (X ⟶ Y) + finrank k (X ⟶ Y') := by
  rw [(KrullSchmidtCat.biprodEquiv k X Y Y').finrank_eq, Module.finrank_prod]

end Biprod

section Shift

variable [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor C n).Linear k]

/-- The grading shift `⟨n⟩` is a linear isomorphism on Hom spaces. -/
def shiftHomEquiv (X Y : C) (n : ℤ) : (X ⟶ Y) ≃ₗ[k] (X⟦n⟧ ⟶ Y⟦n⟧) :=
  LinearEquiv.ofBijective ((shiftFunctor C n).mapLinearMap k)
    ⟨(shiftFunctor C n).map_injective, (shiftFunctor C n).map_surjective⟩

theorem finrank_hom_shift (X Y : C) (n : ℤ) :
    finrank k (X⟦n⟧ ⟶ Y⟦n⟧) = finrank k (X ⟶ Y) :=
  (shiftHomEquiv k X Y n).finrank_eq.symm

/-- `Hom(X⟨a⟩, Y) ≅ Hom(X, Y⟨b⟩)` when `a + b = 0`. -/
theorem finrank_hom_shift_left (X Y : C) {a b : ℤ} (h : a + b = 0) :
    finrank k (X⟦a⟧ ⟶ Y) = finrank k (X ⟶ Y⟦b⟧) := by
  have e : Y ≅ (Y⟦b⟧)⟦a⟧ := ((shiftFunctorCompIsoId C b a (by omega)).app Y).symm
  rw [finrank_hom_congr_right k _ e, finrank_hom_shift]

/-- `Hom(X, Y⟨a⟩) ≅ Hom(X⟨b⟩, Y)` when `a + b = 0`. -/
theorem finrank_hom_shift_right (X Y : C) {a b : ℤ} (h : a + b = 0) :
    finrank k (X ⟶ Y⟦a⟧) = finrank k (X⟦b⟧ ⟶ Y) := by
  have e : X ≅ (X⟦b⟧)⟦a⟧ := ((shiftFunctorCompIsoId C b a (by omega)).app X).symm
  rw [finrank_hom_congr_left k e, finrank_hom_shift]

/-- `Hom^b(X⟨a⟩, Y) = Hom^{b-a}(X, Y)`: `Hom(X⟨a⟩, Y⟨b⟩) ≅ Hom(X, Y⟨c⟩)` when `c + a = b`. -/
theorem finrank_hom_shift_shift (X Y : C) {a b c : ℤ} (h : c + a = b) :
    finrank k (X⟦a⟧ ⟶ Y⟦b⟧) = finrank k (X ⟶ Y⟦c⟧) := by
  have e : Y⟦b⟧ ≅ (Y⟦c⟧)⟦a⟧ := (shiftFunctorAdd' C c a b h).app Y
  rw [finrank_hom_congr_right k _ e, finrank_hom_shift]

omit [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor C n).Linear k] in
theorem finrank_hom_shift_zero (X Y : C) {a : ℤ} (h : a = 0) :
    finrank k (X ⟶ Y⟦a⟧) = finrank k (X ⟶ Y) := by
  subst h
  exact finrank_hom_congr_right k X ((shiftFunctorZero C ℤ).app Y)

omit [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor C n).Linear k] in
theorem finrank_hom_shift_congr (X Y : C) {a b : ℤ} (h : a = b) :
    finrank k (X ⟶ Y⟦a⟧) = finrank k (X ⟶ Y⟦b⟧) := by
  subst h; rfl

end Shift

end HomDim

/-! ## Additive functors, zero objects and finite direct sums -/

section Sums

variable {C : Type*} [Category C] [Preadditive C]

/-- An additive functor preserves binary biproducts (explicit isomorphism). -/
def mapBiprodIso {D : Type*} [Category D] [Preadditive D] [HasBinaryBiproducts C]
    [HasBinaryBiproducts D] (F : C ⥤ D) [F.Additive] (X Y : C) :
    F.obj (X ⊞ Y) ≅ F.obj X ⊞ F.obj Y :=
  KrullSchmidtCat.isoOfData (F.map biprod.inl) (F.map biprod.fst) (F.map biprod.inr)
    (F.map biprod.snd) (by rw [← F.map_comp, biprod.inl_fst, F.map_id])
    (by rw [← F.map_comp, biprod.inr_snd, F.map_id])
    (by rw [← F.map_comp, biprod.inl_snd, F.map_zero])
    (by rw [← F.map_comp, biprod.inr_fst, F.map_zero])
    (by rw [← F.map_comp, ← F.map_comp, ← F.map_add, biprod.total, F.map_id])

variable [HasZeroObject C] [HasBinaryBiproducts C]

open ZeroObject

/-- The direct sum `X₁ ⊕ (X₂ ⊕ (⋯ ⊕ 0))` of a list of objects. -/
def lsum : List C → C
  | [] => 0
  | X :: L => X ⊞ lsum L

@[simp] theorem lsum_nil : lsum ([] : List C) = 0 := rfl

@[simp] theorem lsum_cons (X : C) (L : List C) : lsum (X :: L) = (X ⊞ lsum L) := rfl

/-- Termwise isomorphic lists have isomorphic sums. -/
def lsumMapIso {ι : Type*} (L : List ι) (f g : ι → C) (e : ∀ i, f i ≅ g i) :
    lsum (L.map f) ≅ lsum (L.map g) :=
  match L with
  | [] => Iso.refl _
  | i :: L => biprod.mapIso (e i) (lsumMapIso L f g e)

/-- An additive functor commutes with `lsum`. -/
def mapLsumIso {D : Type*} [Category D] [Preadditive D] [HasZeroObject D]
    [HasBinaryBiproducts D] (F : C ⥤ D) [F.Additive] : ∀ L : List C,
    F.obj (lsum L) ≅ lsum (L.map fun X => F.obj X)
  | [] => (F.map_isZero (isZero_zero C)).isoZero
  | X :: L => mapBiprodIso F X (lsum L) ≪≫ biprod.mapIso (Iso.refl _) (mapLsumIso F L)

/-- An additive functor commutes with `lsum` of a mapped list. -/
def mapLsumMapIso {D : Type*} [Category D] [Preadditive D] [HasZeroObject D]
    [HasBinaryBiproducts D] (F : C ⥤ D) [F.Additive] {ι : Type*} : ∀ (L : List ι) (f : ι → C),
    F.obj (lsum (L.map f)) ≅ lsum (L.map fun i => F.obj (f i))
  | [], _ => (F.map_isZero (isZero_zero C)).isoZero
  | i :: L, f => mapBiprodIso F (f i) _ ≪≫ biprod.mapIso (Iso.refl _) (mapLsumMapIso F L f)

variable (k : Type*) [Field k] [Linear k C] [HomFinite k C]

theorem finrank_hom_lsum_left : ∀ (L : List C) (Y : C),
    finrank k (lsum L ⟶ Y) = (L.map fun X => finrank k (X ⟶ Y)).sum
  | [], Y => finrank_hom_of_isZero_left k (isZero_zero C) Y
  | X :: L, Y => by
    rw [lsum_cons, finrank_hom_biprod_left, finrank_hom_lsum_left L Y, List.map_cons,
      List.sum_cons]

theorem finrank_hom_lsum_right : ∀ (X : C) (L : List C),
    finrank k (X ⟶ lsum L) = (L.map fun Y => finrank k (X ⟶ Y)).sum
  | X, [] => finrank_hom_of_isZero_right k X (isZero_zero C)
  | X, Y :: L => by
    rw [lsum_cons, finrank_hom_biprod_right, finrank_hom_lsum_right X L, List.map_cons,
      List.sum_cons]

theorem list_sum_map_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∀ n : ℕ, ((List.range n).map f).sum = ∑ j ∈ Finset.range n, f j
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, list_sum_map_range f n,
      Finset.sum_range_succ]
    simp

variable [HasShift C ℤ]

/-- **The direct sum over a quantum integer** (CL §2.1.2, `sec:categories`):
`⊕_{[n]_i} X = ⊕_{j=0}^{n-1} X⟨d_i (n - 1 - 2j)⟩`, here with `d = d_i`. -/
def qsum (d : ℤ) (n : ℕ) (X : C) : C :=
  lsum ((List.range n).map fun j : ℕ => X⟦d * ((n : ℤ) - 1 - 2 * (j : ℤ))⟧)

theorem finrank_hom_qsum_left (d : ℤ) (n : ℕ) (X Y : C) :
    finrank k (qsum d n X ⟶ Y) =
      ∑ j ∈ Finset.range n, finrank k (X⟦d * ((n : ℤ) - 1 - 2 * (j : ℤ))⟧ ⟶ Y) := by
  rw [qsum, finrank_hom_lsum_left, List.map_map, list_sum_map_range]
  rfl

theorem finrank_hom_qsum_right (d : ℤ) (n : ℕ) (X Y : C) :
    finrank k (X ⟶ qsum d n Y) =
      ∑ j ∈ Finset.range n, finrank k (X ⟶ Y⟦d * ((n : ℤ) - 1 - 2 * (j : ℤ))⟧) := by
  rw [qsum, finrank_hom_lsum_right, List.map_map, list_sum_map_range]
  rfl

end Sums

/-! ## Shifted morphisms: scalars, powers, homogeneous polynomial evaluation -/

section ShiftedHomAlg

variable {C : Type*} [Category C] [Preadditive C] [HasShift C ℤ]

/-- `ShiftedHom X Y n = Hom(X, Y⟨n⟩)` is a `k`-module. -/
instance ShiftedHom.instModule (k : Type*) [Field k] [Linear k C] (X Y : C) (n : ℤ) :
    Module k (ShiftedHom X Y n) :=
  inferInstanceAs (Module k (X ⟶ Y⟦n⟧))

/-- The identity as a shifted morphism of degree `0`. -/
def shId (X : C) : ShiftedHom X X (0 : ℤ) := ShiftedHom.mk₀ 0 rfl (𝟙 X)

/-- Transport of a shifted morphism along an equality of degrees. -/
def shCast {X Y : C} {a b : ℤ} (f : ShiftedHom X Y a) (h : a = b) : ShiftedHom X Y b := h ▸ f

/-- Powers `f^n` of a shifted endomorphism `f` of degree `d`, of degree `n d` (`f^0 = 1`,
`f^{n+1} = f^n` followed by `f`). -/
def shPow {X : C} {d : ℤ} (f : ShiftedHom X X d) : (n : ℕ) → ShiftedHom X X ((n : ℤ) * d)
  | 0 => ShiftedHom.mk₀ _ (by simp) (𝟙 X)
  | n + 1 => (shPow f n).comp f (by push_cast; ring)

/-- The monomial `x^p y^q` (first `x^p`, then `y^q`) in two shifted endomorphisms. -/
def shMono2 {X : C} {d₁ d₂ : ℤ} (x : ShiftedHom X X d₁) (y : ShiftedHom X X d₂) (p q : ℕ) :
    ShiftedHom X X ((p : ℤ) * d₁ + (q : ℤ) * d₂) :=
  (shPow x p).comp (shPow y q) (by ring)

/-- The monomial `x^p y^q z^r` in three shifted endomorphisms. -/
def shMono3 {X : C} {d₁ d₂ d₃ : ℤ} (x : ShiftedHom X X d₁) (y : ShiftedHom X X d₂)
    (z : ShiftedHom X X d₃) (p q r : ℕ) :
    ShiftedHom X X ((p : ℤ) * d₁ + (q : ℤ) * d₂ + (r : ℤ) * d₃) :=
  (shMono2 x y p q).comp (shPow z r) (by ring)

variable (k : Type*) [Field k] [Linear k C]

/-- **The degree-`deg` part of `P(x, y)`** for shifted endomorphisms `x`, `y` of degrees `d₁`,
`d₂`: `∑ c_{pq} x^p y^q` over the monomials of `P` of weighted degree `p d₁ + q d₂ = deg`. For a
polynomial `P` which is weighted homogeneous of degree `deg` (such as CL's `Q_{ij}`, see
`Diagrams/CL/Scalars.lean`) this is `P(x, y)`. -/
def homogEval2 {X : C} {d₁ d₂ : ℤ} (P : MvPolynomial (Fin 2) k) (x : ShiftedHom X X d₁)
    (y : ShiftedHom X X d₂) (deg : ℤ) : ShiftedHom X X deg :=
  ∑ m ∈ P.support, if h : (m 0 : ℤ) * d₁ + (m 1 : ℤ) * d₂ = deg then
    P.coeff m • shCast (shMono2 x y (m 0) (m 1)) h else 0

/-- The degree-`deg` part of `P(x, y, z)` for three shifted endomorphisms. -/
def homogEval3 {X : C} {d₁ d₂ d₃ : ℤ} (P : MvPolynomial (Fin 3) k) (x : ShiftedHom X X d₁)
    (y : ShiftedHom X X d₂) (z : ShiftedHom X X d₃) (deg : ℤ) : ShiftedHom X X deg :=
  ∑ m ∈ P.support, if h : (m 0 : ℤ) * d₁ + (m 1 : ℤ) * d₂ + (m 2 : ℤ) * d₃ = deg then
    P.coeff m • shCast (shMono3 x y z (m 0) (m 1) (m 2)) h else 0

end ShiftedHomAlg

/-! ## Graded additive `k`-linear bicategories -/

section GradedBicategory

variable (B : Type u) [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ]

/-- **A graded additive bicategory** (CL §2.1.2, `sec:categories`): the Hom categories are
preadditive and carry the grading shift `⟨1⟩` (a `HasShift (a ⟶ b) ℤ` instance, with additive shift
functors), and "the composition maps `Hom(A, B) × Hom(B, C) → Hom(A, C)` form graded additive
functors": for every 1-morphism `f`, whiskering by `f` on either side is an additive functor
commuting with the shift (`Functor.CommShift`). -/
class GradedBicategory where
  precomp_additive {a b : B} (c : B) (f : a ⟶ b) : (precomp c f).Additive
  postcomp_additive (a : B) {b c : B} (g : b ⟶ c) : (postcomp a g).Additive
  shift_additive (a b : B) (n : ℤ) : (shiftFunctor (a ⟶ b) n).Additive
  precomp_commShift {a b : B} (c : B) (f : a ⟶ b) : (precomp c f).CommShift ℤ
  postcomp_commShift (a : B) {b c : B} (g : b ⟶ c) : (postcomp a g).CommShift ℤ

attribute [instance] GradedBicategory.precomp_additive GradedBicategory.postcomp_additive
  GradedBicategory.shift_additive GradedBicategory.precomp_commShift
  GradedBicategory.postcomp_commShift

/-- **A graded additive `k`-linear bicategory**: the Hom categories are `k`-linear and whiskering
and the grading shifts are `k`-linear functors. -/
class GradedBicategory.IsLinear (k : Type*) [Field k] [∀ a b : B, Linear k (a ⟶ b)] : Prop where
  precomp_linear {a b : B} (c : B) (f : a ⟶ b) : (precomp c f).Linear k
  postcomp_linear (a : B) {b c : B} (g : b ⟶ c) : (postcomp a g).Linear k
  shift_linear (a b : B) (n : ℤ) : (shiftFunctor (a ⟶ b) n).Linear k

attribute [instance] GradedBicategory.IsLinear.precomp_linear
  GradedBicategory.IsLinear.postcomp_linear GradedBicategory.IsLinear.shift_linear

variable {B} [GradedBicategory B]

section Whisker

variable {a b c : B}

@[simp] theorem whiskerLeft_add (f : a ⟶ b) {g h : b ⟶ c} (η θ : g ⟶ h) :
    f ◁ (η + θ) = f ◁ η + f ◁ θ :=
  (precomp c f).map_add

@[simp] theorem add_whiskerRight {f g : a ⟶ b} (η θ : f ⟶ g) (h : b ⟶ c) :
    (η + θ) ▷ h = η ▷ h + θ ▷ h :=
  (postcomp a h).map_add

@[simp] theorem whiskerLeft_zero' (f : a ⟶ b) (g h : b ⟶ c) : f ◁ (0 : g ⟶ h) = 0 :=
  (precomp c f).map_zero g h

@[simp] theorem zero_whiskerRight' (f g : a ⟶ b) (h : b ⟶ c) : (0 : f ⟶ g) ▷ h = 0 :=
  (postcomp a h).map_zero f g

variable (k : Type*) [Field k] [∀ a b : B, Linear k (a ⟶ b)] [GradedBicategory.IsLinear B k]

omit [GradedBicategory B] in
@[simp] theorem whiskerLeft_smul (f : a ⟶ b) {g h : b ⟶ c} (r : k) (η : g ⟶ h) :
    f ◁ (r • η) = r • (f ◁ η) :=
  (precomp c f).map_smul r η

omit [GradedBicategory B] in
@[simp] theorem smul_whiskerRight {f g : a ⟶ b} (r : k) (η : f ⟶ g) (h : b ⟶ c) :
    (r • η) ▷ h = r • (η ▷ h) :=
  (postcomp a h).map_smul r η

end Whisker

section Isos

variable {a b c : B}

/-- `f (g⟨n⟩) ≅ (f g)⟨n⟩` (Mathlib order: `f ≫ g⟦n⟧ ≅ (f ≫ g)⟦n⟧`). -/
def whiskerLeftShiftIso (f : a ⟶ b) (g : b ⟶ c) (n : ℤ) : f ≫ g⟦n⟧ ≅ (f ≫ g)⟦n⟧ :=
  ((precomp c f).commShiftIso n).app g

/-- `f⟦n⟧ ≫ g ≅ (f ≫ g)⟦n⟧`. -/
def whiskerRightShiftIso (f : a ⟶ b) (g : b ⟶ c) (n : ℤ) : f⟦n⟧ ≫ g ≅ (f ≫ g)⟦n⟧ :=
  ((postcomp a g).commShiftIso n).app f

/-- `𝟙 ⟦n⟧ ≫ g ≅ g⟦n⟧`. -/
def idShiftCompIso (g : a ⟶ b) (n : ℤ) : (𝟙 a)⟦n⟧ ≫ g ≅ g⟦n⟧ :=
  whiskerRightShiftIso (𝟙 a) g n ≪≫ (shiftFunctor _ n).mapIso (λ_ g)

/-- `f ≫ 𝟙 ⟦n⟧ ≅ f⟦n⟧`. -/
def compIdShiftIso (f : a ⟶ b) (n : ℤ) : f ≫ (𝟙 b)⟦n⟧ ≅ f⟦n⟧ :=
  whiskerLeftShiftIso f (𝟙 b) n ≪≫ (shiftFunctor _ n).mapIso (ρ_ f)

theorem isZero_comp_left {f : a ⟶ b} (hf : IsZero f) (g : b ⟶ c) : IsZero (f ≫ g) :=
  (postcomp a g).map_isZero hf

theorem isZero_comp_right (f : a ⟶ b) {g : b ⟶ c} (hg : IsZero g) : IsZero (f ≫ g) :=
  (precomp c f).map_isZero hg

/-- If the identity 1-morphism of `a` is zero (`a` is a *zero object* in CL's sense, "Important
convention" after Definition 1.2) then every 1-morphism out of `a` is zero. -/
theorem isZero_of_isZero_id_src (h : IsZero (𝟙 a)) (f : a ⟶ b) : IsZero f :=
  (isZero_comp_left h f).of_iso (λ_ f).symm

/-- Every 1-morphism into a zero object is zero. -/
theorem isZero_of_isZero_id_tgt (h : IsZero (𝟙 b)) (f : a ⟶ b) : IsZero f :=
  (isZero_comp_right f h).of_iso (ρ_ f).symm

/-- `𝟙⟦p⟧ ≫ Y⟦q⟧ ≅ Y⟦s⟧` for `q + p = s`. -/
def idShiftCompShiftIso (Y : a ⟶ b) {p q s : ℤ} (h : q + p = s) : (𝟙 a)⟦p⟧ ≫ Y⟦q⟧ ≅ Y⟦s⟧ :=
  idShiftCompIso (Y⟦q⟧) p ≪≫ ((shiftFunctorAdd' _ q p s h).app Y).symm

/-- `X⟦p⟧ ≫ Y⟦q⟧ ≅ (X ≫ Y)⟦s⟧` for `q + p = s`. -/
def shiftCompShiftIso (X : a ⟶ b) (Y : b ⟶ c) {p q s : ℤ} (h : q + p = s) :
    X⟦p⟧ ≫ Y⟦q⟧ ≅ (X ≫ Y)⟦s⟧ :=
  whiskerRightShiftIso X (Y⟦q⟧) p ≪≫ (shiftFunctor _ p).mapIso (whiskerLeftShiftIso X Y q) ≪≫
    ((shiftFunctorAdd' _ q p s h).app (X ≫ Y)).symm

/-- Left whiskering of a shifted 2-morphism `η : g ⟶ h⟨n⟩`: `f ◁ η : f ≫ g ⟶ (f ≫ h)⟨n⟩`. -/
def shWhiskerLeft (f : a ⟶ b) {g h : b ⟶ c} {n : ℤ} (η : ShiftedHom g h n) :
    ShiftedHom (f ≫ g) (f ≫ h) n :=
  η.map (precomp c f)

/-- Right whiskering of a shifted 2-morphism `η : f ⟶ g⟨n⟩`: `η ▷ h : f ≫ h ⟶ (g ≫ h)⟨n⟩`. -/
def shWhiskerRight {f g : a ⟶ b} {n : ℤ} (η : ShiftedHom f g n) (h : b ⟶ c) :
    ShiftedHom (f ≫ h) (g ≫ h) n :=
  η.map (postcomp a h)

variable [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]

/-- `f (Y ⊕ Y') ≅ f Y ⊕ f Y'`. -/
def whiskerLeftBiprodIso (f : a ⟶ b) (Y Y' : b ⟶ c) : f ≫ (Y ⊞ Y') ≅ (f ≫ Y) ⊞ (f ≫ Y') :=
  mapBiprodIso (precomp c f) Y Y'

/-- `(X ⊕ X') g ≅ X g ⊕ X' g`. -/
def whiskerRightBiprodIso (X X' : a ⟶ b) (g : b ⟶ c) : (X ⊞ X') ≫ g ≅ (X ≫ g) ⊞ (X' ≫ g) :=
  mapBiprodIso (postcomp a g) X X'

variable [∀ a b : B, HasZeroObject (a ⟶ b)]

/-- `(⊕_{[n]} 1) X ≅ ⊕_{[n]} X`. -/
def qsumCompIso (d : ℤ) (n : ℕ) (X : b ⟶ c) : qsum d n (𝟙 b) ≫ X ≅ qsum d n X :=
  mapLsumMapIso (postcomp b X) _ _ ≪≫ lsumMapIso _ _ _ fun _ => idShiftCompIso X _

/-- `X (⊕_{[n]} 1) ≅ ⊕_{[n]} X`. -/
def compQsumIso (d : ℤ) (n : ℕ) (X : a ⟶ b) : X ≫ qsum d n (𝟙 b) ≅ qsum d n X :=
  mapLsumMapIso (precomp b X) _ _ ≪≫ lsumMapIso _ _ _ fun _ => compIdShiftIso X _

end Isos

/-! ### Adjunctions -/

section Adjunction

variable {a b c : B}

/-- An adjunction between zero 1-morphisms (unit and counit zero). This is the "vacuous" case
of CL's adjoint induction hypothesis beyond the highest weight. -/
def adjunctionOfIsZero {u : a ⟶ b} {v : b ⟶ a} (hu : IsZero u) (hv : IsZero v) : u ⊣ v where
  unit := 0
  counit := 0
  left_triangle := (isZero_comp_left hu _).eq_of_tgt _ _
  right_triangle := (isZero_comp_right _ hv).eq_of_tgt _ _

variable (k : Type*) [Field k] [∀ a b : B, Linear k (a ⟶ b)] [GradedBicategory.IsLinear B k]

/-- Mathlib's mate bijection is `k`-linear. -/
def mateLinearEquiv {c d e f : B} {g : c ⟶ e} {h : d ⟶ f} {l₁ : c ⟶ d} {r₁ : d ⟶ c}
    {l₂ : e ⟶ f} {r₂ : f ⟶ e} (adj₁ : l₁ ⊣ r₁) (adj₂ : l₂ ⊣ r₂) :
    (g ≫ l₂ ⟶ l₁ ≫ h) ≃ₗ[k] (r₁ ≫ g ⟶ h ≫ r₂) :=
  { mateEquiv adj₁ adj₂ with
    map_add' := fun α β => by
      simp only [Equiv.toFun_as_coe, Bicategory.mateEquiv_apply, bicategoricalComp, whiskerLeft_add,
        add_whiskerRight, Preadditive.add_comp, Preadditive.comp_add]
    map_smul' := fun r α => by
      simp only [Equiv.toFun_as_coe, Bicategory.mateEquiv_apply, bicategoricalComp, whiskerLeft_smul,
        smul_whiskerRight, Linear.smul_comp, Linear.comp_smul, RingHom.id_apply] }

/-- The adjunction isomorphism `Hom(u x, y) ≅ Hom(x, u_R y)` of CL §3.2 (`u ⊣ v`, Mathlib order:
`Hom(x ≫ u, y) ≅ Hom(x, y ≫ v)`). -/
def Adj.homEquivLeft {u : a ⟶ b} {v : b ⟶ a} (adj : u ⊣ v) (x : c ⟶ a) (y : c ⟶ b) :
    (x ≫ u ⟶ y) ≃ₗ[k] (x ⟶ y ≫ v) :=
  Linear.homCongr k (Iso.refl _) (λ_ y).symm ≪≫ₗ mateLinearEquiv k (Adjunction.id c) adj ≪≫ₗ
    Linear.homCongr k (λ_ x) (Iso.refl _)

/-- The adjunction isomorphism `Hom(x, y v_L) ≅ Hom(x v, y)`, i.e. for `u ⊣ v`
`Hom(x, u ≫ y) ≅ Hom(v ≫ x, y)` (Mathlib order). -/
def Adj.homEquivRight {u : a ⟶ b} {v : b ⟶ a} (adj : u ⊣ v) (x : a ⟶ c) (y : b ⟶ c) :
    (x ⟶ u ≫ y) ≃ₗ[k] (v ≫ x ⟶ y) :=
  Linear.homCongr k (ρ_ x).symm (Iso.refl _) ≪≫ₗ mateLinearEquiv k adj (Adjunction.id c) ≪≫ₗ
    Linear.homCongr k (Iso.refl _) (ρ_ y)

/-- **Dimension-level adjunction.** `DimAdj k u v` records the two families of dimension
equalities `dim Hom(x ≫ u, y) = dim Hom(x, y ≫ v)` and `dim Hom(x, u ≫ y) = dim Hom(v ≫ x, y)`
given by an adjunction `u ⊣ v` (CL §3.2, the four isomorphisms displayed before `eq:ind_hyp`
are these two, for `u ⊣ u_R` and for `u_L ⊣ u`). Unlike `u ⊣ v` it is stable under grading
shifts without any coherence between the shift and composition (`DimAdj.shift`), which is all
that the dimension counts of CL §3.2 use. -/
structure DimAdj (u : a ⟶ b) (v : b ⟶ a) : Prop where
  left : ∀ {c : B} (x : c ⟶ a) (y : c ⟶ b), finrank k (x ≫ u ⟶ y) = finrank k (x ⟶ y ≫ v)
  right : ∀ {c : B} (x : a ⟶ c) (y : b ⟶ c), finrank k (x ⟶ u ≫ y) = finrank k (v ≫ x ⟶ y)

theorem Adj.dimAdj {u : a ⟶ b} {v : b ⟶ a} (adj : u ⊣ v) : DimAdj k u v where
  left x y := (Adj.homEquivLeft k adj x y).finrank_eq
  right x y := (Adj.homEquivRight k adj x y).finrank_eq

variable {k}

omit [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B] [GradedBicategory.IsLinear B k] in
theorem DimAdj.of_iso {u u' : a ⟶ b} {v v' : b ⟶ a} (h : DimAdj k u v) (eu : u ≅ u')
    (ev : v ≅ v') : DimAdj k u' v' where
  left x y := by
    rw [← finrank_hom_congr_left k (whiskerLeftIso x eu), h.left,
      finrank_hom_congr_right k x (whiskerLeftIso y ev)]
  right x y := by
    rw [← finrank_hom_congr_right k x (whiskerRightIso eu y), h.right,
      finrank_hom_congr_left k (whiskerRightIso ev x)]

/-- **Adjunctions shift**: if `u ⊣ v` (at the level of Hom dimensions) then
`u⟨n⟩ ⊣ v⟨-n⟩`; e.g. CL §3.2: `(E 1_n)_R = 1_n F ⟨n+1⟩` gives `(1_n F)_L = E 1_n ⟨n+1⟩`. -/
theorem DimAdj.shift {u : a ⟶ b} {v : b ⟶ a} (h : DimAdj k u v) {m n : ℤ} (hmn : m + n = 0) :
    DimAdj k (u⟦m⟧) (v⟦n⟧) where
  left x y := by
    rw [finrank_hom_congr_left k (whiskerLeftShiftIso x u m),
      finrank_hom_shift_left k _ _ hmn, h.left,
      finrank_hom_congr_right k x (whiskerLeftShiftIso y v n),
      finrank_hom_congr_right k x (whiskerRightShiftIso y v n)]
  right x y := by
    rw [finrank_hom_congr_right k x (whiskerRightShiftIso u y m),
      finrank_hom_shift_right k _ _ hmn, h.right,
      finrank_hom_congr_left k (whiskerRightShiftIso v x n),
      finrank_hom_congr_left k (whiskerLeftShiftIso v x n)]

end Adjunction

end GradedBicategory

end Categorification.TwoRep

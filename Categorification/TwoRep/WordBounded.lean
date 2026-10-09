/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.Sl2

/-!
# Words in `E`, `F` and the boundedness hypothesis (BB_w)

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, §3. In Definition 1.2 (`def_Qstrong`) the spaces of 2-morphisms
`Hom(X, Y)` between 1-morphisms are finite dimensional; by the conventions of §2.1.2
(`sec:categories`), `Hom(X, Y)` is the space of degree-zero maps and `Hom^l(X, Y) = Hom(X, Y⟨l⟩)`,
so this is finiteness in each degree. Nothing in Definition 1.2 bounds the degrees `l` in which
`Hom^l(X, Y)` is nonzero.

This file states the additional hypothesis used for the word-generated numerical
adjunction results motivated by CL Proposition 3.9 (`prop:lradj`). It does not prove the
full proposition or Theorem 1.1:

**(BB_w)** for all words `X`, `Z` in the 1-morphisms `E 1_n`, `1_n F` (composites, with the same
source and target), `finrank k Hom(X, Z⟨d⟩) = 0` for `d ≪ 0`, with a separate bound
for each pair. Under `HomFinite`, this is equivalent to vanishing of the Hom spaces.

The hypothesis is imposed separately; no implication from biadjointness or general
graded-bimodule realizations is proved here.

## Main declarations

* `HomBddBelow k X Z`: eventual vanishing of finranks in negative degrees (actual
  Hom-space vanishing under `HomFinite`); closure
  properties (isomorphisms, shifts, direct sums, retracts).
* `StrongSl2.Word S r s X`: the 1-morphism `X : obj r ⟶ obj s` is a word in `E`, `F` (identities
  and arbitrary bracketings allowed).
* `StrongSl2.BBw S`: the hypothesis (BB_w).
* `StrongSl2.WordGen S r s X`: `X` is *word-generated*: obtained from words by composition, grading
  shifts, finite direct sums and passing to retracts (in particular direct summands and isomorphic
  1-morphisms).
* `StrongSl2.bbw`, `StrongSl2.homBddBelow_wordGen` (`BBwProof.lean`): (BB_w) holds in every
  strong 2-representation, and graded Hom spaces between word-generated 1-morphisms are bounded
  below.
* `StrongSl2.NumAdj S r`: the numerical shadow of the adjoint induction hypothesis (3.2) at the
  weight `wt r`, on word-generated test 1-morphisms; `AdjHyp.numAdj`.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Module
open KrullSchmidtCat (HomFinite)
open ZeroObject

universe w v u

/-! ## Graded Hom spaces bounded below -/

section HomBddBelow

variable (k : Type*) [Field k] {C : Type*} [Category C] [Preadditive C] [Linear k C]
  [HasShift C ℤ]

/-- The finranks of `Hom(X, Z⟨d⟩)` vanish for `d ≪ 0`. Under `HomFinite k C`, this
means that the graded Hom space is bounded below. Without finite dimensionality,
vanishing finrank alone does not imply that the Hom space is zero. -/
def HomBddBelow (X Z : C) : Prop := ∃ N : ℤ, ∀ d : ℤ, d < N → finrank k (X ⟶ Z⟦d⟧) = 0

variable {k}

theorem HomBddBelow.of_iso {X X' Z Z' : C} (h : HomBddBelow k X Z) (e : X ≅ X') (f : Z ≅ Z') :
    HomBddBelow k X' Z' := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun d hd => by
    rw [← finrank_hom_congr k e ((shiftFunctor C d).mapIso f)]; exact hN d hd⟩

theorem HomBddBelow.of_isZero_left {X : C} (h : IsZero X) (Z : C) : HomBddBelow k X Z :=
  ⟨0, fun _ _ => finrank_hom_of_isZero_left k h _⟩

theorem HomBddBelow.of_isZero_right (X : C) {Z : C} (h : IsZero Z) : HomBddBelow k X Z :=
  ⟨0, fun d _ => finrank_hom_of_isZero_right k X ((shiftFunctor C d).map_isZero h)⟩

section Shifts

variable [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor C n).Linear k]

theorem HomBddBelow.shift_left {X Z : C} (h : HomBddBelow k X Z) (a : ℤ) :
    HomBddBelow k (X⟦a⟧) Z := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N + a, fun d hd => ?_⟩
  rw [finrank_hom_shift_shift k X Z (c := d - a) (by ring)]
  exact hN _ (by omega)

end Shifts

theorem HomBddBelow.shift_right {X Z : C} (h : HomBddBelow k X Z) (a : ℤ) :
    HomBddBelow k X (Z⟦a⟧) := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N - a, fun d hd => ?_⟩
  exact (finrank_hom_congr_right k X
    ((shiftFunctorAdd' C a d (a + d) rfl).app Z).symm).trans (hN _ (by omega))

section Finite

variable [HomFinite k C]

/-- A retract (in particular a direct summand) of the source keeps the graded Hom space bounded
below. -/
theorem HomBddBelow.of_retract_left {X Y Z : C} (h : HomBddBelow k Y Z) (i : X ⟶ Y) (p : Y ⟶ X)
    (hip : i ≫ p = 𝟙 X) : HomBddBelow k X Z := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun d hd => Nat.le_zero.1 ?_⟩
  rw [← hN d hd]
  refine LinearMap.finrank_le_finrank_of_injective (f := Linear.leftComp k (Z⟦d⟧) p) ?_
  intro f g hfg
  have := congrArg (fun φ => i ≫ φ) hfg
  simpa [Linear.leftComp, ← Category.assoc, hip] using this

/-- A retract of the target keeps the graded Hom space bounded below. -/
theorem HomBddBelow.of_retract_right {X Y Z : C} (h : HomBddBelow k X Y) (i : Z ⟶ Y) (p : Y ⟶ Z)
    (hip : i ≫ p = 𝟙 Z) : HomBddBelow k X Z := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun d hd => Nat.le_zero.1 ?_⟩
  rw [← hN d hd]
  refine LinearMap.finrank_le_finrank_of_injective (f := Linear.rightComp k X (i⟦d⟧')) ?_
  intro f g hfg
  have := congrArg (fun φ => φ ≫ p⟦d⟧') hfg
  simpa [Linear.rightComp, ← Functor.map_comp, hip] using this

variable [HasBinaryBiproducts C]

theorem HomBddBelow.biprod_left {X Y Z : C} (hX : HomBddBelow k X Z) (hY : HomBddBelow k Y Z) :
    HomBddBelow k (X ⊞ Y) Z := by
  obtain ⟨N, hN⟩ := hX
  obtain ⟨M, hM⟩ := hY
  refine ⟨min N M, fun d hd => ?_⟩
  rw [finrank_hom_biprod_left, hN d (lt_of_lt_of_le hd (min_le_left _ _)),
    hM d (lt_of_lt_of_le hd (min_le_right _ _))]

variable [∀ n : ℤ, (shiftFunctor C n).Additive]

theorem HomBddBelow.biprod_right {X Z W : C} (hZ : HomBddBelow k X Z) (hW : HomBddBelow k X W) :
    HomBddBelow k X (Z ⊞ W) := by
  obtain ⟨N, hN⟩ := hZ
  obtain ⟨M, hM⟩ := hW
  refine ⟨min N M, fun d hd => ?_⟩
  rw [finrank_hom_congr_right k X (mapBiprodIso (shiftFunctor C d) Z W), finrank_hom_biprod_right,
    hN d (lt_of_lt_of_le hd (min_le_left _ _)), hM d (lt_of_lt_of_le hd (min_le_right _ _))]

end Finite

end HomBddBelow

/-! ## Words and word-generated 1-morphisms -/

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]

namespace StrongSl2

/-- **Words in `E`, `F`**: the 1-morphisms `obj r ⟶ obj s` obtained from the identities, the
`E 1_n` and the `1_n F` by composition (with any bracketing). -/
inductive Word (S : StrongSl2 k B) : ∀ r s : ℤ, (S.obj r ⟶ S.obj s) → Prop
  | id (r : ℤ) : Word S r r (𝟙 (S.obj r))
  | E (r : ℤ) : Word S r (r + 1) (S.E r)
  | F (r : ℤ) : Word S (r + 1) r (S.F r)
  | comp {r s t : ℤ} {X : S.obj r ⟶ S.obj s} {Y : S.obj s ⟶ S.obj t} :
      Word S r s X → Word S s t Y → Word S r t (X ≫ Y)

/-- **The hypothesis (BB_w)**: the graded Hom spaces between words in `E`, `F` (with the same
source and target) have finrank zero for `d ≪ 0`, with a bound for each pair. Under
`HomFinite`, this is actual Hom-space vanishing; `homBddBelow_wordGen` extends it to
word-generated pairs.

It is not one of the conditions of CL Definition 1.2 (whose finiteness condition is degreewise),
but it follows from them (`StrongSl2.bbw`, `BBwProof.lean`). -/
def BBw (S : StrongSl2 k B) : Prop :=
  ∀ ⦃r s : ℤ⦄ ⦃X Z : S.obj r ⟶ S.obj s⦄, S.Word r s X → S.Word r s Z → HomBddBelow k X Z

/-- **Word-generated 1-morphisms**: the closure of the words in `E`, `F` under composition, grading
shifts, zero, binary direct sums and retracts (hence direct summands and isomorphisms). -/
inductive WordGen (S : StrongSl2 k B) : ∀ r s : ℤ, (S.obj r ⟶ S.obj s) → Prop
  | word {r s : ℤ} {X : S.obj r ⟶ S.obj s} : S.Word r s X → WordGen S r s X
  | zero (r s : ℤ) : WordGen S r s (0 : S.obj r ⟶ S.obj s)
  | biprod {r s : ℤ} {X Y : S.obj r ⟶ S.obj s} :
      WordGen S r s X → WordGen S r s Y → WordGen S r s (X ⊞ Y)
  | shift {r s : ℤ} {X : S.obj r ⟶ S.obj s} (a : ℤ) : WordGen S r s X → WordGen S r s (X⟦a⟧)
  | comp {r s t : ℤ} {X : S.obj r ⟶ S.obj s} {Y : S.obj s ⟶ S.obj t} :
      WordGen S r s X → WordGen S s t Y → WordGen S r t (X ≫ Y)
  | retract {r s : ℤ} {X Y : S.obj r ⟶ S.obj s} (i : X ⟶ Y) (p : Y ⟶ X) (hip : i ≫ p = 𝟙 X) :
      WordGen S r s Y → WordGen S r s X

variable {S : StrongSl2 k B}

namespace WordGen

theorem of_iso {r s : ℤ} {X Y : S.obj r ⟶ S.obj s} (h : S.WordGen r s X) (e : X ≅ Y) :
    S.WordGen r s Y :=
  .retract e.inv e.hom e.inv_hom_id h

theorem id (r : ℤ) : S.WordGen r r (𝟙 (S.obj r)) := .word (.id r)

theorem E (r : ℤ) : S.WordGen r (r + 1) (S.E r) := .word (.E r)

theorem F (r : ℤ) : S.WordGen (r + 1) r (S.F r) := .word (.F r)

theorem of_isZero {r s : ℤ} {X : S.obj r ⟶ S.obj s} (h : IsZero X) : S.WordGen r s X :=
  (WordGen.zero r s).of_iso (h.iso (isZero_zero _)).symm

theorem lsum {r s : ℤ} : ∀ (L : List (S.obj r ⟶ S.obj s)), (∀ X ∈ L, S.WordGen r s X) →
    S.WordGen r s (lsum L)
  | [], _ => .zero r s
  | X :: L, h => .biprod (h X (by simp)) (lsum L fun Y hY => h Y (by simp [hY]))

theorem qsum {r s : ℤ} {X : S.obj r ⟶ S.obj s} (h : S.WordGen r s X) (d : ℤ) (n : ℕ) :
    S.WordGen r s (qsum d n X) :=
  lsum _ fun Y hY => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hY
    exact .shift _ h

end WordGen

/-- The normal form of word-generated 1-morphisms: the closure of the *shifted words* under zero,
binary direct sums and retracts. (Auxiliary; see `WordGen.wordNF`.) -/
inductive WordNF (S : StrongSl2 k B) : ∀ r s : ℤ, (S.obj r ⟶ S.obj s) → Prop
  | shiftWord {r s : ℤ} {X : S.obj r ⟶ S.obj s} (a : ℤ) : S.Word r s X → WordNF S r s (X⟦a⟧)
  | zero (r s : ℤ) : WordNF S r s (0 : S.obj r ⟶ S.obj s)
  | biprod {r s : ℤ} {X Y : S.obj r ⟶ S.obj s} :
      WordNF S r s X → WordNF S r s Y → WordNF S r s (X ⊞ Y)
  | retract {r s : ℤ} {X Y : S.obj r ⟶ S.obj s} (i : X ⟶ Y) (p : Y ⟶ X) (hip : i ≫ p = 𝟙 X) :
      WordNF S r s Y → WordNF S r s X

namespace WordNF

theorem of_iso {r s : ℤ} {X Y : S.obj r ⟶ S.obj s} (h : S.WordNF r s X) (e : X ≅ Y) :
    S.WordNF r s Y :=
  .retract e.inv e.hom e.inv_hom_id h

theorem word {r s : ℤ} {X : S.obj r ⟶ S.obj s} (h : S.Word r s X) : S.WordNF r s X :=
  (WordNF.shiftWord 0 h).of_iso ((shiftFunctorZero _ ℤ).app X)

theorem shift {r s : ℤ} {X : S.obj r ⟶ S.obj s} (h : S.WordNF r s X) (b : ℤ) :
    S.WordNF r s (X⟦b⟧) := by
  induction h with
  | shiftWord a hW => exact (WordNF.shiftWord (a + b) hW).of_iso ((shiftFunctorAdd _ a b).app _)
  | zero =>
    exact (WordNF.zero r s).of_iso
      (((shiftFunctor _ b).map_isZero (isZero_zero _)).iso (isZero_zero _)).symm
  | biprod _ _ ihX ihY => exact (WordNF.biprod ihX ihY).of_iso (mapBiprodIso _ _ _).symm
  | retract i p hip _ ih =>
    exact .retract (i⟦b⟧') (p⟦b⟧') (by rw [← Functor.map_comp, hip, CategoryTheory.Functor.map_id]) ih

/-- A shifted word composed with a normal form is a normal form. -/
theorem shiftWord_comp {r s t : ℤ} {W : S.obj r ⟶ S.obj s} (hW : S.Word r s W) (a : ℤ)
    {Y : S.obj s ⟶ S.obj t} (hY : S.WordNF s t Y) : S.WordNF r t (W⟦a⟧ ≫ Y) := by
  induction hY with
  | shiftWord b hV =>
    exact (WordNF.shiftWord (b + a) (hW.comp hV)).of_iso (shiftCompShiftIso _ _ rfl).symm
  | zero =>
    exact (WordNF.zero r t).of_iso
      ((isZero_comp_right _ (isZero_zero _)).iso (isZero_zero _)).symm
  | biprod _ _ ihX ihY =>
    exact (WordNF.biprod ihX ihY).of_iso
      (whiskerLeftBiprodIso _ _ _).symm
  | retract i p hip _ ih =>
    exact .retract (_ ◁ i) (_ ◁ p)
      (by rw [← Bicategory.whiskerLeft_comp, hip, Bicategory.whiskerLeft_id]) ih

theorem comp {r s t : ℤ} {X : S.obj r ⟶ S.obj s} (hX : S.WordNF r s X) {Y : S.obj s ⟶ S.obj t}
    (hY : S.WordNF s t Y) : S.WordNF r t (X ≫ Y) := by
  induction hX with
  | shiftWord a hW => exact shiftWord_comp hW a hY
  | zero =>
    exact (WordNF.zero r t).of_iso
      ((isZero_comp_left (isZero_zero _) _).iso (isZero_zero _)).symm
  | biprod _ _ ihX ihY =>
    exact (WordNF.biprod ihX ihY).of_iso
      (whiskerRightBiprodIso _ _ _).symm
  | retract i p hip _ ih =>
    exact .retract (i ▷ _) (p ▷ _)
      (by rw [← Bicategory.comp_whiskerRight, hip, Bicategory.id_whiskerRight]) ih

end WordNF

/-- Every word-generated 1-morphism is a retract of a finite direct sum of shifted words. -/
theorem WordGen.wordNF {r s : ℤ} {X : S.obj r ⟶ S.obj s} (h : S.WordGen r s X) :
    S.WordNF r s X := by
  induction h with
  | word hW => exact .word hW
  | zero r s => exact .zero r s
  | biprod _ _ ihX ihY => exact .biprod ihX ihY
  | shift a _ ih => exact ih.shift a
  | comp _ _ ihX ihY => exact ihX.comp ihY
  | retract i p hip _ ih => exact .retract i p hip ih

theorem WordNF.wordGen {r s : ℤ} {X : S.obj r ⟶ S.obj s} (h : S.WordNF r s X) :
    S.WordGen r s X := by
  induction h with
  | shiftWord a hW => exact .shift a (.word hW)
  | zero => exact .zero r s
  | biprod _ _ ihX ihY => exact .biprod ihX ihY
  | retract i p hip _ ih => exact .retract i p hip ih

/-- **The numerical shadow of the adjoint induction hypothesis (3.2) at the weight `n = wt r`**
(CL §3.2, `eq:ind_hyp`): the two families of equalities of Hom-dimensions
`dim Hom(x ≫ F, y) = dim Hom(x, y ≫ E⟨-n-1⟩)` and `dim Hom(x, F ≫ y) = dim Hom(E⟨-n-1⟩ ≫ x, y)`
that the adjunction `1_n F ⊣ E 1_n ⟨-n-1⟩` would give (`AdjHyp.dimAdjF`), for *word-generated*
test 1-morphisms `x`, `y`. It follows from (3.2) at `n` (`AdjHyp.numAdj`), and it is all that the
dimension counts of CL §3.2 use of (3.2). Under the boundedness hypothesis (BB_w) it holds at
every weight (`StrongSl2.numAdj`, `WordNumerics.lean`). -/
structure NumAdj (S : StrongSl2 k B) (r : ℤ) : Prop where
  left : ∀ ⦃c : ℤ⦄ ⦃x : S.obj c ⟶ S.obj (r + 1)⦄ ⦃y : S.obj c ⟶ S.obj r⦄,
    S.WordGen c (r + 1) x → S.WordGen c r y →
      finrank k (x ≫ S.F r ⟶ y) = finrank k (x ⟶ y ≫ (S.E r)⟦-(S.wt r + 1)⟧)
  right : ∀ ⦃c : ℤ⦄ ⦃x : S.obj (r + 1) ⟶ S.obj c⦄ ⦃y : S.obj r ⟶ S.obj c⦄,
    S.WordGen (r + 1) c x → S.WordGen r c y →
      finrank k (x ⟶ S.F r ≫ y) = finrank k ((S.E r)⟦-(S.wt r + 1)⟧ ≫ x ⟶ y)

variable [GradedBicategory.IsLinear B k]

/-- The adjoint induction hypothesis (3.2) at `n` implies its numerical shadow. -/
theorem AdjHyp.numAdj {r : ℤ} (h : S.AdjHyp r) : S.NumAdj r where
  left _ x y _ _ := (h.dimAdjF S).left x y
  right _ x y _ _ := (h.dimAdjF S).right x y

end StrongSl2

end Categorification.TwoRep

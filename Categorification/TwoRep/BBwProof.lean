/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.NumericalTorsion
import Categorification.TwoRep.WordBounded

/-!
# The boundedness hypothesis (BB_w) is a theorem

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, §3. The results of CL §3 (Lemma 3.6, Proposition 3.9) are proved in this
library under the hypothesis (BB_w) (`StrongSl2.BBw`, `WordBounded.lean`): graded Hom spaces between
words in `E`, `F` vanish in degrees `d ≪ 0`. Here (BB_w) is derived from the conditions of CL
Definition 1.2 (`StrongSl2.bbw`). Only the formal adjunction `E 1_n ⊣ 1_n F ⟨n+1⟩`, the
isomorphisms (3), integrability, finite dimensionality of the 2-morphism spaces and
`Hom(1_n, 1_n⟨l⟩) = 0` for `l < 0` are used; the nilHecke action and the left adjoints are not.

## Proof

* **One-sided numerical adjunction** (`finrank_compF_of_bdd`): for word-generated `x`, `y`,
  `dim Hom(x ≫ F, y⟨d⟩) = dim Hom(x, (y ≫ E)⟨d - (n+1)⟩)` as soon as one of the two sides vanishes in
  degrees `d ≪ 0` (`Sl2CatData₀.finrank_f_eq_of_bdd`, `NumericalTorsion.lean`: the defect is
  quantum-integer torsion, and positivity of the quantum integers kills torsion sequences with a
  sign on a half-line).
* **Formal moves**: `dim Hom(x ≫ E, y⟨d⟩) = dim Hom(x, (y ≫ F)⟨d + n + 1⟩)` and
  `dim Hom(F ≫ x, y⟨d⟩) = dim Hom(x, (E ≫ y)⟨d + n + 1⟩)`, from `E ⊣ F⟨n+1⟩` alone.
* **Peeling** (`bdd_comp_word`): if `Hom(1, W)` is bounded below for all words `W` from the object
  `c` to itself, then so is `Hom(X, Z)` for all words `X`, `Z` with source `c`: letters are removed
  from the end of `X` by the formal move (for `E`) and the one-sided numerical adjunction (for `F`).
* **Normal form** (`NormalCl`, `NormalCl.of_word`): every word is, up to shifts, sums and
  retracts, either a word in `F` alone or of the form `Y ≫ E` (from (3): `E F 1_m` is a summand of `F E 1_m ⊕ ⊕ 1_m`).
* **Induction from the lowest weight** (`bdd_src`): for `W = Y ≫ E` with source `c`,
  `Hom(1, Y ≫ E)` is bounded below if `Hom(1 ≫ F, Y)` is (one-sided adjunction), i.e. if
  `Hom(1, E ≫ Y)` is, which is a statement at the source `c - 1`. The base case is `Hom(1_n, 1_n⟨l⟩) = 0`
  for `l < 0`.

## Main declarations

* `StrongSl2.bbw`: **every strong 2-representation of `sl₂` satisfies (BB_w).**
* `StrongSl2.homBddBelow_wordGen`: graded Hom spaces between word-generated 1-morphisms are
  bounded below.
-/

noncomputable section

namespace Categorification.TwoRep.StrongSl2

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Module
open KrullSchmidtCat (HomFinite)
open ZeroObject

universe w v u

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]

variable {S : StrongSl2 k B}

/-! ## A normal form for words -/

/-- Words in `F` alone. -/
inductive FWord (S : StrongSl2 k B) : ∀ r s : ℤ, (S.obj r ⟶ S.obj s) → Prop
  | id (r : ℤ) : FWord S r r (𝟙 (S.obj r))
  | snoc {r s : ℤ} {X : S.obj r ⟶ S.obj (s + 1)} : FWord S r (s + 1) X → FWord S r s (X ≫ S.F s)

theorem FWord.le {r s : ℤ} {X : S.obj r ⟶ S.obj s} (h : S.FWord r s X) : s ≤ r := by
  induction h with
  | id => exact le_rfl
  | snoc _ ih => omega

theorem FWord.word {r s : ℤ} {X : S.obj r ⟶ S.obj s} (h : S.FWord r s X) : S.Word r s X := by
  induction h with
  | id => exact .id _
  | snoc _ ih => exact ih.comp (.F _)

theorem FWord.eq_id {r : ℤ} {X : S.obj r ⟶ S.obj r} (h : S.FWord r r X) : X = 𝟙 _ := by
  cases h with
  | id => rfl
  | snoc h' => have := h'.le; omega

/-- **The normal-form closure**: words in `F` alone, words ending in `E` (`Y ≫ E` with `Y` in the
closure), closed under zero, sums, shifts and retracts. -/
inductive NormalCl (S : StrongSl2 k B) : ∀ r s : ℤ, (S.obj r ⟶ S.obj s) → Prop
  | pureF {r s : ℤ} {X : S.obj r ⟶ S.obj s} : S.FWord r s X → NormalCl S r s X
  | endE {r s : ℤ} {Y : S.obj r ⟶ S.obj s} : NormalCl S r s Y → NormalCl S r (s + 1) (Y ≫ S.E s)
  | zero (r s : ℤ) : NormalCl S r s (0 : S.obj r ⟶ S.obj s)
  | biprod {r s : ℤ} {X Y : S.obj r ⟶ S.obj s} : NormalCl S r s X → NormalCl S r s Y → NormalCl S r s (X ⊞ Y)
  | shift {r s : ℤ} {X : S.obj r ⟶ S.obj s} (a : ℤ) : NormalCl S r s X → NormalCl S r s (X⟦a⟧)
  | retract {r s : ℤ} {X Y : S.obj r ⟶ S.obj s} (i : X ⟶ Y) (p : Y ⟶ X) (hip : i ≫ p = 𝟙 X) :
      NormalCl S r s Y → NormalCl S r s X

namespace NormalCl

theorem of_iso {r s : ℤ} {X Y : S.obj r ⟶ S.obj s} (h : S.NormalCl r s X) (e : X ≅ Y) : S.NormalCl r s Y :=
  .retract e.inv e.hom e.inv_hom_id h

theorem lsum {r s : ℤ} : ∀ (L : List (S.obj r ⟶ S.obj s)), (∀ X ∈ L, S.NormalCl r s X) →
    S.NormalCl r s (TwoRep.lsum L)
  | [], _ => .zero r s
  | X :: L, h => .biprod (h X (by simp)) (lsum L fun Y hY => h Y (by simp [hY]))

theorem qsum {r s : ℤ} {X : S.obj r ⟶ S.obj s} (h : S.NormalCl r s X) (d : ℤ) (n : ℕ) :
    S.NormalCl r s (TwoRep.qsum d n X) :=
  lsum _ fun Y hY => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hY
    exact .shift _ h

theorem wordGen {r s : ℤ} {X : S.obj r ⟶ S.obj s} (h : S.NormalCl r s X) : S.WordGen r s X := by
  induction h with
  | pureF h => exact .word h.word
  | endE _ ih => exact ih.comp (.E _)
  | zero s => exact .zero _ s
  | biprod _ _ ihX ihY => exact .biprod ihX ihY
  | shift a _ ih => exact .shift a ih
  | retract i p hip _ ih => exact .retract i p hip ih

/-- `E F 1_m` is a retract of `F E 1_m` or isomorphic to `F E 1_m ⊕ ⊕ 1_m` (condition (3)), so
`Y ≫ E ≫ F` lies in the closure if `Y ≫ F` does. -/
theorem comp_EF {r s : ℤ} {Y : S.obj r ⟶ S.obj (s + 1)} (hY : S.NormalCl r (s + 1) Y)
    (hYF : S.NormalCl r s (Y ≫ S.F s)) : S.NormalCl r (s + 1) ((Y ≫ S.E (s + 1)) ≫ S.F (s + 1)) := by
  have hFE : S.NormalCl r (s + 1) (Y ≫ S.F s ≫ S.E s) := (endE hYF).of_iso (α_ _ _ _)
  refine NormalCl.of_iso ?_ (α_ _ _ _).symm
  rcases le_total 0 (S.n₀ + 2 * (s + 1)) with hm | hm
  · obtain ⟨e⟩ := S.EF s hm
    refine .retract (Y ◁ (biprod.inl ≫ e.inv)) (Y ◁ (e.hom ≫ biprod.fst)) ?_ hFE
    rw [← Bicategory.whiskerLeft_comp, Category.assoc, e.inv_hom_id_assoc, biprod.inl_fst,
      Bicategory.whiskerLeft_id]
  · obtain ⟨e⟩ := S.FE s hm
    exact (NormalCl.biprod hFE (hY.qsum _ _)).of_iso
      ((whiskerLeftIso Y e ≪≫ whiskerLeftBiprodIso _ _ _ ≪≫
        biprod.mapIso (Iso.refl _) (compQsumIso _ _ _)).symm)

theorem comp_F_aux {r m : ℤ} {X : S.obj r ⟶ S.obj m} (hX : S.NormalCl r m X) :
    ∀ (s : ℤ) (h : m = s + 1), S.NormalCl r s ((h ▸ X : S.obj r ⟶ S.obj (s + 1)) ≫ S.F s) := by
  induction hX with
  | pureF hF =>
    intro s h
    subst h
    exact .pureF hF.snoc
  | @endE m Y hY ih =>
    intro s h
    obtain rfl : m = s := by omega
    obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
    exact comp_EF hY (ih t rfl)
  | zero m =>
    intro s h
    subst h
    exact (NormalCl.zero _ s).of_iso ((isZero_zero _).iso (isZero_comp_left (isZero_zero _) _))
  | biprod _ _ ihX ihY =>
    intro s h
    subst h
    exact (NormalCl.biprod (ihX s rfl) (ihY s rfl)).of_iso (whiskerRightBiprodIso _ _ _).symm
  | shift a _ ih =>
    intro s h
    subst h
    exact (NormalCl.shift a (ih s rfl)).of_iso (whiskerRightShiftIso _ _ _).symm
  | retract i p hip _ ih =>
    intro s h
    subst h
    exact .retract (i ▷ _) (p ▷ _)
      (by rw [← Bicategory.comp_whiskerRight, hip, Bicategory.id_whiskerRight]) (ih s rfl)

theorem comp_F {r s : ℤ} {X : S.obj r ⟶ S.obj (s + 1)} (hX : S.NormalCl r (s + 1) X) :
    S.NormalCl r s (X ≫ S.F s) :=
  comp_F_aux hX s rfl

theorem comp_word {m s : ℤ} {Y : S.obj m ⟶ S.obj s} (hY : S.Word m s Y) :
    ∀ {r : ℤ} {X : S.obj r ⟶ S.obj m}, S.NormalCl r m X → S.NormalCl r s (X ≫ Y) := by
  induction hY with
  | id r => intro r' X hX; exact hX.of_iso (ρ_ X).symm
  | E r => intro r' X hX; exact .endE hX
  | F r => intro r' X hX; exact hX.comp_F
  | comp _ _ ih₁ ih₂ => intro r' X hX; exact (ih₂ (ih₁ hX)).of_iso (α_ _ _ _)

/-- **Every word lies in the normal-form closure.** -/
theorem of_word {r s : ℤ} {W : S.obj r ⟶ S.obj s} (hW : S.Word r s W) : S.NormalCl r s W :=
  (comp_word hW (.pureF (FWord.id r))).of_iso (λ_ W)

end NormalCl

variable [GradedBicategory.IsLinear B k]

/-! ## The numerical data of left composition, without boundedness -/

/-- The categories `Hom(obj c, obj t)`, `t ∈ ℤ`, with the functors `- ≫ E`, `- ≫ F` and the
word-generated 1-morphisms as test objects (no boundedness hypothesis). -/
def leftData₀ (S : StrongSl2 k B) (c : ℤ) : Sl2CatData₀ k (fun t : ℤ => (S.obj c ⟶ S.obj t)) where
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

/-! ## The moves -/

/-- The formal move `Hom(x ≫ E, y) ≅ Hom(x, y ≫ F⟨n+1⟩)`. -/
theorem bdd_compE_of_bdd {c r : ℤ} {x : S.obj c ⟶ S.obj r} {y : S.obj c ⟶ S.obj (r + 1)}
    (h : HomBddBelow k x (y ≫ S.F r)) : HomBddBelow k (x ≫ S.E r) y := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N - (S.n₀ + 2 * r + 1), fun d hd => ?_⟩
  have hadj := (leftData₀ S c).adj r x y d
  change finrank k (x ≫ S.E r ⟶ y⟦d⟧) =
    finrank k (x ⟶ (y ≫ S.F r)⟦d + (S.n₀ + 2 * r + 1)⟧) at hadj
  rw [hadj]
  exact hN _ (by omega)

/-- The formal move `Hom(F ≫ x, y) ≅ Hom(x, E⟨n+1⟩ ≫ y)`. -/
theorem finrank_F_comp (r : ℤ) {c : ℤ} (x : S.obj r ⟶ S.obj c) (y : S.obj (r + 1) ⟶ S.obj c)
    (d : ℤ) : finrank k (S.F r ≫ x ⟶ y⟦d⟧) = finrank k (x ⟶ (S.E r ≫ y)⟦d + (S.n₀ + 2 * r + 1)⟧) := by
  rw [finrank_hom_congr_right k x (whiskerLeftShiftIso (S.E r) y _).symm, (S.dimAdj r).right,
    finrank_hom_congr_left k (whiskerRightShiftIso (S.F r) x _),
    finrank_hom_shift_shift k _ _ (c := d) (by rfl)]

theorem bdd_F_comp_of_bdd {r c : ℤ} {x : S.obj r ⟶ S.obj c} {y : S.obj (r + 1) ⟶ S.obj c}
    (h : HomBddBelow k x (S.E r ≫ y)) : HomBddBelow k (S.F r ≫ x) y := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N - (S.n₀ + 2 * r + 1), fun d hd => ?_⟩
  rw [finrank_F_comp]
  exact hN _ (by omega)

variable [∀ a b : B, HomFinite k (a ⟶ b)]

/-- **One-sided numerical adjunction**: for word-generated `x`, `y`, if one of
`Hom(x ≫ F, y⟨d⟩)`, `Hom(x, (y ≫ E)⟨d⟩)` vanishes for `d ≪ 0`, then
`dim Hom(x ≫ F, y⟨d⟩) = dim Hom(x, (y ≫ E)⟨d - (n+1)⟩)` for all `d`, `n = wt r`. -/
theorem finrank_compF_of_bdd {c r : ℤ} {x : S.obj c ⟶ S.obj (r + 1)} {y : S.obj c ⟶ S.obj r}
    (hx : S.WordGen c (r + 1) x) (hy : S.WordGen c r y)
    (hb : HomBddBelow k (x ≫ S.F r) y ∨ HomBddBelow k x (y ≫ S.E r)) (d : ℤ) :
    finrank k (x ≫ S.F r ⟶ y⟦d⟧) = finrank k (x ⟶ (y ≫ S.E r)⟦d - (S.wt r + 1)⟧) :=
  (leftData₀ S c).finrank_f_eq_of_bdd (t := r) (X := x) (Z := y) hx hy hb d

theorem bdd_compE_of_bdd_compF {c r : ℤ} {x : S.obj c ⟶ S.obj (r + 1)} {y : S.obj c ⟶ S.obj r}
    (hx : S.WordGen c (r + 1) x) (hy : S.WordGen c r y) (h : HomBddBelow k (x ≫ S.F r) y) :
    HomBddBelow k x (y ≫ S.E r) := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N - (S.wt r + 1), fun d hd => ?_⟩
  have := finrank_compF_of_bdd hx hy (Or.inl ⟨N, hN⟩) (d + (S.wt r + 1))
  rw [show d + (S.wt r + 1) - (S.wt r + 1) = d by ring] at this
  rw [← this]
  exact hN _ (by omega)

theorem bdd_compF_of_bdd_compE {c r : ℤ} {x : S.obj c ⟶ S.obj (r + 1)} {y : S.obj c ⟶ S.obj r}
    (hx : S.WordGen c (r + 1) x) (hy : S.WordGen c r y) (h : HomBddBelow k x (y ≫ S.E r)) :
    HomBddBelow k (x ≫ S.F r) y := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N + (S.wt r + 1), fun d hd => ?_⟩
  rw [finrank_compF_of_bdd hx hy (Or.inr ⟨N, hN⟩) d]
  exact hN _ (by omega)

/-! ## Peeling letters off the source word -/

/-- If `Hom(X₁, Z')` is bounded below for all words `Z'`, then so is `Hom(X₁ ≫ Y, Z)` for every word
`Y` and every word `Z`. -/
theorem bdd_comp_word {m s : ℤ} {Y : S.obj m ⟶ S.obj s} (hY : S.Word m s Y) :
    ∀ {c : ℤ} {X₁ : S.obj c ⟶ S.obj m}, S.WordGen c m X₁ →
      (∀ Z' : S.obj c ⟶ S.obj m, S.Word c m Z' → HomBddBelow k X₁ Z') →
      ∀ Z : S.obj c ⟶ S.obj s, S.Word c s Z → HomBddBelow k (X₁ ≫ Y) Z := by
  induction hY with
  | id r =>
    intro c X₁ _ h Z hZ
    exact (h Z hZ).of_iso (ρ_ X₁).symm (Iso.refl Z)
  | E r =>
    intro c X₁ _ h Z hZ
    exact bdd_compE_of_bdd (h _ (hZ.comp (.F r)))
  | F r =>
    intro c X₁ hX₁ h Z hZ
    exact bdd_compF_of_bdd_compE hX₁ (.word hZ) (h _ (hZ.comp (.E r)))
  | comp hY₁ hY₂ ih₁ ih₂ =>
    intro c X₁ hX₁ h Z hZ
    exact (ih₂ (hX₁.comp (.word hY₁)) (ih₁ hX₁ h) Z hZ).of_iso (α_ _ _ _) (Iso.refl Z)

/-- (BB_w) at the source `c` follows from the boundedness of `Hom(1, W)` for words `W : c → c`. -/
theorem bdd_of_bdd_id {c : ℤ}
    (h : ∀ W : S.obj c ⟶ S.obj c, S.Word c c W → HomBddBelow k (𝟙 (S.obj c)) W) {s : ℤ}
    {X Z : S.obj c ⟶ S.obj s} (hX : S.Word c s X) (hZ : S.Word c s Z) : HomBddBelow k X Z :=
  (bdd_comp_word hX (WordGen.id c) h Z hZ).of_iso (λ_ X) (Iso.refl Z)

/-- From words to word-generated 1-morphisms, for a fixed source. -/
theorem homBddBelow_of_words {r : ℤ}
    (h : ∀ {s : ℤ} {X Z : S.obj r ⟶ S.obj s}, S.Word r s X → S.Word r s Z → HomBddBelow k X Z)
    {s : ℤ} {X Z : S.obj r ⟶ S.obj s} (hX : S.WordGen r s X) (hZ : S.WordGen r s Z) :
    HomBddBelow k X Z := by
  have key : ∀ {W : S.obj r ⟶ S.obj s} (a : ℤ), S.Word r s W → ∀ {Z : S.obj r ⟶ S.obj s},
      S.WordNF r s Z → HomBddBelow k (W⟦a⟧) Z := by
    intro W a hW Z hZ
    induction hZ with
    | shiftWord b hV => exact ((h hW hV).shift_right b).shift_left a
    | zero => exact .of_isZero_right _ (isZero_zero _)
    | biprod _ _ ihX ihY => exact ihX.biprod_right ihY
    | retract i p hip _ ih => exact ih.of_retract_right i p hip
  have hZ' := hZ.wordNF
  have hX' := hX.wordNF
  clear hX hZ
  induction hX' with
  | shiftWord a hW => exact key a hW hZ'
  | zero => exact .of_isZero_left (isZero_zero _) _
  | biprod _ _ ihX ihY => exact ihX.biprod_left ihY
  | retract i p hip _ ih => exact ih.of_retract_left i p hip

/-! ## Induction from the lowest weight -/

/-- The key step: if (BB_w) holds at the source `c - 1`, then `Hom(1, W)` is bounded below for
every `W : c → c` in the normal-form closure. -/
theorem bdd_id_of_cl {r s : ℤ} {X : S.obj r ⟶ S.obj s} (hX : S.NormalCl r s X) :
    ∀ (h : s = r),
      (∀ r', r' + 1 = r → ∀ {s' : ℤ} {X' Z' : S.obj r' ⟶ S.obj s'}, S.WordGen r' s' X' →
        S.WordGen r' s' Z' → HomBddBelow k X' Z') →
      HomBddBelow k (𝟙 (S.obj r)) (h ▸ X : S.obj r ⟶ S.obj r) := by
  induction hX with
  | pureF hF =>
    intro h _
    subst h
    rw [hF.eq_id]
    exact ⟨0, fun d hd => S.hom_neg _ d hd⟩
  | @endE s Y hY _ =>
    intro h hprev
    subst h
    have h1 : HomBddBelow k (𝟙 (S.obj s)) (S.E s ≫ Y) :=
      hprev s rfl (.id _) ((WordGen.E s).comp hY.wordGen)
    have h2 : HomBddBelow k (𝟙 (S.obj (s + 1)) ≫ S.F s) Y :=
      (bdd_F_comp_of_bdd h1).of_iso ((ρ_ _) ≪≫ (λ_ _).symm) (Iso.refl Y)
    exact bdd_compE_of_bdd_compF (.id _) hY.wordGen h2
  | zero s =>
    intro h _
    subst h
    exact .of_isZero_right _ (isZero_zero _)
  | biprod _ _ ihX ihY =>
    intro h hprev
    subst h
    exact (ihX rfl hprev).biprod_right (ihY rfl hprev)
  | shift a _ ih =>
    intro h hprev
    subst h
    exact (ih rfl hprev).shift_right a
  | retract i p hip _ ih =>
    intro h hprev
    subst h
    exact (ih rfl hprev).of_retract_right i p hip

/-- **(BB_w) at every source**, by increasing induction from the lowest weight. -/
theorem bdd_src (c : ℤ) {s : ℤ} {X Z : S.obj c ⟶ S.obj s} (hX : S.Word c s X)
    (hZ : S.Word c s Z) : HomBddBelow k X Z := by
  revert s
  refine S.increasing_induction
    (P := fun c => ∀ {s : ℤ} {X Z : S.obj c ⟶ S.obj s}, S.Word c s X → S.Word c s Z →
      HomBddBelow k X Z) ?_ ?_ c
  · intro c hc s X Z _ _
    exact .of_isZero_left (isZero_of_isZero_id_src hc X) Z
  · intro c ih s X Z hX hZ
    refine bdd_of_bdd_id (fun W hW => ?_) hX hZ
    have hprev : ∀ r', r' + 1 = c → ∀ {s' : ℤ} {X' Z' : S.obj r' ⟶ S.obj s'},
        S.WordGen r' s' X' → S.WordGen r' s' Z' → HomBddBelow k X' Z' :=
      fun r' hr' _ _ _ hX' hZ' => homBddBelow_of_words (ih r' (by omega)) hX' hZ'
    exact bdd_id_of_cl (NormalCl.of_word hW) rfl hprev

/-- **(BB_w) is a theorem**: in every strong 2-representation of `sl₂` (CL Definition 1.2), the graded
Hom spaces between words in `E`, `F` vanish in degrees `d ≪ 0`. -/
theorem bbw (S : StrongSl2 k B) : S.BBw :=
  fun _ _ _ _ hX hZ => bdd_src _ hX hZ

/-- Graded Hom spaces between word-generated 1-morphisms are bounded below. -/
theorem homBddBelow_wordGen (S : StrongSl2 k B) {r s : ℤ} {X Z : S.obj r ⟶ S.obj s}
    (hX : S.WordGen r s X) (hZ : S.WordGen r s Z) : HomBddBelow k X Z :=
  homBddBelow_of_words (fun hX' hZ' => bdd_src _ hX' hZ') hX hZ

end Categorification.TwoRep.StrongSl2

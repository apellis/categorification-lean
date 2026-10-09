/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.WeightModuleRing

/-!
# The numerical adjunction without boundedness: quantum-integer torsion and positivity

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, §3 (eq. (3.2) `eq:ind_hyp`, Proposition 3.9 `prop:lradj`).

`NumericalAdjunction.lean` proves the numerical left adjunction
`dim Hom(f X, Z⟨d⟩) = dim Hom(X, (e Z)⟨d - (n₀ + 2t + 1)⟩)` under the hypothesis that all Hom spaces
between test objects are bounded below in degree. Here no boundedness is assumed (`Sl2CatData₀`):

* **Torsion (`Sl2CatData₀.seq_f_torsion`)**: the defect
  `δ = ⟨f X, Z⟩ - T^{n₀ + 2t + 1} ⟨X, e Z⟩` of two-sided sequences of graded dimensions is killed by
  a product of quantum integers `[n]`, `n ≥ 1`. The proof is that of `NumericalAdjunction.lean`
  with the coefficient field `ℚ((q))` replaced by the ring `Tors.Rq = ℚ[T, T⁻¹][[n]⁻¹]` and the
  Laurent-series pairing by the pairing with values in the localized sequences `Tors.MSeq`; the
  `sl₂` lemma is `WtModuleR.F_comm_of_E_comm` (`WeightModuleRing.lean`).
* **Positivity (`Sl2CatData₀.finrank_f_eq_of_bdd`)**: the quantum integers have nonnegative
  coefficients, so a torsion sequence which has a sign on a half-line vanishes
  (`Tors.eq_zero_of_toM_eq_zero`). Hence the numerical adjunction holds **exactly as soon as one of
  the two Hom-sequences vanishes in all degrees `d ≪ 0`**.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits Module
open KrullSchmidtCat (HomFinite)
open ZeroObject
open Tors LaurentPolynomial

/-- The image of `T^n` in `Tors.Rq`. -/
abbrev Tors.tq (n : ℤ) : Rq := algebraMap R₀ Rq (T n)

theorem Tors.tq_zero : tq 0 = 1 := by
  show algebraMap R₀ Rq (T 0) = 1
  rw [T_zero, map_one]

theorem Tors.tq_smul_toM (n : ℤ) (s : Tors.Seq) : tq n • toM s = toM ((T n : R₀) • s) := by
  rw [algebraMap_smul, map_smul]

/-! ## The abstract setting -/

universe u v

variable (k : Type*) [Field k] (C : ℤ → Type u) [∀ t, Category.{v} (C t)]
  [∀ t, Preadditive (C t)] [∀ t, Linear k (C t)] [∀ t, HasShift (C t) ℤ]
  [∀ t, HasZeroObject (C t)] [∀ t, HasBinaryBiproducts (C t)]

/-- **Categorified `sl₂`-weight data**: graded `k`-linear categories `C t` of weight `n₀ + 2t`,
functors `e t : C t ⥤ C (t + 1)` and `f t : C (t + 1) ⥤ C t` commuting with sums and shifts,
condition (3) of CL Definition 1.2, the formal adjunction `e ⊣ f` at the level of Hom-dimensions
(with the shift `n₀ + 2t + 1` of CL eq. `eq_defF`), integrability, and a class `P` of test objects
closed under the operations. No boundedness of Hom spaces is assumed. -/
structure Sl2CatData₀ where
  /-- The weight of `C 0`; `C t` has weight `n₀ + 2t`. -/
  n₀ : ℤ
  /-- The raising functor. -/
  e : ∀ t, C t ⥤ C (t + 1)
  /-- The lowering functor. -/
  f : ∀ t, C (t + 1) ⥤ C t
  eBiprod : ∀ t (X Y : C t), (e t).obj (X ⊞ Y) ≅ (e t).obj X ⊞ (e t).obj Y
  fBiprod : ∀ t (X Y : C (t + 1)), (f t).obj (X ⊞ Y) ≅ (f t).obj X ⊞ (f t).obj Y
  eShift : ∀ t (X : C t) (a : ℤ), (e t).obj (X⟦a⟧) ≅ ((e t).obj X)⟦a⟧
  fShift : ∀ t (X : C (t + 1)) (a : ℤ), (f t).obj (X⟦a⟧) ≅ ((f t).obj X)⟦a⟧
  /-- Condition (3) for `m = n₀ + 2(t + 1) ≥ 0`: `E F 1_m ≅ F E 1_m ⊕_{[m]} 1_m`. -/
  EF : ∀ t (X : C (t + 1)), 0 ≤ n₀ + 2 * (t + 1) →
    Nonempty ((e t).obj ((f t).obj X) ≅
      (f (t + 1)).obj ((e (t + 1)).obj X) ⊞ qsum 1 (n₀ + 2 * (t + 1)).toNat X)
  /-- Condition (3) for `m = n₀ + 2(t + 1) ≤ 0`: `F E 1_m ≅ E F 1_m ⊕_{[-m]} 1_m`. -/
  FE : ∀ t (X : C (t + 1)), n₀ + 2 * (t + 1) ≤ 0 →
    Nonempty ((f (t + 1)).obj ((e (t + 1)).obj X) ≅
      (e t).obj ((f t).obj X) ⊞ qsum 1 (-(n₀ + 2 * (t + 1))).toNat X)
  /-- The formal adjunction `e ⊣ f⟨n₀ + 2t + 1⟩`, at the level of Hom dimensions. -/
  adj : ∀ t (X : C t) (Z : C (t + 1)) (d : ℤ),
    finrank k ((e t).obj X ⟶ Z⟦d⟧) = finrank k (X ⟶ ((f t).obj Z)⟦d + (n₀ + 2 * t + 1)⟧)
  /-- Integrability: `C t` is zero for `|t|` large. -/
  bdd : ∃ N : ℕ, ∀ t : ℤ, (N : ℤ) ≤ |t| → ∀ X : C t, IsZero X
  /-- The class of test objects. -/
  P : ∀ t, C t → Prop
  P_zero : ∀ t, P t 0
  P_biprod : ∀ t {X Y : C t}, P t X → P t Y → P t (X ⊞ Y)
  P_shift : ∀ t {X : C t} (a : ℤ), P t X → P t (X⟦a⟧)
  P_iso : ∀ t {X Y : C t}, P t X → (X ≅ Y) → P t Y
  P_e : ∀ t {X : C t}, P t X → P (t + 1) ((e t).obj X)
  P_f : ∀ t {X : C (t + 1)}, P (t + 1) X → P t ((f t).obj X)

variable {k C}

namespace Sl2CatData₀

variable (D : Sl2CatData₀ k C)

/-! ### Test objects -/

/-- The test objects of all weights. -/
abbrev Ob : Type _ := Σ t : ℤ, {X : C t // D.P t X}

variable {D}

theorem P_lsum {t : ℤ} : ∀ (L : List (C t)), (∀ X ∈ L, D.P t X) → D.P t (lsum L)
  | [], _ => D.P_zero t
  | X :: L, h => D.P_biprod t (h X (by simp)) (P_lsum L fun Y hY => h Y (by simp [hY]))

theorem P_qsum {t : ℤ} {X : C t} (hX : D.P t X) (d : ℤ) (n : ℕ) : D.P t (qsum d n X) :=
  P_lsum _ fun Y hY => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hY
    exact D.P_shift t _ hX

/-- `C t` as `C ((t - 1) + 1)`. -/
def castC {t : ℤ} (X : C t) : C (t - 1 + 1) := cast (congrArg C (by omega)) X

theorem P_castC {t : ℤ} {X : C t} (hX : D.P t X) : D.P (t - 1 + 1) (castC X) := by
  have h : ∀ (s : ℤ) (hs : t = s) (Y : C t), D.P t Y → D.P s (cast (congrArg C hs) Y) := by
    intro s hs Y hY; subst hs; exact hY
  exact h _ (by omega) X hX

variable (D)

/-- The raising map on test objects. -/
def eOb (b : D.Ob) : D.Ob := ⟨b.1 + 1, ⟨(D.e b.1).obj b.2.1, D.P_e _ b.2.2⟩⟩

/-- The lowering map on test objects. -/
def fOb (b : D.Ob) : D.Ob := ⟨b.1 - 1, ⟨(D.f (b.1 - 1)).obj (castC b.2.1), D.P_f _ (P_castC b.2.2)⟩⟩

theorem fOb_succ (r : ℤ) (X : C (r + 1)) (hX : D.P (r + 1) X) :
    D.fOb ⟨r + 1, ⟨X, hX⟩⟩ = ⟨r, ⟨(D.f r).obj X, D.P_f r hX⟩⟩ := by
  have h : ∀ (u : ℤ) (hu : u = r) (hc : C (r + 1) = C (u + 1)) (hP),
      (⟨u, ⟨(D.f u).obj (cast hc X), hP⟩⟩ : D.Ob) = ⟨r, ⟨(D.f r).obj X, D.P_f r hX⟩⟩ := by
    intro u hu hc hP; subst hu; rfl
  exact h (r + 1 - 1) (by omega) _ _

/-! ### Hom-series -/

variable {D}

/-- `C t'` as `C t` along `t' = t`. -/
def castEq {t t' : ℤ} (h : t' = t) (Z : C t') : C t := cast (congrArg C h) Z

theorem P_castEq {t t' : ℤ} (h : t' = t) {Z : C t'} (hZ : D.P t' Z) : D.P t (castEq h Z) := by
  subst h; exact hZ

/-- The graded dimensions `d ↦ dim Hom(X, Z⟨d⟩)`, a two-sided sequence. -/
def seq {t : ℤ} (X Z : C t) : Tors.Seq := fun d : ℤ => (finrank k (X ⟶ Z⟦d⟧) : ℚ)

/-- **The Hom-series** `⟨X, Z⟩`, the image of the graded dimensions in `MSeq` (no boundedness is
needed). -/
def ser {t : ℤ} {X Z : C t} (_hX : D.P t X) (_hZ : D.P t Z) : MSeq := toM (seq (k := k) X Z)

theorem ser_def {t : ℤ} {X Z : C t} (hX : D.P t X) (hZ : D.P t Z) :
    ser hX hZ = toM (seq (k := k) X Z) := rfl

theorem ser_ext {t : ℤ} {X Z X' Z' : C t} {hX : D.P t X} {hZ : D.P t Z} {hX' : D.P t X'}
    {hZ' : D.P t Z'} (h : ∀ d : ℤ, finrank k (X ⟶ Z⟦d⟧) = finrank k (X' ⟶ Z'⟦d⟧)) :
    ser hX hZ = ser hX' hZ' := by
  rw [ser_def, ser_def]; congr 1; funext d; simp only [seq, h]

theorem ser_biprod_left [∀ t, HomFinite k (C t)]
    {t : ℤ} {X Y Z : C t} (hX : D.P t X) (hY : D.P t Y) (hZ : D.P t Z) :
    ser (D.P_biprod t hX hY) hZ = ser hX hZ + ser hY hZ := by
  rw [ser_def, ser_def, ser_def, ← map_add]; congr 1; funext d
  change (finrank k (X ⊞ Y ⟶ Z⟦d⟧) : ℚ) = (finrank k (X ⟶ Z⟦d⟧) : ℚ) + (finrank k (Y ⟶ Z⟦d⟧) : ℚ)
  rw [finrank_hom_biprod_left]; push_cast; rfl

theorem ser_biprod_right [∀ t, HomFinite k (C t)] [∀ t (n : ℤ), (shiftFunctor (C t) n).Additive]
    {t : ℤ} {X Z W : C t} (hX : D.P t X) (hZ : D.P t Z) (hW : D.P t W) :
    ser hX (D.P_biprod t hZ hW) = ser hX hZ + ser hX hW := by
  rw [ser_def, ser_def, ser_def, ← map_add]; congr 1; funext d
  change (finrank k (X ⟶ (Z ⊞ W)⟦d⟧) : ℚ) = (finrank k (X ⟶ Z⟦d⟧) : ℚ) + (finrank k (X ⟶ W⟦d⟧) : ℚ)
  rw [finrank_hom_congr_right k X (mapBiprodIso (shiftFunctor (C t) d) Z W),
    finrank_hom_biprod_right]
  push_cast; rfl

theorem ser_iso_left {t : ℤ} {X X' Z : C t} (hX : D.P t X) (e : X ≅ X') (hZ : D.P t Z) :
    ser (D.P_iso t hX e) hZ = ser hX hZ :=
  ser_ext fun _ => (finrank_hom_congr_left k e _).symm

theorem ser_iso_right {t : ℤ} {X Z Z' : C t} (hX : D.P t X) (hZ : D.P t Z) (e : Z ≅ Z') :
    ser hX (D.P_iso t hZ e) = ser hX hZ :=
  ser_ext fun d => (finrank_hom_congr_right k X ((shiftFunctor _ d).mapIso e)).symm

omit [∀ t, HasZeroObject (C t)] [∀ t, HasBinaryBiproducts (C t)] in
theorem seq_shift_left [∀ t (n : ℤ), (shiftFunctor (C t) n).Additive]
    [∀ t (n : ℤ), (shiftFunctor (C t) n).Linear k] {t : ℤ} (X Z : C t) (a : ℤ) :
    seq (k := k) (X⟦a⟧) Z = (T a : R₀) • seq (k := k) X Z := by
  funext d
  rw [Tors.T_smul_apply]
  change (finrank k (X⟦a⟧ ⟶ Z⟦d⟧) : ℚ) = (finrank k (X ⟶ Z⟦d - a⟧) : ℚ)
  rw [finrank_hom_shift_shift k _ _ (c := d - a) (by ring)]

omit [∀ t, HasZeroObject (C t)] [∀ t, HasBinaryBiproducts (C t)] in
theorem seq_shift_right {t : ℤ} (X Z : C t) (a : ℤ) :
    seq (k := k) X (Z⟦a⟧) = (T (-a) : R₀) • seq (k := k) X Z := by
  funext d
  rw [Tors.T_smul_apply]
  change (finrank k (X ⟶ (Z⟦a⟧)⟦d⟧) : ℚ) = (finrank k (X ⟶ Z⟦d - -a⟧) : ℚ)
  rw [show finrank k (X ⟶ (Z⟦a⟧)⟦d⟧) = finrank k (X ⟶ Z⟦a + d⟧) from
      finrank_hom_congr_right k X ((shiftFunctorAdd' (C t) a d (a + d) rfl).app Z).symm,
    finrank_hom_shift_congr k _ _ (show a + d = d - -a by ring)]

theorem ser_shift_left [∀ t (n : ℤ), (shiftFunctor (C t) n).Additive] [∀ t (n : ℤ), (shiftFunctor (C t) n).Linear k]
    {t : ℤ} {X Z : C t} (hX : D.P t X) (hZ : D.P t Z) (a : ℤ) :
    ser (D.P_shift t a hX) hZ = tq a • ser hX hZ := by
  rw [ser_def, ser_def, tq_smul_toM, seq_shift_left]

theorem ser_shift_right {t : ℤ} {X Z : C t} (hX : D.P t X) (hZ : D.P t Z) (a : ℤ) :
    ser hX (D.P_shift t a hZ) = tq (-a) • ser hX hZ := by
  rw [ser_def, ser_def, tq_smul_toM, seq_shift_right]

theorem seq_adj {t : ℤ} (X : C t) (Z : C (t + 1)) :
    seq (k := k) ((D.e t).obj X) Z =
      (T (-(D.n₀ + 2 * t + 1)) : R₀) • seq (k := k) X ((D.f t).obj Z) := by
  funext d
  rw [Tors.T_smul_apply]
  change (finrank k ((D.e t).obj X ⟶ Z⟦d⟧) : ℚ) =
    (finrank k (X ⟶ ((D.f t).obj Z)⟦d - -(D.n₀ + 2 * t + 1)⟧) : ℚ)
  rw [D.adj, finrank_hom_shift_congr k _ _
    (show d + (D.n₀ + 2 * t + 1) = d - -(D.n₀ + 2 * t + 1) by ring)]

theorem ser_adj {t : ℤ} {X : C t} {Z : C (t + 1)} (hX : D.P t X) (hZ : D.P (t + 1) Z) :
    ser (D.P_e t hX) hZ = tq (-(D.n₀ + 2 * t + 1)) • ser hX (D.P_f t hZ) := by
  rw [ser_def, ser_def, tq_smul_toM, seq_adj]

variable (D) in
/-- The Hom-series on test objects (zero between different weights). -/
def pairOb : D.Ob → D.Ob → MSeq
  | ⟨t, _, hX⟩, ⟨t', _, hZ⟩ => if h : t' = t then ser hX (P_castEq h hZ) else 0

theorem pairOb_same {t : ℤ} {X Z : C t} (hX : D.P t X) (hZ : D.P t Z) :
    D.pairOb ⟨t, X, hX⟩ ⟨t, Z, hZ⟩ = ser hX hZ := by
  simp only [pairOb]
  split_ifs with h
  · rfl
  · exact absurd trivial h

theorem pairOb_ne {t t' : ℤ} {X : C t} {Z : C t'} (hX : D.P t X) (hZ : D.P t' Z) (h : t' ≠ t) :
    D.pairOb ⟨t, X, hX⟩ ⟨t', Z, hZ⟩ = 0 := by
  simp only [pairOb]
  split_ifs with h'
  · exact absurd h' h
  · rfl

/-! ### The `K`-linear split Grothendieck group -/

variable (D) in
/-- The relations of `K ⊗ K_⊕`: sums, shifts (`q ↦ ⟨ε⟩`) and isomorphisms. -/
def relSet (ε : ℤ) : Set (D.Ob →₀ Rq) :=
  {x | ∃ (t : ℤ) (X Y : C t) (hX : D.P t X) (hY : D.P t Y),
      x = Finsupp.single ⟨t, X ⊞ Y, D.P_biprod t hX hY⟩ 1 - Finsupp.single ⟨t, X, hX⟩ 1 -
        Finsupp.single ⟨t, Y, hY⟩ 1} ∪
  {x | ∃ (t : ℤ) (X : C t) (hX : D.P t X) (a : ℤ),
      x = Finsupp.single ⟨t, X⟦a⟧, D.P_shift t a hX⟩ 1 - tq (ε * a) • Finsupp.single ⟨t, X, hX⟩ 1} ∪
  {x | ∃ (t : ℤ) (X Y : C t) (hX : D.P t X) (e : X ≅ Y),
      x = Finsupp.single ⟨t, X, hX⟩ 1 - Finsupp.single ⟨t, Y, D.P_iso t hX e⟩ 1}

variable (D) in
/-- **`K ⊗ K_⊕(P)`**, the split Grothendieck group of the test objects with coefficients in
`Rq`, `q` acting as the shift `⟨ε⟩`. -/
abbrev KMod (ε : ℤ) := (D.Ob →₀ Rq) ⧸ Submodule.span Rq (D.relSet ε)

variable {ε : ℤ}

/-- The class of a test object. -/
def clsOb (ε : ℤ) (b : D.Ob) : D.KMod ε := Submodule.Quotient.mk (Finsupp.single b 1)

theorem KMod.hom_ext {M : Type*} [AddCommGroup M] [Module Rq M] {φ ψ : D.KMod ε →ₗ[Rq] M}
    (h : ∀ b, φ (clsOb ε b) = ψ (clsOb ε b)) : φ = ψ := by
  refine Submodule.linearMap_qext _ (Finsupp.lhom_ext fun b c => ?_)
  have e : Finsupp.single b c = c • Finsupp.single b (1 : Rq) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, e, map_smul]
  exact congrArg (c • ·) (h b)

theorem mk_eq_zero_of_mem {x : D.Ob →₀ Rq} (hx : x ∈ D.relSet ε) :
    (Submodule.Quotient.mk x : D.KMod ε) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).2 (Submodule.subset_span hx)

theorem clsOb_biprod {t : ℤ} {X Y : C t} (hX : D.P t X) (hY : D.P t Y) :
    clsOb ε ⟨t, X ⊞ Y, D.P_biprod t hX hY⟩ = clsOb ε ⟨t, X, hX⟩ + clsOb ε ⟨t, Y, hY⟩ := by
  have := mk_eq_zero_of_mem (ε := ε) (Or.inl (Or.inl ⟨t, X, Y, hX, hY, rfl⟩))
  simp only [Submodule.Quotient.mk_sub] at this
  unfold clsOb
  rw [sub_sub, sub_eq_zero] at this
  exact this

theorem clsOb_shift {t : ℤ} {X : C t} (hX : D.P t X) (a : ℤ) :
    clsOb ε ⟨t, X⟦a⟧, D.P_shift t a hX⟩ = tq (ε * a) • clsOb ε ⟨t, X, hX⟩ := by
  have := mk_eq_zero_of_mem (ε := ε) (Or.inl (Or.inr ⟨t, X, hX, a, rfl⟩))
  simp only [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul] at this
  exact sub_eq_zero.1 this

theorem clsOb_iso {t : ℤ} {X Y : C t} (hX : D.P t X) (e : X ≅ Y) :
    clsOb ε ⟨t, X, hX⟩ = clsOb ε ⟨t, Y, D.P_iso t hX e⟩ := by
  have := mk_eq_zero_of_mem (ε := ε) (Or.inr ⟨t, X, Y, hX, e, rfl⟩)
  simp only [Submodule.Quotient.mk_sub] at this
  exact sub_eq_zero.1 this

theorem clsOb_iso' {t : ℤ} {X Y : C t} (hX : D.P t X) (hY : D.P t Y) (e : X ≅ Y) :
    clsOb ε ⟨t, X, hX⟩ = clsOb ε ⟨t, Y, hY⟩ :=
  clsOb_iso hX e

theorem clsOb_zero (t : ℤ) : clsOb ε ⟨t, (0 : C t), D.P_zero t⟩ = 0 := by
  have e : (0 : C t) ≅ 0 ⊞ 0 :=
    (isZero_zero _).iso ((biprod_isZero_iff _ _).2 ⟨isZero_zero _, isZero_zero _⟩)
  have h1 := clsOb_iso' (ε := ε) (D.P_zero t) (D.P_biprod t (D.P_zero t) (D.P_zero t)) e
  rw [clsOb_biprod (D.P_zero t) (D.P_zero t)] at h1
  simpa using h1

theorem clsOb_of_isZero {t : ℤ} {X : C t} (hX : D.P t X) (h : IsZero X) : clsOb ε ⟨t, X, hX⟩ = 0 := by
  rw [clsOb_iso' hX (D.P_zero t) (h.iso (isZero_zero _)), clsOb_zero]

theorem clsOb_lsum_shift {t : ℤ} {X : C t} (hX : D.P t X) : ∀ (L : List ℤ) (hL),
    clsOb ε ⟨t, lsum (L.map fun a => X⟦a⟧), hL⟩ = (L.map fun a => tq (ε * a)).sum • clsOb ε ⟨t, X, hX⟩
  | [], _ => by simpa using clsOb_zero (ε := ε) t
  | a :: L, _ => by
    simp only [List.map_cons, lsum_cons, List.sum_cons, add_smul]
    rw [clsOb_biprod (D.P_shift t a hX) (P_lsum _ fun Y hY => by
        obtain ⟨b, -, rfl⟩ := List.mem_map.1 hY; exact D.P_shift t b hX),
      clsOb_shift, clsOb_lsum_shift hX L]

theorem clsOb_qsum (hε : ε = 1 ∨ ε = -1) {t : ℤ} {X : C t} (hX : D.P t X) (m : ℕ) :
    clsOb ε ⟨t, qsum 1 m X, P_qsum hX 1 m⟩ = Tors.qiR m • clsOb ε ⟨t, X, hX⟩ := by
  have hq : qsum 1 m X = lsum (((List.range m).map fun j : ℕ => 1 * ((m : ℤ) - 1 - 2 * (j : ℤ))).map
      fun a => X⟦a⟧) := by rw [qsum, List.map_map]; rfl
  have hL := D.P_iso t (P_qsum hX 1 m) (eqToIso hq)
  rw [clsOb_iso' (P_qsum hX 1 m) hL (eqToIso hq), clsOb_lsum_shift (ε := ε) hX _ hL, List.map_map,
    list_sum_map_range]
  congr 1
  rcases hε with rfl | rfl
  · rw [Tors.qiR, Tors.qi0_natCast, Tors.qiN, map_sum]
    exact Finset.sum_congr rfl fun j _ => by simp only [one_mul, Function.comp_apply]
  · rw [Tors.qiR, Tors.qi0_natCast, ← Tors.qiN_reflect, map_sum]
    exact Finset.sum_congr rfl fun j _ => by simp only [one_mul, neg_one_mul, Function.comp_apply]

/-! ### The operators `E`, `F` and the weight module structure -/

variable (D) in
/-- The raising operator on `K ⊗ K_⊕`, rescaled: `E [X] = q^{c t} [e X]` for `X` of weight `t`. -/
def opE (ε : ℤ) (c : ℤ → ℤ) : D.KMod ε →ₗ[Rq] D.KMod ε :=
  (Submodule.span Rq (D.relSet ε)).liftQ
    (Finsupp.linearCombination Rq fun b : D.Ob => tq (c b.1) • clsOb ε (D.eOb b)) (by
      rw [Submodule.span_le]
      rintro x ((⟨t, X, Y, hX, hY, rfl⟩ | ⟨t, X, hX, a, rfl⟩) | ⟨t, X, Y, hX, e, rfl⟩) <;>
        simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul,
          Finsupp.linearCombination_single, one_smul, eOb]
      · rw [clsOb_iso' (D.P_e t (D.P_biprod t hX hY)) (D.P_biprod (t + 1) (D.P_e t hX) (D.P_e t hY))
          (D.eBiprod t X Y), clsOb_biprod (D.P_e t hX) (D.P_e t hY), smul_add]
        abel
      · rw [clsOb_iso' (D.P_e t (D.P_shift t a hX)) (D.P_shift (t + 1) a (D.P_e t hX))
          (D.eShift t X a), clsOb_shift (D.P_e t hX) a, smul_comm, sub_self]
      · rw [clsOb_iso' (D.P_e t hX) (D.P_e t (D.P_iso t hX e)) ((D.e t).mapIso e), sub_self])

variable (D) in
/-- The lowering operator on `K ⊗ K_⊕`, rescaled: `F [X] = q^{-c t} [f X]` for `X` of weight
`t + 1`. -/
def opF (ε : ℤ) (c : ℤ → ℤ) : D.KMod ε →ₗ[Rq] D.KMod ε :=
  (Submodule.span Rq (D.relSet ε)).liftQ
    (Finsupp.linearCombination Rq fun b : D.Ob => tq (-c (b.1 - 1)) • clsOb ε (D.fOb b)) (by
      rw [Submodule.span_le]
      rintro x ((⟨t, X, Y, hX, hY, rfl⟩ | ⟨t, X, hX, a, rfl⟩) | ⟨t, X, Y, hX, e, rfl⟩) <;>
        obtain ⟨r, rfl⟩ : ∃ r, t = r + 1 := ⟨t - 1, by omega⟩ <;>
        simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul,
          Finsupp.linearCombination_single, one_smul, fOb_succ, add_sub_cancel_right]
      · rw [clsOb_iso' (D.P_f r (D.P_biprod (r + 1) hX hY)) (D.P_biprod r (D.P_f r hX) (D.P_f r hY))
          (D.fBiprod r X Y), clsOb_biprod (D.P_f r hX) (D.P_f r hY), smul_add]
        abel
      · rw [clsOb_iso' (D.P_f r (D.P_shift (r + 1) a hX)) (D.P_shift r a (D.P_f r hX))
          (D.fShift r X a), clsOb_shift (D.P_f r hX) a, smul_comm, sub_self]
      · rw [clsOb_iso' (D.P_f r hX) (D.P_f r (D.P_iso (r + 1) hX e)) ((D.f r).mapIso e), sub_self])

theorem opE_clsOb (c : ℤ → ℤ) {t : ℤ} {X : C t} (hX : D.P t X) :
    D.opE ε c (clsOb ε ⟨t, X, hX⟩) = tq (c t) • clsOb ε ⟨t + 1, (D.e t).obj X, D.P_e t hX⟩ := by
  simp only [opE, clsOb, Submodule.liftQ_apply, Finsupp.linearCombination_single, one_smul]; rfl

theorem opF_clsOb (c : ℤ → ℤ) {r : ℤ} {X : C (r + 1)} (hX : D.P (r + 1) X) :
    D.opF ε c (clsOb ε ⟨r + 1, X, hX⟩) = tq (-c r) • clsOb ε ⟨r, (D.f r).obj X, D.P_f r hX⟩ := by
  simp only [opF, clsOb, Submodule.liftQ_apply, Finsupp.linearCombination_single, one_smul,
    fOb_succ, add_sub_cancel_right]

variable (D) in
/-- The weight-`t` subspace of `K ⊗ K_⊕`: the span of the classes of test objects in `C t`. -/
def wtSp (ε : ℤ) (t : ℤ) : Submodule Rq (D.KMod ε) :=
  Submodule.span Rq (Set.range fun X : {X : C t // D.P t X} => clsOb ε ⟨t, X⟩)

theorem clsOb_mem_wtSp {t : ℤ} {X : C t} (hX : D.P t X) : clsOb ε ⟨t, X, hX⟩ ∈ D.wtSp ε t :=
  Submodule.subset_span ⟨⟨X, hX⟩, rfl⟩

theorem wtSp_le {t : ℤ} {p : Submodule Rq (D.KMod ε)}
    (h : ∀ (X : C t) (hX : D.P t X), clsOb ε ⟨t, X, hX⟩ ∈ p) : D.wtSp ε t ≤ p := by
  rw [wtSp, Submodule.span_le]
  rintro _ ⟨⟨X, hX⟩, rfl⟩
  exact h X hX

theorem tq_smul_tq_neg {M : Type*} [AddCommGroup M] [Module Rq M] (a : ℤ) (x : M) :
    tq a • tq (-a) • x = x := by
  rw [smul_smul, ← map_mul, ← T_add, add_neg_cancel, T_zero, map_one, one_smul]

theorem tq_neg_smul_tq {M : Type*} [AddCommGroup M] [Module Rq M] (a : ℤ) (x : M) :
    tq (-a) • tq a • x = x := by
  rw [smul_smul, ← map_mul, ← T_add, neg_add_cancel, T_zero, map_one, one_smul]

variable (D) in
/-- **`K ⊗ K_⊕` is a weight module for `U̇(sl₂)`** (condition (3) gives `EF - FE = [n₀ + 2t]`). -/
def wtModule (ε : ℤ) (hε : ε = 1 ∨ ε = -1) (c : ℤ → ℤ) : WtModuleR Rq Tors.qInts (D.KMod ε) where
  n₀ := D.n₀
  E := D.opE ε c
  F := D.opF ε c
  Wt := D.wtSp ε
  E_mem t := by
    intro v hv
    refine wtSp_le (p := (D.wtSp ε (t + 1)).comap (D.opE ε c)) (fun X hX => ?_) hv
    rw [Submodule.mem_comap, opE_clsOb]
    exact Submodule.smul_mem _ _ (clsOb_mem_wtSp _)
  F_mem t := by
    intro v hv
    refine wtSp_le (p := (D.wtSp ε t).comap (D.opF ε c)) (fun X hX => ?_) hv
    rw [Submodule.mem_comap, opF_clsOb]
    exact Submodule.smul_mem _ _ (clsOb_mem_wtSp _)
  rel t := by
    intro v hv
    have h : v ∈ LinearMap.ker (D.opE ε c ∘ₗ D.opF ε c - D.opF ε c ∘ₗ D.opE ε c -
        Tors.qInts.qi (D.n₀ + 2 * t) • LinearMap.id) := by
      refine wtSp_le (fun X hX => ?_) hv
      obtain ⟨r, rfl⟩ : ∃ r, t = r + 1 := ⟨t - 1, by omega⟩
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
        LinearMap.id_apply]
      rw [opF_clsOb, map_smul, opE_clsOb, tq_neg_smul_tq, opE_clsOb, map_smul, opF_clsOb,
        tq_smul_tq_neg, sub_eq_zero]
      rcases le_total 0 (D.n₀ + 2 * (r + 1)) with hm | hm
      · obtain ⟨i⟩ := D.EF r X hm
        rw [clsOb_iso' _ (D.P_biprod (r + 1) (D.P_f (r + 1) (D.P_e (r + 1) hX)) (P_qsum hX 1 _)) i,
          clsOb_biprod (D.P_f (r + 1) (D.P_e (r + 1) hX)) (P_qsum hX 1 _), clsOb_qsum hε hX,
          Int.toNat_of_nonneg hm]
        abel
      · obtain ⟨i⟩ := D.FE r X hm
        rw [clsOb_iso' _ (D.P_biprod (r + 1) (D.P_e r (D.P_f r hX)) (P_qsum hX 1 _)) i,
          clsOb_biprod (D.P_e r (D.P_f r hX)) (P_qsum hX 1 _), clsOb_qsum hε hX,
          Int.toNat_of_nonneg (by omega), Tors.qiR_neg, neg_smul]
        abel
    have := LinearMap.mem_ker.1 h
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero] at this
    exact this
  bdd := by
    obtain ⟨N, hN⟩ := D.bdd
    refine ⟨N, fun t ht v hv => ?_⟩
    have : D.wtSp ε t ≤ ⊥ := wtSp_le fun X hX => by
      rw [clsOb_of_isZero hX (hN t ht X)]; exact Submodule.zero_mem _
    simpa using this hv


/-! ### Classes span; the pairing -/

theorem iSup_wtSp (ε : ℤ) : ⨆ t, D.wtSp ε t = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    induction x using Finsupp.induction_linear with
    | zero => exact Submodule.zero_mem _
    | add f g hf hg => rw [Submodule.Quotient.mk_add]; exact Submodule.add_mem _ hf hg
    | single b c =>
      have e : Finsupp.single b c = c • Finsupp.single b (1 : Rq) := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [e, Submodule.Quotient.mk_smul]
      exact Submodule.smul_mem _ _
        (Submodule.mem_iSup_of_mem b.1 (clsOb_mem_wtSp (ε := ε) b.2.2))

theorem pairOb_biprod_right [∀ t, HomFinite k (C t)] [∀ t (n : ℤ), (shiftFunctor (C t) n).Additive]
    (b : D.Ob) {t : ℤ} {Z W : C t} (hZ : D.P t Z) (hW : D.P t W) :
    D.pairOb b ⟨t, Z ⊞ W, D.P_biprod t hZ hW⟩ = D.pairOb b ⟨t, Z, hZ⟩ + D.pairOb b ⟨t, W, hW⟩ := by
  obtain ⟨t₀, X, hX⟩ := b
  by_cases h : t = t₀
  · subst h
    rw [pairOb_same, pairOb_same, pairOb_same, ser_biprod_right]
  · rw [pairOb_ne _ _ h, pairOb_ne _ _ h, pairOb_ne _ _ h, add_zero]

theorem pairOb_shift_right (b : D.Ob) {t : ℤ} {Z : C t} (hZ : D.P t Z) (a : ℤ) :
    D.pairOb b ⟨t, Z⟦a⟧, D.P_shift t a hZ⟩ = tq (-a) • D.pairOb b ⟨t, Z, hZ⟩ := by
  obtain ⟨t₀, X, hX⟩ := b
  by_cases h : t = t₀
  · subst h
    rw [pairOb_same, pairOb_same, ser_shift_right]
  · rw [pairOb_ne _ _ h, pairOb_ne _ _ h, smul_zero]

theorem pairOb_iso_right (b : D.Ob) {t : ℤ} {Z Z' : C t} (hZ : D.P t Z) (e : Z ≅ Z') :
    D.pairOb b ⟨t, Z', D.P_iso t hZ e⟩ = D.pairOb b ⟨t, Z, hZ⟩ := by
  obtain ⟨t₀, X, hX⟩ := b
  by_cases h : t = t₀
  · subst h
    rw [pairOb_same, pairOb_same, ser_iso_right hX hZ e]
  · rw [pairOb_ne _ _ h, pairOb_ne _ _ h]

theorem pairOb_biprod_left [∀ t, HomFinite k (C t)]
    {t : ℤ} {X Y : C t} (hX : D.P t X) (hY : D.P t Y) (b : D.Ob) :
    D.pairOb ⟨t, X ⊞ Y, D.P_biprod t hX hY⟩ b = D.pairOb ⟨t, X, hX⟩ b + D.pairOb ⟨t, Y, hY⟩ b := by
  obtain ⟨t₀, Z, hZ⟩ := b
  by_cases h : t₀ = t
  · subst h
    rw [pairOb_same, pairOb_same, pairOb_same, ser_biprod_left]
  · rw [pairOb_ne _ _ h, pairOb_ne _ _ h, pairOb_ne _ _ h, add_zero]

theorem pairOb_shift_left [∀ t (n : ℤ), (shiftFunctor (C t) n).Additive] [∀ t (n : ℤ), (shiftFunctor (C t) n).Linear k]
    {t : ℤ} {X : C t} (hX : D.P t X) (a : ℤ) (b : D.Ob) :
    D.pairOb ⟨t, X⟦a⟧, D.P_shift t a hX⟩ b = tq a • D.pairOb ⟨t, X, hX⟩ b := by
  obtain ⟨t₀, Z, hZ⟩ := b
  by_cases h : t₀ = t
  · subst h
    rw [pairOb_same, pairOb_same, ser_shift_left]
  · rw [pairOb_ne _ _ h, pairOb_ne _ _ h, smul_zero]

theorem pairOb_iso_left {t : ℤ} {X X' : C t} (hX : D.P t X) (e : X ≅ X') (b : D.Ob) :
    D.pairOb ⟨t, X', D.P_iso t hX e⟩ b = D.pairOb ⟨t, X, hX⟩ b := by
  obtain ⟨t₀, Z, hZ⟩ := b
  by_cases h : t₀ = t
  · subst h
    rw [pairOb_same, pairOb_same, ser_iso_left hX e hZ]
  · rw [pairOb_ne _ _ h, pairOb_ne _ _ h]

variable (D) in
/-- The Hom-series `⟨b, -⟩` as a linear form on `K ⊗ K_⊕` with `q ↦ ⟨-1⟩`. -/
def pairRight [∀ t, HomFinite k (C t)] [∀ t (n : ℤ), (shiftFunctor (C t) n).Additive]
    (b : D.Ob) : D.KMod (-1) →ₗ[Rq] MSeq :=
  (Submodule.span Rq (D.relSet (-1))).liftQ
    (Finsupp.linearCombination Rq fun b' : D.Ob => D.pairOb b b') (by
      rw [Submodule.span_le]
      rintro x ((⟨t, X, Y, hX, hY, rfl⟩ | ⟨t, X, hX, a, rfl⟩) | ⟨t, X, Y, hX, e, rfl⟩) <;>
        simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul,
          Finsupp.linearCombination_single, one_smul]
      · rw [pairOb_biprod_right b hX hY]; abel
      · rw [pairOb_shift_right b hX a, neg_one_mul, sub_self]
      · rw [pairOb_iso_right b hX e, sub_self])

theorem pairRight_clsOb [∀ t, HomFinite k (C t)] [∀ t (n : ℤ), (shiftFunctor (C t) n).Additive]
    (b b' : D.Ob) : D.pairRight b (clsOb (-1) b') = D.pairOb b b' := by
  simp only [pairRight, clsOb, Submodule.liftQ_apply, Finsupp.linearCombination_single, one_smul]

variable (D) in
/-- **The Hom-series pairing** `Φ : K ⊗ K_⊕ → (K ⊗ K_⊕)^*`, `Φ [X] [Z] = ⟨X, Z⟩`; the source has
`q ↦ ⟨1⟩` and the target `q ↦ ⟨-1⟩` (`⟨X⟨a⟩, Z⟩ = qᵃ ⟨X, Z⟩`, `⟨X, Z⟨a⟩⟩ = q⁻ᵃ ⟨X, Z⟩`). -/
def Φ [∀ t, HomFinite k (C t)] [∀ t (n : ℤ), (shiftFunctor (C t) n).Additive] [∀ t (n : ℤ), (shiftFunctor (C t) n).Linear k]
    : D.KMod 1 →ₗ[Rq] (D.KMod (-1) →ₗ[Rq] MSeq) :=
  (Submodule.span Rq (D.relSet 1)).liftQ
    (Finsupp.linearCombination Rq fun b : D.Ob => D.pairRight b) (by
      rw [Submodule.span_le]
      rintro x ((⟨t, X, Y, hX, hY, rfl⟩ | ⟨t, X, hX, a, rfl⟩) | ⟨t, X, Y, hX, e, rfl⟩) <;>
        simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul,
          Finsupp.linearCombination_single, one_smul] <;>
        rw [sub_eq_zero]
      · rw [sub_eq_iff_eq_add]
        refine KMod.hom_ext fun b => ?_
        rw [LinearMap.add_apply, pairRight_clsOb, pairRight_clsOb, pairRight_clsOb,
          pairOb_biprod_left, add_comm]
      · refine KMod.hom_ext fun b => ?_
        rw [LinearMap.smul_apply, pairRight_clsOb, pairRight_clsOb, pairOb_shift_left, one_mul]
      · refine KMod.hom_ext fun b => ?_
        rw [pairRight_clsOb, pairRight_clsOb, pairOb_iso_left hX e b])

theorem Φ_clsOb [∀ t, HomFinite k (C t)] [∀ t (n : ℤ), (shiftFunctor (C t) n).Additive] [∀ t (n : ℤ), (shiftFunctor (C t) n).Linear k]
    (b b' : D.Ob) : D.Φ (clsOb 1 b) (clsOb (-1) b') = D.pairOb b b' := by
  simp only [Φ, clsOb, Submodule.liftQ_apply, Finsupp.linearCombination_single, one_smul]
  exact pairRight_clsOb b b'

end Sl2CatData₀

/-! ## The numerical adjunction up to torsion, and exactly under one-sided boundedness -/

namespace Sl2CatData₀

variable {D : Sl2CatData₀ k C}

/-- The rescaling of the operators on the second module: `E [Z] = q^{n₀ + 2t + 1} [e Z]`. -/
def resc (D : Sl2CatData₀ k C) (t : ℤ) : ℤ := D.n₀ + 2 * t + 1

variable [∀ t, HomFinite k (C t)] [∀ t (n : ℤ), (shiftFunctor (C t) n).Additive]
  [∀ t (n : ℤ), (shiftFunctor (C t) n).Linear k]

/-- **The numerical adjunction in `MSeq`**: `⟨f X, Z⟩ = T^{n₀ + 2t + 1} ⟨X, e Z⟩` after inverting
the quantum integers. -/
theorem ser_f_eq {t : ℤ} {X : C (t + 1)} {Z : C t} (hX : D.P (t + 1) X) (hZ : D.P t Z) :
    ser (D.P_f t hX) hZ = tq (D.n₀ + 2 * t + 1) • ser hX (D.P_e t hZ) := by
  set M := D.wtModule 1 (Or.inl rfl) (fun _ => 0) with hM
  set M' := (D.wtModule (-1) (Or.inr rfl) D.resc).homDual MSeq (iSup_wtSp (-1)) with hM'
  have hΦ : ∀ t, ∀ v ∈ M.Wt t, D.Φ v ∈ M'.Wt t := by
    intro t v hv
    refine wtSp_le (p := (M'.Wt t).comap D.Φ) (fun X hX => ?_) hv
    rw [Submodule.mem_comap]
    intro s hs w hw
    refine wtSp_le (p := LinearMap.ker (D.Φ (clsOb 1 ⟨t, X, hX⟩))) (fun Z hZ => ?_) hw
    rw [LinearMap.mem_ker, Φ_clsOb, pairOb_ne _ _ hs]
  have hΦE : ∀ v, D.Φ (M.E v) = M'.E (D.Φ v) := by
    intro v
    have : D.Φ ∘ₗ M.E = M'.E ∘ₗ D.Φ := by
      refine KMod.hom_ext fun b => ?_
      obtain ⟨t, X, hX⟩ := b
      refine KMod.hom_ext fun b' => ?_
      obtain ⟨t', Z, hZ⟩ := b'
      obtain ⟨r, rfl⟩ : ∃ r, t' = r + 1 := ⟨t' - 1, by omega⟩
      change D.Φ (D.opE 1 (fun _ => 0) (clsOb 1 ⟨t, X, hX⟩)) (clsOb (-1) ⟨r + 1, Z, hZ⟩) =
        D.Φ (clsOb 1 ⟨t, X, hX⟩) (D.opF (-1) D.resc (clsOb (-1) ⟨r + 1, Z, hZ⟩))
      rw [opE_clsOb, opF_clsOb, tq_zero, one_smul, map_smul, Φ_clsOb, Φ_clsOb]
      by_cases h : r = t
      · subst h
        rw [pairOb_same, pairOb_same, ser_adj, resc]
      · rw [pairOb_ne _ _ h, pairOb_ne _ _ (by omega), smul_zero]
    exact LinearMap.congr_fun this v
  have key := WtModuleR.F_comm_of_E_comm (M := M) (M' := M') rfl D.Φ hΦ hΦE
    (clsOb_mem_wtSp (ε := 1) hX)
  have key' := LinearMap.congr_fun key (clsOb (-1) ⟨t, Z, hZ⟩)
  change D.Φ (D.opF 1 (fun _ => 0) (clsOb 1 ⟨t + 1, X, hX⟩)) (clsOb (-1) ⟨t, Z, hZ⟩) =
    D.Φ (clsOb 1 ⟨t + 1, X, hX⟩) (D.opE (-1) D.resc (clsOb (-1) ⟨t, Z, hZ⟩)) at key'
  rw [opF_clsOb, opE_clsOb] at key'
  simp only [neg_zero, tq_zero, one_smul] at key'
  rw [map_smul, Φ_clsOb, Φ_clsOb, pairOb_same, pairOb_same, resc] at key'
  exact key'

/-- **The defect of the numerical adjunction is quantum-integer torsion**: the sequence
`d ↦ dim Hom(f X, Z⟨d⟩) - dim Hom(X, (e Z)⟨d - (n₀ + 2t + 1)⟩)` maps to zero in `MSeq`, i.e. it is
killed by a product of quantum integers. No boundedness is assumed. -/
theorem seq_f_torsion {t : ℤ} {X : C (t + 1)} {Z : C t} (hX : D.P (t + 1) X) (hZ : D.P t Z) :
    toM (seq (k := k) ((D.f t).obj X) Z -
      (T (D.n₀ + 2 * t + 1) : R₀) • seq (k := k) X ((D.e t).obj Z)) = 0 := by
  have h := ser_f_eq hX hZ
  rw [ser_def, ser_def, tq_smul_toM] at h
  rw [map_sub, h, sub_self]

/-- **The numerical adjunction holds exactly under one-sided boundedness**: if one of the two
sequences `d ↦ dim Hom(f X, Z⟨d⟩)`, `d ↦ dim Hom(X, (e Z)⟨d⟩)` vanishes for `d ≪ 0`, then
`dim Hom(f X, Z⟨d⟩) = dim Hom(X, (e Z)⟨d - (n₀ + 2t + 1)⟩)` for all `d`. -/
theorem finrank_f_eq_of_bdd {t : ℤ} {X : C (t + 1)} {Z : C t} (hX : D.P (t + 1) X)
    (hZ : D.P t Z)
    (hb : (∃ N : ℤ, ∀ d, d < N → finrank k ((D.f t).obj X ⟶ Z⟦d⟧) = 0) ∨
      (∃ N : ℤ, ∀ d, d < N → finrank k (X ⟶ ((D.e t).obj Z)⟦d⟧) = 0)) (d : ℤ) :
    finrank k ((D.f t).obj X ⟶ Z⟦d⟧) =
      finrank k (X ⟶ ((D.e t).obj Z)⟦d - (D.n₀ + 2 * t + 1)⟧) := by
  set c := D.n₀ + 2 * t + 1 with hc
  set δ : Tors.Seq := seq (k := k) ((D.f t).obj X) Z - (T c : R₀) • seq (k := k) X ((D.e t).obj Z)
    with hδdef
  have hδ : toM δ = 0 := seq_f_torsion hX hZ
  have hδd : ∀ d, δ d = (finrank k ((D.f t).obj X ⟶ Z⟦d⟧) : ℚ) -
      (finrank k (X ⟶ ((D.e t).obj Z)⟦d - c⟧) : ℚ) := by
    intro d
    change seq (k := k) ((D.f t).obj X) Z d - ((T c : R₀) • seq (k := k) X ((D.e t).obj Z)) d = _
    rw [Tors.T_smul_apply]; rfl
  have h0 : δ = 0 := by
    rcases hb with ⟨N, hN⟩ | ⟨N, hN⟩
    · have := Tors.eq_zero_of_toM_eq_zero (s := -δ) (by rw [map_neg, hδ, neg_zero]) (d₀ := N - 1)
        (fun d hd => by
          change 0 ≤ -(δ d)
          rw [hδd, hN d (by omega)]; simp)
      exact neg_eq_zero.1 this
    · exact Tors.eq_zero_of_toM_eq_zero hδ (d₀ := N + c - 1) (fun d hd => by
        rw [hδd, hN (d - c) (by omega)]; simp)
  have : δ d = 0 := by rw [h0]; rfl
  rw [hδd] at this
  exact_mod_cast sub_eq_zero.1 this

end Sl2CatData₀

end Categorification.TwoRep

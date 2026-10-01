/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.Basic
import Categorification.TwoRep.WeightModule
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.RingTheory.LaurentSeries

/-!
# The numerical adjunction: Hom-series and the `sl₂` lemma

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, §3 (the adjoint induction, eq. (3.2) `eq:ind_hyp`, Proposition 3.9
`prop:lradj`). This file proves, in an abstract setting, the *numerical* form of the missing left
adjunction: if a family of graded `k`-linear categories `C t` (`t ∈ ℤ`, "weight `n₀ + 2t`") carries
functors `e t : C t ⥤ C (t+1)`, `f t : C (t+1) ⥤ C t` satisfying CL's condition (3)
(`e f ≅ f e ⊕ [m] 𝟙` for `m ≥ 0`, `f e ≅ e f ⊕ [-m] 𝟙` for `m ≤ 0`, as abstract isomorphisms), the
formal adjunction `e ⊣ f` *at the level of Hom-dimensions with the shift `n₀ + 2t + 1`*
(`Sl2CatData.adj`), integrability, and **bounded-below Hom spaces** (`Sl2CatData.bb`, on a class
`P` of test objects closed under the operations), then `f` is also *left* adjoint to `e` at the
level of Hom-dimensions, with the opposite shift (`Sl2CatData.finrank_f_eq`):

`dim Hom(f X, Z⟨d⟩) = dim Hom(X, (e Z)⟨d - (n₀ + 2t + 1)⟩)`.

Applied to the Hom categories of a strong 2-representation (left and right composition with `E`,
`F`, `WordGen.lean`) this is exactly the Lean predicate `DimAdj k ((F 1_n)⟨-n-1⟩) (E 1_n)` on
word-generated test objects, i.e. the numerical shadow of (3.2) at *every* weight `n`.

## Proof

Everything is linearised over `K = ℚ((q))` (`LSer`), with `q` generic (`isGenericParam_q`).

* `KMod D ε κ` is `K ⊗ K_⊕(P)`, the split Grothendieck group of the objects in `P` with
  coefficients in `K`, `q` acting as the shift `⟨ε⟩` (`ε = ±1`), and with operators
  `E [X] = κ⁻¹ [e X]`, `F [X] = κ [f X]` (`κ` a family of rescalings). Condition (3) makes it a
  `WtModule` (`KMod.wtModule`), i.e. `EF - FE = [n₀ + 2t]` on weight `t`.
* The **Hom-series** `⟨X, Z⟩ = ∑_d dim Hom(X, Z⟨d⟩) qᵈ ∈ ℚ((q))` (`ser`; it is a Laurent series
  by the bounded-below hypothesis) is additive, iso-invariant and satisfies
  `⟨X⟨a⟩, Z⟩ = qᵃ ⟨X, Z⟩`, `⟨X, Z⟨a⟩⟩ = q⁻ᵃ ⟨X, Z⟩`; it gives a `K`-linear map
  `Φ : KMod D 1 1 → (KMod D (-1) κ')^*` (`Φ`), `κ' t = q^{-(n₀ + 2t + 1)}`.
* The dual `(KMod D (-1) κ')^*` with `E^† = (− ∘ F)`, `F^† = (− ∘ E)` is again a `WtModule`
  (`dualWtModule`), the formal adjunction says that `Φ` commutes with `E`
  (`Φ_E`), and `WtModule.F_comm_of_E_comm` (`WeightModule.lean`) gives that `Φ` commutes with
  `F`, which is the claim, coefficient by coefficient.

This is the proof of Theorem C of the private research notes (an `E`-equivariant weight-preserving
map between integrable `U̇(sl₂)`-modules is `F`-equivariant), with the `sl₂` lemma proved there by
complete reducibility replaced by the elementary argument of `WeightModule.lean`.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits Module
open KrullSchmidtCat (HomFinite)
open ZeroObject

/-! ## Laurent series -/

/-- The coefficient field `ℚ((q))`. -/
abbrev LSer := LaurentSeries ℚ

/-- The variable `q = single 1 1 ∈ ℚ((q))`. -/
def qL : LSer := HahnSeries.single 1 1

theorem qL_zpow (n : ℤ) : qL ^ n = HahnSeries.single n 1 := by
  rw [qL, ← RatFunc.single_zpow]

theorem isGenericParam_q : IsGenericParam qL where
  ne_zero := HahnSeries.single_ne_zero one_ne_zero
  pow_ne_one m hm := by
    rw [qL_zpow, ← HahnSeries.single_zero_one]
    intro h
    have := congrArg (fun s : LSer => s.coeff (2 * m)) h
    simp only [HahnSeries.coeff_single_same] at this
    rw [HahnSeries.coeff_single_of_ne (by omega)] at this
    exact one_ne_zero this

theorem coeff_qL_zpow_mul (a d : ℤ) (s : LSer) : (qL ^ a * s).coeff d = s.coeff (d - a) := by
  rw [qL_zpow, show d = (d - a) + a by ring, HahnSeries.coeff_single_mul_add, one_mul,
    add_sub_cancel_right]

/-! ## The abstract setting -/

universe u v

variable (k : Type*) [Field k] (C : ℤ → Type u) [∀ t, Category.{v} (C t)]
  [∀ t, Preadditive (C t)] [∀ t, Linear k (C t)] [∀ t, HasShift (C t) ℤ]
  [∀ t (n : ℤ), (shiftFunctor (C t) n).Additive] [∀ t (n : ℤ), (shiftFunctor (C t) n).Linear k]
  [∀ t, HasZeroObject (C t)] [∀ t, HasBinaryBiproducts (C t)] [∀ t, HomFinite k (C t)]

/-- **Categorified `sl₂`-weight data**: graded `k`-linear categories `C t` of weight `n₀ + 2t`,
functors `e t : C t ⥤ C (t + 1)` and `f t : C (t + 1) ⥤ C t` commuting with sums and shifts,
condition (3) of CL Definition 1.2, the formal adjunction `e ⊣ f` at the level of Hom-dimensions
(with the shift `n₀ + 2t + 1` of CL eq. `eq_defF`), integrability, and a class `P` of test objects
closed under the operations, whose Hom spaces are bounded below in degree. -/
structure Sl2CatData where
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
  /-- **Bounded-below Hom spaces** between test objects. -/
  bb : ∀ t {X Z : C t}, P t X → P t Z → BddBelow (Function.support fun d : ℤ => finrank k (X ⟶ Z⟦d⟧))

variable {k C}

namespace Sl2CatData

variable (D : Sl2CatData k C)

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

/-- **The Hom-series** `⟨X, Z⟩ = ∑_d dim Hom(X, Z⟨d⟩) qᵈ`, a Laurent series by the bounded-below
hypothesis. -/
def ser {t : ℤ} {X Z : C t} (hX : D.P t X) (hZ : D.P t Z) : LSer :=
  HahnSeries.ofSuppBddBelow (fun d : ℤ => (finrank k (X ⟶ Z⟦d⟧) : ℚ)) (by
    obtain ⟨b, hb⟩ := D.bb t hX hZ
    exact ⟨b, fun d hd => hb (by simpa [Function.mem_support] using hd)⟩)

theorem coeff_ser {t : ℤ} {X Z : C t} (hX : D.P t X) (hZ : D.P t Z) (d : ℤ) :
    (ser hX hZ).coeff d = (finrank k (X ⟶ Z⟦d⟧) : ℚ) := rfl

theorem ser_ext {t : ℤ} {X Z X' Z' : C t} {hX : D.P t X} {hZ : D.P t Z} {hX' : D.P t X'}
    {hZ' : D.P t Z'} (h : ∀ d : ℤ, finrank k (X ⟶ Z⟦d⟧) = finrank k (X' ⟶ Z'⟦d⟧)) :
    ser hX hZ = ser hX' hZ' := by
  ext d; rw [coeff_ser, coeff_ser, h]

theorem ser_biprod_left {t : ℤ} {X Y Z : C t} (hX : D.P t X) (hY : D.P t Y) (hZ : D.P t Z) :
    ser (D.P_biprod t hX hY) hZ = ser hX hZ + ser hY hZ := by
  ext d; simp only [coeff_ser, HahnSeries.coeff_add, finrank_hom_biprod_left]; push_cast; rfl

theorem ser_biprod_right {t : ℤ} {X Z W : C t} (hX : D.P t X) (hZ : D.P t Z) (hW : D.P t W) :
    ser hX (D.P_biprod t hZ hW) = ser hX hZ + ser hX hW := by
  ext d
  simp only [coeff_ser, HahnSeries.coeff_add]
  rw [finrank_hom_congr_right k X (mapBiprodIso (shiftFunctor (C t) d) Z W),
    finrank_hom_biprod_right]
  push_cast; rfl

theorem ser_iso_left {t : ℤ} {X X' Z : C t} (hX : D.P t X) (e : X ≅ X') (hZ : D.P t Z) :
    ser (D.P_iso t hX e) hZ = ser hX hZ :=
  ser_ext fun _ => (finrank_hom_congr_left k e _).symm

theorem ser_iso_right {t : ℤ} {X Z Z' : C t} (hX : D.P t X) (hZ : D.P t Z) (e : Z ≅ Z') :
    ser hX (D.P_iso t hZ e) = ser hX hZ :=
  ser_ext fun d => (finrank_hom_congr_right k X ((shiftFunctor _ d).mapIso e)).symm

theorem ser_shift_left {t : ℤ} {X Z : C t} (hX : D.P t X) (hZ : D.P t Z) (a : ℤ) :
    ser (D.P_shift t a hX) hZ = qL ^ a * ser hX hZ := by
  ext d
  rw [coeff_qL_zpow_mul, coeff_ser, coeff_ser, finrank_hom_shift_shift k _ _ (c := d - a) (by ring)]

theorem ser_shift_right {t : ℤ} {X Z : C t} (hX : D.P t X) (hZ : D.P t Z) (a : ℤ) :
    ser hX (D.P_shift t a hZ) = qL ^ (-a) * ser hX hZ := by
  ext d
  rw [coeff_qL_zpow_mul, coeff_ser, coeff_ser,
    show finrank k (X ⟶ (Z⟦a⟧)⟦d⟧) = finrank k (X ⟶ Z⟦a + d⟧) from
      finrank_hom_congr_right k X ((shiftFunctorAdd' (C t) a d (a + d) rfl).app Z).symm,
    finrank_hom_shift_congr k _ _ (show a + d = d - -a by ring)]

theorem ser_adj {t : ℤ} {X : C t} {Z : C (t + 1)} (hX : D.P t X) (hZ : D.P (t + 1) Z) :
    ser (D.P_e t hX) hZ = qL ^ (-(D.n₀ + 2 * t + 1)) * ser hX (D.P_f t hZ) := by
  ext d
  rw [coeff_qL_zpow_mul, coeff_ser, coeff_ser, D.adj,
    finrank_hom_shift_congr k _ _ (show d + (D.n₀ + 2 * t + 1) = d - -(D.n₀ + 2 * t + 1) by ring)]

variable (D) in
/-- The Hom-series on test objects (zero between different weights). -/
def pairOb : D.Ob → D.Ob → LSer
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
def relSet (ε : ℤ) : Set (D.Ob →₀ LSer) :=
  {x | ∃ (t : ℤ) (X Y : C t) (hX : D.P t X) (hY : D.P t Y),
      x = Finsupp.single ⟨t, X ⊞ Y, D.P_biprod t hX hY⟩ 1 - Finsupp.single ⟨t, X, hX⟩ 1 -
        Finsupp.single ⟨t, Y, hY⟩ 1} ∪
  {x | ∃ (t : ℤ) (X : C t) (hX : D.P t X) (a : ℤ),
      x = Finsupp.single ⟨t, X⟦a⟧, D.P_shift t a hX⟩ 1 - qL ^ (ε * a) • Finsupp.single ⟨t, X, hX⟩ 1} ∪
  {x | ∃ (t : ℤ) (X Y : C t) (hX : D.P t X) (e : X ≅ Y),
      x = Finsupp.single ⟨t, X, hX⟩ 1 - Finsupp.single ⟨t, Y, D.P_iso t hX e⟩ 1}

variable (D) in
/-- **`K ⊗ K_⊕(P)`**, the split Grothendieck group of the test objects with coefficients in
`K = ℚ((q))`, `q` acting as the shift `⟨ε⟩`. -/
abbrev KMod (ε : ℤ) := (D.Ob →₀ LSer) ⧸ Submodule.span LSer (D.relSet ε)

variable {ε : ℤ}

/-- The class of a test object. -/
def clsOb (ε : ℤ) (b : D.Ob) : D.KMod ε := Submodule.Quotient.mk (Finsupp.single b 1)

theorem KMod.hom_ext {M : Type*} [AddCommGroup M] [Module LSer M] {φ ψ : D.KMod ε →ₗ[LSer] M}
    (h : ∀ b, φ (clsOb ε b) = ψ (clsOb ε b)) : φ = ψ := by
  refine Submodule.linearMap_qext _ (Finsupp.lhom_ext fun b c => ?_)
  have e : Finsupp.single b c = c • Finsupp.single b (1 : LSer) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, e, map_smul]
  exact congrArg (c • ·) (h b)

theorem mk_eq_zero_of_mem {x : D.Ob →₀ LSer} (hx : x ∈ D.relSet ε) :
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
    clsOb ε ⟨t, X⟦a⟧, D.P_shift t a hX⟩ = qL ^ (ε * a) • clsOb ε ⟨t, X, hX⟩ := by
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
    clsOb ε ⟨t, lsum (L.map fun a => X⟦a⟧), hL⟩ = (L.map fun a => qL ^ (ε * a)).sum • clsOb ε ⟨t, X, hX⟩
  | [], _ => by simpa using clsOb_zero (ε := ε) t
  | a :: L, _ => by
    simp only [List.map_cons, lsum_cons, List.sum_cons, add_smul]
    rw [clsOb_biprod (D.P_shift t a hX) (P_lsum _ fun Y hY => by
        obtain ⟨b, -, rfl⟩ := List.mem_map.1 hY; exact D.P_shift t b hX),
      clsOb_shift, clsOb_lsum_shift hX L]

theorem clsOb_qsum (hε : ε = 1 ∨ ε = -1) {t : ℤ} {X : C t} (hX : D.P t X) (m : ℕ) :
    clsOb ε ⟨t, qsum 1 m X, P_qsum hX 1 m⟩ = qIntZ qL m • clsOb ε ⟨t, X, hX⟩ := by
  have hq : qsum 1 m X = lsum (((List.range m).map fun j : ℕ => 1 * ((m : ℤ) - 1 - 2 * (j : ℤ))).map
      fun a => X⟦a⟧) := by rw [qsum, List.map_map]; rfl
  have hL := D.P_iso t (P_qsum hX 1 m) (eqToIso hq)
  rw [clsOb_iso' (P_qsum hX 1 m) hL (eqToIso hq), clsOb_lsum_shift (ε := ε) hX _ hL, List.map_map,
    list_sum_map_range]
  congr 1
  rcases hε with rfl | rfl
  · rw [← sum_zpow_eq_qIntZ isGenericParam_q m]
    exact Finset.sum_congr rfl fun j _ => by simp only [one_mul, Function.comp_apply]
  · rw [← sum_zpow_neg_eq_qIntZ isGenericParam_q m]
    exact Finset.sum_congr rfl fun j _ => by simp only [one_mul, neg_one_mul, Function.comp_apply]

/-! ### The operators `E`, `F` and the weight module structure -/

variable (D) in
/-- The raising operator on `K ⊗ K_⊕`, rescaled: `E [X] = q^{c t} [e X]` for `X` of weight `t`. -/
def opE (ε : ℤ) (c : ℤ → ℤ) : D.KMod ε →ₗ[LSer] D.KMod ε :=
  (Submodule.span LSer (D.relSet ε)).liftQ
    (Finsupp.linearCombination LSer fun b : D.Ob => qL ^ (c b.1) • clsOb ε (D.eOb b)) (by
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
def opF (ε : ℤ) (c : ℤ → ℤ) : D.KMod ε →ₗ[LSer] D.KMod ε :=
  (Submodule.span LSer (D.relSet ε)).liftQ
    (Finsupp.linearCombination LSer fun b : D.Ob => qL ^ (-c (b.1 - 1)) • clsOb ε (D.fOb b)) (by
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
    D.opE ε c (clsOb ε ⟨t, X, hX⟩) = qL ^ (c t) • clsOb ε ⟨t + 1, (D.e t).obj X, D.P_e t hX⟩ := by
  simp only [opE, clsOb, Submodule.liftQ_apply, Finsupp.linearCombination_single, one_smul]; rfl

theorem opF_clsOb (c : ℤ → ℤ) {r : ℤ} {X : C (r + 1)} (hX : D.P (r + 1) X) :
    D.opF ε c (clsOb ε ⟨r + 1, X, hX⟩) = qL ^ (-c r) • clsOb ε ⟨r, (D.f r).obj X, D.P_f r hX⟩ := by
  simp only [opF, clsOb, Submodule.liftQ_apply, Finsupp.linearCombination_single, one_smul,
    fOb_succ, add_sub_cancel_right]

variable (D) in
/-- The weight-`t` subspace of `K ⊗ K_⊕`: the span of the classes of test objects in `C t`. -/
def wtSp (ε : ℤ) (t : ℤ) : Submodule LSer (D.KMod ε) :=
  Submodule.span LSer (Set.range fun X : {X : C t // D.P t X} => clsOb ε ⟨t, X⟩)

theorem clsOb_mem_wtSp {t : ℤ} {X : C t} (hX : D.P t X) : clsOb ε ⟨t, X, hX⟩ ∈ D.wtSp ε t :=
  Submodule.subset_span ⟨⟨X, hX⟩, rfl⟩

theorem wtSp_le {t : ℤ} {p : Submodule LSer (D.KMod ε)}
    (h : ∀ (X : C t) (hX : D.P t X), clsOb ε ⟨t, X, hX⟩ ∈ p) : D.wtSp ε t ≤ p := by
  rw [wtSp, Submodule.span_le]
  rintro _ ⟨⟨X, hX⟩, rfl⟩
  exact h X hX

theorem zpow_smul_zpow_neg {M : Type*} [AddCommGroup M] [Module LSer M] (a : ℤ) (x : M) :
    qL ^ a • qL ^ (-a) • x = x := by
  rw [smul_smul, ← zpow_add₀ isGenericParam_q.ne_zero, add_neg_cancel, zpow_zero, one_smul]

theorem zpow_neg_smul_zpow {M : Type*} [AddCommGroup M] [Module LSer M] (a : ℤ) (x : M) :
    qL ^ (-a) • qL ^ a • x = x := by
  rw [smul_smul, ← zpow_add₀ isGenericParam_q.ne_zero, neg_add_cancel, zpow_zero, one_smul]

variable (D) in
/-- **`K ⊗ K_⊕` is a weight module for `U̇(sl₂)`** (condition (3) gives `EF - FE = [n₀ + 2t]`). -/
def wtModule (ε : ℤ) (hε : ε = 1 ∨ ε = -1) (c : ℤ → ℤ) : WtModule LSer qL (D.KMod ε) where
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
        qIntZ qL (D.n₀ + 2 * t) • LinearMap.id) := by
      refine wtSp_le (fun X hX => ?_) hv
      obtain ⟨r, rfl⟩ : ∃ r, t = r + 1 := ⟨t - 1, by omega⟩
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
        LinearMap.id_apply]
      rw [opF_clsOb, map_smul, opE_clsOb, zpow_neg_smul_zpow, opE_clsOb, map_smul, opF_clsOb,
        zpow_smul_zpow_neg, sub_eq_zero]
      rcases le_total 0 (D.n₀ + 2 * (r + 1)) with hm | hm
      · obtain ⟨i⟩ := D.EF r X hm
        rw [clsOb_iso' _ (D.P_biprod (r + 1) (D.P_f (r + 1) (D.P_e (r + 1) hX)) (P_qsum hX 1 _)) i,
          clsOb_biprod (D.P_f (r + 1) (D.P_e (r + 1) hX)) (P_qsum hX 1 _), clsOb_qsum hε,
          Int.toNat_of_nonneg hm]
        abel
      · obtain ⟨i⟩ := D.FE r X hm
        rw [clsOb_iso' _ (D.P_biprod (r + 1) (D.P_e r (D.P_f r hX)) (P_qsum hX 1 _)) i,
          clsOb_biprod (D.P_e r (D.P_f r hX)) (P_qsum hX 1 _), clsOb_qsum hε,
          Int.toNat_of_nonneg (by omega), qIntZ_neg, neg_smul]
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

end Sl2CatData

end Categorification.TwoRep

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.SidewaysCrossing

/-!
# Dotted bubbles and fake bubbles (CL §5.1)

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, §5.1 ("Symmetric functions and dotted bubbles"), eqs. (5.1)–(5.6), and the
fake bubbles of §2.6 (`eq_homo_inf_grass`, `eq_infinite_Grass`).

Fix an object `q + 1` of a strong 2-representation of `sl₂`, of weight `n = wt (q + 1)`, and left
adjunctions `A₀ : R_{n-2} ⊣ E 1_{n-2}` (`E 1_{n-2} = grE q`) and `A₁ : R_n ⊣ E 1_n`
(`E 1_n = grE (q + 1)`). The **dotted bubbles** in the region `n` are

* the clockwise bubble with `j` dots `cwBub A₀ j`: the left cup `1_n → R E` (unit of `A₀`), `j`
  (normalized) dots on `E 1_{n-2}`, the right cap `R E → 1_n`; degree `2 (j + 1 - n)`;
* the counter-clockwise bubble with `j` dots `ccwBub A₁ j`: the right cup `1_n → E R`, `j` dots on
  `E 1_n`, the left cap `E R → 1_n` (counit of `A₁`); degree `2 (j + 1 + n)`.

(With the dots `x` normalized so that the nilHecke relation reads `x τ - τ x = 1`, i.e. CL's
`r_i = 1`; CL §2.6.1 reduce `U_Q(sl₂)` to `r_i = 1` by rescaling.) They vanish in negative degree
(`cwBub_eq_zero`, `ccwBub_eq_zero`, CL (3.4)), and, for the normalized left adjunctions
`leftAdjN`, the degree-zero bubbles are the identity, CL (4.1) (`cwBub_deg_zero`,
`ccwBub_deg_zero`; the counter-clockwise one at `n = -1` is CL's `c_{-1}`, Lemma 5.4).

The **fake bubbles** are bubbles with a negative number of dots and nonnegative degree. As in
KL III and CL (`eq_fake_nleqz`, `eq_fake_ngeqz`, and the definition at `n = 0`), they are defined by
the infinite Grassmannian relation `(∑_a ccw_a t^a)(∑_b cw_b t^b) = 1` (with `cw_b`, `ccw_a` the
bubbles of degree `2b`, `2a`) from the real bubbles of the opposite orientation in lower degree
(`grassInv`). `cwL A₀ A₁ m` and `ccwL A₀ A₁ m` are the bubbles with label `m ∈ ℤ` (real for
`m ≥ 0`, fake for `m < 0` of nonnegative degree, `0` otherwise), exactly as `cwL`, `ccwL` of
`Categorification.Diagrams.KL3.Relations`. CL's `φ^n(e_λ)` are products of real bubbles, and CL
(5.4), (5.5) identify the fake bubbles with `φ^n((-1)^r h_r)`; that identification is the
recursion `grassInv` (`sum_mul_grassInv`).

Endomorphisms of an identity 1-morphism commute (`Bicategory.endId_comm`, Eckmann–Hilton), so
`End(1_n)` is a commutative ring (`endIdCommRing`).

## Main declarations

* `grassInv`, `sum_mul_grassInv`: the infinite Grassmannian recursion;
* `Bicategory.endId_comm`, `GradedHomBicat.endIdCommRing`;
* `StrongSl2.cwBub`, `ccwBub`, `isHomogeneous_cwBub`, `isHomogeneous_ccwBub`, `cwBub_eq_zero`,
  `ccwBub_eq_zero`, `exists_eq_smul_id`;
* `StrongSl2.cwR`, `ccwR`, `cwL`, `ccwL` (fake bubbles), `ccwL_fake`, `cwL_fake`;
* `StrongSl2.cwBub_deg_zero`, `ccwBub_deg_zero`;
* `StrongSl2.grassmannian_cw_ccw`, `grassmannian_ccw_cw`: the infinite Grassmannian
  relation in the degrees where it defines the fake bubbles.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

universe w v u

/-! ## The infinite Grassmannian recursion -/

section Grass

variable {A : Type*} [Ring A]

/-- The solution of `(∑_a c_a t^a)(∑_b x_b t^b) = 1` with `c_0 = 1`: `x_0 = 1`,
`x_{k+1} = -∑_{a ≤ k} c_{a+1} x_{k-a}` (the same recursion as
`Categorification.KL3.Diagram.grassInv`). -/
def grassInv (c : ℕ → A) : ℕ → A
  | 0 => 1
  | k + 1 => -∑ a : Fin (k + 1), c (a.1 + 1) * grassInv c (k - a.1)
decreasing_by all_goals omega

theorem grassInv_zero (c : ℕ → A) : grassInv c 0 = 1 := by
  rw [grassInv]

theorem grassInv_succ (c : ℕ → A) (k : ℕ) :
    grassInv c (k + 1) = -∑ a ∈ Finset.range (k + 1), c (a + 1) * grassInv c (k - a) := by
  rw [grassInv, ← Fin.sum_univ_eq_sum_range (fun a => c (a + 1) * grassInv c (k - a))]

/-- **The infinite Grassmannian relation** in degree `K`: `∑_{a ≤ K} c_a x_{K-a} = δ_{K,0}` for
`x = grassInv c`, if `c_0 = 1`. -/
theorem sum_mul_grassInv (c : ℕ → A) (hc : c 0 = 1) (K : ℕ) :
    ∑ a ∈ Finset.range (K + 1), c a * grassInv c (K - a) = if K = 0 then 1 else 0 := by
  cases K with
  | zero => simp [hc, grassInv_zero]
  | succ K =>
    rw [Finset.sum_range_succ', hc, one_mul, Nat.sub_zero, grassInv_succ]
    simp only [Nat.add_sub_add_right, add_neg_cancel, Nat.add_one_ne_zero, ↓reduceIte]

/-- `grassInv` only depends on `c_a` for `a ≥ 1`. -/
theorem grassInv_congr {c c' : ℕ → A} (h : ∀ a, 1 ≤ a → c a = c' a) : grassInv c = grassInv c' := by
  funext K
  induction K using Nat.strong_induction_on with
  | _ K ih =>
    cases K with
    | zero => rw [grassInv_zero, grassInv_zero]
    | succ K =>
      rw [grassInv_succ, grassInv_succ]
      congr 1
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [h (a + 1) (by omega), ih (K - a) (by omega)]

end Grass

/-! ## Endomorphisms of identity 1-morphisms commute -/

section EndId

/-- **Eckmann–Hilton**: endomorphisms of an identity 1-morphism commute. -/
theorem Bicategory.endId_comm {C : Type u} [Bicategory.{w, v} C] {a : C} (f g : 𝟙 a ⟶ 𝟙 a) :
    f ≫ g = g ≫ f := by
  calc f ≫ g = (ρ_ (𝟙 a)).inv ≫ (f ▷ 𝟙 a ≫ 𝟙 a ◁ g) ≫ (ρ_ (𝟙 a)).hom := by
        simp [unitors_equal]
    _ = (ρ_ (𝟙 a)).inv ≫ (𝟙 a ◁ g ≫ f ▷ 𝟙 a) ≫ (ρ_ (𝟙 a)).hom := by
        rw [whisker_exchange]
    _ = g ≫ f := by simp [unitors_equal]

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B] [GradedBicategory.ShiftCoherence B]

/-- The endomorphisms of an identity 1-morphism of the graded-Hom bicategory form a commutative
ring. -/
instance GradedHomBicat.endIdCommRing (a : GradedHomBicat B) : CommRing (End (𝟙 a)) :=
  { (inferInstance : Ring (End (𝟙 a))) with
    mul_comm := fun f g => (Bicategory.endId_comm g f) }

end EndId

/-! ## Dotted bubbles -/

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [GradedBicategory.ShiftCoherence B] [GradedBicategory.IsLinear B k]

namespace StrongSl2

open GradedHomBicat GradedHomCat Module
open KrullSchmidtCat (HomFinite)

variable (S : StrongSl2 k B)

/-- **The clockwise bubble with `j` dots** at the object `r + 1` (weight `n = wt (r + 1)`), for a
left adjunction `A : R_{n-2} ⊣ E 1_{n-2}`: the left cup (unit of `A`), `j` normalized dots on
`E 1_{n-2}`, the right cap (counit of `E 1_{n-2} ⊣ R_{n-2}`). -/
def cwBub {r : ℤ} (A : S.grR r ⊣ S.grE r) (j : ℕ) :
    𝟙 (of (S.obj (r + 1))) ⟶ 𝟙 (of (S.obj (r + 1))) :=
  A.unit ≫ S.grR r ◁ powComp (S.grDotN r) j ≫ S.grCounit r

/-- **The counter-clockwise bubble with `j` dots** at the object `r` (weight `n = wt r`), for a
left adjunction `A : R_n ⊣ E 1_n`: the right cup (unit of `E 1_n ⊣ R_n`), `j` normalized dots on
`E 1_n`, the left cap (counit of `A`). -/
def ccwBub {r : ℤ} (A : S.grR r ⊣ S.grE r) (j : ℕ) : 𝟙 (of (S.obj r)) ⟶ 𝟙 (of (S.obj r)) :=
  S.grUnit r ≫ powComp (S.grDotN r) j ▷ S.grR r ≫ A.counit

theorem cwBubble_eq_cwBub {r : ℤ} (A : S.grR r ⊣ S.grE r) :
    S.cwBubble A.unit = S.cwBub A ((S.wt (r + 1)).toNat - 1) := rfl

theorem ccwBubble_eq_ccwBub {r : ℤ} (A : S.grR r ⊣ S.grE r) :
    S.ccwBubble A.counit = S.ccwBub A ((-S.wt r).toNat - 1) := rfl

theorem isHomogeneous_grDotN (r : ℤ) : IsHomogeneous (S.grDotN r) 2 :=
  (isHomogeneous_of₂ _ _).smul _

/-- The clockwise bubble with `j` dots has degree `2 (j + 1 - n)`. -/
theorem isHomogeneous_cwBub {r : ℤ} (A : S.grR r ⊣ S.grE r)
    (hu : IsHomogeneous A.unit (-(2 * S.wt r + 2))) (j : ℕ) :
    IsHomogeneous (S.cwBub A j) (2 * ((j : ℤ) + 1 - S.wt (r + 1))) :=
  (hu.comp ((isHomogeneous_whiskerLeft _ (GradedHomBicat.isHomogeneous_powComp
    (S.isHomogeneous_grDotN r) j)).comp (isHomogeneous_incl₂ _) rfl) rfl).of_eq
      (by rw [S.wt_add_one]; ring)

/-- The counter-clockwise bubble with `j` dots has degree `2 (j + 1 + n)`. -/
theorem isHomogeneous_ccwBub {r : ℤ} (A : S.grR r ⊣ S.grE r)
    (hc : IsHomogeneous A.counit (2 * S.wt r + 2)) (j : ℕ) :
    IsHomogeneous (S.ccwBub A j) (2 * ((j : ℤ) + 1 + S.wt r)) :=
  ((isHomogeneous_incl₂ _).comp ((isHomogeneous_whiskerRight (GradedHomBicat.isHomogeneous_powComp
    (S.isHomogeneous_grDotN r) j) _).comp hc rfl) rfl).of_eq (by ring)

/-- A homogeneous endomorphism of `1_n` of degree zero is a scalar (Definition 1.2 (2)). -/
theorem exists_eq_smul_id {r : ℤ} {φ : 𝟙 (of (S.obj r)) ⟶ 𝟙 (of (S.obj r))}
    (hφ : IsHomogeneous φ 0) : ∃ c : k, φ = c • 𝟙 _ := by
  by_cases h2 : IsZero (𝟙 (S.obj r))
  · have hz : IsZero (𝟙 (of (S.obj r))) := (incl _).map_isZero h2
    exact ⟨0, hz.eq_of_src _ _⟩
  obtain ⟨g, hg⟩ := exists_incl₂_of_isHomogeneous hφ
  have hid0 : (𝟙 (𝟙 (S.obj r)) : _) ≠ 0 := fun h0 => h2 ((IsZero.iff_id_eq_zero _).2 h0)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hid0).1 (S.hom_zero _ h2) g
  refine ⟨c, ?_⟩
  rw [hg, ← hc]
  change (incl _).map (c • 𝟙 _) = _
  rw [CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id]
  rfl

/-! ## Bubbles with integer labels, and fake bubbles -/

section Labels

variable {q : ℤ} (A₀ : S.grR q ⊣ S.grE q) (A₁ : S.grR (q + 1) ⊣ S.grE (q + 1))

/-- The real clockwise bubble with label `m` in the region `q + 1`, or `0` if `m < 0`. -/
def cwR (m : ℤ) : End (𝟙 (of (S.obj (q + 1)))) :=
  if 0 ≤ m then S.cwBub A₀ m.toNat else 0

/-- The real counter-clockwise bubble with label `m` in the region `q + 1`, or `0` if `m < 0`. -/
def ccwR (m : ℤ) : End (𝟙 (of (S.obj (q + 1)))) :=
  if 0 ≤ m then S.ccwBub A₁ m.toNat else 0

/-- **The clockwise bubble with label `m ∈ ℤ`** in the region `q + 1` of weight `n`: the real
bubble with `m` dots if `m ≥ 0`; if `m < 0` and its degree `2 (m + 1 - n)` is nonnegative, the
fake bubble defined by the infinite Grassmannian relation from the real counter-clockwise bubbles;
`0` otherwise (CL (5.4), (5.5); KL III `eq_infinite_Grass`). -/
def cwL (m : ℤ) : End (𝟙 (of (S.obj (q + 1)))) :=
  if 0 ≤ m then S.cwBub A₀ m.toNat
  else if 0 ≤ m + 1 - S.wt (q + 1) then
    grassInv (fun a => S.ccwR A₁ (-S.wt (q + 1) - 1 + a)) (m + 1 - S.wt (q + 1)).toNat
  else 0

/-- **The counter-clockwise bubble with label `m ∈ ℤ`** in the region `q + 1` of weight `n`: the
real bubble with `m` dots if `m ≥ 0`; if `m < 0` and its degree `2 (m + 1 + n)` is nonnegative,
the fake bubble defined by the infinite Grassmannian relation from the real clockwise bubbles;
`0` otherwise. -/
def ccwL (m : ℤ) : End (𝟙 (of (S.obj (q + 1)))) :=
  if 0 ≤ m then S.ccwBub A₁ m.toNat
  else if 0 ≤ m + 1 + S.wt (q + 1) then
    grassInv (fun b => S.cwR A₀ (S.wt (q + 1) - 1 + b)) (m + 1 + S.wt (q + 1)).toNat
  else 0

theorem cwL_of_nonneg {m : ℤ} (hm : 0 ≤ m) : S.cwL A₀ A₁ m = S.cwBub A₀ m.toNat := by
  rw [cwL, ite_eq_left hm]

theorem ccwL_of_nonneg {m : ℤ} (hm : 0 ≤ m) : S.ccwL A₀ A₁ m = S.ccwBub A₁ m.toNat := by
  rw [ccwL, ite_eq_left hm]

theorem cwR_of_nonneg {m : ℤ} (hm : 0 ≤ m) : S.cwR A₀ m = S.cwBub A₀ m.toNat := by
  rw [cwR, ite_eq_left hm]

theorem ccwR_of_nonneg {m : ℤ} (hm : 0 ≤ m) : S.ccwR A₁ m = S.ccwBub A₁ m.toNat := by
  rw [ccwR, ite_eq_left hm]

/-- The fake counter-clockwise bubble of degree `2 i` at a weight `n ≥ i`. -/
theorem ccwL_fake {i : ℕ} (hi : (i : ℤ) ≤ S.wt (q + 1)) :
    S.ccwL A₀ A₁ (-S.wt (q + 1) - 1 + i) =
      grassInv (fun b => S.cwR A₀ (S.wt (q + 1) - 1 + b)) i := by
  rw [ccwL, ite_eq_right (by omega), ite_eq_left (by omega)]
  congr 1
  omega

/-- The fake clockwise bubble of degree `2 i` at a weight `n ≤ -i`. -/
theorem cwL_fake {i : ℕ} (hi : (i : ℤ) ≤ -S.wt (q + 1)) :
    S.cwL A₀ A₁ (S.wt (q + 1) - 1 + i) =
      grassInv (fun a => S.ccwR A₁ (-S.wt (q + 1) - 1 + a)) i := by
  rw [cwL, ite_eq_right (by omega), ite_eq_left (by omega)]
  congr 1
  omega

end Labels

variable [∀ a b : B, HomFinite k (a ⟶ b)]

omit [GradedBicategory.IsLinear B k] in
/-- A homogeneous endomorphism of `1_n` of negative degree vanishes (Definition 1.2 (2)). -/
theorem eq_zero_of_isHomogeneous_neg {r : ℤ} {φ : 𝟙 (of (S.obj r)) ⟶ 𝟙 (of (S.obj r))} {d : ℤ}
    (hφ : IsHomogeneous φ d) (hd : d < 0) : φ = 0 :=
  GradedHomBicat.eq_zero_of_isHomogeneous (f := 𝟙 (S.obj r)) (g := 𝟙 (S.obj r)) hφ
    (S.hom_neg r d hd)

/-- **CL (3.4)**: clockwise bubbles of negative degree vanish. -/
theorem cwBub_eq_zero {r : ℤ} (A : S.grR r ⊣ S.grE r)
    (hu : IsHomogeneous A.unit (-(2 * S.wt r + 2))) {j : ℕ} (hj : (j : ℤ) < S.wt (r + 1) - 1) :
    S.cwBub A j = 0 :=
  S.eq_zero_of_isHomogeneous_neg (S.isHomogeneous_cwBub A hu j) (by omega)

/-- **CL (3.4)**: counter-clockwise bubbles of negative degree vanish. -/
theorem ccwBub_eq_zero {r : ℤ} (A : S.grR r ⊣ S.grE r)
    (hc : IsHomogeneous A.counit (2 * S.wt r + 2)) {j : ℕ} (hj : (j : ℤ) < -S.wt r - 1) :
    S.ccwBub A j = 0 :=
  S.eq_zero_of_isHomogeneous_neg (S.isHomogeneous_ccwBub A hc j) (by omega)

/-! ## The normalized bubbles -/

variable {S} [∀ a b : B, IsIdempotentComplete (a ⟶ b)]

variable (S) in
/-- **CL (4.1), clockwise**: for the normalized left adjunctions, the clockwise bubble of degree
zero in the region `n = wt (q + 1) ≥ 1` (with `n - 1` dots) is the identity. -/
theorem cwBub_deg_zero {q : ℤ} (hn : 1 ≤ S.wt (q + 1)) :
    S.cwBub (S.leftAdjN q) ((S.wt (q + 1)).toNat - 1) = 𝟙 _ :=
  (S.leftAdjN_spec q).2.2.1 (by rw [S.wt_add_one] at hn; omega)

variable (S) in
/-- **CL (4.1), counter-clockwise**: for the normalized left adjunctions, the counter-clockwise
bubble of degree zero in the region `n = wt r ≤ -2` (with `-n - 1` dots) is the identity. -/
theorem ccwBub_deg_zero {r : ℤ} (hn : S.wt r ≤ -2) :
    S.ccwBub (S.leftAdjN r) ((-S.wt r).toNat - 1) = 𝟙 _ :=
  (S.leftAdjN_spec r).2.2.2.1 hn

variable (S) in
/-- The clockwise bubbles for the normalized left adjunctions vanish in negative degree. -/
theorem cwBubN_eq_zero {q : ℤ} {j : ℕ} (hj : (j : ℤ) < S.wt (q + 1) - 1) :
    S.cwBub (S.leftAdjN q) j = 0 :=
  S.cwBub_eq_zero _ (S.leftAdjN_spec q).1 hj

variable (S) in
/-- The counter-clockwise bubbles for the normalized left adjunctions vanish in negative degree. -/
theorem ccwBubN_eq_zero {r : ℤ} {j : ℕ} (hj : (j : ℤ) < -S.wt r - 1) :
    S.ccwBub (S.leftAdjN r) j = 0 :=
  S.ccwBub_eq_zero _ (S.leftAdjN_spec r).2.1 hj

variable (S) in
/-- The bubbles with integer labels in the region `q + 1`, for the normalized left adjunctions. -/
abbrev cwLN (q m : ℤ) : End (𝟙 (of (S.obj (q + 1)))) :=
  S.cwL (S.leftAdjN q) (S.leftAdjN (q + 1)) m

variable (S) in
/-- The counter-clockwise bubbles with integer labels in the region `q + 1`, for the normalized
left adjunctions. -/
abbrev ccwLN (q m : ℤ) : End (𝟙 (of (S.obj (q + 1)))) :=
  S.ccwL (S.leftAdjN q) (S.leftAdjN (q + 1)) m

variable (S) in
/-- **The infinite Grassmannian relation where it defines the counter-clockwise fake bubbles**: in
the region `n = wt (q + 1) ≥ 1`, for `K ≤ n`,
`∑_{i ≤ K} (cw bubble of degree 2i) (ccw bubble of degree 2(K - i)) = δ_{K,0}`. -/
theorem grassmannian_cw_ccw {q : ℤ} (hn : 1 ≤ S.wt (q + 1)) {K : ℕ}
    (hK : (K : ℤ) ≤ S.wt (q + 1)) :
    ∑ i ∈ Finset.range (K + 1),
        S.cwLN q (S.wt (q + 1) - 1 + i) * S.ccwLN q (-S.wt (q + 1) - 1 + (K - i : ℕ)) =
      if K = 0 then 1 else 0 := by
  set c : ℕ → End (𝟙 (of (S.obj (q + 1)))) :=
    fun b => S.cwR (S.leftAdjN q) (S.wt (q + 1) - 1 + b) with hc
  have hc0 : c 0 = 1 := by
    rw [hc]
    dsimp only
    rw [cwR_of_nonneg _ _ (by omega), show (S.wt (q + 1) - 1 + ((0 : ℕ) : ℤ)).toNat =
      (S.wt (q + 1)).toNat - 1 by omega, cwBub_deg_zero S hn]
    rfl
  rw [← sum_mul_grassInv c hc0 K]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  unfold cwLN ccwLN
  rw [ccwL_fake _ _ _ (by omega), hc]
  dsimp only
  rw [cwL_of_nonneg _ _ _ (by omega), cwR_of_nonneg _ _ (by omega)]

variable (S) in
/-- **The infinite Grassmannian relation where it defines the clockwise fake bubbles**: in the
region `n = wt (q + 1) ≤ -2`, for `K ≤ -n`,
`∑_{i ≤ K} (ccw bubble of degree 2i) (cw bubble of degree 2(K - i)) = δ_{K,0}`. -/
theorem grassmannian_ccw_cw {q : ℤ} (hn : S.wt (q + 1) ≤ -2) {K : ℕ}
    (hK : (K : ℤ) ≤ -S.wt (q + 1)) :
    ∑ i ∈ Finset.range (K + 1),
        S.ccwLN q (-S.wt (q + 1) - 1 + i) * S.cwLN q (S.wt (q + 1) - 1 + (K - i : ℕ)) =
      if K = 0 then 1 else 0 := by
  set c : ℕ → End (𝟙 (of (S.obj (q + 1)))) :=
    fun a => S.ccwR (S.leftAdjN (q + 1)) (-S.wt (q + 1) - 1 + a) with hc
  have hc0 : c 0 = 1 := by
    rw [hc]
    dsimp only
    rw [ccwR_of_nonneg _ _ (by omega), show (-S.wt (q + 1) - 1 + ((0 : ℕ) : ℤ)).toNat =
      (-S.wt (q + 1)).toNat - 1 by omega, ccwBub_deg_zero S hn]
    rfl
  rw [← sum_mul_grassInv c hc0 K]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  unfold cwLN ccwLN
  rw [cwL_fake _ _ _ (by omega), hc]
  dsimp only
  rw [ccwL_of_nonneg _ _ _ (by omega), ccwR_of_nonneg _ _ (by omega)]

end StrongSl2

end Categorification.TwoRep

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.Basic

/-!
# Strong 2-representations of `sl₂` along a weight string

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3. §3 works with
`g = sl₂` ("In this section we assume `g = sl₂`"), weights `n ∈ ℤ` (§2.6.1, `sec:sl2convs`), and
a `Q`-strong 2-representation in the sense of Definition 1.2 (`def_Qstrong`).

`StrongSl2 k B` is this data along **one `α`-string of weights**. The objects are indexed by
`r ∈ ℤ` and object `r` has weight `n = n₀ + 2 r` (`StrongSl2.wt`); so `𝟙 (obj r)` is CL's `1_n`,
`E r : obj r ⟶ obj (r + 1)` is `E 1_n`, and `F r : obj (r + 1) ⟶ obj r` is `1_n F`. (Indexing by
`r` rather than by the weight `n` lets a string of any parity of a general Cartan datum be
restricted to this structure; for `sl₂` itself, `n₀ = 0` and `n₀ = 1` give the even and odd
weights.) **Composition is written in Mathlib's diagrammatic order**: CL's `E F 1_n` (first `F`,
then `E`) is `F r ≫ E r` here, CL's `F E 1_n` is `E r ≫ F r`.

The fields are the conditions of Definition 1.2 for `I = {i}`:

* `adj r : E r ⊣ (F r)⟦n + 1⟧`: `1_n F := (E 1_n)_R ⟨-n-1⟩` (eq. `eq_defF` with `(α_i, λ) = n`,
  `d_i = 1`); `exists_leftAdj`: `E 1_n` also has a left adjoint;
* `integrable`: condition (1), `1_{n}` is zero for `|r| ≫ 0`;
* `hom_neg`, `hom_zero`: condition (2), `Hom(1_n, 1_n⟨l⟩) = 0` for `l < 0` and one-dimensional
  for `l = 0` **when `1_n` is nonzero** (CL's "Important convention" after Definition 1.2: "to be
  precise, condition (2) above should say that `Hom(1_λ, 1_λ)` is one-dimensional if `λ` is
  non-zero"; a weight is *zero* when its identity 1-morphism is a zero object, `IsZero (𝟙 _)`).
  Finite-dimensionality of all 2-Hom spaces is the instance `[∀ a b, HomFinite k (a ⟶ b)]`;
* `EF`, `FE`: condition (3) at the object `r + 1` of weight `m = n₀ + 2 (r + 1)`:
  `E F 1_m ≅ F E 1_m ⊕_{[m]} 1_m` if `m ≥ 0` and `F E 1_m ≅ E F 1_m ⊕_{[-m]} 1_m` if `m ≤ 0`;
* `dot`, `cross` and the relations `cross_sq`, `dot_slide_left`, `dot_slide_right`, `braid`:
  condition (4), the action of the KLR algebra, which for `I = {i}` is the nilHecke algebra with
  CL's relations `eq_nil_rels` and `eq_nil_dotslide` (the latter with the scalar `r_i`). The dot
  has degree `(α_i, α_i) = 2` and the crossing degree `-(α_i, α_i) = -2`.

Condition (5) is vacuous for `I = {i}`.

## The adjoint induction (CL §3.2, `eq:ind_hyp`)

`AdjHyp S r` is CL's adjoint induction hypothesis (3.2) at the weight `n = wt r`:
`(E 1_n)_L ≅ 1_n F ⟨-n-1⟩`, i.e. `F r⟦-(n+1)⟧ ⊣ E r`. (CL also list
`(1_n F)_R ≅ E 1_n ⟨-n-1⟩`, which is the shift of the same adjunction; at the level of Hom
dimensions, the only level used in §3.2, it is `AdjHyp.dimAdjF`.) `adjoint_induction` is the
decreasing induction "starting from the highest weight" for the weights `n ≥ 0`: the hypothesis
holds vacuously beyond the highest weight (`adjHyp_of_isZero`: "for `m` beyond the highest weight
this claim is vacuously true since both maps are zero"), and integrability makes the induction
well founded.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Module
open KrullSchmidtCat (HomFinite)

universe w v u

variable (k : Type*) [Field k] (B : Type u) [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]

/-- **A strong 2-representation of `sl₂` along a weight string** (CL Definition 1.2 with
`I = {i}`, in the conventions of CL §2.6.1 and §3). See the module docstring for the fields. -/
structure StrongSl2 where
  /-- The weight of object `0`; object `r` has weight `n₀ + 2 r`. -/
  n₀ : ℤ
  /-- The objects of the string. -/
  obj : ℤ → B
  /-- `E 1_n`. -/
  E : ∀ r : ℤ, obj r ⟶ obj (r + 1)
  /-- `1_n F`. -/
  F : ∀ r : ℤ, obj (r + 1) ⟶ obj r
  /-- `1_n F := (E 1_n)_R ⟨-(n+1)⟩` (CL eq. `eq_defF`), i.e. `E 1_n ⊣ 1_n F ⟨n+1⟩`. -/
  adj : ∀ r : ℤ, E r ⊣ (F r)⟦n₀ + 2 * r + 1⟧
  /-- `E 1_n` has a left adjoint (Definition 1.2). -/
  exists_leftAdj : ∀ r : ℤ, ∃ L : obj (r + 1) ⟶ obj r, Nonempty (L ⊣ E r)
  /-- Condition (1), integrability. -/
  integrable : ∃ N : ℕ, ∀ r : ℤ, (N : ℤ) ≤ |r| → IsZero (𝟙 (obj r))
  /-- Condition (2): `Hom(1_n, 1_n⟨l⟩) = 0` for `l < 0`. -/
  hom_neg : ∀ r l : ℤ, l < 0 → finrank k (𝟙 (obj r) ⟶ (𝟙 (obj r))⟦l⟧) = 0
  /-- Condition (2): `Hom(1_n, 1_n)` is one-dimensional if `1_n` is nonzero. -/
  hom_zero : ∀ r : ℤ, ¬ IsZero (𝟙 (obj r)) → finrank k (𝟙 (obj r) ⟶ 𝟙 (obj r)) = 1
  /-- Condition (3) for `m ≥ 0`: `E F 1_m ≅ F E 1_m ⊕_{[m]} 1_m`. -/
  EF : ∀ r : ℤ, 0 ≤ n₀ + 2 * (r + 1) →
    Nonempty (F r ≫ E r ≅ (E (r + 1) ≫ F (r + 1)) ⊞ qsum 1 (n₀ + 2 * (r + 1)).toNat (𝟙 _))
  /-- Condition (3) for `m ≤ 0`: `F E 1_m ≅ E F 1_m ⊕_{[-m]} 1_m`. -/
  FE : ∀ r : ℤ, n₀ + 2 * (r + 1) ≤ 0 →
    Nonempty (E (r + 1) ≫ F (r + 1) ≅ (F r ≫ E r) ⊞ qsum 1 (-(n₀ + 2 * (r + 1))).toNat (𝟙 _))
  /-- Condition (4): the scalar `r_i` of the choice of scalars `Q`. -/
  rQ : kˣ
  /-- Condition (4): the dot on `E 1_n`, of degree 2. -/
  dot : ∀ r : ℤ, ShiftedHom (E r) (E r) (2 : ℤ)
  /-- Condition (4): the crossing on `E E 1_n`, of degree `-2`. -/
  cross : ∀ r : ℤ, ShiftedHom (E r ≫ E (r + 1)) (E r ≫ E (r + 1)) (-2 : ℤ)
  /-- `eq_nil_rels`, left: the square of the crossing is zero. -/
  cross_sq : ∀ r : ℤ, (cross r).comp (cross r) (by norm_num : (-2 : ℤ) + -2 = -4) = 0
  /-- `eq_nil_dotslide`, first equality: `r_i · 1 = (dot on the left strand, then crossing) -
  (crossing, then dot on the right strand)`. The left strand of `E E 1_n` is `E 1_{n+2}`
  (`E (r + 1)`), the right strand is `E 1_n` (`E r`). -/
  dot_slide_left : ∀ r : ℤ,
    ShiftedHom.mk₀ (0 : ℤ) rfl ((rQ : k) • 𝟙 (E r ≫ E (r + 1))) =
      (shWhiskerLeft (E r) (dot (r + 1))).comp (cross r) (by norm_num : (-2 : ℤ) + 2 = 0) -
        (cross r).comp (shWhiskerRight (dot r) (E (r + 1))) (by norm_num : (2 : ℤ) + -2 = 0)
  /-- `eq_nil_dotslide`, second equality: `r_i · 1 = (crossing, then dot on the left strand) -
  (dot on the right strand, then crossing)`. -/
  dot_slide_right : ∀ r : ℤ,
    ShiftedHom.mk₀ (0 : ℤ) rfl ((rQ : k) • 𝟙 (E r ≫ E (r + 1))) =
      (cross r).comp (shWhiskerLeft (E r) (dot (r + 1))) (by norm_num : (2 : ℤ) + -2 = 0) -
        (shWhiskerRight (dot r) (E (r + 1))).comp (cross r) (by norm_num : (-2 : ℤ) + 2 = 0)
  /-- `eq_nil_rels`, right: the braid relation on `E E E 1_n`. `τ₁` is the crossing of the two
  left strands, `τ₂` (conjugated by the associator) that of the two right strands. -/
  braid : ∀ r : ℤ,
    let τ₁ : ShiftedHom (E r ≫ E (r + 1) ≫ E (r + 1 + 1)) (E r ≫ E (r + 1) ≫ E (r + 1 + 1))
        (-2 : ℤ) := shWhiskerLeft (E r) (cross (r + 1))
    let τ₂ : ShiftedHom (E r ≫ E (r + 1) ≫ E (r + 1 + 1)) (E r ≫ E (r + 1) ≫ E (r + 1 + 1))
        (-2 : ℤ) :=
      (ShiftedHom.mk₀ (0 : ℤ) rfl (α_ (E r) (E (r + 1)) (E (r + 1 + 1))).inv).comp
        ((shWhiskerRight (cross r) (E (r + 1 + 1))).comp
          (ShiftedHom.mk₀ (0 : ℤ) rfl (α_ (E r) (E (r + 1)) (E (r + 1 + 1))).hom)
          (by norm_num : (0 : ℤ) + -2 = -2)) (by norm_num : (-2 : ℤ) + 0 = -2)
    (τ₁.comp τ₂ (by norm_num : (-2 : ℤ) + -2 = -4)).comp τ₁ (by norm_num : (-2 : ℤ) + -4 = -6) =
      (τ₂.comp τ₁ (by norm_num : (-2 : ℤ) + -2 = -4)).comp τ₂ (by norm_num : (-2 : ℤ) + -4 = -6)

namespace StrongSl2

variable {k B} (S : StrongSl2 k B)

/-- The weight `n = n₀ + 2 r` of object `r`. -/
def wt (r : ℤ) : ℤ := S.n₀ + 2 * r

theorem wt_add_one (r : ℤ) : S.wt (r + 1) = S.wt r + 2 := by simp only [wt]; ring

theorem wt_lt_wt {r r' : ℤ} (h : r < r') : S.wt r < S.wt r' := by simp only [wt]; omega

/-- `E r`, `F r` are zero if their source or target is a zero object. -/
theorem isZero_E_of_left {r : ℤ} (h : IsZero (𝟙 (S.obj r))) : IsZero (S.E r) :=
  isZero_of_isZero_id_src h _

theorem isZero_E_of_right {r : ℤ} (h : IsZero (𝟙 (S.obj (r + 1)))) : IsZero (S.E r) :=
  isZero_of_isZero_id_tgt h _

theorem isZero_F_of_left {r : ℤ} (h : IsZero (𝟙 (S.obj r))) : IsZero (S.F r) :=
  isZero_of_isZero_id_tgt h _

theorem isZero_F_of_right {r : ℤ} (h : IsZero (𝟙 (S.obj (r + 1)))) : IsZero (S.F r) :=
  isZero_of_isZero_id_src h _

/-- **The adjoint induction hypothesis** at the weight `n = wt r` (CL §3.2, eq. (3.2), `eq:ind_hyp`):
`(E 1_n)_L ≅ 1_n F ⟨-n-1⟩`. -/
def AdjHyp (r : ℤ) : Prop := Nonempty ((S.F r)⟦-(S.wt r + 1)⟧ ⊣ S.E r)

/-- Beyond the highest (or lowest) weight the adjoint induction hypothesis holds vacuously: "for
`m` beyond the highest weight this claim is vacuously true since both maps are zero". -/
theorem adjHyp_of_isZero {r : ℤ} (h : IsZero (𝟙 (S.obj r)) ∨ IsZero (𝟙 (S.obj (r + 1)))) :
    S.AdjHyp r := by
  rcases h with h | h
  · exact ⟨adjunctionOfIsZero ((shiftFunctor _ _).map_isZero (S.isZero_F_of_left h))
      (S.isZero_E_of_left h)⟩
  · exact ⟨adjunctionOfIsZero ((shiftFunctor _ _).map_isZero (S.isZero_F_of_right h))
      (S.isZero_E_of_right h)⟩

/-- The integrability bound: all objects `r` with `N ≤ r` are zero. -/
theorem exists_isZero_ge : ∃ N : ℤ, ∀ r : ℤ, N ≤ r → IsZero (𝟙 (S.obj r)) := by
  obtain ⟨N, hN⟩ := S.integrable
  exact ⟨N, fun r hr => hN r (le_trans hr (le_abs_self r))⟩

/-- The integrability bound from below. -/
theorem exists_isZero_le : ∃ N : ℤ, ∀ r : ℤ, r ≤ N → IsZero (𝟙 (S.obj r)) := by
  obtain ⟨N, hN⟩ := S.integrable
  exact ⟨-N - 1, fun r hr => hN r (by rw [abs_of_neg (by omega)]; omega)⟩

/-- **Decreasing induction from the highest weight** (made well founded by integrability): a
property that holds for all zero objects and propagates downwards holds everywhere. -/
theorem decreasing_induction {P : ℤ → Prop} (hzero : ∀ r, IsZero (𝟙 (S.obj r)) → P r)
    (step : ∀ r, (∀ r', r < r' → P r') → P r) (r : ℤ) : P r := by
  obtain ⟨N, hN⟩ := S.exists_isZero_ge
  suffices h : ∀ d : ℕ, ∀ r, N - r ≤ d → P r from h (N - r).toNat r (Int.self_le_toNat _)
  intro d
  induction d with
  | zero => intro r hr; exact hzero r (hN r (by omega))
  | succ d ih =>
    intro r hr
    exact step r fun r' hr' => ih r' (by omega)

/-- **Increasing induction from the lowest weight** (made well founded by integrability). -/
theorem increasing_induction {P : ℤ → Prop} (hzero : ∀ r, IsZero (𝟙 (S.obj r)) → P r)
    (step : ∀ r, (∀ r', r' < r → P r') → P r) (r : ℤ) : P r := by
  obtain ⟨N, hN⟩ := S.exists_isZero_le
  suffices h : ∀ d : ℕ, ∀ r, r - N ≤ d → P r from h (r - N).toNat r (Int.self_le_toNat _)
  intro d
  induction d with
  | zero => intro r hr; exact hzero r (hN r (by omega))
  | succ d ih =>
    intro r hr
    exact step r fun r' hr' => ih r' (by omega)

/-- **CL's adjoint induction** (§3.2, "For positive weight spaces (`n ≥ 0`) we proceed by
decreasing induction on `n` starting from the highest weight"): if the adjoint induction
hypothesis at every `m > n` implies it at `n`, for every `n ≥ 0`, then it holds for all `n ≥ 0`. -/
theorem adjoint_induction
    (step : ∀ r, 0 ≤ S.wt r → (∀ r', r < r' → S.AdjHyp r') → S.AdjHyp r) :
    ∀ r, 0 ≤ S.wt r → S.AdjHyp r := by
  refine S.decreasing_induction (fun r h _ => S.adjHyp_of_isZero (Or.inl h)) ?_
  intro r ih hr
  exact step r hr fun r' hr' => ih r' hr' (le_trans hr (S.wt_lt_wt hr').le)

/-- **CL's adjoint induction for `n ≤ 0`** (§3.2: "For negative weight spaces (`n ≤ 0`) we perform
increasing induction on `n` starting from the lowest weight"; Remark 3.11: "The induction
hypothesis (3.2) is now for `m < n`"). -/
theorem adjoint_induction_neg
    (step : ∀ r, S.wt r ≤ 0 → (∀ r', r' < r → S.AdjHyp r') → S.AdjHyp r) :
    ∀ r, S.wt r ≤ 0 → S.AdjHyp r := by
  refine S.increasing_induction (fun r h _ => S.adjHyp_of_isZero (Or.inl h)) ?_
  intro r ih hr
  exact step r hr fun r' hr' => ih r' hr' (le_trans (S.wt_lt_wt hr').le hr)

/-! ### Dimension-level adjunctions -/

variable [GradedBicategory.IsLinear B k]

/-- `E 1_n ⊣ 1_n F ⟨n+1⟩` at the level of Hom dimensions. -/
theorem dimAdj (r : ℤ) : DimAdj k (S.E r) ((S.F r)⟦S.wt r + 1⟧) :=
  Adj.dimAdj k (S.adj r)

/-- `(1_n F)_L = E 1_n ⟨n+1⟩` (CL §3.2: "Our definition of `1_n F` implies that ... and that
`(1_n F)_L = E 1_n ⟨n+1⟩`"), at the level of Hom dimensions. -/
theorem dimAdj_EF (r : ℤ) : DimAdj k ((S.E r)⟦S.wt r + 1⟧) (S.F r) :=
  ((S.dimAdj r).shift (m := S.wt r + 1) (n := -(S.wt r + 1)) (by ring)).of_iso (Iso.refl _)
    ((shiftFunctorCompIsoId _ (S.wt r + 1) (-(S.wt r + 1)) (by ring)).app (S.F r))

/-- Under the adjoint induction hypothesis, `F r⟦-(n+1)⟧ ⊣ E r` at the level of dimensions. -/
theorem AdjHyp.dimAdj {r : ℤ} (h : S.AdjHyp r) : DimAdj k ((S.F r)⟦-(S.wt r + 1)⟧) (S.E r) :=
  Adj.dimAdj k h.some

/-- Under the adjoint induction hypothesis, `(1_n F)_R ≅ E 1_n ⟨-n-1⟩` (the second half of CL's
`eq:ind_hyp`), at the level of dimensions. -/
theorem AdjHyp.dimAdjF {r : ℤ} (h : S.AdjHyp r) : DimAdj k (S.F r) ((S.E r)⟦-(S.wt r + 1)⟧) :=
  ((h.dimAdj S).shift (m := S.wt r + 1) (n := -(S.wt r + 1)) (by ring)).of_iso
    ((shiftFunctorCompIsoId _ (-(S.wt r + 1)) (S.wt r + 1) (by ring)).app (S.F r)) (Iso.refl _)

end StrongSl2

end Categorification.TwoRep

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqDottedCurls

/-!
# Leftward pitchfork relations from Rouquier's data

Brundan, *On the definition of Kac–Moody 2-category*, arXiv:1501.00350v1, Lemma 4.2.
For data at adjacent weights, the left-cap pitchfork holds at negative source weight and
its left-cup counterpart holds above source weight `-2`. The proof uses the explicit inverse
components, the nilHecke square and braid relations, and the dotted curls, with no grading.

The headline declarations `RouqLoc.capL_pitchfork_of_neg` and
`RouqLoc.cupL_pitchfork_of_gt_neg_two` provide the restricted pitchfork relations needed
for the left-adjunction identities. `RouqLoc.capCross_eq_of_neg` is the intermediate
cap-swap identity (4.5), including its correction at weight `-1`.
-/

noncomputable section
namespace Categorification.TwoRep
open CategoryTheory CategoryTheory.Bicategory
universe w v u

namespace RouqSl2Generic

variable {C : Type u} [Bicategory.{w, v} C] [∀ a b : C, Preadditive (a ⟶ b)]
  [AdditiveWhiskering C] {a b c : C} {E₁ : a ⟶ b} {E₂ : b ⟶ c} {R₂ : c ⟶ b}

/-- Closing the second strand of a crossing is additive. -/
def curlEGMap (u : 𝟙 b ⟶ E₂ ≫ R₂) (e : E₂ ≫ R₂ ⟶ 𝟙 b) :
    (E₁ ≫ E₂ ⟶ E₁ ≫ E₂) →+ (E₁ ⟶ E₁) where
  toFun := curlEG u e
  map_zero' := by simp only [curlEG, AdditiveWhiskering.zero_whiskerRight,
    Limits.comp_zero, Limits.zero_comp]
  map_add' _ _ := by simp only [curlEG, AdditiveWhiskering.add_whiskerRight,
    Preadditive.comp_add, Preadditive.add_comp]

omit [∀ a b : C, Preadditive (a ⟶ b)] [AdditiveWhiskering C] in
/-- Dots on the closed strand at the top are absorbed by the left cap. -/
theorem curlEG_comp_whiskerLeft_cap (u : 𝟙 b ⟶ E₂ ≫ R₂) (e : E₂ ≫ R₂ ⟶ 𝟙 b)
    (t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) (x : E₂ ⟶ E₂) :
    curlEG u e (t ≫ E₁ ◁ x) = curlEG u (x ▷ R₂ ≫ e) t := by
  unfold curlEG
  bicategory

end RouqSl2Generic

namespace SumInvFrom

variable {C : Type u} [Bicategory.{w, v} C] [∀ a b : C, Preadditive (a ⟶ b)]
  [AdditiveWhiskering C] {a b c : C} {X Y Z : a ⟶ b} {f : Y ⟶ X} {g : ℕ → (Z ⟶ X)} {n : ℕ}

/-- A whiskered row with a specified inverse detects equality of outgoing morphisms. -/
theorem whiskerRight_hom_ext (I : SumInvFrom f g n) (E : b ⟶ c) {T : a ⟶ c}
    {u v : X ≫ E ⟶ T} (hf : f ▷ E ≫ u = f ▷ E ≫ v)
    (hg : ∀ j, j < n → g j ▷ E ≫ u = g j ▷ E ≫ v) : u = v := by
  have ht := congrArg (fun z : X ⟶ X => z ▷ E) I.total
  have hs : (∑ j ∈ Finset.range n, I.g' j ≫ g j) ▷ E =
      ∑ j ∈ Finset.range n, (I.g' j ≫ g j) ▷ E :=
    map_sum (AdditiveWhiskering.whiskerRightAddHom X X E) _ _
  rw [AdditiveWhiskering.add_whiskerRight, hs, id_whiskerRight] at ht
  have he : ((I.f' ≫ f) ▷ E + ∑ j ∈ Finset.range n, (I.g' j ≫ g j) ▷ E) ≫ u =
      ((I.f' ≫ f) ▷ E + ∑ j ∈ Finset.range n, (I.g' j ≫ g j) ▷ E) ≫ v := by
    rw [Preadditive.add_comp, Preadditive.add_comp, Preadditive.sum_comp, Preadditive.sum_comp]
    simp only [comp_whiskerRight, Category.assoc]
    rw [hf]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [hg j (Finset.mem_range.mp hj)]
  simpa only [ht, Category.id_comp] using he

/-- The analogous detection statement after left whiskering. -/
theorem whiskerLeft_hom_ext {d : C} (I : SumInvFrom f g n) (E : d ⟶ a) {T : d ⟶ b}
    {u v : E ≫ X ⟶ T} (hf : E ◁ f ≫ u = E ◁ f ≫ v)
    (hg : ∀ j, j < n → E ◁ g j ≫ u = E ◁ g j ≫ v) : u = v := by
  have ht := congrArg (fun z : X ⟶ X => E ◁ z) I.total
  have hs : E ◁ (∑ j ∈ Finset.range n, I.g' j ≫ g j) =
      ∑ j ∈ Finset.range n, E ◁ (I.g' j ≫ g j) :=
    map_sum (AdditiveWhiskering.whiskerLeftAddHom E X X) _ _
  rw [AdditiveWhiskering.whiskerLeft_add, hs, whiskerLeft_id] at ht
  have he : (E ◁ (I.f' ≫ f) + ∑ j ∈ Finset.range n, E ◁ (I.g' j ≫ g j)) ≫ u =
      (E ◁ (I.f' ≫ f) + ∑ j ∈ Finset.range n, E ◁ (I.g' j ≫ g j)) ≫ v := by
    rw [Preadditive.add_comp, Preadditive.add_comp, Preadditive.sum_comp, Preadditive.sum_comp]
    simp only [whiskerLeft_comp, Category.assoc]
    rw [hf]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [hg j (Finset.mem_range.mp hj)]
  simpa only [ht, Category.id_comp] using he

end SumInvFrom

namespace RouqLoc
variable {C : Type u} [Bicategory.{w, v} C] [∀ a b : C, Preadditive (a ⟶ b)]
  [AdditiveWhiskering C]
  {a b c d : C} {E₁ : a ⟶ b} {R₁ : b ⟶ a} {E₂ : b ⟶ c} {R₂ : c ⟶ b}
  {E₃ : c ⟶ d} {R₃ : d ⟶ c}
  {adj₁ : E₁ ⊣ R₁} {adj₂ : E₂ ⊣ R₂} {adj₃ : E₃ ⊣ R₃}
  {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂} {x₃ : E₃ ⟶ E₃}
  {τ₁₂ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂} {τ₂₃ : E₂ ≫ E₃ ⟶ E₂ ≫ E₃} {h h' : ℤ}
  (L : RouqLoc adj₁ adj₂ x₁ x₂ τ₁₂ h) (U : RouqLoc adj₂ adj₃ x₂ x₃ τ₂₃ h')

/-- The cap composite appearing in the left-cap pitchfork calculation. -/
def capCross : (E₂ ≫ R₂) ≫ E₂ ⟶ E₂ :=
  (α_ E₂ R₂ E₂).hom ≫ E₂ ◁ U.sig ≫ (α_ E₂ E₃ R₃).inv ≫ τ₂₃ ▷ R₃ ≫
    (α_ E₂ E₃ R₃).hom ≫ E₂ ◁ U.capL ≫ (ρ_ E₂).hom

omit [AdditiveWhiskering C] in
/-- Move the crossing past the pair of rightward crossings. -/
theorem sig_capCross
    (hB : E₁ ◁ τ₂₃ ≫ ((α_ E₁ E₂ E₃).inv ≫ τ₁₂ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom) ≫ E₁ ◁ τ₂₃ =
      ((α_ E₁ E₂ E₃).inv ≫ τ₁₂ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom) ≫ E₁ ◁ τ₂₃ ≫
        ((α_ E₁ E₂ E₃).inv ≫ τ₁₂ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom)) :
    L.sig ▷ E₂ ≫ U.capCross =
      (α_ R₁ E₁ E₂).hom ≫ R₁ ◁ τ₁₂ ≫ (α_ R₁ E₁ E₂).inv ≫ L.sig ▷ E₂ ≫
        (α_ E₂ R₂ E₂).hom ≫ E₂ ◁ (U.sig ≫ U.capL) ≫ (ρ_ E₂).hom := by
  have hb := RightwardCrossing.mixed_braid adj₂.unit adj₂.counit τ₁₂ adj₁.counit
    adj₃.unit τ₂₃ adj₂.left_triangle hB
  change (𝟙 _ ⊗≫ R₁ ◁ τ₁₂ ⊗≫ (L.sig ▷ E₂ ⊗≫ E₂ ◁ U.sig)) =
    ((L.sig ▷ E₂ ⊗≫ E₂ ◁ U.sig) ⊗≫ τ₂₃ ▷ R₃ ⊗≫ 𝟙 _) at hb
  calc _ = (((L.sig ▷ E₂ ⊗≫ E₂ ◁ U.sig) ⊗≫ τ₂₃ ▷ R₃ ⊗≫ 𝟙 _) :
      (R₁ ≫ E₁) ≫ E₂ ⟶ E₂ ≫ E₃ ≫ R₃) ⊗≫
      E₂ ◁ U.capL ⊗≫ 𝟙 _ := by
        unfold capCross
        bicategory
    _ = _ := by
        rw [← hb]
        bicategory

omit [AdditiveWhiskering C] in
/-- In weights at most one, only two terms of the capped-crossing expansion can survive. -/
theorem sig_capL_low (hh : h ≤ 1) :
    L.sig ≫ L.capL = L.capD 0 ≫ L.cw (-1) + if h = 1 then L.capD 1 else 0 := by
  rcases lt_trichotomy h 0 with hn | hz | hp
  · rw [L.sig_capL hn, L.cw_of_neg_of_lt (by omega) (by omega),
      Limits.comp_zero, ite_eq_right (by omega), add_zero]
  · subst h
    rw [L.sig_capL_expansion]
    change (∑ n ∈ Finset.range 1, L.capD n ≫ L.cw (-(n : ℤ) - 1)) =
      L.capD 0 ≫ L.cw (-1) + 0
    rw [Finset.sum_range_one, add_zero]
    rfl
  · have heq : h = 1 := by omega
    subst h
    rw [L.sig_capL_expansion]
    change (∑ n ∈ Finset.range 2, L.capD n ≫ L.cw (-(n : ℤ) - 1)) =
      L.capD 0 ≫ L.cw (-1) + L.capD 1
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Nat.cast_zero, Nat.cast_one]
    rw [L.cw_of_neg_of_eq (k := -1 - 1) (by omega) (by omega), Category.comp_id]
    rfl

omit [AdditiveWhiskering C] in
/-- The capped pitchfork with dots on its open strand. -/
theorem sig_capD_closed (n : ℕ) :
    L.sig ▷ E₂ ≫ (α_ E₂ R₂ E₂).hom ≫ E₂ ◁ U.capD n ≫ (ρ_ E₂).hom =
      (α_ R₁ E₁ E₂).hom ≫ R₁ ◁ (E₁ ◁ powComp x₂ n ≫ τ₁₂) ≫
        (α_ R₁ E₁ E₂).inv ≫ adj₁.counit ▷ E₂ ≫ (λ_ E₂).hom := by
  calc _ = (L.sig ▷ E₂ ≫ (E₂ ≫ R₂) ◁ powComp x₂ n) ⊗≫ E₂ ◁ adj₂.counit ⊗≫ 𝟙 _ := by
        unfold capD
        bicategory
    _ = ((R₁ ≫ E₁) ◁ powComp x₂ n ≫ L.sig ▷ E₂) ⊗≫ E₂ ◁ adj₂.counit ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange]
    _ = ((R₁ ≫ E₁) ◁ powComp x₂ n) ⊗≫
        (L.sig ▷ E₂ ⊗≫ E₂ ◁ adj₂.counit) ⊗≫ 𝟙 _ := by bicategory
    _ = _ := by
        rw [L.sig_counit_pitchfork]
        bicategory

omit [AdditiveWhiskering C] in
/-- Close a dotted cap after two crossings, retaining an arbitrary outside bubble. -/
theorem cross_sig_capD_closed (n : ℕ) (β : 𝟙 c ⟶ 𝟙 c) :
    (α_ R₁ E₁ E₂).hom ≫ R₁ ◁ τ₁₂ ≫ (α_ R₁ E₁ E₂).inv ≫ L.sig ▷ E₂ ≫
      (α_ E₂ R₂ E₂).hom ≫ E₂ ◁ (U.capD n ≫ β) ≫ (ρ_ E₂).hom =
    (𝟙 _ ⊗≫ R₁ ◁ (τ₁₂ ≫ E₁ ◁ powComp x₂ n ≫ τ₁₂) ⊗≫ adj₁.counit ▷ E₂ ⊗≫
      E₂ ◁ β ⊗≫ 𝟙 _ : (R₁ ≫ E₁) ≫ E₂ ⟶ E₂) := by
  calc _ = (𝟙 _ ⊗≫ R₁ ◁ τ₁₂ ⊗≫
      (L.sig ▷ E₂ ≫ (α_ E₂ R₂ E₂).hom ≫ E₂ ◁ U.capD n ≫ (ρ_ E₂).hom) ⊗≫
      E₂ ◁ β ⊗≫ 𝟙 _ : (R₁ ≫ E₁) ≫ E₂ ⟶ E₂) := by bicategory
    _ = _ := by rw [L.sig_capD_closed U]; bicategory

/-- The crossing component of the cap-swap identity. -/
theorem sig_capCross_of_neg (hw : h' = h + 2) (hh : h < 0) (hsq : τ₁₂ ≫ τ₁₂ = 0)
    (hB : E₁ ◁ τ₂₃ ≫ ((α_ E₁ E₂ E₃).inv ≫ τ₁₂ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom) ≫ E₁ ◁ τ₂₃ =
      ((α_ E₁ E₂ E₃).inv ≫ τ₁₂ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom) ≫ E₁ ◁ τ₂₃ ≫
        ((α_ E₁ E₂ E₃).inv ≫ τ₁₂ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom)) :
    L.sig ▷ E₂ ≫ U.capCross = if h = -1 then
      L.sig ▷ E₂ ≫ (α_ E₂ R₂ E₂).hom ≫ E₂ ◁ adj₂.counit ≫ (ρ_ E₂).hom else 0 := by
  have h0 := L.cross_sig_capD_closed U 0 (U.cw (-1))
  simp only [powComp_zero, whiskerLeft_id, Category.id_comp, hsq,
    AdditiveWhiskering.whiskerLeft_zero, bicategoricalComp, Limits.comp_zero, Limits.zero_comp] at h0
  have h1 := L.cross_sig_capD_closed U 1 (𝟙 (𝟙 c))
  rw [Category.comp_id, powComp_one,
    RightwardCrossing.tau_dot_tau_left _ _ _ hsq L.slide_left] at h1
  have hf : (𝟙 _ ⊗≫ R₁ ◁ τ₁₂ ⊗≫ adj₁.counit ▷ E₂ ⊗≫ E₂ ◁ 𝟙 (𝟙 c) ⊗≫ 𝟙 _ :
      (R₁ ≫ E₁) ≫ E₂ ⟶ E₂) =
      L.sig ▷ E₂ ≫ (α_ E₂ R₂ E₂).hom ≫ E₂ ◁ adj₂.counit ≫ (ρ_ E₂).hom := by
    calc _ = (L.sig ▷ E₂ ⊗≫ E₂ ◁ adj₂.counit) ⊗≫ (ρ_ E₂).hom := by
          rw [L.sig_counit_pitchfork]
          bicategory
      _ = _ := by bicategory
  rw [hf] at h1
  rw [L.sig_capCross U hB, U.sig_capL_low (by omega)]
  split_ifs with hu hh1 hh1
  · rw [AdditiveWhiskering.whiskerLeft_add]
    simp only [Preadditive.add_comp, Preadditive.comp_add]
    rw [h0, zero_add, h1]
  · omega
  · omega
  · simp only [add_zero]
    exact h0

omit [AdditiveWhiskering C] in
/-- The cup component is the closure of a double crossing. -/
theorem cupD_capCross (n : ℕ) :
    L.cupD n ▷ E₂ ≫ U.capCross = (λ_ E₂).hom ≫
      curlEG adj₃.unit U.capL (τ₂₃ ≫ powComp x₂ n ▷ E₃ ≫ τ₂₃) := by
  calc _ = (adj₂.unit ▷ E₂ ⊗≫
      ((powComp x₂ n ▷ (R₂ ≫ E₂)) ≫ E₂ ◁ U.sig) ⊗≫ τ₂₃ ▷ R₃ ⊗≫
      E₂ ◁ U.capL ⊗≫ 𝟙 _ : 𝟙 b ≫ E₂ ⟶ E₂) := by
        unfold cupD capCross
        bicategory
    _ = (adj₂.unit ▷ E₂ ⊗≫
      (E₂ ◁ U.sig ≫ powComp x₂ n ▷ (E₃ ≫ R₃)) ⊗≫ τ₂₃ ▷ R₃ ⊗≫
      E₂ ◁ U.capL ⊗≫ 𝟙 _ : 𝟙 b ≫ E₂ ⟶ E₂) := by rw [whisker_exchange]
    _ = ((adj₂.unit ▷ E₂ ⊗≫ E₂ ◁ U.sig) ⊗≫ (powComp x₂ n ▷ E₃ ≫ τ₂₃) ▷ R₃ ⊗≫
      E₂ ◁ U.capL ⊗≫ 𝟙 _ : 𝟙 b ≫ E₂ ⟶ E₂) := by bicategory
    _ = _ := by
        rw [U.unit_sig_pitchfork]
        unfold curlEG
        bicategory

/-- A double crossing closed on the right, with a bounded number of intervening dots. -/
theorem curlEG_double_dotted (hsq : τ₁₂ ≫ τ₁₂ = 0) {n : ℕ}
    (hn0 : 0 < n) (hn : (n : ℤ) ≤ 1 - h) :
    curlEG adj₂.unit L.capL (τ₁₂ ≫ powComp x₁ n ▷ E₂ ≫ τ₁₂) =
      if (n : ℤ) = 1 - h then -𝟙 E₁ else 0 := by
  have hx : τ₁₂ ≫ powComp x₁ n ▷ E₂ ≫ τ₁₂ =
      -(∑ j ∈ Finset.range n, τ₁₂ ≫ powComp (x₁ ▷ E₂) j ≫
        powComp (E₁ ◁ x₂) (n - 1 - j)) := by
    rw [powComp_whiskerRight, powComp_tau _ _ _ L.slide_right n,
      Preadditive.comp_sub, ← Category.assoc, hsq, Limits.zero_comp, zero_sub,
      Preadditive.comp_sum]
  change (RouqSl2Generic.curlEGMap adj₂.unit L.capL) _ = _
  rw [hx, map_neg, map_sum]
  change -(∑ j ∈ Finset.range n, curlEG adj₂.unit L.capL
    (τ₁₂ ≫ powComp (x₁ ▷ E₂) j ≫ powComp (E₁ ◁ x₂) (n - 1 - j))) = _
  have ht : ∀ j ∈ Finset.range n, curlEG adj₂.unit L.capL
      (τ₁₂ ≫ powComp (x₁ ▷ E₂) j ≫ powComp (E₁ ◁ x₂) (n - 1 - j)) =
      if (n : ℤ) = 1 - h ∧ j = 0 then 𝟙 E₁ else 0 := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [← powComp_whiskerRight, ← whiskerLeft_powComp, ← whisker_exchange,
      ← Category.assoc, curlEG_comp_whiskerRight, RouqSl2Generic.curlEG_comp_whiskerLeft_cap,
      L.curlEG_dotted (by omega)]
    have heq : (↑(n - 1 - j) : ℤ) = -h ↔ (n : ℤ) = 1 - h ∧ j = 0 := by omega
    simp only [heq]
    split_ifs with hjn
    · rcases hjn with ⟨_, rfl⟩
      simp
    · simp
  rw [Finset.sum_congr rfl ht]
  by_cases hne : (n : ℤ) = 1 - h
  · simp [hne, hn0]
  · simp [hne]

/-- The cap-swap identity used to derive the negative-weight left-cap pitchfork. -/
theorem capCross_eq_of_neg (hw : h' = h + 2) (hh : h < 0) (hsq : τ₁₂ ≫ τ₁₂ = 0) (hsq' : τ₂₃ ≫ τ₂₃ = 0)
    (hB : E₁ ◁ τ₂₃ ≫ ((α_ E₁ E₂ E₃).inv ≫ τ₁₂ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom) ≫ E₁ ◁ τ₂₃ =
      ((α_ E₁ E₂ E₃).inv ≫ τ₁₂ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom) ≫ E₁ ◁ τ₂₃ ≫
        ((α_ E₁ E₂ E₃).inv ≫ τ₁₂ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom)) :
    U.capCross = -(L.capL ▷ E₂ ≫ (λ_ E₂).hom) + if h = -1 then
      (α_ E₂ R₂ E₂).hom ≫ E₂ ◁ adj₂.counit ≫ (ρ_ E₂).hom else 0 := by
  apply (L.iN hh.le).whiskerRight_hom_ext E₂
  · have hc : L.sig ▷ E₂ ≫ L.capL ▷ E₂ ≫ (λ_ E₂).hom = 0 := by
      rw [← Category.assoc, ← comp_whiskerRight, L.sig_capL hh,
        AdditiveWhiskering.zero_whiskerRight, Limits.zero_comp]
    rw [Preadditive.comp_add, Preadditive.comp_neg, hc, neg_zero, zero_add,
      L.sig_capCross_of_neg U hw hh hsq hB]
    split_ifs <;> simp
  · intro n hn
    have hcap : L.cupD n ▷ E₂ ≫ L.capL ▷ E₂ ≫ (λ_ E₂).hom =
        if n = (-h - 1).toNat then (λ_ E₂).hom else 0 := by
      rw [← Category.assoc, ← comp_whiskerRight, L.cupD_capL hh hn]
      split_ifs
      · rw [id_whiskerRight, Category.id_comp]
      · rw [AdditiveWhiskering.zero_whiskerRight, Limits.zero_comp]
    rw [Preadditive.comp_add, Preadditive.comp_neg, hcap, L.cupD_capCross U]
    by_cases heq : h = -1
    · have hn0 : n = 0 := by omega
      subst h
      subst n
      have hz : L.cupD 0 ▷ E₂ ≫ (α_ E₂ R₂ E₂).hom ≫ E₂ ◁ adj₂.counit ≫ (ρ_ E₂).hom =
          (λ_ E₂).hom := by
        calc _ = leftZigzag adj₂.unit adj₂.counit ≫ (ρ_ E₂).hom := by
              unfold cupD leftZigzag
              simp only [powComp_zero, id_whiskerRight, Category.comp_id]
              bicategory
          _ = _ := by rw [adj₂.left_triangle]; simp
      simp only [powComp_zero, id_whiskerRight, Category.id_comp, hsq', ite_true]
      rw [show (-(-1 : ℤ) - 1).toNat = 0 by rfl, ite_eq_left rfl, hz]
      have hc0 := (RouqSl2Generic.curlEGMap (E₁ := E₂) adj₃.unit U.capL).map_zero
      change curlEG adj₃.unit U.capL 0 = 0 at hc0
      rw [hc0, Limits.comp_zero]
      abel
    · rw [ite_eq_right heq, Limits.comp_zero, add_zero]
      rcases Nat.eq_zero_or_pos n with hn0 | hn0
      · subst n
        rw [powComp_zero, id_whiskerRight, Category.id_comp, hsq',
          ite_eq_right (by omega)]
        have hc0 := (RouqSl2Generic.curlEGMap (E₁ := E₂) adj₃.unit U.capL).map_zero
        change curlEG adj₃.unit U.capL 0 = 0 at hc0
        rw [hc0, Limits.comp_zero, neg_zero]
      · rw [U.curlEG_double_dotted hsq' hn0 (by omega)]
        have hiff : (n : ℤ) = 1 - h' ↔ n = (-h - 1).toNat := by omega
        simp only [hiff]
        split_ifs
        · rw [Preadditive.comp_neg, Category.comp_id]
        · simp

/-- Moving dots to the cup side of a left curl still gives zero below the boundary. -/
theorem curlEG_cupD_zero {n : ℕ} (hn : (n : ℤ) < -h) :
    curlEG (L.cupD n) L.capL τ₁₂ = 0 := by
  have hh : h < 0 := by omega
  have hb : curlEG adj₂.unit L.capL τ₁₂ = 0 := by
    simpa only [powComp_zero, id_whiskerRight, Category.id_comp, Nat.cast_zero,
      ite_eq_right (by omega : (0 : ℤ) ≠ -h)] using L.curlEG_dotted (n := 0) (by omega)
  change curlEG (adj₂.unit ≫ powComp x₂ n ▷ R₂) L.capL τ₁₂ = 0
  rw [← curlEG_whiskerLeft_comp, whiskerLeft_powComp]
  change (RouqSl2Generic.curlEGMap adj₂.unit L.capL)
    (powComp (E₁ ◁ x₂) n ≫ τ₁₂) = 0
  rw [qpow_tau _ _ _ L.slide_left n, map_add, map_sum]
  change curlEG adj₂.unit L.capL (τ₁₂ ≫ powComp (x₁ ▷ E₂) n) +
    (∑ j ∈ Finset.range n, curlEG adj₂.unit L.capL
      (powComp (E₁ ◁ x₂) j ≫ powComp (x₁ ▷ E₂) (n - 1 - j))) = 0
  rw [← powComp_whiskerRight, curlEG_comp_whiskerRight, hb, Limits.zero_comp, zero_add]
  apply Finset.sum_eq_zero
  intro j hj
  have hj' := Finset.mem_range.mp hj
  rw [← whiskerLeft_powComp, ← powComp_whiskerRight,
    curlEG_comp_whiskerRight, curlEG_whiskerLeft]
  have hc : adj₂.unit ≫ powComp x₂ j ▷ R₂ ≫ L.capL = 0 := by
    simpa only [cw_of_nonneg (L := L) (by positivity : (0 : ℤ) ≤ j),
      Int.toNat_natCast, cupD, Category.assoc] using L.cw_of_lt hh (k := j) (by omega)
  rw [hc, AdditiveWhiskering.whiskerLeft_zero]
  simp

/-- **Brundan, Lemma 4.2, (4.3)**: the left-cap pitchfork at negative source weight. -/
theorem capL_pitchfork_of_neg (hw : h' = h + 2) (hh : h < 0) (hsq : τ₁₂ ≫ τ₁₂ = 0) (hsq' : τ₂₃ ≫ τ₂₃ = 0)
    (hB : E₁ ◁ τ₂₃ ≫ ((α_ E₁ E₂ E₃).inv ≫ τ₁₂ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom) ≫ E₁ ◁ τ₂₃ =
      ((α_ E₁ E₂ E₃).inv ≫ τ₁₂ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom) ≫ E₁ ◁ τ₂₃ ≫
        ((α_ E₁ E₂ E₃).inv ≫ τ₁₂ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom)) :
    (α_ E₂ E₃ R₃).inv ≫ τ₂₃ ▷ R₃ ≫ (α_ E₂ E₃ R₃).hom ≫ E₂ ◁ U.capL ≫ (ρ_ E₂).hom =
      E₂ ◁ U.sigL ≫ (α_ E₂ R₂ E₂).inv ≫ L.capL ▷ E₂ ≫ (λ_ E₂).hom := by
  let p : E₂ ≫ E₃ ≫ R₃ ⟶ E₂ := (α_ E₂ E₃ R₃).inv ≫ τ₂₃ ▷ R₃ ≫
    (α_ E₂ E₃ R₃).hom ≫ E₂ ◁ U.capL ≫ (ρ_ E₂).hom
  let k : E₂ ≫ E₃ ≫ R₃ ⟶ E₂ :=
    E₂ ◁ U.sigL ≫ (α_ E₂ R₂ E₂).inv ≫ L.capL ▷ E₂ ≫ (λ_ E₂).hom
  change p = k
  have hc := L.capCross_eq_of_neg U hw hh hsq hsq' hB
  by_cases heq : h = -1
  · have hz : U.sigL ≫ adj₂.counit = 0 := by
      simpa only [capD, powComp_zero, whiskerLeft_id, Category.id_comp] using
        U.sigL_capD (n := 0) (by omega) (by omega)
    apply neg_injective
    calc -p = E₂ ◁ U.sigL ≫ (α_ E₂ R₂ E₂).inv ≫ U.capCross := by
          calc _ = E₂ ◁ (U.sigL ≫ U.sig) ≫ p := by
                rw [U.sigL_sig_of_nonneg (by omega), AdditiveWhiskering.whiskerLeft_neg,
                  whiskerLeft_id, Preadditive.neg_comp, Category.id_comp]
            _ = _ := by unfold p capCross; bicategory
      _ = -k := by
          rw [hc, ite_eq_left heq, Preadditive.comp_add, Preadditive.comp_neg,
            Preadditive.comp_add, Preadditive.comp_neg]
          change -k + E₂ ◁ U.sigL ≫ (α_ E₂ R₂ E₂).inv ≫
            (α_ E₂ R₂ E₂).hom ≫ E₂ ◁ adj₂.counit ≫ (ρ_ E₂).hom = -k
          rw [Iso.inv_hom_id_assoc, ← whiskerLeft_comp_assoc, hz,
            AdditiveWhiskering.whiskerLeft_zero, Limits.zero_comp, add_zero]
  · have hu : h' ≤ 0 := by omega
    apply (U.iN hu).whiskerLeft_hom_ext E₂
    · calc E₂ ◁ U.sig ≫ p = (α_ E₂ R₂ E₂).inv ≫ U.capCross := by
            unfold p capCross
            simp only [Iso.inv_hom_id_assoc]
        _ = -((α_ E₂ R₂ E₂).inv ≫ L.capL ▷ E₂ ≫ (λ_ E₂).hom) := by
            rw [hc, ite_eq_right heq, add_zero, Preadditive.comp_neg]
        _ = E₂ ◁ U.sig ≫ k := by
            dsimp [k]
            rw [← whiskerLeft_comp_assoc, U.sig_sigL_of_nonpos hu,
              AdditiveWhiskering.whiskerLeft_neg, whiskerLeft_id,
              Preadditive.neg_comp, Category.id_comp]
    · intro n hn
      calc E₂ ◁ U.cupD n ≫ p = (ρ_ E₂).hom ≫ curlEG (U.cupD n) U.capL τ₂₃ := by
            unfold p curlEG
            bicategory
        _ = 0 := by rw [U.curlEG_cupD_zero (by omega), Limits.comp_zero]
        _ = E₂ ◁ U.cupD n ≫ k := by
            dsimp [k]
            rw [← whiskerLeft_comp_assoc, U.cupD_sigL hu hn,
              AdditiveWhiskering.whiskerLeft_zero, Limits.zero_comp]

/-- **Brundan, Lemma 4.2, (4.4)**: the dual left-cup pitchfork above source weight `-2`. -/
theorem cupL_pitchfork_of_gt_neg_two (hw : h' = h + 2) (hh : -2 < h)
    (hsq : τ₁₂ ≫ τ₁₂ = 0) (hsq' : τ₂₃ ≫ τ₂₃ = 0)
    (hB : E₁ ◁ τ₂₃ ≫ ((α_ E₁ E₂ E₃).inv ≫ τ₁₂ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom) ≫ E₁ ◁ τ₂₃ =
      ((α_ E₁ E₂ E₃).inv ≫ τ₁₂ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom) ≫ E₁ ◁ τ₂₃ ≫
        ((α_ E₁ E₂ E₃).inv ≫ τ₁₂ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom)) :
    (λ_ E₂).inv ≫ L.cupL ▷ E₂ ≫ (α_ R₁ E₁ E₂).hom ≫ R₁ ◁ τ₁₂ ≫ (α_ R₁ E₁ E₂).inv =
      (ρ_ E₂).inv ≫ E₂ ◁ U.cupL ≫ (α_ E₂ R₂ E₂).inv ≫ L.sigL ▷ E₂ := by
  have hsqd : dualτ τ₁₂ ≫ dualτ τ₁₂ = 0 := by
    apply Quiver.Hom.unop_inj
    change (-τ₁₂) ≫ (-τ₁₂) = 0
    simp only [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg, hsq]
  have hsqd' : dualτ τ₂₃ ≫ dualτ τ₂₃ = 0 := by
    apply Quiver.Hom.unop_inj
    change (-τ₂₃) ≫ (-τ₂₃) = 0
    simp only [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg, hsq']
  have hBd : Coop.op1 E₃ ◁ dualτ τ₁₂ ≫
      ((α_ (Coop.op1 E₃) (Coop.op1 E₂) (Coop.op1 E₁)).inv ≫ dualτ τ₂₃ ▷ Coop.op1 E₁ ≫
        (α_ (Coop.op1 E₃) (Coop.op1 E₂) (Coop.op1 E₁)).hom) ≫ Coop.op1 E₃ ◁ dualτ τ₁₂ =
      ((α_ (Coop.op1 E₃) (Coop.op1 E₂) (Coop.op1 E₁)).inv ≫ dualτ τ₂₃ ▷ Coop.op1 E₁ ≫
        (α_ (Coop.op1 E₃) (Coop.op1 E₂) (Coop.op1 E₁)).hom) ≫ Coop.op1 E₃ ◁ dualτ τ₁₂ ≫
      ((α_ (Coop.op1 E₃) (Coop.op1 E₂) (Coop.op1 E₁)).inv ≫ dualτ τ₂₃ ▷ Coop.op1 E₁ ≫
        (α_ (Coop.op1 E₃) (Coop.op1 E₂) (Coop.op1 E₁)).hom) := by
    apply Quiver.Hom.unop_inj
    change ((-τ₁₂) ▷ E₃ ≫ (((α_ E₁ E₂ E₃).hom ≫ E₁ ◁ (-τ₂₃)) ≫
        (α_ E₁ E₂ E₃).inv)) ≫ (-τ₁₂) ▷ E₃ =
      ((((α_ E₁ E₂ E₃).hom ≫ E₁ ◁ (-τ₂₃)) ≫ (α_ E₁ E₂ E₃).inv) ≫ (-τ₁₂) ▷ E₃) ≫
        (((α_ E₁ E₂ E₃).hom ≫ E₁ ◁ (-τ₂₃)) ≫ (α_ E₁ E₂ E₃).inv)
    simp only [AdditiveWhiskering.neg_whiskerRight, AdditiveWhiskering.whiskerLeft_neg,
      Preadditive.comp_neg, Preadditive.neg_comp, neg_neg, Category.assoc]
    have hb := congrArg (fun z => (α_ E₁ E₂ E₃).hom ≫ z ≫ (α_ E₁ E₂ E₃).inv) hB.symm
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
      Iso.hom_inv_id, Category.comp_id] using congrArg Neg.neg hb
  have hd := U.dual.capL_pitchfork_of_neg L.dual (by omega) (by omega) hsqd' hsqd hBd
  simp only [dual_capL, dual_sigL] at hd
  have hu := congrArg Quiver.Hom.unop hd
  change ((((λ_ E₂).inv ≫ L.cupL ▷ E₂) ≫ (α_ R₁ E₁ E₂).hom) ≫ R₁ ◁ (-τ₁₂)) ≫
      (α_ R₁ E₁ E₂).inv =
    (((ρ_ E₂).inv ≫ E₂ ◁ U.cupL) ≫ (α_ E₂ R₂ E₂).inv) ≫ (-L.sigL) ▷ E₂ at hu
  simp only [AdditiveWhiskering.whiskerLeft_neg, AdditiveWhiskering.neg_whiskerRight,
    Preadditive.comp_neg, Preadditive.neg_comp, Category.assoc] at hu
  exact neg_injective hu

end RouqLoc
end Categorification.TwoRep

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.AdjointPositive
import Categorification.TwoRep.AdjointInductionNegCor
import Categorification.TwoRep.DotEntriesNeg

/-!
# The adjoint induction hypothesis at the weight `-1`, and CL Proposition 3.9

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, §3, Proposition 3.9 (`prop:lradj`).

At the weight `n = -1` the left and right adjoints of `E 1_{-1}` are expected to coincide without
shift: `(E 1_{-1})_L ≅ 1_{-1} F = R_{-1}`. CL's induction gives nothing here (the induction steps
from the highest and the lowest weight both stop before `-1`). We prove it from (3.2) at the
weights `< -1` (`StrongSl2.adjHyp_of_wt_eq_neg_one`).

Write `E = E 1_{-1}`, `R = R_{-1}`, with unit `η` and counit `ε` of `E ⊣ R`. Condition (3) gives
`R E ≅ E₁ R₁ ⊕ 1_1` at the weight `1` and `E R ≅ X ⊕ 1_{-1}` at the weight `-1`, where
`X = F E 1_{-3}`. Normalize the inclusion `u : 1_1 → R E` and the projection `w : E R → 1_{-1}` of
the summands `1` so that `u ≫ ε = 1` and `η` is the inclusion paired with `w`. Both are possible
because the spaces `Hom(R E, 1_1)` and `Hom(1_{-1}, E R)` are one-dimensional. Then the zigzag of
`(u, w)` is `1` minus a composite `E → X E → E` (`rightZigzag_eq_sub`). Through the two
adjunctions of `E 1_{-3}`, this composite is a closed diagram built from an endomorphism of
`E E 1_{-3}` of degree `-4` (`comp_eq_zero_of_mates`). That endomorphism vanishes by CL Corollary
3.2 for `n ≤ 0` (`cor0Neg_neg`). So `(u, w)` satisfies the zigzag identity for `E`, and the
one-zigzag lemma (`adjHyp_of_rightZigzag`, with `End(E 1_{-1}) = k`) gives (3.2) at `-1`.

With `AdjointPositive.lean` this proves **CL Proposition 3.9 at every weight**
(`StrongSl2.adjHyp`), with shift coherence and Hom-finite, idempotent-complete Hom
categories.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Module
open KrullSchmidtCat (HomFinite)

universe w v u

namespace RightwardCrossing

section NegOne

variable {C : Type u} [Bicategory.{w, v} C] [∀ a b : C, Preadditive (a ⟶ b)]
  [AdditiveWhiskering C]

open AdditiveWhiskering

theorem sub_whiskerRight'' {a b c : C} {f g : a ⟶ b} (η θ : f ⟶ g) (h : b ⟶ c) :
    (η - θ) ▷ h = η ▷ h - θ ▷ h :=
  map_sub (whiskerRightAddHom f g h) η θ

/-- **The zigzag of a unit and a counit coming from two splittings.** Let `E ⊣ R` with unit `η`
and counit `ε`, let `u : 𝟙 ⟶ R ≫ E` satisfy `u ≫ ε = 𝟙`, and let `𝟙 = q₁ ≫ j₁ + w ≫ η` on
`E ≫ R` (a splitting `E ≫ R ≅ X ⊕ 𝟙` whose second inclusion is `η`). Then the zigzag of `(u, w)`
for `E` is the identity minus the composite `E → X E → E`. -/
theorem rightZigzag_eq_sub {b c : C} {E : b ⟶ c} {R : c ⟶ b} {X : b ⟶ b}
    (η : 𝟙 b ⟶ E ≫ R) (eps : R ≫ E ⟶ 𝟙 c) (hZ : leftZigzag η eps = (λ_ E).hom ≫ (ρ_ E).inv)
    (u : 𝟙 c ⟶ R ≫ E) (huε : u ≫ eps = 𝟙 _) (w : E ≫ R ⟶ 𝟙 b) (q₁ : E ≫ R ⟶ X) (j₁ : X ⟶ E ≫ R)
    (htot : q₁ ≫ j₁ + w ≫ η = 𝟙 _) :
    rightZigzag u w = (ρ_ E).hom ≫ (λ_ E).inv -
      (ρ_ E).hom ≫ (((ρ_ E).inv ≫ E ◁ u ≫ (α_ E R E).inv ≫ q₁ ▷ E) ≫
        (j₁ ▷ E ≫ (α_ E R E).hom ≫ E ◁ eps ≫ (ρ_ E).hom)) ≫ (λ_ E).inv := by
  have hw : w ≫ η = 𝟙 _ - q₁ ≫ j₁ := by rw [← htot]; abel
  calc rightZigzag u w
      = E ◁ u ≫ (α_ E R E).inv ≫ (w ≫ η) ▷ E ≫ (α_ E R E).hom ≫ E ◁ eps ≫ (ρ_ E).hom ≫
          (λ_ E).inv := by
        have : rightZigzag u w = E ◁ u ⊗≫ w ▷ E ⊗≫ leftZigzag η eps ⊗≫ 𝟙 _ := by
          rw [hZ, rightZigzag]; bicategory
        rw [this, leftZigzag]; bicategory
    _ = E ◁ u ≫ (α_ E R E).inv ≫ (𝟙 _ - q₁ ≫ j₁) ▷ E ≫ (α_ E R E).hom ≫ E ◁ eps ≫
          (ρ_ E).hom ≫ (λ_ E).inv := by rw [hw]
    _ = E ◁ u ≫ (α_ E R E).inv ≫ (α_ E R E).hom ≫ E ◁ eps ≫ (ρ_ E).hom ≫ (λ_ E).inv -
          E ◁ u ≫ (α_ E R E).inv ≫ (q₁ ≫ j₁) ▷ E ≫ (α_ E R E).hom ≫ E ◁ eps ≫ (ρ_ E).hom ≫
            (λ_ E).inv := by
        rw [sub_whiskerRight'', Preadditive.sub_comp, Preadditive.comp_sub, Preadditive.comp_sub,
          Bicategory.id_whiskerRight, Category.id_comp]
    _ = _ := by
        congr 1
        · calc E ◁ u ≫ (α_ E R E).inv ≫ (α_ E R E).hom ≫ E ◁ eps ≫ (ρ_ E).hom ≫ (λ_ E).inv
              = E ◁ (u ≫ eps) ≫ (ρ_ E).hom ≫ (λ_ E).inv := by
                rw [Iso.inv_hom_id_assoc, Bicategory.whiskerLeft_comp, Category.assoc]
            _ = (ρ_ E).hom ≫ (λ_ E).inv := by
                rw [huε, Bicategory.whiskerLeft_id, Category.id_comp]
        · rw [Bicategory.comp_whiskerRight]
          simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- **A composite through two adjunctions vanishes when the corresponding endomorphism does.**
Let `L ⊣ Em` and `Em ⊣ Rm` (units `η_L`, `ηm`, counits `ε_L`, `εm`), `ϕ : L ⟶ Rm`, and let
`ψ ≫ (ϕ ▷ Em) ≫ ψ' = 𝟙` for `ψ : X ⟶ L ≫ Em`, `ψ' : Rm ≫ Em ⟶ X`. For `A : P ⟶ X ≫ E` and
`B : X ≫ E ⟶ Q`, if the mates `A♭ : Em P ⟶ Em E` and `B♭ : Em E ⟶ Em Q` compose to zero, then
`A ≫ B = 0`. -/
theorem comp_eq_zero_of_mates {a b c : C} {Em : a ⟶ b} {L Rm : b ⟶ a} {X : b ⟶ b}
    {E P Q : b ⟶ c} (η_L : 𝟙 b ⟶ L ≫ Em) (ε_L : Em ≫ L ⟶ 𝟙 a)
    (hL : leftZigzag η_L ε_L = (λ_ L).hom ≫ (ρ_ L).inv)
    (ηm : 𝟙 a ⟶ Em ≫ Rm) (εm : Rm ≫ Em ⟶ 𝟙 b)
    (hRm : rightZigzag ηm εm = (ρ_ Rm).hom ≫ (λ_ Rm).inv) (ϕ : L ⟶ Rm)
    (ψ : X ⟶ L ≫ Em) (ψ' : Rm ≫ Em ⟶ X) (hψ : ψ ≫ ϕ ▷ Em ≫ ψ' = 𝟙 X)
    (A : P ⟶ X ≫ E) (B : X ≫ E ⟶ Q)
    (h0 : (Em ◁ (A ≫ ψ ▷ E ≫ (α_ L Em E).hom) ≫ (α_ Em L (Em ≫ E)).inv ≫
        ε_L ▷ (Em ≫ E) ≫ (λ_ (Em ≫ E)).hom) ≫
      ((λ_ (Em ≫ E)).inv ≫ ηm ▷ (Em ≫ E) ≫ (α_ Em Rm (Em ≫ E)).hom ≫
        Em ◁ ((α_ Rm Em E).inv ≫ ψ' ▷ E ≫ B)) = 0) :
    A ≫ B = 0 := by
  set A_L := A ≫ ψ ▷ E ≫ (α_ L Em E).hom with hAL
  set B_R := (α_ Rm Em E).inv ≫ ψ' ▷ E ≫ B with hBR
  set Af := Em ◁ A_L ≫ (α_ Em L (Em ≫ E)).inv ≫ ε_L ▷ (Em ≫ E) ≫ (λ_ (Em ≫ E)).hom with hAf
  set Bf := (λ_ (Em ≫ E)).inv ≫ ηm ▷ (Em ≫ E) ≫ (α_ Em Rm (Em ≫ E)).hom ≫ Em ◁ B_R with hBf
  have hAB : A ≫ B = A_L ≫ (α_ L Em E).inv ≫ (ϕ ▷ Em) ▷ E ≫ (α_ Rm Em E).hom ≫ B_R := by
    rw [hAL, hBR]
    calc A ≫ B = A ≫ (ψ ≫ ϕ ▷ Em ≫ ψ') ▷ E ≫ B := by
          rw [hψ, Bicategory.id_whiskerRight, Category.id_comp]
      _ = _ := by
          simp only [Bicategory.comp_whiskerRight, Category.assoc, Iso.hom_inv_id_assoc]
  have hA : A_L = 𝟙 _ ⊗≫ η_L ▷ P ⊗≫ L ◁ Af ⊗≫ 𝟙 _ := by
    symm
    calc 𝟙 _ ⊗≫ η_L ▷ P ⊗≫ L ◁ Af ⊗≫ 𝟙 _
        = 𝟙 _ ⊗≫ (η_L ▷ P ≫ (L ≫ Em) ◁ A_L) ⊗≫ L ◁ ε_L ▷ (Em ≫ E) ⊗≫ 𝟙 _ := by
          rw [hAf]; bicategory
      _ = 𝟙 _ ⊗≫ (𝟙 b ◁ A_L ≫ η_L ▷ (L ≫ Em ≫ E)) ⊗≫ L ◁ ε_L ▷ (Em ≫ E) ⊗≫ 𝟙 _ := by
          rw [← whisker_exchange]
      _ = A_L ⊗≫ leftZigzag η_L ε_L ▷ (Em ≫ E) ⊗≫ 𝟙 _ := by
          rw [leftZigzag]; bicategory
      _ = A_L := by rw [hL]; bicategory
  have hB : B_R = 𝟙 _ ⊗≫ Rm ◁ Bf ⊗≫ εm ▷ Q ⊗≫ 𝟙 _ := by
    symm
    calc 𝟙 _ ⊗≫ Rm ◁ Bf ⊗≫ εm ▷ Q ⊗≫ 𝟙 _
        = 𝟙 _ ⊗≫ Rm ◁ ηm ▷ (Em ≫ E) ⊗≫ ((Rm ≫ Em) ◁ B_R ≫ εm ▷ Q) ⊗≫ 𝟙 _ := by
          rw [hBf]; bicategory
      _ = 𝟙 _ ⊗≫ Rm ◁ ηm ▷ (Em ≫ E) ⊗≫ (εm ▷ (Rm ≫ Em ≫ E) ≫ 𝟙 b ◁ B_R) ⊗≫ 𝟙 _ := by
          rw [whisker_exchange]
      _ = 𝟙 _ ⊗≫ rightZigzag ηm εm ▷ (Em ≫ E) ⊗≫ B_R := by
          rw [rightZigzag]; bicategory
      _ = B_R := by rw [hRm]; bicategory
  rw [hAB, hA, hB]
  calc (𝟙 _ ⊗≫ η_L ▷ P ⊗≫ L ◁ Af ⊗≫ 𝟙 _) ≫ (α_ L Em E).inv ≫ (ϕ ▷ Em) ▷ E ≫
        (α_ Rm Em E).hom ≫ (𝟙 _ ⊗≫ Rm ◁ Bf ⊗≫ εm ▷ Q ⊗≫ 𝟙 _)
      = 𝟙 _ ⊗≫ η_L ▷ P ⊗≫ (L ◁ Af ≫ ϕ ▷ (Em ≫ E)) ⊗≫ Rm ◁ Bf ⊗≫ εm ▷ Q ⊗≫ 𝟙 _ := by
        bicategory
    _ = 𝟙 _ ⊗≫ η_L ▷ P ⊗≫ (ϕ ▷ (Em ≫ P) ≫ Rm ◁ Af) ⊗≫ Rm ◁ Bf ⊗≫ εm ▷ Q ⊗≫ 𝟙 _ := by
        rw [whisker_exchange]
    _ = 𝟙 _ ⊗≫ η_L ▷ P ⊗≫ ϕ ▷ (Em ≫ P) ⊗≫ Rm ◁ (Af ≫ Bf) ⊗≫ εm ▷ Q ⊗≫ 𝟙 _ := by
        bicategory
    _ = 0 := by
        rw [h0, whiskerLeft_zero]
        simp [bicategoricalComp]

end NegOne

end RightwardCrossing

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [GradedBicategory.ShiftCoherence B]

omit [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)] in
/-- Two homogeneous 2-morphisms of the same degree, whose degree component lies in a
one-dimensional Hom space, are proportional if the second is nonzero. -/
theorem GradedHomBicat.exists_smul_of_isHomogeneous [GradedBicategory.IsLinear B k]
    {a b : B} {f g : a ⟶ b}
    {φ χ : GradedHomBicat.of₁ f ⟶ GradedHomBicat.of₁ g} {d : ℤ}
    (hφ : GradedHomCat.IsHomogeneous φ d) (hχ : GradedHomCat.IsHomogeneous χ d) (hχ0 : χ ≠ 0)
    (h : finrank k (f ⟶ g⟦d⟧) = 1) : ∃ c : k, φ = c • χ := by
  obtain ⟨x, rfl⟩ := hφ
  obtain ⟨y, rfl⟩ := hχ
  have hy : (y : f ⟶ g⟦d⟧) ≠ 0 := fun h0 => hχ0 (by
    change GradedHomCat.homOf d y = 0
    rw [show y = 0 from h0]
    exact GradedHomCat.homOf_zero d)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hy).1 h x
  exact ⟨c, by rw [← hc, GradedHomCat.homOf_smul]⟩

namespace StrongSl2

open GradedHomBicat GradedHomCat RightwardCrossing

variable (S : StrongSl2 k B) [GradedBicategory.IsLinear B k]

omit [GradedBicategory.IsLinear B k] in
theorem grUnit_ne_zero {r : ℤ} (h : ¬ IsZero (S.E r)) : S.grUnit r ≠ 0 := by
  intro h0
  have hz := S.leftZigzag_grUnit_grCounit r
  rw [h0, leftZigzag, GradedHomBicat.zero_whiskerRight] at hz
  simp only [bicategoricalComp, zero_comp] at hz
  apply id_ne_zero_of_not_isZero h
  have e : 𝟙 (S.grE r) = (λ_ (S.grE r)).inv ≫ ((λ_ (S.grE r)).hom ≫ (ρ_ (S.grE r)).inv) ≫
      (ρ_ (S.grE r)).hom := by simp
  rw [← hz, zero_comp, comp_zero] at e
  exact e

variable [∀ a b : B, HomFinite k (a ⟶ b)]

/-- **(3.2) at the weight `-1`**: at the object `s + 1` of weight `-1`, given (3.2) at the
weights `< -1`, `(E 1_{-1})_L ≅ 1_{-1} F`. -/
theorem adjHyp_of_wt_eq_neg_one {s : ℤ} (h1 : S.wt (s + 1) = -1)
    (hyp : ∀ r', r' < s + 1 → S.AdjHyp r') : S.AdjHyp (s + 1) := by
  by_cases hb : IsZero (𝟙 (S.obj (s + 1)))
  · exact S.adjHyp_of_isZero (Or.inl hb)
  by_cases hc : IsZero (𝟙 (S.obj (s + 1 + 1)))
  · exact S.adjHyp_of_isZero (Or.inr hc)
  have hend : finrank k (S.E (s + 1) ⟶ S.E (s + 1)) = 1 :=
    S.lem1Neg_zero (r₁ := s + 1) (by omega) hyp le_rfl (by omega) hb
  have hE : ¬ IsZero (S.E (s + 1)) := fun hz => by
    rw [finrank_hom_of_isZero_left k hz] at hend; exact zero_ne_one hend
  have ha0 : S.n₀ + 2 * (s + 1) + 1 = 0 := by
    have : S.wt (s + 1) = S.n₀ + 2 * (s + 1) := rfl
    omega
  have hw2 : S.wt (s + 1 + 1) = 1 := by rw [S.wt_add_one, h1]; norm_num
  have hT1 : ((S.wt (s + 1 + 1)).toNat : ℤ) = 1 := by rw [hw2]; rfl
  have hTn : ((-S.wt (s + 1)).toNat : ℤ) = 1 := by rw [h1]; rfl
  obtain ⟨e₁⟩ := S.exists_EFDecomp (r := s + 1) (by omega)
  obtain ⟨f⟩ := S.exists_FEDecomp (r := s) (by omega)
  -- the splitting at the weight `1`
  let ψ1 := S.rhoSourceIso (s + 1)
  let tc : ℤ := 1 * (((S.wt (s + 1 + 1)).toNat : ℕ) - 1 - 2 * ((0 : ℕ) : ℤ))
  let osc : of₁ (S.oneShift (s + 1) 0) ≅ 𝟙 (of (S.obj (s + 1 + 1))) :=
    shiftIso₁ (𝟙 (S.obj (s + 1 + 1))) tc
  let u₀ : 𝟙 (of (S.obj (s + 1 + 1))) ⟶ S.grR (s + 1) ≫ S.grE (s + 1) :=
    osc.inv ≫ incl₂ (ι e₁ 0) ≫ ψ1.inv
  let p₀ : S.grR (s + 1) ≫ S.grE (s + 1) ⟶ 𝟙 (of (S.obj (s + 1 + 1))) :=
    ψ1.hom ≫ incl₂ (π e₁ 0) ≫ osc.hom
  have hup : u₀ ≫ p₀ = 𝟙 _ := by
    have : ι e₁ 0 ≫ π e₁ 0 = 𝟙 _ := ι_π_self e₁ (by omega)
    have h' : incl₂ (ι e₁ 0) ≫ incl₂ (π e₁ 0) = 𝟙 _ := by rw [← incl₂_comp, this, incl₂_id]
    simp only [u₀, p₀, Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% h', Iso.inv_hom_id]
  -- the splitting at the weight `-1`
  let θ := S.rhoTargetIso s
  let tn : ℤ := 1 * ((((-S.wt (s + 1)).toNat : ℕ) : ℤ) - 1 - 2 * ((0 : ℕ) : ℤ))
  let osn : of₁ (S.oneShiftNeg s 0) ≅ 𝟙 (of (S.obj (s + 1))) :=
    shiftIso₁ (𝟙 (S.obj (s + 1))) tn
  let i₀ : 𝟙 (of (S.obj (s + 1))) ⟶ S.grE (s + 1) ≫ S.grR (s + 1) :=
    osn.inv ≫ incl₂ (ιN f 0) ≫ θ.inv
  let w₀ : S.grE (s + 1) ≫ S.grR (s + 1) ⟶ 𝟙 (of (S.obj (s + 1))) :=
    θ.hom ≫ incl₂ (πN f 0) ≫ osn.hom
  let q₁ : S.grE (s + 1) ≫ S.grR (s + 1) ⟶ of₁ (S.F s ≫ S.E s) := θ.hom ≫ incl₂ (πEF f)
  let j₁ : of₁ (S.F s ≫ S.E s) ⟶ S.grE (s + 1) ≫ S.grR (s + 1) := incl₂ (ιEF f) ≫ θ.inv
  have hiw : i₀ ≫ w₀ = 𝟙 _ := by
    have : ιN f 0 ≫ πN f 0 = 𝟙 _ := ιN_πN_self f (by omega)
    have h' : incl₂ (ιN f 0) ≫ incl₂ (πN f 0) = 𝟙 _ := by rw [← incl₂_comp, this, incl₂_id]
    simp only [i₀, w₀, Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% h', Iso.inv_hom_id]
  have htot₀ : q₁ ≫ j₁ + w₀ ≫ i₀ = 𝟙 _ := by
    have htotB := totalN f
    have hN1 : (-S.wt (s + 1)).toNat = 1 := by omega
    rw [hN1, Finset.sum_range_one] at htotB
    have h' : incl₂ (πN f 0) ≫ incl₂ (ιN f 0) + incl₂ (πEF f) ≫ incl₂ (ιEF f) = 𝟙 _ := by
      rw [← incl₂_comp, ← incl₂_comp, ← GradedHomBicat.incl₂_add', htotB, incl₂_id]
    calc q₁ ≫ j₁ + w₀ ≫ i₀ = θ.hom ≫ (incl₂ (πN f 0) ≫ incl₂ (ιN f 0) +
          incl₂ (πEF f) ≫ incl₂ (ιEF f)) ≫ θ.inv := by
          simp only [q₁, j₁, w₀, i₀, Category.assoc, Iso.hom_inv_id_assoc,
            Preadditive.add_comp, Preadditive.comp_add]
          abel
      _ = 𝟙 _ := by rw [h', Category.id_comp, Iso.hom_inv_id]
  -- normalizations
  have hp₀ : IsHomogeneous p₀ 0 :=
    ((S.isHomogeneous_rhoSourceIso_hom (s + 1)).comp ((isHomogeneous_incl₂ _).comp
      ((shiftIso₁_hom_isHomogeneous (𝟙 _) tc : IsHomogeneous osc.hom tc)) rfl) rfl).of_eq (by
        simp only [tc]; push_cast; omega)
  have hu₀ : IsHomogeneous u₀ 0 :=
    (((shiftIso₁_inv_isHomogeneous (𝟙 _) tc : IsHomogeneous osc.inv (-tc))).comp
      ((isHomogeneous_incl₂ _).comp (S.isHomogeneous_rhoSourceIso_inv (s + 1)) rfl) rfl).of_eq (by
        simp only [tc]; push_cast; omega)
  have hi₀ : IsHomogeneous i₀ 0 :=
    (((shiftIso₁_inv_isHomogeneous (𝟙 _) tn : IsHomogeneous osn.inv (-tn))).comp
      ((isHomogeneous_incl₂ _).comp (S.isHomogeneous_rhoTargetIso_inv s) rfl) rfl).of_eq (by
        simp only [tn]; push_cast; omega)
  have hw₀ : IsHomogeneous w₀ 0 :=
    ((S.isHomogeneous_rhoTargetIso_hom s).comp ((isHomogeneous_incl₂ _).comp
      ((shiftIso₁_hom_isHomogeneous (𝟙 _) tn : IsHomogeneous osn.hom tn)) rfl) rfl).of_eq (by
        simp only [tn]; push_cast; omega)
  have hid₁ : 𝟙 (𝟙 (of (S.obj (s + 1 + 1)))) ≠ 0 := id_ne_zero_of_not_isZero hc
  have hid₀ : 𝟙 (𝟙 (of (S.obj (s + 1)))) ≠ 0 := id_ne_zero_of_not_isZero hb
  obtain ⟨l, hl⟩ := GradedHomBicat.exists_smul_of_isHomogeneous (k := k) hp₀
    (isHomogeneous_incl₂ _) (S.grCounit_ne_zero hE) (by
      rw [finrank_hom_shift_zero k _ _ rfl, finrank_hom_congr_left k (whiskerRightShiftIso _ _ _)]
      exact (S.finrank_EF_counit (s + 1)).trans hend)
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hl
    apply hid₁
    rw [← hup, hl, comp_zero]
  obtain ⟨m, hm⟩ := GradedHomBicat.exists_smul_of_isHomogeneous (k := k) hi₀
    (isHomogeneous_incl₂ _) (S.grUnit_ne_zero hE) (by
      rw [finrank_hom_shift_zero k _ _ rfl, finrank_hom_congr_right k _
        (whiskerLeftShiftIso _ _ _)]
      exact (S.finrank_FE_unit (s + 1)).trans hend)
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hm
    apply hid₀
    rw [← hiw, hm, zero_comp]
  let u := l • u₀
  let w := m • w₀
  have huε : u ≫ S.grCounit (s + 1) = 𝟙 _ := by
    have : S.grCounit (s + 1) = l⁻¹ • p₀ := by rw [hl, smul_smul, inv_mul_cancel₀ hl0, one_smul]
    simp only [u, this, Linear.smul_comp, Linear.comp_smul, smul_smul, hup, inv_mul_cancel₀ hl0,
      one_smul]
  have htot : q₁ ≫ j₁ + w ≫ S.grUnit (s + 1) = 𝟙 _ := by
    rw [← htot₀, hm]
    simp only [w, Linear.smul_comp, Linear.comp_smul]
  -- the cross term vanishes
  have hz := rightZigzag_eq_sub (S.grUnit (s + 1)) (S.grCounit (s + 1))
    (S.leftZigzag_grUnit_grCounit (s + 1)) u huε w q₁ j₁ htot
  -- the cross term vanishes, through the adjunctions of `E 1_{-3}`
  obtain ⟨adjL⟩ := hyp s (by omega)
  have hL := (leftZigzag_incl₂ adjL.unit adjL.counit).trans (by
    rw [adjL.left_triangle, incl₂_comp, ← leftUnitor_hom_eq, ← rightUnitor_inv_eq])
  have hm : rightZigzag (S.grUnit s) (S.grCounit s) = (ρ_ (S.grR s)).hom ≫ (λ_ (S.grR s)).inv := by
    rw [rightUnitor_hom_eq, leftUnitor_inv_eq, ← incl₂_comp, rightZigzag_incl₂,
      (S.adj s).right_triangle]
  let ϕ : of₁ ((S.F s)⟦-(S.wt s + 1)⟧) ⟶ S.grR s :=
    (shiftIso₁ (S.F s) (-(S.wt s + 1))).hom ≫ (shiftIso₁ (S.F s) (S.n₀ + 2 * s + 1)).inv
  let ψ : of₁ (S.F s ≫ S.E s) ⟶ of₁ ((S.F s)⟦-(S.wt s + 1)⟧) ≫ S.grE s :=
    (shiftIso₁ (S.F s) (-(S.wt s + 1))).inv ▷ S.grE s
  let ψ' : S.grR s ≫ S.grE s ⟶ of₁ (S.F s ≫ S.E s) := (S.rhoSourceIso s).hom
  have hψ : ψ ≫ ϕ ▷ S.grE s ≫ ψ' = 𝟙 _ := by
    simp only [ψ, ψ', ϕ, rhoSourceIso, whiskerRightIso_hom, ← Bicategory.comp_whiskerRight,
      Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Bicategory.id_whiskerRight]
    rfl
  have hu : IsHomogeneous u 0 := hu₀.smul l
  have hw : IsHomogeneous w 0 := hw₀.smul m
  have hq₁ : IsHomogeneous q₁ 0 :=
    ((S.isHomogeneous_rhoTargetIso_hom s).comp (isHomogeneous_incl₂ _) rfl).of_eq (by omega)
  have hj₁ : IsHomogeneous j₁ 0 :=
    ((isHomogeneous_incl₂ _).comp (S.isHomogeneous_rhoTargetIso_inv s) rfl).of_eq (by omega)
  have hA' : IsHomogeneous ((ρ_ (S.grE (s + 1))).inv ≫ S.grE (s + 1) ◁ u ≫ (α_ _ _ _).inv ≫
      q₁ ▷ S.grE (s + 1)) 0 :=
    ((isHomogeneous_rightUnitor_inv _).comp ((isHomogeneous_whiskerLeft _ hu).comp
      ((isHomogeneous_associator_inv _ _ _).comp (isHomogeneous_whiskerRight hq₁ _) rfl) rfl)
        rfl).of_eq (by ring)
  have hB' : IsHomogeneous (j₁ ▷ S.grE (s + 1) ≫ (α_ _ _ _).hom ≫
      S.grE (s + 1) ◁ S.grCounit (s + 1) ≫ (ρ_ (S.grE (s + 1))).hom) 0 :=
    ((isHomogeneous_whiskerRight hj₁ _).comp ((isHomogeneous_associator_hom _ _ _).comp
      ((isHomogeneous_whiskerLeft _ (isHomogeneous_incl₂ _)).comp
        (isHomogeneous_rightUnitor_hom _) rfl) rfl) rfl).of_eq (by ring)
  have hψd : IsHomogeneous ψ (S.wt s + 1) :=
    (isHomogeneous_whiskerRight (shiftIso₁_inv_isHomogeneous _ _) _).of_eq (by ring)
  have hψ'd : IsHomogeneous ψ' (S.n₀ + 2 * s + 1) := S.isHomogeneous_rhoSourceIso_hom s
  have hws : S.wt s = -3 := by have := S.wt_add_one s; omega
  have hws' : S.n₀ + 2 * s = -3 := hws
  have hcross := comp_eq_zero_of_mates (Em := S.grE s) (L := of₁ ((S.F s)⟦-(S.wt s + 1)⟧))
    (Rm := S.grR s) (X := of₁ (S.F s ≫ S.E s)) (E := S.grE (s + 1)) (P := S.grE (s + 1))
    (Q := S.grE (s + 1)) (incl₂ adjL.unit) (incl₂ adjL.counit) hL (S.grUnit s)
    (S.grCounit s) hm ϕ ψ ψ' hψ
    ((ρ_ (S.grE (s + 1))).inv ≫ S.grE (s + 1) ◁ u ≫ (α_ _ _ _).inv ≫ q₁ ▷ S.grE (s + 1))
    (j₁ ▷ S.grE (s + 1) ≫ (α_ _ _ _).hom ≫ S.grE (s + 1) ◁ S.grCounit (s + 1) ≫
      (ρ_ (S.grE (s + 1))).hom)
    (GradedHomBicat.eq_zero_of_isHomogeneous (k := k) (d := -4)
      ((((isHomogeneous_whiskerLeft _ ((hA'.comp ((isHomogeneous_whiskerRight hψd _).comp
        (isHomogeneous_associator_hom _ _ _) rfl) rfl))).comp
          ((isHomogeneous_associator_inv _ _ _).comp
            ((isHomogeneous_whiskerRight (isHomogeneous_incl₂ _) _).comp
              (isHomogeneous_leftUnitor_hom _) rfl) rfl) rfl).comp
        ((isHomogeneous_leftUnitor_inv _).comp
          ((isHomogeneous_whiskerRight (isHomogeneous_incl₂ _) _).comp
            ((isHomogeneous_associator_hom _ _ _).comp
              (isHomogeneous_whiskerLeft _ ((isHomogeneous_associator_inv _ _ _).comp
                ((isHomogeneous_whiskerRight hψ'd _).comp hB' rfl) rfl)) rfl) rfl) rfl)
          rfl).of_eq (by omega))
      (S.cor0Neg_neg (r₁ := s + 1) (by omega) hyp s (by omega) (by omega) _ (by norm_num)))
  rw [hcross, zero_comp, comp_zero, sub_zero] at hz
  exact S.adjHyp_of_rightZigzag (s + 1) u w (hu.of_eq (by omega)) (hw.of_eq (by omega)) hz hend

/-- **CL Proposition 3.9**: in a strong 2-representation of `sl₂`
(with shift coherence and Hom-finite, idempotent-complete Hom categories), the left adjoint of
`E 1_n` is `1_n F ⟨-n-1⟩` at every weight `n`: `E` and `F` are biadjoint up to the shifts of
(3.2). -/
theorem adjHyp [∀ a b : B, IsIdempotentComplete (a ⟶ b)] (S : StrongSl2 k B)
    (r : ℤ) : S.AdjHyp r := by
  by_cases hr : S.wt r = -1
  · obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by ring⟩
    exact S.adjHyp_of_wt_eq_neg_one hr fun r' hr' =>
      S.adjHyp_of_wt_ne_neg_one (by have := S.wt_lt_wt hr'; omega)
  · exact S.adjHyp_of_wt_ne_neg_one hr

end StrongSl2

end Categorification.TwoRep

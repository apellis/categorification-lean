/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.CyclicDotNegOne

/-!
# Cyclicity of the crossing (CL Lemma 4.2)

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, §4.2, Lemma 4.2 (`lem:B`, eq. (4.10)): the downward crossing defined as the
right mate of the crossing on `E E 1_n` (under the composite adjunction `E E ⊣ R R` of the right
adjunctions) equals the one defined as the left mate (under the composite of the left
adjunctions `R ⊣ E`), provided the dot is cyclic for the chosen left adjunctions (Lemma 4.1).

CL's proof, in the graded-Hom bicategory: both mates of the crossing are homogeneous of degree
`-2`, and the degree `-2` endomorphisms of `E E 1_n` form a line (Corollary 3.2), so the two
mates differ by a scalar `κ` (CL (4.11)). Mates are anti-multiplicative and compatible with
whiskering, and the two mates of the dots agree (Lemma 4.1), so the nilHecke relation
`(E x) τ - τ (x E) = 1` gives `κ = 1` (CL (4.12)–(4.15)).

## Main declarations

* `Bicategory.Adjunction.comp_unit_eq`, `comp_counit_eq`: explicit units and counits of composite
  adjunctions;
* `StrongSl2.cyclic_cross_of_cyclic_dot`: the crossing is cyclic if the dots are;
* `StrongSl2.BBw.leftAdjN`: under (BB_w), a choice of left adjunctions `R_n ⊣ E 1_n` normalized
  as in CL (4.1), for which the dots are cyclic (`BBw.cyclic_dot_leftAdjN`);
* `StrongSl2.BBw.cyclic_cross`: **CL Lemma 4.2 under (BB_w)** for these left adjunctions.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

universe w v u

section Generic

variable {C : Type u} [Bicategory.{w, v} C] {a b c : C} {f₁ : a ⟶ b} {g₁ : b ⟶ a}
  {f₂ : b ⟶ c} {g₂ : c ⟶ b}

theorem comp_unit_eq (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) :
    (adj₁.comp adj₂).unit = adj₁.unit ≫ f₁ ◁ (λ_ g₁).inv ≫ f₁ ◁ adj₂.unit ▷ g₁ ≫
      f₁ ◁ (α_ f₂ g₂ g₁).hom ≫ (α_ f₁ f₂ (g₂ ≫ g₁)).inv := by
  simp only [Bicategory.Adjunction.comp, Bicategory.Adjunction.compUnit]
  bicategory

theorem comp_counit_eq (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) :
    (adj₁.comp adj₂).counit = (α_ g₂ g₁ (f₁ ≫ f₂)).hom ≫ g₂ ◁ (α_ g₁ f₁ f₂).inv ≫
      g₂ ◁ adj₁.counit ▷ f₂ ≫ g₂ ◁ (λ_ f₂).hom ≫ adj₂.counit := by
  simp only [Bicategory.Adjunction.comp, Bicategory.Adjunction.compCounit]
  bicategory

end Generic

/-! ## Composite adjunctions in the graded-Hom bicategory -/

section GradedHom

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B] [GradedBicategory.ShiftCoherence B]
  [GradedBicategory.IsLinear B k]

namespace GradedHomBicat

open GradedHomCat

omit [∀ a b : B, Linear k (a ⟶ b)] [GradedBicategory.IsLinear B k] in
theorem isHomogeneous_comp_unit {a b c : GradedHomBicat B} {f₁ : a ⟶ b} {g₁ : b ⟶ a}
    {f₂ : b ⟶ c} {g₂ : c ⟶ b} (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) {d₁ d₂ : ℤ}
    (h₁ : IsHomogeneous adj₁.unit d₁) (h₂ : IsHomogeneous adj₂.unit d₂) :
    IsHomogeneous (adj₁.comp adj₂).unit (d₁ + d₂) := by
  rw [comp_unit_eq]
  have e1 : IsHomogeneous (λ_ g₁).inv 0 := isHomogeneous_incl₂ (λ_ g₁.as).inv
  have e2 : IsHomogeneous (α_ f₂ g₂ g₁).hom 0 := isHomogeneous_incl₂ (α_ f₂.as g₂.as g₁.as).hom
  have e3 : IsHomogeneous (α_ f₁ f₂ (g₂ ≫ g₁)).inv 0 :=
    isHomogeneous_incl₂ (α_ f₁.as f₂.as (g₂.as ≫ g₁.as)).inv
  exact (h₁.comp ((isHomogeneous_whiskerLeft f₁ e1).comp ((isHomogeneous_whiskerLeft f₁
    (isHomogeneous_whiskerRight h₂ g₁)).comp ((isHomogeneous_whiskerLeft f₁ e2).comp e3
      rfl) rfl) rfl) rfl).of_eq (by ring)

omit [∀ a b : B, Linear k (a ⟶ b)] [GradedBicategory.IsLinear B k] in
theorem isHomogeneous_comp_counit {a b c : GradedHomBicat B} {f₁ : a ⟶ b} {g₁ : b ⟶ a}
    {f₂ : b ⟶ c} {g₂ : c ⟶ b} (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) {d₁ d₂ : ℤ}
    (h₁ : IsHomogeneous adj₁.counit d₁) (h₂ : IsHomogeneous adj₂.counit d₂) :
    IsHomogeneous (adj₁.comp adj₂).counit (d₁ + d₂) := by
  rw [comp_counit_eq]
  have e1 : IsHomogeneous (α_ g₂ g₁ (f₁ ≫ f₂)).hom 0 :=
    isHomogeneous_incl₂ (α_ g₂.as g₁.as (f₁.as ≫ f₂.as)).hom
  have e2 : IsHomogeneous (α_ g₁ f₁ f₂).inv 0 := isHomogeneous_incl₂ (α_ g₁.as f₁.as f₂.as).inv
  have e3 : IsHomogeneous (λ_ f₂).hom 0 := isHomogeneous_incl₂ (λ_ f₂.as).hom
  exact (e1.comp ((isHomogeneous_whiskerLeft g₂ e2).comp ((isHomogeneous_whiskerLeft g₂
    (isHomogeneous_whiskerRight h₁ f₂)).comp ((isHomogeneous_whiskerLeft g₂ e3).comp h₂
      rfl) rfl) rfl) rfl).of_eq (by ring)

theorem conjugateEquiv_sub {a b : GradedHomBicat B} {l : a ⟶ b} {r : b ⟶ a}
    (adj₁ adj₂ : l ⊣ r) (α β : l ⟶ l) :
    conjugateEquiv adj₁ adj₂ (α - β) = conjugateEquiv adj₁ adj₂ α - conjugateEquiv adj₁ adj₂ β := by
  have h := conjugateEquiv_add adj₁ adj₂ (α - β) β
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm

theorem conjugateEquiv_symm_sub {a b : GradedHomBicat B} {l : a ⟶ b} {r : b ⟶ a}
    (adj₁ adj₂ : l ⊣ r) (α β : r ⟶ r) :
    (conjugateEquiv adj₁ adj₂).symm (α - β) =
      (conjugateEquiv adj₁ adj₂).symm α - (conjugateEquiv adj₁ adj₂).symm β := by
  have h := conjugateEquiv_symm_add adj₁ adj₂ (α - β) β
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm

end GradedHomBicat

end GradedHom

/-! ## Lemma 4.2 -/

section Cross

open KrullSchmidtCat (HomFinite)

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [GradedBicategory.ShiftCoherence B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, HomFinite k (a ⟶ b)]

namespace StrongSl2

open GradedHomBicat GradedHomCat Module
open KrullSchmidtCat (HomFinite)

variable (S : StrongSl2 k B)

/-- **CL Lemma 4.2 from Lemma 4.1** under (BB_w): for left adjunctions `R_n ⊣ E 1_n`,
`R_{n+2} ⊣ E 1_{n+2}` (homogeneous units and counits) for which the dots are cyclic, the
crossing on `E E 1_n` is cyclic: its right mate under the composite of the right adjunctions
equals its left mate under the composite of the left adjunctions. -/
theorem cyclic_cross_of_cyclic_dot [∀ a b : B, IsIdempotentComplete (a ⟶ b)] (hS : S.BBw)
    (r : ℤ) (A₁ : S.grR r ⊣ S.grE r) (A₂ : S.grR (r + 1) ⊣ S.grE (r + 1))
    (hu₁ : IsHomogeneous A₁.unit (-(2 * S.wt r + 2)))
    (hc₁ : IsHomogeneous A₁.counit (2 * S.wt r + 2))
    (hu₂ : IsHomogeneous A₂.unit (-(2 * S.wt (r + 1) + 2)))
    (hc₂ : IsHomogeneous A₂.counit (2 * S.wt (r + 1) + 2))
    (h₁ : Bicategory.conjugateEquiv (S.grAdj r) (S.grAdj r) (S.grDotN r) =
      (Bicategory.conjugateEquiv A₁ A₁).symm (S.grDotN r))
    (h₂ : Bicategory.conjugateEquiv (S.grAdj (r + 1)) (S.grAdj (r + 1)) (S.grDotN (r + 1)) =
      (Bicategory.conjugateEquiv A₂ A₂).symm (S.grDotN (r + 1))) :
    Bicategory.conjugateEquiv ((S.grAdj r).comp (S.grAdj (r + 1))) ((S.grAdj r).comp (S.grAdj (r + 1)))
        (S.grCross r) =
      (Bicategory.conjugateEquiv (A₂.comp A₁) (A₂.comp A₁)).symm (S.grCross r) := by
  set Bc := (S.grAdj r).comp (S.grAdj (r + 1)) with hBc
  set Ac := A₂.comp A₁ with hAc
  set τ := S.grCross r with hτ
  set x₁ := S.grDotN r with hx₁
  set x₂ := S.grDotN (r + 1) with hx₂
  -- the two mates of the dots agree
  have hd₁ : Bicategory.conjugateEquiv Bc Bc (x₁ ▷ S.grE (r + 1)) =
      (Bicategory.conjugateEquiv Ac Ac).symm (x₁ ▷ S.grE (r + 1)) := by
    rw [Equiv.eq_symm_apply, hBc, Bicategory.conjugateEquiv_whiskerRight, h₁, hAc,
      Bicategory.conjugateEquiv_whiskerLeft, Equiv.apply_symm_apply]
  have hd₂ : Bicategory.conjugateEquiv Bc Bc (S.grE r ◁ x₂) =
      (Bicategory.conjugateEquiv Ac Ac).symm (S.grE r ◁ x₂) := by
    rw [Equiv.eq_symm_apply, hBc, Bicategory.conjugateEquiv_whiskerLeft, h₂, hAc,
      Bicategory.conjugateEquiv_whiskerRight, Equiv.apply_symm_apply]
  -- the nilHecke relation under both mates
  have hs := S.grDotN_slide r
  have eqR : Bicategory.conjugateEquiv Bc Bc τ ≫ Bicategory.conjugateEquiv Bc Bc (S.grE r ◁ x₂) -
      Bicategory.conjugateEquiv Bc Bc (x₁ ▷ S.grE (r + 1)) ≫ Bicategory.conjugateEquiv Bc Bc τ = 𝟙 _ := by
    have := congrArg (Bicategory.conjugateEquiv Bc Bc) hs
    rw [conjugateEquiv_sub, ← Bicategory.conjugateEquiv_comp, ← Bicategory.conjugateEquiv_comp,
      Bicategory.conjugateEquiv_id] at this
    exact this
  have eqL : (Bicategory.conjugateEquiv Ac Ac).symm τ ≫ (Bicategory.conjugateEquiv Ac Ac).symm (S.grE r ◁ x₂) -
      (Bicategory.conjugateEquiv Ac Ac).symm (x₁ ▷ S.grE (r + 1)) ≫ (Bicategory.conjugateEquiv Ac Ac).symm τ =
        𝟙 _ := by
    have := congrArg (Bicategory.conjugateEquiv Ac Ac).symm hs
    rw [conjugateEquiv_symm_sub, ← Bicategory.conjugateEquiv_symm_comp Ac Ac Ac τ,
      ← Bicategory.conjugateEquiv_symm_comp Ac Ac Ac _ τ, Bicategory.conjugateEquiv_symm_id]
      at this
    rw [← hx₁, ← hx₂] at this
    exact this
  -- the case `τ = 0`
  by_cases hτ0 : τ = 0
  · have c0 : Bicategory.conjugateEquiv Bc Bc 0 = 0 := by
      have h := conjugateEquiv_add Bc Bc 0 0
      rw [add_zero] at h
      simpa using h
    have h1 : 𝟙 (S.grR (r + 1) ≫ S.grR r) = 0 := by
      rw [← eqR, hτ0, c0, zero_comp, comp_zero, sub_zero]
    have hz : ∀ φ : S.grR (r + 1) ≫ S.grR r ⟶ S.grR (r + 1) ≫ S.grR r, φ = 0 := fun φ => by
      rw [← Category.comp_id φ, h1, comp_zero]
    rw [hz (Bicategory.conjugateEquiv Bc Bc τ), hz ((Bicategory.conjugateEquiv Ac Ac).symm τ)]
  -- degrees
  have hBu : IsHomogeneous Bc.unit (0 + 0) :=
    isHomogeneous_comp_unit _ _ (isHomogeneous_incl₂ _) (isHomogeneous_incl₂ _)
  have hBc' : IsHomogeneous Bc.counit (-(0 + 0)) :=
    (isHomogeneous_comp_counit _ _ (isHomogeneous_incl₂ _) (isHomogeneous_incl₂ _)).of_eq
      (by simp)
  have hAu : IsHomogeneous Ac.unit (-(2 * S.wt (r + 1) + 2) + -(2 * S.wt r + 2)) :=
    isHomogeneous_comp_unit A₂ A₁ hu₂ hu₁
  have hAc' : IsHomogeneous Ac.counit (-(-(2 * S.wt (r + 1) + 2) + -(2 * S.wt r + 2))) :=
    (isHomogeneous_comp_counit A₂ A₁ hc₂ hc₁).of_eq (by ring)
  have hτH : IsHomogeneous τ (-2) := isHomogeneous_of₂ _ _
  have hLH : IsHomogeneous ((Bicategory.conjugateEquiv Ac Ac).symm τ) (-2) :=
    isHomogeneous_conjugateEquiv_symm Ac Ac hAu hAc' hτH
  have hτ'H : IsHomogeneous ((Bicategory.conjugateEquiv Bc Bc).symm ((Bicategory.conjugateEquiv Ac Ac).symm τ)) (-2) :=
    isHomogeneous_conjugateEquiv_symm Bc Bc hBu hBc' hLH
  -- the degree `-2` endomorphisms of `E E 1_n` form a line (CL Corollary 3.2)
  have hfin : finrank k (S.E r ≫ S.E (r + 1) ⟶ (S.E r ≫ S.E (r + 1))⟦(-2 : ℤ)⟧) = 1 := by
    have hyp : ∀ r', S.AdjHyp r' := hS.adjHyp
    have hE : ¬ IsZero (S.E r ≫ S.E (r + 1)) := fun hz =>
      hτ0 (((incl _).map_isZero hz).eq_of_src _ _)
    rcases le_or_gt (-2) (S.wt r) with hw | hw
    · refine S.cor0_zero (r₀ := r + 1) (by rw [S.wt_add_one]; omega) (fun r' _ => hyp r')
        (by omega) (fun hz => hE ?_)
      exact isZero_comp_right _ (IsZero.of_iso (isZero_comp_right _ hz) (ρ_ _).symm)
    · refine S.cor0Neg_zero (r₁ := r + 1) (by rw [S.wt_add_one]; omega) (fun r' _ => hyp r')
        (by omega) (by rw [S.wt_add_one]; omega) (fun hz => hE ?_)
      exact isZero_comp_left (IsZero.of_iso (isZero_comp_left hz _) (λ_ _).symm) _
  obtain ⟨κ, hκ⟩ : ∃ κ : k,
      (Bicategory.conjugateEquiv Bc Bc).symm ((Bicategory.conjugateEquiv Ac Ac).symm τ) = κ • τ :=
    GradedHomBicat.exists_smul_of_isHomogeneous hτ'H hτH hτ0 hfin
  have hL : (Bicategory.conjugateEquiv Ac Ac).symm τ = κ • Bicategory.conjugateEquiv Bc Bc τ := by
    apply (Bicategory.conjugateEquiv Bc Bc).symm.injective
    rw [hκ, conjugateEquiv_symm_smul, Equiv.symm_apply_apply]
  rw [hL, ← hd₁, ← hd₂, Linear.smul_comp, Linear.comp_smul, ← smul_sub, eqR] at eqL
  by_cases h1 : 𝟙 (S.grR (r + 1) ≫ S.grR r) = 0
  · have hz : ∀ φ : S.grR (r + 1) ≫ S.grR r ⟶ S.grR (r + 1) ≫ S.grR r, φ = 0 := fun φ => by
      rw [← Category.comp_id φ, h1, comp_zero]
    rw [hz (Bicategory.conjugateEquiv Bc Bc τ), hz ((Bicategory.conjugateEquiv Ac Ac).symm τ)]
  have hκ1 : κ = 1 := by
    have h : (κ - 1) • 𝟙 (S.grR (r + 1) ≫ S.grR r) = 0 := by
      rw [sub_smul, one_smul, eqL, sub_self]
    rcases smul_eq_zero.1 h with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h h1
  rw [hL, hκ1, one_smul]

omit [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem cyclic_dotN_of_cyclic_dot {r : ℤ} (adjL : S.grR r ⊣ S.grE r)
    (h : Bicategory.conjugateEquiv (S.grAdj r) (S.grAdj r) (S.grDot r) =
      (Bicategory.conjugateEquiv adjL adjL).symm (S.grDot r)) :
    Bicategory.conjugateEquiv (S.grAdj r) (S.grAdj r) (S.grDotN r) =
      (Bicategory.conjugateEquiv adjL adjL).symm (S.grDotN r) := by
  rw [grDotN, conjugateEquiv_smul, conjugateEquiv_symm_smul, h]

variable {S}

/-- **The normalized left adjunctions** under (BB_w): for each `n`, a left adjunction
`R_n ⊣ E 1_n` normalized as in CL (4.1), for which the dot is cyclic (`BBw.cyclic_dot`). -/
def BBw.leftAdjN [∀ a b : B, IsIdempotentComplete (a ⟶ b)] (hS : S.BBw) (r : ℤ) :
    S.grR r ⊣ S.grE r :=
  (BBw.cyclic_dot S hS r).choose

theorem BBw.leftAdjN_spec [∀ a b : B, IsIdempotentComplete (a ⟶ b)] (hS : S.BBw) (r : ℤ) :
    IsHomogeneous (hS.leftAdjN r).unit (-(2 * S.wt r + 2)) ∧
      IsHomogeneous (hS.leftAdjN r).counit (2 * S.wt r + 2) ∧
      (-1 ≤ S.wt r → S.cwBubble (hS.leftAdjN r).unit = 𝟙 _) ∧
      (S.wt r ≤ -2 → S.ccwBubble (hS.leftAdjN r).counit = 𝟙 _) ∧
      Bicategory.conjugateEquiv (S.grAdj r) (S.grAdj r) (S.grDot r) =
        (Bicategory.conjugateEquiv (hS.leftAdjN r) (hS.leftAdjN r)).symm (S.grDot r) :=
  (BBw.cyclic_dot S hS r).choose_spec

/-- **CL Lemma 4.1 under (BB_w)**, for the normalized left adjunctions. -/
theorem BBw.cyclic_dot_leftAdjN [∀ a b : B, IsIdempotentComplete (a ⟶ b)] (hS : S.BBw)
    (r : ℤ) :
    Bicategory.conjugateEquiv (S.grAdj r) (S.grAdj r) (S.grDot r) =
      (Bicategory.conjugateEquiv (hS.leftAdjN r) (hS.leftAdjN r)).symm (S.grDot r) :=
  (hS.leftAdjN_spec r).2.2.2.2

/-- **CL Lemma 4.2 under (BB_w)** (cyclicity of the crossing, eq. (4.10)), for the normalized
left adjunctions: the right mate of the crossing on `E E 1_n` under the composite of the right
adjunctions equals its left mate under the composite of the normalized left adjunctions. -/
theorem BBw.cyclic_cross [∀ a b : B, IsIdempotentComplete (a ⟶ b)] (hS : S.BBw) (r : ℤ) :
    Bicategory.conjugateEquiv ((S.grAdj r).comp (S.grAdj (r + 1)))
        ((S.grAdj r).comp (S.grAdj (r + 1))) (S.grCross r) =
      (Bicategory.conjugateEquiv ((hS.leftAdjN (r + 1)).comp (hS.leftAdjN r))
        ((hS.leftAdjN (r + 1)).comp (hS.leftAdjN r))).symm (S.grCross r) :=
  S.cyclic_cross_of_cyclic_dot hS r _ _ (hS.leftAdjN_spec r).1 (hS.leftAdjN_spec r).2.1
    (hS.leftAdjN_spec (r + 1)).1 (hS.leftAdjN_spec (r + 1)).2.1
    (S.cyclic_dotN_of_cyclic_dot _ (hS.cyclic_dot_leftAdjN r))
    (S.cyclic_dotN_of_cyclic_dot _ (hS.cyclic_dot_leftAdjN (r + 1)))

end StrongSl2

end Cross

end Categorification.TwoRep

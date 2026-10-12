/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqAdjunction

/-!
# Opposite adjunction at a finite dotted-unit boundary

This is the boundary form of the argument for Brundan, Theorem 4.3. The composite
`E ≫ R` is decomposed by the original dotted units and their inverse coefficients.
There is no lower edge, lower crossing, or auxiliary zero category. The cap is the
coefficient in degree `n-1` with positive sign; in degree zero it is zero.

The dotted-unit components alone detect equality. Applied to the upper cap-swap
calculation, this gives the cap pitchfork and upward triangle with the prescribed
upper `cupL`. Right-mate reflection preserves the same coefficient data and gives
the downward triangle. Degree zero follows from the original right-adjunction
triangle and the zero identity forced by the empty finite decomposition.

`oppositeAdjunction` needs only the upper local inversion, its square-zero crossing,
and finite inverse coefficients, not a braid involving a nonexistent lower edge.
Its concrete application is the absent-colour cyclotomic adjunction.
-/

noncomputable section
namespace Categorification.TwoRep
open CategoryTheory CategoryTheory.Bicategory
universe w v u
namespace RouqBoundary
variable {C : Type u} [Bicategory.{w,v} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [AdditiveWhiskering C]
  {a b c : C} {E : a ⟶ b} {R : b ⟶ a} {E' : b ⟶ c} {R' : c ⟶ b}
  {A : E ⊣ R} {B : E' ⊣ R'} {x : E ⟶ E} {x' : E' ⟶ E'}
  {τ : E ≫ E' ⟶ E ≫ E'} {h : ℤ}

def cupD (A : E ⊣ R) (x : E ⟶ E) (j : ℕ) : 𝟙 a ⟶ E ≫ R :=
  A.unit ≫ powComp x j ▷ R

/-- The actual finite dotted-unit decomposition, without a lower edge. -/
structure Coefficients (A : E ⊣ R) (x : E ⟶ E) (n : ℕ) where
  coeff : ℕ → (E ≫ R ⟶ 𝟙 a)
  total : ∑ j ∈ Finset.range n, coeff j ≫ cupD A x j = 𝟙 (E ≫ R)
  entry : ∀ j l, j < n → l < n → cupD A x j ≫ coeff l =
    if j = l then 𝟙 (𝟙 a) else 0

variable {n : ℕ} (D : Coefficients A x n)

def cap : E ≫ R ⟶ 𝟙 a := if 0 < n then D.coeff (n-1) else 0

omit [AdditiveWhiskering C] in
theorem cup_cap (hn : 0 < n) {j : ℕ} (hj : j < n) :
    cupD A x j ≫ cap D = if j = n-1 then 𝟙 (𝟙 a) else 0 := by
  rw [cap, ite_eq_left hn]
  exact D.entry j (n-1) hj (by omega)

include D in
theorem hom_ext {F T : a ⟶ c} (f g : (E ≫ R) ≫ F ⟶ T)
    (he : ∀ j, j < n → cupD A x j ▷ F ≫ f = cupD A x j ▷ F ≫ g) : f = g := by
  have ht := congrArg (fun z => z ▷ F) D.total
  have hs : (∑ j ∈ Finset.range n, D.coeff j ≫ cupD A x j) ▷ F =
      ∑ j ∈ Finset.range n, (D.coeff j ≫ cupD A x j) ▷ F :=
    map_sum (AdditiveWhiskering.whiskerRightAddHom _ _ F) _ _
  rw [hs, id_whiskerRight] at ht
  calc f = (∑ j ∈ Finset.range n, (D.coeff j ≫ cupD A x j) ▷ F) ≫ f := by rw [ht, Category.id_comp]
       _ = (∑ j ∈ Finset.range n, (D.coeff j ≫ cupD A x j) ▷ F) ≫ g := by
         simp only [Preadditive.sum_comp, comp_whiskerRight, Category.assoc]
         apply Finset.sum_congr rfl
         intro j hj
         rw [he j (Finset.mem_range.mp hj)]
       _ = g := by rw [ht, Category.id_comp]

variable (U : RouqLoc A B x x' τ h)

omit [AdditiveWhiskering C] in
/-- Only the original upper right adjunction is involved in this closure. -/
theorem cup_capCross (j : ℕ) :
    cupD A x j ▷ E ≫ U.capCross = (λ_ E).hom ≫
      curlEG B.unit U.capL (τ ≫ powComp x j ▷ E' ≫ τ) := by
  calc _ = (A.unit ▷ E ⊗≫
      ((powComp x j ▷ (R ≫ E)) ≫ E ◁ U.sig) ⊗≫ τ ▷ R' ⊗≫
      E ◁ U.capL ⊗≫ 𝟙 _ : 𝟙 a ≫ E ⟶ E) := by
        unfold cupD RouqLoc.capCross
        bicategory
    _ = (A.unit ▷ E ⊗≫
      (E ◁ U.sig ≫ powComp x j ▷ (E' ≫ R')) ⊗≫ τ ▷ R' ⊗≫
      E ◁ U.capL ⊗≫ 𝟙 _ : 𝟙 a ≫ E ⟶ E) := by rw [whisker_exchange]
    _ = ((A.unit ▷ E ⊗≫ E ◁ U.sig) ⊗≫ (powComp x j ▷ E' ≫ τ) ▷ R' ⊗≫
      E ◁ U.capL ⊗≫ 𝟙 _ : 𝟙 a ≫ E ⟶ E) := by bicategory
    _ = _ := by
      rw [U.unit_sig_pitchfork]
      unfold curlEG
      bicategory

/-- The absent boundary has no crossing summand to check. -/
theorem capCross_eq (hn : 0 < n) (hw : h = 2 - (n : ℤ)) (hsq : τ ≫ τ = 0) :
    U.capCross = -(cap D ▷ E ≫ (λ_ E).hom) + if n = 1 then
      (α_ E R E).hom ≫ E ◁ A.counit ≫ (ρ_ E).hom else 0 := by
  apply hom_ext D
  intro j hj
  have hcap : cupD A x j ▷ E ≫ cap D ▷ E ≫ (λ_ E).hom =
      if j = n-1 then (λ_ E).hom else 0 := by
    rw [← Category.assoc, ← comp_whiskerRight, cup_cap D hn hj]
    split_ifs
    · rw [id_whiskerRight, Category.id_comp]
    · rw [AdditiveWhiskering.zero_whiskerRight, Limits.zero_comp]
  rw [Preadditive.comp_add, Preadditive.comp_neg, hcap, cup_capCross U]
  by_cases heq : n = 1
  · have hj0 : j = 0 := by omega
    subst n
    subst j
    have hz : cupD A x 0 ▷ E ≫ (α_ E R E).hom ≫ E ◁ A.counit ≫ (ρ_ E).hom =
        (λ_ E).hom := by
      calc _ = leftZigzag A.unit A.counit ≫ (ρ_ E).hom := by
            unfold cupD leftZigzag
            simp only [powComp_zero, id_whiskerRight, Category.comp_id]
            bicategory
        _ = _ := by rw [A.left_triangle]; simp
    simp only [powComp_zero, id_whiskerRight, Category.id_comp, hsq, ite_true]
    rw [hz]
    have hc0 := (RouqSl2Generic.curlEGMap (E₁ := E) B.unit U.capL).map_zero
    change curlEG B.unit U.capL 0 = 0 at hc0
    rw [hc0, Limits.comp_zero]
    abel
  · rw [ite_eq_right heq, Limits.comp_zero, add_zero]
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · subst j
      rw [powComp_zero, id_whiskerRight, Category.id_comp, hsq,
        ite_eq_right (by omega)]
      have hc0 := (RouqSl2Generic.curlEGMap (E₁ := E) B.unit U.capL).map_zero
      change curlEG B.unit U.capL 0 = 0 at hc0
      rw [hc0, Limits.comp_zero, neg_zero]
    · rw [U.curlEG_double_dotted hsq hj0 (by omega)]
      have hiff : (j : ℤ) = 1-h ↔ j = n-1 := by omega
      simp only [hiff]
      split_ifs
      · rw [Preadditive.comp_neg, Category.comp_id]
      · simp

/-- The upper inverse and actual boundary coefficient satisfy the cap pitchfork. -/
theorem cap_pitchfork (hn : 1 < n) (hw : h = 2 - (n : ℤ)) (hsq : τ ≫ τ = 0) :
    (α_ E E' R').inv ≫ τ ▷ R' ≫ (α_ E E' R').hom ≫ E ◁ U.capL ≫ (ρ_ E).hom =
      E ◁ U.sigL ≫ (α_ E R E).inv ≫ cap D ▷ E ≫ (λ_ E).hom := by
  let p : E ≫ E' ≫ R' ⟶ E := (α_ E E' R').inv ≫ τ ▷ R' ≫
    (α_ E E' R').hom ≫ E ◁ U.capL ≫ (ρ_ E).hom
  let k : E ≫ E' ≫ R' ⟶ E := E ◁ U.sigL ≫ (α_ E R E).inv ≫ cap D ▷ E ≫ (λ_ E).hom
  change p = k
  have hc := capCross_eq D U (by omega) hw hsq
  have hu : h ≤ 0 := by omega
  apply (U.iN hu).whiskerLeft_hom_ext E
  · calc E ◁ U.sig ≫ p = (α_ E R E).inv ≫ U.capCross := by
          unfold p RouqLoc.capCross
          simp only [Iso.inv_hom_id_assoc]
      _ = -((α_ E R E).inv ≫ cap D ▷ E ≫ (λ_ E).hom) := by
          rw [hc, ite_eq_right (by omega : n ≠ 1), add_zero, Preadditive.comp_neg]
      _ = E ◁ U.sig ≫ k := by
          dsimp [k]
          rw [← whiskerLeft_comp_assoc, U.sig_sigL_of_nonpos hu,
            AdditiveWhiskering.whiskerLeft_neg, whiskerLeft_id,
            Preadditive.neg_comp, Category.id_comp]
  · intro j hj
    calc E ◁ U.cupD j ≫ p = (ρ_ E).hom ≫ curlEG (U.cupD j) U.capL τ := by
          unfold p curlEG
          bicategory
      _ = 0 := by rw [U.curlEG_cupD_zero (by omega), Limits.comp_zero]
      _ = E ◁ U.cupD j ≫ k := by
          dsimp [k]
          rw [← whiskerLeft_comp_assoc, U.cupD_sigL hu hj,
            AdditiveWhiskering.whiskerLeft_zero, Limits.zero_comp]

/-- The upward triangle at a positive-degree actual boundary. -/
theorem triangle_pos (hn : 0 < n) (hw : h = 2 - (n : ℤ)) (hsq : τ ≫ τ = 0) :
    (ρ_ E).inv ≫ E ◁ U.cupL ≫ (α_ E R E).inv ≫ cap D ▷ E ≫ (λ_ E).hom = 𝟙 E := by
  by_cases heq : n = 1
  · have hu : 0 < h := by omega
    have hs : U.cupL ≫ U.sig = 0 := U.cupL_sig hu
    have hb : U.cupL ≫ A.counit = 𝟙 (𝟙 b) := by
      simpa only [RouqLoc.capD, powComp_zero, whiskerLeft_id, Category.id_comp,
        show (h-1).toNat = 0 by omega, ite_true] using U.cupL_capD hu (n := 0) (by omega)
    let z := (ρ_ E).inv ≫ E ◁ U.cupL ≫ (α_ E R E).inv ≫ cap D ▷ E ≫ (λ_ E).hom
    change z = 𝟙 E
    have hz : (ρ_ E).inv ≫ E ◁ U.cupL ≫ (α_ E R E).inv ≫ U.capCross = 0 := by
      unfold RouqLoc.capCross
      rw [Iso.inv_hom_id_assoc, ← whiskerLeft_comp_assoc, hs,
        AdditiveWhiskering.whiskerLeft_zero, Limits.zero_comp, Limits.comp_zero]
    have he : 0 = -z + 𝟙 E := by
      calc 0 = (ρ_ E).inv ≫ E ◁ U.cupL ≫ (α_ E R E).inv ≫ U.capCross := hz.symm
        _ = -z + 𝟙 E := by
          rw [capCross_eq D U hn hw hsq, ite_eq_left heq]
          simp only [Preadditive.comp_add, Preadditive.comp_neg]
          change -z + (ρ_ E).inv ≫ E ◁ U.cupL ≫ (α_ E R E).inv ≫
            (α_ E R E).hom ≫ E ◁ A.counit ≫ (ρ_ E).hom = -z + 𝟙 E
          rw [Iso.inv_hom_id_assoc, ← whiskerLeft_comp_assoc, hb, whiskerLeft_id,
            Category.id_comp, Iso.inv_hom_id]
    exact (eq_of_sub_eq_zero (by
      simpa only [sub_eq_add_neg, add_comm] using he.symm) : 𝟙 E = z).symm
  · have hu : h ≤ 0 := by omega
    have hp := cap_pitchfork D U (by omega) hw hsq
    calc _ = (ρ_ E).inv ≫ E ◁ U.cupD (-h).toNat ≫
        (E ◁ U.sigL ≫ (α_ E R E).inv ≫ cap D ▷ E ≫ (λ_ E).hom) := by
          rw [U.cupL_of_nonpos hu]
          bicategory
      _ = curlEG (U.cupD (-h).toNat) U.capL τ := by rw [← hp]; rfl
      _ = 𝟙 E := U.curlEG_cupD_self hu

include D in
/-- The zero-degree decomposition forces zero identity on the original induction. -/
theorem id_eq_zero (hn : n = 0) : 𝟙 E = 0 := by
  have ht : 𝟙 (E ≫ R) = 0 := by simpa only [hn, Finset.sum_range_zero] using D.total.symm
  have hu : A.unit = 0 := by
    calc A.unit = A.unit ≫ 𝟙 (E ≫ R) := (Category.comp_id _).symm
         _ = 0 := by rw [ht, Limits.comp_zero]
  have hz := A.left_triangle
  rw [leftZigzag_eq, hu, AdditiveWhiskering.zero_whiskerRight, Limits.zero_comp] at hz
  have hz' := congrArg (fun z => (λ_ E).inv ≫ z ≫ (ρ_ E).hom) hz
  simpa only [Limits.comp_zero, Limits.zero_comp, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id] using hz'.symm

/-- The upward triangle includes the actual zero-degree case. -/
theorem triangle (hw : h = 2 - (n : ℤ)) (hsq : τ ≫ τ = 0) :
    (ρ_ E).inv ≫ E ◁ U.cupL ≫ (α_ E R E).inv ≫ cap D ▷ E ≫ (λ_ E).hom = 𝟙 E := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · rw [cap, ite_eq_right (by omega), AdditiveWhiskering.zero_whiskerRight,
      Limits.zero_comp, Limits.comp_zero, Limits.comp_zero, Limits.comp_zero,
      id_eq_zero D hn]
  · exact triangle_pos D U hn hw hsq

omit [AdditiveWhiskering C] [∀ a b : C, Preadditive (a ⟶ b)] in
theorem mirror_cup (j : ℕ) :
    cupD (HOp.adjunction A) (conjugateEquiv A A x) j = cupD A x j := by
  change A.unit ≫ E ◁ powComp (conjugateEquiv A A x) j = _
  rw [← RouqSl2Generic.rightMate_pow, unit_whiskerLeft_conjugateEquiv]
  rfl

/-- Reflection preserves the actual inverse coefficients, not just their dimensions. -/
def mirror : Coefficients (HOp.adjunction A) (conjugateEquiv A A x) n where
  coeff := D.coeff
  total := by
    change (∑ j ∈ Finset.range n, D.coeff j ≫
      (cupD (C := HOp C) (HOp.adjunction A) (conjugateEquiv A A x) j : 𝟙 a ⟶ E ≫ R)) = 𝟙 (E ≫ R)
    simpa only [mirror_cup] using D.total
  entry j l hj hl := by
    change (cupD (C := HOp C) (HOp.adjunction A) (conjugateEquiv A A x) j :
      𝟙 a ⟶ E ≫ R) ≫ D.coeff l =
      if j = l then 𝟙 (𝟙 a) else 0
    simpa only [mirror_cup] using D.entry j l hj hl

theorem rightZigzag_boundary (hw : h = 2 - (n : ℤ)) (hsq : τ ≫ τ = 0) :
    rightZigzag U.cupL (cap D) = (ρ_ E).hom ≫ (λ_ E).inv := by
  have ht := triangle D U hw hsq
  have he := congrArg (fun z => (ρ_ E).hom ≫ z ≫ (λ_ E).inv) ht
  rw [rightZigzag_eq]
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
    Category.comp_id, Category.id_comp] using he

/-- The downward triangle follows by reflecting the same finite coefficient proof. -/
def oppositeAdjunction (hw : h = 2 - (n : ℤ)) (hsq : τ ≫ τ = 0) : R ⊣ E where
  unit := U.cupL
  counit := cap D
  right_triangle := rightZigzag_boundary D U hw hsq
  left_triangle := by
    let Dm : Coefficients (HOp.adjunction A) U.dotD₁ n := mirror D
    have ht : rightZigzag (B := HOp C) (f := HOp.op1 E) (g := HOp.op1 R)
        U.mirror.cupL (cap Dm) = (ρ_ (HOp.op1 R)).hom ≫ (λ_ (HOp.op1 R)).inv :=
      rightZigzag_boundary Dm U.mirror hw (U.mirror_square hsq)
    have hc : cap Dm = cap D := rfl
    rw [rightZigzag_eq, U.mirror_cupL, hc] at ht
    rw [leftZigzag_eq]
    exact ht

end RouqBoundary
end Categorification.TwoRep

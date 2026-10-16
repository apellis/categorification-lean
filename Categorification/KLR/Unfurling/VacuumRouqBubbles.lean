/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.VacuumLabelLocDual
import Categorification.KLR.Unfurling.VacuumMixedDual

/-!
# The bubbles of Rouquier's data under an additive functor

B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, proof of the
theorem with label `nondegenerate`. Let `L` be Rouquier's data (`RouqLoc`, J. Brundan, *On the
definition of Kac–Moody 2-category*, arXiv:1501.00350v1, Definition 1.1) of a colour at a weight
`h`, in `LinearCat k` over a field, and let `G` be an additive functor from the endomorphisms of
the middle object to a `k`-linear category (for instance evaluation at an object `V` of the middle
category, or at one block of it). The bubbles `RouqLoc.cw`, `RouqLoc.ccw` of `L` are the images of
the bubbles of the Kac–Moody 2-category (`map_cw`, `map_ccw`). This file evaluates their images
under `G` by `ev_comp_eq_lwSeq` and `ev_comp_eq_lwSeq_dual`, whose hypotheses on the crossing, the
caps and the cups are supplied by `L`:

* `h ≤ 0` (`cw_app_eq_lwSeq`): the clockwise bubble with `k` dots is the cup, `k` dots on
  `F E` and the leftward cap. The rightward crossing satisfies the dot slide
  (`RouqLoc.sig_dot_sub`), kills the leftward cap if `h < 0` (`RouqLoc.sig_capL`) and maps it to
  the cap if `h = 0`; the bubbles in degrees below `-h` are `δ` (Brundan (3.7)).
* `h ≥ 0` (`ccw_app_eq_lwSeq`): the counterclockwise bubble with `k` dots is the leftward cup,
  `k` dots on `E F` and the cap, and the crossing enters with a sign.

The labels (the decomposition of `G (F E)` or `G (E F)`, and the chains of the other sign)
remain hypotheses; `VacuumLabelLoc` and `VacuumLabelLocDual` provide them from the Rouquier
data of the labels.
-/

noncomputable section

namespace Categorification.KLR.Unfurling

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits TwoRep PowerSeries

universe w v u

variable {k : Type w} [Field k] {C₁ C₂ C₃ : LinearCat.{w, v, u} k}
  {E₁ : C₁ ⟶ C₂} {R₁ : C₂ ⟶ C₁} {E₂ : C₂ ⟶ C₃} {R₂ : C₃ ⟶ C₂}
  {adj₁ : E₁ ⊣ R₁} {adj₂ : E₂ ⊣ R₂} {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂}
  {τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂} {h : ℤ} (L : RouqLoc adj₁ adj₂ x₁ x₂ τ h)
  {D : Type*} [Category D] [Preadditive D] [Linear k D] (G : (C₂ ⟶ C₂) ⥤ D) [G.Additive]

/-- The dot on `G (F E)`. -/
abbrev dotQ : End (G.obj (E₂ ≫ R₂)) := G.map (x₂ ▷ R₂)

/-- The dot on `G (E F)`. -/
abbrev dotP : End (G.obj (R₁ ≫ E₁)) := G.map (R₁ ◁ x₁)

omit [Preadditive D] [Linear k D] [G.Additive] in
theorem map_powComp {f : C₂ ⟶ C₂} (x : f ⟶ f) (n : ℕ) :
    G.map (powComp x n) = @HPow.hPow (End (G.obj f)) ℕ (End (G.obj f)) _ (G.map x) n := by
  induction n with
  | zero => exact G.map_id _
  | succ n ih => rw [powComp_succ, G.map_comp, ih, pow_succ', End.mul_def]

omit [Linear k D] in
/-- The dot slide under `G` (Brundan (2.3)). -/
theorem map_sig_dot_sub :
    G.map L.sig ≫ dotQ (x₂ := x₂) G - dotP (x₁ := x₁) G ≫ G.map L.sig =
      G.map adj₁.counit ≫ G.map adj₂.unit := by
  rw [← G.map_comp, ← G.map_comp, ← G.map_comp, ← G.map_sub, L.sig_dot_sub]

omit [Preadditive D] [Linear k D] [G.Additive] in
/-- The clockwise bubble under `G`. -/
theorem map_cw (m : ℕ) :
    G.map (L.cw m) = G.map adj₂.unit ≫ (dotQ (x₂ := x₂) G ^ m : End _) ≫ G.map L.capL := by
  rw [← L.cupD_capL_eq_cw, RouqLoc.cupD, RightwardCrossing.powComp_whiskerRight, G.map_comp,
    G.map_comp, map_powComp, Category.assoc]

omit [Preadditive D] [Linear k D] [G.Additive] in
/-- The counterclockwise bubble under `G`. -/
theorem map_ccw (m : ℕ) :
    G.map (L.ccw m) = G.map L.cupL ≫ (dotP (x₁ := x₁) G ^ m : End _) ≫ G.map adj₁.counit := by
  rw [← L.cupL_capD_eq_ccw, RouqLoc.capD, RightwardCrossing.whiskerLeft_powComp, G.map_comp,
    G.map_comp, map_powComp]

/-- **The clockwise bubbles of Rouquier's data under `G`, `h ≤ 0`** (Webster,
arXiv:1603.06311v3, proof of the theorem with label `nondegenerate`). Let `G (F E) = ⊕ₐ Wₐ` over
lowest weight labels `a`, with `zₐ + yₐ` the dot on `Wₐ` and `yₐ^m` killing the cup for `m ≥ hₐ`,
and for each highest weight label `b` an inverse `w_b` of `D - z_b` on `G (F E)` and a chain
`c_{b,m} : G 𝟙 → G (E F)` of length `Λ_b` (`VacuumLabelLoc`), with
`∑ₐ hₐ = -h + ∑_b Λ_b > 0`. Then the clockwise bubble with `k` dots acts under `G` by
`[t^{k+1+h}] ∏_b (1 - z_b t)^{Λ_b} ∏ₐ (1 - zₐ t)^{-hₐ}`. -/
theorem cw_app_eq_lwSeq (hh : h ≤ 0) {R : Type*} [CommRing R] [Algebra k R]
    (ev : End (G.obj (𝟙 C₂)) →ₐ[k] R)
    {A : Type*} [Fintype A] {Wa : A → D}
    (π : ∀ a, G.obj (E₂ ≫ R₂) ⟶ Wa a) (ι : ∀ a, Wa a ⟶ G.obj (E₂ ≫ R₂))
    (νa : ∀ a, G.obj (𝟙 C₂) ⟶ Wa a) (y : ∀ a, End (Wa a)) (za : A → k) (hp : A → ℕ)
    (hπι : ∑ a, π a ≫ ι a = 𝟙 _)
    (hc : ∀ n a, (G.map adj₂.unit ≫ (dotQ (x₂ := x₂) G ^ n : End _)) ≫ π a =
      νa a ≫ ((algebraMap k (End (Wa a)) (za a) + y a) ^ n : End (Wa a)))
    (hν : ∀ a m, hp a ≤ m → νa a ≫ (y a ^ m : End (Wa a)) = 0)
    {B : Type*} [Fintype B] [DecidableEq B] (zb : B → k) (hzb : Function.Injective zb)
    (Λ : B → ℕ) (w : B → End (G.obj (E₂ ≫ R₂)))
    (hw₁ : ∀ b, (dotQ (x₂ := x₂) G - algebraMap k _ (zb b)) * w b = 1)
    (hw₂ : ∀ b, w b * (dotQ (x₂ := x₂) G - algebraMap k _ (zb b)) = 1)
    (c : B → ℕ → (G.obj (𝟙 C₂) ⟶ G.obj (R₁ ≫ E₁))) (β : B → ℕ → ℕ → k)
    (hcN : ∀ b m, m < Λ b →
      c b m ≫ (dotP (x₁ := x₁) G - algebraMap k (End (G.obj (R₁ ≫ E₁))) (zb b) :
        End _) = ∑ j ∈ Finset.range m, β b m j • c b j)
    (hβ : ∀ b m, m + 1 < Λ b → β b (m + 1) m ≠ 0)
    (hcκ : ∀ b m, m < Λ b → c b m ≫ G.map adj₁.counit = if m = 0 then 𝟙 _ else 0)
    (hN : ∑ a, hp a = (-h).toNat + ∑ b, Λ b) (hNpos : 0 < ∑ a, hp a) (m : ℕ) :
    ev (G.map (L.cw m)) = algebraMap k R (lwSeq (-h).toNat
      ((∏ b, (1 - PowerSeries.C (zb b) * X) ^ Λ b) *
        ((∏ a, oneSubUnit (za a) ^ (-(hp a : ℤ)) : (PowerSeries k)ˣ) : PowerSeries k)) m) := by
  rw [map_cw]
  refine ev_comp_eq_lwSeq ev π ι νa y za hp (G.map adj₂.unit) (G.map L.capL)
    (dotQ G) hπι hc hν zb hzb Λ w hw₁ hw₂ (G.map L.sig) (G.map adj₁.counit) (dotP G)
    (map_sig_dot_sub L G) c β hcN hβ hcκ (-h).toNat hN hNpos ?_ ?_ m
  · by_cases h0 : h = 0
    · subst h0
      simp only [neg_zero, Int.toNat_zero, ↓reduceIte]
      have h1 : L.sig ≫ L.capL = adj₁.counit := by
        rw [L.capL_of_nonneg le_rfl, Preadditive.comp_neg, ← Category.assoc,
          L.sig_sigL_of_nonpos le_rfl, Preadditive.neg_comp, Category.id_comp, neg_neg,
          Int.toNat_zero, L.capD_zero]
      have h2 := congrArg G.map h1
      rw [Functor.map_comp] at h2
      exact h2
    · have hlt : h < 0 := lt_of_le_of_ne hh h0
      simp only [show (-h).toNat ≠ 0 by omega, ↓reduceIte]
      have h1 := congrArg G.map (L.sig_capL hlt)
      rw [Functor.map_comp, Functor.map_zero] at h1
      exact h1
  · intro t ht
    refine Eq.trans (congrArg ev (map_cw L G t).symm) ?_
    by_cases htn : t + 1 = (-h).toNat
    · have : ((t : ℕ) : ℤ) = -h - 1 := by omega
      rw [this, L.cw_boundary]
      simp only [htn, ↓reduceIte]
      rw [G.map_id]
      exact ev.map_one
    · have : ((t : ℕ) : ℤ) < -h - 1 := by omega
      rw [L.cw_eq_zero_of_lt this]
      simp only [htn, ↓reduceIte]
      rw [G.map_zero]
      exact ev.map_zero

/-- **The counterclockwise bubbles of Rouquier's data under `G`, `h ≥ 0`** (Webster,
arXiv:1603.06311v3, proof of the theorem with label `nondegenerate`). Let `G (E F) = ⊕ₐ Wₐ` over
highest weight labels `a`, with `zₐ + yₐ` the dot on `Wₐ` and `yₐ^m` killing the cap for
`m ≥ hₐ`, and for each lowest weight label `b` an inverse `w_b` of `D - z_b` on `G (E F)` and a
chain `c_{b,m} : G (F E) → G 𝟙` of length `Λ_b` (`VacuumLabelLocDual`), with
`∑ₐ hₐ = h + ∑_b Λ_b > 0`. Then the counterclockwise bubble with `k` dots acts under `G` by
`[t^{k+1-h}] ∏_b (1 - z_b t)^{Λ_b} ∏ₐ (1 - zₐ t)^{-hₐ}`. -/
theorem ccw_app_eq_lwSeq (hh : 0 ≤ h) {R : Type*} [CommRing R] [Algebra k R]
    (ev : End (G.obj (𝟙 C₂)) →ₐ[k] R)
    {A : Type*} [Fintype A] {Wa : A → D}
    (π : ∀ a, Wa a ⟶ G.obj (R₁ ≫ E₁)) (ι : ∀ a, G.obj (R₁ ≫ E₁) ⟶ Wa a)
    (νa : ∀ a, Wa a ⟶ G.obj (𝟙 C₂)) (y : ∀ a, End (Wa a)) (za : A → k) (hp : A → ℕ)
    (hπι : ∑ a, ι a ≫ π a = 𝟙 _)
    (hc : ∀ n a, π a ≫ (dotP (x₁ := x₁) G ^ n : End _) ≫ G.map adj₁.counit =
      ((algebraMap k (End (Wa a)) (za a) + y a) ^ n : End (Wa a)) ≫ νa a)
    (hν : ∀ a m, hp a ≤ m → (y a ^ m : End (Wa a)) ≫ νa a = 0)
    {B : Type*} [Fintype B] [DecidableEq B] (zb : B → k) (hzb : Function.Injective zb)
    (Λ : B → ℕ) (w : B → End (G.obj (R₁ ≫ E₁)))
    (hw₁ : ∀ b, (dotP (x₁ := x₁) G - algebraMap k _ (zb b)) * w b = 1)
    (hw₂ : ∀ b, w b * (dotP (x₁ := x₁) G - algebraMap k _ (zb b)) = 1)
    (c : B → ℕ → (G.obj (E₂ ≫ R₂) ⟶ G.obj (𝟙 C₂))) (β : B → ℕ → ℕ → k)
    (hcN : ∀ b m, m < Λ b →
      (dotQ (x₂ := x₂) G - algebraMap k (End (G.obj (E₂ ≫ R₂))) (zb b) :
        End _) ≫ c b m = ∑ j ∈ Finset.range m, β b m j • c b j)
    (hβ : ∀ b m, m + 1 < Λ b → β b (m + 1) m ≠ 0)
    (hcκ : ∀ b m, m < Λ b → G.map adj₂.unit ≫ c b m = if m = 0 then 𝟙 _ else 0)
    (hN : ∑ a, hp a = h.toNat + ∑ b, Λ b) (hNpos : 0 < ∑ a, hp a) (m : ℕ) :
    ev (G.map (L.ccw m)) = algebraMap k R (lwSeq h.toNat
      ((∏ b, (1 - PowerSeries.C (zb b) * X) ^ Λ b) *
        ((∏ a, oneSubUnit (za a) ^ (-(hp a : ℤ)) : (PowerSeries k)ˣ) : PowerSeries k)) m) := by
  rw [map_ccw]
  refine ev_comp_eq_lwSeq_dual ev π ι νa y za hp (G.map L.cupL) (G.map adj₁.counit)
    (dotP G) hπι hc hν zb hzb Λ w hw₁ hw₂ (-G.map L.sig) (G.map adj₂.unit) (dotQ G) ?_
    c β hcN hβ hcκ h.toNat hN hNpos ?_ ?_ m
  · rw [Preadditive.comp_neg, Preadditive.neg_comp, sub_neg_eq_add, neg_add_eq_sub,
      map_sig_dot_sub L G]
  · by_cases h0 : h = 0
    · subst h0
      simp only [Int.toNat_zero, ↓reduceIte]
      have h1 : L.cupL ≫ L.sig = -adj₂.unit := by
        rw [L.cupL_of_nonpos le_rfl, Category.assoc, L.sigL_sig_of_nonneg le_rfl,
          Preadditive.comp_neg, Category.comp_id, neg_zero, Int.toNat_zero, L.cupD_zero]
      have h2 := congrArg G.map h1
      rw [Functor.map_comp, Functor.map_neg] at h2
      exact (Preadditive.comp_neg _ _).trans ((congrArg Neg.neg h2).trans (neg_neg _))
    · have hlt : 0 < h := lt_of_le_of_ne hh (Ne.symm h0)
      simp only [show h.toNat ≠ 0 by omega, ↓reduceIte]
      have h1 := congrArg G.map
        ((L.cupL_of_pos hlt).symm ▸ L.cupN_sig hh (n := (h - 1).toNat) (by omega))
      rw [Functor.map_comp, Functor.map_zero] at h1
      exact (Preadditive.comp_neg _ _).trans ((congrArg Neg.neg h1).trans neg_zero)
  · intro t ht
    refine Eq.trans (congrArg ev (map_ccw L G t).symm) ?_
    by_cases htn : t + 1 = h.toNat
    · have : ((t : ℕ) : ℤ) = h - 1 := by omega
      rw [this, L.ccw_boundary]
      simp only [htn, ↓reduceIte]
      rw [G.map_id]
      exact ev.map_one
    · have : ((t : ℕ) : ℤ) < h - 1 := by omega
      rw [L.ccw_eq_zero_of_lt this]
      simp only [htn, ↓reduceIte]
      rw [G.map_zero]
      exact ev.map_zero

end Categorification.KLR.Unfurling

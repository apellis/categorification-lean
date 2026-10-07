/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.DecompFE

/-!
# `β_n = -1` for `n ≤ -1` and the decompositions of CL §5.3 for `n ≤ 0`

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, §5.3, Lemma 5.4 ("A similar calculation for `n ≤ 0` using a clockwise oriented
bubble with `-n+1` dots ... then `β_n = -r_i^{-2}` for `n < 0`"), with the dots normalized to
`r_i = 1`; the mirror image of `BetaCoeff.lean`.

By `BBw.decompFE_beta`, at a weight `n = wt (q + 1) ≤ 0` there is `β` with `σ ≫ β σ' = 1_{EF1_n}`.
Closing the downward strand of `σσ' = β⁻¹` on the right, with the right cup of `E 1_{n-2}`,
`-n + 1` dots and the left cap (`capCupY`), gives `β⁻¹` on the identity side (the degree-zero
counter-clockwise bubble at the weight `n - 2` is `1`, CL (4.1)) and, by the pitchfork relations
(`capCupY_sigma_sideL`), the curl `curlEG` of `τ (x^{-n+1} E) τ` on `E 1_{n-2}`. By the nilHecke
relations (`tau_powComp_tau'`, `qpow_tau`) this curl is `-1`: curls of `τ` with fewer than `-n`
dots on the closed strand vanish by degrees (Lemma 3.1), and the remaining bubbles are those of
degree `≤ 0` at the weight `n` (CL (4.1) and `c_{-1} = 1`). Hence `β = -1`
(`BBw.beta_eq_neg_one_neg`).

## Main declarations

* generic: `curlEG` and its sliding lemmas, `qpow_tau`, `tau_powComp'`, `tau_powComp_tau'`;
* `StrongSl2.BBw.curlEG_ccupD_self`, `StrongSl2.BBw.beta_eq_neg_one_neg`;
* `StrongSl2.BBw.decompFE`: **for `n ≤ 0`, `σσ' = -1` on `EF1_n` and
  `1_{FE1_n} = -σ'σ + ∑_k ccomp_k ccup_k`**; `StrongSl2.BBw.decompEF_neg`: `σσ' = -1` for `n ≤ 0`.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

universe w v u

/-! ## Curls closing the right strand -/

section Generic

variable {C : Type u} [Bicategory.{w, v} C] {a b c : C} {Em : a ⟶ b} {Ep : b ⟶ c}
  {Rp : c ⟶ b}

/-- The curl of `w : Em ≫ Ep ⟶ Em ≫ Ep` on `Em`, closing `Ep` with the cup `u` and the cap `eps`. -/
def curlEG (u : 𝟙 b ⟶ Ep ≫ Rp) (eps : Ep ≫ Rp ⟶ 𝟙 b) (w : Em ≫ Ep ⟶ Em ≫ Ep) : Em ⟶ Em :=
  (ρ_ Em).inv ≫ Em ◁ u ≫ (α_ Em Ep Rp).inv ≫ w ▷ Rp ≫ (α_ Em Ep Rp).hom ≫ Em ◁ eps ≫
    (ρ_ Em).hom

theorem curlE_eq_curlEG (Bp : Ep ⊣ Rp) (Ap : Rp ⊣ Ep) (w : Em ≫ Ep ⟶ Em ≫ Ep) :
    curlE Bp Ap w = curlEG Bp.unit Ap.counit w := rfl

/-- Dots on the closed strand at the bottom are absorbed into the cup. -/
theorem curlEG_whiskerLeft_comp (u : 𝟙 b ⟶ Ep ≫ Rp) (eps : Ep ≫ Rp ⟶ 𝟙 b) (z : Ep ⟶ Ep)
    (w : Em ≫ Ep ⟶ Em ≫ Ep) : curlEG u eps (Em ◁ z ≫ w) = curlEG (u ≫ z ▷ Rp) eps w := by
  unfold curlEG
  bicategory

/-- The curl of dots on the closed strand is a bubble. -/
theorem curlEG_whiskerLeft (u : 𝟙 b ⟶ Ep ≫ Rp) (eps : Ep ≫ Rp ⟶ 𝟙 b) (z : Ep ⟶ Ep) :
    curlEG u eps (Em ◁ z) = (ρ_ Em).inv ≫ Em ◁ (u ≫ z ▷ Rp ≫ eps) ≫ (ρ_ Em).hom := by
  unfold curlEG
  bicategory

/-- Dots on the open strand at the bottom slide out of the curl. -/
theorem curlEG_whiskerRight_comp (u : 𝟙 b ⟶ Ep ≫ Rp) (eps : Ep ≫ Rp ⟶ 𝟙 b) (z : Em ⟶ Em)
    (w : Em ≫ Ep ⟶ Em ≫ Ep) : curlEG u eps (z ▷ Ep ≫ w) = z ≫ curlEG u eps w := by
  unfold curlEG
  calc _ = 𝟙 _ ⊗≫ (Em ◁ u ≫ z ▷ (Ep ≫ Rp)) ⊗≫ w ▷ Rp ⊗≫ Em ◁ eps ⊗≫ 𝟙 _ := by
        bicategory
    _ = 𝟙 _ ⊗≫ (z ▷ 𝟙 b ≫ Em ◁ u) ⊗≫ w ▷ Rp ⊗≫ Em ◁ eps ⊗≫ 𝟙 _ := by
        rw [whisker_exchange]
    _ = _ := by
        bicategory

/-- Dots on the open strand at the top slide out of the curl. -/
theorem curlEG_comp_whiskerRight (u : 𝟙 b ⟶ Ep ≫ Rp) (eps : Ep ≫ Rp ⟶ 𝟙 b) (z : Em ⟶ Em)
    (w : Em ≫ Ep ⟶ Em ≫ Ep) : curlEG u eps (w ≫ z ▷ Ep) = curlEG u eps w ≫ z := by
  unfold curlEG
  calc _ = 𝟙 _ ⊗≫ Em ◁ u ⊗≫ w ▷ Rp ⊗≫ (z ▷ (Ep ≫ Rp) ≫ Em ◁ eps) ⊗≫ 𝟙 _ := by
        bicategory
    _ = 𝟙 _ ⊗≫ Em ◁ u ⊗≫ w ▷ Rp ⊗≫ (Em ◁ eps ≫ z ▷ 𝟙 b) ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange]
    _ = _ := by
        bicategory

end Generic

/-! ## The nilHecke algebra, the other dot slide -/

section NilHecke

variable {D : Type*} [Category D] [Preadditive D] {X : D} (t p q : X ⟶ X)

/-- `x₂^m τ = τ x₁^m + ∑_{a<m} x₂^a x₁^{m-1-a}` from `x₂ τ - τ x₁ = 1` (diagrammatic order). -/
theorem qpow_tau (hs : q ≫ t - t ≫ p = 𝟙 X) : ∀ m : ℕ,
    powComp q m ≫ t = t ≫ powComp p m +
      ∑ a ∈ Finset.range m, powComp q a ≫ powComp p (m - 1 - a)
  | 0 => by simp
  | m + 1 => by
    have hs' : q ≫ t = t ≫ p + 𝟙 X := by rw [← hs, add_sub_cancel]
    rw [powComp_succ, Category.assoc, hs', Preadditive.comp_add, Category.comp_id,
      ← Category.assoc, qpow_tau hs m, Preadditive.add_comp, Category.assoc, ← powComp_succ,
      Preadditive.sum_comp, Finset.sum_range_succ, add_assoc]
    congr 2
    · refine Finset.sum_congr rfl fun a ha => ?_
      have ha' := Finset.mem_range.1 ha
      rw [Category.assoc, ← powComp_succ, show m - 1 - a + 1 = m + 1 - 1 - a by omega]
    · rw [show m + 1 - 1 - m = 0 by omega, powComp_zero, Category.comp_id]

/-- `τ x₁^{m+1} τ = -∑_{a ≤ m} x₂^a x₁^{m-a} τ`, from `τ² = 0` and `x₂ τ - τ x₁ = 1`. -/
theorem tau_powComp_tau' (htt : t ≫ t = 0) (hs : q ≫ t - t ≫ p = 𝟙 X) (m : ℕ) :
    t ≫ powComp p (m + 1) ≫ t =
      -∑ a ∈ Finset.range (m + 1), powComp q a ≫ powComp p (m - a) ≫ t := by
  have h := qpow_tau t p q hs (m + 1)
  have h2 : t ≫ powComp p (m + 1) = powComp q (m + 1) ≫ t -
      ∑ a ∈ Finset.range (m + 1), powComp q a ≫ powComp p (m + 1 - 1 - a) := by
    rw [h, add_sub_cancel_right]
  rw [← Category.assoc, h2, Preadditive.sub_comp, Category.assoc, htt, comp_zero, zero_sub,
    Preadditive.sum_comp]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Category.assoc, show m + 1 - 1 - a = m - a by omega]

end NilHecke

/-! ## Linearity in the graded-Hom bicategory -/

section GradedHom

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B] [GradedBicategory.ShiftCoherence B]
  [GradedBicategory.IsLinear B k]

namespace GradedHomBicat

open GradedHomCat

variable {a b c : GradedHomBicat B} {Em : a ⟶ b} {Ep : b ⟶ c} {Rp : c ⟶ b}

theorem curlEG_add (u : 𝟙 b ⟶ Ep ≫ Rp) (eps : Ep ≫ Rp ⟶ 𝟙 b) (w₁ w₂ : Em ≫ Ep ⟶ Em ≫ Ep) :
    curlEG u eps (w₁ + w₂) = curlEG u eps w₁ + curlEG u eps w₂ := by
  simp only [curlEG, add_whiskerRight, Preadditive.add_comp, Preadditive.comp_add]

theorem curlEG_zero (u : 𝟙 b ⟶ Ep ≫ Rp) (eps : Ep ≫ Rp ⟶ 𝟙 b) :
    curlEG u eps (0 : Em ≫ Ep ⟶ Em ≫ Ep) = 0 := by
  simp only [curlEG, zero_whiskerRight, zero_comp, comp_zero]

theorem curlEG_neg (u : 𝟙 b ⟶ Ep ≫ Rp) (eps : Ep ≫ Rp ⟶ 𝟙 b) (w : Em ≫ Ep ⟶ Em ≫ Ep) :
    curlEG u eps (-w) = -curlEG u eps w := by
  refine eq_neg_of_add_eq_zero_left ?_
  rw [← curlEG_add, neg_add_cancel, curlEG_zero]

theorem curlEG_sum (u : 𝟙 b ⟶ Ep ≫ Rp) (eps : Ep ≫ Rp ⟶ 𝟙 b) {ι : Type*} (s : Finset ι)
    (w : ι → (Em ≫ Ep ⟶ Em ≫ Ep)) :
    curlEG u eps (∑ i ∈ s, w i) = ∑ i ∈ s, curlEG u eps (w i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using curlEG_zero u eps
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, curlEG_add, ih]

theorem curlEG_sub (u : 𝟙 b ⟶ Ep ≫ Rp) (eps : Ep ≫ Rp ⟶ 𝟙 b) (w₁ w₂ : Em ≫ Ep ⟶ Em ≫ Ep) :
    curlEG u eps (w₁ - w₂) = curlEG u eps w₁ - curlEG u eps w₂ := by
  rw [sub_eq_add_neg, curlEG_add, curlEG_neg, ← sub_eq_add_neg]

theorem isHomogeneous_curlEG {u : 𝟙 b ⟶ Ep ≫ Rp} {eps : Ep ≫ Rp ⟶ 𝟙 b}
    {w : Em ≫ Ep ⟶ Em ≫ Ep} {du dw de : ℤ} (hu : IsHomogeneous u du)
    (hw : IsHomogeneous w dw) (he : IsHomogeneous eps de) :
    IsHomogeneous (curlEG u eps w) (du + dw + de) :=
  ((isHomogeneous_rightUnitor_inv _).comp ((isHomogeneous_whiskerLeft _ hu).comp
    ((isHomogeneous_associator_inv _ _ _).comp ((isHomogeneous_whiskerRight hw _).comp
      ((isHomogeneous_associator_hom _ _ _).comp ((isHomogeneous_whiskerLeft _ he).comp
        (isHomogeneous_rightUnitor_hom _) rfl) rfl) rfl) rfl) rfl) rfl).of_eq (by ring)

theorem capCupY_smul {Rm : b ⟶ a} (Bm : Em ⊣ Rm) (Am : Rm ⊣ Em) (y : Em ⟶ Em) (t : k)
    (f : Rm ≫ Em ⟶ Rm ≫ Em) : capCupY Bm Am y (t • f) = t • capCupY Bm Am y f := by
  simp only [capCupY, whiskerLeft_smul, Linear.smul_comp, Linear.comp_smul]

end GradedHomBicat

end GradedHom

/-! ## `β = -1` for `n ≤ -1` -/

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [GradedBicategory.ShiftCoherence B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, KrullSchmidtCat.HomFinite k (a ⟶ b)] [∀ a b : B, IsIdempotentComplete (a ⟶ b)]

namespace StrongSl2

open GradedHomBicat GradedHomCat

variable {S : StrongSl2 k B} (hS : S.BBw)

omit [∀ a b : B, KrullSchmidtCat.HomFinite k (a ⟶ b)]
  [∀ a b : B, IsIdempotentComplete (a ⟶ b)] in
theorem ccupD_zero (q : ℤ) : S.ccupD q 0 = S.grUnit (q + 1) := by
  simp [ccupD]

/-- **Curls with fewer than `-n` dots on the closed strand vanish** (by degrees). -/
theorem BBw.curlEG_ccupD_eq_zero {q : ℤ} {a : ℕ} (ha : (a : ℤ) < -S.wt (q + 1)) :
    curlEG (S.ccupD q a) (hS.leftAdjN (q + 1)).counit (S.grCross q) = 0 :=
  hS.grE_end_eq_zero (isHomogeneous_curlEG (S.isHomogeneous_ccupD q a)
    (isHomogeneous_of₂ _ _) (hS.leftAdjN_spec (q + 1)).2.1) (by omega)

omit [∀ a b : B, KrullSchmidtCat.HomFinite k (a ⟶ b)]
  [∀ a b : B, IsIdempotentComplete (a ⟶ b)] in
/-- `curl(x₂^a x₁^b τ) = x^b curl(x'^a τ)`. -/
theorem curlEG_dots_tau {q : ℤ} (A : S.grR (q + 1) ⊣ S.grE (q + 1)) (a b : ℕ) :
    curlEG (S.grUnit (q + 1)) A.counit (powComp (S.grE q ◁ S.grDotN (q + 1)) a ≫
        powComp (S.grDotN q ▷ S.grE (q + 1)) b ≫ S.grCross q) =
      powComp (S.grDotN q) b ≫ curlEG (S.ccupD q a) A.counit (S.grCross q) := by
  rw [← Category.assoc, ← powComp_whiskerRight_comm, Category.assoc, ← powComp_whiskerRight,
    curlEG_whiskerRight_comp, ← whiskerLeft_powComp, curlEG_whiskerLeft_comp]
  rfl

omit [∀ a b : B, KrullSchmidtCat.HomFinite k (a ⟶ b)]
  [∀ a b : B, IsIdempotentComplete (a ⟶ b)] in
/-- `curl(x₂^a x₁^b) = x^b (bubble with a dots)`. -/
theorem curlEG_dots {q : ℤ} (A : S.grR (q + 1) ⊣ S.grE (q + 1)) (a b : ℕ) :
    curlEG (S.grUnit (q + 1)) A.counit (powComp (S.grE q ◁ S.grDotN (q + 1)) a ≫
        powComp (S.grDotN q ▷ S.grE (q + 1)) b) =
      powComp (S.grDotN q) b ≫
        ((ρ_ (S.grE q)).inv ≫ S.grE q ◁ S.ccwBub A a ≫ (ρ_ (S.grE q)).hom) := by
  rw [← powComp_whiskerRight_comm, ← powComp_whiskerRight, curlEG_whiskerRight_comp,
    ← whiskerLeft_powComp, curlEG_whiskerLeft]
  rfl

/-- **The curl with `-n` dots on the closed strand is `1`**, at the weight `n ≤ -1`. -/
theorem BBw.curlEG_ccupD_self {q : ℤ} (hn : S.wt (q + 1) ≤ -1) :
    curlEG (S.ccupD q (-S.wt (q + 1)).toNat) (hS.leftAdjN (q + 1)).counit (S.grCross q) =
      𝟙 _ := by
  set N := (-S.wt (q + 1)).toNat with hN
  have hNn : (N : ℤ) = -S.wt (q + 1) := Int.toNat_of_nonneg (by omega)
  set A := hS.leftAdjN (q + 1)
  have hcup : S.ccupD q N = S.grUnit (q + 1) ≫ powComp (S.grDotN (q + 1)) N ▷ S.grR (q + 1) :=
    rfl
  have hz : curlEG (S.grUnit (q + 1)) A.counit (S.grCross q) = 0 := by
    rw [← ccupD_zero q]
    exact hS.curlEG_ccupD_eq_zero (by omega)
  rw [hcup, ← curlEG_whiskerLeft_comp, whiskerLeft_powComp,
    qpow_tau _ _ _ (S.grDotN_slide q), curlEG_add, curlEG_sum, ← powComp_whiskerRight,
    curlEG_comp_whiskerRight, hz, zero_comp, zero_add,
    Finset.sum_congr rfl (fun a _ => curlEG_dots A a (N - 1 - a)),
    Finset.sum_eq_single_of_mem (N - 1) (Finset.mem_range.2 (by omega))]
  · rw [show N - 1 - (N - 1) = 0 by omega, powComp_zero, Category.id_comp,
      show N - 1 = (-S.wt (q + 1)).toNat - 1 from rfl, hS.ccwBub_deg_zero' hn,
      Bicategory.whiskerLeft_id, Category.id_comp, Iso.inv_hom_id]
  · intro a ha hne
    have ha' := Finset.mem_range.1 ha
    rw [hS.ccwBub_eq_zero (by omega), whiskerLeft_zero, zero_comp, comp_zero, comp_zero]

/-- **The closed diagram for `n ≤ -1`**: the curl of `τ (x^{-n+1} E) τ` on `E 1_{n-2}` is `-1`. -/
theorem BBw.curlEG_tau_dots_tau {q : ℤ} (hn : S.wt (q + 1) ≤ -1) :
    curlEG (S.grUnit (q + 1)) (hS.leftAdjN (q + 1)).counit (S.grCross q ≫
        powComp (S.grDotN q) ((-S.wt (q + 1)).toNat + 1) ▷ S.grE (q + 1) ≫ S.grCross q) =
      -𝟙 _ := by
  set N := (-S.wt (q + 1)).toNat with hN
  have hNn : (N : ℤ) = -S.wt (q + 1) := Int.toNat_of_nonneg (by omega)
  rw [powComp_whiskerRight, tau_powComp_tau' _ _ _ (S.grCross_sq q) (S.grDotN_slide q),
    curlEG_neg, curlEG_sum, Finset.sum_congr rfl (fun a _ => curlEG_dots_tau _ a (N - a)),
    Finset.sum_range_succ, Finset.sum_eq_zero, zero_add, Nat.sub_self, powComp_zero,
    Category.id_comp, hS.curlEG_ccupD_self hn]
  intro a ha
  rw [hS.curlEG_ccupD_eq_zero (by have := Finset.mem_range.1 ha; omega), comp_zero]

/-- **CL Lemma 5.4, `β_n = -r_i^{-2}`, for `n ≤ -1`** (with normalized dots, `β = -1`): if
`σ ≫ β σ' = 1_{EF1_n}` and `E F 1_n ≠ 0`, then `β = -1`. -/
theorem BBw.beta_eq_neg_one_neg {q : ℤ} (hn : S.wt (q + 1) ≤ -1) {β : k}
    (hβ : S.grSigma q ≫ (β • hS.sideL q) = 𝟙 _)
    (hRE : ¬ IsZero (S.grR q ≫ S.grE q)) : β = -1 := by
  set N := (-S.wt (q + 1)).toNat with hN
  have hNn : (N : ℤ) = -S.wt (q + 1) := Int.toNat_of_nonneg (by omega)
  have hwq : S.wt q = S.wt (q + 1) - 2 := by have := S.wt_add_one q; omega
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [zero_smul, comp_zero] at hβ
    exact hRE ((IsZero.iff_id_eq_zero _).2 hβ.symm)
  have h1 : S.grSigma q ≫ hS.sideL q = β⁻¹ • 𝟙 _ := by
    rw [← hβ, Linear.comp_smul, smul_smul, inv_mul_cancel₀ hβ0, one_smul]
  have htr := capCupY_sigma_sideL (S.grAdj q) (hS.leftAdjN q) (S.grAdj (q + 1))
    (hS.leftAdjN (q + 1)) (S.grCross q) (powComp (S.grDotN q) (N + 1))
  rw [← grSigma_eq_mateEquiv] at htr
  change capCupY _ _ _ (S.grSigma q ≫ hS.sideL q) =
    curlEG (S.grUnit (q + 1)) (hS.leftAdjN (q + 1)).counit _ at htr
  have hbub : S.ccwBub (hS.leftAdjN q) (N + 1) = 𝟙 _ := by
    have h := BBw.ccwBub_deg_zero hS (r := q) (by omega)
    rwa [show (-S.wt q).toNat - 1 = N + 1 by omega] at h
  rw [h1, capCupY_smul, capCupY_id,
    show (S.grAdj q).unit ≫ powComp (S.grDotN q) (N + 1) ▷ S.grR q ≫ (hS.leftAdjN q).counit =
      S.ccwBub (hS.leftAdjN q) (N + 1) from rfl, hbub, id_whiskerRight, Category.id_comp,
    Iso.inv_hom_id, hS.curlEG_tau_dots_tau hn] at htr
  have hE : 𝟙 (S.grE q) ≠ 0 := by
    intro h0
    apply hRE
    refine (IsZero.iff_id_eq_zero _).2 ?_
    rw [← Bicategory.whiskerLeft_id, h0, GradedHomBicat.whiskerLeft_zero]
  have h2 : (β⁻¹ + 1) • 𝟙 (S.grE q) = 0 := by rw [add_smul, htr, one_smul, neg_add_cancel]
  have h3 : β⁻¹ = -1 := eq_neg_of_add_eq_zero_left ((smul_eq_zero.1 h2).resolve_right hE)
  rw [← inv_inv β, h3, inv_neg, inv_one]

/-- **CL relations for `n ≤ 0` with `β = -1`**: `σσ' = -1` on `EF1_n` and
`1_{FE1_n} = -σ'σ + ∑_k ccomp_k ccup_k` (KL III `eq_ident_decomp` for `n ≤ 0`). -/
theorem BBw.decompFE {q : ℤ} (hn : S.wt (q + 1) ≤ 0) :
    S.grSigma q ≫ hS.sideL q = -𝟙 _ ∧
      -(hS.sideL q ≫ S.grSigma q) +
        ∑ j ∈ Finset.range (-S.wt (q + 1)).toNat, hS.compKN q j ≫ S.ccupD q j = 𝟙 _ := by
  rcases lt_or_eq_of_le hn with hn' | hn'
  · obtain ⟨β, h1, h2⟩ := hS.decompFE_beta hn
    by_cases hRE : IsZero (S.grR q ≫ S.grE q)
    · refine ⟨hRE.eq_of_src _ _, ?_⟩
      rw [← h2, hRE.eq_of_tgt (hS.sideL q) 0, zero_comp, neg_zero, smul_zero]
    · have hβ := hS.beta_eq_neg_one_neg (by omega) h1 hRE
      subst hβ
      refine ⟨?_, ?_⟩
      · rw [← h1, Linear.comp_smul, neg_smul, one_smul, neg_neg]
      · rw [← h2, neg_smul, one_smul]
  · obtain ⟨h1, h2⟩ := hS.decompEF (q := q) (by omega)
    have hN : (S.wt (q + 1)).toNat = 0 := by omega
    have hN' : (-S.wt (q + 1)).toNat = 0 := by omega
    rw [hN, Finset.sum_range_zero, add_zero] at h2
    rw [hN', Finset.sum_range_zero, add_zero, h1, neg_neg]
    exact ⟨by rw [← h2, neg_neg], rfl⟩

end StrongSl2

end Categorification.TwoRep

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.BetaCoeffNeg

/-!
# The curl relations (CL §5.3)

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, §5.3 ("It is clear that relations (A1)–(A5) allow you to simplify clockwise
oriented curls. Less obvious is that they also allow you to simplify counter-clockwise curls"), and
the curl relations of the extended `sl₂` relations (`eq_reduction-ngeqz`, `eq_reduction-nleqz`;
KL III's `curlR`, `curlL`), with the dots normalized to `r_i = 1`.

At the object `q + 1` of weight `n`, with `E 1_{n-2} = grE q` and `E 1_n = grE (q + 1)`:

* the **left curl** `curlE` on `E 1_{n-2}` (closing `E 1_n` on the left with the right cup and the
  left cap) is `∑_{g ≤ n} x^{n-g} · (counter-clockwise bubble of degree 2g)` for `n ≥ 0`
  (`curlE_eq`) and `0` for `n < 0`;
* the **right curl** `curlG` on `E 1_n` (closing `E 1_{n-2}` on the right with the left cup and the
  right cap) is `-∑_{g ≤ -n} (clockwise bubble of degree 2g) · x^{-n-g}` for `n ≤ 0`
  (`curlG_eq`) and `0` for `n > 0`.

The proof for `n ≥ 0`: the left cap is `-σ' ∘ (n dots) ∘ (right cap)` (`sideL_comp_capD`;
Brundan's definition (1.17) of the leftward cap, arXiv:1501.00350v1), by closing both sides with
the left cup (`sideL_cap_closed`): the closed diagram is a curl with `n` dots, which is `-1`
(nilHecke). Then `σ ∘ (left cap)` is determined by the decomposition of `1_{EF1_n}` and the
Grassmannian relation (`grSigma_comp_leftCounit`), and the curl is its mate. For `n ≤ 0` the
mirror argument gives that the left cup is `(right cup with -n dots) ∘ σ'`
(`ccupD_comp_sideL_self`) and then `(left cup) ∘ σ` (`leftUnit_comp_grSigma`).

## Main declarations

* generic: `curlG_comp_whiskerRight_cap`, `sideL_cap_closed`, `capTest`, `cupTest`,
  `cupTest_sideL`, `counit_comp_bubble`;
* `StrongSl2.sideL_comp_capD`, `grSigma_comp_leftCounit`, `curlE_eq` (`n ≥ 0`);
* `StrongSl2.ccupD_comp_sideL_self`, `leftUnit_comp_grSigma`, `curlG_eq` (`n ≤ 0`).
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

universe w v u

/-! ## Generic bicategory lemmas -/

section Generic

variable {C : Type u} [Bicategory.{w, v} C] {a b c : C} {Em : a ⟶ b} {Ep : b ⟶ c}
  {Rm : b ⟶ a} {Rp : c ⟶ b}

/-- Dots on the closed strand at the top of a curl are absorbed into the cap. -/
theorem curlG_comp_whiskerRight_cap {R : b ⟶ a} {E : a ⟶ b} {E' : b ⟶ c} (u : 𝟙 b ⟶ R ≫ E)
    (eps : R ≫ E ⟶ 𝟙 b) (z : E ⟶ E) (w : E ≫ E' ⟶ E ≫ E') :
    curlG u eps (w ≫ z ▷ E') = curlG u (R ◁ z ≫ eps) w := by
  unfold curlG
  bicategory

/-- Closing the downward strand of `σ' ∘ c` with the left cup of `Ep`: the curl of `τ` with the
cap `c`. -/
theorem sideL_cap_closed (Am : Rm ⊣ Em) (Ap : Rp ⊣ Ep) (τ : Em ≫ Ep ⟶ Em ≫ Ep)
    (c : Rm ≫ Em ⟶ 𝟙 b) :
    (ρ_ Ep).inv ≫ Ep ◁ Ap.unit ≫ (α_ Ep Rp Ep).inv ≫ ((mateEquiv Am Ap).symm τ ≫ c) ▷ Ep ≫
        (λ_ Ep).hom = curlG Am.unit c τ := by
  have h := sideL_trace_aux Am Ap τ (𝟙 _)
  simp only [Bicategory.whiskerLeft_id, Category.id_comp, Category.comp_id] at h
  rw [comp_whiskerRight]
  simp only [← Category.assoc] at h ⊢
  rw [h]
  unfold curlG
  simp only [Category.assoc]

/-- The left cap tested against the left cup: `χ ↦ (E ◁ η') ≫ (χ ▷ E)`, injective. -/
def capTest (Ap : Rp ⊣ Ep) (χ : Ep ≫ Rp ⟶ 𝟙 b) : Ep ⟶ Ep :=
  (ρ_ Ep).inv ≫ Ep ◁ Ap.unit ≫ (α_ Ep Rp Ep).inv ≫ χ ▷ Ep ≫ (λ_ Ep).hom

theorem capTest_injective (Ap : Rp ⊣ Ep) : Function.Injective (capTest Ap) := by
  intro χ₁ χ₂ h
  have : Ap.homEquiv₂ χ₁ = Ap.homEquiv₂ χ₂ := by
    have e : ∀ χ, Ap.homEquiv₂ χ = capTest Ap χ ≫ (λ_ Ep).inv := fun χ => by
      rw [Adjunction.homEquiv₂_apply, capTest]; simp
    rw [e, e, h]
  exact Ap.homEquiv₂.injective this

theorem capTest_counit (Ap : Rp ⊣ Ep) : capTest Ap Ap.counit = 𝟙 Ep := by
  calc capTest Ap Ap.counit = 𝟙 _ ⊗≫ rightZigzag Ap.unit Ap.counit ⊗≫ 𝟙 _ := by
        unfold capTest rightZigzag; bicategory
    _ = 𝟙 Ep := by rw [Ap.right_triangle]; bicategory

/-- The left cup tested against the left cap: `f ↦ (E ◁ f) ≫ (ε' ▷ E)`, injective. -/
def cupTest (Am : Rm ⊣ Em) (f : 𝟙 b ⟶ Rm ≫ Em) : Em ⟶ Em :=
  (ρ_ Em).inv ≫ Em ◁ f ≫ (α_ Em Rm Em).inv ≫ Am.counit ▷ Em ≫ (λ_ Em).hom

theorem cupTest_injective (Am : Rm ⊣ Em) : Function.Injective (cupTest Am) := by
  intro f₁ f₂ h
  have : Am.homEquiv₁ f₁ = Am.homEquiv₁ f₂ := by
    have e : ∀ f, Am.homEquiv₁ f = (ρ_ Em).hom ≫ cupTest Am f := fun f => by
      rw [Adjunction.homEquiv₁_apply, cupTest]; simp
    rw [e, e, h]
  exact Am.homEquiv₁.injective this

theorem cupTest_unit (Am : Rm ⊣ Em) : cupTest Am Am.unit = 𝟙 Em := by
  calc cupTest Am Am.unit = 𝟙 _ ⊗≫ rightZigzag Am.unit Am.counit ⊗≫ 𝟙 _ := by
        unfold cupTest rightZigzag; bicategory
    _ = 𝟙 Em := by rw [Am.right_triangle]; bicategory

/-- The right cup followed by the leftward sideways crossing, tested against the left cap: a
curl on `Em`. -/
theorem cupTest_sideL (Am : Rm ⊣ Em) (Ap : Rp ⊣ Ep) (τ : Em ≫ Ep ⟶ Em ≫ Ep)
    (u : 𝟙 b ⟶ Ep ≫ Rp) :
    cupTest Am (u ≫ (mateEquiv Am Ap).symm τ) = curlEG u Ap.counit τ := by
  have h := pitchfork_sideL Am Ap τ
  calc cupTest Am (u ≫ (mateEquiv Am Ap).symm τ)
      = 𝟙 _ ⊗≫ Em ◁ u ⊗≫ (Em ◁ (mateEquiv Am Ap).symm τ ⊗≫ Am.counit ▷ Em) ⊗≫ 𝟙 _ := by
        unfold cupTest; bicategory
    _ = _ := by
        rw [h]; unfold curlEG; bicategory

/-- A bubble below a cap moves onto the target side of the upward strand. -/
theorem counit_comp_bubble {R : b ⟶ a} {E : a ⟶ b} (eps : R ≫ E ⟶ 𝟙 b) (γ : 𝟙 b ⟶ 𝟙 b) :
    eps ≫ γ = R ◁ ((ρ_ E).inv ≫ E ◁ γ ≫ (ρ_ E).hom) ≫ eps := by
  calc eps ≫ γ = 𝟙 _ ⊗≫ (eps ▷ 𝟙 b ≫ 𝟙 b ◁ γ) ⊗≫ 𝟙 _ := by
        bicategory
    _ = 𝟙 _ ⊗≫ ((R ≫ E) ◁ γ ≫ eps ▷ 𝟙 b) ⊗≫ 𝟙 _ := by
        rw [whisker_exchange]
    _ = _ := by
        bicategory

/-- A bubble above a cup moves onto the source side of the upward strand. -/
theorem bubble_comp_unit {E : a ⟶ b} {R : b ⟶ a} (u : 𝟙 a ⟶ E ≫ R) (γ : 𝟙 a ⟶ 𝟙 a) :
    γ ≫ u = u ≫ ((λ_ E).inv ≫ γ ▷ E ≫ (λ_ E).hom) ▷ R := by
  calc γ ≫ u = 𝟙 _ ⊗≫ (γ ▷ 𝟙 a ≫ 𝟙 a ◁ u) ⊗≫ 𝟙 _ := by
        bicategory
    _ = 𝟙 _ ⊗≫ (𝟙 a ◁ u ≫ γ ▷ (E ≫ R)) ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange]
    _ = _ := by
        bicategory

/-- Closing a map `1 ⟶ E R` (on the source side of `E`) with the right cap of `E`. -/
def closeR {E : a ⟶ b} {R : b ⟶ a} (B : E ⊣ R) (f : 𝟙 a ⟶ E ≫ R) : E ⟶ E :=
  (λ_ E).inv ≫ f ▷ E ≫ (α_ E R E).hom ≫ E ◁ B.counit ≫ (ρ_ E).hom

/-- `closeR` of a bubble, the right cup and dots `z`: the bubble on the source side of `E`, then
`z`. -/
theorem closeR_bubble_unit {E : a ⟶ b} {R : b ⟶ a} (B : E ⊣ R) (γ : 𝟙 a ⟶ 𝟙 a) (z : E ⟶ E) :
    closeR B (γ ≫ B.unit ≫ z ▷ R) = ((λ_ E).inv ≫ γ ▷ E ≫ (λ_ E).hom) ≫ z := by
  calc closeR B (γ ≫ B.unit ≫ z ▷ R)
      = 𝟙 _ ⊗≫ γ ▷ E ⊗≫ B.unit ▷ E ⊗≫ (z ▷ (R ≫ E) ≫ E ◁ B.counit) ⊗≫ 𝟙 _ := by
        unfold closeR; bicategory
    _ = 𝟙 _ ⊗≫ γ ▷ E ⊗≫ B.unit ▷ E ⊗≫ (E ◁ B.counit ≫ z ▷ 𝟙 b) ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange]
    _ = 𝟙 _ ⊗≫ γ ▷ E ⊗≫ leftZigzag B.unit B.counit ⊗≫ z ▷ 𝟙 b ⊗≫ 𝟙 _ := by
        rw [leftZigzag]; bicategory
    _ = ((λ_ E).inv ≫ γ ▷ E ≫ (λ_ E).hom) ≫ z := by
        rw [B.left_triangle]; bicategory

/-- `closeR` of `η' ≫ σ` is the curl of `τ`. -/
theorem closeR_unit_sigma {E₁ : a ⟶ b} {E₂ : b ⟶ c} {R₁ : b ⟶ a} {R₂ : c ⟶ b} (B₁ : E₁ ⊣ R₁)
    (B₂ : E₂ ⊣ R₂) (u : 𝟙 b ⟶ R₁ ≫ E₁) (τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) :
    closeR B₂ (u ≫ mateEquiv B₁ B₂ τ) = curlG u B₁.counit τ := by
  have h := RightwardCrossing.pitchfork_cap B₂.unit B₂.counit τ B₁.counit B₂.left_triangle
  rw [RightwardCrossing.sigma_eq_mateEquiv] at h
  calc closeR B₂ (u ≫ mateEquiv B₁ B₂ τ)
      = 𝟙 _ ⊗≫ u ▷ E₂ ⊗≫ (mateEquiv B₁ B₂ τ ▷ E₂ ⊗≫ E₂ ◁ B₂.counit) ⊗≫ 𝟙 _ := by
        unfold closeR; bicategory
    _ = _ := by
        rw [h]; unfold curlG; bicategory

end Generic

/-! ## Whiskering sums in the graded-Hom bicategory -/

section GradedHom

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B] [GradedBicategory.ShiftCoherence B]

theorem GradedHomBicat.whiskerLeft_sum {a b c : GradedHomBicat B} (f : a ⟶ b) {g h : b ⟶ c}
    {ι : Type*} (s : Finset ι) (θ : ι → (g ⟶ h)) : f ◁ (∑ j ∈ s, θ j) = ∑ j ∈ s, f ◁ θ j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact GradedHomBicat.whiskerLeft_zero f
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, GradedHomBicat.whiskerLeft_add, ih]

end GradedHom

/-! ## The strong 2-representation -/

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [GradedBicategory.ShiftCoherence B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, KrullSchmidtCat.HomFinite k (a ⟶ b)] [∀ a b : B, IsIdempotentComplete (a ⟶ b)]

namespace StrongSl2

open GradedHomBicat GradedHomCat

variable (S : StrongSl2 k B)

theorem sideL_eq (q : ℤ) : S.sideLN q =
    (mateEquiv (S.leftAdjN q) (S.leftAdjN (q + 1))).symm (S.grCross q) := rfl

/-- **The right curl at `n = 0`** (`c_0^+` of CL (`eq_def_czeropm`)): the curl of `τ` on `E 1_0`
is `-1`. -/
theorem curlG_zero_wt {q : ℤ} (h0 : S.wt (q + 1) = 0) :
    curlG (S.leftAdjN q).unit (S.grCounit q) (S.grCross q) = -𝟙 _ := by
  obtain ⟨h1, _⟩ := S.decompEF (q := q) (by omega)
  have htr := sideL_trace (S.leftAdjN q) (S.leftAdjN (q + 1)) (S.grAdj q) (S.grAdj (q + 1))
    (S.grCross q) (powComp (S.grDotN (q + 1)) 1)
  rw [← grSigma_eq_mateEquiv] at htr
  change rtrace _ _ _ (S.sideLN q ≫ S.grSigma q) = _ at htr
  have hbub : S.cwBub (S.leftAdjN (q + 1)) 1 = 𝟙 _ := by
    have h := cwBub_deg_zero S (q := q + 1) (by rw [S.wt_add_one]; omega)
    rwa [show (S.wt (q + 1 + 1)).toNat - 1 = 1 by rw [S.wt_add_one]; omega] at h
  rw [h1, show (-𝟙 (S.grE (q + 1) ≫ S.grR (q + 1))) = (-1 : k) • 𝟙 _ by rw [neg_one_smul],
    rtrace_smul, rtrace_id, grAdj_counit, grAdj_counit,
    show (S.leftAdjN (q + 1)).unit ≫ S.grR (q + 1) ◁ powComp (S.grDotN (q + 1)) 1 ≫
      S.grCounit (q + 1) = S.cwBub (S.leftAdjN (q + 1)) 1 from rfl, hbub,
    Bicategory.whiskerLeft_id, Category.id_comp, Iso.inv_hom_id, whiskerLeft_powComp,
    tau_powComp_tau _ _ _ (S.grCross_sq q) (S.grDotN_slide_right q) 0, Finset.sum_range_one,
    powComp_zero, powComp_zero, Category.id_comp, Category.id_comp, neg_one_smul] at htr
  exact htr.symm

/-- **The curl with `n` dots on the closed strand at the top is `-1`**, at the weight `n ≥ 0`. -/
theorem curlG_tau_dots_top {q : ℤ} (hn : 0 ≤ S.wt (q + 1)) :
    curlG (S.leftAdjN q).unit (S.grCounit q)
      (S.grCross q ≫ powComp (S.grDotN q) (S.wt (q + 1)).toNat ▷ S.grE (q + 1)) = -𝟙 _ := by
  set N := (S.wt (q + 1)).toNat with hN
  have hNn : (N : ℤ) = S.wt (q + 1) := Int.toNat_of_nonneg hn
  rcases lt_or_eq_of_le hn with hn' | hn'
  · set A := S.leftAdjN q
    have hz : curlG A.unit (S.grCounit q) (S.grCross q) = 0 := by
      rw [← cupD_zero A]
      exact S.curlG_cupD_eq_zero (by omega)
    have hs := qpow_tau (S.grCross q) (S.grDotN q ▷ S.grE (q + 1)) (S.grE q ◁ S.grDotN (q + 1))
      (S.grDotN_slide q) N
    have hτ : S.grCross q ≫ powComp (S.grDotN q ▷ S.grE (q + 1)) N =
        powComp (S.grE q ◁ S.grDotN (q + 1)) N ≫ S.grCross q -
          ∑ a ∈ Finset.range N, powComp (S.grE q ◁ S.grDotN (q + 1)) a ≫
            powComp (S.grDotN q ▷ S.grE (q + 1)) (N - 1 - a) := by
      rw [hs, add_sub_cancel_right]
    rw [powComp_whiskerRight, hτ, curlG_sub, curlG_sum, ← whiskerLeft_powComp,
      curlG_whiskerLeft_comp, hz, comp_zero, zero_sub]
    have hterm : ∀ a, curlG A.unit (S.grCounit q) (powComp (S.grE q ◁ S.grDotN (q + 1)) a ≫
        powComp (S.grDotN q ▷ S.grE (q + 1)) (N - 1 - a)) =
          powComp (S.grDotN (q + 1)) a ≫ ((λ_ (S.grE (q + 1))).inv ≫
            S.cwBub A (N - 1 - a) ▷ S.grE (q + 1) ≫ (λ_ (S.grE (q + 1))).hom) := by
      intro a
      rw [← whiskerLeft_powComp, curlG_whiskerLeft_comp, ← powComp_whiskerRight,
        curlG_whiskerRight]
      rfl
    rw [Finset.sum_congr rfl (fun a _ => hterm a),
      Finset.sum_eq_single_of_mem 0 (Finset.mem_range.2 (by omega))]
    · rw [powComp_zero, Category.id_comp, Nat.sub_zero, cwBub_deg_zero S (by omega),
        id_whiskerRight, Category.id_comp, Iso.inv_hom_id]
    · intro a ha hne
      have ha' := Finset.mem_range.1 ha
      rw [S.cwBubN_eq_zero (by omega), zero_whiskerRight, zero_comp, comp_zero, comp_zero]
  · rw [show N = 0 by omega, powComp_zero, id_whiskerRight, Category.comp_id]
    exact S.curlG_zero_wt hn'.symm

/-- **The left cap for `n ≥ 0`** (Brundan, arXiv:1501.00350v1, (1.17)): the counit of the
normalized left adjunction `R_n ⊣ E 1_n` is `-σ' ∘ (n dots) ∘ (right cap)`. -/
theorem sideL_comp_capD {q : ℤ} (hn : 0 ≤ S.wt (q + 1)) :
    S.sideLN q ≫ S.capD q (S.wt (q + 1)).toNat = -(S.leftAdjN (q + 1)).counit := by
  apply capTest_injective (S.leftAdjN (q + 1))
  have hneg : capTest (S.leftAdjN (q + 1)) (-(S.leftAdjN (q + 1)).counit) =
      -capTest (S.leftAdjN (q + 1)) (S.leftAdjN (q + 1)).counit := by
    have : (-(S.leftAdjN (q + 1)).counit) ▷ S.grE (q + 1) =
        -((S.leftAdjN (q + 1)).counit ▷ S.grE (q + 1)) := by
      refine eq_neg_of_add_eq_zero_left ?_
      rw [← GradedHomBicat.add_whiskerRight, neg_add_cancel, GradedHomBicat.zero_whiskerRight]
    simp only [capTest, this, Preadditive.neg_comp, Preadditive.comp_neg]
  rw [hneg, capTest_counit, capTest, sideL_eq, sideL_cap_closed, capD,
    ← curlG_comp_whiskerRight_cap, S.curlG_tau_dots_top hn]

/-- The extended component `comp_{-1} = ∑_{g ≤ n} cap_{n-g} ∘ (fake ccw bubble of degree 2g)`. -/
def compKe (q : ℤ) : S.grR q ≫ S.grE q ⟶ 𝟙 (of (S.obj (q + 1))) :=
  ∑ g ∈ Finset.range ((S.wt (q + 1)).toNat + 1),
    S.capD q ((S.wt (q + 1)).toNat - g) ≫ S.ccwLN q (-S.wt (q + 1) - 1 + g)

/-- `cup_k ≫ comp_{-1} = 0` for `k < n` (the Grassmannian relation in degree `k + 1 ≤ n`). -/
theorem cupD_comp_compKe {q : ℤ} {j : ℕ} (hj : j < (S.wt (q + 1)).toNat) :
    S.cupD (S.leftAdjN q) j ≫ S.compKe q = 0 := by
  rw [compKe, Preadditive.comp_sum]
  set N := (S.wt (q + 1)).toNat with hN
  have hn1 : 1 ≤ S.wt (q + 1) := by omega
  have hNn : (N : ℤ) = S.wt (q + 1) := Int.toNat_of_nonneg (by omega)
  have hterm : ∀ g, S.cupD (S.leftAdjN q) j ≫ S.capD q (N - g) ≫
      S.ccwLN q (-S.wt (q + 1) - 1 + g) =
        S.ccwLN q (-S.wt (q + 1) - 1 + g) * End.of (S.cwBub (S.leftAdjN q) (j + (N - g))) := by
    intro g
    rw [← Category.assoc, cupD_comp_capD]
    rfl
  simp only [hterm]
  have hvan : ∀ g, j + (N - g) < N - 1 → S.cwBub (S.leftAdjN q) (j + (N - g)) = 0 :=
    fun g hg => S.cwBubN_eq_zero (by omega)
  have hJN : j + 2 ≤ N + 1 := by omega
  rw [← Finset.sum_range_add_sum_Ico _ hJN, Finset.sum_eq_zero (s := Finset.Ico _ _)
    (fun g hg => by rw [hvan g (by have := Finset.mem_Ico.1 hg; omega), mul_zero]), add_zero]
  have hG := S.grassmannian_cw_ccw hn1 (K := j + 1) (by omega)
  rw [ite_eq_right (by omega), ← Finset.sum_range_reflect] at hG
  rw [← hG]
  refine Finset.sum_congr rfl fun g hg => ?_
  have hg' := Finset.mem_range.1 hg
  rw [show j + 1 + 1 - 1 - g = j + 1 - g by omega, show j + 1 - (j + 1 - g) = g by omega,
    mul_comm, S.cwL_eq_cwBub hn1, show j + (N - g) = N - 1 + (j + 1 - g) by omega]

/-- **`σ ∘ (left cap)` for `n ≥ 0`**: `σ ≫ ε' = ∑_{g ≤ n} cap_{n-g} ∘ (ccw bubble of degree 2g)`. -/
theorem grSigma_comp_leftCounit {q : ℤ} (hn : 0 ≤ S.wt (q + 1)) :
    S.grSigma q ≫ (S.leftAdjN (q + 1)).counit = S.compKe q := by
  set N := (S.wt (q + 1)).toNat with hN
  have hNn : (N : ℤ) = S.wt (q + 1) := Int.toNat_of_nonneg hn
  obtain ⟨h1, h2⟩ := S.decompEF (q := q) hn
  rw [← sub_eq_zero]
  set X := S.grSigma q ≫ (S.leftAdjN (q + 1)).counit - S.compKe q with hX
  -- σ' ≫ X = 0
  have hσ'X : S.sideLN q ≫ X = 0 := by
    have hc : S.sideLN q ≫ S.compKe q = -(S.leftAdjN (q + 1)).counit := by
      rw [compKe, Preadditive.comp_sum, Finset.sum_range_succ', Finset.sum_eq_zero]
      · rw [zero_add, Nat.sub_zero, ← Category.assoc, S.sideL_comp_capD hn]
        unfold ccwLN
        rw [ccwL_fake _ _ _ (i := 0) (by omega)]
        simp [grassInv_zero]
      · intro g hg
        have hg' := Finset.mem_range.1 hg
        rw [← Category.assoc, S.eq_zero_from_ER ((S.isHomogeneous_sideLN q).comp
          (S.isHomogeneous_capD q _) rfl) (by omega), zero_comp]
    rw [hX, Preadditive.comp_sub, ← Category.assoc, h1, hc]
    simp
  -- cup_k ≫ X = 0
  have hcupX : ∀ j, j < N → S.cupD (S.leftAdjN q) j ≫ X = 0 := by
    intro j hj
    rw [hX, Preadditive.comp_sub, ← Category.assoc, S.cupD_comp_grSigma (by omega), zero_comp,
      S.cupD_comp_compKe hj, sub_zero]
  -- X = 0 by the decomposition of 1_{EF1_n}
  have : X = 𝟙 _ ≫ X := (Category.id_comp X).symm
  rw [this, ← h2, Preadditive.add_comp, Preadditive.sum_comp, Preadditive.neg_comp,
    Category.assoc, hσ'X, comp_zero, neg_zero, zero_add]
  exact Finset.sum_eq_zero fun j hj => by
    rw [Category.assoc, hcupX j (Finset.mem_range.1 hj), comp_zero]

/-- **The left curl relation for `n ≥ 0`** (KL III `curlL`, CL `eq_reduction-ngeqz`): the curl
`curlE` on `E 1_{n-2}` is `∑_{g ≤ n} x^{n-g} · (ccw bubble of degree 2g)`. -/
theorem curlE_eq {q : ℤ} (hn : 0 ≤ S.wt (q + 1)) :
    curlE (S.grAdj (q + 1)) (S.leftAdjN (q + 1)) (S.grCross q) =
      ∑ g ∈ Finset.range ((S.wt (q + 1)).toNat + 1),
        powComp (S.grDotN q) ((S.wt (q + 1)).toNat - g) ≫
          S.rightBub (S.ccwLN q (-S.wt (q + 1) - 1 + g)) := by
  have h := S.grSigma_comp_leftCounit hn
  rw [grSigma_eq_mateEquiv, sigma_comp_counit, compKe, grAdj_counit] at h
  have h' : S.grR q ◁ curlE (S.grAdj (q + 1)) (S.leftAdjN (q + 1)) (S.grCross q) ≫
      S.grCounit q = S.grR q ◁ (∑ g ∈ Finset.range ((S.wt (q + 1)).toNat + 1),
        powComp (S.grDotN q) ((S.wt (q + 1)).toNat - g) ≫
          S.rightBub (S.ccwLN q (-S.wt (q + 1) - 1 + g))) ≫ S.grCounit q := by
    rw [h, GradedHomBicat.whiskerLeft_sum, Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Bicategory.whiskerLeft_comp, Category.assoc, capD, Category.assoc, rightBub,
      ← counit_comp_bubble]
  have hinj : Function.Injective fun f : S.grE q ⟶ S.grE q => S.grR q ◁ f ≫ S.grCounit q := by
    intro f₁ f₂ hf
    have e : ∀ f : S.grE q ⟶ S.grE q, (S.grAdj q).homEquiv₁ (f ≫ (ρ_ _).inv) =
        S.grR q ◁ f ≫ S.grCounit q := fun f => by
      rw [Adjunction.homEquiv₁_apply, grAdj_counit]; bicategory
    have h2 : (S.grAdj q).homEquiv₁ (f₁ ≫ (ρ_ _).inv) =
        (S.grAdj q).homEquiv₁ (f₂ ≫ (ρ_ _).inv) := by
      rw [e, e]; exact hf
    exact (cancel_mono _).1 ((S.grAdj q).homEquiv₁.injective h2)
  exact hinj h'

/-- **The left curl vanishes for `n < 0`** (by degrees). -/
theorem curlE_eq_zero {q : ℤ} (hn : S.wt (q + 1) < 0) :
    curlE (S.grAdj (q + 1)) (S.leftAdjN (q + 1)) (S.grCross q) = 0 := by
  rw [curlE_eq_curlEG, grAdj_unit, ← ccupD_zero q]
  exact S.curlEG_ccupD_eq_zero (by omega)

/-- **The right curl vanishes for `n > 0`** (by degrees). -/
theorem curlG_eq_zero {q : ℤ} (hn : 0 < S.wt (q + 1)) :
    curlG (S.leftAdjN q).unit (S.grCounit q) (S.grCross q) = 0 := by
  rw [← cupD_zero (S.leftAdjN q)]
  exact S.curlG_cupD_eq_zero (by omega)

/-- **The left curl with `-n` dots on the closed strand is `1`**, at every weight `n ≤ 0`. -/
theorem curlEG_ccupD_self' {q : ℤ} (hn : S.wt (q + 1) ≤ 0) :
    curlEG (S.ccupD q (-S.wt (q + 1)).toNat) (S.leftAdjN (q + 1)).counit (S.grCross q) =
      𝟙 _ := by
  rcases lt_or_eq_of_le hn with hn' | hn'
  · exact S.curlEG_ccupD_self (by omega)
  obtain ⟨h1, _⟩ := S.decompFE (q := q) hn
  have hwq : S.wt q = -2 := by have := S.wt_add_one q; omega
  have htr := capCupY_sigma_sideL (S.grAdj q) (S.leftAdjN q) (S.grAdj (q + 1))
    (S.leftAdjN (q + 1)) (S.grCross q) (S.grDotN q)
  rw [← grSigma_eq_mateEquiv] at htr
  change capCupY _ _ _ (S.grSigma q ≫ S.sideLN q) =
    curlEG (S.grUnit (q + 1)) (S.leftAdjN (q + 1)).counit _ at htr
  have hτxτ : S.grCross q ≫ S.grDotN q ▷ S.grE (q + 1) ≫ S.grCross q = -S.grCross q := by
    have hs := S.grDotN_slide q
    have : S.grCross q ≫ S.grDotN q ▷ S.grE (q + 1) =
        S.grE q ◁ S.grDotN (q + 1) ≫ S.grCross q - 𝟙 _ := by rw [← hs]; abel
    rw [← Category.assoc, this, Preadditive.sub_comp, Category.assoc, S.grCross_sq,
      comp_zero, zero_sub, Category.id_comp]
  have hbub : (S.grAdj q).unit ≫ S.grDotN q ▷ S.grR q ≫ (S.leftAdjN q).counit = 𝟙 _ := by
    have h := ccwBub_deg_zero S (r := q) (by omega)
    rw [show (-S.wt q).toNat - 1 = 1 by omega] at h
    simp only [ccwBub, powComp_succ, powComp_zero, Category.id_comp] at h
    exact h
  rw [h1, show (-𝟙 (S.grR q ≫ S.grE q)) = (-1 : k) • 𝟙 _ by rw [neg_one_smul], capCupY_smul,
    capCupY_id, hbub, id_whiskerRight, Category.id_comp, Iso.inv_hom_id, hτxτ, curlEG_neg,
    neg_one_smul] at htr
  rw [show (-S.wt (q + 1)).toNat = 0 by omega, ccupD_zero]
  exact neg_inj.1 htr.symm

/-- **The left cup for `n ≤ 0`** (Brundan, arXiv:1501.00350v1, (1.18)): the unit of the normalized
left adjunction `R_{n-2} ⊣ E 1_{n-2}` is `(right cup with -n dots) ∘ σ'`. -/
theorem ccupD_comp_sideL_self {q : ℤ} (hn : S.wt (q + 1) ≤ 0) :
    S.ccupD q (-S.wt (q + 1)).toNat ≫ S.sideLN q = (S.leftAdjN q).unit := by
  apply cupTest_injective (S.leftAdjN q)
  rw [cupTest_unit, sideL_eq, cupTest_sideL, S.curlEG_ccupD_self' hn]

/-- The extended left-cup expression `∑_{g ≤ -n} (fake cw bubble of degree 2g) ∘ ccup_{-n-g}`. -/
def cupKNe (q : ℤ) : 𝟙 (of (S.obj (q + 1))) ⟶ S.grE (q + 1) ≫ S.grR (q + 1) :=
  ∑ g ∈ Finset.range ((-S.wt (q + 1)).toNat + 1),
    S.cwLN q (S.wt (q + 1) - 1 + g) ≫ S.ccupD q ((-S.wt (q + 1)).toNat - g)

/-- `ccup_{-n} ≫ ccomp_k = -(fake cw bubble of degree 2(-n-k))` for `k < -n`. -/
theorem ccupD_self_comp_compKN {q : ℤ} {j : ℕ} (hj : j < (-S.wt (q + 1)).toNat) :
    S.ccupD q (-S.wt (q + 1)).toNat ≫ S.compKN q j =
      -S.cwLN q (S.wt (q + 1) - 1 + ((-S.wt (q + 1)).toNat - j : ℕ)) := by
  rw [compKN, Preadditive.comp_sum]
  set N := (-S.wt (q + 1)).toNat with hN
  have hn1 : S.wt (q + 1) ≤ -1 := by omega
  have hNn : (N : ℤ) = -S.wt (q + 1) := Int.toNat_of_nonneg (by omega)
  set K := N - j with hK
  have hK1 : 1 ≤ K := by omega
  have hterm : ∀ g, S.ccupD q N ≫ S.ccapD (S.leftAdjN (q + 1)) (N - 1 - j - g) ≫
      S.cwLN q (S.wt (q + 1) - 1 + g) =
        S.cwLN q (S.wt (q + 1) - 1 + g) *
          End.of (S.ccwBub (S.leftAdjN (q + 1)) (N + (N - 1 - j - g))) := by
    intro g
    rw [← Category.assoc, ccupD_comp_ccapD]
    rfl
  simp only [hterm]
  have hG := S.grassmannian_ccw_cw' hn1 (K := K) (by omega)
  rw [ite_eq_right (by omega), Finset.sum_range_succ'] at hG
  rw [← Finset.sum_range_reflect]
  have hlast : S.ccwLN q (-S.wt (q + 1) - 1 + ((0 : ℕ) : ℤ)) = 1 := by
    rw [S.ccwL_eq_ccwBub hn1, Nat.add_zero, S.ccwBub_deg_zero' hn1]
    rfl
  rw [hlast, one_mul, Nat.sub_zero] at hG
  rw [eq_neg_iff_add_eq_zero, ← hG]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  rw [S.ccwL_eq_ccwBub hn1, mul_comm, show K - 1 - i = K - (i + 1) by omega,
    show N + (N - 1 - j - (K - (i + 1))) = N - 1 + (i + 1) by omega]

/-- **`(left cup) ∘ σ` for `n ≤ 0`**: `η' ≫ σ = -∑_{g ≤ -n} (cw bubble of degree 2g) ∘ ccup_{-n-g}`. -/
theorem leftUnit_comp_grSigma {q : ℤ} (hn : S.wt (q + 1) ≤ 0) :
    (S.leftAdjN q).unit ≫ S.grSigma q = -S.cupKNe q := by
  set N := (-S.wt (q + 1)).toNat with hN
  have hNn : (N : ℤ) = -S.wt (q + 1) := Int.toNat_of_nonneg (by omega)
  obtain ⟨h1, h2⟩ := S.decompFE (q := q) hn
  have hcw0 : S.cwLN q (S.wt (q + 1) - 1 + ((0 : ℕ) : ℤ)) = 1 := by
    unfold cwLN
    rw [cwL_fake _ _ _ (i := 0) (by omega)]
    simp [grassInv_zero]
  rw [← sub_eq_zero, sub_neg_eq_add]
  set Y := (S.leftAdjN q).unit ≫ S.grSigma q + S.cupKNe q with hY
  -- Y ≫ σ' = 0
  have hYσ' : Y ≫ S.sideLN q = 0 := by
    have hc : S.cupKNe q ≫ S.sideLN q = (S.leftAdjN q).unit := by
      rw [cupKNe, Preadditive.sum_comp, Finset.sum_range_succ', Finset.sum_eq_zero]
      · rw [zero_add, Nat.sub_zero, Category.assoc, S.ccupD_comp_sideL_self hn, hcw0]
        exact Category.id_comp _
      · intro g hg
        have hg' := Finset.mem_range.1 hg
        rw [Category.assoc, S.ccupD_comp_sideL (by omega), comp_zero]
    rw [hY, Preadditive.add_comp, Category.assoc, h1, hc]
    simp
  -- Y ≫ ccomp_k = 0
  have hYc : ∀ j, j < N → Y ≫ S.compKN q j = 0 := by
    intro j hj
    rw [hY, Preadditive.add_comp, Category.assoc, S.grSigma_comp_compKN, comp_zero, zero_add,
      cupKNe, Preadditive.sum_comp, Finset.sum_range_succ',
      Finset.sum_eq_single_of_mem (N - 1 - j) (Finset.mem_range.2 (by omega))]
    · rw [Category.assoc, Category.assoc, show N - (N - 1 - j + 1) = j by omega,
        S.ccupD_comp_compKN hj hj, ite_eq_left rfl, Category.comp_id, Nat.sub_zero,
        S.ccupD_self_comp_compKN hj, hcw0, show N - 1 - j + 1 = N - j by omega]
      change _ + 𝟙 _ ≫ _ = _
      rw [Category.id_comp, add_neg_cancel]
    · intro g hg hne
      have hg' := Finset.mem_range.1 hg
      rw [Category.assoc, S.ccupD_comp_compKN hj (by omega), ite_eq_right (by omega),
        comp_zero]
  have : Y = Y ≫ 𝟙 _ := (Category.comp_id Y).symm
  rw [this, ← h2, Preadditive.comp_add, Preadditive.comp_sum, Preadditive.comp_neg,
    ← Category.assoc, hYσ', zero_comp, neg_zero, zero_add]
  exact Finset.sum_eq_zero fun j hj => by
    rw [← Category.assoc, hYc j (Finset.mem_range.1 hj), zero_comp]

/-- **The right curl relation for `n ≤ 0`** (KL III `curlR`, CL `eq_reduction-nleqz`): the curl
`curlG` on `E 1_n` is `-∑_{g ≤ -n} (cw bubble of degree 2g) · x^{-n-g}`. -/
theorem curlG_eq {q : ℤ} (hn : S.wt (q + 1) ≤ 0) :
    curlG (S.leftAdjN q).unit (S.grCounit q) (S.grCross q) =
      -∑ g ∈ Finset.range ((-S.wt (q + 1)).toNat + 1),
        S.leftBub (S.cwLN q (S.wt (q + 1) - 1 + g)) ≫
          powComp (S.grDotN (q + 1)) ((-S.wt (q + 1)).toNat - g) := by
  have h := S.leftUnit_comp_grSigma hn
  rw [grSigma_eq_mateEquiv] at h
  have hc := closeR_unit_sigma (S.grAdj q) (S.grAdj (q + 1)) (S.leftAdjN q).unit (S.grCross q)
  rw [h, grAdj_counit] at hc
  rw [← hc, cupKNe]
  have hlin : ∀ f g : 𝟙 (of (S.obj (q + 1))) ⟶ S.grE (q + 1) ≫ S.grR (q + 1),
      closeR (S.grAdj (q + 1)) (f + g) =
        closeR (S.grAdj (q + 1)) f + closeR (S.grAdj (q + 1)) g := by
    intro f g
    simp only [closeR, GradedHomBicat.add_whiskerRight, Preadditive.add_comp,
      Preadditive.comp_add]
  have hzero : closeR (S.grAdj (q + 1)) 0 = 0 := by
    simp only [closeR, GradedHomBicat.zero_whiskerRight, zero_comp, comp_zero]
  have hnegc : ∀ f : 𝟙 (of (S.obj (q + 1))) ⟶ S.grE (q + 1) ≫ S.grR (q + 1),
      closeR (S.grAdj (q + 1)) (-f) = -closeR (S.grAdj (q + 1)) f := by
    intro f
    refine eq_neg_of_add_eq_zero_left ?_
    rw [← hlin, neg_add_cancel, hzero]
  have hsum : ∀ (s : Finset ℕ) (F : ℕ → (𝟙 (of (S.obj (q + 1))) ⟶ S.grE (q + 1) ≫ S.grR (q + 1))),
      closeR (S.grAdj (q + 1)) (∑ g ∈ s, F g) = ∑ g ∈ s, closeR (S.grAdj (q + 1)) (F g) := by
    intro s F
    classical
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hlin, ih]
  rw [hnegc, hsum]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [ccupD, ← grAdj_unit, closeR_bubble_unit]
  rfl

end StrongSl2

end Categorification.TwoRep

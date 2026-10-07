/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.BetaCoeff

/-!
# CL Lemma 5.4: `c_{-1} = 1` and `β_0 = -1`; the decompositions of `1_{EF1_n}` for `n ≥ 0`

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, §4.1, eq. (4.2) (`eq_defcmone`: after fixing the adjunctions, the
counter-clockwise degree-zero bubble at the weight `-1` is a scalar `c_{-1}`) and §5.3, Lemma 5.4
(`lem_coeff`), with the dots normalized to `r_i = 1`.

**`c_{-1} = 1`.** CL's proof uses the decomposition of `1_{EF1_1}` (`BBw.decompEF_pos` at `n = 1`):
`1_{EF1_1} = -σσ' + (cup ∘ cap)`. We place it between the right cup and the left cap of `E 1_{-1}`
(`capCup`): on `1` this gives the counter-clockwise bubble at the weight `-1` next to `E 1_{-1}`,
i.e. `c_{-1} · 1`; on `cup ∘ cap` it gives the two zigzags, i.e. `1` (`capCup_counit_unit`); on
`σσ'` it gives, by the pitchfork relations (`RightwardCrossing.pitchfork_cup`, `pitchfork_sideL`),
a diagram containing `τ τ = 0` (`capCup_sigma_sideL`). Hence `c_{-1} = 1` (`BBw.ccwBub_neg_one`),
as `E 1_{-1} ≠ 0` when `1_{-1} ≠ 0`.

**`β_0 = -1`.** At `n = 0`, `ζ = σ'` and `σ' β σ = 1`, `β σσ' = 1`. Closing the downward strand of
`σ'σ` on the left gives `β⁻¹ = C₀`, the curl of `τ` on `E 1_0` (`sideL_trace`, as for `n ≥ 1`);
closing the downward strand of `σσ'` on the right, with one dot (`capCupY_sigma_sideL`, `τ x τ =
-τ`), gives `β · (-C'₀) = 1` for the curl `C'₀` of `τ` on `E 1_{-2}`; capping `β σσ' = 1` with the
cap of `E 1_{-2}` (`sideL_comp_counit`, `sigma_comp_counit`) gives `β C₀ C'₀ = 1`. Hence `C'₀ = 1`
and `β = -1` (`BBw.beta_eq_neg_one_zero`). CL's proof ("Capping off the top of
(`eq_ident_decompT`) for `n = 0` ... implies that `β_0 = -r_i^2`") states `β_0 = -r_i^2`, which
contradicts the statement of the lemma (`β_n = -r_i^{-2}`) unless `r_i^4 = 1`; with
`c_0^+ = -1/(β_0 r_i)` and `c_0^+ = r_i` (both in CL's proof) the value is `-r_i^{-2}`.

With `BBw.decompEF_pos` this gives the decompositions for all `n ≥ 0` (`BBw.decompEF`).

## Main declarations

* generic: `pitchfork_sideL`, `capCup`, `capCupY`, `capCup_counit_unit`, `capCup_sigma_sideL`,
  `capCupY_sigma_sideL`, `sideL_comp_counit`, `curlE`, `sigma_comp_counit`;
* `StrongSl2.BBw.ccwBub_neg_one`: **`c_{-1} = 1`**;
* `StrongSl2.BBw.beta_eq_neg_one_zero`: **`β_0 = -1`**;
* `StrongSl2.BBw.decompEF`: **`σ'σ = -1` on `FE1_n` and `1_{EF1_n} = -σσ' + ∑_k comp_k cup_k` for
  `n ≥ 0`**.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

universe w v u

section Generic

variable {C : Type u} [Bicategory.{w, v} C] {a b c : C} {Em : a ⟶ b} {Ep : b ⟶ c}
  {Rm : b ⟶ a} {Rp : c ⟶ b}

/-- **Pitchfork for the leftward sideways crossing**: `(ε'_μ E_μ) ∘ (E_μ σ'_μ) =
(E_μ ε'_{μ+2}) ∘ (τ_μ R_{μ+2})`. Only the zigzag identity of `Am : Rm ⊣ Em` is used. -/
theorem pitchfork_sideL (Am : Rm ⊣ Em) (Ap : Rp ⊣ Ep) (τ : Em ≫ Ep ⟶ Em ≫ Ep) :
    Em ◁ (mateEquiv Am Ap).symm τ ⊗≫ Am.counit ▷ Em =
      𝟙 _ ⊗≫ τ ▷ Rp ⊗≫ Em ◁ Ap.counit ⊗≫ 𝟙 _ := by
  calc _ = 𝟙 _ ⊗≫ Em ◁ Am.unit ▷ (Ep ≫ Rp) ⊗≫ (Em ≫ Rm) ◁ (τ ▷ Rp) ⊗≫
          ((Em ≫ Rm) ◁ (Em ◁ Ap.counit) ≫ Am.counit ▷ (Em ≫ 𝟙 b)) ⊗≫ 𝟙 _ := by
        rw [mateEquiv_symm_apply']; bicategory
    _ = 𝟙 _ ⊗≫ Em ◁ Am.unit ▷ (Ep ≫ Rp) ⊗≫
          ((Em ≫ Rm) ◁ (τ ▷ Rp) ≫ Am.counit ▷ ((Em ≫ Ep) ≫ Rp)) ⊗≫ Em ◁ Ap.counit ⊗≫ 𝟙 _ := by
        rw [whisker_exchange]; bicategory
    _ = 𝟙 _ ⊗≫ rightZigzag Am.unit Am.counit ▷ (Ep ≫ Rp) ⊗≫ τ ▷ Rp ⊗≫ Em ◁ Ap.counit ⊗≫
          𝟙 _ := by
        rw [whisker_exchange, rightZigzag]; bicategory
    _ = _ := by
        rw [Am.right_triangle]; bicategory

/-- An endomorphism `f` of `R E` placed between the right cup and the left cap of `E`. -/
def capCup (Bm : Em ⊣ Rm) (Am : Rm ⊣ Em) (f : Rm ≫ Em ⟶ Rm ≫ Em) : Em ⟶ Em :=
  (λ_ Em).inv ≫ Bm.unit ▷ Em ≫ (α_ Em Rm Em).hom ≫ Em ◁ f ≫ (α_ Em Rm Em).inv ≫
    Am.counit ▷ Em ≫ (λ_ Em).hom

theorem capCup_id (Bm : Em ⊣ Rm) (Am : Rm ⊣ Em) :
    capCup Bm Am (𝟙 _) = (λ_ Em).inv ≫ (Bm.unit ≫ Am.counit) ▷ Em ≫ (λ_ Em).hom := by
  unfold capCup
  bicategory

/-- The cup–cap term: the two zigzags. -/
theorem capCup_counit_unit (Bm : Em ⊣ Rm) (Am : Rm ⊣ Em) :
    capCup Bm Am (Bm.counit ≫ Am.unit) = 𝟙 Em := by
  calc capCup Bm Am (Bm.counit ≫ Am.unit)
      = 𝟙 _ ⊗≫ leftZigzag Bm.unit Bm.counit ⊗≫ rightZigzag Am.unit Am.counit ⊗≫ 𝟙 _ := by
        unfold capCup leftZigzag rightZigzag; bicategory
    _ = 𝟙 Em := by
        rw [Bm.left_triangle, Am.right_triangle]; bicategory

/-- The double sideways crossing between the right cup and the left cap: a diagram containing
`τ τ`. -/
theorem capCup_sigma_sideL (Bm : Em ⊣ Rm) (Am : Rm ⊣ Em) (Bp : Ep ⊣ Rp) (Ap : Rp ⊣ Ep)
    (τ : Em ≫ Ep ⟶ Em ≫ Ep) :
    capCup Bm Am (mateEquiv Bm Bp τ ≫ (mateEquiv Am Ap).symm τ) =
      (ρ_ Em).inv ≫ Em ◁ Bp.unit ≫ (α_ Em Ep Rp).inv ≫ (τ ≫ τ) ▷ Rp ≫ (α_ Em Ep Rp).hom ≫
        Em ◁ Ap.counit ≫ (ρ_ Em).hom := by
  have h1 := RightwardCrossing.pitchfork_cup Bm.unit Bm.counit Bp.unit τ Bm.left_triangle
  have h2 := pitchfork_sideL Am Ap τ
  rw [RightwardCrossing.sigma_eq_mateEquiv] at h1
  calc capCup Bm Am (mateEquiv Bm Bp τ ≫ (mateEquiv Am Ap).symm τ)
      = 𝟙 _ ⊗≫ (Bm.unit ▷ Em ⊗≫ Em ◁ mateEquiv Bm Bp τ) ⊗≫
          (Em ◁ (mateEquiv Am Ap).symm τ ⊗≫ Am.counit ▷ Em) ⊗≫ 𝟙 _ := by
        unfold capCup; bicategory
    _ = _ := by
        rw [h1, h2]; bicategory

/-- `capCup` with `y` on the upward strand of the right cup. -/
def capCupY (Bm : Em ⊣ Rm) (Am : Rm ⊣ Em) (y : Em ⟶ Em) (f : Rm ≫ Em ⟶ Rm ≫ Em) : Em ⟶ Em :=
  (λ_ Em).inv ≫ (Bm.unit ≫ y ▷ Rm) ▷ Em ≫ (α_ Em Rm Em).hom ≫ Em ◁ f ≫ (α_ Em Rm Em).inv ≫
    Am.counit ▷ Em ≫ (λ_ Em).hom

theorem capCupY_id (Bm : Em ⊣ Rm) (Am : Rm ⊣ Em) (y : Em ⟶ Em) :
    capCupY Bm Am y (𝟙 _) =
      (λ_ Em).inv ≫ (Bm.unit ≫ y ▷ Rm ≫ Am.counit) ▷ Em ≫ (λ_ Em).hom := by
  unfold capCupY
  bicategory

/-- The double sideways crossing between the right cup with `y` and the left cap: `τ (y E) τ`. -/
theorem capCupY_sigma_sideL (Bm : Em ⊣ Rm) (Am : Rm ⊣ Em) (Bp : Ep ⊣ Rp) (Ap : Rp ⊣ Ep)
    (τ : Em ≫ Ep ⟶ Em ≫ Ep) (y : Em ⟶ Em) :
    capCupY Bm Am y (mateEquiv Bm Bp τ ≫ (mateEquiv Am Ap).symm τ) =
      (ρ_ Em).inv ≫ Em ◁ Bp.unit ≫ (α_ Em Ep Rp).inv ≫ (τ ≫ y ▷ Ep ≫ τ) ▷ Rp ≫
        (α_ Em Ep Rp).hom ≫ Em ◁ Ap.counit ≫ (ρ_ Em).hom := by
  have h1 := RightwardCrossing.pitchfork_cup Bm.unit Bm.counit Bp.unit τ Bm.left_triangle
  have h2 := pitchfork_sideL Am Ap τ
  rw [RightwardCrossing.sigma_eq_mateEquiv] at h1
  calc capCupY Bm Am y (mateEquiv Bm Bp τ ≫ (mateEquiv Am Ap).symm τ)
      = 𝟙 _ ⊗≫ Bm.unit ▷ Em ⊗≫ (y ▷ (Rm ≫ Em) ≫ Em ◁ mateEquiv Bm Bp τ) ⊗≫
          Em ◁ (mateEquiv Am Ap).symm τ ⊗≫ Am.counit ▷ Em ⊗≫ 𝟙 _ := by
        unfold capCupY; bicategory
    _ = 𝟙 _ ⊗≫ (Bm.unit ▷ Em ⊗≫ Em ◁ mateEquiv Bm Bp τ) ⊗≫ y ▷ (Ep ≫ Rp) ⊗≫
          (Em ◁ (mateEquiv Am Ap).symm τ ⊗≫ Am.counit ▷ Em) ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange]; bicategory
    _ = _ := by
        rw [h1, h2]; bicategory

/-- Capping the leftward sideways crossing with the right cap gives a curl on `Ep`. -/
theorem sideL_comp_counit (Am : Rm ⊣ Em) (Ap : Rp ⊣ Ep) (Bm : Em ⊣ Rm)
    (τ : Em ≫ Ep ⟶ Em ≫ Ep) :
    (mateEquiv Am Ap).symm τ ≫ Bm.counit = curlG Am.unit Bm.counit τ ▷ Rp ≫ Ap.counit := by
  calc _ = 𝟙 _ ⊗≫ Am.unit ▷ (Ep ≫ Rp) ⊗≫ Rm ◁ τ ▷ Rp ⊗≫
          ((Rm ≫ Em) ◁ Ap.counit ≫ Bm.counit ▷ 𝟙 b) ⊗≫ 𝟙 _ := by
        rw [mateEquiv_symm_apply']; bicategory
    _ = 𝟙 _ ⊗≫ Am.unit ▷ (Ep ≫ Rp) ⊗≫ Rm ◁ τ ▷ Rp ⊗≫
          (Bm.counit ▷ (Ep ≫ Rp) ≫ 𝟙 b ◁ Ap.counit) ⊗≫ 𝟙 _ := by
        rw [whisker_exchange]
    _ = _ := by
        unfold curlG; bicategory

/-- The curl on `Em` closing `Ep` on the right with the right cup and the left cap. -/
def curlE (Bp : Ep ⊣ Rp) (Ap : Rp ⊣ Ep) (w : Em ≫ Ep ⟶ Em ≫ Ep) : Em ⟶ Em :=
  (ρ_ Em).inv ≫ Em ◁ Bp.unit ≫ (α_ Em Ep Rp).inv ≫ w ▷ Rp ≫ (α_ Em Ep Rp).hom ≫
    Em ◁ Ap.counit ≫ (ρ_ Em).hom

/-- Capping the rightward sideways crossing with the left cap gives a curl on `Em`. -/
theorem sigma_comp_counit (Bm : Em ⊣ Rm) (Bp : Ep ⊣ Rp) (Ap : Rp ⊣ Ep)
    (τ : Em ≫ Ep ⟶ Em ≫ Ep) :
    mateEquiv Bm Bp τ ≫ Ap.counit = Rm ◁ curlE Bp Ap τ ≫ Bm.counit := by
  calc _ = 𝟙 _ ⊗≫ Rm ◁ Em ◁ Bp.unit ⊗≫ Rm ◁ τ ▷ Rp ⊗≫
          (Bm.counit ▷ (Ep ≫ Rp) ≫ 𝟙 b ◁ Ap.counit) ⊗≫ 𝟙 _ := by
        rw [mateEquiv_apply']; bicategory
    _ = 𝟙 _ ⊗≫ Rm ◁ Em ◁ Bp.unit ⊗≫ Rm ◁ τ ▷ Rp ⊗≫
          ((Rm ≫ Em) ◁ Ap.counit ≫ Bm.counit ▷ 𝟙 b) ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange]
    _ = _ := by
        unfold curlE; bicategory

end Generic

/-! ## `c_{-1} = 1` -/

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [GradedBicategory.ShiftCoherence B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, KrullSchmidtCat.HomFinite k (a ⟶ b)] [∀ a b : B, IsIdempotentComplete (a ⟶ b)]

namespace StrongSl2

open GradedHomBicat GradedHomCat

variable {S : StrongSl2 k B} (hS : S.BBw)

omit [GradedBicategory.ShiftCoherence B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, KrullSchmidtCat.HomFinite k (a ⟶ b)] [∀ a b : B, IsIdempotentComplete (a ⟶ b)] in
/-- At a weight `n ≤ -1`, `E 1_n` is nonzero if `1_n` is (`1_n` is a summand of `F E 1_n`). -/
theorem not_isZero_E_of_wt_neg {r : ℤ} (hn : S.wt r ≤ -1) (h : ¬ IsZero (𝟙 (S.obj r))) :
    ¬ IsZero (S.E r) := by
  obtain ⟨q, rfl⟩ : ∃ q, r = q + 1 := ⟨r - 1, by ring⟩
  intro hE
  obtain ⟨e⟩ := S.exists_FEDecomp (r := q) (by omega)
  have h0 : 0 < (-S.wt (q + 1)).toNat := by omega
  have hz : IsZero (S.oneShiftNeg q 0) := by
    refine (IsZero.iff_id_eq_zero _).2 ?_
    rw [← ιN_πN_self e h0, (isZero_comp_left hE _).eq_of_tgt (ιN e 0) 0, zero_comp]
  apply h
  exact ((shiftFunctor _ (-(1 * ((((-S.wt (q + 1)).toNat : ℕ) : ℤ) - 1 - 2 * ((0 : ℕ) : ℤ))))).map_isZero
    hz).of_iso ((shiftFunctorCompIsoId _ _ _ (by ring)).app _).symm

/-- **`c_{-1} = 1`** (CL Lemma 5.4, first item): for the normalized left adjunctions, the
counter-clockwise degree-zero bubble at the weight `-1` is the identity. -/
theorem BBw.ccwBub_neg_one {r : ℤ} (hr : S.wt r = -1) : S.ccwBub (hS.leftAdjN r) 0 = 𝟙 _ := by
  by_cases h0 : IsZero (𝟙 (S.obj r))
  · exact ((incl _).map_isZero h0).eq_of_src _ _
  obtain ⟨c, hc⟩ := S.exists_eq_smul_id ((S.isHomogeneous_ccwBub _ (hS.leftAdjN_spec r).2.1 0).of_eq
    (by push_cast; omega))
  -- the decomposition of `1_{EF1_1}`
  obtain ⟨_, h2⟩ := hS.decompEF_pos (q := r) (by rw [S.wt_add_one]; omega)
  have hN : (S.wt (r + 1)).toNat = 1 := by rw [S.wt_add_one]; omega
  have hcomp : hS.compK r 0 = S.grCounit r := by
    rw [BBw.compK, hN, Finset.sum_range_one, show 1 - 1 - 0 - 0 = 0 from rfl]
    unfold BBw.ccwL
    rw [ccwL_fake _ _ _ (i := 0) (by rw [S.wt_add_one]; omega)]
    simp [capD, grassInv_zero]
  rw [hN, Finset.sum_range_one, hcomp, cupD_zero] at h2
  have h2' : S.grCounit r ≫ (hS.leftAdjN r).unit = 𝟙 _ + S.grSigma r ≫ hS.sideL r := by
    rw [← h2]; abel
  -- place it between the right cup and the left cap of `E 1_{-1}`
  have h3 := congrArg (capCup (S.grAdj r) (hS.leftAdjN r)) h2'
  have hadd : ∀ f g : S.grR r ≫ S.grE r ⟶ S.grR r ≫ S.grE r,
      capCup (S.grAdj r) (hS.leftAdjN r) (f + g) =
        capCup (S.grAdj r) (hS.leftAdjN r) f + capCup (S.grAdj r) (hS.leftAdjN r) g := by
    intro f g
    simp only [capCup, GradedHomBicat.whiskerLeft_add, Preadditive.add_comp,
      Preadditive.comp_add]
  rw [hadd, capCup_id, show S.grCounit r = (S.grAdj r).counit from rfl, capCup_counit_unit,
    grSigma_eq_mateEquiv, show hS.sideL r = (mateEquiv (hS.leftAdjN r) (hS.leftAdjN (r + 1))).symm
      (S.grCross r) from rfl, capCup_sigma_sideL, S.grCross_sq, zero_whiskerRight, zero_comp,
    comp_zero, comp_zero, comp_zero, add_zero] at h3
  have hb : (S.grAdj r).unit ≫ (hS.leftAdjN r).counit = c • 𝟙 _ := by
    rw [← hc]
    simp [ccwBub]
  rw [hb, GradedHomBicat.smul_whiskerRight, id_whiskerRight, Linear.smul_comp, Linear.comp_smul,
    Category.id_comp, Iso.inv_hom_id] at h3
  replace h3 := h3.symm
  have hE : 𝟙 (S.grE r) ≠ 0 := fun h => S.not_isZero_E_of_wt_neg (by omega) h0
    (by
      refine (IsZero.iff_id_eq_zero _).2 (incl₂_injective ?_)
      change incl₂ (𝟙 (S.E r)) = (incl _).map 0
      rw [incl₂_id, Functor.map_zero]
      exact h)
  have hc1 : c = 1 := by
    have h4 : (c - 1) • 𝟙 (S.grE r) = 0 := by rw [sub_smul, h3, one_smul, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h4).resolve_right hE)
  rw [hc, hc1, one_smul]

/-- Under (BB_w), a homogeneous degree-zero endomorphism of `E 1_m` is a scalar. -/
theorem BBw.exists_eq_smul_id_E (hS : S.BBw) {r : ℤ} {ψ : S.grE r ⟶ S.grE r} (hψ : IsHomogeneous ψ 0) :
    ∃ c : k, ψ = c • 𝟙 _ := by
  by_cases h₀ : IsZero (𝟙 (S.obj r))
  · exact ⟨0, ((incl _).map_isZero (S.isZero_E_of_left h₀)).eq_of_src _ _⟩
  by_cases h₁ : IsZero (𝟙 (S.obj (r + 1)))
  · exact ⟨0, ((incl _).map_isZero (S.isZero_E_of_right h₁)).eq_of_src _ _⟩
  have hfin := S.finrank_End_E_eq_one (fun r' => hS.adjHyp r') h₀ h₁
  have hid : 𝟙 (S.grE r) ≠ 0 := by
    intro h
    have hz : IsZero (S.E r) := by
      refine (IsZero.iff_id_eq_zero _).2 (incl₂_injective ?_)
      change incl₂ (𝟙 (S.E r)) = (incl _).map 0
      rw [incl₂_id, Functor.map_zero]
      exact h
    rw [finrank_hom_of_isZero_left k hz] at hfin
    exact zero_ne_one hfin
  exact GradedHomBicat.exists_smul_of_isHomogeneous hψ (isHomogeneous_id _) hid
    (by rw [finrank_hom_shift_zero k _ _ (rfl : (0 : ℤ) = 0)]; exact hfin)

/-- **CL Lemma 5.4 at `n = 0`** (`β_0 = -r_i^{-2}`, i.e. `-1` for normalized dots): if
`σ' ≫ β σ = 1_{FE1_0}`, `β σ σ' = 1_{EF1_0}` and `F E 1_0 ≠ 0`, then `β = -1`. Three closings:
the downward strand of `σ'σ` on the left (`sideL_trace`: `β⁻¹ =` the curl `C₀` of `τ` on `E 1_0`),
the downward strand of `σσ'` on the right (`capCupY_sigma_sideL`: with `τ x τ = -τ`,
`β · (-C'₀) = 1` for the curl `C'₀` of `τ` on `E 1_{-2}`), and the cap of `E 1_{-2}` on top of
`β σσ' = 1` (`sideL_comp_counit`, `sigma_comp_counit`: `C'₀ = 1`). (CL: "Capping off the top of
(`eq_ident_decompT`) for `n = 0` ... implies that `β_0 = -r_i^2`"; with `c_0^+ = -1/(β_0 r_i)` and
`c_0^+ = r_i` this is `β_0 = -r_i^{-2}`, as in the statement of the lemma.) -/
theorem BBw.beta_eq_neg_one_zero {q : ℤ} (h0 : S.wt (q + 1) = 0) {β : k}
    (h1 : hS.sideL q ≫ (β • S.grSigma q) = 𝟙 _) (h2 : β • (S.grSigma q ≫ hS.sideL q) = 𝟙 _)
    (hER : ¬ IsZero (S.grE (q + 1) ≫ S.grR (q + 1))) : β = -1 := by
  have hwq : S.wt q = -2 := by have := S.wt_add_one q; omega
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [zero_smul, comp_zero] at h1
    exact hER ((IsZero.iff_id_eq_zero _).2 h1.symm)
  have hEp : 𝟙 (S.grE (q + 1)) ≠ 0 := by
    intro h
    apply hER
    refine (IsZero.iff_id_eq_zero _).2 ?_
    rw [← Bicategory.id_whiskerRight, h, zero_whiskerRight]
  have hEm : 𝟙 (S.grE q) ≠ 0 := by
    intro h
    apply hER
    refine (IsZero.iff_id_eq_zero _).2 ?_
    rw [← h1, Linear.comp_smul]
    have : 𝟙 (S.grR q ≫ S.grE q) = 0 := by
      rw [← Bicategory.whiskerLeft_id, h, GradedHomBicat.whiskerLeft_zero]
    rw [show hS.sideL q ≫ S.grSigma q = hS.sideL q ≫ 𝟙 _ ≫ S.grSigma q by rw [Category.id_comp],
      this, zero_comp, comp_zero, smul_zero]
  -- step 1: closing `σ'σ` on the left
  set C₀ := curlG (hS.leftAdjN q).unit (S.grCounit q) (S.grCross q) with hC₀
  have hstep1 : β⁻¹ • 𝟙 (S.grE (q + 1)) = C₀ := by
    have htr := sideL_trace (hS.leftAdjN q) (hS.leftAdjN (q + 1)) (S.grAdj q) (S.grAdj (q + 1))
      (S.grCross q) (powComp (S.grDotN (q + 1)) 1)
    rw [← grSigma_eq_mateEquiv] at htr
    change rtrace _ _ _ (hS.sideL q ≫ S.grSigma q) = _ at htr
    have hσσ : hS.sideL q ≫ S.grSigma q = β⁻¹ • 𝟙 _ := by
      rw [← h1, Linear.comp_smul, smul_smul, inv_mul_cancel₀ hβ0, one_smul]
    have hbub : S.cwBub (hS.leftAdjN (q + 1)) 1 = 𝟙 _ := by
      have h := BBw.cwBub_deg_zero hS (q := q + 1) (by rw [S.wt_add_one]; omega)
      rwa [show (S.wt (q + 1 + 1)).toNat - 1 = 1 by rw [S.wt_add_one]; omega] at h
    rw [hσσ, rtrace_smul, rtrace_id, grAdj_counit, grAdj_counit,
      show (hS.leftAdjN (q + 1)).unit ≫ S.grR (q + 1) ◁ powComp (S.grDotN (q + 1)) 1 ≫
        S.grCounit (q + 1) = S.cwBub (hS.leftAdjN (q + 1)) 1 from rfl, hbub,
      Bicategory.whiskerLeft_id, Category.id_comp, Iso.inv_hom_id, whiskerLeft_powComp,
      tau_powComp_tau _ _ _ (S.grCross_sq q) (S.grDotN_slide_right q) 0, Finset.sum_range_one,
      powComp_zero, powComp_zero, Category.id_comp, Category.id_comp] at htr
    exact htr
  -- step 2: closing `σσ'` on the right
  set C' := curlE (S.grAdj (q + 1)) (hS.leftAdjN (q + 1)) (S.grCross q) with hC'
  have hstep2 : β • (-C') = 𝟙 (S.grE q) := by
    have htr := capCupY_sigma_sideL (S.grAdj q) (hS.leftAdjN q) (S.grAdj (q + 1))
      (hS.leftAdjN (q + 1)) (S.grCross q) (S.grDotN q)
    rw [← grSigma_eq_mateEquiv] at htr
    change capCupY _ _ _ (S.grSigma q ≫ hS.sideL q) = _ at htr
    have hτxτ : S.grCross q ≫ S.grDotN q ▷ S.grE (q + 1) ≫ S.grCross q = -S.grCross q := by
      have hs := S.grDotN_slide q
      have : S.grCross q ≫ S.grDotN q ▷ S.grE (q + 1) =
          S.grE q ◁ S.grDotN (q + 1) ≫ S.grCross q - 𝟙 _ := by rw [← hs]; abel
      rw [← Category.assoc, this, Preadditive.sub_comp, Category.assoc, S.grCross_sq,
        comp_zero, zero_sub, Category.id_comp]
    have hbub : (S.grAdj q).unit ≫ S.grDotN q ▷ S.grR q ≫ (hS.leftAdjN q).counit = 𝟙 _ := by
      have h := BBw.ccwBub_deg_zero hS (r := q) (by omega)
      rw [show (-S.wt q).toNat - 1 = 1 by omega] at h
      simp only [ccwBub, powComp_succ, powComp_zero, Category.id_comp] at h
      exact h
    have hlin : capCupY (S.grAdj q) (hS.leftAdjN q) (S.grDotN q)
        (β • (S.grSigma q ≫ hS.sideL q)) =
          β • capCupY (S.grAdj q) (hS.leftAdjN q) (S.grDotN q) (S.grSigma q ≫ hS.sideL q) := by
      simp only [capCupY, GradedHomBicat.whiskerLeft_smul, Linear.smul_comp, Linear.comp_smul]
    rw [h2, capCupY_id, hbub, id_whiskerRight, Category.id_comp, Iso.inv_hom_id, htr, hτxτ]
      at hlin
    have hneg : (-S.grCross q) ▷ S.grR (q + 1) = -(S.grCross q ▷ S.grR (q + 1)) := by
      refine eq_neg_of_add_eq_zero_left ?_
      rw [← GradedHomBicat.add_whiskerRight, neg_add_cancel, GradedHomBicat.zero_whiskerRight]
    rw [hlin, hC', curlE, hneg]
    simp only [Preadditive.neg_comp, Preadditive.comp_neg, smul_neg]
  -- step 3: the cap of `E 1_{-2}` on top of `β σσ' = 1`
  obtain ⟨c', hc'⟩ := hS.exists_eq_smul_id_E (r := q) (ψ := C') (by
    refine ((isHomogeneous_rightUnitor_inv _).comp ((isHomogeneous_whiskerLeft _
      (isHomogeneous_incl₂ _)).comp ((isHomogeneous_associator_inv _ _ _).comp
        ((isHomogeneous_whiskerRight (isHomogeneous_of₂ _ _) _).comp
          ((isHomogeneous_associator_hom _ _ _).comp ((isHomogeneous_whiskerLeft _
            (hS.leftAdjN_spec (q + 1)).2.1).comp (isHomogeneous_rightUnitor_hom _) rfl) rfl)
              rfl) rfl) rfl) rfl).of_eq ?_
    rw [S.wt_add_one]; omega)
  have hε : S.grCounit q ≠ 0 := S.grCounit_ne_zero (fun hz => hEm (by
    have := (incl _).map_isZero hz
    exact (IsZero.iff_id_eq_zero _).1 this))
  have hstep3 : c' = 1 := by
    have h3 : S.grCounit q = (β • (S.grSigma q ≫ hS.sideL q)) ≫ S.grCounit q := by
      rw [h2, Category.id_comp]
    rw [Linear.smul_comp, Category.assoc,
      show hS.sideL q ≫ S.grCounit q = C₀ ▷ S.grR (q + 1) ≫ (hS.leftAdjN (q + 1)).counit from
        sideL_comp_counit (hS.leftAdjN q) (hS.leftAdjN (q + 1)) (S.grAdj q) (S.grCross q),
      ← hstep1, GradedHomBicat.smul_whiskerRight, id_whiskerRight, Linear.smul_comp,
      Category.id_comp, Linear.comp_smul, smul_smul, mul_inv_cancel₀ hβ0, one_smul,
      grSigma_eq_mateEquiv, sigma_comp_counit, ← hC', hc', GradedHomBicat.whiskerLeft_smul,
      Bicategory.whiskerLeft_id, Linear.smul_comp, Category.id_comp] at h3
    rw [grAdj_counit] at h3
    have h4 : (c' - 1) • S.grCounit q = 0 := by rw [sub_smul, ← h3, one_smul, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h4).resolve_right hε)
  rw [hc', hstep3, one_smul, smul_neg] at hstep2
  have h5 : (β + 1) • 𝟙 (S.grE q) = 0 := by
    rw [add_smul, one_smul]
    calc β • 𝟙 (S.grE q) + 𝟙 (S.grE q) = β • 𝟙 (S.grE q) + -(β • 𝟙 (S.grE q)) := by
          rw [hstep2]
      _ = 0 := add_neg_cancel _
  exact eq_neg_of_add_eq_zero_left ((smul_eq_zero.1 h5).resolve_right hEm)

/-- **CL relations (A2), (A5) with `β = -1`, for all `n ≥ 0`**: `σ' σ = -1` on `FE1_n` and
`1_{EF1_n} = -σσ' + ∑_k comp_k cup_k` (KL III `eq_ident_decomp` for `n ≥ 0`). -/
theorem BBw.decompEF {q : ℤ} (hn : 0 ≤ S.wt (q + 1)) :
    hS.sideL q ≫ S.grSigma q = -𝟙 _ ∧
      -(S.grSigma q ≫ hS.sideL q) +
        ∑ j ∈ Finset.range (S.wt (q + 1)).toNat, hS.compK q j ≫ S.cupD (hS.leftAdjN q) j =
          𝟙 _ := by
  rcases lt_or_eq_of_le hn with hn | hn
  · exact hS.decompEF_pos (by omega)
  obtain ⟨β, h1, h2⟩ := hS.decompEF_beta (q := q) (by omega)
  have hN : (S.wt (q + 1)).toNat = 0 := by omega
  rw [hN, Finset.sum_range_zero, add_zero] at h2 ⊢
  by_cases hER : IsZero (S.grE (q + 1) ≫ S.grR (q + 1))
  · refine ⟨hER.eq_of_src _ _, ?_⟩
    rw [← h2, hER.eq_of_tgt (S.grSigma q) 0, zero_comp, neg_zero, smul_zero]
  · have hβ := hS.beta_eq_neg_one_zero hn.symm h1 h2 hER
    subst hβ
    refine ⟨?_, ?_⟩
    · rw [← h1, Linear.comp_smul, neg_smul, one_smul, neg_neg]
    · rw [← h2, neg_smul, one_smul]

end StrongSl2

end Categorification.TwoRep

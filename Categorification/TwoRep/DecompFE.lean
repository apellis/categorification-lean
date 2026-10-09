/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.CoeffLemma

/-!
# The decomposition of `1_{FE1_n}` for `n ≤ 0` (CL §§5.2–5.3, `n ≤ 0`)

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, §5.2 ("Results for `n ≤ 0` are proven similarly") and §5.3 (relations (A1)–(A5)
for `n ≤ 0`, the analogue of Proposition 5.2), the mirror image of `DecompEF.lean`.

Fix the object `q + 1` of weight `n = wt (q + 1) ≤ 0`. CL's map (Corollary 3.13 for `n ≤ 0`)

  `ζ = σ ⊕ ⊕_{k<-n} ccup_k : E F 1_n ⊕ ⊕_k 1_n⟨-n-1-2k⟩ → F E 1_n`

(the rightward sideways crossing `σ = grSigma q` and `ccup_k` the right cup of `E 1_n` followed by
`k` dots, `ccupD`) is an isomorphism with inverse `β σ' ⊕ ⊕_k ccomp_k`, where
`ccomp_k = ∑_g ccap_{-n-1-k-g} ∘ (fake clockwise bubble of degree 2g)` (`compKN`): the relations

* (B1) `ccup_{k'} ≫ ccomp_k = δ_{k k'}` (`ccupD_comp_compKN`), from the normalization of the
  counter-clockwise degree-zero bubble (CL (4.1) for `n ≤ -2`, `c_{-1} = 1` for `n = -1`) and the
  definition of the fake clockwise bubbles;
* (B3) `ccup_k ≫ σ' = 0` for `k < -n` (`ccupD_comp_sideL`) and (B4) `σ ≫ ccomp_k = 0`
  (`grSigma_comp_compKN`), by degrees;
* (B2) `σ ≫ β σ' = 1_{EF1_n}` and (B5) `1_{FE1_n} = β σ'σ + ∑_k ccomp_k ccup_k`
  (`decompFE_beta`).

The proof of (B2), (B5) starts from a decomposition `F E 1_n ≅ E F 1_n ⊕ ⊕_{[-n]} 1_n`
(Definition 1.2 (3)) transported to the graded-Hom bicategory and inverts the triangular matrix of
the cups (`inCupSpan_of_triangular`). By Lemma 3.12 (both spaces one-dimensional, Corollary 3.2)
the inclusion and the projection of `E F 1_n` are multiples of `σ` and `σ'` unless the crossing
vanishes, in which case `E F 1_n = 0`.

## Main declarations

* `StrongSl2.ccupD`, `ccapD`, `compKN`, `ccupD_comp_compKN` (B1),
  `ccupD_comp_sideL` (B3), `grSigma_comp_compKN` (B4), `decompFE_beta` (B2, B5);
* `StrongSl2.finrank_EE_neg_two` (Corollary 3.2 at every weight).
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

universe w v u

/-! ## Vanishing by the left adjunction -/

section GradedHom

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B] [GradedBicategory.ShiftCoherence B]

namespace GradedHomBicat

open GradedHomCat

/-- A homogeneous `χ : 1 ⟶ R E` vanishes if, under `R ⊣ E`, the corresponding endomorphisms of `E`
vanish in its degree (shifted by the degree of the counit). -/
theorem eq_zero_of_isHomogeneous_left_unit_side {a b : GradedHomBicat B} {E : a ⟶ b}
    {R : b ⟶ a} (adj : R ⊣ E) {c : ℤ} (hc : IsHomogeneous adj.counit c) {d : ℤ}
    (hE : ∀ ψ : E ⟶ E, IsHomogeneous ψ (c + d) → ψ = 0) {χ : 𝟙 b ⟶ R ≫ E}
    (hχ : IsHomogeneous χ d) : χ = 0 := by
  have hψ : IsHomogeneous ((ρ_ E).inv ≫ adj.homEquiv₁ χ) (c + d) := by
    rw [Adjunction.homEquiv₁_apply]
    have h1 : IsHomogeneous (adj.counit ▷ E ≫ (λ_ E).hom) c :=
      (isHomogeneous_whiskerRight hc E).comp (isHomogeneous_leftUnitor_hom E) (zero_add c)
    have h2 : IsHomogeneous ((α_ E R E).inv ≫ adj.counit ▷ E ≫ (λ_ E).hom) c :=
      (isHomogeneous_associator_inv E R E).comp h1 (add_zero c)
    have h3 := (isHomogeneous_whiskerLeft E hχ).comp h2 rfl
    exact (isHomogeneous_rightUnitor_inv E).comp h3 (add_zero _)
  have h0 : adj.homEquiv₁ χ = 0 := by
    have := hE _ hψ
    rw [← Category.id_comp (adj.homEquiv₁ χ), ← Iso.hom_inv_id (ρ_ E), Category.assoc, this,
      comp_zero]
  have : χ = adj.homEquiv₁.symm 0 := by rw [← h0, Equiv.symm_apply_apply]
  rw [this, Adjunction.homEquiv₁_symm_apply]
  simp only [whiskerLeft_zero, comp_zero]

/-- A homogeneous `χ : R E ⟶ 1` vanishes if, under `E ⊣ R`, the corresponding endomorphisms of `E`
vanish in its degree. -/
theorem eq_zero_of_isHomogeneous_right_counit_side {a b : GradedHomBicat B} {E : a ⟶ b}
    {R : b ⟶ a} (adj : E ⊣ R) {u : ℤ} (hu : IsHomogeneous adj.unit u) {d : ℤ}
    (hE : ∀ ψ : E ⟶ E, IsHomogeneous ψ (d + u) → ψ = 0) {χ : R ≫ E ⟶ 𝟙 b}
    (hχ : IsHomogeneous χ d) : χ = 0 := by
  have hψ : IsHomogeneous (adj.homEquiv₁.symm χ ≫ (ρ_ E).hom) (d + u) := by
    rw [Adjunction.homEquiv₁_symm_apply]
    have h1 : IsHomogeneous (E ◁ χ ≫ (ρ_ E).hom) d :=
      (isHomogeneous_whiskerLeft E hχ).comp (isHomogeneous_rightUnitor_hom E) (zero_add d)
    have h2 : IsHomogeneous ((α_ E R E).hom ≫ E ◁ χ ≫ (ρ_ E).hom) d :=
      (isHomogeneous_associator_hom E R E).comp h1 (add_zero d)
    have h3 : IsHomogeneous (adj.unit ▷ E ≫ (α_ E R E).hom ≫ E ◁ χ ≫ (ρ_ E).hom) (d + u) :=
      (isHomogeneous_whiskerRight hu E).comp h2 rfl
    have h4 := (isHomogeneous_leftUnitor_inv E).comp h3 (add_zero (d + u))
    simpa only [Category.assoc] using h4
  have h0 : adj.homEquiv₁.symm χ = 0 := by
    have := hE _ hψ
    rw [← Category.comp_id (adj.homEquiv₁.symm χ), ← Iso.hom_inv_id (ρ_ E), ← Category.assoc,
      this, zero_comp]
  have : χ = adj.homEquiv₁ 0 := by rw [← h0, Equiv.apply_symm_apply]
  rw [this, Adjunction.homEquiv₁_apply]
  simp only [whiskerLeft_zero, zero_comp]

end GradedHomBicat

end GradedHom

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [GradedBicategory.ShiftCoherence B] [GradedBicategory.IsLinear B k]

namespace StrongSl2

open GradedHomBicat GradedHomCat Module
open KrullSchmidtCat (HomFinite)

variable (S : StrongSl2 k B)

/-- **The right cup with `j` dots** `1_n → F E 1_n` (the unit of `E 1_n ⊣ R_n`, then `j` dots on
`E 1_n`), at the object `q + 1`. -/
def ccupD (q : ℤ) (j : ℕ) : 𝟙 (of (S.obj (q + 1))) ⟶ S.grE (q + 1) ≫ S.grR (q + 1) :=
  S.grUnit (q + 1) ≫ powComp (S.grDotN (q + 1)) j ▷ S.grR (q + 1)

/-- **The left cap with `j` dots** `F E 1_n → 1_n` (`j` dots on `E 1_n`, then the counit of a left
adjunction `A : R_n ⊣ E 1_n`). -/
def ccapD {q : ℤ} (A : S.grR (q + 1) ⊣ S.grE (q + 1)) (j : ℕ) :
    S.grE (q + 1) ≫ S.grR (q + 1) ⟶ 𝟙 (of (S.obj (q + 1))) :=
  powComp (S.grDotN (q + 1)) j ▷ S.grR (q + 1) ≫ A.counit

theorem ccupD_comp_ccapD {q : ℤ} (A : S.grR (q + 1) ⊣ S.grE (q + 1)) (i j : ℕ) :
    S.ccupD q i ≫ S.ccapD A j = S.ccwBub A (i + j) := by
  simp only [ccupD, ccapD, ccwBub, Category.assoc]
  rw [← Category.assoc (powComp (S.grDotN (q + 1)) i ▷ S.grR (q + 1)), ← comp_whiskerRight,
    powComp_add]

theorem isHomogeneous_ccupD (q : ℤ) (j : ℕ) : IsHomogeneous (S.ccupD q j) (2 * (j : ℤ)) :=
  ((isHomogeneous_incl₂ _).comp (isHomogeneous_whiskerRight (GradedHomBicat.isHomogeneous_powComp
    (S.isHomogeneous_grDotN (q + 1)) j) _) rfl).of_eq (by ring)

theorem isHomogeneous_ccapD {q : ℤ} (A : S.grR (q + 1) ⊣ S.grE (q + 1))
    (hc : IsHomogeneous A.counit (2 * S.wt (q + 1) + 2)) (j : ℕ) :
    IsHomogeneous (S.ccapD A j) (2 * (j : ℤ) + 2 * S.wt (q + 1) + 2) :=
  ((isHomogeneous_whiskerRight (GradedHomBicat.isHomogeneous_powComp
    (S.isHomogeneous_grDotN (q + 1)) j) _).comp hc rfl).of_eq (by ring)

/-! ### The decomposition `F E 1_n ≅ E F 1_n ⊕ ⊕_{[-n]} 1_n` in the graded-Hom bicategory -/

section Decomp

variable {S} {q : ℤ} (e : S.FEDecomp q)

/-- `1_n⟨-n-1-2j⟩ ≅ 1_n` in the graded-Hom bicategory. -/
def oneShiftNegIso₁ (S : StrongSl2 k B) (q : ℤ) (j : ℕ) :
    of₁ (S.oneShiftNeg q j) ≅ 𝟙 (of (S.obj (q + 1))) :=
  shiftIso₁ (𝟙 (S.obj (q + 1))) (1 * ((((-S.wt (q + 1)).toNat : ℕ) : ℤ) - 1 - 2 * (j : ℤ)))

/-- The inclusion of `E F 1_n` into `F E 1_n`, in the graded-Hom bicategory. -/
def grιEF : S.grR q ≫ S.grE q ⟶ S.grE (q + 1) ≫ S.grR (q + 1) :=
  (S.rhoSourceIso q).hom ≫ incl₂ (ιEF e) ≫ (S.rhoTargetIso q).inv

/-- The projection of `F E 1_n` onto `E F 1_n`, in the graded-Hom bicategory. -/
def grπEF : S.grE (q + 1) ≫ S.grR (q + 1) ⟶ S.grR q ≫ S.grE q :=
  (S.rhoTargetIso q).hom ≫ incl₂ (πEF e) ≫ (S.rhoSourceIso q).inv

/-- The inclusion of the summand `1_n⟨-n-1-2j⟩` into `F E 1_n`. -/
def grιN (j : ℕ) : 𝟙 (of (S.obj (q + 1))) ⟶ S.grE (q + 1) ≫ S.grR (q + 1) :=
  (oneShiftNegIso₁ S q j).inv ≫ incl₂ (ιN e j) ≫ (S.rhoTargetIso q).inv

/-- The projection of `F E 1_n` onto the summand `1_n⟨-n-1-2j⟩`. -/
def grπN (j : ℕ) : S.grE (q + 1) ≫ S.grR (q + 1) ⟶ 𝟙 (of (S.obj (q + 1))) :=
  (S.rhoTargetIso q).hom ≫ incl₂ (πN e j) ≫ (oneShiftNegIso₁ S q j).hom

omit [GradedBicategory.IsLinear B k] in
theorem grιEF_grπEF : grιEF e ≫ grπEF e = 𝟙 _ := by
  simp only [grιEF, grπEF, Category.assoc, Iso.inv_hom_id_assoc, incl₂_comp_assoc',
    show ιEF e ≫ πEF e = 𝟙 _ by simp [ιEF, πEF], incl₂_id, Category.id_comp, Iso.hom_inv_id]

omit [GradedBicategory.IsLinear B k] in
theorem grιN_grπN_self {j : ℕ} (hj : j < (-S.wt (q + 1)).toNat) : grιN e j ≫ grπN e j = 𝟙 _ := by
  simp only [grιN, grπN, Category.assoc, Iso.inv_hom_id_assoc, incl₂_comp_assoc', ιN_πN_self e hj,
    incl₂_id, Category.id_comp, Iso.inv_hom_id]

omit [GradedBicategory.IsLinear B k] in
/-- The decomposition of the identity of `F E 1_n`, in the graded-Hom bicategory. -/
theorem grTotalN :
    ∑ j ∈ Finset.range (-S.wt (q + 1)).toNat, grπN e j ≫ grιN e j + grπEF e ≫ grιEF e = 𝟙 _ := by
  have h : ∀ j ∈ Finset.range (-S.wt (q + 1)).toNat, grπN e j ≫ grιN e j =
      (S.rhoTargetIso q).hom ≫ incl₂ (πN e j ≫ ιN e j) ≫ (S.rhoTargetIso q).inv := by
    intro j _
    simp only [grπN, grιN, Category.assoc, Iso.hom_inv_id_assoc, incl₂_comp_assoc']
  have hEF : grπEF e ≫ grιEF e =
      (S.rhoTargetIso q).hom ≫ incl₂ (πEF e ≫ ιEF e) ≫ (S.rhoTargetIso q).inv := by
    simp only [grπEF, grιEF, Category.assoc, Iso.inv_hom_id_assoc, incl₂_comp_assoc']
  rw [Finset.sum_congr rfl h, hEF, ← Preadditive.comp_sum, ← Preadditive.sum_comp,
    ← Preadditive.comp_add, ← Preadditive.add_comp]
  have : ∑ j ∈ Finset.range (-S.wt (q + 1)).toNat, incl₂ (πN e j ≫ ιN e j) +
      incl₂ (πEF e ≫ ιEF e) = 𝟙 (of₁ (S.E (q + 1) ≫ S.F (q + 1))) := by
    change ∑ j ∈ _, (incl _).map _ + (incl _).map _ = _
    rw [← Functor.map_sum, ← Functor.map_add, totalN e]
    exact (incl _).map_id _
  rw [this, Category.id_comp, Iso.hom_inv_id]

omit [GradedBicategory.IsLinear B k] in
theorem isHomogeneous_grιEF : IsHomogeneous (grιEF e) (-2) :=
  ((S.isHomogeneous_rhoSourceIso_hom q).comp ((isHomogeneous_incl₂ _).comp
    (S.isHomogeneous_rhoTargetIso_inv q) rfl) rfl).of_eq (by ring)

omit [GradedBicategory.IsLinear B k] in
theorem isHomogeneous_grπEF : IsHomogeneous (grπEF e) 2 :=
  ((S.isHomogeneous_rhoTargetIso_hom q).comp ((isHomogeneous_incl₂ _).comp
    (S.isHomogeneous_rhoSourceIso_inv q) rfl) rfl).of_eq (by ring)

omit [GradedBicategory.IsLinear B k] in
theorem isHomogeneous_grιN (hn : S.wt (q + 1) ≤ 0) (j : ℕ) :
    IsHomogeneous (grιN e j) (2 * (j : ℤ)) :=
  ((shiftIso₁_inv_isHomogeneous (𝟙 (S.obj (q + 1))) _).comp ((isHomogeneous_incl₂ _).comp
    (S.isHomogeneous_rhoTargetIso_inv q) rfl) rfl).of_eq (by
      have h1 : (((-S.wt (q + 1)).toNat : ℕ) : ℤ) = -S.wt (q + 1) := Int.toNat_of_nonneg (by omega)
      rw [h1]; simp only [wt]; ring)

omit [GradedBicategory.IsLinear B k] in
theorem isHomogeneous_grπN (hn : S.wt (q + 1) ≤ 0) (j : ℕ) :
    IsHomogeneous (grπN e j) (-2 * (j : ℤ)) :=
  ((S.isHomogeneous_rhoTargetIso_hom q).comp ((isHomogeneous_incl₂ _).comp
    (shiftIso₁_hom_isHomogeneous (𝟙 (S.obj (q + 1))) _) rfl) rfl).of_eq (by
      have h1 : (((-S.wt (q + 1)).toNat : ℕ) : ℤ) = -S.wt (q + 1) := Int.toNat_of_nonneg (by omega)
      rw [h1]; simp only [wt]; ring)

end Decomp

/-! ### Consequences at every weight -/

variable [∀ a b : B, HomFinite k (a ⟶ b)] [∀ a b : B, IsIdempotentComplete (a ⟶ b)] {S}

variable (S) in
/-- **Corollary 3.2**, at every weight: the degree `-2` endomorphisms of a nonzero
`E E 1_m` form a line. -/
theorem finrank_EE_neg_two {r : ℤ} (hE : ¬ IsZero (S.E r ≫ S.E (r + 1))) :
    finrank k (S.E r ≫ S.E (r + 1) ⟶ (S.E r ≫ S.E (r + 1))⟦(-2 : ℤ)⟧) = 1 := by
  have hyp : ∀ r', S.AdjHyp r' := S.adjHyp
  rcases le_or_gt (-2) (S.wt r) with hw | hw
  · refine S.cor0_zero (r₀ := r + 1) (by rw [S.wt_add_one]; omega) (fun r' _ => hyp r')
      (by omega) (fun hz => hE ?_)
    exact isZero_comp_right _ (IsZero.of_iso (isZero_comp_right _ hz) (ρ_ _).symm)
  · refine S.cor0Neg_zero (r₁ := r + 1) (by rw [S.wt_add_one]; omega) (fun r' _ => hyp r')
      (by omega) (by rw [S.wt_add_one]; omega) (fun hz => hE ?_)
    exact isZero_comp_left (IsZero.of_iso (isZero_comp_left hz _) (λ_ _).symm) _

variable (S) in
/-- A homogeneous `1_n ⟶ E F 1_n` of degree `< 2 - 2n` vanishes. -/
theorem eq_zero_to_RE {q : ℤ}
    {χ : 𝟙 (of (S.obj (q + 1))) ⟶ S.grR q ≫ S.grE q} {d : ℤ} (hχ : IsHomogeneous χ d)
    (hd : d < 2 - 2 * S.wt (q + 1)) : χ = 0 :=
  eq_zero_of_isHomogeneous_left_unit_side (S.leftAdjN q) (S.leftAdjN_spec q).2.1
    (fun _ hψ => S.grE_end_eq_zero hψ (by rw [S.wt_add_one] at hd; omega)) hχ

variable (S) in
/-- A homogeneous `E F 1_n ⟶ 1_n` of negative degree vanishes. -/
theorem eq_zero_from_RE {q : ℤ}
    {χ : S.grR q ≫ S.grE q ⟶ 𝟙 (of (S.obj (q + 1)))} {d : ℤ} (hχ : IsHomogeneous χ d)
    (hd : d < 0) : χ = 0 :=
  eq_zero_of_isHomogeneous_right_counit_side (S.grAdj q) (u := 0) (isHomogeneous_incl₂ _)
    (fun _ hψ => S.grE_end_eq_zero hψ (by omega)) hχ

/-- **CL (4.1) and `c_{-1} = 1`**: at every weight `n ≤ -1`, the counter-clockwise degree-zero
bubble is the identity. -/
theorem ccwBub_deg_zero' {r : ℤ} (hn : S.wt r ≤ -1) :
    S.ccwBub (S.leftAdjN r) ((-S.wt r).toNat - 1) = 𝟙 _ := by
  rcases lt_or_eq_of_le hn with h | h
  · exact ccwBub_deg_zero S (by omega)
  · rw [show (-S.wt r).toNat - 1 = 0 by omega]
    exact S.ccwBub_neg_one h

/-- **The infinite Grassmannian relation where it defines the clockwise fake bubbles**, at every
weight `n ≤ -1`. -/
theorem grassmannian_ccw_cw' {q : ℤ} (hn : S.wt (q + 1) ≤ -1) {K : ℕ}
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
      (-S.wt (q + 1)).toNat - 1 by omega, S.ccwBub_deg_zero' hn]
    rfl
  rw [← sum_mul_grassInv c hc0 K]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  unfold cwLN ccwLN
  rw [cwL_fake _ _ _ (by omega), hc]
  dsimp only
  rw [ccwL_of_nonneg _ _ _ (by omega), ccwR_of_nonneg _ _ (by omega)]

variable (S) in
/-- Real counter-clockwise bubbles with integer labels `≥ -n - 1`. -/
theorem ccwL_eq_ccwBub {q : ℤ} (hn1 : S.wt (q + 1) ≤ -1) (i : ℕ) :
    S.ccwLN q (-S.wt (q + 1) - 1 + i) =
      S.ccwBub (S.leftAdjN (q + 1)) ((-S.wt (q + 1)).toNat - 1 + i) := by
  unfold ccwLN
  rw [ccwL_of_nonneg _ _ _ (by omega)]
  congr 1
  omega

variable (S) in
/-- **(B3)** (a curl vanishes): for `k < -n`, `ccup_k ≫ σ' = 0` (by degrees). -/
theorem ccupD_comp_sideL {q : ℤ} {j : ℕ} (hj : (j : ℤ) < -S.wt (q + 1)) :
    S.ccupD q j ≫ S.sideLN q = 0 :=
  S.eq_zero_to_RE ((S.isHomogeneous_ccupD q j).comp (S.isHomogeneous_sideLN q) rfl) (by omega)

variable (S) in
/-- The `k`-th component of the inverse of `ζ` for `n ≤ 0`:
`ccomp_k = ∑_{g < -n - k} ccap_{-n-1-k-g} ∘ (fake clockwise bubble of degree 2g)`. -/
def compKN (q : ℤ) (j : ℕ) : S.grE (q + 1) ≫ S.grR (q + 1) ⟶ 𝟙 (of (S.obj (q + 1))) :=
  ∑ g ∈ Finset.range ((-S.wt (q + 1)).toNat - j),
    S.ccapD (S.leftAdjN (q + 1)) ((-S.wt (q + 1)).toNat - 1 - j - g) ≫
      S.cwLN q (S.wt (q + 1) - 1 + g)

variable (S) in
/-- **(B4)**: `σ ≫ ccomp_k = 0` (by degrees). -/
theorem grSigma_comp_compKN (q : ℤ) (j : ℕ) :
    S.grSigma q ≫ S.compKN q j = 0 := by
  rw [compKN, Preadditive.comp_sum]
  refine Finset.sum_eq_zero fun g hg => ?_
  have hg' := Finset.mem_range.1 hg
  rw [← Category.assoc, S.eq_zero_from_RE ((S.isHomogeneous_grSigma q).comp
    (S.isHomogeneous_ccapD _ (S.leftAdjN_spec (q + 1)).2.1 _) rfl) (by omega), zero_comp]

variable (S) in
/-- **(B1)**: `ccup_{k'} ≫ ccomp_k = δ_{k k'}` for `k, k' < -n`. -/
theorem ccupD_comp_compKN {q : ℤ} {j j' : ℕ} (hj : j < (-S.wt (q + 1)).toNat)
    (hj' : j' < (-S.wt (q + 1)).toNat) :
    S.ccupD q j' ≫ S.compKN q j = if j = j' then 𝟙 _ else 0 := by
  rw [compKN, Preadditive.comp_sum]
  set N := (-S.wt (q + 1)).toNat with hN
  have hn1 : S.wt (q + 1) ≤ -1 := by omega
  have hNn : (N : ℤ) = -S.wt (q + 1) := Int.toNat_of_nonneg (by omega)
  have hterm : ∀ g, S.ccupD q j' ≫ S.ccapD (S.leftAdjN (q + 1)) (N - 1 - j - g) ≫
      S.cwLN q (S.wt (q + 1) - 1 + g) =
        S.cwLN q (S.wt (q + 1) - 1 + g) *
          End.of (S.ccwBub (S.leftAdjN (q + 1)) (j' + (N - 1 - j - g))) := by
    intro g
    rw [← Category.assoc, ccupD_comp_ccapD]
    rfl
  simp only [hterm]
  have hvan : ∀ g, j' + (N - 1 - j - g) < N - 1 →
      S.ccwBub (S.leftAdjN (q + 1)) (j' + (N - 1 - j - g)) = 0 := fun g hg =>
    S.ccwBubN_eq_zero (by omega)
  by_cases hjj : j' < j
  · rw [ite_eq_right (by omega)]
    refine Finset.sum_eq_zero fun g hg => ?_
    rw [hvan g (by have := Finset.mem_range.1 hg; omega), mul_zero]
  · set D := j' - j with hD
    have hDN : D + 1 ≤ N - j := by omega
    rw [← Finset.sum_range_add_sum_Ico _ hDN, Finset.sum_eq_zero (s := Finset.Ico _ _)
      (fun g hg => by rw [hvan g (by have := Finset.mem_Ico.1 hg; omega), mul_zero]), add_zero]
    have hG := S.grassmannian_ccw_cw' hn1 (K := D) (by omega)
    rw [← Finset.sum_range_reflect] at hG
    have hif : (if j = j' then (𝟙 _ : 𝟙 (of (S.obj (q + 1))) ⟶ 𝟙 _) else 0) =
        if D = 0 then (1 : End (𝟙 (of (S.obj (q + 1))))) else 0 := by
      by_cases h : j = j'
      · rw [ite_eq_left h, ite_eq_left (by omega)]; rfl
      · rw [ite_eq_right h, ite_eq_right (by omega)]
    rw [hif, ← hG]
    refine Finset.sum_congr rfl fun g hg => ?_
    have hg' := Finset.mem_range.1 hg
    rw [show D + 1 - 1 - g = D - g by omega, show D - (D - g) = g by omega, mul_comm,
      S.ccwL_eq_ccwBub hn1, show j' + (N - 1 - j - g) = N - 1 + (D - g) by omega]

variable (S) in
/-- **CL Proposition 5.1 for `n ≤ 0` (form of `ζ⁻¹`), first part, and (B2)**: for
`n = wt (q + 1) ≤ 0` there are a scalar `β` and maps `φ_k : F E 1_n → 1_n` with
`σ ≫ β σ' = 1_{EF1_n}` and `1_{FE1_n} = β σ'σ + ∑_{k<-n} φ_k ∘ ccup_k`. -/
theorem exists_decompFE_aux {q : ℤ} (hn : S.wt (q + 1) ≤ 0) :
    ∃ (β : k) (φ : ℕ → (S.grE (q + 1) ≫ S.grR (q + 1) ⟶ 𝟙 (of (S.obj (q + 1))))),
      S.grSigma q ≫ (β • S.sideLN q) = 𝟙 _ ∧
      β • (S.sideLN q ≫ S.grSigma q) +
        ∑ j ∈ Finset.range (-S.wt (q + 1)).toNat, φ j ≫ S.ccupD q j = 𝟙 _ := by
  set N := (-S.wt (q + 1)).toNat with hN
  have hNn : (N : ℤ) = -S.wt (q + 1) := Int.toNat_of_nonneg (by omega)
  -- the weight `n` is zero: everything vanishes
  by_cases h1 : IsZero (𝟙 (S.obj (q + 1)))
  · have hRE : IsZero (S.grR q ≫ S.grE q) :=
      (incl _).map_isZero (isZero_comp_left ((shiftFunctor _ _).map_isZero
        (S.isZero_F_of_right h1)) _)
    have hER : IsZero (S.grE (q + 1) ≫ S.grR (q + 1)) :=
      (incl _).map_isZero (isZero_comp_left (S.isZero_E_of_left h1) _)
    exact ⟨1, 0, hRE.eq_of_src _ _, hER.eq_of_src _ _⟩
  obtain ⟨e⟩ := S.exists_FEDecomp hn
  -- the matrix of the cups in the summands `1_n⟨-n-1-2j⟩` is triangular
  have hcupπ : ∀ j i : ℕ, IsHomogeneous (S.ccupD q j ≫ grπN e i)
      (2 * (j : ℤ) - 2 * (i : ℤ)) := fun j i =>
    (S.isHomogeneous_ccupD q j).comp (isHomogeneous_grπN e hn i) (by ring)
  have hlow : ∀ j i, j < N → i < N → j < i → S.ccupD q j ≫ grπN e i = 0 :=
    fun j i _ _ hji => S.eq_zero_of_isHomogeneous_neg (hcupπ j i) (by omega)
  have hcupEF : ∀ j, j < N → S.ccupD q j ≫ grπEF e = 0 := fun j hj =>
    S.eq_zero_to_RE ((S.isHomogeneous_ccupD q j).comp (isHomogeneous_grπEF e) rfl) (by omega)
  have hexpand : ∀ j, j < N → ∀ {Y : _} (y : S.grE (q + 1) ≫ S.grR (q + 1) ⟶ Y),
      S.ccupD q j ≫ y =
        ∑ i ∈ Finset.range N, (S.ccupD q j ≫ grπN e i) ≫ grιN e i ≫ y := by
    intro j hj Y y
    conv_lhs => rw [← Category.id_comp y, ← grTotalN e]
    rw [Preadditive.add_comp, Preadditive.comp_add, Preadditive.sum_comp, Preadditive.comp_sum,
      Category.assoc, ← Category.assoc (S.ccupD q j) (grπEF e), hcupEF j hj, zero_comp, add_zero]
    simp only [Category.assoc]
    rfl
  have hexp : ∀ j, j < N → S.ccupD q j =
      ∑ i ∈ Finset.range N, (S.ccupD q j ≫ grπN e i) ≫ grιN e i := by
    intro j hj
    have := hexpand j hj (𝟙 _)
    simpa only [Category.comp_id] using this
  have hdiag : ∀ j, j < N → ∃ s : k, s ≠ 0 ∧
      S.ccupD q j ≫ grπN e j = s • 𝟙 (𝟙 (of (S.obj (q + 1)))) := by
    intro j hj
    obtain ⟨s, hs⟩ := S.exists_eq_smul_id ((hcupπ j j).of_eq (by ring))
    refine ⟨s, fun hs0 => h1 ?_, hs⟩
    have hn1 : S.wt (q + 1) ≤ -1 := by omega
    have hbub : S.ccupD q j ≫ S.ccapD (S.leftAdjN (q + 1)) (N - 1 - j) = 𝟙 _ := by
      rw [ccupD_comp_ccapD, show j + (N - 1 - j) = N - 1 by omega]
      exact S.ccwBub_deg_zero' hn1
    rw [hexpand j hj, Finset.sum_eq_zero] at hbub
    · refine (IsZero.iff_id_eq_zero _).2 (incl₂_injective ?_)
      change incl₂ (𝟙 (𝟙 (S.obj (q + 1)))) = (incl _).map 0
      rw [incl₂_id, Functor.map_zero]
      exact hbub.symm
    · intro i hi
      have hi' := Finset.mem_range.1 hi
      rcases lt_trichotomy j i with h | h | h
      · rw [hlow j i hj hi' h, zero_comp]
      · subst h
        rw [hs, hs0, zero_smul, zero_comp]
      · rw [S.eq_zero_of_isHomogeneous_neg (d := 2 * (i : ℤ) - 2 * (j : ℤ))
          ((isHomogeneous_grιN e hn i).comp (S.isHomogeneous_ccapD _
            (S.leftAdjN_spec (q + 1)).2.1 _) (by omega)) (by omega), comp_zero]
  -- the projection onto `⊕_j 1_n⟨-n-1-2j⟩` is a combination of the cups
  obtain ⟨φ, hφ⟩ : InCupSpan N (S.ccupD q) (∑ j ∈ Finset.range N, grπN e j ≫ grιN e j) :=
    InCupSpan.sum _ fun j hj => inCupSpan_of_triangular (grιN e) (grπN e) hlow hdiag hexp j
      (Finset.mem_range.1 hj) (grπN e j)
  -- the crossing vanishes: `E F 1_n = 0`
  by_cases hτ : S.grCross q = 0
  · have hRE : IsZero (S.grR q ≫ S.grE q) := by
      have hEEB := S.isZero_E_E_of_grCross_eq_zero hτ
      have hEER : IsZero (S.grE q ≫ (S.grE (q + 1) ≫ S.grR (q + 1))) :=
        (incl _).map_isZero ((isZero_comp_left hEEB _).of_iso (α_ _ _ _).symm)
      have h0 : 𝟙 (S.grE q ≫ (S.grR q ≫ S.grE q)) = 0 := by
        rw [← Bicategory.whiskerLeft_id, ← grιEF_grπEF e, Bicategory.whiskerLeft_comp,
          hEER.eq_of_src (S.grE q ◁ grπEF e) 0, comp_zero]
      have hzS : IsZero (S.grE q ≫ (S.grR q ≫ S.grE q)) := (IsZero.iff_id_eq_zero _).2 h0
      have hz : leftZigzag (S.grUnit q) (S.grCounit q) = 0 := by
        rw [leftZigzag, hzS.eq_of_src (S.grE q ◁ S.grCounit q) 0]
        simp [bicategoricalComp]
      have hE0 : 𝟙 (S.grE q) = 0 := by
        have : 𝟙 (S.grE q) = (λ_ _).inv ≫ ((λ_ _).hom ≫ (ρ_ _).inv) ≫ (ρ_ _).hom := by simp
        rw [this, ← S.leftZigzag_grUnit_grCounit q, hz, zero_comp, comp_zero]
      refine (IsZero.iff_id_eq_zero _).2 ?_
      rw [← Bicategory.whiskerLeft_id, hE0, GradedHomBicat.whiskerLeft_zero]
    refine ⟨1, φ, hRE.eq_of_src _ _, ?_⟩
    rw [hRE.eq_of_tgt (S.sideLN q) 0, zero_comp, smul_zero, zero_add, ← hφ]
    have := grTotalN e
    rwa [hRE.eq_of_tgt (grπEF e) 0, zero_comp, add_zero] at this
  -- Lemma 3.12: the inclusion and projection of `E F 1_n` are multiples of `σ` and `σ'`
  have hEE : ¬ IsZero (S.E q ≫ S.E (q + 1)) := fun hz =>
    hτ (((incl _).map_isZero hz).eq_of_src _ _)
  have hfin := S.finrank_EE_neg_two hEE
  have hσ0 : S.grSigma q ≠ 0 := by
    intro h0
    apply hτ
    have : S.grCross q = (mateEquiv (S.grAdj q) (S.grAdj (q + 1))).symm (S.grSigma q) := by
      rw [grSigma_eq_mateEquiv, Equiv.symm_apply_apply]
    rw [this, h0]
    exact (Equiv.symm_apply_eq _).2 (mateEquiv_zero _ _).symm
  have hσ'0 : S.sideLN q ≠ 0 := by
    intro h0
    apply hτ
    have : S.grCross q = mateEquiv (S.leftAdjN q) (S.leftAdjN (q + 1)) (S.sideLN q) :=
      ((Bicategory.mateEquiv _ _).apply_symm_apply (S.grCross q)).symm
    rw [this, h0, mateEquiv_zero]
  obtain ⟨c, hc⟩ : ∃ c : k, grιEF e = c • S.grSigma q := by
    have hcd : IsHomogeneous ((S.rhoSourceIso q).inv ≫ S.grSigma q ≫ (S.rhoTargetIso q).hom) 0 :=
      ((S.isHomogeneous_rhoSourceIso_inv q).comp ((S.isHomogeneous_grSigma q).comp
        (S.isHomogeneous_rhoTargetIso_hom q) rfl) rfl).of_eq (by ring)
    obtain ⟨g, hg⟩ := exists_incl₂_of_isHomogeneous hcd
    have hg0 : g ≠ 0 := by
      rintro rfl
      apply hσ0
      have : S.grSigma q = (S.rhoSourceIso q).hom ≫ incl₂ 0 ≫ (S.rhoTargetIso q).inv := by
        rw [← hg]; simp
      rw [this]
      change _ ≫ (incl _).map 0 ≫ _ = 0
      rw [Functor.map_zero, zero_comp, comp_zero]
    have hdim : finrank k (S.F q ≫ S.E q ⟶ S.E (q + 1) ≫ S.F (q + 1)) = 1 := by
      rw [lemHoms_EF_FE]; exact hfin
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' g hg0).1 hdim (ιEF e)
    refine ⟨c, ?_⟩
    have hs : S.grSigma q = (S.rhoSourceIso q).hom ≫ incl₂ g ≫ (S.rhoTargetIso q).inv := by
      rw [← hg]; simp
    rw [grιEF, ← hc, hs]
    change _ ≫ (incl _).map (c • g) ≫ _ = _
    rw [Functor.map_smul, Linear.smul_comp, Linear.comp_smul]
    rfl
  obtain ⟨a, ha⟩ : ∃ a : k, grπEF e = a • S.sideLN q := by
    have hcd : IsHomogeneous ((S.rhoTargetIso q).inv ≫ S.sideLN q ≫ (S.rhoSourceIso q).hom) 0 :=
      ((S.isHomogeneous_rhoTargetIso_inv q).comp ((S.isHomogeneous_sideLN q).comp
        (S.isHomogeneous_rhoSourceIso_hom q) rfl) rfl).of_eq (by ring)
    obtain ⟨g, hg⟩ := exists_incl₂_of_isHomogeneous hcd
    have hg0 : g ≠ 0 := by
      rintro rfl
      apply hσ'0
      have : S.sideLN q = (S.rhoTargetIso q).hom ≫ incl₂ 0 ≫ (S.rhoSourceIso q).inv := by
        rw [← hg]; simp
      rw [this]
      change _ ≫ (incl _).map 0 ≫ _ = 0
      rw [Functor.map_zero, zero_comp, comp_zero]
    have hdim : finrank k (S.E (q + 1) ≫ S.F (q + 1) ⟶ S.F q ≫ S.E q) = 1 := by
      rw [S.lemHoms_FE_EF (S.adjHyp q) (S.adjHyp (q + 1))]; exact hfin
    obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' g hg0).1 hdim (πEF e)
    refine ⟨a, ?_⟩
    have hs : S.sideLN q = (S.rhoTargetIso q).hom ≫ incl₂ g ≫ (S.rhoSourceIso q).inv := by
      rw [← hg]; simp
    rw [grπEF, ← ha, hs]
    change _ ≫ (incl _).map (a • g) ≫ _ = _
    rw [Functor.map_smul, Linear.smul_comp, Linear.comp_smul]
    rfl
  have hRE : grιEF e ≫ grπEF e = (c * a) • (S.grSigma q ≫ S.sideLN q) := by
    rw [hc, ha, Linear.smul_comp, Linear.comp_smul, smul_smul]
  have hEF : grπEF e ≫ grιEF e = (c * a) • (S.sideLN q ≫ S.grSigma q) := by
    rw [hc, ha, Linear.smul_comp, Linear.comp_smul, smul_smul, mul_comm a c]
  refine ⟨c * a, φ, ?_, ?_⟩
  · rw [Linear.comp_smul, ← hRE, grιEF_grπEF]
  · rw [← hEF, ← hφ]
    exact (add_comm _ _).trans (grTotalN e)

variable (S) in
/-- **CL Propositions 5.1, 5.2 for `n ≤ 0`** (relations (B2), (B5)): for `n = wt (q + 1) ≤ 0`
there is a scalar `β` with `σ ≫ β σ' = 1_{EF1_n}` and
`1_{FE1_n} = β σ'σ + ∑_{k<-n} ccomp_k ∘ ccup_k` (`compKN`). -/
theorem decompFE_beta {q : ℤ} (hn : S.wt (q + 1) ≤ 0) :
    ∃ β : k, S.grSigma q ≫ (β • S.sideLN q) = 𝟙 _ ∧
      β • (S.sideLN q ≫ S.grSigma q) +
        ∑ j ∈ Finset.range (-S.wt (q + 1)).toNat, S.compKN q j ≫ S.ccupD q j = 𝟙 _ := by
  obtain ⟨β, φ, h1, h2⟩ := S.exists_decompFE_aux hn
  refine ⟨β, h1, ?_⟩
  have hφ : ∀ j ∈ Finset.range (-S.wt (q + 1)).toNat, φ j = S.compKN q j := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    have := congrArg (· ≫ S.compKN q j) h2
    simp only [Preadditive.add_comp, Preadditive.sum_comp, Linear.smul_comp, Category.assoc,
      S.grSigma_comp_compKN, comp_zero, smul_zero, zero_add, Category.id_comp] at this
    rw [← this, Finset.sum_eq_single_of_mem j hj]
    · rw [S.ccupD_comp_compKN hj' hj', ite_eq_left rfl, Category.comp_id]
    · intro i hi hij
      rw [S.ccupD_comp_compKN hj' (Finset.mem_range.1 hi), ite_eq_right (Ne.symm hij), comp_zero]
  rw [← h2]
  congr 1
  exact Finset.sum_congr rfl fun j hj => by rw [hφ j hj]

end StrongSl2

end Categorification.TwoRep

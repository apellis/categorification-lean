/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.AdjointWeightZero
import Categorification.TwoRep.Biadjoint
import Categorification.TwoRep.WordNumerics
import Categorification.TwoRep.CoopCoherence
import Categorification.TwoRep.Duality

/-!
# Invertibility of Rouquier's maps `σ_0` and `ρ_2`, and (3.2) at the weights `0` and `-2`

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, §3, Proposition 3.9 (`prop:lradj`); the maps `σ_λ`, `ρ_λ` are those of
R. Rouquier, *2-Kac–Moody algebras*, arXiv:0812.5023v1, in the form of J. Brundan, *On the
definition of Kac–Moody 2-category*, arXiv:1501.00350v1 (`σ` is Brundan's (1.6)).

In a strong 2-representation of `sl₂` (`StrongSl2`) the rightward crossing
`σ_λ : E F 1_λ → F E 1_λ` (`StrongSl2.sigma`, `StrongSl2.grSigma`) is built from the unit of
`E 1_λ ⊣ R_λ`, the crossing and the counit of `E 1_{λ-2} ⊣ R_{λ-2}`. Rouquier's map at `λ = 0` is
`ρ_0 = σ_0`, and at `λ = 2` it is `ρ_2 = (σ_2, ε_0, ε_0 ∘ (R_0 x)) : E F 1_2 → F E 1_2 ⊕ 1_2 ⊕ 1_2`.
This file proves that both are invertible using only the numerical shadow of (3.2) at the
weights `> 0` (`StrongSl2.NumAdj`), hence unconditionally. These are exactly the
hypotheses of `adjHyp_of_wt_eq_zero` (Brundan's argument, `AdjointWeightZero.lean`), which
therefore gives (3.2) at weight `0`; the dual 2-representation (`Duality.lean`)
turns this into (3.2) at weight `-2`.

* `σ_0`: condition (3) of CL Definition 1.2 gives `E F 1_0 ≅ F E 1_0`; the space
  `Hom(E F 1_0, F E 1_0)` (in the degree of `σ_0`) is one-dimensional (CL Lemma 3.12 with
  Corollary 3.2), and `σ_0 ≠ 0` because the crossing `τ` on `E E 1_{-2}` is recovered from `σ_0`
  by a cup and a cap (`cross_eq_of_sigma`) and `τ ≠ 0` by the nilHecke relation.
* `ρ_2`: in a decomposition `E F 1_2 ≅ F E 1_2 ⊕ 1_2⟨1⟩ ⊕ 1_2⟨-1⟩`, `σ_2` is a nonzero multiple of
  the projection onto `F E 1_2`, `ε_0` vanishes on `F E 1_2` and on `1_2⟨1⟩` (degrees, and
  `Hom(F E 1_2, 1_2⟨j⟩) = 0` for `j < 3`), and on `1_2⟨1⟩` the third component is the subdiagonal
  dot entry (CL Lemma 3.6) followed by the component of `ε_0` on `1_2⟨-1⟩`. So the matrix is
  lower triangular with invertible diagonal.

## Main declarations

* `RightwardCrossing.cross_eq_of_sigma`: the crossing is recovered from the rightward crossing
  (any bicategory, only the zigzag identities are used);
* `RightwardCrossing.isIsoToSum₃_of_triangular`: a block-triangular criterion for
  `IsIsoToSum₃`;
* `StrongSl2.grSigma_ne_zero`, `StrongSl2.exists_grSigma_eq_smul_πFE`;
* `StrongSl2.isIso_sigma_of_wt_eq_zero`, `StrongSl2.isIso_grSigma_of_wt_eq_zero`,
  `StrongSl2.isIso_grSigma_zero`: `σ_0` is invertible;
* `StrongSl2.isIsoToSum₃_rho_two`, `StrongSl2.isIsoToSum₃_rhoTwo`: `ρ_2` is invertible
  (Hom categories idempotent complete, for CL Lemma 3.6);
* `StrongSl2.adjHyp_wt_zero`, `StrongSl2.adjHyp_wt_neg_two`: **CL
  Proposition 3.9 at the weights `0` and `-2`** (with shift coherence, Hom-finite
  and idempotent-complete Hom categories).
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Module
open KrullSchmidtCat (HomFinite)

universe w v u

namespace RightwardCrossing

variable {C : Type u} [Bicategory.{w, v} C] {a b c : C} {E₁ : a ⟶ b} {E₂ : b ⟶ c}
  {R₁ : b ⟶ a} {R₂ : c ⟶ b}

/-- **The crossing from the rightward crossing**: `τ = (E₁ E₂ ε₂) ∘ (E₁ σ E₂) ∘ (η₁ E₁ E₂)`,
i.e. the inverse of the double mate that defines `σ`. Only the zigzag identities of `E₁` and
`E₂` are used. -/
theorem cross_eq_of_sigma (η₁ : 𝟙 a ⟶ E₁ ≫ R₁) (ε₁ : R₁ ≫ E₁ ⟶ 𝟙 b) (η₂ : 𝟙 b ⟶ E₂ ≫ R₂)
    (ε₂ : R₂ ≫ E₂ ⟶ 𝟙 c) (τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂)
    (hZ₁ : leftZigzag η₁ ε₁ = (λ_ E₁).hom ≫ (ρ_ E₁).inv)
    (hZ₂ : leftZigzag η₂ ε₂ = (λ_ E₂).hom ≫ (ρ_ E₂).inv) :
    τ = 𝟙 _ ⊗≫ η₁ ▷ (E₁ ≫ E₂) ⊗≫ E₁ ◁ (sigma η₂ τ ε₁ ▷ E₂) ⊗≫ E₁ ◁ E₂ ◁ ε₂ ⊗≫ 𝟙 _ := by
  symm
  calc 𝟙 _ ⊗≫ η₁ ▷ (E₁ ≫ E₂) ⊗≫ E₁ ◁ (sigma η₂ τ ε₁ ▷ E₂) ⊗≫ E₁ ◁ E₂ ◁ ε₂ ⊗≫ 𝟙 _
      = 𝟙 _ ⊗≫ η₁ ▷ (E₁ ≫ E₂) ⊗≫ E₁ ◁ (sigma η₂ τ ε₁ ▷ E₂ ⊗≫ E₂ ◁ ε₂) ⊗≫ 𝟙 _ := by
        bicategory
    _ = 𝟙 _ ⊗≫ η₁ ▷ (E₁ ≫ E₂) ⊗≫ E₁ ◁ (𝟙 _ ⊗≫ R₁ ◁ τ ⊗≫ ε₁ ▷ E₂ ⊗≫ 𝟙 _) ⊗≫ 𝟙 _ := by
        rw [pitchfork_cap η₂ ε₂ τ ε₁ hZ₂]
    _ = 𝟙 _ ⊗≫ (η₁ ▷ (E₁ ≫ E₂) ≫ (E₁ ≫ R₁) ◁ τ) ⊗≫ E₁ ◁ ε₁ ▷ E₂ ⊗≫ 𝟙 _ := by
        bicategory
    _ = 𝟙 _ ⊗≫ (𝟙 a ◁ τ ≫ η₁ ▷ (E₁ ≫ E₂)) ⊗≫ E₁ ◁ ε₁ ▷ E₂ ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange]
    _ = 𝟙 _ ⊗≫ τ ⊗≫ leftZigzag η₁ ε₁ ▷ E₂ ⊗≫ 𝟙 _ := by
        rw [leftZigzag]; bicategory
    _ = τ := by
        rw [hZ₁]; bicategory

end RightwardCrossing

section Finrank

variable (k : Type*) [Field k] {D : Type*} [Category D] [Preadditive D] [Linear k D]

/-- In a one-dimensional Hom space containing an isomorphism, every nonzero morphism is an
isomorphism. -/
theorem isIso_of_finrank_eq_one {X Y : D} (e : X ≅ Y) (h : finrank k (X ⟶ Y) = 1) {f : X ⟶ Y}
    (hf : f ≠ 0) : IsIso f := by
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' f hf).1 h e.hom
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    have hX : IsZero X := by
      rw [IsZero.iff_id_eq_zero, ← e.hom_inv_id, ← hc, zero_comp]
    rw [finrank_hom_of_isZero_left k hX] at h
    exact zero_ne_one h
  refine ⟨c • e.inv, ?_, ?_⟩
  · rw [Linear.comp_smul, ← Linear.smul_comp, hc, e.hom_inv_id]
  · rw [Linear.smul_comp, ← Linear.comp_smul, hc, e.inv_hom_id]

/-- A nonzero multiple of an isomorphism is an isomorphism. -/
theorem isIso_smul {X Y : D} (f : X ⟶ Y) [IsIso f] {c : k} (hc : c ≠ 0) : IsIso (c • f) :=
  ⟨c⁻¹ • inv f, by simp [smul_smul, hc], by simp [smul_smul, hc]⟩

end Finrank

namespace RightwardCrossing

section Triangular

variable {D : Type*} [Category D] [Preadditive D]

/-- **A block-triangular criterion for `IsIsoToSum₃`.** If `X` is split by `iₖ : Zₖ ⟶ X`,
`pₖ : X ⟶ Zₖ` (`∑ pₖ ≫ iₖ = 𝟙`) and the matrix `(iₖ ≫ fⱼ)` is lower triangular with invertible
diagonal (`i₂ ≫ f₁ = i₃ ≫ f₁ = i₁ ≫ f₂ = i₃ ≫ f₂ = i₁ ≫ f₃ = 0`), then `(f₁, f₂, f₃)` is an
isomorphism onto the sum. -/
theorem isIsoToSum₃_of_triangular {X Z₁ Z₂ Z₃ Y₁ Y₂ Y₃ : D} {f₁ : X ⟶ Y₁} {f₂ : X ⟶ Y₂}
    {f₃ : X ⟶ Y₃} (i₁ : Z₁ ⟶ X) (i₂ : Z₂ ⟶ X) (i₃ : Z₃ ⟶ X) (p₁ : X ⟶ Z₁) (p₂ : X ⟶ Z₂)
    (p₃ : X ⟶ Z₃) (htot : p₁ ≫ i₁ + p₂ ≫ i₂ + p₃ ≫ i₃ = 𝟙 X)
    (h12 : i₂ ≫ f₁ = 0) (h13 : i₃ ≫ f₁ = 0) (h21 : i₁ ≫ f₂ = 0) (h23 : i₃ ≫ f₂ = 0)
    (h31 : i₁ ≫ f₃ = 0) [IsIso (i₁ ≫ f₁)] [IsIso (i₂ ≫ f₂)] [IsIso (i₃ ≫ f₃)] :
    IsIsoToSum₃ f₁ f₂ f₃ := by
  let g₁ := inv (i₁ ≫ f₁) ≫ i₁
  let g₃ := inv (i₃ ≫ f₃) ≫ i₃
  let g₂ := inv (i₂ ≫ f₂) ≫ i₂ - inv (i₂ ≫ f₂) ≫ (i₂ ≫ f₃) ≫ g₃
  have e₁ : g₁ ≫ f₁ = 𝟙 _ := by simp only [g₁, Category.assoc, IsIso.inv_hom_id]
  have e₂ : inv (i₂ ≫ f₂) ≫ i₂ ≫ f₂ = 𝟙 _ := IsIso.inv_hom_id _
  have e₃ : g₃ ≫ f₃ = 𝟙 _ := by simp only [g₃, Category.assoc, IsIso.inv_hom_id]
  have c₁ : ∀ {W : D} (h : Z₁ ⟶ W), (i₁ ≫ f₁) ≫ inv (i₁ ≫ f₁) ≫ h = h := fun h => by
    rw [IsIso.hom_inv_id_assoc]
  have c₃ : ∀ {W : D} (h : Z₃ ⟶ W), (i₃ ≫ f₃) ≫ inv (i₃ ≫ f₃) ≫ h = h := fun h => by
    rw [IsIso.hom_inv_id_assoc]
  have c₂ : ∀ {W : D} (h : Z₂ ⟶ W), (i₂ ≫ f₂) ≫ inv (i₂ ≫ f₂) ≫ h = h := fun h => by
    rw [IsIso.hom_inv_id_assoc]
  have hP : ∀ {Z : D} (i : Z ⟶ X), i ≫ (f₁ ≫ g₁ + f₂ ≫ g₂ + f₃ ≫ g₃) =
      (i ≫ f₁) ≫ g₁ + (i ≫ f₂) ≫ g₂ + (i ≫ f₃) ≫ g₃ := fun i => by
    simp only [Preadditive.comp_add, Category.assoc]
  have hP₁ : i₁ ≫ (f₁ ≫ g₁ + f₂ ≫ g₂ + f₃ ≫ g₃) = i₁ := by
    rw [hP, h21, h31, zero_comp, zero_comp, add_zero, add_zero]
    exact c₁ i₁
  have hP₂ : i₂ ≫ (f₁ ≫ g₁ + f₂ ≫ g₂ + f₃ ≫ g₃) = i₂ := by
    rw [hP, h12, zero_comp, zero_add]
    simp only [g₂, Preadditive.comp_sub, c₂]
    abel
  have hP₃ : i₃ ≫ (f₁ ≫ g₁ + f₂ ≫ g₂ + f₃ ≫ g₃) = i₃ := by
    rw [hP, h13, h23, zero_comp, zero_comp, zero_add, zero_add]
    exact c₃ i₃
  refine ⟨g₁, g₂, g₃, ?_, ⟨e₁, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, e₃⟩⟩
  · rw [← Category.id_comp (f₁ ≫ g₁ + f₂ ≫ g₂ + f₃ ≫ g₃), ← htot]
    simp only [Preadditive.add_comp, Category.assoc, hP₁, hP₂, hP₃]
  · simp only [g₁, Category.assoc, h21, comp_zero]
  · simp only [g₁, Category.assoc, h31, comp_zero]
  · simp only [g₂, g₃, Preadditive.sub_comp, Category.assoc, h12, h13, comp_zero, sub_zero]
  · simp only [g₂, g₃, Preadditive.sub_comp, Category.assoc, h23, comp_zero, sub_zero]
    exact e₂
  · simp only [g₂, g₃, Preadditive.sub_comp, Category.assoc, IsIso.inv_hom_id, Category.comp_id,
      sub_self]
  · simp only [g₃, Category.assoc, h13, comp_zero]
  · simp only [g₃, Category.assoc, h23, comp_zero]

end Triangular

end RightwardCrossing

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [GradedBicategory.ShiftCoherence B]

namespace StrongSl2

open GradedHomBicat GradedHomCat RightwardCrossing

variable (S : StrongSl2 k B)

/-- If the rightward crossing `σ_λ` vanishes, so does the crossing on `E E 1_{λ-2}`. -/
theorem grCross_eq_zero_of_grSigma_eq_zero {r : ℤ} (h : S.grSigma r = 0) : S.grCross r = 0 := by
  rw [cross_eq_of_sigma (S.grUnit r) (S.grCounit r) (S.grUnit (r + 1)) (S.grCounit (r + 1))
    (S.grCross r) (S.leftZigzag_grUnit_grCounit r) (S.leftZigzag_grUnit_grCounit (r + 1))]
  change 𝟙 _ ⊗≫ _ ⊗≫ _ ◁ (S.grSigma r ▷ _) ⊗≫ _ ⊗≫ 𝟙 _ = _
  rw [h, GradedHomBicat.zero_whiskerRight, GradedHomBicat.whiskerLeft_zero]
  simp [bicategoricalComp]

section Linear

variable [GradedBicategory.IsLinear B k]

/-- If the crossing on `E E 1_n` vanishes, then `E E 1_n = 0` (nilHecke relation
`τ ∘ (x E) - (E x) ∘ τ = 1`). -/
theorem isZero_E_E_of_grCross_eq_zero {r : ℤ} (h : S.grCross r = 0) :
    IsZero (S.E r ≫ S.E (r + 1)) := by
  have hs := S.grDotN_slide r
  rw [h, comp_zero, zero_comp, sub_zero] at hs
  refine (IsZero.iff_id_eq_zero _).2 (incl₂_injective ?_)
  change incl₂ (𝟙 (S.E r ≫ S.E (r + 1))) = (incl _).map 0
  rw [incl₂_id, Functor.map_zero]
  exact hs.symm

variable [∀ a b : B, HomFinite k (a ⟶ b)]

/-- **`σ_λ ≠ 0`** at a weight `λ = wt (r + 1) ≥ 0` with `1_{λ+2} ≠ 0`, given the numerical
shadow of (3.2) at the weights `> λ`: the crossing on `E E 1_{λ-2}` is nonzero since
`End^{-2}(E E 1_{λ-2})` is one-dimensional (CL Corollary 3.2). -/
theorem grSigma_ne_zero {r : ℤ} (hn : 0 ≤ S.wt (r + 1)) (hyp : ∀ r', r + 1 < r' → S.NumAdj r')
    (h : ¬ IsZero (𝟙 (S.obj (r + 1 + 1)))) : S.grSigma r ≠ 0 := by
  intro hσ
  have hz := S.isZero_E_E_of_grCross_eq_zero (S.grCross_eq_zero_of_grSigma_eq_zero hσ)
  have h1 := S.cor0_zero_of_numAdj hn hyp (r := r) (by omega) h
  rw [finrank_hom_of_isZero_left k hz] at h1
  exact zero_ne_one h1

/-- The rightward crossing `σ_λ` in `B` is nonzero (same hypotheses as `grSigma_ne_zero`). -/
theorem sigma_ne_zero {r : ℤ} (hn : 0 ≤ S.wt (r + 1)) (hyp : ∀ r', r + 1 < r' → S.NumAdj r')
    (h : ¬ IsZero (𝟙 (S.obj (r + 1 + 1)))) : S.sigma r ≠ 0 := by
  intro hσ
  apply S.grSigma_ne_zero hn hyp h
  rw [grSigma_eq, hσ, of₂_zero]

/-- The shape of `σ_λ` in `B`: `R r ≫ E r ≅ (F r ≫ E r)⟨n+1⟩` and
`(E (r+1) ≫ R (r+1))⟨-2⟩ ≅ (E (r+1) ≫ F (r+1))⟨n+1⟩` (`n = wt r`), so that the degree `-2`
2-morphisms `R r ≫ E r ⟶ E (r+1) ≫ R (r+1)` are the degree `0` 2-morphisms
`E F 1_λ ⟶ F E 1_λ`. -/
def sigmaTargetIso (r : ℤ) :
    (S.E (r + 1) ≫ (S.F (r + 1))⟦S.n₀ + 2 * (r + 1) + 1⟧)⟦(-2 : ℤ)⟧ ≅
      (S.E (r + 1) ≫ S.F (r + 1))⟦S.n₀ + 2 * r + 1⟧ :=
  (shiftFunctor _ (-2 : ℤ)).mapIso (whiskerLeftShiftIso _ _ _) ≪≫
    ((shiftFunctorAdd' _ (S.n₀ + 2 * (r + 1) + 1) (-2) (S.n₀ + 2 * r + 1) (by ring)).app _).symm

omit [∀ a b : B, HomFinite k (a ⟶ b)] [GradedBicategory.ShiftCoherence B] in
/-- `Hom(R r ≫ E r, (E (r+1) ≫ R (r+1))⟨-2⟩) ≅ Hom(E F 1_λ, F E 1_λ)` on dimensions. -/
theorem finrank_sigma_space (r : ℤ) :
    finrank k ((S.F r)⟦S.n₀ + 2 * r + 1⟧ ≫ S.E r ⟶
        (S.E (r + 1) ≫ (S.F (r + 1))⟦S.n₀ + 2 * (r + 1) + 1⟧)⟦(-2 : ℤ)⟧) =
      finrank k (S.F r ≫ S.E r ⟶ S.E (r + 1) ≫ S.F (r + 1)) := by
  rw [finrank_hom_congr k (whiskerRightShiftIso _ _ _) (S.sigmaTargetIso r),
    finrank_hom_shift]

/-- **`σ_0` is invertible** (Rouquier's `ρ_0`; cl36h Prop R0): at the object `s + 1` of weight
`0`, given the numerical shadow of (3.2) at the weights `> 0`, the rightward crossing
`σ_0 : R_{-2} E_{-2} → (E_0 R_0)⟨-2⟩` is an isomorphism of `B`. -/
theorem isIso_sigma_of_wt_eq_zero {s : ℤ} (h0 : S.wt (s + 1) = 0)
    (hyp : ∀ r', s + 1 < r' → S.NumAdj r') : IsIso (S.sigma s) := by
  have h0' : S.n₀ + 2 * (s + 1) = 0 := h0
  -- condition (3) at weight `0`: `E F 1_0 ≅ F E 1_0`
  obtain ⟨θ⟩ := S.EF s (by omega)
  have hZ : IsZero (qsum (C := S.obj (s + 1) ⟶ S.obj (s + 1)) 1 (S.n₀ + 2 * (s + 1)).toNat
      (𝟙 _)) := by
    rw [h0']
    exact isZero_zero _
  let θ₀ : S.F s ≫ S.E s ≅ S.E (s + 1) ≫ S.F (s + 1) := θ ≪≫ (isoBiprodZero hZ).symm
  -- the corresponding isomorphism in the degree of `σ_0`
  let Θ : (S.F s)⟦S.n₀ + 2 * s + 1⟧ ≫ S.E s ≅
      (S.E (s + 1) ≫ (S.F (s + 1))⟦S.n₀ + 2 * (s + 1) + 1⟧)⟦(-2 : ℤ)⟧ :=
    whiskerRightShiftIso _ _ _ ≪≫ (shiftFunctor _ _).mapIso θ₀ ≪≫ (S.sigmaTargetIso s).symm
  by_cases hX : IsZero ((S.F s)⟦S.n₀ + 2 * s + 1⟧ ≫ S.E s)
  · have hY := hX.of_iso Θ.symm
    exact ⟨0, hX.eq_of_src _ _, hY.eq_of_src _ _⟩
  have h2 : ¬ IsZero (𝟙 (S.obj (s + 1 + 1))) := by
    intro h2
    apply hX
    refine IsZero.of_iso ?_ Θ
    refine (shiftFunctor _ _).map_isZero ?_
    exact isZero_comp_left (S.isZero_E_of_right h2) _
  have hσ := S.sigma_ne_zero (by omega) hyp h2
  have hdim : finrank k (ShiftedHom ((S.F s)⟦S.n₀ + 2 * s + 1⟧ ≫ S.E s)
      (S.E (s + 1) ≫ (S.F (s + 1))⟦S.n₀ + 2 * (s + 1) + 1⟧) (-2 : ℤ)) = 1 := by
    change finrank k (_ ⟶ _) = 1
    rw [finrank_sigma_space, lemHoms_EF_FE]
    exact S.cor0_zero_of_numAdj (r₀ := s + 1) (by omega) hyp (by omega) h2
  exact isIso_of_finrank_eq_one k Θ hdim hσ

/-- **`σ_0` is invertible in the graded-Hom bicategory** (the form of the hypothesis of
`adjHyp_of_wt_eq_zero`, `adjHyp_of_wt_eq_neg_two`). -/
theorem isIso_grSigma_of_wt_eq_zero {s : ℤ} (h0 : S.wt (s + 1) = 0)
    (hyp : ∀ r', s + 1 < r' → S.NumAdj r') : IsIso (S.grSigma s) := by
  have := S.isIso_sigma_of_wt_eq_zero h0 hyp
  exact S.isIso_grSigma s

/-- **`σ_0` is invertible.** -/
theorem isIso_grSigma_zero (S : StrongSl2 k B) {s : ℤ} (h0 : S.wt (s + 1) = 0) :
    IsIso (S.grSigma s) :=
  S.isIso_grSigma_of_wt_eq_zero h0 fun r' _ => S.numAdj r'


/-! ## `ρ_2` -/

/-- The left whiskering of `E F 1_λ`'s unshifting: `R r ≫ E r ≅ F r ≫ E r` in the graded-Hom
bicategory, homogeneous of degree `n + 1` (`n = wt r`). -/
def rhoSourceIso (r : ℤ) : S.grR r ≫ S.grE r ≅ of₁ (S.F r ≫ S.E r) :=
  whiskerRightIso (shiftIso₁ (S.F r) _) (S.grE r)

/-- `E (r+1) ≫ R (r+1) ≅ E (r+1) ≫ F (r+1)` in the graded-Hom bicategory. -/
def rhoTargetIso (r : ℤ) : S.grE (r + 1) ≫ S.grR (r + 1) ≅ of₁ (S.E (r + 1) ≫ S.F (r + 1)) :=
  whiskerLeftIso (S.grE (r + 1)) (shiftIso₁ (S.F (r + 1)) _)

omit [GradedBicategory.IsLinear B k] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem isHomogeneous_rhoSourceIso_inv (r : ℤ) :
    IsHomogeneous (S.rhoSourceIso r).inv (-(S.n₀ + 2 * r + 1)) :=
  isHomogeneous_whiskerRight (shiftIso₁_inv_isHomogeneous _ _) _

omit [GradedBicategory.IsLinear B k] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem isHomogeneous_rhoSourceIso_hom (r : ℤ) :
    IsHomogeneous (S.rhoSourceIso r).hom (S.n₀ + 2 * r + 1) :=
  isHomogeneous_whiskerRight (shiftIso₁_hom_isHomogeneous _ _) _

omit [GradedBicategory.IsLinear B k] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem isHomogeneous_rhoTargetIso_hom (r : ℤ) :
    IsHomogeneous (S.rhoTargetIso r).hom (S.n₀ + 2 * (r + 1) + 1) :=
  isHomogeneous_whiskerLeft _ (shiftIso₁_hom_isHomogeneous _ _)

omit [GradedBicategory.IsLinear B k] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem isHomogeneous_rhoTargetIso_inv (r : ℤ) :
    IsHomogeneous (S.rhoTargetIso r).inv (-(S.n₀ + 2 * (r + 1) + 1)) :=
  isHomogeneous_whiskerLeft _ (shiftIso₁_inv_isHomogeneous _ _)

/-- **`σ_λ` is a nonzero multiple of the projection onto `F E 1_λ`** (cl36h Prop R1, (F1)–(F4)):
at a weight `λ = wt (r + 1) ≥ 0` with `1_{λ+2} ≠ 0`, given the numerical shadow of (3.2) at the
weights `> λ`, for every decomposition `E F 1_λ ≅ F E 1_λ ⊕ ⊕_{[λ]} 1_λ` the rightward crossing is
`c` times the projection onto `F E 1_λ`, with `c ≠ 0`. -/
theorem exists_grSigma_eq_smul_πFE {r : ℤ} (hn : 0 ≤ S.wt (r + 1))
    (hyp : ∀ r', r + 1 < r' → S.NumAdj r') (h : ¬ IsZero (𝟙 (S.obj (r + 1 + 1))))
    (e : S.EFDecomp r) :
    ∃ c : k, c ≠ 0 ∧ S.grSigma r =
      c • ((S.rhoSourceIso r).hom ≫ incl₂ (πFE e) ≫ (S.rhoTargetIso r).inv) := by
  have hφ : IsHomogeneous ((S.rhoSourceIso r).inv ≫ S.grSigma r ≫ (S.rhoTargetIso r).hom) 0 :=
    (S.isHomogeneous_rhoSourceIso_inv r).comp ((S.isHomogeneous_grSigma r).comp
      (S.isHomogeneous_rhoTargetIso_hom r) rfl) (by ring)
  obtain ⟨g, hg⟩ := exists_incl₂_of_isHomogeneous hφ
  have hdim : finrank k (S.F r ≫ S.E r ⟶ S.E (r + 1) ≫ S.F (r + 1)) = 1 := by
    rw [lemHoms_EF_FE]
    exact S.cor0_zero_of_numAdj (r₀ := r + 1) hn hyp (by omega) h
  have hπ : πFE e ≠ 0 := by
    intro h0
    have hid : ιFE e ≫ πFE e = 𝟙 _ := by simp [ιFE, πFE]
    rw [h0, comp_zero] at hid
    have hz : IsZero (S.E (r + 1) ≫ S.F (r + 1)) := (IsZero.iff_id_eq_zero _).2 hid.symm
    rw [finrank_hom_of_isZero_right k _ hz] at hdim
    exact zero_ne_one hdim
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hπ).1 hdim g
  have hg0 : g ≠ 0 := by
    rintro rfl
    apply S.grSigma_ne_zero hn hyp h
    have : S.grSigma r = (S.rhoSourceIso r).hom ≫ incl₂ 0 ≫ (S.rhoTargetIso r).inv := by
      rw [← hg]; simp
    rw [this]
    change _ ≫ (incl _).map 0 ≫ _ = 0
    rw [Functor.map_zero, zero_comp, comp_zero]
  refine ⟨c, fun hc0 => hg0 (by rw [← hc, hc0, zero_smul]), ?_⟩
  have : S.grSigma r = (S.rhoSourceIso r).hom ≫ incl₂ g ≫ (S.rhoTargetIso r).inv := by
    rw [← hg]; simp
  rw [this, ← hc]
  change _ ≫ (incl _).map (c • πFE e) ≫ _ = _
  rw [Functor.map_smul, Linear.smul_comp, Linear.comp_smul]
  rfl

omit [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [GradedBicategory.IsLinear B k] in
/-- A homogeneous 2-morphism of the graded-Hom bicategory whose degree component lies in a zero
Hom space is zero. -/
theorem _root_.Categorification.TwoRep.GradedHomBicat.eq_zero_of_isHomogeneous {a b : B}
    {f g : a ⟶ b} {φ : of₁ f ⟶ of₁ g} {d : ℤ} (hφ : IsHomogeneous φ d)
    (h : finrank k (f ⟶ g⟦d⟧) = 0) : φ = 0 := by
  obtain ⟨c, rfl⟩ := hφ
  have : Subsingleton (f ⟶ g⟦d⟧) := Module.finrank_zero_iff.1 h
  rw [Subsingleton.elim c 0]
  exact homOf_zero d

omit [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [GradedBicategory.IsLinear B k] [∀ a b : B, HomFinite k (a ⟶ b)] in
/-- A nonzero homogeneous 2-morphism of the graded-Hom bicategory whose degree component lies in a
one-dimensional Hom space containing an isomorphism is an isomorphism. -/
theorem _root_.Categorification.TwoRep.GradedHomBicat.isIso_of_isHomogeneous {a b : B}
    {f g : a ⟶ b} {φ : of₁ f ⟶ of₁ g} {d : ℤ} (hφ : IsHomogeneous φ d) (hne : φ ≠ 0)
    (e : f ≅ g⟦d⟧) (h : finrank k (f ⟶ g⟦d⟧) = 1) : IsIso φ := by
  obtain ⟨c, rfl⟩ := hφ
  have hc : (c : f ⟶ g⟦d⟧) ≠ 0 := fun h0 => hne (by
    change homOf d c = 0
    rw [show c = 0 from h0]
    exact homOf_zero d)
  have : IsIso (c : f ⟶ g⟦d⟧) := isIso_of_finrank_eq_one k e h hc
  exact isIso_homOf d c

omit [GradedBicategory.IsLinear B k] [∀ a b : B, HomFinite k (a ⟶ b)] in
theorem grCounit_ne_zero {r : ℤ} (h : ¬ IsZero (S.E r)) : S.grCounit r ≠ 0 := by
  intro h0
  have hz := S.leftZigzag_grUnit_grCounit r
  rw [h0, leftZigzag, GradedHomBicat.whiskerLeft_zero] at hz
  simp only [bicategoricalComp, comp_zero] at hz
  apply h
  refine (IsZero.iff_id_eq_zero _).2 (incl₂_injective ?_)
  change incl₂ (𝟙 (S.E r)) = (incl _).map 0
  rw [incl₂_id, Functor.map_zero]
  have e : 𝟙 (S.grE r) = (λ_ (S.grE r)).inv ≫ ((λ_ (S.grE r)).hom ≫ (ρ_ (S.grE r)).inv) ≫
      (ρ_ (S.grE r)).hom := by simp
  rw [← hz, zero_comp, comp_zero] at e
  exact e

omit [GradedBicategory.ShiftCoherence B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, HomFinite k (a ⟶ b)] in
/-- The numerical shadow of `finrank_FE_one`: `dim Hom(F E 1_n, 1_n ⟨l⟩) =
dim Hom(E 1_n, E 1_n ⟨l - n - 1⟩)`, given `NumAdj` at `n`. -/
theorem finrank_FE_one_of_numAdj {r : ℤ} (h : S.NumAdj r) (l : ℤ) :
    finrank k (S.E r ≫ S.F r ⟶ (𝟙 (S.obj r))⟦l⟧) =
      finrank k (S.E r ⟶ (S.E r)⟦l + -(S.wt r + 1)⟧) := by
  rw [h.left (.word (.E r)) (.shift l (.word (.id r))), finrank_hom_congr_right k _
      (idShiftCompShiftIso (p := l) (q := -(S.wt r + 1)) (s := l + -(S.wt r + 1)) (S.E r)
        (by ring))]

/-- **`ρ_2` is invertible** (cl36h Prop R1 at `λ = 2`): at the object `s + 1` of weight `0`,
given the numerical shadow of (3.2) at the weights `> 0`, the map
`ρ_2 = (σ_2, ε_0, ε_0 ∘ (R_0 x)) : R_0 E_0 → E_2 R_2 ⊕ 1_2 ⊕ 1_2` is an isomorphism of the
graded-Hom bicategory (in the form of the hypothesis of `adjHyp_of_wt_eq_zero`). The proof is
the block-triangular argument: in a decomposition `E F 1_2 ≅ F E 1_2 ⊕ 1_2⟨1⟩ ⊕ 1_2⟨-1⟩`, `σ_2` is a
nonzero multiple of the projection onto `F E 1_2` (`exists_grSigma_eq_smul_πFE`), `ε_0` is a nonzero
multiple of the projection onto `1_2⟨-1⟩` (degrees and `Hom(F E 1_2, 1_2⟨j⟩) = 0` for `j < 3`), and
`ε_0 ∘ (R_0 x)` restricted to `1_2⟨1⟩` is the subdiagonal dot entry times that multiple, nonzero by
CL Lemma 3.6 (`lemXind_of_numAdj`). -/
theorem isIsoToSum₃_rho_two [∀ a b : B, IsIdempotentComplete (a ⟶ b)] {s : ℤ}
    (h0 : S.wt (s + 1) = 0) (hyp : ∀ r', s + 1 < r' → S.NumAdj r') :
    IsIsoToSum₃ (S.grSigma (s + 1)) (S.grCounit (s + 1))
      (S.grR (s + 1) ◁ S.grDot (s + 1) ≫ S.grCounit (s + 1)) := by
  have hw1 : S.wt (s + 1 + 1) = 2 := by rw [S.wt_add_one, h0]; norm_num
  have ha : S.n₀ + 2 * (s + 1) + 1 = 1 := by
    have : S.wt (s + 1) = S.n₀ + 2 * (s + 1) := rfl
    omega
  by_cases h2 : IsZero (𝟙 (S.obj (s + 1 + 1)))
  · -- everything is zero
    have hz : ∀ {c : B} (f : S.obj (s + 1 + 1) ⟶ c), IsZero (of₁ f) := fun f =>
      (incl _).map_isZero (isZero_of_isZero_id_src h2 f)
    have hX : IsZero (S.grR (s + 1) ≫ S.grE (s + 1)) := hz _
    have hY₁ : IsZero (S.grE (s + 1 + 1) ≫ S.grR (s + 1 + 1)) := hz _
    have hY₂ : IsZero (𝟙 (of (S.obj (s + 1 + 1)))) := hz _
    refine ⟨0, 0, 0, hX.eq_of_src _ _, ⟨hY₁.eq_of_src _ _, hY₁.eq_of_src _ _, hY₁.eq_of_src _ _⟩,
      ⟨hY₂.eq_of_src _ _, hY₂.eq_of_src _ _, hY₂.eq_of_src _ _⟩,
      ⟨hY₂.eq_of_src _ _, hY₂.eq_of_src _ _, hY₂.eq_of_src _ _⟩⟩
  obtain ⟨e⟩ := S.exists_EFDecomp (r := s + 1) (by omega)
  have hT : (S.wt (s + 1 + 1)).toNat = 2 := by rw [hw1]; rfl
  set ψ := S.rhoSourceIso (s + 1) with hψ
  -- the decomposition
  let i₁ := incl₂ (ιFE e) ≫ ψ.inv
  let i₂ := incl₂ (ι e 1) ≫ ψ.inv
  let i₃ := incl₂ (ι e 0) ≫ ψ.inv
  let p₁ := ψ.hom ≫ incl₂ (πFE e)
  let p₂ := ψ.hom ≫ incl₂ (π e 1)
  let p₃ := ψ.hom ≫ incl₂ (π e 0)
  have htotB := total e
  rw [hT, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    at htotB
  have hadd : ∀ {f g : S.obj (s + 1 + 1) ⟶ S.obj (s + 1 + 1)} (x y : f ⟶ g),
      incl₂ (x + y) = incl₂ x + incl₂ y := fun x y => (incl _).map_add
  have htot' : incl₂ (πFE e) ≫ incl₂ (ιFE e) + incl₂ (π e 1) ≫ incl₂ (ι e 1) +
      incl₂ (π e 0) ≫ incl₂ (ι e 0) = 𝟙 _ := by
    rw [← incl₂_id, ← htotB, hadd, hadd, incl₂_comp, incl₂_comp, incl₂_comp]
    abel
  have htot : p₁ ≫ i₁ + p₂ ≫ i₂ + p₃ ≫ i₃ = 𝟙 _ := by
    calc p₁ ≫ i₁ + p₂ ≫ i₂ + p₃ ≫ i₃ = ψ.hom ≫ (incl₂ (πFE e) ≫ incl₂ (ιFE e) +
          incl₂ (π e 1) ≫ incl₂ (ι e 1) + incl₂ (π e 0) ≫ incl₂ (ι e 0)) ≫ ψ.inv := by
          simp only [p₁, p₂, p₃, i₁, i₂, i₃, Preadditive.add_comp, Preadditive.comp_add,
            Category.assoc]
      _ = 𝟙 _ := by rw [htot', Category.id_comp, Iso.hom_inv_id]
  have hιπFE : ∀ j, ι e j ≫ πFE e = 0 := fun j => by simp [ι, πFE]
  -- the column of `σ_2`
  have hσ : i₂ ≫ S.grSigma (s + 1) = 0 ∧ i₃ ≫ S.grSigma (s + 1) = 0 ∧
      IsIso (i₁ ≫ S.grSigma (s + 1)) := by
    by_cases h3 : IsZero (𝟙 (S.obj (s + 1 + 1 + 1)))
    · have hZ : IsZero (of₁ (S.E (s + 1 + 1) ≫ S.F (s + 1 + 1))) :=
        (incl _).map_isZero (isZero_comp_left (S.isZero_E_of_right h3) _)
      have hY : IsZero (S.grE (s + 1 + 1) ≫ S.grR (s + 1 + 1)) :=
        (incl _).map_isZero (isZero_comp_left (S.isZero_E_of_right h3) _)
      exact ⟨hY.eq_of_tgt _ _, hY.eq_of_tgt _ _, ⟨0, hZ.eq_of_src _ _, hY.eq_of_src _ _⟩⟩
    obtain ⟨c, hc0, hc⟩ := S.exists_grSigma_eq_smul_πFE (r := s + 1) (by omega)
      (fun r' hr' => hyp r' (by omega)) h3 e
    have key : ∀ (W : of (S.obj (s + 1 + 1)) ⟶ of (S.obj (s + 1 + 1))) (j : W ⟶ _),
        (j ≫ ψ.inv) ≫ S.grSigma (s + 1) =
          c • ((j ≫ incl₂ (πFE e)) ≫ (S.rhoTargetIso (s + 1)).inv) := by
      intro W j
      rw [hc, Linear.comp_smul]
      simp
    refine ⟨?_, ?_, ?_⟩
    · rw [key, ← incl₂_comp, hιπFE]; change c • ((incl _).map 0 ≫ _) = 0; simp
    · rw [key, ← incl₂_comp, hιπFE]; change c • ((incl _).map 0 ≫ _) = 0; simp
    · rw [key, ← incl₂_comp, show ιFE e ≫ πFE e = 𝟙 _ by simp [ιFE, πFE], incl₂_id,
        Category.id_comp]
      exact ⟨c⁻¹ • (S.rhoTargetIso (s + 1)).hom, by simp [smul_smul, hc0], by simp [smul_smul, hc0]⟩
  -- the column of `ε_0`
  have hn : 0 ≤ S.wt (s + 1) := by omega
  have hψi : IsHomogeneous ψ.inv (-1) := (S.isHomogeneous_rhoSourceIso_inv (s + 1)).of_eq (by omega)
  have hFE : ∀ l : ℤ, l < 3 →
      finrank k (S.E (s + 1 + 1) ≫ S.F (s + 1 + 1) ⟶ (𝟙 (S.obj (s + 1 + 1)))⟦l⟧) = 0 := by
    intro l hl
    rw [S.finrank_FE_one_of_numAdj (hyp _ (by omega)) l]
    exact S.lem1_neg_of_numAdj hn hyp (s + 1 + 1) (by omega) _ (by omega)
  have hos : ∀ (j : ℕ) (d : ℤ), finrank k (S.oneShift (s + 1) j ⟶ (𝟙 (S.obj (s + 1 + 1)))⟦d⟧) =
      finrank k (𝟙 (S.obj (s + 1 + 1)) ⟶ (𝟙 (S.obj (s + 1 + 1)))⟦d - (1 - 2 * (j : ℤ))⟧) := by
    intro j d
    rw [oneShift, hT, finrank_hom_shift_shift k _ _ (c := d - (1 - 2 * (j : ℤ))) (by push_cast; ring)]
  have hi₁ : IsHomogeneous i₁ (-1) := (isHomogeneous_incl₂ _).comp hψi (by ring)
  have hi₂ : IsHomogeneous i₂ (-1) := (isHomogeneous_incl₂ _).comp hψi (by ring)
  have hi₃ : IsHomogeneous i₃ (-1) := (isHomogeneous_incl₂ _).comp hψi (by ring)
  have h21 : i₁ ≫ S.grCounit (s + 1) = 0 :=
    GradedHomBicat.eq_zero_of_isHomogeneous (d := -1) (hi₁.comp (isHomogeneous_incl₂ _) (by ring))
      (hFE _ (by norm_num))
  have h23 : i₃ ≫ S.grCounit (s + 1) = 0 :=
    GradedHomBicat.eq_zero_of_isHomogeneous (d := -1) (hi₃.comp (isHomogeneous_incl₂ _) (by ring))
      (by rw [hos]; exact S.hom_neg _ _ (by norm_num))
  have hE : ¬ IsZero (S.E (s + 1)) := fun hz => by
    have := S.lem1_zero_of_numAdj (r₀ := s + 1) hn hyp le_rfl h2
    rw [finrank_hom_of_isZero_left k hz] at this
    exact zero_ne_one this
  have h22 : IsIso (i₂ ≫ S.grCounit (s + 1)) := by
    refine GradedHomBicat.isIso_of_isHomogeneous (k := k) (d := -1)
      (hi₂.comp (isHomogeneous_incl₂ _) (by ring))
      ?_ (eqToIso (by simp only [oneShift, hT]; norm_num)) ?_
    · intro h0
      apply S.grCounit_ne_zero hE
      rw [← Category.id_comp (S.grCounit (s + 1)), ← htot]
      simp only [Preadditive.add_comp, Category.assoc]
      simp only [h21, h0, h23, comp_zero, add_zero]
    · rw [hos, finrank_hom_shift_zero k _ _ (by norm_num)]
      exact S.hom_zero _ h2
  -- the column of `ε_0 ∘ (R_0 x)`
  have hdot : IsHomogeneous (S.grR (s + 1) ◁ S.grDot (s + 1)) 2 :=
    isHomogeneous_whiskerLeft _ (isHomogeneous_of₂ _ _)
  have h31 : i₁ ≫ (S.grR (s + 1) ◁ S.grDot (s + 1) ≫ S.grCounit (s + 1)) = 0 :=
    GradedHomBicat.eq_zero_of_isHomogeneous (d := 1)
      (hi₁.comp (hdot.comp (isHomogeneous_incl₂ _) (by ring : (0 : ℤ) + 2 = 2))
        (by ring : (2 : ℤ) + -1 = 1)) (hFE _ (by norm_num))
  have hx : ψ.inv ≫ S.grR (s + 1) ◁ S.grDot (s + 1) =
      of₁ (S.F (s + 1)) ◁ S.grDot (s + 1) ≫ ψ.inv := by
    simp only [ψ, rhoSourceIso, whiskerRightIso_inv]
    exact (whisker_exchange _ _).symm
  have h21' : incl₂ (ιFE e) ≫ ψ.inv ≫ S.grCounit (s + 1) = 0 := by
    rw [← Category.assoc]; exact h21
  have h23' : incl₂ (ι e 0) ≫ ψ.inv ≫ S.grCounit (s + 1) = 0 := by
    rw [← Category.assoc]; exact h23
  have hM33 : i₃ ≫ (S.grR (s + 1) ◁ S.grDot (s + 1) ≫ S.grCounit (s + 1)) =
      (incl₂ (ι e 0) ≫ of₁ (S.F (s + 1)) ◁ S.grDot (s + 1) ≫ incl₂ (π e 1)) ≫
        (i₂ ≫ S.grCounit (s + 1)) := by
    calc i₃ ≫ (S.grR (s + 1) ◁ S.grDot (s + 1) ≫ S.grCounit (s + 1))
        = incl₂ (ι e 0) ≫ (ψ.inv ≫ S.grR (s + 1) ◁ S.grDot (s + 1)) ≫ S.grCounit (s + 1) := by
          simp only [i₃, Category.assoc]
      _ = incl₂ (ι e 0) ≫ of₁ (S.F (s + 1)) ◁ S.grDot (s + 1) ≫
            (incl₂ (πFE e) ≫ incl₂ (ιFE e) + incl₂ (π e 1) ≫ incl₂ (ι e 1) +
              incl₂ (π e 0) ≫ incl₂ (ι e 0)) ≫ ψ.inv ≫ S.grCounit (s + 1) := by
          rw [hx, htot']
          simp only [Category.assoc]
          erw [Category.id_comp]
      _ = _ := by
          simp only [Preadditive.add_comp, Category.assoc, h21', h23',
            comp_zero, add_zero, zero_add, i₂]
  have hent : incl₂ (ι e 0) ≫ of₁ (S.F (s + 1)) ◁ S.grDot (s + 1) ≫ incl₂ (π e 1) =
      of₂ 2 (entry e 0 1) := by
    rw [whiskerLeft_of₂, incl₂_eq_of₂, incl₂_eq_of₂,
      of₂_comp_of₂ (shWhiskerLeft (S.F (s + 1)) (S.dot (s + 1)))
        (ShiftedHom.mk₀ (0 : ℤ) rfl (π e 1)) (by norm_num : (0 : ℤ) + 2 = 2),
      of₂_comp_of₂ _ _ (by norm_num : (2 : ℤ) + 0 = 2), ShiftedHom.comp_mk₀,
      ShiftedHom.mk₀_comp]
    rfl
  have hD : IsIso (entry e 0 1) :=
    lemXind_of_numAdj (r := s) hn hyp h2 e 0 (by rw [hT]; norm_num)
  have h33 : IsIso (i₃ ≫ (S.grR (s + 1) ◁ S.grDot (s + 1) ≫ S.grCounit (s + 1))) := by
    rw [hM33, hent]
    have := isIso_of₂ 2 (entry e 0 1)
    infer_instance
  obtain ⟨h12, h13, h11⟩ := hσ
  exact isIsoToSum₃_of_triangular i₁ i₂ i₃ p₁ p₂ p₃ htot h12 h13 h21 h23 h31

/-- **`ρ_2` is invertible.** -/
theorem isIsoToSum₃_rhoTwo [∀ a b : B, IsIdempotentComplete (a ⟶ b)] (S : StrongSl2 k B)
    {s : ℤ} (h0 : S.wt (s + 1) = 0) :
    IsIsoToSum₃ (S.grSigma (s + 1)) (S.grCounit (s + 1))
      (S.grR (s + 1) ◁ S.grDot (s + 1) ≫ S.grCounit (s + 1)) :=
  S.isIsoToSum₃_rho_two h0 fun r' _ => S.numAdj r'

/-- **CL Proposition 3.9 at weight `0`**: `(E 1_0)_L ≅ 1_0 F ⟨-1⟩`. The inputs of
Brundan's argument (`adjHyp_of_wt_eq_zero`) are supplied by `isIso_grSigma_of_wt_eq_zero`
(`σ_0`), `isIsoToSum₃_rho_two` (`ρ_2`) and CL Lemma 3.1 (`End(E 1_0) = k`), all from the
numerical shadow of (3.2) at the weights `> 0` (`numAdj`). -/
theorem adjHyp_wt_zero [∀ a b : B, IsIdempotentComplete (a ⟶ b)] (S : StrongSl2 k B)
    {r : ℤ} (h0 : S.wt r = 0) : S.AdjHyp r := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by ring⟩
  by_cases h2 : IsZero (𝟙 (S.obj (s + 1 + 1)))
  · exact S.adjHyp_of_isZero (Or.inr h2)
  have hyp : ∀ r', s + 1 < r' → S.NumAdj r' := fun r' _ => S.numAdj r'
  exact S.adjHyp_of_wt_eq_zero h0 (S.isIso_grSigma_of_wt_eq_zero (s := s) h0 hyp)
    (S.isIsoToSum₃_rho_two h0 hyp) (S.lem1_zero_of_numAdj (r₀ := s + 1) (by omega) hyp le_rfl h2)

/-- **CL Proposition 3.9 at weight `-2`**: `(E 1_{-2})_L ≅ 1_{-2} F ⟨1⟩`, by the
weight-`0` case applied to the dual 2-representation `S.dual` on the bidual `Bᶜᵒᵒᵖ`
(`dual_adjHyp_iff`: (3.2) at `μ` in the dual is (3.2) at `-μ-2`). -/
theorem adjHyp_wt_neg_two [∀ a b : B, IsIdempotentComplete (a ⟶ b)]
    (S : StrongSl2 k B) {r : ℤ} (h2 : S.wt r = -2) : S.AdjHyp r := by
  have h := S.dual.adjHyp_wt_zero (r := -(r + 1)) (by
    rw [dual_wt, show -(-(r + 1)) = r + 1 by ring, S.wt_add_one, h2]; norm_num)
  rwa [dual_adjHyp_iff, show -(-(r + 1) + 1) = r by ring] at h

end Linear

end StrongSl2

end Categorification.TwoRep

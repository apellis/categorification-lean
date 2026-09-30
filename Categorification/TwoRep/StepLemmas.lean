/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.ShiftInterchange
import Categorification.TwoRep.Biadjoint
import Categorification.TwoRep.KrullSchmidt

/-!
# Whiskering by `E 1_n` at the induction step (repair of CL Lemma 3.6, part I)

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, §3.3, proof of Lemma 3.6 (`lem:Xind`). CL's proof uses that `F E 1_n` has no
direct summand `1_n ⟨l⟩` ("the space of inclusions `Hom(1_n⟨l⟩, F E 1_n)` [...] is zero"), which
is false as stated for `l ≤ -n-1` (the unit of `E 1_n ⊣ 1_n F ⟨n+1⟩` is such an inclusion), and
whose correct proof through the projections (`Biadjoint.not_retract_one_FE`) needs the adjoint
induction hypothesis (3.2) *at* the weight `n` — circular at the induction step. This file gives
the non-circular replacements, at the induction step `n = wt (r + 1) ≥ 0` with (3.2) assumed only
for the weights `m > n`:

* `lemA` (**Lemma A**): for every endomorphism `f : E 1_{n-2} → E 1_{n-2} ⟨m⟩` of negative degree
  `m < 0`, the whiskering `E 1_n f : E E 1_{n-2} → E E 1_{n-2} ⟨m⟩` vanishes. Proof: `E 1_n f`
  commutes with the dot `x_L` on the `E 1_n` strand (the interchange law for shifted 2-morphisms,
  `shWhisker_exchange`); `τ ∘ E 1_n f` has degree `m - 2 < -2`, hence vanishes by Corollary 3.2
  at the weight `n - 2` (`cor0_neg`, available at the step); the nilHecke relation
  `r · 1 = τ x_L - x_R τ` then gives `r · E 1_n f = τ (x_L ∘ E 1_n f) - x_R (τ ∘ E 1_n f) =
  (τ ∘ E 1_n f) x_L = 0`.
* `not_retract_one_FE_step` (**Corollary B**): if `1_n ≠ 0` then `F E 1_n` has no direct summand
  `1_n ⟨l⟩`, for any `l`. Proof: an inclusion `1_n⟨l⟩ → F E 1_n` forces `l ≤ -n-1` (Lemma 3.1);
  `1_n⟨l⟩` is then a summand of `E F 1_n = E 1_{n-2} F 1_{n-2}`, and the projection
  `E 1_{n-2} F 1_{n-2} → 1_n⟨l⟩`, written through the adjunction `E 1_{n-2} ⊣ F 1_{n-2}⟨n-1⟩` as
  `(F ◁ f)` followed by the counit (`exists_eq_whiskerLeft_comp_counit`), involves an endomorphism
  `f` of `E 1_{n-2}` of degree `l + n - 1 < 0`; whiskering by `E 1_n` kills the projection (Lemma
  A) but not the identity of `1_n⟨l⟩ E 1_n`, so `E 1_n = 0`, and then `F E 1_n = 0` has no nonzero
  summand at all.
* `isZero_comp_E_of_retract_shift` and `eq_zero_of_retract_of_retract_shift` (**Corollary C**,
  first half): if `Z` and `Z⟨j⟩` are both direct summands of `E 1_{n-2}` with `j ≠ 0`, then
  `Z E 1_n = 0` (Lemma A applied to "project to one, include the other").

Indexing: `n = wt (r + 1)`, `E 1_n = E (r + 1)`, `E 1_{n-2} = E r`, `F E 1_n = E (r + 1) ≫ F (r + 1)`,
`E F 1_n = F r ≫ E r`, `E E 1_{n-2} = E r ≫ E (r + 1)` (Mathlib's diagrammatic order).
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Module
open KrullSchmidtCat (HomFinite)

universe w v u

/-! ## Bicategorical preliminaries -/

section Bicat

variable {B : Type u} [Bicategory.{w, v} B]

/-- **Factorization through the counit**: for an adjunction `l ⊣ r`, every 2-morphism
`β : r ≫ g ⟶ h` is of the form `r ◁ α` followed by the counit, for `α : g ⟶ l ≫ h` its mate. -/
theorem exists_eq_whiskerLeft_comp_counit {c d e : B} {l : c ⟶ d} {r : d ⟶ c} (adj : l ⊣ r)
    {g : c ⟶ e} {h : d ⟶ e} (β : r ≫ g ⟶ h) :
    ∃ α : g ⟶ l ≫ h, β = r ◁ α ≫ (α_ r l h).inv ≫ adj.counit ▷ h ≫ (λ_ h).hom := by
  have hβ := (Bicategory.mateEquiv adj (Bicategory.Adjunction.id e)).apply_symm_apply
    (β ≫ (ρ_ h).inv)
  rw [Bicategory.mateEquiv_apply] at hβ
  refine ⟨(ρ_ g).inv ≫ (Bicategory.mateEquiv adj (Bicategory.Adjunction.id e)).symm
    (β ≫ (ρ_ h).inv), ?_⟩
  generalize (Bicategory.mateEquiv adj (Bicategory.Adjunction.id e)).symm (β ≫ (ρ_ h).inv) = α'
    at hβ ⊢
  have e2 := congrArg (fun φ => φ ≫ (ρ_ h).hom) hβ
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at e2
  rw [← e2]
  simp only [Bicategory.Adjunction.homEquiv₁_apply, Bicategory.Adjunction.homEquiv₂_apply]
  dsimp only [Bicategory.Adjunction.id]
  bicategory

variable [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]

/-- If `η ▷ w = 0` then `(u ◁ η) ▷ w = 0`. -/
theorem whiskerLeft_whiskerRight_eq_zero {a b c d : B} (u : a ⟶ b) {x x' : b ⟶ c} (η : x ⟶ x')
    (w : c ⟶ d) (h : η ▷ w = 0) : (u ◁ η) ▷ w = 0 := by
  rw [whisker_assoc, h, whiskerLeft_zero', zero_comp, comp_zero]

end Bicat

/-! ## Lemma A -/

namespace StrongSl2

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [∀ a b : B, HomFinite k (a ⟶ b)] (S : StrongSl2 k B)

omit [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)] in
/-- A morphism into a Hom space of dimension zero is zero. -/
theorem eq_zero_of_finrank_eq_zero {a b : B} {X Y : a ⟶ b} (h : finrank k (X ⟶ Y) = 0)
    (f : X ⟶ Y) : f = 0 := by
  have := Module.finrank_zero_iff.1 h
  exact Subsingleton.elim _ _

variable [GradedBicategory.ShiftInterchange B]

/-- **Lemma A** (repair of CL Lemma 3.6): at the induction step `n = wt (r + 1) ≥ 0`, assuming
the adjoint induction hypothesis (3.2) for the weights `> n`, every endomorphism
`f : E 1_{n-2} → E 1_{n-2} ⟨m⟩` of negative degree satisfies `E 1_n f = 0` (as a shifted
2-morphism `E E 1_{n-2} → E E 1_{n-2} ⟨m⟩`; here `E 1_n f = f ▷ E (r + 1)`). -/
theorem lemA {r : ℤ} (hn : 0 ≤ S.wt (r + 1)) (hyp : ∀ r', r + 1 < r' → S.AdjHyp r') {m : ℤ}
    (hm : m < 0) (f : ShiftedHom (S.E r) (S.E r) m) : shWhiskerRight f (S.E (r + 1)) = 0 := by
  set N := S.nh r
  set φ : ShiftedHom (S.E r ≫ S.E (r + 1)) (S.E r ≫ S.E (r + 1)) m :=
    shWhiskerRight f (S.E (r + 1)) with hφ
  -- `τ ∘ φ` has degree `m - 2 < -2`: Corollary 3.2 at the weight `n - 2`
  have hτφ : N.τ.comp φ (by ring : m + -2 = m - 2) = 0 :=
    eq_zero_of_finrank_eq_zero (S.cor0_neg (r₀ := r + 1) hn hyp r (by omega) (m - 2) (by omega)) _
  -- `φ` commutes with the dot on the `E 1_n` strand (interchange)
  have hcomm : N.xL.comp φ (by ring : m + 2 = m + 2) = φ.comp N.xL (by ring : 2 + m = m + 2) :=
    (shWhisker_exchange f (S.dot (r + 1)) (by ring) (by ring)).symm
  -- the nilHecke relation `r · 1 = τ x_L - x_R τ`, composed with `φ`
  have key : ((S.rQ : k) • NH2.one (W := S.E r ≫ S.E (r + 1))).comp φ (add_zero m) = 0 := by
    rw [NH2.one, ← ShiftedHom.mk₀_smul]
    change (ShiftedHom.mk₀ (0 : ℤ) rfl ((N.r : k) • 𝟙 _)).comp φ (add_zero m) = 0
    rw [N.slide₂, ShiftedHom.sub_comp',
      ShiftedHom.comp_assoc _ _ _ (by norm_num : (2 : ℤ) + -2 = 0) (by ring : m + 2 = m + 2)
        (by ring), hcomm,
      ← ShiftedHom.comp_assoc _ _ _ (by ring : m + -2 = m - 2) (by ring : (2 : ℤ) + m = m + 2)
        (by ring), hτφ, ShiftedHom.zero_comp,
      ShiftedHom.comp_assoc _ _ _ (by norm_num : (-2 : ℤ) + 2 = 0) (by ring : m + -2 = m - 2)
        (by ring), hτφ, ShiftedHom.comp_zero, sub_zero]
  rw [ShiftedHom.smul_comp', NH2.one, ShiftedHom.mk₀_id_comp] at key
  have := congrArg (fun ψ => ((S.rQ⁻¹ : kˣ) : k) • ψ) key
  simpa only [smul_smul, Units.inv_mul, one_smul, smul_zero] using this

/-- **Lemma A, unshifted form**: `f ▷ E (r + 1) = 0` as a 2-morphism
`E r ≫ E (r + 1) ⟶ (E r)⟦m⟧ ≫ E (r + 1)`. -/
theorem lemA' {r : ℤ} (hn : 0 ≤ S.wt (r + 1)) (hyp : ∀ r', r + 1 < r' → S.AdjHyp r') {m : ℤ}
    (hm : m < 0) (f : S.E r ⟶ (S.E r)⟦m⟧) : f ▷ S.E (r + 1) = 0 :=
  (shWhiskerRight_eq_zero_iff (f : ShiftedHom (S.E r) (S.E r) m) _).1 (S.lemA hn hyp hm f)

/-! ## Corollary B: `F E 1_n` has no summand `1_n ⟨l⟩` at the induction step -/

/-- **Corollary B** (non-circular replacement for the summand claim in CL's proof of Lemma 3.6):
at the induction step `n = wt (r + 1) ≥ 0`, assuming the adjoint induction hypothesis (3.2) only
for the weights `> n`, if `1_n ≠ 0` then `1_n ⟨l⟩` is not a direct summand of `F E 1_n`, for any
`l`. (Compare `Biadjoint.not_retract_one_FE`, which assumes (3.2) at `n` itself.) -/
theorem not_retract_one_FE_step {r : ℤ} (hn : 0 ≤ S.wt (r + 1))
    (hyp : ∀ r', r + 1 < r' → S.AdjHyp r') (h : ¬ IsZero (𝟙 (S.obj (r + 1)))) (l : ℤ)
    (i : ((𝟙 (S.obj (r + 1)))⟦l⟧) ⟶ S.E (r + 1) ≫ S.F (r + 1))
    (p : S.E (r + 1) ≫ S.F (r + 1) ⟶ ((𝟙 (S.obj (r + 1)))⟦l⟧)) : i ≫ p ≠ 𝟙 _ := by
  intro hip
  have hne : ¬ IsZero ((𝟙 (S.obj (r + 1)))⟦l⟧) := fun hz => by
    have e : 𝟙 (S.obj (r + 1)) ≅ (((𝟙 (S.obj (r + 1)))⟦l⟧))⟦-l⟧ :=
      ((shiftFunctorCompIsoId _ l (-l) (by ring)).app _).symm
    exact h (((shiftFunctor _ (-l)).map_isZero hz).of_iso e)
  have hw : S.wt (r + 1) = S.wt r + 2 := S.wt_add_one r
  by_cases hl : 0 < l + (S.wt (r + 1) + 1)
  · -- the inclusion vanishes by Lemma 3.1
    have h0 := S.finrank_one_FE (r + 1) l
    rw [S.lem1_neg (r₀ := r + 1) hn hyp (r + 1) le_rfl _ (by omega)] at h0
    have : i = 0 := eq_zero_of_finrank_eq_zero h0 i
    exact hne ((IsZero.iff_id_eq_zero _).2 (by rw [← hip, this, zero_comp]))
  -- `l ≤ -n-1`: transfer the summand to `E F 1_n = E 1_{n-2} F 1_{n-2}`
  obtain ⟨e⟩ := S.EF r (by rw [← wt]; exact hn)
  set i' : ((𝟙 (S.obj (r + 1)))⟦l⟧) ⟶ S.F r ≫ S.E r := i ≫ biprod.inl ≫ e.inv with hi'
  set p' : S.F r ≫ S.E r ⟶ ((𝟙 (S.obj (r + 1)))⟦l⟧) := e.hom ≫ biprod.fst ≫ p with hp'
  have hip' : i' ≫ p' = 𝟙 ((𝟙 (S.obj (r + 1)))⟦l⟧) := by
    rw [hi', hp']
    simp only [Category.assoc, Iso.inv_hom_id_assoc, biprod.inl_fst_assoc]
    exact hip
  -- shift so that the adjunction `E 1_{n-2} ⊣ F 1_{n-2} ⟨n-1⟩` applies
  set s := S.wt r + 1 with hs
  set i'' : ((𝟙 (S.obj (r + 1)))⟦l⟧)⟦s⟧ ⟶ (S.F r)⟦s⟧ ≫ S.E r :=
    i'⟦s⟧' ≫ (whiskerRightShiftIso (S.F r) (S.E r) s).inv with hi''
  set q : (S.F r)⟦s⟧ ≫ S.E r ⟶ ((𝟙 (S.obj (r + 1)))⟦l⟧)⟦s⟧ :=
    (whiskerRightShiftIso (S.F r) (S.E r) s).hom ≫ p'⟦s⟧' with hq
  have hiq : i'' ≫ q = 𝟙 _ := by
    rw [hi'', hq, Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp, hip',
      CategoryTheory.Functor.map_id]
  -- the projection factors through the counit, via a negative-degree endomorphism of `E 1_{n-2}`
  obtain ⟨α, hα⟩ := exists_eq_whiskerLeft_comp_counit (S.adj r) q
  let e₁ : S.E r ≫ ((𝟙 (S.obj (r + 1)))⟦l⟧)⟦s⟧ ≅ (S.E r)⟦l + s⟧ :=
    whiskerLeftIso (S.E r) ((shiftFunctorAdd' _ l s (l + s) rfl).app (𝟙 (S.obj (r + 1)))).symm ≪≫
      compIdShiftIso (S.E r) (l + s)
  have hf : (α ≫ e₁.hom) ▷ S.E (r + 1) = 0 := S.lemA' hn hyp (by omega) (α ≫ e₁.hom)
  have hα0 : α ▷ S.E (r + 1) = 0 := by
    have : α = (α ≫ e₁.hom) ≫ e₁.inv := by simp
    rw [this, comp_whiskerRight, hf, zero_comp]
  have hq0 : q ▷ S.E (r + 1) = 0 := by
    rw [hα]
    erw [comp_whiskerRight, whiskerLeft_whiskerRight_eq_zero _ _ _ hα0, zero_comp]
  -- hence `1_n ⟨l⟩ E 1_n = 0`, so `E 1_n = 0`
  have hz : IsZero (((𝟙 (S.obj (r + 1)))⟦l⟧)⟦s⟧ ≫ S.E (r + 1)) := by
    rw [IsZero.iff_id_eq_zero, ← Bicategory.id_whiskerRight, ← hiq, comp_whiskerRight, hq0, comp_zero]
  have hzE : IsZero (S.E (r + 1)) := by
    have e₂ : ((𝟙 (S.obj (r + 1)))⟦l⟧)⟦s⟧ ≫ S.E (r + 1) ≅ (S.E (r + 1))⟦l + s⟧ :=
      whiskerRightIso ((shiftFunctorAdd' _ l s (l + s) rfl).app (𝟙 (S.obj (r + 1)))).symm _ ≪≫
        idShiftCompIso (S.E (r + 1)) (l + s)
    exact (((shiftFunctor _ (-(l + s))).map_isZero (hz.of_iso e₂.symm)).of_iso
      ((shiftFunctorCompIsoId _ (l + s) (-(l + s)) (by ring)).app _).symm)
  have hp0 : p = 0 := (isZero_comp_left hzE (S.F (r + 1))).eq_of_src p 0
  exact hne ((IsZero.iff_id_eq_zero _).2 (by rw [← hip, hp0, comp_zero]))

/-! ## Corollary C: an indecomposable summand of `E 1_{n-2}` seen by `E 1_n` occurs once -/

/-- **Corollary C, first half**: at the induction step, if `Z₁` and `Z₂` are direct summands of
`E 1_{n-2}` with `Z₁ ≅ Z₂ ⟨j⟩` for some `j < 0`, then `Z₁ E 1_n = 0`. (Project to `Z₁`, include
`Z₂⟨j⟩`: this is an endomorphism of `E 1_{n-2}` of degree `j < 0`, killed by `E 1_n` by Lemma A,
but it is a retraction of `Z₁`.) -/
theorem isZero_comp_E_of_retract_shift {r : ℤ} (hn : 0 ≤ S.wt (r + 1))
    (hyp : ∀ r', r + 1 < r' → S.AdjHyp r') {Z₁ Z₂ : S.obj r ⟶ S.obj (r + 1)}
    (i₁ : Z₁ ⟶ S.E r) (p₁ : S.E r ⟶ Z₁) (h₁ : i₁ ≫ p₁ = 𝟙 Z₁) (i₂ : Z₂ ⟶ S.E r)
    (p₂ : S.E r ⟶ Z₂) (h₂ : i₂ ≫ p₂ = 𝟙 Z₂) {j : ℤ} (hj : j < 0) (e : Z₁ ≅ Z₂⟦j⟧) :
    IsZero (Z₁ ≫ S.E (r + 1)) := by
  have hf := S.lemA' hn hyp hj (p₁ ≫ e.hom ≫ i₂⟦j⟧')
  have hid : (i₁ ≫ (p₁ ≫ e.hom ≫ i₂⟦j⟧') ≫ p₂⟦j⟧' ≫ e.inv) = 𝟙 Z₁ := by
    simp only [Category.assoc, ← Functor.map_comp_assoc, h₂, CategoryTheory.Functor.map_id,
      Category.id_comp, Iso.hom_inv_id, Category.comp_id, h₁]
  rw [IsZero.iff_id_eq_zero, ← Bicategory.id_whiskerRight, ← hid, comp_whiskerRight,
    comp_whiskerRight, hf, zero_comp, comp_zero]

/-- **Corollary C, first half**: at the induction step, if both `X` and `X⟨j⟩` are direct summands
of `E 1_{n-2}` and `X E 1_n ≠ 0`, then `j = 0`. -/
theorem eq_zero_of_retract_of_retract_shift {r : ℤ} (hn : 0 ≤ S.wt (r + 1))
    (hyp : ∀ r', r + 1 < r' → S.AdjHyp r') {X : S.obj r ⟶ S.obj (r + 1)}
    (hX : ¬ IsZero (X ≫ S.E (r + 1))) (i₀ : X ⟶ S.E r) (p₀ : S.E r ⟶ X) (h₀ : i₀ ≫ p₀ = 𝟙 X)
    {j : ℤ} (i : X⟦j⟧ ⟶ S.E r) (p : S.E r ⟶ X⟦j⟧) (h : i ≫ p = 𝟙 _) : j = 0 := by
  by_contra hj
  rcases lt_or_gt_of_ne hj with hj | hj
  · have hz := S.isZero_comp_E_of_retract_shift hn hyp i p h i₀ p₀ h₀ hj (Iso.refl _)
    have hz' : IsZero ((X ≫ S.E (r + 1))⟦j⟧) := hz.of_iso (whiskerRightShiftIso _ _ _).symm
    exact hX (((shiftFunctor _ (-j)).map_isZero hz').of_iso
      ((shiftFunctorCompIsoId _ j (-j) (by ring)).app _).symm)
  · exact hX (S.isZero_comp_E_of_retract_shift hn hyp i₀ p₀ h₀ i p h (by omega : -j < 0)
      ((shiftFunctorCompIsoId _ j (-j) (by ring)).app X).symm)

variable [∀ a b : B, IsIdempotentComplete (a ⟶ b)]

omit [GradedBicategory.ShiftInterchange B] [∀ a b : B, IsIdempotentComplete (a ⟶ b)] in
/-- The dimension count behind Corollary C: `Hom^{-2}(E E 1_{n-2}, E E 1_{n-2})` is one-dimensional
(Corollary 3.2), and `E E 1_{n-2} ≅ D⟨1⟩ ⊕ D⟨-1⟩` (`D = E^{(2)} 1_{n-2}`), so `End(D) = k` and
`Hom(D, D⟨-2⟩) = 0` whenever `E E 1_{n-2} ≠ 0`. -/
theorem finrank_E2_of_iso {r : ℤ} (hn : 0 ≤ S.wt (r + 1)) (hyp : ∀ r', r + 1 < r' → S.AdjHyp r')
    (h2 : ¬ IsZero (𝟙 (S.obj (r + 1 + 1)))) {D : S.obj r ⟶ S.obj (r + 1 + 1)}
    (eD : S.E r ≫ S.E (r + 1) ≅ D⟦(1 : ℤ)⟧ ⊞ D⟦(-1 : ℤ)⟧) (hD : ¬ IsZero D) :
    finrank k (D ⟶ D) = 1 ∧ finrank k (D ⟶ D⟦(-2 : ℤ)⟧) = 0 := by
  have h1 := S.cor0_zero (r₀ := r + 1) hn hyp (r := r) (by omega) h2
  have s1 : (D⟦(1 : ℤ)⟧)⟦(-2 : ℤ)⟧ ≅ D⟦(-1 : ℤ)⟧ :=
    ((shiftFunctorAdd' _ (1 : ℤ) (-2) (-1) (by norm_num)).app D).symm
  have s2 : (D⟦(-1 : ℤ)⟧)⟦(-2 : ℤ)⟧ ≅ D⟦(-3 : ℤ)⟧ :=
    ((shiftFunctorAdd' _ (-1 : ℤ) (-2) (-3) (by norm_num)).app D).symm
  rw [finrank_hom_congr k eD ((shiftFunctor _ (-2 : ℤ)).mapIso eD),
    finrank_hom_congr_right k _ (mapBiprodIso (shiftFunctor _ (-2 : ℤ)) _ _),
    finrank_hom_biprod_left, finrank_hom_biprod_right, finrank_hom_biprod_right,
    finrank_hom_congr_right k (D⟦(1 : ℤ)⟧) s1, finrank_hom_congr_right k (D⟦(1 : ℤ)⟧) s2,
    finrank_hom_congr_right k (D⟦(-1 : ℤ)⟧) s1, finrank_hom_congr_right k (D⟦(-1 : ℤ)⟧) s2,
    finrank_hom_shift_shift k _ _ (c := -2) (by norm_num),
    finrank_hom_shift_shift k _ _ (c := -4) (by norm_num),
    finrank_hom_shift k, finrank_hom_shift_shift k _ _ (c := -2) (by norm_num)] at h1
  have hpos : 0 < finrank k (D ⟶ D) := KrullSchmidtCat.finrank_end_pos k hD
  omega

omit [GradedBicategory.ShiftInterchange B] in
/-- **Corollary C, second half**: at the induction step, a 1-morphism `X` with `X E 1_n ≠ 0` does
not occur twice (with the same shift) as a direct summand of `E 1_{n-2}`: there is no `Y` with
`E 1_{n-2} ≅ X ⊕ X ⊕ Y`. (Whisker by `E 1_n`: an indecomposable summand `Z` of `X E 1_n` would
have multiplicity `≥ 2` in `E E 1_{n-2} ≅ D⟨1⟩ ⊕ D⟨-1⟩`, `D = E^{(2)} 1_{n-2}` a brick with
`D⟨1⟩ ≇ D⟨-1⟩` by Corollary 3.2.) -/
theorem not_iso_biprod_self {r : ℤ} (hn : 0 ≤ S.wt (r + 1)) (hyp : ∀ r', r + 1 < r' → S.AdjHyp r')
    {X : S.obj r ⟶ S.obj (r + 1)} (hX : ¬ IsZero (X ≫ S.E (r + 1)))
    (Y : S.obj r ⟶ S.obj (r + 1)) (e : S.E r ≅ X ⊞ (X ⊞ Y)) : False := by
  let := k0ShiftOfHasShift (S.obj r ⟶ S.obj (r + 1 + 1))
  have eEE : S.E r ≫ S.E (r + 1) ≅ (X ≫ S.E (r + 1)) ⊞ ((X ≫ S.E (r + 1)) ⊞ Y ≫ S.E (r + 1)) :=
    whiskerRightIso e _ ≪≫ whiskerRightBiprodIso _ _ _ ≪≫
      biprod.mapIso (Iso.refl _) (whiskerRightBiprodIso _ _ _)
  have h2 : ¬ IsZero (𝟙 (S.obj (r + 1 + 1))) := fun hz =>
    hX (isZero_comp_right X (S.isZero_E_of_right hz))
  obtain ⟨D, ⟨eD⟩⟩ := S.exists_E2 r
  -- `D ≠ 0`, since `X E 1_n` is a nonzero summand of `E E 1_{n-2} ≅ D⟨1⟩ ⊕ D⟨-1⟩`
  have hD : ¬ IsZero D := fun hz => by
    have hEE : IsZero (S.E r ≫ S.E (r + 1)) := by
      refine IsZero.of_iso ?_ eD
      have hz1 := (shiftFunctor _ (1 : ℤ)).map_isZero hz
      have hz2 := (shiftFunctor _ (-1 : ℤ)).map_isZero hz
      rw [IsZero.iff_id_eq_zero, ← biprod.total, hz1.eq_of_src biprod.inl 0,
        hz2.eq_of_src biprod.inr 0, comp_zero, comp_zero, add_zero]
    have hid : (𝟙 (X ≫ S.E (r + 1)) : _ ⟶ _) = biprod.inl ≫ eEE.inv ≫ eEE.hom ≫ biprod.fst := by
      simp
    rw [hEE.eq_of_tgt eEE.inv 0, zero_comp, comp_zero] at hid
    exact hX ((IsZero.iff_id_eq_zero _).2 hid)
  obtain ⟨hend, hneg⟩ := S.finrank_E2_of_iso hn hyp h2 eD hD
  have hDind : KrullSchmidtCat.IsIndec D := ((isBrick_iff k).2 hend).1
  have hD1 : KrullSchmidtCat.IsIndec (D⟦(1 : ℤ)⟧) := KrullSchmidtCat.IsIndec.sh k 1 hDind
  have hD2 : KrullSchmidtCat.IsIndec (D⟦(-1 : ℤ)⟧) := KrullSchmidtCat.IsIndec.sh k (-1) hDind
  -- `D⟨1⟩ ≇ D⟨-1⟩`, since `Hom(D, D⟨-2⟩) = 0`
  have hniso : ¬ Nonempty (D⟦(1 : ℤ)⟧ ≅ D⟦(-1 : ℤ)⟧) := fun ⟨e'⟩ => by
    let e'' : D ≅ D⟦(-2 : ℤ)⟧ :=
      ((shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by norm_num)).app D).symm ≪≫
        (shiftFunctor _ (-1 : ℤ)).mapIso e' ≪≫
        ((shiftFunctorAdd' _ (-1 : ℤ) (-1) (-2) (by norm_num)).app D).symm
    have h0 : e''.hom = 0 := eq_zero_of_finrank_eq_zero hneg _
    exact hD ((IsZero.iff_id_eq_zero D).2 (by rw [← e''.hom_inv_id, h0, zero_comp]))
  -- an indecomposable summand `Z` of `X E 1_n` and its multiplicities
  obtain ⟨Z, f, g, hZ, hfg⟩ := exists_indec_retract k hX
  obtain ⟨W', ⟨φ⟩⟩ := exists_iso_biprod_of_retract f g hfg
  have hd := KrullSchmidtCat.multK_self_pos k hZ
  rw [KrullSchmidtCat.multK_of] at hd
  have hA : 2 * KrullSchmidtCat.mult k hZ Z ≤ KrullSchmidtCat.mult k hZ (S.E r ≫ S.E (r + 1)) := by
    rw [KrullSchmidtCat.mult_iso k hZ eEE, KrullSchmidtCat.mult_biprod,
      KrullSchmidtCat.mult_biprod, KrullSchmidtCat.mult_iso k hZ φ, KrullSchmidtCat.mult_biprod]
    have := mult_nonneg k hZ (Y ≫ S.E (r + 1))
    have := mult_nonneg k hZ W'
    omega
  have hB : KrullSchmidtCat.mult k hZ (S.E r ≫ S.E (r + 1)) ≤ KrullSchmidtCat.mult k hZ Z := by
    rw [KrullSchmidtCat.mult_iso k hZ eD, KrullSchmidtCat.mult_biprod]
    have m0 : ∀ {Z' : S.obj r ⟶ S.obj (r + 1 + 1)}, KrullSchmidtCat.IsIndec Z' →
        ¬ Nonempty (Z ≅ Z') → KrullSchmidtCat.mult k hZ Z' = 0 := fun hZ' h => by
      have := KrullSchmidtCat.multK_of_not_iso k hZ hZ' h
      rwa [KrullSchmidtCat.multK_of] at this
    by_cases h1 : Nonempty (Z ≅ D⟦(1 : ℤ)⟧)
    · obtain ⟨e1⟩ := h1
      rw [m0 hD2 fun ⟨e2⟩ => hniso ⟨e1.symm ≪≫ e2⟩, ← KrullSchmidtCat.mult_iso k hZ e1]
      omega
    · rw [m0 hD1 h1]
      by_cases h2' : Nonempty (Z ≅ D⟦(-1 : ℤ)⟧)
      · obtain ⟨e2⟩ := h2'
        rw [← KrullSchmidtCat.mult_iso k hZ e2]
        omega
      · rw [m0 hD2 h2']
        omega
  omega

end StrongSl2

end Categorification.TwoRep

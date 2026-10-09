/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.FakeBubbles

/-!
# The form of `ζ⁻¹` and the decomposition of `1_{EF1_n}` for `n ≥ 0` (CL §§5.2–5.3)

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, §5.2 (Proposition 5.1, eqs. (5.7), (5.8)) and §5.3 (relations (A1)–(A5),
Proposition 5.2, Corollary 5.3), for `n ≥ 0`.

Fix the object `q + 1` of weight `n = wt (q + 1) ≥ 0`. In the graded-Hom bicategory, with
`R E = grR q ≫ grE q` (CL's `E F 1_n`) and `E R = grE (q+1) ≫ grR (q+1)` (CL's `F E 1_n`), CL's map

  `ζ = σ' ⊕ ⊕_{k<n} cup_k : F E 1_n ⊕ ⊕_k 1_n⟨n-1-2k⟩ → E F 1_n`

(Corollary 3.13, with the sideways crossing `σ' = sideLN q` of (4.16) and `cup_k` the left cup
followed by `k` dots, `cupD`) is an isomorphism, and CL show that its inverse is

  `ζ⁻¹ = β σ ⊕ ⊕_k comp_k`,   `comp_k = ∑_{g} (k-th cap with dots) ∘ (fake bubble of degree 2g)`

(Proposition 5.1, with the coefficients of Proposition 5.2: the fake bubbles are the solution of the
infinite Grassmannian relation). We prove this in the form of the relations it is equivalent to
(CL's (A1)–(A5)):

* (A1) `cup_{k'} ≫ comp_k = δ_{k k'}` (`cupD_comp_compK`): pure bubble algebra, from the
  normalization (4.1) and the definition of the fake bubbles (`grassmannian_cw_ccw`);
* (A3) `cup_k ≫ σ = 0` for `k < n` (`cupD_comp_grSigma`; a curl) and
  (A4) `σ' ≫ comp_k = 0` (`sideL_comp_compK`): both by degrees, as `End(E 1_n)` has no
  negative-degree elements (Lemma 3.1);
* (A2) `σ' ≫ β σ = 1` and (A5) `1_{EF1_n} = β σ σ' + ∑_k comp_k cup_k` (`decompEF_beta`).

For (A2), (A5) we start from a decomposition `E F 1_n ≅ F E 1_n ⊕ ⊕_{[n]} 1_n` (Definition 1.2 (3)),
transported to the graded-Hom bicategory (`grι`, `grπ`, `grιFE`, `grπFE`). By degrees, the
matrix of the cups in the summands `1_n⟨n-1-2j⟩` is triangular; its diagonal entries are nonzero
because the degree-zero bubble is `1` (this replaces CL's appeal to Lemma 3.6). Inverting the
triangular matrix (`inCupSpan_of_triangular`) writes the projection onto `⊕_j 1_n⟨n-1-2j⟩` as
`∑_k φ_k ∘ cup_k`. By Lemma 3.12 (`lemHoms_EF_FE_eq_one`, `lemHoms_FE_EF_eq_one`) the projection and
the inclusion of `F E 1_n` are multiples of `σ` and `σ'` (this is CL's first claim of Proposition
5.1). Finally `φ_k = comp_k` by composing (A5) with `comp_k` and using (A1), (A4).

The value `β = -1` (CL Lemma 5.4, with `r_i = 1`) is proved in a separate file.

## Main declarations

* generic: `InCupSpan`, `inCupSpan_of_triangular`; `GradedHomBicat.eq_zero_of_isHomogeneous_unit_side`,
  `GradedHomBicat.eq_zero_of_isHomogeneous_counit_side`, `GradedHomBicat.mateEquiv_zero`;
* `StrongSl2.cupD`, `capD`, `compK`, `cupD_comp_compK` (A1), `cupD_comp_grSigma` (A3),
  `sideL_comp_compK` (A4), `decompEF_beta` (A2, A5 and Proposition 5.1).
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

universe w v u

/-! ## Inverting a triangular matrix of cups -/

section Span

variable {C : Type*} [Category C] [Preadditive C] {k : Type*} [Field k] [Linear k C]
  {U V : C} (N : ℕ) (c : ℕ → (U ⟶ V))

/-- `f` is a combination `∑_{i<N} φ_i ≫ c_i` of the maps `c_i : U ⟶ V`. -/
def InCupSpan (f : V ⟶ V) : Prop := ∃ φ : ℕ → (V ⟶ U), f = ∑ i ∈ Finset.range N, φ i ≫ c i

variable {N c}

theorem InCupSpan.add {f g : V ⟶ V} (hf : InCupSpan N c f) (hg : InCupSpan N c g) :
    InCupSpan N c (f + g) := by
  obtain ⟨φ, rfl⟩ := hf
  obtain ⟨ψ, rfl⟩ := hg
  exact ⟨φ + ψ, by simp only [Pi.add_apply, Preadditive.add_comp, Finset.sum_add_distrib]⟩

theorem InCupSpan.smul {f : V ⟶ V} (t : k) (hf : InCupSpan N c f) : InCupSpan N c (t • f) := by
  obtain ⟨φ, rfl⟩ := hf
  exact ⟨t • φ, by simp only [Pi.smul_apply, Linear.smul_comp, Finset.smul_sum]⟩

theorem InCupSpan.neg {f : V ⟶ V} (hf : InCupSpan N c f) : InCupSpan N c (-f) := by
  obtain ⟨φ, rfl⟩ := hf
  exact ⟨-φ, by simp only [Pi.neg_apply, Preadditive.neg_comp, Finset.sum_neg_distrib]⟩

theorem InCupSpan.sub {f g : V ⟶ V} (hf : InCupSpan N c f) (hg : InCupSpan N c g) :
    InCupSpan N c (f - g) := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

theorem InCupSpan.zero : InCupSpan N c 0 := ⟨0, by simp⟩

theorem InCupSpan.sum {ι : Type*} (s : Finset ι) {f : ι → (V ⟶ V)}
    (hf : ∀ i ∈ s, InCupSpan N c (f i)) : InCupSpan N c (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using InCupSpan.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem inCupSpan_comp (g : V ⟶ U) {j : ℕ} (hj : j < N) : InCupSpan N c (g ≫ c j) := by
  classical
  refine ⟨fun i => if i = j then g else 0, ?_⟩
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_range.2 hj)]
  · simp
  · intro i _ hij
    simp [hij]

/-- **Inverting a triangular matrix of cups.** Let `ι_j : U ⟶ V`, `π_j : V ⟶ U` and `c_j : U ⟶ V`
(`j < N`) be such that `c_j = ∑_i (c_j ≫ π_i) ≫ ι_i`, `c_j ≫ π_i = 0` for `i > j` and
`c_j ≫ π_j` is a nonzero scalar. Then every `g ≫ ι_j` is a combination of the `c_k`. -/
theorem inCupSpan_of_triangular (ι : ℕ → (U ⟶ V)) (π : ℕ → (V ⟶ U))
    (hlow : ∀ j i, j < N → i < N → j < i → c j ≫ π i = 0)
    (hdiag : ∀ j, j < N → ∃ s : k, s ≠ 0 ∧ c j ≫ π j = s • 𝟙 U)
    (hexp : ∀ j, j < N → c j = ∑ i ∈ Finset.range N, (c j ≫ π i) ≫ ι i) :
    ∀ j, j < N → ∀ g : V ⟶ U, InCupSpan N c (g ≫ ι j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj g
    obtain ⟨s, hs, hsj⟩ := hdiag j hj
    have hc : c j = s • ι j + ∑ i ∈ Finset.range j, (c j ≫ π i) ≫ ι i := by
      nth_rewrite 1 [hexp j hj]
      rw [← Finset.sum_range_add_sum_Ico _ hj.le, add_comm]
      congr 1
      rw [Finset.sum_eq_single_of_mem j (Finset.mem_Ico.2 ⟨le_rfl, hj⟩)]
      · rw [hsj, Linear.smul_comp, Category.id_comp]
      · intro i hi hij
        rw [hlow j i hj (Finset.mem_Ico.1 hi).2 (lt_of_le_of_ne (Finset.mem_Ico.1 hi).1
          (Ne.symm hij)), zero_comp]
    have h2 : s • ι j = c j - ∑ i ∈ Finset.range j, (c j ≫ π i) ≫ ι i :=
      eq_sub_of_add_eq hc.symm
    have hι : ι j = s⁻¹ • (c j - ∑ i ∈ Finset.range j, (c j ≫ π i) ≫ ι i) := by
      rw [← h2, smul_smul, inv_mul_cancel₀ hs, one_smul]
    rw [hι, Linear.comp_smul, Preadditive.comp_sub, Preadditive.comp_sum]
    refine ((inCupSpan_comp g hj).sub (InCupSpan.sum _ fun i hi => ?_)).smul _
    rw [← Category.assoc]
    exact ih i (Finset.mem_range.1 hi) (by have := Finset.mem_range.1 hi; omega) _

end Span

/-! ## Vanishing by adjunction in the graded-Hom bicategory -/

section GradedHom

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B] [GradedBicategory.ShiftCoherence B]

namespace GradedHomBicat

open GradedHomCat

/-- A homogeneous `χ : 1 ⟶ E R` vanishes if, under `E ⊣ R`, the corresponding endomorphisms of `E`
vanish in its degree. -/
theorem eq_zero_of_isHomogeneous_unit_side {a b : GradedHomBicat B} {E : a ⟶ b} {R : b ⟶ a}
    (adj : E ⊣ R) {c : ℤ} (hc : IsHomogeneous adj.counit c) {d : ℤ}
    (hE : ∀ ψ : E ⟶ E, IsHomogeneous ψ (d + c) → ψ = 0) {χ : 𝟙 a ⟶ E ≫ R}
    (hχ : IsHomogeneous χ d) : χ = 0 := by
  have hψ : IsHomogeneous ((λ_ E).inv ≫ adj.homEquiv₂.symm χ) (d + c) := by
    rw [Adjunction.homEquiv₂_symm_apply]
    exact ((isHomogeneous_leftUnitor_inv _).comp ((isHomogeneous_whiskerRight hχ _).comp
      ((isHomogeneous_associator_hom _ _ _).comp ((isHomogeneous_whiskerLeft _ hc).comp
        (isHomogeneous_rightUnitor_hom _) rfl) rfl) rfl) rfl).of_eq (by ring)
  have h0 : adj.homEquiv₂.symm χ = 0 := by
    have := hE _ hψ
    rw [← Category.id_comp (adj.homEquiv₂.symm χ), ← Iso.hom_inv_id (λ_ E), Category.assoc, this,
      comp_zero]
  have : χ = adj.homEquiv₂ 0 := by rw [← h0, Equiv.apply_symm_apply]
  rw [this, Adjunction.homEquiv₂_apply, zero_whiskerRight, comp_zero, comp_zero, comp_zero]

/-- A homogeneous `χ : E R ⟶ 1` vanishes if, under `R ⊣ E`, the corresponding endomorphisms of `E`
vanish in its degree (shifted by the degree of the unit). -/
theorem eq_zero_of_isHomogeneous_counit_side {a b : GradedHomBicat B} {R : b ⟶ a} {E : a ⟶ b}
    (adj : R ⊣ E) {u : ℤ} (hu : IsHomogeneous adj.unit u) {d : ℤ}
    (hE : ∀ ψ : E ⟶ E, IsHomogeneous ψ (u + d) → ψ = 0) {χ : E ≫ R ⟶ 𝟙 a}
    (hχ : IsHomogeneous χ d) : χ = 0 := by
  have hψ : IsHomogeneous (adj.homEquiv₂ χ ≫ (λ_ E).hom) (u + d) := by
    rw [Adjunction.homEquiv₂_apply]
    have h1 : IsHomogeneous ((χ ▷ E) ≫ (λ_ E).hom) d :=
      (isHomogeneous_whiskerRight hχ E).comp (isHomogeneous_leftUnitor_hom E) (zero_add d)
    have h2 : IsHomogeneous ((α_ E R E).inv ≫ (χ ▷ E) ≫ (λ_ E).hom) d :=
      (isHomogeneous_associator_inv E R E).comp h1 (add_zero d)
    have h3 : IsHomogeneous (E ◁ adj.unit ≫ (α_ E R E).inv ≫ (χ ▷ E) ≫ (λ_ E).hom) (u + d) :=
      (isHomogeneous_whiskerLeft E hu).comp h2 (add_comm d u)
    simpa only [Category.assoc] using
      (isHomogeneous_rightUnitor_inv E).comp h3 (add_zero (u + d))
  have h0 : adj.homEquiv₂ χ = 0 := by
    have := hE _ hψ
    rw [← Category.comp_id (adj.homEquiv₂ χ), ← Iso.hom_inv_id (λ_ E), ← Category.assoc, this,
      zero_comp]
  have : χ = adj.homEquiv₂.symm 0 := by rw [← h0, Equiv.symm_apply_apply]
  rw [this, Adjunction.homEquiv₂_symm_apply, zero_whiskerRight, zero_comp]

/-- The mate of `0` is `0`. -/
theorem mateEquiv_zero {c d e f : GradedHomBicat B} {g : c ⟶ e} {h : d ⟶ f}
    {l₁ : c ⟶ d} {r₁ : d ⟶ c} {l₂ : e ⟶ f} {r₂ : f ⟶ e} (adj₁ : l₁ ⊣ r₁) (adj₂ : l₂ ⊣ r₂) :
    mateEquiv adj₁ adj₂ (0 : g ≫ l₂ ⟶ l₁ ≫ h) = 0 := by
  rw [mateEquiv_eq_comp, zero_whiskerRight, whiskerLeft_zero]
  simp only [zero_comp, comp_zero]

end GradedHomBicat

end GradedHom

/-! ## Cups, caps and the decomposition data -/

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [GradedBicategory.ShiftCoherence B] [GradedBicategory.IsLinear B k]

namespace StrongSl2

open GradedHomBicat GradedHomCat Module
open KrullSchmidtCat (HomFinite)

variable (S : StrongSl2 k B)

theorem powComp_add {D : Type*} [Category D] {X : D} (f : X ⟶ X) (i : ℕ) :
    ∀ j : ℕ, powComp f i ≫ powComp f j = powComp f (i + j)
  | 0 => by simp
  | j + 1 => by rw [powComp_succ, ← Category.assoc, powComp_add f i j, ← powComp_succ]; rfl

/-- **The left cup with `j` dots** `1_n → E F 1_n` (CL's cup of Corollary 3.13 followed by `j`
dots), at the object `q + 1`, for a left adjunction `A : R_{n-2} ⊣ E 1_{n-2}`. -/
def cupD {q : ℤ} (A : S.grR q ⊣ S.grE q) (j : ℕ) :
    𝟙 (of (S.obj (q + 1))) ⟶ S.grR q ≫ S.grE q :=
  A.unit ≫ S.grR q ◁ powComp (S.grDotN q) j

/-- **The right cap with `j` dots** `E F 1_n → 1_n` (`j` dots, then the counit of
`E 1_{n-2} ⊣ R_{n-2}`). -/
def capD (q : ℤ) (j : ℕ) : S.grR q ≫ S.grE q ⟶ 𝟙 (of (S.obj (q + 1))) :=
  S.grR q ◁ powComp (S.grDotN q) j ≫ S.grCounit q

theorem cupD_comp_capD {q : ℤ} (A : S.grR q ⊣ S.grE q) (i j : ℕ) :
    S.cupD A i ≫ S.capD q j = S.cwBub A (i + j) := by
  simp only [cupD, capD, cwBub, Category.assoc]
  rw [← Category.assoc (S.grR q ◁ powComp (S.grDotN q) i), ← Bicategory.whiskerLeft_comp,
    powComp_add]

theorem isHomogeneous_cupD {q : ℤ} (A : S.grR q ⊣ S.grE q)
    (hu : IsHomogeneous A.unit (-(2 * S.wt q + 2))) (j : ℕ) :
    IsHomogeneous (S.cupD A j) (2 * (j : ℤ) - 2 * S.wt (q + 1) + 2) :=
  (hu.comp (isHomogeneous_whiskerLeft _ (GradedHomBicat.isHomogeneous_powComp
    (S.isHomogeneous_grDotN q) j)) rfl).of_eq (by rw [S.wt_add_one]; ring)

theorem isHomogeneous_capD (q : ℤ) (j : ℕ) : IsHomogeneous (S.capD q j) (2 * (j : ℤ)) :=
  ((isHomogeneous_whiskerLeft _ (GradedHomBicat.isHomogeneous_powComp
    (S.isHomogeneous_grDotN q) j)).comp (isHomogeneous_incl₂ _) rfl).of_eq (by ring)

/-! ### The decomposition `E F 1_n ≅ F E 1_n ⊕ ⊕_{[n]} 1_n` in the graded-Hom bicategory -/

section Decomp

variable {S} {q : ℤ} (e : S.EFDecomp q)

/-- `1_n⟨n-1-2j⟩ ≅ 1_n` in the graded-Hom bicategory (degree `n - 1 - 2j`). -/
def oneShiftIso₁ (S : StrongSl2 k B) (q : ℤ) (j : ℕ) :
    of₁ (S.oneShift q j) ≅ 𝟙 (of (S.obj (q + 1))) :=
  shiftIso₁ (𝟙 (S.obj (q + 1))) (1 * ((((S.wt (q + 1)).toNat : ℕ) : ℤ) - 1 - 2 * (j : ℤ)))

/-- The inclusion of `F E 1_n` into `E F 1_n`, in the graded-Hom bicategory. -/
def grιFE : S.grE (q + 1) ≫ S.grR (q + 1) ⟶ S.grR q ≫ S.grE q :=
  (S.rhoTargetIso q).hom ≫ incl₂ (ιFE e) ≫ (S.rhoSourceIso q).inv

/-- The projection of `E F 1_n` onto `F E 1_n`, in the graded-Hom bicategory. -/
def grπFE : S.grR q ≫ S.grE q ⟶ S.grE (q + 1) ≫ S.grR (q + 1) :=
  (S.rhoSourceIso q).hom ≫ incl₂ (πFE e) ≫ (S.rhoTargetIso q).inv

/-- The inclusion of the summand `1_n⟨n-1-2j⟩` into `E F 1_n`, in the graded-Hom bicategory. -/
def grι (j : ℕ) : 𝟙 (of (S.obj (q + 1))) ⟶ S.grR q ≫ S.grE q :=
  (oneShiftIso₁ S q j).inv ≫ incl₂ (ι e j) ≫ (S.rhoSourceIso q).inv

/-- The projection of `E F 1_n` onto the summand `1_n⟨n-1-2j⟩`, in the graded-Hom bicategory. -/
def grπ (j : ℕ) : S.grR q ≫ S.grE q ⟶ 𝟙 (of (S.obj (q + 1))) :=
  (S.rhoSourceIso q).hom ≫ incl₂ (π e j) ≫ (oneShiftIso₁ S q j).hom

omit [GradedBicategory.IsLinear B k] [∀ a b : B, HasZeroObject (a ⟶ b)]
  [∀ a b : B, HasBinaryBiproducts (a ⟶ b)] in
theorem incl₂_comp_assoc' {a b : B} {f g h : a ⟶ b} {x : of a ⟶ of b} (η : f ⟶ g) (θ : g ⟶ h)
    (y : of₁ h ⟶ x) : incl₂ η ≫ incl₂ θ ≫ y = incl₂ (η ≫ θ) ≫ y := by
  rw [incl₂_comp, Category.assoc]

omit [GradedBicategory.IsLinear B k] in
theorem grιFE_grπFE : grιFE e ≫ grπFE e = 𝟙 _ := by
  simp only [grιFE, grπFE, Category.assoc, Iso.inv_hom_id_assoc, incl₂_comp_assoc',
    show ιFE e ≫ πFE e = 𝟙 _ by simp [ιFE, πFE], incl₂_id, Category.id_comp, Iso.hom_inv_id]

omit [GradedBicategory.IsLinear B k] in
theorem grι_grπ_self {j : ℕ} (hj : j < (S.wt (q + 1)).toNat) : grι e j ≫ grπ e j = 𝟙 _ := by
  simp only [grι, grπ, Category.assoc, Iso.inv_hom_id_assoc, incl₂_comp_assoc', ι_π_self e hj,
    incl₂_id, Category.id_comp, Iso.inv_hom_id]

omit [GradedBicategory.IsLinear B k] in
theorem grι_grπ_ne {j j' : ℕ} (h : j ≠ j') : grι e j ≫ grπ e j' = 0 := by
  simp only [grι, grπ, Category.assoc, Iso.inv_hom_id_assoc, incl₂_comp_assoc', ι_π_ne e h]
  change _ ≫ (incl _).map 0 ≫ _ = 0
  rw [Functor.map_zero, zero_comp, comp_zero]

omit [GradedBicategory.IsLinear B k] in
/-- The decomposition of the identity of `E F 1_n`, in the graded-Hom bicategory. -/
theorem grTotal :
    ∑ j ∈ Finset.range (S.wt (q + 1)).toNat, grπ e j ≫ grι e j + grπFE e ≫ grιFE e = 𝟙 _ := by
  have h : ∀ j ∈ Finset.range (S.wt (q + 1)).toNat, grπ e j ≫ grι e j =
      (S.rhoSourceIso q).hom ≫ incl₂ (π e j ≫ ι e j) ≫ (S.rhoSourceIso q).inv := by
    intro j _
    simp only [grπ, grι, Category.assoc, Iso.hom_inv_id_assoc, incl₂_comp_assoc']
  have hFE : grπFE e ≫ grιFE e =
      (S.rhoSourceIso q).hom ≫ incl₂ (πFE e ≫ ιFE e) ≫ (S.rhoSourceIso q).inv := by
    simp only [grπFE, grιFE, Category.assoc, Iso.inv_hom_id_assoc, incl₂_comp_assoc']
  rw [Finset.sum_congr rfl h, hFE, ← Preadditive.comp_sum, ← Preadditive.sum_comp,
    ← Preadditive.comp_add, ← Preadditive.add_comp]
  have : ∑ j ∈ Finset.range (S.wt (q + 1)).toNat, incl₂ (π e j ≫ ι e j) +
      incl₂ (πFE e ≫ ιFE e) = 𝟙 (of₁ (S.F q ≫ S.E q)) := by
    change ∑ j ∈ _, (incl _).map _ + (incl _).map _ = _
    rw [← Functor.map_sum, ← Functor.map_add, total e]
    exact (incl _).map_id _
  rw [this, Category.id_comp, Iso.hom_inv_id]

omit [GradedBicategory.IsLinear B k] in
theorem isHomogeneous_grιFE : IsHomogeneous (grιFE e) 2 :=
  ((S.isHomogeneous_rhoTargetIso_hom q).comp ((isHomogeneous_incl₂ _).comp
    (S.isHomogeneous_rhoSourceIso_inv q) rfl) rfl).of_eq (by ring)

omit [GradedBicategory.IsLinear B k] in
theorem isHomogeneous_grπFE : IsHomogeneous (grπFE e) (-2) :=
  ((S.isHomogeneous_rhoSourceIso_hom q).comp ((isHomogeneous_incl₂ _).comp
    (S.isHomogeneous_rhoTargetIso_inv q) rfl) rfl).of_eq (by ring)

omit [GradedBicategory.IsLinear B k] in
theorem isHomogeneous_grι (hn : 0 ≤ S.wt (q + 1)) (j : ℕ) :
    IsHomogeneous (grι e j) (2 * (j : ℤ) - 2 * S.wt (q + 1) + 2) :=
  ((shiftIso₁_inv_isHomogeneous (𝟙 (S.obj (q + 1))) _).comp ((isHomogeneous_incl₂ _).comp
    (S.isHomogeneous_rhoSourceIso_inv q) rfl) rfl).of_eq (by
      have h1 : (((S.wt (q + 1)).toNat : ℕ) : ℤ) = S.wt (q + 1) := Int.toNat_of_nonneg hn
      rw [h1]; simp only [wt]; ring)

omit [GradedBicategory.IsLinear B k] in
theorem isHomogeneous_grπ (hn : 0 ≤ S.wt (q + 1)) (j : ℕ) :
    IsHomogeneous (grπ e j) (2 * S.wt (q + 1) - 2 - 2 * (j : ℤ)) :=
  ((S.isHomogeneous_rhoSourceIso_hom q).comp ((isHomogeneous_incl₂ _).comp
    (shiftIso₁_hom_isHomogeneous (𝟙 (S.obj (q + 1))) _) rfl) rfl).of_eq (by
      have h1 : (((S.wt (q + 1)).toNat : ℕ) : ℤ) = S.wt (q + 1) := Int.toNat_of_nonneg hn
      rw [h1]; simp only [wt]; ring)

end Decomp

/-! ### Consequences at every weight -/

variable [∀ a b : B, HomFinite k (a ⟶ b)] [∀ a b : B, IsIdempotentComplete (a ⟶ b)] {S}

variable (S) in
/-- `E 1_m` has no endomorphisms of negative degree (Lemma 3.1 and its `n ≤ 0`
version). -/
theorem finrank_end_E_neg (r : ℤ) {l : ℤ} (hl : l < 0) :
    finrank k (S.E r ⟶ (S.E r)⟦l⟧) = 0 := by
  by_cases hr : 0 ≤ S.wt r
  · exact S.lem1_neg hr (fun r' _ => S.adjHyp r') r le_rfl l hl
  · exact S.lem1Neg_neg (le_of_lt (not_le.1 hr)) (fun r' _ => S.adjHyp r') r le_rfl l hl

variable (S) in
theorem grE_end_eq_zero {r : ℤ} {ψ : S.grE r ⟶ S.grE r} {l : ℤ} (hψ : IsHomogeneous ψ l)
    (hl : l < 0) : ψ = 0 :=
  GradedHomBicat.eq_zero_of_isHomogeneous hψ (S.finrank_end_E_neg r hl)

variable (S) in
/-- A homogeneous `1_n ⟶ F E 1_n` of negative degree vanishes. -/
theorem eq_zero_to_ER {q : ℤ} {χ : 𝟙 (of (S.obj (q + 1))) ⟶ S.grE (q + 1) ≫ S.grR (q + 1)}
    {d : ℤ} (hχ : IsHomogeneous χ d) (hd : d < 0) : χ = 0 :=
  eq_zero_of_isHomogeneous_unit_side (S.grAdj (q + 1)) (c := 0) (isHomogeneous_incl₂ _)
    (fun _ hψ => S.grE_end_eq_zero hψ (by omega)) hχ

variable (S) in
/-- A homogeneous `F E 1_n ⟶ 1_n` of degree `< 2n + 2` vanishes. -/
theorem eq_zero_from_ER {q : ℤ} {χ : S.grE (q + 1) ≫ S.grR (q + 1) ⟶ 𝟙 (of (S.obj (q + 1)))}
    {d : ℤ} (hχ : IsHomogeneous χ d) (hd : d < 2 * S.wt (q + 1) + 2) : χ = 0 :=
  eq_zero_of_isHomogeneous_counit_side (S.leftAdjN (q + 1)) (S.leftAdjN_spec (q + 1)).1
    (fun _ hψ => S.grE_end_eq_zero hψ (by omega)) hχ

variable (S) in
/-- **(A3)** (a curl vanishes): for `k < n`, `cup_k ≫ σ = 0` (by degrees). -/
theorem cupD_comp_grSigma {q : ℤ} {j : ℕ} (hj : (j : ℤ) < S.wt (q + 1)) :
    S.cupD (S.leftAdjN q) j ≫ S.grSigma q = 0 :=
  S.eq_zero_to_ER ((S.isHomogeneous_cupD _ (S.leftAdjN_spec q).1 j).comp
    (S.isHomogeneous_grSigma q) rfl) (by omega)

variable (S) in
/-- The `k`-th component of `ζ⁻¹` (CL (5.8) with the coefficients of Proposition 5.2):
`comp_k = ∑_{g < n - k} cap_{n-1-k-g} ∘ (fake counter-clockwise bubble of degree 2g)`. -/
def compK (q : ℤ) (j : ℕ) : S.grR q ≫ S.grE q ⟶ 𝟙 (of (S.obj (q + 1))) :=
  ∑ g ∈ Finset.range ((S.wt (q + 1)).toNat - j),
    S.capD q ((S.wt (q + 1)).toNat - 1 - j - g) ≫ S.ccwLN q (-S.wt (q + 1) - 1 + g)

variable (S) in
/-- **(A4)**: `σ' ≫ comp_k = 0` (by degrees). -/
theorem sideL_comp_compK (q : ℤ) (j : ℕ) :
    S.sideLN q ≫ S.compK q j = 0 := by
  rw [compK, Preadditive.comp_sum]
  refine Finset.sum_eq_zero fun g hg => ?_
  have hg' := Finset.mem_range.1 hg
  rw [← Category.assoc, S.eq_zero_from_ER ((S.isHomogeneous_sideLN q).comp
    (S.isHomogeneous_capD q _) rfl) (by omega), zero_comp]

variable (S) in
/-- Real clockwise bubbles with integer labels `≥ n - 1`. -/
theorem cwL_eq_cwBub {q : ℤ} (hn1 : 1 ≤ S.wt (q + 1)) (i : ℕ) :
    S.cwLN q (S.wt (q + 1) - 1 + i) = S.cwBub (S.leftAdjN q) ((S.wt (q + 1)).toNat - 1 + i) := by
  unfold cwLN
  rw [cwL_of_nonneg _ _ _ (by omega)]
  congr 1
  omega

variable (S) in
/-- **(A1)**: `cup_{k'} ≫ comp_k = δ_{k k'}` for `k, k' < n`. -/
theorem cupD_comp_compK {q : ℤ} {j j' : ℕ} (hj : j < (S.wt (q + 1)).toNat)
    (hj' : j' < (S.wt (q + 1)).toNat) :
    S.cupD (S.leftAdjN q) j' ≫ S.compK q j = if j = j' then 𝟙 _ else 0 := by
  rw [compK, Preadditive.comp_sum]
  set N := (S.wt (q + 1)).toNat with hN
  have hn1 : 1 ≤ S.wt (q + 1) := by omega
  have hNn : (N : ℤ) = S.wt (q + 1) := Int.toNat_of_nonneg (by omega)
  have hterm : ∀ g, S.cupD (S.leftAdjN q) j' ≫ S.capD q (N - 1 - j - g) ≫
      S.ccwLN q (-S.wt (q + 1) - 1 + g) =
        S.ccwLN q (-S.wt (q + 1) - 1 + g) *
          End.of (S.cwBub (S.leftAdjN q) (j' + (N - 1 - j - g))) := by
    intro g
    rw [← Category.assoc, cupD_comp_capD]
    rfl
  simp only [hterm]
  -- the terms with `j' + (N - 1 - j - g) < N - 1` vanish
  have hvan : ∀ g, j' + (N - 1 - j - g) < N - 1 →
      S.cwBub (S.leftAdjN q) (j' + (N - 1 - j - g)) = 0 := fun g hg =>
    S.cwBubN_eq_zero (by omega)
  by_cases hjj : j' < j
  · rw [ite_eq_right (by omega)]
    refine Finset.sum_eq_zero fun g hg => ?_
    rw [hvan g (by have := Finset.mem_range.1 hg; omega), mul_zero]
  · set D := j' - j with hD
    have hDN : D + 1 ≤ N - j := by omega
    rw [← Finset.sum_range_add_sum_Ico _ hDN, Finset.sum_eq_zero (s := Finset.Ico _ _)
      (fun g hg => by rw [hvan g (by have := Finset.mem_Ico.1 hg; omega), mul_zero]), add_zero]
    have hG := S.grassmannian_cw_ccw hn1 (K := D) (by omega)
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
      S.cwL_eq_cwBub hn1, show j' + (N - 1 - j - g) = N - 1 + (D - g) by omega]

variable (S) in
/-- **CL Proposition 5.1 (form of `ζ⁻¹`), first part, and (A2)**: for `n = wt (q + 1) ≥ 0` there
are a scalar `β` and maps `φ_k : E F 1_n → 1_n` with `σ' ≫ β σ = 1_{FE1_n}` and
`1_{EF1_n} = β σ σ' + ∑_{k<n} φ_k ∘ cup_k`. -/
theorem exists_decompEF_aux {q : ℤ} (hn : 0 ≤ S.wt (q + 1)) :
    ∃ (β : k) (φ : ℕ → (S.grR q ≫ S.grE q ⟶ 𝟙 (of (S.obj (q + 1))))),
      S.sideLN q ≫ (β • S.grSigma q) = 𝟙 _ ∧
      β • (S.grSigma q ≫ S.sideLN q) +
        ∑ j ∈ Finset.range (S.wt (q + 1)).toNat, φ j ≫ S.cupD (S.leftAdjN q) j = 𝟙 _ := by
  set N := (S.wt (q + 1)).toNat with hN
  have hNn : (N : ℤ) = S.wt (q + 1) := Int.toNat_of_nonneg hn
  -- the weight `n` is zero: everything vanishes
  by_cases h1 : IsZero (𝟙 (S.obj (q + 1)))
  · have hRE : IsZero (S.grR q ≫ S.grE q) :=
      (incl _).map_isZero (isZero_comp_left ((shiftFunctor _ _).map_isZero
        (S.isZero_F_of_right h1)) _)
    have hER : IsZero (S.grE (q + 1) ≫ S.grR (q + 1)) :=
      (incl _).map_isZero (isZero_comp_left (S.isZero_E_of_left h1) _)
    exact ⟨1, 0, hER.eq_of_src _ _, hRE.eq_of_src _ _⟩
  obtain ⟨e⟩ := S.exists_EFDecomp hn
  -- the matrix of the cups in the summands `1_n⟨n-1-2j⟩` is triangular
  have hcupπ : ∀ j i : ℕ, IsHomogeneous (S.cupD (S.leftAdjN q) j ≫ grπ e i)
      (2 * (j : ℤ) - 2 * (i : ℤ)) := fun j i =>
    (S.isHomogeneous_cupD _ (S.leftAdjN_spec q).1 j).comp (isHomogeneous_grπ e hn i) (by ring)
  have hlow : ∀ j i, j < N → i < N → j < i → S.cupD (S.leftAdjN q) j ≫ grπ e i = 0 :=
    fun j i _ _ hji => S.eq_zero_of_isHomogeneous_neg (hcupπ j i) (by omega)
  have hcupFE : ∀ j, j < N → S.cupD (S.leftAdjN q) j ≫ grπFE e = 0 := fun j hj =>
    S.eq_zero_to_ER ((S.isHomogeneous_cupD _ (S.leftAdjN_spec q).1 j).comp
      (isHomogeneous_grπFE e) rfl) (by omega)
  have hexpand : ∀ j, j < N → ∀ {Y : _} (y : S.grR q ≫ S.grE q ⟶ Y),
      S.cupD (S.leftAdjN q) j ≫ y =
        ∑ i ∈ Finset.range N, (S.cupD (S.leftAdjN q) j ≫ grπ e i) ≫ grι e i ≫ y := by
    intro j hj Y y
    conv_lhs => rw [← Category.id_comp y, ← grTotal e]
    rw [Preadditive.add_comp, Preadditive.comp_add, Preadditive.sum_comp, Preadditive.comp_sum,
      Category.assoc, ← Category.assoc (S.cupD _ j) (grπFE e), hcupFE j hj, zero_comp, add_zero]
    simp only [Category.assoc]
    rfl
  have hexp : ∀ j, j < N → S.cupD (S.leftAdjN q) j =
      ∑ i ∈ Finset.range N, (S.cupD (S.leftAdjN q) j ≫ grπ e i) ≫ grι e i := by
    intro j hj
    have := hexpand j hj (𝟙 _)
    simpa only [Category.comp_id] using this
  have hdiag : ∀ j, j < N → ∃ s : k, s ≠ 0 ∧
      S.cupD (S.leftAdjN q) j ≫ grπ e j = s • 𝟙 (𝟙 (of (S.obj (q + 1)))) := by
    intro j hj
    obtain ⟨s, hs⟩ := S.exists_eq_smul_id ((hcupπ j j).of_eq (by ring))
    refine ⟨s, fun hs0 => h1 ?_, hs⟩
    have hn1 : 1 ≤ S.wt (q + 1) := by omega
    have hbub : S.cupD (S.leftAdjN q) j ≫ S.capD q (N - 1 - j) = 𝟙 _ := by
      rw [cupD_comp_capD, show j + (N - 1 - j) = N - 1 by omega]
      exact cwBub_deg_zero S hn1
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
          ((isHomogeneous_grι e hn i).comp (S.isHomogeneous_capD q _) (by omega))
          (by omega), comp_zero]
  -- the projection onto `⊕_j 1_n⟨n-1-2j⟩` is a combination of the cups
  obtain ⟨φ, hφ⟩ : InCupSpan N (S.cupD (S.leftAdjN q))
      (∑ j ∈ Finset.range N, grπ e j ≫ grι e j) :=
    InCupSpan.sum _ fun j hj => inCupSpan_of_triangular (grι e) (grπ e) hlow hdiag hexp j
      (Finset.mem_range.1 hj) (grπ e j)
  -- the weight `n + 2` is zero: `F E 1_n` vanishes
  by_cases h2 : IsZero (𝟙 (S.obj (q + 1 + 1)))
  · have hER : IsZero (S.grE (q + 1) ≫ S.grR (q + 1)) :=
      (incl _).map_isZero (isZero_comp_left (S.isZero_E_of_right h2) _)
    refine ⟨1, φ, hER.eq_of_src _ _, ?_⟩
    rw [hER.eq_of_tgt (S.grSigma q) 0, zero_comp, smul_zero, zero_add, ← hφ]
    have := grTotal e
    rwa [hER.eq_of_tgt (grπFE e) 0, zero_comp, add_zero] at this
  -- Lemma 3.12: the projection and the inclusion of `F E 1_n` are multiples of `σ` and `σ'`
  obtain ⟨c, hc0, hσ⟩ := S.exists_grSigma_eq_smul_πFE hn (fun r' _ => S.numAdj r') h2 e
  have hσ' : S.grSigma q = c • grπFE e := hσ
  obtain ⟨a, ha⟩ : ∃ a : k, grιFE e = a • S.sideLN q := by
    have hcd : IsHomogeneous ((S.rhoTargetIso q).inv ≫ S.sideLN q ≫ (S.rhoSourceIso q).hom) 0 :=
      ((S.isHomogeneous_rhoTargetIso_inv q).comp ((S.isHomogeneous_sideLN q).comp
        (S.isHomogeneous_rhoSourceIso_hom q) rfl) rfl).of_eq (by ring)
    obtain ⟨g, hg⟩ := exists_incl₂_of_isHomogeneous hcd
    have hdim : finrank k (S.E (q + 1) ≫ S.F (q + 1) ⟶ S.F q ≫ S.E q) = 1 :=
      S.lemHoms_FE_EF_eq_one (r₀ := q + 1) hn (fun r' _ => S.adjHyp r') le_rfl (S.adjHyp q)
        (S.adjHyp (q + 1)) h2
    have hsL : S.sideLN q = (S.rhoTargetIso q).hom ≫ incl₂ g ≫ (S.rhoSourceIso q).inv := by
      rw [← hg]
      simp
    by_cases hg0 : g = 0
    · have hs0 : S.sideLN q = 0 := by
        rw [hsL, hg0]
        change _ ≫ (incl _).map 0 ≫ _ = 0
        rw [Functor.map_zero, zero_comp, comp_zero]
      have hτ : S.grCross q = 0 := by
        have : S.grCross q = mateEquiv (S.leftAdjN q) (S.leftAdjN (q + 1)) (S.sideLN q) := by
          exact ((Bicategory.mateEquiv _ _).apply_symm_apply (S.grCross q)).symm
        rw [this, hs0, mateEquiv_zero]
      have hσ0 : S.grSigma q = 0 := by rw [grSigma_eq_mateEquiv, hτ, mateEquiv_zero]
      have hπ0 : grπFE e = 0 := by
        rw [hσ'] at hσ0
        exact (smul_eq_zero.1 hσ0).resolve_left hc0
      refine ⟨0, ?_⟩
      rw [zero_smul]
      calc grιFE e = grιFE e ≫ grπFE e ≫ grιFE e := by
            rw [← Category.assoc, grιFE_grπFE, Category.id_comp]
        _ = 0 := by rw [hπ0, zero_comp, comp_zero]
    · obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' g hg0).1 hdim (ιFE e)
      refine ⟨a, ?_⟩
      rw [grιFE, ← ha, hsL]
      change _ ≫ (incl _).map (a • g) ≫ _ = _
      rw [Functor.map_smul, Linear.smul_comp, Linear.comp_smul]
      rfl
  refine ⟨a * c⁻¹, φ, ?_, ?_⟩
  · rw [hσ', smul_smul, mul_assoc, inv_mul_cancel₀ hc0, mul_one, Linear.comp_smul,
      ← Linear.smul_comp, ← ha, grιFE_grπFE]
  · rw [hσ', Linear.smul_comp, smul_smul, mul_assoc, inv_mul_cancel₀ hc0, mul_one,
      ← Linear.comp_smul, ← ha, ← hφ]
    exact (add_comm _ _).trans (grTotal e)

variable (S) in
/-- **CL Propositions 5.1, 5.2 and Corollary 5.3 for `n ≥ 0`** (relations (A2), (A5)): for
`n = wt (q + 1) ≥ 0` there is a scalar `β` with `σ' ≫ β σ = 1_{FE1_n}` and
`1_{EF1_n} = β σ σ' + ∑_{k<n} comp_k ∘ cup_k`, where `comp_k` is built from the fake bubbles
(`compK`); i.e. `ζ⁻¹ = β σ ⊕ ⊕_k comp_k`. (`β = -1` by CL Lemma 5.4.) -/
theorem decompEF_beta {q : ℤ} (hn : 0 ≤ S.wt (q + 1)) :
    ∃ β : k, S.sideLN q ≫ (β • S.grSigma q) = 𝟙 _ ∧
      β • (S.grSigma q ≫ S.sideLN q) +
        ∑ j ∈ Finset.range (S.wt (q + 1)).toNat, S.compK q j ≫ S.cupD (S.leftAdjN q) j =
          𝟙 _ := by
  obtain ⟨β, φ, h1, h2⟩ := S.exists_decompEF_aux hn
  refine ⟨β, h1, ?_⟩
  have hφ : ∀ j ∈ Finset.range (S.wt (q + 1)).toNat, φ j = S.compK q j := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    have := congrArg (· ≫ S.compK q j) h2
    simp only [Preadditive.add_comp, Preadditive.sum_comp, Linear.smul_comp, Category.assoc,
      S.sideL_comp_compK, comp_zero, smul_zero, zero_add, Category.id_comp] at this
    rw [← this, Finset.sum_eq_single_of_mem j hj]
    · rw [S.cupD_comp_compK hj' hj', ite_eq_left rfl, Category.comp_id]
    · intro i hi hij
      rw [S.cupD_comp_compK hj' (Finset.mem_range.1 hi), ite_eq_right (Ne.symm hij), comp_zero]
  rw [← h2]
  congr 1
  exact Finset.sum_congr rfl fun j hj => by rw [hφ j hj]

end StrongSl2

end Categorification.TwoRep

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.Basic

/-!
# Krull–Schmidt, cancellation, bricks and ranks (CL §3.1)

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, §3.1 (`Some general notions`): "The fact that the space of maps between
any two 1-morphisms in a `Q`-strong 2-representation of `g` is finite dimensional means that the
Krull-Schmidt property holds for Hom categories. [...] In particular, this means that if `A, B, C`
are morphisms and `V` is a `ℤ`-graded vector space then we have the following cancellation laws
(see section 4 of [CK3]): `A ⊕ B ≅ A ⊕ C ⇒ B ≅ C`, `A ⊗_k V ≅ B ⊗_k V ⇒ A ≅ B`."

We work in a `k`-linear category `𝒞` over a field with binary biproducts, idempotent complete and
Hom-finite (the Hom categories of a `Q`-strong 2-representation), reusing the Krull–Schmidt
theory of `Categorification.KrullSchmidtCat` (local endomorphism rings of indecomposables, the
multiplicity functionals `multK` on the split Grothendieck group).

## Main results

* `nonempty_iso_of_of_eq`: **Krull–Schmidt uniqueness in iso form**: objects with the same class
  in the split Grothendieck group are isomorphic.
* `cancel_biprod` (**first cancellation law**): `A ⊕ B ≅ A ⊕ C ⇒ B ≅ C`.
* `cancel_shiftSum` (**second cancellation law**): for a graded vector space `V ≠ 0`, given by the
  nonempty list `L` of the degrees of a homogeneous basis, `A ⊗ V = ⊕_{d ∈ L} A⟨d⟩`, and if no
  indecomposable object is isomorphic to a nonzero shift of itself, then
  `A ⊗ V ≅ B ⊗ V ⇒ A ≅ B`.
* `IsBrick`, `isBrick_iff`: a brick is an indecomposable `A` with `End(A) = k`; equivalently
  `dim End(A) = 1`.
* `rk0 k A f`: the `A`-rank of `f : X ⟶ Y`, the rank of the pairing
  `Hom(A, X) × Hom(Y, A) → End(A)`, `(g, h) ↦ g ≫ f ≫ h`; `rk k A f = ∑ᶠ i, rk0 k (A⟨i⟩) f`, the
  total `A`-rank. Basic properties: `rk0_id` (`rk_A(1_A) = 1` for a brick), `rk0_le_left`,
  `rk0_le_right`, `rk0_comp_iso`, `rk0_iso_comp`.

## Precision about the source

* The second cancellation law is **false** as stated without further hypotheses: it fails for
  `V = 0`, and it fails when an indecomposable is isomorphic to a nonzero shift of itself (if
  `Z ≅ Z⟨2⟩ ≇ Z⟨1⟩`, then for `V = k ⊕ k⟨1⟩` the objects `A = Z ⊕ Z` and `B = Z ⊕ Z⟨1⟩` satisfy
  `A ⊗ V ≅ Z² ⊕ Z⟨1⟩² ≅ B ⊗ V` while `A ≇ B` (such `Z` exist, e.g. for `ℤ/2`-graded vector
  spaces with `⟨1⟩` the parity shift); in `K₀` this is the zero divisor
  `(1 + q)(1 - q) = 0` of `ℤ[q]/(q² - 1)`). We assume `V ≠ 0` and the rigidity hypothesis
  `hrig` (no indecomposable is isomorphic to a nonzero shift of itself), under which `K₀` is a
  free `ℤ[q, q⁻¹]`-module (`KrullSchmidtCat.indecBasis`). The first law needs neither.
* CL's second description of the `A`-rank (via decompositions `X = A ⊗ V ⊕ B`) is not
  formalized here; the definition used is CL's first one (rank of the pairing). Since `End(A)` is
  one-dimensional, the rank of the pairing with values in `End(A)` is the rank of the bilinear form
  with values in `k`.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits Module
open KrullSchmidtCat

universe v u

variable (k : Type*) [Field k] {𝒞 : Type u} [Category.{v} 𝒞] [Preadditive 𝒞] [Linear k 𝒞]
  [HomFinite k 𝒞] [HasBinaryBiproducts 𝒞] [IsIdempotentComplete 𝒞]

section Cancellation

omit [Linear k 𝒞] [HomFinite k 𝒞] in
/-- **The complement of a retract** in an idempotent complete category: if `f ≫ g = 𝟙 Z` for
`f : Z ⟶ X`, `g : X ⟶ Z`, then `X ≅ Z ⊞ Y` for some `Y`. -/
theorem exists_iso_biprod_of_retract {Z X : 𝒞} (f : Z ⟶ X) (g : X ⟶ Z) (hfg : f ≫ g = 𝟙 Z) :
    ∃ Y : 𝒞, Nonempty (X ≅ Z ⊞ Y) := by
  have he : (g ≫ f) ≫ (g ≫ f) = g ≫ f := by
    rw [Category.assoc, reassoc_of% hfg]
  obtain ⟨Y, i', p', h₁, h₂⟩ :=
    IsIdempotentComplete.idempotents_split X (𝟙 X - g ≫ f) (idem_one_sub he)
  refine ⟨Y, ⟨isoOfData f g i' p' hfg h₁ ?_ ?_ ?_⟩⟩
  · have h0 : f ≫ (𝟙 X - g ≫ f) = 0 := by
      rw [Preadditive.comp_sub, Category.comp_id, reassoc_of% hfg, sub_self]
    calc f ≫ p' = f ≫ (p' ≫ i') ≫ p' := by rw [Category.assoc, h₁, Category.comp_id]
      _ = 0 := by rw [h₂, ← Category.assoc, h0, zero_comp]
  · have h0 : (𝟙 X - g ≫ f) ≫ g = 0 := by
      rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, hfg, Category.comp_id, sub_self]
    calc i' ≫ g = (i' ≫ p') ≫ i' ≫ g := by rw [h₁, Category.id_comp]
      _ = i' ≫ (p' ≫ i') ≫ g := by simp only [Category.assoc]
      _ = 0 := by rw [h₂, h0, comp_zero]
  · rw [h₂]; abel

omit [HasBinaryBiproducts 𝒞] in
include k in
/-- Every nonzero object has an indecomposable retract (induction on `dim End(X)`). -/
theorem exists_indec_retract {X : 𝒞} (hX : ¬ IsZero X) :
    ∃ (Z : 𝒞) (f : Z ⟶ X) (g : X ⟶ Z), IsIndec Z ∧ f ≫ g = 𝟙 Z := by
  induction h : finrank k (X ⟶ X) using Nat.strong_induction_on generalizing X with
  | _ n ih =>
    by_cases hi : IsIndec X
    · exact ⟨X, 𝟙 X, 𝟙 X, hi, Category.comp_id _⟩
    obtain ⟨e, he, he0, he1⟩ : ∃ e : X ⟶ X, e ≫ e = e ∧ e ≠ 0 ∧ e ≠ 𝟙 X := by
      by_contra hne
      push_neg at hne
      exact hi ⟨hX, fun e he => by
        by_cases h' : e = 0
        · exact Or.inl h'
        · exact Or.inr (hne e he h')⟩
    obtain ⟨Y, Z, i, p, i', p', h₁, h₂, h₃, h₄, h₅, h₆⟩ := exists_split e he
    have hY : ¬ IsZero Y := fun hY => he0 (by rw [← h₅, hY.eq_of_src i, Limits.comp_zero])
    have hZ : ¬ IsZero Z := fun hZ => he1 (by
      have : 𝟙 X - e = 0 := by rw [← h₆, hZ.eq_of_src i', Limits.comp_zero]
      exact (sub_eq_zero.1 this).symm)
    obtain ⟨W, f, g, hW, hfg⟩ := ih _ (by rw [← h]; exact finrank_end_lt k i p i' p' h₁ h₂ h₃ h₄ hZ)
      hY rfl
    exact ⟨W, f ≫ i, p ≫ g, hW, by rw [Category.assoc, reassoc_of% h₁, hfg]⟩

omit [HasBinaryBiproducts 𝒞] [IsIdempotentComplete 𝒞] in
theorem mult_nonneg {Z : 𝒞} (hZ : IsIndec Z) (X : 𝒞) : 0 ≤ mult k hZ X := by
  rw [mult, sub_nonneg, Nat.cast_le]
  exact Submodule.finrank_le _

omit [HasBinaryBiproducts 𝒞] [IsIdempotentComplete 𝒞] in
/-- If the multiplicity of the indecomposable `Z` in `X` is positive, `Z` is a retract of `X`. -/
theorem exists_retract_of_mult_pos {Z X : 𝒞} (hZ : IsIndec Z) (h : 0 < mult k hZ X) :
    ∃ (f : Z ⟶ X) (g : X ⟶ Z), f ≫ g = 𝟙 Z := by
  rw [mult, sub_pos, Nat.cast_lt] at h
  have hne : rad k hZ X ≠ ⊤ := fun ht => by rw [ht, finrank_top] at h; exact lt_irrefl _ h
  obtain ⟨f, -, hf⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.2 hne : rad k hZ X < ⊤)
  rw [mem_rad] at hf
  push_neg at hf
  obtain ⟨g, u, hu⟩ := hf
  refine ⟨f, g ≫ (↑u⁻¹ : End Z), ?_⟩
  have := u.inv_mul
  rw [End.mul_def, hu] at this
  rw [← Category.assoc]; exact this

omit [IsIdempotentComplete 𝒞] in
theorem multK_pos_of_iso_biprod {Z X Y : 𝒞} (hZ : IsIndec Z) (φ : X ≅ Z ⊞ Y) :
    0 < multK k hZ (SplitK0.of X) := by
  rw [SplitK0.of_eq_add_of_iso φ, map_add, multK_of k hZ Y]
  have := multK_self_pos k hZ
  have := mult_nonneg k hZ Y
  omega

include k in
/-- **Krull–Schmidt uniqueness, iso form**: in a Hom-finite idempotent complete `k`-linear
category, two objects with the same class in the split Grothendieck group are isomorphic.
(Induction on `dim End(X)`: split off an indecomposable summand `Z` of `X`; its multiplicity in
`Y` is positive, so it is also a summand of `Y`; cancel it in `K₀`.) -/
theorem nonempty_iso_of_of_eq {X Y : 𝒞} (h : SplitK0.of X = SplitK0.of Y) : Nonempty (X ≅ Y) := by
  induction hn : finrank k (X ⟶ X) using Nat.strong_induction_on generalizing X Y with
  | _ n ih =>
    by_cases hX : IsZero X
    · by_cases hY : IsZero Y
      · exact ⟨hX.iso hY⟩
      · exfalso
        obtain ⟨Z, f, g, hZ, hfg⟩ := exists_indec_retract k hY
        obtain ⟨Y', ⟨φ⟩⟩ := exists_iso_biprod_of_retract f g hfg
        have := multK_pos_of_iso_biprod k hZ φ
        rw [← h, SplitK0.of_isZero hX, map_zero] at this
        exact lt_irrefl _ this
    · obtain ⟨Z, f, g, hZ, hfg⟩ := exists_indec_retract k hX
      obtain ⟨X', ⟨φ⟩⟩ := exists_iso_biprod_of_retract f g hfg
      have hpos := multK_pos_of_iso_biprod k hZ φ
      rw [h, multK_of] at hpos
      obtain ⟨f', g', hfg'⟩ := exists_retract_of_mult_pos k hZ hpos
      obtain ⟨Y', ⟨ψ⟩⟩ := exists_iso_biprod_of_retract f' g' hfg'
      have h' : SplitK0.of X' = SplitK0.of Y' := by
        have := h
        rw [SplitK0.of_eq_add_of_iso φ, SplitK0.of_eq_add_of_iso ψ] at this
        exact add_left_cancel this
      have hlt : finrank k (X' ⟶ X') < n := by
        rw [← hn]
        exact finrank_end_lt k (biprod.inr ≫ φ.inv) (φ.hom ≫ biprod.snd) (biprod.inl ≫ φ.inv)
          (φ.hom ≫ biprod.fst) (by simp) (by simp) (by simp) (by simp) hZ.1
      obtain ⟨χ⟩ := ih _ hlt h' rfl
      exact ⟨φ ≪≫ biprod.mapIso (Iso.refl Z) χ ≪≫ ψ.symm⟩

include k in
/-- **The first cancellation law** (CL §3.1): `A ⊕ B ≅ A ⊕ C ⇒ B ≅ C`. -/
theorem cancel_biprod {A B C : 𝒞} (e : A ⊞ B ≅ A ⊞ C) : Nonempty (B ≅ C) := by
  refine nonempty_iso_of_of_eq k ?_
  have := SplitK0.of_iso e
  rw [SplitK0.of_biprod, SplitK0.of_biprod] at this
  exact add_left_cancel this

section Shift

variable [HasShift 𝒞 ℤ] [∀ n : ℤ, (shiftFunctor 𝒞 n).Additive]

omit [Linear k 𝒞] [HomFinite k 𝒞] [IsIdempotentComplete 𝒞] in
variable (𝒞) in
/-- The shift data on `K₀(𝒞)` of a grading shift `⟨1⟩` (a `HasShift 𝒞 ℤ` with additive shift
functors), making `K₀(𝒞)` a `ℤ[q, q⁻¹]`-module. -/
def k0ShiftOfHasShift : SplitK0.K0Shift 𝒞 where
  sh n X := X⟦n⟧
  sh_iso n _ _ e := ⟨(shiftFunctor 𝒞 n).mapIso e⟩
  sh_biprod n X Y := ⟨mapBiprodIso (shiftFunctor 𝒞 n) X Y⟩
  sh_zero X := ⟨(shiftFunctorZero 𝒞 ℤ).app X⟩
  sh_add m n X := ⟨(shiftFunctorAdd 𝒞 m n).app X⟩

/-- The augmentation `ℤ[q, q⁻¹] → ℤ`, `q ↦ 1`. -/
def augmentation : LaurentPolynomial ℤ →ₐ[ℤ] ℤ :=
  AddMonoidAlgebra.lift ℤ ℤ ℤ 1

theorem augmentation_T (n : ℤ) : augmentation (LaurentPolynomial.T n) = 1 := by
  rw [augmentation, LaurentPolynomial.T, AddMonoidAlgebra.lift_single]
  simp

theorem augmentation_sum_T (L : List ℤ) :
    augmentation (L.map LaurentPolynomial.T).sum = L.length := by
  induction L with
  | nil => simp
  | cons d L ih =>
    rw [List.map_cons, List.sum_cons, map_add, augmentation_T, ih, List.length_cons]
    push_cast; ring

/-- The graded dimension `∑_{d ∈ L} q^d` of `V = ⊕_{d ∈ L} k⟨d⟩` is not a zero divisor if
`V ≠ 0`. -/
theorem sum_T_mem_nonZeroDivisors {L : List ℤ} (hL : L ≠ []) :
    (L.map LaurentPolynomial.T).sum ∈ nonZeroDivisors (LaurentPolynomial ℤ) := by
  refine mem_nonZeroDivisors_of_ne_zero fun h => ?_
  have := congrArg augmentation h
  rw [augmentation_sum_T, map_zero] at this
  exact hL (List.eq_nil_of_length_eq_zero (by exact_mod_cast this))

variable [HasZeroObject 𝒞]

omit [Linear k 𝒞] [HomFinite k 𝒞] [IsIdempotentComplete 𝒞] in
theorem of_lsum_shift (A : 𝒞) (L : List ℤ) :
    letI := k0ShiftOfHasShift 𝒞
    SplitK0.of (lsum (L.map fun d => A⟦d⟧)) =
      (L.map fun d => (LaurentPolynomial.T d : LaurentPolynomial ℤ)).sum • SplitK0.of A := by
  letI := k0ShiftOfHasShift 𝒞
  induction L with
  | nil => simp [SplitK0.of_isZero (isZero_zero 𝒞)]
  | cons d L ih =>
    rw [List.map_cons, lsum_cons, SplitK0.of_biprod, ih, List.map_cons, List.sum_cons, add_smul,
      SplitK0.T_smul_of]
    rfl

include k in
/-- **The second cancellation law** (CL §3.1): `A ⊗ V ≅ B ⊗ V ⇒ A ≅ B` for a graded vector
space `V = ⊕_{d ∈ L} k⟨d⟩`, **under the hypotheses `V ≠ 0` and that no indecomposable object is
isomorphic to a nonzero shift of itself**, without which the statement is false (see the module
docstring). -/
theorem cancel_shiftSum (hrig : ∀ (n : ℤ) (X : 𝒞), IsIndec X → Nonempty (X⟦n⟧ ≅ X) → n = 0)
    {L : List ℤ} (hL : L ≠ []) {A B : 𝒞}
    (e : lsum (L.map fun d => A⟦d⟧) ≅ lsum (L.map fun d => B⟦d⟧)) : Nonempty (A ≅ B) := by
  letI := k0ShiftOfHasShift 𝒞
  refine nonempty_iso_of_of_eq k ?_
  have h := SplitK0.of_iso e
  rw [of_lsum_shift, of_lsum_shift, ← sub_eq_zero, ← smul_sub] at h
  exact sub_eq_zero.1 (eq_zero_of_smul_eq_zero k hrig (sum_T_mem_nonZeroDivisors hL) h)

end Shift

end Cancellation

/-! ## Bricks and `A`-rank -/

section Rank

omit [HomFinite k 𝒞] [HasBinaryBiproducts 𝒞] [IsIdempotentComplete 𝒞] in
variable {k} in
/-- A **brick** (CL §3.1): an indecomposable object `A` with `End(A) = k`. -/
def IsBrick (k : Type*) [Field k] [Linear k 𝒞] (A : 𝒞) : Prop :=
  IsIndec A ∧ finrank k (A ⟶ A) = 1

omit [HasBinaryBiproducts 𝒞] [IsIdempotentComplete 𝒞] in
/-- An object is a brick iff its endomorphism algebra is one-dimensional. -/
theorem isBrick_iff {A : 𝒞} : IsBrick k A ↔ finrank k (A ⟶ A) = 1 := by
  refine ⟨And.right, fun h => ?_⟩
  unfold IsBrick IsIndec
  refine ⟨⟨fun hA => ?_, fun e he => ?_⟩, h⟩
  · have := finrank_hom_of_isZero_left k hA A
    omega
  · have h1 : (𝟙 A : A ⟶ A) ≠ 0 := fun h0 => by
      have := finrank_hom_of_isZero_left k ((IsZero.iff_id_eq_zero A).2 h0) A
      omega
    obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' (𝟙 A) h1).1 h e
    rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul] at he
    have hc : c * c = c := smul_left_injective k h1 he
    have : c * (c - 1) = 0 := by rw [mul_sub, hc, mul_one, sub_self]
    rcases mul_eq_zero.1 this with h0 | h0
    · left; rw [h0, zero_smul]
    · right; rw [sub_eq_zero.1 h0, one_smul]

omit [HomFinite k 𝒞] [HasBinaryBiproducts 𝒞] [IsIdempotentComplete 𝒞] in
variable {k} in
/-- The pairing `Hom(A, X) × Hom(Y, A) → End(A)`, `(g, h) ↦ g ≫ f ≫ h`, attached to
`f : X ⟶ Y` (CL §3.1). -/
def rankPairing (k : Type*) [Field k] [Linear k 𝒞] (A : 𝒞) {X Y : 𝒞} (f : X ⟶ Y) :
    (A ⟶ X) →ₗ[k] (Y ⟶ A) →ₗ[k] (A ⟶ A) :=
  LinearMap.mk₂ k (fun g h => g ≫ f ≫ h) (fun g g' h => by simp) (fun c g h => by simp)
    (fun g h h' => by simp) (fun c g h => by simp)

omit [HomFinite k 𝒞] [HasBinaryBiproducts 𝒞] [IsIdempotentComplete 𝒞] in
variable {k} in
/-- **The `A`-rank** `rk⁰_A(f)` of `f : X ⟶ Y` (CL §3.1): the rank of the pairing
`Hom(A, X) × Hom(Y, A) → Hom(A, A)`, `(g, h) ↦ g ≫ f ≫ h`. For a brick `A`, `Hom(A, A) = k` and
this is the rank of a `k`-valued bilinear form. -/
def rk0 (k : Type*) [Field k] [Linear k 𝒞] (A : 𝒞) {X Y : 𝒞} (f : X ⟶ Y) : ℕ :=
  finrank k (LinearMap.range (rankPairing k A f))

omit [HasBinaryBiproducts 𝒞] [IsIdempotentComplete 𝒞] in
theorem rk0_le_left (A : 𝒞) {X Y : 𝒞} (f : X ⟶ Y) : rk0 k A f ≤ finrank k (A ⟶ X) :=
  LinearMap.finrank_range_le _

omit [HasBinaryBiproducts 𝒞] [IsIdempotentComplete 𝒞] in
/-- `rk_A(1_A) = 1` for a brick `A`: the identity "gives an isomorphism on one summand `A`". -/
theorem rk0_id {A : 𝒞} (hA : IsBrick k A) : rk0 k A (𝟙 A) = 1 := by
  refine le_antisymm (hA.2 ▸ rk0_le_left k A (𝟙 A)) ?_
  refine Nat.one_le_iff_ne_zero.2 fun h0 => ?_
  rw [rk0, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h0
  have := congrArg (fun φ => φ (𝟙 A) (𝟙 A)) h0
  simp only [rankPairing, LinearMap.mk₂_apply, Category.comp_id, LinearMap.zero_apply] at this
  exact hA.1.1 ((IsZero.iff_id_eq_zero A).2 this)

omit [HomFinite k 𝒞] [HasBinaryBiproducts 𝒞] [IsIdempotentComplete 𝒞] in
/-- The `A`-rank is invariant under composition with an isomorphism on the target. -/
theorem rk0_comp_iso (A : 𝒞) {X Y Y' : 𝒞} (f : X ⟶ Y) (e : Y ≅ Y') :
    rk0 k A (f ≫ e.hom) = rk0 k A f := by
  let L : ((Y ⟶ A) →ₗ[k] (A ⟶ A)) ≃ₗ[k] ((Y' ⟶ A) →ₗ[k] (A ⟶ A)) :=
    LinearEquiv.arrowCongr (Linear.homCongr k e (Iso.refl A)) (LinearEquiv.refl k _)
  have : rankPairing k A (f ≫ e.hom) = L.toLinearMap ∘ₗ rankPairing k A f := by
    ext g h
    simp [L, rankPairing, LinearEquiv.arrowCongr_apply, Linear.homCongr_symm_apply]
  rw [rk0, rk0, this, LinearMap.range_comp, LinearEquiv.finrank_map_eq]

omit [HomFinite k 𝒞] [HasBinaryBiproducts 𝒞] [IsIdempotentComplete 𝒞] in
/-- The `A`-rank is invariant under composition with an isomorphism on the source. -/
theorem rk0_iso_comp (A : 𝒞) {X X' Y : 𝒞} (e : X' ≅ X) (f : X ⟶ Y) :
    rk0 k A (e.hom ≫ f) = rk0 k A f := by
  let L : (A ⟶ X) ≃ₗ[k] (A ⟶ X') := Linear.homCongr k (Iso.refl A) e.symm
  have : rankPairing k A (e.hom ≫ f) = rankPairing k A f ∘ₗ L.symm.toLinearMap := by
    ext g h
    simp [L, rankPairing, Linear.homCongr_symm_apply]
  rw [rk0, rk0, this, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]

section TotalRank

variable [HasShift 𝒞 ℤ]

omit [HomFinite k 𝒞] [HasBinaryBiproducts 𝒞] [IsIdempotentComplete 𝒞] in
variable {k} in
/-- **The total `A`-rank** `rk_A(f) = ∑_i rk⁰_{A⟨i⟩}(f)` (CL §3.1; "In this paper, this will
always turn out to be a finite integer" — as a `finsum` it is `0` if infinitely many terms are
nonzero). -/
def rk (k : Type*) [Field k] [Linear k 𝒞] (A : 𝒞) {X Y : 𝒞} (f : X ⟶ Y) : ℕ :=
  ∑ᶠ i : ℤ, rk0 k (A⟦i⟧) f

end TotalRank

end Rank

end Categorification.TwoRep

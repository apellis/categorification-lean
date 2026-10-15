/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqCurl
import Mathlib.RingTheory.Polynomial.Nilpotent

/-!
# Nilpotent bubbles for Rouquier's data with nilpotent dots

Single-colour input for the `sl₂` coproduct (B. Webster, *Unfurling Khovanov–Lauda–Rouquier
algebras*, arXiv:1603.06311v3, Theorem `th:coproduct` and Lemma `lem:many-sl2`, whose proof
refers to J. Brundan, A. Savage, B. Webster, *The degenerate Heisenberg category and its
Grothendieck ring*, arXiv:1812.03255v3, §5, Theorem 5.4 and Lemmas 5.6–5.12). Webster works in a
category where the dots are topologically nilpotent; here the dots are nilpotent.

For Rouquier's data at one weight `h` (`RouqLoc`; J. Brundan, *On the definition of Kac–Moody
2-category*, arXiv:1501.00350v1, Definition 1.1) whose dots `x₁`, `x₂` are nilpotent, the dotted
bubbles of all degrees except the two boundary ones (`ccw (h - 1) = cw (-h - 1) = 1`) are
nilpotent elements of the commutative ring `End (𝟙 b)`: by Brundan's infinite Grassmannian
relation (Theorem 3.2, `RouqLoc.infGrass`) the two bubble generating functions are polynomials
inverse to each other, and the non-constant coefficients of a unit polynomial over a commutative
ring are nilpotent.

We also record the dot slide through the leftward crossing (a consequence of Brundan (2.3),
(3.5), (3.6), (3.7)) and deduce that the scalars which appear when a dotted rightward cup is
closed off by the leftward crossing and a dotted rightward cap, or by an inverse component
(`♠`-cup, `♣`-cap), are nilpotent away from the Kronecker deltas of Brundan's Lemma 3.1.

## Main statements

* `RouqLoc.sigL_dot`, `RouqLoc.dot_sigL_pow`: `σ' ∘ x = x ∘ σ' - η' ∘ ε'` and its iterate;
* `RouqLoc.ccw_isNilpotent`, `RouqLoc.cw_isNilpotent`: the bubbles of non-boundary degree;
* `RouqLoc.cw_ccw_isNilpotent`: products `cw r ∘ ccw s` with `r + s ≥ -1`;
* `RouqLoc.cupN_capD_sub_isNilpotent`, `RouqLoc.cupD_capN_sub_isNilpotent`,
  `RouqLoc.cupD_sigL_capD_isNilpotent`: the three families of closed diagrams used by the
  coproduct.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Bicategory

universe w v u

/-- The endomorphisms of an identity 1-morphism form a commutative ring (Eckmann–Hilton,
`Bicategory.endId_comm`). -/
@[reducible]
def endIdCommRing {C : Type u} [Bicategory.{w, v} C] [∀ a b : C, Preadditive (a ⟶ b)] (b : C) :
    CommRing (End (𝟙 b)) :=
  { (inferInstance : Ring (End (𝟙 b))) with
    mul_comm := fun f g => Bicategory.endId_comm g f }

namespace RouqLoc

variable {C : Type u} [Bicategory.{w, v} C] [∀ a b : C, Preadditive (a ⟶ b)]
  [AdditiveWhiskering C] {a b c : C} {E₁ : a ⟶ b} {R₁ : b ⟶ a} {E₂ : b ⟶ c} {R₂ : c ⟶ b}
  {adj₁ : E₁ ⊣ R₁} {adj₂ : E₂ ⊣ R₂} {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂}
  {τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂} {h : ℤ} (L : RouqLoc adj₁ adj₂ x₁ x₂ τ h)

/-! ## Boundary values -/

section Boundary

omit [AdditiveWhiskering C] in
theorem ccw_eq_zero_of_lt {j : ℤ} (hj : j < h - 1) : L.ccw j = 0 := by
  by_cases hh : 0 < h
  · exact L.ccw_of_lt hh hj
  · exact L.ccw_of_neg_of_lt (by omega) hj

omit [AdditiveWhiskering C] in
theorem cw_eq_zero_of_lt {j : ℤ} (hj : j < -h - 1) : L.cw j = 0 := by
  by_cases hh : h < 0
  · exact L.cw_of_lt hh hj
  · exact L.cw_of_neg_of_lt (by omega) hj

omit [AdditiveWhiskering C] in
theorem ccw_boundary : L.ccw (h - 1) = 𝟙 _ := by
  by_cases hh : 0 < h
  · exact L.ccw_self hh
  · exact L.ccw_of_neg_of_eq (by omega) rfl

omit [AdditiveWhiskering C] in
theorem cw_boundary : L.cw (-h - 1) = 𝟙 _ := by
  by_cases hh : h < 0
  · exact L.cw_self hh
  · exact L.cw_of_neg_of_eq (by omega) rfl

/-- With `x₁ⁿ = 0`, the counter-clockwise bubbles with at least `n` dots vanish. -/
theorem ccw_eq_zero_of_ge {n : ℕ} (hx : powComp x₁ n = 0) {k : ℤ} (hk : (n : ℤ) ≤ k) :
    L.ccw k = 0 := by
  rw [L.ccw_of_nonneg (by omega), capD]
  obtain ⟨d, hd⟩ : ∃ d : ℕ, k.toNat = n + d := ⟨k.toNat - n, by omega⟩
  rw [hd, ← powComp_comp_powComp, hx, Limits.zero_comp, AdditiveWhiskering.whiskerLeft_zero,
    Limits.zero_comp, Limits.comp_zero]

/-- With `x₂ⁿ = 0`, the clockwise bubbles with at least `n` dots vanish. -/
theorem cw_eq_zero_of_ge {n : ℕ} (hx : powComp x₂ n = 0) {k : ℤ} (hk : (n : ℤ) ≤ k) :
    L.cw k = 0 := by
  rw [L.cw_of_nonneg (by omega), cupD]
  obtain ⟨d, hd⟩ : ∃ d : ℕ, k.toNat = n + d := ⟨k.toNat - n, by omega⟩
  rw [hd, ← powComp_comp_powComp, hx, Limits.zero_comp, AdditiveWhiskering.zero_whiskerRight,
    Limits.comp_zero, Limits.zero_comp]

end Boundary


/-! ## Dots and the leftward crossing -/

section Slide

omit [AdditiveWhiskering C] in
theorem dot_capD (m : ℕ) : R₁ ◁ x₁ ≫ L.capD m = L.capD (m + 1) := by
  rw [capD, capD, ← Category.assoc, ← Bicategory.whiskerLeft_comp, comp_powComp]

omit [AdditiveWhiskering C] in
theorem dotPow_capD (r m : ℕ) : R₁ ◁ powComp x₁ r ≫ L.capD m = L.capD (r + m) := by
  rw [capD, capD, ← Category.assoc, ← Bicategory.whiskerLeft_comp, powComp_comp_powComp]

omit [AdditiveWhiskering C] in
theorem cupD_dot (m : ℕ) : L.cupD m ≫ x₂ ▷ R₂ = L.cupD (m + 1) := by
  rw [cupD, cupD, Category.assoc, ← Bicategory.comp_whiskerRight, ← powComp_succ]

omit [AdditiveWhiskering C] in
theorem cupD_dotPow (m r : ℕ) : L.cupD m ≫ powComp x₂ r ▷ R₂ = L.cupD (m + r) := by
  rw [cupD, cupD, Category.assoc, ← Bicategory.comp_whiskerRight, powComp_comp_powComp]

omit [AdditiveWhiskering C] in
theorem capD_zero : L.capD 0 = adj₁.counit := by simp [capD]

omit [AdditiveWhiskering C] in
theorem cupD_zero : L.cupD 0 = adj₂.unit := by simp [cupD]

/-- Brundan (2.3) rearranged: `x ∘ σ = σ ∘ x - (cup) ∘ (cap)` on `E F 1_λ`. -/
theorem dot_sig : R₁ ◁ x₁ ≫ L.sig = L.sig ≫ x₂ ▷ R₂ - L.capD 0 ≫ L.cupD 0 := by
  rw [capD_zero, cupD_zero, ← L.sig_dot_sub]
  abel

/-- **A dot slides through the leftward crossing**: `σ' ∘ x = x ∘ σ' - η' ∘ ε'` (composition in
diagrammatic order: `σ' ≫ x = x ≫ σ' - ε' ≫ η'`), for every weight. A consequence of Brundan
(2.3), (3.3), (3.5)–(3.7), (1.17), (1.18). -/
theorem sigL_dot : L.sigL ≫ R₁ ◁ x₁ = x₂ ▷ R₂ ≫ L.sigL - L.capL ≫ L.cupL := by
  rcases lt_or_ge h 0 with hh | hh
  · have e1 : L.sigL ≫ R₁ ◁ x₁ = -(L.sigL ≫ (R₁ ◁ x₁ ≫ L.sig) ≫ L.sigL) := by
      calc L.sigL ≫ R₁ ◁ x₁ = L.sigL ≫ R₁ ◁ x₁ ≫ (-(L.sig ≫ L.sigL)) := by
            rw [L.sig_sigL_of_nonpos hh.le, neg_neg, Category.comp_id]
        _ = _ := by simp only [Preadditive.comp_neg, Category.assoc]
    obtain ⟨H, hH⟩ : ∃ H : ℕ, (-h).toNat = H + 1 := ⟨(-h).toNat - 1, by omega⟩
    have hs : (∑ n ∈ Finset.range (-h).toNat, L.capN n ≫ L.cupD n) ≫ x₂ ▷ R₂ ≫ L.sigL =
        L.capL ≫ L.cupL := by
      rw [Preadditive.sum_comp, hH, Finset.sum_range_succ, Finset.sum_eq_zero, zero_add,
        L.capL_of_neg hh, L.cupL_of_nonpos hh.le, hH, show (-h - 1).toNat = H by omega,
        Category.assoc, reassoc_of% (L.cupD_dot H)]
      intro m hm
      rw [Category.assoc, reassoc_of% (L.cupD_dot m),
        L.cupD_sigL hh.le (by have := Finset.mem_range.mp hm; omega), Limits.comp_zero]
    have hsig := L.sigL_sig_of_nonpos hh.le
    rw [e1, L.dot_sig]
    simp only [Preadditive.sub_comp, Preadditive.comp_sub, Category.assoc]
    rw [L.cupD_sigL hh.le (by omega), Limits.comp_zero, Limits.comp_zero, sub_zero,
      reassoc_of% hsig, Preadditive.sub_comp, hs, Category.id_comp]
    abel
  · have hX : ∑ m ∈ Finset.range h.toNat, L.capD m ≫ L.cupN m - L.sig ≫ L.sigL = 𝟙 _ := by
      rw [L.sig_sigL_of_nonneg hh]; abel
    have hsig := L.sigL_sig_of_nonneg hh
    have e1 : L.sigL ≫ R₁ ◁ x₁ = ∑ m ∈ Finset.range h.toNat,
        L.sigL ≫ L.capD (m + 1) ≫ L.cupN m + x₂ ▷ R₂ ≫ L.sigL +
          L.sigL ≫ L.capD 0 ≫ L.cupD 0 ≫ L.sigL := by
      calc L.sigL ≫ R₁ ◁ x₁ = L.sigL ≫ R₁ ◁ x₁ ≫
            (∑ m ∈ Finset.range h.toNat, L.capD m ≫ L.cupN m - L.sig ≫ L.sigL) := by
            rw [hX, Category.comp_id]
        _ = _ := by
            simp only [Preadditive.comp_sub, Preadditive.comp_sum]
            rw [reassoc_of% (L.dot_sig)]
            simp only [Preadditive.sub_comp, Preadditive.comp_sub, Category.assoc]
            rw [reassoc_of% hsig]
            simp only [Preadditive.neg_comp, Category.id_comp, ← Category.assoc (R₁ ◁ x₁),
              L.dot_capD]
            abel
    rw [e1]
    rcases eq_or_lt_of_le hh with h0 | hpos
    · subst h0
      have hc : L.capL = -(L.sigL ≫ L.capD 0) := L.capL_of_nonneg le_rfl
      have hu : L.cupL = L.cupD 0 ≫ L.sigL := L.cupL_of_nonpos le_rfl
      rw [show (0 : ℤ).toNat = 0 from rfl, Finset.sum_range_zero, hc, hu]
      simp only [Preadditive.neg_comp, Category.assoc]
      abel
    · obtain ⟨H, hH⟩ : ∃ H : ℕ, h.toNat = H + 1 := ⟨h.toNat - 1, by omega⟩
      have h0 : L.sigL ≫ L.capD 0 = 0 := L.sigL_capD hh (by omega)
      rw [reassoc_of% h0, Limits.zero_comp, add_zero, hH, Finset.sum_range_succ,
        Finset.sum_eq_zero, zero_add, L.capL_of_nonneg hh, L.cupL_of_pos hpos,
        show (h - 1).toNat = H by omega, show h.toNat = H + 1 from hH]
      · simp only [Preadditive.neg_comp, Category.assoc]
        abel
      · intro m hm
        rw [reassoc_of% (L.sigL_capD hh (n := m + 1) (by have := Finset.mem_range.mp hm; omega)),
          Limits.zero_comp]

/-- The iterated dot slide through the leftward crossing. -/
theorem dotPow_sigL (i : ℕ) :
    powComp x₂ i ▷ R₂ ≫ L.sigL = L.sigL ≫ R₁ ◁ powComp x₁ i +
      ∑ l ∈ Finset.range i,
        powComp x₂ l ▷ R₂ ≫ L.capL ≫ L.cupL ≫ R₁ ◁ powComp x₁ (i - 1 - l) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hx : x₂ ▷ R₂ ≫ L.sigL = L.sigL ≫ R₁ ◁ x₁ + L.capL ≫ L.cupL := by
      rw [L.sigL_dot]; abel
    rw [powComp_succ, Bicategory.comp_whiskerRight, Category.assoc, hx, Preadditive.comp_add,
      ← Category.assoc, ih, Preadditive.add_comp, Finset.sum_range_succ, Category.assoc,
      ← Bicategory.whiskerLeft_comp, ← powComp_succ, Preadditive.sum_comp,
      show i + 1 - 1 - i = 0 by omega, powComp_zero, Bicategory.whiskerLeft_id,
      Category.comp_id]
    rw [add_assoc]
    congr 2
    apply Finset.sum_congr rfl
    intro l hl
    have hl' := Finset.mem_range.mp hl
    rw [Category.assoc, Category.assoc, Category.assoc, ← Bicategory.whiskerLeft_comp,
      ← powComp_succ, show i - 1 - l + 1 = i + 1 - 1 - l by omega]

end Slide

/-! ## The two bubble polynomials are inverse -/

section Grass

theorem grass_coeff (n : ℕ) :
    ∑ j ∈ Finset.range (n + 2), L.ccw (h - 1 + j) ≫
      L.cw (-h - 1 + (n + 1 : ℕ) - j) = 0 := by
  have hg := L.infGrass n (min h 0 - 1) (n + h.natAbs + 3) (by omega) (by
    have : h ≤ (h.natAbs : ℤ) := Int.le_natAbs
    have : -h ≤ (h.natAbs : ℤ) := by simpa only [Int.natCast_natAbs] using (neg_le_abs h)
    omega)
  have hw := sum_range_window
    (fun r : ℤ => L.ccw r ≫ L.cw ((n : ℤ) - 1 - r))
    (lo := min h 0 - 1) (K := n + h.natAbs + 3) (lo' := h - 1) (K' := n + 2)
    (by
      intro r hr
      rcases hr with hr | hr
      · rw [L.ccw_eq_zero_of_lt hr, Limits.zero_comp]
      · rw [L.cw_eq_zero_of_lt (by omega), Limits.comp_zero])
    (by omega) (by
      have : h ≤ (h.natAbs : ℤ) := Int.le_natAbs
      have : -h ≤ (h.natAbs : ℤ) := by simpa only [Int.natCast_natAbs] using (neg_le_abs h)
      omega)
  rw [hw] at hg
  convert hg using 2 with j
  congr 2
  omega

attribute [local instance] endIdCommRing

open Polynomial in
/-- The polynomial `∑_{i < K} ccw (h - 1 + i) tⁱ`. -/
def ccwPoly (K : ℕ) : (End (𝟙 b))[X] :=
  ∑ i ∈ Finset.range K, monomial i (L.ccw (h - 1 + i))

open Polynomial in
/-- The polynomial `∑_{j < K} cw (-h - 1 + j) tʲ`. -/
def cwPoly (K : ℕ) : (End (𝟙 b))[X] :=
  ∑ j ∈ Finset.range K, monomial j (L.cw (-h - 1 + j))

open Polynomial in
theorem coeff_ccwPoly {n K : ℕ} (hx : powComp x₁ n = 0) (hK : (n : ℤ) ≤ h - 1 + K) (i : ℕ) :
    (L.ccwPoly K).coeff i = L.ccw (h - 1 + i) := by
  rw [ccwPoly, finsetSum_coeff]
  simp only [coeff_monomial]
  by_cases hi : i < K
  · rw [Finset.sum_eq_single i (fun j _ hj => ite_eq_right hj) (fun hi' => (hi' (Finset.mem_range.mpr hi)).elim),
      ite_eq_left rfl]
  · rw [Finset.sum_eq_zero (fun j hj => ite_eq_right (by
      have := Finset.mem_range.mp hj; omega)), L.ccw_eq_zero_of_ge hx (by omega)]

open Polynomial in
theorem coeff_cwPoly {n K : ℕ} (hx : powComp x₂ n = 0) (hK : (n : ℤ) ≤ -h - 1 + K) (j : ℕ) :
    (L.cwPoly K).coeff j = L.cw (-h - 1 + j) := by
  rw [cwPoly, finsetSum_coeff]
  simp only [coeff_monomial]
  by_cases hj : j < K
  · rw [Finset.sum_eq_single j (fun i _ hi => ite_eq_right hi) (fun hj' => (hj' (Finset.mem_range.mpr hj)).elim),
      ite_eq_left rfl]
  · rw [Finset.sum_eq_zero (fun i hi => ite_eq_right (by
      have := Finset.mem_range.mp hi; omega)), L.cw_eq_zero_of_ge hx (by omega)]

open Polynomial in
/-- **Brundan, Theorem 3.2** in polynomial form: with nilpotent dots, the two bubble polynomials
are inverse to each other. -/
theorem ccwPoly_mul_cwPoly {n : ℕ} (hx₁ : powComp x₁ n = 0) (hx₂ : powComp x₂ n = 0) :
    L.ccwPoly (n + h.natAbs + 1) * L.cwPoly (n + h.natAbs + 1) = 1 := by
  have hK1 : (n : ℤ) ≤ h - 1 + (n + h.natAbs + 1 : ℕ) := by
    have := le_abs_self h
    have := neg_le_abs h
    push_cast; omega
  have hK2 : (n : ℤ) ≤ -h - 1 + (n + h.natAbs + 1 : ℕ) := by
    have := le_abs_self h
    have := neg_le_abs h
    push_cast; omega
  ext d
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, coeff_one]
  simp only [L.coeff_ccwPoly hx₁ hK1, L.coeff_cwPoly hx₂ hK2]
  rcases d with _ | d
  · simp only [Finset.sum_range_one, Nat.cast_zero, add_zero, Nat.sub_zero]
    rw [L.ccw_boundary, L.cw_boundary]
    simp only [ite_true]
    exact mul_one (1 : End (𝟙 b))
  · rw [ite_eq_right (Nat.succ_ne_zero d)]
    have hg := L.grass_coeff d
    rw [← hg]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    change L.cw _ ≫ L.ccw _ = _
    rw [Bicategory.endId_comm]
    congr 2
    push_cast [Nat.cast_sub (show j ≤ d + 1 by omega)]
    ring

/-- **Nilpotent counter-clockwise bubbles**: with nilpotent dots, `ccw k` is nilpotent for
`k ≥ h`. -/
theorem ccw_isNilpotent {n : ℕ} (hx₁ : powComp x₁ n = 0) (hx₂ : powComp x₂ n = 0) {k : ℤ}
    (hk : h ≤ k) : IsNilpotent (R := End (𝟙 b)) (L.ccw k) := by
  have hu : IsUnit (L.ccwPoly (n + h.natAbs + 1)) :=
    IsUnit.of_mul_eq_one _ (L.ccwPoly_mul_cwPoly hx₁ hx₂)
  have hK1 : (n : ℤ) ≤ h - 1 + (n + h.natAbs + 1 : ℕ) := by
    have := le_abs_self h
    have := neg_le_abs h
    push_cast; omega
  have := (Polynomial.coeff_isUnit_isNilpotent_of_isUnit hu).2 (k - h + 1).toNat (by omega)
  rwa [L.coeff_ccwPoly hx₁ hK1, show h - 1 + ((k - h + 1).toNat : ℤ) = k by omega] at this

/-- **Nilpotent clockwise bubbles**: with nilpotent dots, `cw k` is nilpotent for `k ≥ -h`. -/
theorem cw_isNilpotent {n : ℕ} (hx₁ : powComp x₁ n = 0) (hx₂ : powComp x₂ n = 0) {k : ℤ}
    (hk : -h ≤ k) : IsNilpotent (R := End (𝟙 b)) (L.cw k) := by
  have hu : IsUnit (L.cwPoly (n + h.natAbs + 1)) :=
    IsUnit.of_mul_eq_one _ ((mul_comm _ _).trans (L.ccwPoly_mul_cwPoly hx₁ hx₂))
  have hK2 : (n : ℤ) ≤ -h - 1 + (n + h.natAbs + 1 : ℕ) := by
    have := le_abs_self h
    have := neg_le_abs h
    push_cast; omega
  have := (Polynomial.coeff_isUnit_isNilpotent_of_isUnit hu).2 (k + h + 1).toNat (by omega)
  rwa [L.coeff_cwPoly hx₂ hK2, show -h - 1 + ((k + h + 1).toNat : ℤ) = k by omega] at this

/-- Products of bubbles of total degree `r + s ≥ -1` are nilpotent. -/
theorem cw_ccw_isNilpotent {n : ℕ} (hx₁ : powComp x₁ n = 0) (hx₂ : powComp x₂ n = 0) {r s : ℤ}
    (hrs : -1 ≤ r + s) : IsNilpotent (R := End (𝟙 b)) (L.cw r ≫ L.ccw s) := by
  rcases lt_trichotomy r (-h - 1) with hr | hr | hr
  · rw [L.cw_eq_zero_of_lt hr, Limits.zero_comp]
    exact IsNilpotent.zero
  · rw [hr, L.cw_boundary, Category.id_comp]
    exact L.ccw_isNilpotent hx₁ hx₂ (by omega)
  · rw [← End.mul_def]
    exact (Commute.all _ _).isNilpotent_mul_left (L.cw_isNilpotent hx₁ hx₂ (by omega))

end Grass

/-! ## Closed diagrams -/

section Closed

attribute [local instance] endIdCommRing

omit [AdditiveWhiskering C] in
theorem cupL_capD_eq_ccw (k : ℕ) : L.cupL ≫ L.capD k = L.ccw k := by
  rw [L.ccw_of_nonneg (by positivity), Int.toNat_natCast]

omit [AdditiveWhiskering C] in
theorem cupD_capL_eq_cw (k : ℕ) : L.cupD k ≫ L.capL = L.cw k := by
  rw [L.cw_of_nonneg (by positivity), Int.toNat_natCast]

omit [AdditiveWhiskering C] in
theorem isNilpotent_sum_end {ι : Type*} (s : Finset ι) (f : ι → (𝟙 b ⟶ 𝟙 b))
    (hf : ∀ i ∈ s, IsNilpotent (R := End (𝟙 b)) (f i)) :
    IsNilpotent (R := End (𝟙 b)) (∑ i ∈ s, f i) := by
  rw [← mem_nilradical]
  exact Ideal.sum_mem _ fun i hi => mem_nilradical.mpr (hf i hi)

variable {n : ℕ} (hx₁ : powComp x₁ n = 0) (hx₂ : powComp x₂ n = 0)
include hx₁ hx₂

/-- **The `♠`-cups against the dotted caps**: `ε(xⁱ) ∘ η'_m` is `δ_{m i}` up to a nilpotent
scalar (Brundan (3.6) for `i < h`, and Brundan (3.12) with nilpotent bubbles for `i ≥ h`). -/
theorem cupN_capD_sub_isNilpotent {m : ℕ} (hm : m < h.toNat) (i : ℕ) :
    IsNilpotent (R := End (𝟙 b)) (L.cupN m ≫ L.capD i - if m = i then 𝟙 _ else 0) := by
  have hpos : 0 < h := by omega
  by_cases hi : i < h.toNat
  · rw [L.cupN_capD hpos.le hm hi, sub_self]
    exact IsNilpotent.zero
  · rw [ite_eq_right (by omega), sub_zero, L.cupN_expansion hpos hm, Preadditive.sum_comp]
    refine isNilpotent_sum_end _ _ fun r _ => ?_
    rw [Category.assoc, Category.assoc, L.dotPow_capD, L.cupL_capD_eq_ccw]
    exact L.cw_ccw_isNilpotent hx₁ hx₂ (by push_cast; omega)

/-- **The `♣`-caps against the dotted cups**: `ε'_m ∘ η(xʲ)` is `δ_{j m}` up to a nilpotent
scalar (Brundan (3.7) for `j < -h`, and Brundan (3.13) with nilpotent bubbles for `j ≥ -h`). -/
theorem cupD_capN_sub_isNilpotent {m : ℕ} (hm : m < (-h).toNat) (j : ℕ) :
    IsNilpotent (R := End (𝟙 b)) (L.cupD j ≫ L.capN m - if j = m then 𝟙 _ else 0) := by
  have hneg : h < 0 := by omega
  by_cases hj : j < (-h).toNat
  · rw [L.cupD_capN hneg.le hj hm, sub_self]
    exact IsNilpotent.zero
  · rw [ite_eq_right (by omega), sub_zero, L.capN_expansion hneg hm, Preadditive.comp_sum]
    refine isNilpotent_sum_end _ _ fun r _ => ?_
    rw [← Category.assoc, ← Category.assoc, L.cupD_dotPow, L.cupD_capL_eq_cw]
    exact L.cw_ccw_isNilpotent hx₁ hx₂ (by push_cast; omega)

omit hx₁ hx₂ in
/-- Closing the leftward crossing with a dotted cup and a dotted cap, after sliding the dots
of the cap through the crossing (`dotPow_sigL`). -/
theorem cupD_sigL_capD (j i : ℕ) :
    L.cupD j ≫ L.sigL ≫ L.capD i = L.cupD (j + i) ≫ L.sigL ≫ L.capD 0 -
      ∑ l ∈ Finset.range i, L.cw (j + l : ℕ) ≫ L.ccw (i - 1 - l : ℕ) := by
  have hs : L.sigL ≫ R₁ ◁ powComp x₁ i = powComp x₂ i ▷ R₂ ≫ L.sigL -
      ∑ l ∈ Finset.range i,
        powComp x₂ l ▷ R₂ ≫ L.capL ≫ L.cupL ≫ R₁ ◁ powComp x₁ (i - 1 - l) := by
    rw [L.dotPow_sigL]; abel
  have hc : ∀ k : ℕ, L.capD k = R₁ ◁ powComp x₁ k ≫ L.capD 0 := fun k => by
    rw [L.dotPow_capD, add_zero]
  rw [hc i, reassoc_of% hs]
  simp only [Preadditive.sub_comp, Preadditive.comp_sub, Preadditive.sum_comp,
    Preadditive.comp_sum, Category.assoc]
  rw [reassoc_of% (L.cupD_dotPow j i)]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [← hc, reassoc_of% (L.cupD_dotPow j l), L.cupL_capD_eq_ccw, ← Category.assoc,
    L.cupD_capL_eq_cw]

/-- **The leftward crossing closed by a dotted cup and a dotted cap is nilpotent.** -/
theorem cupD_sigL_capD_isNilpotent (j i : ℕ) :
    IsNilpotent (R := End (𝟙 b)) (L.cupD j ≫ L.sigL ≫ L.capD i) := by
  have hsum : ∀ j i : ℕ, IsNilpotent (R := End (𝟙 b))
      (∑ l ∈ Finset.range i, L.cw (j + l : ℕ) ≫ L.ccw (i - 1 - l : ℕ)) := fun j i =>
    isNilpotent_sum_end _ _ fun l hl => L.cw_ccw_isNilpotent hx₁ hx₂ (by
      have := Finset.mem_range.mp hl; push_cast [Nat.cast_sub (show l ≤ i - 1 by omega),
        Nat.cast_sub (show 1 ≤ i by omega)]; omega)
  have hP : IsNilpotent (R := End (𝟙 b)) (L.cupD (j + i) ≫ L.sigL ≫ L.capD 0) := by
    rcases lt_or_ge 0 h with hh | hh
    · rw [L.sigL_capD hh.le (by omega), Limits.comp_zero]
      exact IsNilpotent.zero
    · have e := L.cupD_sigL_capD 0 (j + i)
      rw [zero_add] at e
      have e' : L.cupD (j + i) ≫ L.sigL ≫ L.capD 0 = L.cupD 0 ≫ L.sigL ≫ L.capD (j + i) +
          ∑ l ∈ Finset.range (j + i), L.cw (0 + l : ℕ) ≫ L.ccw (j + i - 1 - l : ℕ) := by
        rw [e]; abel
      rw [e', ← mem_nilradical]
      refine Ideal.add_mem _ ?_ (mem_nilradical.mpr (hsum 0 (j + i)))
      rw [mem_nilradical]
      rcases lt_or_eq_of_le hh with hneg | h0
      · rw [← Category.assoc, L.cupD_sigL hneg.le (by omega), Limits.zero_comp]
        exact IsNilpotent.zero
      · have hu : L.cupL = L.cupD 0 ≫ L.sigL := by
          rw [L.cupL_of_nonpos hh, show (-h).toNat = 0 by omega]
        rw [← Category.assoc, ← hu, L.cupL_capD_eq_ccw]
        exact L.ccw_isNilpotent hx₁ hx₂ (by omega)
  rw [L.cupD_sigL_capD, ← mem_nilradical]
  exact Ideal.sub_mem _ (mem_nilradical.mpr hP) (mem_nilradical.mpr (hsum j i))

end Closed

end RouqLoc

end Categorification.TwoRep

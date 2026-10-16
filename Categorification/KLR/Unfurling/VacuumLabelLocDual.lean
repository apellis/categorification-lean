/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.VacuumLabelLoc

/-!
# Rouquier's data of a lowest weight label at the generating object

B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, proof of the
theorem with label `nondegenerate`, for a positive weight of the colour (`ev_comp_eq_lwSeq_dual`).
This is the mirror of `VacuumLabelLoc`. Let `L` be Rouquier's data (`RouqLoc`, J. Brundan, *On the
definition of Kac–Moody 2-category*, arXiv:1501.00350v1, Definition 1.1) of one label at a
weight `h ≤ 0` in `LinearCat k`, and let `V` be an object with `E F V = 0` (`V` is lowest weight
for the label). If the dots are nilpotent and `End V` is reduced, then at `V`

* the `♣`-caps `c_m = ε'_m` and the dotted cups `κ ≫ yᵐ` (`m < -h`) decompose the identity of
  `F E V` (`sum_capN_cupD_app`, Brundan (1.9) at `V`);
* `κ ≫ yᵐ' ≫ c_m = δ_{m m'}` for all `m'` (`cupD_app_capN_app`): for `m' < -h` by Brundan (3.7),
  and for `m' ≥ -h` because the bubble is nilpotent (`RouqLoc.cupD_capN_sub_isNilpotent`);
* so a polynomial dot `p(y)` acts on the caps triangularly (`aeval_sub_capN_app`), as needed by
  the chains of `ev_comp_eq_lwSeq_dual`.

The abstract statements are `dot_comp_chain`, `pow_comp_chain`, `aeval_comp_chain` and
`aeval_sub_comp_chain`.
-/

noncomputable section

namespace Categorification.KLR.Unfurling

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits TwoRep Polynomial

section Chain

variable {L : Type*} [CommRing L] {C : Type*} [Category C] [Preadditive C] [Linear L C]

/-- **The caps of a lowest weight label lower the dot**: if `∑_{m<Λ} c_m ≫ κ ≫ yᵐ = 1` and
`κ ≫ y^{m'} ≫ c_m = δ_{m m'}` for `m < Λ` and all `m'`, then `y ≫ c_m = c_{m-1}`
(`0` for `m = 0`). -/
theorem dot_comp_chain {V P : C} (κ : V ⟶ P) (y : End P) (Λ : ℕ) (c : ℕ → (P ⟶ V))
    (htot : ∑ m ∈ Finset.range Λ, c m ≫ κ ≫ (y ^ m : End P) = 𝟙 P)
    (hcc : ∀ m m', m < Λ → κ ≫ (y ^ m' : End P) ≫ c m = if m' = m then 𝟙 V else 0)
    (m : ℕ) (hm : m < Λ) : y ≫ c m = if m = 0 then 0 else c (m - 1) := by
  have h : y ≫ c m = ∑ m' ∈ Finset.range Λ, c m' ≫ κ ≫ (y ^ (m' + 1) : End P) ≫ c m := by
    conv_lhs => rw [← Category.id_comp y, ← htot]
    rw [Preadditive.sum_comp, Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun m' _ => ?_
    rw [pow_succ', End.mul_def]
    simp only [Category.assoc]
  rw [h]
  simp only [hcc m _ hm]
  rcases m with _ | m
  · exact Finset.sum_eq_zero fun m' _ => by
      simp only [show m' + 1 ≠ 0 by omega, ↓reduceIte, Limits.comp_zero]
  · rw [Finset.sum_eq_single m (fun m' _ hm' => by
        simp only [show m' + 1 ≠ m + 1 by omega, ↓reduceIte, Limits.comp_zero])
      (fun h' => absurd (Finset.mem_range.mpr (by omega)) h')]
    simp

variable {V P : C} (κ : V ⟶ P) (y : End P) (Λ : ℕ) (c : ℕ → (P ⟶ V))
  (htot : ∑ m ∈ Finset.range Λ, c m ≫ κ ≫ (y ^ m : End P) = 𝟙 P)
  (hcc : ∀ m m', m < Λ → κ ≫ (y ^ m' : End P) ≫ c m = if m' = m then 𝟙 V else 0)
include htot hcc

/-- Powers of the dot on the caps of a lowest weight label: `yⁿ ≫ c_m = c_{m-n}`. -/
theorem pow_comp_chain (n m : ℕ) (hm : m < Λ) :
    (y ^ n : End P) ≫ c m = if n ≤ m then c (m - n) else 0 := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', End.mul_def, Category.assoc, dot_comp_chain κ y Λ c htot hcc m hm]
    rcases m with _ | m
    · simp
    · simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, ih m (by omega),
        Nat.add_le_add_iff_right, Nat.add_sub_add_right]

/-- **The dot `p(y)` on the caps of a lowest weight label**:
`p(y) ≫ c_m = ∑_{j ≤ m} p_{m-j} c_j`. -/
theorem aeval_comp_chain (p : L[X]) (m : ℕ) (hm : m < Λ) :
    (aeval y p : End P) ≫ c m = ∑ j ∈ Finset.range (m + 1), p.coeff (m - j) • c j := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, Preadditive.add_comp, hp, hq, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [coeff_add, add_smul]
  | monomial n a =>
    rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      Linear.smul_comp, pow_comp_chain κ y Λ c htot hcc n m hm]
    simp only [coeff_monomial]
    by_cases hn : n ≤ m
    · simp only [hn, ↓reduceIte]
      rw [Finset.sum_eq_single (m - n)]
      · simp only [show m - (m - n) = n by omega, ↓reduceIte]
      · intro j hj hjn
        simp only [show n ≠ m - j by have := Finset.mem_range.mp hj; omega, ↓reduceIte, zero_smul]
      · intro h'
        exact absurd (Finset.mem_range.mpr (by omega)) h'
    · simp only [hn, ↓reduceIte, smul_zero]
      exact (Finset.sum_eq_zero fun j hj => by
        simp only [show n ≠ m - j by have := Finset.mem_range.mp hj; omega, ↓reduceIte,
          zero_smul]).symm

/-- The chain of `ev_comp_eq_lwSeq_dual`: with `z = p₀`,
`(p(y) - z) ≫ c_m = ∑_{j < m} p_{m-j} c_j`. -/
theorem aeval_sub_comp_chain (p : L[X]) (m : ℕ) (hm : m < Λ) :
    (aeval y p - algebraMap L (End P) (p.coeff 0) : End P) ≫ c m =
      ∑ j ∈ Finset.range m, p.coeff (m - j) • c j := by
  rw [Preadditive.sub_comp, aeval_comp_chain κ y Λ c htot hcc p m hm, Finset.sum_range_succ,
    Nat.sub_self, Algebra.algebraMap_eq_smul_one, Linear.smul_comp, End.one_def,
    Category.id_comp, add_sub_cancel_right]

end Chain

universe w v u

variable {k : Type w} [CommRing k] {C₁ C₂ C₃ : LinearCat.{w, v, u} k}
  {E₁ : C₁ ⟶ C₂} {R₁ : C₂ ⟶ C₁} {E₂ : C₂ ⟶ C₃} {R₂ : C₃ ⟶ C₂}
  {adj₁ : E₁ ⊣ R₁} {adj₂ : E₂ ⊣ R₂} {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂}
  {τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂} {h : ℤ} (L : RouqLoc adj₁ adj₂ x₁ x₂ τ h) (V : (C₂ : Type u))

/-- The dot on `F E V`. -/
abbrev dotAt₂ : End (R₂.obj.obj (E₂.obj.obj V)) := R₂.obj.map (x₂.hom.app V)

omit L in
theorem powComp_whiskerRight_app (n : ℕ) :
    (powComp x₂ n ▷ R₂).hom.app V = (dotAt₂ (x₂ := x₂) (R₂ := R₂) V ^ n : End _) := by
  induction n with
  | zero =>
    show R₂.obj.map (𝟙 _) = _
    exact R₂.obj.map_id _
  | succ n ih =>
    rw [powComp_succ, Bicategory.comp_whiskerRight, pow_succ', End.mul_def, ← ih]
    rfl

theorem cupD_app (m : ℕ) :
    (L.cupD m).hom.app V =
      adj₂.unit.hom.app V ≫ (dotAt₂ (x₂ := x₂) (R₂ := R₂) V ^ m : End _) := by
  rw [← powComp_whiskerRight_app]
  rfl

/-- **The `♣`-caps and dotted cups decompose `F E V`** when `E F V = 0` (Brundan (1.9) at
`V`). -/
theorem sum_capN_cupD_app (hh : h ≤ 0) (hY : IsZero (E₁.obj.obj (R₁.obj.obj V))) :
    ∑ m ∈ Finset.range (-h).toNat, (L.capN m).hom.app V ≫ adj₂.unit.hom.app V ≫
      (dotAt₂ (x₂ := x₂) (R₂ := R₂) V ^ m : End _) = 𝟙 (R₂.obj.obj (E₂.obj.obj V)) := by
  have hY' : IsZero ((evalAt V).obj (R₁ ≫ E₁)) := hY
  have t := ((L.iN hh).map (evalAt V)).total
  have h0 : ((L.iN hh).map (evalAt V)).f' ≫ (evalAt V).map L.sig = 0 := by
    rw [hY'.eq_zero_of_tgt ((L.iN hh).map (evalAt V)).f', Limits.zero_comp]
  rw [h0, zero_add] at t
  refine Eq.trans (Finset.sum_congr rfl fun m _ => ?_) t
  show _ = ((L.iN hh).g' m).hom.app V ≫ (L.cupD m).hom.app V
  rw [cupD_app]
  simp only [RouqLoc.capN, hh, ↓reduceDIte]
  rfl

/-- **The dotted cups against the `♣`-caps at `V`**: `κ ≫ yᵐ' ≫ c_m = δ_{m m'}` for every `m'`,
if the dots are nilpotent and `End V` is reduced. -/
theorem cupD_app_capN_app {n : ℕ} (hx₁ : powComp x₁ n = 0) (hx₂ : powComp x₂ n = 0)
    [IsReduced (End V)] {m : ℕ} (hm : m < (-h).toNat) (m' : ℕ) :
    adj₂.unit.hom.app V ≫ (dotAt₂ (x₂ := x₂) (R₂ := R₂) V ^ m' : End _) ≫
      (L.capN m).hom.app V = if m' = m then 𝟙 V else 0 := by
  have hz := ((L.cupD_capN_sub_isNilpotent hx₁ hx₂ hm m').map (endIdEval V)).eq_zero
  rw [map_sub, sub_eq_zero] at hz
  refine Eq.trans ?_ (hz.trans ?_)
  · show _ = (L.cupD m').hom.app V ≫ (L.capN m).hom.app V
    rw [cupD_app]
    exact (Category.assoc _ _ _).symm
  by_cases hmm : m' = m
  · subst hmm; simp only [↓reduceIte]; rfl
  · simp only [hmm, ↓reduceIte, map_zero]

/-- **The dot `p(y)` on the `♣`-caps at `V`**: with `E F V = 0`, nilpotent dots and `End V`
reduced, `(p(y) - p₀) ≫ c_m = ∑_{j<m} p_{m-j} c_j` for `m < -h`. -/
theorem aeval_sub_capN_app (hh : h ≤ 0) (hY : IsZero (E₁.obj.obj (R₁.obj.obj V))) {n : ℕ}
    (hx₁ : powComp x₁ n = 0) (hx₂ : powComp x₂ n = 0) [IsReduced (End V)] (p : k[X]) {m : ℕ}
    (hm : m < (-h).toNat) :
    (aeval (dotAt₂ (x₂ := x₂) (R₂ := R₂) V) p -
      algebraMap k (End (R₂.obj.obj (E₂.obj.obj V))) (p.coeff 0) : End _) ≫
        (L.capN m).hom.app V =
      ∑ j ∈ Finset.range m, p.coeff (m - j) • (L.capN j).hom.app V :=
  aeval_sub_comp_chain (adj₂.unit.hom.app V) (dotAt₂ V) (-h).toNat
    (fun m => (L.capN m).hom.app V) (sum_capN_cupD_app L V hh hY)
    (fun _ m' hm => cupD_app_capN_app L V hx₁ hx₂ hm m') p m hm

end Categorification.KLR.Unfurling

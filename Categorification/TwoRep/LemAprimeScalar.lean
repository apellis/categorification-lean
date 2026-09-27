/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.LemAprime

/-!
# CL Lemma 3.8: the two maps are nonzero multiples of the generator of Corollary 3.3

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, Lemma 3.8 (`lem:A'`): the two maps of `LemAprime.lean` "are non-zero multiples
of the unique 2-morphism `E 1_m → E E F 1_m ⟨-m-1⟩` from Corollary 3.3". Corollary 3.3 (`cor2`)
gives the dimension of that space; here we transport it to the Hom spaces in which the two maps
live (`finrank_hom_Asum_FW`, `finrank_hom_Bsum_FW`) and conclude: for every nonzero `u` in the
respective space, each map is `c • u` with `c ≠ 0` (`lemAprimeLeft_eq_smul`,
`lemAprimeRight_eq_smul`). Hypotheses: (3.2) at the weights `> m` (as in Corollary 3.3), and
`1_{m+2} ≠ 0`; the right map moreover needs the two coherence mixins, as in `LemAprime.lean`.
-/

noncomputable section

namespace Categorification.TwoRep.StrongSl2

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Module
open KrullSchmidtCat (HomFinite)

universe w v u

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [∀ a b : B, HomFinite k (a ⟶ b)] {S : StrongSl2 k B} {r : ℤ}

/-- The space of the left map of Lemma 3.8 is one-dimensional (Corollary 3.3). -/
theorem finrank_hom_Asum_FW (hn : 0 ≤ S.wt (r + 1)) (hyp : ∀ r', r + 1 < r' → S.AdjHyp r')
    (h : ¬ IsZero (𝟙 (S.obj (r + 1 + 1)))) : finrank k (S.Asum r 0 ⟶ S.FW r) = 1 := by
  have hN : (((S.wt (r + 1 + 1)).toNat : ℕ) : ℤ) = S.wt (r + 1 + 1) := by
    rw [Int.toNat_of_nonneg (by rw [S.wt_add_one]; omega)]
  rw [finrank_hom_congr_left k (S.AsumIso r 0),
    finrank_hom_shift_left k _ _ (b := -(S.wt (r + 1) + 1)) (by rw [hN, S.wt_add_one]; push_cast; ring)]
  exact S.cor2 (r₀ := r + 1) hn hyp le_rfl h

/-- The space of the right map of Lemma 3.8 is one-dimensional (Corollary 3.3). -/
theorem finrank_hom_Bsum_FW (hn : 0 ≤ S.wt (r + 1)) (hyp : ∀ r', r + 1 < r' → S.AdjHyp r')
    (h : ¬ IsZero (𝟙 (S.obj (r + 1 + 1)))) :
    finrank k (S.Bsum r 0 ⟶ S.F r ≫ (S.E r ≫ S.E (r + 1))⟦(-2 : ℤ)⟧) = 1 := by
  have hN : (((S.wt (r + 1)).toNat : ℕ) : ℤ) = S.wt (r + 1) := Int.toNat_of_nonneg hn
  rw [finrank_hom_congr k (S.BsumIso r 0) (whiskerLeftShiftIso _ _ _),
    finrank_hom_shift_shift k _ _ (c := -(S.wt (r + 1) + 1)) (by rw [hN]; push_cast; ring)]
  exact S.cor2 (r₀ := r + 1) hn hyp le_rfl h

variable (e : S.EFDecomp r) (e₂ : S.EFDecomp (r + 1))

include e₂ in
omit [GradedBicategory.IsLinear B k] [∀ a b : B, HomFinite k (a ⟶ b)] in
/-- `E 1_m ≠ 0` when `1_{m+2} ≠ 0` and `m + 2 > 0`: `E F 1_{m+2}` contains the summand
`1_{m+2}⟨m+1⟩`. -/
theorem not_isZero_E_of_EFDecomp (hN : 0 < (S.wt (r + 1 + 1)).toNat)
    (h : ¬ IsZero (𝟙 (S.obj (r + 1 + 1)))) : ¬ IsZero (S.E (r + 1)) := by
  intro hz
  have hz' : IsZero (S.F (r + 1) ≫ S.E (r + 1)) := isZero_comp_right _ hz
  have hid : (𝟙 (S.oneShift (r + 1) 0) : _ ⟶ _) = 0 := by
    rw [← ι_π_self e₂ hN, hz'.eq_of_tgt (ι e₂ 0) 0, zero_comp]
  have hz'' : IsZero (S.oneShift (r + 1) 0) := (IsZero.iff_id_eq_zero _).2 hid
  exact h (((shiftFunctor _ (-(1 * ((((S.wt (r + 1 + 1)).toNat : ℕ) : ℤ) - 1 -
    2 * ((0 : ℕ) : ℤ))))).map_isZero hz'').of_iso
    ((shiftFunctorCompIsoId _ _ _ (by ring)).app _).symm)

/-- **CL Lemma 3.8, left map**: it is a nonzero multiple of any nonzero element of the
one-dimensional space `Hom(E 1_m 1_{m+2}⟨m+1⟩, E E F 1_m)`. -/
theorem lemAprimeLeft_eq_smul (hn : 0 ≤ S.wt (r + 1)) (hyp : ∀ r', r + 1 < r' → S.AdjHyp r')
    (h : ¬ IsZero (𝟙 (S.obj (r + 1 + 1)))) (u : S.Asum r 0 ⟶ S.FW r) (hu : u ≠ 0) :
    ∃ c : k, c ≠ 0 ∧ lemAprimeLeft e e₂ = c • u := by
  have hN : 0 < (S.wt (r + 1 + 1)).toNat := by rw [Int.lt_toNat, S.wt_add_one]; omega
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' u hu).1 (finrank_hom_Asum_FW hn hyp h)
    (lemAprimeLeft e e₂)
  refine ⟨c, fun hc0 => ?_, hc.symm⟩
  exact lemAprimeLeft_ne_zero e e₂ hN (not_isZero_E_of_EFDecomp e₂ hN h)
    (by rw [← hc, hc0, zero_smul])

include e₂ in
/-- **CL Lemma 3.8, right map**: it is a nonzero multiple of any nonzero element of the
one-dimensional space `Hom(1_m⟨m-1⟩ E 1_m, E E F 1_m ⟨-2⟩)` (for `m > 0`). -/
theorem lemAprimeRight_eq_smul [GradedBicategory.ShiftInterchange B] [GradedBicategory.ShiftAssoc B]
    (hm : 0 < S.wt (r + 1)) (hyp : ∀ r', r + 1 < r' → S.AdjHyp r')
    (h : ¬ IsZero (𝟙 (S.obj (r + 1 + 1))))
    (u : S.Bsum r 0 ⟶ S.F r ≫ (S.E r ≫ S.E (r + 1))⟦(-2 : ℤ)⟧) (hu : u ≠ 0) :
    ∃ c : k, c ≠ 0 ∧ lemAprimeRight e = c • u := by
  have hN : 0 < (S.wt (r + 1 + 1)).toNat := by rw [Int.lt_toNat, S.wt_add_one]; omega
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' u hu).1 (finrank_hom_Bsum_FW hm.le hyp h)
    (lemAprimeRight e)
  refine ⟨c, fun hc0 => ?_, hc.symm⟩
  exact lemAprimeRight_ne_zero e (by rw [Int.lt_toNat]; omega) (not_isZero_E_of_EFDecomp e₂ hN h)
    (by rw [← hc, hc0, zero_smul])

end Categorification.TwoRep.StrongSl2

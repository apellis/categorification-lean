/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.TypeA.DoubleCoset
import Categorification.WeightedKLR.RedStrands.StendhalBasisSymm

/-!
# The bimodule `B̃_e` is `T̃^λ`

Webster's bimodules `B̃_w` (arXiv:1309.3796v2, Definitions 6.1–6.3) are spanned by braided
Stendhal diagrams whose red strands trace out `w`. For the identity permutation, the red strands
read `λ_1, …, λ_ℓ` at the top and at the bottom, and these diagrams are Stendhal diagrams: this
is the case `w = e` (or `w' = e`) of Lemma 6.5, `B̃_{ww'} ≅ B̃_w ⊗_{T̃} B̃_{w'}`.

Braided Stendhal diagrams map to Stendhal diagrams with all orders of red strands by imposing the
vanishing of red crossings (`BraidedStendhalAlgebra.toAllOrders`). A reduced word whose bottom
and top both have their red strands in order never crosses two red strands
(`noRedCross_of_isRedOrdered`), so this map sends the basis of Proposition 6.4 for `w = e`
(`BraidedStendhalAlgebra.cornerBasis`) to the basis of Proposition 4.16
(`stendhalBasisOfSymm`), term by term.

## Main results

* `redWord_eq_finRange_iff`: the red strands of `i` read `λ_1, …, λ_ℓ` iff `i` is red-ordered.
* `noRedCross_of_isRedOrdered`: a reduced word between red-ordered sequences has no red
  crossing.
* `BraidedStendhalAlgebra.cornerEquivStendhal`: for symmetric `Q`, `B̃_e ≃ T̃^λ` as `k`-modules,
  given by `toAllOrders` (`cornerEquivStendhal_apply`).
-/

set_option backward.isDefEq.respectTransparency false

namespace Categorification.Stendhal

open MvPolynomial KLR TypeA Equiv

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "R" => KLR.KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)

/-! ### Red-ordered sequences -/

omit [DecidableEq I] in
/-- A sequence is red-ordered iff its red labels increase from left to right. -/
theorem isRedOrdered_iff_pairwise (i : Seq μ) :
    IsRedOrdered i ↔ (redWord i).Pairwise (· < ·) := by
  rw [redWord, List.pairwise_filterMap]
  constructor
  · intro h
    refine (List.pairwise_lt_finRange m).imp fun {a b} hab r hr r' hr' => ?_
    exact h a b r r' hab (Sum.getRight?_eq_some_iff.1 hr) (Sum.getRight?_eq_some_iff.1 hr')
  · intro h a b r r' hab ha hb
    rw [List.pairwise_iff_getElem] at h
    have := h a b (by simp) (by simp) hab
    simp only [List.getElem_finRange, Fin.cast_mk, Fin.eta] at this
    exact this r (by simp [ha]) r' (by simp [hb])

omit [DecidableEq I] in
/-- The red strands of `i` read `λ_1, …, λ_ℓ` from left to right iff `i` is red-ordered. -/
theorem redWord_eq_finRange_iff (i : Seq μ) : redWord i = List.finRange ℓ ↔ IsRedOrdered i := by
  rw [isRedOrdered_iff_pairwise]
  refine ⟨fun h => h ▸ List.pairwise_lt_finRange ℓ, fun h => ?_⟩
  have hperm : List.Perm (redWord i) (List.finRange ℓ) := by
    refine (List.perm_ext_iff_of_nodup (h.imp ne_of_lt) (List.nodup_finRange ℓ)).2 fun r => ?_
    simp only [List.mem_finRange, iff_true, redWord, List.mem_filterMap,
      Sum.getRight?_eq_some_iff]
    obtain ⟨a, ha⟩ := exists_lbl_eq_inr i r
    exact ⟨a, by simp, ha⟩
  exact hperm.eq_of_pairwise (fun _ _ _ _ h₁ h₂ => (lt_asymm h₁ h₂).elim) h
    (List.pairwise_lt_finRange ℓ)

/-! ### Reduced words between red-ordered sequences -/

omit [DecidableEq I] in
/-- A reduced word whose permutation inverts no pair of red strands of `i` never crosses two red
strands. -/
theorem noRedCross_of_isReduced : ∀ (γ : List ℕ) (i : Seq μ), IsReduced m γ →
    (∀ a b : Fin m, a < b → wordProd m γ b < wordProd m γ a →
      (i.lbl a).isLeft ∨ (i.lbl b).isLeft) → NoRedCross γ i
  | [], _, _, _ => trivial
  | j :: γ, i, hred, hinv => by
    obtain ⟨hj, hγ, hasc⟩ := IsReduced.cons_inv hred
    set σ := wordProd m γ with hσ
    refine ⟨noRedCross_of_isReduced γ i hγ fun a b hab hba => hinv a b hab ?_, fun h => ?_⟩
    · rw [wordProd_cons, Perm.mul_apply, Perm.mul_apply, ← hσ]
      change σ b < σ a at hba
      by_contra hc
      have hv1 := sadj_val_of_lt hj (σ b)
      have hv2 := sadj_val_of_lt hj (σ a)
      rw [Fin.lt_def] at hba hc
      rcases swapNat_cases j (σ b) with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ | ⟨h1, h1', h1''⟩ <;>
      rcases swapNat_cases j (σ a) with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ | ⟨h2, h2', h2''⟩ <;>
      try omega
      have hb : σ⁻¹ ⟨j, by omega⟩ = b := by
        rw [Perm.inv_eq_iff_eq]; ext; simp [h1]
      have ha : σ⁻¹ ⟨j + 1, hj⟩ = a := by
        rw [Perm.inv_eq_iff_eq]; ext; simp [h2]
      rw [hb, ha] at hasc
      exact lt_asymm hab hasc
    · have key := hinv (σ⁻¹ ⟨j, by omega⟩) (σ⁻¹ ⟨j + 1, h⟩) hasc (by
        rw [wordProd_cons, Perm.mul_apply, Perm.mul_apply, ← hσ]
        simp only [Perm.inv_def, Equiv.apply_symm_apply]
        rw [sadj_apply_left h, sadj_apply_right h, Fin.lt_def]
        simp)
      simpa [Seq.smul_apply, Perm.inv_def] using key

omit [DecidableEq I] in
/-- If `i` and `w • i` are red-ordered, `w` inverts no pair of red strands of `i`. -/
theorem isLeft_or_isLeft_of_isRedOrdered {i : Seq μ} {w : Perm (Fin m)} (hi : IsRedOrdered i)
    (hwi : IsRedOrdered (w • i)) {a b : Fin m} (hab : a < b) (hba : w b < w a) :
    (i.lbl a).isLeft ∨ (i.lbl b).isLeft := by
  by_contra hc
  simp only [not_or, Bool.not_eq_true, Sum.isLeft_eq_false, Sum.isRight_iff] at hc
  obtain ⟨⟨r, hr⟩, ⟨r', hr'⟩⟩ := hc
  have h₁ := hi a b r r' hab hr hr'
  have h₂ := hwi (w b) (w a) r' r hba (by simpa [Seq.smul_apply] using hr')
    (by simpa [Seq.smul_apply] using hr)
  exact lt_asymm h₁ h₂

omit [DecidableEq I] in
/-- **A reduced word between red-ordered sequences crosses no two red strands.** -/
theorem noRedCross_of_isRedOrdered {γ : List ℕ} {i : Seq μ} (hγ : IsReduced m γ)
    (hi : IsRedOrdered i) (hwi : IsRedOrdered (wordProd m γ • i)) : NoRedCross γ i :=
  noRedCross_of_isReduced γ i hγ fun _ _ hab hba =>
    isLeft_or_isLeft_of_isRedOrdered hi hwi hab hba

/-! ### Braided Stendhal diagrams with no red crossing -/

namespace BraidedStendhalAlgebra

variable (k Q Λ ν) in
/-- Imposing the vanishing of red crossings: braided Stendhal diagrams map to Stendhal diagrams
with all orders of red strands (arXiv:1309.3796v2, Definitions 4.5 and 6.3). -/
noncomputable def toAllOrders :
    BraidedStendhalAlgebra k Q Λ ν →ₐ[k] StendhalAlgebraAllOrders k Q Λ ν :=
  RingQuot.liftAlgHom k ⟨RingQuot.mkAlgHom k (Stendhal.Rel k Q Λ ν), fun _ _ h => by
    cases h with
    | klr h => exact RingQuot.mkAlgHom_rel k (Stendhal.Rel.klr h)
    | red_dot a i h => exact RingQuot.mkAlgHom_rel k (Stendhal.Rel.red_dot a i h)⟩

theorem toAllOrders_ofKLR (x : R) :
    toAllOrders k Q Λ ν (ofKLR k Q Λ ν x) = StendhalAlgebraAllOrders.ofKLR k Q Λ ν x := by
  obtain ⟨a, rfl⟩ := KLR.KLRAlgebra.mk_surjective (k := k) (Q := stendhalQ Q Λ) (ν := μ) x
  rw [ofKLR_mk, StendhalAlgebraAllOrders.ofKLR_mk, toAllOrders]
  exact RingQuot.liftAlgHom_mkAlgHom_apply k _ _ _

/-- The idempotent of red order `λ_1, …, λ_ℓ` goes to `redOrderedIdem`. -/
theorem toAllOrders_redIdem :
    toAllOrders k Q Λ ν (ofKLR k Q Λ ν (redIdem k Q Λ (List.finRange ℓ))) =
      StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν := by
  classical
  rw [toAllOrders_ofKLR, redIdem, map_sum, StendhalAlgebraAllOrders.redOrderedIdem]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext i
  simp [redWord_eq_finRange_iff]

/-- `toAllOrders` maps `B̃_e` into `T̃^λ`. -/
theorem toAllOrders_mem_corner (x : cornerSpace k Q Λ ν (List.finRange ℓ) (List.finRange ℓ)) :
    toAllOrders k Q Λ ν x.1 ∈ Subsemigroup.corner
      (StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν) := by
  obtain ⟨y, hy⟩ := x.2
  have hP := StendhalAlgebraAllOrders.isIdempotentElem_redOrderedIdem (k := k) (Q := Q)
    (Λ := Λ) (ν := ν)
  rw [Subsemigroup.mem_corner_iff hP, ← hy]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulRight_apply,
    LinearMap.mulLeft_apply, map_mul, toAllOrders_redIdem]
  constructor
  · rw [← mul_assoc, hP.eq]
  · rw [mul_assoc, mul_assoc, hP.eq]

variable (k Q Λ ν) in
/-- `toAllOrders` on `B̃_e`, as a `k`-linear map to `T̃^λ`. -/
noncomputable def cornerToStendhal :
    cornerSpace k Q Λ ν (List.finRange ℓ) (List.finRange ℓ) →ₗ[k] StendhalAlgebra k Q Λ ν where
  toFun x := ⟨toAllOrders k Q Λ ν x.1, toAllOrders_mem_corner x⟩
  map_add' x y := Subtype.ext (map_add (toAllOrders k Q Λ ν) x.1 y.1)
  map_smul' c x := Subtype.ext (map_smul (toAllOrders k Q Λ ν) c x.1)

variable (hQ : KLRSymm Q)
  (ρ : Equiv.Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ)
  (hρ : ∀ w, IsReduced (Multiset.card (stendhalWeight ℓ ν)) (ρ w) ∧
    wordProd (Multiset.card (stendhalWeight ℓ ν)) (ρ w) = w)

/-- The basis diagrams of `B̃_e` are the Stendhal terms. -/
def cornerIdxEquiv :
    {b : BlackIdx (ℓ := ℓ) ν //
        redWord (b.1.2.1 • b.1.1) = List.finRange ℓ ∧ redWord b.1.1 = List.finRange ℓ} ≃
      {b // IsStendhalTerm (ν := ν) (ℓ := ℓ) ρ b} where
  toFun b := ⟨b.1.1, (redWord_eq_finRange_iff _).1 b.2.2,
    (redWord_eq_finRange_iff _).1 b.2.1,
    fun a ha => by
      by_contra hl
      simp only [Bool.not_eq_true, Sum.isLeft_eq_false] at hl
      exact (Finsupp.mem_support_iff.1 ha) (b.1.2 a hl),
    noRedCross_of_isRedOrdered (hρ _).1 ((redWord_eq_finRange_iff _).1 b.2.2)
      (by rw [(hρ _).2]; exact (redWord_eq_finRange_iff _).1 b.2.1)⟩
  invFun b := ⟨⟨b.1, fun a ha => by
      by_contra hu
      have := b.2.2.2.1 a (Finsupp.mem_support_iff.2 hu)
      exact KLRAlgebra.not_isRight_of_isLeft this ha⟩,
    (redWord_eq_finRange_iff _).2 b.2.2.1, (redWord_eq_finRange_iff _).2 b.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **`B̃_e ≃ T̃^λ`** (arXiv:1309.3796v2, Definitions 4.5 and 6.3, the case `w = e` of Lemma 6.5)
for symmetric `Q`, over every commutative ring: the braided Stendhal diagrams whose red strands
read `λ_1, …, λ_ℓ` at the top and the bottom are the Stendhal diagrams. The map is `toAllOrders`
(`cornerEquivStendhal_apply`). -/
noncomputable def cornerEquivStendhal :
    cornerSpace k Q Λ ν (List.finRange ℓ) (List.finRange ℓ) ≃ₗ[k] StendhalAlgebra k Q Λ ν :=
  (cornerBasis hQ ρ hρ (List.finRange ℓ) (List.finRange ℓ)).equiv
    (stendhalBasisOfSymm Q Λ hQ ρ hρ) (cornerIdxEquiv ρ hρ)

theorem cornerEquivStendhal_eq :
    (cornerEquivStendhal hQ ρ hρ).toLinearMap = cornerToStendhal k Q Λ ν := by
  refine (cornerBasis hQ ρ hρ (List.finRange ℓ) (List.finRange ℓ)).ext fun b => ?_
  rw [LinearEquiv.coe_coe, cornerEquivStendhal, Module.Basis.equiv_apply,
    stendhalBasisOfSymm_apply]
  apply Subtype.ext
  change (stendhalTerm Q Λ _ _).1 = toAllOrders k Q Λ ν _
  rw [stendhalTerm_val, cornerBasis_apply, toAllOrders_ofKLR, KLR.KLRAlgebra.stdElt]
  rfl

theorem cornerEquivStendhal_apply
    (x : cornerSpace k Q Λ ν (List.finRange ℓ) (List.finRange ℓ)) :
    (cornerEquivStendhal hQ ρ hρ x).1 = toAllOrders k Q Λ ν x.1 := by
  have := LinearMap.congr_fun (cornerEquivStendhal_eq hQ ρ hρ) x
  exact congrArg Subtype.val this

end BraidedStendhalAlgebra

end Categorification.Stendhal

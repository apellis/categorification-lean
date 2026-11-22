/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.AddRedInjective
import Categorification.WeightedKLR.RedStrands.BlackInduction

/-!
# Sliding a black strand past the last red strand

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.6,
Proposition 4.32. Appending the last red strand `λ_ℓ` and then a black strand `i` on the far
right gives the loadings `(s, i, λ_ℓ)`, while appending them in the other order gives
`(s, λ_ℓ, i)`. The two loadings differ by the crossing `ψ` of the last two strands. This file
records the loading combinatorics and the slide of a diagram through that crossing.

## Main results

* `swap_blackRedLoading`: the crossing of the last two strands exchanges the loadings.
* `slide_crossing`: a diagram on the old strands slides through the crossing of the last
  black strand with the last red strand.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA Equiv

variable {I : Type*} {ℓ : ℕ}

section Loadings

variable (i : I) (ν : Multiset I)

local notation "μ" => stendhalWeight ℓ ν
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "μ'" => stendhalWeight (ℓ + 1) νᵢ
local notation "N₀" => Multiset.card (stendhalWeight ℓ ν)

theorem card_stendhalWeight_append :
    Multiset.card μ' = N₀ + 2 := by
  simp [stendhalWeight]
  omega

/-- The loading `(s, i, λ_ℓ)`: append the black strand, then the last red strand. -/
def blackRedLoading (s : Seq μ) : Seq μ' :=
  appendRedLoading (appendBlackLoading i ν s)

/-- The loading `(s, λ_ℓ, i)`: append the last red strand, then the black strand. -/
def redBlackLoading (s : Seq μ) : Seq μ' :=
  appendBlackLoading (ℓ := ℓ + 1) i ν (appendRedLoading s)

variable {i ν}

theorem blackRedLoading_lbl_of_lt (s : Seq μ) (a : Fin (Multiset.card μ'))
    (ha : a.val < N₀) :
    (blackRedLoading i ν s).lbl a = addRedColor ℓ (s.lbl ⟨a.val, ha⟩) := by
  have hb : a.val < Multiset.card (stendhalWeight ℓ νᵢ) := by
    simp [stendhalWeight] at ha ⊢; omega
  have h := appendRedLoading_lbl (appendBlackLoading i ν s) ⟨a.val, hb⟩
  rw [appendBlackLoading_lbl_of_lt i ν s _ ha] at h
  exact h

theorem blackRedLoading_lbl_of_eq (s : Seq μ) (a : Fin (Multiset.card μ'))
    (ha : a.val = N₀) : (blackRedLoading i ν s).lbl a = .inl i := by
  have hb : a.val < Multiset.card (stendhalWeight ℓ νᵢ) := by
    simp [stendhalWeight] at ha ⊢; omega
  have h := appendRedLoading_lbl (appendBlackLoading i ν s) ⟨a.val, hb⟩
  rw [appendBlackLoading_lbl_of_eq i ν s _ ha] at h
  exact h

theorem blackRedLoading_lbl_of_last (s : Seq μ) (a : Fin (Multiset.card μ'))
    (ha : a.val = N₀ + 1) : (blackRedLoading i ν s).lbl a = .inr (Fin.last ℓ) := by
  have h := hasLastRed_appendRedLoading (appendBlackLoading i ν s)
  rw [HasLastRed, show lastRedPosition ℓ νᵢ = a from Fin.ext (by
    simp [lastRedPosition, ha, stendhalWeight]; omega)] at h
  exact h

theorem redBlackLoading_lbl_of_lt (s : Seq μ) (a : Fin (Multiset.card μ'))
    (ha : a.val < N₀) :
    (redBlackLoading i ν s).lbl a = addRedColor ℓ (s.lbl ⟨a.val, ha⟩) := by
  have hb : a.val < Multiset.card (stendhalWeight (ℓ + 1) ν) := by
    simp [stendhalWeight] at ha ⊢; omega
  rw [redBlackLoading, appendBlackLoading_lbl_of_lt (ℓ := ℓ + 1) i ν _ _ hb,
    show (⟨a.val, hb⟩ : Fin _) = appendRedPosition ⟨a.val, ha⟩ from Fin.ext rfl,
    appendRedLoading_lbl]

theorem redBlackLoading_lbl_of_eq (s : Seq μ) (a : Fin (Multiset.card μ'))
    (ha : a.val = N₀) : (redBlackLoading i ν s).lbl a = .inr (Fin.last ℓ) := by
  have hb : a.val < Multiset.card (stendhalWeight (ℓ + 1) ν) := by
    simp [stendhalWeight] at ha ⊢; omega
  rw [redBlackLoading, appendBlackLoading_lbl_of_lt (ℓ := ℓ + 1) i ν _ _ hb]
  have h := hasLastRed_appendRedLoading s
  rwa [HasLastRed, show lastRedPosition ℓ ν = ⟨a.val, hb⟩ from Fin.ext (by
    simp [lastRedPosition, ha, stendhalWeight])] at h

theorem redBlackLoading_lbl_of_last (s : Seq μ) (a : Fin (Multiset.card μ'))
    (ha : a.val = N₀ + 1) : (redBlackLoading i ν s).lbl a = .inl i := by
  rw [redBlackLoading]
  exact appendBlackLoading_lbl_of_eq (ℓ := ℓ + 1) i ν _ _ (by
    simp [stendhalWeight] at ha ⊢; omega)

/-- The crossing of the last two strands exchanges `(s, i, λ_ℓ)` and `(s, λ_ℓ, i)`. -/
theorem swap_blackRedLoading (s : Seq μ) :
    sadj (Multiset.card μ') N₀ • blackRedLoading i ν s = redBlackLoading i ν s := by
  have hN : N₀ + 1 < Multiset.card μ' := by rw [card_stendhalWeight_append]; omega
  apply Subtype.ext
  funext a
  change (blackRedLoading i ν s).lbl ((sadj (Multiset.card μ') N₀).symm a) =
    (redBlackLoading i ν s).lbl a
  rw [show (sadj (Multiset.card μ') N₀).symm = sadj (Multiset.card μ') N₀ from
    TypeA.sadj_inv _ _]
  rcases lt_trichotomy a.val N₀ with h | h | h
  · rw [sadj_apply_of_ne a (by omega) (by omega), blackRedLoading_lbl_of_lt s a h,
      redBlackLoading_lbl_of_lt s a h]
  · rw [show a = ⟨N₀, by omega⟩ from Fin.ext h, sadj_apply_left hN,
      blackRedLoading_lbl_of_last s _ rfl, redBlackLoading_lbl_of_eq s _ rfl]
  · have h' : a.val = N₀ + 1 := by
      have := a.isLt
      have hc := card_stendhalWeight_append (ℓ := ℓ) i ν
      omega
    rw [show a = ⟨N₀ + 1, hN⟩ from Fin.ext h', sadj_apply_right hN,
      blackRedLoading_lbl_of_eq s _ rfl, redBlackLoading_lbl_of_last s _ rfl]

/-- The crossing of the last two strands exchanges `(s, λ_ℓ, i)` and `(s, i, λ_ℓ)`. -/
theorem swap_redBlackLoading (s : Seq μ) :
    sadj (Multiset.card μ') N₀ • redBlackLoading i ν s = blackRedLoading i ν s := by
  rw [← swap_blackRedLoading, smul_smul, TypeA.sadj_mul_self, one_smul]

theorem blackRedLoading_injective : Function.Injective (blackRedLoading (ℓ := ℓ) i ν) := by
  intro s t h
  apply Subtype.ext
  funext a
  have ha : a.val < Multiset.card (stendhalWeight (ℓ + 1) νᵢ) := by
    rw [card_stendhalWeight_append]; omega
  have := congrArg (fun u => u.lbl ⟨a.val, ha⟩) h
  have hs := blackRedLoading_lbl_of_lt (i := i) s ⟨a.val, ha⟩ a.isLt
  have ht := blackRedLoading_lbl_of_lt (i := i) t ⟨a.val, ha⟩ a.isLt
  exact addRedColor_injective ℓ (hs.symm.trans (this.trans ht))

theorem redBlackLoading_injective : Function.Injective (redBlackLoading (ℓ := ℓ) i ν) := by
  intro s t h
  apply blackRedLoading_injective
  rw [← swap_redBlackLoading, h, swap_redBlackLoading]

end Loadings

namespace StendhalAlgebraAllOrders

variable [DecidableEq I] {k : Type*} [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}
  {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}

theorem sum_e :
    (∑ s : Seq (stendhalWeight ℓ ν), e s : StendhalAlgebraAllOrders k Q Λ ν) = 1 := by
  simp only [e, ← map_sum, KLRAlgebra.sum_e, map_one]

theorem ψ_mul_e (j : ℕ) (s : Seq (stendhalWeight ℓ ν)) :
    (ψ j * e s : StendhalAlgebraAllOrders k Q Λ ν) =
      e (sadj (Multiset.card (stendhalWeight ℓ ν)) j • s) * ψ j := by
  rw [ψ, e, e, ← map_mul, KLRAlgebra.ψ_mul_e, map_mul]

theorem ψ_eq_zero (j : ℕ) (h : Multiset.card (stendhalWeight ℓ ν) ≤ j + 1) :
    (ψ j : StendhalAlgebraAllOrders k Q Λ ν) = 0 := by
  rw [ψ, KLRAlgebra.ψ_eq_zero j h, map_zero]

theorem ψ_mul_ψ (j l : ℕ) (h : j + 1 < l) :
    (ψ j * ψ l : StendhalAlgebraAllOrders k Q Λ ν) = ψ l * ψ j := by
  rw [ψ, ψ, ← map_mul, KLRAlgebra.ψ_mul_ψ j l h, map_mul]

theorem x_mul_ψ (a : Fin (Multiset.card (stendhalWeight ℓ ν))) (j : ℕ) (h₁ : a.val ≠ j)
    (h₂ : a.val ≠ j + 1) :
    (x a * ψ j : StendhalAlgebraAllOrders k Q Λ ν) = ψ j * x a := by
  rw [x, ψ, ← map_mul, KLRAlgebra.x_mul_ψ a j h₁ h₂, map_mul]

end StendhalAlgebraAllOrders

section Algebra

variable [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I) (ν : Multiset I)

local notation "Λ₀" => (Λ ∘ Fin.castSucc)
local notation "μ" => stendhalWeight ℓ ν
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "μ'" => stendhalWeight (ℓ + 1) νᵢ
local notation "N₀" => Multiset.card (stendhalWeight ℓ ν)
local notation "A₀" => StendhalAlgebraAllOrders k Q Λ₀ ν
local notation "A" => StendhalAlgebraAllOrders k Q Λ νᵢ

/-- Append the black strand `i` and then the last red strand `λ_ℓ` on the right of a
diagram: the loading `(s, i, λ_ℓ)`. -/
def blackRedValue (z : A₀) : A :=
  (appendRedAllOrders Q Λ νᵢ (appendBlackAllOrders Q Λ₀ i ν z).val).val

/-- Append the last red strand `λ_ℓ` and then the black strand `i` on the right of a
diagram: the loading `(s, λ_ℓ, i)`. -/
def redBlackValue (z : A₀) : A :=
  (appendBlackAllOrders Q Λ i ν (appendRedAllOrders Q Λ ν z).val).val

theorem blackRedValue_mul (z w : A₀) :
    blackRedValue Q Λ i ν (z * w) = blackRedValue Q Λ i ν z * blackRedValue Q Λ i ν w := by
  simp only [blackRedValue, map_mul, KLR.Corner.val_mul]

theorem redBlackValue_mul (z w : A₀) :
    redBlackValue Q Λ i ν (z * w) = redBlackValue Q Λ i ν z * redBlackValue Q Λ i ν w := by
  simp only [redBlackValue, map_mul, KLR.Corner.val_mul]

theorem blackRedValue_add (z w : A₀) :
    blackRedValue Q Λ i ν (z + w) = blackRedValue Q Λ i ν z + blackRedValue Q Λ i ν w := by
  simp only [blackRedValue, map_add, KLR.Corner.val_add]

theorem redBlackValue_add (z w : A₀) :
    redBlackValue Q Λ i ν (z + w) = redBlackValue Q Λ i ν z + redBlackValue Q Λ i ν w := by
  simp only [redBlackValue, map_add, KLR.Corner.val_add]

theorem blackRedValue_zero : blackRedValue Q Λ i ν 0 = 0 := by
  simp only [blackRedValue, map_zero, KLR.Corner.val_zero]

theorem redBlackValue_zero : redBlackValue Q Λ i ν 0 = 0 := by
  simp only [redBlackValue, map_zero, KLR.Corner.val_zero]

theorem blackRedValue_smul (c : k) (z : A₀) :
    blackRedValue Q Λ i ν (c • z) = c • blackRedValue Q Λ i ν z := by
  rw [blackRedValue, appendBlackAllOrders_smul, appendRedAllOrders_smul]; rfl

theorem redBlackValue_smul (c : k) (z : A₀) :
    redBlackValue Q Λ i ν (c • z) = c • redBlackValue Q Λ i ν z := by
  rw [redBlackValue, appendRedAllOrders_smul, appendBlackAllOrders_smul]; rfl

theorem blackRedValue_e (s : Seq μ) :
    blackRedValue Q Λ i ν (StendhalAlgebraAllOrders.e s) =
      StendhalAlgebraAllOrders.e (blackRedLoading i ν s) := by
  rw [blackRedValue, appendBlackAllOrders_e, appendRedAllOrders_e]; rfl

theorem redBlackValue_e (s : Seq μ) :
    redBlackValue Q Λ i ν (StendhalAlgebraAllOrders.e s) =
      StendhalAlgebraAllOrders.e (redBlackLoading i ν s) := by
  rw [redBlackValue, appendRedAllOrders_e, appendBlackAllOrders_e]; rfl

omit [DecidableEq I] in
private theorem lt_card_append (a : Fin N₀) : a.val < Multiset.card μ' := by
  have := card_stendhalWeight_append (ℓ := ℓ) i ν
  omega

theorem blackRedValue_x (a : Fin N₀) :
    blackRedValue Q Λ i ν (StendhalAlgebraAllOrders.x a) =
      StendhalAlgebraAllOrders.x ⟨a.val, lt_card_append i ν a⟩ *
        blackRedValue Q Λ i ν 1 := by
  rw [blackRedValue, appendBlackAllOrders_x, map_mul, KLR.Corner.val_mul,
    appendRedAllOrders_x, mul_assoc, ← KLR.Corner.val_mul, ← map_mul, one_mul]
  rfl

theorem redBlackValue_x (a : Fin N₀) :
    redBlackValue Q Λ i ν (StendhalAlgebraAllOrders.x a) =
      StendhalAlgebraAllOrders.x ⟨a.val, lt_card_append i ν a⟩ *
        redBlackValue Q Λ i ν 1 := by
  rw [redBlackValue, appendRedAllOrders_x, map_mul, KLR.Corner.val_mul,
    appendBlackAllOrders_x, mul_assoc, ← KLR.Corner.val_mul, ← map_mul, one_mul]
  rfl

theorem blackRedValue_ψ (j : ℕ) (hj : j + 1 < N₀) :
    blackRedValue Q Λ i ν (StendhalAlgebraAllOrders.ψ j) =
      StendhalAlgebraAllOrders.ψ j * blackRedValue Q Λ i ν 1 := by
  have hj' : j + 1 < Multiset.card (stendhalWeight ℓ νᵢ) := by
    simp [stendhalWeight] at hj ⊢; omega
  rw [blackRedValue, appendBlackAllOrders_ψ Q Λ₀ i ν j hj, map_mul, KLR.Corner.val_mul,
    appendRedAllOrders_ψ Q Λ νᵢ j hj', mul_assoc, ← KLR.Corner.val_mul, ← map_mul,
    one_mul]
  rfl

theorem redBlackValue_ψ (j : ℕ) (hj : j + 1 < N₀) :
    redBlackValue Q Λ i ν (StendhalAlgebraAllOrders.ψ j) =
      StendhalAlgebraAllOrders.ψ j * redBlackValue Q Λ i ν 1 := by
  have hj' : j + 1 < Multiset.card (stendhalWeight (ℓ + 1) ν) := by
    simp [stendhalWeight] at hj ⊢; omega
  rw [redBlackValue, appendRedAllOrders_ψ Q Λ ν j hj, map_mul, KLR.Corner.val_mul,
    appendBlackAllOrders_ψ Q Λ i ν j hj', mul_assoc, ← KLR.Corner.val_mul, ← map_mul,
    one_mul]
  rfl

local notation "ψ₀" => (StendhalAlgebraAllOrders.ψ N₀ : A)

private theorem slide_e (s : Seq μ) :
    blackRedValue Q Λ i ν (StendhalAlgebraAllOrders.e s) * ψ₀ =
      ψ₀ * redBlackValue Q Λ i ν (StendhalAlgebraAllOrders.e s) := by
  rw [blackRedValue_e, redBlackValue_e, StendhalAlgebraAllOrders.ψ_mul_e, swap_redBlackLoading]

private theorem slide_one :
    blackRedValue Q Λ i ν 1 * ψ₀ = ψ₀ * redBlackValue Q Λ i ν 1 := by
  rw [← StendhalAlgebraAllOrders.sum_e]
  induction (Finset.univ : Finset (Seq μ)) using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, blackRedValue_zero, redBlackValue_zero, zero_mul, mul_zero]
  | insert s t hs ih =>
    rw [Finset.sum_insert hs, blackRedValue_add, redBlackValue_add, add_mul, mul_add,
      slide_e, ih]

/-- A diagram on the old strands slides through the crossing of the appended black strand
`i` with the last red strand `λ_ℓ` (arXiv:1309.3796v3, §4.6, proof of Proposition 4.32). -/
theorem slide_crossing (z : A₀) :
    blackRedValue Q Λ i ν z * ψ₀ = ψ₀ * redBlackValue Q Λ i ν z := by
  obtain ⟨z, rfl⟩ := StendhalAlgebraAllOrders.ofKLR_surjective z
  obtain ⟨a, rfl⟩ := KLRAlgebra.mk_surjective z
  induction a using FreeAlgebra.induction with
  | grade0 r =>
    rw [AlgHom.commutes, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, blackRedValue_smul,
      redBlackValue_smul, smul_mul_assoc, mul_smul_comm, slide_one]
  | grade1 g =>
    cases g with
    | idem s => exact slide_e Q Λ i ν s
    | dot a =>
      change blackRedValue Q Λ i ν (StendhalAlgebraAllOrders.x a) * ψ₀ =
        ψ₀ * redBlackValue Q Λ i ν (StendhalAlgebraAllOrders.x a)
      rw [blackRedValue_x, redBlackValue_x, mul_assoc, slide_one, ← mul_assoc,
        StendhalAlgebraAllOrders.x_mul_ψ _ _ (by simp; omega) (by simp; omega), mul_assoc]
    | cross j =>
      change blackRedValue Q Λ i ν (StendhalAlgebraAllOrders.ψ j) * ψ₀ =
        ψ₀ * redBlackValue Q Λ i ν (StendhalAlgebraAllOrders.ψ j)
      by_cases hj : j + 1 < N₀
      · rw [blackRedValue_ψ Q Λ i ν j hj, redBlackValue_ψ Q Λ i ν j hj, mul_assoc, slide_one,
          ← mul_assoc, StendhalAlgebraAllOrders.ψ_mul_ψ j N₀ hj, mul_assoc]
      · rw [StendhalAlgebraAllOrders.ψ_eq_zero j (by omega), blackRedValue_zero,
          redBlackValue_zero, zero_mul, mul_zero]
  | mul a b ha hb =>
    rw [map_mul, map_mul, blackRedValue_mul, redBlackValue_mul, mul_assoc, hb, ← mul_assoc, ha,
      mul_assoc]
  | add a b ha hb =>
    rw [map_add, map_add, blackRedValue_add, redBlackValue_add, add_mul, mul_add, ha, hb]

end Algebra

end Categorification.Stendhal

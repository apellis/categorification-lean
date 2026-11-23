/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidedAppendCoset

set_option backward.isDefEq.respectTransparency false

/-!
# Standard diagrams through the appended black strand

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §6.1,
proof of Proposition 6.7. With the reduced words `lastCosetWord ρ` on the weight with an extra
black strand, every standard diagram `ψ_w x^u e(t)` with `t` ending in the new strand factors as
`ψ_c x_{last}^n` times the image of a standard diagram under the append map, where
`w = c (τ × 1)` is the last-coset factorisation.

## Main results

* `appendIdx` : the index `(s i, c (τ × 1), u + n·last)`.
* `coset_mul_appendBlackValue_basis` : `ψ_c x_last^n · append(ψ_{ρ τ} x^u e(s))` is the standard
  diagram with index `appendIdx c n b`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA MvPolynomial Equiv

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (i : I) (ν : Multiset I)

local notation "μ" => stendhalWeight ℓ ν
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "last" => lastPos (BraidedStendhalAlgebra.appendCard i ν (ℓ := ℓ))

namespace BraidedStendhalAlgebra

/-- Dots on the new last strand commute with crossings of old strands. -/
theorem commute_x_last_ψw {Q' : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k} {L : List ℕ}
    (hL : ValidWord (Multiset.card μ) L) (n : ℕ) :
    Commute (KLRAlgebra.x (Q := Q') (k := k) (ν := stendhalWeight ℓ νᵢ) last ^ n) (ψw L) := by
  refine Commute.pow_left ?_ n
  induction L with
  | nil => exact Commute.one_right _
  | cons j L ih =>
    rw [ψw_cons]
    have hj : j + 1 < Multiset.card μ := hL j (List.mem_cons_self ..)
    refine Commute.mul_right ?_ (ih fun a ha => hL a (List.mem_cons_of_mem _ ha))
    exact KLRAlgebra.x_mul_ψ _ j (by simp; omega) (by simp; omega)

omit [DecidableEq I] in
theorem appendPos_injective : Function.Injective (appendPos (ℓ := ℓ) i ν) := fun a b h =>
  Fin.ext (by simpa [appendPos] using congrArg Fin.val h)

omit [DecidableEq I] in
theorem appendPos_ne_last (a : Fin (Multiset.card μ)) : appendPos i ν a ≠ last := by
  intro h
  have := congrArg Fin.val h
  simp only [appendPos, lastPos_val] at this
  exact absurd a.isLt (by omega)

omit [DecidableEq I] in
theorem lt_of_lbl_isRight (s : Seq μ) (a : Fin (Multiset.card (stendhalWeight ℓ νᵢ)))
    (ha : ((appendBlackLoading i ν s).lbl a).isRight) : a.val < Multiset.card μ := by
  by_contra hn
  have := a.isLt
  have := card_stendhalWeight_addBlack i ν (ℓ := ℓ)
  rw [appendBlackLoading_lbl_of_eq i ν _ _ (by omega)] at ha
  simp at ha

/-- The dot vector `u + n · last` on the weight with the new strand. -/
def appendDots (u : Fin (Multiset.card μ) →₀ ℕ) (n : ℕ) :
    Fin (Multiset.card (stendhalWeight ℓ νᵢ)) →₀ ℕ :=
  u.mapDomain (appendPos i ν) + Finsupp.single last n

omit [DecidableEq I] in
theorem appendDots_appendPos (u : Fin (Multiset.card μ) →₀ ℕ) (n : ℕ)
    (a : Fin (Multiset.card μ)) : appendDots i ν u n (appendPos i ν a) = u a := by
  have h1 : (u.mapDomain (appendPos i ν)) (appendPos i ν a) = u a :=
    Finsupp.mapDomain_apply_of_injective (appendPos_injective i ν) u a
  rw [appendDots, Finsupp.add_apply, h1, Finsupp.single_eq_of_ne (appendPos_ne_last i ν a),
    add_zero]

omit [DecidableEq I] in
theorem appendDots_last (u : Fin (Multiset.card μ) →₀ ℕ) (n : ℕ) :
    appendDots i ν u n last = n := by
  rw [appendDots, Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.mapDomain_of_notMem_range _ _ (by rintro ⟨a, ha⟩; exact appendPos_ne_last i ν a ha),
    zero_add]

omit [DecidableEq I] in
theorem appendPos_val_cast (a : Fin (Multiset.card (stendhalWeight ℓ νᵢ)))
    (h : a.val < Multiset.card μ) : appendPos i ν ⟨a.val, h⟩ = a := Fin.ext rfl

/-- The index `(s i, c (τ × 1), u + n · last)`. -/
def appendIdx (c : Perm (Fin (Multiset.card (stendhalWeight ℓ νᵢ)))) (n : ℕ)
    (b : BlackIdx (ℓ := ℓ) ν) : BlackIdx (ℓ := ℓ) νᵢ :=
  ⟨(appendBlackLoading i ν b.1.1, c * extPerm (appendCard i ν) b.1.2.1,
      appendDots i ν b.1.2.2 n), fun a ha => by
    have h := lt_of_lbl_isRight i ν _ a ha
    change appendDots i ν b.1.2.2 n a = 0
    rw [← appendPos_val_cast i ν a h, appendDots_appendPos]
    refine b.2 _ ?_
    rw [← appendPos_val_cast i ν a h, appendBlackLoading_lbl_appendPos] at ha
    exact ha⟩

omit [DecidableEq I] in
theorem monomial_appendDots (u : Fin (Multiset.card μ) →₀ ℕ) (n : ℕ) :
    (monomial (appendDots i ν u n) 1 : MvPolynomial _ k) =
      rename (appendPos i ν) (monomial u 1) * X last ^ n := by
  rw [rename_monomial, X_pow_eq_monomial, monomial_mul_monomial, one_mul, appendDots]

variable (hQ : KLRSymm Q)
  (ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ) (hρ : IsReducedChoice ρ)

/-- `ψ_c x_last^n · append(ψ_{ρ τ} x^u e(s)) = ψ_{c(τ×1)} x^{u + n·last} e(s i)`, for `c` increasing
on the old strands. -/
theorem coset_mul_appendBlackValue_basis
    {c : Perm (Fin (Multiset.card (stendhalWeight ℓ νᵢ)))}
    (hc : StrictMono fun x : Fin (Multiset.card μ) => c (blockEquiv (appendCard i ν) (Sum.inl x)))
    (n : ℕ) (b : BlackIdx (ℓ := ℓ) ν) :
    ofKLR k Q Λ νᵢ (ψw (canWord _ c) * KLRAlgebra.x last ^ n) *
        appendBlackValue Q Λ i ν (basis hQ ρ hρ b) =
      basis (Λ := Λ) (ν := νᵢ) hQ (lastCosetWord (appendCard i ν) ρ)
        (isReducedChoice_lastCosetWord hρ) (appendIdx i ν c n b) := by
  have hsplit := lastCosetSplit_eq (appendCard i ν) (τ := b.1.2.1) hc
  rw [basis_apply, basis_apply, appendBlackValue_std Q Λ i ν (hρ _).1.1, ← map_mul]
  congr 1
  change _ = ψw (lastCosetWord (appendCard i ν) ρ (c * extPerm _ b.1.2.1)) *
    pol (monomial (appendDots i ν b.1.2.2 n) 1) * e (appendBlackLoading i ν b.1.1)
  rw [lastCosetWord, hsplit, ψw_append, monomial_appendDots, map_mul, map_pow,
    pol_X]
  have hx := (commute_x_last_ψw i ν (Q' := stendhalQ Q Λ) (hρ b.1.2.1).1.1 n).eq
  simp only [mul_assoc]
  rw [← mul_assoc (KLRAlgebra.x _ ^ n), hx, mul_assoc]
  congr 2
  rw [← mul_assoc, ← mul_assoc]
  congr 1
  rw [← pol_X, ← map_pow, ← map_mul, ← map_mul, mul_comm]

end BraidedStendhalAlgebra

end Categorification.Stendhal

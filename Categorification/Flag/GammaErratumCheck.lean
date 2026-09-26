/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.GammaCyclic
import Categorification.Flag.SlRootDatum

/-!
# `Γ_N` against the revised Definition 4.1 of the Khovanov–Lauda erratum

M. Khovanov, A. D. Lauda, *Erratum to: "A categorification of quantum sl(n)"*, Quantum Topol. 2
(2011), 97–99 ([Err]); the revised Definition 4.1 is formalized as
`Categorification.KL3.Diagram.Signed.presSignedQT` (literal) and `presSignedQT'` (consistent
variant) in `Categorification.Diagrams.KL3.SignedSlnErratum`.

We compare the relations changed by [Err] with the path-model maps of
`Categorification.Flag.GammaSideways` and `Categorification.Flag.GammaCyclic`, for adjacent
colours `i · j = -1` (`(slCartan m).dot i j = -1`). Here `crosslW i j` is `Γ_N` of the sideways
crossing `crossl i j : E_i F_j → F_j E_i` and `crossrW i j` that of
`crossr i j : F_j E_i → E_i F_j` ([Err] p. 98, first display, which fixes exactly these
composites); both are followed by an arbitrary 1-morphism `Y`.

## Results (`i · j = -1`)

* `downupEF_W_consistent` : `Γ(crossl i j ≫ crossr i j) = (j - i)` on `E_i F_j Y`;
* `downupFE_W_consistent` : `Γ(crossr i j ≫ crossl i j) = (j - i)` on `F_j E_i Y`;
* `rotCrossRW_add_rotCrossLW` : `Γ(rotCrossR) + Γ(rotCrossL) = 0` ([Err] p. 97 display, which is
  the same in the literal and the consistent version);
* `downupEF_W_ne_literal`, `downupFE_W_ne_literal` : the literal (3.13) of [Err] p. 98
  (`crossl i j ≫ crossr i j = (i - j)`, and `crossr i j ≫ crossl i j = (i - j)` from the second
  display with its `(i, j)` our `(j, i)`) fails whenever the bimodule is not killed by `2`.

In terms of `Rel`: `downupEF i j` of `presSignedQT'` is the first statement, `downupFE j i` of
`presSignedQT'` (`crossr i j ≫ crossl i j = (j - i)` on `F_j E_i`) is the second, and
`cycCrossR j i` of both presentations is the third; the literal `downupEF i j` resp.
`downupFE j i` of `presSignedQT` is the negation of the first resp. second.

The sign discrepancy comes from [Err]'s own revised Lemma 6.4 ([Err] p. 97): `Γ(crossl)` is the
swap and `Γ(crossr i j)` is minus the swap exactly when `j → i` (`i = j + 1`), which is what
`crosslW_one` and `crossrW_one` prove; the product is `-1 = j - i` for `i = j + 1` and
`1 = j - i` for `j = i + 1`. The index conventions agree with those of the signed `R(ν)`
relations of Definition 4.1, which `Γ_N` satisfies with the printed sign `(i - j)`
(`Categorification.KL3.Diagram.Signed.gammaCross_sq`).
-/

noncomputable section

open scoped TensorProduct

namespace Categorification.Flag

universe u

variable {K : Type u} [Field K] {m : ℕ}

/-- For `sl_{m+1}`, `i · j = -1` iff `i = j + 1` or `j = i + 1`. -/
theorem slCartan_dot_eq_neg_one_iff (i j : Fin m) :
    (slCartan m).dot i j = -1 ↔ (i.castSucc = j.succ ∨ j.castSucc = i.succ) := by
  have e : (i.castSucc = j.succ ∨ j.castSucc = i.succ) ↔
      ((i : ℕ) = (j : ℕ) + 1 ∨ (j : ℕ) = (i : ℕ) + 1) := by
    simp only [Fin.ext_iff, Fin.coe_castSucc, Fin.val_succ]
  rw [e, slCartan_dot]
  clear e
  split_ifs with h1 h2
  · subst h1
    constructor <;> intro h
    · exact absurd h (by decide)
    · rcases h with h | h <;> omega
  · constructor <;> intro _
    · omega
    · rfl
  · constructor <;> intro h
    · exact absurd h (by decide)
    · exact absurd (by rcases h with h | h <;> omega) h2

/-- For adjacent colours, `j - i = -1` if `i = j + 1` and `1` otherwise. -/
theorem sub_of_adj {i j : Fin m} (hadj : (slCartan m).dot i j = -1) :
    ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) = if i.castSucc = j.succ then -1 else 1 := by
  have h := (slCartan_dot_eq_neg_one_iff i j).1 hadj
  simp only [Fin.ext_iff, Fin.coe_castSucc, Fin.val_succ] at h
  split_ifs with h1
  · simp only [Fin.ext_iff, Fin.coe_castSucc, Fin.val_succ] at h1; clear hadj; omega
  · simp only [Fin.ext_iff, Fin.coe_castSucc, Fin.val_succ] at h1; clear hadj; omega

theorem ne_of_adj {i j : Fin m} (hadj : (slCartan m).dot i j = -1) : i ≠ j := by
  rintro rfl
  rw [slCartan_dot, if_pos rfl] at hadj
  exact absurd hadj (by decide)

/-- Multiplication by `-1` resp. `1`. -/
theorem mulB_intCast_sign {A B : Type u} [CommRing A] [CommRing B] (M : BRing A B) (P : Prop)
    [Decidable P] :
    BHom.mulB (((if P then -1 else 1 : ℤ)) : M.T) = if P then -BHom.id M else BHom.id M := by
  split_ifs <;> ext x <;> simp

/-- A bimodule map which is multiplication by both `s` and `-s`, `s = ±1`, forces `2 z = 0`. -/
theorem two_mul_eq_zero_of_mulB {A B : Type u} [CommRing A] [CommRing B] {M : BRing A B}
    {s : ℤ} (hs : s = 1 ∨ s = -1)
    (h : BHom.mulB ((s : ℤ) : M.T) = BHom.mulB ((-s : ℤ) : M.T)) (z : M.T) : (2 : M.T) * z = 0 := by
  have hz := congrArg (fun φ : BHom M M => φ z) h
  simp only [BHom.mulB_apply] at hz
  rcases hs with rfl | rfl
  · push_cast at hz
    rw [two_mul]; nth_rewrite 1 [← one_mul z]; rw [hz]; ring
  · push_cast at hz
    rw [two_mul]; nth_rewrite 1 [← neg_neg z, ← neg_one_mul z]; rw [hz]; ring

section DownUp

variable (i j : Fin m) {p q r q' : Comp m} (hEi : StepR (true, i) q p) (hFj : StepR (false, j) r q)
  (hFj' : StepR (false, j) q' p) (hEi' : StepR (true, i) r q') {E : Type u} [CommRing E]
  (Y : BRing (H K r) E)

/-- **The consistent `downupEF` holds on the path model**: for `i · j = -1`,
`Γ(crossl i j ≫ crossr i j)` is multiplication by `j - i` on `E_i F_j Y`
(relation `downupEF i j` of `presSignedQT'`). -/
theorem downupEF_W_consistent (hadj : (slCartan m).dot i j = -1) :
    (crossrW K i j hFj' hEi' hEi hFj Y).comp (crosslW K i j hEi hFj hFj' hEi' Y) =
      BHom.mulB ((((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) : ℤ) : _) := by
  rw [downupEF_W i j hEi hFj hFj' hEi' Y (ne_of_adj hadj), sub_of_adj hadj, mulB_intCast_sign]

/-- **The consistent `downupFE` holds on the path model**: for `i · j = -1`,
`Γ(crossr i j ≫ crossl i j)` is multiplication by `j - i` on `F_j E_i Y`
(relation `downupFE j i` of `presSignedQT'`). -/
theorem downupFE_W_consistent (hadj : (slCartan m).dot i j = -1) :
    (crosslW K i j hEi hFj hFj' hEi' Y).comp (crossrW K i j hFj' hEi' hEi hFj Y) =
      BHom.mulB ((((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) : ℤ) : _) := by
  rw [downupFE_W i j hEi hFj hFj' hEi' Y (ne_of_adj hadj), sub_of_adj hadj, mulB_intCast_sign]

theorem sign_of_adj {i j : Fin m} (hadj : (slCartan m).dot i j = -1) :
    ((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) = 1 ∨ ((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) = -1 := by
  have := sub_of_adj hadj
  split_ifs at this <;> omega

/-- **The literal `downupEF` of [Err] p. 98 fails on the path model**: for `i · j = -1`,
`Γ(crossl i j ≫ crossr i j)` is not multiplication by the printed `i - j`, unless `2` kills
`E_i F_j Y`. -/
theorem downupEF_W_ne_literal (hadj : (slCartan m).dot i j = -1)
    (h2 : ∃ z : ((stepB K (true, i) q p hEi).tensor ((stepB K (false, j) r q hFj).tensor Y)).T,
      (2 : _) * z ≠ 0) :
    (crossrW K i j hFj' hEi' hEi hFj Y).comp (crosslW K i j hEi hFj hFj' hEi' Y) ≠
      BHom.mulB ((((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ) : _) := by
  intro h
  rw [downupEF_W_consistent i j hEi hFj hFj' hEi' Y hadj,
    show ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) = -(((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) by ring] at h
  obtain ⟨z, hz⟩ := h2
  exact hz (two_mul_eq_zero_of_mulB (sign_of_adj hadj) h.symm z)

/-- **The literal `downupFE` of [Err] p. 98 fails on the path model**: for `i · j = -1`,
`Γ(crossr i j ≫ crossl i j)` on `F_j E_i Y` is not multiplication by the printed sign (the
second display with its `(i, j)` our `(j, i)`, i.e. `i - j`), unless `2` kills `F_j E_i Y`. -/
theorem downupFE_W_ne_literal (hadj : (slCartan m).dot i j = -1)
    (h2 : ∃ z : ((stepB K (false, j) q' p hFj').tensor ((stepB K (true, i) r q' hEi').tensor Y)).T,
      (2 : _) * z ≠ 0) :
    (crosslW K i j hEi hFj hFj' hEi' Y).comp (crossrW K i j hFj' hEi' hEi hFj Y) ≠
      BHom.mulB ((((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ) : _) := by
  intro h
  rw [downupFE_W_consistent i j hEi hFj hFj' hEi' Y hadj,
    show ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) = -(((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) by ring] at h
  obtain ⟨z, hz⟩ := h2
  exact hz (two_mul_eq_zero_of_mulB (sign_of_adj hadj) h.symm z)

end DownUp

section Cyclic

variable (i j : Fin m) {t r₁ r₂ w : Comp m} (hFj : StepR (false, j) r₁ t)
  (hFi : StepR (false, i) r₂ r₁) (hFi' : StepR (false, i) w t) (hFj' : StepR (false, j) r₂ w)
  {E : Type u} [CommRing E] (Y : BRing (H K r₂) E)

/-- **The revised cyclicity of [Err] p. 97 holds on the path model**: for `i · j = -1`,
`Γ(rotCrossR j i) + Γ(rotCrossL j i) = 0` (relation `cycCrossR j i` of `presSignedQT` and
`presSignedQT'`). -/
theorem rotCrossRW_add_rotCrossLW (hadj : (slCartan m).dot i j = -1) :
    rotCrossRW K i j hFj hFi hFi' hFj' Y + rotCrossLW K i j hFj hFi hFi' hFj' Y = 0 := by
  rw [rotCrossRW_eq_neg_rotCrossLW i j hFj hFi hFi' hFj' Y (ne_of_adj hadj)
    ((slCartan_dot_eq_neg_one_iff i j).1 hadj)]
  ext x
  simp

end Cyclic

end Categorification.Flag

end

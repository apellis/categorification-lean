/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.GammaFlagBraid
import Categorification.Diagrams.KL3.GammaFlagDecomp

/-!
# The KLR relations of `Γ_N` in degenerate regions

KL III, arXiv:0807.3250v1, Definition 4.1 (eqs. (4.11), (4.13), (4.14)) and Proposition 6.8.

In the path model a 1-morphism `E_{i₁} ⋯ E_{iₖ} 1_λ` is zero as soon as one intermediate region
fails to be a composition (a block would become negative). The relations of the KLR algebra on
two and three strands (`Categorification.KLR.Diagram.Rel`) are equations between maps
`E_c E_d 1_λ → E_d E_c 1_λ` resp. `E_c E_d E_e 1_λ → E_e E_d E_c 1_λ`; a composite passing through
a zero 1-morphism is zero. This file classifies the possible degeneracies and proves the
identities the surviving side must then satisfy.

## Two strands: the double crossing (4.11)

`swap_cases`: if `E_i E_j 1_λ ≠ 0`, then either `E_j E_i 1_λ ≠ 0` (`gammaCross_sq` applies), or
`j = i + 1` and `λ_{i+1} = 0`. In the latter case the composite `ψ_{ji} ψ_{ij}` is zero, and
`Q^τ_{ij}(ξ_i, ξ_j)` vanishes on `E_i E_j 1_λ` because the two dots coincide (`degen_xi_eq`: the
variable moved by `E_j` into the empty block `i + 1` is the one moved on by `E_i`):
`degen_qSigned_eq_zero`, `degen_cross_sq`.

## Three strands: the braid relations (4.13), (4.14)

`braid_cases`: if `E_c E_d E_e 1_λ ≠ 0` and `E_e E_d E_c 1_λ ≠ 0`, then either all four
intermediate 1-morphisms of `ψ₀ψ₁ψ₀` and `ψ₁ψ₀ψ₁` are nonzero (`braid_three`, `braidQ_three`,
`braidQ_signed` apply), or `c = e` and exactly one of the following holds:

* (a) `d = c + 1` and `λ_{c+1} = 1`: `E_d E_c E_c 1_λ = 0`, so `ψ₀ψ₁ψ₀ = 0`, while `ψ₁ψ₀ψ₁` passes
  through `E_c E_c E_d 1_λ ≠ 0`; the relation reads `ψ₁ψ₀ψ₁ = 1` (`braidR_degenerate`);
* (b) `c = d + 1` and `λ_{d+1} = 0`: `E_c E_c E_d 1_λ = 0`, so `ψ₁ψ₀ψ₁ = 0`, while `ψ₀ψ₁ψ₀` passes
  through `E_d E_c E_c 1_λ ≠ 0`; the relation reads `ψ₀ψ₁ψ₀ = 1` (`braidL_degenerate`).

In both cases `Q̄^τ_{cd}` is the constant `∓1` and the extra term of the polynomial identity
`braid_poly` is killed by the coincidence of two dots in the target. When `c ≠ e` no degeneracy
occurs at all (given a nonzero source and target), and when the source or the target is zero both
sides of every relation are zero. Together with the dot slides (`crossU_rules`, whose source and
target are the two 1-morphisms of the relation) this covers every instance of the KLR relations on
two and three strands of any path.
-/

noncomputable section

namespace Categorification.KL3.Diagram.Signed

open Categorification.Flag MvPolynomial

universe u

variable {K : Type u} [Field K] {m : ℕ}

/-! ### Regions -/

section Regions

variable {m : ℕ}

theorem raise_val (i : Fin m) (d : Fin (m + 1) → ℕ) (j : Fin (m + 1)) :
    raise i d j = if j = i.castSucc then d j + 1 else if j = i.succ then d j - 1 else d j := rfl

/-- Case analysis on the value of a raised composition at a block. -/
theorem raise_val_elim (i : Fin m) (d : Fin (m + 1) → ℕ) (k : Fin (m + 1)) {P : ℕ → Prop}
    (h : P (raise i d k)) :
    (k = i.castSucc ∧ P (d k + 1)) ∨ (k ≠ i.castSucc ∧ k = i.succ ∧ P (d k - 1)) ∨
      (k ≠ i.castSucc ∧ k ≠ i.succ ∧ P (d k)) := by
  rw [raise_val] at h
  by_cases hA : k = i.castSucc
  · rw [if_pos hA] at h
    exact Or.inl ⟨hA, h⟩
  · rw [if_neg hA] at h
    by_cases hB : k = i.succ
    · rw [if_pos hB] at h
      exact Or.inr (Or.inl ⟨hA, hB, h⟩)
    · rw [if_neg hB] at h
      exact Or.inr (Or.inr ⟨hA, hB, h⟩)

/-- Two raises commute, provided no block becomes negative in between. -/
theorem raise_comm (i j : Fin m) (d : Fin (m + 1) → ℕ) (hij : i.succ = j.castSucc → 0 < d i.succ)
    (hji : j.succ = i.castSucc → 0 < d j.succ) : raise i (raise j d) = raise j (raise i d) := by
  funext k
  have hi := castSucc_ne_succ' i
  have hi' := (castSucc_ne_succ' i).symm
  have hj := castSucc_ne_succ' j
  have hj' := (castSucc_ne_succ' j).symm
  by_cases h1 : k = i.castSucc
  · subst h1
    by_cases h3 : i.castSucc = j.castSucc
    · have := Fin.castSucc_injective _ h3
      subst this
      rfl
    · by_cases h4 : i.castSucc = j.succ
      · have := hji h4.symm
        rw [← h4] at this
        simp only [raise_val, if_true, if_neg hi, if_neg h3, if_pos h4]
        omega
      · simp only [raise_val, if_true, if_neg hi, if_neg h3, if_neg h4]
  · by_cases h2 : k = i.succ
    · subst h2
      by_cases h3 : i.succ = j.castSucc
      · have := hij h3
        simp only [raise_val, if_neg h1, if_true, if_pos h3]
        omega
      · by_cases h4 : i.succ = j.succ
        · have := Fin.succ_injective _ h4
          subst this
          rfl
        · simp only [raise_val, if_neg h1, if_true, if_neg h3, if_neg h4]
    · simp only [raise_val, if_neg h1, if_neg h2]

/-- **Two strands.** If `E_i E_j 1_{r₂}` is nonzero, then either `E_j E_i 1_{r₂}` is nonzero, or
`j = i + 1` and block `i + 1` of `r₂` is empty. -/
theorem swap_cases (i j : Fin m) {t r₁ r₂ : Comp m} (h₁ : StepR (true, i) r₁ t)
    (h₂ : StepR (true, j) r₂ r₁) :
    (∃ r₁' : Comp m, StepR (true, j) r₁' t ∧ StepR (true, i) r₂ r₁') ∨
      (j.castSucc = i.succ ∧ r₂ i.succ = 0) := by
  have hi' := (castSucc_ne_succ' i).symm
  by_cases hz : r₂ i.succ = 0
  · right
    refine ⟨?_, hz⟩
    have := h₁.2
    rw [← h₂.1] at this
    rcases raise_val_elim j r₂ i.succ this with ⟨hA, _⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩
    · exact hA.symm
    · omega
    · omega
  · left
    refine ⟨raise i r₂, ⟨?_, ?_⟩, ⟨rfl, Nat.pos_of_ne_zero hz⟩⟩
    · rw [raise_comm j i r₂ (fun _ => h₂.2) (fun _ => Nat.pos_of_ne_zero hz), h₂.1, h₁.1]
    · rw [raise_val]
      by_cases hA : j.succ = i.castSucc
      · rw [if_pos hA]; omega
      · rw [if_neg hA]
        by_cases hB : j.succ = i.succ
        · rw [if_pos hB]
          have := Fin.succ_injective _ hB
          subst this
          have := h₁.2
          rw [← h₂.1, raise_val, if_neg hi', if_pos rfl] at this
          exact this
        · rw [if_neg hB]
          exact h₂.2

/-- **Three strands.** If `E_c E_d E_e 1_{r₃}` and `E_e E_d E_c 1_{r₃}` are nonzero, then either
all intermediate 1-morphisms of `ψ₀ψ₁ψ₀` and `ψ₁ψ₀ψ₁` are nonzero, or `c = e` and one of the two
degenerate configurations (a), (b) occurs (in which case the target regions coincide with the source
regions, and the intermediate 1-morphisms of the surviving side are nonzero). -/
theorem braid_cases (c d e : Fin m) {s r₁ r₂ r₃ f₁ f₂ : Comp m} (h₁ : StepR (true, c) r₁ s)
    (h₂ : StepR (true, d) r₂ r₁) (h₃ : StepR (true, e) r₃ r₂) (hf₁ : StepR (true, e) f₁ s)
    (hd₂ : StepR (true, d) f₂ f₁) (hc₃ : StepR (true, c) r₃ f₂) :
    (∃ a₁ b₂ : Comp m, StepR (true, d) a₁ s ∧ StepR (true, c) r₂ a₁ ∧ StepR (true, e) f₂ a₁ ∧
      StepR (true, e) b₂ r₁ ∧ StepR (true, d) r₃ b₂ ∧ StepR (true, c) b₂ f₁) ∨
    (c = e ∧ d.castSucc = c.succ ∧ r₃ c.succ = 1 ∧ r₂ c.succ = 0 ∧ f₂ = r₂ ∧ f₁ = r₁ ∧
      ∃ b₂ : Comp m, StepR (true, c) b₂ r₁ ∧ StepR (true, d) r₃ b₂) ∨
    (c = e ∧ c.castSucc = d.succ ∧ r₃ d.succ = 0 ∧ f₂ = r₂ ∧ f₁ = r₁ ∧
      ∃ a₁ : Comp m, StepR (true, d) a₁ s ∧ StepR (true, c) r₂ a₁) := by
  have hc := castSucc_ne_succ' c
  have hc' := (castSucc_ne_succ' c).symm
  have hd := castSucc_ne_succ' d
  have hd' := (castSucc_ne_succ' d).symm
  -- the target regions when `c = e`
  have htarget : c = e → f₂ = r₂ ∧ f₁ = r₁ := by
    intro hce
    subst hce
    have e2 : f₂ = r₂ := hc₃.1.symm.trans h₃.1
    exact ⟨e2, by rw [← hd₂.1, e2, h₂.1]⟩
  rcases swap_cases c d h₁ h₂ with ⟨a₁, ha₁, ha₂⟩ | ⟨hdc, hr₂⟩
  · rcases swap_cases c e ha₂ h₃ with ⟨f₂', hf₂', hc₃'⟩ | ⟨_, hr₃⟩
    · have hf : f₂' = f₂ := hc₃'.1.symm.trans hc₃.1
      subst hf
      rcases swap_cases d e h₂ h₃ with ⟨b₂, hb₂, hb₃⟩ | ⟨hed, hr₃⟩
      · rcases swap_cases c e h₁ hb₂ with ⟨f₁', hf₁', hb₁'⟩ | ⟨hec, hb⟩
        · have hf : f₁' = f₁ := by
            rw [← hb₁'.1, ← hd₂.1, ← hc₃.1, ← hb₃.1]
            exact raise_comm c d r₃ (fun _ => hc₃.2) (fun _ => hb₃.2)
          subst hf
          exact Or.inl ⟨a₁, b₂, ha₁, ha₂, hf₂', hb₂, hb₃, hb₁'⟩
        · exfalso
          have h1 := hc₃.2
          rw [← hb₃.1] at hb
          rcases raise_val_elim d r₃ c.succ (P := fun n => n = 0) hb with ⟨_, hb⟩ | ⟨_, hB, hb⟩ | ⟨_, _, hb⟩
          · omega
          · have := Fin.succ_injective _ hB
            subst this
            have h2 := hd₂.2
            rw [← hc₃.1, raise_val, if_neg hc', if_pos rfl] at h2
            omega
          · omega
      · -- braidR's first intermediate is missing: `e = d + 1`, `r₃ d.succ = 0`
        have h2 := hd₂.2
        rw [← hc₃.1] at h2
        rcases raise_val_elim c r₃ d.succ h2 with ⟨hA, _⟩ | ⟨_, _, h2⟩ | ⟨_, _, h2⟩
        · have hce : c = e := Fin.castSucc_injective _ (hA.symm.trans hed.symm)
          subst hce
          obtain ⟨e2, e1⟩ := htarget rfl
          exact Or.inr (Or.inr ⟨rfl, hA.symm, hr₃, e2, e1, a₁, ha₁, ha₂⟩)
        · omega
        · omega
    · exfalso
      exact absurd hr₃ hc₃.2.ne'
  · -- braidL's first intermediate is missing: `d = c + 1`, `r₂ c.succ = 0`
    have h1 := hc₃.2
    have hce : c = e ∧ r₃ c.succ = 1 := by
      rw [← h₃.1] at hr₂
      rcases raise_val_elim e r₃ c.succ (P := fun n => n = 0) hr₂ with ⟨_, h⟩ | ⟨_, hB, h⟩ | ⟨_, _, h⟩
      · omega
      · exact ⟨Fin.succ_injective _ hB, by omega⟩
      · omega
    obtain ⟨hce, hr₃⟩ := hce
    subst hce
    obtain ⟨e2, e1⟩ := htarget rfl
    refine Or.inr (Or.inl ⟨rfl, hdc, hr₃, hr₂, e2, e1, ?_⟩)
    rcases swap_cases d c h₂ h₃ with ⟨b₂, hb₂, hb₃⟩ | ⟨hcd, _⟩
    · exact ⟨b₂, hb₂, hb₃⟩
    · exfalso
      rw [castSucc_eq_succ_iff] at hdc hcd
      omega

end Regions

/-! ### Coincidence of the dots -/

section Dots

variable (c : Fin m)

/-- If block `c + 1` of the right region of `E_c` has one element, the dot of `E_c` is the Chern
class `x_{c+1,1}` of that element, acting on the right. -/
theorem xi_eq_right_x {s r : Comp m} (h : StepR (true, c) s r) (hs : s c.succ = 1) :
    xiStep K (true, c) s r h = (stepB K (true, c) s r h).right (x K s c.succ 1) := by
  have hc := Eright_charpoly (K := K) c h
  rw [hs, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hc
  simp only [pow_zero, pow_one, one_mul, x_zero, map_one, Nat.sub_self, Nat.sub_zero, mul_one,
    neg_one_mul] at hc
  exact sub_eq_zero.1 ((sub_eq_add_neg _ _).trans hc)

/-- If block `c` of the left region of `E_c` has one element, the dot of `E_c` is the Chern class
`x_{c,1}` of that element, acting on the left. -/
theorem xi_eq_left_x {t r : Comp m} (h : StepR (true, c) t r) (hr : r c.castSucc = 1) :
    xiStep K (true, c) t r h = (stepB K (true, c) t r h).left (x K r c.castSucc 1) := by
  have hc := Eleft_charpoly (K := K) c h
  rw [hr, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hc
  simp only [pow_zero, pow_one, one_mul, x_zero, map_one, Nat.sub_self, Nat.sub_zero, mul_one,
    neg_one_mul] at hc
  exact sub_eq_zero.1 ((sub_eq_add_neg _ _).trans hc)

variable {c} {d : Fin m} {t r₁ r₂ : Comp m} (h₁ : StepR (true, c) r₁ t) (h₂ : StepR (true, d) r₂ r₁)

include h₂ in
theorem degen_middle (hadj : d.castSucc = c.succ) (hdeg : r₂ c.succ = 0) : r₁ c.succ = 1 := by
  rw [← h₂.1, ← hadj, raise_castSucc, hadj, hdeg]

/-- **The two dots of `E_c E_{c+1} 1_λ` coincide when `λ_{c+1} = 0`**: the variable moved by
`E_{c+1}` into the empty block `c + 1` is the variable moved on by `E_c`. -/
theorem degen_xi_eq (hadj : d.castSucc = c.succ) (hdeg : r₂ c.succ = 0) :
    BRing.tmul (stepB K (true, c) r₁ t h₁) (stepB K (true, d) r₂ r₁ h₂) (eXi K c r₁ h₁.2) 1 =
      BRing.tmul (stepB K (true, c) r₁ t h₁) (stepB K (true, d) r₂ r₁ h₂) 1 (eXi K d r₂ h₂.2) := by
  have h1 := degen_middle h₂ hadj hdeg
  have e1 : eXi K c r₁ h₁.2 = xiStep K (true, c) r₁ t h₁ := rfl
  have e2 : eXi K d r₂ h₂.2 = xiStep K (true, d) r₂ r₁ h₂ := rfl
  rw [e1, e2, xi_eq_right_x c h₁ h1, xi_eq_left_x d h₂ (by rw [hadj]; exact h1), hadj,
    ← mul_one ((stepB K (true, c) r₁ t h₁).right _), BRing.tmul_balance, mul_one]

/-- **KL III (4.11) in the degenerate region**: on `E_c E_{c+1} 1_λ` with `λ_{c+1} = 0` (so that
`E_{c+1} E_c 1_λ = 0` and the double crossing vanishes), `Q^τ_{c,c+1}(ξ_c, ξ_{c+1}) = 0`. -/
theorem degen_qSigned_eq_zero (hadj : d.castSucc = c.succ) (hdeg : r₂ c.succ = 0) :
    eval₂ (scal h₁ h₂) ![BRing.tmul _ _ (eXi K c r₁ h₁.2) 1, BRing.tmul _ _ 1 (eXi K d r₂ h₂.2)]
      (qSigned K m c d) = 0 := by
  have hcd : c ≠ d := fun h => by subst h; exact castSucc_ne_succ' c hadj
  have hval := castSucc_eq_succ_iff.1 hadj
  have hdot : (slCartan m).dot c d = -1 := by
    rw [slCartan_dot, if_neg hcd, if_pos (Or.inl hval.symm)]
  rw [qSigned_of_adj hdot, show ((c : ℕ) : ℤ) - ((d : ℕ) : ℤ) = -1 by omega, neg_one_zsmul,
    eval₂_neg, eval₂_sub, eval₂_X, eval₂_X]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [degen_xi_eq h₁ h₂ hadj hdeg, sub_self, neg_zero]

/-- The double-crossing relation in the degenerate region, as an equation of maps: both sides
are zero on `E_c E_{c+1} 1_λ` (the composite through `E_{c+1} E_c 1_λ = 0`, and multiplication by
`Q^τ`). -/
theorem degen_cross_sq (hadj : d.castSucc = c.succ) (hdeg : r₂ c.succ = 0) :
    BHom.mulB (eval₂ (scal h₁ h₂) ![BRing.tmul _ _ (eXi K c r₁ h₁.2) 1,
      BRing.tmul _ _ 1 (eXi K d r₂ h₂.2)] (qSigned K m c d)) = (0 : BHom (TwoP (K := K) h₁ h₂) _) := by
  rw [degen_qSigned_eq_zero h₁ h₂ hadj hdeg]
  exact BHom.ext fun z => zero_mul z

end Dots

/-! ### The braid relations in the degenerate regions -/

section Braid

theorem qbar_X1_sub_X0 : KLR.qbar (X 1 - X 0 : MvPolynomial (Fin 2) K) = -1 := by
  apply X_sub_X_mul_left_cancel (show (0 : Fin 3) ≠ 2 by decide)
  rw [KLR.qbar_spec, map_sub, map_sub, rename_X, rename_X, rename_X, rename_X]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  ring

theorem qbar_X0_sub_X1 : KLR.qbar (X 0 - X 1 : MvPolynomial (Fin 2) K) = 1 := by
  apply X_sub_X_mul_left_cancel (show (0 : Fin 3) ≠ 2 by decide)
  rw [KLR.qbar_spec, map_sub, map_sub, rename_X, rename_X, rename_X, rename_X]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  ring

variable (c d : Fin m)

theorem Qf_of_castSucc_eq_succ (hadj : d.castSucc = c.succ) : Qf K c d = X 1 - X 0 := by
  have hadj' : ¬ c.castSucc = d.succ := by rw [castSucc_eq_succ_iff] at hadj ⊢; omega
  rw [Qf, Fc, Fc, if_pos hadj, if_neg hadj', map_one, mul_one]

theorem Qf_of_succ_eq_castSucc (hadj : c.castSucc = d.succ) : Qf K c d = X 0 - X 1 := by
  have hadj' : ¬ d.castSucc = c.succ := by rw [castSucc_eq_succ_iff] at hadj ⊢; omega
  rw [Qf, Fc, Fc, if_neg hadj', if_pos hadj, one_mul, map_sub, rename_X, rename_X]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

variable {s r₁ r₂ r₃ a₁ b₂ : Comp m} {E : Type u} [CommRing E]
  (h₁ : StepR (true, c) r₁ s) (h₂ : StepR (true, d) r₂ r₁) (h₃ : StepR (true, c) r₃ r₂)
  (Y : BRing (H K r₃) E)

/-- **KL III (4.14) in the degenerate region (a)**: on `E_c E_{c+1} E_c 1_λ` with `λ_{c+1} = 1`,
`E_{c+1} E_c E_c 1_λ = 0`, so `Γ_N(ψ₀ψ₁ψ₀) = 0`, and the relation
`ψ₀ψ₁ψ₀ − ψ₁ψ₀ψ₁ = Q̄^τ_{c,c+1}(ξ₀, ξ₁, ξ₂) = −1` reads `Γ_N(ψ₁ψ₀ψ₁) = 1`. -/
theorem braidR_degenerate (hadj : d.castSucc = c.succ) (hdeg : r₃ c.succ = 1)
    (hb₂ : StepR (true, c) b₂ r₁) (hb₃ : StepR (true, d) r₃ b₂) :
    braidR K c d c h₁ h₂ h₃ hb₂ hb₃ hb₂ h₁ h₂ h₃ Y = BHom.id _ := by
  have hcd : c ≠ d := fun h => by subst h; exact castSucc_ne_succ' c hadj
  have hr₂ : r₂ c.succ = 0 := by rw [← h₃.1, raise_succ, hdeg]
  have hzero : ∀ q, ev3 K (stepB K _ _ _ h₁) (stepB K _ _ _ h₂) (stepB K _ _ _ h₃) Y
      (eXi K c r₁ h₁.2) (eXi K d r₂ h₂.2) (eXi K c r₃ h₃.2) (op0 d c q) = 0 := by
    intro q
    rw [op0, if_neg (Ne.symm hcd), mS0, Fc, if_pos hadj, map_mul, ev3_at01_sub,
      degen_xi_eq h₁ h₂ hadj hr₂, sub_self, BRing.zero_tmul, BHom.map_zero, zero_mul]
  refine ext3 (K := K) _ _ _ Y (eXi K c r₁ h₁.2) (eXi K d r₂ h₂.2) (eXi K c r₃ h₃.2)
    (stepE_spanned c h₁) (stepE_spanned d h₂) (stepE_spanned c h₃) _ _ fun p x => ?_
  have hp := braid_poly c d c p
  rw [if_pos ⟨rfl, hcd⟩, Qf_of_castSucc_eq_succ c d hadj, qbar_X1_sub_X0, neg_one_mul] at hp
  have hB : op1 c d (op0 c c (op1 d c p)) = op0 d c (op1 c c (op0 c d p)) + p := by
    linear_combination (-1 : MvPolynomial (Fin 3) K) * hp
  rw [braidR_eval, BHom.id_apply, hB, map_add, hzero, zero_add]

/-- **KL III (4.14) in the degenerate region (b)**: on `E_c E_{c-1} E_c 1_λ` with `λ_c = 0`,
`E_c E_c E_{c-1} 1_λ = 0`, so `Γ_N(ψ₁ψ₀ψ₁) = 0`, and the relation
`ψ₀ψ₁ψ₀ − ψ₁ψ₀ψ₁ = Q̄^τ_{c,c-1}(ξ₀, ξ₁, ξ₂) = 1` reads `Γ_N(ψ₀ψ₁ψ₀) = 1`. -/
theorem braidL_degenerate (hadj : c.castSucc = d.succ) (hdeg : r₃ d.succ = 0)
    (ha₁ : StepR (true, d) a₁ s) (ha₂ : StepR (true, c) r₂ a₁) :
    braidL K c d c h₁ h₂ h₃ ha₁ ha₂ ha₂ h₁ h₂ h₃ Y = BHom.id _ := by
  have hcd : c ≠ d := fun h => by subst h; exact castSucc_ne_succ' c hadj
  have hzero : ∀ q, ev3 K (stepB K _ _ _ h₁) (stepB K _ _ _ h₂) (stepB K _ _ _ h₃) Y
      (eXi K c r₁ h₁.2) (eXi K d r₂ h₂.2) (eXi K c r₃ h₃.2) (op1 c d q) = 0 := by
    intro q
    rw [op1, if_neg hcd, mS1, Fc, if_pos hadj, map_mul, ev3_at12_sub,
      degen_xi_eq h₂ h₃ hadj hdeg, sub_self, BRing.zero_tmul, BHom.map_zero, BRing.tmul_zero,
      zero_mul]
  refine ext3 (K := K) _ _ _ Y (eXi K c r₁ h₁.2) (eXi K d r₂ h₂.2) (eXi K c r₃ h₃.2)
    (stepE_spanned c h₁) (stepE_spanned d h₂) (stepE_spanned c h₃) _ _ fun p x => ?_
  have hp := braid_poly c d c p
  rw [if_pos ⟨rfl, hcd⟩, Qf_of_succ_eq_castSucc c d hadj, qbar_X0_sub_X1, one_mul] at hp
  have hA : op0 d c (op1 c c (op0 c d p)) = op1 c d (op0 c c (op1 d c p)) + p := by
    linear_combination hp
  rw [braidL_eval, BHom.id_apply, hA, map_add, hzero, zero_add]

end Braid

end Categorification.KL3.Diagram.Signed

end

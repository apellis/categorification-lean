/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.KL1

/-!
# The idempotent decomposition of `1_{iji}`

M. Khovanov, A. Lauda, *A diagrammatic approach to categorification of quantum groups I*,
arXiv:0803.4121v2, §2.2 ("Examples"), the Remark after item 7) and the displayed computation
following it (TeX label `eq_square`).

If `i · j = -1` (i.e. `i` and `j` are joined by an edge of `Γ`), the elements
`ψ_1 ψ_2 ψ_1 1_{iji}` and `-ψ_2 ψ_1 ψ_2 1_{iji}` of `R(2i + j)` are mutually orthogonal
idempotents; by (2.8) (`KL1.braid_hard`) they sum to `1_{iji}`. Positions are zero-indexed:
the paper's `ψ_1`, `ψ_2` are `ψ 0`, `ψ 1` here.

## Main results

* `KL1.Remark.idemL_mul_self` : `(ψ_1 ψ_2 ψ_1 1_{iji})² = ψ_1 ψ_2 ψ_1 1_{iji}` (equation
  `eq_square`; the proof follows the paper's diagrammatic computation).
* `KL1.Remark.idemR_mul_self`, `KL1.Remark.idemL_mul_idemR`, `KL1.Remark.idemR_mul_idemL`,
  `KL1.Remark.idemL_add_idemR` : the rest of the Remark.

These hold over any commutative ring `k`.
-/

namespace Categorification.KLR.KL1

open MvPolynomial Equiv TypeA KLRAlgebra

variable {I : Type*} [DecidableEq I] {Γ : SimpleGraph I} [DecidableRel Γ.Adj]
  {k : Type*} [CommRing k]

namespace Remark

variable (i j : I)

/-- The weight `2i + j`, written so that `iji` is its defining sequence. -/
abbrev ν₃ : Multiset I := {i, j, i}

/-- The sequence `iji`. -/
def iji : Seq (ν₃ i j) := ⟨![i, j, i], by rw [Fin.univ_val_map]; rfl⟩

/-- The sequence `jii`. -/
def jii : Seq (ν₃ i j) :=
  ⟨![j, i, i], by rw [Fin.univ_val_map]; exact Multiset.coe_eq_coe.2 (List.Perm.swap i j [i])⟩

variable {i j}

omit [DecidableEq I] in
theorem sadj0_iji : sadj (Multiset.card (ν₃ i j)) 0 • iji i j = jii i j := by
  apply Subtype.ext; funext a; change Fin 3 at a
  fin_cases a <;> rfl

omit [DecidableEq I] in
theorem sadj0_jii : sadj (Multiset.card (ν₃ i j)) 0 • jii i j = iji i j := by
  apply Subtype.ext; funext a; change Fin 3 at a
  fin_cases a <;> rfl

omit [DecidableEq I] in
theorem sadj1_jii : sadj (Multiset.card (ν₃ i j)) 1 • jii i j = jii i j := by
  apply Subtype.ext; funext a; change Fin 3 at a
  fin_cases a <;> rfl

local notation "R" => R1 k Γ (ν₃ i j)

/-- The element `ψ_1 ψ_2 ψ_1 1_{iji}` (paper's indexing). -/
noncomputable def idemL (Γ : SimpleGraph I) [DecidableRel Γ.Adj] (i j : I) : R1 k Γ (ν₃ i j) :=
  ψ 0 * ψ 1 * ψ 0 * e (iji i j)

/-- The element `-ψ_2 ψ_1 ψ_2 1_{iji}` (paper's indexing). -/
noncomputable def idemR (Γ : SimpleGraph I) [DecidableRel Γ.Adj] (i j : I) : R1 k Γ (ν₃ i j) :=
  -(ψ 1 * ψ 0 * ψ 1 * e (iji i j))

theorem ψ0_e_iji : (ψ 0 * e (iji i j) : R) = e (jii i j) * ψ 0 := by
  rw [ψ_mul_e, sadj0_iji]

theorem ψ0_e_jii : (ψ 0 * e (jii i j) : R) = e (iji i j) * ψ 0 := by
  rw [ψ_mul_e, sadj0_jii]

theorem ψ1_e_jii : (ψ 1 * e (jii i j) : R) = e (jii i j) * ψ 1 := by
  rw [ψ_mul_e, sadj1_jii]

/-- `ψ_1 ψ_2 ψ_1 1_{iji} = 1_{iji} ψ_1 ψ_2 ψ_1`. -/
theorem idemL_eq : (idemL Γ i j : R) = e (iji i j) * (ψ 0 * ψ 1 * ψ 0) := by
  rw [idemL]
  simp only [mul_assoc]
  rw [ψ0_e_iji, ← mul_assoc (ψ 1), ψ1_e_jii, mul_assoc (e (jii i j)), ← mul_assoc (ψ 0) (e _),
    ψ0_e_jii]
  simp only [mul_assoc]

theorem e_mul_idemL : (e (iji i j) * idemL Γ i j : R) = idemL Γ i j := by
  rw [idemL_eq, ← mul_assoc, e_mul_self]

theorem idemL_mul_e : (idemL Γ i j * e (iji i j) : R) = idemL Γ i j := by
  rw [idemL, mul_assoc, e_mul_self]

/-- **KL I §2.2, Remark, equation `eq_square`**: for `i · j = -1`, `ψ_1 ψ_2 ψ_1 1_{iji}` is an
idempotent. -/
theorem idemL_mul_self (hadj : Γ.Adj i j) : (idemL Γ i j * idemL Γ i j : R) = idemL Γ i j := by
  -- the relations used
  have hsq : (ψ 0 * ψ 0 * e (jii i j) : R) =
      (x ⟨0, by simp⟩ + x ⟨1, by simp⟩) * e (jii i j) :=
    KL1.ψ_sq_of_adj 0 (by simp) (jii i j) (by exact hadj.symm)
  have hsq1 : (ψ 1 * ψ 1 * e (jii i j) : R) = 0 := KL1.ψ_sq_of_eq 1 (by simp) (jii i j) rfl
  have hnh : (ψ 1 * x ⟨1, by simp⟩ * e (jii i j) - x ⟨2, by simp⟩ * ψ 1 * e (jii i j) : R) =
      e (jii i j) :=
    KL1.ψ_x_sub_of_eq 1 (by simp) (jii i j) rfl
  have hx0 : (x ⟨0, by simp⟩ * ψ 1 : R) = ψ 1 * x ⟨0, by simp⟩ :=
    x_mul_ψ _ 1 (by simp) (by simp)
  have h1F : (ψ 1 * e (jii i j) : R) = e (jii i j) * ψ 1 := ψ1_e_jii
  have h0E : (ψ 0 * e (iji i j) : R) = e (jii i j) * ψ 0 := ψ0_e_iji
  -- first step: `a² = ψ_1 ψ_2 ψ_1 ψ_1 ψ_2 ψ_1 1_{iji}`
  have hEa := e_mul_idemL (Γ := Γ) (k := k) (i := i) (j := j)
  have s1 : (idemL Γ i j * idemL Γ i j : R) =
      ψ 0 * ψ 1 * (ψ 0 * ψ 0 * (ψ 1 * (ψ 0 * e (iji i j)))) := by
    simp only [idemL, mul_assoc] at hEa ⊢
    rw [hEa]
  -- second step: use `ψ_1² 1_{jii} = (x_1 + x_2) 1_{jii}`
  have s2 : (ψ 0 * ψ 0 * (ψ 1 * (ψ 0 * e (iji i j))) : R) =
      (x ⟨0, by simp⟩ + x ⟨1, by simp⟩) * (ψ 1 * e (jii i j)) * ψ 0 := by
    rw [h0E, ← mul_assoc (ψ 1), h1F, mul_assoc (e _), ← mul_assoc (ψ 0 * ψ 0), hsq]
    simp only [mul_assoc]
  -- third step: the two dots
  have t1 : (ψ 1 * x ⟨0, by simp⟩ * (ψ 1 * e (jii i j)) : R) = 0 := by
    rw [← hx0, mul_assoc, ← mul_assoc (ψ 1) (ψ 1), hsq1, mul_zero]
  have t2 : (ψ 1 * x ⟨1, by simp⟩ * (ψ 1 * e (jii i j)) : R) = ψ 1 * e (jii i j) := by
    have e1 : (ψ 1 * x ⟨1, by simp⟩ * e (jii i j) : R) =
        x ⟨2, by simp⟩ * ψ 1 * e (jii i j) + e (jii i j) :=
      eq_add_of_sub_eq' hnh
    calc (ψ 1 * x ⟨1, by simp⟩ * (ψ 1 * e (jii i j)) : R)
        = ψ 1 * x ⟨1, by simp⟩ * e (jii i j) * ψ 1 := by rw [h1F, ← mul_assoc]
      _ = (x ⟨2, by simp⟩ * ψ 1 * e (jii i j) + e (jii i j)) * ψ 1 := by rw [e1]
      _ = x ⟨2, by simp⟩ * (ψ 1 * (e (jii i j) * ψ 1)) + e (jii i j) * ψ 1 := by
        simp only [add_mul, mul_assoc]
      _ = x ⟨2, by simp⟩ * (ψ 1 * ψ 1 * e (jii i j)) + e (jii i j) * ψ 1 := by
        rw [← h1F, mul_assoc]
      _ = ψ 1 * e (jii i j) := by rw [hsq1, mul_zero, zero_add, h1F]
  rw [s1, s2]
  calc (ψ 0 * ψ 1 * ((x ⟨0, by simp⟩ + x ⟨1, by simp⟩) * (ψ 1 * e (jii i j)) * ψ 0) : R)
      = ψ 0 * (ψ 1 * x ⟨0, by simp⟩ * (ψ 1 * e (jii i j)) +
          ψ 1 * x ⟨1, by simp⟩ * (ψ 1 * e (jii i j))) * ψ 0 := by
        simp only [mul_add, add_mul, mul_assoc]
    _ = ψ 0 * (e (jii i j) * ψ 1) * ψ 0 := by rw [t1, t2, zero_add, h1F]
    _ = ψ 0 * ψ 1 * (e (jii i j) * ψ 0) := by rw [← h1F]; simp only [mul_assoc]
    _ = idemL Γ i j := by rw [← h0E, idemL]; simp only [mul_assoc]

/-- **KL I (2.8)**: `ψ_1 ψ_2 ψ_1 1_{iji} + (-ψ_2 ψ_1 ψ_2 1_{iji}) = 1_{iji}`. -/
theorem idemL_add_idemR (hadj : Γ.Adj i j) :
    (idemL Γ i j + idemR Γ i j : R) = e (iji i j) := by
  rw [idemL, idemR, ← sub_eq_add_neg]
  exact KL1.braid_hard 0 (by simp) (iji i j) rfl (by exact hadj)

theorem idemR_eq (hadj : Γ.Adj i j) : (idemR Γ i j : R) = e (iji i j) - idemL Γ i j := by
  rw [← idemL_add_idemR hadj]; abel

/-- The Remark of KL I §2.2: `-ψ_2 ψ_1 ψ_2 1_{iji}` is an idempotent. -/
theorem idemR_mul_self (hadj : Γ.Adj i j) : (idemR Γ i j * idemR Γ i j : R) = idemR Γ i j := by
  rw [idemR_eq hadj, sub_mul, mul_sub, mul_sub, e_mul_self, e_mul_idemL, idemL_mul_e,
    idemL_mul_self hadj]
  abel

/-- The Remark of KL I §2.2: the two idempotents are orthogonal. -/
theorem idemL_mul_idemR (hadj : Γ.Adj i j) : (idemL Γ i j * idemR Γ i j : R) = 0 := by
  rw [idemR_eq hadj, mul_sub, idemL_mul_e, idemL_mul_self hadj, sub_self]

/-- The Remark of KL I §2.2: the two idempotents are orthogonal. -/
theorem idemR_mul_idemL (hadj : Γ.Adj i j) : (idemR Γ i j * idemL Γ i j : R) = 0 := by
  rw [idemR_eq hadj, sub_mul, e_mul_idemL, idemL_mul_self hadj, sub_self]

end Remark

end Categorification.KLR.KL1

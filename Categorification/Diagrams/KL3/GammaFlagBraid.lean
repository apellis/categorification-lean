/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.GammaFlagSigned
import Categorification.Flag.GammaThree

/-!
# `Γ_N` respects the braid relations (4.13), (4.14) of `U→(sl_n)` with the polynomials `Q^τ`

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, Definition 4.1
(TeX label `def_Ucatq-sln`, eqs. (4.13), (4.14)) and §6.2, Proposition 6.8 (eqs. (6.20), (6.21)).

`Categorification.Flag.braidQ_three` states the deformed braid relation with the polynomial
`Qf c d = F_{dc}(u, v) F_{cd}(v, u)` read off from `Γ_N` of the crossings (KL III (6.8)). Here we
identify it with the signed polynomial `Q^τ_{cd}` of Definition 4.1 (`qSigned`):

* `qf_eq_qSigned` : `Qf c d = Q^τ_{cd}` for `c ≠ d`;
* `braidQ_signed` : `Γ_N(ψ₀ψ₁ψ₀) − Γ_N(ψ₁ψ₀ψ₁) = Q̄^τ_{cd}(ξ₀, ξ₁, ξ₂)` on `E_c E_d E_c 1` for
  `c ≠ d`, which is the relation `KLR.Diagram.Rel.braidQ` of `Signed.presSigned` (placed on upward
  strands) evaluated in `Flag_N` on three-strand paths, with arbitrary suffix.

The undeformed braid relation `braid` of the presentation is `Categorification.Flag.braid_three`.
-/

noncomputable section

namespace Categorification.KL3.Diagram.Signed

open Categorification.Flag MvPolynomial

universe u

variable {K : Type u} [Field K] {m : ℕ}

/-- **The double-crossing polynomial of `Γ_N` is the signed `Q^τ`**: for `c ≠ d`,
`F_{dc}(u, v) F_{cd}(v, u) = Q^τ_{cd}(u, v)` (KL III (4.11) and (6.8)). -/
theorem qf_eq_qSigned {i j : Fin m} (hij : i ≠ j) : Qf K i j = qSigned K m i j := by
  by_cases hadj : j.castSucc = i.succ
  · -- `j = i + 1`
    have hadj' : ¬ i.castSucc = j.succ := by
      rw [castSucc_eq_succ_iff] at hadj ⊢; omega
    have hdot : (slCartan m).dot i j = -1 := by
      rw [slCartan_dot, if_neg hij, if_pos (Or.inl (castSucc_eq_succ_iff.1 hadj).symm)]
    have hij' : (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) = -1 := by
      have := castSucc_eq_succ_iff.1 hadj; omega
    rw [Qf, Fc, Fc, if_pos hadj, if_neg hadj', map_one, mul_one, qSigned_of_adj hdot, hij',
      neg_one_zsmul, neg_sub]
  · by_cases hadj' : i.castSucc = j.succ
    · -- `i = j + 1`
      have hdot : (slCartan m).dot i j = -1 := by
        rw [slCartan_dot, if_neg hij, if_pos (Or.inr (castSucc_eq_succ_iff.1 hadj').symm)]
      have hij' : (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) = 1 := by
        have := castSucc_eq_succ_iff.1 hadj'; omega
      rw [Qf, Fc, Fc, if_neg hadj, if_pos hadj', one_mul, qSigned_of_adj hdot, hij', one_zsmul,
        map_sub, rename_X, rename_X]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    · -- `i · j = 0`
      have hdot : (slCartan m).dot i j = 0 := by
        rw [slCartan_dot, if_neg hij, if_neg]
        rw [castSucc_eq_succ_iff] at hadj hadj'
        omega
      rw [Qf, Fc, Fc, if_neg hadj, if_neg hadj', map_one, mul_one, qSigned_of_dot_eq_zero hdot]

/-- **KL III (4.14) with the signed polynomials `Q^τ` in `Flag_N`** (Proposition 6.8, (6.21)):
for `c ≠ d`, on `E_c E_d E_c 1` followed by any suffix `X`,
`Γ_N(ψ₀ ψ₁ ψ₀) − Γ_N(ψ₁ ψ₀ ψ₁)` is multiplication by
`Q̄^τ_{cd}(ξ₀, ξ₁, ξ₂) = (Q^τ_{cd}(ξ₀, ξ₁) − Q^τ_{cd}(ξ₂, ξ₁)) / (ξ₀ − ξ₂)`. -/
theorem braidQ_signed (c d : Fin m) (hcd : c ≠ d) {s r₁ r₂ r₃ a₁ b₂ : Comp m} {E : Type u}
    [CommRing E] (h₁ : StepR (true, c) r₁ s) (h₂ : StepR (true, d) r₂ r₁)
    (h₃ : StepR (true, c) r₃ r₂) (ha₁ : StepR (true, d) a₁ s) (ha₂ : StepR (true, c) r₂ a₁)
    (hb₂ : StepR (true, c) b₂ r₁) (hb₃ : StepR (true, d) r₃ b₂) (X : BRing (H K r₃) E) :
    braidL K c d c h₁ h₂ h₃ ha₁ ha₂ ha₂ h₁ h₂ h₃ X -
        braidR K c d c h₁ h₂ h₃ hb₂ hb₃ hb₂ h₁ h₂ h₃ X =
      BHom.mulB (ev3 K _ _ _ X (eXi K c r₁ h₁.2) (eXi K d r₂ h₂.2) (eXi K c r₃ h₃.2)
        (KLR.qbar (qSigned K m c d))) := by
  rw [← qf_eq_qSigned hcd]
  exact braidQ_three c d h₁ h₂ ha₁ hcd h₃ ha₂ hb₂ hb₃ X

end Categorification.KL3.Diagram.Signed

end

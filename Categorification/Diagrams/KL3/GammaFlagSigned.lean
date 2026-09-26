/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.SignedSln
import Categorification.Flag.GammaWhisker

/-!
# `Γ_N` respects the signed relation (4.11) of `U→(sl_n)` with the polynomials `Q^τ`

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, Definition 4.1
(TeX label `def_Ucatq-sln`, eq. (4.11)) and §6.1.2, Definition 6.2 (eq. (6.8), TeX label
`eq_gamma_dcross`), Proposition 6.8 (eq. (6.19)).

For distinct colours `i ≠ j` we assemble KL III's `Γ_N` of the upward crossing
`E_i E_j 1 → E_j E_i 1` on the path model of `Categorification.Flag.GammaWord` from the three
cases of (6.8):

* `i · j = 0`: the swap (`Categorification.Flag.crossFarP`);
* `j = i + 1` (`i → j` in KL III's orientation `1 → 2 → ⋯`): the restriction from the non-flag
  product (`crossAdjNF`);
* `i = j + 1` (`j → i`): minus the push-forward to the non-flag product (`crossAdjFN`),

and prove that the double crossing is multiplication by the signed polynomial
`Q^τ_{ij}(x_left, x_right)` of Definition 4.1 (`Categorification.KL3.Diagram.Signed.qSigned`):

* `gammaCross_sq` : `Γ(ψ_{ji}) ∘ Γ(ψ_{ij}) = Q^τ_{ij}(ξ_left, ξ_right)`, i.e. `1` if `i · j = 0`
  and `(i - j)(ξ_left - ξ_right)` if `i · j = -1`.

This is exactly the relation `KLR.Diagram.Rel.sqNe i j` of the presentation `Signed.presSigned`
(placed on upward strands, `relationQ`), evaluated in `Flag_N` on two-strand paths. Whiskered
versions at every position follow from `Categorification.Flag.twoAt_comp`.
-/

noncomputable section

namespace Categorification.KL3.Diagram.Signed

open Categorification.Flag MvPolynomial

universe u

variable {K : Type u} [Field K] {m : ℕ}

theorem castSucc_eq_succ_iff {i j : Fin m} : j.castSucc = i.succ ↔ (j : ℕ) = i + 1 := by
  rw [Fin.ext_iff, Fin.coe_castSucc, Fin.val_succ]

variable (K) in
/-- **`Γ_N` of the upward crossing `E_i E_j 1 → E_j E_i 1`** for `i ≠ j` (KL III (6.8)), on the
path model. -/
def gammaCross (i j : Fin m) (hij : i ≠ j) {t r₁ r₂ r₁' : Comp m} (h₁ : StepR (true, i) r₁ t)
    (h₂ : StepR (true, j) r₂ r₁) (h₁' : StepR (true, j) r₁' t) (h₂' : StepR (true, i) r₂ r₁') :
    BHom (TwoP (K := K) h₁ h₂) (TwoP (K := K) h₁' h₂') :=
  if hadj : j.castSucc = i.succ then crossAdjNF K i j hadj h₁ h₂ h₁' h₂'
  else if hadj' : i.castSucc = j.succ then crossAdjFN K j i hadj' h₁' h₂' h₁ h₂
  else crossFarP K i j hij (Ne.symm hadj) (Ne.symm hadj') h₁ h₂ h₁' h₂'

/-- The scalars `K → Γ(E_i E_j 1)`. -/
def scal {i j : Fin m} {t r₁ r₂ : Comp m} (h₁ : StepR (true, i) r₁ t)
    (h₂ : StepR (true, j) r₂ r₁) : K →+* (TwoP (K := K) h₁ h₂).T :=
  (TwoP (K := K) h₁ h₂).left.comp (algebraMap K (H K t))

/-- **KL III (4.11) with the signed polynomials `Q^τ` in `Flag_N`**: for `i ≠ j` the double
crossing `Γ(ψ_{ji}) ∘ Γ(ψ_{ij})` on `E_i E_j 1` is multiplication by
`Q^τ_{ij}(ξ_left, ξ_right)` (`qSigned`). -/
theorem gammaCross_sq (i j : Fin m) (hij : i ≠ j) {t r₁ r₂ r₁' : Comp m}
    (h₁ : StepR (true, i) r₁ t) (h₂ : StepR (true, j) r₂ r₁) (h₁' : StepR (true, j) r₁' t)
    (h₂' : StepR (true, i) r₂ r₁') :
    (gammaCross K j i hij.symm h₁' h₂' h₁ h₂).comp (gammaCross K i j hij h₁ h₂ h₁' h₂') =
      BHom.mulB (eval₂ (scal h₁ h₂) ![BRing.tmul _ _ (eXi K i r₁ h₁.2) 1,
        BRing.tmul _ _ 1 (eXi K j r₂ h₂.2)] (qSigned K m i j)) := by
  by_cases hadj : j.castSucc = i.succ
  · -- `j = i + 1`
    have hadj' : ¬ i.castSucc = j.succ := by
      rw [castSucc_eq_succ_iff] at hadj ⊢; omega
    have hdot : (slCartan m).dot i j = -1 := by
      rw [slCartan_dot, if_neg hij, if_pos (Or.inl (castSucc_eq_succ_iff.1 hadj).symm)]
    have hij' : (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) = -1 := by
      have := castSucc_eq_succ_iff.1 hadj; omega
    unfold gammaCross
    rw [dif_pos hadj, dif_neg hadj', dif_pos hadj, crossAdj_sq_NF, qSigned_of_adj hdot, hij',
      neg_one_zsmul, eval₂_neg, eval₂_sub, eval₂_X, eval₂_X]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, neg_sub]
  · by_cases hadj' : i.castSucc = j.succ
    · -- `i = j + 1`
      have hdot : (slCartan m).dot i j = -1 := by
        rw [slCartan_dot, if_neg hij, if_pos (Or.inr (castSucc_eq_succ_iff.1 hadj').symm)]
      have hij' : (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) = 1 := by
        have := castSucc_eq_succ_iff.1 hadj'; omega
      unfold gammaCross
      rw [dif_neg hadj, dif_pos hadj', dif_pos hadj', crossAdj_sq_FN, qSigned_of_adj hdot, hij',
        one_zsmul, eval₂_sub, eval₂_X, eval₂_X]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    · -- `i · j = 0`
      have hdot : (slCartan m).dot i j = 0 := by
        rw [slCartan_dot, if_neg hij, if_neg]
        rw [castSucc_eq_succ_iff] at hadj hadj'
        omega
      have hadj₂ : ¬ i.castSucc = j.succ := hadj'
      have hadj₃ : ¬ j.castSucc = i.succ := hadj
      unfold gammaCross
      rw [dif_neg hadj, dif_neg hadj', dif_neg hadj₂, dif_neg hadj₃, crossFarP_sq,
        qSigned_of_dot_eq_zero hdot, eval₂_one, BHom.mulB_one]

end Categorification.KL3.Diagram.Signed

end

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.GammaFlagBraid
import Categorification.Diagrams.KL3.Relations
import Categorification.Flag.GammaCurl

/-!
# `Γ_N` of real and fake bubbles, and the curl relations with KL III's indexing

KL III, arXiv:0807.3250v1, Definition 3.1 (eq. `eq_infinite_Grass`: the fake bubbles; item iv):
the curl relations) and Proposition 6.3.

In the 2-category `U` the fake bubbles are *defined* by the infinite Grassmannian recursion
(`Categorification.KL3.Diagram.grassInv`, `cwL`, `ccwL`). Here we evaluate that recursion under
`Γ_N`: with `n = λ_i - λ_{i+1}` for a composition `λ` (the region) and colour `i`,

* `cwRealH λ i α`, `ccwRealH λ i α` : `Γ_N` of the real clockwise / counterclockwise bubble with
  `α` dots, as elements of `H_λ` — `Ψ_{α+1-n}` resp. `Φ_{α+1+n}` (`0` in negative degree), where
  `Ψ_f = (-1)^f ∑_{u+v=f} x_{i+1,u} x̄_{i,v}` and `Φ_g = (-1)^g ∑_{u+v=g} x_{i,u} x̄_{i+1,v}`;
  `cwRealH_eq_capEFP`, `ccwRealH_eq_capFEP` : these are the path-model composites (cup, dots,
  cap) whenever the bubble passes through a nonzero 1-morphism;
* `cwLH`, `ccwLH` : `Γ_N` of the labelled bubbles `cwL`, `ccwL` of Definition 3.1 (real for labels
  `≥ 0`, fake otherwise), obtained by applying `Γ_N` to the definition;
* **fake bubbles** (`cwLH_eq`, `ccwLH_eq`): for every label `m ∈ ℤ`,
  `Γ_N(cwL m) = Ψ_{m+1-n}` and `Γ_N(ccwL m) = Φ_{m+1+n}` (`0` in negative degree): the fake bubbles
  are sent to the corresponding coefficients of the inverse series, by the Grassmannian identity
  `Φ Ψ = 1` in `H_λ` (`Categorification.Flag.grassmannianH`);
* **the curl relations** (`curlRW_eq_curlRHS`, `curlLW_eq_curlLHS`): `Γ_N(curlR)` and
  `Γ_N(curlL)` are `Γ_N` of the right-hand sides `curlRHS`, `curlLHS` of Definition 3.1, term by
  term with KL III's indices.
-/

noncomputable section

namespace Categorification.KL3.Diagram.Signed

open Categorification.Flag MvPolynomial

universe u

variable {K : Type u} [Field K] {m : ℕ}

/-! ### The Grassmannian recursion -/

section Grass

variable {A : Type*} [CommRing A]

theorem grassInv_congr (c c' : ℕ → A) (h : ∀ a, c (a + 1) = c' (a + 1)) :
    ∀ k, grassInv c k = grassInv c' k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | k
    · rw [grassInv_zero, grassInv_zero]
    · rw [grassInv_succ, grassInv_succ]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [h, ih _ (by omega)]

/-- **The Grassmannian recursion computes the inverse series**: if `c₀ = 1` and
`∑_{a+b=N} c_a ψ_b = δ_{N,0}`, then `grassInv c = ψ`. -/
theorem grassInv_eq (c ψ : ℕ → A) (hc : c 0 = 1)
    (h : ∀ N, ∑ p ∈ Finset.antidiagonal N, c p.1 * ψ p.2 = if N = 0 then 1 else 0) :
    ∀ k, grassInv c k = ψ k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | k
    · have h0 := h 0
      simp only [Finset.antidiagonal_zero, Finset.sum_singleton, hc, one_mul] at h0
      rw [grassInv_zero, h0, if_pos trivial]
    · have hk := h (k + 1)
      rw [Finset.Nat.sum_antidiagonal_succ, hc, one_mul, if_neg (Nat.succ_ne_zero k)] at hk
      dsimp only at hk
      rw [grassInv_succ, eq_neg_of_add_eq_zero_left hk, neg_inj,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← Fin.sum_univ_eq_sum_range
          (fun a => c (a + 1) * ψ (k - a))]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [ih _ (by omega)]

end Grass

/-! ### Real and fake bubbles in `H_λ` -/

section Bubbles

variable (lam : Comp m) (i : Fin m)

/-- `n = ⟨i, λ⟩ = λ_i - λ_{i+1}`. -/
abbrev nH : ℤ := (lam i.castSucc : ℤ) - lam i.succ

/-- `Ψ_f = (-1)^f ∑_{u+v=f} x_{i+1,u} x̄_{i,v}`: the clockwise bubble of degree `2f`. -/
abbrev PsiH (f : ℕ) : H K lam := bubbleSeq (x K lam i.succ) (xbar K lam i.castSucc) f

/-- `Φ_g = (-1)^g ∑_{u+v=g} x_{i,u} x̄_{i+1,v}`: the counterclockwise bubble of degree `2g`. -/
abbrev PhiH (g : ℕ) : H K lam := bubbleSeq (x K lam i.castSucc) (xbar K lam i.succ) g

/-- `Γ_N` of the real clockwise bubble with `α` dots in the region `λ` (KL III Proposition 6.3;
`bubbleEFH_eq`). -/
def cwRealH (α : ℕ) : H K lam :=
  if lam i.castSucc ≤ α + lam i.succ + 1 then PsiH lam i (α + lam i.succ + 1 - lam i.castSucc)
  else 0

/-- `Γ_N` of the real counterclockwise bubble with `α` dots in the region `λ` (`bubbleFEH_eq`). -/
def ccwRealH (α : ℕ) : H K lam :=
  if lam i.succ ≤ α + lam i.castSucc + 1 then PhiH lam i (α + lam i.castSucc + 1 - lam i.succ)
  else 0

/-- `Γ_N` of `cwR` (the real clockwise bubble with label `m`, `0` for `m < 0`). -/
def cwRH (mm : ℤ) : H K lam := if 0 ≤ mm then cwRealH lam i mm.toNat else 0

/-- `Γ_N` of `ccwR`. -/
def ccwRH (mm : ℤ) : H K lam := if 0 ≤ mm then ccwRealH lam i mm.toNat else 0

/-- **`Γ_N` of the labelled clockwise bubble `cwL`** of Definition 3.1 (real or fake), obtained
by applying `Γ_N` to its definition (`Categorification.KL3.Diagram.cwL`). -/
def cwLH (mm : ℤ) : H K lam :=
  if 0 ≤ mm then cwRealH lam i mm.toNat
  else if 0 ≤ mm + 1 - nH lam i then
    grassInv (fun a => ccwRH lam i (-nH lam i - 1 + a)) (mm + 1 - nH lam i).toNat
  else 0

/-- **`Γ_N` of the labelled counterclockwise bubble `ccwL`** of Definition 3.1. -/
def ccwLH (mm : ℤ) : H K lam :=
  if 0 ≤ mm then ccwRealH lam i mm.toNat
  else if 0 ≤ mm + 1 + nH lam i then
    grassInv (fun b => cwRH lam i (nH lam i - 1 + b)) (mm + 1 + nH lam i).toNat
  else 0

theorem PhiH_zero : PhiH (K := K) lam i 0 = 1 := by
  simp [PhiH, bubbleSeq, x_zero, xbar_zero']

theorem PsiH_zero : PsiH (K := K) lam i 0 = 1 := by
  simp [PsiH, bubbleSeq, x_zero, xbar_zero']

/-- **Fake clockwise bubbles**: for every label `m`, `Γ_N(cwL m) = Ψ_{m+1-n}` (and `0` if
`m + 1 - n < 0`). -/
theorem cwLH_eq (mm : ℤ) :
    cwLH (K := K) lam i mm = if 0 ≤ mm + 1 - nH lam i then PsiH lam i (mm + 1 - nH lam i).toNat
      else 0 := by
  have hn : nH lam i = (lam i.castSucc : ℤ) - lam i.succ := rfl
  unfold cwLH
  by_cases h0 : 0 ≤ mm
  · rw [if_pos h0, cwRealH]
    by_cases h1 : lam i.castSucc ≤ mm.toNat + lam i.succ + 1
    · rw [if_pos h1, if_pos (by omega)]
      congr 1
      omega
    · rw [if_neg h1, if_neg (by omega)]
  · rw [if_neg h0]
    by_cases h1 : 0 ≤ mm + 1 - nH lam i
    · rw [if_pos h1, if_pos h1]
      rw [grassInv_congr _ (PhiH lam i) (fun a => by
        rw [ccwRH, if_pos (by omega), ccwRealH, if_pos (by omega)]
        congr 1
        omega)]
      exact grassInv_eq _ _ (PhiH_zero lam i)
        (grassmannianH (K := K) lam i.castSucc i.succ) _
    · rw [if_neg h1, if_neg h1]

/-- **Fake counterclockwise bubbles**: for every label `m`, `Γ_N(ccwL m) = Φ_{m+1+n}` (and `0` if
`m + 1 + n < 0`). -/
theorem ccwLH_eq (mm : ℤ) :
    ccwLH (K := K) lam i mm = if 0 ≤ mm + 1 + nH lam i then PhiH lam i (mm + 1 + nH lam i).toNat
      else 0 := by
  have hn : nH lam i = (lam i.castSucc : ℤ) - lam i.succ := rfl
  unfold ccwLH
  by_cases h0 : 0 ≤ mm
  · rw [if_pos h0, ccwRealH]
    by_cases h1 : lam i.succ ≤ mm.toNat + lam i.castSucc + 1
    · rw [if_pos h1, if_pos (by omega)]
      congr 1
      omega
    · rw [if_neg h1, if_neg (by omega)]
  · rw [if_neg h0]
    by_cases h1 : 0 ≤ mm + 1 + nH lam i
    · rw [if_pos h1, if_pos h1]
      rw [grassInv_congr _ (PsiH lam i) (fun a => by
        rw [cwRH, if_pos (by omega), cwRealH, if_pos (by omega)]
        congr 1
        omega)]
      exact grassInv_eq _ _ (PsiH_zero lam i)
        (grassmannianH (K := K) lam i.succ i.castSucc) _
    · rw [if_neg h1, if_neg h1]

end Bubbles

/-! ### The curl relations with KL III's indexing -/

section Curls

theorem BHom.mulB_zero' {A B : Type u} [CommRing A] [CommRing B] (M : BRing A B) :
    BHom.mulB (0 : M.T) = 0 := by
  ext z; rw [BHom.mulB_apply, zero_mul, BHom.zero_apply]

variable (i : Fin m)

/-- **`Γ_N` respects the right curl relation** (KL III Definition 3.1 iv), `curlR`, with the
right-hand side `curlRHS`): on `E_i ⊗ Y` with region `r` to the right of `E_i` and
`n = ⟨i, λ⟩ = r_i - r_{i+1}`,
`Γ_N(curlR) = -∑_{f=0}^{-n} (E_i with -n - f dots) · Γ_N(cwL (n - 1 + f))`, the bubbles (real or
fake) acting in the region `r`. -/
theorem curlRW_eq_curlRHS {q r s : Comp m} (h : StepR (true, i) r s) (hq : StepR (true, i) q r)
    {E : Type u} [CommRing E] (Y : BRing (H K r) E) :
    curlRW K i h hq Y = BHom.mulB (-∑ f ∈ Finset.range (-nH r i + 1).toNat,
      BRing.tmul (stepB K (true, i) r s h) Y (eXi K i r h.2 ^ (-nH r i - f).toNat)
        (Y.left (cwLH r i (nH r i - 1 + f)))) := by
  have hn : nH r i = (r i.castSucc : ℤ) - r i.succ := rfl
  rw [curlRW_eq]
  split_ifs with hc
  · rw [show (-nH r i + 1).toNat = r i.succ - r i.castSucc + 1 by omega]
    congr 2
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [cwLH_eq, if_pos (by omega), show (-nH r i - f).toNat = r i.succ - r i.castSucc - f by omega,
      show (nH r i - 1 + f + 1 - nH r i).toNat = f by omega]
  · rw [show (-nH r i + 1).toNat = 0 by omega, Finset.sum_range_zero, neg_zero, BHom.mulB_zero']

/-- **`Γ_N` respects the left curl relation** (KL III Definition 3.1 iv), `curlL`, with the
right-hand side `curlLHS`): on `E_i ⊗ Y` with region `s` to the left of `E_i` and
`n = ⟨i, λ⟩ = s_i - s_{i+1}`,
`Γ_N(curlL) = ∑_{g=0}^{n} Γ_N(ccwL (-n - 1 + g)) · (E_i with n - g dots)`, the bubbles (real or
fake) acting in the region `s`. -/
theorem curlLW_eq_curlLHS {r s s' : Comp m} (h : StepR (true, i) r s) (hs : StepR (true, i) s s')
    {E : Type u} [CommRing E] (Y : BRing (H K r) E) :
    curlLW K i h hs Y = BHom.mulB (∑ g ∈ Finset.range (nH s i + 1).toNat,
      BRing.tmul (stepB K (true, i) r s h) Y
        ((stepB K (true, i) r s h).left (ccwLH s i (-nH s i - 1 + g)) *
          xiStep K (true, i) r s h ^ (nH s i - g).toNat) 1) := by
  have hn : nH s i = (s i.castSucc : ℤ) - s i.succ := rfl
  rw [curlLW_eq]
  split_ifs with hc
  · rw [show (nH s i + 1).toNat = s i.castSucc - s i.succ + 1 by omega]
    congr 1
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [ccwLH_eq, if_pos (by omega), show (nH s i - g).toNat = s i.castSucc - s i.succ - g by omega,
      show (-nH s i - 1 + g + 1 + nH s i).toNat = g by omega]
  · rw [show (nH s i + 1).toNat = 0 by omega, Finset.sum_range_zero, BHom.mulB_zero']

end Curls

/-! ### Real bubbles are the path-model composites -/

section RealBubbles

attribute [local instance] rightAlgebra midAlgebra

variable (i : Fin m) {s s' : Comp m} (hE : StepR (true, i) s s') (hF : StepR (false, i) s' s)

theorem cupFE_slide_pow (α : ℕ) :
    BRing.tmul (Fst (K := K) i hF) (Est (K := K) i hE) 1 (eXi K i s hE.2 ^ α) * cupFE K i hE hF =
      BRing.tmul (Fst (K := K) i hF) (Est (K := K) i hE) (eXi K i s hE.2 ^ α) 1 *
        cupFE K i hE hF := by
  induction α with
  | zero => simp only [pow_zero]
  | succ α ih =>
    have e1 : BRing.tmul (Fst (K := K) i hF) (Est (K := K) i hE) 1 (eXi K i s hE.2 ^ (α + 1)) =
        BRing.tmul _ _ 1 (eXi K i s hE.2) * BRing.tmul _ _ 1 (eXi K i s hE.2 ^ α) := by
      rw [BRing.tmul_mul_tmul, one_mul, pow_succ']
    have e2 : BRing.tmul (Fst (K := K) i hF) (Est (K := K) i hE) (eXi K i s hE.2 ^ (α + 1)) 1 =
        BRing.tmul _ _ (eXi K i s hE.2 ^ α) 1 * BRing.tmul _ _ (eXi K i s hE.2) 1 := by
      rw [BRing.tmul_mul_tmul, one_mul, pow_succ]
    rw [e1, e2, mul_assoc, ih, mul_left_comm, ← cupFE_slide, mul_assoc]

theorem cupEF_slide_pow (α : ℕ) :
    BRing.tmul (Est (K := K) i hE) (Fst (K := K) i hF) 1 (eXi K i s hE.2 ^ α) * cupEF K i hE hF =
      BRing.tmul (Est (K := K) i hE) (Fst (K := K) i hF) (eXi K i s hE.2 ^ α) 1 *
        cupEF K i hE hF := by
  induction α with
  | zero => simp only [pow_zero]
  | succ α ih =>
    have e1 : BRing.tmul (Est (K := K) i hE) (Fst (K := K) i hF) 1 (eXi K i s hE.2 ^ (α + 1)) =
        BRing.tmul _ _ 1 (eXi K i s hE.2) * BRing.tmul _ _ 1 (eXi K i s hE.2 ^ α) := by
      rw [BRing.tmul_mul_tmul, one_mul, pow_succ']
    have e2 : BRing.tmul (Est (K := K) i hE) (Fst (K := K) i hF) (eXi K i s hE.2 ^ (α + 1)) 1 =
        BRing.tmul _ _ (eXi K i s hE.2 ^ α) 1 * BRing.tmul _ _ (eXi K i s hE.2) 1 := by
      rw [BRing.tmul_mul_tmul, one_mul, pow_succ]
    rw [e1, e2, mul_assoc, ih, mul_left_comm, ← cupEF_slide, mul_assoc]

/-- **The counterclockwise bubble in the path model** (cup `1 → F_i E_i`, `α` dots on `E_i`, cap
`F_i E_i → 1`; `Categorification.KL3.Diagram.ccwReal`) is `ccwRealH s i α` in `H_s`. -/
theorem capFEP_bubble_eq (α : ℕ) :
    capFEP K i hE hF (BRing.tmul _ _ 1 (eXi K i s hE.2 ^ α) * cupFE K i hE hF) =
      ccwRealH s i α := by
  rw [cupFE_slide_pow]
  have e : capFEP K i hE hF (BRing.tmul _ _ (eXi K i s hE.2 ^ α) 1 * cupFE K i hE hF) =
      bubbleFEH i s hE.2 α := by
    rw [capFEP, map_mul, feEquiv_tmul, feEquiv_cupFE]
    rfl
  rw [e, bubbleFEH_eq, ccwRealH]

/-- **The clockwise bubble in the path model** (cup `1 → E_i F_i`, `α` dots on `F_i`, cap
`E_i F_i → 1`; `Categorification.KL3.Diagram.cwReal`) is `cwRealH s' i α` in `H_{s'}`. -/
theorem capEFP_bubble_eq (α : ℕ) :
    capEFP K i hE hF (BRing.tmul _ _ 1 (eXi K i s hE.2 ^ α) * cupEF K i hE hF) =
      cwRealH s' i α := by
  rw [cupEF_slide_pow]
  have e : capEFP K i hE hF (BRing.tmul _ _ (eXi K i s hE.2 ^ α) 1 * cupEF K i hE hF) =
      hCast K hE.1 (bubbleEFH i s hE.2 α) := by
    rw [capEFP, map_mul, efEquiv_tmul, efEquiv_cupEF]
    rfl
  rw [e, bubbleEFH_eq, cwRealH]
  have key : ∀ (t : Comp m) (e : raise i s = t), hCast K e
      (if raise i s i.castSucc ≤ α + raise i s i.succ + 1 then
        bubbleSeq (x K (raise i s) i.succ) (xbar K (raise i s) i.castSucc)
          (α + raise i s i.succ + 1 - raise i s i.castSucc) else 0) =
      if t i.castSucc ≤ α + t i.succ + 1 then PsiH t i (α + t i.succ + 1 - t i.castSucc) else 0 := by
    intro t e; subst e; rfl
  exact key s' hE.1

end RealBubbles

end Categorification.KL3.Diagram.Signed

end

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.GammaCups
import Categorification.Flag.GammaDown

/-!
# Cups and caps on the path model: dots, swapped cup elements and values of caps

KL III, arXiv:0807.3250v1, §6.1.1 (Definition 6.1, eqs. (6.2)–(6.5)) and Lemma 5.4.
Complements to `Categorification.Flag.GammaCups` used to evaluate composites of cups, caps and
crossings (the sideways crossings, rotations and curls of Definition 3.1).

For a colour `c`, `s' = +_c s`, the strands `E = Est c hE` (from `s` to `s'`) and
`F = Fst c hF` (from `s'` to `s`):

* `xsFE_eq`, `xsEF_eq` : the coefficients `x(s)_{c,β}` of the cup `1_s → F E` and
  `x(s')_{c+1,β}` of the cup `1_{s'} → E F` are the images of `x_{c,β} ∈ H_s` resp.
  `x_{c+1,β} ∈ H_{s'}` under the outer actions;
* `cupFE_swap`, `cupFEW_apply'` : Lemma 5.4 (i) on the path model: the cup element of `F E 1_s`
  is `∑_g (-1)^{d-g} x(s)_{c,d-g} ⊗ ξ^g` (the polynomial part on `E`, the coefficients acting from
  the left);
* `cupFE_slide`, `cupEF_slide` : Lemma 5.4 (iii), (iv): dots slide through both cups;
* `capEFP_mul_left`, `capFEP_mul_left` : dots slide across both caps;
* `capEFP_xi_pow`, `capFEP_xi_pow` : the caps on `ξ^e ⊗ 1` resp. `1 ⊗ ξ^e` below the top
  degree: `0` below, `1` in the lowest nonzero degree (KL III (6.4), (6.5));
* block sizes: `dFE_eq` (`d = s_c`), `dEF_eq` (`s_{c+1} - 1`).
-/

noncomputable section

open scoped TensorProduct

namespace Categorification.Flag

universe u

variable {K : Type u} [Field K] {m : ℕ}

attribute [local instance] rightAlgebra midAlgebra

section CupCap

variable (c : Fin m) {s s' : Comp m} (hE : StepR (true, c) s s') (hF : StepR (false, c) s' s)

theorem castSucc_ne_succ' (c : Fin m) : c.castSucc ≠ c.succ := (Fin.castSucc_lt_succ c).ne

/-- The size `d` of block `c` of `s` in the cup `1_s → F E`. -/
theorem dFE_eq : dFE c hE = s c.castSucc := by
  rw [dFE, dBlock_eq (Sigma.fst : Gen s → Fin (m + 1)) (movedVar c s hE.2) c.castSucc
    (castSucc_ne_succ' c), card_labSet_sigma]

/-- The size of block `c + 1` of `+_c s`, minus one, in the cup `1_{s'} → E F`. -/
theorem dEF_eq : dEF c hE = s c.succ - 1 := by
  rw [dEF, dBlockR]
  have h1 := card_split_some (Sigma.fst : Gen s → Fin (m + 1)) (movedVar c s hE.2) c.succ
  rw [if_pos (show c.succ = (movedVar c s hE.2).fst from rfl), card_labSet_sigma] at h1
  exact h1

/-- The cup coefficient `x(s)_{c,β}` is `x_{c,β} ∈ H_s` acting on `F` from the left. -/
theorem xsFE_eq (β : ℕ) : xsFE c hE β = eRight K c s hE.2 (x K s c.castSucc β) := by
  rcases β with _ | β
  · rw [x_zero, map_one]; exact xB_zero _
  · rw [eRight_x, if_neg (castSucc_ne_succ' c), add_zero]

/-- The cup coefficient `x(s')_{c+1,β}` is `x_{c+1,β} ∈ H_{s'}` acting on `F` from the right. -/
theorem xsEF_eq (β : ℕ) : xsEF c hE β = eLeft K c s hE.2 (x K (raise c s) c.succ β) := by
  rcases β with _ | β
  · rw [x_zero, map_one]; exact xB_zero _
  · rw [eLeft_x, if_neg (castSucc_ne_succ' c).symm, add_zero]
    rfl

/-- **Lemma 5.4 (i) on the path model**: the cup element of `F E 1_s` with its polynomial part on
`E`: `∑_f (-1)^{d-f} ξ^f ⊗ x_{d-f} = ∑_g (-1)^{d-g} x_{d-g} ⊗ ξ^g`. -/
theorem cupFE_swap : cupFE K c hE hF = ∑ g ∈ Finset.range (dFE c hE + 1),
    BRing.tmul (Fst (K := K) c hF) (Est (K := K) c hE)
      ((-1) ^ (dFE c hE - g) * xsFE c hE (dFE c hE - g) : ERing K c s hE.2)
      (eXi K c s hE.2 ^ g) := by
  apply (feEquiv K c hE hF).injective
  rw [feEquiv_cupFE, cupEltKL, lemma_5_4_i_KL, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [feEquiv_tmul, ← neg_one_pow_tmul_one, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rfl

theorem cupFEW_apply' {C : Type u} [CommRing C] (X : BRing (H K s) C) (x : X.T) :
    cupFEW K c hE hF X x = ∑ g ∈ Finset.range (dFE c hE + 1),
      BRing.tmul (Fst (K := K) c hF) ((Est (K := K) c hE).tensor X)
        ((-1) ^ (dFE c hE - g) * xsFE c hE (dFE c hE - g) : ERing K c s hE.2)
        (BRing.tmul _ X (eXi K c s hE.2 ^ g) x) := by
  show (BRing.assoc _ _ X).hom (BRing.tmul _ X (cupFE K c hE hF) x) = _
  rw [cupFE_swap, BRing.sum_tmul, BHom.map_sum]
  exact Finset.sum_congr rfl fun g _ =>
    BRing.assoc_hom_tmul (M := Fst (K := K) c hF) (N := Est (K := K) c hE) (P := X) _ _ _

/-- **Lemma 5.4 (iii) on the path model**: `(ξ ⊗ 1) · cup = (1 ⊗ ξ) · cup` in `F E 1_s`. -/
theorem cupFE_slide :
    BRing.tmul (Fst (K := K) c hF) (Est (K := K) c hE) (eXi K c s hE.2) 1 * cupFE K c hE hF =
      BRing.tmul (Fst (K := K) c hF) (Est (K := K) c hE) 1 (eXi K c s hE.2) * cupFE K c hE hF := by
  apply (feEquiv K c hE hF).injective
  rw [map_mul, map_mul, feEquiv_cupFE, feEquiv_tmul, feEquiv_tmul, cupEltKL_eq, mul_left_comm,
    mul_left_comm (_ ⊗ₜ _)]
  congr 1
  exact lemma_5_4_iii

/-- The whiskered version of `cupFE_slide`. -/
theorem cupFEW_slide {C : Type u} [CommRing C] (X : BRing (H K s) C) (x : X.T) :
    BRing.tmul (Fst (K := K) c hF) ((Est (K := K) c hE).tensor X) (eXi K c s hE.2) 1 *
        cupFEW K c hE hF X x =
      BRing.tmul (Fst (K := K) c hF) ((Est (K := K) c hE).tensor X) 1
        (BRing.tmul _ X (eXi K c s hE.2) 1) * cupFEW K c hE hF X x := by
  show _ * (BRing.assoc _ _ X).hom (BRing.tmul _ X (cupFE K c hE hF) x) =
    _ * (BRing.assoc _ _ X).hom (BRing.tmul _ X (cupFE K c hE hF) x)
  have e1 : BRing.tmul (Fst (K := K) c hF) ((Est (K := K) c hE).tensor X) (eXi K c s hE.2) 1 =
      (BRing.assoc _ _ X).hom (BRing.tmul _ X (BRing.tmul _ _ (eXi K c s hE.2) 1) 1) := by
    rw [BRing.assoc_hom_tmul]; rfl
  have e2 : BRing.tmul (Fst (K := K) c hF) ((Est (K := K) c hE).tensor X) 1
      (BRing.tmul _ X (eXi K c s hE.2) 1) =
      (BRing.assoc _ _ X).hom (BRing.tmul _ X (BRing.tmul _ _ 1 (eXi K c s hE.2)) 1) := by
    rw [BRing.assoc_hom_tmul]
  rw [e1, e2, BRing.assoc_hom_apply, BRing.assoc_hom_apply, BRing.assoc_hom_apply, ← map_mul,
    ← map_mul, BRing.tmul_mul_tmul, BRing.tmul_mul_tmul, cupFE_slide]

/-- **Lemma 5.4 (iv) on the path model**: `(ξ ⊗ 1) · cup = (1 ⊗ ξ) · cup` in `E F 1_{s'}`. -/
theorem cupEF_slide :
    BRing.tmul (Est (K := K) c hE) (Fst (K := K) c hF) (eXi K c s hE.2) 1 * cupEF K c hE hF =
      BRing.tmul (Est (K := K) c hE) (Fst (K := K) c hF) 1 (eXi K c s hE.2) * cupEF K c hE hF := by
  apply (efEquiv K c hE hF).injective
  rw [map_mul, map_mul, efEquiv_cupEF, efEquiv_tmul, efEquiv_tmul, cupEltRKL_eq, mul_left_comm,
    mul_left_comm (_ ⊗ₜ _)]
  congr 1
  exact lemma_5_4_iv _ _

/-- The whiskered version of `cupEF_slide`. -/
theorem cupEFW_slide {C : Type u} [CommRing C] (Y : BRing (H K s') C) (y : Y.T) :
    BRing.tmul (Est (K := K) c hE) ((Fst (K := K) c hF).tensor Y) (eXi K c s hE.2) 1 *
        cupEFW K c hE hF Y y =
      BRing.tmul (Est (K := K) c hE) ((Fst (K := K) c hF).tensor Y) 1
        (BRing.tmul _ Y (eXi K c s hE.2) 1) * cupEFW K c hE hF Y y := by
  show _ * (BRing.assoc _ _ Y).hom (BRing.tmul _ Y (cupEF K c hE hF) y) =
    _ * (BRing.assoc _ _ Y).hom (BRing.tmul _ Y (cupEF K c hE hF) y)
  have e1 : BRing.tmul (Est (K := K) c hE) ((Fst (K := K) c hF).tensor Y) (eXi K c s hE.2) 1 =
      (BRing.assoc _ _ Y).hom (BRing.tmul _ Y (BRing.tmul _ _ (eXi K c s hE.2) 1) 1) := by
    rw [BRing.assoc_hom_tmul]; rfl
  have e2 : BRing.tmul (Est (K := K) c hE) ((Fst (K := K) c hF).tensor Y) 1
      (BRing.tmul _ Y (eXi K c s hE.2) 1) =
      (BRing.assoc _ _ Y).hom (BRing.tmul _ Y (BRing.tmul _ _ 1 (eXi K c s hE.2)) 1) := by
    rw [BRing.assoc_hom_tmul]
  rw [e1, e2, BRing.assoc_hom_apply, BRing.assoc_hom_apply, BRing.assoc_hom_apply, ← map_mul,
    ← map_mul, BRing.tmul_mul_tmul, BRing.tmul_mul_tmul, cupEF_slide]

/-- **Dots slide across the cap `E F → 1`**: `cap((w a) ⊗ b) = cap(a ⊗ (w b))`. -/
theorem capEFP_mul_left (w a b : ERing K c s hE.2) :
    capEFP K c hE hF (BRing.tmul _ _ (w * a) b) = capEFP K c hE hF (BRing.tmul _ _ a (w * b)) := by
  simp only [capEFP, efEquiv_tmul, capEF_tmul]
  rw [mul_assoc, mul_left_comm]

/-- **Dots slide across the cap `F E → 1`**: `cap((w a) ⊗ b) = cap(a ⊗ (w b))`. -/
theorem capFEP_mul_left (w a b : ERing K c s hE.2) :
    capFEP K c hE hF (BRing.tmul _ _ (w * a) b) = capFEP K c hE hF (BRing.tmul _ _ a (w * b)) := by
  simp only [capFEP, feEquiv_tmul, capFE_tmul]
  rw [mul_assoc, mul_left_comm]

/-- **The cap `E F → 1` below its top degree** (KL III (6.5)): on `ξ^e ⊗ 1`, `0` if
`e + 1 < s_c + 1` and `1` if `e = s_c`. -/
theorem capEFP_xi_pow (e : ℕ) (he : e ≤ s c.castSucc) :
    capEFP K c hE hF (BRing.tmul _ _ (eXi K c s hE.2 ^ e) 1) =
      if e = s c.castSucc then 1 else 0 := by
  have hB := blockCardL_movedVar c s hE.2
  simp only [capEFP, efEquiv_tmul]
  rw [show (1 : ERing K c s hE.2) = eXi K c s hE.2 ^ 0 from (pow_zero _).symm]
  erw [capEF_xi]
  rw [hB, add_zero]
  split_ifs with h1 h2 h2
  · rw [show e + 1 - (s c.castSucc + 1) = 0 by omega, pow_zero, one_mul, xbarB_zero, map_one,
      map_one]
  · omega
  · omega
  · rw [map_zero, map_zero]

/-- **The cap `F E → 1` below its top degree** (KL III (6.4)): on `1 ⊗ ξ^e`, `0` if
`e + 1 < s_{c+1}` and `1` if `e + 1 = s_{c+1}`. -/
theorem capFEP_xi_pow (e : ℕ) (he : e + 1 ≤ s c.succ) :
    capFEP K c hE hF (BRing.tmul _ _ 1 (eXi K c s hE.2 ^ e)) =
      if e + 1 = s c.succ then 1 else 0 := by
  have hB := blockCard_movedVar c s hE.2
  simp only [capFEP, feEquiv_tmul]
  rw [show (1 : ERing K c s hE.2) = eXi K c s hE.2 ^ 0 from (pow_zero _).symm]
  erw [capFE_xi]
  rw [hB, zero_add]
  split_ifs with h1 h2 h2
  · rw [show e + 1 - s c.succ = 0 by omega, pow_zero, one_mul, xbarB_zero, map_one]
  · omega
  · omega
  · rw [map_zero]

/-- The whiskered cup `1 → F E` commutes with multiplication on the suffix. -/
theorem cupFEW_mul {C : Type u} [CommRing C] (X : BRing (H K s) C) (w x : X.T) :
    cupFEW K c hE hF X (w * x) =
      BRing.tmul (Fst (K := K) c hF) ((Est (K := K) c hE).tensor X) 1 (BRing.tmul _ X 1 w) *
        cupFEW K c hE hF X x := by
  rw [cupFEW_apply, cupFEW_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [BRing.tmul_mul_tmul, BRing.tmul_mul_tmul, one_mul, one_mul]

/-- The whiskered cup `1 → E F` commutes with multiplication on the suffix. -/
theorem cupEFW_mul {C : Type u} [CommRing C] (Y : BRing (H K s') C) (w y : Y.T) :
    cupEFW K c hE hF Y (w * y) =
      BRing.tmul (Est (K := K) c hE) ((Fst (K := K) c hF).tensor Y) 1 (BRing.tmul _ Y 1 w) *
        cupEFW K c hE hF Y y := by
  rw [cupEFW_apply, cupEFW_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [BRing.tmul_mul_tmul, BRing.tmul_mul_tmul, one_mul, one_mul]

/-- **Dots slide across the whiskered cap `E F → 1`**. -/
theorem capEFW_slide {C : Type u} [CommRing C] (Y : BRing (H K s') C) (w : ERing K c s hE.2)
    (v : ((Est (K := K) c hE).tensor ((Fst (K := K) c hF).tensor Y)).T) :
    capEFW K c hE hF Y (BRing.tmul (Est (K := K) c hE) ((Fst (K := K) c hF).tensor Y) 1
      (BRing.tmul (Fst (K := K) c hF) Y w 1) * v) =
      capEFW K c hE hF Y (BRing.tmul (Est (K := K) c hE) ((Fst (K := K) c hF).tensor Y) w 1 * v) := by
  set u₁ := BRing.tmul (Est (K := K) c hE) ((Fst (K := K) c hF).tensor Y) 1
    (BRing.tmul (Fst (K := K) c hF) Y w 1)
  set u₂ := BRing.tmul (Est (K := K) c hE) ((Fst (K := K) c hF).tensor Y) w 1
  have key : ∀ (a : (Est (K := K) c hE).T) (b : (Fst (K := K) c hF).T) (y : Y.T),
      capEFW K c hE hF Y (u₁ * BRing.tmul (Est (K := K) c hE) ((Fst (K := K) c hF).tensor Y) a (BRing.tmul (Fst (K := K) c hF) Y b y)) =
        capEFW K c hE hF Y (u₂ * BRing.tmul (Est (K := K) c hE) ((Fst (K := K) c hF).tensor Y) a (BRing.tmul (Fst (K := K) c hF) Y b y)) := by
    intro a b y
    simp only [u₁, u₂]
    simp only [BRing.tmul_mul_tmul, one_mul, mul_one]
    rw [capEFW_tmul, capEFW_tmul, ← capEFP_mul_left]
  refine BRing.induction_on (P := fun v => capEFW K c hE hF Y (u₁ * v) = capEFW K c hE hF Y (u₂ * v))
    v (by beta_reduce; rw [mul_zero, mul_zero]) (fun a n => ?_) (fun x x' hx hx' => ?_)
  · refine BRing.induction_on (P := fun n => capEFW K c hE hF Y (u₁ * BRing.tmul (Est (K := K) c hE) ((Fst (K := K) c hF).tensor Y) a n) =
      capEFW K c hE hF Y (u₂ * BRing.tmul (Est (K := K) c hE) ((Fst (K := K) c hF).tensor Y) a n)) n
      (by beta_reduce; rw [BRing.tmul_zero, mul_zero, mul_zero]) (fun b y => key a b y)
      (fun x x' hx hx' => ?_)
    beta_reduce at hx hx' ⊢
    rw [BRing.tmul_add, mul_add, mul_add, BHom.map_add, BHom.map_add, hx, hx']
  · beta_reduce at hx hx' ⊢
    rw [mul_add, mul_add, BHom.map_add, BHom.map_add, hx, hx']

/-- **Dots slide across the whiskered cap `F E → 1`**. -/
theorem capFEW_slide {C : Type u} [CommRing C] (Y : BRing (H K s) C) (w : ERing K c s hE.2)
    (v : ((Fst (K := K) c hF).tensor ((Est (K := K) c hE).tensor Y)).T) :
    capFEW K c hE hF Y (BRing.tmul (Fst (K := K) c hF) ((Est (K := K) c hE).tensor Y) 1
      (BRing.tmul (Est (K := K) c hE) Y w 1) * v) =
      capFEW K c hE hF Y (BRing.tmul (Fst (K := K) c hF) ((Est (K := K) c hE).tensor Y) w 1 * v) := by
  set u₁ := BRing.tmul (Fst (K := K) c hF) ((Est (K := K) c hE).tensor Y) 1
    (BRing.tmul (Est (K := K) c hE) Y w 1)
  set u₂ := BRing.tmul (Fst (K := K) c hF) ((Est (K := K) c hE).tensor Y) w 1
  have key : ∀ (a : (Fst (K := K) c hF).T) (b : (Est (K := K) c hE).T) (y : Y.T),
      capFEW K c hE hF Y (u₁ * BRing.tmul (Fst (K := K) c hF) ((Est (K := K) c hE).tensor Y) a (BRing.tmul (Est (K := K) c hE) Y b y)) =
        capFEW K c hE hF Y (u₂ * BRing.tmul (Fst (K := K) c hF) ((Est (K := K) c hE).tensor Y) a (BRing.tmul (Est (K := K) c hE) Y b y)) := by
    intro a b y
    simp only [u₁, u₂]
    simp only [BRing.tmul_mul_tmul, one_mul, mul_one]
    rw [capFEW_tmul, capFEW_tmul, ← capFEP_mul_left]
  refine BRing.induction_on (P := fun v => capFEW K c hE hF Y (u₁ * v) = capFEW K c hE hF Y (u₂ * v))
    v (by beta_reduce; rw [mul_zero, mul_zero]) (fun a n => ?_) (fun x x' hx hx' => ?_)
  · refine BRing.induction_on (P := fun n => capFEW K c hE hF Y (u₁ * BRing.tmul (Fst (K := K) c hF) ((Est (K := K) c hE).tensor Y) a n) =
      capFEW K c hE hF Y (u₂ * BRing.tmul (Fst (K := K) c hF) ((Est (K := K) c hE).tensor Y) a n)) n
      (by beta_reduce; rw [BRing.tmul_zero, mul_zero, mul_zero]) (fun b y => key a b y)
      (fun x x' hx hx' => ?_)
    beta_reduce at hx hx' ⊢
    rw [BRing.tmul_add, mul_add, mul_add, BHom.map_add, BHom.map_add, hx, hx']
  · beta_reduce at hx hx' ⊢
    rw [mul_add, mul_add, BHom.map_add, BHom.map_add, hx, hx']

/-- The cup coefficient `x(s')_{c+1,β}` is `x_{c+1,β} ∈ H_{s'}` acting on `F` from the right. -/
theorem Fst_right_x (β : ℕ) :
    (Fst (K := K) c hF).right (x K s' c.succ β) = (xsEF c hE β : ERing K c s hE.2) := by
  have e : (Fst (K := K) c hF).right (x K s' c.succ β) =
      eLeft K c s hE.2 (hCast K hF.1.symm (x K s' c.succ β)) := rfl
  rw [e, hCast_x, xsEF_eq]

/-- The cup coefficient `x(s)_{c,β}` is `x_{c,β} ∈ H_s` acting on `F` from the left. -/
theorem Fst_left_x (β : ℕ) :
    (Fst (K := K) c hF).left (x K s c.castSucc β) = (xsFE c hE β : ERing K c s hE.2) := by
  have e : (Fst (K := K) c hF).left (x K s c.castSucc β) =
      eRight K c s hE.2 (x K s c.castSucc β) := rfl
  rw [e, xsFE_eq]

/-- The whiskered cap `F E → 1` commutes with multiplication on the suffix. -/
theorem capFEW_mul {C : Type u} [CommRing C] (Y : BRing (H K s) C) (w : Y.T)
    (v : ((Fst (K := K) c hF).tensor ((Est (K := K) c hE).tensor Y)).T) :
    capFEW K c hE hF Y (BRing.tmul (Fst (K := K) c hF) ((Est (K := K) c hE).tensor Y) 1
      (BRing.tmul (Est (K := K) c hE) Y 1 w) * v) = w * capFEW K c hE hF Y v := by
  set u := BRing.tmul (Fst (K := K) c hF) ((Est (K := K) c hE).tensor Y) 1
    (BRing.tmul (Est (K := K) c hE) Y 1 w)
  refine BRing.induction_on (P := fun v => capFEW K c hE hF Y (u * v) = w * capFEW K c hE hF Y v)
    v (by beta_reduce; rw [mul_zero, BHom.map_zero, mul_zero]) (fun a n => ?_)
    (fun x x' hx hx' => ?_)
  · refine BRing.induction_on (P := fun n => capFEW K c hE hF Y (u * BRing.tmul
      (Fst (K := K) c hF) ((Est (K := K) c hE).tensor Y) a n) =
      w * capFEW K c hE hF Y (BRing.tmul (Fst (K := K) c hF) ((Est (K := K) c hE).tensor Y) a n)) n
      (by beta_reduce; rw [BRing.tmul_zero, mul_zero, BHom.map_zero, mul_zero]) (fun b y => ?_)
      (fun x x' hx hx' => ?_)
    · beta_reduce
      simp only [u]
      simp only [BRing.tmul_mul_tmul, one_mul]
      rw [capFEW_tmul, capFEW_tmul, mul_left_comm]
    · beta_reduce at hx hx' ⊢
      rw [BRing.tmul_add, mul_add, BHom.map_add, BHom.map_add, hx, hx', mul_add]
  · beta_reduce at hx hx' ⊢
    rw [mul_add, BHom.map_add, BHom.map_add, hx, hx', mul_add]

/-- The whiskered cap `E F → 1` commutes with multiplication on the suffix. -/
theorem capEFW_mul {C : Type u} [CommRing C] (Y : BRing (H K s') C) (w : Y.T)
    (v : ((Est (K := K) c hE).tensor ((Fst (K := K) c hF).tensor Y)).T) :
    capEFW K c hE hF Y (BRing.tmul (Est (K := K) c hE) ((Fst (K := K) c hF).tensor Y) 1
      (BRing.tmul (Fst (K := K) c hF) Y 1 w) * v) = w * capEFW K c hE hF Y v := by
  set u := BRing.tmul (Est (K := K) c hE) ((Fst (K := K) c hF).tensor Y) 1
    (BRing.tmul (Fst (K := K) c hF) Y 1 w)
  refine BRing.induction_on (P := fun v => capEFW K c hE hF Y (u * v) = w * capEFW K c hE hF Y v)
    v (by beta_reduce; rw [mul_zero, BHom.map_zero, mul_zero]) (fun a n => ?_)
    (fun x x' hx hx' => ?_)
  · refine BRing.induction_on (P := fun n => capEFW K c hE hF Y (u * BRing.tmul
      (Est (K := K) c hE) ((Fst (K := K) c hF).tensor Y) a n) =
      w * capEFW K c hE hF Y (BRing.tmul (Est (K := K) c hE) ((Fst (K := K) c hF).tensor Y) a n)) n
      (by beta_reduce; rw [BRing.tmul_zero, mul_zero, BHom.map_zero, mul_zero]) (fun b y => ?_)
      (fun x x' hx hx' => ?_)
    · beta_reduce
      simp only [u]
      simp only [BRing.tmul_mul_tmul, one_mul]
      rw [capEFW_tmul, capEFW_tmul, mul_left_comm]
    · beta_reduce at hx hx' ⊢
      rw [BRing.tmul_add, mul_add, BHom.map_add, BHom.map_add, hx, hx', mul_add]
  · beta_reduce at hx hx' ⊢
    rw [mul_add, BHom.map_add, BHom.map_add, hx, hx', mul_add]

end CupCap

end Categorification.Flag

end

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.GammaSideways

/-!
# Cyclicity of crossings of distinct colours (KL III `eq_cyclic_cross-gen`)

KL III, arXiv:0807.3250v1, Definition 3.1 (TeX label `eq_cyclic_cross-gen`; relations
`Categorification.KL3.Diagram.Rel.cycCrossR`, `cycCrossL`) and §6.2 (the proposition after
Lemma 6.4: "both the far left and right bimodule maps are given by (6.9)").

The two rotations of the upward crossing `E_j E_i → E_i E_j` by nested cups and caps
(`Categorification.KL3.Diagram.rotCrossR`, `rotCrossL`) are written out layer by layer on the
path model (`rotCrossRW`, `rotCrossLW`, with an arbitrary 1-morphism `Y` on the right). The middle
three layers of each form a sideways crossing (`rotCrossRW_eq`, `rotCrossLW_eq`), so the rotations
are computed from Lemma 6.4 (`Categorification.Flag.GammaSideways`).

## Main results (`i ≠ j`)

* `rotCrossLW_eq_crossDn` : the left rotation equals `Γ_N` of the downward crossing (6.9)
  (followed by `Y`) for all `i ≠ j`;
* `rotCrossRW_eq_crossDn` : the right rotation equals it if `i · j = 0`, and equals **minus** it
  if `i · j = -1`;
* `rotCrossRW_eq_neg_rotCrossLW` : for adjacent colours the two rotations differ by the sign `-1`.

So the literal relation `eq_cyclic_cross-gen` (right rotation = downward crossing = left rotation)
holds on the path model for distant colours, and fails for adjacent colours whenever the
bimodules involved are nonzero and `2 ≠ 0` in `K`, whatever normalization is chosen for the
downward crossing. This is corrected in Khovanov–Lauda's *Erratum to "A categorification of
quantum sl(n)"*, Quantum Topol. 2 (2011), 97–99, whose revised Definition 4.1 keeps cyclicity of
crossings except for `i · j = -1`, where the two rotations differ by `-1`, as proved here (cf.
`Categorification.Flag.downupEF_W` for the sideways crossings).

The values at `1` (`rotCrossRW_one`, `rotCrossLW_one`) use the transport of `x_{c,1}` and
`x_{c+1,1}` across a downward strand (`Fx_castSucc`, `Fx_succ`) and the caps below and at their
lowest nonzero degree (`capFEP_one_xi_pow`, `capEFP_xi_pow_one`).
-/

noncomputable section

open scoped TensorProduct

namespace Categorification.Flag

universe u

variable {K : Type u} [Field K] {m : ℕ}

attribute [local instance] rightAlgebra midAlgebra

/-! ### Elementary symmetric functions across a strand -/

section Transport

theorem xbar_zero' {n : ℕ} (d : Fin n → ℕ) (j : Fin n) : xbar K d j 0 = 1 :=
  (hEquiv K d).injective (by rw [hEquiv_xbar, xbarB_zero, map_one])

theorem xbar_one {n : ℕ} (d : Fin n → ℕ) (j : Fin n) : xbar K d j 1 = -x K d j 1 := by
  have h := sum_x_mul_xbar (k := K) (d := d) j 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, if_neg one_ne_zero,
    Nat.sub_zero, Nat.sub_self, x_zero, one_mul] at h
  rw [xbar_zero', mul_one] at h
  exact eq_neg_of_add_eq_zero_left h

variable (c : Fin m) {r s : Comp m} (h : StepR (false, c) r s)

/-- Across `F_c` (from `r = +_c s` to `s`): `x(s)_{c,1} = x(r)_{c,1} - ξ` (the moved variable
enters block `c`). -/
theorem Fx_castSucc :
    (stepB K (false, c) r s h).left (x K s c.castSucc 1) =
      (stepB K (false, c) r s h).right (x K r c.castSucc 1) - xiStep K (false, c) r s h := by
  have e1 : ((stepB K (false, c) r s h).left (x K s c.castSucc 1) : ERing K c s h.2) =
      eRight K c s h.2 (x K s c.castSucc 1) := rfl
  have e2 : ((stepB K (false, c) r s h).right (x K r c.castSucc 1) : ERing K c s h.2) =
      eLeft K c s h.2 (hCast K h.1.symm (x K r c.castSucc 1)) := rfl
  rw [e1, e2, hCast_x, eRight_x, eLeft_x, if_neg (castSucc_ne_succ' c), if_pos rfl, xB_zero,
    mul_one, add_zero]
  exact (add_sub_cancel_right _ _).symm

/-- Across `F_c`: `x(s)_{c+1,1} = x(r)_{c+1,1} + ξ` (the moved variable leaves block `c + 1`). -/
theorem Fx_succ :
    (stepB K (false, c) r s h).left (x K s c.succ 1) =
      (stepB K (false, c) r s h).right (x K r c.succ 1) + xiStep K (false, c) r s h := by
  have e1 : ((stepB K (false, c) r s h).left (x K s c.succ 1) : ERing K c s h.2) =
      eRight K c s h.2 (x K s c.succ 1) := rfl
  have e2 : ((stepB K (false, c) r s h).right (x K r c.succ 1) : ERing K c s h.2) =
      eLeft K c s h.2 (hCast K h.1.symm (x K r c.succ 1)) := rfl
  rw [e1, e2, hCast_x, eRight_x, eLeft_x, if_pos rfl, if_neg (castSucc_ne_succ' c).symm, xB_zero,
    mul_one, add_zero]
  rfl

end Transport

/-! ### Values of the caps -/

section CapValues

variable (c : Fin m) {s s' : Comp m} (hE : StepR (true, c) s s') (hF : StepR (false, c) s' s)

/-- **KL III (6.4)** on the path model: the cap `F E → 1` on `1 ⊗ ξ^e`. -/
theorem capFEP_one_xi_pow (e : ℕ) :
    capFEP K c hE hF (BRing.tmul _ _ 1 (eXi K c s hE.2 ^ e)) =
      if s c.succ ≤ e + 1 then (-1) ^ (e + 1 - s c.succ) * xbar K s c.succ (e + 1 - s c.succ)
      else 0 := by
  have hB := blockCard_movedVar c s hE.2
  simp only [capFEP, feEquiv_tmul]
  rw [show (1 : ERing K c s hE.2) = eXi K c s hE.2 ^ 0 from (pow_zero _).symm]
  erw [capFE_xi]
  rw [hB, zero_add]
  split_ifs
  · rw [map_mul, map_pow, map_neg, map_one]
    congr 1
    rw [AlgEquiv.symm_apply_eq, hEquiv_xbar]
    rfl
  · rw [map_zero]

/-- **KL III (6.5)** on the path model: the cap `E F → 1` on `ξ^e ⊗ 1`. -/
theorem capEFP_xi_pow_one (e : ℕ) :
    capEFP K c hE hF (BRing.tmul _ _ (eXi K c s hE.2 ^ e) 1) =
      if s c.castSucc + 1 ≤ e + 1 then
        (-1) ^ (e + 1 - (s c.castSucc + 1)) * xbar K s' c.castSucc (e + 1 - (s c.castSucc + 1))
      else 0 := by
  have hB := blockCardL_movedVar c s hE.2
  simp only [capEFP, efEquiv_tmul]
  rw [show (1 : ERing K c s hE.2) = eXi K c s hE.2 ^ 0 from (pow_zero _).symm]
  erw [capEF_xi]
  rw [hB, add_zero]
  split_ifs
  · rw [map_mul, map_pow, map_neg, map_one, map_mul, map_pow, map_neg, map_one,
      borelEquivH'_xbarB, hCast_xbar]
  · rw [map_zero, map_zero]

/-- The cup `1 → E F` with its coefficients acting on the suffix. -/
theorem cupEFW_apply'' {C : Type u} [CommRing C] (Y : BRing (H K s') C) (y : Y.T) :
    cupEFW K c hE hF Y y = ∑ g ∈ Finset.range (dEF c hE + 1), (-1) ^ (dEF c hE - g) *
      BRing.tmul (Est (K := K) c hE) ((Fst (K := K) c hF).tensor Y) (eXi K c s hE.2 ^ g)
        (BRing.tmul (Fst (K := K) c hF) Y 1 (Y.left (x K s' c.succ (dEF c hE - g)) * y)) := by
  rw [cupEFW_apply]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [neg_one_pow_mul_tmul, ← Fst_right_x c hE hF, ← mul_one ((Fst (K := K) c hF).right _),
    BRing.tmul_balance]

end CapValues

/-! ### The right rotation `rotCrossR` -/

section RotR

variable (i j : Fin m) {t r₁ r₂ w : Comp m} (hFj : StepR (false, j) r₁ t)
  (hFi : StepR (false, i) r₂ r₁) (hFi' : StepR (false, i) w t) (hFj' : StepR (false, j) r₂ w)
  {E : Type u} [CommRing E] (Y : BRing (H K r₂) E)

variable (K) in
/-- **`Γ_N` of the right rotation of the upward crossing** `rotCrossR j i : F_j F_i 1 → F_i F_j 1`
(KL III `eq_cyclic_cross-gen`, left-hand picture; `Categorification.KL3.Diagram.rotCrossR`),
followed by `Y`, layer by layer: the cup `1 → E_j F_j` on the right, the cup `1 → E_i F_i`
inside it, the upward crossing `E_j E_i → E_i E_j`, the cap `F_i E_i → 1`, the cap
`F_j E_j → 1` on the left. -/
def rotCrossRW : BHom ((stepB K (false, j) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y))
    ((stepB K (false, i) w t hFi').tensor ((stepB K (false, j) r₂ w hFj').tensor Y)) :=
  (capFEW K j (hFj : StepR (true, j) t r₁) hFj
    ((stepB K (false, i) w t hFi').tensor ((stepB K (false, j) r₂ w hFj').tensor Y))).comp
  ((BHom.whiskerLeft (stepB K (false, j) r₁ t hFj) (capFEW K i (hFi : StepR (true, i) r₁ r₂) hFi
    ((stepB K (true, j) t r₁ hFj).tensor ((stepB K (false, i) w t hFi').tensor
      ((stepB K (false, j) r₂ w hFj').tensor Y))))).comp
  ((BHom.whiskerLeft (stepB K (false, j) r₁ t hFj) (BHom.whiskerLeft (stepB K (false, i) r₂ r₁ hFi)
    (locTwo (crossU K j i (hFj' : StepR (true, j) w r₂) (hFi' : StepR (true, i) t w)
      (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, j) t r₁))
      ((stepB K (false, i) w t hFi').tensor ((stepB K (false, j) r₂ w hFj').tensor Y))))).comp
  ((BHom.whiskerLeft (stepB K (false, j) r₁ t hFj) (BHom.whiskerLeft (stepB K (false, i) r₂ r₁ hFi)
    (BHom.whiskerLeft (stepB K (true, j) w r₂ hFj') (cupEFW K i (hFi' : StepR (true, i) t w) hFi'
      ((stepB K (false, j) r₂ w hFj').tensor Y))))).comp
  (BHom.whiskerLeft (stepB K (false, j) r₁ t hFj) (BHom.whiskerLeft (stepB K (false, i) r₂ r₁ hFi)
    (cupEFW K j (hFj' : StepR (true, j) w r₂) hFj' Y))))))

/-- The middle three layers of `rotCrossR` form the sideways crossing `crossr j i`. -/
theorem rotCrossRW_eq : rotCrossRW K i j hFj hFi hFi' hFj' Y =
    (capFEW K j (hFj : StepR (true, j) t r₁) hFj
      ((stepB K (false, i) w t hFi').tensor ((stepB K (false, j) r₂ w hFj').tensor Y))).comp
    ((BHom.whiskerLeft (stepB K (false, j) r₁ t hFj)
      (crossrW K j i hFi (hFj' : StepR (true, j) w r₂) (hFj : StepR (true, j) t r₁) hFi'
        ((stepB K (false, j) r₂ w hFj').tensor Y))).comp
    (BHom.whiskerLeft (stepB K (false, j) r₁ t hFj) (BHom.whiskerLeft (stepB K (false, i) r₂ r₁ hFi)
      (cupEFW K j (hFj' : StepR (true, j) w r₂) hFj' Y)))) := by
  rw [crossrW, BHom.whiskerLeft_comp, BHom.whiskerLeft_comp]
  rfl

/-- `rotCrossR` and the dot of the right strand `F_i`. -/
theorem rotCrossRW_dotR (hij : i ≠ j) (z) :
    rotCrossRW K i j hFj hFi hFi' hFj' Y
        (BRing.tmul (stepB K (false, j) r₁ t hFj) ((stepB K (false, i) r₂ r₁ hFi).tensor Y) 1
          (BRing.tmul (stepB K (false, i) r₂ r₁ hFi) Y (eXi K i r₁ hFi.2) 1) * z) =
      BRing.tmul (stepB K (false, i) w t hFi') ((stepB K (false, j) r₂ w hFj').tensor Y)
        (eXi K i t hFi'.2) 1 * rotCrossRW K i j hFj hFi hFi' hFj' Y z := by
  rw [rotCrossRW_eq]
  simp only [BHom.comp_apply]
  rw [whiskerLeft_mul_right _ _ _ _ (fun z => whiskerLeft_mul_left _ _ z _),
    whiskerLeft_mul_right _ _ _ _ (crossrW_dotF j i hFi _ _ hFi' _ (Ne.symm hij)), capFEW_mul]

/-- `rotCrossR` and the dot of the left strand `F_j`. -/
theorem rotCrossRW_dotL (hij : i ≠ j) (z) :
    rotCrossRW K i j hFj hFi hFi' hFj' Y
        (BRing.tmul (stepB K (false, j) r₁ t hFj) ((stepB K (false, i) r₂ r₁ hFi).tensor Y)
          (eXi K j t hFj.2) 1 * z) =
      BRing.tmul (stepB K (false, i) w t hFi') ((stepB K (false, j) r₂ w hFj').tensor Y) 1
        (BRing.tmul (stepB K (false, j) r₂ w hFj') Y (eXi K j w hFj'.2) 1) *
        rotCrossRW K i j hFj hFi hFi' hFj' Y z := by
  rw [rotCrossRW_eq]
  simp only [BHom.comp_apply]
  rw [whiskerLeft_mul_left, whiskerLeft_mul_left,
    ← capFEW_slide j (hFj : StepR (true, j) t r₁) hFj _ _,
    ← whiskerLeft_mul_right _ _ _ _ (crossrW_dotE j i hFi (hFj' : StepR (true, j) w r₂)
      (hFj : StepR (true, j) t r₁) hFi' _ (Ne.symm hij))]
  rw [whiskerLeft_mul_image _ _ _ (BRing.tmul (stepB K (false, i) r₂ r₁ hFi) _ 1
      (BRing.tmul (stepB K (true, j) w r₂ hFj') ((stepB K (false, j) r₂ w hFj').tensor Y) 1
        (BRing.tmul (stepB K (false, j) r₂ w hFj') Y (eXi K j w hFj'.2) 1)))
    (whiskerLeft_mul_image _ _ _ _ (fun y =>
      (cupEFW_slide j (hFj' : StepR (true, j) w r₂) hFj' Y y)))]
  rw [whiskerLeft_mul_right _ _ _ _ (crossrW_mul_suffix j i hFi _ _ hFi' _ _), capFEW_mul]

/-- One summand of `rotCrossR(1 ⊗ 1 ⊗ y)`. -/
theorem rotCrossRW_term (hij : i ≠ j) (n g : ℕ) (y : Y.T) :
    capFEW K j (hFj : StepR (true, j) t r₁) hFj
      ((stepB K (false, i) w t hFi').tensor ((stepB K (false, j) r₂ w hFj').tensor Y))
      (BRing.tmul (stepB K (false, j) r₁ t hFj) ((stepB K (true, j) t r₁ hFj).tensor
          ((stepB K (false, i) w t hFi').tensor ((stepB K (false, j) r₂ w hFj').tensor Y))) 1
        (crossrW K j i hFi (hFj' : StepR (true, j) w r₂) (hFj : StepR (true, j) t r₁) hFi'
          ((stepB K (false, j) r₂ w hFj').tensor Y)
          (BRing.tmul (stepB K (false, i) r₂ r₁ hFi) ((stepB K (true, j) w r₂ hFj').tensor
            ((stepB K (false, j) r₂ w hFj').tensor Y)) 1
          ((-1) ^ n * BRing.tmul (stepB K (true, j) w r₂ hFj') ((stepB K (false, j) r₂ w hFj').tensor Y)
            (eXi K j w hFj'.2 ^ g) (BRing.tmul (stepB K (false, j) r₂ w hFj') Y 1 y))))) =
      (-1) ^ n * ((if j.castSucc = i.succ then -1 else 1) *
        BRing.tmul (stepB K (false, i) w t hFi') ((stepB K (false, j) r₂ w hFj').tensor Y)
          ((stepB K (false, i) w t hFi').left (capFEP K j (hFj : StepR (true, j) t r₁) hFj
            (BRing.tmul _ _ 1 (eXi K j t hFj.2 ^ g))))
          (BRing.tmul (stepB K (false, j) r₂ w hFj') Y 1 y)) := by
  rw [tmul_neg_one_pow_mul, BHom.map_neg_one_pow_mul, tmul_neg_one_pow_mul,
    BHom.map_neg_one_pow_mul]
  congr 1
  have e : BRing.tmul (stepB K (false, i) r₂ r₁ hFi) ((stepB K (true, j) w r₂ hFj').tensor
      ((stepB K (false, j) r₂ w hFj').tensor Y)) 1
      (BRing.tmul (stepB K (true, j) w r₂ hFj') ((stepB K (false, j) r₂ w hFj').tensor Y)
        (eXi K j w hFj'.2 ^ g) (BRing.tmul (stepB K (false, j) r₂ w hFj') Y 1 y)) =
      BRing.tmul (stepB K (false, i) r₂ r₁ hFi) ((stepB K (true, j) w r₂ hFj').tensor
        ((stepB K (false, j) r₂ w hFj').tensor Y)) 1
        (BRing.tmul (stepB K (true, j) w r₂ hFj') ((stepB K (false, j) r₂ w hFj').tensor Y)
          (eXi K j w hFj'.2 ^ g) 1) *
      BRing.tmul (stepB K (false, i) r₂ r₁ hFi) ((stepB K (true, j) w r₂ hFj').tensor
        ((stepB K (false, j) r₂ w hFj').tensor Y)) 1
        (BRing.tmul (stepB K (true, j) w r₂ hFj') ((stepB K (false, j) r₂ w hFj').tensor Y) 1
          (BRing.tmul (stepB K (false, j) r₂ w hFj') Y 1 y)) := by
    simp only [BRing.tmul_mul_tmul, mul_one, one_mul]
  rw [e, crossrW_dotE_pow j i hFi _ _ hFi' _ (Ne.symm hij), crossrW_one j i hFi _ _ hFi' _
    (Ne.symm hij)]
  split_ifs
  · simp only [mul_neg, BRing.tmul_neg, BHom.map_neg, BRing.tmul_mul_tmul, mul_one, one_mul,
      capFEW_tmul, BRing.tensor_left, neg_one_mul]
    rw [BRing.tmul_neg, BHom.map_neg, capFEW_tmul, BRing.tensor_left, BRing.tmul_mul_tmul,
      one_mul, mul_one]
  · simp only [BRing.tmul_mul_tmul, mul_one, one_mul, capFEW_tmul]
    rw [BRing.tensor_left, BRing.tmul_mul_tmul, one_mul, mul_one]

/-- **The right rotation at `1`**: for `i ≠ j`, `rotCrossR(1 ⊗ 1 ⊗ y)` is `1 ⊗ 1 ⊗ y` if
`i · j = 0`, `-(1 ⊗ 1 ⊗ y)` if `j = i + 1`, and `1 ⊗ ξ_j y - ξ_i ⊗ 1 ⊗ y` if `i = j + 1`. -/
theorem rotCrossRW_one (hij : i ≠ j) (y : Y.T) :
    rotCrossRW K i j hFj hFi hFi' hFj' Y (BRing.tmul _ _ 1 (BRing.tmul _ _ 1 y)) =
      if i.castSucc = j.succ then
        BRing.tmul (stepB K (false, i) w t hFi') ((stepB K (false, j) r₂ w hFj').tensor Y) 1
          (BRing.tmul (stepB K (false, j) r₂ w hFj') Y (eXi K j w hFj'.2) y) -
        BRing.tmul (stepB K (false, i) w t hFi') ((stepB K (false, j) r₂ w hFj').tensor Y)
          (eXi K i t hFi'.2) (BRing.tmul (stepB K (false, j) r₂ w hFj') Y 1 y)
      else if j.castSucc = i.succ then -BRing.tmul _ _ 1 (BRing.tmul _ _ 1 y)
      else BRing.tmul _ _ 1 (BRing.tmul _ _ 1 y) := by
  rw [rotCrossRW_eq]
  simp only [BHom.comp_apply, BHom.whiskerLeft_tmul]
  rw [cupEFW_apply'' j _ _ Y y, BRing.tmul_sum, BHom.map_sum, BRing.tmul_sum, BHom.map_sum]
  rw [Finset.sum_congr rfl fun g _ => rotCrossRW_term i j hFj hFi hFi' hFj' Y hij _ g _]
  simp only [capFEP_one_xi_pow j (hFj : StepR (true, j) t r₁) hFj]
  have hd : dEF j (hFj' : StepR (true, j) w r₂) = w j.succ - 1 := dEF_eq j _
  have hw : w j.succ = t j.succ + (if i.castSucc = j.succ then 1 else 0) := by
    rw [← hFi'.1, raise]
    by_cases h1 : j.succ = i.castSucc
    · rw [if_pos h1, if_pos h1.symm]
    · have h3 : j.succ ≠ i.succ := fun h => hij (Fin.succ_injective _ h).symm
      rw [if_neg h1, if_neg h3, if_neg (fun h => h1 h.symm), add_zero]
  have ht := hFj.2
  set d := dEF j (hFj' : StepR (true, j) w r₂) with hd'
  by_cases hadj : i.castSucc = j.succ
  · have hadj' : ¬ j.castSucc = i.succ := by
      intro h
      have h1 := congrArg Fin.val hadj
      have h2 := congrArg Fin.val h
      simp only [Fin.coe_castSucc, Fin.val_succ] at h1 h2
      omega
    rw [if_pos hadj] at hw
    rw [if_pos hadj]
    simp only [if_neg hadj', one_mul]
    obtain ⟨b, hb⟩ : ∃ b, t j.succ = b + 1 := ⟨t j.succ - 1, by omega⟩
    have hdb : d = b + 1 := by omega
    rw [hdb, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_eq_zero (fun g hg => by
      rw [if_neg (by rw [hb]; have := Finset.mem_range.1 hg; omega), map_zero, BRing.zero_tmul,
        mul_zero])]
    rw [if_pos (by omega), if_pos (by omega), zero_add,
      show b + 1 - b = 1 by omega, show b + 1 - (b + 1) = 0 by omega,
      show b + 1 - t j.succ = 0 by omega, show b + 1 + 1 - t j.succ = 1 by omega,
      pow_zero, pow_one, pow_zero, pow_one, one_mul, one_mul, xbar_zero', map_one, x_zero, map_one,
      one_mul, xbar_one, neg_one_mul (-x K t j.succ 1), neg_neg]
    -- transport `x_{j+1,1}` across `F_i` and `F_j`
    have e1 : (stepB K (false, i) w t hFi').left (x K t j.succ 1) =
        (stepB K (false, i) w t hFi').right (x K w j.succ 1) - xiStep K (false, i) w t hFi' := by
      have := Fx_castSucc (K := K) i hFi'
      rw [hadj] at this
      exact this
    rw [e1, BRing.sub_tmul, ← mul_one ((stepB K (false, i) w t hFi').right (x K w j.succ 1)),
      BRing.tmul_balance, BRing.tensor_left, BRing.tmul_mul_tmul, mul_one, one_mul,
      Fx_succ j hFj', BRing.add_tmul, ← mul_one ((stepB K (false, j) r₂ w hFj').right _),
      BRing.tmul_balance]
    have hx1 : xiStep K (false, j) r₂ w hFj' = eXi K j w hFj'.2 := rfl
    have hx2 : xiStep K (false, i) w t hFi' = eXi K i t hFi'.2 := rfl
    rw [BRing.tmul_add, neg_one_mul, hx1, hx2]
    abel
  · rw [if_neg hadj, add_zero] at hw
    rw [if_neg hadj]
    have hdb : d = t j.succ - 1 := by omega
    rw [Finset.sum_eq_single d (fun g hg hgd => by
      rw [if_neg (show ¬ t j.succ ≤ g + 1 by have := Finset.mem_range.1 hg; omega), map_zero,
        BRing.zero_tmul, mul_zero, mul_zero]) (fun h => absurd (Finset.mem_range.2 (Nat.lt_succ_self d)) h)]
    rw [if_pos (show t j.succ ≤ d + 1 by omega), show d + 1 - t j.succ = 0 by omega, Nat.sub_self, pow_zero, pow_zero,
      one_mul, one_mul, xbar_zero', map_one, x_zero, map_one, one_mul]
    split_ifs
    · rw [neg_one_mul]
    · rw [one_mul]

theorem tauDn_ne (hij : i ≠ j) : tauDn K j i hFj hFi hFi' hFj' = 0 := by
  unfold tauDn
  rw [tauU_ne i j hij, BHom.swapConj_zero]

/-- The downward crossing (6.9), followed by `Y`, at `1`. -/
theorem locTwo_crossDn_one (hij : i ≠ j) (y : Y.T) :
    locTwo (crossDn K j i hFj hFi hFi' hFj') Y (BRing.tmul _ _ 1 (BRing.tmul _ _ 1 y)) =
      if i.castSucc = j.succ then
        BRing.tmul (stepB K (false, i) w t hFi') ((stepB K (false, j) r₂ w hFj').tensor Y)
          (eXi K i t hFi'.2) (BRing.tmul (stepB K (false, j) r₂ w hFj') Y 1 y) -
        BRing.tmul (stepB K (false, i) w t hFi') ((stepB K (false, j) r₂ w hFj').tensor Y) 1
          (BRing.tmul (stepB K (false, j) r₂ w hFj') Y (eXi K j w hFj'.2) y)
      else BRing.tmul _ _ 1 (BRing.tmul _ _ 1 y) := by
  rw [locTwo_tmul, ← BRing.one_eq, crossDn_one, if_neg hij]
  split_ifs
  · rw [BRing.sub_tmul, BHom.map_sub, BRing.assoc_hom_tmul, BRing.assoc_hom_tmul]
  · rw [BRing.one_eq, BRing.assoc_hom_tmul]

theorem locTwo_crossDn_dotL (hij : i ≠ j) (z) :
    locTwo (crossDn K j i hFj hFi hFi' hFj') Y
        (BRing.tmul (stepB K (false, j) r₁ t hFj) ((stepB K (false, i) r₂ r₁ hFi).tensor Y)
          (eXi K j t hFj.2) 1 * z) =
      BRing.tmul (stepB K (false, i) w t hFi') ((stepB K (false, j) r₂ w hFj').tensor Y) 1
        (BRing.tmul (stepB K (false, j) r₂ w hFj') Y (eXi K j w hFj'.2) 1) *
        locTwo (crossDn K j i hFj hFi hFi' hFj') Y z := by
  have := BHom.congr_apply ((crossDn_rules (K := K) j i hFj hFi hFi' hFj').locL Y) z
  rw [BHom.comp_apply, BHom.add_apply, tauDn_ne i j hFj hFi hFi' hFj' hij, locTwo_neg, locTwo_zero,
    BHom.neg_apply, BHom.zero_apply, neg_zero, zero_add, BHom.comp_apply, BHom.mulB_apply, BHom.mulB_apply] at this
  exact this

theorem locTwo_crossDn_dotR (hij : i ≠ j) (z) :
    locTwo (crossDn K j i hFj hFi hFi' hFj') Y
        (BRing.tmul (stepB K (false, j) r₁ t hFj) ((stepB K (false, i) r₂ r₁ hFi).tensor Y) 1
          (BRing.tmul (stepB K (false, i) r₂ r₁ hFi) Y (eXi K i r₁ hFi.2) 1) * z) =
      BRing.tmul (stepB K (false, i) w t hFi') ((stepB K (false, j) r₂ w hFj').tensor Y)
        (eXi K i t hFi'.2) 1 * locTwo (crossDn K j i hFj hFi hFi' hFj') Y z := by
  have := BHom.congr_apply ((crossDn_rules (K := K) j i hFj hFi hFi' hFj').locR Y) z
  rw [BHom.comp_apply, BHom.sub_apply, tauDn_ne i j hFj hFi hFi' hFj' hij, locTwo_neg, locTwo_zero,
    BHom.neg_apply, BHom.zero_apply, neg_zero, sub_zero, BHom.comp_apply, BHom.mulB_apply, BHom.mulB_apply] at this
  exact this

/-- **Cyclicity of crossings of distinct colours, right rotation** (KL III `eq_cyclic_cross-gen`,
relation `cycCrossR`): for `i ≠ j`, the right rotation of the upward crossing `E_j E_i → E_i E_j`
is `Γ_N` of the downward crossing `F_j F_i → F_i F_j` (6.9) if `i · j = 0`, and **minus** it if
`i · j = -1`. -/
theorem rotCrossRW_eq_crossDn (hij : i ≠ j) :
    rotCrossRW K i j hFj hFi hFi' hFj' Y =
      if i.castSucc = j.succ ∨ j.castSucc = i.succ then -locTwo (crossDn K j i hFj hFi hFi' hFj') Y
      else locTwo (crossDn K j i hFj hFi hFi' hFj') Y := by
  refine BHom.ext fun z => ?_
  refine ext_two (Y := Y) (eXi K j t hFj.2) (eXi K i r₁ hFi.2) (stepF_spanned j hFj)
    (stepF_spanned i hFi) (rotCrossRW K i j hFj hFi hFi' hFj' Y).toAddHom
    (if i.castSucc = j.succ ∨ j.castSucc = i.succ then -locTwo (crossDn K j i hFj hFi hFi' hFj') Y
      else locTwo (crossDn K j i hFj hFi hFi' hFj') Y : BHom _ _).toAddHom
    (BRing.tmul _ _ 1 (BRing.tmul _ _ (eXi K j w hFj'.2) 1)) (BRing.tmul _ _ (eXi K i t hFi'.2) 1)
    (fun z => ?_) (fun z => ?_) (fun z => ?_) (fun z => ?_) (fun y => ?_) z
  · rw [BHom.toAddHom_apply, BHom.toAddHom_apply, rotCrossRW_dotL i j hFj hFi hFi' hFj' Y hij]
  · rw [BHom.toAddHom_apply, BHom.toAddHom_apply]
    split_ifs
    · rw [BHom.neg_apply, BHom.neg_apply, locTwo_crossDn_dotL i j hFj hFi hFi' hFj' Y hij, mul_neg]
    · rw [locTwo_crossDn_dotL i j hFj hFi hFi' hFj' Y hij]
  · rw [BHom.toAddHom_apply, BHom.toAddHom_apply, rotCrossRW_dotR i j hFj hFi hFi' hFj' Y hij]
  · rw [BHom.toAddHom_apply, BHom.toAddHom_apply]
    split_ifs
    · rw [BHom.neg_apply, BHom.neg_apply, locTwo_crossDn_dotR i j hFj hFi hFi' hFj' Y hij, mul_neg]
    · rw [locTwo_crossDn_dotR i j hFj hFi hFi' hFj' Y hij]
  · rw [BHom.toAddHom_apply, BHom.toAddHom_apply, rotCrossRW_one i j hFj hFi hFi' hFj' Y hij]
    by_cases h1 : i.castSucc = j.succ
    · rw [if_pos h1, if_pos (Or.inl h1), BHom.neg_apply,
        locTwo_crossDn_one i j hFj hFi hFi' hFj' Y hij, if_pos h1, neg_sub]
    · by_cases h2 : j.castSucc = i.succ
      · rw [if_neg h1, if_pos h2, if_pos (Or.inr h2), BHom.neg_apply,
          locTwo_crossDn_one i j hFj hFi hFi' hFj' Y hij, if_neg h1]
      · rw [if_neg h1, if_neg h2, if_neg (not_or.2 ⟨h1, h2⟩),
          locTwo_crossDn_one i j hFj hFi hFi' hFj' Y hij, if_neg h1]

end RotR

/-! ### The left rotation `rotCrossL` -/

section RotL

variable (i j : Fin m) {t r₁ r₂ w : Comp m} (hFj : StepR (false, j) r₁ t)
  (hFi : StepR (false, i) r₂ r₁) (hFi' : StepR (false, i) w t) (hFj' : StepR (false, j) r₂ w)
  {E : Type u} [CommRing E] (Y : BRing (H K r₂) E)

variable (K) in
/-- **`Γ_N` of the left rotation of the upward crossing** `rotCrossL j i : F_j F_i 1 → F_i F_j 1`
(KL III `eq_cyclic_cross-gen`, right-hand picture; `Categorification.KL3.Diagram.rotCrossL`),
followed by `Y`, layer by layer: the cup `1 → F_i E_i` on the left, the cup `1 → F_j E_j` inside
it, the upward crossing `E_j E_i → E_i E_j`, the cap `E_j F_j → 1`, the cap `E_i F_i → 1` on the
right. -/
def rotCrossLW : BHom ((stepB K (false, j) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y))
    ((stepB K (false, i) w t hFi').tensor ((stepB K (false, j) r₂ w hFj').tensor Y)) :=
  (BHom.whiskerLeft (stepB K (false, i) w t hFi') (BHom.whiskerLeft (stepB K (false, j) r₂ w hFj')
    (capEFW K i (hFi : StepR (true, i) r₁ r₂) hFi Y))).comp
  ((BHom.whiskerLeft (stepB K (false, i) w t hFi') (BHom.whiskerLeft (stepB K (false, j) r₂ w hFj')
    (BHom.whiskerLeft (stepB K (true, i) r₁ r₂ hFi)
      (capEFW K j (hFj : StepR (true, j) t r₁) hFj ((stepB K (false, i) r₂ r₁ hFi).tensor Y))))).comp
  ((BHom.whiskerLeft (stepB K (false, i) w t hFi') (BHom.whiskerLeft (stepB K (false, j) r₂ w hFj')
    (locTwo (crossU K j i (hFj' : StepR (true, j) w r₂) (hFi' : StepR (true, i) t w)
      (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, j) t r₁))
      ((stepB K (false, j) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y))))).comp
  ((BHom.whiskerLeft (stepB K (false, i) w t hFi') (cupFEW K j (hFj' : StepR (true, j) w r₂) hFj'
    ((stepB K (true, i) t w hFi').tensor ((stepB K (false, j) r₁ t hFj).tensor
      ((stepB K (false, i) r₂ r₁ hFi).tensor Y))))).comp
  (cupFEW K i (hFi' : StepR (true, i) t w) hFi'
    ((stepB K (false, j) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y))))))

/-- The middle three layers of `rotCrossL` form the sideways crossing `crossl i j`. -/
theorem rotCrossLW_eq : rotCrossLW K i j hFj hFi hFi' hFj' Y =
    (BHom.whiskerLeft (stepB K (false, i) w t hFi') (BHom.whiskerLeft (stepB K (false, j) r₂ w hFj')
      (capEFW K i (hFi : StepR (true, i) r₁ r₂) hFi Y))).comp
    ((BHom.whiskerLeft (stepB K (false, i) w t hFi')
      (crosslW K i j (hFi' : StepR (true, i) t w) hFj hFj' (hFi : StepR (true, i) r₁ r₂)
        ((stepB K (false, i) r₂ r₁ hFi).tensor Y))).comp
    (cupFEW K i (hFi' : StepR (true, i) t w) hFi'
      ((stepB K (false, j) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y)))) := by
  rw [crosslW, BHom.whiskerLeft_comp, BHom.whiskerLeft_comp]
  rfl

/-- `rotCrossL` and the dot of the left strand `F_j`. -/
theorem rotCrossLW_dotL (hij : i ≠ j) (z) :
    rotCrossLW K i j hFj hFi hFi' hFj' Y
        (BRing.tmul (stepB K (false, j) r₁ t hFj) ((stepB K (false, i) r₂ r₁ hFi).tensor Y)
          (eXi K j t hFj.2) 1 * z) =
      BRing.tmul (stepB K (false, i) w t hFi') ((stepB K (false, j) r₂ w hFj').tensor Y) 1
        (BRing.tmul (stepB K (false, j) r₂ w hFj') Y (eXi K j w hFj'.2) 1) *
        rotCrossLW K i j hFj hFi hFi' hFj' Y z := by
  rw [rotCrossLW_eq]
  simp only [BHom.comp_apply]
  rw [cupFEW_mul, whiskerLeft_mul_right _ _ _ _ (crosslW_dotF i j _ hFj hFj' _ _ hij),
    whiskerLeft_mul_right _ _ _ _ (fun z => whiskerLeft_mul_left _ _ z _)]

/-- `rotCrossL` and the dot of the right strand `F_i`. -/
theorem rotCrossLW_dotR (hij : i ≠ j) (z) :
    rotCrossLW K i j hFj hFi hFi' hFj' Y
        (BRing.tmul (stepB K (false, j) r₁ t hFj) ((stepB K (false, i) r₂ r₁ hFi).tensor Y) 1
          (BRing.tmul (stepB K (false, i) r₂ r₁ hFi) Y (eXi K i r₁ hFi.2) 1) * z) =
      BRing.tmul (stepB K (false, i) w t hFi') ((stepB K (false, j) r₂ w hFj').tensor Y)
        (eXi K i t hFi'.2) 1 * rotCrossLW K i j hFj hFi hFi' hFj' Y z := by
  rw [rotCrossLW_eq]
  simp only [BHom.comp_apply]
  rw [cupFEW_mul, whiskerLeft_mul_right _ _ _ _ (crosslW_mul_suffix i j _ hFj hFj' _ _ _)]
  rw [whiskerLeft_mul_congr _ _ _ (BRing.tmul (stepB K (false, j) r₂ w hFj') _ 1
      (BRing.tmul (stepB K (true, i) r₁ r₂ hFi) ((stepB K (false, i) r₂ r₁ hFi).tensor Y)
        (eXi K i r₁ hFi.2) 1))
    (whiskerLeft_mul_congr _ _ _ _ (capEFW_slide i (hFi : StepR (true, i) r₁ r₂) hFi Y _))]
  rw [← whiskerLeft_mul_right _ _ _ _ (crosslW_dotE i j (hFi' : StepR (true, i) t w) hFj hFj'
      (hFi : StepR (true, i) r₁ r₂) _ hij),
    ← cupFEW_slide i (hFi' : StepR (true, i) t w) hFi', whiskerLeft_mul_left,
    whiskerLeft_mul_left]

/-- **The left rotation at `1`**: for `i ≠ j`, `rotCrossL(1 ⊗ 1 ⊗ y)` is `1 ⊗ 1 ⊗ y` unless
`i = j + 1`, where it is `ξ_i ⊗ 1 ⊗ y - 1 ⊗ ξ_j y`. -/
theorem rotCrossLW_one (hij : i ≠ j) (y : Y.T) :
    rotCrossLW K i j hFj hFi hFi' hFj' Y (BRing.tmul _ _ 1 (BRing.tmul _ _ 1 y)) =
      if i.castSucc = j.succ then
        BRing.tmul (stepB K (false, i) w t hFi') ((stepB K (false, j) r₂ w hFj').tensor Y)
          (eXi K i t hFi'.2) (BRing.tmul (stepB K (false, j) r₂ w hFj') Y 1 y) -
        BRing.tmul (stepB K (false, i) w t hFi') ((stepB K (false, j) r₂ w hFj').tensor Y) 1
          (BRing.tmul (stepB K (false, j) r₂ w hFj') Y (eXi K j w hFj'.2) y)
      else BRing.tmul _ _ 1 (BRing.tmul _ _ 1 y) := by
  rw [rotCrossLW_eq]
  simp only [BHom.comp_apply]
  rw [cupFEW_apply', BHom.map_sum, BHom.map_sum]
  have hterm : ∀ g, BHom.whiskerLeft (stepB K (false, i) w t hFi')
      (BHom.whiskerLeft (stepB K (false, j) r₂ w hFj') (capEFW K i (hFi : StepR (true, i) r₁ r₂) hFi Y))
      (BHom.whiskerLeft (stepB K (false, i) w t hFi')
        (crosslW K i j (hFi' : StepR (true, i) t w) hFj hFj' (hFi : StepR (true, i) r₁ r₂)
          ((stepB K (false, i) r₂ r₁ hFi).tensor Y))
        (BRing.tmul (stepB K (false, i) w t hFi') _
          ((-1) ^ (dFE i (hFi' : StepR (true, i) t w) - g) *
            xsFE i (hFi' : StepR (true, i) t w) (dFE i (hFi' : StepR (true, i) t w) - g) :
              ERing K i t hFi'.2)
          (BRing.tmul (stepB K (true, i) t w hFi') _ (eXi K i t hFi'.2 ^ g)
            (BRing.tmul (stepB K (false, j) r₁ t hFj) _ 1 (BRing.tmul (stepB K (false, i) r₂ r₁ hFi) Y
              1 y))))) =
      BRing.tmul (stepB K (false, i) w t hFi') ((stepB K (false, j) r₂ w hFj').tensor Y)
        ((-1) ^ (dFE i (hFi' : StepR (true, i) t w) - g) *
            xsFE i (hFi' : StepR (true, i) t w) (dFE i (hFi' : StepR (true, i) t w) - g) :
              ERing K i t hFi'.2)
        (BRing.tmul (stepB K (false, j) r₂ w hFj') Y 1
          (Y.left (capEFP K i (hFi : StepR (true, i) r₁ r₂) hFi
            (BRing.tmul _ _ (eXi K i r₁ hFi.2 ^ g) 1)) * y)) := by
    intro g
    have e : BRing.tmul (stepB K (true, i) t w hFi') ((stepB K (false, j) r₁ t hFj).tensor
        ((stepB K (false, i) r₂ r₁ hFi).tensor Y)) (eXi K i t hFi'.2 ^ g)
          (BRing.tmul (stepB K (false, j) r₁ t hFj) _ 1 (BRing.tmul (stepB K (false, i) r₂ r₁ hFi) Y
            1 y)) =
        BRing.tmul (stepB K (true, i) t w hFi') ((stepB K (false, j) r₁ t hFj).tensor
          ((stepB K (false, i) r₂ r₁ hFi).tensor Y)) (eXi K i t hFi'.2 ^ g) 1 *
        BRing.tmul (stepB K (true, i) t w hFi') ((stepB K (false, j) r₁ t hFj).tensor
          ((stepB K (false, i) r₂ r₁ hFi).tensor Y)) 1
          (BRing.tmul (stepB K (false, j) r₁ t hFj) _ 1 (BRing.tmul (stepB K (false, i) r₂ r₁ hFi) Y
            1 y)) := by
      simp only [BRing.tmul_mul_tmul, mul_one, one_mul]
    rw [BHom.whiskerLeft_tmul, e, crosslW_dotE_pow i j _ hFj hFj' _ _ hij,
      crosslW_one i j _ hFj hFj' _ _ hij, BHom.whiskerLeft_tmul]
    simp only [BRing.tmul_mul_tmul, one_mul, mul_one]
    rw [BHom.whiskerLeft_tmul, capEFW_tmul]
  rw [Finset.sum_congr rfl fun g _ => hterm g]
  simp only [capEFP_xi_pow_one i (hFi : StepR (true, i) r₁ r₂) hFi]
  have hd : dFE i (hFi' : StepR (true, i) t w) = t i.castSucc := dFE_eq i _
  have hr : r₁ i.castSucc + (if i.castSucc = j.succ then 1 else 0) = t i.castSucc := by
    rw [← hFj.1, raise]
    by_cases h1 : i.castSucc = j.castSucc
    · exact absurd (Fin.castSucc_injective _ h1) hij
    · by_cases h2 : i.castSucc = j.succ
      · rw [if_neg h1, if_pos h2, if_pos h2]
        have := hFj.2; rw [← h2] at this; omega
      · rw [if_neg h1, if_neg h2, if_neg h2, add_zero]
  set d := dFE i (hFi' : StepR (true, i) t w) with hd'
  by_cases hadj : i.castSucc = j.succ
  · rw [if_pos hadj] at hr
    rw [if_pos hadj]
    obtain ⟨b, hb⟩ : ∃ b, r₁ i.castSucc = b := ⟨_, rfl⟩
    have hdb : d = b + 1 := by omega
    rw [hdb, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_eq_zero (fun g hg => by
      rw [if_neg (show ¬ r₁ i.castSucc + 1 ≤ g + 1 by have := Finset.mem_range.1 hg; omega),
        map_zero, zero_mul, BRing.tmul_zero, BRing.tmul_zero])]
    rw [if_pos (by omega), if_pos (by omega), zero_add, hb,
      show b + 1 - (b + 1) = 0 by omega, show b + 1 + 1 - (b + 1) = 1 by omega,
      show b + 1 - b = 1 by omega]
    simp only [pow_zero, pow_one, one_mul]
    rw [xbar_zero', map_one, one_mul, xbar_one, neg_one_mul (-x K r₂ i.castSucc 1), neg_neg,
      show (xsFE i (hFi' : StepR (true, i) t w) 0 : ERing K i t hFi'.2) = 1 by
        rw [xsFE_eq, x_zero, map_one]]
    -- transport
    rw [← Fst_left_x i (hFi' : StepR (true, i) t w) hFi' 1, Fx_castSucc i hFi']
    have e2 : x K w i.castSucc 1 = x K w j.succ 1 := by rw [hadj]
    have e3 : x K r₂ i.castSucc 1 = x K r₂ j.succ 1 := by rw [hadj]
    rw [e2, e3, neg_one_mul, BRing.neg_tmul, BRing.sub_tmul,
      ← mul_one ((stepB K (false, i) w t hFi').right (x K w j.succ 1)), BRing.tmul_balance,
      BRing.tensor_left, BRing.tmul_mul_tmul, mul_one, one_mul, Fx_succ j hFj',
      BRing.add_tmul, ← mul_one ((stepB K (false, j) r₂ w hFj').right _), BRing.tmul_balance,
      BRing.tmul_add]
    have hx1 : xiStep K (false, j) r₂ w hFj' = eXi K j w hFj'.2 := rfl
    have hx2 : xiStep K (false, i) w t hFi' = eXi K i t hFi'.2 := rfl
    rw [hx1, hx2]
    abel
  · rw [if_neg hadj, add_zero] at hr
    rw [if_neg hadj]
    rw [Finset.sum_eq_single d (fun g hg hgd => by
      rw [if_neg (show ¬ r₁ i.castSucc + 1 ≤ g + 1 by have := Finset.mem_range.1 hg; omega),
        map_zero, zero_mul, BRing.tmul_zero, BRing.tmul_zero])
      (fun h => absurd (Finset.mem_range.2 (Nat.lt_succ_self d)) h)]
    rw [if_pos (by omega), show d + 1 - (r₁ i.castSucc + 1) = 0 by omega, Nat.sub_self, pow_zero,
      pow_zero, one_mul, one_mul, xbar_zero', map_one, one_mul, xsFE_eq, x_zero, map_one]

/-- **Cyclicity of crossings of distinct colours, left rotation** (KL III `eq_cyclic_cross-gen`,
relation `cycCrossL`): for `i ≠ j`, the left rotation of the upward crossing `E_j E_i → E_i E_j` is
`Γ_N` of the downward crossing `F_j F_i → F_i F_j` (6.9). -/
theorem rotCrossLW_eq_crossDn (hij : i ≠ j) :
    rotCrossLW K i j hFj hFi hFi' hFj' Y = locTwo (crossDn K j i hFj hFi hFi' hFj') Y := by
  refine BHom.ext fun z => ?_
  refine ext_two (Y := Y) (eXi K j t hFj.2) (eXi K i r₁ hFi.2) (stepF_spanned j hFj)
    (stepF_spanned i hFi) (rotCrossLW K i j hFj hFi hFi' hFj' Y).toAddHom
    (locTwo (crossDn K j i hFj hFi hFi' hFj') Y).toAddHom
    (BRing.tmul _ _ 1 (BRing.tmul _ _ (eXi K j w hFj'.2) 1)) (BRing.tmul _ _ (eXi K i t hFi'.2) 1)
    (fun z => ?_) (fun z => ?_) (fun z => ?_) (fun z => ?_) (fun y => ?_) z
  · rw [BHom.toAddHom_apply, BHom.toAddHom_apply, rotCrossLW_dotL i j hFj hFi hFi' hFj' Y hij]
  · rw [BHom.toAddHom_apply, BHom.toAddHom_apply, locTwo_crossDn_dotL i j hFj hFi hFi' hFj' Y hij]
  · rw [BHom.toAddHom_apply, BHom.toAddHom_apply, rotCrossLW_dotR i j hFj hFi hFi' hFj' Y hij]
  · rw [BHom.toAddHom_apply, BHom.toAddHom_apply, locTwo_crossDn_dotR i j hFj hFi hFi' hFj' Y hij]
  · rw [BHom.toAddHom_apply, BHom.toAddHom_apply, rotCrossLW_one i j hFj hFi hFi' hFj' Y hij,
      locTwo_crossDn_one i j hFj hFi hFi' hFj' Y hij]

/-- **The two rotations of an upward crossing differ by a sign for adjacent colours**: for
`i · j = -1`, `rotCrossR j i = - rotCrossL j i` on the path model, so the literal relation
`eq_cyclic_cross-gen` (`rotCrossR = downward crossing = rotCrossL`) fails for adjacent colours,
independently of the normalization of the downward crossing. -/
theorem rotCrossRW_eq_neg_rotCrossLW (hij : i ≠ j) (hadj : i.castSucc = j.succ ∨ j.castSucc = i.succ) :
    rotCrossRW K i j hFj hFi hFi' hFj' Y = -rotCrossLW K i j hFj hFi hFi' hFj' Y := by
  rw [rotCrossRW_eq_crossDn i j hFj hFi hFi' hFj' Y hij, if_pos hadj,
    rotCrossLW_eq_crossDn i j hFj hFi hFi' hFj' Y hij]

end RotL

end Categorification.Flag

end

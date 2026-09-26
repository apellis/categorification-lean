/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.GammaCurl

/-!
# Cyclicity of the crossing of equal colours (KL III `eq_cyclic_cross-gen`, `i = j`)

KL III, arXiv:0807.3250v1, Definition 3.1 (TeX label `eq_cyclic_cross-gen`, listed among the
`sl₂`-relations for `i = j`; `Categorification.KL3.Diagram.Rel.cycCrossR`, `cycCrossL`) and
Proposition 6.3 (Lauda's computation, arXiv:0803.3652).

For two downward strands of the same colour `i`, both rotations of the upward crossing
(`rotCrossRW`, `rotCrossLW` of `Categorification.Flag.GammaCyclic`) equal `Γ_N` of the downward
crossing (6.9) (`crossDn`, the divided difference `-∂`).

## Method

The rotations are compared with the downward crossing through their values at `1` and their
dot slides (`ext_two`), as for distinct colours, but now the dot slides of the upward crossing
have the correction `τ` (the identity for equal colours): the rotation `R(ψ)` of the crossing
satisfies `R(ψ)(ξ z) = ξ' R(ψ)(z) ∓ R(τ)(z)`, and `R(τ)` (the rotation of the identity) is the
identification `tauDn` of the two orders of `F_i F_i` (`rotTauRW_eq`).

* `capFE_xbar_vanish` : the double cap `F_i F_i E_i E_i → 1` vanishes on `ξ^{e₁} ⊗ ξ^{e₂}` below
  the top degree (the inner cap produces a dual elementary symmetric function of the middle
  region, which is transported across `E_i`, `Eleft_xbar_succ`);
* `rotCrossRW_same_one` : `R(ψ)(1 ⊗ 1 ⊗ y) = 0`;
* `rotCrossRW_same_eq` : **`rotCrossR i i = Γ_N` of the downward crossing** on `F_i F_i Y`;
* `rotCrossLW_same_eq` : the same for the left rotation.
-/

noncomputable section

open scoped TensorProduct

namespace Categorification.Flag

universe u

variable {K : Type u} [Field K] {m : ℕ}

attribute [local instance] rightAlgebra midAlgebra

/-! ### Generic whiskering lemmas -/

section GenericW

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]

/-- Left whiskering transports a dot slide with a correction term. -/
theorem whiskerLeft_mul_add (M : BRing A B) {N N' : BRing B C} (F G : BHom N N') (w : N.T)
    (w' : N'.T) (hF : ∀ z, F (w * z) = G z + w' * F z) (y : (M.tensor N).T) :
    BHom.whiskerLeft M F (BRing.tmul M N 1 w * y) =
      BHom.whiskerLeft M G y + BRing.tmul M N' 1 w' * BHom.whiskerLeft M F y := by
  refine BRing.induction_on (P := fun y => BHom.whiskerLeft M F (BRing.tmul M N 1 w * y) =
    BHom.whiskerLeft M G y + BRing.tmul M N' 1 w' * BHom.whiskerLeft M F y) y
    (by beta_reduce; simp only [mul_zero, BHom.map_zero, add_zero])
    (fun a b => ?_) (fun y y' hy hy' => ?_)
  · beta_reduce
    rw [BRing.tmul_mul_tmul, one_mul, BHom.whiskerLeft_tmul, BHom.whiskerLeft_tmul,
      BHom.whiskerLeft_tmul, BRing.tmul_mul_tmul, one_mul, hF, BRing.tmul_add]
  · beta_reduce at hy hy' ⊢
    rw [mul_add, BHom.map_add, hy, hy', BHom.map_add, BHom.map_add, mul_add]
    abel

end GenericW

/-! ### Dual elementary symmetric functions across `E_c` -/

section XbarTransport

variable (c : Fin m) {t r : Comp m} (h : StepR (true, c) t r)

/-- Across `E_c` (from `t` to `r = +_c t`): `x̄(r)_{c+1,k+1} = ξ x̄(t)_{c+1,k} + x̄(t)_{c+1,k+1}`
(KL III Proposition 5.3, eq. (5.33)). -/
theorem Eleft_xbar_succ (k : ℕ) :
    (stepB K (true, c) t r h).left (xbar K r c.succ (k + 1)) =
      xiStep K (true, c) t r h * (stepB K (true, c) t r h).right (xbar K t c.succ k) +
        (stepB K (true, c) t r h).right (xbar K t c.succ (k + 1)) := by
  have e1 : ∀ α, ((stepB K (true, c) t r h).left (xbar K r c.succ α) : ERing K c t h.2) =
      pL K (Sigma.fst : Gen t → Fin (m + 1)) (movedVar c t h.2) c.castSucc
        (xbarB K (moveLab (Sigma.fst : Gen t → Fin (m + 1)) (movedVar c t h.2) c.castSucc)
          c.succ α) := by
    intro α
    show eLeft K c t h.2 (hCast K h.1.symm (xbar K r c.succ α)) = _
    rw [hCast_xbar, eLeft, AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe]
    congr 1
    rw [AlgEquiv.symm_apply_eq, borelEquivH'_xbarB]
  have e2 : ∀ α, ((stepB K (true, c) t r h).right (xbar K t c.succ α) : ERing K c t h.2) =
      pR K (Sigma.fst : Gen t → Fin (m + 1)) (movedVar c t h.2)
        (xbarB K (Sigma.fst : Gen t → Fin (m + 1)) c.succ α) := by
    intro α
    show eRight K c t h.2 (xbar K t c.succ α) = _
    rw [eRight, AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, hEquiv_xbar]
  rw [e1, e2, e2]
  exact pL_xbarB_of_eq (k := K) (lab := (Sigma.fst : Gen t → Fin (m + 1)))
    (v₀ := movedVar c t h.2) (j' := c.castSucc) (castSucc_ne_succ' c).symm k

/-- Across `E_c` (from `s` to `r = +_c s`): `x̄(s)_{c,k+1} = ξ x̄(r)_{c,k} + x̄(r)_{c,k+1}`
(KL III Proposition 5.3, eq. (5.32)). -/
theorem Eright_xbar_succ {s r : Comp m} (h : StepR (true, c) s r) (k : ℕ) :
    (stepB K (true, c) s r h).right (xbar K s c.castSucc (k + 1)) =
      xiStep K (true, c) s r h * (stepB K (true, c) s r h).left (xbar K r c.castSucc k) +
        (stepB K (true, c) s r h).left (xbar K r c.castSucc (k + 1)) := by
  have e1 : ∀ α, ((stepB K (true, c) s r h).left (xbar K r c.castSucc α) : ERing K c s h.2) =
      pL K (Sigma.fst : Gen s → Fin (m + 1)) (movedVar c s h.2) c.castSucc
        (xbarB K (moveLab (Sigma.fst : Gen s → Fin (m + 1)) (movedVar c s h.2) c.castSucc)
          c.castSucc α) := by
    intro α
    show eLeft K c s h.2 (hCast K h.1.symm (xbar K r c.castSucc α)) = _
    rw [hCast_xbar, eLeft, AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe]
    congr 1
    rw [AlgEquiv.symm_apply_eq, borelEquivH'_xbarB]
  have e2 : ∀ α, ((stepB K (true, c) s r h).right (xbar K s c.castSucc α) : ERing K c s h.2) =
      pR K (Sigma.fst : Gen s → Fin (m + 1)) (movedVar c s h.2)
        (xbarB K (Sigma.fst : Gen s → Fin (m + 1)) c.castSucc α) := by
    intro α
    show eRight K c s h.2 (xbar K s c.castSucc α) = _
    rw [eRight, AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, hEquiv_xbar]
  rw [e2, e1, e1]
  exact pR_xbarB_of_move (k := K) (lab := (Sigma.fst : Gen s → Fin (m + 1)))
    (v₀ := movedVar c s h.2) (j' := c.castSucc) (castSucc_ne_succ' c) k

end XbarTransport

/-! ### The crossing of equal colours on monomials in the dots -/

section CrossMonomial

variable (c : Fin m) {t r₁ r₂ r₁' : Comp m} (h₁ : StepR (true, c) r₁ t)
  (h₂ : StepR (true, c) r₂ r₁) (h₁' : StepR (true, c) r₁' t) (h₂' : StepR (true, c) r₂ r₁')

/-- **KL III (6.8) for `i = j`**: `ψ(ξ^g ⊗ ξ^h) = ∑_{f<g} ξ^{g+h-1-f} ⊗ ξ^f - ∑_{f<h} ξ^{g+h-1-f} ⊗ ξ^f`. -/
theorem crossU_same_tmul_pow (g h : ℕ) :
    crossU K c c h₁ h₂ h₁' h₂' (BRing.tmul _ _ (eXi K c r₁ h₁.2 ^ g) (eXi K c r₂ h₂.2 ^ h)) =
      ∑ f ∈ Finset.range g, BRing.tmul (stepB K (true, c) r₁' t h₁') (stepB K (true, c) r₂ r₁' h₂')
          (eXi K c r₁' h₁'.2 ^ (g + h - 1 - f)) (eXi K c r₂ h₂'.2 ^ f) -
        ∑ f ∈ Finset.range h, BRing.tmul (stepB K (true, c) r₁' t h₁') (stepB K (true, c) r₂ r₁' h₂')
          (eXi K c r₁' h₁'.2 ^ (g + h - 1 - f)) (eXi K c r₂ h₂'.2 ^ f) := by
  have := (crossU_rules (K := K) c c h₁ h₂ h₁' h₂').eval2
    (MvPolynomial.X 0 ^ g * MvPolynomial.X 1 ^ h : MvPolynomial (Fin 2) K) 1
  rw [tauU_one, if_pos rfl, crossU_one, if_pos rfl, mul_zero, add_zero, mul_one,
    ddiff_X_pow_mul_X_pow (k := K) (show (0 : Fin 2) ≠ 1 by decide)] at this
  have hev : ∀ {A B C : Type u} [CommRing A] [Algebra K A] [CommRing B] [CommRing C]
      (L : BRing A B) (L' : BRing B C) (a : L.T) (b : L'.T) (p q : ℕ),
      ev2 K L L' a b (MvPolynomial.X 0 ^ p * MvPolynomial.X 1 ^ q) = BRing.tmul _ _ (a ^ p) (b ^ q) := by
    intro A B C _ _ _ _ L L' a b p q
    rw [map_mul, map_pow, map_pow,
      show ev2 K L L' a b (MvPolynomial.X 0) = BRing.tmul L L' a 1 from MvPolynomial.eval₂Hom_X' _ _ 0,
      show ev2 K L L' a b (MvPolynomial.X 1) = BRing.tmul L L' 1 b from MvPolynomial.eval₂Hom_X' _ _ 1,
      BRing.tmul_pow, BRing.tmul_pow, one_pow, one_pow, BRing.tmul_mul_tmul, mul_one, one_mul]
  rw [hev, map_sub, map_sum, map_sum] at this
  simp only [hev] at this
  rw [mul_one] at this
  exact this

theorem tauU_same_tmul_pow (g h : ℕ) :
    tauU K c c h₁ h₂ h₁' h₂' (BRing.tmul _ _ (eXi K c r₁ h₁.2 ^ g) (eXi K c r₂ h₂.2 ^ h)) =
      BRing.tmul (stepB K (true, c) r₁' t h₁') (stepB K (true, c) r₂ r₁' h₂')
        (eXi K c r₁' h₁'.2 ^ g) (eXi K c r₂ h₂'.2 ^ h) := by
  have hL : ∀ (g : ℕ) y, tauU K c c h₁ h₂ h₁' h₂' (BRing.tmul (stepB K (true, c) r₁ t h₁)
      (stepB K (true, c) r₂ r₁ h₂) (eXi K c r₁ h₁.2 ^ g) 1 * y) =
      BRing.tmul (stepB K (true, c) r₁' t h₁') (stepB K (true, c) r₂ r₁' h₂')
        (eXi K c r₁' h₁'.2 ^ g) 1 * tauU K c c h₁ h₂ h₁' h₂' y := by
    intro g
    induction g with
    | zero => intro y; simp only [pow_zero, ← BRing.one_eq, one_mul]
    | succ g ih =>
      intro y
      have := BHom.congr_apply (tauU_xiL (K := K) c c h₁ h₂ h₁' h₂')
        (BRing.tmul (stepB K (true, c) r₁ t h₁) (stepB K (true, c) r₂ r₁ h₂)
          (eXi K c r₁ h₁.2 ^ g) 1 * y)
      rw [BHom.comp_apply, BHom.comp_apply, BHom.mulB_apply, BHom.mulB_apply, ih, ← mul_assoc,
        ← mul_assoc, BRing.tmul_mul_tmul, BRing.tmul_mul_tmul] at this
      simp only [pow_succ']
      simpa only [mul_one, one_mul] using this
  have hR : ∀ (h : ℕ) y, tauU K c c h₁ h₂ h₁' h₂' (BRing.tmul (stepB K (true, c) r₁ t h₁)
      (stepB K (true, c) r₂ r₁ h₂) 1 (eXi K c r₂ h₂.2 ^ h) * y) =
      BRing.tmul (stepB K (true, c) r₁' t h₁') (stepB K (true, c) r₂ r₁' h₂')
        1 (eXi K c r₂ h₂'.2 ^ h) * tauU K c c h₁ h₂ h₁' h₂' y := by
    intro h
    induction h with
    | zero => intro y; simp only [pow_zero, ← BRing.one_eq, one_mul]
    | succ h ih =>
      intro y
      have := BHom.congr_apply (tauU_xiR (K := K) c c h₁ h₂ h₁' h₂')
        (BRing.tmul (stepB K (true, c) r₁ t h₁) (stepB K (true, c) r₂ r₁ h₂)
          1 (eXi K c r₂ h₂.2 ^ h) * y)
      rw [BHom.comp_apply, BHom.comp_apply, BHom.mulB_apply, BHom.mulB_apply, ih, ← mul_assoc,
        ← mul_assoc, BRing.tmul_mul_tmul, BRing.tmul_mul_tmul] at this
      simp only [pow_succ']
      simpa only [mul_one, one_mul] using this
  have e : BRing.tmul (stepB K (true, c) r₁ t h₁) (stepB K (true, c) r₂ r₁ h₂)
      (eXi K c r₁ h₁.2 ^ g) (eXi K c r₂ h₂.2 ^ h) =
      BRing.tmul _ _ (eXi K c r₁ h₁.2 ^ g) 1 * (BRing.tmul _ _ 1 (eXi K c r₂ h₂.2 ^ h) * 1) := by
    rw [mul_one, BRing.tmul_mul_tmul, mul_one, one_mul]
  rw [e, hL, hR, tauU_one, if_pos rfl, mul_one, BRing.tmul_mul_tmul, mul_one, one_mul]

end CrossMonomial

/-! ### Rotations of an arbitrary two-strand map -/

section RotGen

variable (i j : Fin m) {t r₁ r₂ w : Comp m} (hFj : StepR (false, j) r₁ t)
  (hFi : StepR (false, i) r₂ r₁) (hFi' : StepR (false, i) w t) (hFj' : StepR (false, j) r₂ w)
  {E : Type u} [CommRing E] (Y : BRing (H K r₂) E)

variable (K) in
/-- The right rotation of an arbitrary map `φ : E_j E_i → E_i E_j` (the five layers of
`rotCrossRW`, with `φ` in the middle). -/
def rotGen (φ : BHom ((stepB K (true, j) w r₂ hFj').tensor (stepB K (true, i) t w hFi'))
      ((stepB K (true, i) r₁ r₂ hFi).tensor (stepB K (true, j) t r₁ hFj))) :
    BHom ((stepB K (false, j) r₁ t hFj).tensor ((stepB K (false, i) r₂ r₁ hFi).tensor Y))
      ((stepB K (false, i) w t hFi').tensor ((stepB K (false, j) r₂ w hFj').tensor Y)) :=
  (capFEW K j (hFj : StepR (true, j) t r₁) hFj
    ((stepB K (false, i) w t hFi').tensor ((stepB K (false, j) r₂ w hFj').tensor Y))).comp
  ((BHom.whiskerLeft (stepB K (false, j) r₁ t hFj) (capFEW K i (hFi : StepR (true, i) r₁ r₂) hFi
    ((stepB K (true, j) t r₁ hFj).tensor ((stepB K (false, i) w t hFi').tensor
      ((stepB K (false, j) r₂ w hFj').tensor Y))))).comp
  ((BHom.whiskerLeft (stepB K (false, j) r₁ t hFj) (BHom.whiskerLeft (stepB K (false, i) r₂ r₁ hFi)
    (locTwo φ ((stepB K (false, i) w t hFi').tensor ((stepB K (false, j) r₂ w hFj').tensor Y))))).comp
  ((BHom.whiskerLeft (stepB K (false, j) r₁ t hFj) (BHom.whiskerLeft (stepB K (false, i) r₂ r₁ hFi)
    (BHom.whiskerLeft (stepB K (true, j) w r₂ hFj') (cupEFW K i (hFi' : StepR (true, i) t w) hFi'
      ((stepB K (false, j) r₂ w hFj').tensor Y))))).comp
  (BHom.whiskerLeft (stepB K (false, j) r₁ t hFj) (BHom.whiskerLeft (stepB K (false, i) r₂ r₁ hFi)
    (cupEFW K j (hFj' : StepR (true, j) w r₂) hFj' Y))))))

theorem rotCrossRW_eq_rotGen : rotCrossRW K i j hFj hFi hFi' hFj' Y =
    rotGen K i j hFj hFi hFi' hFj' Y (crossU K j i (hFj' : StepR (true, j) w r₂)
      (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, j) t r₁)) := rfl

variable (φ : BHom ((stepB K (true, j) w r₂ hFj').tensor (stepB K (true, i) t w hFi'))
      ((stepB K (true, i) r₁ r₂ hFi).tensor (stepB K (true, j) t r₁ hFj)))

/-- The part of `rotGen φ` after the crossing, applied to a dot on the left input strand of `φ`
(which comes from the outer cup): it becomes the dot of the right output strand `F_j`. -/
theorem rotGen_fwdL (z) :
    capFEW K j (hFj : StepR (true, j) t r₁) hFj _
      (BHom.whiskerLeft (stepB K (false, j) r₁ t hFj) (capFEW K i (hFi : StepR (true, i) r₁ r₂) hFi
        ((stepB K (true, j) t r₁ hFj).tensor ((stepB K (false, i) w t hFi').tensor
          ((stepB K (false, j) r₂ w hFj').tensor Y))))
      (BHom.whiskerLeft (stepB K (false, j) r₁ t hFj) (BHom.whiskerLeft (stepB K (false, i) r₂ r₁ hFi)
        (locTwo φ ((stepB K (false, i) w t hFi').tensor ((stepB K (false, j) r₂ w hFj').tensor Y))))
      (BHom.whiskerLeft (stepB K (false, j) r₁ t hFj) (BHom.whiskerLeft (stepB K (false, i) r₂ r₁ hFi)
        (BHom.whiskerLeft (stepB K (true, j) w r₂ hFj') (cupEFW K i (hFi' : StepR (true, i) t w) hFi'
          ((stepB K (false, j) r₂ w hFj').tensor Y))))
        (BRing.tmul (stepB K (false, j) r₁ t hFj) _ 1 (BRing.tmul (stepB K (false, i) r₂ r₁ hFi) _ 1
          (BRing.tmul (stepB K (true, j) w r₂ hFj') ((stepB K (false, j) r₂ w hFj').tensor Y)
            (eXi K j w hFj'.2) 1)) *
        BHom.whiskerLeft (stepB K (false, j) r₁ t hFj) (BHom.whiskerLeft (stepB K (false, i) r₂ r₁ hFi)
          (cupEFW K j (hFj' : StepR (true, j) w r₂) hFj' Y)) z)))) =
      BRing.tmul (stepB K (false, i) w t hFi') ((stepB K (false, j) r₂ w hFj').tensor Y) 1
        (BRing.tmul (stepB K (false, j) r₂ w hFj') Y (eXi K j w hFj'.2) 1) *
        rotGen K i j hFj hFi hFi' hFj' Y φ z := by
  simp only [rotGen, BHom.comp_apply]
  rw [whiskerLeft_mul_image _ _ _ (BRing.tmul (stepB K (false, i) r₂ r₁ hFi) _ 1
      (BRing.tmul (stepB K (true, j) w r₂ hFj') ((stepB K (false, j) r₂ w hFj').tensor Y) 1
        (BRing.tmul (stepB K (false, j) r₂ w hFj') Y (eXi K j w hFj'.2) 1)))
    (whiskerLeft_mul_image _ _ _ _ (fun y =>
      (cupEFW_slide j (hFj' : StepR (true, j) w r₂) hFj' Y y)))]
  rw [whiskerLeft_mul_right _ _ _ _ (whiskerLeft_mul_right _ _ _ _
      (whiskerLeft_mul_right _ _ _ _ (cupEFW_mul i _ _ _ _))),
    whiskerLeft_mul_right _ _ _ _ (whiskerLeft_mul_right _ _ _ _ (locTwo_mul_suffix' _ _ _)),
    whiskerLeft_mul_right _ _ _ _ (capFEW_mul i _ _ _ _), capFEW_mul]

/-- The part of `rotGen φ` after the inner cup, applied to a dot on the right input strand of `φ`
(which comes from the inner cup): it becomes the dot of the left output strand `F_i`. -/
theorem rotGen_fwdR (x) :
    capFEW K j (hFj : StepR (true, j) t r₁) hFj _
      (BHom.whiskerLeft (stepB K (false, j) r₁ t hFj) (capFEW K i (hFi : StepR (true, i) r₁ r₂) hFi
        ((stepB K (true, j) t r₁ hFj).tensor ((stepB K (false, i) w t hFi').tensor
          ((stepB K (false, j) r₂ w hFj').tensor Y))))
      (BHom.whiskerLeft (stepB K (false, j) r₁ t hFj) (BHom.whiskerLeft (stepB K (false, i) r₂ r₁ hFi)
        (locTwo φ ((stepB K (false, i) w t hFi').tensor ((stepB K (false, j) r₂ w hFj').tensor Y))))
      (BRing.tmul (stepB K (false, j) r₁ t hFj) _ 1 (BRing.tmul (stepB K (false, i) r₂ r₁ hFi) _ 1
          (BRing.tmul (stepB K (true, j) w r₂ hFj') _ 1
            (BRing.tmul (stepB K (true, i) t w hFi') ((stepB K (false, i) w t hFi').tensor
              ((stepB K (false, j) r₂ w hFj').tensor Y)) (eXi K i t hFi'.2) 1))) *
        BHom.whiskerLeft (stepB K (false, j) r₁ t hFj) (BHom.whiskerLeft (stepB K (false, i) r₂ r₁ hFi)
          (BHom.whiskerLeft (stepB K (true, j) w r₂ hFj') (cupEFW K i (hFi' : StepR (true, i) t w)
            hFi' ((stepB K (false, j) r₂ w hFj').tensor Y)))) x))) =
      BRing.tmul (stepB K (false, i) w t hFi') ((stepB K (false, j) r₂ w hFj').tensor Y)
        (eXi K i t hFi'.2) 1 *
      capFEW K j (hFj : StepR (true, j) t r₁) hFj _
      (BHom.whiskerLeft (stepB K (false, j) r₁ t hFj) (capFEW K i (hFi : StepR (true, i) r₁ r₂) hFi
        ((stepB K (true, j) t r₁ hFj).tensor ((stepB K (false, i) w t hFi').tensor
          ((stepB K (false, j) r₂ w hFj').tensor Y))))
      (BHom.whiskerLeft (stepB K (false, j) r₁ t hFj) (BHom.whiskerLeft (stepB K (false, i) r₂ r₁ hFi)
        (locTwo φ ((stepB K (false, i) w t hFi').tensor ((stepB K (false, j) r₂ w hFj').tensor Y))))
        (BHom.whiskerLeft (stepB K (false, j) r₁ t hFj) (BHom.whiskerLeft (stepB K (false, i) r₂ r₁ hFi)
          (BHom.whiskerLeft (stepB K (true, j) w r₂ hFj') (cupEFW K i (hFi' : StepR (true, i) t w)
            hFi' ((stepB K (false, j) r₂ w hFj').tensor Y)))) x))) := by
  rw [whiskerLeft_mul_image _ _ _ (BRing.tmul (stepB K (false, i) r₂ r₁ hFi) _ 1
      (BRing.tmul (stepB K (true, j) w r₂ hFj') _ 1
        (BRing.tmul (stepB K (true, i) t w hFi') ((stepB K (false, i) w t hFi').tensor
          ((stepB K (false, j) r₂ w hFj').tensor Y)) 1
          (BRing.tmul (stepB K (false, i) w t hFi') _ (eXi K i t hFi'.2) 1))))
    (whiskerLeft_mul_image _ _ _ _ (whiskerLeft_mul_image _ _ _ _ (fun y =>
      (cupEFW_slide i (hFi' : StepR (true, i) t w) hFi' _ y))))]
  rw [whiskerLeft_mul_right _ _ _ _ (whiskerLeft_mul_right _ _ _ _ (locTwo_mul_suffix' _ _ _)),
    whiskerLeft_mul_right _ _ _ _ (capFEW_mul i _ _ _ _), capFEW_mul]

/-- A dot on the left source strand `F_j` of `rotGen φ` slides across the outer cap to the right
output strand of `φ`. -/
theorem rotGen_bwdL (z) :
    rotGen K i j hFj hFi hFi' hFj' Y φ (BRing.tmul (stepB K (false, j) r₁ t hFj)
      ((stepB K (false, i) r₂ r₁ hFi).tensor Y) (eXi K j t hFj.2) 1 * z) =
    capFEW K j (hFj : StepR (true, j) t r₁) hFj _
      (BHom.whiskerLeft (stepB K (false, j) r₁ t hFj) (capFEW K i (hFi : StepR (true, i) r₁ r₂) hFi
        ((stepB K (true, j) t r₁ hFj).tensor ((stepB K (false, i) w t hFi').tensor
          ((stepB K (false, j) r₂ w hFj').tensor Y))))
      (BRing.tmul (stepB K (false, j) r₁ t hFj) _ 1 (BRing.tmul (stepB K (false, i) r₂ r₁ hFi) _ 1
          (BRing.tmul (stepB K (true, i) r₁ r₂ hFi) _ 1
            (BRing.tmul (stepB K (true, j) t r₁ hFj) ((stepB K (false, i) w t hFi').tensor
              ((stepB K (false, j) r₂ w hFj').tensor Y)) (eXi K j t hFj.2) 1))) *
      BHom.whiskerLeft (stepB K (false, j) r₁ t hFj) (BHom.whiskerLeft (stepB K (false, i) r₂ r₁ hFi)
        (locTwo φ ((stepB K (false, i) w t hFi').tensor ((stepB K (false, j) r₂ w hFj').tensor Y))))
      (BHom.whiskerLeft (stepB K (false, j) r₁ t hFj) (BHom.whiskerLeft (stepB K (false, i) r₂ r₁ hFi)
        (BHom.whiskerLeft (stepB K (true, j) w r₂ hFj') (cupEFW K i (hFi' : StepR (true, i) t w) hFi'
          ((stepB K (false, j) r₂ w hFj').tensor Y))))
        (BHom.whiskerLeft (stepB K (false, j) r₁ t hFj) (BHom.whiskerLeft (stepB K (false, i) r₂ r₁ hFi)
          (cupEFW K j (hFj' : StepR (true, j) w r₂) hFj' Y)) z)))) := by
  simp only [rotGen, BHom.comp_apply]
  rw [whiskerLeft_mul_left, whiskerLeft_mul_left, whiskerLeft_mul_left, whiskerLeft_mul_left,
    ← capFEW_slide j (hFj : StepR (true, j) t r₁) hFj _ _,
    ← whiskerLeft_mul_right _ _ _ _ (capFEW_mul i _ _ _ _)]

/-- A dot on the right source strand `F_i` of `rotGen φ` slides across the inner cap to the left
output strand of `φ`. -/
theorem rotGen_bwdR (z) :
    rotGen K i j hFj hFi hFi' hFj' Y φ (BRing.tmul (stepB K (false, j) r₁ t hFj)
      ((stepB K (false, i) r₂ r₁ hFi).tensor Y) 1
        (BRing.tmul (stepB K (false, i) r₂ r₁ hFi) Y (eXi K i r₁ hFi.2) 1) * z) =
    capFEW K j (hFj : StepR (true, j) t r₁) hFj _
      (BHom.whiskerLeft (stepB K (false, j) r₁ t hFj) (capFEW K i (hFi : StepR (true, i) r₁ r₂) hFi
        ((stepB K (true, j) t r₁ hFj).tensor ((stepB K (false, i) w t hFi').tensor
          ((stepB K (false, j) r₂ w hFj').tensor Y))))
      (BRing.tmul (stepB K (false, j) r₁ t hFj) _ 1 (BRing.tmul (stepB K (false, i) r₂ r₁ hFi) _ 1
          (BRing.tmul (stepB K (true, i) r₁ r₂ hFi) ((stepB K (true, j) t r₁ hFj).tensor
            ((stepB K (false, i) w t hFi').tensor ((stepB K (false, j) r₂ w hFj').tensor Y)))
            (eXi K i r₁ hFi.2) 1)) *
      BHom.whiskerLeft (stepB K (false, j) r₁ t hFj) (BHom.whiskerLeft (stepB K (false, i) r₂ r₁ hFi)
        (locTwo φ ((stepB K (false, i) w t hFi').tensor ((stepB K (false, j) r₂ w hFj').tensor Y))))
      (BHom.whiskerLeft (stepB K (false, j) r₁ t hFj) (BHom.whiskerLeft (stepB K (false, i) r₂ r₁ hFi)
        (BHom.whiskerLeft (stepB K (true, j) w r₂ hFj') (cupEFW K i (hFi' : StepR (true, i) t w) hFi'
          ((stepB K (false, j) r₂ w hFj').tensor Y))))
        (BHom.whiskerLeft (stepB K (false, j) r₁ t hFj) (BHom.whiskerLeft (stepB K (false, i) r₂ r₁ hFi)
          (cupEFW K j (hFj' : StepR (true, j) w r₂) hFj' Y)) z)))) := by
  simp only [rotGen, BHom.comp_apply]
  rw [whiskerLeft_mul_right _ _ _ _ (fun z => whiskerLeft_mul_left _ _ z _),
    whiskerLeft_mul_right _ _ _ _ (fun z => whiskerLeft_mul_left _ _ z _),
    whiskerLeft_mul_right _ _ _ _ (fun z => whiskerLeft_mul_left _ _ z _),
    whiskerLeft_mul_congr _ _ _ _ (capFEW_slide i (hFi : StepR (true, i) r₁ r₂) hFi _ _)]

end RotGen

/-! ### The right rotation for equal colours -/

section RotSame

variable (i : Fin m) {t r₁ r₂ w : Comp m} (hFj : StepR (false, i) r₁ t)
  (hFi : StepR (false, i) r₂ r₁) (hFi' : StepR (false, i) w t) (hFj' : StepR (false, i) r₂ w)
  {E : Type u} [CommRing E] (Y : BRing (H K r₂) E)

/-- **The two caps of the rotation vanish below the top degree.** -/
theorem rotCap_vanish (e₁ e₂ : ℕ) (he : e₁ + e₂ + 2 < r₁ i.succ + t i.succ)
    (W : ((stepB K (false, i) w t hFi').tensor ((stepB K (false, i) r₂ w hFj').tensor Y)).T) :
    capFEW K i (hFj : StepR (true, i) t r₁) hFj
      ((stepB K (false, i) w t hFi').tensor ((stepB K (false, i) r₂ w hFj').tensor Y))
      (BHom.whiskerLeft (stepB K (false, i) r₁ t hFj) (capFEW K i (hFi : StepR (true, i) r₁ r₂) hFi
        ((stepB K (true, i) t r₁ hFj).tensor ((stepB K (false, i) w t hFi').tensor
          ((stepB K (false, i) r₂ w hFj').tensor Y))))
        (BRing.tmul (stepB K (false, i) r₁ t hFj) _ 1 (BRing.tmul (stepB K (false, i) r₂ r₁ hFi) _ 1
          (BRing.tmul (stepB K (true, i) r₁ r₂ hFi) ((stepB K (true, i) t r₁ hFj).tensor
            ((stepB K (false, i) w t hFi').tensor ((stepB K (false, i) r₂ w hFj').tensor Y)))
            (eXi K i r₁ hFi.2 ^ e₁) (BRing.tmul (stepB K (true, i) t r₁ hFj) _
              (eXi K i t hFj.2 ^ e₂) W))))) = 0 := by
  have hcapR : ∀ (a : H K t) (mm : (stepB K (true, i) t r₁ hFj).T),
      capFEP K i (hFj : StepR (true, i) t r₁) hFj (BRing.tmul (stepB K (false, i) r₁ t hFj)
        (stepB K (true, i) t r₁ hFj) 1 ((stepB K (true, i) t r₁ hFj).right a * mm)) =
      a * capFEP K i (hFj : StepR (true, i) t r₁) hFj (BRing.tmul _ _ 1 mm) := by
    intro a mm
    rw [← capFEP_right, BRing.tensor_right, BRing.tmul_mul_tmul, one_mul]
  rw [BHom.whiskerLeft_tmul, capFEW_tmul, capFEP_one_xi_pow]
  split_ifs with h1
  · -- the inner cap is `(-1)^k x̄(r₁)_{i+1,k}`, `k = e₁ + 1 - r₁_{i+1}`
    rw [BRing.tensor_left, BRing.tmul_mul_tmul, one_mul, map_mul, map_pow, map_neg, map_one,
      capFEW_tmul]
    obtain ⟨k, hk⟩ : ∃ k, e₁ + 1 - r₁ i.succ = k := ⟨_, rfl⟩
    rw [hk]
    have hsign : ((-1 : (stepB K (true, i) t r₁ hFj).T) ^ k) = (stepB K (true, i) t r₁ hFj).right
        ((-1) ^ k) := by rw [map_pow, map_neg, map_one]
    rw [hsign, mul_assoc]
    rcases k with _ | k
    · rw [xbar_zero', map_one, one_mul, hcapR, capFEP_one_xi_pow, if_neg (by omega), mul_zero,
        map_zero, zero_mul]
    · have hxi : xiStep K (true, i) t r₁ hFj = eXi K i t hFj.2 := rfl
      rw [Eleft_xbar_succ, ← hxi, add_mul, mul_add, BRing.tmul_add, capFEP_add]
      have t1 : capFEP K i (hFj : StepR (true, i) t r₁) hFj (BRing.tmul (stepB K (false, i) r₁ t hFj)
          (stepB K (true, i) t r₁ hFj) 1 ((stepB K (true, i) t r₁ hFj).right ((-1) ^ (k + 1)) *
            (xiStep K (true, i) t r₁ hFj * (stepB K (true, i) t r₁ hFj).right (xbar K t i.succ k) *
              xiStep K (true, i) t r₁ hFj ^ e₂))) =
          ((-1) ^ (k + 1) * xbar K t i.succ k) * capFEP K i (hFj : StepR (true, i) t r₁) hFj
            (BRing.tmul _ _ 1 (xiStep K (true, i) t r₁ hFj ^ (e₂ + 1))) := by
        rw [← hcapR, map_mul, pow_succ']
        congr 2
        ring
      have t2 : capFEP K i (hFj : StepR (true, i) t r₁) hFj (BRing.tmul (stepB K (false, i) r₁ t hFj)
          (stepB K (true, i) t r₁ hFj) 1 ((stepB K (true, i) t r₁ hFj).right ((-1) ^ (k + 1)) *
            ((stepB K (true, i) t r₁ hFj).right (xbar K t i.succ (k + 1)) *
              xiStep K (true, i) t r₁ hFj ^ e₂))) =
          ((-1) ^ (k + 1) * xbar K t i.succ (k + 1)) * capFEP K i (hFj : StepR (true, i) t r₁) hFj
            (BRing.tmul _ _ 1 (xiStep K (true, i) t r₁ hFj ^ e₂)) := by
        rw [← hcapR, map_mul, mul_assoc]
      rw [t1, t2, hxi, capFEP_one_xi_pow, capFEP_one_xi_pow, if_neg (by omega), if_neg (by omega),
        mul_zero, mul_zero, add_zero, map_zero, zero_mul]
  · rw [map_zero, zero_mul, BRing.tmul_zero, BHom.map_zero]

variable (K) in
/-- The two caps after the crossing, as an additive map of the crossing's output. -/
def rotQ (W : ((stepB K (false, i) w t hFi').tensor ((stepB K (false, i) r₂ w hFj').tensor Y)).T) :
    BRing.TT (stepB K (true, i) r₁ r₂ hFi) (stepB K (true, i) t r₁ hFj) →+
      ((stepB K (false, i) w t hFi').tensor ((stepB K (false, i) r₂ w hFj').tensor Y)).T :=
  AddMonoidHom.mk' (fun u => capFEW K i (hFj : StepR (true, i) t r₁) hFj
      ((stepB K (false, i) w t hFi').tensor ((stepB K (false, i) r₂ w hFj').tensor Y))
      (BHom.whiskerLeft (stepB K (false, i) r₁ t hFj) (capFEW K i (hFi : StepR (true, i) r₁ r₂) hFi
        ((stepB K (true, i) t r₁ hFj).tensor ((stepB K (false, i) w t hFi').tensor
          ((stepB K (false, i) r₂ w hFj').tensor Y))))
        (BRing.tmul (stepB K (false, i) r₁ t hFj) _ 1 (BRing.tmul (stepB K (false, i) r₂ r₁ hFi) _ 1
          ((BRing.assoc (stepB K (true, i) r₁ r₂ hFi) (stepB K (true, i) t r₁ hFj)
            ((stepB K (false, i) w t hFi').tensor ((stepB K (false, i) r₂ w hFj').tensor Y))).hom
            (BRing.tmul _ _ u W))))))
    (fun u v => by
      simp only
      rw [BRing.add_tmul, BHom.map_add, BRing.tmul_add, BRing.tmul_add, BHom.map_add,
        BHom.map_add])

theorem rotQ_apply (W : ((stepB K (false, i) w t hFi').tensor
      ((stepB K (false, i) r₂ w hFj').tensor Y)).T) (u) :
    capFEW K i (hFj : StepR (true, i) t r₁) hFj
      ((stepB K (false, i) w t hFi').tensor ((stepB K (false, i) r₂ w hFj').tensor Y))
      (BHom.whiskerLeft (stepB K (false, i) r₁ t hFj) (capFEW K i (hFi : StepR (true, i) r₁ r₂) hFi
        ((stepB K (true, i) t r₁ hFj).tensor ((stepB K (false, i) w t hFi').tensor
          ((stepB K (false, i) r₂ w hFj').tensor Y))))
        (BRing.tmul (stepB K (false, i) r₁ t hFj) _ 1 (BRing.tmul (stepB K (false, i) r₂ r₁ hFi) _ 1
          ((BRing.assoc (stepB K (true, i) r₁ r₂ hFi) (stepB K (true, i) t r₁ hFj)
            ((stepB K (false, i) w t hFi').tensor ((stepB K (false, i) r₂ w hFj').tensor Y))).hom
            (BRing.tmul _ _ u W))))) = rotQ K i hFj hFi hFi' hFj' Y W u := rfl

/-- The two caps after the crossing vanish on `ξ^g ⊗ ξ^h` below the top degree. -/
theorem rotPsi_vanish (g h : ℕ) (hgh : g + h + 1 < r₁ i.succ + t i.succ)
    (W : ((stepB K (false, i) w t hFi').tensor ((stepB K (false, i) r₂ w hFj').tensor Y)).T) :
    capFEW K i (hFj : StepR (true, i) t r₁) hFj
      ((stepB K (false, i) w t hFi').tensor ((stepB K (false, i) r₂ w hFj').tensor Y))
      (BHom.whiskerLeft (stepB K (false, i) r₁ t hFj) (capFEW K i (hFi : StepR (true, i) r₁ r₂) hFi
        ((stepB K (true, i) t r₁ hFj).tensor ((stepB K (false, i) w t hFi').tensor
          ((stepB K (false, i) r₂ w hFj').tensor Y))))
        (BRing.tmul (stepB K (false, i) r₁ t hFj) _ 1 (BRing.tmul (stepB K (false, i) r₂ r₁ hFi) _ 1
          (locTwo (crossU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w)
            (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁))
            ((stepB K (false, i) w t hFi').tensor ((stepB K (false, i) r₂ w hFj').tensor Y))
            (BRing.tmul (stepB K (true, i) w r₂ hFj') _ (eXi K i w hFj'.2 ^ g)
              (BRing.tmul (stepB K (true, i) t w hFi') _ (eXi K i t hFi'.2 ^ h) W)))))) = 0 := by
  rw [locTwo_tmul, rotQ_apply, crossU_same_tmul_pow, map_sub, map_sum, map_sum,
    Finset.sum_eq_zero, Finset.sum_eq_zero, sub_zero]
  all_goals
    intro f hf
    have := Finset.mem_range.1 hf
    rw [← rotQ_apply, BRing.assoc_hom_tmul]
    exact rotCap_vanish i hFj hFi hFi' hFj' Y (g + h - 1 - f) f (by omega) W

variable (K) in
/-- The crossing followed by the two caps, as an additive map. -/
def rotP : ((stepB K (true, i) w r₂ hFj').tensor ((stepB K (true, i) t w hFi').tensor
      ((stepB K (false, i) w t hFi').tensor ((stepB K (false, i) r₂ w hFj').tensor Y)))).T →+
      ((stepB K (false, i) w t hFi').tensor ((stepB K (false, i) r₂ w hFj').tensor Y)).T :=
  AddMonoidHom.mk' (fun V => capFEW K i (hFj : StepR (true, i) t r₁) hFj
      ((stepB K (false, i) w t hFi').tensor ((stepB K (false, i) r₂ w hFj').tensor Y))
      (BHom.whiskerLeft (stepB K (false, i) r₁ t hFj) (capFEW K i (hFi : StepR (true, i) r₁ r₂) hFi
        ((stepB K (true, i) t r₁ hFj).tensor ((stepB K (false, i) w t hFi').tensor
          ((stepB K (false, i) r₂ w hFj').tensor Y))))
        (BRing.tmul (stepB K (false, i) r₁ t hFj) _ 1 (BRing.tmul (stepB K (false, i) r₂ r₁ hFi) _ 1
          (locTwo (crossU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w)
            (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁))
            ((stepB K (false, i) w t hFi').tensor ((stepB K (false, i) r₂ w hFj').tensor Y)) V)))))
    (fun u v => by
      simp only
      rw [BHom.map_add, BRing.tmul_add, BRing.tmul_add, BHom.map_add, BHom.map_add])

theorem addHom_neg_one_pow_mul {A B : Type*} [Ring A] [Ring B] (f : A →+ B) (n : ℕ) (a : A)
    (h : f a = 0) : f ((-1) ^ n * a) = 0 := by
  rcases neg_one_pow_eq_or A n with e | e <;> rw [e]
  · rw [one_mul, h]
  · rw [neg_one_mul, map_neg, h, neg_zero]

/-- **The right rotation of the crossing of equal colours vanishes at `1`.** -/
theorem rotCrossRW_same_one (y : Y.T) :
    rotCrossRW K i i hFj hFi hFi' hFj' Y (BRing.tmul _ _ 1 (BRing.tmul _ _ 1 y)) = 0 := by
  have hw : w i.succ = r₁ i.succ := by rw [← hFi'.1, ← hFj.1]
  have ht := hFj.2
  have hw1 := hFj'.2
  simp only [rotCrossRW, BHom.comp_apply]
  rw [BHom.whiskerLeft_tmul, BHom.whiskerLeft_tmul, BHom.whiskerLeft_tmul, BHom.whiskerLeft_tmul,
    BHom.whiskerLeft_tmul, BHom.whiskerLeft_tmul]
  show rotP K i hFj hFi hFi' hFj' Y _ = 0
  rw [cupEFW_apply'' i (hFj' : StepR (true, i) w r₂) hFj' Y y, BHom.map_sum, map_sum]
  refine Finset.sum_eq_zero fun g hg => ?_
  have hg' := Finset.mem_range.1 hg
  rw [BHom.map_neg_one_pow_mul]
  refine addHom_neg_one_pow_mul _ _ _ ?_
  rw [BHom.whiskerLeft_tmul, cupEFW_apply'' i (hFi' : StepR (true, i) t w) hFi' _, BRing.tmul_sum,
    map_sum]
  refine Finset.sum_eq_zero fun h hh => ?_
  have hh' := Finset.mem_range.1 hh
  rw [tmul_neg_one_pow_mul]
  refine addHom_neg_one_pow_mul _ _ _ ?_
  have hd1 := dEF_eq i (hFj' : StepR (true, i) w r₂)
  have hd2 := dEF_eq i (hFi' : StepR (true, i) t w)
  exact rotPsi_vanish i hFj hFi hFi' hFj' Y g h (by omega) _

/-- The two caps on `ξ^g ⊗ ξ^h` up to the top degree: `1` exactly in the top degree. -/
theorem rotCap_top (g h : ℕ) (hg : g + 1 ≤ r₁ i.succ) (hh : h + 1 ≤ t i.succ)
    (W : ((stepB K (false, i) w t hFi').tensor ((stepB K (false, i) r₂ w hFj').tensor Y)).T) :
    capFEW K i (hFj : StepR (true, i) t r₁) hFj
      ((stepB K (false, i) w t hFi').tensor ((stepB K (false, i) r₂ w hFj').tensor Y))
      (BHom.whiskerLeft (stepB K (false, i) r₁ t hFj) (capFEW K i (hFi : StepR (true, i) r₁ r₂) hFi
        ((stepB K (true, i) t r₁ hFj).tensor ((stepB K (false, i) w t hFi').tensor
          ((stepB K (false, i) r₂ w hFj').tensor Y))))
        (BRing.tmul (stepB K (false, i) r₁ t hFj) _ 1 (BRing.tmul (stepB K (false, i) r₂ r₁ hFi) _ 1
          (BRing.tmul (stepB K (true, i) r₁ r₂ hFi) ((stepB K (true, i) t r₁ hFj).tensor
            ((stepB K (false, i) w t hFi').tensor ((stepB K (false, i) r₂ w hFj').tensor Y)))
            (eXi K i r₁ hFi.2 ^ g) (BRing.tmul (stepB K (true, i) t r₁ hFj) _
              (eXi K i t hFj.2 ^ h) W))))) =
      if g + 1 = r₁ i.succ ∧ h + 1 = t i.succ then W else 0 := by
  rw [BHom.whiskerLeft_tmul, capFEW_tmul, capFEP_xi_pow i _ _ _ hg]
  by_cases h1 : g + 1 = r₁ i.succ
  · rw [if_pos h1, map_one, one_mul, capFEW_tmul, capFEP_xi_pow i _ _ _ hh]
    by_cases h2 : h + 1 = t i.succ
    · rw [if_pos h2, if_pos ⟨h1, h2⟩, map_one, one_mul]
    · rw [if_neg h2, if_neg (fun h => h2 h.2), map_zero, zero_mul]
  · rw [if_neg h1, if_neg (fun h => h1 h.1), map_zero, zero_mul, BRing.tmul_zero, BHom.map_zero]

variable (K) in
/-- The crossing `τ` (the identity for equal colours) followed by the two caps, additively. -/
def rotTP : ((stepB K (true, i) w r₂ hFj').tensor ((stepB K (true, i) t w hFi').tensor
      ((stepB K (false, i) w t hFi').tensor ((stepB K (false, i) r₂ w hFj').tensor Y)))).T →+
      ((stepB K (false, i) w t hFi').tensor ((stepB K (false, i) r₂ w hFj').tensor Y)).T :=
  AddMonoidHom.mk' (fun V => capFEW K i (hFj : StepR (true, i) t r₁) hFj
      ((stepB K (false, i) w t hFi').tensor ((stepB K (false, i) r₂ w hFj').tensor Y))
      (BHom.whiskerLeft (stepB K (false, i) r₁ t hFj) (capFEW K i (hFi : StepR (true, i) r₁ r₂) hFi
        ((stepB K (true, i) t r₁ hFj).tensor ((stepB K (false, i) w t hFi').tensor
          ((stepB K (false, i) r₂ w hFj').tensor Y))))
        (BRing.tmul (stepB K (false, i) r₁ t hFj) _ 1 (BRing.tmul (stepB K (false, i) r₂ r₁ hFi) _ 1
          (locTwo (tauU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w)
            (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁))
            ((stepB K (false, i) w t hFi').tensor ((stepB K (false, i) r₂ w hFj').tensor Y)) V)))))
    (fun u v => by
      simp only
      rw [BHom.map_add, BRing.tmul_add, BRing.tmul_add, BHom.map_add, BHom.map_add])

/-- **The rotation of the identity is the identity at `1`.** -/
theorem rotTau_one (y : Y.T) :
    rotGen K i i hFj hFi hFi' hFj' Y (tauU K i i (hFj' : StepR (true, i) w r₂)
      (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁))
      (BRing.tmul _ _ 1 (BRing.tmul _ _ 1 y)) = BRing.tmul _ _ 1 (BRing.tmul _ _ 1 y) := by
  have hw : w i.succ = r₁ i.succ := by rw [← hFi'.1, ← hFj.1]
  have ht := hFj.2
  have hw1 := hFj'.2
  have hd1 := dEF_eq i (hFj' : StepR (true, i) w r₂)
  have hd2 := dEF_eq i (hFi' : StepR (true, i) t w)
  simp only [rotGen, BHom.comp_apply]
  rw [BHom.whiskerLeft_tmul, BHom.whiskerLeft_tmul, BHom.whiskerLeft_tmul, BHom.whiskerLeft_tmul,
    BHom.whiskerLeft_tmul, BHom.whiskerLeft_tmul]
  show rotTP K i hFj hFi hFi' hFj' Y _ = _
  rw [cupEFW_apply'' i (hFj' : StepR (true, i) w r₂) hFj' Y y, BHom.map_sum, map_sum,
    Finset.sum_eq_single (dEF i (hFj' : StepR (true, i) w r₂))]
  · rw [BHom.map_neg_one_pow_mul, Nat.sub_self, pow_zero, one_mul, BHom.whiskerLeft_tmul,
      cupEFW_apply'' i (hFi' : StepR (true, i) t w) hFi' _, BRing.tmul_sum, map_sum,
      Finset.sum_eq_single (dEF i (hFi' : StepR (true, i) t w))]
    · rw [Nat.sub_self, pow_zero, one_mul, x_zero, map_one, one_mul, x_zero, map_one, one_mul]
      show capFEW K i (hFj : StepR (true, i) t r₁) hFj _ _ = _
      rw [locTwo_tmul, tauU_same_tmul_pow, BRing.assoc_hom_tmul, rotCap_top i hFj hFi hFi' hFj' Y
        _ _ (by omega) (by omega), if_pos ⟨by omega, by omega⟩]
    · intro h hh hhd
      have hh' := Finset.mem_range.1 hh
      rw [tmul_neg_one_pow_mul]
      refine addHom_neg_one_pow_mul _ _ _ ?_
      show capFEW K i (hFj : StepR (true, i) t r₁) hFj _ _ = 0
      rw [locTwo_tmul, tauU_same_tmul_pow, BRing.assoc_hom_tmul, rotCap_top i hFj hFi hFi' hFj' Y
        _ _ (by omega) (by omega), if_neg (by omega)]
    · intro h; exact absurd (Finset.mem_range.2 (Nat.lt_succ_self _)) h
  · intro g hg hgd
    have hg' := Finset.mem_range.1 hg
    rw [BHom.map_neg_one_pow_mul]
    refine addHom_neg_one_pow_mul _ _ _ ?_
    rw [BHom.whiskerLeft_tmul, cupEFW_apply'' i (hFi' : StepR (true, i) t w) hFi' _, BRing.tmul_sum,
      map_sum]
    refine Finset.sum_eq_zero fun h hh => ?_
    have hh' := Finset.mem_range.1 hh
    rw [tmul_neg_one_pow_mul]
    refine addHom_neg_one_pow_mul _ _ _ ?_
    show capFEW K i (hFj : StepR (true, i) t r₁) hFj _ _ = 0
    rw [locTwo_tmul, tauU_same_tmul_pow, BRing.assoc_hom_tmul, rotCap_top i hFj hFi hFi' hFj' Y
      _ _ (by omega) (by omega), if_neg (by omega)]
  · intro h; exact absurd (Finset.mem_range.2 (Nat.lt_succ_self _)) h

/-! #### Dot slides of the crossing, whiskered by the two downward strands -/

theorem wPsi_L (v) :
    BHom.whiskerLeft (stepB K (false, i) r₁ t hFj) (BHom.whiskerLeft (stepB K (false, i) r₂ r₁ hFi) (locTwo (crossU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)) ((stepB K (false, i) w t hFi').tensor ((stepB K (false, i) r₂ w hFj').tensor Y)))) (BRing.tmul (stepB K (false, i) r₁ t hFj) _ 1 (BRing.tmul (stepB K (false, i) r₂ r₁ hFi) _ 1 (BRing.tmul (stepB K (true, i) w r₂ hFj') ((stepB K (true, i) t w hFi').tensor ((stepB K (false, i) w t hFi').tensor ((stepB K (false, i) r₂ w hFj').tensor Y))) (eXi K i w hFj'.2) 1)) * v) =
      BHom.whiskerLeft (stepB K (false, i) r₁ t hFj) (BHom.whiskerLeft (stepB K (false, i) r₂ r₁ hFi) (locTwo (tauU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)) ((stepB K (false, i) w t hFi').tensor ((stepB K (false, i) r₂ w hFj').tensor Y)))) (v) + BRing.tmul (stepB K (false, i) r₁ t hFj) _ 1 (BRing.tmul (stepB K (false, i) r₂ r₁ hFi) _ 1 (BRing.tmul (stepB K (true, i) r₁ r₂ hFi) _ 1 (BRing.tmul (stepB K (true, i) t r₁ hFj) ((stepB K (false, i) w t hFi').tensor ((stepB K (false, i) r₂ w hFj').tensor Y)) (eXi K i t hFj.2) 1))) * BHom.whiskerLeft (stepB K (false, i) r₁ t hFj) (BHom.whiskerLeft (stepB K (false, i) r₂ r₁ hFi) (locTwo (crossU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)) ((stepB K (false, i) w t hFi').tensor ((stepB K (false, i) r₂ w hFj').tensor Y)))) (v) := by
  refine whiskerLeft_mul_add _ _ _ _ _ (fun u => whiskerLeft_mul_add _ _ _ _ _ (fun u' => ?_) u) v
  have := BHom.congr_apply ((crossU_rules (K := K) i i (hFj' : StepR (true, i) w r₂)
    (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)).locL
      ((stepB K (false, i) w t hFi').tensor ((stepB K (false, i) r₂ w hFj').tensor Y))) u'
  rw [BHom.comp_apply, BHom.add_apply, BHom.comp_apply, BHom.mulB_apply, BHom.mulB_apply] at this
  exact this

theorem wPsi_R (v) :
    BHom.whiskerLeft (stepB K (false, i) r₁ t hFj) (BHom.whiskerLeft (stepB K (false, i) r₂ r₁ hFi) (locTwo (crossU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)) ((stepB K (false, i) w t hFi').tensor ((stepB K (false, i) r₂ w hFj').tensor Y)))) (BRing.tmul (stepB K (false, i) r₁ t hFj) _ 1 (BRing.tmul (stepB K (false, i) r₂ r₁ hFi) _ 1 (BRing.tmul (stepB K (true, i) w r₂ hFj') _ 1 (BRing.tmul (stepB K (true, i) t w hFi') ((stepB K (false, i) w t hFi').tensor ((stepB K (false, i) r₂ w hFj').tensor Y)) (eXi K i t hFi'.2) 1))) * v) =
      -BHom.whiskerLeft (stepB K (false, i) r₁ t hFj) (BHom.whiskerLeft (stepB K (false, i) r₂ r₁ hFi) (locTwo (tauU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)) ((stepB K (false, i) w t hFi').tensor ((stepB K (false, i) r₂ w hFj').tensor Y)))) (v) + BRing.tmul (stepB K (false, i) r₁ t hFj) _ 1 (BRing.tmul (stepB K (false, i) r₂ r₁ hFi) _ 1 (BRing.tmul (stepB K (true, i) r₁ r₂ hFi) ((stepB K (true, i) t r₁ hFj).tensor ((stepB K (false, i) w t hFi').tensor ((stepB K (false, i) r₂ w hFj').tensor Y))) (eXi K i r₁ hFi.2) 1)) * BHom.whiskerLeft (stepB K (false, i) r₁ t hFj) (BHom.whiskerLeft (stepB K (false, i) r₂ r₁ hFi) (locTwo (crossU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)) ((stepB K (false, i) w t hFi').tensor ((stepB K (false, i) r₂ w hFj').tensor Y)))) (v) := by
  have hneg : ∀ u, BHom.whiskerLeft (stepB K (false, i) r₁ t hFj) (BHom.whiskerLeft (stepB K (false, i) r₂ r₁ hFi) (locTwo (-(tauU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁))) ((stepB K (false, i) w t hFi').tensor ((stepB K (false, i) r₂ w hFj').tensor Y)))) u =
      -BHom.whiskerLeft (stepB K (false, i) r₁ t hFj) (BHom.whiskerLeft (stepB K (false, i) r₂ r₁ hFi) (locTwo (tauU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)) ((stepB K (false, i) w t hFi').tensor ((stepB K (false, i) r₂ w hFj').tensor Y)))) (u) := by
    intro u; rw [locTwo_neg, BHom.whiskerLeft_neg, BHom.whiskerLeft_neg]; rfl
  rw [← hneg]
  refine whiskerLeft_mul_add _ _ _ _ _ (fun u => whiskerLeft_mul_add _ _ _ _ _ (fun u' => ?_) u) v
  have := BHom.congr_apply ((crossU_rules (K := K) i i (hFj' : StepR (true, i) w r₂)
    (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)).locR
      ((stepB K (false, i) w t hFi').tensor ((stepB K (false, i) r₂ w hFj').tensor Y))) u'
  rw [BHom.comp_apply, BHom.sub_apply, BHom.comp_apply, BHom.mulB_apply, BHom.mulB_apply] at this
  rw [this, locTwo_neg, BHom.neg_apply, sub_eq_add_neg]
  exact add_comm _ _

theorem wTau_L (v) :
    BHom.whiskerLeft (stepB K (false, i) r₁ t hFj) (BHom.whiskerLeft (stepB K (false, i) r₂ r₁ hFi) (locTwo (tauU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)) ((stepB K (false, i) w t hFi').tensor ((stepB K (false, i) r₂ w hFj').tensor Y)))) (BRing.tmul (stepB K (false, i) r₁ t hFj) _ 1 (BRing.tmul (stepB K (false, i) r₂ r₁ hFi) _ 1 (BRing.tmul (stepB K (true, i) w r₂ hFj') ((stepB K (true, i) t w hFi').tensor ((stepB K (false, i) w t hFi').tensor ((stepB K (false, i) r₂ w hFj').tensor Y))) (eXi K i w hFj'.2) 1)) * v) = BRing.tmul (stepB K (false, i) r₁ t hFj) _ 1 (BRing.tmul (stepB K (false, i) r₂ r₁ hFi) _ 1 (BRing.tmul (stepB K (true, i) r₁ r₂ hFi) ((stepB K (true, i) t r₁ hFj).tensor ((stepB K (false, i) w t hFi').tensor ((stepB K (false, i) r₂ w hFj').tensor Y))) (eXi K i r₁ hFi.2) 1)) * BHom.whiskerLeft (stepB K (false, i) r₁ t hFj) (BHom.whiskerLeft (stepB K (false, i) r₂ r₁ hFi) (locTwo (tauU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)) ((stepB K (false, i) w t hFi').tensor ((stepB K (false, i) r₂ w hFj').tensor Y)))) (v) := by
  refine whiskerLeft_mul_right _ _ _ _ (fun u => whiskerLeft_mul_right _ _ _ _ (fun u' => ?_) u) v
  have := BHom.congr_apply ((crossU_rules (K := K) i i (hFj' : StepR (true, i) w r₂)
    (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)).locτL
      ((stepB K (false, i) w t hFi').tensor ((stepB K (false, i) r₂ w hFj').tensor Y))) u'
  rw [BHom.comp_apply, BHom.comp_apply, BHom.mulB_apply, BHom.mulB_apply] at this
  exact this

theorem wTau_R (v) :
    BHom.whiskerLeft (stepB K (false, i) r₁ t hFj) (BHom.whiskerLeft (stepB K (false, i) r₂ r₁ hFi) (locTwo (tauU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)) ((stepB K (false, i) w t hFi').tensor ((stepB K (false, i) r₂ w hFj').tensor Y)))) (BRing.tmul (stepB K (false, i) r₁ t hFj) _ 1 (BRing.tmul (stepB K (false, i) r₂ r₁ hFi) _ 1 (BRing.tmul (stepB K (true, i) w r₂ hFj') _ 1 (BRing.tmul (stepB K (true, i) t w hFi') ((stepB K (false, i) w t hFi').tensor ((stepB K (false, i) r₂ w hFj').tensor Y)) (eXi K i t hFi'.2) 1))) * v) = BRing.tmul (stepB K (false, i) r₁ t hFj) _ 1 (BRing.tmul (stepB K (false, i) r₂ r₁ hFi) _ 1 (BRing.tmul (stepB K (true, i) r₁ r₂ hFi) _ 1 (BRing.tmul (stepB K (true, i) t r₁ hFj) ((stepB K (false, i) w t hFi').tensor ((stepB K (false, i) r₂ w hFj').tensor Y)) (eXi K i t hFj.2) 1))) * BHom.whiskerLeft (stepB K (false, i) r₁ t hFj) (BHom.whiskerLeft (stepB K (false, i) r₂ r₁ hFi) (locTwo (tauU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)) ((stepB K (false, i) w t hFi').tensor ((stepB K (false, i) r₂ w hFj').tensor Y)))) (v) := by
  refine whiskerLeft_mul_right _ _ _ _ (fun u => whiskerLeft_mul_right _ _ _ _ (fun u' => ?_) u) v
  have := BHom.congr_apply ((crossU_rules (K := K) i i (hFj' : StepR (true, i) w r₂)
    (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)).locτR
      ((stepB K (false, i) w t hFi').tensor ((stepB K (false, i) r₂ w hFj').tensor Y))) u'
  rw [BHom.comp_apply, BHom.comp_apply, BHom.mulB_apply, BHom.mulB_apply] at this
  exact this

theorem rotL2_mul (x) : BRing.tmul (stepB K (false, i) r₁ t hFj) _ 1 (BRing.tmul (stepB K (false, i) r₂ r₁ hFi) _ 1 (BRing.tmul (stepB K (true, i) w r₂ hFj') ((stepB K (true, i) t w hFi').tensor ((stepB K (false, i) w t hFi').tensor ((stepB K (false, i) r₂ w hFj').tensor Y))) (eXi K i w hFj'.2) 1)) * BHom.whiskerLeft (stepB K (false, i) r₁ t hFj) (BHom.whiskerLeft (stepB K (false, i) r₂ r₁ hFi) (BHom.whiskerLeft (stepB K (true, i) w r₂ hFj') (cupEFW K i (hFi' : StepR (true, i) t w) hFi' ((stepB K (false, i) r₂ w hFj').tensor Y)))) x = BHom.whiskerLeft (stepB K (false, i) r₁ t hFj) (BHom.whiskerLeft (stepB K (false, i) r₂ r₁ hFi) (BHom.whiskerLeft (stepB K (true, i) w r₂ hFj') (cupEFW K i (hFi' : StepR (true, i) t w) hFi' ((stepB K (false, i) r₂ w hFj').tensor Y)))) (BRing.tmul (stepB K (false, i) r₁ t hFj) _ 1 (BRing.tmul (stepB K (false, i) r₂ r₁ hFi) _ 1 (BRing.tmul (stepB K (true, i) w r₂ hFj') ((stepB K (false, i) r₂ w hFj').tensor Y) (eXi K i w hFj'.2) 1)) * x) :=
  (whiskerLeft_mul_right _ _ _ _ (fun z => whiskerLeft_mul_right _ _ _ _
    (fun z' => whiskerLeft_mul_left _ _ z' _) z) x).symm

/-! #### Dot slides of the rotations -/

/-- The rotation of `τ` moves the dot of `F_j` (left) to `F_i` (left). -/
theorem rotTau_dotL (z) :
    rotGen K i i hFj hFi hFi' hFj' Y (tauU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)) (BRing.tmul (stepB K (false, i) r₁ t hFj) ((stepB K (false, i) r₂ r₁ hFi).tensor Y) (eXi K i t hFj.2) 1 * z) =
      BRing.tmul (stepB K (false, i) w t hFi') ((stepB K (false, i) r₂ w hFj').tensor Y)
        (eXi K i t hFi'.2) 1 * rotGen K i i hFj hFi hFi' hFj' Y (tauU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)) z := by
  rw [rotGen_bwdL, ← wTau_R, rotGen_fwdR]
  rfl

/-- The rotation of `τ` moves the dot of `F_i` (right) to `F_j` (right). -/
theorem rotTau_dotR (z) :
    rotGen K i i hFj hFi hFi' hFj' Y (tauU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)) (BRing.tmul (stepB K (false, i) r₁ t hFj) ((stepB K (false, i) r₂ r₁ hFi).tensor Y) 1 (BRing.tmul (stepB K (false, i) r₂ r₁ hFi) Y (eXi K i r₁ hFi.2) 1) * z) =
      BRing.tmul (stepB K (false, i) w t hFi') ((stepB K (false, i) r₂ w hFj').tensor Y) 1
        (BRing.tmul (stepB K (false, i) r₂ w hFj') Y (eXi K i w hFj'.2) 1) * rotGen K i i hFj hFi hFi' hFj' Y (tauU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)) z := by
  rw [rotGen_bwdR, ← wTau_L, rotL2_mul, rotGen_fwdL]

/-- **The rotation of the crossing, left dot**: `R(ψ)(ξ_{F_j} z) = ξ'_{F_j} R(ψ)(z) - R(τ)(z)`. -/
theorem rotPsi_dotL (z) :
    rotGen K i i hFj hFi hFi' hFj' Y (crossU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)) (BRing.tmul (stepB K (false, i) r₁ t hFj) ((stepB K (false, i) r₂ r₁ hFi).tensor Y) (eXi K i t hFj.2) 1 * z) =
      BRing.tmul (stepB K (false, i) w t hFi') ((stepB K (false, i) r₂ w hFj').tensor Y) 1
        (BRing.tmul (stepB K (false, i) r₂ w hFj') Y (eXi K i w hFj'.2) 1) * rotGen K i i hFj hFi hFi' hFj' Y (crossU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)) z - rotGen K i i hFj hFi hFi' hFj' Y (tauU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)) z := by
  rw [rotGen_bwdL, eq_sub_of_add_eq' (wPsi_L i hFj hFi hFi' hFj' Y _).symm, BHom.map_sub,
    BHom.map_sub, rotL2_mul, rotGen_fwdL]
  rfl

/-- **The rotation of the crossing, right dot**: `R(ψ)(ξ_{F_i} z) = ξ'_{F_i} R(ψ)(z) + R(τ)(z)`. -/
theorem rotPsi_dotR (z) :
    rotGen K i i hFj hFi hFi' hFj' Y (crossU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)) (BRing.tmul (stepB K (false, i) r₁ t hFj) ((stepB K (false, i) r₂ r₁ hFi).tensor Y) 1 (BRing.tmul (stepB K (false, i) r₂ r₁ hFi) Y (eXi K i r₁ hFi.2) 1) * z) =
      BRing.tmul (stepB K (false, i) w t hFi') ((stepB K (false, i) r₂ w hFj').tensor Y)
        (eXi K i t hFi'.2) 1 * rotGen K i i hFj hFi hFi' hFj' Y (crossU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)) z + rotGen K i i hFj hFi hFi' hFj' Y (tauU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)) z := by
  rw [rotGen_bwdR, eq_sub_of_add_eq' (wPsi_R i hFj hFi hFi' hFj' Y _).symm, sub_neg_eq_add,
    BHom.map_add, BHom.map_add, rotGen_fwdR]
  rfl

/-! #### The downward crossing and its correction -/

theorem locTauDn_dotL (z) :
    locTwo (tauDn K i i hFj hFi hFi' hFj') Y (BRing.tmul (stepB K (false, i) r₁ t hFj) ((stepB K (false, i) r₂ r₁ hFi).tensor Y) (eXi K i t hFj.2) 1 * z) =
      BRing.tmul (stepB K (false, i) w t hFi') ((stepB K (false, i) r₂ w hFj').tensor Y)
        (eXi K i t hFi'.2) 1 * locTwo (tauDn K i i hFj hFi hFi' hFj') Y z := by
  have := BHom.congr_apply ((crossDn_rules (K := K) i i hFj hFi hFi' hFj').locτL Y) z
  rw [BHom.comp_apply, BHom.comp_apply, BHom.mulB_apply, BHom.mulB_apply, locTwo_neg,
    BHom.neg_apply, BHom.neg_apply, mul_neg, neg_inj] at this
  exact this

theorem locTauDn_dotR (z) :
    locTwo (tauDn K i i hFj hFi hFi' hFj') Y (BRing.tmul (stepB K (false, i) r₁ t hFj) ((stepB K (false, i) r₂ r₁ hFi).tensor Y) 1 (BRing.tmul (stepB K (false, i) r₂ r₁ hFi) Y (eXi K i r₁ hFi.2) 1) * z) =
      BRing.tmul (stepB K (false, i) w t hFi') ((stepB K (false, i) r₂ w hFj').tensor Y) 1
        (BRing.tmul (stepB K (false, i) r₂ w hFj') Y (eXi K i w hFj'.2) 1) * locTwo (tauDn K i i hFj hFi hFi' hFj') Y z := by
  have := BHom.congr_apply ((crossDn_rules (K := K) i i hFj hFi hFi' hFj').locτR Y) z
  rw [BHom.comp_apply, BHom.comp_apply, BHom.mulB_apply, BHom.mulB_apply, locTwo_neg,
    BHom.neg_apply, BHom.neg_apply, mul_neg, neg_inj] at this
  exact this

theorem locCrossDn_dotL (z) :
    locTwo (crossDn K i i hFj hFi hFi' hFj') Y (BRing.tmul (stepB K (false, i) r₁ t hFj) ((stepB K (false, i) r₂ r₁ hFi).tensor Y) (eXi K i t hFj.2) 1 * z) =
      -locTwo (tauDn K i i hFj hFi hFi' hFj') Y z + BRing.tmul (stepB K (false, i) w t hFi') ((stepB K (false, i) r₂ w hFj').tensor Y) 1
        (BRing.tmul (stepB K (false, i) r₂ w hFj') Y (eXi K i w hFj'.2) 1) * locTwo (crossDn K i i hFj hFi hFi' hFj') Y z := by
  have := BHom.congr_apply ((crossDn_rules (K := K) i i hFj hFi hFi' hFj').locL Y) z
  rw [BHom.comp_apply, BHom.add_apply, BHom.comp_apply, BHom.mulB_apply, BHom.mulB_apply,
    locTwo_neg, BHom.neg_apply] at this
  exact this

theorem locCrossDn_dotR (z) :
    locTwo (crossDn K i i hFj hFi hFi' hFj') Y (BRing.tmul (stepB K (false, i) r₁ t hFj) ((stepB K (false, i) r₂ r₁ hFi).tensor Y) 1 (BRing.tmul (stepB K (false, i) r₂ r₁ hFi) Y (eXi K i r₁ hFi.2) 1) * z) =
      BRing.tmul (stepB K (false, i) w t hFi') ((stepB K (false, i) r₂ w hFj').tensor Y)
        (eXi K i t hFi'.2) 1 * locTwo (crossDn K i i hFj hFi hFi' hFj') Y z + locTwo (tauDn K i i hFj hFi hFi' hFj') Y z := by
  have := BHom.congr_apply ((crossDn_rules (K := K) i i hFj hFi hFi' hFj').locR Y) z
  rw [BHom.comp_apply, BHom.sub_apply, BHom.comp_apply, BHom.mulB_apply, BHom.mulB_apply,
    locTwo_neg, BHom.neg_apply, sub_neg_eq_add] at this
  exact this

/-- **The rotation of the identity is the identity** (the correction terms agree):
`R(τ) = tauDn`. -/
theorem rotTau_eq : rotGen K i i hFj hFi hFi' hFj' Y (tauU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁)) = locTwo (tauDn K i i hFj hFi hFi' hFj') Y := by
  refine BHom.ext fun z => ?_
  refine ext_two (Y := Y) (eXi K i t hFj.2) (eXi K i r₁ hFi.2) (stepF_spanned i hFj)
    (stepF_spanned i hFi) (rotGen K i i hFj hFi hFi' hFj' Y (tauU K i i (hFj' : StepR (true, i) w r₂) (hFi' : StepR (true, i) t w) (hFi : StepR (true, i) r₁ r₂) (hFj : StepR (true, i) t r₁))).toAddHom (locTwo (tauDn K i i hFj hFi hFi' hFj') Y).toAddHom
    (BRing.tmul _ _ (eXi K i t hFi'.2) 1) (BRing.tmul _ _ 1 (BRing.tmul _ _ (eXi K i w hFj'.2) 1))
    (fun z => ?_) (fun z => ?_) (fun z => ?_) (fun z => ?_) (fun y => ?_) z
  · rw [BHom.toAddHom_apply, BHom.toAddHom_apply, rotTau_dotL]
  · rw [BHom.toAddHom_apply, BHom.toAddHom_apply, locTauDn_dotL]
  · rw [BHom.toAddHom_apply, BHom.toAddHom_apply, rotTau_dotR]
  · rw [BHom.toAddHom_apply, BHom.toAddHom_apply, locTauDn_dotR]
  · rw [BHom.toAddHom_apply, BHom.toAddHom_apply, rotTau_one, locTwo_tmul, ← BRing.one_eq,
      tauDn_one, if_pos rfl, BRing.one_eq (M := stepB K (false, i) w t hFi')
        (N := stepB K (false, i) r₂ w hFj'), BRing.assoc_hom_tmul]

/-- **Cyclicity of the crossing of equal colours, right rotation** (KL III `eq_cyclic_cross-gen`
for `i = j`, relation `cycCrossR`; Proposition 6.3): the right rotation of the upward crossing
`E_i E_i → E_i E_i` is `Γ_N` of the downward crossing (6.9) on `F_i F_i Y`. -/
theorem rotCrossRW_same_eq : rotCrossRW K i i hFj hFi hFi' hFj' Y = locTwo (crossDn K i i hFj hFi hFi' hFj') Y := by
  refine BHom.ext fun z => sub_eq_zero.1 ?_
  have key := ext_two (Y := Y) (eXi K i t hFj.2) (eXi K i r₁ hFi.2) (stepF_spanned i hFj)
    (stepF_spanned i hFi) ((rotCrossRW K i i hFj hFi hFi' hFj' Y).toAddHom - (locTwo (crossDn K i i hFj hFi hFi' hFj') Y).toAddHom) 0
    (BRing.tmul _ _ 1 (BRing.tmul _ _ (eXi K i w hFj'.2) 1)) (BRing.tmul _ _ (eXi K i t hFi'.2) 1)
    (fun z => ?_) (fun z => by rw [AddMonoidHom.zero_apply, AddMonoidHom.zero_apply, mul_zero])
    (fun z => ?_) (fun z => by rw [AddMonoidHom.zero_apply, AddMonoidHom.zero_apply, mul_zero])
    (fun y => ?_) z
  · rw [AddMonoidHom.sub_apply, BHom.toAddHom_apply, BHom.toAddHom_apply] at key
    rw [key, AddMonoidHom.zero_apply]
  · rw [AddMonoidHom.sub_apply, AddMonoidHom.sub_apply, BHom.toAddHom_apply, BHom.toAddHom_apply,
      BHom.toAddHom_apply, BHom.toAddHom_apply, rotCrossRW_eq_rotGen, rotPsi_dotL,
      locCrossDn_dotL, rotTau_eq, mul_sub]
    abel
  · rw [AddMonoidHom.sub_apply, AddMonoidHom.sub_apply, BHom.toAddHom_apply, BHom.toAddHom_apply,
      BHom.toAddHom_apply, BHom.toAddHom_apply, rotCrossRW_eq_rotGen, rotPsi_dotR,
      locCrossDn_dotR, rotTau_eq, mul_sub]
    abel
  · rw [AddMonoidHom.sub_apply, BHom.toAddHom_apply, BHom.toAddHom_apply, AddMonoidHom.zero_apply,
      rotCrossRW_same_one, locTwo_tmul, ← BRing.one_eq, crossDn_one, if_pos rfl, BRing.zero_tmul,
      BHom.map_zero, sub_zero]

end RotSame

end Categorification.Flag

end

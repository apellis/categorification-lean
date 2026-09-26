/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.GammaWhisker

/-!
# `Γ_N` of the upward crossing for all pairs of colours (KL III (6.8))

KL III, arXiv:0807.3250v1, §6.1.2, Definition 6.2, eq. (6.8) (TeX label `eq_gamma_dcross`).

`crossU K c d … : Γ(E_c E_d 1) → Γ(E_d E_c 1)` is `Γ_N` of the upward crossing for arbitrary
colours `c`, `d` on the path model, assembled from the four cases of (6.8):

* `c = d`: the divided difference (`crossEEP2`, the version of `crossEEP` in which the middle
  regions of source and target are stored separately);
* `d = c + 1`: `crossAdjNF`; `c = d + 1`: `crossAdjFN`; otherwise `crossFarP`.

We record the rules that determine it on all polynomials in the dots (`Categorification.Flag.
eval_twisted`): with `ξ_L`, `ξ_R` the dots of the source and `ξ'_L`, `ξ'_R` those of the target,
and `τ` (`tauU`) the identification of source and target if `c = d` (zero otherwise),

* `crossU_xiL` : `ψ ∘ ξ_L = τ + ξ'_R ∘ ψ`, `crossU_xiR` : `ψ ∘ ξ_R = ξ'_L ∘ ψ − τ`;
* `tauU_xiL`, `tauU_xiR` : `τ` commutes with the dots;
* `crossU_one` : `ψ(1) = 0` if `c = d`, `ξ'_R − ξ'_L` if `c = d + 1`, and `1` otherwise;
  `tauU_one`.
-/

noncomputable section

namespace Categorification.Flag

universe u

variable {K : Type u} [Field K] {m : ℕ}

attribute [local instance] rightAlgebra midAlgebra jointAlgebra

/-! ### The same-colour crossing with separate middle regions -/

section EE2

variable (i : Fin m) {t r₁ r₂ r₁' : Comp m} (h₁ : StepR (true, i) r₁ t)
  (h₂ : StepR (true, i) r₂ r₁) (h₁' : StepR (true, i) r₁' t) (h₂' : StepR (true, i) r₂ r₁')

theorem crossEE_one' {V : Type*} [Fintype V] [DecidableEq V] {J : Type*} [Fintype J]
    [DecidableEq J] (lab : V → J) (v₁ v₂ : V) (j₂ : J) (hne : v₁ ≠ v₂) (hj : lab v₁ ≠ j₂) :
    crossEE K lab v₁ v₂ j₂ hne hj ((1 : BorelRing K (splitLab (moveLab lab v₂ j₂) v₁)) ⊗ₜ[BorelRing K
      (moveLab lab v₂ j₂)] (1 : BorelRing K (splitLab lab v₂))) = 0 := by
  have h := crossEE_xi (k := K) lab v₁ v₂ j₂ hne hj 0 0
  simp only [pow_zero, Finset.range_zero, Finset.sum_empty, sub_self] at h
  exact h

variable (K) in
/-- `Γ` of the crossing of two strands coloured `i`, from `Γ(E_i E_i 1)` with middle region `r₁`
to `Γ(E_i E_i 1)` with middle region `r₁'` (both models on the variables `Gen r₂`, with the
moved variables `⟨i+1, 0⟩` and `⟨i+1, 1⟩`). -/
def crossEEP2 : BHom (TwoP (K := K) h₁ h₂) (TwoP (K := K) h₁' h₂') :=
  transportBHom (eeEquiv K i i h₁ h₂ (eeVar i h₁ h₂) (eeVar_hv i h₁ h₂))
    (eeEquiv K i i h₁' h₂' (eeVar i h₁' h₂') (eeVar_hv i h₁' h₂'))
    (crossEE K (Sigma.fst : Gen r₂ → Fin (m + 1)) (eeVar i h₁ h₂) (movedVar i r₂ h₂.2)
      i.castSucc (ee_ne i h₂ _ (eeVar_hv i h₁ h₂)) (ee_hj i h₂ _ (eeVar_hv i h₁ h₂)))
    (crossEE_add _ _ _ _ _ _)
    (fun a y => by
      rw [eeEquiv_left, crossEE_left, eeEquiv_left]
      all_goals rfl)
    (fun c y => by
      rw [eeEquiv_right, crossEE_right _ _ _ _ _ _ ((ee_lab i h₂ _ (eeVar_hv i h₁ h₂)).trans rfl),
        eeEquiv_right])

variable (K) in
/-- The identification of `Γ(E_i E_i 1)` with middle regions `r₁` and `r₁'`. -/
def tauEE : BHom (TwoP (K := K) h₁ h₂) (TwoP (K := K) h₁' h₂') :=
  transportBHom (eeEquiv K i i h₁ h₂ (eeVar i h₁ h₂) (eeVar_hv i h₁ h₂))
    (eeEquiv K i i h₁' h₂' (eeVar i h₁' h₂') (eeVar_hv i h₁' h₂')) id (fun _ _ => rfl)
    (fun a y => by
      simp only [id]
      rw [eeEquiv_left, eeEquiv_left]
      all_goals rfl)
    (fun c y => by
      simp only [id]
      rw [eeEquiv_right, eeEquiv_right])

theorem crossEEP2_apply (y : (TwoP (K := K) h₁ h₂).T) :
    eeEquiv K i i h₁' h₂' (eeVar i h₁' h₂') (eeVar_hv i h₁' h₂') (crossEEP2 K i h₁ h₂ h₁' h₂' y) =
      crossEE K (Sigma.fst : Gen r₂ → Fin (m + 1)) (eeVar i h₁ h₂) (movedVar i r₂ h₂.2)
        i.castSucc (ee_ne i h₂ _ (eeVar_hv i h₁ h₂)) (ee_hj i h₂ _ (eeVar_hv i h₁ h₂))
        (eeEquiv K i i h₁ h₂ (eeVar i h₁ h₂) (eeVar_hv i h₁ h₂) y) := by
  unfold crossEEP2
  exact transportBHom_apply (M := TwoP (K := K) h₁ h₂) (N := TwoP (K := K) h₁' h₂') _ _ _ _ _ _ y

theorem tauEE_apply (y : (TwoP (K := K) h₁ h₂).T) :
    eeEquiv K i i h₁' h₂' (eeVar i h₁' h₂') (eeVar_hv i h₁' h₂') (tauEE K i h₁ h₂ h₁' h₂' y) =
      eeEquiv K i i h₁ h₂ (eeVar i h₁ h₂) (eeVar_hv i h₁ h₂) y := by
  unfold tauEE
  exact transportBHom_apply (M := TwoP (K := K) h₁ h₂) (N := TwoP (K := K) h₁' h₂') _ _ _ _ _ _ y

theorem crossEEP2_xiL :
    (crossEEP2 K i h₁ h₂ h₁' h₂').comp (BHom.mulB (BRing.tmul _ _ (eXi K i r₁ h₁.2) 1)) =
      tauEE K i h₁ h₂ h₁' h₂' + (BHom.mulB (BRing.tmul _ _ 1 (eXi K i r₂ h₂'.2))).comp
        (crossEEP2 K i h₁ h₂ h₁' h₂') := by
  refine BHom.ext fun y => ?_
  apply (eeEquiv K i i h₁' h₂' (eeVar i h₁' h₂') (eeVar_hv i h₁' h₂')).injective
  rw [BHom.comp_apply, crossEEP2_apply, BHom.mulB_apply, map_mul, eeEquiv_xi_left,
    crossEE_xi_left, BHom.add_apply, BHom.comp_apply, BHom.mulB_apply, map_add, map_mul,
    tauEE_apply, crossEEP2_apply, eeEquiv_xi_right]

theorem crossEEP2_xiR :
    (crossEEP2 K i h₁ h₂ h₁' h₂').comp (BHom.mulB (BRing.tmul _ _ 1 (eXi K i r₂ h₂.2))) =
      (BHom.mulB (BRing.tmul _ _ (eXi K i r₁' h₁'.2) 1)).comp (crossEEP2 K i h₁ h₂ h₁' h₂') -
        tauEE K i h₁ h₂ h₁' h₂' := by
  refine BHom.ext fun y => ?_
  apply (eeEquiv K i i h₁' h₂' (eeVar i h₁' h₂') (eeVar_hv i h₁' h₂')).injective
  rw [BHom.comp_apply, crossEEP2_apply, BHom.mulB_apply, map_mul, eeEquiv_xi_right,
    crossEE_xi_right, BHom.sub_apply, BHom.comp_apply, BHom.mulB_apply, map_sub, map_mul,
    tauEE_apply, crossEEP2_apply, eeEquiv_xi_left]
  all_goals rfl

theorem tauEE_xiL :
    (tauEE K i h₁ h₂ h₁' h₂').comp (BHom.mulB (BRing.tmul _ _ (eXi K i r₁ h₁.2) 1)) =
      (BHom.mulB (BRing.tmul _ _ (eXi K i r₁' h₁'.2) 1)).comp (tauEE K i h₁ h₂ h₁' h₂') := by
  refine BHom.ext fun y => ?_
  apply (eeEquiv K i i h₁' h₂' (eeVar i h₁' h₂') (eeVar_hv i h₁' h₂')).injective
  rw [BHom.comp_apply, tauEE_apply, BHom.mulB_apply, map_mul, eeEquiv_xi_left, BHom.comp_apply,
    BHom.mulB_apply, map_mul, tauEE_apply, eeEquiv_xi_left]
  all_goals rfl

theorem tauEE_xiR :
    (tauEE K i h₁ h₂ h₁' h₂').comp (BHom.mulB (BRing.tmul _ _ 1 (eXi K i r₂ h₂.2))) =
      (BHom.mulB (BRing.tmul _ _ 1 (eXi K i r₂ h₂'.2))).comp (tauEE K i h₁ h₂ h₁' h₂') := by
  refine BHom.ext fun y => ?_
  apply (eeEquiv K i i h₁' h₂' (eeVar i h₁' h₂') (eeVar_hv i h₁' h₂')).injective
  rw [BHom.comp_apply, tauEE_apply, BHom.mulB_apply, map_mul, eeEquiv_xi_right, BHom.comp_apply,
    BHom.mulB_apply, map_mul, tauEE_apply, eeEquiv_xi_right]

theorem crossEEP2_one : crossEEP2 K i h₁ h₂ h₁' h₂' 1 = 0 := by
  apply (eeEquiv K i i h₁' h₂' (eeVar i h₁' h₂') (eeVar_hv i h₁' h₂')).injective
  rw [crossEEP2_apply, map_one, Algebra.TensorProduct.one_def, crossEE_one', map_zero]

theorem tauEE_one : tauEE K i h₁ h₂ h₁' h₂' 1 = 1 := by
  apply (eeEquiv K i i h₁' h₂' (eeVar i h₁' h₂') (eeVar_hv i h₁' h₂')).injective
  rw [tauEE_apply, map_one, map_one]

end EE2

/-! ### Values at `1` of the other crossings -/

section One

theorem crossFarP_one (i j : Fin m) (hij : i ≠ j) (hf₁ : i.succ ≠ j.castSucc)
    (hf₂ : j.succ ≠ i.castSucc) {t r₁ r₂ r₁' : Comp m} (h₁ : StepR (true, i) r₁ t)
    (h₂ : StepR (true, j) r₂ r₁) (h₁' : StepR (true, j) r₁' t) (h₂' : StepR (true, i) r₂ r₁') :
    crossFarP K i j hij hf₁ hf₂ h₁ h₂ h₁' h₂' 1 = 1 := by
  apply (eeEquiv K j i h₁' h₂' (movedVar j r₂ h₂.2) (far_hv j i hij.symm h₂' h₂)).injective
  rw [crossFarP_apply, map_one, map_one]
  simp only [crossFar, map_one]

theorem crossNFβ_one {V : Type*} [Fintype V] [DecidableEq V] {J : Type*} [Fintype J]
    [DecidableEq J] (lab : V → J) (v w : V) (α β : J) (hβ : lab v = β) (hw : lab w ≠ β)
    (hα : lab w ≠ α) : crossNFβ (K := K) lab v w α β hβ hw hα
      ((1 : BorelRing K (splitLab (moveLab lab w β) v)) ⊗ₜ[BorelRing K (moveLab lab w β)]
        (1 : BorelRing K (splitLab lab w))) =
      (1 : BorelRing K (splitLab (moveLab lab v α) w)) ⊗ₜ[BorelRing K (moveLab lab v α)]
        (1 : BorelRing K (splitLab lab v)) := by
  subst hβ
  have h := crossNF_xi (k := K) α hw hα 0 0
  simp only [pow_zero] at h
  exact h

theorem crossFNβ_one {V : Type*} [Fintype V] [DecidableEq V] {J : Type*} [Fintype J]
    [DecidableEq J] (lab : V → J) (v w : V) (α β : J) (hβ : lab v = β) (hw : lab w ≠ β)
    (hα : lab w ≠ α) : crossFNβ (K := K) lab v w α β hβ hw hα
      ((1 : BorelRing K (splitLab (moveLab lab v α) w)) ⊗ₜ[BorelRing K (moveLab lab v α)]
        (1 : BorelRing K (splitLab lab v))) =
      (xi K (moveLab lab w β) v ⊗ₜ[BorelRing K (moveLab lab w β)]
        (1 : BorelRing K (splitLab lab w))) - 1 ⊗ₜ xi K lab w := by
  subst hβ
  have h := crossFN_xi (k := K) α hw hα 0 0
  simp only [pow_zero, zero_add, pow_one] at h
  exact h

theorem crossAdjNF_one (i j : Fin m) (hadj : j.castSucc = i.succ) {t r₁ r₂ r₁' : Comp m}
    (h₁ : StepR (true, i) r₁ t) (h₂ : StepR (true, j) r₂ r₁) (h₁' : StepR (true, j) r₁' t)
    (h₂' : StepR (true, i) r₂ r₁') : crossAdjNF K i j hadj h₁ h₂ h₁' h₂' 1 = 1 := by
  apply (eeEquiv K j i h₁' h₂' (movedVar j r₂ h₂.2) (far_hv j i (adj_ne hadj).symm h₂' h₂)).injective
  rw [crossAdjNF_apply, map_one, map_one, Algebra.TensorProduct.one_def, crossNFβ_one,
    ← Algebra.TensorProduct.one_def]

theorem crossAdjFN_one (i j : Fin m) (hadj : j.castSucc = i.succ) {t r₁ r₂ r₁' : Comp m}
    (h₁ : StepR (true, i) r₁ t) (h₂ : StepR (true, j) r₂ r₁) (h₁' : StepR (true, j) r₁' t)
    (h₂' : StepR (true, i) r₂ r₁') : crossAdjFN K i j hadj h₁ h₂ h₁' h₂' 1 =
      BRing.tmul _ _ 1 (eXi K j r₂ h₂.2) - BRing.tmul _ _ (eXi K i r₁ h₁.2) 1 := by
  apply (eeEquiv K i j h₁ h₂ (movedVar i r₂ h₂'.2) (far_hv i j (adj_ne hadj) h₂ h₂')).injective
  rw [crossAdjFN_apply, map_one, Algebra.TensorProduct.one_def, crossFNβ_one, map_sub,
    eeEquiv_xi_left, eeEquiv_xi_right, neg_sub]

end One

/-! ### The uniform crossing -/

section Uniform

theorem BHom.zero_add' {A B : Type u} [CommRing A] [CommRing B] {M N : BRing A B}
    (φ : BHom M N) : 0 + φ = φ := BHom.ext fun _ => zero_add _

theorem BHom.sub_zero' {A B : Type u} [CommRing A] [CommRing B] {M N : BRing A B}
    (φ : BHom M N) : φ - 0 = φ := BHom.ext fun _ => sub_zero _

variable (K) in
/-- **`Γ_N` of the upward crossing `E_c E_d 1 → E_d E_c 1`** for arbitrary colours
(KL III (6.8)). -/
def crossU (c d : Fin m) {t r₁ r₂ r₁' : Comp m} (h₁ : StepR (true, c) r₁ t)
    (h₂ : StepR (true, d) r₂ r₁) (h₁' : StepR (true, d) r₁' t) (h₂' : StepR (true, c) r₂ r₁') :
    BHom (TwoP (K := K) h₁ h₂) (TwoP (K := K) h₁' h₂') :=
  if hcd : c = d then by subst hcd; exact crossEEP2 K c h₁ h₂ h₁' h₂'
  else if hadj : d.castSucc = c.succ then crossAdjNF K c d hadj h₁ h₂ h₁' h₂'
  else if hadj' : c.castSucc = d.succ then crossAdjFN K d c hadj' h₁' h₂' h₁ h₂
  else crossFarP K c d hcd (Ne.symm hadj) (Ne.symm hadj') h₁ h₂ h₁' h₂'

variable (K) in
/-- The identification of source and target used in the dot slides of `crossU` (zero unless
`c = d`). -/
def tauU (c d : Fin m) {t r₁ r₂ r₁' : Comp m} (h₁ : StepR (true, c) r₁ t)
    (h₂ : StepR (true, d) r₂ r₁) (h₁' : StepR (true, d) r₁' t) (h₂' : StepR (true, c) r₂ r₁') :
    BHom (TwoP (K := K) h₁ h₂) (TwoP (K := K) h₁' h₂') :=
  if hcd : c = d then by subst hcd; exact tauEE K c h₁ h₂ h₁' h₂' else 0

variable (c d : Fin m) {t r₁ r₂ r₁' : Comp m} (h₁ : StepR (true, c) r₁ t)
  (h₂ : StepR (true, d) r₂ r₁) (h₁' : StepR (true, d) r₁' t) (h₂' : StepR (true, c) r₂ r₁')

/-- **Dot slide, left strand**: `ψ ∘ ξ_L = τ + ξ'_R ∘ ψ`. -/
theorem crossU_xiL :
    (crossU K c d h₁ h₂ h₁' h₂').comp (BHom.mulB (BRing.tmul _ _ (eXi K c r₁ h₁.2) 1)) =
      tauU K c d h₁ h₂ h₁' h₂' + (BHom.mulB (BRing.tmul _ _ 1 (eXi K c r₂ h₂'.2))).comp
        (crossU K c d h₁ h₂ h₁' h₂') := by
  by_cases hcd : c = d
  · subst hcd
    simp only [crossU, tauU, dif_pos rfl]
    exact crossEEP2_xiL (K := K) c h₁ h₂ h₁' h₂'
  · simp only [crossU, tauU, dif_neg hcd]
    rw [BHom.zero_add']
    by_cases hadj : d.castSucc = c.succ
    · rw [dif_pos hadj]; exact crossAdjNF_xiL (K := K) c d hadj h₁ h₂ h₁' h₂'
    · rw [dif_neg hadj]
      by_cases hadj' : c.castSucc = d.succ
      · rw [dif_pos hadj']; exact crossAdjFN_xiL (K := K) d c hadj' h₁' h₂' h₁ h₂
      · rw [dif_neg hadj']; exact crossFarP_xiL (K := K) c d hcd _ _ h₁ h₂ h₁' h₂'

/-- **Dot slide, right strand**: `ψ ∘ ξ_R = ξ'_L ∘ ψ − τ`. -/
theorem crossU_xiR :
    (crossU K c d h₁ h₂ h₁' h₂').comp (BHom.mulB (BRing.tmul _ _ 1 (eXi K d r₂ h₂.2))) =
      (BHom.mulB (BRing.tmul _ _ (eXi K d r₁' h₁'.2) 1)).comp (crossU K c d h₁ h₂ h₁' h₂') -
        tauU K c d h₁ h₂ h₁' h₂' := by
  by_cases hcd : c = d
  · subst hcd
    simp only [crossU, tauU, dif_pos rfl]
    exact crossEEP2_xiR (K := K) c h₁ h₂ h₁' h₂'
  · simp only [crossU, tauU, dif_neg hcd]
    rw [BHom.sub_zero']
    by_cases hadj : d.castSucc = c.succ
    · rw [dif_pos hadj]; exact crossAdjNF_xiR (K := K) c d hadj h₁ h₂ h₁' h₂'
    · rw [dif_neg hadj]
      by_cases hadj' : c.castSucc = d.succ
      · rw [dif_pos hadj']; exact crossAdjFN_xiR (K := K) d c hadj' h₁' h₂' h₁ h₂
      · rw [dif_neg hadj']; exact crossFarP_xiR (K := K) c d hcd _ _ h₁ h₂ h₁' h₂'

theorem tauU_xiL :
    (tauU K c d h₁ h₂ h₁' h₂').comp (BHom.mulB (BRing.tmul _ _ (eXi K c r₁ h₁.2) 1)) =
      (BHom.mulB (BRing.tmul _ _ (eXi K d r₁' h₁'.2) 1)).comp (tauU K c d h₁ h₂ h₁' h₂') := by
  by_cases hcd : c = d
  · subst hcd
    simp only [tauU, dif_pos rfl]
    exact tauEE_xiL (K := K) c h₁ h₂ h₁' h₂'
  · simp only [tauU, dif_neg hcd]
    ext y; simp

theorem tauU_xiR :
    (tauU K c d h₁ h₂ h₁' h₂').comp (BHom.mulB (BRing.tmul _ _ 1 (eXi K d r₂ h₂.2))) =
      (BHom.mulB (BRing.tmul _ _ 1 (eXi K c r₂ h₂'.2))).comp (tauU K c d h₁ h₂ h₁' h₂') := by
  by_cases hcd : c = d
  · subst hcd
    simp only [tauU, dif_pos rfl]
    exact tauEE_xiR (K := K) c h₁ h₂ h₁' h₂'
  · simp only [tauU, dif_neg hcd]
    ext y; simp

theorem tauU_one : tauU K c d h₁ h₂ h₁' h₂' 1 = if c = d then 1 else 0 := by
  by_cases hcd : c = d
  · subst hcd
    simp only [tauU, dif_pos rfl, if_true]
    exact tauEE_one (K := K) c h₁ h₂ h₁' h₂'
  · simp only [tauU, dif_neg hcd, if_neg hcd]; rfl

/-- **The value at `1`**: `0` if `c = d`, `ξ'_R − ξ'_L` if `c = d + 1`, `1` otherwise. -/
theorem crossU_one :
    crossU K c d h₁ h₂ h₁' h₂' 1 = if c = d then 0 else if c.castSucc = d.succ then
      BRing.tmul _ _ 1 (eXi K c r₂ h₂'.2) - BRing.tmul _ _ (eXi K d r₁' h₁'.2) 1 else 1 := by
  by_cases hcd : c = d
  · subst hcd
    simp only [crossU, dif_pos rfl, if_true]
    exact crossEEP2_one (K := K) c h₁ h₂ h₁' h₂'
  · simp only [crossU, dif_neg hcd, if_neg hcd]
    by_cases hadj : d.castSucc = c.succ
    · have hadj' : ¬ c.castSucc = d.succ := by
        intro h
        have h1 := congrArg Fin.val hadj
        have h2 := congrArg Fin.val h
        simp only [Fin.coe_castSucc, Fin.val_succ] at h1 h2
        omega
      rw [dif_pos hadj, if_neg hadj']
      exact crossAdjNF_one (K := K) c d hadj h₁ h₂ h₁' h₂'
    · rw [dif_neg hadj]
      by_cases hadj' : c.castSucc = d.succ
      · rw [dif_pos hadj', if_pos hadj']
        exact crossAdjFN_one (K := K) d c hadj' h₁' h₂' h₁ h₂
      · rw [dif_neg hadj', if_neg hadj']
        exact crossFarP_one (K := K) c d hcd _ _ h₁ h₂ h₁' h₂'

end Uniform

end Categorification.Flag

end

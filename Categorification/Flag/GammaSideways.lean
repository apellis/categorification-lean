/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.GammaCupCap

/-!
# Sideways crossings of distinct colours (KL III Lemma 6.4) and `downupEF`, `downupFE`

KL III, arXiv:0807.3250v1, §6.2, Lemma 6.4 (TeX label `lem_other_crossings`, eqs.
`eq_lem_crossr`, `eq_lem_crossl`) and the relations `eq_downup_ij-gen` of Definition 3.1
(`Categorification.KL3.Diagram.Rel.downupEF`, `downupFE`).

KL III *define* the sideways crossings as composites of an upward crossing with a cup and a cap
(`Categorification.KL3.Diagram.crossl`, `crossr`). On the path model, with an arbitrary
1-morphism `Y` on the right:

* `crosslW i j … Y : E_i F_j Y → F_j E_i Y` is the cup `1 → F_j E_j` on the left, the upward
  crossing `E_j E_i → E_i E_j` (`crossU`), and the cap `E_j F_j → 1` on the right;
* `crossrW i j … Y : F_j E_i Y → E_i F_j Y` is the cup `1 → E_j F_j` on the right, the upward
  crossing `E_i E_j → E_j E_i`, and the cap `F_j E_j → 1` on the left.

## Main results (`i ≠ j`)

* **Lemma 6.4 for `crossl`**: `crossl` is the swap `ξ_i^{α₁} ⊗ ξ_j^{α₂} ↦ ξ_j^{α₂} ⊗ ξ_i^{α₁}`:
  it sends `1 ⊗ 1 ⊗ y` to `1 ⊗ 1 ⊗ y` (`crosslW_one`), commutes with the dots of both strands
  (`crosslW_dotE`, `crosslW_dotF`) and with the suffix (`crosslW_mul_suffix`), and is a map of
  bimodules; this determines it (`ext_two`).
* **Lemma 6.4 for `crossr`, as printed, fails for `i = j + 1`**: `crossr` commutes with the dots
  and the suffix in the same way (`crossrW_dotE`, `crossrW_dotF`, `crossrW_mul_suffix`), but
  `crossr(1 ⊗ 1 ⊗ y) = -(1 ⊗ 1 ⊗ y)` when `i = j + 1` (`j → i`), and `1 ⊗ 1 ⊗ y` otherwise
  (`crossrW_one`). So `crossr` is the swap for `i · j = 0` and for `j = i + 1`, and **minus** the
  swap for `i = j + 1`.
* **`downupEF`, `downupFE`** (KL III `eq_downup_ij-gen`, asserted to hold in `U→` by
  Definition 4.1): `crossr ∘ crossl` on `E_i F_j` and `crossl ∘ crossr` on `F_j E_i` are the
  identity, **except for `i = j + 1`, where they are minus the identity** (`downupEF_W`,
  `downupFE_W`).

These sign failures of the arXiv v1 text are corrected by Khovanov–Lauda in *Erratum to "A
categorification of quantum sl(n)"*, Quantum Topol. 2 (2011), 97–99: there Lemma 6.4 gives the
`F_j E_i → E_i F_j` map with a sign `-1` when `j → i`, and the relations `eq_downup_ij-gen` of
Definition 4.1 acquire signs. The corrected Definition 4.1 is not formalized here.

The cups, caps and crossings are those of KL III (6.2)–(6.5), (6.8) as formalized in
`Categorification.Flag.GammaCups` and `Categorification.Flag.GammaCross`; the relative sign of
the cup `1 → E F` and the cap `F E → 1` in `crossr` is fixed by the zigzag and bubble
normalizations only up to a weight-dependent factor, which is where a repair would have to act.
-/

noncomputable section

open scoped TensorProduct

namespace Categorification.Flag

universe u

/-! ### Generic lemmas -/

section Generic

variable {A B C D E : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D] [CommRing E]

/-- A whiskered two-strand map on a pure tensor. -/
theorem locTwo_tmul {D' : Type u} [CommRing D'] {L : BRing A B} {L' : BRing B C}
    {R : BRing A D'} {R' : BRing D' C} (φ : BHom (L.tensor L') (R.tensor R')) (X : BRing C E)
    (a : L.T) (b : L'.T) (x : X.T) :
    locTwo φ X (BRing.tmul _ _ a (BRing.tmul _ _ b x)) =
      (BRing.assoc R R' X).hom (BRing.tmul _ X (φ (BRing.tmul _ _ a b)) x) := by
  show (BRing.assoc R R' X).hom (BHom.whiskerRight φ X ((BRing.assoc L L' X).inv _)) = _
  rw [BRing.assoc_inv_tmul, BHom.whiskerRight_tmul]

/-- **Two strands and a suffix are determined by the dots**: if `L₁`, `L₂` are spanned by the
powers of their dots over their right rings, additive maps out of `L₁ ⊗ (L₂ ⊗ Y)` which multiply
by the same elements under both dots and agree on `1 ⊗ 1 ⊗ y` agree. -/
theorem ext_two {L₁ : BRing A B} {L₂ : BRing B C} {Y : BRing C D} (ξ₁ : L₁.T) (ξ₂ : L₂.T)
    (h₁ : SpannedBy L₁ ξ₁) (h₂ : SpannedBy L₂ ξ₂) {Z : Type u} [CommRing Z]
    (Φ Ψ : (L₁.tensor (L₂.tensor Y)).T →+ Z) (u₁ u₂ : Z)
    (hΦ₁ : ∀ z, Φ (BRing.tmul _ _ ξ₁ 1 * z) = u₁ * Φ z)
    (hΨ₁ : ∀ z, Ψ (BRing.tmul _ _ ξ₁ 1 * z) = u₁ * Ψ z)
    (hΦ₂ : ∀ z, Φ (BRing.tmul _ _ 1 (BRing.tmul _ _ ξ₂ 1) * z) = u₂ * Φ z)
    (hΨ₂ : ∀ z, Ψ (BRing.tmul _ _ 1 (BRing.tmul _ _ ξ₂ 1) * z) = u₂ * Ψ z)
    (h1 : ∀ y, Φ (BRing.tmul _ _ 1 (BRing.tmul _ _ 1 y)) = Ψ (BRing.tmul _ _ 1 (BRing.tmul _ _ 1 y)))
    (z : (L₁.tensor (L₂.tensor Y)).T) : Φ z = Ψ z := by
  let S : AddSubgroup (L₁.tensor (L₂.tensor Y)).T := (Φ - Ψ).ker
  have hS : ∀ w, w ∈ S ↔ Φ w = Ψ w := fun w => by
    show (Φ - Ψ) w = 0 ↔ _
    rw [AddMonoidHom.sub_apply, sub_eq_zero]
  have inner : ∀ n : (L₂.tensor Y).T, BRing.inclR L₁ (L₂.tensor Y) n ∈ S := by
    refine span_level L₂ Y ξ₂ h₂ (BRing.inclR L₁ (L₂.tensor Y)) S (fun w hw => ?_) (fun y => ?_)
    · rw [hS] at hw ⊢
      have e : BRing.inclR L₁ (L₂.tensor Y) (BRing.tmul L₂ Y ξ₂ 1) =
          BRing.tmul _ _ 1 (BRing.tmul _ _ ξ₂ 1) := rfl
      rw [e, hΦ₂, hΨ₂, hw]
    · rw [hS]; exact h1 y
  have key : z ∈ S := by
    refine span_level L₁ (L₂.tensor Y) ξ₁ h₁ (RingHom.id _) S (fun w hw => ?_) (fun n => inner n) z
    rw [hS] at hw ⊢
    rw [RingHom.id_apply, hΦ₁, hΨ₁, hw]
  exact (hS z).1 key

/-- Left whiskering transports an equality of multiplications. -/
theorem whiskerLeft_mul_congr (M : BRing A B) {N N' : BRing B C} (ψ : BHom N N') (w w' : N.T)
    (hψ : ∀ z, ψ (w * z) = ψ (w' * z)) (y : (M.tensor N).T) :
    BHom.whiskerLeft M ψ (BRing.tmul M N 1 w * y) = BHom.whiskerLeft M ψ (BRing.tmul M N 1 w' * y) := by
  refine BRing.induction_on (P := fun y => BHom.whiskerLeft M ψ (BRing.tmul M N 1 w * y) =
    BHom.whiskerLeft M ψ (BRing.tmul M N 1 w' * y)) y
    (by beta_reduce; rw [mul_zero, mul_zero]) (fun a b => ?_) (fun y y' hy hy' => ?_)
  · beta_reduce
    rw [BRing.tmul_mul_tmul, BRing.tmul_mul_tmul, BHom.whiskerLeft_tmul, BHom.whiskerLeft_tmul, hψ]
  · beta_reduce at hy hy' ⊢
    rw [mul_add, mul_add, BHom.map_add, BHom.map_add, hy, hy']

/-- A whiskered two-strand map commutes with multiplication by elements of the suffix (the
multiplication on the left). -/
theorem locTwo_mul_suffix' {D' : Type u} [CommRing D'] {L : BRing A B} {L' : BRing B C}
    {R : BRing A D'} {R' : BRing D' C} (φ : BHom (L.tensor L') (R.tensor R')) (X : BRing C E)
    (z : X.T) (y : (L.tensor (L'.tensor X)).T) :
    locTwo φ X (BRing.tmul L (L'.tensor X) 1 (BRing.tmul L' X 1 z) * y) =
      BRing.tmul R (R'.tensor X) 1 (BRing.tmul R' X 1 z) * locTwo φ X y := by
  rw [mul_comm, locTwo_mul_suffix, mul_comm]

/-- Bimodule maps commute with signs. -/
theorem BHom.map_neg_one_pow_mul {M N : BRing A B} (φ : BHom M N) (n : ℕ) (x : M.T) :
    φ ((-1) ^ n * x) = (-1) ^ n * φ x := by
  induction n with
  | zero => rw [pow_zero, pow_zero, one_mul, one_mul]
  | succ n ih => rw [pow_succ, mul_assoc, neg_one_mul, mul_neg, BHom.map_neg, ih, pow_succ,
      mul_assoc, neg_one_mul, mul_neg]

theorem tmul_neg_one_pow_mul {M : BRing A B} {N : BRing B C} (a : M.T) (n : ℕ) (b : N.T) :
    BRing.tmul M N a ((-1) ^ n * b) = (-1) ^ n * BRing.tmul M N a b := by
  induction n with
  | zero => rw [pow_zero, pow_zero, one_mul, one_mul]
  | succ n ih => rw [pow_succ, mul_assoc, neg_one_mul, mul_neg, BRing.tmul_neg, ih, pow_succ,
      mul_assoc, neg_one_mul, mul_neg]

theorem neg_one_pow_mul_tmul {M : BRing A B} {N : BRing B C} (a : M.T) (n : ℕ) (b : N.T) :
    BRing.tmul M N ((-1) ^ n * a) b = (-1) ^ n * BRing.tmul M N a b := by
  induction n with
  | zero => rw [pow_zero, pow_zero, one_mul, one_mul]
  | succ n ih => rw [pow_succ, mul_assoc, neg_one_mul, mul_neg, BRing.neg_tmul, ih, pow_succ,
      mul_assoc, neg_one_mul, mul_neg]

/-- Multiplying the image of a left-whiskered map, under an equality on the image of the inner map. -/
theorem whiskerLeft_mul_image (M : BRing A B) {N N' : BRing B C} (ψ : BHom N N') (u u' : N'.T)
    (hψ : ∀ z, u * ψ z = u' * ψ z) (y : (M.tensor N).T) :
    BRing.tmul M N' 1 u * BHom.whiskerLeft M ψ y = BRing.tmul M N' 1 u' * BHom.whiskerLeft M ψ y := by
  refine BRing.induction_on (P := fun y => BRing.tmul M N' 1 u * BHom.whiskerLeft M ψ y =
    BRing.tmul M N' 1 u' * BHom.whiskerLeft M ψ y) y
    (by beta_reduce; rw [BHom.map_zero, mul_zero, mul_zero]) (fun a b => ?_) (fun y y' hy hy' => ?_)
  · beta_reduce
    rw [BHom.whiskerLeft_tmul, BRing.tmul_mul_tmul, BRing.tmul_mul_tmul, hψ]
  · beta_reduce at hy hy' ⊢
    rw [BHom.map_add, mul_add, mul_add, hy, hy']

end Generic

variable {K : Type u} [Field K] {m : ℕ}


/-- `Γ(F_c)` is spanned by the powers of its dot over its right ring (KL III §5.1.1,
`eBasisLeft`). -/
theorem stepF_spanned (c : Fin m) {r s : Comp m} (h : StepR (false, c) r s) :
    SpannedBy (stepB K (false, c) r s h) (eXi K c s h.2) := by
  intro x
  letI := eLeftAlgebra K c s h.2
  refine ⟨_, fun a => hCast K h.1 ((eBasisLeft K c s h.2).repr x a), ?_⟩
  conv_lhs => rw [← (eBasisLeft K c s h.2).sum_repr x]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Algebra.smul_def, eBasisLeft_apply]
  have e : (stepB K (false, c) r s h).right (hCast K h.1 ((eBasisLeft K c s h.2).repr x a)) =
      eLeft K c s h.2 (hCast K h.1.symm (hCast K h.1 ((eBasisLeft K c s h.2).repr x a))) := rfl
  rw [e, hCast_trans_apply, hCast_rfl]
  rfl

/-! ### Crossings of distinct colours: pointwise dot slides -/

section CrossNe

variable (c d : Fin m) (hcd : c ≠ d) {t r₁ r₂ r₁' : Comp m} (h₁ : StepR (true, c) r₁ t)
  (h₂ : StepR (true, d) r₂ r₁) (h₁' : StepR (true, d) r₁' t) (h₂' : StepR (true, c) r₂ r₁')
include hcd

theorem tauU_ne : tauU K c d h₁ h₂ h₁' h₂' = 0 := by
  unfold tauU; rw [dif_neg hcd]

/-- For `c ≠ d` the dots slide freely through the upward crossing, whiskered by `X`: the dot of
the left input strand becomes the dot of the right output strand. -/
theorem locTwo_crossU_dotL {E : Type u} [CommRing E] (X : BRing (H K r₂) E) (z) :
    locTwo (crossU K c d h₁ h₂ h₁' h₂') X
        (BRing.tmul _ _ (eXi K c r₁ h₁.2) 1 * z) =
      BRing.tmul _ _ 1 (BRing.tmul _ X (eXi K c r₂ h₂'.2) 1) *
        locTwo (crossU K c d h₁ h₂ h₁' h₂') X z := by
  have := BHom.congr_apply ((crossU_rules (K := K) c d h₁ h₂ h₁' h₂').locL X) z
  rw [BHom.comp_apply, BHom.add_apply, tauU_ne c d hcd, locTwo_zero, BHom.zero_apply, zero_add,
    BHom.comp_apply, BHom.mulB_apply, BHom.mulB_apply] at this
  exact this

/-- The dot of the right input strand becomes the dot of the left output strand. -/
theorem locTwo_crossU_dotR {E : Type u} [CommRing E] (X : BRing (H K r₂) E) (z) :
    locTwo (crossU K c d h₁ h₂ h₁' h₂') X
        (BRing.tmul _ _ 1 (BRing.tmul _ X (eXi K d r₂ h₂.2) 1) * z) =
      BRing.tmul _ _ (eXi K d r₁' h₁'.2) 1 * locTwo (crossU K c d h₁ h₂ h₁' h₂') X z := by
  have := BHom.congr_apply ((crossU_rules (K := K) c d h₁ h₂ h₁' h₂').locR X) z
  rw [BHom.comp_apply, BHom.sub_apply, tauU_ne c d hcd, locTwo_zero, BHom.zero_apply, sub_zero,
    BHom.comp_apply, BHom.mulB_apply, BHom.mulB_apply] at this
  exact this

/-- `ψ(ξ_L^g) = ξ'^g_R ψ(1)` for `c ≠ d`. -/
theorem crossU_xiL_pow (g : ℕ) :
    crossU K c d h₁ h₂ h₁' h₂' (BRing.tmul _ _ (eXi K c r₁ h₁.2 ^ g) 1) =
      BRing.tmul _ _ 1 (eXi K c r₂ h₂'.2 ^ g) * crossU K c d h₁ h₂ h₁' h₂' 1 := by
  induction g with
  | zero => rw [pow_zero, pow_zero, ← BRing.one_eq, ← BRing.one_eq, one_mul]
  | succ g ih =>
    have := BHom.congr_apply (crossU_xiL (K := K) c d h₁ h₂ h₁' h₂')
      (BRing.tmul _ _ (eXi K c r₁ h₁.2 ^ g) 1)
    rw [BHom.comp_apply, BHom.add_apply, tauU_ne c d hcd, BHom.zero_apply, zero_add,
      BHom.comp_apply, BHom.mulB_apply, BHom.mulB_apply, BRing.tmul_mul_tmul, mul_one, ih,
      ← mul_assoc, BRing.tmul_mul_tmul, one_mul, ← pow_succ'] at this
    rw [this, pow_succ']

/-- `ψ(ξ_R^g) = ξ'^g_L ψ(1)` for `c ≠ d`. -/
theorem crossU_xiR_pow (g : ℕ) :
    crossU K c d h₁ h₂ h₁' h₂' (BRing.tmul _ _ 1 (eXi K d r₂ h₂.2 ^ g)) =
      BRing.tmul _ _ (eXi K d r₁' h₁'.2 ^ g) 1 * crossU K c d h₁ h₂ h₁' h₂' 1 := by
  induction g with
  | zero => rw [pow_zero, pow_zero, ← BRing.one_eq, ← BRing.one_eq, one_mul]
  | succ g ih =>
    have := BHom.congr_apply (crossU_xiR (K := K) c d h₁ h₂ h₁' h₂')
      (BRing.tmul _ _ 1 (eXi K d r₂ h₂.2 ^ g))
    rw [BHom.comp_apply, BHom.sub_apply, tauU_ne c d hcd, BHom.zero_apply, sub_zero,
      BHom.comp_apply, BHom.mulB_apply, BHom.mulB_apply, BRing.tmul_mul_tmul, mul_one, ih,
      ← mul_assoc, BRing.tmul_mul_tmul, one_mul, ← pow_succ'] at this
    rw [this, pow_succ']

end CrossNe

/-! ### The sideways crossing `E_i F_j → F_j E_i` -/

section Crossl

variable (i j : Fin m) {p q r q' : Comp m} (hEi : StepR (true, i) q p) (hFj : StepR (false, j) r q)
  (hFj' : StepR (false, j) q' p) (hEi' : StepR (true, i) r q') {E : Type u} [CommRing E]
  (Y : BRing (H K r) E)

variable (K) in
/-- **`Γ_N` of the sideways crossing** `crossl i j : E_i F_j 1 → F_j E_i 1` (KL III
`eq_crossl-gen`), followed by `Y`: the cup `1 → F_j E_j` on the left, the upward crossing
`E_j E_i → E_i E_j`, the cap `E_j F_j → 1` on the right. -/
def crosslW : BHom ((stepB K (true, i) q p hEi).tensor ((stepB K (false, j) r q hFj).tensor Y))
    ((stepB K (false, j) q' p hFj').tensor ((stepB K (true, i) r q' hEi').tensor Y)) :=
  (BHom.whiskerLeft (stepB K (false, j) q' p hFj') (BHom.whiskerLeft (stepB K (true, i) r q' hEi')
    (capEFW K j (hFj : StepR (true, j) q r) hFj Y))).comp
  ((BHom.whiskerLeft (stepB K (false, j) q' p hFj') (locTwo (crossU K j i
      (hFj' : StepR (true, j) p q') hEi hEi' (hFj : StepR (true, j) q r))
      ((stepB K (false, j) r q hFj).tensor Y))).comp
    (cupFEW K j (hFj' : StepR (true, j) p q') hFj'
      ((stepB K (true, i) q p hEi).tensor ((stepB K (false, j) r q hFj).tensor Y))))

/-- The cap part of `crosslW` on a pure tensor. -/
theorem crosslCap_tmul (u : (stepB K (true, i) r q' hEi').T)
    (v : (stepB K (true, j) q r (hFj : StepR (true, j) q r)).T) (y : Y.T) :
    BHom.whiskerLeft (stepB K (true, i) r q' hEi') (capEFW K j (hFj : StepR (true, j) q r) hFj Y)
        ((BRing.assoc (stepB K (true, i) r q' hEi') (stepB K (true, j) q r hFj)
          ((stepB K (false, j) r q hFj).tensor Y)).hom
          (BRing.tmul _ _ (BRing.tmul (stepB K (true, i) r q' hEi') (stepB K (true, j) q r hFj) u v)
            (BRing.tmul (stepB K (false, j) r q hFj) Y 1 y))) =
      BRing.tmul (stepB K (true, i) r q' hEi') Y u
        (Y.left (capEFP K j (hFj : StepR (true, j) q r) hFj
          (BRing.tmul (stepB K (true, j) q r hFj) (stepB K (false, j) r q hFj) v 1)) * y) := by
  rw [BRing.assoc_hom_tmul, BHom.whiskerLeft_tmul, capEFW_tmul]

/-- **Lemma 6.4, value at `1`**: for `i ≠ j`, `crossl(1 ⊗ 1 ⊗ y) = 1 ⊗ 1 ⊗ y`. -/
theorem crosslW_one (hij : i ≠ j) (y : Y.T) :
    crosslW K i j hEi hFj hFj' hEi' Y (BRing.tmul _ _ 1 (BRing.tmul _ _ 1 y)) =
      BRing.tmul _ _ 1 (BRing.tmul _ _ 1 y) := by
  have hji : j ≠ i := Ne.symm hij
  simp only [crosslW, BHom.comp_apply]
  rw [cupFEW_apply', BHom.map_sum, BHom.map_sum]
  -- the crossing on `ξ^g ⊗ 1`
  have hψ : ∀ g, locTwo (crossU K j i (hFj' : StepR (true, j) p q') hEi hEi'
      (hFj : StepR (true, j) q r)) ((stepB K (false, j) r q hFj).tensor Y)
      (BRing.tmul (stepB K (true, j) p q' hFj') _ (eXi K j p hFj'.2 ^ g)
        (BRing.tmul (stepB K (true, i) q p hEi) _ 1 (BRing.tmul (stepB K (false, j) r q hFj) Y 1 y))) =
      (BRing.assoc _ _ _).hom (BRing.tmul _ _ (BRing.tmul (stepB K (true, i) r q' hEi')
        (stepB K (true, j) q r hFj) 1 (eXi K j q hFj.2 ^ g) *
        crossU K j i (hFj' : StepR (true, j) p q') hEi hEi' (hFj : StepR (true, j) q r) 1)
        (BRing.tmul (stepB K (false, j) r q hFj) Y 1 y)) := by
    intro g
    rw [locTwo_tmul, crossU_xiL_pow j i hji]
  simp only [BHom.whiskerLeft_tmul, hψ]
  rw [crossU_one, if_neg hji]
  have hq : p j.castSucc + (if j.castSucc = i.succ then 1 else 0) = q j.castSucc := by
    rw [← hEi.1, raise]
    split_ifs with h1 h2 h2
    · exact absurd (Fin.castSucc_injective _ h1) hji
    · exact absurd (Fin.castSucc_injective _ h1) hji
    · have := hEi.2; rw [← h2] at this; omega
    · rfl
  have hd : dFE j (hFj' : StepR (true, j) p q') = p j.castSucc := dFE_eq j _
  rw [Finset.sum_eq_single (dFE j (hFj' : StepR (true, j) p q'))]
  · rw [Nat.sub_self, pow_zero, one_mul, xsFE_eq, x_zero, map_one]
    split_ifs with hadj
    · rw [if_pos hadj] at hq
      rw [mul_sub, BRing.tmul_mul_tmul, BRing.tmul_mul_tmul, one_mul, one_mul, mul_one,
        BRing.sub_tmul, BHom.map_sub, BHom.map_sub, crosslCap_tmul, crosslCap_tmul,
        ← pow_succ, capEFP_xi_pow j _ _ _ (by omega), capEFP_xi_pow j _ _ _ (by omega),
        if_pos (by omega), if_neg (by omega), map_one, map_zero, one_mul, zero_mul]
      simp only [BRing.tmul_zero, sub_zero]
    · rw [if_neg hadj, add_zero] at hq
      rw [mul_one, crosslCap_tmul, capEFP_xi_pow j _ _ _ (by omega), if_pos (by omega),
        map_one, one_mul]
  · intro g hg hgd
    have hg' : g ≤ dFE j (hFj' : StepR (true, j) p q') := Nat.lt_succ_iff.1 (Finset.mem_range.1 hg)
    split_ifs with hadj
    · rw [if_pos hadj] at hq
      rw [mul_sub, BRing.tmul_mul_tmul, BRing.tmul_mul_tmul, one_mul, one_mul, mul_one,
        BRing.sub_tmul, BHom.map_sub, BHom.map_sub, crosslCap_tmul, crosslCap_tmul,
        ← pow_succ, capEFP_xi_pow j _ _ _ (by omega), capEFP_xi_pow j _ _ _ (by omega),
        if_neg (by omega), if_neg (by omega), map_zero, zero_mul]
      simp only [BRing.tmul_zero, sub_zero]
    · rw [if_neg hadj, add_zero] at hq
      rw [mul_one, crosslCap_tmul, capEFP_xi_pow j _ _ _ (by omega), if_neg (by omega),
        map_zero, zero_mul]
      simp only [BRing.tmul_zero]
  · intro h; exact absurd (Finset.mem_range.2 (Nat.lt_succ_self _)) h

/-- **Lemma 6.4, the dot of `E_i`**: `crossl` commutes with the dot on the upward strand. -/
theorem crosslW_dotE (hij : i ≠ j) (z) :
    crosslW K i j hEi hFj hFj' hEi' Y
        (BRing.tmul (stepB K (true, i) q p hEi) ((stepB K (false, j) r q hFj).tensor Y)
          (eXi K i q hEi.2) 1 * z) =
      BRing.tmul (stepB K (false, j) q' p hFj') ((stepB K (true, i) r q' hEi').tensor Y) 1
        (BRing.tmul (stepB K (true, i) r q' hEi') Y (eXi K i r hEi'.2) 1) *
        crosslW K i j hEi hFj hFj' hEi' Y z := by
  simp only [crosslW, BHom.comp_apply]
  rw [cupFEW_mul, whiskerLeft_mul_right _ _ _ _
      (locTwo_crossU_dotR j i (Ne.symm hij) (hFj' : StepR (true, j) p q') hEi hEi'
        (hFj : StepR (true, j) q r) _),
    whiskerLeft_mul_right _ _ _ _ (fun z => whiskerLeft_mul_left _ _ z _)]

/-- **Lemma 6.4, the dot of `F_j`**: `crossl` commutes with the dot on the downward strand. -/
theorem crosslW_dotF (hij : i ≠ j) (z) :
    crosslW K i j hEi hFj hFj' hEi' Y
        (BRing.tmul (stepB K (true, i) q p hEi) ((stepB K (false, j) r q hFj).tensor Y) 1
          (BRing.tmul (stepB K (false, j) r q hFj) Y (eXi K j q hFj.2) 1) * z) =
      BRing.tmul (stepB K (false, j) q' p hFj') ((stepB K (true, i) r q' hEi').tensor Y)
        (eXi K j p hFj'.2) 1 * crosslW K i j hEi hFj hFj' hEi' Y z := by
  have hji : j ≠ i := Ne.symm hij
  simp only [crosslW, BHom.comp_apply]
  -- through the cup and the crossing (suffix elements)
  rw [cupFEW_mul, whiskerLeft_mul_right _ _ _ _ (locTwo_mul_suffix' _ _ _)]
  -- across the cap
  rw [whiskerLeft_mul_congr _ _ _ (BRing.tmul (stepB K (true, i) r q' hEi')
      ((stepB K (true, j) q r hFj).tensor ((stepB K (false, j) r q hFj).tensor Y)) 1
      (BRing.tmul (stepB K (true, j) q r hFj) ((stepB K (false, j) r q hFj).tensor Y)
        (eXi K j q hFj.2) 1))
    (whiskerLeft_mul_congr _ _ _ _ (capEFW_slide j (hFj : StepR (true, j) q r) hFj Y _))]
  -- back through the crossing and across the cup
  rw [← whiskerLeft_mul_right _ _ _ _
      (locTwo_crossU_dotL j i hji (hFj' : StepR (true, j) p q') hEi hEi'
        (hFj : StepR (true, j) q r) _),
    ← cupFEW_slide j (hFj' : StepR (true, j) p q') hFj',
    whiskerLeft_mul_left, whiskerLeft_mul_left]

/-- `crossl` commutes with multiplication on the suffix. -/
theorem crosslW_mul_suffix (w : Y.T) (z) :
    crosslW K i j hEi hFj hFj' hEi' Y
        (BRing.tmul (stepB K (true, i) q p hEi) ((stepB K (false, j) r q hFj).tensor Y) 1
          (BRing.tmul (stepB K (false, j) r q hFj) Y 1 w) * z) =
      BRing.tmul (stepB K (false, j) q' p hFj') ((stepB K (true, i) r q' hEi').tensor Y) 1
        (BRing.tmul (stepB K (true, i) r q' hEi') Y 1 w) * crosslW K i j hEi hFj hFj' hEi' Y z := by
  simp only [crosslW, BHom.comp_apply]
  rw [cupFEW_mul, whiskerLeft_mul_right _ _ _ _ (locTwo_mul_suffix' _ _ _),
    whiskerLeft_mul_right _ _ _ _ (whiskerLeft_mul_right _ _ _ _ (capEFW_mul j _ _ Y w))]

/-- Powers of the dot of `E_i` through `crossl`. -/
theorem crosslW_dotE_pow (hij : i ≠ j) (g : ℕ) (z) :
    crosslW K i j hEi hFj hFj' hEi' Y
        (BRing.tmul (stepB K (true, i) q p hEi) ((stepB K (false, j) r q hFj).tensor Y)
          (eXi K i q hEi.2 ^ g) 1 * z) =
      BRing.tmul (stepB K (false, j) q' p hFj') ((stepB K (true, i) r q' hEi').tensor Y) 1
        (BRing.tmul (stepB K (true, i) r q' hEi') Y (eXi K i r hEi'.2 ^ g) 1) *
        crosslW K i j hEi hFj hFj' hEi' Y z := by
  induction g generalizing z with
  | zero =>
    simp only [pow_zero, ← BRing.one_eq, one_mul]
  | succ g ih =>
    have e1 : BRing.tmul (stepB K (true, i) q p hEi) ((stepB K (false, j) r q hFj).tensor Y)
        (eXi K i q hEi.2 ^ (g + 1)) 1 = BRing.tmul _ _ (eXi K i q hEi.2) 1 *
          BRing.tmul _ _ (eXi K i q hEi.2 ^ g) 1 := by
      rw [BRing.tmul_mul_tmul, mul_one, pow_succ']
    rw [e1, mul_assoc, crosslW_dotE i j hEi hFj hFj' hEi' Y hij, ih, ← mul_assoc,
      BRing.tmul_mul_tmul, BRing.tmul_mul_tmul, one_mul, mul_one, ← pow_succ']

end Crossl

/-! ### The sideways crossing `F_j E_i → E_i F_j` -/

section Crossr

variable (i j : Fin m) {p q r q' : Comp m} (hFj : StepR (false, j) q p) (hEi : StepR (true, i) r q)
  (hEi' : StepR (true, i) q' p) (hFj' : StepR (false, j) r q') {E : Type u} [CommRing E]
  (Y : BRing (H K r) E)

variable (K) in
/-- **`Γ_N` of the sideways crossing** `crossr i j : F_j E_i 1 → E_i F_j 1` (KL III
`eq_crossr-gen`), followed by `Y`: the cup `1 → E_j F_j` on the right, the upward crossing
`E_i E_j → E_j E_i`, the cap `F_j E_j → 1` on the left. -/
def crossrW : BHom ((stepB K (false, j) q p hFj).tensor ((stepB K (true, i) r q hEi).tensor Y))
    ((stepB K (true, i) q' p hEi').tensor ((stepB K (false, j) r q' hFj').tensor Y)) :=
  (capFEW K j (hFj : StepR (true, j) p q) hFj
    ((stepB K (true, i) q' p hEi').tensor ((stepB K (false, j) r q' hFj').tensor Y))).comp
  ((BHom.whiskerLeft (stepB K (false, j) q p hFj) (locTwo (crossU K i j hEi
      (hFj' : StepR (true, j) q' r) (hFj : StepR (true, j) p q) hEi')
      ((stepB K (false, j) r q' hFj').tensor Y))).comp
    (BHom.whiskerLeft (stepB K (false, j) q p hFj) (BHom.whiskerLeft (stepB K (true, i) r q hEi)
      (cupEFW K j (hFj' : StepR (true, j) q' r) hFj' Y))))

/-- The cap part of `crossrW` on a pure tensor. -/
theorem crossrCap_tmul (u : (stepB K (true, j) p q (hFj : StepR (true, j) p q)).T)
    (v : (stepB K (true, i) q' p hEi').T) (w : ((stepB K (false, j) r q' hFj').tensor Y).T) :
    capFEW K j (hFj : StepR (true, j) p q) hFj
        ((stepB K (true, i) q' p hEi').tensor ((stepB K (false, j) r q' hFj').tensor Y))
        (BRing.tmul (stepB K (false, j) q p hFj) _ 1
          ((BRing.assoc (stepB K (true, j) p q hFj) (stepB K (true, i) q' p hEi')
            ((stepB K (false, j) r q' hFj').tensor Y)).hom
            (BRing.tmul _ _ (BRing.tmul (stepB K (true, j) p q hFj) (stepB K (true, i) q' p hEi') u v)
              w))) =
      BRing.tmul (stepB K (true, i) q' p hEi') ((stepB K (false, j) r q' hFj').tensor Y)
        ((stepB K (true, i) q' p hEi').left (capFEP K j (hFj : StepR (true, j) p q) hFj
          (BRing.tmul (stepB K (false, j) q p hFj) (stepB K (true, j) p q hFj) 1 u)) * v) w := by
  rw [BRing.assoc_hom_tmul, capFEW_tmul, BRing.tensor_left, BRing.tmul_mul_tmul, one_mul]

/-- **Lemma 6.4 for `crossr`, value at `1`**: for `i ≠ j`, `crossr(1 ⊗ 1 ⊗ y)` is `1 ⊗ 1 ⊗ y`,
except for `i = j + 1` (`j → i`), where it is `-(1 ⊗ 1 ⊗ y)`. -/
theorem crossrW_one (hij : i ≠ j) (y : Y.T) :
    crossrW K i j hFj hEi hEi' hFj' Y (BRing.tmul _ _ 1 (BRing.tmul _ _ 1 y)) =
      if i.castSucc = j.succ then -BRing.tmul _ _ 1 (BRing.tmul _ _ 1 y)
      else BRing.tmul _ _ 1 (BRing.tmul _ _ 1 y) := by
  have hij' : ¬ i = j := hij
  simp only [crossrW, BHom.comp_apply, BHom.whiskerLeft_tmul]
  rw [cupEFW_apply, BRing.tmul_sum, BHom.map_sum, BRing.tmul_sum, BHom.map_sum]
  have hp : p j.succ = q' j.succ + (if i.castSucc = j.succ then 1 else 0) := by
    rw [← hEi'.1, raise]
    by_cases h1 : j.succ = i.castSucc
    · rw [if_pos h1, if_pos h1.symm]
    · have h3 : j.succ ≠ i.succ := fun h => hij (Fin.succ_injective _ h).symm
      rw [if_neg h1, if_neg h3, if_neg (fun h => h1 h.symm), add_zero]
  have hq' := hFj'.2
  have hd : dEF j (hFj' : StepR (true, j) q' r) = q' j.succ - 1 := dEF_eq j _
  set d := dEF j (hFj' : StepR (true, j) q' r) with hd'
  have hterm : ∀ g ∈ Finset.range (d + 1),
      capFEW K j (hFj : StepR (true, j) p q) hFj
        ((stepB K (true, i) q' p hEi').tensor ((stepB K (false, j) r q' hFj').tensor Y))
        (BRing.tmul (stepB K (false, j) q p hFj) _ 1
          (locTwo (crossU K i j hEi (hFj' : StepR (true, j) q' r) (hFj : StepR (true, j) p q) hEi')
            ((stepB K (false, j) r q' hFj').tensor Y)
            (BRing.tmul (stepB K (true, i) r q hEi) _ 1
              (BRing.tmul (stepB K (true, j) q' r hFj') ((stepB K (false, j) r q' hFj').tensor Y)
                ((-1) ^ (d - g) * eXi K j q' hFj'.2 ^ g : ERing K j q' hFj'.2)
                (BRing.tmul (stepB K (false, j) r q' hFj') Y (xsEF j hFj' (d - g)) y))))) =
      if g = d then (if i.castSucc = j.succ then -BRing.tmul _ _ 1 (BRing.tmul _ _ 1 y)
        else BRing.tmul _ _ 1 (BRing.tmul _ _ 1 y)) else 0 := by
    intro g hg
    have hg' : g ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hg)
    rw [← Fst_right_x j (hFj' : StepR (true, j) q' r) hFj', ← mul_one
      ((stepB K (false, j) r q' hFj').right (x K r j.succ (d - g))), BRing.tmul_balance,
      locTwo_tmul, tmul_neg_one_pow_mul, BHom.map_neg_one_pow_mul,
      crossU_xiR_pow i j hij, crossU_one, if_neg hij', neg_one_pow_mul_tmul,
      BHom.map_neg_one_pow_mul, tmul_neg_one_pow_mul, BHom.map_neg_one_pow_mul]
    split_ifs with hadj hgd hgd
    · subst hgd
      rw [if_pos hadj] at hp
      rw [mul_sub, BRing.tmul_mul_tmul, BRing.tmul_mul_tmul, one_mul, mul_one, one_mul,
        ← pow_succ, BRing.sub_tmul, BHom.map_sub, BRing.tmul_sub, BHom.map_sub, crossrCap_tmul,
        crossrCap_tmul,
        capFEP_xi_pow j _ _ _ (by omega), capFEP_xi_pow j _ _ _ (by omega), if_neg (by omega),
        if_pos (by omega), map_zero, map_one, zero_mul, one_mul, Nat.sub_self, pow_zero, one_mul,
        x_zero, map_one, one_mul, BRing.zero_tmul, zero_sub]
    · rw [if_pos hadj] at hp
      rw [mul_sub, BRing.tmul_mul_tmul, BRing.tmul_mul_tmul, one_mul, mul_one, one_mul,
        ← pow_succ, BRing.sub_tmul, BHom.map_sub, BRing.tmul_sub, BHom.map_sub, crossrCap_tmul,
        crossrCap_tmul,
        capFEP_xi_pow j _ _ _ (by omega), capFEP_xi_pow j _ _ _ (by omega), if_neg (by omega),
        if_neg (by omega), map_zero]
      simp only [zero_mul, BRing.zero_tmul, sub_zero, mul_zero]
    · subst hgd
      rw [if_neg hadj, add_zero] at hp
      rw [mul_one, crossrCap_tmul, capFEP_xi_pow j _ _ _ (by omega), if_pos (by omega), map_one,
        one_mul, Nat.sub_self, pow_zero, one_mul, x_zero, map_one, one_mul]
    · rw [if_neg hadj, add_zero] at hp
      rw [mul_one, crossrCap_tmul, capFEP_xi_pow j _ _ _ (by omega), if_neg (by omega), map_zero]
      simp only [zero_mul, BRing.zero_tmul, mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range (d + 1)) d,
    if_pos (Finset.mem_range.2 (Nat.lt_succ_self d))]

/-- **Lemma 6.4 for `crossr`, the dot of `E_i`**: `crossr` commutes with the dot on the upward
strand. -/
theorem crossrW_dotE (hij : i ≠ j) (z) :
    crossrW K i j hFj hEi hEi' hFj' Y
        (BRing.tmul (stepB K (false, j) q p hFj) ((stepB K (true, i) r q hEi).tensor Y) 1
          (BRing.tmul (stepB K (true, i) r q hEi) Y (eXi K i r hEi.2) 1) * z) =
      BRing.tmul (stepB K (true, i) q' p hEi') ((stepB K (false, j) r q' hFj').tensor Y)
        (eXi K i q' hEi'.2) 1 * crossrW K i j hFj hEi hEi' hFj' Y z := by
  simp only [crossrW, BHom.comp_apply]
  rw [whiskerLeft_mul_right _ _ _ _ (fun z => whiskerLeft_mul_left _ _ z _),
    whiskerLeft_mul_right _ _ _ _
      (locTwo_crossU_dotL i j hij hEi (hFj' : StepR (true, j) q' r) (hFj : StepR (true, j) p q)
        hEi' _),
    capFEW_mul]

/-- **Lemma 6.4 for `crossr`, the dot of `F_j`**: `crossr` commutes with the dot on the downward
strand. -/
theorem crossrW_dotF (hij : i ≠ j) (z) :
    crossrW K i j hFj hEi hEi' hFj' Y
        (BRing.tmul (stepB K (false, j) q p hFj) ((stepB K (true, i) r q hEi).tensor Y)
          (eXi K j p hFj.2) 1 * z) =
      BRing.tmul (stepB K (true, i) q' p hEi') ((stepB K (false, j) r q' hFj').tensor Y) 1
        (BRing.tmul (stepB K (false, j) r q' hFj') Y (eXi K j q' hFj'.2) 1) *
        crossrW K i j hFj hEi hEi' hFj' Y z := by
  simp only [crossrW, BHom.comp_apply]
  rw [whiskerLeft_mul_left, whiskerLeft_mul_left,
    ← capFEW_slide j (hFj : StepR (true, j) p q) hFj _ _,
    ← whiskerLeft_mul_right _ _ _ _
      (locTwo_crossU_dotR i j hij hEi (hFj' : StepR (true, j) q' r) (hFj : StepR (true, j) p q)
        hEi' _)]
  -- across the cup on the right
  rw [whiskerLeft_mul_image _ _ _ (BRing.tmul (stepB K (true, i) r q hEi) _ 1
      (BRing.tmul (stepB K (true, j) q' r hFj') ((stepB K (false, j) r q' hFj').tensor Y) 1
        (BRing.tmul (stepB K (false, j) r q' hFj') Y (eXi K j q' hFj'.2) 1)))
    (whiskerLeft_mul_image _ _ _ _ (fun y =>
      (cupEFW_slide j (hFj' : StepR (true, j) q' r) hFj' Y y)))]
  rw [whiskerLeft_mul_right _ _ _ _ (locTwo_mul_suffix' _ _ _), capFEW_mul]

/-- `crossr` commutes with multiplication on the suffix. -/
theorem crossrW_mul_suffix (w : Y.T) (z) :
    crossrW K i j hFj hEi hEi' hFj' Y
        (BRing.tmul (stepB K (false, j) q p hFj) ((stepB K (true, i) r q hEi).tensor Y) 1
          (BRing.tmul (stepB K (true, i) r q hEi) Y 1 w) * z) =
      BRing.tmul (stepB K (true, i) q' p hEi') ((stepB K (false, j) r q' hFj').tensor Y) 1
        (BRing.tmul (stepB K (false, j) r q' hFj') Y 1 w) * crossrW K i j hFj hEi hEi' hFj' Y z := by
  simp only [crossrW, BHom.comp_apply]
  rw [whiskerLeft_mul_right _ _ _ _ (whiskerLeft_mul_right _ _ _ _ (cupEFW_mul j _ _ Y w)),
    whiskerLeft_mul_right _ _ _ _ (locTwo_mul_suffix' _ _ _), capFEW_mul]

/-- Powers of the dot of `E_i` through `crossr`. -/
theorem crossrW_dotE_pow (hij : i ≠ j) (g : ℕ) (z) :
    crossrW K i j hFj hEi hEi' hFj' Y
        (BRing.tmul (stepB K (false, j) q p hFj) ((stepB K (true, i) r q hEi).tensor Y) 1
          (BRing.tmul (stepB K (true, i) r q hEi) Y (eXi K i r hEi.2 ^ g) 1) * z) =
      BRing.tmul (stepB K (true, i) q' p hEi') ((stepB K (false, j) r q' hFj').tensor Y)
        (eXi K i q' hEi'.2 ^ g) 1 * crossrW K i j hFj hEi hEi' hFj' Y z := by
  induction g generalizing z with
  | zero =>
    simp only [pow_zero, ← BRing.one_eq, one_mul]
  | succ g ih =>
    have e1 : BRing.tmul (stepB K (false, j) q p hFj) ((stepB K (true, i) r q hEi).tensor Y) 1
        (BRing.tmul (stepB K (true, i) r q hEi) Y (eXi K i r hEi.2 ^ (g + 1)) 1) =
        BRing.tmul _ _ 1 (BRing.tmul _ Y (eXi K i r hEi.2) 1) *
          BRing.tmul _ _ 1 (BRing.tmul _ Y (eXi K i r hEi.2 ^ g) 1) := by
      rw [BRing.tmul_mul_tmul, BRing.tmul_mul_tmul, mul_one, one_mul, pow_succ']
    rw [e1, mul_assoc, crossrW_dotE i j hFj hEi hEi' hFj' Y hij, ih, ← mul_assoc,
      BRing.tmul_mul_tmul, mul_one, ← pow_succ']

end Crossr

/-! ### `downupEF` and `downupFE` -/

section DownUp

variable (i j : Fin m) {p q r q' : Comp m} (hEi : StepR (true, i) q p) (hFj : StepR (false, j) r q)
  (hFj' : StepR (false, j) q' p) (hEi' : StepR (true, i) r q') {E : Type u} [CommRing E]
  (Y : BRing (H K r) E)

/-- **`downupEF` on the path model** (KL III `eq_downup_ij-gen`, first relation): for `i ≠ j`,
`crossr ∘ crossl` on `E_i F_j Y` is the identity, **except for `i = j + 1`** (`j → i`), where it
is minus the identity (`crossrW_one`). -/
theorem downupEF_W (hij : i ≠ j) :
    (crossrW K i j hFj' hEi' hEi hFj Y).comp (crosslW K i j hEi hFj hFj' hEi' Y) =
      if i.castSucc = j.succ then -BHom.id _ else BHom.id _ := by
  refine BHom.ext fun z => ?_
  refine ext_two (Y := Y) (eXi K i q hEi.2) (eXi K j q hFj.2) (stepE_spanned i hEi)
    (stepF_spanned j hFj) ((crossrW K i j hFj' hEi' hEi hFj Y).comp
      (crosslW K i j hEi hFj hFj' hEi' Y)).toAddHom
    (if i.castSucc = j.succ then -BHom.id _ else BHom.id _ : BHom _ _).toAddHom
    (BRing.tmul _ _ (eXi K i q hEi.2) 1) (BRing.tmul _ _ 1 (BRing.tmul _ _ (eXi K j q hFj.2) 1))
    (fun z => ?_) (fun z => ?_) (fun z => ?_) (fun z => ?_) (fun y => ?_) z
  · rw [BHom.toAddHom_apply, BHom.toAddHom_apply, BHom.comp_apply, BHom.comp_apply,
      crosslW_dotE i j hEi hFj hFj' hEi' Y hij, crossrW_dotE i j hFj' hEi' hEi hFj Y hij]
  · rw [BHom.toAddHom_apply, BHom.toAddHom_apply]
    split_ifs
    · rw [BHom.neg_apply, BHom.id_apply, BHom.neg_apply, BHom.id_apply, mul_neg]
    · rw [BHom.id_apply, BHom.id_apply]
  · rw [BHom.toAddHom_apply, BHom.toAddHom_apply, BHom.comp_apply, BHom.comp_apply,
      crosslW_dotF i j hEi hFj hFj' hEi' Y hij, crossrW_dotF i j hFj' hEi' hEi hFj Y hij]
  · rw [BHom.toAddHom_apply, BHom.toAddHom_apply]
    split_ifs
    · rw [BHom.neg_apply, BHom.id_apply, BHom.neg_apply, BHom.id_apply, mul_neg]
    · rw [BHom.id_apply, BHom.id_apply]
  · rw [BHom.toAddHom_apply, BHom.toAddHom_apply, BHom.comp_apply,
      crosslW_one i j hEi hFj hFj' hEi' Y hij, crossrW_one i j hFj' hEi' hEi hFj Y hij]
    split_ifs <;> rfl

/-- **`downupFE` on the path model** (KL III `eq_downup_ij-gen`, second relation, for the colours
`(j, i)`): for `i ≠ j`, `crossl ∘ crossr` on `F_j E_i Y` is the identity, **except for `i = j + 1`**,
where it is minus the identity. -/
theorem downupFE_W (hij : i ≠ j) :
    (crosslW K i j hEi hFj hFj' hEi' Y).comp (crossrW K i j hFj' hEi' hEi hFj Y) =
      if i.castSucc = j.succ then -BHom.id _ else BHom.id _ := by
  refine BHom.ext fun z => ?_
  refine ext_two (Y := Y) (eXi K j p hFj'.2) (eXi K i r hEi'.2) (stepF_spanned j hFj')
    (stepE_spanned i hEi') ((crosslW K i j hEi hFj hFj' hEi' Y).comp
      (crossrW K i j hFj' hEi' hEi hFj Y)).toAddHom
    (if i.castSucc = j.succ then -BHom.id _ else BHom.id _ : BHom _ _).toAddHom
    (BRing.tmul _ _ (eXi K j p hFj'.2) 1) (BRing.tmul _ _ 1 (BRing.tmul _ _ (eXi K i r hEi'.2) 1))
    (fun z => ?_) (fun z => ?_) (fun z => ?_) (fun z => ?_) (fun y => ?_) z
  · rw [BHom.toAddHom_apply, BHom.toAddHom_apply, BHom.comp_apply, BHom.comp_apply,
      crossrW_dotF i j hFj' hEi' hEi hFj Y hij, crosslW_dotF i j hEi hFj hFj' hEi' Y hij]
  · rw [BHom.toAddHom_apply, BHom.toAddHom_apply]
    split_ifs
    · rw [BHom.neg_apply, BHom.id_apply, BHom.neg_apply, BHom.id_apply, mul_neg]
    · rw [BHom.id_apply, BHom.id_apply]
  · rw [BHom.toAddHom_apply, BHom.toAddHom_apply, BHom.comp_apply, BHom.comp_apply,
      crossrW_dotE i j hFj' hEi' hEi hFj Y hij, crosslW_dotE i j hEi hFj hFj' hEi' Y hij]
  · rw [BHom.toAddHom_apply, BHom.toAddHom_apply]
    split_ifs
    · rw [BHom.neg_apply, BHom.id_apply, BHom.neg_apply, BHom.id_apply, mul_neg]
    · rw [BHom.id_apply, BHom.id_apply]
  · rw [BHom.toAddHom_apply, BHom.toAddHom_apply, BHom.comp_apply,
      crossrW_one i j hFj' hEi' hEi hFj Y hij]
    split_ifs
    · rw [BHom.map_neg, crosslW_one i j hEi hFj hFj' hEi' Y hij]; rfl
    · rw [crosslW_one i j hEi hFj hFj' hEi' Y hij]; rfl

end DownUp

end Categorification.Flag

end

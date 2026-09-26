/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.GammaThree

/-!
# `Γ_N` of the downward crossing (KL III (6.9))

KL III, arXiv:0807.3250v1, §6.1.2, Definition 6.2, eq. (6.9) (TeX label `eq_gamma_dcross_down`,
`sln-2008-ArXiv.tex`).

In the path model of `Categorification.Flag.GammaWord`, a strand `F_i` is the *opposite*
bimodule of the strand `E_i` running between the same two regions in the other direction: both
are the ring `H_{t^{+i}}` (`ERing`), with the two actions exchanged (`stepB_false`). Hence
`Γ(F_i F_j 1)` is the opposite of `Γ(E_j E_i 1)` up to the swap of tensor factors (`swapIso`).

Comparing (6.8) with (6.9) term by term, `Γ_N` of the downward crossing
`F_i F_j 1 → F_j F_i 1` is the upward crossing `E_j E_i 1 → E_i E_j 1` transported along these
identifications (`crossDn`):

* `i · j = 0`: both are the swap `ξ_i^{α₁} ⊗ ξ_j^{α₂} ↦ ξ_j^{α₂} ⊗ ξ_i^{α₁}`;
* `i = j`: (6.9) is the divided difference `-∂ = ∂_{x_R x_L}` (the sums in (6.9) are those of
  (6.8) with `α₁`, `α₂` exchanged);
* `i → j` resp. `j → i`: (6.9) is `ξ_j^{α₂+1} ⊗ ξ_i^{α₁} − ξ_j^{α₂} ⊗ ξ_i^{α₁+1}` resp.
  `ξ_j^{α₂} ⊗ ξ_i^{α₁}`, which are (6.8) for `E_j E_i` read backwards.

## Main declarations

* `BRing.opB`, `BHom.opH` : the opposite bimodule and map; `BRing.swapIso` :
  `M^op ⊗ N^op ≅ (N ⊗ M)^op`; `BHom.swapConj` : transport of maps along it.
* `stepB_false` : `Γ(F_i)` is the opposite of `Γ(E_i)` (definitionally).
* `crossDn` : **`Γ_N` of the downward crossing** on the path model.
* `crossDn_rules` : its dot slides (`DotRules` with correction `-τ`, i.e. the nilHecke relations
  with `∂_{x_R x_L}` for `i = j`);
* `crossDn_one`, `tauDn_one` : the values at `1` (`0` if `i = j`, `ξ'_L − ξ'_R` if `i → j`, `1`
  otherwise), which together with `crossDn_rules` give (6.9) on all `ξ_i^{α₁} ⊗ ξ_j^{α₂}`.
-/

noncomputable section

namespace Categorification.Flag

universe u

/-! ### Opposite bimodules -/

namespace BRing

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]

/-- **The opposite bimodule**: the same ring with the two actions exchanged. -/
def opB (M : BRing A B) : BRing B A := ⟨M.T, M.right, M.left⟩

@[simp] theorem opB_T (M : BRing A B) : (opB M).T = M.T := rfl

variable (N : BRing A B) (M : BRing B C)

/-- The ring map `M^op ⊗ N^op → N ⊗ M`, `m ⊗ n ↦ n ⊗ m`. -/
def swapHom : TT (opB M) (opB N) →+* TT N M :=
  liftRingHom (inclR N M) (inclL N M) fun b => by
    show tmul N M 1 (M.left b) = tmul N M (N.right b) 1
    exact (tmul_right_one b).symm

/-- The ring map `N ⊗ M → M^op ⊗ N^op`, `n ⊗ m ↦ m ⊗ n`. -/
def swapInv : TT N M →+* TT (opB M) (opB N) :=
  liftRingHom (inclR (opB M) (opB N)) (inclL (opB M) (opB N)) fun b => by
    show tmul (opB M) (opB N) 1 (N.right b) = tmul (opB M) (opB N) (M.left b) 1
    exact (tmul_right_one (M := opB M) (N := opB N) b).symm

variable {N M}

theorem swapHom_tmul (m : M.T) (n : N.T) :
    swapHom N M (tmul (opB M) (opB N) m n) = tmul N M n m := by
  show tmul N M 1 m * tmul N M n 1 = _
  rw [tmul_mul_tmul, one_mul, mul_one]

theorem swapInv_tmul (n : N.T) (m : M.T) :
    swapInv N M (tmul N M n m) = tmul (opB M) (opB N) m n := by
  show tmul (opB M) (opB N) 1 n * tmul (opB M) (opB N) m 1 = _
  rw [tmul_mul_tmul, one_mul, mul_one]

variable (N M)

theorem swapInv_swapHom : (swapInv N M).comp (swapHom N M) = RingHom.id _ :=
  ringHom_ext fun m n => by
    rw [RingHom.comp_apply, swapHom_tmul, swapInv_tmul, RingHom.id_apply]

theorem swapHom_swapInv : (swapHom N M).comp (swapInv N M) = RingHom.id _ :=
  ringHom_ext fun n m => by
    rw [RingHom.comp_apply, swapInv_tmul, swapHom_tmul, RingHom.id_apply]

/-- **`M^op ⊗ N^op ≅ (N ⊗ M)^op`**, `m ⊗ n ↦ n ⊗ m`. -/
def swapIso : BIso ((opB M).tensor (opB N)) (opB (N.tensor M)) :=
  BIso.ofRingEquiv (RingEquiv.ofHomInv (swapHom N M) (swapInv N M) (swapInv_swapHom N M)
      (swapHom_swapInv N M))
    (fun c => by
      show swapHom N M (tmul (opB M) (opB N) (M.right c) 1) = tmul N M 1 (M.right c)
      rw [swapHom_tmul])
    (fun a => by
      show swapHom N M (tmul (opB M) (opB N) 1 (N.left a)) = tmul N M (N.left a) 1
      rw [swapHom_tmul])

variable {N M}

theorem swapIso_hom_tmul (m : M.T) (n : N.T) :
    (swapIso N M).hom (tmul (opB M) (opB N) m n) = tmul N M n m := swapHom_tmul m n

theorem swapIso_inv_tmul (n : N.T) (m : M.T) :
    (swapIso N M).inv (tmul N M n m) = tmul (opB M) (opB N) m n := swapInv_tmul n m

theorem swapIso_inv_apply (y : TT N M) : (swapIso N M).inv y = swapInv N M y := rfl

end BRing

namespace BHom

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]

/-- **The opposite of a bimodule map** (the same function). -/
def opH {M N : BRing A B} (φ : BHom M N) : BHom (BRing.opB M) (BRing.opB N) :=
  ⟨φ.toFun, φ.map_add, φ.map_right, φ.map_left⟩

theorem opH_apply {M N : BRing A B} (φ : BHom M N) (x : M.T) : opH φ x = φ x := rfl

variable {B' B'' : Type u} [CommRing B'] [CommRing B''] {N : BRing A B} {M : BRing B C}
  {N' : BRing A B'} {M' : BRing B' C} {N'' : BRing A B''} {M'' : BRing B'' C}

/-- **Transport of a map `N ⊗ M → N' ⊗ M'` to `M^op ⊗ N^op → M'^op ⊗ N'^op`.** -/
def swapConj (φ : BHom (N.tensor M) (N'.tensor M')) :
    BHom ((BRing.opB M).tensor (BRing.opB N)) ((BRing.opB M').tensor (BRing.opB N')) :=
  (BRing.swapIso N' M').inv.comp ((opH φ).comp (BRing.swapIso N M).hom)

theorem swapConj_apply (φ : BHom (N.tensor M) (N'.tensor M'))
    (y : ((BRing.opB M).tensor (BRing.opB N)).T) :
    swapConj φ y = BRing.swapInv N' M' (φ (BRing.swapHom N M y)) := rfl

theorem swapConj_comp (φ : BHom (N.tensor M) (N'.tensor M'))
    (ψ : BHom (N'.tensor M') (N''.tensor M'')) :
    swapConj (ψ.comp φ) = (swapConj ψ).comp (swapConj φ) := by
  ext y
  simp only [swapConj_apply, comp_apply]
  rw [← RingHom.comp_apply (BRing.swapHom N' M') (BRing.swapInv N' M'), BRing.swapHom_swapInv,
    RingHom.id_apply]

theorem swapConj_add (φ ψ : BHom (N.tensor M) (N'.tensor M')) :
    swapConj (φ + ψ) = swapConj φ + swapConj ψ := by
  ext y; simp only [swapConj_apply, add_apply]; exact _root_.map_add (BRing.swapInv N' M') _ _

theorem swapConj_sub (φ ψ : BHom (N.tensor M) (N'.tensor M')) :
    swapConj (φ - ψ) = swapConj φ - swapConj ψ := by
  ext y; simp only [swapConj_apply, sub_apply]; exact _root_.map_sub (BRing.swapInv N' M') _ _

theorem swapConj_neg (φ : BHom (N.tensor M) (N'.tensor M')) :
    swapConj (-φ) = -swapConj φ := by
  ext y; simp only [swapConj_apply, neg_apply]; exact _root_.map_neg (BRing.swapInv N' M') _

theorem swapConj_zero : swapConj (0 : BHom (N.tensor M) (N'.tensor M')) = 0 := by
  ext y; simp only [swapConj_apply, zero_apply]; exact _root_.map_zero (BRing.swapInv N' M')

theorem swapConj_mulB (n : N.T) (m : M.T) :
    swapConj (mulB (BRing.tmul N M n m)) = mulB (BRing.tmul (BRing.opB M) (BRing.opB N) m n) := by
  ext y
  simp only [swapConj_apply, mulB_apply, map_mul]
  rw [BRing.swapInv_tmul, ← RingHom.comp_apply (BRing.swapInv N M) (BRing.swapHom N M),
    BRing.swapInv_swapHom, RingHom.id_apply]

theorem swapConj_one (φ : BHom (N.tensor M) (N'.tensor M')) :
    swapConj φ 1 = BRing.swapInv N' M' (φ 1) := by
  rw [swapConj_apply, map_one]

end BHom


/-! ### Two strands: polynomials in the dots -/

section Two

open MvPolynomial

variable {K : Type u} [CommRing K] {A B B' C : Type u} [CommRing A] [Algebra K A] [CommRing B]
  [CommRing B'] [CommRing C]

variable (K) in
/-- The polynomials in the two dots of `L₁ ⊗ L₂`: `x₀ ↦ ξ₁ ⊗ 1`, `x₁ ↦ 1 ⊗ ξ₂`. -/
def ev2 (L₁ : BRing A B) (L₂ : BRing B C) (ξ₁ : L₁.T) (ξ₂ : L₂.T) :
    MvPolynomial (Fin 2) K →+* (L₁.tensor L₂).T :=
  eval₂Hom ((L₁.tensor L₂).left.comp (algebraMap K A)) ![BRing.tmul _ _ ξ₁ 1, BRing.tmul _ _ 1 ξ₂]

/-- **A two-strand map with nilHecke-type dot slides on polynomials in the dots**:
`φ(q · y) = (∂_{x₀x₁} q) τ(y) + (s q) φ(y)`. -/
theorem DotRules.eval2 {L₁ : BRing A B} {L₂ : BRing B C} {L₁' : BRing A B'} {L₂' : BRing B' C}
    {φ τ : BHom (L₁.tensor L₂) (L₁'.tensor L₂')} {ξ₁ : L₁.T} {ξ₂ : L₂.T} {ξ₁' : L₁'.T}
    {ξ₂' : L₂'.T} (hr : DotRules φ τ ξ₁ ξ₂ ξ₁' ξ₂') (q : MvPolynomial (Fin 2) K)
    (y : (L₁.tensor L₂).T) :
    φ (ev2 K L₁ L₂ ξ₁ ξ₂ q * y) = ev2 K L₁' L₂' ξ₁' ξ₂' (ddiff 0 1 q) * τ y +
      ev2 K L₁' L₂' ξ₁' ξ₂' (rename (Equiv.swap 0 1) q) * φ y := by
  have e0 : ∀ (L : BRing A B) (L' : BRing B C) (a : L.T) (b : L'.T),
      ev2 K L L' a b (X 0) = BRing.tmul _ _ a 1 := fun _ _ _ _ => eval₂Hom_X' _ _ 0
  have e1 : ∀ (L : BRing A B) (L' : BRing B C) (a : L.T) (b : L'.T),
      ev2 K L L' a b (X 1) = BRing.tmul _ _ 1 b := fun _ _ _ _ => eval₂Hom_X' _ _ 1
  have e0' : ∀ (L : BRing A B') (L' : BRing B' C) (a : L.T) (b : L'.T),
      ev2 K L L' a b (X 0) = BRing.tmul _ _ a 1 := fun _ _ _ _ => eval₂Hom_X' _ _ 0
  have e1' : ∀ (L : BRing A B') (L' : BRing B' C) (a : L.T) (b : L'.T),
      ev2 K L L' a b (X 1) = BRing.tmul _ _ 1 b := fun _ _ _ _ => eval₂Hom_X' _ _ 1
  have t0 : ∀ y, τ (ev2 K L₁ L₂ ξ₁ ξ₂ (X 0) * y) = ev2 K L₁' L₂' ξ₁' ξ₂' (X 0) * τ y := by
    intro y; rw [e0, e0']; exact BHom.congr_apply hr.τL y
  have t1 : ∀ y, τ (ev2 K L₁ L₂ ξ₁ ξ₂ (X 1) * y) = ev2 K L₁' L₂' ξ₁' ξ₂' (X 1) * τ y := by
    intro y; rw [e1, e1']; exact BHom.congr_apply hr.τR y
  refine eval_twisted (ev2 K L₁ L₂ ξ₁ ξ₂) (ev2 K L₁' L₂' ξ₁' ξ₂') φ τ 0 1 (by decide)
    (BHom.map_add _) (fun i y => ?_) (fun c y => ?_) (fun y => ?_) (fun y => ?_)
    (fun i hi0 hi1 y => ?_) q y
  · fin_cases i
    · exact t0 y
    · exact t1 y
  · rw [show ev2 K L₁ L₂ ξ₁ ξ₂ (MvPolynomial.C c) = _ from eval₂Hom_C _ _ c,
      show ev2 K L₁' L₂' ξ₁' ξ₂' (MvPolynomial.C c) = _ from eval₂Hom_C _ _ c]
    exact BHom.map_left _ _ _
  · rw [e0, e1']; exact BHom.congr_apply hr.φL y
  · rw [e1, e0']; exact BHom.congr_apply hr.φR y
  · fin_cases i
    · exact absurd rfl hi0
    · exact absurd rfl hi1

end Two

/-! ### The downward crossing -/

section Down

variable {K : Type u} [Field K] {m : ℕ}

/-- **`Γ(F_i)` is the opposite of `Γ(E_i)`**: the strand `F_i` from `t` to `r` (`r = t^{+i}`) and
the strand `E_i` from `r` to `t` are the same ring `H_{t^{+i}}` with the actions exchanged. -/
theorem stepB_false (i : Fin m) {r t : Comp m} (h : StepR (false, i) r t) :
    stepB K (false, i) r t h = BRing.opB (stepB K (true, i) t r h) := rfl

/-- The dot of `F_i` is the dot of `E_i`. -/
theorem xiStep_false (i : Fin m) {r t : Comp m} (h : StepR (false, i) r t) :
    xiStep K (false, i) r t h = xiStep K (true, i) t r h := rfl

variable (K) in
/-- **`Γ_N` of the downward crossing** `F_i F_j 1_{r₂} → F_j F_i 1_{r₂}` (KL III (6.9)) on the
path model: the upward crossing `E_j E_i 1_t → E_i E_j 1_t` (`crossU`), transported along
`Γ(F_i F_j 1) ≅ Γ(E_j E_i 1)^op`. -/
def crossDn (i j : Fin m) {t r₁ r₂ r₁' : Comp m} (h₁ : StepR (false, i) r₁ t)
    (h₂ : StepR (false, j) r₂ r₁) (h₁' : StepR (false, j) r₁' t) (h₂' : StepR (false, i) r₂ r₁') :
    BHom ((stepB K (false, i) r₁ t h₁).tensor (stepB K (false, j) r₂ r₁ h₂))
      ((stepB K (false, j) r₁' t h₁').tensor (stepB K (false, i) r₂ r₁' h₂')) :=
  BHom.swapConj (N := stepB K (true, j) r₁ r₂ h₂) (M := stepB K (true, i) t r₁ h₁)
    (N' := stepB K (true, i) r₁' r₂ h₂') (M' := stepB K (true, j) t r₁' h₁')
    (crossU K j i (h₂ : StepR (true, j) r₁ r₂) (h₁ : StepR (true, i) t r₁)
      (h₂' : StepR (true, i) r₁' r₂) (h₁' : StepR (true, j) t r₁'))

variable (K) in
/-- The correction term of the dot slides of `crossDn` (the identification of source and target if
`i = j`, zero otherwise). -/
def tauDn (i j : Fin m) {t r₁ r₂ r₁' : Comp m} (h₁ : StepR (false, i) r₁ t)
    (h₂ : StepR (false, j) r₂ r₁) (h₁' : StepR (false, j) r₁' t) (h₂' : StepR (false, i) r₂ r₁') :
    BHom ((stepB K (false, i) r₁ t h₁).tensor (stepB K (false, j) r₂ r₁ h₂))
      ((stepB K (false, j) r₁' t h₁').tensor (stepB K (false, i) r₂ r₁' h₂')) :=
  BHom.swapConj (N := stepB K (true, j) r₁ r₂ h₂) (M := stepB K (true, i) t r₁ h₁)
    (N' := stepB K (true, i) r₁' r₂ h₂') (M' := stepB K (true, j) t r₁' h₁')
    (tauU K j i (h₂ : StepR (true, j) r₁ r₂) (h₁ : StepR (true, i) t r₁)
      (h₂' : StepR (true, i) r₁' r₂) (h₁' : StepR (true, j) t r₁'))

variable (i j : Fin m) {t r₁ r₂ r₁' : Comp m} (h₁ : StepR (false, i) r₁ t)
  (h₂ : StepR (false, j) r₂ r₁) (h₁' : StepR (false, j) r₁' t) (h₂' : StepR (false, i) r₂ r₁')

/-- **Dot slides of the downward crossing** (KL III (6.9)): with `ξ_L = ξ_i`, `ξ_R = ξ_j` the dots
of `F_i F_j 1` and `ξ'_L = ξ_j`, `ξ'_R = ξ_i` those of `F_j F_i 1`,
`ψ ξ_L = ξ'_R ψ + τ`, `ψ ξ_R = ξ'_L ψ − τ`: the nilHecke relations with `∂_{x_R x_L}` for
`i = j` (`DotRules` with correction `-τ`). -/
theorem crossDn_rules : DotRules (crossDn K i j h₁ h₂ h₁' h₂') (-tauDn K i j h₁ h₂ h₁' h₂')
    (eXi K i t h₁.2) (eXi K j r₁ h₂.2) (eXi K j t h₁'.2) (eXi K i r₁' h₂'.2) := by
  have hL := crossU_xiL (K := K) j i (h₂ : StepR (true, j) r₁ r₂) (h₁ : StepR (true, i) t r₁)
    (h₂' : StepR (true, i) r₁' r₂) (h₁' : StepR (true, j) t r₁')
  have hR := crossU_xiR (K := K) j i (h₂ : StepR (true, j) r₁ r₂) (h₁ : StepR (true, i) t r₁)
    (h₂' : StepR (true, i) r₁' r₂) (h₁' : StepR (true, j) t r₁')
  have tL := tauU_xiL (K := K) j i (h₂ : StepR (true, j) r₁ r₂) (h₁ : StepR (true, i) t r₁)
    (h₂' : StepR (true, i) r₁' r₂) (h₁' : StepR (true, j) t r₁')
  have tR := tauU_xiR (K := K) j i (h₂ : StepR (true, j) r₁ r₂) (h₁ : StepR (true, i) t r₁)
    (h₂' : StepR (true, i) r₁' r₂) (h₁' : StepR (true, j) t r₁')
  replace hL := congrArg BHom.swapConj hL
  replace hR := congrArg BHom.swapConj hR
  replace tL := congrArg BHom.swapConj tL
  replace tR := congrArg BHom.swapConj tR
  simp only [BHom.swapConj_comp, BHom.swapConj_add, BHom.swapConj_sub,
    BHom.swapConj_mulB] at hL hR tL tR
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `ψ ξ_L = −τ + ξ'_R ψ`, from the upward slide of the right strand
    ext y
    have := BHom.congr_apply hR y
    simp only [BHom.comp_apply, BHom.sub_apply, BHom.add_apply, BHom.neg_apply,
      BHom.mulB_apply] at this ⊢
    rw [← sub_eq_neg_add]
    exact this
  · ext y
    have := BHom.congr_apply hL y
    simp only [BHom.comp_apply, BHom.sub_apply, BHom.add_apply, BHom.neg_apply,
      BHom.mulB_apply] at this ⊢
    rw [sub_neg_eq_add]
    exact this.trans (add_comm _ _)
  · ext y
    have := BHom.congr_apply tR y
    simp only [BHom.comp_apply, BHom.neg_apply, BHom.mulB_apply, BHom.map_neg, mul_neg] at this ⊢
    exact congrArg Neg.neg this
  · ext y
    have := BHom.congr_apply tL y
    simp only [BHom.comp_apply, BHom.neg_apply, BHom.mulB_apply, BHom.map_neg, mul_neg] at this ⊢
    exact congrArg Neg.neg this

/-- **The value of the downward crossing at `1`** (KL III (6.9) at `α₁ = α₂ = 0`): `0` if
`i = j`, `ξ'_L − ξ'_R = ξ_j ⊗ 1 − 1 ⊗ ξ_i` if `j = i + 1` (`i → j`), and `1` otherwise. -/
theorem crossDn_one : crossDn K i j h₁ h₂ h₁' h₂' 1 =
    if j = i then 0 else if j.castSucc = i.succ then
      BRing.tmul _ _ (eXi K j t h₁'.2) 1 - BRing.tmul _ _ 1 (eXi K i r₁' h₂'.2) else 1 := by
  unfold crossDn
  rw [BHom.swapConj_one, crossU_one]
  split_ifs
  · exact map_zero _
  · rw [map_sub, BRing.swapInv_tmul, BRing.swapInv_tmul]
    rfl
  · exact map_one _

theorem tauDn_one : tauDn K i j h₁ h₂ h₁' h₂' 1 = if j = i then 1 else 0 := by
  unfold tauDn
  rw [BHom.swapConj_one, tauU_one]
  split_ifs
  · exact map_one _
  · exact map_zero _

/-- **KL III (6.9) on all polynomials in the dots**: on `q(ξ_i ⊗ 1, 1 ⊗ ξ_j)` (e.g.
`ξ_i^{α₁} ⊗ ξ_j^{α₂}` for `q = x₀^{α₁} x₁^{α₂}`), the downward crossing is `−∂_{x₀x₁} q` if
`i = j` and `(s q) · ψ(1)` otherwise, evaluated at the dots `ξ_j ⊗ 1`, `1 ⊗ ξ_i` of the target. -/
theorem crossDn_eval (q : MvPolynomial (Fin 2) K) :
    crossDn K i j h₁ h₂ h₁' h₂' (ev2 K (stepB K _ _ _ h₁) (stepB K _ _ _ h₂) (eXi K i t h₁.2)
        (eXi K j r₁ h₂.2) q) =
      if j = i then -ev2 K (stepB K _ _ _ h₁') (stepB K _ _ _ h₂') (eXi K j t h₁'.2)
        (eXi K i r₁' h₂'.2) (ddiff 0 1 q) else
        ev2 K (stepB K _ _ _ h₁') (stepB K _ _ _ h₂') (eXi K j t h₁'.2) (eXi K i r₁' h₂'.2)
          (MvPolynomial.rename (Equiv.swap 0 1) q) * crossDn K i j h₁ h₂ h₁' h₂' 1 := by
  have := (crossDn_rules (K := K) i j h₁ h₂ h₁' h₂').eval2 q 1
  rw [mul_one, BHom.neg_apply, tauDn_one] at this
  rw [this]
  split_ifs with h
  · rw [crossDn_one, if_pos h, mul_zero, add_zero, mul_neg, mul_one]
  · rw [neg_zero, mul_zero, zero_add]

end Down

end Categorification.Flag

end

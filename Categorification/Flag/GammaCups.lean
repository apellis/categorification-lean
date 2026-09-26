/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.GammaWhisker

/-!
# Cups, caps and biadjointness on the path model (KL III Definition 6.1)

Khovanov–Lauda III, arXiv:0807.3250v1, §6.1.1 (TeX `sln-2008-ArXiv.tex`, Definition 6.1,
label `def_biadjoint`, eqs. (6.2)–(6.5)) and the biadjointness part of Proposition 6.3.

With the conventions of `Categorification.Flag.GammaWord`, for compositions `s`, `s' = +_i s` and
`P : StepR (true, i) s s'` (equivalently `StepR (false, i) s' s`) the strands are

* `E = stepB (true, i) s s'`, a `(H_{s'}, H_s)`-bimodule, and
* `F = stepB (false, i) s' s`, a `(H_s, H_{s'})`-bimodule,

both with underlying ring `H_{s^{+i}} = ERing K i s`. The 1-morphism `F E 1_s` is the ring
`H_{s^{+i}} ⊗_{H_{s'}} H_{s^{+i}}` of `Categorification.Flag.Cups` (`feEquiv`), and `E F 1_{s'}`
is the ring `H_{s^{+i}} ⊗_{H_s} H_{s^{+i}}` of `Categorification.Flag.CupsMirror` (`efEquiv`).

## Main definitions and results

* `cupFE` : the element `∑_f (-1)^{d-f} ξ^f ⊗ x(s)_{i,d-f}` of `F E 1_s` (KL III (6.2)), central
  for the `H_s`-bimodule structure (`cupFE_central`, from KL III Corollary 5.5);
* `cupFEW X : X → F ⊗ (E ⊗ X)`: **`Γ` of the cup `1_s → F E 1_s`** (KL III (6.2)), whiskered by
  an arbitrary 1-morphism `X` on the right; a bimodule map;
* `capEFP : E F 1_{s'} → H_{s'}` : `Γ` of the cap `E F 1_{s'} → 1_{s'}` (KL III (6.5)), a map of
  `H_{s'}`-bimodules (`capEFP_left`, `capEFP_right`); `capEFW Y : E ⊗ (F ⊗ Y) → Y`, whiskered;
* `cupEF`, `cupEFW` (KL III (6.3)) and `capFEP`, `capFEW` (KL III (6.4)): the other cup and cap;
* **the four zigzag identities** (KL III (3.1), (3.2): the biadjointness relations of
  Definition 3.1, checked for `Γ_N` in Proposition 6.3), on `E ⊗ X` resp. `F ⊗ X` for every
  1-morphism `X` (hence at every position of every path, whiskering on the left by `atPrefix`):
  `zigzag_E` (`(cap_EF ∘ 1_E) ∘ (1_E ∘ cup_FE) = 1_E`), `zigzag_F`
  (`(1_F ∘ cap_EF) ∘ (cup_FE ∘ 1_F) = 1_F`), `zigzag_F'` (`(cap_FE ∘ 1_F) ∘ (1_F ∘ cup_EF) = 1_F`),
  `zigzag_E'` (`(1_E ∘ cap_FE) ∘ (cup_EF ∘ 1_E) = 1_E`);
* `cycDot_F`, `cycDot_F'` : **cyclicity of dots** (KL III (3.3); relations `cycDotL`, `cycDotR` of
  `Categorification.Diagrams.KL3.Relations`): both rotations of the upward dot (`rotDotL`,
  `rotDotR`) are `Γ` of the downward dot (multiplication by `ξ_i` on the strand `F_i`);
* `bubbleFEW_eq` : `Γ` of the counterclockwise dotted bubble is multiplication by `bubbleFEH`,
  so the bubble relations of `Categorification.Flag.Bubbles` (positivity, normalization, infinite
  Grassmannian relation) hold for `Γ_N` of bubbles.

These are transported from the Borel-model statements of `Categorification.Flag.Adjunction` and
`Categorification.Flag.Bubbles` (`snake_*`, `bubbleFE`).
-/

noncomputable section

open scoped TensorProduct

namespace Categorification.Flag

universe u

variable {K : Type u} [Field K] {m : ℕ}

attribute [local instance] rightAlgebra midAlgebra

variable (i : Fin m) {s s' : Comp m} (hE : StepR (true, i) s s') (hF : StepR (false, i) s' s)

/-- The strand `E_i` from `s` to `s'`. -/
abbrev Est : BRing (H K s') (H K s) := stepB K (true, i) s s' hE

/-- The strand `F_i` from `s'` to `s`. -/
abbrev Fst : BRing (H K s) (H K s') := stepB K (false, i) s' s hF

/-! ### `F E 1_s` -/

variable (K) in
/-- The middle ring of `F E 1_s`: `H_{s'} ≅ BorelRing (move)`. -/
def feB : H K s' ≃ₐ[K] BorelRing K (moveLab (Sigma.fst : Gen s → Fin (m + 1)) (movedVar i s hE.2)
    i.castSucc) :=
  (hCast K hE.1.symm).trans (borelEquivH' K _ (raise i s) (card_moveLab i s hE.2)).symm

variable (K) in
/-- **`F E 1_s` is the ring of `Categorification.Flag.Cups`**. -/
def feEquiv : BRing.TT (Fst (K := K) i hF) (Est (K := K) i hE) ≃+*
    CupRing K (Sigma.fst : Gen s → Fin (m + 1)) (movedVar i s hE.2) i.castSucc :=
  BRing.tensorRingEquiv (Fst (K := K) i hF) (Est (K := K) i hE) (feB K i hE).toRingEquiv
    (RingEquiv.refl _) (RingEquiv.refl _) (fun _ => rfl) (fun _ => rfl)

theorem feEquiv_tmul (a b : ERing K i s hE.2) :
    feEquiv K i hE hF (BRing.tmul _ _ a b) = a ⊗ₜ b := by
  unfold feEquiv
  rw [BRing.tensorRingEquiv_tmul]
  rfl

/-- The size `d = s_i` of block `i` (KL III: `k_i - k_{i-1}`). -/
abbrev dFE : ℕ := dBlock (Sigma.fst : Gen s → Fin (m + 1)) (movedVar i s hE.2) i.castSucc

/-- `x(s)_{i,β} ∈ H_{s^{+i}}`. -/
abbrev xsFE (β : ℕ) : ERing K i s hE.2 :=
  xs (k := K) (lab := (Sigma.fst : Gen s → Fin (m + 1))) (v₀ := movedVar i s hE.2) i.castSucc β

variable (K) in
/-- **The cup element** `∑_{f ≤ d} (-1)^{d-f} ξ^f ⊗ x(s)_{i,d-f}` of `F E 1_s` (KL III (6.2),
Corollary 5.5). -/
def cupFE : (Fst (K := K) i hF).tensor (Est (K := K) i hE) |>.T :=
  ∑ f ∈ Finset.range (dFE i hE + 1), BRing.tmul (Fst (K := K) i hF) (Est (K := K) i hE)
    ((-1) ^ (dFE i hE - f) * eXi K i s hE.2 ^ f : ERing K i s hE.2) (xsFE i hE (dFE i hE - f))

theorem feEquiv_cupFE :
    feEquiv K i hE hF (cupFE K i hE hF) =
      cupEltKL K (Sigma.fst : Gen s → Fin (m + 1)) (movedVar i s hE.2) i.castSucc := by
  rw [cupFE, map_sum, cupEltKL]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [feEquiv_tmul, ← neg_one_pow_tmul_one, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rfl

/-- **The cup element is central** (KL III Corollary 5.5): `(a ⊗ 1) c = (1 ⊗ a) c` for `a ∈ H_s`. -/
theorem cupFE_central (a : H K s) :
    ((Fst (K := K) i hF).tensor (Est (K := K) i hE)).left a * cupFE K i hE hF =
      ((Fst (K := K) i hF).tensor (Est (K := K) i hE)).right a * cupFE K i hE hF := by
  apply (feEquiv K i hE hF).injective
  rw [map_mul, map_mul, feEquiv_cupFE, BRing.tensor_left, BRing.tensor_right, feEquiv_tmul,
    feEquiv_tmul]
  exact cupEltKL_bimodule i s hE.2 a

variable (K) in
/-- **`Γ` of the cup `1_s → F_i E_i 1_s`** (KL III (6.2)), whiskered by `X` on the right:
`x ↦ ∑_f (-1)^{d-f} ξ^f ⊗ (x(s)_{i,d-f} ⊗ x)`. -/
def cupFEW {C : Type u} [CommRing C] (X : BRing (H K s) C) :
    BHom X ((Fst (K := K) i hF).tensor ((Est (K := K) i hE).tensor X)) where
  toFun x := (BRing.assoc (Fst (K := K) i hF) (Est (K := K) i hE) X).hom
    (BRing.tmul _ X (cupFE K i hE hF) x)
  map_add x y := by rw [BRing.tmul_add, BHom.map_add]
  map_left a x := by
    rw [← BRing.tmul_balance, ← cupFE_central]
    have : BRing.tmul _ X (((Fst (K := K) i hF).tensor (Est (K := K) i hE)).left a *
        cupFE K i hE hF) x = (((Fst (K := K) i hF).tensor (Est (K := K) i hE)).tensor X).left a *
          BRing.tmul _ X (cupFE K i hE hF) x := by
      rw [BRing.tensor_left (M := (Fst (K := K) i hF).tensor (Est (K := K) i hE)) (N := X),
        BRing.tmul_mul_tmul, one_mul]
    rw [this, BHom.map_left]
  map_right d x := by
    have : BRing.tmul _ X (cupFE K i hE hF) (X.right d * x) =
        (((Fst (K := K) i hF).tensor (Est (K := K) i hE)).tensor X).right d *
          BRing.tmul _ X (cupFE K i hE hF) x := by
      rw [BRing.tensor_right (M := (Fst (K := K) i hF).tensor (Est (K := K) i hE)) (N := X),
        BRing.tmul_mul_tmul, one_mul]
    rw [this, BHom.map_right]

/-! ### `E F 1_{s'}` and the cap -/

variable (K) in
/-- **`E F 1_{s'}` is the ring of `Categorification.Flag.CupsMirror`**. -/
def efEquiv : BRing.TT (Est (K := K) i hE) (Fst (K := K) i hF) ≃+*
    CupRingR (k := K) (Sigma.fst : Gen s → Fin (m + 1)) (movedVar i s hE.2) :=
  BRing.tensorRingEquiv (Est (K := K) i hE) (Fst (K := K) i hF) (hEquiv K s).toRingEquiv
    (RingEquiv.refl _) (RingEquiv.refl _) (fun _ => rfl) (fun _ => rfl)

theorem efEquiv_tmul (a b : ERing K i s hE.2) :
    efEquiv K i hE hF (BRing.tmul _ _ a b) = a ⊗ₜ b := by
  unfold efEquiv
  rw [BRing.tensorRingEquiv_tmul]
  rfl

variable (K) in
/-- **`Γ` of the cap `E_i F_i 1_{s'} → 1_{s'}`** (KL III (6.5)): `m ⊗ m' ↦ tr(m m')`, with values
in `H_{s'}`. -/
def capEFP (y : ((Est (K := K) i hE).tensor (Fst (K := K) i hF)).T) : H K s' :=
  hCast K hE.1 (borelEquivH' K _ (raise i s) (card_moveLab i s hE.2)
    (capEF K (Sigma.fst : Gen s → Fin (m + 1)) (movedVar i s hE.2) i.castSucc (efEquiv K i hE hF y)))

theorem capEFP_add (y y' : ((Est (K := K) i hE).tensor (Fst (K := K) i hF)).T) :
    capEFP K i hE hF (y + y') = capEFP K i hE hF y + capEFP K i hE hF y' := by
  simp only [capEFP, map_add]

/-- `E.left ∘ cap = p_2^* ∘ cap_EF`. -/
theorem Est_left_capEFP (y : ((Est (K := K) i hE).tensor (Fst (K := K) i hF)).T) :
    (Est (K := K) i hE).left (capEFP K i hE hF y) =
      pL K (Sigma.fst : Gen s → Fin (m + 1)) (movedVar i s hE.2) i.castSucc
        (capEF K (Sigma.fst : Gen s → Fin (m + 1)) (movedVar i s hE.2) i.castSucc
          (efEquiv K i hE hF y)) := by
  show eLeft K i s hE.2 (hCast K hE.1.symm (capEFP K i hE hF y)) = _
  rw [capEFP, hCast_trans_apply, hCast_rfl, eLeft, AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe,
    AlgHom.coe_coe, AlgEquiv.symm_apply_apply]

theorem Est_left_eq (a : H K s') :
    (Est (K := K) i hE).left a = pL K (Sigma.fst : Gen s → Fin (m + 1)) (movedVar i s hE.2)
      i.castSucc ((borelEquivH' K _ (raise i s) (card_moveLab i s hE.2)).symm
        (hCast K hE.1.symm a)) := rfl

theorem Fst_right_eq (a : H K s') :
    (Fst (K := K) i hF).right a = pL K (Sigma.fst : Gen s → Fin (m + 1)) (movedVar i s hE.2)
      i.castSucc ((borelEquivH' K _ (raise i s) (card_moveLab i s hE.2)).symm
        (hCast K hE.1.symm a)) := rfl

theorem hCast_borelEquivH'_symm (a : H K s') :
    hCast K hE.1 (borelEquivH' K _ (raise i s) (card_moveLab i s hE.2)
      ((borelEquivH' K _ (raise i s) (card_moveLab i s hE.2)).symm (hCast K hE.1.symm a))) = a := by
  rw [AlgEquiv.apply_symm_apply, hCast_trans_apply, hCast_rfl]

/-- The cap is a map of left `H_{s'}`-modules. -/
theorem capEFP_left (a : H K s') (y : ((Est (K := K) i hE).tensor (Fst (K := K) i hF)).T) :
    capEFP K i hE hF (((Est (K := K) i hE).tensor (Fst (K := K) i hF)).left a * y) =
      a * capEFP K i hE hF y := by
  rw [capEFP, map_mul, BRing.tensor_left, efEquiv_tmul, Est_left_eq i hE, capEF_left, map_mul,
    map_mul, hCast_borelEquivH'_symm i hE]
  rfl

/-- The cap is a map of right `H_{s'}`-modules. -/
theorem capEFP_right (a : H K s') (y : ((Est (K := K) i hE).tensor (Fst (K := K) i hF)).T) :
    capEFP K i hE hF (((Est (K := K) i hE).tensor (Fst (K := K) i hF)).right a * y) =
      a * capEFP K i hE hF y := by
  rw [capEFP, map_mul, BRing.tensor_right, efEquiv_tmul, Fst_right_eq i hE hF, capEF_right,
    map_mul, map_mul, hCast_borelEquivH'_symm i hE]
  rfl

variable (K) in
/-- The whiskered cap as an additive map `(E F) ⊗ Y → Y`. -/
def capEFAdd {C : Type u} [CommRing C] (Y : BRing (H K s') C) :
    BRing.TT ((Est (K := K) i hE).tensor (Fst (K := K) i hF)) Y →+ Y.T :=
  BRing.liftAdd
    { toFun := fun y => AddMonoidHom.mulLeft (Y.left (capEFP K i hE hF y))
      map_zero' := by
        ext x
        have : capEFP K i hE hF 0 = 0 := by simp [capEFP]
        simp [this]
      map_add' := fun y y' => by
        ext x
        simp only [AddMonoidHom.coe_mulLeft, AddMonoidHom.add_apply]
        rw [capEFP_add, map_add, add_mul] }
    (fun y a x => by
      show Y.left (capEFP K i hE hF (((Est (K := K) i hE).tensor (Fst (K := K) i hF)).right a * y)) *
        x = Y.left (capEFP K i hE hF y) * (Y.left a * x)
      rw [capEFP_right, map_mul]
      ring)

theorem capEFAdd_tmul {C : Type u} [CommRing C] (Y : BRing (H K s') C)
    (y : ((Est (K := K) i hE).tensor (Fst (K := K) i hF)).T) (x : Y.T) :
    capEFAdd K i hE hF Y (BRing.tmul _ Y y x) = Y.left (capEFP K i hE hF y) * x :=
  BRing.liftAdd_tmul _ _ y x

variable (K) in
/-- **`Γ` of the cap `E_i F_i 1_{s'} → 1_{s'}`**, whiskered by `Y` on the right. -/
def capEFW {C : Type u} [CommRing C] (Y : BRing (H K s') C) :
    BHom ((Est (K := K) i hE).tensor ((Fst (K := K) i hF).tensor Y)) Y where
  toFun z := capEFAdd K i hE hF Y ((BRing.assoc (Est (K := K) i hE) (Fst (K := K) i hF) Y).inv z)
  map_add z z' := by rw [BHom.map_add, map_add]
  map_left a z := by
    rw [BHom.map_left]
    refine BRing.induction_on (P := fun w => capEFAdd K i hE hF Y
      ((((Est (K := K) i hE).tensor (Fst (K := K) i hF)).tensor Y).left a * w) =
        Y.left a * capEFAdd K i hE hF Y w) _ (by simp) (fun y x => ?_) (fun w w' hw hw' => ?_)
    · beta_reduce
      rw [BRing.tensor_left (M := (Est (K := K) i hE).tensor (Fst (K := K) i hF)) (N := Y),
        BRing.tmul_mul_tmul, one_mul, capEFAdd_tmul, capEFAdd_tmul, capEFP_left, map_mul, mul_assoc]
    · beta_reduce at hw hw' ⊢
      rw [mul_add, map_add, hw, hw', map_add, mul_add]
  map_right d z := by
    rw [BHom.map_right]
    refine BRing.induction_on (P := fun w => capEFAdd K i hE hF Y
      ((((Est (K := K) i hE).tensor (Fst (K := K) i hF)).tensor Y).right d * w) =
        Y.right d * capEFAdd K i hE hF Y w) _ (by simp) (fun y x => ?_) (fun w w' hw hw' => ?_)
    · beta_reduce
      rw [BRing.tensor_right (M := (Est (K := K) i hE).tensor (Fst (K := K) i hF)) (N := Y),
        BRing.tmul_mul_tmul, one_mul, capEFAdd_tmul, capEFAdd_tmul, mul_left_comm]
    · beta_reduce at hw hw' ⊢
      rw [mul_add, map_add, hw, hw', map_add, mul_add]

theorem capEFW_tmul {C : Type u} [CommRing C] (Y : BRing (H K s') C) (a b : ERing K i s hE.2)
    (y : Y.T) :
    capEFW K i hE hF Y (BRing.tmul _ _ a (BRing.tmul _ Y b y)) =
      Y.left (capEFP K i hE hF (BRing.tmul _ _ a b)) * y := by
  show capEFAdd K i hE hF Y ((BRing.assoc _ _ Y).inv (BRing.tmul _ _ a (BRing.tmul _ Y b y))) = _
  rw [BRing.assoc_inv_tmul, capEFAdd_tmul]

/-! ### The zigzag identity -/

theorem cupFEW_apply {C : Type u} [CommRing C] (X : BRing (H K s) C) (x : X.T) :
    cupFEW K i hE hF X x = ∑ f ∈ Finset.range (dFE i hE + 1),
      BRing.tmul (Fst (K := K) i hF) ((Est (K := K) i hE).tensor X)
        ((-1) ^ (dFE i hE - f) * eXi K i s hE.2 ^ f : ERing K i s hE.2)
        (BRing.tmul _ X (xsFE i hE (dFE i hE - f)) x) := by
  show (BRing.assoc _ _ X).hom (BRing.tmul _ X (cupFE K i hE hF) x) = _
  rw [cupFE, BRing.sum_tmul, BHom.map_sum]
  exact Finset.sum_congr rfl fun f _ =>
    BRing.assoc_hom_tmul (M := Fst (K := K) i hF) (N := Est (K := K) i hE) (P := X) _ _ _

theorem Est_left_capEFP_tmul (a b : ERing K i s hE.2) :
    (Est (K := K) i hE).left (capEFP K i hE hF (BRing.tmul _ _ a b)) =
      pL K (Sigma.fst : Gen s → Fin (m + 1)) (movedVar i s hE.2) i.castSucc
        (capEF K (Sigma.fst : Gen s → Fin (m + 1)) (movedVar i s hE.2) i.castSucc (a ⊗ₜ b)) := by
  rw [Est_left_capEFP, efEquiv_tmul]

/-- **The zigzag identity** `(cap_EF ∘ 1_E) ∘ (1_E ∘ cup_FE) = 1_E` (KL III (3.1), Proposition 6.3)
on `E_i ⊗ X`, for every 1-morphism `X` to the right of `E_i`: `Γ_N` preserves the first
biadjointness relation. -/
theorem zigzag_E {C : Type u} [CommRing C] (X : BRing (H K s) C) :
    (capEFW K i hE hF ((Est (K := K) i hE).tensor X)).comp
        (BHom.whiskerLeft (Est (K := K) i hE) (cupFEW K i hE hF X)) = BHom.id _ := by
  refine BHom.ext_tensor fun a x => ?_
  rw [BHom.comp_apply, BHom.whiskerLeft_tmul, cupFEW_apply, BRing.tmul_sum, BHom.map_sum,
    BHom.id_apply]
  simp only [capEFW_tmul]
  have h1 : ∀ f, ((Est (K := K) i hE).tensor X).left (capEFP K i hE hF (BRing.tmul _ _ a
      ((-1) ^ (dFE i hE - f) * eXi K i s hE.2 ^ f : ERing K i s hE.2))) *
        BRing.tmul _ X (xsFE i hE (dFE i hE - f)) x =
      BRing.tmul _ X ((-1) ^ (dFE i hE - f) * pL K (Sigma.fst : Gen s → Fin (m + 1))
        (movedVar i s hE.2) i.castSucc (capEF K (Sigma.fst : Gen s → Fin (m + 1))
          (movedVar i s hE.2) i.castSucc (a ⊗ₜ (eXi K i s hE.2 ^ f))) *
            xsFE i hE (dFE i hE - f)) x := by
    intro f
    rw [BRing.tensor_left, BRing.tmul_mul_tmul, one_mul, Est_left_capEFP_tmul, capEF_tmul,
      capEF_tmul]
    congr 2
    have e : ((-1) ^ (dFE i hE - f) * eXi K i s hE.2 ^ f : ERing K i s hE.2) =
        pL K (Sigma.fst : Gen s → Fin (m + 1)) (movedVar i s hE.2) i.castSucc ((-1) ^ (dFE i hE - f)) *
          eXi K i s hE.2 ^ f := by
      rw [map_pow, map_neg, map_one]
    rw [e, mul_left_comm, trL_pL_mul, map_mul, map_pow, map_neg, map_one]
  simp only [h1]
  rw [← BRing.sum_tmul]
  congr 1
  exact snake_E_FE (Sigma.fst : Gen s → Fin (m + 1)) (movedVar i s hE.2) i.castSucc a

theorem Fst_right_capEFP_tmul (a b : ERing K i s hE.2) :
    (Fst (K := K) i hF).right (capEFP K i hE hF (BRing.tmul _ _ a b)) =
      pL K (Sigma.fst : Gen s → Fin (m + 1)) (movedVar i s hE.2) i.castSucc
        (capEF K (Sigma.fst : Gen s → Fin (m + 1)) (movedVar i s hE.2) i.castSucc (a ⊗ₜ b)) :=
  Est_left_capEFP_tmul i hE hF a b

/-- **The zigzag identity** `(1_F ∘ cap_EF) ∘ (cup_FE ∘ 1_F) = 1_F` (KL III (3.1),
Proposition 6.3) on `F_i ⊗ X`, for every 1-morphism `X` to the right of `F_i`. -/
theorem zigzag_F {C : Type u} [CommRing C] (X : BRing (H K s') C) :
    (BHom.whiskerLeft (Fst (K := K) i hF) (capEFW K i hE hF X)).comp
        (cupFEW K i hE hF ((Fst (K := K) i hF).tensor X)) = BHom.id _ := by
  refine BHom.ext_tensor fun a x => ?_
  rw [BHom.comp_apply, cupFEW_apply, BHom.map_sum, BHom.id_apply]
  simp only [BHom.whiskerLeft_tmul, capEFW_tmul]
  have h1 : ∀ f, BRing.tmul (Fst (K := K) i hF) X
      ((-1) ^ (dFE i hE - f) * eXi K i s hE.2 ^ f : ERing K i s hE.2)
      (X.left (capEFP K i hE hF (BRing.tmul _ _ (xsFE i hE (dFE i hE - f)) a)) * x) =
      BRing.tmul _ X ((-1) ^ (dFE i hE - f) * eXi K i s hE.2 ^ f *
        pL K (Sigma.fst : Gen s → Fin (m + 1)) (movedVar i s hE.2) i.castSucc
          (capEF K (Sigma.fst : Gen s → Fin (m + 1)) (movedVar i s hE.2) i.castSucc
            (xsFE i hE (dFE i hE - f) ⊗ₜ a))) x := by
    intro f
    rw [← BRing.tmul_balance, Fst_right_capEFP_tmul, mul_comm]
  simp only [h1]
  rw [← BRing.sum_tmul]
  congr 1
  exact snake_F_FE (Sigma.fst : Gen s → Fin (m + 1)) (movedVar i s hE.2) i.castSucc a

/-! ### The other cup and cap: `1_{s'} → E F 1_{s'}` and `F E 1_s → 1_s` -/

/-- The size `d = s_{i+1} - 1` (KL III: `k_{i+1} - k_i` for `k = s'`). -/
abbrev dEF : ℕ := dBlockR (Sigma.fst : Gen s → Fin (m + 1)) (movedVar i s hE.2)

/-- `x(s')_{i+1,β} ∈ H_{s^{+i}}`. -/
abbrev xsEF (β : ℕ) : ERing K i s hE.2 :=
  xsR (k := K) (Sigma.fst : Gen s → Fin (m + 1)) (movedVar i s hE.2) β

variable (K) in
/-- **The cup element** `∑_{g ≤ d} (-1)^{d-g} ξ^g ⊗ x(s')_{i+1,d-g}` of `E F 1_{s'}` (KL III (6.3),
Corollary 5.5). -/
def cupEF : ((Est (K := K) i hE).tensor (Fst (K := K) i hF)).T :=
  ∑ g ∈ Finset.range (dEF i hE + 1), BRing.tmul (Est (K := K) i hE) (Fst (K := K) i hF)
    ((-1) ^ (dEF i hE - g) * eXi K i s hE.2 ^ g : ERing K i s hE.2) (xsEF i hE (dEF i hE - g))

theorem efEquiv_cupEF :
    efEquiv K i hE hF (cupEF K i hE hF) =
      cupEltRKL K (Sigma.fst : Gen s → Fin (m + 1)) (movedVar i s hE.2) := by
  rw [cupEF, map_sum, cupEltRKL]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [efEquiv_tmul, ← neg_one_pow_tmul_one, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rfl

/-- **The cup element `cupEF` is central** (KL III Corollary 5.5, second map). -/
theorem cupEF_central (a : H K s') :
    ((Est (K := K) i hE).tensor (Fst (K := K) i hF)).left a * cupEF K i hE hF =
      ((Est (K := K) i hE).tensor (Fst (K := K) i hF)).right a * cupEF K i hE hF := by
  apply (efEquiv K i hE hF).injective
  rw [map_mul, map_mul, efEquiv_cupEF, BRing.tensor_left, BRing.tensor_right, efEquiv_tmul,
    efEquiv_tmul, Est_left_eq i hE, Fst_right_eq i hE hF]
  exact cupR_bimodule (Sigma.fst : Gen s → Fin (m + 1)) (movedVar i s hE.2) i.castSucc
    (Fin.castSucc_lt_succ i).ne
    ((borelEquivH' K _ (raise i s) (card_moveLab i s hE.2)).symm (hCast K hE.1.symm a))

variable (K) in
/-- **`Γ` of the cup `1_{s'} → E_i F_i 1_{s'}`** (KL III (6.3)), whiskered by `Y` on the right. -/
def cupEFW {C : Type u} [CommRing C] (Y : BRing (H K s') C) :
    BHom Y ((Est (K := K) i hE).tensor ((Fst (K := K) i hF).tensor Y)) where
  toFun y := (BRing.assoc (Est (K := K) i hE) (Fst (K := K) i hF) Y).hom
    (BRing.tmul _ Y (cupEF K i hE hF) y)
  map_add x y := by rw [BRing.tmul_add, BHom.map_add]
  map_left a x := by
    rw [← BRing.tmul_balance, ← cupEF_central]
    have : BRing.tmul _ Y (((Est (K := K) i hE).tensor (Fst (K := K) i hF)).left a *
        cupEF K i hE hF) x = (((Est (K := K) i hE).tensor (Fst (K := K) i hF)).tensor Y).left a *
          BRing.tmul _ Y (cupEF K i hE hF) x := by
      rw [BRing.tensor_left (M := (Est (K := K) i hE).tensor (Fst (K := K) i hF)) (N := Y),
        BRing.tmul_mul_tmul, one_mul]
    rw [this, BHom.map_left]
  map_right d x := by
    have : BRing.tmul _ Y (cupEF K i hE hF) (Y.right d * x) =
        (((Est (K := K) i hE).tensor (Fst (K := K) i hF)).tensor Y).right d *
          BRing.tmul _ Y (cupEF K i hE hF) x := by
      rw [BRing.tensor_right (M := (Est (K := K) i hE).tensor (Fst (K := K) i hF)) (N := Y),
        BRing.tmul_mul_tmul, one_mul]
    rw [this, BHom.map_right]

theorem cupEFW_apply {C : Type u} [CommRing C] (Y : BRing (H K s') C) (y : Y.T) :
    cupEFW K i hE hF Y y = ∑ g ∈ Finset.range (dEF i hE + 1),
      BRing.tmul (Est (K := K) i hE) ((Fst (K := K) i hF).tensor Y)
        ((-1) ^ (dEF i hE - g) * eXi K i s hE.2 ^ g : ERing K i s hE.2)
        (BRing.tmul _ Y (xsEF i hE (dEF i hE - g)) y) := by
  show (BRing.assoc _ _ Y).hom (BRing.tmul _ Y (cupEF K i hE hF) y) = _
  rw [cupEF, BRing.sum_tmul, BHom.map_sum]
  exact Finset.sum_congr rfl fun g _ =>
    BRing.assoc_hom_tmul (M := Est (K := K) i hE) (N := Fst (K := K) i hF) (P := Y) _ _ _

variable (K) in
/-- **`Γ` of the cap `F_i E_i 1_s → 1_s`** (KL III (6.4)): `m ⊗ m' ↦ tr(m m')`, in `H_s`. -/
def capFEP (y : ((Fst (K := K) i hF).tensor (Est (K := K) i hE)).T) : H K s :=
  (hEquiv K s).symm
    (capFE K (Sigma.fst : Gen s → Fin (m + 1)) (movedVar i s hE.2) i.castSucc (feEquiv K i hE hF y))

theorem capFEP_add (y y' : ((Fst (K := K) i hF).tensor (Est (K := K) i hE)).T) :
    capFEP K i hE hF (y + y') = capFEP K i hE hF y + capFEP K i hE hF y' := by
  simp only [capFEP, map_add]

/-- The cap `F E → 1` is a map of left `H_s`-modules. -/
theorem capFEP_left (a : H K s) (y : ((Fst (K := K) i hF).tensor (Est (K := K) i hE)).T) :
    capFEP K i hE hF (((Fst (K := K) i hF).tensor (Est (K := K) i hE)).left a * y) =
      a * capFEP K i hE hF y := by
  rw [capFEP, map_mul, BRing.tensor_left, feEquiv_tmul]
  show (hEquiv K s).symm (capFE K _ _ _ ((pR K _ _ (hEquiv K s a) ⊗ₜ 1) * _)) = _
  rw [capFE_left, map_mul, AlgEquiv.symm_apply_apply]
  rfl

/-- The cap `F E → 1` is a map of right `H_s`-modules. -/
theorem capFEP_right (a : H K s) (y : ((Fst (K := K) i hF).tensor (Est (K := K) i hE)).T) :
    capFEP K i hE hF (((Fst (K := K) i hF).tensor (Est (K := K) i hE)).right a * y) =
      a * capFEP K i hE hF y := by
  rw [capFEP, map_mul, BRing.tensor_right, feEquiv_tmul]
  show (hEquiv K s).symm (capFE K _ _ _ ((1 ⊗ₜ pR K _ _ (hEquiv K s a)) * _)) = _
  rw [capFE_right, map_mul, AlgEquiv.symm_apply_apply]
  rfl

variable (K) in
/-- The whiskered cap `F E → 1` as an additive map `(F E) ⊗ Y → Y`. -/
def capFEAdd {C : Type u} [CommRing C] (Y : BRing (H K s) C) :
    BRing.TT ((Fst (K := K) i hF).tensor (Est (K := K) i hE)) Y →+ Y.T :=
  BRing.liftAdd
    { toFun := fun y => AddMonoidHom.mulLeft (Y.left (capFEP K i hE hF y))
      map_zero' := by
        ext x
        have : capFEP K i hE hF 0 = 0 := by simp [capFEP]
        simp [this]
      map_add' := fun y y' => by
        ext x
        simp only [AddMonoidHom.coe_mulLeft, AddMonoidHom.add_apply]
        rw [capFEP_add, map_add, add_mul] }
    (fun y a x => by
      show Y.left (capFEP K i hE hF (((Fst (K := K) i hF).tensor (Est (K := K) i hE)).right a * y)) *
        x = Y.left (capFEP K i hE hF y) * (Y.left a * x)
      rw [capFEP_right, map_mul]
      ring)

theorem capFEAdd_tmul {C : Type u} [CommRing C] (Y : BRing (H K s) C)
    (y : ((Fst (K := K) i hF).tensor (Est (K := K) i hE)).T) (x : Y.T) :
    capFEAdd K i hE hF Y (BRing.tmul _ Y y x) = Y.left (capFEP K i hE hF y) * x :=
  BRing.liftAdd_tmul _ _ y x

variable (K) in
/-- **`Γ` of the cap `F_i E_i 1_s → 1_s`**, whiskered by `Y` on the right. -/
def capFEW {C : Type u} [CommRing C] (Y : BRing (H K s) C) :
    BHom ((Fst (K := K) i hF).tensor ((Est (K := K) i hE).tensor Y)) Y where
  toFun z := capFEAdd K i hE hF Y ((BRing.assoc (Fst (K := K) i hF) (Est (K := K) i hE) Y).inv z)
  map_add z z' := by rw [BHom.map_add, map_add]
  map_left a z := by
    rw [BHom.map_left]
    refine BRing.induction_on (P := fun w => capFEAdd K i hE hF Y
      ((((Fst (K := K) i hF).tensor (Est (K := K) i hE)).tensor Y).left a * w) =
        Y.left a * capFEAdd K i hE hF Y w) _ (by simp) (fun y x => ?_) (fun w w' hw hw' => ?_)
    · beta_reduce
      rw [BRing.tensor_left (M := (Fst (K := K) i hF).tensor (Est (K := K) i hE)) (N := Y),
        BRing.tmul_mul_tmul, one_mul, capFEAdd_tmul, capFEAdd_tmul, capFEP_left, map_mul, mul_assoc]
    · beta_reduce at hw hw' ⊢
      rw [mul_add, map_add, hw, hw', map_add, mul_add]
  map_right d z := by
    rw [BHom.map_right]
    refine BRing.induction_on (P := fun w => capFEAdd K i hE hF Y
      ((((Fst (K := K) i hF).tensor (Est (K := K) i hE)).tensor Y).right d * w) =
        Y.right d * capFEAdd K i hE hF Y w) _ (by simp) (fun y x => ?_) (fun w w' hw hw' => ?_)
    · beta_reduce
      rw [BRing.tensor_right (M := (Fst (K := K) i hF).tensor (Est (K := K) i hE)) (N := Y),
        BRing.tmul_mul_tmul, one_mul, capFEAdd_tmul, capFEAdd_tmul, mul_left_comm]
    · beta_reduce at hw hw' ⊢
      rw [mul_add, map_add, hw, hw', map_add, mul_add]

theorem capFEW_tmul {C : Type u} [CommRing C] (Y : BRing (H K s) C) (a b : ERing K i s hE.2)
    (y : Y.T) :
    capFEW K i hE hF Y (BRing.tmul _ _ a (BRing.tmul _ Y b y)) =
      Y.left (capFEP K i hE hF (BRing.tmul _ _ a b)) * y := by
  show capFEAdd K i hE hF Y ((BRing.assoc _ _ Y).inv (BRing.tmul _ _ a (BRing.tmul _ Y b y))) = _
  rw [BRing.assoc_inv_tmul, capFEAdd_tmul]

theorem pR_capFE_eq (a b : ERing K i s hE.2) :
    eRight K i s hE.2 (capFEP K i hE hF (BRing.tmul _ _ a b)) =
      pR K (Sigma.fst : Gen s → Fin (m + 1)) (movedVar i s hE.2)
        (capFE K (Sigma.fst : Gen s → Fin (m + 1)) (movedVar i s hE.2) i.castSucc (a ⊗ₜ b)) := by
  rw [capFEP, feEquiv_tmul, eRight, AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe,
    AlgEquiv.apply_symm_apply]

/-- **The zigzag identity** `(cap_FE ∘ 1_F) ∘ (1_F ∘ cup_EF) = 1_F` (KL III (3.2),
Proposition 6.3) on `F_i ⊗ X`, for every 1-morphism `X` to the right of `F_i`. -/
theorem zigzag_F' {C : Type u} [CommRing C] (X : BRing (H K s') C) :
    (capFEW K i hE hF ((Fst (K := K) i hF).tensor X)).comp
        (BHom.whiskerLeft (Fst (K := K) i hF) (cupEFW K i hE hF X)) = BHom.id _ := by
  refine BHom.ext_tensor fun a x => ?_
  rw [BHom.comp_apply, BHom.whiskerLeft_tmul, cupEFW_apply, BRing.tmul_sum, BHom.map_sum,
    BHom.id_apply]
  simp only [capFEW_tmul]
  have h1 : ∀ g, ((Fst (K := K) i hF).tensor X).left (capFEP K i hE hF (BRing.tmul _ _ a
      ((-1) ^ (dEF i hE - g) * eXi K i s hE.2 ^ g : ERing K i s hE.2))) *
        BRing.tmul _ X (xsEF i hE (dEF i hE - g)) x =
      BRing.tmul _ X ((-1) ^ (dEF i hE - g) * pR K (Sigma.fst : Gen s → Fin (m + 1))
        (movedVar i s hE.2) (capFE K (Sigma.fst : Gen s → Fin (m + 1))
          (movedVar i s hE.2) i.castSucc (a ⊗ₜ (eXi K i s hE.2 ^ g))) *
            xsEF i hE (dEF i hE - g)) x := by
    intro g
    rw [BRing.tensor_left, BRing.tmul_mul_tmul, one_mul]
    congr 1
    show eRight K i s hE.2 (capFEP K i hE hF _) * _ = _
    rw [pR_capFE_eq, capFE_tmul, capFE_tmul]
    congr 1
    have e : ((-1) ^ (dEF i hE - g) * eXi K i s hE.2 ^ g : ERing K i s hE.2) =
        pR K (Sigma.fst : Gen s → Fin (m + 1)) (movedVar i s hE.2) ((-1) ^ (dEF i hE - g)) *
          eXi K i s hE.2 ^ g := by
      rw [map_pow, map_neg, map_one]
    rw [e, mul_left_comm, trR_pR_mul, map_mul, map_pow, map_neg, map_one]
  simp only [h1]
  rw [← BRing.sum_tmul]
  congr 1
  exact snake_F_EF (Sigma.fst : Gen s → Fin (m + 1)) (movedVar i s hE.2) i.castSucc a

/-- **The zigzag identity** `(1_E ∘ cap_FE) ∘ (cup_EF ∘ 1_E) = 1_E` (KL III (3.2),
Proposition 6.3) on `E_i ⊗ X`, for every 1-morphism `X` to the right of `E_i`. -/
theorem zigzag_E' {C : Type u} [CommRing C] (X : BRing (H K s) C) :
    (BHom.whiskerLeft (Est (K := K) i hE) (capFEW K i hE hF X)).comp
        (cupEFW K i hE hF ((Est (K := K) i hE).tensor X)) = BHom.id _ := by
  refine BHom.ext_tensor fun a x => ?_
  rw [BHom.comp_apply, cupEFW_apply, BHom.map_sum, BHom.id_apply]
  simp only [BHom.whiskerLeft_tmul, capFEW_tmul]
  have h1 : ∀ g, BRing.tmul (Est (K := K) i hE) X
      ((-1) ^ (dEF i hE - g) * eXi K i s hE.2 ^ g : ERing K i s hE.2)
      (X.left (capFEP K i hE hF (BRing.tmul _ _ (xsEF i hE (dEF i hE - g)) a)) * x) =
      BRing.tmul _ X ((-1) ^ (dEF i hE - g) * eXi K i s hE.2 ^ g *
        pR K (Sigma.fst : Gen s → Fin (m + 1)) (movedVar i s hE.2)
          (capFE K (Sigma.fst : Gen s → Fin (m + 1)) (movedVar i s hE.2) i.castSucc
            (xsEF i hE (dEF i hE - g) ⊗ₜ a))) x := by
    intro g
    rw [← BRing.tmul_balance, mul_comm]
    congr 2
    exact pR_capFE_eq i hE hF _ _
  simp only [h1]
  rw [← BRing.sum_tmul]
  congr 1
  exact snake_E_EF (Sigma.fst : Gen s → Fin (m + 1)) (movedVar i s hE.2) i.castSucc a

/-! ### Bubbles -/

variable (K) in
/-- **`Γ` of the counterclockwise bubble with `α` dots** in the region `s` (cup `1 → F E`, `α` dots
on the strand `F`, cap `F E → 1`; by the cyclicity of dots the position of the dots does not
matter), whiskered by `X`. -/
def bubbleFEW {C : Type u} [CommRing C] (X : BRing (H K s) C) (α : ℕ) : BHom X X :=
  (capFEW K i hE hF X).comp ((BHom.mulB (BRing.tmul (Fst (K := K) i hF) ((Est (K := K) i hE).tensor X)
    (eXi K i s hE.2 ^ α : ERing K i s hE.2) 1)).comp (cupFEW K i hE hF X))

/-- **The bubble is multiplication by `bubbleFEH`** (whose closed form is `bubbleFEH_eq`, with the
positivity and normalization axioms and the infinite Grassmannian relation, KL III (3.4), (3.7),
in `Categorification.Flag.Bubbles`). -/
theorem bubbleFEW_eq {C : Type u} [CommRing C] (X : BRing (H K s) C) (α : ℕ) :
    bubbleFEW K i hE hF X α = BHom.mulB (X.left (bubbleFEH i s hE.2 α)) := by
  refine BHom.ext fun x => ?_
  rw [bubbleFEW, BHom.comp_apply, BHom.comp_apply, cupFEW_apply, BHom.mulB_apply, Finset.mul_sum,
    BHom.map_sum, BHom.mulB_apply]
  have h1 : ∀ f, BRing.tmul (Fst (K := K) i hF) ((Est (K := K) i hE).tensor X)
      (eXi K i s hE.2 ^ α : ERing K i s hE.2) 1 *
      BRing.tmul _ _ ((-1) ^ (dFE i hE - f) * eXi K i s hE.2 ^ f : ERing K i s hE.2)
        (BRing.tmul _ X (xsFE i hE (dFE i hE - f)) x) =
      BRing.tmul _ _ (eXi K i s hE.2 ^ α * ((-1) ^ (dFE i hE - f) * eXi K i s hE.2 ^ f) :
        ERing K i s hE.2) (BRing.tmul _ X (xsFE i hE (dFE i hE - f)) x) := by
    intro f; rw [BRing.tmul_mul_tmul, one_mul]
  simp only [h1, capFEW_tmul, ← Finset.sum_mul, ← map_sum]
  congr 2
  have hsum : ∀ (S : Finset ℕ) (g : ℕ → ((Fst (K := K) i hF).tensor (Est (K := K) i hE)).T),
      ∑ f ∈ S, capFEP K i hE hF (g f) = capFEP K i hE hF (∑ f ∈ S, g f) := by
    intro S g
    induction S using Finset.induction_on with
    | empty => simp [capFEP]
    | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, capFEP_add]
  rw [hsum, bubbleFEH, capFEP, map_sum]
  congr 2
  rw [cupEltKL, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [feEquiv_tmul, ← neg_one_pow_tmul_one, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rfl

/-! ### Cyclicity of dots -/

/-- **KL III (3.3), right-hand picture** (`rotDotL`): the upward dot rotated by the cup
`1 → F E` on the left and the cap `E F → 1` on the right is the downward dot, on `F_i ⊗ X`. -/
theorem cycDot_F {C : Type u} [CommRing C] (X : BRing (H K s') C) :
    (BHom.whiskerLeft (Fst (K := K) i hF) (capEFW K i hE hF X)).comp
      ((BHom.mulB (BRing.tmul (Fst (K := K) i hF) ((Est (K := K) i hE).tensor
          ((Fst (K := K) i hF).tensor X)) 1 (BRing.tmul _ _ (eXi K i s hE.2) 1))).comp
        (cupFEW K i hE hF ((Fst (K := K) i hF).tensor X))) =
      BHom.mulB (BRing.tmul _ _ (eXi K i s hF.2) 1) := by
  refine BHom.ext_tensor fun (a : ERing K i s hE.2) x => ?_
  rw [BHom.comp_apply, BHom.comp_apply, cupFEW_apply, BHom.mulB_apply, Finset.mul_sum,
    BHom.map_sum, BHom.mulB_apply, BRing.tmul_mul_tmul, one_mul]
  have h0 : ∀ f, BRing.tmul (Fst (K := K) i hF) ((Est (K := K) i hE).tensor
      ((Fst (K := K) i hF).tensor X)) 1 (BRing.tmul _ _ (eXi K i s hE.2) 1) *
      BRing.tmul _ _ ((-1) ^ (dFE i hE - f) * eXi K i s hE.2 ^ f : ERing K i s hE.2)
        (BRing.tmul _ _ (xsFE i hE (dFE i hE - f)) (BRing.tmul _ X a x)) =
      BRing.tmul _ _ ((-1) ^ (dFE i hE - f) * eXi K i s hE.2 ^ f : ERing K i s hE.2)
        (BRing.tmul _ _ (eXi K i s hE.2 * xsFE i hE (dFE i hE - f)) (BRing.tmul _ X a x)) := by
    intro f
    rw [BRing.tmul_mul_tmul, BRing.tmul_mul_tmul, one_mul, one_mul]
  simp only [h0, BHom.whiskerLeft_tmul, capEFW_tmul]
  have h2 : ∀ f, (Fst (K := K) i hF).right (capEFP K i hE hF
      (BRing.tmul _ _ (eXi K i s hE.2 * xsFE i hE (dFE i hE - f) : ERing K i s hE.2) a)) =
      pL K (Sigma.fst : Gen s → Fin (m + 1)) (movedVar i s hE.2) i.castSucc
          (capEF K (Sigma.fst : Gen s → Fin (m + 1)) (movedVar i s hE.2) i.castSucc
            (xsFE i hE (dFE i hE - f) ⊗ₜ (eXi K i s hE.2 * a))) := by
    intro f
    rw [Fst_right_capEFP_tmul, capEF_tmul, capEF_tmul, mul_assoc, mul_left_comm]
  have h1 : ∀ f, BRing.tmul (Fst (K := K) i hF) X
      ((-1) ^ (dFE i hE - f) * eXi K i s hE.2 ^ f : ERing K i s hE.2)
      (X.left (capEFP K i hE hF (BRing.tmul (Est (K := K) i hE) (Fst (K := K) i hF)
        (eXi K i s hE.2 * xsFE i hE (dFE i hE - f) : ERing K i s hE.2) a)) * x) =
      BRing.tmul (Fst (K := K) i hF) X ((-1) ^ (dFE i hE - f) * eXi K i s hE.2 ^ f *
        pL K (Sigma.fst : Gen s → Fin (m + 1)) (movedVar i s hE.2) i.castSucc
          (capEF K (Sigma.fst : Gen s → Fin (m + 1)) (movedVar i s hE.2) i.castSucc
            (xsFE i hE (dFE i hE - f) ⊗ₜ (eXi K i s hE.2 * a))) : ERing K i s hE.2) x := by
    intro f
    rw [← BRing.tmul_balance, h2, mul_comm]
  simp only [h1]
  rw [← BRing.sum_tmul]
  congr 1
  exact snake_F_FE (Sigma.fst : Gen s → Fin (m + 1)) (movedVar i s hE.2) i.castSucc
    (eXi K i s hE.2 * a)

/-- **KL III (3.3), left-hand picture** (`rotDotR`): the upward dot rotated by the cup `1 → E F`
on the right and the cap `F E → 1` on the left is the downward dot, on `F_i ⊗ X`. -/
theorem cycDot_F' {C : Type u} [CommRing C] (X : BRing (H K s') C) :
    (capFEW K i hE hF ((Fst (K := K) i hF).tensor X)).comp
      ((BHom.mulB (BRing.tmul (Fst (K := K) i hF) ((Est (K := K) i hE).tensor
          ((Fst (K := K) i hF).tensor X)) 1 (BRing.tmul _ _ (eXi K i s hE.2) 1))).comp
        (BHom.whiskerLeft (Fst (K := K) i hF) (cupEFW K i hE hF X))) =
      BHom.mulB (BRing.tmul _ _ (eXi K i s hF.2) 1) := by
  refine BHom.ext_tensor fun (a : ERing K i s hE.2) x => ?_
  rw [BHom.comp_apply, BHom.comp_apply, BHom.whiskerLeft_tmul, cupEFW_apply, BRing.tmul_sum,
    BHom.mulB_apply, Finset.mul_sum, BHom.map_sum, BHom.mulB_apply, BRing.tmul_mul_tmul, one_mul]
  have h0 : ∀ g, BRing.tmul (Fst (K := K) i hF) ((Est (K := K) i hE).tensor
      ((Fst (K := K) i hF).tensor X)) 1 (BRing.tmul _ _ (eXi K i s hE.2) 1) *
      BRing.tmul _ _ a (BRing.tmul _ _ ((-1) ^ (dEF i hE - g) * eXi K i s hE.2 ^ g : ERing K i s hE.2)
        (BRing.tmul _ X (xsEF i hE (dEF i hE - g)) x)) =
      BRing.tmul _ _ a (BRing.tmul _ _ (eXi K i s hE.2 * ((-1) ^ (dEF i hE - g) *
        eXi K i s hE.2 ^ g) : ERing K i s hE.2) (BRing.tmul _ X (xsEF i hE (dEF i hE - g)) x)) := by
    intro g
    rw [BRing.tmul_mul_tmul, BRing.tmul_mul_tmul, one_mul, one_mul]
  simp only [h0, capFEW_tmul]
  have h1 : ∀ g, ((Fst (K := K) i hF).tensor X).left (capFEP K i hE hF (BRing.tmul _ _ a
      (eXi K i s hE.2 * ((-1) ^ (dEF i hE - g) * eXi K i s hE.2 ^ g) : ERing K i s hE.2))) *
        BRing.tmul _ X (xsEF i hE (dEF i hE - g)) x =
      BRing.tmul _ X ((-1) ^ (dEF i hE - g) * pR K (Sigma.fst : Gen s → Fin (m + 1))
        (movedVar i s hE.2) (capFE K (Sigma.fst : Gen s → Fin (m + 1))
          (movedVar i s hE.2) i.castSucc ((eXi K i s hE.2 * a) ⊗ₜ (eXi K i s hE.2 ^ g))) *
            xsEF i hE (dEF i hE - g)) x := by
    intro g
    rw [BRing.tensor_left, BRing.tmul_mul_tmul, one_mul]
    congr 1
    show eRight K i s hE.2 (capFEP K i hE hF _) * _ = _
    rw [pR_capFE_eq, capFE_tmul, capFE_tmul]
    congr 1
    have e : (a * (eXi K i s hE.2 * ((-1) ^ (dEF i hE - g) * eXi K i s hE.2 ^ g)) : ERing K i s hE.2) =
        pR K (Sigma.fst : Gen s → Fin (m + 1)) (movedVar i s hE.2) ((-1) ^ (dEF i hE - g)) *
          (eXi K i s hE.2 * a * eXi K i s hE.2 ^ g) := by
      rw [map_pow, map_neg, map_one]; ring
    rw [e, trR_pR_mul, map_mul, map_pow, map_neg, map_one]
  simp only [h1]
  rw [← BRing.sum_tmul]
  congr 1
  exact snake_F_EF (Sigma.fst : Gen s → Fin (m + 1)) (movedVar i s hE.2) i.castSucc
    (eXi K i s hE.2 * a)

end Categorification.Flag

end

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.BarK0
import Categorification.KLR.Prop34

/-!
# `γ` commutes with the bar involutions and is an isometry

Khovanov–Lauda I (arXiv:0803.4121v2), §3.1: `K₀(R) = ⨁_ν K₀(R(ν))` carries the bar involution
`[P] ↦ [P̄]` and the bilinear form `([P], [Q]) = gdim (P^ψ ⊗ Q)` (weight spaces orthogonal), and
in the proof of Proposition 3.4 "the homomorphism `γ_{ℚ(q)}` respects the bilinear forms". The
bar involution of `f` is fixed by `θ_i ↦ θ_i` and `v ↦ v⁻¹`; since `[P_i]` is bar-invariant,
`γ` intertwines the two bar involutions.

## Main results

* `GradingDatum.barR` : the bar involution of `K₀(R)`, componentwise (`barR_of`), antilinear
  (`barR_smul`) and involutive (`barR_barR`).
* `GradingDatum.pformR` : KL I's bilinear form on `K₀(R)` (orthogonal sum of `K0.pform`),
  symmetric (`pformR_comm`) and `ℤ[q, q⁻¹]`-bilinear (`pformR_smul_left`, `pformR_smul_right`).

For KL I (`klGradingDatum k Γ`, in namespace `KLGamma`):

* `barR_clsSeq` : `\overline{[P_l]} = [P_l]`.
* `barR_gammaZ` : **`\overline{γ(x)} = γ(x̄)`** on `'f_{ℤ[q,q⁻¹]}` (bar: `q ↦ q⁻¹` on
  coefficients, `LaurentPolynomial.invert`).
* `barQ_qToV` : the specialisation `q ↦ v⁻¹` intertwines `q ↦ q⁻¹` and `v ↦ v⁻¹`.
* `barK0Q` : the bar involution of `K₀(R)_{ℚ(q)} = ℚ(v) ⊗ K₀(R)`, `a ⊗ z ↦ ā ⊗ z̄`, with
  `gammaQ_bar` (**`γ_{ℚ(q)}(x̄) = \overline{γ_{ℚ(q)}(x)}`** on `'f`) and `gammaF_barF`
  (**on `f`**, under the Gabber–Kac hypothesis used to define `γ_{ℚ(q)}` on `f`).
* `pformQ` : KL I's bilinear form on `K₀(R)_{ℚ(q)}`, with values in `ℚ((q))`,
  `pformQ (a ⊗ z) (b ⊗ w) = Ψ(a) Ψ(b) (z, w)` (`Ψ : ℚ(v) → ℚ((q))`, `v ↦ q⁻¹`), which is
  `Ψ`-semilinear in each variable (`pformQ_smul_left`, `pformQ_smul_right`).
* `pformQ_gammaQ` : **`γ_{ℚ(q)}` is an isometry**: `(γ x, γ y) = Ψ((x, y))` for all
  `x, y ∈ 'f` (Lusztig's form on the right).
-/

noncomputable section

namespace Categorification.KLR

open Graded KLRAlgebra LaurentPolynomial QuantumGroup TypeA

variable {I : Type*} [DecidableEq I] {k : Type*} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}

/-! ### The bar involution and the bilinear form on `K₀(R)` -/

namespace GradingDatum

variable (G : GradingDatum Q) (hsymm : ∀ a b, G.degΨ a b = G.degΨ b a)

theorem K0R_of_smul' (p : LaurentPolynomial ℤ) {ν : Multiset I} (y : K0 (G.grade ν)) :
    DirectSum.of G.K0fam ν (p • y) = p • (DirectSum.of G.K0fam ν y : G.K0R) := by
  rw [← DirectSum.lof_eq_of (LaurentPolynomial ℤ), ← DirectSum.lof_eq_of (LaurentPolynomial ℤ),
    map_smul]

/-- **The bar involution of `K₀(R) = ⨁_ν K₀(R(ν))`**, componentwise. -/
def barR : G.K0R →+ G.K0R :=
  DirectSum.toAddMonoid fun ν => (DirectSum.of G.K0fam ν).comp (K0.bar (G.psi hsymm ν))

theorem barR_of (ν : Multiset I) (x : K0 (G.grade ν)) :
    G.barR hsymm (DirectSum.of G.K0fam ν x) = DirectSum.of G.K0fam ν (K0.bar (G.psi hsymm ν) x) :=
  DirectSum.toAddMonoid_of _ _ _

theorem barR_barR (z : G.K0R) : G.barR hsymm (G.barR hsymm z) = z := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | of ν x => rw [barR_of, barR_of, K0.bar_bar]
  | add z z' hz hz' => rw [map_add, map_add, hz, hz']

/-- `\overline{p z} = p̄ z̄`. -/
theorem barR_smul (p : LaurentPolynomial ℤ) (z : G.K0R) :
    G.barR hsymm (p • z) = invert p • G.barR hsymm z := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | of ν x => rw [← K0R_of_smul', barR_of, barR_of, K0.bar_smul, K0R_of_smul']
  | add z z' hz hz' => rw [smul_add, map_add, hz, hz', map_add, smul_add]

variable [∀ ν, HasGdim (G.grade ν)]

/-- **KL I's bilinear form on `K₀(R)`**: the orthogonal sum of the forms `K0.pform` on the
weight spaces (KL I §3.1: "subspaces corresponding to different `ν`'s are orthogonal"). -/
def pformR : G.K0R →+ G.K0R →+ LaurentSeries ℤ :=
  DirectSum.toAddMonoid fun ν => (K0.pform (G.grade ν) (G.psi hsymm ν)).compl₂
    (DirectSum.component ℤ (Multiset I) G.K0fam ν).toAddMonoidHom

theorem pformR_of_of (ν : Multiset I) (x y : K0 (G.grade ν)) :
    G.pformR hsymm (DirectSum.of G.K0fam ν x) (DirectSum.of G.K0fam ν y) =
      K0.pform (G.grade ν) (G.psi hsymm ν) x y := by
  rw [pformR, DirectSum.toAddMonoid_of, AddMonoidHom.compl₂_apply, LinearMap.toAddMonoidHom_coe,
    ← DirectSum.apply_eq_component, DirectSum.of_eq_same]

theorem pformR_of_of_ne {ν μ : Multiset I} (h : ν ≠ μ) (x : K0 (G.grade ν))
    (y : K0 (G.grade μ)) :
    G.pformR hsymm (DirectSum.of G.K0fam ν x) (DirectSum.of G.K0fam μ y) = 0 := by
  rw [pformR, DirectSum.toAddMonoid_of, AddMonoidHom.compl₂_apply, LinearMap.toAddMonoidHom_coe,
    ← DirectSum.apply_eq_component, DirectSum.of_eq_of_ne _ _ _ (Ne.symm h), map_zero]

theorem pformR_of (ν : Multiset I) (x : K0 (G.grade ν)) (μ : Multiset I) (y : K0 (G.grade μ)) :
    G.pformR hsymm (DirectSum.of G.K0fam ν x) (DirectSum.of G.K0fam μ y) =
      G.pformR hsymm (DirectSum.of G.K0fam μ y) (DirectSum.of G.K0fam ν x) := by
  by_cases h : ν = μ
  · subst h
    rw [pformR_of_of, pformR_of_of, K0.pform_comm]
  · rw [pformR_of_of_ne _ _ h, pformR_of_of_ne _ _ (Ne.symm h)]

/-- **The form on `K₀(R)` is symmetric.** -/
theorem pformR_comm (z w : G.K0R) : G.pformR hsymm z w = G.pformR hsymm w z := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | of ν x =>
    induction w using DirectSum.induction_on with
    | zero => simp
    | of μ y => exact G.pformR_of hsymm ν x μ y
    | add w w' hw hw' => rw [map_add, hw, hw', map_add, AddMonoidHom.add_apply]
  | add z z' hz hz' => rw [map_add, AddMonoidHom.add_apply, hz, hz', map_add]

theorem pformR_T_smul_right (a : ℤ) (z w : G.K0R) :
    G.pformR hsymm z ((T a : LaurentPolynomial ℤ) • w) =
      HahnSeries.single a 1 * G.pformR hsymm z w := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | of ν x =>
    induction w using DirectSum.induction_on with
    | zero => simp
    | of μ y =>
      rw [← K0R_of_smul']
      by_cases h : ν = μ
      · subst h
        rw [pformR_of_of, pformR_of_of, K0.pform_T_smul_right]
      · rw [pformR_of_of_ne _ _ h, pformR_of_of_ne _ _ h, mul_zero]
    | add w w' hw hw' => rw [smul_add, map_add, hw, hw', map_add, mul_add]
  | add z z' hz hz' => simp only [map_add, AddMonoidHom.add_apply, hz, hz', mul_add]

/-- `(z, p w) = p (z, w)`. -/
theorem pformR_smul_right (p : LaurentPolynomial ℤ) (z w : G.K0R) :
    G.pformR hsymm z (p • w) = toLaurentSeries p * G.pformR hsymm z w :=
  K0.map_smul_of_T (F := G.pformR hsymm z) (fun a w => G.pformR_T_smul_right hsymm a z w) p w

/-- `(p z, w) = p (z, w)`. -/
theorem pformR_smul_left (p : LaurentPolynomial ℤ) (z w : G.K0R) :
    G.pformR hsymm (p • z) w = toLaurentSeries p * G.pformR hsymm z w := by
  rw [pformR_comm, pformR_smul_right, pformR_comm]

end GradingDatum

/-! ### KL I: `γ` and the bar involutions -/

namespace KLGamma

variable (k : Type*) [Field k] (Γ : SimpleGraph I) [DecidableRel Γ.Adj]

local notation "Gkl" => klGradingDatum k Γ

/-- The bar involution of `K₀(R)` for KL I. -/
abbrev barR : (Gkl).K0R →+ (Gkl).K0R := (Gkl).barR KL1.degΨ_symm

/-- KL I's bilinear form on `K₀(R)`. -/
abbrev pformR : (Gkl).K0R →+ (Gkl).K0R →+ LaurentSeries ℤ := (Gkl).pformR KL1.degΨ_symm

/-- `[P_l]` is bar-invariant. -/
theorem barR_clsSeq (l : List I) : barR k Γ (clsSeq k Γ l) = clsSeq k Γ l := by
  rw [clsSeq, GradingDatum.barR_of]
  congr 1
  exact K0.bar_ofIdempotent_of_fixed _ _ _ (hflip_e _)

/-- The ring involution `q ↦ q⁻¹` of `ℤ[q, q⁻¹]`. -/
abbrev invertHom : LaurentPolynomial ℤ →+* LaurentPolynomial ℤ :=
  (invert : LaurentPolynomial ℤ ≃ₐ[ℤ] LaurentPolynomial ℤ).toRingEquiv.toRingHom

/-- **`γ` commutes with the bar involutions** on `'f_{ℤ[q,q⁻¹]}`: `\overline{γ(x)} = γ(x̄)`,
where `x̄` fixes the words and inverts `q` in the coefficients. -/
theorem barR_gammaZ (x : PreF (LaurentPolynomial ℤ) I) :
    barR k Γ (gammaZ k Γ x) = gammaZ k Γ (PreF.bar (invertHom) x) := by
  induction x using PreF.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | smul_word w r =>
    rw [map_smul, gammaZ_word, GradingDatum.barR_smul, barR_clsSeq, PreF.bar_smul,
      PreF.bar_word, map_smul, gammaZ_word]
    rfl

/-- `\overline{q^n} = q^{-n}` specialises to `v ↦ v⁻¹`: `barQ ∘ qToV = qToV ∘ invert`. -/
theorem barQ_qToV (p : LaurentPolynomial ℤ) : barQ (qToV p) = qToV (invert p) := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p p' hp hp' => rw [map_add, map_add, hp, hp', map_add, map_add]
  | single n m =>
    have hT : (Finsupp.single n m : LaurentPolynomial ℤ) = m • T n := by
      rw [T, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hT, map_zsmul, map_zsmul, map_zsmul, map_zsmul, invert_T, qToV_T, qToV_T,
      Units.val_zpow_eq_zpow_val, map_zpow₀, barQ_vQ, Units.val_zpow_eq_zpow_val,
      Units.val_inv_eq_inv_val, inv_zpow', neg_neg]

/-- `Ψ ∘ qToV` is the inclusion `ℤ[q, q⁻¹] → ℚ((q))`. -/
theorem lsCast_toLaurentSeries (p : LaurentPolynomial ℤ) :
    lsCast (toLaurentSeries p) = vToLS (qToV p) := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p p' hp hp' => rw [map_add, map_add, hp, hp', map_add, map_add]
  | single n m =>
    have hT : (Finsupp.single n m : LaurentPolynomial ℤ) = m • T n := by
      rw [T, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hT, map_zsmul, map_zsmul, K0.toLaurentSeries_T, map_zsmul, map_zsmul, vToLS_qToV_T,
      lsCast_single, Int.cast_one]

section Constructions

attribute [local instance] qToVAlgebra

theorem algebraMap_eq_qToV (p : LaurentPolynomial ℤ) :
    algebraMap (LaurentPolynomial ℤ) (RatFunc ℚ) p = qToV p := rfl

/-! #### The bar involution on `K₀(R)_{ℚ(q)}` -/

/-- **The bar involution of `K₀(R)_{ℚ(q)} = ℚ(v) ⊗_{ℤ[q,q⁻¹]} K₀(R)`**, `a ⊗ z ↦ ā ⊗ z̄`
(`v ↦ v⁻¹` on `ℚ(v)`). -/
def barK0Q : K0Q k Γ →+ K0Q k Γ :=
  TensorProduct.liftAddHom
    { toFun := fun a =>
        { toFun := fun z => (barQ a ⊗ₜ[LaurentPolynomial ℤ] barR k Γ z :
            TensorProduct (LaurentPolynomial ℤ) (RatFunc ℚ) (Gkl).K0R)
          map_zero' := by rw [map_zero, TensorProduct.tmul_zero]
          map_add' := fun z z' => by rw [map_add, TensorProduct.tmul_add] }
      map_zero' := by ext z; simp
      map_add' := fun a a' => by ext z; simp [TensorProduct.add_tmul] }
    (fun p a z => by
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [GradingDatum.barR_smul, ← TensorProduct.smul_tmul, Algebra.smul_def, Algebra.smul_def,
        map_mul, algebraMap_eq_qToV, algebraMap_eq_qToV, barQ_qToV])

theorem barK0Q_tmul (a : RatFunc ℚ) (z : (Gkl).K0R) :
    barK0Q k Γ (a ⊗ₜ[LaurentPolynomial ℤ] z : K0Q k Γ) =
      (barQ a ⊗ₜ[LaurentPolynomial ℤ] barR k Γ z : K0Q k Γ) :=
  TensorProduct.liftAddHom_tmul _ _ _ _

theorem barK0Q_toK0Q (z : (Gkl).K0R) : barK0Q k Γ (toK0Q k Γ z) = toK0Q k Γ (barR k Γ z) := by
  change barK0Q k Γ ((1 : RatFunc ℚ) ⊗ₜ[LaurentPolynomial ℤ] z : K0Q k Γ) = _
  rw [barK0Q_tmul, map_one]
  rfl

/-- `barK0Q` is semilinear for `v ↦ v⁻¹`. -/
theorem barK0Q_smul (b : RatFunc ℚ) (t : K0Q k Γ) :
    barK0Q k Γ (b • t) = barQ b • barK0Q k Γ t := by
  refine TensorProduct.induction_on (motive := fun t : TensorProduct (LaurentPolynomial ℤ)
    (RatFunc ℚ) (Gkl).K0R => barK0Q k Γ (b • (t : K0Q k Γ)) = barQ b • barK0Q k Γ t) t
    ?_ ?_ ?_
  · show barK0Q k Γ (b • (0 : K0Q k Γ)) = _
    rw [smul_zero, map_zero, smul_zero]
  · intro a z
    change barK0Q k Γ (b • a ⊗ₜ[LaurentPolynomial ℤ] z) = _
    rw [TensorProduct.smul_tmul', barK0Q_tmul, barK0Q_tmul, smul_eq_mul, map_mul]
    rfl
  · intro x y hx hy
    change barK0Q k Γ (b • ((x : K0Q k Γ) + y)) = _
    rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- **`γ_{ℚ(q)}` commutes with the bar involutions** on `'f`. -/
theorem gammaQ_bar (x : PreF (RatFunc ℚ) I) :
    gammaQ k Γ (PreF.bar barQ x) = barK0Q k Γ (gammaQ k Γ x) := by
  induction x using PreF.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | smul_word w r =>
    rw [PreF.bar_smul, PreF.bar_word, map_smul, map_smul, barK0Q_smul, gammaQ_word,
      barK0Q_toK0Q, barR_clsSeq]

/-- **`γ_{ℚ(q)} : f → K₀(R)_{ℚ(q)}` commutes with the bar involutions** (under the Gabber–Kac
hypothesis `hGK` used to define `γ_{ℚ(q)}` on `f`). -/
theorem gammaF_barF (hGK : PreF.GabberKac (KL.C Γ).dot vQ (KL.C Γ).c) (z : KL.F Γ) :
    gammaF k Γ hGK ((KL.C Γ).barF z) = barK0Q k Γ (gammaF k Γ hGK z) := by
  obtain ⟨x, rfl⟩ := PreF.π_surjective (dot := (KL.C Γ).dot) (v := vQ) (c := (KL.C Γ).c) z
  exact gammaQ_bar k Γ x

/-! #### The bilinear form on `K₀(R)_{ℚ(q)}` -/

/-- `w ↦ ((a ⊗ z) ↦ Ψ(a) (w, z))`. -/
def pformQAux (w : (Gkl).K0R) : K0Q k Γ →+ LaurentSeries ℚ :=
  TensorProduct.liftAddHom
    ((AddMonoidHom.mul.compl₂ (lsCast.toAddMonoidHom.comp (pformR k Γ w))).comp
      vToLS.toAddMonoidHom)
    (fun p a z => by
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.compl₂_apply, AddMonoidHom.mul_apply,
        RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe]
      rw [GradingDatum.pformR_smul_right, map_mul, lsCast_toLaurentSeries, Algebra.smul_def,
        map_mul, algebraMap_eq_qToV]
      ring)

theorem pformQAux_tmul (w : (Gkl).K0R) (a : RatFunc ℚ) (z : (Gkl).K0R) :
    pformQAux k Γ w (a ⊗ₜ[LaurentPolynomial ℤ] z : K0Q k Γ) =
      vToLS a * lsCast (pformR k Γ w z) :=
  TensorProduct.liftAddHom_tmul _ _ _ _

theorem pformQAux_ext {f g : K0Q k Γ →+ LaurentSeries ℚ}
    (h : ∀ (a : RatFunc ℚ) (z : (Gkl).K0R),
      f (a ⊗ₜ[LaurentPolynomial ℤ] z : K0Q k Γ) = g (a ⊗ₜ[LaurentPolynomial ℤ] z : K0Q k Γ)) :
    f = g := by
  refine AddMonoidHom.ext fun t => ?_
  refine TensorProduct.induction_on (motive := fun t : TensorProduct (LaurentPolynomial ℤ)
    (RatFunc ℚ) (Gkl).K0R => f t = g t) t ?_ h ?_
  · exact (map_zero f).trans (map_zero g).symm
  · intro x y hx hy
    exact (map_add f x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add g x y).symm)

theorem pformQAux_add (w w' : (Gkl).K0R) :
    pformQAux k Γ (w + w') = pformQAux k Γ w + pformQAux k Γ w' :=
  pformQAux_ext k Γ fun a z => by
    rw [AddMonoidHom.add_apply, pformQAux_tmul, pformQAux_tmul, pformQAux_tmul, map_add,
      AddMonoidHom.add_apply, map_add, mul_add]

theorem pformQAux_zero : pformQAux k Γ 0 = 0 :=
  pformQAux_ext k Γ fun a z => by
    rw [pformQAux_tmul, map_zero, AddMonoidHom.zero_apply, map_zero, mul_zero,
      AddMonoidHom.zero_apply]

theorem pformQAux_smul (p : LaurentPolynomial ℤ) (w : (Gkl).K0R) (t : K0Q k Γ) :
    pformQAux k Γ (p • w) t = vToLS (qToV p) * pformQAux k Γ w t := by
  have : pformQAux k Γ (p • w) =
      (AddMonoidHom.mulLeft (vToLS (qToV p))).comp (pformQAux k Γ w) :=
    pformQAux_ext k Γ fun a z => by
      rw [pformQAux_tmul, AddMonoidHom.comp_apply, pformQAux_tmul, AddMonoidHom.coe_mulLeft,
        GradingDatum.pformR_smul_left, map_mul, lsCast_toLaurentSeries]
      ring
  rw [this]
  rfl

/-- **KL I's bilinear form on `K₀(R)_{ℚ(q)}`**, with values in `ℚ((q))`:
`(a ⊗ w, b ⊗ z) = Ψ(a) Ψ(b) (w, z)`, where `Ψ : ℚ(v) → ℚ((q))`, `v ↦ q⁻¹`. -/
def pformQ : K0Q k Γ →+ K0Q k Γ →+ LaurentSeries ℚ :=
  TensorProduct.liftAddHom
    { toFun := fun a =>
        { toFun := fun w => (AddMonoidHom.mulLeft (vToLS a)).comp (pformQAux k Γ w)
          map_zero' := by rw [pformQAux_zero, AddMonoidHom.comp_zero]
          map_add' := fun w w' => by rw [pformQAux_add, AddMonoidHom.comp_add] }
      map_zero' := by ext w t; simp
      map_add' := fun a a' => by ext w t; simp [add_mul] }
    (fun p a w => by
      refine AddMonoidHom.ext fun t => ?_
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.comp_apply,
        AddMonoidHom.coe_mulLeft]
      rw [pformQAux_smul, Algebra.smul_def, map_mul, algebraMap_eq_qToV]
      ring)

theorem pformQ_tmul (a : RatFunc ℚ) (w : (Gkl).K0R) (t : K0Q k Γ) :
    pformQ k Γ (a ⊗ₜ[LaurentPolynomial ℤ] w : K0Q k Γ) t = vToLS a * pformQAux k Γ w t :=
  congrArg (fun F : K0Q k Γ →+ LaurentSeries ℚ => F t) (TensorProduct.liftAddHom_tmul _ _ a w)

theorem pformQ_tmul_tmul (a b : RatFunc ℚ) (w z : (Gkl).K0R) :
    pformQ k Γ (a ⊗ₜ[LaurentPolynomial ℤ] w : K0Q k Γ) (b ⊗ₜ[LaurentPolynomial ℤ] z : K0Q k Γ) =
      vToLS a * vToLS b * lsCast (pformR k Γ w z) := by
  rw [pformQ_tmul, pformQAux_tmul, mul_assoc]

/-- On `K₀(R) ⊆ K₀(R)_{ℚ(q)}`, `pformQ` is the form of `K₀(R)`, read in `ℚ((q))`. -/
theorem pformQ_toK0Q (w z : (Gkl).K0R) :
    pformQ k Γ (toK0Q k Γ w) (toK0Q k Γ z) = lsCast (pformR k Γ w z) := by
  change pformQ k Γ ((1 : RatFunc ℚ) ⊗ₜ[LaurentPolynomial ℤ] w : K0Q k Γ)
    ((1 : RatFunc ℚ) ⊗ₜ[LaurentPolynomial ℤ] z : K0Q k Γ) = _
  rw [pformQ_tmul_tmul, map_one, one_mul, one_mul]

/-- `pformQ` is `Ψ`-semilinear in its second variable. -/
theorem pformQ_smul_right (b : RatFunc ℚ) (s t : K0Q k Γ) :
    pformQ k Γ s (b • t) = vToLS b * pformQ k Γ s t := by
  refine TensorProduct.induction_on (motive := fun s : TensorProduct (LaurentPolynomial ℤ)
    (RatFunc ℚ) (Gkl).K0R => pformQ k Γ s (b • t) = vToLS b * pformQ k Γ s t) s
    ?_ ?_ ?_
  · show pformQ k Γ (0 : K0Q k Γ) (b • t) = vToLS b * pformQ k Γ (0 : K0Q k Γ) t
    rw [map_zero, AddMonoidHom.zero_apply, AddMonoidHom.zero_apply, mul_zero]
  · intro a w
    rw [pformQ_tmul, pformQ_tmul]
    refine TensorProduct.induction_on (motive := fun t : TensorProduct (LaurentPolynomial ℤ)
      (RatFunc ℚ) (Gkl).K0R => vToLS a * pformQAux k Γ w (b • (t : K0Q k Γ)) =
        vToLS b * (vToLS a * pformQAux k Γ w t)) t ?_ ?_ ?_
    · show vToLS a * pformQAux k Γ w (b • (0 : K0Q k Γ)) = _
      simp
    · intro c z
      change vToLS a * pformQAux k Γ w (b • c ⊗ₜ[LaurentPolynomial ℤ] z) = _
      rw [TensorProduct.smul_tmul', pformQAux_tmul, pformQAux_tmul, smul_eq_mul, map_mul]
      ring
    · intro x y hx hy
      change vToLS a * pformQAux k Γ w (b • ((x : K0Q k Γ) + y)) =
        vToLS b * (vToLS a * pformQAux k Γ w ((x : K0Q k Γ) + y))
      rw [smul_add, map_add, map_add, mul_add, mul_add, hx, hy, mul_add]
  · intro x y hx hy
    change pformQ k Γ ((x : K0Q k Γ) + y) (b • t) = vToLS b * pformQ k Γ ((x : K0Q k Γ) + y) t
    rw [map_add, AddMonoidHom.add_apply, AddMonoidHom.add_apply, hx, hy, mul_add]

/-- `pformQ` is symmetric. -/
theorem pformQ_comm (s t : K0Q k Γ) : pformQ k Γ s t = pformQ k Γ t s := by
  refine TensorProduct.induction_on (motive := fun s : TensorProduct (LaurentPolynomial ℤ)
    (RatFunc ℚ) (Gkl).K0R => pformQ k Γ s t = pformQ k Γ t s) s ?_ ?_ ?_
  · show pformQ k Γ (0 : K0Q k Γ) t = pformQ k Γ t (0 : K0Q k Γ)
    rw [map_zero, map_zero, AddMonoidHom.zero_apply]
  · intro a w
    refine TensorProduct.induction_on (motive := fun t : TensorProduct (LaurentPolynomial ℤ)
      (RatFunc ℚ) (Gkl).K0R => pformQ k Γ (a ⊗ₜ[LaurentPolynomial ℤ] w : K0Q k Γ) t =
        pformQ k Γ t (a ⊗ₜ[LaurentPolynomial ℤ] w : K0Q k Γ)) t ?_ ?_ ?_
    · show pformQ k Γ _ (0 : K0Q k Γ) = pformQ k Γ (0 : K0Q k Γ) _
      rw [map_zero, map_zero, AddMonoidHom.zero_apply]
    · intro b z
      rw [pformQ_tmul_tmul, pformQ_tmul_tmul, GradingDatum.pformR_comm]
      ring
    · intro x y hx hy
      change pformQ k Γ _ ((x : K0Q k Γ) + y) = pformQ k Γ ((x : K0Q k Γ) + y) _
      rw [map_add, map_add, AddMonoidHom.add_apply, hx, hy]
  · intro x y hx hy
    change pformQ k Γ ((x : K0Q k Γ) + y) t = pformQ k Γ t ((x : K0Q k Γ) + y)
    rw [map_add, AddMonoidHom.add_apply, map_add, hx, hy]

/-- `pformQ` is `Ψ`-semilinear in its first variable. -/
theorem pformQ_smul_left (b : RatFunc ℚ) (s t : K0Q k Γ) :
    pformQ k Γ (b • s) t = vToLS b * pformQ k Γ s t := by
  rw [pformQ_comm, pformQ_smul_right, pformQ_comm]

end Constructions

/-- The forms agree on words: `(γ(θ_w), γ(θ_y)) = Ψ((θ_w, θ_y))`. -/
theorem pformQ_gammaQ_word (w y : FreeMonoid I) :
    pformQ k Γ (gammaQ k Γ (PreF.word w)) (gammaQ k Γ (PreF.word y)) =
      vToLS ((KL.C Γ).form (PreF.word w) (PreF.word y)) := by
  rw [gammaQ_word, gammaQ_word, pformQ_toK0Q]
  by_cases h : ((FreeMonoid.toList w : List I) : Multiset I) = (FreeMonoid.toList y : Multiset I)
  · rw [clsSeq_eq k Γ (FreeMonoid.toList y) h.symm, clsSeq, GradingDatum.pformR_of_of,
      K0.pform_comm]
    change lsCast (K0.pform _ _ (K0.of ((Gkl).projP (Seq.ofList _ h.symm)))
      (K0.of ((Gkl).projP _))) = _
    rw [GradingDatum.pform_projP_eq_homForm, lsCast_homForm_projP, wordFn_ofList_lbl,
      wordFn_ofList_lbl, FreeMonoid.ofList_toList, FreeMonoid.ofList_toList]
  · rw [clsSeq, clsSeq, GradingDatum.pformR_of_of_ne _ _ h, map_zero, CartanDatum.form,
      PreF.form_eq_zero_of_wt_ne (a := w) (b := y) h, map_zero]

/-- **`γ_{ℚ(q)}` is an isometry** (KL I §3.1, proof of Proposition 3.4: "the homomorphism
`γ_{ℚ(q)}` respects the bilinear forms"): `(γ x, γ y) = Ψ((x, y))` for all `x, y ∈ 'f`, where
`( , )` on the left is KL I's form `gdim (P^ψ ⊗ Q)` and on the right Lusztig's form, and
`Ψ : ℚ(v) → ℚ((q))`, `v ↦ q⁻¹`. -/
theorem pformQ_gammaQ (x y : PreF (RatFunc ℚ) I) :
    pformQ k Γ (gammaQ k Γ x) (gammaQ k Γ y) = vToLS ((KL.C Γ).form x y) := by
  induction x using PreF.induction_linear with
  | zero => rw [map_zero, map_zero, AddMonoidHom.zero_apply, map_zero, LinearMap.zero_apply,
      map_zero]
  | add x x' hx hx' => rw [map_add, map_add, AddMonoidHom.add_apply, hx, hx', map_add,
      LinearMap.add_apply, map_add]
  | smul_word w r =>
    rw [map_smul, pformQ_smul_left, map_smul, LinearMap.smul_apply, smul_eq_mul, map_mul]
    congr 1
    induction y using PreF.induction_linear with
    | zero => rw [map_zero, map_zero, map_zero, map_zero]
    | add y y' hy hy' => rw [map_add, map_add, hy, hy', map_add, map_add]
    | smul_word y s =>
      rw [map_smul, pformQ_smul_right, pformQ_gammaQ_word,
        LinearMap.map_smul ((KL.C Γ).form (PreF.word w)) s (PreF.word y), smul_eq_mul, map_mul]

/-- **The integral `γ` is an isometry** on words: `([P_w], [P_y]) = Ψ((θ_w, θ_y))`. -/
theorem lsCast_pformR_gammaZ_word (w y : FreeMonoid I) :
    lsCast (pformR k Γ (gammaZ k Γ (PreF.word w)) (gammaZ k Γ (PreF.word y))) =
      vToLS ((KL.C Γ).form (PreF.word w) (PreF.word y)) := by
  rw [← pformQ_toK0Q, ← gammaQ_word_eq, ← gammaQ_word_eq, pformQ_gammaQ_word]

end KLGamma

end Categorification.KLR

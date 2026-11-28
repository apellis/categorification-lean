/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.QuantumCoevaluation

/-!
# The normalizing scalar of the quantum coevaluation

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 7.5. For the evaluation `ev_μ` normalized by `ev_μ(v_l^{μ*}, v_h^μ) = 1`, the
canonical element `coev_μ(1)` has component `a⁻¹ v_l^μ ⊗ v_h^{μ*}` in
`(V_μ)_low ⊗ (V_{μ*})_high` and `v_h^μ ⊗ v_l^{μ*}` in `(V_μ)_high ⊗ (V_{μ*})_low`, where
`Θ(v_l^{μ*}) = a v_h^μ` (`dualLowestScalar`). Webster normalizes `[L_μ] = a coev_μ(1)` by its
first component and reads off the second as `(-1)^{2ρ^∨(μ)} q^{-2⟨μ,ρ⟩} v_h ⊗ v_l`.

Here:

* `evaluationPairing_F_smul_right`: `ev(y, Fᵢ x) = -v^{dᵢ(⟨i,Λ⟩-2)} ev(Fᵢ y, x)` for `y` of
  weight `Λ` (from `ev(u y, x) = ev(y, S(u) x)` with `S(K̃ᵢ Fᵢ) = -Fᵢ`), and its divided power
  version `evaluationPairing_qDivPow_F_smul_right`;
* `evaluationPairing_dividedLoweringWord`: along an extremal divided word `e` (each block
  `Fᵢ^{(n)}` is applied at a weight `Λ` with `⟨i, Λ⟩ = n`, `IsExtremalWord`),
  `ev(y, F_{e.reverse} v_h^μ) = (-1)^{|e|} v^{-Σ dᵢ} ev(F_e y, v_h^μ)`;
* `dualLowestScalar_eq`: **`a = (-1)^{|β|} v^{-Σ_{i ∈ β} dᵢ} c`**, where `β` is the black content
  of the coevaluation word (`|β| = 2ρ^∨(μ)` and `Σ_{i∈β} dᵢ = (μ - w₀μ, ρ) = 2⟨μ, ρ⟩`) and
  `c = (v_l^{μ*}(w), v_l^{μ*}(w̄))` compares the lowest weight vectors of `V_{μ*}` built from the
  reduced expression `w` and from the reversed expression `w̄`;
* `dualLowestSign_mul_self`: `c² = 1`, so `a = ±(-1)^{2ρ^∨(μ)} v^{-2⟨μ,ρ⟩}`.

Webster's factor is `c = 1`: his lowest weight vector `[P⁰_{i^{μ*}}]` does not depend on the
reduced expression (Proposition 7.2, proved for the projectives in the library as
`KLR.CycKLR.coevaluationProjective_iso_of_same_weyl`); on the vectors of `V_{μ*}` this
independence is not formalized here. The second component in Webster's proof is computed by
invariance from the first; with the coproduct `Δ(Fᵢ) = Fᵢ ⊗ K̃ᵢ⁻¹ + 1 ⊗ Fᵢ` of §1.2 invariant
tensors satisfy `(u ⊗ 1) t = (1 ⊗ S⁻¹(u)) t`, so the operator in the printed display is
`S⁻¹(F_{i^μ})`; with `S` in its place the factor would be `q^{+2⟨μ,ρ⟩}`. The factor printed,
`(-1)^{2ρ^∨(μ)} q^{-2⟨μ,ρ⟩}`, is the one obtained with `S⁻¹` (`q = v`).
-/

noncomputable section

namespace Categorification.Stendhal.QuantumDual

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop KLR.CycKLR Module
open scoped TensorProduct

variable {I K H Y : Type*} [Fintype I] [DecidableEq I] [AddCommGroup Y]
    {Δ : LusztigCartanDatum I} {R : Δ.RootDatum Y}
    [Field K] [ConditionallyCompleteLinearOrder K] [IsStrictOrderedRing K]
    [AddCommGroup H] [Module K H] (P : Matrix.Realization Δ.cartanMatrix K H)

local notation "vQ" => (RatFunc.X : RatFunc ℚ)
local notation "𝕂" => RatFunc ℚ
local instance : NeZero vQ := ⟨RatFunc.X_ne_zero⟩
local notation "𝕌" => QuantumGroup R vQ
local notation "hCartan" => Δ.isGeneralizedCartan_cartanMatrix
local notation "Dc" => P.cartanDatum hCartan
local notation "cs" => P.coxeterSystem hCartan

/-! ### Extremal divided words -/

section Extremal

variable (R) in
/-- A divided word `e = [(i₁, n₁), (i₂, n₂), …]`, applied from the head, is **extremal** at the
weight `Λ` if every block `Fᵢ^{(n)}` is applied at a weight `Λ'` with `⟨i, Λ'⟩ = n`. -/
def IsExtremalWord : (Y →+ ℤ) → List (I × ℕ) → Prop
  | _, [] => True
  | Λ, a :: e => Λ (R.coroot a.1) = a.2 ∧ IsExtremalWord (Λ - (a.2 : ℤ) • R.root a.1) e

omit [Fintype I] [DecidableEq I] in
theorem isExtremalWord_append_singleton (Λ : Y →+ ℤ) (e : List (I × ℕ)) (i : I) (n : ℕ) :
    IsExtremalWord R Λ (e ++ [(i, n)]) ↔ IsExtremalWord R Λ e ∧
      (Λ - (e.map fun a => (a.2 : ℤ) • R.root a.1).sum) (R.coroot i) = n := by
  induction e generalizing Λ with
  | nil => simp [IsExtremalWord]
  | cons a e ih =>
    simp only [List.cons_append, IsExtremalWord, ih, List.map_cons, List.sum_cons,
      sub_add_eq_sub_sub,
      and_assoc]

/-- The number of lowering generators of a divided word. -/
def wordHeight (e : List (I × ℕ)) : ℕ := (e.map Prod.snd).sum

variable (Δ) in
/-- The `ρ`-degree `Σ dᵢ n` of a divided word. -/
def wordRhoDegree (e : List (I × ℕ)) : ℤ := (e.map fun a => (Δ.d a.1 : ℤ) * a.2).sum

end Extremal

/-! ### Moving lowering generators across `ev_μ` -/

section Moving

variable [FiniteDimensional K H] (hR : R.IsXRegular) (μ : Dom R) (weight : P.integralWeights)
  (hdom : P.IsDominantIntegral (weight : Dual K H))
  (hm : ∀ j, (weight : Dual K H) (P.coroot j) = (μ.1 (R.coroot j) : K))
  (w : List I)
variable (hw : (P.coxeterSystem Δ.isGeneralizedCartan_cartanMatrix).IsReduced w.reverse)
  (hlong : ∀ i, (P.coxeterSystem Δ.isGeneralizedCartan_cartanMatrix).IsLeftDescent
    ((P.coxeterSystem Δ.isGeneralizedCartan_cartanMatrix).wordProd w.reverse) i)

local notation "μs" => dualWeight P μ weight hdom hm w hw hlong
local notation "Vμ" => IrreducibleModule R vQ (Subtype.val μ)
local notation "Vμs" =>
  IrreducibleModule R vQ (Subtype.val (dualWeight P μ weight hdom hm w hw hlong))
local notation "ev" => evaluationPairing P hR μ weight hdom hm w hw hlong

omit [FiniteDimensional K H] in
private theorem Kt_F_smul_of_mem {Λ : Y →+ ℤ} {y : Vμs} (hy : y ∈ weightSpace R vQ Vμs Λ)
    (i : I) : Kt R vQ i • F R vQ i • y = vQ ^ ((Δ.d i : ℤ) * (Λ (R.coroot i) - 2)) •
      F R vQ i • y := by
  rw [Kt, F_smul_mem_weightSpace hy i (ktilde R i)]
  congr 2
  simp only [ktilde, AddMonoidHom.sub_apply, map_nsmul, R.root_coroot,
    Δ.cartanMatrix_self, nsmul_eq_mul]

include hR in
/-- **Moving `Fᵢ` across `ev_μ`**: for `y` of weight `Λ`,
`ev(y, Fᵢ x) = -v^{dᵢ(⟨i,Λ⟩-2)} ev(Fᵢ y, x)`. -/
theorem evaluationPairing_F_smul_right {Λ : Y →+ ℤ} {y : Vμs}
    (hy : y ∈ weightSpace R vQ Vμs Λ) (i : I) (x : Vμ) :
    ev y (F R vQ i • x) = -(vQ ^ ((Δ.d i : ℤ) * (Λ (R.coroot i) - 2)) * ev (F R vQ i • y) x) := by
  have h := evaluationPairing_smul_left P hR μ weight hdom hm w hw hlong
    (Kt R vQ i * F R vQ i) y x
  have hS : antipode R vQ (Kt R vQ i * F R vQ i) = -F R vQ i := by
    rw [antipode_mul, antipode_F, Kt, antipode_K, neg_mul, mul_assoc, K_add, add_neg_cancel,
      K_zero, mul_one]
  rw [hS, neg_smul, map_neg, mul_smul, Kt_F_smul_of_mem P μ weight hdom hm w hw hlong hy i,
    LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul] at h
  rw [h, neg_neg]

include hR in
theorem evaluationPairing_F_pow_smul_right {Λ : Y →+ ℤ} {y : Vμs}
    (hy : y ∈ weightSpace R vQ Vμs Λ) (i : I) (n : ℕ) (x : Vμ) :
    ev y (F R vQ i ^ n • x) = (-1) ^ n * vQ ^ ((Δ.d i : ℤ) * (n * Λ (R.coroot i) - n * (n + 1))) *
      ev (F R vQ i ^ n • y) x := by
  induction n generalizing Λ y with
  | zero => simp
  | succ n ih =>
    have hy' := F_smul_mem_weightSpace hy i
    rw [pow_succ', mul_smul, evaluationPairing_F_smul_right P hR μ weight hdom hm w hw hlong hy,
      ih hy', ← mul_smul, ← pow_succ (F R vQ i) n]
    have hc : (Λ - R.root i) (R.coroot i) = Λ (R.coroot i) - 2 := by
      simp [R.root_coroot, Δ.cartanMatrix_self]
    rw [hc]
    have hv : vQ ≠ 0 := RatFunc.X_ne_zero
    have he : vQ ^ ((Δ.d i : ℤ) * (Λ (R.coroot i) - 2)) *
        vQ ^ ((Δ.d i : ℤ) * (n * (Λ (R.coroot i) - 2) - n * (n + 1))) =
        vQ ^ ((Δ.d i : ℤ) * (((n + 1 : ℕ) : ℤ) * Λ (R.coroot i) -
          ((n + 1 : ℕ) : ℤ) * (((n + 1 : ℕ) : ℤ) + 1))) := by
      rw [← zpow_add₀ hv]
      congr 1
      push_cast
      ring
    rw [← he, pow_succ (-1 : 𝕂) n, ← pow_succ' (F R vQ i) n]
    generalize vQ ^ ((Δ.d i : ℤ) * (Λ (R.coroot i) - 2)) = a
    generalize vQ ^ ((Δ.d i : ℤ) * (n * (Λ (R.coroot i) - 2) - n * (n + 1))) = b
    ring

include hR in
/-- **Moving `Fᵢ^{(n)}` across `ev_μ`**: for `y` of weight `Λ`,
`ev(y, Fᵢ^{(n)} x) = (-1)^n v^{dᵢ(n⟨i,Λ⟩ - n(n+1))} ev(Fᵢ^{(n)} y, x)`. -/
theorem evaluationPairing_qDivPow_F_smul_right {Λ : Y →+ ℤ} {y : Vμs}
    (hy : y ∈ weightSpace R vQ Vμs Λ) (i : I) (n : ℕ) (x : Vμ) :
    ev y (qDivPow (vQ ^ Δ.d i) n (F R vQ i) • x) =
      (-1) ^ n * vQ ^ ((Δ.d i : ℤ) * (n * Λ (R.coroot i) - n * (n + 1))) *
        ev (qDivPow (vQ ^ Δ.d i) n (F R vQ i) • y) x := by
  rw [qDivPow, smul_assoc, smul_assoc, LinearMap.map_smul, LinearMap.map_smul, LinearMap.smul_apply,
    smul_eq_mul, smul_eq_mul,
    evaluationPairing_F_pow_smul_right P hR μ weight hdom hm w hw hlong hy]
  ring

variable (R) in
/-- `F_e y`: the divided word `e` applied to `y`, head first. -/
def applyDividedWord {M : Type*} [AddCommGroup M] [Module 𝕌 M] (e : List (I × ℕ)) (y : M) : M :=
  e.foldl (fun z a => qDivPow (vQ ^ Δ.d a.1) a.2 (F R vQ a.1) • z) y

omit [Fintype I] in
theorem dividedLoweringWord_eq_applyDividedWord (ν : Dom R) (e : List (I × ℕ)) :
    dividedLoweringWord ν e = applyDividedWord R e (IrreducibleModule.hwv R vQ ν.1) := rfl

omit [Fintype I] in
theorem applyDividedWord_mem {M : Type*} [AddCommGroup M] [Module 𝕂 M] [Module 𝕌 M]
    [IsScalarTower 𝕂 𝕌 M] {Λ : Y →+ ℤ} {y : M} (hy : y ∈ weightSpace R vQ M Λ)
    (e : List (I × ℕ)) :
    applyDividedWord R e y ∈
      weightSpace R vQ M (Λ - (e.map fun a => (a.2 : ℤ) • R.root a.1).sum) := by
  induction e generalizing Λ y with
  | nil => simpa [applyDividedWord] using hy
  | cons a e ih =>
    have h1 : qDivPow (vQ ^ Δ.d a.1) a.2 (F R vQ a.1) • y ∈
        weightSpace R vQ M (Λ - (a.2 : ℤ) • R.root a.1) := by
      rw [qDivPow, smul_assoc]
      refine Submodule.smul_mem _ _ ?_
      clear ih
      induction a.2 generalizing y Λ with
      | zero => simpa using hy
      | succ n ihn =>
        rw [pow_succ', mul_smul]
        have := F_smul_mem_weightSpace (ihn hy) a.1
        convert this using 2
        push_cast
        rw [add_smul, one_smul, sub_add_eq_sub_sub]
    have := ih h1
    simp only [applyDividedWord, List.foldl_cons, List.map_cons, List.sum_cons] at this ⊢
    convert this using 2
    abel

include hR in
/-- **Moving an extremal divided word across `ev_μ`**: if `e` is extremal at the weight `Λ` of
`y`, then `ev(y, F_{e.reverse} v_h^μ) = (-1)^{|e|} v^{-Σ dᵢ} ev(F_e y, v_h^μ)`. -/
theorem evaluationPairing_dividedLoweringWord {Λ : Y →+ ℤ} {y : Vμs}
    (hy : y ∈ weightSpace R vQ Vμs Λ) (e : List (I × ℕ)) (he : IsExtremalWord R Λ e) :
    ev y (dividedLoweringWord μ e.reverse) =
      (-1) ^ wordHeight e * vQ ^ (-wordRhoDegree Δ e) *
        ev (applyDividedWord R e y) (IrreducibleModule.hwv R vQ μ.1) := by
  induction e generalizing Λ y with
  | nil => simp [dividedLoweringWord, applyDividedWord, wordHeight, wordRhoDegree]
  | cons a e ih =>
    obtain ⟨ha, he⟩ := he
    have hy' : qDivPow (vQ ^ Δ.d a.1) a.2 (F R vQ a.1) • y ∈
        weightSpace R vQ Vμs (Λ - (a.2 : ℤ) • R.root a.1) := by
      simpa [applyDividedWord] using applyDividedWord_mem hy [a]
    have hs : dividedLoweringWord μ (a :: e).reverse =
        qDivPow (vQ ^ Δ.d a.1) a.2 (F R vQ a.1) • dividedLoweringWord μ e.reverse := by
      simp [dividedLoweringWord, List.foldl_append]
    rw [hs, evaluationPairing_qDivPow_F_smul_right P hR μ weight hdom hm w hw hlong hy,
      ih hy' he, ha]
    have hv : vQ ≠ 0 := RatFunc.X_ne_zero
    simp only [applyDividedWord, List.foldl_cons, wordHeight, wordRhoDegree, List.map_cons,
      List.sum_cons, pow_add]
    have hz : vQ ^ ((Δ.d a.1 : ℤ) * ((a.2 : ℤ) * (a.2 : ℤ) - (a.2 : ℤ) * ((a.2 : ℤ) + 1))) *
        vQ ^ (-(e.map fun a => (Δ.d a.1 : ℤ) * a.2).sum) =
        vQ ^ (-((Δ.d a.1 : ℤ) * a.2 + (e.map fun a => (Δ.d a.1 : ℤ) * a.2).sum)) := by
      rw [← zpow_add₀ hv]
      congr 1
      ring
    rw [← hz]
    ring

end Moving

/-! ### Coevaluation words are extremal -/

section Words

omit [DecidableEq I] in
/-- **The coevaluation divided word is extremal** (Webster, Definition 7.1): along a nonnegative
reflection path from an integral weight `λ` matching `Λ`, each block `Fᵢ^{(n)}` has
`n = ⟨i, Λ'⟩` at the weight `Λ'` where it is applied. -/
theorem isExtremalWord_coevaluationDividedWord (lam : P.integralWeights) (Λ : Y →+ ℤ)
    (hΛ : ∀ j, (Dc).coroot j lam = Λ (R.coroot j)) (u : List I)
    (hu : Stendhal.NonnegativeReflectionPath Dc lam u) :
    IsExtremalWord R Λ (Stendhal.coevaluationDividedWord Dc lam u) := by
  induction u generalizing lam Λ with
  | nil => trivial
  | cons i u ih =>
    obtain ⟨h0, hu⟩ := hu
    refine ⟨?_, ih _ _ (fun j => ?_) hu⟩
    · change Λ (R.coroot i) = ((((Dc).coroot i lam).toNat : ℕ) : ℤ)
      rw [Int.toNat_of_nonneg h0, hΛ]
    · change (Dc).coroot j ((Dc).reflection i lam) =
        (Λ - ((((Dc).coroot i lam).toNat : ℕ) : ℤ) • R.root i) (R.coroot j)
      rw [Int.toNat_of_nonneg h0, CartanDatum.reflection_apply, map_sub, map_zsmul,
        AddMonoidHom.sub_apply, AddMonoidHom.zsmul_apply, R.root_coroot, hΛ, hΛ, smul_eq_mul,
        smul_eq_mul, ← CartanDatum.cartanMatrix_apply, P.cartanMatrix_cartanDatum]

omit [Fintype I] [DecidableEq I] in
theorem wordHeight_reverse (e : List (I × ℕ)) : wordHeight e.reverse = wordHeight e := by
  simp [wordHeight, List.map_reverse, List.sum_reverse]

omit [Fintype I] [DecidableEq I] in
theorem wordRhoDegree_reverse (e : List (I × ℕ)) :
    wordRhoDegree Δ e.reverse = wordRhoDegree Δ e := by
  simp [wordRhoDegree, List.map_reverse, List.sum_reverse]

omit [Fintype I] [DecidableEq I] in
theorem expandDiv_reverse (e : List (I × ℕ)) :
    KLR.KLRAlgebra.expandDiv e.reverse = (KLR.KLRAlgebra.expandDiv e).reverse := by
  induction e with
  | nil => rfl
  | cons a e ih =>
    rw [List.reverse_cons, Categorification.KLR.expandDiv_append, ih]
    simp [KLR.KLRAlgebra.expandDiv, List.reverse_replicate]

end Words

/-! ### The scalar `a` -/

section Scalar

variable [FiniteDimensional K H] [Finite (P.weylGroup Δ.isGeneralizedCartan_cartanMatrix)]
  (hR : R.IsXRegular) (μ : Dom R) (weight : P.integralWeights)
  (hdom : P.IsDominantIntegral (weight : Dual K H))
  (hm : ∀ j, (weight : Dual K H) (P.coroot j) = (μ.1 (R.coroot j) : K))
  (w : List I)
variable (hw : (P.coxeterSystem Δ.isGeneralizedCartan_cartanMatrix).IsReduced w.reverse)
  (hlong : ∀ i, (P.coxeterSystem Δ.isGeneralizedCartan_cartanMatrix).IsLeftDescent
    ((P.coxeterSystem Δ.isGeneralizedCartan_cartanMatrix).wordProd w.reverse) i)

local notation "μs" => dualWeight P μ weight hdom hm w hw hlong
local notation "Vμ" => IrreducibleModule R vQ (Subtype.val μ)
local notation "Vμs" =>
  IrreducibleModule R vQ (Subtype.val (dualWeight P μ weight hdom hm w hw hlong))
local notation "ev" => evaluationPairing P hR μ weight hdom hm w hw hlong
local notation "aμ" => dualLowestScalar P hR μ weight hdom hm w hw hlong
local notation "Bs" =>
  IrreducibleModule.form (Subtype.val (dualWeight P μ weight hdom hm w hw hlong)) hR hvn_ratFunc
local notation "vls" => lowestVector P (dualWeight P μ weight hdom hm w hw hlong)
  (dualIntegralWeight P weight w) w
local notation "vlsr" => lowestVector P (dualWeight P μ weight hdom hm w hw hlong)
  (dualIntegralWeight P weight w) w.reverse
local notation "dμ" => Stendhal.coevaluationDividedWord Dc weight w

include hdom hm hw in
omit [FiniteDimensional K H] [Finite (P.weylGroup Δ.isGeneralizedCartan_cartanMatrix)] in
theorem dualIntegralWeight_coroot_int (j : I) :
    (Dc).coroot j (dualIntegralWeight P weight w) = (μs).1 (R.coroot j) := by
  apply Int.cast_injective (α := K)
  rw [P.coroot_cartanDatum_cast, dualIntegralWeight_coroot P μ weight hdom hm w hw hlong]

include hdom hw hlong in
omit [FiniteDimensional K H] [Finite (P.weylGroup Δ.isGeneralizedCartan_cartanMatrix)] in
/-- The lowest weight vector of `V_{μ*}` along the reversed expression is `F_{d̄} v_h^{μ*}` for
the reversed divided word `d̄` of `μ` along `w` (`coevaluationDividedWord_reverse`). -/
theorem lowestVector_reverse_eq :
    vlsr = dividedLoweringWord μs (dμ).reverse := by
  unfold lowestVector dualIntegralWeight
  rw [Stendhal.coevaluationDividedWord_reverse]

include hdom hm hw hlong in
omit [FiniteDimensional K H] [Finite (P.weylGroup Δ.isGeneralizedCartan_cartanMatrix)] in
theorem isExtremalWord_reverse : IsExtremalWord R (μs).1 (dμ).reverse := by
  have h := isExtremalWord_coevaluationDividedWord P (dualIntegralWeight P weight w) (μs).1
    (dualIntegralWeight_coroot_int P μ weight hdom hm w hw hlong) w.reverse
    (Stendhal.nonnegativeReflectionPath_of_reduced P hCartan _
      (isDominantIntegral_dualIntegralWeight P weight hdom w hlong) w.reverse
      (by rw [List.reverse_reverse]; exact ((cs).isReduced_reverse_iff w).mp hw))
  unfold dualIntegralWeight at h
  rwa [Stendhal.coevaluationDividedWord_reverse] at h

include hR hdom hm hw hlong in
/-- **The scalar of `coev_μ`** (Webster, proof of Proposition 7.5):
`a = (-1)^{|β|} v^{-Σ_{i∈β} dᵢ} (v_l^{μ*}(w̄), v_l^{μ*}(w))`, where `Θ(v_l^{μ*}) = a v_h^μ`,
`|β| = 2ρ^∨(μ)` is the number of lowering generators of the coevaluation word of `μ` and
`Σ_{i∈β} dᵢ = 2⟨μ, ρ⟩` its `ρ`-degree. -/
theorem dualLowestScalar_eq :
    aμ = (-1) ^ wordHeight dμ * vQ ^ (-wordRhoDegree Δ dμ) * Bs vlsr vls := by
  have hev := evaluationPairing_hwv_lowest P hR μ weight hdom hm w hw hlong
  have hd : lowestVector P μ weight w = dividedLoweringWord μ (dμ).reverse.reverse := by
    rw [List.reverse_reverse]; rfl
  rw [hd, evaluationPairing_dividedLoweringWord P hR μ weight hdom hm w hw hlong
    (IrreducibleModule.hwv_mem_weightSpace (R := R) (v := vQ) (Λ := (μs).1)) _
    (isExtremalWord_reverse P μ weight hdom hm w hw hlong), wordHeight_reverse,
    wordRhoDegree_reverse, ← dividedLoweringWord_eq_applyDividedWord,
    ← lowestVector_reverse_eq P μ weight hdom hm w hw hlong, evaluationPairing_apply,
    twistLowestEquiv_symm_hwv, map_smul, smul_eq_mul] at hev
  have ha := dualLowestScalar_ne_zero P hR μ weight hdom hm w hw hlong
  rw [← hev]
  field_simp

omit [FiniteDimensional K H] [Finite (P.weylGroup Δ.isGeneralizedCartan_cartanMatrix)] in
theorem lowestContent_reverse :
    lowestContent P (dualIntegralWeight P weight w) w.reverse = lowestContent P weight w := by
  unfold lowestContent
  rw [← Stendhal.expand_coevaluationDividedWord, ← Stendhal.expand_coevaluationDividedWord]
  unfold dualIntegralWeight
  rw [Stendhal.coevaluationDividedWord_reverse, expandDiv_reverse, Multiset.coe_reverse]

omit [FiniteDimensional K H] [Finite (P.weylGroup Δ.isGeneralizedCartan_cartanMatrix)] in
include hdom hw hlong in
/-- The lowest weight vector of `V_{μ*}` along the reversed expression has weight `-μ`. -/
theorem lowestVector_reverse_mem_weightSpace : vlsr ∈ weightSpace R vQ Vμs (-μ.1) := by
  have h := lowestVector_mem_weightSpace P μs (dualIntegralWeight P weight w) w.reverse
  have he : (μs).1 - R.rootSum (lowestContent P weight w) = -μ.1 := by
    rw [dualWeight_val, sub_sub_cancel_left]
  rwa [lowestContent_reverse P weight w, he] at h

include hR hdom hm hw hlong in
/-- The two lowest weight vectors of `V_{μ*}` are proportional:
`v_l^{μ*}(w̄) = c v_l^{μ*}(w)` with `c = (v_l^{μ*}(w̄), v_l^{μ*}(w))`. -/
theorem lowestVector_reverse_eq_smul : vlsr = Bs vlsr vls • vls := by
  have hx := twistLowestLinear_mem_weightSpace P hR μ weight hdom hm w hw hlong
    (lowestVector_reverse_mem_weightSpace P μ weight hdom hm w hw hlong)
  rw [neg_neg] at hx
  obtain ⟨c, hc⟩ := exists_eq_smul_hwv_of_mem_weightSpace
    (hvt := LusztigF.transcendental_ratFunc_X) (hR := hR) μ hx
  have hz : vlsr = (c * (aμ)⁻¹) • vls := by
    have h := congrArg (twistLowestEquiv P hR μ weight hdom hm w hw hlong).symm hc
    change (twistLowestEquiv P hR μ weight hdom hm w hw hlong).symm
      (twistLowestEquiv P hR μ weight hdom hm w hw hlong vlsr) = _ at h
    rw [LinearEquiv.symm_apply_apply, map_smul, twistLowestEquiv_symm_hwv, smul_smul] at h
    exact h
  have hn := form_lowestVector P hR μs (dualIntegralWeight P weight w)
    (isDominantIntegral_dualIntegralWeight P weight hdom w hlong)
    (dualIntegralWeight_coroot P μ weight hdom hm w hw hlong) w hw
  conv_rhs => rw [hz]
  rw [LinearMap.map_smul, LinearMap.smul_apply, hn, smul_eq_mul, mul_one]
  exact hz

include hR hdom hm hw hlong in
/-- **The comparison sign squares to one**: `c² = 1`, from `(v_l, v_l) = 1` for both reduced
expressions. -/
theorem lowestVector_reverse_form_mul_self : Bs vlsr vls * Bs vlsr vls = 1 := by
  have hr := form_lowestVector P hR μs (dualIntegralWeight P weight w)
    (isDominantIntegral_dualIntegralWeight P weight hdom w hlong)
    (dualIntegralWeight_coroot P μ weight hdom hm w hw hlong) w.reverse
    (by rw [List.reverse_reverse]; exact ((cs).isReduced_reverse_iff w).mp hw)
  have hn := form_lowestVector P hR μs (dualIntegralWeight P weight w)
    (isDominantIntegral_dualIntegralWeight P weight hdom w hlong)
    (dualIntegralWeight_coroot P μ weight hdom hm w hw hlong) w hw
  have h := lowestVector_reverse_eq_smul P hR μ weight hdom hm w hw hlong
  set c := Bs vlsr vls
  rw [h] at hr
  simpa only [map_smul, LinearMap.smul_apply, hn, smul_eq_mul, mul_one] using hr

include hR hdom hm hw hlong in
/-- **`a = ±(-1)^{2ρ^∨(μ)} v^{-2⟨μ,ρ⟩}`** (Webster, proof of Proposition 7.5, up to the sign
comparing the lowest weight vectors of `V_{μ*}` for `w` and `w̄`; Webster's value is `+`). -/
theorem dualLowestScalar_eq_or :
    aμ = (-1) ^ wordHeight dμ * vQ ^ (-wordRhoDegree Δ dμ) ∨
      aμ = -((-1) ^ wordHeight dμ * vQ ^ (-wordRhoDegree Δ dμ)) := by
  rw [dualLowestScalar_eq P hR μ weight hdom hm w hw hlong]
  rcases mul_self_eq_one_iff.mp
    (lowestVector_reverse_form_mul_self P hR μ weight hdom hm w hw hlong) with h | h
  · left; rw [h, mul_one]
  · right; rw [h, mul_neg_one]

include hR hdom hm hw hlong in
/-- **Webster's value** `a = (-1)^{2ρ^∨(μ)} q^{-2⟨μ,ρ⟩}` (proof of Proposition 7.5), given that
the lowest weight vectors of `V_{μ*}` along `w` and along the reversed expression agree (the
vector form of Proposition 7.2, a hypothesis here). -/
theorem dualLowestScalar_eq_of_lowestVector_reverse (hrev : vlsr = vls) :
    aμ = (-1) ^ wordHeight dμ * vQ ^ (-wordRhoDegree Δ dμ) := by
  rw [dualLowestScalar_eq P hR μ weight hdom hm w hw hlong, hrev,
    form_lowestVector P hR μs (dualIntegralWeight P weight w)
      (isDominantIntegral_dualIntegralWeight P weight hdom w hlong)
      (dualIntegralWeight_coroot P μ weight hdom hm w hw hlong) w hw, mul_one]

end Scalar

end Categorification.Stendhal.QuantumDual

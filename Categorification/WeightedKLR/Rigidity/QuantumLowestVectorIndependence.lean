/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.QuantumCoevaluationScalar
import LieLean.Algebra.QuantumGroup.ModuleSymmetry.Braid

/-!
# The extremal vectors of a divided coevaluation word depend only on the Weyl element

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.1,
Proposition 7.2, on vectors: for a reduced expression `w` of an element `g` of the Weyl group
and a dominant weight `λ`, the vector `F_{d(w)} v_h` of the divided coevaluation word `d(w)`
(`dividedLoweringWord`) depends only on `g`. Webster states this for the projectives
`P⁰_{i^λ}` (formalized as `KLR.CycKLR.coevaluationProjective_iso_of_same_weyl`); here it is
proved in the irreducible module `V_λ` of the quantum group over `ℚ(v)`.

Proof (ours, through Lusztig's symmetries `T_i = T''_{i,1}` of integrable modules): at each step
of an extremal word the current vector `x` has `E_i x = 0`
(`Stendhal.quantum_weightSpace_raise_extremal_eq_bot`) and `⟨i, wt x⟩ = n`, so
`T_i x = (-1)^n v_i^n F_i^{(n)} x` (cf. Lusztig, *Introduction to quantum groups*, 5.2.2;
`IntegrableSl2.T_dF_of_primitive`). Hence
`F_{d(w)} v_h = (-1)^{|d|} v^{-Σ dᵢ nᵢ} T_{w_k} ⋯ T_{w_1} v_h`
(`dividedLoweringWord_eq_smul_wordT`). The `T_i` satisfy the braid relations on integrable
modules (`QuantumGroup.wordT_braid`, Lusztig 39.4.3), so by Matsumoto's theorem the operator
depends only on `g` (`CoxeterSystem.braidLift_wordProd`), and the scalar depends only on the
content of the word, which depends only on `g`
(`Stendhal.coevaluationWord_multiplicities_eq_of_reduced`).

* `isBraidLiftable_nodeT`: the module symmetries satisfy the braid relations of the Coxeter
  matrix.
* `nodeT_eq_smul_qDivPow_F`: `T_i x = (-1)^n v_i^n F_i^{(n)} x` for `E_i x = 0`, `⟨i, wt x⟩ = n`.
* `dividedLoweringWord_eq_of_wordProd_eq`: **the vector form of Proposition 7.2**.
* `lowestVector_reverse_eq_lowestVector`: the lowest weight vectors of `V_{μ*}` along `w` and
  along the reversed expression agree, so the sign `c` of `QuantumDual.dualLowestScalar_eq` is
  `1`;
* `dualLowestScalar_eq_webster`: **`a = (-1)^{2ρ^∨(μ)} v^{-2⟨μ,ρ⟩}`**, Webster's value in the
  proof of Proposition 7.5, with no further hypothesis.
-/

noncomputable section

namespace Categorification.Stendhal.QuantumDual

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop KLR.CycKLR Module

/-! ### Lusztig's symmetries on integrable modules -/

section Symmetries

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
  {M : Type*} [AddCommGroup M] [Module k M] [Module (QuantumGroup R v) M]
  [IsScalarTower k (QuantumGroup R v) M] (hM : IsIntegrable R v M)

/-- **The braid relations for Lusztig's symmetries of an integrable module** (Lusztig 39.4.3,
via `QuantumGroup.wordT_braid`), in the form `IsBraidLiftable` used by Matsumoto's theorem. -/
theorem isBraidLiftable_nodeT :
    D.cartanMatrix.coxeterMatrix.IsBraidLiftable (nodeT R v M hv hM) := by
  intro i j hij hm
  have hMij := Matrix.coxeterMatrix_apply_of_ne D.cartanMatrix hij
  have hfin : D.cartanMatrix i j * D.cartanMatrix j i ≤ 3 := by
    by_contra h
    exact hm (by rw [hMij]; exact Matrix.coxeterEntry_of_four_le (by omega))
  change ((CoxeterSystem.alternatingWord i j (D.cartanMatrix.coxeterMatrix i j)).map _).prod =
    ((CoxeterSystem.alternatingWord j i (D.cartanMatrix.coxeterMatrix j i)).map _).prod
  rw [coxeterMatrix_comm i j]
  exact wordT_braid hv hM hij hfin

/-- **Lusztig's symmetry on a primitive vector** (cf. Lusztig 5.2.2): if `E_i x = 0` and `x` has a
weight `Λ` with `⟨i, Λ⟩ = n`, then `T_i x = (-1)^n v_i^n F_i^{(n)} x`. -/
theorem nodeT_eq_smul_qDivPow_F {Λ : Y →+ ℤ} {x : M} (hx : x ∈ weightSpace R v M Λ) (i : I)
    (n : ℕ) (hn : Λ (R.coroot i) = n) (hE : E R v i • x = 0) :
    nodeT R v M hv hM i x =
      ((-1) ^ n * (v ^ D.d i) ^ n) • (qDivPow (v ^ D.d i) n (F R v i) • x) := by
  have hη : x ∈ (nodeSl2 R v M hv hM i).wt n := by
    rw [nodeSl2_wt, ← hn]
    exact mem_nodeWt_of_mem hx
  have h := IntegrableSl2.T_dF_of_primitive (V := nodeSl2 R v M hv hM i)
    (pow_ne_zero _ (NeZero.ne v)) (pow_d_ne_one hv i) (pow_ne_zero _ (NeZero.ne v))
    (fun _ _ => rfl) hη hE (Nat.zero_le n)
  rw [IntegrableSl2.dF_zero, Nat.sub_zero, zero_add, mul_one] at h
  rw [h, IntegrableSl2.dF, nodeSl2_F, ← act_qDivPow]
  rfl

end Symmetries

/-! ### Divided coevaluation words through the symmetries -/

section Words

variable {I K H Y : Type*} [Fintype I] [DecidableEq I] [AddCommGroup Y]
    {Δ : LusztigCartanDatum I} {R : Δ.RootDatum Y}
    [Field K] [ConditionallyCompleteLinearOrder K] [IsStrictOrderedRing K]
    [AddCommGroup H] [Module K H] (P : Matrix.Realization Δ.cartanMatrix K H)

local notation "vQ" => (RatFunc.X : RatFunc ℚ)
local instance : NeZero vQ := ⟨RatFunc.X_ne_zero⟩
local notation "hCartan" => Δ.isGeneralizedCartan_cartanMatrix
local notation "Dc" => P.cartanDatum hCartan
local notation "cs" => P.coxeterSystem hCartan

omit [Fintype I] [DecidableEq I] in
theorem wordHeight_eq_length (d : List (I × ℕ)) :
    wordHeight d = (KLR.KLRAlgebra.expandDiv d).length := by
  induction d with
  | nil => rfl
  | cons a d ih =>
    have hx : KLR.KLRAlgebra.expandDiv (a :: d) =
        List.replicate a.2 a.1 ++ KLR.KLRAlgebra.expandDiv d := List.flatMap_cons
    rw [hx, List.length_append, List.length_replicate, ← ih]
    simp only [wordHeight, List.map_cons, List.sum_cons]

omit [Fintype I] [DecidableEq I] in
theorem wordRhoDegree_eq_sum (d : List (I × ℕ)) :
    wordRhoDegree Δ d = ((KLR.KLRAlgebra.expandDiv d).map fun i => (Δ.d i : ℤ)).sum := by
  induction d with
  | nil => rfl
  | cons a d ih =>
    have hx : KLR.KLRAlgebra.expandDiv (a :: d) =
        List.replicate a.2 a.1 ++ KLR.KLRAlgebra.expandDiv d := List.flatMap_cons
    rw [hx, List.map_append, List.sum_append, List.map_replicate, List.sum_replicate, ← ih]
    simp only [wordRhoDegree, List.map_cons, List.sum_cons, nsmul_eq_mul]
    ring

variable [FiniteDimensional K H] (hR : R.IsXRegular) (ν : Dom R) (lam : P.integralWeights)
  (hdom : P.IsDominantIntegral (lam : Dual K H))
  (hm : ∀ j, (lam : Dual K H) (P.coroot j) = (ν.1 (R.coroot j) : K))

omit [Fintype I] [DecidableEq I] in
theorem ratFunc_X_pow_ne_one : ∀ n : ℕ, 0 < n → vQ ^ n ≠ 1 :=
  fun _ hn => LusztigF.pow_ne_one_of_transcendental LusztigF.transcendental_ratFunc_X hn

local notation "hvQ" => ratFunc_X_pow_ne_one
set_option hygiene false in
local notation "TV" => nodeT R vQ (IrreducibleModule R vQ ν.1) hvQ
  (IrreducibleModule.isIntegrable hR hvQ ν.2)

include hR hdom hm in
/-- **A divided coevaluation word through Lusztig's symmetries**: for a reduced expression `w`
(`w.reverse` reduced), `F_{d(w)} v_h = (-1)^{|d|} v^{-Σ dᵢ nᵢ} T_{w_k} ⋯ T_{w_1} v_h`, with
`d = d(w)` the divided coevaluation word. -/
theorem dividedLoweringWord_eq_smul_wordT (w : List I) (hw : (cs).IsReduced w.reverse) :
    dividedLoweringWord ν (coevaluationDividedWord Dc lam w) =
      ((-1) ^ wordHeight (coevaluationDividedWord Dc lam w) *
        vQ ^ (-wordRhoDegree Δ (coevaluationDividedWord Dc lam w))) •
        (w.reverse.map TV).prod (IrreducibleModule.hwv R vQ ν.1) := by
  induction w using List.reverseRecOn with
  | nil => simp [dividedLoweringWord, coevaluationDividedWord, wordHeight, wordRhoDegree]
  | append_singleton w i ih =>
    rw [List.reverse_append, List.reverse_singleton, List.singleton_append] at hw
    have hw' : (cs).IsReduced w.reverse := by simpa using hw.drop 1
    have hnd : ¬(cs).IsLeftDescent ((cs).wordProd w.reverse) i := by
      apply (cs).not_isLeftDescent_iff.mpr
      rw [← (cs).wordProd_cons, hw.eq, hw'.eq, List.length_cons]
    -- the pairing read by the last block
    set e := (Dc).coroot i (w.foldl (fun μ j => (Dc).reflection j μ) lam) with he
    have he0 : 0 ≤ e := by
      have h := Matrix.Realization.apply_coroot_nonneg_of_not_isLeftDescent hdom hnd
      rw [← coe_foldl_reflection_cartanDatum P hCartan w lam,
        ← P.coroot_cartanDatum_cast hCartan] at h
      exact_mod_cast h
    set x := dividedLoweringWord ν (coevaluationDividedWord Dc lam w) with hxdef
    have hx : x ∈ weightSpace R vQ _ (ν.1 - R.rootSum (lowestContent P lam w)) :=
      lowestVector_mem_weightSpace P ν lam w
    have hpair : (ν.1 - R.rootSum (lowestContent P lam w)) (R.coroot i) = (e.toNat : ℕ) := by
      rw [Int.toNat_of_nonneg he0]
      exact coevaluation_endpoint_pairing R P ν.1 lam hm w
        (nonnegativeReflectionPath_of_reduced P hCartan lam hdom w hw') i
    have hβ : (lam : Dual K H) - P.rootOf (fun j => (lowestContent P lam w j : ℤ)) =
        ((cs).wordProd w.reverse).val lam := by
      have h := rootSum_coevaluationWord_of_reduced P hCartan lam hdom w hw'
      rw [P.coe_rootSum_cartanDatum hCartan] at h
      change P.rootOf (fun j => (lowestContent P lam w j : ℤ)) = _ at h
      rw [h, sub_sub_cancel]
    have hE : E R vQ i • x = 0 := by
      have h1 := E_smul_mem_weightSpace (R := R) (v := vQ) hx i
      rw [quantum_weightSpace_raise_extremal_eq_bot P hR ν.1 (lam : Dual K H) hdom hm _
        (lowestContent P lam w) hβ i hnd, Submodule.mem_bot] at h1
      exact h1
    have hT := nodeT_eq_smul_qDivPow_F hvQ (IrreducibleModule.isIntegrable hR hvQ ν.2) hx i
      e.toNat hpair hE
    have hs : dividedLoweringWord ν (coevaluationDividedWord Dc lam (w ++ [i])) =
        qDivPow (vQ ^ Δ.d i) e.toNat (F R vQ i) • x := by
      rw [coevaluationDividedWord_snoc]
      simp [dividedLoweringWord, List.foldl_append, hxdef, he]
    have hv : vQ ≠ 0 := RatFunc.X_ne_zero
    have hc : ((-1 : RatFunc ℚ) ^ e.toNat * (vQ ^ Δ.d i) ^ e.toNat) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (pow_ne_zero _ hv))
    rw [hs, eq_inv_smul_iff₀ hc |>.mpr hT.symm, ih hw', List.reverse_append,
      List.reverse_singleton, List.singleton_append, List.map_cons, List.prod_cons,
      Module.End.mul_apply, map_smul, smul_smul, coevaluationDividedWord_snoc]
    congr 1
    simp only [wordHeight, wordRhoDegree, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero, ← he]
    rw [pow_add, neg_add, zpow_add₀ hv, ← pow_mul, show
      vQ ^ (-((Δ.d i : ℤ) * (e.toNat : ℤ))) = ((vQ ^ (Δ.d i * e.toNat)))⁻¹ by
        rw [zpow_neg, ← zpow_natCast]; push_cast; rfl]
    have h1 : ((-1 : RatFunc ℚ) ^ e.toNat)⁻¹ = (-1) ^ e.toNat := by
      rw [← inv_pow, inv_neg, inv_one]
    rw [mul_inv, h1]
    ring

include hR hdom hm in
/-- **Webster's Proposition 7.2 on vectors**: for two reduced expressions `w`, `w'` of the same
element of the Weyl group (`w.reverse`, `w'.reverse` reduced with the same product), the
divided coevaluation words give the same vector `F_{d(w)} v_h = F_{d(w')} v_h` of `V_λ`. -/
theorem dividedLoweringWord_eq_of_wordProd_eq (w w' : List I) (hw : (cs).IsReduced w.reverse)
    (hw' : (cs).IsReduced w'.reverse)
    (he : (cs).wordProd w.reverse = (cs).wordProd w'.reverse) :
    dividedLoweringWord ν (coevaluationDividedWord Dc lam w) =
      dividedLoweringWord ν (coevaluationDividedWord Dc lam w') := by
  have hmul := coevaluationWord_multiplicities_eq_of_reduced P hCartan lam hdom w w' hw hw' he
  rw [← expand_coevaluationDividedWord, ← expand_coevaluationDividedWord] at hmul
  have hht : wordHeight (coevaluationDividedWord Dc lam w) =
      wordHeight (coevaluationDividedWord Dc lam w') := by
    rw [wordHeight_eq_length, wordHeight_eq_length, ← Multiset.coe_card, hmul, Multiset.coe_card]
  have hrho : wordRhoDegree Δ (coevaluationDividedWord Dc lam w) =
      wordRhoDegree Δ (coevaluationDividedWord Dc lam w') := by
    rw [wordRhoDegree_eq_sum, wordRhoDegree_eq_sum, ← Multiset.sum_coe, ← Multiset.map_coe, hmul,
      Multiset.map_coe, Multiset.sum_coe]
  have hg := isBraidLiftable_nodeT hvQ (IrreducibleModule.isIntegrable hR hvQ ν.2)
  rw [dividedLoweringWord_eq_smul_wordT P hR ν lam hdom hm w hw,
    dividedLoweringWord_eq_smul_wordT P hR ν lam hdom hm w' hw', hht, hrho,
    ← CoxeterSystem.braidLift_wordProd hg hw,
    ← CoxeterSystem.braidLift_wordProd hg hw', he]

end Words

/-! ### The sign of the coevaluation scalar -/

section Scalar

variable {I K H Y : Type*} [Fintype I] [DecidableEq I] [AddCommGroup Y]
    {Δ : LusztigCartanDatum I} {R : Δ.RootDatum Y}
    [Field K] [ConditionallyCompleteLinearOrder K] [IsStrictOrderedRing K]
    [AddCommGroup H] [Module K H] (P : Matrix.Realization Δ.cartanMatrix K H)

local notation "vQ" => (RatFunc.X : RatFunc ℚ)
local instance : NeZero vQ := ⟨RatFunc.X_ne_zero⟩
local notation "hCartan" => Δ.isGeneralizedCartan_cartanMatrix
local notation "Dc" => P.cartanDatum hCartan
local notation "cs" => P.coxeterSystem hCartan

variable [FiniteDimensional K H] [Finite (P.weylGroup Δ.isGeneralizedCartan_cartanMatrix)]
  (hR : R.IsXRegular) (μ : Dom R) (weight : P.integralWeights)
  (hdom : P.IsDominantIntegral (weight : Dual K H))
  (hm : ∀ j, (weight : Dual K H) (P.coroot j) = (μ.1 (R.coroot j) : K))
  (w : List I)
variable (hw : (P.coxeterSystem Δ.isGeneralizedCartan_cartanMatrix).IsReduced w.reverse)
  (hlong : ∀ i, (P.coxeterSystem Δ.isGeneralizedCartan_cartanMatrix).IsLeftDescent
    ((P.coxeterSystem Δ.isGeneralizedCartan_cartanMatrix).wordProd w.reverse) i)

local notation "μs" => dualWeight P μ weight hdom hm w hw hlong
local notation "dμ" => Stendhal.coevaluationDividedWord Dc weight w

include hR hdom hm hw hlong in
/-- **The lowest weight vectors of `V_{μ*}` along `w` and its reverse agree** (finite type:
`w` and `w.reverse` are both reduced expressions of `w₀ = w₀⁻¹`). This is the value `c = 1` of
the comparison sign in `QuantumDual.dualLowestScalar_eq`. -/
theorem lowestVector_reverse_eq_lowestVector :
    lowestVector P μs (dualIntegralWeight P weight w) w.reverse =
      lowestVector P μs (dualIntegralWeight P weight w) w := by
  have hπ : (cs).wordProd w.reverse = (cs).longestElement := by
    have h : ((cs).wordProd w.reverse)⁻¹ = (cs).longestElement :=
      (cs).eq_longestElement_iff_forall_isRightDescent.2 fun j =>
        (cs).isRightDescent_inv_iff.2 (hlong j)
    rw [← (cs).inv_longestElement, ← h, inv_inv]
  have hrev : (cs).IsReduced w.reverse.reverse := by
    rw [List.reverse_reverse]; exact ((cs).isReduced_reverse_iff w).mp hw
  have he : (cs).wordProd w.reverse.reverse = (cs).wordProd w.reverse := by
    rw [CoxeterSystem.wordProd_reverse, hπ, (cs).inv_longestElement]
  exact dividedLoweringWord_eq_of_wordProd_eq P hR μs (dualIntegralWeight P weight w)
    (isDominantIntegral_dualIntegralWeight P weight hdom w hlong)
    (dualIntegralWeight_coroot P μ weight hdom hm w hw hlong) w.reverse w hrev hw he

include hR hdom hm hw hlong in
/-- **Webster's value of the coevaluation scalar** (proof of Proposition 7.5):
`Θ(v_l^{μ*}) = a v_h^μ` with `a = (-1)^{2ρ^∨(μ)} v^{-2⟨μ,ρ⟩}`, where `2ρ^∨(μ) = |d|` is the
number of lowering generators of the coevaluation word `d` of `μ` and `2⟨μ,ρ⟩ = Σ_{i ∈ d} dᵢ`
its `ρ`-degree. -/
theorem dualLowestScalar_eq_webster :
    dualLowestScalar P hR μ weight hdom hm w hw hlong =
      (-1) ^ wordHeight dμ * vQ ^ (-wordRhoDegree Δ dμ) :=
  dualLowestScalar_eq_of_lowestVector_reverse P hR μ weight hdom hm w hw hlong
    (lowestVector_reverse_eq_lowestVector P hR μ weight hdom hm w hw hlong)

end Scalar

end Categorification.Stendhal.QuantumDual

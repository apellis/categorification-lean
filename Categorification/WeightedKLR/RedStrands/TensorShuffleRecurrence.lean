/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorCoproductWords
import Categorification.WeightedKLR.RedStrands.TensorWordProjectives

/-!
# Shuffle coefficients of ordinary and divided black blocks

Webster, arXiv:1309.3796v2, §4.6–4.7 and (5.10). In the bar coproduct
a final letter assigned to the earlier factor crosses the final red strand
and each previously assigned black strand of the final factor. The exponent
is the signed degree of these crossings. The quasi-R equivalence carries
these divided tensor words to the ordinary-coproduct words.
-/

noncomputable section
namespace Categorification.Stendhal.FirstWeight
open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF TensorProduct
open scoped TensorProduct
local notation "L" => RatFunc ℚ
local notation "v" => (RatFunc.X : L)
local instance : NeZero v := ⟨RatFunc.X_ne_zero⟩
variable {I Y : Type*} [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I} {R : D.RootDatum Y} {m : ℕ}
local notation "𝕌" => LieLean.QuantumGroup R v
local notation "divF" => fun (i : I) (a : ℕ) => qDivPow (v ^ D.d i) a (F R v i)

private theorem bar_divF (i : I) (n : ℕ) : barHom R (divF i n) = divF i n := by
  simp [qDivPow, barHom_smul, bar_qFactorial]

/-- The divided bar coproduct has the factor `vᵢ^(-rs)` and the positive torus
on the right. Here `r` counts final-factor letters and `s` preceding-factor letters. -/
theorem barComul_dividedF (i : I) (n : ℕ) :
    barComul R (divF i n) = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
      ((v ^ D.d i) ^ (p.1*p.2))⁻¹ • (divF i p.2 ⊗ₜ[L] (divF i p.1 * K R v (ktilde R i) ^ p.2)) := by
  rw [barComul_apply, bar_divF, Categorification.QuantumGroup.comul_dividedF, map_sum]
  apply Finset.sum_congr rfl
  rintro ⟨r,s⟩ _
  simp only [barTensor_smul, map_pow, RatFunc.bar_X, inv_pow, barTensor_tmul, bar_divF, map_mul,
    barHom_K, neg_neg]

variable (wt : Fin (m+1) → Dom R)
local notation "wt₀" => fun j : Fin m => wt (Fin.castSucc j)
local notation "λ₁" => wt (Fin.last m)
local notation "V₀" => TensorSpace wt₀
local notation "V₁" => IrreducibleModule R v (Subtype.val λ₁)

private abbrev barPair : 𝕌 ⊗[L] 𝕌 →ₐ[L] Module.End L (V₀ ⊗[L] V₁) :=
  (Module.endTensorEndAlgHom (R := L) (S := L) (A := L)).comp
    (Algebra.TensorProduct.map (barTensorRepresentation wt₀) (Algebra.lsmul L L V₁))

private theorem barPair_tmul (a b : 𝕌) (x : V₀) (y : V₁) :
    barPair wt (a ⊗ₜ[L] b) (x ⊗ₜ[L] y) = barTensorRepresentation wt₀ a x ⊗ₜ[L] (b • y) := by
  simp [barPair, Module.endTensorEndAlgHom_apply]

private theorem bar_append (u : 𝕌) (x : V₀) (y : V₁) :
    barTensorRepresentation wt u (appendTensor wt x y) =
      (tensorSplitLast wt).symm (barPair wt (barComul R u) (x ⊗ₜ[L] y)) := by
  change (tensorSplitLast wt).symm (barPair wt (barComul R u)
    (tensorSplitLast wt ((tensorSplitLast wt).symm (x ⊗ₜ[L] y)))) = _
  rw [LinearEquiv.apply_symm_apply]

/-- Assigning an ordinary black letter to the prefix contributes the right
weight evaluated at the positive symmetrized coroot. Assigning it to the
last factor has coefficient one. -/
theorem barTensorRepresentation_F_append (i : I) (x : V₀) (y : V₁) {μ : Y →+ ℤ}
    (hy : y ∈ weightSpace R v V₁ μ) :
    barTensorRepresentation wt (F R v i) (appendTensor wt x y) =
      v ^ μ (ktilde R i) • appendTensor wt (barTensorRepresentation wt₀ (F R v i) x) y +
        appendTensor wt x (F R v i • y) := by
  rw [bar_append, barComul_F, map_add, LinearMap.add_apply, barPair_tmul, barPair_tmul, map_add,
    (mem_weightSpace.mp hy) _, map_one, Module.End.one_apply, TensorProduct.tmul_smul, map_smul]
  rfl

/-- A divided block splits between `r` right and `s` left letters with
exponent `s μ(k̃ᵢ) − dᵢrs`. -/
theorem barTensorRepresentation_dividedF_append (i : I) (n : ℕ) (x : V₀) (y : V₁)
    {μ : Y →+ ℤ} (hy : y ∈ weightSpace R v V₁ μ) :
    barTensorRepresentation wt (divF i n) (appendTensor wt x y) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
        v ^ ((p.2 : ℤ) * μ (ktilde R i) - (D.d i : ℤ) * (p.1*p.2)) •
          appendTensor wt (barTensorRepresentation wt₀ (divF i p.2) x) (divF i p.1 • y) := by
  rw [bar_append, barComul_dividedF, map_sum, LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  rintro ⟨r,s⟩ _
  have ht : K R v (ktilde R i) ^ s = K R v (s • ktilde R i) :=
    (map_pow (KHom R v) (Multiplicative.ofAdd (ktilde R i)) s).symm
  rw [map_smul, LinearMap.smul_apply, barPair_tmul, mul_smul, ht, (mem_weightSpace.mp hy) _,
    smul_comm (divF i r), TensorProduct.tmul_smul, map_smul, map_smul, smul_smul]
  congr 1
  rw [map_nsmul, nsmul_eq_mul, zpow_sub₀ RatFunc.X_ne_zero, ← pow_mul,
    ← Nat.cast_mul, ← Nat.cast_mul, zpow_natCast, mul_comm, div_eq_mul_inv]

omit [DecidableEq I] in
/-- The final-factor weight counts the red/black crossing and every
black/black crossing, including nonsimply-laced Cartan degrees. -/
theorem shuffleExponent_eq_crossings (highest : Y →+ ℤ) (u : List I) (i : I) :
    (highest - (u.map R.root).sum) (ktilde R i) =
      (D.d i : ℤ) * highest (R.coroot i) - (u.map fun j => D.dot i j).sum := by
  rw [AddMonoidHom.sub_apply]
  congr 1
  · simp [ktilde]
  · induction u with
    | nil => simp
    | cons j u ih => simp [AddMonoidHom.add_apply, root_ktilde_eq_dot, ih]

/-- Read a suffix of divided black blocks from left to right. -/
def barDividedWordOp : List (I × ℕ) → Module.End L (TensorSpace wt)
  | [] => 1
  | (i,a) :: tail => barDividedWordOp tail * barTensorRepresentation wt (divF i a)

/-- Split each successive divided block between the earlier tensor and the
final factor. Each right assignment lowers the weight used for later
shuffle coefficients. -/
def dividedShuffle (x : V₀) (y : V₁) (μ : Y →+ ℤ) : List (I × ℕ) → TensorSpace wt
  | [] => appendTensor wt x y
  | (i,n) :: tail => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
      v ^ ((p.2 : ℤ) * μ (ktilde R i) - (D.d i : ℤ) * (p.1*p.2)) •
        dividedShuffle (barTensorRepresentation wt₀ (divF i p.2) x) (divF i p.1 • y)
          (μ - p.1 • R.root i) tail

/-- The recursive signed shuffle evaluates every post-red suffix, including
zero-sized divided powers and the empty suffix. -/
theorem barDividedWordOp_append (x : V₀) (y : V₁) {μ : Y →+ ℤ} (hy : y ∈ weightSpace R v V₁ μ)
    (d : List (I × ℕ)) :
    barDividedWordOp wt d (appendTensor wt x y) = dividedShuffle wt x y μ d := by
  induction d generalizing x y μ with
  | nil => rfl
  | cons q d ih =>
    obtain ⟨i,n⟩ := q
    rw [barDividedWordOp, Module.End.mul_apply, barTensorRepresentation_dividedF_append wt i n x y hy,
      map_sum, dividedShuffle]
    apply Finset.sum_congr rfl
    rintro ⟨r,s⟩ _
    rw [map_smul, ih _ _ (qDivPow_F_smul_mem_weightSpace hy i r)]

/-- The ordinary vector in the bar coproduct convention, obtained by assigning
each undivided black letter to one of the two factors in the shuffle. -/
def barOrdinaryWord : {n : ℕ} → TensorWord I n → (weights : Fin n → Dom R) → TensorSpace weights
  | _, .empty, weights => tensorWordVector .empty weights
  | n+1, .red w, weights => appendTensor weights (barOrdinaryWord w (fun j => weights (Fin.castSucc j)))
      (IrreducibleModule.hwv R v (weights (Fin.last n)).1)
  | _, .black w i a, weights => barTensorRepresentation weights (F R v i ^ a) (barOrdinaryWord w weights)

variable [Finite I] {C : Categorification.QuantumGroup.CartanDatum I} {R' : C.toLusztig.RootDatum Y}

/-- The quasi-R equivalence carries all ordinary shuffle words to the
ordinary vectors in the printed coproduct convention. -/
theorem tensorCoproductEquiv_ordinary (hR : R'.IsXRegular) :
    ∀ {n : ℕ} (w : TensorWord I n) (weights : Fin n → Dom R'),
    tensorCoproductEquiv hR weights (barOrdinaryWord w weights) = tensorWordUndivided w weights
  | _, .empty, weights => rfl
  | _, .red w, weights => by
    rw [barOrdinaryWord, tensorCoproductEquiv_append, tensorCoproductEquiv_ordinary hR w]
    rfl
  | _, .black w i a, weights => by
    rw [barOrdinaryWord, tensorCoproductEquiv_act, tensorCoproductEquiv_ordinary hR w]
    rfl

end Categorification.Stendhal.FirstWeight

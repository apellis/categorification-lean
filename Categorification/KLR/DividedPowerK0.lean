/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Cor215
import Categorification.KLR.GradingFlip
import Categorification.Algebra.Graded.IdempotentSplittingK0

/-!
# The projectives `P_i` of divided-power expressions in `K₀(R(ν))`

M. Khovanov, A. Lauda, *A diagrammatic approach to categorification of quantum groups I*,
arXiv:0803.4121v2, §2.5 (TeX lines ~1615–1660): for a divided-power expression
`i = i_1^{(n_1)} ⋯ i_r^{(n_r)} ∈ Seq'(ν)` (a list `d` of pairs `(i_a, n_a)`), the graded
projective left module

  `P_i = R(ν) ψ(1_i) {-⟨i⟩}`   (`projDiv`),

"We have `P_î ≅ P_i^{i!}`", and Proposition 2.13 (left modules):
`P_{…ij…} ≅ P_{…ji…}` if `i · j = 0` and `P_{…iji…} ≅ P_{…i^{(2)}j…} ⊕ P_{…ji^{(2)}…}` if
`i · j = -1`.

We prove the corresponding identities in `K₀(R(ν))` (a `ℤ[q, q⁻¹]`-module, `q^a [P] = [P{a}]`),
for the KL I grading over any commutative ring `k`:

* `K0_projP_expandDiv` : `[P_î] = i! [P_i]`, with `i! = [n_1]! ⋯ [n_r]! ∈ ℤ[q, q⁻¹]`
  (`P_î = R(ν) 1_î` is `projSeq`, which is `GradingDatum.projP` over a field);
* `K0_projDiv_zero` : `[P_{…ij…}] = [P_{…ji…}]` if `i · j = 0`;
* `K0_projDiv_neg_one` : `[P_{…iji…}] = [P_{…i^{(2)}j…}] + [P_{…ji^{(2)}…}]` if `i · j = -1`.

The proofs apply `Graded.K0.of_ofIdempotent_eq_sum_of_isSplitting` to the images under `ψ`
(`hflip`, degree-preserving by `KL1.hflip_mem_grade`) of the splittings of
`Categorification.KLR.NilHeckeBlockSplitting` and `Categorification.KLR.Cor215`.
-/

noncomputable section

namespace Categorification.KLR

open Graded KLRAlgebra LaurentPolynomial QuantumGroup Finset

/-! ### Quantum integers in `ℤ[q, q⁻¹]` -/

/-- The unit `q = T 1 ∈ ℤ[q, q⁻¹]`. -/
def qUnitLP : (LaurentPolynomial ℤ)ˣ where
  val := T 1
  inv := T (-1)
  val_inv := by rw [← T_add]; simp
  inv_val := by rw [← T_add]; simp

theorem val_qUnitLP_zpow (z : ℤ) :
    ((qUnitLP ^ z : (LaurentPolynomial ℤ)ˣ) : LaurentPolynomial ℤ) = T z := by
  rcases z with n | n
  · rw [Int.ofNat_eq_coe, zpow_natCast, Units.val_pow_eq_pow_val]
    show (T 1 : LaurentPolynomial ℤ) ^ n = _
    rw [T_pow, mul_one]
  · rw [zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val]
    show (T (-1) : LaurentPolynomial ℤ) ^ (n + 1) = _
    rw [T_pow, Int.negSucc_eq]
    congr 1
    push_cast; ring

theorem qint_qUnitLP (n : ℕ) :
    qint qUnitLP n = ∑ j ∈ range n, (T ((n : ℤ) - 1 - 2 * j) : LaurentPolynomial ℤ) := by
  rw [qint_eq_sum]
  exact sum_congr rfl fun j _ => val_qUnitLP_zpow _

/-- The factor `q^{-n(n-1)/2} [n]!` of a divided power `i^{(n)}`, in `ℤ[q, q⁻¹]`. -/
def blockFactorLP (n : ℕ) : LaurentPolynomial ℤ := T (-(n.choose 2 : ℤ)) * qfact qUnitLP n

theorem blockFactorLP_zero : blockFactorLP 0 = 1 := by simp [blockFactorLP]

theorem blockFactorLP_succ (n : ℕ) :
    blockFactorLP (n + 1) = blockFactorLP n * (T (-(n : ℤ)) * qint qUnitLP (n + 1)) := by
  rw [blockFactorLP, blockFactorLP, qfact_succ, NilHecke.choose_two_succ,
    show (-(((n.choose 2 + n : ℕ)) : ℤ)) = -(n.choose 2 : ℤ) + -(n : ℤ) by push_cast; ring,
    T_add]
  ring

theorem sum_T_two_mul_sub (n : ℕ) :
    ∑ j : Fin (n + 1), (T (2 * ((j : ℤ) - n)) : LaurentPolynomial ℤ) =
      T (-(n : ℤ)) * qint qUnitLP (n + 1) := by
  rw [qint_qUnitLP, mul_sum, Fin.sum_univ_eq_sum_range (fun j => (T (2 * ((j : ℤ) - n)) :
    LaurentPolynomial ℤ)) (n + 1), ← sum_range_reflect]
  refine sum_congr rfl fun j hj => ?_
  rw [mem_range] at hj
  rw [← T_add]
  congr 1
  push_cast [Nat.cast_sub (show j ≤ n by omega)]
  ring

/-- `i! = [n_1]! ⋯ [n_r]!` in `ℤ[q, q⁻¹]`. -/
def divQFactLP {I : Type*} (d : List (I × ℕ)) : LaurentPolynomial ℤ :=
  (d.map fun q => qfact qUnitLP q.2).prod

theorem prod_blockFactorLP_blocksDiv {I : Type*} (d : List (I × ℕ)) (p : ℕ) :
    ((blocksDiv d p).map fun b => blockFactorLP b.2).prod =
      T (-(divAngle d : ℤ)) * divQFactLP d := by
  induction d generalizing p with
  | nil => simp [blocksDiv, divAngle, divQFactLP]
  | cons q d ih =>
    simp only [blocksDiv, List.map_cons, List.prod_cons, ih, divAngle, divQFactLP,
      List.sum_cons]
    rw [blockFactorLP, show (-(((q.2.choose 2 + (d.map fun q => q.2.choose 2).sum : ℕ)) : ℤ)) =
      -(q.2.choose 2 : ℤ) + -(((d.map fun q => q.2.choose 2).sum : ℕ) : ℤ) by push_cast; ring,
      T_add]
    ring

/-! ### Splittings under the antiinvolution -/

theorem _root_.Categorification.Graded.IsSplitting.map_anti {A : Type*} [Ring A] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {E' : A} {E a b : ι → A} (h : Graded.IsSplitting E' E a b) (φ : A →+ A)
    (hφ : ∀ x y, φ (x * y) = φ y * φ x) :
    Graded.IsSplitting (φ E') (fun j => φ (E j)) (fun j => φ (b j)) (fun j => φ (a j)) where
  mul_eq i j := by
    rw [← hφ, h.mul_eq]
    by_cases hij : j = i
    · subst hij; simp
    · rw [if_neg hij, if_neg (Ne.symm hij), map_zero]
  sum_eq := by simp_rw [← hφ, ← map_sum, h.sum_eq]

/-! ### The modules `P_i` -/

section Proj

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {Γ : SimpleGraph I}
  [DecidableRel Γ.Adj] {ν : Multiset I}

local notation "A" => R1 k Γ ν
local notation "Gkl" => klGradingDatum k Γ

/-- `hflip` as an additive map of `R(ν)`. -/
def hflipAddKL : A →+ A := AddMonoidHom.mk' hflip hflip_add

@[simp] theorem hflipAddKL_apply (a : A) : hflipAddKL a = hflip a := rfl

variable (k Γ) in
/-- The graded projective module `P_t = R(ν) 1_t` of a sequence `t` (as `GradingDatum.projP`,
over any commutative ring `k`). -/
def projSeq (t : Seq ν) : GProj ((klGradingDatum k Γ).grade ν) :=
  GProj.ofIdempotent (e t : A) (e_mul_self t) ((klGradingDatum k Γ).e_mem_grade t)

variable (k Γ) in
/-- The graded projective module `R(ν) ψ(1_t^{bs})` for a sequence `t` with divided-power blocks
`bs` (without grading shift). -/
def projFlip (t : Seq ν) (bs : List (ℕ × ℕ)) (h : IsBlocks t bs) : GProj ((klGradingDatum k Γ).grade ν) :=
  GProj.ofIdempotent (hflip (divIdem t bs : A)) (isIdempotentElem_hflip_divIdem h)
    (KL1.hflip_mem_grade (divIdem_mem_grade _ h))

variable (k Γ) in
/-- **The projective `P_i = R(ν) ψ(1_i) {-⟨i⟩}`** of a divided-power expression `i` (KL I §2.5). -/
def projDiv (d : List (I × ℕ)) (h : (expandDiv d : Multiset I) = ν) :
    GProj ((klGradingDatum k Γ).grade ν) :=
  (projFlip k Γ _ _ (isBlocks_ofList d h)).shift (-(divAngle d : ℤ))

theorem K0_of_projFlip_congr {t t' : Seq ν} {bs bs' : List (ℕ × ℕ)} (h : IsBlocks t bs)
    (h' : IsBlocks t' bs') (he : (divIdem t bs : A) = divIdem t' bs') :
    K0.of (projFlip k Γ t bs h) = K0.of (projFlip k Γ t' bs' h') :=
  K0.of_ofIdempotent_congr (congrArg hflip he) _ _ _ _

/-- **Splitting a divided power, `K₀` form**:
`[R(ν) ψ(1_{…i^{(n)} i…})] = q^{-n} [n+1] [R(ν) ψ(1_{…i^{(n+1)}…})]`. -/
theorem K0_projFlip_succ {i : Seq ν} {p n : ℕ} {bs : List (ℕ × ℕ)}
    (h : IsBlocks i ((p, n + 1) :: bs)) :
    K0.of (projFlip k Γ i ((p, n) :: bs) (h.cons_mono (Nat.le_succ n))) =
      (T (-(n : ℤ)) * qint qUnitLP (n + 1)) • K0.of (projFlip k Γ i ((p, n + 1) :: bs) h) := by
  have hpn := h.le _ List.mem_cons_self
  have hc := h.const _ List.mem_cons_self
  simp only at hpn
  have hcl : ∀ a : Fin (Multiset.card ν), p ≤ a → (a : ℕ) < p + (n + 1) →
      i.lbl a = i.lbl ⟨p, by omega⟩ := fun a h1 h2 => hc a _ h1 h2 le_rfl (by simp only; omega)
  have S := (isSplitting_divIdem_succ (k := k) (Q := klQ Γ) h).map_anti hflipAddKL hflip_mul
  simp only [hflipAddKL_apply] at S
  rw [projFlip, projFlip, K0.of_ofIdempotent_eq_sum_of_isSplitting (dg := fun j : Fin (n + 1) =>
    2 * ((n : ℤ) - j)) S (fun j => ?_) (fun j => ?_) _ (fun _ => _) _ (fun _ => _),
    ← sum_T_two_mul_sub, sum_smul]
  · refine sum_congr rfl fun j _ => ?_
    congr 2
    ring
  · exact KL1.hflip_mem_grade (blockB_mem_grade (klGradingDatum k Γ) hpn hcl hc
      (show (j : ℕ) ≤ n by omega))
  · refine KL1.hflip_mem_grade ?_
    have := SetLike.mul_mem_graded (divIdem_mem_grade (klGradingDatum k Γ) h.tail)
      (blockA_mem_grade (klGradingDatum k Γ) hpn hcl hc j)
    convert this using 2
    show -(2 * ((n : ℤ) - j)) = 0 + 2 * ((j : ℤ) - n)
    ring

/-- **A divided power in a context, `K₀` form**:
`[R(ν) ψ(1_{…i⋯i…})] = q^{-n(n-1)/2} [n]! [R(ν) ψ(1_{…i^{(n)}…})]`. -/
theorem K0_projFlip_block {i : Seq ν} {p : ℕ} {bs : List (ℕ × ℕ)} (hbs : IsBlocks i bs) :
    ∀ {n : ℕ} (h : IsBlocks i ((p, n) :: bs)),
      K0.of (projFlip k Γ i bs hbs) = blockFactorLP n • K0.of (projFlip k Γ i ((p, n) :: bs) h)
  | 0, h => by
    rw [blockFactorLP_zero, one_smul]
    refine K0_of_projFlip_congr _ _ ?_
    rw [divIdem, divIdem, blocksElt_cons]
    simp only
    rw [blockElt_zero, one_mul]
  | n + 1, h => by
    rw [K0_projFlip_block hbs (h.cons_mono (Nat.le_succ n)), K0_projFlip_succ h, ← mul_smul,
      blockFactorLP_succ]

/-- Iterating over all blocks: `[R(ν) 1_t] = ∏_b q^{-n_b(n_b-1)/2} [n_b]! · [R(ν) ψ(1_t^{bs})]`. -/
theorem K0_projP_eq_prod_smul {t : Seq ν} :
    ∀ {bs : List (ℕ × ℕ)} (h : IsBlocks t bs),
      K0.of (projSeq k Γ t) =
        (bs.map fun b => blockFactorLP b.2).prod • K0.of (projFlip k Γ t bs h)
  | [], h => by
    rw [List.map_nil, List.prod_nil, one_smul]
    exact K0.of_ofIdempotent_congr (e := (e t : A)) (e' := hflip (divIdem t [] : A))
      (by rw [divIdem_nil, hflip_e]) _ _ _ _
  | b :: bs, h => by
    rw [K0_projP_eq_prod_smul h.tail, K0_projFlip_block (p := b.1) (n := b.2) h.tail h,
      List.map_cons, List.prod_cons, ← mul_smul, mul_comm]

/-- **KL I §2.5, `P_î ≅ P_i^{i!}` in `K₀`**: `[P_î] = i! [P_i]` for a divided-power expression
`i` with expansion `î` (`P_î = R(ν) 1_î`, `P_i = R(ν) ψ(1_i) {-⟨i⟩}`). -/
theorem K0_projP_expandDiv (d : List (I × ℕ)) (h : (expandDiv d : Multiset I) = ν) :
    K0.of (projSeq k Γ (Seq.ofList (expandDiv d) h)) =
      divQFactLP d • K0.of (projDiv k Γ d h) := by
  rw [K0_projP_eq_prod_smul (isBlocks_ofList d h), prod_blockFactorLP_blocksDiv, projDiv,
    ← K0.T_smul_of, ← mul_smul, mul_comm]

/-- **KL I, Proposition 2.13, case `i · j = -1`, in `K₀`**:
`[P_{…iji…}] = [P_{…i^{(2)}j…}] + [P_{…ji^{(2)}…}]`. -/
theorem K0_projDiv_neg_one (d' d'' : List (I × ℕ)) {i j : I} (hadj : Γ.Adj i j)
    (h₁ : (expandDiv (d' ++ [(i, 1), (j, 1), (i, 1)] ++ d'') : Multiset I) = ν)
    (h₂ : (expandDiv (d' ++ [(i, 2), (j, 1)] ++ d'') : Multiset I) = ν)
    (h₃ : (expandDiv (d' ++ [(j, 1), (i, 2)] ++ d'') : Multiset I) = ν) :
    K0.of (projDiv k Γ _ h₁) = K0.of (projDiv k Γ _ h₂) + K0.of (projDiv k Γ _ h₃) := by
  obtain ⟨f₁, f₂, a₁, b₁, a₂, b₂, H, H₁, H₂, ha₁, hb₁, ha₂, hb₂⟩ :=
    prop213_neg_one_divIdemOf (k := k) d' d'' hadj h₁ h₂ h₃
  have S := (isSplitting_of_isOrthDecomp H H₁ H₂).map_anti hflipAddKL hflip_mul
  simp only [hflipAddKL_apply] at S
  have key := K0.of_ofIdempotent_eq_sum_of_isSplitting (dg := fun _ : Fin 2 => (1 : ℤ)) S
    (fun j => by fin_cases j <;> exact KL1.hflip_mem_grade (by simpa))
    (fun j => by fin_cases j <;> exact KL1.hflip_mem_grade (by simpa))
    (isIdempotentElem_hflip_divIdem (isBlocks_ofList _ h₁))
    (fun j => by fin_cases j
                 · exact isIdempotentElem_hflip_divIdem (isBlocks_ofList _ h₂)
                 · exact isIdempotentElem_hflip_divIdem (isBlocks_ofList _ h₃))
    (KL1.hflip_mem_grade (divIdemOf_mem_grade _ _ h₁))
    (fun j => by fin_cases j
                 · exact KL1.hflip_mem_grade (divIdemOf_mem_grade _ _ h₂)
                 · exact KL1.hflip_mem_grade (divIdemOf_mem_grade _ _ h₃))
  rw [Fin.sum_univ_two] at key
  have e₁ : divAngle (d' ++ [(i, 1), (j, 1), (i, 1)] ++ d'') = divAngle d' + divAngle d'' := by
    simp [divAngle_append, divAngle]
  have e₂ : divAngle (d' ++ [(i, 2), (j, 1)] ++ d'') = divAngle d' + divAngle d'' + 1 := by
    simp [divAngle_append, divAngle]; omega
  have e₃ : divAngle (d' ++ [(j, 1), (i, 2)] ++ d'') = divAngle d' + divAngle d'' + 1 := by
    simp [divAngle_append, divAngle]; omega
  have key' : K0.of (projFlip k Γ _ _ (isBlocks_ofList _ h₁)) =
      (T (-1) : LaurentPolynomial ℤ) • K0.of (projFlip k Γ _ _ (isBlocks_ofList _ h₂)) +
        (T (-1) : LaurentPolynomial ℤ) • K0.of (projFlip k Γ _ _ (isBlocks_ofList _ h₃)) := key
  rw [projDiv, projDiv, projDiv, ← K0.T_smul_of, ← K0.T_smul_of, ← K0.T_smul_of, e₁, e₂, e₃,
    key', smul_add, ← mul_smul, ← mul_smul, ← T_add]
  congr 3 <;> push_cast <;> ring_nf

/-- **KL I, Proposition 2.13, case `i · j = 0`, in `K₀`**: `[P_{…ij…}] = [P_{…ji…}]`. -/
theorem K0_projDiv_zero (d' d'' : List (I × ℕ)) {i j : I} (hne : i ≠ j) (hadj : ¬ Γ.Adj i j)
    (h₁ : (expandDiv (d' ++ [(i, 1), (j, 1)] ++ d'') : Multiset I) = ν)
    (h₂ : (expandDiv (d' ++ [(j, 1), (i, 1)] ++ d'') : Multiset I) = ν) :
    K0.of (projDiv k Γ _ h₁) = K0.of (projDiv k Γ _ h₂) := by
  obtain ⟨a, b, H, ha, hb⟩ := prop213_zero_divIdemOf (k := k) d' d'' hne hadj h₁ h₂
  have S := (isSplitting_of_isEquivPair H).map_anti hflipAddKL hflip_mul
  simp only [hflipAddKL_apply] at S
  have key := K0.of_ofIdempotent_eq_sum_of_isSplitting (dg := fun _ : Unit => (0 : ℤ)) S
    (fun _ => KL1.hflip_mem_grade (by simpa using hb)) (fun _ => KL1.hflip_mem_grade (by simpa))
    (isIdempotentElem_hflip_divIdem (isBlocks_ofList _ h₁))
    (fun _ => isIdempotentElem_hflip_divIdem (isBlocks_ofList _ h₂))
    (KL1.hflip_mem_grade (divIdemOf_mem_grade _ _ h₁))
    (fun _ => KL1.hflip_mem_grade (divIdemOf_mem_grade _ _ h₂))
  rw [Fintype.sum_unique, neg_zero, T_zero, one_smul] at key
  have e : divAngle (d' ++ [(i, 1), (j, 1)] ++ d'') = divAngle (d' ++ [(j, 1), (i, 1)] ++ d'') := by
    simp [divAngle_append, divAngle]
  rw [projDiv, projDiv, ← K0.T_smul_of, ← K0.T_smul_of, e]
  exact congrArg _ key

end Proj

end Categorification.KLR

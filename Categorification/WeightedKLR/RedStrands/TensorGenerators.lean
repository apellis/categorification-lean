/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorAction
import Categorification.KLR.CyclotomicIntegralLattice
import LieLean.Algebra.QuantumGroup.Modified.TensorVermaIntegral

/-!
# Divided words in the tensor product of highest-weight lattices

Webster, arXiv:1309.3796v2, §4.7, before Lemma 4.36 and in the proof of
Theorem 4.38. Adjoining a red strand tensors with its highest vector.
Adjoining a black divided block acts by the divided lowering operator
on the prefix already present. The last-factor term in the coproduct has
coefficient one and the other terms lower the last factor fewer times.
-/

noncomputable section
namespace Categorification.Stendhal.FirstWeight

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop
open KLR.CycKLR LusztigF
open scoped TensorProduct

local notation "𝕍" => (RatFunc.X : RatFunc ℚ)
local notation "𝕂" => RatFunc ℚ
local notation "LP" => LaurentPolynomial ℤ
local instance : NeZero 𝕍 := ⟨RatFunc.X_ne_zero⟩

variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y]
    {D : LusztigCartanDatum I} {R : D.RootDatum Y} {ℓ : ℕ}

private abbrev HW (wt : Dom R) := IrreducibleModule R 𝕍 wt.1
local notation "divF" => fun (i : I) (n : ℕ) => qDivPow (𝕍 ^ D.d i) n (F R 𝕍 i)

/-- A red/black word with `n` ordered red strands. A black letter records
its colour and divided-power multiplicity. -/
inductive TensorWord (I : Type*) : ℕ → Type _
  | empty : TensorWord I 0
  | red {n} : TensorWord I n → TensorWord I (n + 1)
  | black {n} : TensorWord I n → I → ℕ → TensorWord I n

/-- The divided-power counterpart of Webster's recursively defined vectors
preceding Lemma 4.36. -/
def tensorWordVector : {n : ℕ} → TensorWord I n → (wt : Fin n → Dom R) → TensorSpace wt
  | _, .empty, wt => PiTensorProduct.tprod 𝕂 (fun j => IrreducibleModule.hwv R 𝕍 (wt j).1)
  | _, .red w, wt => appendTensor wt (tensorWordVector w (fun j => wt (Fin.castSucc j)))
      (IrreducibleModule.hwv R 𝕍 (wt (Fin.last _)).1)
  | _, .black w i a, wt => tensorRepresentation wt (divF i a) (tensorWordVector w wt)

private abbrev wordSpan (wt : Fin ℓ → Dom R) : Submodule LP (TensorSpace wt) :=
  Submodule.span LP (Set.range fun w : TensorWord I ℓ => tensorWordVector w wt)

omit [Finite I] in
private theorem wordSpan_stable (wt : Fin ℓ → Dom R) (i : I) (n : ℕ)
    {x : TensorSpace wt} (hx : x ∈ wordSpan wt) :
    tensorRepresentation wt (divF i n) x ∈ wordSpan wt := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    exact Submodule.subset_span ⟨w.black i n, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx =>
    rw [tensor_laurent_smul, map_smul, ← tensor_laurent_smul]
    exact Submodule.smul_mem _ a hx

variable (wt : Fin (ℓ + 1) → Dom R)
local notation "wt₀" => fun j : Fin ℓ => wt (Fin.castSucc j)
local notation "λ₁" => wt (Fin.last ℓ)
local notation "V₀" => TensorSpace wt₀
local notation "V₁" => HW λ₁

omit [Finite I] in
private theorem append_pure (x : ∀ j : Fin ℓ, HW (wt j.castSucc)) (y : V₁) :
    appendTensor wt (PiTensorProduct.tprod 𝕂 x) y =
      PiTensorProduct.tprod 𝕂 (Fin.lastCases y x) := by
  apply (tensorSplitLast wt).injective
  rw [appendTensor, LinearEquiv.apply_symm_apply, tensorSplitLast_tprod]
  simp

private theorem append_mem_integralTensor {x : V₀} (hx : x ∈ integralTensor wt₀)
    {y : V₁} (hy : y ∈ hwIntegral λ₁) : appendTensor wt x y ∈ integralTensor wt := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨f, hf, rfl⟩ := hz
    rw [append_pure]
    apply Submodule.subset_span
    refine ⟨Fin.lastCases y f, ?_, rfl⟩
    intro j
    induction j using Fin.lastCases with
    | last => simpa using hy
    | cast j => simpa using hf j
  | zero => simp [appendTensor]
  | add a b _ _ ha hb => simpa [appendTensor, TensorProduct.add_tmul] using add_mem ha hb
  | smul c a _ ha =>
    rw [appendTensor, tensor_laurent_smul, ← TensorProduct.smul_tmul', map_smul, ← tensor_laurent_smul]
    exact (integralTensor wt).smul_mem c ha

private theorem maps_integralTensor_of_words (f : Module.End 𝕂 (TensorSpace wt))
    (S : Submodule LP (TensorSpace wt))
    (h : ∀ x ∈ integralTensor wt₀, ∀ d : List (I × ℕ),
      f (appendTensor wt x (dividedLoweringWord λ₁ d)) ∈ S)
    {z : TensorSpace wt} (hz : z ∈ integralTensor wt) : f z ∈ S := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, ha, rfl⟩ := hz
    let x := PiTensorProduct.tprod 𝕂 (fun j : Fin ℓ => a j.castSucc)
    have hx : x ∈ integralTensor wt₀ := Submodule.subset_span ⟨_, fun j => ha j.castSucc, rfl⟩
    have he : PiTensorProduct.tprod 𝕂 a = appendTensor wt x (a (Fin.last ℓ)) := by
      apply (tensorSplitLast wt).injective
      rw [tensorSplitLast_tprod, appendTensor, LinearEquiv.apply_symm_apply]
    rw [he]
    have hy := ha (Fin.last ℓ)
    rw [← span_dividedLoweringWord] at hy
    generalize a (Fin.last ℓ) = y at hy ⊢
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨d, rfl⟩ := hy; exact h x hx d
    | zero => simp [appendTensor, S.zero_mem]
    | add a b _ _ ha hb => simpa [appendTensor, TensorProduct.tmul_add] using S.add_mem ha hb
    | smul c a _ ha =>
      simpa [appendTensor, hw_laurent_smul_eq, TensorProduct.tmul_smul, tensor_laurent_smul] using
        S.smul_mem c ha
  | zero => simp [S.zero_mem]
  | add a b _ _ ha hb => rw [map_add]; exact S.add_mem ha hb
  | smul c a _ ha => rw [tensor_laurent_smul, map_smul, ← tensor_laurent_smul]; exact S.smul_mem c ha

omit [Finite I] in
private theorem word_weight (highest : Dom R) (d : List (I × ℕ)) :
    ∃ μ, dividedLoweringWord highest d ∈ weightSpace R 𝕍 (HW highest) μ := by
  induction d using List.reverseRecOn with
  | nil => exact ⟨highest.1, IrreducibleModule.hwv_mem_weightSpace⟩
  | append_singleton d a ih =>
    obtain ⟨μ, hμ⟩ := ih
    obtain ⟨i,n⟩ := a
    refine ⟨μ - n • R.root i, ?_⟩
    rw [show dividedLoweringWord highest (d ++ [(i,n)]) = divF i n • dividedLoweringWord highest d by
      simp [dividedLoweringWord, List.foldl_append]]
    exact qDivPow_F_smul_mem_weightSpace hμ i n

private theorem dividedWord_mem (highest : Dom R) (d : List (I × ℕ)) :
    dividedLoweringWord highest d ∈ hwIntegral highest := by
  rw [← span_dividedLoweringWord]
  exact Submodule.subset_span (Set.mem_range_self d)

private theorem integralTensor_dividedF : ∀ {n : ℕ} (wt : Fin n → Dom R)
    (i : I) (a : ℕ) (z : TensorSpace wt), z ∈ integralTensor wt →
      tensorRepresentation wt (divF i a) z ∈ integralTensor wt
  | 0, wt, i, 0, z, hz => by simpa only [qDivPow_zero', map_one, Module.End.one_apply] using hz
  | 0, wt, i, a+1, z, _ => by
    have he : tensorRepresentation wt (divF i (a+1)) = 0 := by
      change (Algebra.ofId 𝕂 _) (counit R 𝕍 (divF i (a+1))) = 0
      simp [qDivPow]
    rw [he, LinearMap.zero_apply]
    exact zero_mem _
  | n+1, wt, i, a, z, hz => by
    refine maps_integralTensor_of_words wt _ _ (fun x hx d => ?_) hz
    obtain ⟨μ,hμ⟩ := word_weight (wt (Fin.last n)) d
    rw [tensorRepresentation_dividedF_append _ _ _ _ _ hμ]
    exact Submodule.sum_mem _ (fun p _ => Submodule.smul_mem _ _ (append_mem_integralTensor _
      (integralTensor_dividedF _ _ _ _ hx)
      (dF_smul_mem_hwIntegral _ i _ (dividedWord_mem _ d))))

private theorem tensorWord_mem : ∀ {n : ℕ} (w : TensorWord I n) (wt : Fin n → Dom R),
    tensorWordVector w wt ∈ integralTensor wt
  | _, .empty, wt => Submodule.subset_span ⟨_, fun j => hwv_mem_hwIntegral (wt j), rfl⟩
  | _, .red w, wt => append_mem_integralTensor wt (tensorWord_mem w _) (hwv_mem_hwIntegral _)
  | _, .black w i a, wt => integralTensor_dividedF _ i a _ (tensorWord_mem w wt)

omit [Finite I] in
private theorem append_highest_mem_wordSpan {x : V₀} (hx : x ∈ wordSpan wt₀) :
    appendTensor wt x (IrreducibleModule.hwv R 𝕍 λ₁.1) ∈ wordSpan wt := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨w,rfl⟩ := hz
    exact Submodule.subset_span ⟨w.red, rfl⟩
  | zero => simp [appendTensor]
  | add a b _ _ ha hb => simpa [appendTensor, TensorProduct.add_tmul] using add_mem ha hb
  | smul c a _ ha =>
    rw [appendTensor, tensor_laurent_smul, ← TensorProduct.smul_tmul', map_smul, ← tensor_laurent_smul]
    exact (wordSpan wt).smul_mem c ha

omit [Finite I] in
private theorem append_word_mem_wordSpan (d : List (I × ℕ)) :
    ∀ x ∈ wordSpan wt₀, appendTensor wt x (dividedLoweringWord λ₁ d) ∈ wordSpan wt := by
  induction d using List.reverseRecOn with
  | nil => exact fun _ hx => append_highest_mem_wordSpan wt hx
  | append_singleton d a ih =>
    obtain ⟨i,n⟩ := a
    let y := dividedLoweringWord λ₁ d
    obtain ⟨μ,hμ⟩ := word_weight λ₁ d
    rw [show dividedLoweringWord λ₁ (d ++ [(i,n)]) = divF i n • y by
      simp [dividedLoweringWord, y, List.foldl_append]]
    induction n using Nat.strong_induction_on with
    | h n hn =>
      intro x hx
      let term (p : ℕ × ℕ) := dividedCoefficient (R := R) μ i p.1 p.2 •
        appendTensor wt (tensorRepresentation wt₀ (divF i p.2) x) (divF i p.1 • y)
      have hall : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, term p ∈ wordSpan wt := by
        rw [← tensorRepresentation_dividedF_append wt i n x y hμ]
        exact wordSpan_stable _ _ _ (ih x hx)
      have hm : (n,0) ∈ Finset.HasAntidiagonal.antidiagonal n := by simp
      rw [← Finset.sum_erase_add _ _ hm] at hall
      have hlow : ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n).erase (n,0), term p ∈ wordSpan wt := by
        apply Submodule.sum_mem
        rintro ⟨r,s⟩ hrs
        obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hrs
        have hsum : r + s = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hm
        have hr : r < n := by
          by_contra! h
          exact hne (Prod.ext (by simpa using (show r = n by omega)) (by simpa using (show s = 0 by omega)))
        exact (wordSpan wt).smul_mem _ (hn r hr _ (wordSpan_stable _ _ _ hx))
      have htop : term (n,0) ∈ wordSpan wt := by
        simpa only [add_sub_cancel_left] using (wordSpan wt).sub_mem hall hlow
      simpa only [term, dividedCoefficient_zero_right, one_smul, qDivPow_zero', map_one,
        Module.End.one_apply] using htop

/-- The ordered red insertions and divided black blocks generate the whole
integral tensor product, including zero red weights and the empty tuple
(Webster, §4.7, proof of Theorem 4.38). -/
theorem span_tensorWordVector : ∀ {n : ℕ} (wt : Fin n → Dom R),
    Submodule.span LP (Set.range (fun w : TensorWord I n => tensorWordVector w wt)) =
      integralTensor wt
  | 0, wt => by
    apply le_antisymm (Submodule.span_le.mpr ?_)
    · apply Submodule.span_le.mpr
      rintro z ⟨a, _, rfl⟩
      have he : a = fun j => IrreducibleModule.hwv R 𝕍 (wt j).1 := funext (fun j => j.elim0)
      rw [he]
      exact Submodule.subset_span ⟨.empty, rfl⟩
    · rintro z ⟨w,rfl⟩
      exact tensorWord_mem w wt
  | n+1, wt => by
    apply le_antisymm (Submodule.span_le.mpr ?_)
    · intro z hz
      exact maps_integralTensor_of_words wt LinearMap.id (wordSpan wt)
        (fun x hx d => append_word_mem_wordSpan wt d x (by
          change x ∈ Submodule.span LP _
          rw [span_tensorWordVector (fun j : Fin n => wt j.castSucc)]
          exact hx)) hz
    · rintro z ⟨w,rfl⟩
      exact tensorWord_mem w wt

end Categorification.Stendhal.FirstWeight

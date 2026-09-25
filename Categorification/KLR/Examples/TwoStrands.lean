/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Examples.Small

/-!
# `R(i + j)` as a ring of `2 × 2` matrices

M. Khovanov, A. Lauda, *A diagrammatic approach to categorification of quantum groups I*,
arXiv:0803.4121v2, §2.2 ("Examples"), items 4) and 7).

For `i ≠ j`, `Seq(i + j) = {ij, ji}` and `R(i + j)` embeds in `2 × 2` matrices over
`k[x_1, x_2]`: rows and columns are indexed by `ij` (index `0`) and `ji` (index `1`), the
variable `x_1` records the strand labelled `i` and `x_2` the strand labelled `j`, and

* `1_{ij} ↦ E_{00}`, `1_{ji} ↦ E_{11}`;
* the dot on the `a`-th strand of `1_{ij}` goes to `x_a E_{00}`, and of `1_{ji}` to
  `x_{3-a} E_{11}`;
* the crossing with bottom `ij` goes to `A E_{10}`, and with bottom `ji` to `B E_{01}`,

where `A B = Q_{ij}(x_1, x_2) = Q_{ji}(x_2, x_1)`. The image is the subalgebra of matrices
whose bottom-left entry is divisible by `A` and top-right entry by `B`.

## Main results

* `TwoStrand.equiv` : for general data `Q` over an integral domain, and `A, B ≠ 0` with
  `Q_{ij}(x_1, x_2) = A B = Q_{ji}(x_2, x_1)`, `R(i + j) ≅ {M | A ∣ M₁₀, B ∣ M₀₁}`.
* `TwoStrand.KL1.nonAdjEquiv` : **KL I §2.2, Example 4** (`i · j = 0`): `R(i + j)` is
  isomorphic to the ring of `2 × 2` matrices over `k[x_1, x_2]` (the paper: over `ℤ`).
* `TwoStrand.KL1.adjEquiv` : **KL I §2.2, Example 7** (`i · j = -1`): `R(i + j)` is isomorphic
  to the ring of `2 × 2` matrices over `k[x_1, x_2]` whose bottom-left entry is divisible by
  `x_1 + x_2`.

The images of the generators are recorded in `toMat_e`, `toMat_x`, `toMat_ψ` and, in the
form displayed in the paper, `toMat_x_mul_e_sij`, `toMat_ψ_mul_e_sij`, `toMat_ψ_mul_e_sji`.

Injectivity uses only the spanning half of KL I, Theorem 2.5 (each corner `_sR_t` is
`ψ_{w} k[x_1, x_2] 1_t` for the unique `w` with `w t = s`), together with the fact that
`A`, `B` are non-zero-divisors.
-/

namespace Categorification.KLR

open MvPolynomial Equiv TypeA KLRAlgebra

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]

namespace TwoStrand

/-! ### The two sequences -/

section seq

variable (i j : I)

/-- The sequence `ij ∈ Seq(i + j)`. -/
def sij : Seq ({i, j} : Multiset I) := ⟨![i, j], by rw [Fin.univ_val_map]; rfl⟩

/-- The sequence `ji ∈ Seq(i + j)`. -/
def sji : Seq ({i, j} : Multiset I) :=
  ⟨![j, i], by rw [Fin.univ_val_map]; exact Multiset.pair_comm j i⟩

variable {i j}

omit [DecidableEq I] in
theorem seq_cases (t : Seq ({i, j} : Multiset I)) : t = sij i j ∨ t = sji i j := by
  obtain ⟨t, ht⟩ := t
  change Fin 2 → I at t
  rw [Fin.univ_val_map] at ht
  change t 0 ::ₘ t 1 ::ₘ 0 = i ::ₘ j ::ₘ 0 at ht
  rcases Multiset.cons_eq_cons.1 ht with ⟨h0, h1⟩ | ⟨_, cs, h1, h2⟩
  · left
    have h1' : t 1 = j := Multiset.singleton_inj.1 h1
    apply Subtype.ext; funext a; fin_cases a
    · exact h0
    · exact h1'
  · right
    have hc : cs = 0 := by
      have := congrArg Multiset.card h1
      simp only [Multiset.card_cons, Multiset.card_zero] at this
      exact Multiset.card_eq_zero.1 (by omega)
    subst hc
    have h1' : t 1 = i := Multiset.singleton_inj.1 h1
    have h0' : j = t 0 := Multiset.singleton_inj.1 h2
    apply Subtype.ext; funext a; fin_cases a
    · exact h0'.symm
    · exact h1'

omit [DecidableEq I] in
theorem sij_ne_sji (hij : i ≠ j) : sij i j ≠ sji i j := fun h =>
  hij (by simpa [sij, sji] using congrFun (congrArg Subtype.val h) (0 : Fin 2))

omit [DecidableEq I] in
theorem sadj_smul_sij : sadj (Multiset.card ({i, j} : Multiset I)) 0 • sij i j = sji i j := by
  apply Subtype.ext; funext a; change Fin 2 at a
  fin_cases a <;> simp [sadj, sij, sji, Seq.smul_apply, swap_apply_def]

omit [DecidableEq I] in
theorem sadj_smul_sji : sadj (Multiset.card ({i, j} : Multiset I)) 0 • sji i j = sij i j := by
  apply Subtype.ext; funext a; change Fin 2 at a
  fin_cases a <;> simp [sadj, sij, sji, Seq.smul_apply, swap_apply_def]

theorem sum_seq {M : Type*} [AddCommMonoid M] (hij : i ≠ j) (f : Seq ({i, j} : Multiset I) → M) :
    ∑ t, f t = f (sij i j) + f (sji i j) := by
  have : (Finset.univ : Finset (Seq ({i, j} : Multiset I))) = {sij i j, sji i j} := by
    ext t
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact seq_cases t
  rw [this, Finset.sum_pair (sij_ne_sji hij)]

end seq

/-! ### The matrices -/

/-- `2 × 2` matrices over `k[x_1, x_2]`. -/
abbrev Mat (k : Type*) [CommRing k] : Type _ := Matrix (Fin 2) (Fin 2) (MvPolynomial (Fin 2) k)

omit [DecidableEq I] in
theorem mat_eq {M N : Mat k} (h₀₀ : M 0 0 = N 0 0) (h₀₁ : M 0 1 = N 0 1) (h₁₀ : M 1 0 = N 1 0)
    (h₁₁ : M 1 1 = N 1 1) : M = N := by
  refine Matrix.ext fun a b => ?_
  fin_cases a <;> fin_cases b
  exacts [h₀₀, h₀₁, h₁₀, h₁₁]

section map

variable (i j : I) (A B : MvPolynomial (Fin 2) k)

/-- Image of the idempotent `1_t`. -/
noncomputable def eMat (t : Seq ({i, j} : Multiset I)) : Mat k :=
  if t = sij i j then !![1, 0; 0, 0] else !![0, 0; 0, 1]

/-- Image of the dot on the strand at position `a` (`a = 0, 1`). -/
noncomputable def xMat (a : ℕ) : Mat k :=
  if a = 0 then !![X 0, 0; 0, X 1] else !![X 1, 0; 0, X 0]

/-- Image of the crossing `ψ_l` (zero unless `l = 0`). -/
noncomputable def ψMat (l : ℕ) : Mat k := if l = 0 then !![0, B; A, 0] else 0

/-- The values of the generators. -/
noncomputable def genMat : Gen ({i, j} : Multiset I) → Mat k
  | .idem t => eMat i j t
  | .dot a => xMat a.val
  | .cross l => ψMat A B l

omit [DecidableEq I] in
theorem rename_rename_swap (p : MvPolynomial (Fin 2) k) :
    rename ![1, 0] (rename ![1, 0] p) = p := by
  rw [rename_rename]
  have : (![1, 0] ∘ ![1, 0] : Fin 2 → Fin 2) = id := by
    funext a; fin_cases a <;> rfl
  rw [this, rename_id_apply]

omit [DecidableEq I] in
theorem rename_swap_injective :
    Function.Injective (rename ![1, 0] : MvPolynomial (Fin 2) k → MvPolynomial (Fin 2) k) :=
  Function.LeftInverse.injective rename_rename_swap

omit [DecidableEq I] in
/-- Evaluating a polynomial at the images of the two dots. -/
theorem ncEval_xMat (p : MvPolynomial (Fin 2) k) :
    ncEval ![xMat (k := k) 0, xMat 1] p = !![p, 0; 0, rename ![1, 0] p] := by
  let d : Fin 2 → (Fin 2 → MvPolynomial (Fin 2) k) := fun a => ![X a, X (![1, 0] a)]
  have hd : ![xMat (k := k) 0, xMat 1] = fun a => Matrix.diagonalAlgHom k (d a) := by
    funext a
    fin_cases a <;>
      (ext b c; fin_cases b <;> fin_cases c <;> simp [xMat, d, Matrix.diagonal])
  rw [hd, ← PolyRep.algHom_ncEval, ncEval_eq_aeval]
  have hc : ∀ c : Fin 2, (aeval d p) c = aeval (fun a => d a c) p := by
    intro c
    show Pi.evalAlgHom k (fun _ => MvPolynomial (Fin 2) k) c (aeval d p) = _
    rw [← AlgHom.comp_apply, comp_aeval]
    rfl
  have h0 : aeval (fun a => d a 0) p = p := by
    have : (fun a => d a 0) = X := by funext a; rfl
    rw [this, aeval_X_left_apply]
  have h1 : aeval (fun a => d a 1) p = rename ![1, 0] p := by
    have : (fun a => d a 1) = X ∘ ![1, 0] := by funext a; rfl
    rw [this]; rfl
  have hv : aeval d p = ![p, rename ![1, 0] p] := by
    funext c; rw [hc]; fin_cases c
    exacts [h0, h1]
  rw [hv]
  apply mat_eq <;> simp [Matrix.diagonal]

end map

section hom

variable {i j : I} (hij : i ≠ j) (A B : MvPolynomial (Fin 2) k)
  {Q : I → I → MvPolynomial (Fin 2) k}
  (hQ₁ : Q i j = A * B) (hQ₂ : rename ![1, 0] (Q j i) = A * B)

omit [DecidableEq I] in
theorem xMat_comm (a b : ℕ) : xMat (k := k) a * xMat b = xMat b * xMat a := by
  unfold xMat
  split_ifs <;> apply mat_eq <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem xMat_mul_eMat (a : ℕ) (t : Seq ({i, j} : Multiset I)) :
    xMat (k := k) a * eMat i j t = eMat i j t * xMat a := by
  unfold xMat eMat
  split_ifs <;> apply mat_eq <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

include hij in
theorem eMat_mul_eMat (s t : Seq ({i, j} : Multiset I)) :
    eMat (k := k) i j s * eMat i j t = if s = t then eMat i j s else 0 := by
  have hne := sij_ne_sji hij
  rcases seq_cases s with rfl | rfl <;> rcases seq_cases t with rfl | rfl <;>
    apply mat_eq <;> simp [eMat, hne, hne.symm, Matrix.mul_apply, Fin.sum_univ_two]

include hij in
theorem ψMat_mul_eMat (t : Seq ({i, j} : Multiset I)) :
    ψMat A B 0 * eMat (k := k) i j t =
      eMat i j (sadj (Multiset.card ({i, j} : Multiset I)) 0 • t) * ψMat A B 0 := by
  have hne := sij_ne_sji hij
  rcases seq_cases t with rfl | rfl
  · rw [sadj_smul_sij]
    apply mat_eq <;> simp [eMat, ψMat, hne.symm, Matrix.mul_apply, Fin.sum_univ_two]
  · rw [sadj_smul_sji]
    apply mat_eq <;> simp [eMat, ψMat, hne.symm, Matrix.mul_apply, Fin.sum_univ_two]

omit [DecidableEq I] in
theorem xMat_ψMat_sub : xMat (k := k) 0 * ψMat A B 0 - ψMat A B 0 * xMat 1 = 0 := by
  apply mat_eq <;> simp [xMat, ψMat, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

omit [DecidableEq I] in
theorem ψMat_xMat_sub : ψMat A B 0 * xMat (k := k) 0 - xMat 1 * ψMat A B 0 = 0 := by
  apply mat_eq <;> simp [xMat, ψMat, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

include hij hQ₁ hQ₂ in
theorem genMat_rel ⦃a b : FreeAlgebra k (Gen ({i, j} : Multiset I))⦄
    (h : Rel k Q ({i, j} : Multiset I) a b) :
    FreeAlgebra.lift k (genMat i j A B) a = FreeAlgebra.lift k (genMat i j A B) b := by
  have hne := sij_ne_sji hij
  have hlbl : ∀ t : Seq ({i, j} : Multiset I),
      t.lbl ⟨0, Nat.zero_lt_two⟩ ≠ t.lbl ⟨1, Nat.one_lt_two⟩ := by
    intro t
    rcases seq_cases t with rfl | rfl
    · exact hij
    · exact Ne.symm hij
  cases h with
  | idem_mul s t =>
    simp only [fe, map_mul, FreeAlgebra.lift_ι_apply, genMat]
    rw [eMat_mul_eMat hij]
    split_ifs <;> simp [genMat]
  | idem_sum =>
    simp only [fe, map_sum, FreeAlgebra.lift_ι_apply, genMat, map_one]
    rw [sum_seq hij]
    apply mat_eq <;> simp [eMat, hne.symm]
  | dot_idem a t =>
    simp only [fe, fx, map_mul, FreeAlgebra.lift_ι_apply, genMat]
    exact xMat_mul_eMat _ _
  | cross_idem l t =>
    simp only [fe, fψ, map_mul, FreeAlgebra.lift_ι_apply, genMat]
    by_cases hl : l = 0
    · subst hl; exact ψMat_mul_eMat hij A B t
    · simp [ψMat, hl]
  | cross_zero l h =>
    simp only [fψ, FreeAlgebra.lift_ι_apply, genMat, map_zero]
    change 2 ≤ l + 1 at h
    simp [ψMat, show l ≠ 0 by omega]
  | dot_dot a b =>
    simp only [fx, map_mul, FreeAlgebra.lift_ι_apply, genMat]
    exact xMat_comm _ _
  | cross_cross l l' h =>
    simp only [fψ, map_mul, FreeAlgebra.lift_ι_apply, genMat]
    simp [ψMat, show l' ≠ 0 by omega]
  | dot_cross a l h₁ h₂ =>
    simp only [fx, fψ, map_mul, FreeAlgebra.lift_ι_apply, genMat]
    have : l ≠ 0 := by
      rintro rfl
      have := a.isLt; change a.val < 2 at this; omega
    simp [ψMat, this]
  | dot_cross_left l h t =>
    change l + 1 < 2 at h
    obtain rfl : l = 0 := by omega
    rw [if_neg (hlbl t), map_zero]
    simp only [fe, fx, fψ, map_mul, map_sub, FreeAlgebra.lift_ι_apply, genMat]
    rw [xMat_ψMat_sub, zero_mul]
  | dot_cross_right l h t =>
    change l + 1 < 2 at h
    obtain rfl : l = 0 := by omega
    rw [if_neg (hlbl t), map_zero]
    simp only [fe, fx, fψ, map_mul, map_sub, FreeAlgebra.lift_ι_apply, genMat]
    rw [ψMat_xMat_sub, zero_mul]
  | cross_sq l h t =>
    change l + 1 < 2 at h
    obtain rfl : l = 0 := by omega
    rw [if_neg (hlbl t)]
    simp only [fe, fψ, map_mul, FreeAlgebra.lift_ι_apply, genMat, PolyRep.algHom_ncEval]
    have hv : (fun c => FreeAlgebra.lift k (genMat i j A B)
        (![fx k ({i, j} : Multiset I) ⟨0, Nat.zero_lt_two⟩, fx k _ ⟨1, h⟩] c)) =
        ![xMat (k := k) 0, xMat 1] := by
      funext c; fin_cases c <;> simp [fx, genMat]
    rw [hv, ncEval_xMat]
    rcases seq_cases t with rfl | rfl
    · rw [show (sij i j).lbl ⟨0, Nat.zero_lt_two⟩ = i from rfl,
        show (sij i j).lbl ⟨0 + 1, h⟩ = j from rfl, hQ₁]
      apply mat_eq <;> simp [eMat, ψMat, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
    · rw [show (sji i j).lbl ⟨0, Nat.zero_lt_two⟩ = j from rfl,
        show (sji i j).lbl ⟨0 + 1, h⟩ = i from rfl, hQ₂]
      apply mat_eq <;> simp [eMat, ψMat, hne.symm, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
  | braid l h t =>
    change l + 2 < 2 at h
    omega

variable (Q) in
/-- The map `R(i + j) → Mat₂(k[x_1, x_2])`. -/
noncomputable def toMat : KLRAlgebra k Q ({i, j} : Multiset I) →ₐ[k] Mat k :=
  RingQuot.liftAlgHom k ⟨FreeAlgebra.lift k (genMat i j A B), fun _ _ h =>
    genMat_rel hij A B hQ₁ hQ₂ h⟩

theorem toMat_mk (a : FreeAlgebra k (Gen ({i, j} : Multiset I))) :
    toMat hij A B Q hQ₁ hQ₂ (mk k Q _ a) = FreeAlgebra.lift k (genMat i j A B) a :=
  RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _

@[simp] theorem toMat_e (t : Seq ({i, j} : Multiset I)) :
    toMat hij A B Q hQ₁ hQ₂ (e t) = eMat i j t := by
  rw [e, toMat_mk, FreeAlgebra.lift_ι_apply]; rfl

@[simp] theorem toMat_x (a : Fin (Multiset.card ({i, j} : Multiset I))) :
    toMat hij A B Q hQ₁ hQ₂ (x a) = xMat a.val := by
  rw [x, toMat_mk, FreeAlgebra.lift_ι_apply]; rfl

@[simp] theorem toMat_ψ (l : ℕ) :
    toMat hij A B Q hQ₁ hQ₂ (ψ l) = ψMat A B l := by
  rw [ψ, toMat_mk, FreeAlgebra.lift_ι_apply]; rfl

theorem toMat_pol (p : MvPolynomial (Fin 2) k) :
    toMat hij A B Q hQ₁ hQ₂ (pol p) = !![p, 0; 0, rename ![1, 0] p] := by
  have := ncEval_eq_pol (k := k) (Q := Q) (ν := ({i, j} : Multiset I)) id p
  rw [rename_id_apply] at this
  rw [← this, PolyRep.algHom_ncEval, ← ncEval_xMat]
  congr 1
  funext a; fin_cases a <;> exact toMat_x hij A B hQ₁ hQ₂ _

theorem toMat_pol_e_sij (p : MvPolynomial (Fin 2) k) :
    toMat hij A B Q hQ₁ hQ₂ (pol p * e (sij i j)) = !![p, 0; 0, 0] := by
  rw [map_mul, toMat_pol, toMat_e]
  simp [eMat, Matrix.mul_fin_two]

theorem toMat_pol_e_sji (p : MvPolynomial (Fin 2) k) :
    toMat hij A B Q hQ₁ hQ₂ (pol p * e (sji i j)) = !![0, 0; 0, rename ![1, 0] p] := by
  rw [map_mul, toMat_pol, toMat_e]
  simp [eMat, (sij_ne_sji hij).symm, Matrix.mul_fin_two]

theorem toMat_ψ_pol_e_sij (p : MvPolynomial (Fin 2) k) :
    toMat hij A B Q hQ₁ hQ₂ (ψ 0 * pol p * e (sij i j)) = !![0, 0; A * p, 0] := by
  rw [map_mul, map_mul, toMat_pol, toMat_e, toMat_ψ]
  simp [eMat, ψMat, Matrix.mul_fin_two]

theorem toMat_ψ_pol_e_sji (p : MvPolynomial (Fin 2) k) :
    toMat hij A B Q hQ₁ hQ₂ (ψ 0 * pol p * e (sji i j)) =
      !![0, B * rename ![1, 0] p; 0, 0] := by
  rw [map_mul, map_mul, toMat_pol, toMat_e, toMat_ψ]
  simp [eMat, ψMat, (sij_ne_sji hij).symm, Matrix.mul_fin_two]

/-- KL I §2.2, Examples 4 and 7: the dots on `1_{ij}` go to `x_1 E_{00}` and `x_2 E_{00}`. -/
theorem toMat_x_mul_e_sij (a : Fin 2) :
    toMat hij A B Q hQ₁ hQ₂ (x (ν := ({i, j} : Multiset I)) a * e (sij i j)) =
      !![X a, 0; 0, 0] := by
  have := toMat_pol_e_sij hij A B hQ₁ hQ₂ (X a)
  rwa [pol_X] at this

/-- KL I §2.2, Examples 4 and 7: the crossing with bottom `ij` goes to `A E_{10}`. -/
theorem toMat_ψ_mul_e_sij : toMat hij A B Q hQ₁ hQ₂ (ψ 0 * e (sij i j)) = !![0, 0; A, 0] := by
  have := toMat_ψ_pol_e_sij hij A B hQ₁ hQ₂ 1
  rwa [map_one, mul_one, mul_one] at this

/-- KL I §2.2, Examples 4 and 7: the crossing with bottom `ji` goes to `B E_{01}`. -/
theorem toMat_ψ_mul_e_sji : toMat hij A B Q hQ₁ hQ₂ (ψ 0 * e (sji i j)) = !![0, B; 0, 0] := by
  have := toMat_ψ_pol_e_sji hij A B hQ₁ hQ₂ 1
  rwa [map_one, mul_one, map_one, mul_one] at this

end hom

/-! ### The image -/

variable (A B : MvPolynomial (Fin 2) k)

/-- The subalgebra of `2 × 2` matrices over `k[x_1, x_2]` whose bottom-left entry is divisible
by `A` and whose top-right entry is divisible by `B`. -/
def sub : Subalgebra k (Mat k) where
  carrier := {M | A ∣ M 1 0 ∧ B ∣ M 0 1}
  mul_mem' := by
    rintro M N ⟨h₁, h₂⟩ ⟨h₃, h₄⟩
    simp only [Set.mem_setOf_eq, Matrix.mul_apply, Fin.sum_univ_two]
    exact ⟨dvd_add (dvd_mul_of_dvd_left h₁ _) (dvd_mul_of_dvd_right h₃ _),
      dvd_add (dvd_mul_of_dvd_right h₄ _) (dvd_mul_of_dvd_left h₂ _)⟩
  add_mem' := by
    rintro M N ⟨h₁, h₂⟩ ⟨h₃, h₄⟩
    exact ⟨dvd_add h₁ h₃, dvd_add h₂ h₄⟩
  algebraMap_mem' c := by
    simp [Matrix.algebraMap_matrix_apply]

theorem mem_sub {M : Mat k} : M ∈ sub A B ↔ A ∣ M 1 0 ∧ B ∣ M 0 1 := Iff.rfl

section equiv

variable {i j : I} (hij : i ≠ j) {Q : I → I → MvPolynomial (Fin 2) k}
  (hQ₁ : Q i j = A * B) (hQ₂ : rename ![1, 0] (Q j i) = A * B)

theorem toMat_mem (r : KLRAlgebra k Q ({i, j} : Multiset I)) :
    toMat hij A B Q hQ₁ hQ₂ r ∈ sub A B := by
  refine mem_of_gens _ _ (fun t => ?_) (fun a => ?_) (fun l => ?_) r
  · rw [toMat_e, mem_sub]; unfold eMat; split_ifs <;> simp
  · rw [toMat_x, mem_sub]; unfold xMat; split_ifs <;> simp
  · rw [toMat_ψ, mem_sub]; unfold ψMat; split_ifs <;> simp

/-- The words `ρ₂ 1 = []`, `ρ₂ s = [0]` for `S_2`. -/
private def ρ₂ (w : Perm (Fin 2)) : List ℕ := if w = 1 then [] else [0]

private theorem sadj_two : sadj 2 0 = swap 0 1 := by
  rw [sadj, dif_pos (by norm_num)]; rfl

private theorem sadj_two_ne_one : sadj 2 0 ≠ 1 := by rw [sadj_two]; decide

private theorem perm_two (w : Perm (Fin 2)) : w = 1 ∨ w = sadj 2 0 := by
  rw [sadj_two]; revert w; decide

private theorem hρ₂ (w : Perm (Fin 2)) : IsReduced 2 (ρ₂ w) ∧ wordProd 2 (ρ₂ w) = w := by
  rcases perm_two w with rfl | rfl
  · have : ρ₂ 1 = [] := if_pos rfl
    rw [this]
    exact ⟨⟨by simp [ValidWord], by simp [wordProd, length_eq_zero_iff]⟩, rfl⟩
  · have : ρ₂ (sadj 2 0) = [0] := if_neg sadj_two_ne_one
    rw [this, wordProd_singleton]
    refine ⟨⟨by simp [ValidWord], ?_⟩, rfl⟩
    rw [wordProd_singleton, length_sadj (by norm_num)]
    rfl

omit [DecidableEq I] in
include hij in
private theorem sadj_smul_ne (t : Seq ({i, j} : Multiset I)) :
    sadj (Multiset.card ({i, j} : Multiset I)) 0 • t ≠ t := by
  have hne := sij_ne_sji hij
  rcases seq_cases t with rfl | rfl
  · rw [sadj_smul_sij]; exact hne.symm
  · rw [sadj_smul_sji]; exact hne

include hij in
/-- Each corner `e_s R(i + j) e_t` is `c_{st} · k[x_1, x_2] · e_t`, where `c_{st} = 1` if
`s = t` and `ψ_0` otherwise (spanning half of KL I, Theorem 2.5). -/
theorem corner_eq (s t : Seq ({i, j} : Multiset I)) (r : KLRAlgebra k Q ({i, j} : Multiset I)) :
    ∃ p, e s * r * e t = (if s = t then 1 else ψ 0) * pol p * e t := by
  have hr : e s * (e s * r * e t) * e t = e s * r * e t := by
    simp only [← mul_assoc, e_mul_self]; rw [mul_assoc _ (e t), e_mul_self]
  have hmem := mem_span_corner' (Q := Q) (ν := ({i, j} : Multiset I)) ρ₂ hρ₂ t s hr
  set c : KLRAlgebra k Q ({i, j} : Multiset I) := if s = t then 1 else ψ 0
  let L : MvPolynomial (Fin 2) k →ₗ[k] KLRAlgebra k Q ({i, j} : Multiset I) :=
    (LinearMap.mulRight k (e t)).comp ((LinearMap.mulLeft k c).comp
      (pol (k := k) (Q := Q) (ν := ({i, j} : Multiset I))).toLinearMap)
  have hle : Submodule.span k {b : KLRAlgebra k Q ({i, j} : Multiset I) |
      ∃ (w : Perm (Fin (Multiset.card ({i, j} : Multiset I)))) (u : Fin 2 →₀ ℕ),
        w • t = s ∧ ψw (ρ₂ w) * pol (monomial u 1) * e t = b}
      ≤ LinearMap.range L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨w, u, hw, rfl⟩
    refine ⟨monomial u 1, ?_⟩
    simp only [L, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
      LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
    congr 2
    rcases perm_two w with h1 | h1
    · have hw' : w • t = t := by rw [h1, one_smul]
      have hst : s = t := hw.symm.trans hw'
      have : ρ₂ w = [] := if_pos h1
      simp [c, this, hst]
    · have hw' : w • t ≠ t := by
        rw [h1]; exact sadj_smul_ne hij t
      have hst : s ≠ t := hw ▸ hw'
      have : ρ₂ w = [0] := by rw [h1]; exact if_neg sadj_two_ne_one
      simp [c, this, hst, ψw]
  obtain ⟨p, hp⟩ := hle hmem
  exact ⟨p, hp.symm⟩

variable [IsDomain k]

include hij in
theorem toMat_injective (hA : A ≠ 0) (hB : B ≠ 0) :
    Function.Injective (toMat hij A B Q hQ₁ hQ₂) := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  have hne := sij_ne_sji hij
  have key : ∀ s t, e s * r * e t = 0 := by
    intro s t
    obtain ⟨p, hp⟩ := corner_eq hij s t r
    have h0 : toMat hij A B Q hQ₁ hQ₂ (e s * r * e t) = 0 := by
      rw [map_mul, map_mul, hr, mul_zero, zero_mul]
    rw [hp] at h0 ⊢
    suffices p = 0 by rw [this, map_zero, mul_zero, zero_mul]
    rcases seq_cases s with rfl | rfl <;> rcases seq_cases t with rfl | rfl
    · rw [if_pos rfl, one_mul, toMat_pol_e_sij] at h0
      simpa using congrFun (congrFun h0 0) 0
    · rw [if_neg hne, toMat_ψ_pol_e_sji] at h0
      have := congrFun (congrFun h0 0) 1
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.zero_apply,
        mul_eq_zero, hB, false_or] at this
      exact rename_swap_injective (by rw [this, map_zero])
    · rw [if_neg hne.symm, toMat_ψ_pol_e_sij] at h0
      have := congrFun (congrFun h0 1) 0
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.zero_apply,
        mul_eq_zero, hA, false_or] at this
      exact this
    · rw [if_pos rfl, one_mul, toMat_pol_e_sji] at h0
      have := congrFun (congrFun h0 1) 1
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.zero_apply] at this
      exact rename_swap_injective (by rw [this, map_zero])
  have hsum : r = ∑ s, ∑ t, e s * r * e t := by
    simp only [← Finset.mul_sum, ← Finset.sum_mul, sum_e, one_mul, mul_one]
  rw [hsum]
  simp [key]

omit [IsDomain k] in
theorem toMat_surjective (M : Mat k) (hM : M ∈ sub A B) :
    ∃ r, toMat hij A B Q hQ₁ hQ₂ r = M := by
  obtain ⟨⟨q, hq⟩, ⟨q', hq'⟩⟩ := hM
  let P : MvPolynomial (Fin 2) k → KLRAlgebra k Q ({i, j} : Multiset I) := fun p => pol p
  refine ⟨P (M 0 0) * e (sij i j) + P (rename ![1, 0] (M 1 1)) * e (sji i j) +
    ψ 0 * P q * e (sij i j) + ψ 0 * P (rename ![1, 0] q') * e (sji i j), ?_⟩
  rw [map_add, map_add, map_add, toMat_pol_e_sij, toMat_pol_e_sji, toMat_ψ_pol_e_sij,
    toMat_ψ_pol_e_sji, rename_rename_swap, rename_rename_swap]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [hq, hq']

/-- **`R(i + j)` for general data** (`i ≠ j`, `k` an integral domain): if
`Q_{ij}(x_1, x_2) = A B = Q_{ji}(x_2, x_1)` with `A, B ≠ 0`, then `R(i + j)` is isomorphic to
the ring of `2 × 2` matrices over `k[x_1, x_2]` whose bottom-left entry is divisible by `A`
and whose top-right entry is divisible by `B`. -/
noncomputable def equiv (hA : A ≠ 0) (hB : B ≠ 0) :
    KLRAlgebra k Q ({i, j} : Multiset I) ≃ₐ[k] sub A B :=
  AlgEquiv.ofBijective ((toMat hij A B Q hQ₁ hQ₂).codRestrict _ (toMat_mem A B hij hQ₁ hQ₂))
    ⟨fun r s h => toMat_injective A B hij hQ₁ hQ₂ hA hB (congrArg Subtype.val h),
      fun ⟨M, hM⟩ => by
        obtain ⟨r, hr⟩ := toMat_surjective A B hij hQ₁ hQ₂ M hM
        exact ⟨r, Subtype.ext hr⟩⟩

@[simp] theorem coe_equiv (hA : A ≠ 0) (hB : B ≠ 0) (r : KLRAlgebra k Q ({i, j} : Multiset I)) :
    (equiv A B hij hQ₁ hQ₂ hA hB r : Mat k) = toMat hij A B Q hQ₁ hQ₂ r := rfl

end equiv

/-! ### The KL I examples -/

namespace KL1

variable (Γ : SimpleGraph I) [DecidableRel Γ.Adj] [IsDomain k] {i j : I}

omit [IsDomain k] in
theorem sub_one_one : sub (1 : MvPolynomial (Fin 2) k) 1 = ⊤ :=
  eq_top_iff.2 fun _ _ => ⟨one_dvd _, one_dvd _⟩

omit [DecidableEq I] [IsDomain k] in
theorem klQ_nonAdj₁ (hadj : ¬ Γ.Adj i j) : (klQ Γ i j : MvPolynomial (Fin 2) k) = 1 * 1 := by
  simp [klQ, hadj]

omit [DecidableEq I] [IsDomain k] in
theorem klQ_nonAdj₂ (hadj : ¬ Γ.Adj i j) :
    rename (![1, 0] : Fin 2 → Fin 2) (klQ Γ j i : MvPolynomial (Fin 2) k) = 1 * 1 := by
  simp only [klQ]
  rw [if_neg (fun h : Γ.Adj j i => hadj h.symm)]
  simp

omit [DecidableEq I] [IsDomain k] in
theorem klQ_adj₁ (hadj : Γ.Adj i j) :
    (klQ Γ i j : MvPolynomial (Fin 2) k) = (X 0 + X 1) * 1 := by
  simp [klQ, hadj]

omit [DecidableEq I] [IsDomain k] in
theorem klQ_adj₂ (hadj : Γ.Adj i j) :
    rename (![1, 0] : Fin 2 → Fin 2) (klQ Γ j i : MvPolynomial (Fin 2) k) = (X 0 + X 1) * 1 := by
  simp [klQ, hadj.symm, add_comm]

/-- **KL I §2.2, Example 4** (`i · j = 0`, i.e. `i ≠ j` not joined by an edge): `R(i + j)` is
isomorphic to the ring of `2 × 2` matrices with coefficients in `k[x_1, x_2]` (the paper:
`k = ℤ`). The generators go to `1_{ij} ↦ E_{00}`, `1_{ji} ↦ E_{11}`, `ψ 1_{ij} ↦ E_{10}`,
`ψ 1_{ji} ↦ E_{01}`, `x_a 1_{ij} ↦ x_a E_{00}` (see `toMat_x_mul_e_sij`, …). -/
noncomputable def nonAdjEquiv (hij : i ≠ j) (hadj : ¬ Γ.Adj i j) :
    R1 k Γ ({i, j} : Multiset I) ≃ₐ[k] Mat k :=
  (equiv (1 : MvPolynomial (Fin 2) k) 1 hij (klQ_nonAdj₁ Γ hadj)
      (klQ_nonAdj₂ Γ hadj) one_ne_zero one_ne_zero).trans
    ((Subalgebra.equivOfEq _ _ sub_one_one).trans Subalgebra.topEquiv)

theorem nonAdjEquiv_apply (hij : i ≠ j) (hadj : ¬ Γ.Adj i j)
    (r : R1 k Γ ({i, j} : Multiset I)) :
    nonAdjEquiv Γ hij hadj r = toMat hij 1 1 (klQ Γ) (klQ_nonAdj₁ Γ hadj)
      (klQ_nonAdj₂ Γ hadj) r := rfl

omit [IsDomain k] in
theorem X_add_X_ne_zero [Nontrivial k] : (X 0 + X 1 : MvPolynomial (Fin 2) k) ≠ 0 := by
  intro h
  have := congrArg (coeff (Finsupp.single 0 1)) h
  simp [coeff_X', Finsupp.single_eq_single_iff] at this

/-- The subalgebra of `2 × 2` matrices over `k[x_1, x_2]` whose bottom-left entry is divisible by
`x_1 + x_2`. -/
noncomputable abbrev adjSub : Subalgebra k (Mat k) := sub (X 0 + X 1) 1

omit [IsDomain k] in
theorem mem_adjSub {M : Mat k} : M ∈ adjSub ↔ (X 0 + X 1) ∣ M 1 0 :=
  ⟨fun h => h.1, fun h => ⟨h, one_dvd _⟩⟩

/-- **KL I §2.2, Example 7** (`i · j = -1`, i.e. `i`, `j` joined by an edge): `R(i + j)` is
isomorphic to the ring of `2 × 2` matrices with coefficients in `k[x_1, x_2]` whose bottom-left
entry is divisible by `x_1 + x_2` (the paper: `k = ℤ`). The generators go to
`1_{ij} ↦ E_{00}`, `1_{ji} ↦ E_{11}`, `ψ 1_{ij} ↦ (x_1 + x_2) E_{10}`, `ψ 1_{ji} ↦ E_{01}`,
`x_a 1_{ij} ↦ x_a E_{00}` (see `toMat_x_mul_e_sij`, `toMat_ψ_mul_e_sij`, …). -/
noncomputable def adjEquiv (hadj : Γ.Adj i j) :
    R1 k Γ ({i, j} : Multiset I) ≃ₐ[k] adjSub (k := k) :=
  equiv (X 0 + X 1) 1 (Γ.ne_of_adj hadj) (klQ_adj₁ Γ hadj)
    (klQ_adj₂ Γ hadj) X_add_X_ne_zero one_ne_zero

theorem adjEquiv_apply (hadj : Γ.Adj i j) (r : R1 k Γ ({i, j} : Multiset I)) :
    (adjEquiv Γ hadj r : Mat k) = toMat (Γ.ne_of_adj hadj) (X 0 + X 1) 1 (klQ Γ)
      (klQ_adj₁ Γ hadj) (klQ_adj₂ Γ hadj) r := rfl

end KL1

end TwoStrand

end Categorification.KLR

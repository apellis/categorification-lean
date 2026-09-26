/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.DividedPowerK0

/-!
# `1_î` as a sum of `i!` orthogonal idempotents equivalent to `1_i`

M. Khovanov, A. Lauda, *A diagrammatic approach to categorification of quantum groups I*,
arXiv:0803.4121v2, §2.2 Example 3 (TeX lines ~700–712: "The regular representation of `NH_m`
decomposes as the sum of `m!` copies of the polynomial one … `NH_m ≅ P_m^{[m]!}`") and §2.5
(`P_î ≅ P_i^{i!}`).

For a divided-power expression `i = i_1^{(n_1)} ⋯ i_r^{(n_r)}` (a list `d`) with expansion `î`, we
compose the splittings of `Categorification.KLR.NilHeckeBlockSplitting` along all blocks of `i`
(`Graded.IsSplitting.trans`) and obtain (`exists_orthogonal_decomposition_e`) a family of
`n_1! ⋯ n_r!` mutually orthogonal idempotents `g_j` of `R(ν)` with `∑_j g_j = 1_î`, each
equivalent to `1_i` via homogeneous elements `a_j ∈ R(ν)_{d_j}`, `b_j ∈ R(ν)_{-d_j}`
(`a_j b_j = g_j`, `b_j a_j = 1_i`), where the degrees are distributed as the coefficients of
`q^{-⟨i⟩} i!`: `∑_j q^{d_j} = q^{-⟨i⟩} [n_1]! ⋯ [n_r]!`. For `ν = m·i` and `i = i^{(m)}` this is
the decomposition of `1 ∈ R(m i) ≅ NH_m` into `m!` orthogonal idempotents equivalent to `e_m`,
with degrees `q^{-m(m-1)/2} [m]! = ∑_{w ∈ S_m} q^{-2 ℓ(w)}`.
-/

noncomputable section

namespace Categorification

open Graded

/-! ### Composing splittings -/

namespace Graded.IsSplitting

variable {A : Type*} [Ring A]

/-- **Composition of splittings**: if `E'' = ∑_i a_i b_i` splits through `E'` and
`E' = ∑_k a'_k b'_k` splits through `E` (with `E`, `E''` idempotents), then
`E'' = ∑_{(i,k)} (a_i a'_k)(b'_k b_i)` splits through `E`. -/
theorem trans {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {E'' E' E : A} {a b : ι → A} {a' b' : κ → A}
    (h₁ : IsSplitting E'' (fun _ => E') a b) (h₂ : IsSplitting E' (fun _ => E) a' b')
    (hE : IsIdempotentElem E) (hE'' : IsIdempotentElem E'') :
    IsSplitting E'' (fun _ : ι × κ => E) (fun p => a p.1 * a' p.2) (fun p => b' p.2 * b p.1) where
  mul_eq p q := by
    rw [show b' p.2 * b p.1 * (a q.1 * a' q.2) = b' p.2 * (b p.1 * a q.1) * a' q.2 by
      simp only [mul_assoc], h₁.mul_eq]
    by_cases h1 : p.1 = q.1
    · rw [if_pos h1, mul_assoc, h₂.left_mul_a, ← mul_assoc, h₂.mul_eq]
      by_cases h2 : p.2 = q.2
      · rw [if_pos h2, if_pos (Prod.ext h1 h2), hE.eq]
      · rw [if_neg h2, if_neg (fun h => h2 (congrArg Prod.snd h)), zero_mul]
    · rw [if_neg h1, if_neg (fun h => h1 (congrArg Prod.fst h)), mul_zero, zero_mul]
  sum_eq := by
    rw [Fintype.sum_prod_type]
    have : ∀ i, ∑ k, a i * a' k * (b' k * b i) = a i * b i * E'' := fun i => by
      simp only [show ∀ k, a i * a' k * (b' k * b i) = a i * (a' k * b' k) * b i from fun k => by
        simp only [mul_assoc]]
      rw [← Finset.sum_mul, ← Finset.mul_sum, h₂.sum_eq, mul_assoc, ← h₁.b_mul_right,
        ← mul_assoc]
    simp_rw [this, ← Finset.sum_mul, h₁.sum_eq, hE''.eq]

/-- A splitting of `E'` through a single idempotent `E` gives a decomposition of `E'` into
the orthogonal idempotents `g_j = a_j E b_j`, each equivalent to `E` via `(a_j E, E b_j)`. -/
theorem orthogonalIdempotents {ι : Type*} [Fintype ι] [DecidableEq ι] {E' E : A} {a b : ι → A}
    (h : IsSplitting E' (fun _ => E) a b) (hE : IsIdempotentElem E)
    (hE' : IsIdempotentElem E') :
    OrthogonalIdempotents (fun j => a j * E * b j) ∧ ∑ j, a j * E * b j = E' ∧
      ∀ j, IsEquivPair (a j * E) (E * b j) (a j * E * b j) E := by
  have hba : ∀ j, b j * (a j * E) = E := fun j => by rw [← mul_assoc, h.mul_self, hE.eq]
  have hba' : ∀ j, E * b j * (a j * E) = E := fun j => by rw [mul_assoc, hba, hE.eq]
  have hab : ∀ j, a j * E * (E * b j) = a j * E * b j := fun j => by
    rw [← mul_assoc, mul_assoc (a j), hE.eq]
  refine ⟨⟨fun j => ?_, fun i j hij => ?_⟩, ?_, fun j => ⟨hab j, hba' j, ?_, ?_⟩⟩
  · show a j * E * b j * (a j * E * b j) = a j * E * b j
    rw [mul_assoc (a j * E), ← mul_assoc (b j), hba, ← mul_assoc, mul_assoc (a j), hE.eq]
  · show a i * E * b i * (a j * E * b j) = 0
    rw [mul_assoc (a i * E), ← mul_assoc (b i), ← mul_assoc (b i), h.mul_ne hij, zero_mul,
      zero_mul, mul_zero]
  · have : ∀ j, a j * E * b j = a j * b j * E' := fun j => by
      rw [mul_assoc, ← h.b_mul_right, ← mul_assoc]
    simp_rw [this, ← Finset.sum_mul, h.sum_eq, hE'.eq]
  · rw [mul_assoc, hba', mul_assoc, hE.eq]
  · rw [hba', ← mul_assoc, hE.eq]

end Graded.IsSplitting

namespace KLR

open KLRAlgebra LaurentPolynomial QuantumGroup

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {Γ : SimpleGraph I}
  [DecidableRel Γ.Adj] {ν : Multiset I}

local notation "A" => R1 k Γ ν

variable (k Γ) in
/-- A splitting of `E'` through `E` by homogeneous elements for the KL I grading, with its
degrees: `E' = ∑_j a_j b_j`, `b_i a_j = δ_{ij} E`, `a_j ∈ R(ν)_{d_j}`, `b_j ∈ R(ν)_{-d_j}`. -/
structure GradedSplitting (E' E : A) where
  /-- The index type. -/
  ι : Type
  [fintype : Fintype ι]
  [decEq : DecidableEq ι]
  /-- The elements `a_j`. -/
  a : ι → A
  /-- The elements `b_j`. -/
  b : ι → A
  /-- The degrees `d_j`. -/
  dg : ι → ℤ
  split : IsSplitting E' (fun _ => E) a b
  mem_a : ∀ j, a j ∈ (klGradingDatum k Γ).grade ν (dg j)
  mem_b : ∀ j, b j ∈ (klGradingDatum k Γ).grade ν (-dg j)

attribute [instance] GradedSplitting.fintype GradedSplitting.decEq

namespace GradedSplitting

/-- The generating function `∑_j q^{d_j}` of the degrees. -/
def genFun {E' E : A} (S : GradedSplitting k Γ E' E) : LaurentPolynomial ℤ := ∑ j, T (S.dg j)

/-- The trivial splitting of an idempotent through itself. -/
def refl {E : A} (hE : IsIdempotentElem E) (hE0 : E ∈ (klGradingDatum k Γ).grade ν 0) :
    GradedSplitting k Γ E E where
  ι := Unit
  a _ := E
  b _ := E
  dg _ := 0
  split := ⟨fun _ _ => by simp [hE.eq], by simp [hE.eq]⟩
  mem_a _ := hE0
  mem_b _ := by simpa using hE0

theorem genFun_refl {E : A} (hE : IsIdempotentElem E) (hE0 : E ∈ (klGradingDatum k Γ).grade ν 0) :
    (refl hE hE0).genFun = 1 := by
  simp [genFun, refl, T_zero]

/-- Composition of graded splittings. -/
def trans {E'' E' E : A} (S₁ : GradedSplitting k Γ E'' E') (S₂ : GradedSplitting k Γ E' E)
    (hE : IsIdempotentElem E) (hE'' : IsIdempotentElem E'') : GradedSplitting k Γ E'' E where
  ι := S₁.ι × S₂.ι
  a p := S₁.a p.1 * S₂.a p.2
  b p := S₂.b p.2 * S₁.b p.1
  dg p := S₁.dg p.1 + S₂.dg p.2
  split := S₁.split.trans S₂.split hE hE''
  mem_a p := SetLike.mul_mem_graded (S₁.mem_a p.1) (S₂.mem_a p.2)
  mem_b p := by
    have := SetLike.mul_mem_graded (S₂.mem_b p.2) (S₁.mem_b p.1)
    convert this using 2
    ring

theorem genFun_trans {E'' E' E : A} (S₁ : GradedSplitting k Γ E'' E')
    (S₂ : GradedSplitting k Γ E' E) (hE : IsIdempotentElem E) (hE'' : IsIdempotentElem E'') :
    (S₁.trans S₂ hE hE'').genFun = S₁.genFun * S₂.genFun := by
  simp only [genFun, trans, Fintype.sum_prod_type, T_add, Finset.sum_mul_sum]

theorem card_trans {E'' E' E : A} (S₁ : GradedSplitting k Γ E'' E')
    (S₂ : GradedSplitting k Γ E' E) (hE : IsIdempotentElem E) (hE'' : IsIdempotentElem E'') :
    Fintype.card (S₁.trans S₂ hE hE'').ι = Fintype.card S₁.ι * Fintype.card S₂.ι :=
  Fintype.card_prod _ _

end GradedSplitting

/-- The splitting of `1_{…i^{(n)} i…}` through `1_{…i^{(n+1)}…}` as a graded splitting. -/
def gradedSplittingSucc {i : Seq ν} {p n : ℕ} {bs : List (ℕ × ℕ)}
    (h : IsBlocks i ((p, n + 1) :: bs)) :
    GradedSplitting k Γ (divIdem i ((p, n) :: bs)) (divIdem i ((p, n + 1) :: bs)) where
  ι := Fin (n + 1)
  a j := divIdem i bs * blockA k (klQ Γ) i (h.le _ List.mem_cons_self) j
  b j := blockB k (klQ Γ) i (h.le _ List.mem_cons_self) j
  dg j := 2 * ((j : ℤ) - n)
  split := isSplitting_divIdem_succ h
  mem_a j := by
    have hpn := h.le _ List.mem_cons_self
    have hc := h.const _ List.mem_cons_self
    simp only at hpn
    rw [← zero_add (2 * ((j : ℤ) - n))]
    exact SetLike.mul_mem_graded (divIdem_mem_grade (klGradingDatum k Γ) h.tail)
      (blockA_mem_grade (klGradingDatum k Γ) hpn (c := i.lbl ⟨p, by omega⟩)
        (fun a h1 h2 => hc a _ h1 h2 le_rfl (by simp only; omega)) hc j)
  mem_b j := by
    have hpn := h.le _ List.mem_cons_self
    have hc := h.const _ List.mem_cons_self
    simp only at hpn
    have := blockB_mem_grade (klGradingDatum k Γ) hpn (c := i.lbl ⟨p, by omega⟩)
      (fun a h1 h2 => hc a _ h1 h2 le_rfl (by simp only; omega)) hc (show (j : ℕ) ≤ n by omega)
    convert this using 2
    show -(2 * ((j : ℤ) - n)) = 2 * ((n : ℤ) - j)
    ring

theorem genFun_gradedSplittingSucc {i : Seq ν} {p n : ℕ} {bs : List (ℕ × ℕ)}
    (h : IsBlocks i ((p, n + 1) :: bs)) :
    (gradedSplittingSucc (k := k) (Γ := Γ) h).genFun = T (-(n : ℤ)) * qint qUnitLP (n + 1) :=
  sum_T_two_mul_sub n

/-- The graded splitting of `1_{…i⋯i…}` through `1_{…i^{(N)}…}`, with generating function
`q^{-N(N-1)/2} [N]!` and `N!` terms. -/
theorem exists_gradedSplitting_block {i : Seq ν} {p : ℕ} {bs : List (ℕ × ℕ)} (hbs : IsBlocks i bs) :
    ∀ {N : ℕ}, IsBlocks i ((p, N) :: bs) →
      ∃ S : GradedSplitting k Γ (divIdem i bs) (divIdem i ((p, N) :: bs)),
        S.genFun = blockFactorLP N ∧ Fintype.card S.ι = N.factorial
  | 0, h => by
    have he : (divIdem i ((p, 0) :: bs) : A) = divIdem i bs := by
      rw [divIdem, divIdem, blocksElt_cons]; simp only; rw [blockElt_zero, one_mul]
    rw [he]
    exact ⟨GradedSplitting.refl (isIdempotentElem_divIdem hbs) (divIdem_mem_grade _ hbs),
      by rw [GradedSplitting.genFun_refl, blockFactorLP_zero], rfl⟩
  | N + 1, h => by
    obtain ⟨S, hS, hc⟩ := exists_gradedSplitting_block hbs (h.cons_mono (Nat.le_succ N))
    refine ⟨S.trans (gradedSplittingSucc h) (isIdempotentElem_divIdem h)
      (isIdempotentElem_divIdem hbs), ?_, ?_⟩
    · rw [GradedSplitting.genFun_trans, hS, genFun_gradedSplittingSucc, blockFactorLP_succ]
    · rw [GradedSplitting.card_trans, hc, Nat.factorial_succ, mul_comm]
      congr 1
      exact Fintype.card_fin (N + 1)

/-- Iterating over all blocks. -/
theorem exists_gradedSplitting_e {t : Seq ν} :
    ∀ {bs : List (ℕ × ℕ)}, IsBlocks t bs →
      ∃ S : GradedSplitting k Γ (e t) (divIdem t bs),
        S.genFun = (bs.map fun b => blockFactorLP b.2).prod ∧
          Fintype.card S.ι = (bs.map fun b => b.2.factorial).prod
  | [], h => by
    rw [divIdem_nil]
    exact ⟨GradedSplitting.refl (e_mul_self t) ((klGradingDatum k Γ).e_mem_grade t),
      by rw [GradedSplitting.genFun_refl]; rfl, rfl⟩
  | b :: bs, h => by
    obtain ⟨S, hS, hc⟩ := exists_gradedSplitting_e h.tail
    obtain ⟨S', hS', hc'⟩ := exists_gradedSplitting_block (k := k) (Γ := Γ) (p := b.1)
      (N := b.2) h.tail h
    refine ⟨S.trans S' (isIdempotentElem_divIdem h) (e_mul_self t), ?_, ?_⟩
    · rw [GradedSplitting.genFun_trans, hS, hS', List.map_cons, List.prod_cons, mul_comm]
    · rw [GradedSplitting.card_trans, hc, hc', List.map_cons, List.prod_cons, mul_comm]

omit [DecidableEq I] in
theorem prod_factorial_blocksDiv (d : List (I × ℕ)) (p : ℕ) :
    ((blocksDiv d p).map fun b => b.2.factorial).prod = (d.map fun q => q.2.factorial).prod := by
  induction d generalizing p with
  | nil => rfl
  | cons q d ih => simp only [blocksDiv, List.map_cons, List.prod_cons, ih]

/-- **KL I §2.2 Example 3 and §2.5: `1_î` decomposes into `i!` copies of `1_i`.** For a
divided-power expression `i = i_1^{(n_1)} ⋯ i_r^{(n_r)}` (the list `d`) with expansion `î`, there
are `n_1! ⋯ n_r!` mutually orthogonal idempotents `g_j` with `∑_j g_j = 1_î`, and homogeneous
`a_j ∈ R(ν)_{d_j}`, `b_j ∈ R(ν)_{-d_j}` with `a_j b_j = g_j`, `b_j a_j = 1_i` (so
`R(ν) g_j ≅ (R(ν) 1_i){-d_j}` and `g_j M ≅ (1_i M){d_j}`), whose degrees satisfy
`∑_j q^{d_j} = q^{-⟨i⟩} [n_1]! ⋯ [n_r]!`. -/
theorem exists_orthogonal_decomposition_e (d : List (I × ℕ))
    (h : (expandDiv d : Multiset I) = ν) :
    ∃ (ι : Type) (_ : Fintype ι) (g a b : ι → A) (dg : ι → ℤ),
      OrthogonalIdempotents g ∧ ∑ j, g j = e (Seq.ofList (expandDiv d) h) ∧
      (∀ j, IsEquivPair (a j) (b j) (g j) (divIdemOf d h)) ∧
      (∀ j, a j ∈ (klGradingDatum k Γ).grade ν (dg j)) ∧
      (∀ j, b j ∈ (klGradingDatum k Γ).grade ν (-dg j)) ∧
      ∑ j, (T (dg j) : LaurentPolynomial ℤ) = T (-(divAngle d : ℤ)) * divQFactLP d ∧
      Fintype.card ι = (d.map fun q => q.2.factorial).prod := by
  obtain ⟨S, hS, hc⟩ := exists_gradedSplitting_e (k := k) (Γ := Γ) (isBlocks_ofList d h)
  have hE := isIdempotentElem_divIdemOf (k := k) (Q := klQ Γ) d h
  obtain ⟨ho, hsum, hpair⟩ := S.split.orthogonalIdempotents hE (e_mul_self _)
  refine ⟨S.ι, inferInstance, fun j => S.a j * divIdemOf d h * S.b j,
    fun j => S.a j * divIdemOf d h, fun j => divIdemOf d h * S.b j, S.dg, ho, hsum, hpair,
    fun j => ?_, fun j => ?_, ?_, ?_⟩
  · have := SetLike.mul_mem_graded (S.mem_a j) (divIdemOf_mem_grade (klGradingDatum k Γ) d h)
    rwa [add_zero] at this
  · have := SetLike.mul_mem_graded (divIdemOf_mem_grade (klGradingDatum k Γ) d h) (S.mem_b j)
    rwa [zero_add] at this
  · rw [← GradedSplitting.genFun, hS, prod_blockFactorLP_blocksDiv]
  · rw [hc, prod_factorial_blocksDiv]

end KLR

end Categorification

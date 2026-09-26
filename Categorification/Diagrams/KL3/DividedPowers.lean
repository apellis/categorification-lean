/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.KaroubiKLR
import Categorification.KLR.NilHeckeBlockSplitting
import Categorification.KLR.DividedPowerDecomposition

/-!
# Divided powers `E_{+i^{(m)}} 1_λ` in `U̇`

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.5
(TeX label `subsec_dirsumdecs`), equation (3.54) and the display following (3.55):

  `E_{+i^{(m)}} 1_λ := (E_{+i^m} 1_λ, e_{+i,m}) {m(1-m)/2 · i·i/2}`,
  `E_{+i^m} 1_λ ≅ (E_{+i^{(m)}} 1_λ)^{⊕[m]_i!}`.

The idempotent `e_{+i,m}` is the image under `ϕ_{mi,λ}` (`toUEnd`) of the nilHecke idempotent
`e_{i,m} = x^δ ψ_{w_0} 1_{i^m}` of KL I §2.2 (`divIdem t [(0, m)]` for the sequence `t = i^m`),
which is what KL III's picture denotes ("similar to the idempotent `e_{i,m}` in [KL1, §2.2]").

The decomposition follows from the splitting of `1_{i^m}` in `R(mi) ≅ NH_m` into `m!` orthogonal
idempotents equivalent to `e_{i,m}` (`Categorification.KLR.NilHeckeBlockSplitting`, iterated
here for an arbitrary grading datum along the block `[0, m)`, `exists_split`), transported to
`U̇` with `kOrthIso` and `kIso` (`Categorification.Diagrams.KL3.KaroubiKLR`). The shifts are
the exponents of `[m]_i! = ∏_{n=1}^{m} [n]_i`, `[n]_i = ∑_{r=0}^{n-1} q_i^{n-1-2r}`,
`q_i = q^{d_i}` (`d_i = i·i/2`).

Only the upward case `E_{+i^{(m)}}` is treated: `ϕ_{ν,λ}` is available here for upward strands
only (`Categorification.Diagrams.KL3.Upward`); the downward case `E_{-i^{(m)}}` needs the
corresponding homomorphism `ϕ_{-ν,λ}` (or a symmetry of `U` exchanging orientations).

## Main results

* `seqPow i m`: the sequence `i^m`; `divCorner i m`: the idempotent `e_{i,m}` as a
  `CornerIdem`.
* `objEdiv RD k i m μ s`: **KL III (3.54)**, the 1-morphism `E_{+i^{(m)}} 1_μ {s}` of `U̇`.
* `exists_split`: `1_{i^m} = ∑_j A_j B_j` with `B_j A_{j'} = δ_{j j'} e_{i,N}` along the block
  `[0, N)`, with degrees, for any `N ≤ m`.
* `Epow_decomp`: **KL III (display after (3.55))**: `E_{+i^m} 1_μ ≅ ⨁_j E_{+i^{(m)}} 1_μ {s_j}`
  with `m!` summands and `∑_j q^{s_j} = ∏_{n=0}^{m-1} ∑_{r=0}^{n} q^{d_i (2r - n)} = [m]_i!`.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory CategoryTheory.Limits StringDiagrams QuantumGroup UDot Presentation
  Categorification.GradedBicat KLR KLR.KLRAlgebra KLR.Diagram LaurentPolynomial

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (k : Type w) [CommRing k] [DecidableEq I]

section Seqs

variable (i : I) (m : ℕ)

/-- The sequence `i^m ∈ Seq(m i)`. -/
def seqPow : Seq (Multiset.replicate m i) :=
  Seq.ofList (List.replicate m i) (Multiset.coe_replicate m i)

omit [DecidableEq I] in
theorem seqPow_lbl (a : Fin (Multiset.card (Multiset.replicate m i))) : (seqPow i m).lbl a = i := by
  rw [seqPow, Seq.ofList_lbl, List.getElem_replicate]

omit [DecidableEq I] in
theorem word_seqPow : word (seqPow i m) = List.replicate m i := by
  apply List.ext_getElem
  · simp
  · intro n h₁ h₂
    rw [getElem_word, List.getElem_replicate]
    exact seqPow_lbl i m _

omit [DecidableEq I] in
theorem isBlocks_seqPow {N : ℕ} (hN : N ≤ m) : IsBlocks (seqPow i m) [(0, N)] where
  le b hb := by
    rw [List.mem_singleton] at hb; subst hb
    simp only [Multiset.card_replicate, zero_add]; exact hN
  const b hb := by
    rw [List.mem_singleton] at hb; subst hb
    intro a b _ _ _ _
    rw [seqPow_lbl, seqPow_lbl]
  disj := List.pairwise_singleton _ _

variable {k}

theorem e_mul_divIdem {ν : Multiset I} {t : Seq ν} {bs : List (ℕ × ℕ)}
    (h : ∀ b ∈ bs, IsConstOn t b.1 b.2) : (e t * divIdem t bs : R2 k C ν) = divIdem t bs := by
  rw [divIdem, blocksElt_mul_e h, ← mul_assoc, e_mul_self]

variable (k C)

/-- The idempotent `e_{i,N} ⊗ 1` (the nilHecke idempotent on the first `N` strands) of
`R(m i)`, as an idempotent of the corner of `1_{i^m}`. For `N = m` it is KL III's `e_{+i,m}`. -/
def divCorner (N : ℕ) (hN : N ≤ m) : CornerIdem C k (seqPow i m) where
  f := divIdem (seqPow i m) [(0, N)]
  deg0 := divIdem_mem_grade _ (isBlocks_seqPow i m hN)
  idem := isIdempotentElem_divIdem (isBlocks_seqPow i m hN)
  left := e_mul_divIdem (isBlocks_seqPow i m hN).const

end Seqs

/-! ## Splitting `1_{i^m}` along the block -/

section Split

variable {k} (i : I) (m : ℕ)

local notation "G2" => klGradingDatum2 k C
local notation "t" => seqPow i m
local notation "ν" => Multiset.replicate m i

theorem divIdem_zero : (divIdem t [(0, 0)] : R2 k C ν) = e t := by
  rw [divIdem, blocksElt_cons, blockElt_zero, blocksElt_nil, one_mul, one_mul]

/-- **Splitting `1_{i^m}` through `e_{i,N} ⊗ 1`**: for `N ≤ m` there are `a_j, b_j ∈ R(m i)` with
`1_{i^m} = ∑_j a_j b_j` and `b_j a_{j'} = δ_{j j'} (e_{i,N} ⊗ 1)`, `a_j` of degree `d_j` and `b_j`
of degree `-d_j`, `N!` indices and `∑_j q^{d_j} = ∏_{n < N} ∑_{r ≤ n} q^{(i·i)(r - n)}`. -/
theorem exists_split : ∀ N : ℕ, N ≤ m →
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (a b : ι → R2 k C ν) (dg : ι → ℤ),
      Graded.IsSplitting (e t) (fun _ => divIdem t [(0, N)]) a b ∧
      (∀ j, a j ∈ (klGradingDatum2 k C).grade ν (dg j)) ∧ (∀ j, b j ∈ (klGradingDatum2 k C).grade ν (-dg j)) ∧
      Fintype.card ι = N.factorial ∧
      ∑ j, (T (dg j) : LaurentPolynomial ℤ) =
        ∏ n ∈ Finset.range N, ∑ r ∈ Finset.range (n + 1), T (C.dot i i * ((r : ℤ) - n))
  | 0, _ => by
    refine ⟨Unit, inferInstance, inferInstance, fun _ => e t, fun _ => e t, fun _ => 0,
      ⟨fun _ _ => ?_, ?_⟩, fun _ => (klGradingDatum2 k C).e_mem_grade t, fun _ => ?_, rfl, ?_⟩
    · rw [if_pos rfl, divIdem_zero, e_mul_self]
    · simp [e_mul_self]
    · simpa using (klGradingDatum2 k C).e_mem_grade t
    · simp
  | N + 1, hN => by
    obtain ⟨ι, _, _, a, b, dg, hS, ha, hb, hc, hgen⟩ := exists_split N (by omega)
    have hB := isBlocks_seqPow i m hN
    have hB' : IsBlocks t ((0, N + 1) :: []) := hB
    have hstep := isSplitting_divIdem_succ (k := k) (Q := klQ2 k C) hB'
    have hpn := hB'.le _ List.mem_cons_self
    have hc' := hB'.const _ List.mem_cons_self
    have hcl : ∀ a' : Fin (Multiset.card ν), 0 ≤ (a' : ℕ) → (a' : ℕ) < 0 + (N + 1) →
        (seqPow i m).lbl a' = i := fun a' _ _ => seqPow_lbl i m a'
    refine ⟨ι × Fin (N + 1), inferInstance, inferInstance,
      fun p => a p.1 * (divIdem t [] * blockA k (klQ2 k C) t hpn p.2),
      fun p => blockB k (klQ2 k C) t hpn p.2 * b p.1,
      fun p => dg p.1 + C.dot i i * ((p.2 : ℤ) - N),
      hS.trans hstep (isIdempotentElem_divIdem hB) (e_mul_self t), fun p => ?_, fun p => ?_,
      ?_, ?_⟩
    · have h1 := blockA_mem_grade G2 hpn hcl hc' p.2
      have h2 := SetLike.mul_mem_graded (divIdem_mem_grade G2 (IsBlocks.tail hB')) h1
      have h3 := SetLike.mul_mem_graded (ha p.1) h2
      convert h3 using 2
      simp [klGradingDatum2]
    · have h1 := blockB_mem_grade G2 hpn hcl hc' (j := p.2) (by omega)
      have h3 := SetLike.mul_mem_graded h1 (hb p.1)
      convert h3 using 2
      simp only [klGradingDatum2]
      ring
    · rw [Fintype.card_prod, hc, Fintype.card_fin, Nat.factorial_succ, mul_comm]
    · rw [Fintype.sum_prod_type, Finset.prod_range_succ, ← hgen, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Fin.sum_univ_eq_sum_range (fun r => (T (dg j) * T (C.dot i i * ((r : ℤ) - N)) :
        LaurentPolynomial ℤ)) (N + 1)]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [T_add]

end Split

/-! ## `E_{+i^m} 1_λ ≅ (E_{+i^{(m)}} 1_λ)^{⊕[m]_i!}` -/

section Decomp

variable (i : I) (m : ℕ) (μ : X)

/-- **KL III (3.54)**: the 1-morphism `E_{+i^{(m)}} 1_μ {s} = (E_{+i^m} 1_μ, e_{+i,m})
{m(1-m)/2 · d_i + s}` of `U̇`. -/
abbrev objEdiv (s : ℤ) : UKar RD k (wν RD (Multiset.replicate m i) + μ) μ :=
  kobj RD μ (divCorner C k i m m le_rfl) (-((m.choose 2 : ℕ) : ℤ) * di C i + s)

omit [DecidableEq I] in
theorem nfObj_congr_list {lam' μ' : X} {l l' : List (Letter I)} (hl : l = l')
    (h : wt RD μ' l = lam') (h' : wt RD μ' l' = lam') (s : ℤ) :
    nfObj RD k lam' μ' l h s = nfObj RD k lam' μ' l' h' s := by
  subst hl; rfl

theorem kobj_congr_shift {ν : Multiset I} {s' : Seq ν} (F : CornerIdem C k s') {t₁ t₂ : ℤ}
    (h : t₁ = t₂) : kobj RD μ F t₁ = kobj RD μ F t₂ := by
  subst h; rfl

omit [DecidableEq I] in
theorem prod_T_eq (s : Finset ℕ) (f : ℕ → ℤ) :
    ∏ n ∈ s, (T (f n) : LaurentPolynomial ℤ) = T (∑ n ∈ s, f n) := by
  induction s using Finset.induction_on with
  | empty => simp [T_zero]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, T_add]

omit [DecidableEq I] in
theorem sum_range_choose_two (m : ℕ) : ∑ n ∈ Finset.range m, (n : ℤ) = ((m.choose 2 : ℕ) : ℤ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ, Nat.choose_one_right]
    push_cast; ring

/-- **KL III, display after (3.55)**: `E_{+i^m} 1_μ ≅ (E_{+i^{(m)}} 1_μ)^{⊕[m]_i!}`: a direct sum
of `m!` shifted copies of `E_{+i^{(m)}} 1_μ` whose shifts `s_j` are the exponents of
`[m]_i! = ∏_{n=0}^{m-1} ∑_{r=0}^{n} q^{d_i (2r - n)}` (`q_i = q^{d_i}`). -/
theorem Epow_decomp :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (sh : ι → ℤ),
      Fintype.card ι = m.factorial ∧
      ∑ j, (T (sh j) : LaurentPolynomial ℤ) =
        ∏ n ∈ Finset.range m, ∑ r ∈ Finset.range (n + 1), T (di C i * (2 * (r : ℤ) - n)) ∧
      Nonempty (nfObj RD k (wν RD (Multiset.replicate m i) + μ) μ (ups (List.replicate m i))
          (by rw [← word_seqPow i m]; exact wt_ups_word (μ := μ) (seqPow i m)) 0 ≅
        ⨁ fun j => objEdiv RD k i m μ (sh j)) := by
  classical
  obtain ⟨ι, _, _, a, b, dg, hS, ha, hb, hc, hgen⟩ := exists_split (k := k) i m m le_rfl
  have hE : IsIdempotentElem (divIdem (seqPow i m) [(0, m)] : R2 k C (Multiset.replicate m i)) :=
    (divCorner C k i m m le_rfl).idem
  obtain ⟨ho, hsum, hpair⟩ := hS.orthogonalIdempotents hE (e_mul_self (seqPow i m))
  have hdeg : ∀ j, a j * divIdem (seqPow i m) [(0, m)] * b j ∈ (klGradingDatum2 k C).grade (Multiset.replicate m i) 0 :=
    fun j => by
      have := SetLike.mul_mem_graded (SetLike.mul_mem_graded (ha j)
        (divCorner C k i m m le_rfl).deg0) (hb j)
      rwa [add_zero, add_neg_cancel] at this
  let Gs : ι → CornerIdem C k (seqPow i m) := fun j =>
    { f := a j * divIdem (seqPow i m) [(0, m)] * b j
      deg0 := hdeg j
      idem := ho.idem j
      left := by
        rw [← hsum, Finset.sum_mul, Finset.sum_eq_single j
          (fun j' _ h => ho.ortho h) (fun h => absurd (Finset.mem_univ j) h), (ho.idem j).eq] }
  have hortho : ∀ j j', j ≠ j' → (Gs j).f * (Gs j').f = 0 := fun j j' h => ho.ortho h
  have iso1 := kOrthIso (RD := RD) (μ := μ) (CornerIdem.ofE (C := C) (k := k) (seqPow i m)) Gs
    hsum hortho 0
  have iso2 : ∀ j, kobj RD μ (Gs j) 0 ≅ objEdiv RD k i m μ (dg j + (m.choose 2 : ℕ) * di C i) :=
    fun j => kIso (Gs j) (divCorner C k i m m le_rfl) (hpair j)
      (by have := SetLike.mul_mem_graded (ha j) (divCorner C k i m m le_rfl).deg0
          rwa [add_zero] at this)
      (by have := SetLike.mul_mem_graded (divCorner C k i m m le_rfl).deg0 (hb j)
          rwa [zero_add] at this) 0 ≪≫
      eqToIso (kobj_congr_shift RD k μ (divCorner C k i m m le_rfl) (by ring))
  refine ⟨ι, inferInstance, inferInstance, fun j => dg j + (m.choose 2 : ℕ) * di C i, hc, ?_,
    ⟨eqToIso ?_ ≪≫ iso1 ≪≫ biproduct.mapIso iso2⟩⟩
  · simp only [T_add, ← Finset.sum_mul, hgen]
    rw [← sum_range_choose_two, Finset.sum_mul, ← prod_T_eq, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun n _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← T_add, ← two_mul_di C i]
    congr 1
    ring
  · rw [kobj_ofE]
    exact nfObj_congr_list RD k (by rw [word_seqPow]) _ _ 0

end Decomp

end Categorification.KL3.Diagram

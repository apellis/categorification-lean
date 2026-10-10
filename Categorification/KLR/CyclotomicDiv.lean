/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicProj

/-!
# KK's element `A` is a unit times a central monic polynomial

S.-J. Kang, M. Kashiwara, *Categorification of highest weight modules via
Khovanov–Lauda–Rouquier algebras*, arXiv:1102.4677v4, §4.2 (before Lemma 4.18 and in the proof of
Lemma 4.19): the image of KK's `A` in `R(β)[t]` is
`∑_𝐢 a_i(t) ∏_{𝐢_b ≠ i} Q_{i, 𝐢_b}(t, x_b) e(𝐢)`, "a monic polynomial up to an invertible
multiple" with central coefficients' leading part (KK Remark 4.20 (i)). Here:

* `divByMonic_add_mul_of_degree_lt`, `divByMonic_add'`, `divByMonic_mul_C'`, `divByMonicLin`:
  division by a monic polynomial over a noncommutative ring (KK's Lemma 4.19 uses the division
  algorithm in `A[t]`).
* `natDegree_fSplit_gPol`, `leadingCoeff_fSplit_gPol`: the `t`-degree and the leading coefficient
  of each `a_i(t) F_n(i 𝐢')` depend only on `β` (they are products over the multiset `β`).
* `aPrime_comm`: KK's `A` is central in `R(i) ⊗ R(β)`.
* `aMonic`, `monic_aMonic`, `theta_aPrime_eq_smul`, `aMonic_comm`: `θ(A) = λ · M` with `λ` a unit
  of `k` and `M` monic and central in `R(β)[t]`.
-/

namespace Categorification.KLR

open Equiv TypeA PolyRep
open scoped TensorProduct

/-! ### Division by a monic polynomial over a noncommutative ring -/

section MonicDiv

variable {R : Type*} [Ring R] {M : Polynomial R}

theorem divByMonic_add_mul_of_degree_lt (hM : M.Monic) (q : Polynomial R) {r : Polynomial R}
    (hr : r.degree < M.degree) : (r + M * q) /ₘ M = q :=
  (Polynomial.div_modByMonic_unique q r hM ⟨rfl, hr⟩).1

theorem degree_mul_C_le' (p : Polynomial R) (c : R) : (p * Polynomial.C c).degree ≤ p.degree := by
  rw [Polynomial.degree_le_iff_coeff_zero]
  intro n hn
  rw [Polynomial.coeff_mul_C, Polynomial.coeff_eq_zero_of_degree_lt hn, zero_mul]

theorem divByMonic_add' (hM : M.Monic) (p p' : Polynomial R) :
    (p + p') /ₘ M = p /ₘ M + p' /ₘ M := by
  nontriviality R
  have h : p + p' = (p %ₘ M + p' %ₘ M) + M * (p /ₘ M + p' /ₘ M) := by
    conv_lhs => rw [← Polynomial.modByMonic_add_div p M, ← Polynomial.modByMonic_add_div p' M]
    rw [mul_add]; abel
  rw [h, divByMonic_add_mul_of_degree_lt hM]
  exact (Polynomial.degree_add_le _ _).trans_lt
    (max_lt (Polynomial.degree_modByMonic_lt _ hM) (Polynomial.degree_modByMonic_lt _ hM))

theorem divByMonic_mul_C' (hM : M.Monic) (p : Polynomial R) (c : R) :
    (p * Polynomial.C c) /ₘ M = (p /ₘ M) * Polynomial.C c := by
  nontriviality R
  have h : p * Polynomial.C c = (p %ₘ M) * Polynomial.C c + M * ((p /ₘ M) * Polynomial.C c) := by
    conv_lhs => rw [← Polynomial.modByMonic_add_div p M]
    rw [add_mul, mul_assoc]
  rw [h, divByMonic_add_mul_of_degree_lt hM]
  exact (degree_mul_C_le' _ c).trans_lt (Polynomial.degree_modByMonic_lt _ hM)

theorem mul_divByMonic_of_commute (hM : M.Monic) {q : Polynomial R} (h : Commute q M) :
    (q * M) /ₘ M = q := by
  rw [h.eq]; exact Polynomial.mul_divByMonic_cancel_left q hM

theorem smul_eq_mul_C_algebraMap {k : Type*} [CommRing k] [Algebra k R] (c : k)
    (p : Polynomial R) : c • p = p * Polynomial.C (algebraMap k R c) :=
  Polynomial.ext fun n => by
    rw [Polynomial.coeff_smul, Polynomial.coeff_mul_C, Algebra.smul_def, Algebra.commutes]

variable (k : Type*) [CommRing k] [Algebra k R] in
/-- Division by a monic polynomial, as a `k`-linear map. -/
noncomputable def divByMonicLin (hM : M.Monic) : Polynomial R →ₗ[k] Polynomial R where
  toFun p := p /ₘ M
  map_add' := divByMonic_add' hM
  map_smul' c p := by
    simp only [RingHom.id_apply]
    rw [smul_eq_mul_C_algebraMap, divByMonic_mul_C' hM, ← smul_eq_mul_C_algebraMap]

theorem divByMonicLin_apply {k : Type*} [CommRing k] [Algebra k R] (hM : M.Monic)
    (p : Polynomial R) : divByMonicLin k hM p = p /ₘ M := rfl

end MonicDiv

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]

namespace KLRAlgebra

variable {Q : I → I → MvPolynomial (Fin 2) k}

/-! ### `t`-degree and leading coefficient of `a_i(t) F_n(i 𝐢')` -/

section Lead

variable (i : I) (β : Multiset I) (a : I → Polynomial k)

local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "Pb" => MvPolynomial (Fin (Multiset.card β)) k

variable (Q) in
/-- The leading coefficient in `t` of the factor of `F_n` at a strand of colour `j`:
`−1` if `j = i`, else that of `Q_{j,i}(x, t)`. -/
noncomputable def lcFac (j : I) : k :=
  if j = i then -1 else (polyInY (Q j i)).leadingCoeff.coeff 0

variable (Q) in
/-- The `t`-degree of the factor of `F_n` at a strand of colour `j`. -/
noncomputable def degFac (j : I) : ℕ :=
  if j = i then 0 else (polyInY (Q j i)).natDegree

omit [DecidableEq I] in
theorem cons1_succ (s : Seq β) (b : ℕ) (hb : b + 1 < Multiset.card (Si + β)) :
    (cons1 i β s).1 ⟨b + 1, hb⟩ = s.1 ⟨b, by rw [card_single_add] at hb; omega⟩ := by
  rw [Seq.append_apply_ge _ _ _ (by simp)]
  congr 1

theorem fSplit_cycFac_succ (hsym : ∀ a b, a ≠ b → Q b a = MvPolynomial.rename ![1, 0] (Q a b))
    (s : Seq β) (b : ℕ) (hb : b + 1 < Multiset.card (Si + β)) :
    fSplit (k := k) i β (cycFac Q (cons1 i β s) (b + 1)) =
      if s.1 ⟨b, by rw [card_single_add] at hb; omega⟩ = i then -1 else
        MvPolynomial.aeval ![Polynomial.C (MvPolynomial.X
          ⟨b, by rw [card_single_add] at hb; omega⟩ : Pb), Polynomial.X]
          (Q (s.1 ⟨b, by rw [card_single_add] at hb; omega⟩) i) := by
  unfold cycFac
  simp only [hb, ↓reduceDIte, show 1 ≤ b + 1 by omega, ↓reduceIte, cons1_zero, cons1_succ]
  split_ifs with h
  · rw [map_neg, map_one]
  · rw [fSplit_rename_vec2, hsym _ _ h, MvPolynomial.aeval_rename]
    congr 2
    funext c; fin_cases c <;> rfl

omit [DecidableEq I] in
theorem aeval_C_X_eq_map (q : MvPolynomial (Fin 2) k) (z : Pb) :
    MvPolynomial.aeval ![Polynomial.C z, Polynomial.X] q =
      (polyInY q).map (Polynomial.aeval z).toRingHom := by
  rw [show (polyInY q).map (Polynomial.aeval z).toRingHom =
    Polynomial.mapAlgHom (Polynomial.aeval z) (polyInY q) from rfl, polyInY, ← AlgHom.comp_apply,
    MvPolynomial.comp_aeval]
  congr 2
  funext c
  fin_cases c
  · simp [Polynomial.mapAlgHom]
  · simp [Polynomial.mapAlgHom]

omit [DecidableEq I] in
theorem lc_coeff_zero_of_isUnit [IsDomain k] {q : MvPolynomial (Fin 2) k}
    (hq : IsUnit (polyInY q).leadingCoeff) :
    Polynomial.C ((polyInY q).leadingCoeff.coeff 0) = (polyInY q).leadingCoeff ∧
      IsUnit ((polyInY q).leadingCoeff.coeff 0) := by
  obtain ⟨c, hc, hcq⟩ := Polynomial.isUnit_iff.1 hq
  rw [← hcq, Polynomial.coeff_C_zero]
  exact ⟨rfl, hc⟩

omit [DecidableEq I] in
theorem lead_aeval_C_X [IsDomain k] {q : MvPolynomial (Fin 2) k}
    (hq : IsUnit (polyInY q).leadingCoeff) (z : Pb) :
    (MvPolynomial.aeval ![Polynomial.C z, Polynomial.X] q).leadingCoeff =
        MvPolynomial.C ((polyInY q).leadingCoeff.coeff 0) ∧
      (MvPolynomial.aeval ![Polynomial.C z, Polynomial.X] q).natDegree = (polyInY q).natDegree := by
  obtain ⟨h1, h2⟩ := lc_coeff_zero_of_isUnit hq
  have hne : (Polynomial.aeval z).toRingHom (polyInY q).leadingCoeff ≠ 0 := by
    rw [← h1]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_C,
      MvPolynomial.algebraMap_eq, ne_eq, MvPolynomial.C_eq_zero]
    exact h2.ne_zero
  rw [aeval_C_X_eq_map, Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hne,
    Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hne, ← h1]
  simp

variable [IsDomain k]

/-- The `t`-degree and leading coefficient of the factor of `F_n` at strand `b + 1`. -/
theorem lead_fSplit_cycFac_succ
    (hsym : ∀ a b, a ≠ b → Q b a = MvPolynomial.rename ![1, 0] (Q a b))
    (hQ : ∀ a b : I, a ≠ b → IsUnit (polyInY (Q a b)).leadingCoeff)
    (s : Seq β) (b : ℕ) (hb : b + 1 < Multiset.card (Si + β)) :
    (fSplit (k := k) i β (cycFac Q (cons1 i β s) (b + 1))).leadingCoeff =
        MvPolynomial.C (lcFac Q i (s.1 ⟨b, by rw [card_single_add] at hb; omega⟩)) ∧
      (fSplit (k := k) i β (cycFac Q (cons1 i β s) (b + 1))).natDegree =
        degFac Q i (s.1 ⟨b, by rw [card_single_add] at hb; omega⟩) := by
  rw [fSplit_cycFac_succ i β hsym s b hb, lcFac, degFac]
  split_ifs with h
  · simp
  · exact lead_aeval_C_X β (hQ _ _ h) _

theorem isUnit_lcFac (hQ : ∀ a b : I, a ≠ b → IsUnit (polyInY (Q a b)).leadingCoeff) (j : I) :
    IsUnit (lcFac Q i j) := by
  rw [lcFac]
  split_ifs with h
  · exact isUnit_one.neg
  · exact (lc_coeff_zero_of_isUnit (hQ _ _ h)).2

omit [DecidableEq I] [IsDomain k] in
theorem prod_seq_map {M : Type*} [CommMonoid M] (f : I → M) (s : Seq β) :
    ∏ b, f (s.1 b) = (β.map f).prod := by
  rw [Finset.prod_eq_multiset_prod, show (Finset.univ.val.map fun b => f (s.1 b)) =
    (Finset.univ.val.map s.1).map f from (Multiset.map_map _ _ _).symm, s.2]

omit [DecidableEq I] [IsDomain k] in
theorem sum_seq_map {M : Type*} [AddCommMonoid M] (f : I → M) (s : Seq β) :
    ∑ b, f (s.1 b) = (β.map f).sum := by
  rw [Finset.sum_eq_multiset_sum, show (Finset.univ.val.map fun b => f (s.1 b)) =
    (Finset.univ.val.map s.1).map f from (Multiset.map_map _ _ _).symm, s.2]

variable (Q) in
/-- The leading coefficient `λ = ∏_{b} lcFac(β_b)` of `θ(A)` (a unit). -/
noncomputable def lamA : k := (β.map (lcFac Q i)).prod

variable (Q) in
/-- The `t`-degree of `θ(A)`. -/
noncomputable def degA : ℕ := (a i).natDegree + (β.map (degFac Q i)).sum

theorem isUnit_lamA (hQ : ∀ a b : I, a ≠ b → IsUnit (polyInY (Q a b)).leadingCoeff) :
    IsUnit (lamA Q i β) := by
  rw [lamA]
  induction β using Multiset.induction_on with
  | empty => simp
  | cons j β ih => rw [Multiset.map_cons, Multiset.prod_cons]; exact (isUnit_lcFac i hQ j).mul ih

omit [IsDomain k] in
/-- `fSplit (gPol s) = fSplit (a_i(x_0)) * ∏_{b < n} fSplit (factor at strand b + 1)`. -/
theorem fSplit_gPol_eq (s : Seq β) :
    fSplit (k := k) i β (gPol Q i β a s) =
      fSplit i β (cycA a (zero_lt_card_single_add i β) (cons1 i β s)) *
        ∏ b : Fin (Multiset.card β), fSplit i β (cycFac Q (cons1 i β s) (b.val + 1)) := by
  rw [gPol, map_mul, cycF, map_prod, Finset.prod_range_succ', Finset.prod_range
    (fun b => fSplit i β (cycFac Q (cons1 i β s) (b + 1)))]
  have h0 : cycFac Q (cons1 i β s) 0 = 1 := by
    unfold cycFac; split_ifs <;> first | rfl | omega
  rw [h0, map_one, mul_one]

theorem lead_fSplit_gPol (hsym : ∀ a b, a ≠ b → Q b a = MvPolynomial.rename ![1, 0] (Q a b))
    (hQ : ∀ a b : I, a ≠ b → IsUnit (polyInY (Q a b)).leadingCoeff) (ha : (a i).Monic)
    (s : Seq β) :
    (fSplit (k := k) i β (gPol Q i β a s)).leadingCoeff = MvPolynomial.C (lamA Q i β) ∧
      (fSplit (k := k) i β (gPol Q i β a s)).natDegree = degA Q i β a := by
  have hA : (fSplit (k := k) i β (cycA a (zero_lt_card_single_add i β) (cons1 i β s))).Monic ∧
      (fSplit (k := k) i β (cycA a (zero_lt_card_single_add i β) (cons1 i β s))).natDegree =
        (a i).natDegree := by
    rw [cycA, cons1_zero, ← Polynomial.aeval_algHom_apply, fSplit_X_zero, aeval_X_eq_map]
    exact ⟨ha.map _, ha.natDegree_map _⟩
  have hb : ∀ b : Fin (Multiset.card β), b.val + 1 < Multiset.card (Si + β) := fun b => by
    rw [card_single_add]; omega
  have hlead := fun b : Fin (Multiset.card β) => lead_fSplit_cycFac_succ i β hsym hQ s b.val (hb b)
  have hne : ∀ b ∈ (Finset.univ : Finset (Fin (Multiset.card β))),
      fSplit (k := k) i β (cycFac Q (cons1 i β s) (b.val + 1)) ≠ 0 := fun b _ h => by
    have := (hlead b).1
    rw [h, Polynomial.leadingCoeff_zero, eq_comm, MvPolynomial.C_eq_zero] at this
    exact (isUnit_lcFac i hQ _).ne_zero this
  rw [fSplit_gPol_eq, Polynomial.leadingCoeff_mul, Polynomial.natDegree_mul hA.1.ne_zero
    (Finset.prod_ne_zero_iff.2 hne), Polynomial.leadingCoeff_prod, Polynomial.natDegree_prod _ _ hne,
    hA.1.leadingCoeff, one_mul, hA.2, degA, lamA, ← prod_seq_map β _ s, ← sum_seq_map β _ s, map_prod]
  refine ⟨Finset.prod_congr rfl fun b _ => ?_, congrArg _ (Finset.sum_congr rfl fun b _ => ?_)⟩
  · rw [(hlead b).1]
  · rw [(hlead b).2]

end Lead

/-! ### `A` is central in `R(i) ⊗ R(β)`, and `θ(A) = λ M` -/

section Central

variable (i : I) (β : Multiset I) (a : I → Polynomial k)

local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "T" => KLRAlgebra k Q Si ⊗[k] KLRAlgebra k Q β
local notation "Rb" => KLRAlgebra k Q β
local notation "R" => KLRAlgebra k Q (Si + β)
local notation "Pb" => MvPolynomial (Fin (Multiset.card β)) k

theorem aElt_mem_subR1_single :
    (aElt a (zero_lt_card_single_add i β) (Multiset.card β) : R) ∈
      subR1 (k := k) (Q := Q) (Si + β) :=
  Subalgebra.sum_mem _ fun s _ => Subalgebra.mul_mem _ (pol_mem_subR1 _) (e_mem_subR1 s)

theorem concat_mem_subR1 (t : T) : concat Q Si β t ∈ subR1 (k := k) (Q := Q) (Si + β) := by
  induction t using TensorProduct.inductionOn with
  | add s t hs ht => rw [map_add]; exact Subalgebra.add_mem _ hs ht
  | tmul c b =>
    have hcb : (c ⊗ₜ b : T) = (c ⊗ₜ 1) * (1 ⊗ₜ b) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hcb, concat_mul]
    refine Subalgebra.mul_mem _ ?_ (concat_one_tmul_mem_subR1 i β b)
    rw [← sec_singlePoly (Q := Q) i c, sec]
    induction singlePoly Q i c using Polynomial.induction_on with
    | C r =>
      rw [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul',
        map_smul, ← Algebra.TensorProduct.one_def, concat_one]
      exact Subalgebra.smul_mem _ (oneConcat_mem_subR1 i β) r
    | add p q hp hq => rw [map_add, TensorProduct.add_tmul, map_add]; exact Subalgebra.add_mem _ hp hq
    | monomial n r h =>
      rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X,
        show ∀ u v : KLRAlgebra k Q Si, ((u * v) ⊗ₜ[k] (1 : Rb) : T) =
            (u ⊗ₜ[k] (1 : Rb)) * (v ⊗ₜ[k] (1 : Rb)) from
          fun u v => by rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one],
        concat_mul, concat_x_tmul_one]
      exact Subalgebra.mul_mem _ h
        (Subalgebra.mul_mem _ (x_mem_subR1 _) (oneConcat_mem_subR1 i β))

variable {P : I → I → MvPolynomial (Fin 2) k}

/-- **KK Remark 4.20 (i)**: `A` is central in `R(i) ⊗ R(β)`. -/
theorem aPrime_comm [IsDomain k] (hPQ : ∀ a b, a ≠ b → Q a b = P b a * MvPolynomial.rename ![1, 0] (P a b))
    (hP : ∀ a b, a ≠ b → P a b ≠ 0) (t : T) :
    aPrime Q i β a * t = t * aPrime Q i β a := by
  apply concat_injective hPQ hP
  have hA := aElt_mul_oneConcat (Q := Q) i β a
  have hcomm := aElt_comm_subR1 (Q := Q) a (zero_lt_card_single_add i β) (Multiset.card β)
    (card_single_add i β).symm (concat_mem_subR1 i β t)
  have h1 := commute_oneConcat_subR1 (k := k) (Q := Q) i β (aElt_mem_subR1_single i β a)
  rw [concat_mul, concat_mul, ← hA, mul_assoc, oneConcat_mul_concat, h1, ← mul_assoc,
    concat_mul_oneConcat, hcomm]

variable (Q) in
/-- `M = λ⁻¹ θ(A)`: KK's `A` in `R(β)[t]`, normalized to be monic. -/
noncomputable def aMonic : Polynomial Rb :=
  Ring.inverse (lamA Q i β) • theta Q i β (aPrime Q i β a)

theorem coeff_theta_aPrime (n : ℕ) :
    (theta Q i β (aPrime Q i β a)).coeff n =
      ∑ s : Seq β, pol ((fSplit (k := k) i β (gPol Q i β a s)).coeff n) * e s := by
  rw [theta_aPrime, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Polynomial.coeff_mul_C, Polynomial.coeff_map]
  rfl

variable [IsDomain k]

theorem theta_aPrime_eq_smul (hQ : ∀ a b : I, a ≠ b → IsUnit (polyInY (Q a b)).leadingCoeff) :
    theta Q i β (aPrime Q i β a) = lamA Q i β • aMonic Q i β a := by
  rw [aMonic, smul_smul, Ring.mul_inverse_cancel _ (isUnit_lamA i β hQ), one_smul]

/-- `M = λ⁻¹ θ(A)` is monic of degree `deg a_i + ∑_b deg_t Q_{β_b, i}`. -/
theorem monic_aMonic (hsym : ∀ a b, a ≠ b → Q b a = MvPolynomial.rename ![1, 0] (Q a b))
    (hQ : ∀ a b : I, a ≠ b → IsUnit (polyInY (Q a b)).leadingCoeff) (ha : (a i).Monic) :
    (aMonic Q i β a).Monic := by
  have hl := lead_fSplit_gPol (Q := Q) i β a hsym hQ ha
  refine Polynomial.monic_of_degree_le (degA Q i β a) ?_ ?_
  · rw [Polynomial.degree_le_iff_coeff_zero]
    intro n hn
    rw [aMonic, Polynomial.coeff_smul, coeff_theta_aPrime]
    have hn' : degA Q i β a < n := by exact_mod_cast hn
    rw [Finset.sum_eq_zero fun s _ => ?_, smul_zero]
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt ((hl s).2.symm ▸ hn'), map_zero, zero_mul]
  · rw [aMonic, Polynomial.coeff_smul, coeff_theta_aPrime]
    have : ∀ s : Seq β, (pol ((fSplit (k := k) i β (gPol Q i β a s)).coeff (degA Q i β a)) * e s :
        Rb) = algebraMap k Rb (lamA Q i β) * e s := fun s => by
      rw [← (hl s).2, Polynomial.coeff_natDegree, (hl s).1, MvPolynomial.algHom_C]
    rw [Finset.sum_congr rfl fun s _ => this s, ← Finset.mul_sum, sum_e, mul_one, Algebra.smul_def,
      ← map_mul, Ring.inverse_mul_cancel _ (isUnit_lamA i β hQ),
      map_one]

/-- `M` is central in `R(β)[t]`. -/
theorem aMonic_comm (hPQ : ∀ a b, a ≠ b → Q a b = P b a * MvPolynomial.rename ![1, 0] (P a b))
    (hP : ∀ a b, a ≠ b → P a b ≠ 0) (q : Polynomial Rb) :
    Commute q (aMonic Q i β a) := by
  rw [← theta_thetaInv (Q := Q) i β q, aMonic]
  refine Commute.smul_right ?_ _
  rw [Commute, SemiconjBy, ← map_mul, ← map_mul, aPrime_comm i β a hPQ hP]

end Central

end KLRAlgebra

end Categorification.KLR

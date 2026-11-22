/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.Stendhal
import Categorification.KLR.BasisTheoremGeneral
import Categorification.KLR.BaseChange
import Categorification.KLR.Prop213
import Categorification.KLR.Filtration
import Categorification.WeightedKLR.GalleryBasis.Corner

set_option backward.isDefEq.respectTransparency false

/-!
# Braided Stendhal diagrams

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §6.1,
Definitions 6.1–6.3 and Proposition 6.4. A `w`-Stendhal diagram is a Stendhal diagram whose
red strands trace out the permutation `w` (Definition 6.1). Webster's bimodule `B̃_w`
(Definitions 6.2, 6.3) is the span of such diagrams modulo the local relations of `T̃` and the
relations (6.20a)–(6.20c) moving black strands, dots and red strands through a red/red crossing.

All these relations are distinct-colour KLR relations: the red labels are pairwise distinct, so
no correction term occurs when a strand passes a red/red crossing. We therefore model the
diagrams for all `w` at once by the algebra `BraidedStendhalAlgebra`: the KLR algebra of the
data `stendhalQ Q Λ` with dots on red strands set to zero, but red strands allowed to cross.
The span of `w`-Stendhal diagrams with bottom red order `λ` is the corner cut out by the
idempotents with red order `λ` at the bottom and `w · λ` at the top.

## Main definitions

* `Stendhal.BraidedStendhalAlgebra`: diagrams with black strands of weight `ν`, red strands
  `λ_1, …, λ_ℓ` in any order, and red/red crossings.
* `Stendhal.BraidedStendhalAlgebra.toKLR`: the map to the KLR algebra of `stendhalQ Q Λ`
  killing dots on red strands.
* `Stendhal.BraidedStendhalAlgebra.cornerSpace`: Webster's `B̃_w`, the diagrams whose red
  strands read `κ` at the bottom and `κ'` at the top.

## Main results

* `Stendhal.BraidedStendhalAlgebra.basis`: **Webster, Proposition 6.4**, for all `w` at once:
  for every choice `ρ` of reduced words, the diagrams `ψ_{ρ(σ)} x^u e(i)` with no dots on red
  strands form a `k`-basis.
* `Stendhal.BraidedStendhalAlgebra.cornerBasis`: the same statement for `B̃_w`.

The proof of linear independence follows Webster's: the KLR algebra maps onto the braided
algebra, and the map `toKLR` back to the KLR algebra fixes the diagrams without red dots, whose
independence is the KLR basis theorem (KL I, Theorem 2.5, over any commutative ring for
symmetric data).

The grading is not formalized here: a red/red crossing has degree `-⟨λ_a, λ_b⟩`, which is not
determined by the KLR data `stendhalQ Q Λ`.
-/

namespace Categorification.Stendhal

open MvPolynomial KLR TypeA

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)

/-! ### Generic facts about `ncEval` -/

section ncEval

variable {A : Type*} [Ring A] [Algebra k A]

omit [DecidableEq I] in
private theorem pow_mul_of_commute (z y e : A) (_hz : Commute z e) (hy : Commute y e)
    (h : z * e = y * e) (s : ℕ) : z ^ s * e = y ^ s * e := by
  induction s with
  | zero => simp
  | succ s ih =>
    calc z ^ (s + 1) * e = z * (z ^ s * e) := by rw [pow_succ', mul_assoc]
      _ = z * (e * y ^ s) := by rw [ih, (hy.pow_left s).eq]
      _ = z * e * y ^ s := (mul_assoc _ _ _).symm
      _ = y * e * y ^ s := by rw [h]
      _ = y ^ (s + 1) * e := by rw [mul_assoc, ← (hy.pow_left s).eq, ← mul_assoc, pow_succ']

omit [DecidableEq I] in
private theorem prod_ofFn_mul_of_commute {n : ℕ} (z y : Fin n → A) (e : A)
    (hz : ∀ b, Commute (z b) e) (hy : ∀ b, Commute (y b) e) (h : ∀ b, z b * e = y b * e) :
    (List.ofFn z).prod * e = (List.ofFn y).prod * e := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hP : Commute (List.ofFn fun b : Fin n => y b.succ).prod e :=
      Commute.list_prod_left _ _ fun x hx => by
        obtain ⟨b, rfl⟩ := List.mem_ofFn.mp hx
        exact hy _
    have ih' := ih (fun b => z b.succ) (fun b => y b.succ) (fun b => hz _) (fun b => hy _)
      (fun b => h _)
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    calc z 0 * (List.ofFn fun b : Fin n => z b.succ).prod * e
        = z 0 * ((List.ofFn fun b : Fin n => y b.succ).prod * e) := by rw [mul_assoc, ih']
      _ = z 0 * e * (List.ofFn fun b : Fin n => y b.succ).prod := by
          rw [hP.eq, mul_assoc]
      _ = y 0 * e * (List.ofFn fun b : Fin n => y b.succ).prod := by rw [h 0]
      _ = y 0 * (List.ofFn fun b : Fin n => y b.succ).prod * e := by
          rw [mul_assoc, ← hP.eq, mul_assoc]

omit [DecidableEq I] in
/-- Evaluations at families that agree after multiplication by a commuting element agree after
multiplication by it. -/
theorem ncEval_mul_of_commute {n : ℕ} (z y : Fin n → A) (e : A) (hz : ∀ b, Commute (z b) e)
    (hy : ∀ b, Commute (y b) e) (h : ∀ b, z b * e = y b * e) (p : MvPolynomial (Fin n) k) :
    ncEval z p * e = ncEval y p * e := by
  induction p using MvPolynomial.induction_on' with
  | monomial s c =>
    rw [ncEval_monomial, ncEval_monomial, mul_assoc, mul_assoc,
      prod_ofFn_mul_of_commute (fun a => z a ^ s a) (fun a => y a ^ s a) e
        (fun b => (hz b).pow_left _) (fun b => (hy b).pow_left _)
        (fun b => pow_mul_of_commute _ _ _ (hz b) (hy b) (h b) _)]
  | add p q hp hq => rw [ncEval_add, ncEval_add, add_mul, add_mul, hp, hq]

omit [DecidableEq I] in
/-- Algebra maps commute with `ncEval`. -/
theorem algHom_ncEval {B : Type*} [Ring B] [Algebra k B] (F : A →ₐ[k] B) {n : ℕ}
    (y : Fin n → A) (p : MvPolynomial (Fin n) k) :
    F (ncEval y p) = ncEval (fun a => F (y a)) p := by
  induction p using MvPolynomial.induction_on' with
  | monomial s c =>
    rw [ncEval_monomial, ncEval_monomial, map_mul, AlgHom.commutes, map_list_prod,
      List.map_ofFn]
    simp only [Function.comp_def, map_pow]
  | add p q hp hq => rw [ncEval_add, map_add, hp, hq, ncEval_add]

omit [DecidableEq I] in
/-- Evaluating at the images of variables under an algebra map is renaming. -/
theorem ncEval_algHom_X' {B : Type*} [Ring B] [Algebra k B] {n n' : ℕ}
    (φ : MvPolynomial (Fin n') k →ₐ[k] B) (v : Fin n → Fin n') (p : MvPolynomial (Fin n) k) :
    ncEval (fun a => φ (X (v a))) p = φ (rename v p) := by
  conv_rhs => rw [p.as_sum]
  simp only [ncEval, Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [rename_monomial, monomial_eq, Finsupp.prod_mapDomain_index
    (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _), Finsupp.prod_fintype _ _
    (fun _ => pow_zero _), ← List.prod_ofFn, map_mul, algHom_C, map_list_prod, List.map_ofFn]
  simp only [Function.comp_def, map_pow]

end ncEval

/-! ### Red labels -/

section labels

variable {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)

omit [DecidableEq I] in
/-- Each red label occurs once. -/
theorem eq_of_lbl_eq_inr (i : Seq μ) {a b : Fin m} (r : Fin ℓ) (ha : i.lbl a = .inr r)
    (hb : i.lbl b = .inr r) : a = b := by
  classical
  have hred : Multiset.count (Sum.inr r : I ⊕ Fin ℓ) (ν.map Sum.inl) = 0 :=
    Multiset.count_eq_zero_of_notMem (by simp)
  have hcnt : Multiset.count (Sum.inr r : I ⊕ Fin ℓ) μ ≤ 1 := by
    rw [stendhalWeight, Multiset.count_add, hred, zero_add]
    exact Multiset.nodup_iff_count_le_one.mp (Finset.univ.nodup.map Sum.inr_injective) _
  have hcard : (Finset.univ.filter (fun a => Sum.inr r = i.lbl a)).card ≤ 1 := by
    rw [← i.2, Multiset.count_map] at hcnt
    exact hcnt
  exact Finset.card_le_one_iff.mp hcard (by simp [ha]) (by simp [hb])

omit [DecidableEq I] in
/-- Two positions with the same red label coincide. -/
theorem eq_of_lbl_eq_of_isRight (i : Seq μ) {a b : Fin m} (h : i.lbl a = i.lbl b)
    (hr : (i.lbl a).isRight) : a = b := by
  obtain ⟨r, hr'⟩ : ∃ r, i.lbl a = .inr r := by
    rcases hl : i.lbl a with _ | r
    · simp [hl] at hr
    · exact ⟨r, rfl⟩
  exact eq_of_lbl_eq_inr i r hr' (h ▸ hr')

end labels

omit [DecidableEq I] in
/-- The data `stendhalQ Q Λ` are symmetric when `Q` is. -/
theorem stendhalQ_symm (hQ : KLRSymm Q) : KLRSymm (stendhalQ Q Λ) := by
  rintro (i | r) (j | t) h
  · exact hQ i j (fun he => h (congrArg Sum.inl he))
  · simp [stendhalQ]
  · simp [stendhalQ]
  · simp [stendhalQ]

/-! ### The algebra of braided Stendhal diagrams -/

section Rel

variable (k) (ν : Multiset I)

local notation "μ" => stendhalWeight ℓ ν
local notation "Fr" => FreeAlgebra k (Gen μ)

/-- The relations of braided Stendhal diagrams (arXiv:1309.3796v2, Definition 6.3): the KLR
relations for `stendhalQ Q Λ`, which contain the local relations of `T̃` and (6.20a)–(6.20c),
and dots on red strands vanish. Red strands may cross. -/
inductive BraidedRel : Fr → Fr → Prop
  /-- The KLR relations. -/
  | klr {a b : Fr} (h : KLR.Rel k (stendhalQ Q Λ) μ a b) : BraidedRel a b
  /-- Red strands carry no dots. -/
  | red_dot (a : Fin (Multiset.card μ)) (i : Seq μ) (h : (i.lbl a).isRight) :
      BraidedRel (fx k μ a * fe k μ i) 0

end Rel

variable (k) in
/-- Braided Stendhal diagrams with black strands of weight `ν` and red strands
`λ_1, …, λ_ℓ` (arXiv:1309.3796v2, Definitions 6.1–6.3, for all permutations `w` and all red
orders at once). -/
def BraidedStendhalAlgebra (ν : Multiset I) : Type _ :=
  RingQuot (BraidedRel k Q Λ ν)

/-! ### Killing the dots on red strands -/

namespace KLRAlgebra

variable {Q Λ} {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "R" => KLR.KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)

open KLR.KLRAlgebra

/-- The sum of the idempotents with a black strand at position `a`. -/
noncomputable def blackIdem (a : Fin m) : R :=
  ∑ i ∈ Finset.univ.filter (fun i : Seq μ => (i.lbl a).isLeft), e i

/-- The dot at position `a`, multiplied by `blackIdem a`. -/
noncomputable def blackDot (a : Fin m) : R := x a * blackIdem a

theorem blackIdem_mul_e (a : Fin m) (i : Seq μ) :
    (blackIdem a * e i : R) = if (i.lbl a).isLeft then e i else 0 := by
  simp only [blackIdem, Finset.sum_mul, e_mul_e, Finset.sum_ite_eq', Finset.mem_filter,
    Finset.mem_univ, true_and]

theorem e_mul_blackIdem (a : Fin m) (i : Seq μ) :
    (e i * blackIdem a : R) = if (i.lbl a).isLeft then e i else 0 := by
  simp only [blackIdem, Finset.mul_sum, e_mul_e, Finset.sum_ite_eq, Finset.mem_filter,
    Finset.mem_univ, true_and]

/-- Setting the variables of red strands of `i` to zero. -/
noncomputable def blackSubst (i : Seq μ) :
    MvPolynomial (Fin m) k →ₐ[k] MvPolynomial (Fin m) k :=
  aeval fun a => if (i.lbl a).isLeft then (X a : MvPolynomial (Fin m) k) else 0

omit [DecidableEq I] in
theorem blackSubst_X (i : Seq μ) (a : Fin m) :
    blackSubst (k := k) i (X a) = if (i.lbl a).isLeft then X a else 0 := by
  simp [blackSubst]

theorem blackDot_mul_e (a : Fin m) (i : Seq μ) :
    (blackDot a * e i : R) = pol (blackSubst i (X a)) * e i := by
  rw [blackDot, mul_assoc, blackIdem_mul_e, blackSubst_X]
  split_ifs <;> simp

theorem blackDot_commute_e (a : Fin m) (i : Seq μ) : Commute (blackDot a : R) (e i) := by
  change blackDot a * e i = e i * blackDot a
  rw [blackDot, mul_assoc, blackIdem_mul_e, ← mul_assoc, ← x_mul_e, mul_assoc, e_mul_blackIdem]

theorem blackDot_mul_pol_mul_e (a : Fin m) (i : Seq μ) (p : MvPolynomial (Fin m) k) :
    (blackDot a * (pol p * e i) : R) = pol (blackSubst i (X a) * p) * e i := by
  rw [← (e_commute_pol i p).eq, ← mul_assoc, blackDot_mul_e, mul_assoc, (e_commute_pol i p).eq,
    ← mul_assoc, ← map_mul]

omit [DecidableEq I] in
theorem blackSubst_monomial (i : Seq μ) (u : Fin m →₀ ℕ)
    (hu : ∀ a, (i.lbl a).isRight → u a = 0) :
    blackSubst i (monomial u (1 : k)) = monomial u 1 := by
  rw [blackSubst, aeval_monomial, monomial_eq, map_one, one_mul, map_one, one_mul]
  refine Finsupp.prod_congr fun a ha => ?_
  have : (i.lbl a).isLeft := by
    rcases h : i.lbl a with _ | _
    · rfl
    · exact absurd (hu a (by simp [h])) (Finsupp.mem_support_iff.mp ha)
  simp [this]

omit [DecidableEq I] in
theorem blackSubst_rename (i : Seq μ) {n : ℕ} (f : Fin n → Fin m)
    (hf : ∀ b, (i.lbl (f b)).isLeft) (p : MvPolynomial (Fin n) k) :
    blackSubst (k := k) i (rename f p) = rename f p := by
  have : (blackSubst (k := k) i).comp (rename f) =
      (rename f : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin m) k) :=
    MvPolynomial.algHom_ext fun b => by simp [blackSubst, hf b]
  exact congrArg (fun φ : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin m) k => φ p) this

/-- The generators of the KLR algebra, with dots on red strands set to zero. -/
noncomputable def blackGen : Gen μ → R
  | .idem i => e i
  | .dot a => blackDot a
  | .cross j => ψ j

/-- The free algebra on the generators maps to `R` through `blackGen`. -/
noncomputable def blackFree : FreeAlgebra k (Gen μ) →ₐ[k] R :=
  FreeAlgebra.lift k blackGen

@[simp] theorem blackFree_fe (i : Seq μ) : blackFree (Q := Q) (Λ := Λ) (fe k μ i) = e i :=
  FreeAlgebra.lift_ι_apply _ _
@[simp] theorem blackFree_fx (a : Fin m) :
    blackFree (Q := Q) (Λ := Λ) (fx k μ a) = blackDot a :=
  FreeAlgebra.lift_ι_apply _ _
@[simp] theorem blackFree_fψ (j : ℕ) : blackFree (Q := Q) (Λ := Λ) (fψ k μ j) = ψ j :=
  FreeAlgebra.lift_ι_apply _ _

theorem ncEval_blackDot_mul_e {n : ℕ} (f : Fin n → Fin m) (p : MvPolynomial (Fin n) k)
    (i : Seq μ) :
    ncEval (fun b => (blackDot (f b) : R)) p * e i = pol (blackSubst i (rename f p)) * e i := by
  refine (ncEval_mul_of_commute (A := R) (fun b => blackDot (f b))
    (fun b => pol (blackSubst i (X (f b)))) (e i) (fun b => blackDot_commute_e _ i)
    (fun b => (e_commute_pol i _).symm) (fun b => blackDot_mul_e _ i) p).trans ?_
  exact congrArg (· * e i) (ncEval_algHom_X' ((pol (Q := stendhalQ Q Λ) (ν := μ)).comp
    (blackSubst i)) f p)

theorem blackFree_ncEval_mul_e {n : ℕ} (f : Fin n → Fin m) (p : MvPolynomial (Fin n) k)
    (i : Seq μ) :
    blackFree (Q := Q) (Λ := Λ) (ncEval (fun b => fx k μ (f b)) p) * e i =
      pol (blackSubst i (rename f p)) * e i := by
  rw [algHom_ncEval]
  simp only [blackFree_fx]
  exact ncEval_blackDot_mul_e f p i

theorem eq_of_forall_mul_e {y z : R} (h : ∀ i : Seq μ, y * e i = z * e i) : y = z := by
  rw [← mul_one y, ← mul_one z, ← sum_e, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => h i


theorem blackDot_mul_e' (a : Fin m) (i : Seq μ) :
    (blackDot a * e i : R) = if (i.lbl a).isLeft then x a * e i else 0 := by
  rw [blackDot, mul_assoc, blackIdem_mul_e]
  split_ifs <;> simp

omit [DecidableEq I] in
theorem isLeft_of_isRight_eq {i : Seq μ} {a b : Fin m} (hab : a ≠ b)
    (h : i.lbl a = i.lbl b) : (i.lbl a).isLeft := by
  rcases hl : i.lbl a with _ | r
  · rfl
  · exact absurd (eq_of_lbl_eq_of_isRight i h (by simp [hl])) hab

omit [DecidableEq I] in
theorem vec_fx_two (a b : Fin m) :
    ![fx k μ a, fx k μ b] = fun c => fx k μ (![a, b] c) := by
  funext c; fin_cases c <;> rfl

omit [DecidableEq I] in
theorem vec_fx_three (a b c : Fin m) :
    ![fx k μ a, fx k μ b, fx k μ c] = fun d => fx k μ (![a, b, c] d) := by
  funext d; fin_cases d <;> rfl

theorem vec_x_two (a b : Fin m) :
    (![x a, x b] : Fin 2 → R) = fun c => x (![a, b] c) := by
  funext c; fin_cases c <;> rfl

theorem vec_x_three (a b c : Fin m) :
    (![x a, x b, x c] : Fin 3 → R) = fun d => x (![a, b, c] d) := by
  funext d; fin_cases d <;> rfl

/-- `blackFree` respects the KLR relations. -/
theorem blackFree_rel {y z : FreeAlgebra k (Gen μ)} (h : KLR.Rel k (stendhalQ Q Λ) μ y z) :
    blackFree (Q := Q) (Λ := Λ) y = blackFree z := by
  cases h with
  | idem_mul i j =>
    simp only [map_mul, blackFree_fe, e_mul_e]
    split_ifs <;> simp
  | idem_sum => simp [map_sum, sum_e]
  | dot_idem a i =>
    simp only [map_mul, blackFree_fe, blackFree_fx]; exact (blackDot_commute_e a i).eq
  | cross_idem j i => simp only [map_mul, blackFree_fe, blackFree_fψ]; exact ψ_mul_e j i
  | cross_zero j h => simp only [blackFree_fψ, map_zero]; exact ψ_eq_zero j h
  | dot_dot a b =>
    simp only [map_mul, blackFree_fx]
    refine eq_of_forall_mul_e fun i => ?_
    rw [mul_assoc, mul_assoc, ← one_mul (e i), ← map_one (pol (Q := stendhalQ Q Λ) (ν := μ)),
      blackDot_mul_pol_mul_e, blackDot_mul_pol_mul_e, blackDot_mul_pol_mul_e,
      blackDot_mul_pol_mul_e, mul_one, mul_one, mul_comm (blackSubst i (X a))]
  | cross_cross j l h => simp only [map_mul, blackFree_fψ]; exact ψ_mul_ψ j l h
  | dot_cross a j h₁ h₂ =>
    simp only [map_mul, blackFree_fx, blackFree_fψ]
    refine eq_of_forall_mul_e fun i => ?_
    rw [mul_assoc, ψ_mul_e, ← mul_assoc, blackDot_mul_e', lbl_sadj_of_ne i a h₁ h₂,
      mul_assoc, blackDot_mul_e']
    split_ifs
    · rw [mul_assoc, ← ψ_mul_e, ← mul_assoc, ← mul_assoc, x_mul_ψ a j h₁ h₂]
    · simp
  | dot_cross_left j h i =>
    simp only [map_mul, map_sub, blackFree_fx, blackFree_fψ]
    rw [apply_ite (blackFree (Q := Q) (Λ := Λ)), blackFree_fe, map_zero, sub_mul, mul_assoc,
      ψ_mul_e, ← mul_assoc, blackDot_mul_e', lbl_sadj_left h, mul_assoc (ψ j), blackDot_mul_e']
    by_cases hb : (i.lbl ⟨j + 1, h⟩).isLeft
    · simp only [hb, ↓reduceIte]
      rw [mul_assoc, ← ψ_mul_e, ← mul_assoc, ← mul_assoc, ← sub_mul, dot_cross_left]
    · simp only [hb, ↓reduceIte, Bool.false_eq_true, zero_mul, mul_zero, sub_zero]
      split_ifs with hl
      · exact absurd (hl ▸ isLeft_of_isRight_eq (by simp [Fin.ext_iff]) hl) hb
      · rfl
  | dot_cross_right j h i =>
    simp only [map_mul, map_sub, blackFree_fx, blackFree_fψ]
    rw [apply_ite (blackFree (Q := Q) (Λ := Λ)), blackFree_fe, map_zero, sub_mul, mul_assoc,
      blackDot_mul_e', mul_assoc (blackDot _), ψ_mul_e, ← mul_assoc, blackDot_mul_e',
      lbl_sadj_right h]
    by_cases hb : (i.lbl ⟨j, by omega⟩).isLeft
    · simp only [hb, ↓reduceIte]
      rw [mul_assoc (x _), ← ψ_mul_e, ← mul_assoc, ← mul_assoc, ← sub_mul, dot_cross_right]
    · simp only [hb, ↓reduceIte, Bool.false_eq_true, zero_mul, mul_zero, sub_zero]
      split_ifs with hl
      · exact absurd (isLeft_of_isRight_eq (by simp [Fin.ext_iff]) hl) hb
      · rfl
  | cross_sq j h i =>
    simp only [map_mul, blackFree_fψ, blackFree_fe]
    rw [ψ_sq j h, apply_ite (blackFree (Q := Q) (Λ := Λ))]
    split_ifs with hl
    · simp
    · rw [vec_fx_two, map_mul, blackFree_fe, blackFree_ncEval_mul_e, vec_x_two, ncEval_eq_pol]
      congr 2
      symm
      rcases ha : i.lbl ⟨j, by omega⟩ with a | r <;> rcases hb : i.lbl ⟨j + 1, h⟩ with b | t
      · exact blackSubst_rename i _ (fun c => by fin_cases c <;> simp [ha, hb]) _
      · simp [blackSubst, ha]
      · simp [blackSubst, hb]
      · simp [stendhalQ]
  | braid j h i =>
    simp only [map_mul, map_sub, blackFree_fψ, blackFree_fe]
    rw [braid j h, apply_ite (blackFree (Q := Q) (Λ := Λ))]
    split_ifs with hc
    · rw [vec_fx_three, map_mul, blackFree_fe, blackFree_ncEval_mul_e, vec_x_three,
        ncEval_eq_pol]
      congr 2
      symm
      have h0 : (i.lbl ⟨j, by omega⟩).isLeft :=
        isLeft_of_isRight_eq (by simp [Fin.ext_iff]) hc.1
      have h2 : (i.lbl ⟨j + 2, h⟩).isLeft := hc.1 ▸ h0
      rcases ha : i.lbl ⟨j, by omega⟩ with a | r
      · rcases hb : i.lbl ⟨j + 1, by omega⟩ with b | t
        · refine blackSubst_rename i _ (fun c => ?_) _
          fin_cases c
          · simpa using h0
          · simp [hb]
          · simpa using h2
        · simp only [stendhalQ_inl_inr]
          rw [X_pow_eq_monomial, qbar_monomial]
          simp [blackSubst, h0, h2]
      · simp [ha] at h0
    · simp

end KLRAlgebra

namespace BraidedStendhalAlgebra

variable {Q Λ} {ν : Multiset I}

noncomputable instance : Ring (BraidedStendhalAlgebra k Q Λ ν) :=
  inferInstanceAs (Ring (RingQuot _))
noncomputable instance : Algebra k (BraidedStendhalAlgebra k Q Λ ν) :=
  inferInstanceAs (Algebra k (RingQuot _))

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "R" => KLR.KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)

variable (k Q Λ ν) in
/-- The map from the KLR algebra of `stendhalQ Q Λ`. -/
noncomputable def ofKLR : R →ₐ[k] BraidedStendhalAlgebra k Q Λ ν :=
  RingQuot.liftAlgHom k ⟨RingQuot.mkAlgHom k (BraidedRel k Q Λ ν),
    fun _ _ h => RingQuot.mkAlgHom_rel k (BraidedRel.klr h)⟩

theorem ofKLR_mk (a : FreeAlgebra k (Gen μ)) :
    ofKLR k Q Λ ν (KLRAlgebra.mk k _ _ a) = RingQuot.mkAlgHom k (BraidedRel k Q Λ ν) a :=
  RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _

theorem ofKLR_surjective : Function.Surjective (ofKLR k Q Λ ν) := by
  intro y
  obtain ⟨a, rfl⟩ := RingQuot.mkAlgHom_surjective k (BraidedRel k Q Λ ν) y
  exact ⟨_, ofKLR_mk a⟩

/-- Red strands carry no dots. -/
theorem ofKLR_x_mul_e_of_red (a : Fin m) (i : Seq μ) (h : (i.lbl a).isRight) :
    ofKLR k Q Λ ν (KLRAlgebra.x a * KLRAlgebra.e i) = 0 := by
  rw [KLRAlgebra.x, KLRAlgebra.e, ← map_mul, ofKLR_mk,
    RingQuot.mkAlgHom_rel k (BraidedRel.red_dot (Q := Q) (Λ := Λ) a i h), map_zero]

variable (k Q Λ ν) in
/-- The map to the KLR algebra killing dots on red strands, induced by `blackFree`. -/
noncomputable def toKLR : BraidedStendhalAlgebra k Q Λ ν →ₐ[k] R :=
  RingQuot.liftAlgHom k ⟨KLRAlgebra.blackFree, fun _ _ h => by
    cases h with
    | klr h => exact KLRAlgebra.blackFree_rel h
    | red_dot a i h =>
      rw [map_mul, KLRAlgebra.blackFree_fx, KLRAlgebra.blackFree_fe,
        KLRAlgebra.blackDot_mul_e', map_zero]
      rcases hl : i.lbl a with _ | _
      · simp [hl] at h
      · simp⟩

theorem toKLR_ofKLR_mk (a : FreeAlgebra k (Gen μ)) :
    toKLR k Q Λ ν (ofKLR k Q Λ ν (KLRAlgebra.mk k _ _ a)) = KLRAlgebra.blackFree a := by
  rw [ofKLR_mk]
  exact RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _

theorem toKLR_ofKLR_e (i : Seq μ) :
    toKLR k Q Λ ν (ofKLR k Q Λ ν (KLRAlgebra.e i)) = KLRAlgebra.e i := by
  rw [KLRAlgebra.e, toKLR_ofKLR_mk, KLRAlgebra.blackFree_fe]
  rfl

theorem toKLR_ofKLR_x (a : Fin m) :
    toKLR k Q Λ ν (ofKLR k Q Λ ν (KLRAlgebra.x a)) = KLRAlgebra.blackDot a := by
  rw [KLRAlgebra.x, toKLR_ofKLR_mk, KLRAlgebra.blackFree_fx]

theorem toKLR_ofKLR_ψ (j : ℕ) :
    toKLR k Q Λ ν (ofKLR k Q Λ ν (KLRAlgebra.ψ j)) = KLRAlgebra.ψ j := by
  rw [KLRAlgebra.ψ, toKLR_ofKLR_mk, KLRAlgebra.blackFree_fψ]
  rfl

theorem toKLR_ofKLR_ψw (ρ : List ℕ) :
    toKLR k Q Λ ν (ofKLR k Q Λ ν (KLRAlgebra.ψw ρ)) = KLRAlgebra.ψw ρ := by
  rw [KLRAlgebra.ψw, map_list_prod, map_list_prod, List.map_map, List.map_map]
  congr 1
  exact List.map_congr_left fun j _ => toKLR_ofKLR_ψ j

theorem toKLR_ofKLR_pol_mul_e (p : MvPolynomial (Fin m) k) (i : Seq μ) :
    toKLR k Q Λ ν (ofKLR k Q Λ ν (KLRAlgebra.pol p * KLRAlgebra.e i)) =
      KLRAlgebra.pol (KLRAlgebra.blackSubst i p) * KLRAlgebra.e i := by
  rw [map_mul, map_mul, toKLR_ofKLR_e]
  have := KLRAlgebra.ncEval_eq_pol (k := k) (Q := stendhalQ Q Λ) (ν := μ) id p
  simp only [rename_id, AlgHom.id_apply] at this
  rw [← this, algHom_ncEval, algHom_ncEval]
  simp only [id, toKLR_ofKLR_x]
  have h2 := KLRAlgebra.ncEval_blackDot_mul_e (Q := Q) (Λ := Λ) id p i
  simpa only [rename_id, AlgHom.id_apply, id] using h2

/-- The diagrams `ψ_{ρ(σ)} x^u e(i)` with no dots on red strands. -/
def BlackIdx (ν : Multiset I) : Type _ :=
  {b : Seq (stendhalWeight ℓ ν) × Equiv.Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) ×
      (Fin (Multiset.card (stendhalWeight ℓ ν)) →₀ ℕ) //
    ∀ a, (b.1.lbl a).isRight → b.2.2 a = 0}

theorem toKLR_ofKLR_std (ρ : List ℕ) (u : Fin m →₀ ℕ) (i : Seq μ)
    (hu : ∀ a, (i.lbl a).isRight → u a = 0) :
    toKLR k Q Λ ν (ofKLR k Q Λ ν
      (KLRAlgebra.ψw ρ * KLRAlgebra.pol (monomial u 1) * KLRAlgebra.e i)) =
      KLRAlgebra.ψw ρ * KLRAlgebra.pol (monomial u 1) * KLRAlgebra.e i := by
  rw [mul_assoc, map_mul, map_mul, toKLR_ofKLR_ψw, toKLR_ofKLR_pol_mul_e,
    KLRAlgebra.blackSubst_monomial i u hu]

theorem ofKLR_std_eq_zero (ρ : List ℕ) (u : Fin m →₀ ℕ) (i : Seq μ) (a : Fin m)
    (ha : (i.lbl a).isRight) (hu : u a ≠ 0) :
    ofKLR k Q Λ ν (KLRAlgebra.ψw ρ * KLRAlgebra.pol (monomial u 1) * KLRAlgebra.e i) = 0 := by
  have hle : Finsupp.single a 1 ≤ u := by
    rw [Finsupp.single_le_iff]; omega
  have : (monomial u 1 : MvPolynomial (Fin m) k) = monomial (u - Finsupp.single a 1) 1 * X a := by
    rw [X, monomial_mul_monomial, one_mul, tsub_add_cancel_of_le hle]
  rw [this, map_mul KLRAlgebra.pol, KLRAlgebra.pol_X, mul_assoc, mul_assoc, map_mul, map_mul,
    ofKLR_x_mul_e_of_red a i ha, mul_zero, mul_zero]

variable (hQ : KLRSymm Q)
  (ρ : Equiv.Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ)
  (hρ : ∀ w, IsReduced (Multiset.card (stendhalWeight ℓ ν)) (ρ w) ∧
    wordProd (Multiset.card (stendhalWeight ℓ ν)) (ρ w) = w)

/-- The family of diagrams of Webster's Proposition 6.4. -/
noncomputable def stdElt (b : BlackIdx (ℓ := ℓ) ν) : BraidedStendhalAlgebra k Q Λ ν :=
  ofKLR k Q Λ ν (KLRAlgebra.ψw (ρ b.1.2.1) * KLRAlgebra.pol (monomial b.1.2.2 1) *
    KLRAlgebra.e b.1.1)

include hQ hρ in
theorem linearIndependent_stdElt :
    LinearIndependent k (stdElt (k := k) (Q := Q) (Λ := Λ) ρ) := by
  let B := KLRAlgebra.basisOfSymm (stendhalQ_symm Q Λ hQ) ρ hρ
  refine LinearIndependent.of_comp (toKLR k Q Λ ν).toLinearMap ?_
  have : (toKLR k Q Λ ν).toLinearMap ∘ stdElt (k := k) (Q := Q) (Λ := Λ) ρ =
      B ∘ Subtype.val := by
    funext b
    simp only [Function.comp_apply, AlgHom.toLinearMap_apply, stdElt, B,
      KLRAlgebra.basisOfSymm_apply]
    exact toKLR_ofKLR_std _ _ _ b.2
  rw [this]
  exact B.linearIndependent.comp _ Subtype.val_injective

include hQ hρ in
theorem span_stdElt :
    Submodule.span k (Set.range (stdElt (k := k) (Q := Q) (Λ := Λ) ρ)) = ⊤ := by
  let B := KLRAlgebra.basisOfSymm (stendhalQ_symm Q Λ hQ) ρ hρ
  rw [eq_top_iff]
  rintro y -
  obtain ⟨z, rfl⟩ := ofKLR_surjective (k := k) (Q := Q) (Λ := Λ) (ν := ν) y
  have hz : z ∈ Submodule.span k (Set.range B) := B.span_eq ▸ Submodule.mem_top
  have := Submodule.mem_map_of_mem (f := (ofKLR k Q Λ ν).toLinearMap) hz
  rw [Submodule.map_span] at this
  refine Submodule.span_le.mpr ?_ this
  rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
  simp only [AlgHom.toLinearMap_apply, B, KLRAlgebra.basisOfSymm_apply]
  by_cases hb : ∀ a, (b.1.lbl a).isRight → b.2.2 a = 0
  · exact Submodule.subset_span ⟨⟨b, hb⟩, rfl⟩
  · push Not at hb
    obtain ⟨a, ha, hu⟩ := hb
    rw [ofKLR_std_eq_zero _ _ _ a ha hu]
    exact Submodule.zero_mem _

/-- **Webster, Proposition 6.4** (arXiv:1309.3796v2), for all red permutations at once: for
symmetric `Q` and a choice `ρ` of reduced words, the braided Stendhal diagrams
`ψ_{ρ(σ)} x^u e(i)` with no dots on red strands form a `k`-basis. -/
noncomputable def basis :
    Module.Basis (BlackIdx (ℓ := ℓ) ν) k (BraidedStendhalAlgebra k Q Λ ν) :=
  Module.Basis.mk (linearIndependent_stdElt hQ ρ hρ) (span_stdElt hQ ρ hρ).ge

theorem basis_apply (b : BlackIdx (ℓ := ℓ) ν) :
    basis hQ ρ hρ b = ofKLR k Q Λ ν (KLRAlgebra.ψw (ρ b.1.2.1) *
      KLRAlgebra.pol (monomial b.1.2.2 1) * KLRAlgebra.e b.1.1) := by
  simp [basis, stdElt]

end BraidedStendhalAlgebra


/-! ### The bimodules `B̃_w` -/

section Corner

variable {Q Λ} {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "R" => KLR.KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)

/-- The red labels of a sequence, read from left to right. -/
def redWord (i : Seq μ) : List (Fin ℓ) :=
  (List.finRange m).filterMap fun a => (i.lbl a).getRight?

variable (k Q Λ) in
/-- The sum of the idempotents `e(i)` whose red labels read `κ` from left to right. -/
noncomputable def redIdem (κ : List (Fin ℓ)) : R :=
  ∑ i ∈ Finset.univ.filter (fun i : Seq μ => redWord i = κ), KLRAlgebra.e i

theorem redIdem_mul_std (κ' κ : List (Fin ℓ)) (ρ : List ℕ) (p : MvPolynomial (Fin m) k)
    (i : Seq μ) :
    redIdem k Q Λ κ' * (KLRAlgebra.ψw ρ * KLRAlgebra.pol p * KLRAlgebra.e i) *
        redIdem k Q Λ κ =
      if redWord (wordProd m ρ • i) = κ' ∧ redWord i = κ then
        KLRAlgebra.ψw ρ * KLRAlgebra.pol p * KLRAlgebra.e i else 0 := by
  have hR : (KLRAlgebra.ψw ρ * KLRAlgebra.pol p * KLRAlgebra.e i : R) * redIdem k Q Λ κ =
      if redWord i = κ then KLRAlgebra.ψw ρ * KLRAlgebra.pol p * KLRAlgebra.e i else 0 := by
    simp only [redIdem, Finset.mul_sum, mul_assoc, KLRAlgebra.e_mul_e, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq]
    simp
  have hL : (redIdem k Q Λ κ' * (KLRAlgebra.ψw ρ * KLRAlgebra.pol p * KLRAlgebra.e i) : R) =
      if redWord (wordProd m ρ • i) = κ' then
        KLRAlgebra.ψw ρ * KLRAlgebra.pol p * KLRAlgebra.e i else 0 := by
    have he : ∀ j : Seq μ, (KLRAlgebra.e j * (KLRAlgebra.ψw ρ * KLRAlgebra.pol p *
        KLRAlgebra.e i) : R) = if j = wordProd m ρ • i then
          KLRAlgebra.ψw ρ * KLRAlgebra.pol p * KLRAlgebra.e i else 0 := by
      intro j
      rw [← mul_assoc, ← mul_assoc, KLRAlgebra.e_mul_ψw, mul_assoc (KLRAlgebra.ψw ρ),
        (KLRAlgebra.e_commute_pol _ p).eq, mul_assoc, mul_assoc, KLRAlgebra.e_mul_e]
      by_cases hj : j = wordProd m ρ • i
      · subst hj
        simp only [inv_smul_smul, ↓reduceIte, ← mul_assoc]
      · have hj' : (wordProd m ρ)⁻¹ • j ≠ i := fun h => hj (by rw [← h, smul_inv_smul])
        simp only [hj, hj', ↓reduceIte, mul_zero]
    simp only [redIdem, Finset.sum_mul, he]
    rw [Finset.sum_ite_eq']
    simp
  rw [hL]
  split_ifs with h₁ h₂ h₂ <;> simp_all

namespace BraidedStendhalAlgebra

variable (k Q Λ ν) in
/-- **Webster's bimodule `B̃_w`** (arXiv:1309.3796v2, Definitions 6.1–6.3): braided Stendhal
diagrams whose red strands read `κ` at the bottom and `κ'` at the top. For `κ` the order
`λ_1, …, λ_ℓ` and `κ'` its image under `w`, this is the span of the `w`-Stendhal diagrams. -/
noncomputable abbrev cornerSpace (κ' κ : List (Fin ℓ)) :
    Submodule k (BraidedStendhalAlgebra k Q Λ ν) :=
  LinearMap.range (LinearMap.mulLeft k (ofKLR k Q Λ ν (redIdem k Q Λ κ')) ∘ₗ
    LinearMap.mulRight k (ofKLR k Q Λ ν (redIdem k Q Λ κ)))

variable (hQ : KLRSymm Q)
  (ρ : Equiv.Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ)
  (hρ : ∀ w, IsReduced (Multiset.card (stendhalWeight ℓ ν)) (ρ w) ∧
    wordProd (Multiset.card (stendhalWeight ℓ ν)) (ρ w) = w)

/-- **Webster, Proposition 6.4** (arXiv:1309.3796v2): for symmetric `Q` and a choice `ρ` of
reduced words, the diagrams `ψ_{ρ(σ)} x^u e(i)` with no dots on red strands, with the red
strands of `i` reading `κ` and those of `σ • i` reading `κ'`, form a basis of `B̃`. -/
noncomputable def cornerBasis (κ' κ : List (Fin ℓ)) :
    Module.Basis
      {b : BlackIdx (ℓ := ℓ) ν // redWord (b.1.2.1 • b.1.1) = κ' ∧ redWord b.1.1 = κ}
      k (cornerSpace k Q Λ ν κ' κ) := by
  classical
  exact WeightedKLR.basisRangeOfApply (basis hQ ρ hρ) _ _ fun b => by
    have h := redIdem_mul_std (k := k) (Q := Q) (Λ := Λ) κ' κ (ρ b.1.2.1)
      (monomial b.1.2.2 1) b.1.1
    simp only [mul_assoc] at h
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulRight_apply,
      LinearMap.mulLeft_apply, basis_apply, ← map_mul, mul_assoc]
    rw [h, (hρ _).2]
    split_ifs <;> simp

theorem cornerBasis_apply (κ' κ : List (Fin ℓ)) (b) :
    (cornerBasis (Λ := Λ) hQ ρ hρ κ' κ b : BraidedStendhalAlgebra k Q Λ ν) =
      ofKLR k Q Λ ν (KLRAlgebra.ψw (ρ b.1.1.2.1) * KLRAlgebra.pol (monomial b.1.1.2.2 1) *
        KLRAlgebra.e b.1.1.1) := by
  simp [cornerBasis, basis_apply]

end BraidedStendhalAlgebra

end Corner

end Categorification.Stendhal

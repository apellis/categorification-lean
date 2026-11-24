/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.SimpleNilHecke
import Categorification.KLR.Cyclotomic
import Mathlib.Algebra.Category.ModuleCat.Simple

/-!
# The terminal one-colour cyclotomic module

For the single-colour step in Webster, arXiv:1309.3796v2, Proposition 7.2,
the coinvariant action descends to the cyclotomic block of black content equal
to the coroot pairing. Its simple module is the coinvariant module.
At weight two the first dot and crossing satisfy the matrix-unit relations.
-/

noncomputable section

namespace Categorification.KLR.CycKLR

open KLRAlgebra Categorification.NilHecke Polynomial

section CoinvariantAction

variable {I k : Type*} [DecidableEq I] [Field k] {ν : Multiset I} {i : I}
  (same : ∀ j ∈ ν, j = i) (Q : I → I → MvPolynomial (Fin 2) k)

local notation "n" => Multiset.card ν
local notation "powers" => fun _ : I => (Polynomial.X ^ n : Polynomial k)
local notation "R" => CycKLR k Q powers ν

/-- The coinvariant polynomial module of a single colour descends to the
terminal cyclotomic block, when the number of black strands equals the
highest coroot pairing. -/
def terminalCoinvAct : R →ₐ[k] Module.End k (Coinv k n) :=
  CycKLR.lift (klrAct same Q) fun s => by
    by_cases h : 0 < n
    · rw [cycElt_of_pos _ _ s h, map_mul, map_pow, Polynomial.aeval_X,
        map_pow, klrAct_x, ← coinvMul_pow, coinvMul_eq_zero (X_pow_mem_coinvIdeal ⟨0,h⟩),
        zero_mul]
    · simp [cycElt, h]

@[simp] theorem terminalCoinvAct_mk (r : KLRAlgebra k Q ν) :
    terminalCoinvAct same Q (CycKLR.mk k Q powers ν r) = klrAct same Q r :=
  CycKLR.lift_mk _ _ _

/-- The coinvariant module over the saturated one-colour cyclotomic block. -/
def terminalCoinvModule : ModuleCat R := by
  letI : Module R (Coinv k n) := Module.compHom _ (terminalCoinvAct same Q).toRingHom
  exact ModuleCat.of R (Coinv k n)

/-- The terminal cyclotomic action on coinvariants is simple. -/
theorem terminalCoinvModule_simple : CategoryTheory.Simple (terminalCoinvModule same Q) := by
  let _ : Module R (Coinv k n) := Module.compHom _ (terminalCoinvAct same Q).toRingHom
  change CategoryTheory.Simple (ModuleCat.of R (Coinv k n))
  apply simple_iff_isSimpleModule.mpr
  let π := (CycKLR.mk k Q powers ν).toRingHom
  let _ : RingHomSurjective π := ⟨CycKLR.mk_surjective⟩
  let e := KLRRep.of same Q
  let comparison : KLRRep same Q →ₛₗ[π] Coinv k n :=
    { toFun := e.symm
      map_add' := fun x y => map_add e.symm x y
      map_smul' := by
        intro r v
        obtain ⟨x, rfl⟩ := e.surjective v
        change e.symm (r • KLRRep.of same Q x) =
          terminalCoinvAct same Q (CycKLR.mk k Q powers ν r) (e.symm (e x))
        rw [klr_smul_def, terminalCoinvAct_mk]
        exact e.symm_apply_apply _ ▸ rfl }
  exact (comparison.isSimpleModule_iff_of_bijective e.symm.bijective).mp
    (isSimpleModule_klrRep same Q)

end CoinvariantAction

section TwoBlack

variable {k : Type*} [Field k] (Q : Unit → Unit → MvPolynomial (Fin 2) k)

local notation "ν" => Multiset.replicate 2 ()
local notation "powers" => fun _ : Unit => (Polynomial.X ^ 2 : Polynomial k)
local notation "π" => CycKLR.mk k Q powers ν
local notation "R" => CycKLR k Q powers ν
local notation "p" => π (x (⟨0, by decide⟩ : Fin (Multiset.card ν)))
local notation "q" => π (x (⟨1, by decide⟩ : Fin (Multiset.card ν)))
local notation "d" => π (ψ 0)

/-- The weight-two nilHecke relations in a cut follow from the first dot
square, the nilHecke crossing square and slide, and commutation of the dots. -/
theorem terminalTwoBlack_relations_of_first_dot_sq_zero {S : Type*} [Ring S]
    (first second crossing : S) (pp : first*first=0) (dd : crossing*crossing=0) (right : crossing*first-second*crossing=1) (pq : first*second=second*first) :
    first+second=0 ∧ second*second=0 ∧ crossing*first+first*crossing=1 := by
  have dp : crossing*first=second*crossing+1 := (sub_eq_iff_eq_add.mp right).trans (add_comm _ _)
  have sum : first+second= -(second*(second*crossing)) := by
    have h : (0 : S)=second*(second*crossing)+(first+second) := calc
      0 = crossing*(first*first) := by rw [pp, mul_zero]
      _ = (crossing*first)*first := (mul_assoc crossing first first).symm
      _ = second*(second*crossing)+(first+second) := by
        rw [dp, add_mul, one_mul, mul_assoc, dp, mul_add, mul_one]
        abel
    have e := congrArg (fun z : S => z-second*(second*crossing)) h
    abel_nf at e ⊢
    exact e.symm
  have sumD : (first+second)*crossing=0 := by
    calc
      _ = -(second*(second*crossing))*crossing := congrArg (· * crossing) sum
      _ = 0 := by rw [neg_mul, mul_assoc, mul_assoc, dd, mul_zero, mul_zero, neg_zero]
  have comm : (first+second)*second=second*(first+second) := by rw [add_mul, mul_add, pq]
  have sumZero : first+second=0 := calc
    _ = (first+second)*(crossing*first-second*crossing) := by rw [right, mul_one]
    _ = 0 := by rw [mul_sub, ← mul_assoc (first+second) crossing, ← mul_assoc (first+second) second,
      sumD, comm, mul_assoc, sumD, zero_mul, mul_zero, sub_self]
  have qNeg : second = -first := by
    exact (eq_neg_iff_add_eq_zero.mpr (by rw [add_comm, sumZero]))
  exact ⟨sumZero, by rw [qNeg, neg_mul_neg, pp],
    by simpa only [qNeg, neg_mul, sub_neg_eq_add] using right⟩

/-- The two-strand terminal cyclotomic block at weight two satisfies the
rank-two matrix-unit relations in its first dot and crossing. -/
theorem twoBlack_terminal_relations : p*p=0 ∧ d*d=0 ∧ p+q=0 ∧ d*p+p*d=1 := by
  let allSame : ∀ j ∈ ν, j = () := fun j _ => Subsingleton.elim j ()
  let := Seq.uniqueOfForall allSame
  let s : Seq ν := default
  have eOne : (e s : KLRAlgebra k Q ν)=1 :=
    e_eq_one_of_forall allSame Q s
  have hnil := ψ_sq (Q := Q) 0 (by decide) s
  rw [ite_eq_left (Subsingleton.elim _ _), eOne, mul_one] at hnil
  have hRight := dot_cross_right (Q := Q) 0 (by decide) s
  rw [ite_eq_left (Subsingleton.elim _ _), eOne, mul_one] at hRight
  have dd : d*d=0 := by simpa only [map_mul, map_zero] using congrArg π hnil
  have right : d*p-q*d=1 := by
    simpa only [map_sub, map_mul, map_one] using congrArg π hRight
  have hCyc := mk_cycElt (Q := Q) (a := powers) s
  rw [cycElt_of_pos _ _ s (by decide), eOne, mul_one, map_pow,
    Polynomial.aeval_X, map_pow] at hCyc
  have pp : p*p=0 := (pow_two p).symm.trans hCyc
  have pq : p*q=q*p := by
    simpa only [map_mul] using
      (congrArg π (x_mul_x (Q := Q) («ν» := ν) ⟨0, by decide⟩ ⟨1, by decide⟩))

  obtain ⟨hsum, _, hslide⟩ := terminalTwoBlack_relations_of_first_dot_sq_zero p q d pp dd right pq
  exact ⟨pp, dd, hsum, hslide⟩



end TwoBlack

end Categorification.KLR.CycKLR

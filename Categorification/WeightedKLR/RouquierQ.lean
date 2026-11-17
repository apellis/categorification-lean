/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Cartan
import Categorification.WeightedKLR.Deformation
import Categorification.WeightedKLR.KLR.SpacedComparison
import Categorification.KLR.Rouquier.Polynomial
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors

/-!
# Rouquier polynomial conditions for weighted graphs

Webster, arXiv:1209.2463v4, §2.1 and Proposition 2.14, forms the ordinary
crossing polynomial by multiplying the edge polynomials in both directions,
exchanging the variables for the reversed edges. The standing hypotheses
make this a homogeneous Rouquier polynomial with invertible pure-power
coefficients (Rouquier, arXiv:0812.5023v1, §3.2.3, pp. 27–28).

The proof works over every commutative ring, including the constant-polynomial
case. The Cartan datum records the loop-deleted edge multiplicities; no
condition on loops is required for these off-diagonal polynomial statements.
-/

noncomputable section

namespace Categorification.WeightedKLR

open MvPolynomial Finsupp

variable {k : Type*} [CommRing k]

private theorem coeff_mul_single_of_top {P R : MvPolynomial (Fin 2) k} {c d : ℕ}
    (hP : ∀ s ∈ P.support, s 0 ≤ c ∧ (s 0 = c → s = single 0 c))
    (hR : ∀ s ∈ R.support, s 0 ≤ d ∧ (s 0 = d → s = single 0 d)) :
    (P * R).coeff (single 0 (c + d)) = P.coeff (single 0 c) * R.coeff (single 0 d) := by
  rw [single_add]
  apply AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd
  intro s t hs ht he
  obtain ⟨hs0, hst⟩ := hP s hs
  obtain ⟨ht0, htt⟩ := hR t ht
  have he0 := congrArg (fun v : Fin 2 →₀ ℕ => v 0) he
  simp only [Finsupp.add_apply, single_eq_same] at he0
  exact ⟨hst (by omega), htt (by omega)⟩

private theorem mapDomain_swap_swap (d : Fin 2 →₀ ℕ) :
    mapDomain ![(1 : Fin 2), 0] (mapDomain ![(1 : Fin 2), 0] d) = d := by
  rw [← mapDomain_comp]
  have hh : (![(1 : Fin 2), 0] ∘ ![(1 : Fin 2), 0]) = id := by
    funext x; fin_cases x <;> rfl
  rw [hh, mapDomain_id]

private theorem homogeneous_swap {P : MvPolynomial (Fin 2) k} {a b D : ℕ}
    (hP : P.IsWeightedHomogeneous ![a, b] D) :
    (rename (![1, 0] : Fin 2 → Fin 2) P).IsWeightedHomogeneous ![b, a] D := by
  have hinj : Function.Injective (![1, 0] : Fin 2 → Fin 2) := by decide
  intro d hd
  rw [← mapDomain_swap_swap d, coeff_rename_mapDomain _ hinj] at hd
  have hh := hP hd
  have h0 : (mapDomain ![(1 : Fin 2), 0] d) 0 = d 1 := by
    simpa using mapDomain_apply_of_injective hinj d 1
  have h1 : (mapDomain ![(1 : Fin 2), 0] d) 1 = d 0 := by
    simpa using mapDomain_apply_of_injective hinj d 0
  simp only [weight_apply, smul_eq_mul] at hh ⊢
  rw [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two] at hh ⊢
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, h0, h1, add_comm] using hh

private theorem coeff_swap_pure (P : MvPolynomial (Fin 2) k) (i : Fin 2) (n : ℕ) :
    (rename (![1, 0] : Fin 2 → Fin 2) P).coeff (single (![1, 0] i) n) =
      P.coeff (single i n) := by
  have hinj : Function.Injective (![1, 0] : Fin 2 → Fin 2) := by decide
  simpa only [mapDomain_single] using coeff_rename_mapDomain _ hinj P (single i n)

private theorem coeff_swap_zero (P : MvPolynomial (Fin 2) k) (n : ℕ) :
    (rename (![1, 0] : Fin 2 → Fin 2) P).coeff (single 0 n) =
      P.coeff (single 1 n) := by
  simpa using coeff_swap_pure P 1 n

namespace WeightedGraph.IsUnitHomogeneous

/-- Reversing an edge exchanges its two multiplicities and weights. -/
theorem swap {a b c d : ℕ} {P : MvPolynomial (Fin 2) k}
    (hP : IsUnitHomogeneous a b c d P) :
    IsUnitHomogeneous b a d c (rename (![1, 0] : Fin 2 → Fin 2) P) := by
  refine ⟨hP.1.symm, ?_, ?_, ?_⟩
  · simpa only [hP.1] using homogeneous_swap hP.2.1
  · simpa only [Matrix.cons_val_one] using (coeff_swap_pure P 1 d) ▸ hP.2.2.2
  · simpa only [Matrix.cons_val_zero] using (coeff_swap_pure P 0 c) ▸ hP.2.2.1

/-- Products add edge multiplicities and multiply their invertible pure-power
coefficients, as in Webster Proposition 2.14. -/
theorem mul {a b c c' d d' : ℕ} (ha : 0 < a) (hb : 0 < b)
    {P R : MvPolynomial (Fin 2) k}
    (hP : IsUnitHomogeneous a b c c' P) (hR : IsUnitHomogeneous a b d d' R) :
    IsUnitHomogeneous a b (c + d) (c' + d') (P * R) := by
  have htP := hasUnitTop_of_isUnitHomogeneous ha hb hP
  have htR := hasUnitTop_of_isUnitHomogeneous ha hb hR
  have hsP := hasUnitTop_of_isUnitHomogeneous hb ha hP.swap
  have hsR := hasUnitTop_of_isUnitHomogeneous hb ha hR.swap
  refine ⟨by nlinarith [hP.1, hR.1], ?_, ?_, ?_⟩
  · simpa only [Nat.mul_add] using hP.2.1.mul hR.2.1
  · rw [coeff_mul_single_of_top htP.2 htR.2]
    exact hP.2.2.1.mul hR.2.2.1
  · have hh := coeff_mul_single_of_top hsP.2 hsR.2
    rw [← map_mul, coeff_swap_zero, coeff_swap_zero, coeff_swap_zero] at hh
    rw [hh]
    exact hP.2.2.2.mul hR.2.2.2

/-- The empty edge product has multiplicities zero and coefficient one. -/
theorem one (a b : ℕ) : IsUnitHomogeneous a b 0 0 (1 : MvPolynomial (Fin 2) k) := by
  refine ⟨by simp, ?_, ?_, ?_⟩
  · simpa using isWeightedHomogeneous_one k (![a, b] : Fin 2 → ℕ)
  · simp
  · simp

/-- Multiplicities add across any finite family of edge polynomials. -/
theorem prod {α : Type*} (s : Finset α) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (c d : α → ℕ) (P : α → MvPolynomial (Fin 2) k)
    (hP : ∀ e ∈ s, IsUnitHomogeneous a b (c e) (d e) (P e)) :
    IsUnitHomogeneous a b (∑ e ∈ s, c e) (∑ e ∈ s, d e) (∏ e ∈ s, P e) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one (k := k) a b
  | @insert e s he ih =>
      simpa only [Finset.sum_insert he, Finset.prod_insert he] using
        (hP e (Finset.mem_insert_self e s)).mul ha hb
          (ih (fun f hf => hP f (Finset.mem_insert_of_mem hf)))

end WeightedGraph.IsUnitHomogeneous

namespace WeightedGraph.Standing

variable {I 𝕜 : Type*} [DecidableEq I] {Γ : WeightedGraph I 𝕜 k}

private theorem isUnitHomogeneous_edgeProd (hS : Γ.Standing) (i j : I) :
    IsUnitHomogeneous (hS.symm i) (hS.symm j)
      (∑ e, if Γ.head e = i ∧ Γ.tail e = j then hS.edgeMult e else 0)
      (∑ e, if Γ.head e = i ∧ Γ.tail e = j then hS.edgeMultRev e else 0)
      (Γ.edgeProd j i) := by
  classical
  have hh := IsUnitHomogeneous.prod
    (Finset.univ.filter fun e => Γ.tail e = j ∧ Γ.head e = i)
    (hS.symm_pos i) (hS.symm_pos j) hS.edgeMult hS.edgeMultRev Γ.Q
    (fun e he => ?_)
  · simpa only [edgeProd, Finset.sum_filter, and_comm] using hh
  · obtain ⟨-, he⟩ := Finset.mem_filter.1 he
    simpa only [he.1, he.2] using hS.isUnitHomogeneous_Q_rev e

/-- Webster Proposition 2.14: the polynomial obtained by multiplying the edge
polynomials in both directions has the standing homogeneous unit coefficients.
The multiplicities are the sums defining the loop-deleted Cartan datum. -/
theorem isUnitHomogeneous_klrQ (hS : Γ.Standing) (i j : I) :
    IsUnitHomogeneous (hS.symm i) (hS.symm j)
      (hS.rootMultiplicity i j) (hS.rootMultiplicity j i) (Γ.klrQ i j) := by
  classical
  have hh := (hS.isUnitHomogeneous_edgeProd i j).mul
    (hS.symm_pos i) (hS.symm_pos j) (hS.isUnitHomogeneous_edgeProd j i).swap
  simpa only [klrQ, rootMultiplicity, and_comm, add_comm] using hh

/-- The crossing polynomials in Webster Proposition 2.14 satisfy Rouquier's
homogeneous polynomial hypotheses (arXiv:0812.5023v1, §3.2.3, pp. 27–28).
This holds over every commutative coefficient ring, including Cartan exponent
zero, where the polynomial is one invertible constant. -/
theorem isRouquierQ (hS : Γ.Standing) : KLR.IsRouquierQ hS.cartanDatum Γ.klrQ := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro i j _
    have hflip : (![1, 0] : Fin 2 → Fin 2) ∘ ![1, 0] = id := by
      funext a; fin_cases a <;> rfl
    simp only [klrQ, map_mul, rename_rename, hflip, rename_id]
    exact mul_comm _ _
  · intro i j hij
    have hh := isWeightedHomogeneous_intCast_mul
      (hS.isUnitHomogeneous_klrQ i j).2.1 2
    convert hh using 1
    · rw [hS.cartanDatum_dot_self i, hS.cartanDatum_dot_self j]
      funext a
      fin_cases a <;> rfl
    · rw [hS.cartanDatum_dot_of_ne hij]
      push_cast
      ring
  · intro i j hij
    rw [hS.cartanDatum_dij hij]
    exact (hS.isUnitHomogeneous_klrQ i j).2.2.1

end WeightedGraph.Standing

end Categorification.WeightedKLR

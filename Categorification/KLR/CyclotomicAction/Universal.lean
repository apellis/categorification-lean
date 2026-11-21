/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.PresCL
import Categorification.KLR.Rouquier.PolynomialDegree

/-!
# The universal cyclotomic quotient `Ř^λ`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §3.4,
**Definition 3.24** (the algebra `Ř^λ`) and the action part of **Proposition 3.25**.

Webster defines `Ř^λ` as the quotient of `End_𝒰(⊕_𝐢 F_𝐢 λ) ≅ R ⊗ Λ`, where `Λ` is a tensor product
of rings of symmetric functions in alphabets `p_j`, by the relations

* `e(𝐢) (y_1^{λ^{i_1}} - e_1(p_{i_1}) y_1^{λ^{i_1} - 1} + ⋯ + (-1)^{λ^{i_1}} e_{λ^{i_1}}(p_{i_1})) = 0`,
* `e_n(p_j) = 0` for `n > λ^j`,

with `λ^j = ⟨α_j^∨, λ⟩`. The second family of relations replaces `Λ` by the polynomial ring
`Ř^λ_λ = k[e_n(p_j) | j ∈ I, 1 ≤ n ≤ λ^j]`, and the first is the cyclotomic relation for the monic
polynomials `a_j(y) = y^{λ^j} - e_1(p_j) y^{λ^j - 1} + ⋯ + (-1)^{λ^j} e_{λ^j}(p_j)` over that ring.
So `Ř^λ` is the cyclotomic quotient of the KLR algebra over `Ř^λ_λ` with these universal
cyclotomic polynomials; this is Webster's algebraic form of the definition, and it is how it is
defined here:

* `UnivCycRing k lam`: the polynomial ring `Ř^λ_λ`, with variable `⟨j, n⟩` standing for
  `e_{n+1}(p_j)`;
* `univCycPoly k lam j`: the polynomial `a_j`, monic of degree `λ^j` (`univCycPoly_monic`,
  `univCycPoly_natDegree`);
* `cycQ k lam Q`: the KLR polynomials `Q_ij` with coefficients in `Ř^λ_λ`;
* `UnivCyc k lam Q ν`: the algebra `Ř^λ_ν`.

Specializing every `e_n(p_j)` to `0` recovers `R^λ`, as Webster notes after the definition.

**Proposition 3.25, the action.** Since `a_j` is monic of degree `λ^j`, the Kang–Kashiwara
action of Theorem 3.17 applies over the base ring `Ř^λ_λ` (Kang–Kashiwara allow any commutative
base ring), and the Cautis–Lauda presentation acts on the weight spaces of `Ř^λ`
(`univCyclotomicPresCL`), with `E_i`, `F_i` acting by cyclotomic restriction and induction. The
presentation is the one over `Ř^λ_λ`, so the action is `Ř^λ_λ`-linear. Webster's Morita
comparison of `Ř^λ` with `End_𝒰(F_𝐢 λ)` modulo the maps factoring through some `F_𝐣 E_j` is a
step of his route, not formalized separately (as for Propositions 3.13 and 3.16).
-/

namespace Categorification.KLR.CyclotomicAction

open Polynomial QuantumGroup

universe u v w u₁

noncomputable section

variable {I : Type u} [DecidableEq I] (k : Type v) [CommRing k] (lam : I → ℕ)

/-- **The ring `Ř^λ_λ`** (Webster, arXiv:1309.3796v2, Definition 3.24): the polynomial ring over
`k` in the elementary symmetric functions `e_n(p_j)`, `j ∈ I`, `1 ≤ n ≤ λ^j`. The variable
`⟨j, n⟩` stands for `e_{n+1}(p_j)`. -/
abbrev UnivCycRing : Type (max u v) := MvPolynomial (Σ j : I, Fin (lam j)) k

/-- The terms of `univCycPoly` below the leading one:
`∑_{n=1}^{λ^j} (-1)^n e_n(p_j) y^{λ^j - n}`. -/
def univCycTail (j : I) : (UnivCycRing k lam)[X] :=
  ∑ n : Fin (lam j), C ((-1) ^ (n.val + 1) *
    (MvPolynomial.X (⟨j, n⟩ : Σ j : I, Fin (lam j)) : UnivCycRing k lam)) *
      X ^ (lam j - (n.val + 1))

/-- **The universal cyclotomic polynomial** at `j`:
`y^{λ^j} - e_1(p_j) y^{λ^j - 1} + ⋯ + (-1)^{λ^j} e_{λ^j}(p_j)`. -/
def univCycPoly (j : I) : (UnivCycRing k lam)[X] :=
  X ^ lam j + univCycTail k lam j

omit [DecidableEq I] in
theorem univCycTail_degree_lt (j : I) : (univCycTail k lam j).degree < lam j := by
  unfold univCycTail
  refine (degree_sum_le _ _).trans_lt ?_
  refine (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun n _ => ?_
  refine (degree_C_mul_X_pow_le _ _).trans_lt ?_
  exact WithBot.coe_lt_coe.2 (Nat.sub_lt (by have := n.isLt; omega) n.val.succ_pos)

omit [DecidableEq I] in
theorem univCycPoly_monic (j : I) : (univCycPoly k lam j).Monic :=
  monic_X_pow_add (univCycTail_degree_lt k lam j)

omit [DecidableEq I] in
theorem univCycPoly_natDegree [Nontrivial k] (j : I) :
    (univCycPoly k lam j).natDegree = lam j := by
  unfold univCycPoly
  rw [natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  rw [degree_X_pow]
  exact univCycTail_degree_lt k lam j

/-- The KLR polynomials `Q_ij` with coefficients in `Ř^λ_λ`. -/
def cycQ (Q : I → I → MvPolynomial (Fin 2) k) (i j : I) :
    MvPolynomial (Fin 2) (UnivCycRing k lam) :=
  MvPolynomial.map (algebraMap k (UnivCycRing k lam)) (Q i j)

/-- **The universal cyclotomic quotient `Ř^λ_ν`** (Webster, arXiv:1309.3796v2,
Definition 3.24): the KLR algebra over `Ř^λ_λ` modulo the cyclotomic relations for the universal
polynomials `univCycPoly`. -/
abbrev UnivCyc (Q : I → I → MvPolynomial (Fin 2) k) (ν : Multiset I) : Type _ :=
  CycKLR (UnivCycRing k lam) (cycQ k lam Q) (univCycPoly k lam) ν

variable {k lam}

omit [DecidableEq I] in
/-- Rouquier's conditions on `Q` survive the extension of scalars to `Ř^λ_λ`. -/
theorem _root_.Categorification.KLR.IsRouquierQ.cycQ {C : CartanDatum I} {Q : I → I → MvPolynomial (Fin 2) k}
    (hQ : IsRouquierQ C Q) : IsRouquierQ C (cycQ k lam Q) where
  symm i j hij := by
    simp only [CyclotomicAction.cycQ]
    rw [← MvPolynomial.map_rename, hQ.symm i j hij]
  homogeneous i j hij := by
    intro d hd
    refine hQ.homogeneous i j hij ?_
    intro h0
    apply hd
    simp only [CyclotomicAction.cycQ, MvPolynomial.coeff_map, h0, map_zero]
  unit_coeff i j hij := by
    simp only [CyclotomicAction.cycQ, MvPolynomial.coeff_map]
    exact (hQ.unit_coeff i j hij).map _

variable {C : CartanDatum I} {Q : I → I → MvPolynomial (Fin 2) k} (hQ : IsRouquierQ C Q)
  {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y] (RD : UDot.WeightDatum C X Y) (Λ : X)
  (hΛ : ∀ i, (lam i : ℤ) = RD.pair (RD.iY i) Λ)

omit [DecidableEq I] in
include hΛ in
theorem univCycPoly_natDegree_pair [Nontrivial k] (i : I) :
    ((univCycPoly k lam i).natDegree : ℤ) = RD.pair (RD.iY i) Λ := by
  rw [univCycPoly_natDegree, hΛ]

/-- **The Cautis–Lauda presentation acts on the universal cyclotomic quotients**
(Webster, arXiv:1309.3796v2, Proposition 3.25, the action: "the category of `Ř^λ` modules carries a
natural action of `𝒰`"), for `Q` of Webster's form over a nontrivial commutative ring `k`: the
weight spaces are the categories of `Ř^λ_ν`-modules, and `E_i`, `F_i` act by cyclotomic
restriction and induction. The presentation is over `Ř^λ_λ` (`cycQ`), so the action is
`Ř^λ_λ`-linear. This is Theorem 3.17 (`cyclotomicPresCL`) over the base ring `Ř^λ_λ` with the
universal cyclotomic polynomials. -/
def univCyclotomicPresCL [Nontrivial k] :=
  cyclotomicPresCL.{u, max u v, w} hQ.cycQ.klrSymm hQ.cycQ.polyInY_leading
    (univCycPoly_monic k lam) RD Λ (univCycPoly_natDegree_pair RD Λ hΛ)
    (fun i j hji => hQ.cycQ.polyInY_degree_pair RD i j hji) hQ.cycQ.homogeneous

end

end Categorification.KLR.CyclotomicAction

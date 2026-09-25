/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.BasisTheorem
import Categorification.KLR.KL1

/-!
# KL I, Theorem 2.5 and Corollary 2.6

The basis theorem and faithfulness of the polynomial representation for the rings `R(ν)`
of KL I (arXiv:0803.4121v2, §2.3), attached to a simple graph `Γ`, over `ℤ` as in the paper
(and more generally over any integral domain).

* `KL1.cornerBasis` : **Theorem 2.5.** For any choice of minimal presentations `ρ w` of the
  permutations `w ∈ S_m`, `_jR(ν)_i` is free with basis `_jB_i = {ψ_{ρ w} x^u e_i}` over
  `w ∈ S_m` with `w • i = j` and `u ∈ ℕ^m`.
* `KL1.polyRepKL1_injective` : **Corollary 2.6.** `Pol_ν` is a faithful `R(ν)`-module, for
  every orientation of `Γ`.

Homogeneity of the basis elements for the grading of KL I is
`ψw_mul_pol_monomial_mul_e_mem_grade` (`Categorification.KLR.Grading`).
-/

namespace Categorification.KLR.KL1

open Equiv MvPolynomial TypeA KLRAlgebra

variable {I : Type*} [DecidableEq I] {Γ : SimpleGraph I} [DecidableRel Γ.Adj]
  {k : Type*} [CommRing k] [IsDomain k] {ν : Multiset I}

omit [DecidableEq I] [IsDomain k] in
theorem klP_ne_zero [Nontrivial k] (o : I → I → Prop) [DecidableRel o] (a b : I) :
    (klP Γ o a b : MvPolynomial (Fin 2) k) ≠ 0 := by
  unfold klP
  split_ifs
  · intro h
    have := congrArg (MvPolynomial.coeff (Finsupp.single 0 1)) h
    simp [MvPolynomial.coeff_X', Finsupp.single_eq_single_iff] at this
  · exact one_ne_zero

/-- A canonical orientation of `Γ`: orient each edge along an (arbitrary) well-order of `I`. -/
noncomputable def stdOrient : I → I → Prop := WellOrderingRel

noncomputable instance : DecidableRel (stdOrient (I := I)) := Classical.decRel _

omit [DecidableEq I] [DecidableRel Γ.Adj] in
theorem stdOrient_spec : ∀ a b, Γ.Adj a b → (stdOrient a b ↔ ¬ stdOrient b a) := by
  intro a b hab
  have hne : a ≠ b := Γ.ne_of_adj hab
  constructor
  · intro h h'; exact asymm (r := WellOrderingRel) h h'
  · intro h
    rcases (WellOrderingRel.isWellOrder (α := I)).trichotomous a b with h1 | h1 | h1
    · exact h1
    · exact absurd h1 hne
    · exact absurd h1 h

variable (ρ : Perm (Fin (Multiset.card ν)) → List ℕ)
  (hρ : ∀ w, IsReduced (Multiset.card ν) (ρ w) ∧ wordProd (Multiset.card ν) (ρ w) = w)

/-- **KL I, Theorem 2.5.** For any choice `ρ` of minimal presentations of permutations,
`_jR(ν)_i` is a free module with basis `ψ_{ρ w} x^u e_i` (`w • i = j`, `u ∈ ℕ^m`). Over `ℤ`
this is the statement of the paper; it holds over any integral domain. -/
noncomputable def cornerBasis (j i : Seq ν) :
    Basis (CornerIdx j i) k (corner (Q := klQ (k := k) Γ) j i) :=
  KLRAlgebra.cornerBasis (klQ_eq_klP (Γ := Γ) stdOrient_spec) (fun a b _ => klP_ne_zero _ a b)
    ρ hρ j i

theorem cornerBasis_apply (j i : Seq ν) (b : CornerIdx j i) :
    (KL1.cornerBasis (k := k) (Γ := Γ) ρ hρ j i b : R1 k Γ ν) =
      ψw (ρ b.1.1) * pol (monomial b.2 1) * e i :=
  KLRAlgebra.cornerBasis_apply _ _ ρ hρ j i b

/-- The whole ring `R(ν)` has basis `ψ_{ρ w} x^u e_i` (all `i, w, u`). -/
noncomputable def basis :
    Basis (Seq ν × Perm (Fin (Multiset.card ν)) × (Fin (Multiset.card ν) →₀ ℕ)) k (R1 k Γ ν) :=
  KLRAlgebra.basis (klQ_eq_klP (Γ := Γ) stdOrient_spec) (fun a b _ => klP_ne_zero _ a b) ρ hρ

/-- **KL I, Corollary 2.6.** For every orientation of `Γ`, `Pol_ν` is a faithful
`R(ν)`-module. -/
theorem polyRepKL1_injective (o : I → I → Prop) [DecidableRel o]
    (ho : ∀ a b, Γ.Adj a b → (o a b ↔ ¬ o b a)) :
    Function.Injective (polyRepKL1 (k := k) ho ν) :=
  polyRep_injective _ (fun a b _ => klP_ne_zero o a b)

end Categorification.KLR.KL1

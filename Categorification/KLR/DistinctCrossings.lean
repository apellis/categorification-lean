/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Filtration
import Categorification.TypeA.WeakOrder

/-!
# Words of crossings between strands of different labels

In a KLR algebra `R(ν)`, a dot slides through a crossing of two strands with different labels,
and such a crossing squares to a polynomial in the dots (Khovanov–Lauda, *A diagrammatic
approach to categorification of quantum groups I*, arXiv:0803.4121v2, relations (2.4)–(2.6);
Rouquier, arXiv:0812.5023v1, §3.2.1). Hence, for a word `ρ` of crossings each of which joins
two strands of different labels at the idempotent `e(i)`:

* polynomials slide through `ψ_ρ e(i)` with relabelling, `f ψ_ρ e(i) = ψ_ρ (w⁻¹ f) e(i)`
  (`pol_mul_ψw_mul_e`), and
* `ψ_{ρ^{rev}} ψ_ρ e(i)` is a polynomial in the dots times `e(i)`
  (`exists_ψw_reverse_mul_ψw_mul_e`).

A reduced word only crosses pairs of strands that are inverted by the permutation it represents
(`TypeA.IsReduced.crossing_mem_invSet`), so the hypothesis holds for a reduced word whose
inversions all join strands of different labels (`crossesDistinct_of_isReduced`). This is the
computation behind the element `y = θ̇ θ` of the half twist in Webster, *Knot invariants and
higher representation theory*, arXiv:1309.3796v3, proof of Theorem 6.14.

## Main results

* `TypeA.IsReduced.crossing_mem_invSet`: each crossing of a reduced word is an inversion.
* `KLRAlgebra.CrossesDistinct`: every crossing of `ρ` on `e(i)` joins different labels.
* `KLRAlgebra.pol_mul_ψw_mul_e`, `KLRAlgebra.exists_ψw_reverse_mul_ψw_mul_e`.
* `KLRAlgebra.crossesDistinct_of_isReduced`.
-/

namespace Categorification

open Equiv MvPolynomial

namespace TypeA

variable {m : ℕ}

/-- **Crossings of a reduced word are inversions.** In a reduced word `α ++ j :: σ`, the
crossing `j` joins the strands that start at the positions `u⁻¹ j < u⁻¹ (j + 1)`,
`u = wordProd σ`, and this pair is an inversion of the whole word. -/
theorem IsReduced.crossing_mem_invSet {α σ : List ℕ} {j : ℕ} (hr : IsReduced m (α ++ j :: σ))
    (hj : j + 1 < m) :
    (wordProd m σ)⁻¹ ⟨j, by omega⟩ < (wordProd m σ)⁻¹ ⟨j + 1, hj⟩ ∧
      ((wordProd m σ)⁻¹ ⟨j, by omega⟩, (wordProd m σ)⁻¹ ⟨j + 1, hj⟩) ∈
        invSet m (wordProd m (α ++ j :: σ)) := by
  have hv := hr.validWord
  rw [validWord_append, validWord_cons] at hv
  obtain ⟨hvα, -, hvσ⟩ := hv
  set u := wordProd m σ
  set a := wordProd m α
  have hw : wordProd m (α ++ j :: σ) = a * (sadj m j * u) := by simp [u, a]
  have hl := hr.length_eq
  rw [hw] at hl
  simp only [List.length_append, List.length_cons] at hl
  have h1 : length m a ≤ α.length := length_wordProd_le hvα
  have h2 : length m u ≤ σ.length := length_wordProd_le hvσ
  have h3 := length_mul_le a (sadj m j * u)
  have h4 := length_sadj_mul_le j u
  have hlt : u⁻¹ ⟨j, by omega⟩ < u⁻¹ ⟨j + 1, hj⟩ := by
    by_contra hc
    have hgt : u⁻¹ ⟨j + 1, hj⟩ < u⁻¹ ⟨j, by omega⟩ :=
      lt_of_le_of_ne (not_lt.1 hc) (u⁻¹.injective.ne (by simp [Fin.ext_iff]))
    have := length_sadj_mul_of_gt hj hgt
    omega
  refine ⟨hlt, ?_⟩
  rw [hw]
  refine invSet_subset_of_length_add (by omega) ?_
  rw [invSet_sadj_mul_of_lt hj hlt]
  exact Finset.mem_insert_self _ _

end TypeA

namespace KLR

variable {I : Type*} {k : Type*} [CommRing k] [DecidableEq I]

namespace KLRAlgebra

open TypeA

variable {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}

local notation "m" => Multiset.card ν

/-- A dot slides through a crossing of strands with different labels:
`x_p ψ_j e(i) = ψ_j x_{s_j p} e(i)` when `i_j ≠ i_{j+1}`. -/
theorem x_mul_ψ_mul_e_of_ne (p : Fin m) (j : ℕ) (i : Seq ν)
    (hne : ∀ h : j + 1 < m, i.lbl ⟨j, by omega⟩ ≠ i.lbl ⟨j + 1, h⟩) :
    (x p * ψ j * e i : KLRAlgebra k Q ν) = ψ j * x (sadj m j p) * e i := by
  by_cases h : j + 1 < m
  · by_cases hp : p.val = j
    · rcases p with ⟨p, hp0⟩
      simp only at hp
      subst hp
      rw [sadj_apply_left h]
      have := dot_cross_left (k := k) (Q := Q) p h i
      rw [ite_eq_right (hne h), sub_mul, sub_eq_zero] at this
      exact this
    by_cases hp' : p.val = j + 1
    · rcases p with ⟨p, hp0⟩
      simp only at hp'
      subst hp'
      rw [sadj_apply_right h]
      have := dot_cross_right (k := k) (Q := Q) j h i
      rw [ite_eq_right (hne h), sub_mul, sub_eq_zero] at this
      exact this.symm
    · rw [sadj_apply_of_ne p hp hp', x_mul_ψ p j hp hp']
  · simp [ψ_eq_zero (k := k) (Q := Q) (ν := ν) j (by omega)]

/-- Polynomials slide through a crossing of strands with different labels:
`f ψ_j e(i) = ψ_j (s_j f) e(i)` when `i_j ≠ i_{j+1}`. -/
theorem pol_mul_ψ_mul_e_of_ne (f : MvPolynomial (Fin m) k) (j : ℕ) (i : Seq ν)
    (hne : ∀ h : j + 1 < m, i.lbl ⟨j, by omega⟩ ≠ i.lbl ⟨j + 1, h⟩) :
    (pol f * ψ j * e i : KLRAlgebra k Q ν) = ψ j * pol (rename (sadj m j) f) * e i := by
  induction f using MvPolynomial.induction_on with
  | C c => rw [algHom_C, rename_C, algHom_C, Algebra.commutes]
  | add f g hf hg => rw [map_add, add_mul, add_mul, hf, hg, map_add, map_add, mul_add, add_mul]
  | mul_X f p hf =>
    rw [map_mul, pol_X, mul_assoc, mul_assoc, ← mul_assoc (x p), x_mul_ψ_mul_e_of_ne p j i hne,
      mul_assoc, x_mul_e]
    simp only [← mul_assoc]
    rw [hf, map_mul, rename_X, map_mul, pol_X]
    simp only [mul_assoc, x_mul_e]

/-- Every crossing of the word `ρ`, applied to `e(i)` from the bottom, joins two strands with
different labels. -/
def CrossesDistinct : List ℕ → Seq ν → Prop
  | [], _ => True
  | j :: σ, i => (∀ h : j + 1 < m, (wordProd m σ • i).lbl ⟨j, by omega⟩ ≠
      (wordProd m σ • i).lbl ⟨j + 1, h⟩) ∧ CrossesDistinct σ i

/-- Polynomials slide through a word of crossings of strands with different labels:
`f ψ_ρ e(i) = ψ_ρ (w⁻¹ f) e(i)`, `w = wordProd ρ`. -/
theorem pol_mul_ψw_mul_e (f : MvPolynomial (Fin m) k) {ρ : List ℕ} {i : Seq ν}
    (hρ : CrossesDistinct ρ i) :
    (pol f * ψw ρ * e i : KLRAlgebra k Q ν) =
      ψw ρ * pol (rename ⇑(wordProd m ρ)⁻¹ f) * e i := by
  induction ρ generalizing f with
  | nil => simp
  | cons j σ ih =>
    obtain ⟨hj, hσ⟩ := hρ
    rw [ψw_cons, ← mul_assoc, mul_assoc, ψw_mul_e, ← mul_assoc, pol_mul_ψ_mul_e_of_ne f j _ hj,
      mul_assoc, mul_assoc, ← ψw_mul_e, ← mul_assoc (pol _), ih _ hσ, rename_rename,
      wordProd_cons, mul_inv_rev, sadj_inv, Perm.coe_mul]
    simp only [mul_assoc]

/-- `ψ_{ρ^{rev}} ψ_ρ e(i)` is a polynomial in the dots times `e(i)` when every crossing of `ρ`
joins strands with different labels. -/
theorem exists_ψw_reverse_mul_ψw_mul_e {ρ : List ℕ} {i : Seq ν} (hρ : CrossesDistinct ρ i) :
    ∃ f : MvPolynomial (Fin m) k, (ψw ρ.reverse * ψw ρ * e i : KLRAlgebra k Q ν) = pol f * e i := by
  induction ρ with
  | nil => exact ⟨1, by simp⟩
  | cons j σ ih =>
    obtain ⟨hj, hσ⟩ := hρ
    obtain ⟨f, hf⟩ := ih hσ
    by_cases h : j + 1 < m
    · have hsq := ψ_sq (k := k) (Q := Q) j h (wordProd m σ • i)
      rw [ite_eq_right (hj h), ncEval_x₂] at hsq
      set g := rename ![(⟨j, by omega⟩ : Fin m), ⟨j + 1, h⟩]
        (Q ((wordProd m σ • i).lbl ⟨j, by omega⟩) ((wordProd m σ • i).lbl ⟨j + 1, h⟩))
      refine ⟨f * rename ⇑(wordProd m σ)⁻¹ g, ?_⟩
      calc (ψw (j :: σ).reverse * ψw (j :: σ) * e i : KLRAlgebra k Q ν)
          = ψw σ.reverse * (ψ j * ψ j * e (wordProd m σ • i)) * ψw σ := by
            rw [List.reverse_cons, ψw_append, ψw_cons, ψw_cons, ψw_nil, mul_one]
            simp only [mul_assoc]
            rw [ψw_mul_e]
        _ = ψw σ.reverse * (pol g * ψw σ * e i) := by
            rw [hsq]; simp only [mul_assoc]; rw [ψw_mul_e]
        _ = ψw σ.reverse * ψw σ * e i * pol (rename ⇑(wordProd m σ)⁻¹ g) := by
            rw [pol_mul_ψw_mul_e g hσ, mul_assoc (ψw σ), ← (e_commute_pol i _).eq]
            simp only [mul_assoc]
        _ = pol (f * rename ⇑(wordProd m σ)⁻¹ g) * e i := by
            rw [hf, map_mul, mul_assoc, (e_commute_pol i _).eq, mul_assoc]
    · refine ⟨0, ?_⟩
      rw [ψw_cons, ψ_eq_zero j (by omega), zero_mul, mul_zero, zero_mul, map_zero, zero_mul]

omit [DecidableEq I] in
/-- A reduced word crosses only pairs of strands inverted by its permutation, so it satisfies
`CrossesDistinct` at `e(i)` when every inversion joins two different labels of `i`. -/
theorem crossesDistinct_of_isReduced {ρ : List ℕ} (hr : IsReduced m ρ) (i : Seq ν)
    (hi : ∀ p ∈ invSet m (wordProd m ρ), i.lbl p.1 ≠ i.lbl p.2) : CrossesDistinct ρ i := by
  suffices ∀ σ α : List ℕ, ρ = α ++ σ → CrossesDistinct σ i from this ρ [] rfl
  intro σ
  induction σ with
  | nil => intro _ _; trivial
  | cons j σ ih =>
    intro α hα
    refine ⟨fun h => ?_, ih (α ++ [j]) (by simp [hα])⟩
    subst hα
    obtain ⟨-, hmem⟩ := hr.crossing_mem_invSet h
    exact hi _ hmem
end KLRAlgebra

end KLR

end Categorification

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.StendhalBasisSymm
import Categorification.KLR.InductionFree

/-!
# The basis of `T̃^λ` with dots on top

Webster, arXiv:1309.3796v3, Proposition 4.16, in the form with the dots at the top of the
diagrams: for symmetric `Q`, over every commutative ring, the images `x^u ψ_{ρ w} e(i)` of the
terms of the KLR basis with dots on top (`KLRAlgebra.lbasis`, KL I, Theorem 2.5) that survive in
`T̃^λ` form a basis. A term survives when `i` and `w • i` have their red strands in order, no dot
sits on a red strand of the top `w • i`, and `ρ w` exchanges no two red strands
(`IsTopTerm`). This is the form used for the left module structure of a corner `e T̃^{λ⁺}` in
the proof of Lemma 7.17.

## Main results

* `ro_mul_ofKLR_topElt_mul_ro`: cutting a term by the idempotent of `T̃^λ`.
* `topBasis`: the basis.
-/

set_option backward.isDefEq.respectTransparency false

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace Categorification.Stendhal

open MvPolynomial KLR TypeA Equiv StendhalAlgebraAllOrders

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "R" => KLR.KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)

variable (ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ)

/-- The terms `x^u ψ_{ρ w} e(i)` of the KLR basis with dots on top that survive in `T̃^λ`: `i`
and `w • i` have their red strands in order, `u` puts no dot on a red strand of `w • i`, and
`ρ w` exchanges no two red strands. -/
def IsTopTerm (b : KLR.Seq μ × Perm (Fin m) × (Fin m →₀ ℕ)) : Prop :=
  IsRedOrdered b.1 ∧ IsRedOrdered (b.2.1 • b.1) ∧
    (∀ a ∈ b.2.2.support, ((b.2.1 • b.1).1 a).isLeft) ∧ NoRedCross (ρ b.2.1) b.1

/-- The term `x^u ψ_{ρ w} e(i)` of the KLR algebra. -/
noncomputable def topElt (b : KLR.Seq μ × Perm (Fin m) × (Fin m →₀ ℕ)) : R :=
  KLRAlgebra.pol (monomial b.2.2 1) * KLRAlgebra.ψw (ρ b.2.1) * KLRAlgebra.e b.1

variable {ρ}

theorem topElt_mul_e (b : KLR.Seq μ × Perm (Fin m) × (Fin m →₀ ℕ)) :
    topElt ρ b * KLRAlgebra.e b.1 = topElt (Q := Q) (Λ := Λ) ρ b := by
  rw [topElt, mul_assoc, KLRAlgebra.e_mul_self]

theorem e_mul_topElt (hρ : ∀ w, wordProd m (ρ w) = w)
    (b : KLR.Seq μ × Perm (Fin m) × (Fin m →₀ ℕ)) :
    KLRAlgebra.e (b.2.1 • b.1) * topElt ρ b = topElt (Q := Q) (Λ := Λ) ρ b := by
  have h := KLRAlgebra.e_mul_pol_ψw_e (Q := stendhalQ Q Λ) (monomial b.2.2 (1 : k))
    (ρ b.2.1) b.1
  rw [hρ] at h
  exact h

theorem topElt_eq_pol_e_mul (hρ : ∀ w, wordProd m (ρ w) = w)
    (b : KLR.Seq μ × Perm (Fin m) × (Fin m →₀ ℕ)) :
    topElt (Q := Q) (Λ := Λ) ρ b =
      KLRAlgebra.pol (monomial b.2.2 1) * KLRAlgebra.e (b.2.1 • b.1) *
        (KLRAlgebra.ψw (ρ b.2.1) * KLRAlgebra.e b.1) := by
  conv_lhs => rw [← e_mul_topElt hρ b]
  rw [topElt, ← mul_assoc, ← mul_assoc, ← (KLRAlgebra.e_commute_pol _ _).eq, mul_assoc,
    mul_assoc]

open Classical in
/-- **Cutting a term by the idempotent of `T̃^λ`**: `x^u ψ_{ρ w} e(i)` survives exactly when it
is a term with dots on top. -/
theorem ro_mul_ofKLR_topElt_mul_ro (hρ : ∀ w, wordProd m (ρ w) = w)
    (b : KLR.Seq μ × Perm (Fin m) × (Fin m →₀ ℕ)) :
    redOrderedIdem k Q Λ ν * ofKLR k Q Λ ν (topElt ρ b) * redOrderedIdem k Q Λ ν =
      if IsTopTerm ρ b then ofKLR k Q Λ ν (topElt ρ b) else 0 := by
  set y := ofKLR k Q Λ ν (topElt ρ b)
  have hr : y * redOrderedIdem k Q Λ ν = if IsRedOrdered b.1 then y else 0 := by
    have hy : y = y * e b.1 := by
      change _ = ofKLR k Q Λ ν _ * ofKLR k Q Λ ν _
      rw [← map_mul, topElt_mul_e]
    calc y * redOrderedIdem k Q Λ ν = y * (e b.1 * redOrderedIdem k Q Λ ν) := by
          rw [← mul_assoc, ← hy]
      _ = _ := by rw [e_mul_redOrderedIdem]; split_ifs <;> simp [← hy]
  have hl : redOrderedIdem k Q Λ ν * y = if IsRedOrdered (b.2.1 • b.1) then y else 0 := by
    have hy : y = e (b.2.1 • b.1) * y := by
      change _ = ofKLR k Q Λ ν _ * ofKLR k Q Λ ν _
      rw [← map_mul, e_mul_topElt hρ]
    calc redOrderedIdem k Q Λ ν * y = redOrderedIdem k Q Λ ν * e (b.2.1 • b.1) * y := by
          rw [mul_assoc, ← hy]
      _ = _ := by rw [redOrderedIdem_mul_e]; split_ifs <;> simp [← hy]
  rw [hl]
  by_cases h₁ : IsRedOrdered (b.2.1 • b.1)
  · simp only [h₁, ↓reduceIte, hr]
    by_cases h₂ : IsRedOrdered b.1
    · simp only [h₂, ↓reduceIte]
      by_cases h₃ : ∀ a ∈ b.2.2.support, ((b.2.1 • b.1).1 a).isLeft
      · by_cases h₄ : NoRedCross (ρ b.2.1) b.1
        · have ht : IsTopTerm ρ b := ⟨h₂, h₁, h₃, h₄⟩
          simp only [ht, ↓reduceIte]
        · have ht : ¬ IsTopTerm ρ b := fun h => h₄ h.2.2.2
          have hy : y = 0 := by
            simp only [y]
            rw [topElt_eq_pol_e_mul hρ, map_mul, ofKLR_ψw_mul_e_of_not_noRedCross _ _ h₄,
              mul_zero]
          simp only [ht, ↓reduceIte, hy]
      · have ht : ¬ IsTopTerm ρ b := fun h => h₃ h.2.2.1
        push Not at h₃
        obtain ⟨a, ha, har⟩ := h₃
        have hy : y = 0 := by
          simp only [y]
          rw [topElt_eq_pol_e_mul hρ, map_mul,
            ofKLR_pol_mul_e_of_red _ _ ha (by simpa using har), zero_mul]
        simp only [ht, ↓reduceIte, hy]
    · have ht : ¬ IsTopTerm ρ b := fun h => h₂ h.1
      simp only [h₂, ht, ↓reduceIte]
  · have ht : ¬ IsTopTerm ρ b := fun h => h₁ h.2.1
    simp only [h₁, ht, ↓reduceIte, zero_mul]

variable (Q Λ) in
/-- The term `x^u ψ_{ρ w} e(i)` (`IsTopTerm`) as an element of `T̃^λ`. -/
noncomputable def topTerm (hρ : ∀ w, wordProd m (ρ w) = w) (b : {b // IsTopTerm ρ b}) :
    StendhalAlgebra k Q Λ ν :=
  ⟨ofKLR k Q Λ ν (topElt ρ b.1), _,
    (ro_mul_ofKLR_topElt_mul_ro hρ b.1).trans (ite_eq_left_of_eq_true _ _ (eq_true b.2))⟩

theorem topTerm_val (hρ : ∀ w, wordProd m (ρ w) = w) (b : {b // IsTopTerm ρ b}) :
    (topTerm Q Λ hρ b).1 = ofKLR k Q Λ ν (topElt ρ b.1) :=
  rfl

/-- `toKLR` sends each term with dots on top to the same element of the KLR algebra. -/
theorem toKLR_topTerm (hρ : ∀ w, wordProd m (ρ w) = w) (b : {b // IsTopTerm ρ b}) :
    toKLR k Q Λ ν (stendhalValₗ (topTerm Q Λ hρ b)) = topElt ρ b.1 := by
  classical
  change toKLR k Q Λ ν (topTerm Q Λ hρ b).1 = _
  have hu : ∀ a, ((b.1.2.1 • b.1.1).lbl a).isRight → b.1.2.2 a = 0 := fun a ha => by
    by_contra hu
    exact KLRAlgebra.not_isRight_of_isLeft (b.2.2.2.1 a (Finsupp.mem_support_iff.2 hu)) ha
  have hψ := toKLR_ofKLR_std (Q := Q) (Λ := Λ) (ρ b.1.2.1) 0 b.1.1
    (fun _ _ => rfl) b.2.2.2.2
  rw [monomial_zero', C_1, map_one, mul_one] at hψ
  rw [topTerm_val, topElt_eq_pol_e_mul hρ, map_mul, map_mul, toKLR_ofKLR_pol_mul_e, hψ,
    KLRAlgebra.blackSubst_monomial _ _ hu, ← topElt_eq_pol_e_mul hρ]

/-- The terms with dots on top are linearly independent in `T̃^λ` for symmetric `Q`. -/
theorem linearIndependent_topTerm (hQ : KLRSymm Q)
    (hρ : ∀ w, IsReduced m (ρ w) ∧ wordProd m (ρ w) = w) :
    LinearIndependent k (topTerm Q Λ (ν := ν) (fun w => (hρ w).2)) := by
  have hB := (KLR.KLRAlgebra.lbasis (stendhalQ_symm (Q := Q) (Λ := Λ) hQ) ρ hρ).linearIndependent
  refine LinearIndependent.of_comp ((toKLR k Q Λ ν).toLinearMap ∘ₗ stendhalValₗ) ?_
  have : (⇑((toKLR k Q Λ ν).toLinearMap ∘ₗ stendhalValₗ) ∘
      topTerm Q Λ (ν := ν) (fun w => (hρ w).2)) =
      KLR.KLRAlgebra.lbasis (stendhalQ_symm (Q := Q) (Λ := Λ) hQ) ρ hρ ∘ Subtype.val := by
    funext b
    simp only [Function.comp_apply, LinearMap.coe_comp, AlgHom.toLinearMap_apply,
      KLR.KLRAlgebra.lbasis_apply]
    exact toKLR_topTerm _ b
  rw [this]
  exact hB.comp _ Subtype.val_injective

/-- The terms with dots on top span `T̃^λ` for symmetric `Q`. -/
theorem span_topTerm (hQ : KLRSymm Q) (hρ : ∀ w, IsReduced m (ρ w) ∧ wordProd m (ρ w) = w) :
    ⊤ ≤ Submodule.span k (Set.range (topTerm Q Λ (ν := ν) (fun w => (hρ w).2))) := by
  classical
  intro x _
  have hx' := (Subsemigroup.mem_corner_iff isIdempotentElem_redOrderedIdem).1 x.2
  obtain ⟨y, hy⟩ := ofKLR_surjective (k := k) (Q := Q) (Λ := Λ) (ν := ν) x.1
  let B := KLR.KLRAlgebra.lbasis (stendhalQ_symm (Q := Q) (Λ := Λ) hQ) ρ hρ
  have hys : y = ∑ b ∈ (B.repr y).support, B.repr y b • topElt ρ b := by
    conv_lhs => rw [← B.linearCombination_repr y]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [KLR.KLRAlgebra.lbasis_apply]
    rfl
  have hx : x = ∑ b ∈ (B.repr y).support,
      if h : IsTopTerm ρ b then B.repr y b • topTerm Q Λ (fun w => (hρ w).2) ⟨b, h⟩ else 0 := by
    apply stendhalValₗ_injective
    rw [map_sum]
    change x.1 = _
    rw [← hx'.2, ← hx'.1, ← hy]
    conv_lhs => rw [hys]
    rw [map_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_smul, mul_smul_comm, smul_mul_assoc, ro_mul_ofKLR_topElt_mul_ro (fun w => (hρ w).2)]
    split_ifs with h
    · rw [map_smul]; rfl
    · rw [smul_zero, map_zero]
  rw [hx]
  refine Submodule.sum_mem _ fun b _ => ?_
  split_ifs with h
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  · exact Submodule.zero_mem _

variable (Q Λ) in
/-- **A basis of `T̃^λ` with dots on top** (arXiv:1309.3796v3, Proposition 4.16) for symmetric
`Q`, over every commutative ring: the terms `x^u ψ_{ρ w} e(i)` with `IsTopTerm`. -/
noncomputable def topBasis (hQ : KLRSymm Q) (ρ : Perm (Fin m) → List ℕ)
    (hρ : ∀ w, IsReduced m (ρ w) ∧ wordProd m (ρ w) = w) :
    Module.Basis {b // IsTopTerm (ν := ν) (ℓ := ℓ) ρ b} k (StendhalAlgebra k Q Λ ν) :=
  Module.Basis.mk (linearIndependent_topTerm hQ hρ) (span_topTerm hQ hρ)

theorem topBasis_apply (hQ : KLRSymm Q) (ρ : Perm (Fin m) → List ℕ)
    (hρ : ∀ w, IsReduced m (ρ w) ∧ wordProd m (ρ w) = w) (b : {b // IsTopTerm (ν := ν) ρ b}) :
    topBasis Q Λ hQ ρ hρ b = topTerm Q Λ (fun w => (hρ w).2) b :=
  Module.Basis.mk_apply _ _ _

end Categorification.Stendhal

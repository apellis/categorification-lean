/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapEndIndex

/-!
# The generators of the end corner of `T̃^{λ⁺}`

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17, in the case `j = ℓ`. For a generator
`g = (x, j, u)` (`EndGen`), the element `γ_g = x · e(j) · ψ_{ρ₃(u)} e(u⁻¹(i j))` of `T̃^{λ⁺}`
(`genElt`), with the diagram `x` of `λ` on the first `m` strands, lies in the corner `e(j) T̃^{λ⁺}`
of the end block, and the diagrams at the maximum act on it by the basis: for a basis term `y`
of `T̃^{(μ,μ*)}` with bottom `j`, `y · γ_g` is the basis term of `T̃^{λ⁺}` indexed by the pair
`(g, y)` (`endStendhal_topTerm_mul_genElt`). The end idempotent keeps exactly the basis terms
whose top lies in the end block (`endStendhal_one_mul_topTerm`).

## Main definitions

* `genElt`: the generators.

## Main results

* `endStendhal_topTerm_mul_genElt`: the action of the basis of `T̃^{(μ,μ*)}` on the generators.
* `endStendhal_e_mul_genElt`: the generators lie in the corners `e(j) T̃^{λ⁺}`.
* `endStendhal_one_mul_topTerm`: the end idempotent on the basis of `T̃^{λ⁺}`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA Equiv MvPolynomial StendhalAlgebraAllOrders

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Tc" => StendhalAlgebra k Q Λc ν₀
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc ℓ le_rfl) (ν + ν₀)
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc ℓ le_rfl)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "bot" => botMap k Q Λ Λc ℓ le_rfl ν ν₀

/-! ### Images of corner elements -/

/-- The end block on an element of `T̃^{(μ,μ*)}` given by a KLR diagram. -/
theorem endStendhal_of_val (z : Tc) (x : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀))
    (hx : z.val = StendhalAlgebraAllOrders.ofKLR k Q Λc ν₀ x) :
    endStendhal Q Λ Λc ν ν₀ z = bot (endMapKLR Q Λ Λc ν ν₀ x) := by
  rw [endStendhal, stendhalLift_apply, hx, allOrdersLift_ofKLR]
  rfl

/-- The order projection on a basis term with dots on top is the basis term. -/
theorem botMap_topElt {ρ : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀)))) → List ℕ}
    (hρ : ∀ w, wordProd M (ρ w) = w) (b : {b // IsTopTerm ρ b}) :
    bot (topElt (Q := Q) (Λ := plusLabels Λ Λc ℓ le_rfl) ρ b.1) =
      topTerm Q (plusLabels Λ Λc ℓ le_rfl) hρ b := by
  apply Subtype.ext
  change ofKLR k Q _ (ν + ν₀) _ * redOrderedIdem k Q _ (ν + ν₀) = _
  rw [topTerm_val]
  have h := ro_mul_ofKLR_topElt_mul_ro (Q := Q) (Λ := plusLabels Λ Λc ℓ le_rfl) hρ b.1
  rw [ite_eq_left_of_eq_true _ _ (eq_true b.2)] at h
  have hE := isIdempotentElem_redOrderedIdem (k := k) (Q := Q) (Λ := plusLabels Λ Λc ℓ le_rfl)
    (ν := ν + ν₀)
  conv_lhs => rw [← h]
  rw [mul_assoc, hE.eq, h]

/-- The order projection of the end block on red-ordered idempotents. -/
theorem endStendhal_e (j : Seq (stendhalWeight 2 ν₀)) (hj : IsRedOrdered j) :
    endStendhal Q Λ Λc ν ν₀ (StendhalAlgebra.e j hj) =
      bot (endMapKLR Q Λ Λc ν ν₀ (KLRAlgebra.e j)) :=
  endStendhal_of_val _ _ rfl

/-! ### The generators -/

variable (ρ₁ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ)
  (ρ₂ : Perm (Fin (Multiset.card (stendhalWeight 2 ν₀))) → List ℕ)
  (ρ₃ : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀)))) → List ℕ)

variable (Q Λ Λc) in
/-- The KLR diagram `x · e(j) · ψ_{ρ₃(u)} e(u⁻¹(i j))` of a generator `g = (x, j, u)`. -/
def genKLR (g : EndGen ν₀ ρ₁) : Rp :=
  prefixMapKLR Q Λ Λc ν ν₀ (topElt (Q := Q) (Λ := Λ) ρ₁ g.1.1.1) *
    endMapKLR Q Λ Λc ν ν₀ (KLRAlgebra.e g.1.2.1) * ψw (ρ₃ g.1.2.2.1) * KLRAlgebra.e g.bot

variable (Q Λ Λc) in
/-- **The generator** `γ_g` of the end corner of `T̃^{λ⁺}`. -/
def genElt (g : EndGen ν₀ ρ₁) : Tp := bot (genKLR Q Λ Λc ρ₁ ρ₃ g)

variable {ρ₁ ρ₃}

theorem endMapKLR_e_mul_genKLR (g : EndGen ν₀ ρ₁) :
    endMapKLR Q Λ Λc ν ν₀ (KLRAlgebra.e g.1.2.1) * genKLR Q Λ Λc ρ₁ ρ₃ g =
      genKLR Q Λ Λc ρ₁ ρ₃ g := by
  simp only [genKLR, ← mul_assoc]
  rw [← (commute_prefixMapKLR_endMapKLR Q Λ Λc ν ν₀ _ _).eq,
    mul_assoc (prefixMapKLR Q Λ Λc ν ν₀ _) (endMapKLR Q Λ Λc ν ν₀ _), ← endMapKLR_mul,
    e_mul_self]

/-- The generator `γ_g` lies in the corner `e(j) T̃^{λ⁺}` of its loading `j`. -/
theorem endStendhal_e_mul_genElt (g : EndGen ν₀ ρ₁) :
    endStendhal Q Λ Λc ν ν₀ (StendhalAlgebra.e g.1.2.1 g.2.1) * genElt Q Λ Λc ρ₁ ρ₃ g =
      genElt Q Λ Λc ρ₁ ρ₃ g := by
  rw [endStendhal_e, genElt, ← map_mul, endMapKLR_e_mul_genKLR]

/-- The generator `γ_g` lies in the corner of the end block. -/
theorem endStendhal_one_mul_genElt (g : EndGen ν₀ ρ₁) :
    endStendhal Q Λ Λc ν ν₀ 1 * genElt Q Λ Λc ρ₁ ρ₃ g = genElt Q Λ Λc ρ₁ ρ₃ g := by
  rw [← endStendhal_e_mul_genElt, ← mul_assoc, ← map_mul, one_mul]

/-- **The diagrams at the maximum act on the generators by the basis**: for a basis term `y` of
`T̃^{(μ,μ*)}` with bottom `j`, `y · γ_g` is the basis term of `T̃^{λ⁺}` indexed by `(g, y)`. -/
theorem endStendhal_topTerm_mul_genElt (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w) (p : EndPair ρ₁ ρ₂) :
    endStendhal Q Λ Λc ν ν₀ (topTerm Q Λc (fun b => (hρ₂ b).2) p.1.2) *
        genElt Q Λ Λc ρ₁ ρ₃ p.1.1 =
      topTerm Q (plusLabels Λ Λc ℓ le_rfl) (fun w => (endWord_spec hρ₁ hρ₂ hρ₃ w).2)
        (endPairIdx ρ₁ ρ₂ ρ₃ (endWord_spec hρ₁ hρ₂ hρ₃) p) := by
  obtain ⟨⟨g, y⟩, hp⟩ := p
  obtain ⟨⟨⟨⟨i, a, d⟩, hx⟩, j, u⟩, hj, hbot⟩ := g
  obtain ⟨⟨j', b, d'⟩, hy⟩ := y
  simp only at hp
  subst hp
  rw [endStendhal_of_val _ _ (topTerm_val _ _), genElt, ← map_mul,
    ← botMap_topElt (fun w => (endWord_spec hρ₁ hρ₂ hρ₃ w).2)]
  congr 1
  -- the KLR identity
  have hc := commute_prefixMapKLR_endMapKLR Q Λ Λc ν ν₀
  simp only [genKLR, ← mul_assoc]
  rw [← (hc _ _).eq, mul_assoc (prefixMapKLR Q Λ Λc ν ν₀ _) (endMapKLR Q Λ Λc ν ν₀ _),
    ← endMapKLR_mul, topElt_mul_e]
  simp only [topElt]
  rw [prefixMapKLR_mul_endMapKLR _ _ (hρ₁ a).1.1 (hρ₂ b).1.1, mul_assoc _ (KLRAlgebra.e _),
    e_mul_ψw,
    (hρ₃ u.1).2, mul_assoc]
  simp only [EndGen.bot, endSeq]
  rw [mul_assoc (ψw _), e_mul_self, ← mul_assoc, mul_assoc (pol _), ← ψw_append,
    ← monomial_endExp (d, d')]
  change _ = pol _ * ψw (endWord ρ₁ ρ₂ ρ₃ (blockPerm _ a b * u.1)) * KLRAlgebra.e _
  rw [endWord_blockPerm_mul]
  rfl

/-! ### The end idempotent on the basis of `T̃^{λ⁺}` -/

theorem endMapKLR_sum {ι : Type*} (S : Finset ι)
    (f : ι → KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) :
    endMapKLR Q Λ Λc ν ν₀ (∑ x ∈ S, f x) = ∑ x ∈ S, endMapKLR Q Λ Λc ν ν₀ (f x) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    unfold endMapKLR; rw [map_zero, map_zero]; rfl
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, endMapKLR_add, ih]

theorem endMapKLR_e_eq_sum (t : Seq (stendhalWeight 2 ν₀)) :
    endMapKLR Q Λ Λc ν ν₀ (KLRAlgebra.e t) =
      ∑ s : Seq (stendhalWeight ℓ ν), KLRAlgebra.e (endSeq s t) := by
  rw [endMapKLR_eq_sum]
  exact Finset.sum_congr rfl fun s _ => insertMap_e s le_rfl t

/-- **The end idempotent keeps exactly the basis terms whose top lies in the end block.** -/
theorem endStendhal_one_mul_topTerm
    {ρ : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀)))) → List ℕ}
    (hρ : ∀ w, wordProd M (ρ w) = w) (b : {b // IsTopTerm ρ b}) :
    endStendhal Q Λ Λc ν ν₀ 1 * topTerm Q (plusLabels Λ Λc ℓ le_rfl) hρ b =
      if b.1.2.1 • b.1.1 ∈ endSet ν ν₀ then topTerm Q (plusLabels Λ Λc ℓ le_rfl) hρ b else 0 := by
  classical
  rw [endStendhal_one_eq_endBot, endBot_apply, ← botMap_topElt hρ, ← map_mul,
    ← e_mul_topElt hρ b.1, ← mul_assoc, redOrderedKLR]
  rw [endMapKLR_sum, Finset.sum_mul, Finset.sum_mul]
  simp_rw [endMapKLR_e_eq_sum, Finset.sum_mul, KLRAlgebra.e_mul_e]
  split_ifs with hm
  · obtain ⟨s, t, hst⟩ := exists_endSeq_of_mem hm
    have ht : IsRedOrdered t := ((isRedOrdered_endSeq s t).1 (hst ▸ b.2.2.1)).2
    rw [Finset.sum_eq_single_of_mem t (Finset.mem_filter.2 ⟨Finset.mem_univ _, ht⟩),
      Finset.sum_eq_single s, ite_eq_left_of_eq_true _ _ (eq_true hst), hst, e_mul_topElt hρ b.1]
    · intro s' _ hs'
      rw [ite_eq_right_of_eq_false _ _
        (eq_false fun h => hs' (endSeq_injective (h.trans hst.symm)).1), zero_mul]
    · simp
    · intro t' _ ht'
      refine Finset.sum_eq_zero fun s' _ => ?_
      rw [ite_eq_right_of_eq_false _ _
        (eq_false fun h => ht' (endSeq_injective (h.trans hst.symm)).2), zero_mul]
  · rw [Finset.sum_eq_zero fun t _ => Finset.sum_eq_zero fun s _ => ?_, map_zero]
    split_ifs with h
    · exact absurd (h ▸ endSeq_mem_endSet s t) hm
    · exact zero_mul _

end Categorification.Stendhal.CupCap

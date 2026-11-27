/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidCornerIndex

/-!
# The generators of the corner of the maximum after `λ_j`

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17, for the cap after the red strand `λ_j`.
For a generator `g = (s, t, d, u)` (`MidGen`), the element
`γ_g = e(midSeq s t) · x^{d} · ψ_{ρ₃(u)} e(u⁻¹ (midSeq s t))` of `T̃^{λ⁺}` (`midGenElt`), with
the dots `x^d` on the strands of `λ` outside the window, lies in the corner `e(t) T̃^{λ⁺}` of the
maximum, and the diagrams at the maximum act on it by the basis: for a basis term `y` of
`T̃^{(μ,μ*)}` with bottom `t`, `y · γ_g` is the basis term of `T̃^{λ⁺}` indexed by the pair
`(g, y)` (`midStendhal_topTerm_mul_midGenElt`), for the reduced words adapted to the window
(`midWord`). The unit of the maximum keeps exactly the basis terms whose top lies in `midSet`
(`midStendhal_one_mul_topTermSeq`).

## Main definitions

* `CupCap.midGenElt`: the generators.

## Main results

* `CupCap.botMap_topEltSeq`: the quotient map on a basis term with dots on top.
* `CupCap.midStendhal_topTerm_mul_midGenElt`: the action of the basis of `T̃^{(μ,μ*)}` on the
  generators.
* `CupCap.midStendhal_e_mul_midGenElt`: the generators lie in the corners `e(t) T̃^{λ⁺}`.
* `CupCap.midStendhal_one_mul_topTermSeq`: the unit of the maximum on the basis of `T̃^{λ⁺}`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA Equiv MvPolynomial StendhalAlgebraAllOrders

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Tc" => StendhalAlgebra k Q Λc ν₀
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "bot" => botMap k Q Λ Λc j hj ν ν₀
local notation "σ" => midStendhal j hj Q Λ Λc ν ν₀
local notation "ι" => insertMap (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc

/-! ### Images of elements -/

/-- The diagrams at the maximum on an element of `T̃^{(μ,μ*)}` given by a KLR diagram. -/
theorem midStendhal_of_val (z : Tc) (x : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀))
    (hx : z.val = StendhalAlgebraAllOrders.ofKLR k Q Λc ν₀ x) :
    σ z = bot (midMapKLR j hj Q Λ Λc ν ν₀ x) := by
  rw [midStendhal, stendhalLift_apply, hx, allOrdersLift_ofKLR]
  rfl

/-- The quotient map onto `T̃^{λ⁺}` on a basis term with dots on top is the basis term. -/
theorem botMap_topEltSeq
    {ρ : Seq (stendhalWeight (ℓ + 2) (ν + ν₀)) → Perm (Fin M) → List ℕ}
    (hρ : ∀ i w, wordProd M (ρ i w) = w) (b : {b // IsTopTermSeq ρ b}) :
    bot (topElt (Q := Q) (Λ := plusLabels Λ Λc j hj) (ρ b.1.1) b.1) =
      topTermSeq Q (plusLabels Λ Λc j hj) hρ b := by
  apply Subtype.ext
  change ofKLR k Q _ (ν + ν₀) _ * redOrderedIdem k Q _ (ν + ν₀) = _
  rw [topTermSeq_val]
  have h := ro_mul_ofKLR_topElt_mul_ro (Q := Q) (Λ := plusLabels Λ Λc j hj) (hρ b.1.1) b.1
  rw [ite_eq_left_of_eq_true _ _ (eq_true (show IsTopTerm (ρ b.1.1) b.1 from b.2))] at h
  have hE := isIdempotentElem_redOrderedIdem (k := k) (Q := Q) (Λ := plusLabels Λ Λc j hj)
    (ν := ν + ν₀)
  conv_lhs => rw [← h]
  rw [mul_assoc, hE.eq, h]

/-! ### The generators -/

variable (ρ₂ : Perm (Fin (Multiset.card (stendhalWeight 2 ν₀))) → List ℕ)
  (ρ₃ : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀)))) → List ℕ)

variable (Q Λ Λc) in
/-- The KLR diagram `e(midSeq s t) · x^d · ψ_{ρ₃(u)} e(u⁻¹ (midSeq s t))` of a generator, with
the dots `x^d` on the strands of `λ` outside the window. -/
def midGenKLR (g : MidGen j hj ν ν₀) : Rp :=
  KLRAlgebra.e (midSeq j hj g.s g.t) * pol (rename (outPos j ν₀ g.s) (monomial g.d 1)) *
    ψw (ρ₃ g.u) * KLRAlgebra.e g.bot

variable (Q Λ Λc) in
/-- **The generator** `γ_g` of the corner of the maximum of `T̃^{λ⁺}`. -/
def midGenElt (g : MidGen j hj ν ν₀) : Tp := bot (midGenKLR Q Λ Λc ρ₃ g)

variable {ρ₂ ρ₃}

theorem midMapKLR_e_mul_midGenKLR (g : MidGen j hj ν ν₀) :
    midMapKLR j hj Q Λ Λc ν ν₀ (KLRAlgebra.e g.t) * midGenKLR Q Λ Λc ρ₃ g =
      midGenKLR Q Λ Λc ρ₃ g := by
  simp only [midGenKLR, ← mul_assoc]
  rw [midMapKLR_mul_e_midSeq, insertMap_e]
  change KLRAlgebra.e (midSeq j hj g.s g.t) * KLRAlgebra.e (midSeq j hj g.s g.t) * _ * _ * _ = _
  rw [e_mul_self]

/-- The generator `γ_g` lies in the corner `e(t) T̃^{λ⁺}` of its loading `t`. -/
theorem midStendhal_e_mul_midGenElt (g : MidGen j hj ν ν₀) :
    σ (StendhalAlgebra.e g.t g.ht) * midGenElt Q Λ Λc ρ₃ g = midGenElt Q Λ Λc ρ₃ g := by
  rw [midStendhal_of_val _ (KLRAlgebra.e g.t) rfl, midGenElt, ← map_mul,
    midMapKLR_e_mul_midGenKLR]

/-- The generator `γ_g` lies in the corner of the maximum. -/
theorem midStendhal_one_mul_midGenElt (g : MidGen j hj ν ν₀) :
    σ 1 * midGenElt Q Λ Λc ρ₃ g = midGenElt Q Λ Λc ρ₃ g := by
  rw [← midStendhal_e_mul_midGenElt, ← mul_assoc, ← map_mul, one_mul]

/-- **The diagrams at the maximum act on the generators by the basis**: for a basis term `y` of
`T̃^{(μ,μ*)}` with bottom `t`, `y · γ_g` is the basis term of `T̃^{λ⁺}` indexed by `(g, y)`,
for the reduced words adapted to the window. -/
theorem midStendhal_topTerm_mul_midGenElt (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w) (p : MidPair j hj ν ρ₂) :
    σ (topTerm Q Λc (fun b => (hρ₂ b).2) p.1.2) * midGenElt Q Λ Λc ρ₃ p.1.1 =
      topTermSeq Q (plusLabels Λ Λc j hj) (fun i w => (midWord_spec hρ₂ hρ₃ i w).2)
        (midPairIdx ρ₃ hρ₂ hρ₃ p) := by
  rw [midStendhal_of_val _ _ (topTerm_val _ _), midGenElt, ← map_mul,
    ← botMap_topEltSeq (fun i w => (midWord_spec hρ₂ hρ₃ i w).2)]
  congr 1
  obtain ⟨⟨g, ⟨⟨t₁, b, d'⟩, hy⟩⟩, hp⟩ := p
  change t₁ = g.t at hp
  subst hp
  have hβ := (hρ₂ b).1.1
  have hmid : (winPerm (midPos_add_N_le j ν₀ g.s) b * g.u) • g.bot = midSeq j hj g.s (b • g.t) := by
    rw [mul_smul, MidGen.smul_bot, winPerm_smul_midSeq]
  change midMapKLR j hj Q Λ Λc ν ν₀ (pol (monomial d' 1) * ψw (ρ₂ b) * KLRAlgebra.e g.t) *
      midGenKLR Q Λ Λc ρ₃ g =
    pol (monomial (midExp j ν₀ g.s (g.d, d')) 1) *
      ψw (midWord j hj ρ₂ ρ₃ g.bot (winPerm (midPos_add_N_le j ν₀ g.s) b * g.u)) *
      KLRAlgebra.e g.bot
  rw [midWord_eq hmid, midWordAt_winPerm_mul (u := ⟨g.u, g.hu⟩)]
  simp only [midGenKLR, ← mul_assoc]
  rw [midMapKLR_mul_e_midSeq, insertMap_pol_ψw_e _ _ _ hβ]
  change pol _ * ψw _ * KLRAlgebra.e (midSeq j hj g.s g.t) * KLRAlgebra.e (midSeq j hj g.s g.t) *
      _ * _ * _ = _
  set A : Rp := pol (rename (winPos (midPos_add_N_le j ν₀ g.s)) (monomial d' 1))
  set B : Rp := ψw (shiftWord (midPos j g.s) (ρ₂ b))
  set E : Rp := KLRAlgebra.e (midSeq j hj g.s g.t)
  set P : Rp := pol (rename (outPos j ν₀ g.s) (monomial g.d 1))
  set C : Rp := ψw (ρ₃ g.u)
  set F : Rp := KLRAlgebra.e g.bot
  have hEE : E * E = E := e_mul_self _
  have hEP : E * P = P * E := (e_commute_pol _ _).eq
  have hBP : B * P = P * B := (pol_out_mul_ψw_shift _ _ hβ).symm
  have hECF : E * (C * F) = C * F := by
    simp only [E, C, F]
    rw [← mul_assoc, e_mul_ψw, (hρ₃ g.u).2, ← MidGen.smul_bot, inv_smul_smul, mul_assoc,
      e_mul_self]
  have hAP : A * P = pol (monomial (midExp j ν₀ g.s (g.d, d')) 1) := by
    simp only [A, P]
    rw [← map_mul, monomial_midExp, mul_comm]
  have hBC : B * C = ψw (shiftWord (midPos j g.s) (ρ₂ b) ++ ρ₃ g.u) := (ψw_append _ _).symm
  calc A * B * E * E * P * C * F = A * (B * P) * (E * (C * F)) := by
        rw [mul_assoc A B E, mul_assoc A (B * E) E, mul_assoc B E E, hEE, mul_assoc A (B * E) P,
          mul_assoc B E P, hEP]
        simp only [mul_assoc]
    _ = _ := by rw [hBP, hECF, ← mul_assoc, ← mul_assoc, hAP, mul_assoc _ B C, hBC, mul_assoc]

/-! ### The unit of the maximum on the basis of `T̃^{λ⁺}` -/

/-- **The unit of the maximum keeps exactly the basis terms whose top lies in `midSet`.** -/
theorem midStendhal_one_mul_topTermSeq
    {ρ : Seq (stendhalWeight (ℓ + 2) (ν + ν₀)) → Perm (Fin M) → List ℕ}
    (hρ : ∀ i w, wordProd M (ρ i w) = w) (b : {b // IsTopTermSeq ρ b}) :
    σ 1 * topTermSeq Q (plusLabels Λ Λc j hj) hρ b =
      if b.1.2.1 • b.1.1 ∈ midSet j hj ν ν₀ then topTermSeq Q (plusLabels Λ Λc j hj) hρ b
      else 0 := by
  classical
  rw [midStendhal_one_eq_midBot, midBot_apply, ← botMap_topEltSeq hρ, ← map_mul,
    ← e_mul_topElt (hρ b.1.1) b.1, ← mul_assoc, redOrderedKLR]
  rw [midMapKLR_sum, Finset.sum_mul, Finset.sum_mul]
  simp_rw [midMapKLR_e, Finset.sum_mul, KLRAlgebra.e_mul_e]
  split_ifs with hm
  · obtain ⟨s, t, hst⟩ := exists_midSeq_of_mem hm
    have ht : IsRedOrdered t := ((isRedOrdered_midSeq s t).1 (hst ▸ b.2.2.1)).2
    rw [Finset.sum_eq_single_of_mem t (Finset.mem_filter.2 ⟨Finset.mem_univ _, ht⟩),
      Finset.sum_eq_single s, ite_eq_left_of_eq_true _ _ (eq_true hst), hst,
      e_mul_topElt (hρ b.1.1) b.1]
    · intro s' _ hs'
      rw [ite_eq_right_of_eq_false _ _
        (eq_false fun h => hs' (midSeq_injective (h.trans hst.symm)).1), zero_mul]
    · simp
    · intro t' _ ht'
      refine Finset.sum_eq_zero fun s' _ => ?_
      rw [ite_eq_right_of_eq_false _ _
        (eq_false fun h => ht' (midSeq_injective (h.trans hst.symm)).2), zero_mul]
  · rw [Finset.sum_eq_zero fun t _ => Finset.sum_eq_zero fun s _ => ?_, map_zero]
    split_ifs with h
    · exact absurd (h ▸ midSeq_mem_midSet s t) hm
    · exact zero_mul _

end Categorification.Stendhal.CupCap

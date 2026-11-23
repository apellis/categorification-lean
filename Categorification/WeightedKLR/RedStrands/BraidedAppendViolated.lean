/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidedAppendTensor
import Categorification.WeightedKLR.RedStrands.BraidedViolatedIdentity

set_option backward.isDefEq.respectTransparency false

/-!
# The appended black strand on the quotients by violated idempotents

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §6.1,
Proposition 6.7. The append map `φ`, adding a black strand at the right, sends violated
idempotents to violated idempotents, so it descends to the quotients `B = B̃ / J` by the ideals
of violated idempotents. The freeness statement for `B̃` (`mult_injective_append`) descends to
these quotients: an element `e_{κ'} z φ(e_κ)` with `z ∈ J` is a sum of products
`e_{κ'} x φ(e_{κ'} y e_κ)` with `x ∈ J`, because a violated idempotent can be pushed to the red
order `κ'` (`redProj_mul_e_mem_violSpan`) and the corner `e_{κ'} B̃(ν + i) φ(e_κ)` is spanned by
the products `ψ_c x^n φ(e_{κ'} y e_κ)` (`exists_cosetGen_sum`).

## Main results

* `appendViol`: the append map on the quotients.
* `violMk_mult_injective_append`, `violMk_mult_surjective_append`: multiplication
  `e_{κ'} B(ν + i) ⊗_{φ} e_{κ'} B(ν) e_κ → e_{κ'} B(ν + i) φ(e_κ)` is bijective. This is the
  module-level form of the isomorphism `E_i ∘ B_s ≅ B_s ∘ E_i` of Proposition 6.7.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA MvPolynomial Equiv

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (i : I) (ν : Multiset I)

local notation "μ" => stendhalWeight ℓ ν
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)

namespace BraidedStendhalAlgebra

omit [DecidableEq I] in
/-- A black strand at the right keeps a violated loading violated. -/
theorem isViolated_appendBlackLoading {s : Seq μ} (hs : IsViolated s) :
    IsViolated (appendBlackLoading i ν s) := by
  obtain ⟨h, hl⟩ := hs
  have h' : 0 < Multiset.card (stendhalWeight ℓ νᵢ) := by
    rw [card_stendhalWeight_addBlack]; omega
  refine ⟨h', ?_⟩
  rw [appendBlackLoading_lbl_of_lt i ν s _ h]
  exact hl

theorem appendBlackAlg_e (s : Seq μ) :
    appendBlackAlg Q Λ i ν (ofKLR k Q Λ ν (KLRAlgebra.e s)) =
      ofKLR k Q Λ νᵢ (KLRAlgebra.e (appendBlackLoading i ν s)) :=
  appendBlackValue_e Q Λ i ν s

theorem appendBlackAlg_mem_violIdeal {z : BraidedStendhalAlgebra k Q Λ ν}
    (hz : z ∈ violIdeal k Q Λ ν) : appendBlackAlg Q Λ i ν z ∈ violIdeal k Q Λ νᵢ := by
  rw [violIdeal, TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure] at hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨_, ⟨a, -, g, ⟨s, hs, rfl⟩, rfl⟩, b, -, rfl⟩ := hz
    rw [map_mul, map_mul, appendBlackAlg_e]
    refine TwoSidedIdeal.mul_mem_right _ _ _ (TwoSidedIdeal.mul_mem_left _ _ _ ?_)
    exact TwoSidedIdeal.subset_span ⟨_, isViolated_appendBlackLoading i ν hs, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add z w _ _ hz hw => rw [map_add]; exact add_mem hz hw
  | neg z _ hz => rw [map_neg]; exact neg_mem hz

/-- The append map on the quotients, as a function. -/
def appendViolFun : ViolQuotient k Q Λ ν → ViolQuotient k Q Λ νᵢ :=
  Quotient.lift (fun z => violMk k Q Λ νᵢ (appendBlackAlg Q Λ i ν z)) fun a b h => by
    have h' : a - b ∈ violIdeal k Q Λ ν := (TwoSidedIdeal.rel_iff _ a b).1 h
    have := appendBlackAlg_mem_violIdeal Q Λ i ν h'
    rw [map_sub, ← violMk_eq_zero_iff, map_sub, sub_eq_zero] at this
    exact this

theorem appendViolFun_violMk (z : BraidedStendhalAlgebra k Q Λ ν) :
    appendViolFun Q Λ i ν (violMk k Q Λ ν z) = violMk k Q Λ νᵢ (appendBlackAlg Q Λ i ν z) :=
  rfl

/-- The append map on the quotients by violated idempotents. -/
def appendViol : ViolQuotient k Q Λ ν →ₙₐ[k] ViolQuotient k Q Λ νᵢ where
  toFun := appendViolFun Q Λ i ν
  map_smul' c x := by
    obtain ⟨x, rfl⟩ := violMk_surjective x
    rw [← map_smul, appendViolFun_violMk, appendViolFun_violMk, map_smul, map_smul]
    rfl
  map_zero' := by
    rw [← map_zero (violMk k Q Λ ν), appendViolFun_violMk, map_zero, map_zero]
  map_add' x y := by
    obtain ⟨x, rfl⟩ := violMk_surjective x
    obtain ⟨y, rfl⟩ := violMk_surjective y
    rw [← map_add, appendViolFun_violMk, appendViolFun_violMk, appendViolFun_violMk, map_add,
      map_add]
  map_mul' x y := by
    obtain ⟨x, rfl⟩ := violMk_surjective x
    obtain ⟨y, rfl⟩ := violMk_surjective y
    rw [← map_mul, appendViolFun_violMk, appendViolFun_violMk, appendViolFun_violMk, map_mul,
      map_mul]

theorem appendViol_violMk (z : BraidedStendhalAlgebra k Q Λ ν) :
    appendViol Q Λ i ν (violMk k Q Λ ν z) = violMk k Q Λ νᵢ (appendBlackAlg Q Λ i ν z) :=
  rfl

variable (hQ : KLRSymm Q)
  (ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ) (hρ : IsReducedChoice ρ)

variable (k) in
/-- The products `e_{κ'} x φ(e_{κ'} y e_κ)` with a violated factor. -/
def appendViolSpan (κ' κ : List (Fin ℓ)) : Submodule k (BraidedStendhalAlgebra k Q Λ νᵢ) :=
  Submodule.span k {w | ∃ x y, (violMk k Q Λ νᵢ x = 0 ∨ violMk k Q Λ ν y = 0) ∧
    w = redProj k Q Λ νᵢ κ' * x *
      appendBlackAlg Q Λ i ν (redProj k Q Λ ν κ' * y * redProj k Q Λ ν κ)}

include hQ hρ in
theorem redProj_mul_violSpan_mem (κ' κ : List (Fin ℓ)) {w : BraidedStendhalAlgebra k Q Λ νᵢ}
    (hw : w ∈ violSpan k Q Λ νᵢ κ') (b : BraidedStendhalAlgebra k Q Λ νᵢ) :
    redProj k Q Λ νᵢ κ' * w * b * appendBlackAlg Q Λ i ν (redProj k Q Λ ν κ) ∈
      appendViolSpan k Q Λ i ν κ' κ := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨u, j, x, hj, hjκ, rfl⟩ := hw
    set E := ofKLR k Q Λ νᵢ (KLRAlgebra.e j)
    have hE : E * redProj k Q Λ νᵢ κ' = E := by
      rw [e_mul_redProj]; simp only [hjκ, ↓reduceIte, E]
    obtain ⟨t, ht⟩ := exists_cosetGen_sum Q Λ i ν hQ ρ hρ κ' (redProj k Q Λ ν κ) (x * b)
    have he : redProj k Q Λ νᵢ κ' * (u * E * x) * b *
        appendBlackAlg Q Λ i ν (redProj k Q Λ ν κ) =
        redProj k Q Λ νᵢ κ' * u * E * (redProj k Q Λ νᵢ κ' * (x * b) *
          appendBlackAlg Q Λ i ν (redProj k Q Λ ν κ)) := by
      conv_lhs => rw [← hE]
      simp only [mul_assoc]
    rw [he, ht, Finsupp.mul_sum]
    refine Submodule.sum_mem _ fun p _ => Submodule.subset_span ⟨u * E * cosetGen Q Λ i ν κ' p,
      t p, Or.inl ?_, ?_⟩
    · rw [map_mul, map_mul, violMk_e hj, mul_zero, zero_mul]
    · simp only [mul_assoc]
  | zero => rw [mul_zero, zero_mul, zero_mul]; exact zero_mem _
  | add w w' _ _ hw hw' => rw [mul_add, add_mul, add_mul]; exact add_mem hw hw'
  | smul r w _ hw =>
    rw [mul_smul_comm, smul_mul_assoc, smul_mul_assoc]; exact Submodule.smul_mem _ r hw

include hQ hρ in
theorem redProj_mul_mul_appendBlackAlg_mem (κ' κ : List (Fin ℓ))
    (z : BraidedStendhalAlgebra k Q Λ νᵢ) (hz : violMk k Q Λ νᵢ z = 0) :
    redProj k Q Λ νᵢ κ' * z * appendBlackAlg Q Λ i ν (redProj k Q Λ ν κ) ∈
      appendViolSpan k Q Λ i ν κ' κ := by
  rw [violMk_eq_zero_iff, violIdeal, TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure] at hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨_, ⟨a, -, g, ⟨j, hj, rfl⟩, rfl⟩, b, -, rfl⟩ := hz
    have hw := redProj_mul_e_mem_violSpan (isReducedChoice_lastCosetWord
      (hm := appendCard i ν) hρ) hQ (κ₂ := κ') _ _ rfl j hj rfl a
    have := redProj_mul_violSpan_mem Q Λ i ν hQ ρ hρ κ' κ hw b
    have hP := isIdempotentElem_redProj (k := k) (Q := Q) (Λ := Λ) (ν := νᵢ) κ'
    have he : redProj k Q Λ νᵢ κ' * (a * ofKLR k Q Λ νᵢ (KLRAlgebra.e j) * b) =
        redProj k Q Λ νᵢ κ' * (redProj k Q Λ νᵢ κ' * a * ofKLR k Q Λ νᵢ (KLRAlgebra.e j)) *
          b := by
      simp only [← mul_assoc, hP.eq]
    rw [he]
    exact this
  | zero => rw [mul_zero, zero_mul]; exact zero_mem _
  | add z w _ _ hz hw => rw [mul_add, add_mul]; exact add_mem hz hw
  | neg z _ hz => rw [mul_neg, neg_mul]; exact neg_mem hz

include hQ hρ in
/-- **Webster, Proposition 6.7** (arXiv:1309.3796v2), injectivity, on the quotients by violated
idempotents: multiplication `e_{κ'} B(ν + i) ⊗_φ e_{κ'} B(ν) e_κ → B(ν + i)` is injective. -/
theorem violMk_mult_injective_append (κ' κ : List (Fin ℓ)) :
    Function.Injective (TensorAlong.mult
      ((idemAppend Q Λ i ν κ').map (violMk k Q Λ νᵢ))
      ((idemBase Q Λ ν κ').map (violMk k Q Λ ν)) ((idemBase Q Λ ν κ).map (violMk k Q Λ ν)) :
      TensorAlong k _ _ (appendViol Q Λ i ν) (violMk k Q Λ νᵢ (redProj k Q Λ νᵢ κ'))
        (violMk k Q Λ ν (redProj k Q Λ ν κ')) (violMk k Q Λ ν (redProj k Q Λ ν κ)) →ₗ[k] _) :=
  TensorAlong.mult_injective_of_ker (violMk k Q Λ νᵢ) (violMk k Q Λ ν)
    (fun c => appendViol_violMk Q Λ i ν c) _ _ _ violMk_surjective violMk_surjective
    (mult_injective_append Q Λ i ν hQ ρ hρ κ' κ)
    (redProj_mul_mul_appendBlackAlg_mem Q Λ i ν hQ ρ hρ κ' κ)

include hQ hρ in
/-- **Webster, Proposition 6.7** (arXiv:1309.3796v2), surjectivity, on the quotients by violated
idempotents: every element of `e_{κ'} B(ν + i) φ(e_κ)` is a product. -/
theorem violMk_mult_surjective_append (κ' κ : List (Fin ℓ)) (z : ViolQuotient k Q Λ νᵢ) :
    ∃ t, TensorAlong.mult
      ((idemAppend Q Λ i ν κ').map (violMk k Q Λ νᵢ))
      ((idemBase Q Λ ν κ').map (violMk k Q Λ ν)) ((idemBase Q Λ ν κ).map (violMk k Q Λ ν))
      (t : TensorAlong k _ _ (appendViol Q Λ i ν) (violMk k Q Λ νᵢ (redProj k Q Λ νᵢ κ'))
        (violMk k Q Λ ν (redProj k Q Λ ν κ')) (violMk k Q Λ ν (redProj k Q Λ ν κ))) =
      violMk k Q Λ νᵢ (redProj k Q Λ νᵢ κ') * z *
        appendViol Q Λ i ν (violMk k Q Λ ν (redProj k Q Λ ν κ)) :=
  TensorAlong.mult_surjective_of_surjective (violMk k Q Λ νᵢ) (violMk k Q Λ ν)
    (fun c => appendViol_violMk Q Λ i ν c) _ _ _ violMk_surjective
    (mult_surjective_append Q Λ i ν hQ ρ hρ κ' κ) z

end BraidedStendhalAlgebra

end Categorification.Stendhal

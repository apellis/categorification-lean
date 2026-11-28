/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ExactMulRightTransport
import Categorification.WeightedKLR.RedStrands.RedFirstDoubleCentralizer

set_option backward.isDefEq.respectTransparency false

/-!
# A corner copresentation of `T^λ` from crossings with embedded cokernels

Reduction step for B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, Corollary 5.32 (v2: Corollary 5.29): the hypothesis
`HasCornerCopresentation e⁰` of the double centralizer theorem follows once the base crossing of
Lemma 5.25 (v2: Lemma 5.23) has a cokernel embedding into a free module.

A crossing `s ⟶ t` (`CrossPair`) is *exact* (`ExactCrossPair`) when its element `c ∈ e(s) T e(t)`
has a cokernel `T / T c` embedding into a free module (`IsExactMulRight c g`). Adding black or
red strands on the right preserves exact crossings (`exactCrossPair_appendBlack`,
`exactCrossPair_appendRed'`, from `isExactMulRight_appendBlack`, `isExactMulRight_emptyRed`), so
if the base crossings at red-first loadings are exact (`ExactBaseCrossing`), every red-ordered
loading reaches a red-first one by exact crossings (`exactReach_of_isRedOrdered`). The product
`θ_s` of the chain from `s` then has a cokernel without nonzero submodules killed by `e⁰`
(`isCornerFaithfulQuot_mul`), and these elements form a corner copresentation
(`hasCornerCopresentation_redFirstIdem_of_exactBaseCrossing`).

## Main results

* `eq_zero_of_redFirstIdem_mul`: `T^λ` acts faithfully on `e⁰ T^λ` from the right.
* `hasCornerCopresentation_redFirstIdem_of_exactBaseCrossing`: the corner copresentation, given
  exact base crossings.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra InductionAlong

variable {I : Type} [DecidableEq I] {k : Type} [Field k] (Q : I → I → MvPolynomial (Fin 2) k)

/-- An exact crossing `s ⟶ t`: an element `c` with `e(s) c = c = c e(t)` such that `x ↦ x c` is
injective on `T^λ e(s)` and the cokernel of `z ↦ z c` embeds into a free module. -/
def ExactCrossPair {m : ℕ} (Λ : Fin m → I →₀ ℕ) (ν : Multiset I)
    (s t : Seq (stendhalWeight m ν)) : Prop :=
  ∃ (hs : IsRedOrdered s) (ht : IsRedOrdered t) (c : TensorProductAlgebra k Q Λ ν),
    (∀ x, x * redLoadingIdem Q Λ ν s hs = x → x * c = 0 → x = 0) ∧
      c * redLoadingIdem Q Λ ν t ht = c ∧ redLoadingIdem Q Λ ν s hs * c = c ∧
        ∃ (n : ℕ) (g : Fin n → TensorProductAlgebra k Q Λ ν), IsExactMulRight c g

/-- A chain of exact crossings from `s` to a red-first loading. -/
def ExactReach {m : ℕ} (Λ : Fin m → I →₀ ℕ) (ν : Multiset I) (s : Seq (stendhalWeight m ν)) :
    Prop :=
  ∃ t, IsRedOrdered t ∧ IsRedFirst t ∧ Relation.ReflTransGen (ExactCrossPair Q Λ ν) s t

section Transport

variable {C : QuantumGroup.CartanDatum I}

/-- Adding a black strand on the right transports an exact crossing. -/
theorem exactCrossPair_appendBlack (hQ : IsRouquierQ C Q) {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ)
    (i : I) (ν : Multiset I) {s t : Seq (stendhalWeight ℓ ν)}
    (hst : ExactCrossPair Q Λ ν s t) :
    ExactCrossPair Q Λ ({i} + ν) (appendBlackLoading i ν s) (appendBlackLoading i ν t) := by
  obtain ⟨hs, ht, c, hinj, hc, hsc, n, g, hg⟩ := hst
  refine ⟨appendBlackLoading_ordered i ν s hs, appendBlackLoading_ordered i ν t ht,
    appendBlackNU (Q := Q) (Λ := Λ) i ν c, fun x hx h0 => ?_, ?_, ?_, _, _,
    isExactMulRight_appendBlack Q Λ i ν C hQ hg⟩
  · refine eq_zero_of_mul_map (appendBlackNU (Q := Q) (Λ := Λ) i ν)
      (isIdempotentElem_redLoadingIdem Q Λ ν s hs) c
      (appendBlack_ind_map_injective C hQ (rmulLIdeal_injective hinj)) x ?_ h0
    change x * appendBlack Q Λ i ν (redLoadingIdem Q Λ ν s hs) = x
    rw [appendBlack_mk_e]; exact hx
  · change appendBlack Q Λ i ν c * _ = _
    rw [show redLoadingIdem Q Λ ({i} + ν) (appendBlackLoading i ν t) _ =
      appendBlack Q Λ i ν (redLoadingIdem Q Λ ν t ht) from (appendBlack_mk_e Q Λ i ν t ht).symm,
      ← map_mul, hc]
    rfl
  · change _ * appendBlack Q Λ i ν c = appendBlack Q Λ i ν c
    rw [show redLoadingIdem Q Λ ({i} + ν) (appendBlackLoading i ν s) _ =
      appendBlack Q Λ i ν (redLoadingIdem Q Λ ν s hs) from (appendBlack_mk_e Q Λ i ν s hs).symm,
      ← map_mul, hsc]

/-- Adding a red strand on the right transports an exact crossing. -/
theorem exactCrossPair_appendRed (hQs : KLRSymm Q) {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ)
    (θ : Multiset I) {s t : Seq (stendhalWeight ℓ (θ + 0))}
    (hst : ExactCrossPair Q (Λ ∘ Fin.castSucc) (θ + 0) s t) :
    ExactCrossPair Q Λ (θ + 0) (appendRedLoading s) (appendRedLoading t) := by
  obtain ⟨hs, ht, c, hinj, hc, hsc, n, g, hg⟩ := hst
  refine ⟨(appendRedLoading_ordered_iff s).2 hs, (appendRedLoading_ordered_iff t).2 ht,
    emptyRedHom Q Λ θ c, fun x hx h0 => ?_, ?_, ?_, _, _, isExactMulRight_emptyRed Q Λ θ hQs hg⟩
  · refine eq_zero_of_mul_map (emptyRedHom Q Λ θ)
      (isIdempotentElem_redLoadingIdem Q _ _ s hs) c
      (emptyRed_lIdeal_ind_map_injective Q Λ θ hQs (rmulLIdeal_injective hinj)) x ?_ h0
    rw [emptyRedHom_apply, appendRed_mk_e]; exact hx
  · rw [emptyRedHom_apply, show redLoadingIdem Q Λ (θ + 0) (appendRedLoading t) _ =
      (appendRed Q Λ (θ + 0) (redLoadingIdem Q _ _ t ht)).val from (appendRed_mk_e Q Λ _ t ht).symm]
    change (appendRed Q Λ (θ + 0) c * appendRed Q Λ (θ + 0) _).val = _
    rw [← map_mul, hc]
  · rw [emptyRedHom_apply, show redLoadingIdem Q Λ (θ + 0) (appendRedLoading s) _ =
      (appendRed Q Λ (θ + 0) (redLoadingIdem Q _ _ s hs)).val from (appendRed_mk_e Q Λ _ s hs).symm]
    change (appendRed Q Λ (θ + 0) _ * appendRed Q Λ (θ + 0) c).val = _
    rw [← map_mul, hsc]

/-- Adding a red strand on the right transports an exact crossing, at any black weight. -/
theorem exactCrossPair_appendRed' (hQs : KLRSymm Q) {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ)
    (ν : Multiset I) {s t : Seq (stendhalWeight ℓ ν)}
    (hst : ExactCrossPair Q (Λ ∘ Fin.castSucc) ν s t) :
    ExactCrossPair Q Λ ν (appendRedLoading s) (appendRedLoading t) := by
  have key : ∀ s t : Seq (stendhalWeight ℓ (ν + 0)),
      ExactCrossPair Q (Λ ∘ Fin.castSucc) (ν + 0) s t →
        ExactCrossPair Q Λ (ν + 0) (appendRedLoading s) (appendRedLoading t) :=
    fun _ _ => exactCrossPair_appendRed Q hQs Λ ν
  rw [add_zero] at key
  exact key s t hst

end Transport

/-- The base crossings at red-first loadings are exact: moving the last red strand left past
the last black strand of a loading whose other red strands all come first. -/
def ExactBaseCrossing : Prop :=
  ∀ {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I) (β : Multiset I)
    (u : Seq (stendhalWeight ℓ β)),
    IsRedOrdered u → IsRedFirst u →
      ExactCrossPair Q Λ ({i} + β) (appendRedLoading (appendBlackLoading i β u))
        (appendBlackLoading i β (appendRedLoading u))

section Reach

open FirstWeight

variable {Q} {C : QuantumGroup.CartanDatum I} (hQ : IsRouquierQ C Q) (hQs : KLRSymm Q)
  (hbase : ExactBaseCrossing Q)

include hQ hbase in
/-- After adding a red strand on the right of a red-first loading, a chain of exact crossings
reaches a red-first loading. -/
theorem exactReach_appendRed_of_isRedFirst : ∀ (n : ℕ) {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ)
    (ν : Multiset I), Multiset.card ν = n → ∀ t : Seq (stendhalWeight ℓ ν),
      IsRedOrdered t → IsRedFirst t → ExactReach Q Λ ν (appendRedLoading t)
  | 0, ℓ, Λ, ν, hn, t, ht, _ =>
    ⟨_, (appendRedLoading_ordered_iff t).2 ht, isRedFirst_of_card_eq_zero hn _,
      Relation.ReflTransGen.refl⟩
  | n + 1, ℓ, Λ, ν, hn, t, ht, htf => by
    obtain ⟨j, hj⟩ := exists_terminal_inl_of_isRedFirst (by omega) t htf
    obtain ⟨β, rfl⟩ : ∃ β, ν = {j} + β :=
      ⟨_, by rw [Multiset.singleton_add, Multiset.cons_erase (mem_of_lbl_eq_inl t _ hj)]⟩
    obtain ⟨t₁, ht₁, rfl⟩ := exists_appendBlack_terminal t hj ht
    have hrf := (isRedFirst_appendBlackLoading_iff j β t₁).1 htf
    obtain ⟨r, hr, hrf', hch⟩ := exactReach_appendRed_of_isRedFirst n Λ β
      (by simp at hn; omega) t₁ ht₁ hrf
    refine ⟨appendBlackLoading j β r, appendBlackLoading_ordered j β r hr,
      (isRedFirst_appendBlackLoading_iff j β r).2 hrf', Relation.ReflTransGen.head
        (hbase Λ j β t₁ ht₁ hrf)
        (hch.lift _ fun a b h => exactCrossPair_appendBlack Q hQ Λ j β h)⟩

include hQ hQs hbase in
/-- **Every red-ordered loading reaches a red-first loading** by a chain of exact crossings. -/
theorem exactReach_of_isRedOrdered : ∀ (n : ℕ) {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (ν : Multiset I),
    ℓ + Multiset.card ν = n → ∀ s : Seq (stendhalWeight ℓ ν), IsRedOrdered s →
      ExactReach Q Λ ν s
  | 0, ℓ, Λ, ν, hn, s, hs =>
    ⟨s, hs, isRedFirst_of_card_eq_zero (by omega) s, Relation.ReflTransGen.refl⟩
  | n + 1, ℓ, Λ, ν, hn, s, hs => by
    cases h : s.lbl (terminalPos (ν := ν) (ℓ := ℓ) (by omega)) with
    | inl j =>
      obtain ⟨β, rfl⟩ : ∃ β, ν = {j} + β :=
        ⟨_, by rw [Multiset.singleton_add, Multiset.cons_erase (mem_of_lbl_eq_inl s _ h)]⟩
      obtain ⟨u, hu, rfl⟩ := exists_appendBlack_terminal s h hs
      obtain ⟨r, hr, hrf, hch⟩ := exactReach_of_isRedOrdered n Λ β
        (by simp at hn; omega) u hu
      exact ⟨appendBlackLoading j β r, appendBlackLoading_ordered j β r hr,
        (isRedFirst_appendBlackLoading_iff j β r).2 hrf,
        hch.lift _ fun a b h => exactCrossPair_appendBlack Q hQ Λ j β h⟩
    | inr r =>
      cases ℓ with
      | zero => exact r.elim0
      | succ ℓ =>
        have hpos :
            terminalPos (ν := ν) (ℓ := ℓ + 1) (by omega) = lastRedPosition ℓ ν := by
          apply Fin.ext
          change Multiset.card (stendhalWeight (ℓ + 1) ν) - 1 = ν.card + ℓ
          rw [cardinal_weight]; omega
        have hlast := terminal_red_last s hs r (hpos ▸ h)
        obtain ⟨⟨u, hu⟩, hus⟩ :=
          (appendRedOrderedEquiv (ℓ := ℓ) (ν := ν)).surjective ⟨s, hs, hlast⟩
        obtain rfl : appendRedLoading u = s := congrArg Subtype.val hus
        obtain ⟨r₁, hr₁, hrf₁, hch₁⟩ := exactReach_of_isRedOrdered n (Λ ∘ Fin.castSucc) ν
          (by omega) u hu
        obtain ⟨r₂, hr₂, hrf₂, hch₂⟩ :=
          exactReach_appendRed_of_isRedFirst hQ hbase _ Λ ν rfl r₁ hr₁ hrf₁
        exact ⟨r₂, hr₂, hrf₂,
          (hch₁.lift _ fun a b h => exactCrossPair_appendRed' Q hQs Λ ν h).trans hch₂⟩

end Reach

section Chain

variable {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (ν : Multiset I)

local notation "T" => TensorProductAlgebra k Q Λ ν
local notation "e⁰" => redFirstIdem Q Λ ν

/-- **The product of a chain of exact crossings**: if `T^λ` acts faithfully on `e⁰ T^λ` from the
right, a chain of exact crossings from `s` to a red-first loading gives `θ ∈ e(s) T^λ e⁰` with
`x ↦ x θ` injective on `T^λ e(s)` and `T^λ / T^λ θ` without nonzero submodules killed by `e⁰`. -/
theorem exists_corner_of_exactChain (hfaith : ∀ y : T, (∀ a, e⁰ * a * y = 0) → y = 0)
    {s t : Seq (stendhalWeight ℓ ν)} (ht : IsRedOrdered t) (htf : IsRedFirst t)
    (hch : Relation.ReflTransGen (ExactCrossPair Q Λ ν) s t) (hs : IsRedOrdered s) :
    ∃ c : T, redLoadingIdem Q Λ ν s hs * c = c ∧ c * e⁰ = c ∧
      (∀ x, x * redLoadingIdem Q Λ ν s hs = x → x * c = 0 → x = 0) ∧
        IsCornerFaithfulQuot e⁰ c := by
  revert hs
  induction hch using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro hs
    have hid := isIdempotentElem_redLoadingIdem Q Λ ν t ht
    refine ⟨redLoadingIdem Q Λ ν t ht, hid.eq, redLoadingIdem_mul_redFirstIdem Q Λ ν t ht htf,
      fun x hx h0 => hx.symm.trans h0, isCornerFaithfulQuot_idem hid hfaith⟩
  | head hst _ ih =>
    intro hs
    obtain ⟨hs₁, hs', c₁, hinj, hc, hsc, n, g, hg⟩ := hst
    obtain ⟨c₂, hsc₂, hc₂, hinj₂, hq₂⟩ := ih hs'
    refine ⟨c₁ * c₂, by rw [← mul_assoc, hsc], by rw [mul_assoc, hc₂], fun x hx h0 => ?_,
      isCornerFaithfulQuot_mul (isIdempotentElem_redLoadingIdem Q Λ ν _ hs') hc hsc₂ hinj₂
        (isCornerFaithfulQuot_of_isExactMulRight hfaith hg) hq₂⟩
    refine hinj x hx (hinj₂ _ (by rw [mul_assoc, hc]) ?_)
    rw [mul_assoc]; exact h0

/-- **A corner copresentation from chains**: if every red-ordered loading reaches a red-first
one by exact crossings and `T^λ` acts faithfully on `e⁰ T^λ` from the right, then `T^λ` has a
corner copresentation with respect to `e⁰`. -/
theorem hasCornerCopresentation_redFirstIdem_of_exactReach
    (hfaith : ∀ y : T, (∀ a, e⁰ * a * y = 0) → y = 0)
    (hreach : ∀ s, IsRedOrdered s → ExactReach Q Λ ν s) :
    HasCornerCopresentation e⁰ := by
  classical
  have hc : ∀ s : TensorProductAlgebra.OrderedLoading (ℓ := ℓ) ν, ∃ c : T,
      TensorProductAlgebra.boundaryIdem Q Λ ν s * c = c ∧ c * e⁰ = c ∧
        (∀ x, x * TensorProductAlgebra.boundaryIdem Q Λ ν s = x → x * c = 0 → x = 0) ∧
          IsCornerFaithfulQuot e⁰ c := fun s => by
    obtain ⟨t, ht, htf, hch⟩ := hreach s.1 s.2
    exact exists_corner_of_exactChain Q Λ ν hfaith ht htf hch s.2
  choose c hpc hce hinj hq using hc
  exact hasCornerCopresentation_of_family
    (TensorProductAlgebra.completeOrthogonalIdempotents_boundaryIdem (k := k) Q Λ ν) c hpc hce
    hinj hq

end Chain

end Categorification.Stendhal

namespace Categorification.Stendhal

section Std

open KLR KL3.Diagram

open scoped Classical

variable {I : Type} {k : Type} [Field k] {C : QuantumGroup.CartanDatum I}
  {Q : I → I → MvPolynomial (Fin 2) k} (hR : IsRouquierQ C Q)
  (hQs : KLRSymm Q)

local notation "QL" => Q

include hR hQs in
/-- `T^λ` acts faithfully on `e⁰ T^λ` from the right (Webster, arXiv:1309.3796v3, Lemma 5.25,
reflected by the anti-involution): if `e⁰ a y = 0` for every `a`, then `y = 0`. -/
theorem eq_zero_of_redFirstIdem_mul {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I)
    (y : TensorProductAlgebra k QL Λ ν)
    (hy : ∀ a, redFirstIdem QL Λ ν * a * y = 0) : y = 0 := by
  have h : tensorFlip y = 0 := eq_zero_of_mul_redFirstProjective hR hQs Λ ν _ fun c hc => by
    have h1 := congrArg tensorFlip (hy (tensorFlip c))
    rw [tensorFlip_mul, tensorFlip_mul, tensorFlip_tensorFlip, tensorFlip_redFirstIdem,
      map_zero, hc] at h1
    exact h1
  rw [← tensorFlip_tensorFlip y, h, map_zero]

include hR hQs in
/-- **Dominant dimension at least two, from exact base crossings** (reduction step for Webster,
arXiv:1309.3796v3, Corollary 5.32): if the base crossings at red-first loadings are exact, then
`T^λ` has a corner copresentation with respect to `e⁰`. -/
theorem hasCornerCopresentation_redFirstIdem_of_exactBaseCrossing
    (hbase : ExactBaseCrossing QL) {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I) :
    HasCornerCopresentation (redFirstIdem QL Λ ν) :=
  hasCornerCopresentation_redFirstIdem_of_exactReach QL Λ ν
    (eq_zero_of_redFirstIdem_mul hR hQs Λ ν)
    fun s hs => exactReach_of_isRedOrdered hR hQs hbase _ Λ ν rfl s hs

end Std

end Categorification.Stendhal

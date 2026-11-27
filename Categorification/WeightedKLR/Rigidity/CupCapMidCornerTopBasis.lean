/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapTopBasis

/-!
# Bases with dots on top for reduced words chosen loading by loading

Webster, arXiv:1309.3796v3, Proposition 4.16, with the reduced words allowed to depend on the
bottom loading. The KLR algebra is the sum of the right ideals `R(ν) e(i)`, and the terms of the
basis with dots on top ending in `e(i)` form a basis of `R(ν) e(i)` for every choice of reduced
words; so the reduced word of `w` may be chosen separately for each bottom loading `i`
(`KLRAlgebra.lbasisSeq`). The same holds for the basis of `T̃^λ` with dots on top
(`Stendhal.topBasisSeq`), whose terms are the terms `topTerm` of `CupCapTopBasis`, one word
choice for each loading.

In the proof of Lemma 7.17 for a cap after `λ_j`, the window of the strands at the maximum sits at
a position depending on the loading, and the reduced word adapted to the window depends on it.

## Main definitions

* `KLRAlgebra.lbasisSeq`: KL I, Theorem 2.5 with dots on top, words chosen per loading.
* `Stendhal.IsTopTermSeq`, `Stendhal.topTermSeq`, `Stendhal.topBasisSeq`: the same for `T̃^λ`.
-/

set_option backward.isDefEq.respectTransparency false

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace Categorification

open MvPolynomial TypeA Equiv

namespace KLR.KLRAlgebra

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} (hsym : KLRSymm Q) {κ : Multiset I}

local notation "m" => Multiset.card κ

theorem lbasis_mul_e (ρ : Perm (Fin m) → List ℕ) (hρ : ∀ w, IsReduced m (ρ w) ∧
    wordProd m (ρ w) = w) (b : Seq κ × Perm (Fin m) × (Fin m →₀ ℕ)) (i : Seq κ) :
    lbasis hsym ρ hρ b * e i = if b.1 = i then lbasis hsym ρ hρ b else 0 := by
  rw [lbasis_apply, mul_assoc, e_mul_e]
  split_ifs <;> simp

variable (ρ : Seq κ → Perm (Fin (Multiset.card κ)) → List ℕ)
  (hρ : ∀ (i : Seq κ) (w : Perm (Fin (Multiset.card κ))),
    IsReduced (Multiset.card κ) (ρ i w) ∧ wordProd (Multiset.card κ) (ρ i w) = w)

/-- The term `x^d ψ_{ρ_i w} e(i)`, with the word chosen for the bottom loading `i`. -/
noncomputable def lbasisSeqElt (b : Seq κ × Perm (Fin m) × (Fin m →₀ ℕ)) : KLRAlgebra k Q κ :=
  pol (monomial b.2.2 1) * ψw (ρ b.1 b.2.1) * e b.1

theorem lbasis_eq_lbasisSeqElt (i : Seq κ) (b : Seq κ × Perm (Fin m) × (Fin m →₀ ℕ))
    (hb : b.1 = i) : lbasis hsym (ρ i) (hρ i) b = lbasisSeqElt (Q := Q) ρ b := by
  rw [lbasis_apply, lbasisSeqElt, hb]

theorem lbasis_mul_e_eq (i : Seq κ) (b : Seq κ × Perm (Fin m) × (Fin m →₀ ℕ)) :
    lbasis hsym (ρ i) (hρ i) b * e i = if b.1 = i then lbasisSeqElt (Q := Q) ρ b else 0 := by
  rw [lbasis_mul_e]
  split_ifs with h
  · exact lbasis_eq_lbasisSeqElt hsym ρ hρ i b h
  · rfl

include hsym hρ in
theorem linearIndependent_lbasisSeqElt :
    LinearIndependent k (lbasisSeqElt (k := k) (Q := Q) ρ) := by
  classical
  rw [linearIndependent_iff']
  intro s g hg b hb
  have hli := (lbasis hsym (ρ b.1) (hρ b.1)).linearIndependent
  rw [linearIndependent_iff'] at hli
  refine hli (s.filter (·.1 = b.1)) g ?_ b (Finset.mem_filter.2 ⟨hb, rfl⟩)
  have h := congrArg (· * e (Q := Q) b.1) hg
  simp only [Finset.sum_mul, smul_mul_assoc, zero_mul] at h
  rw [Finset.sum_filter]
  refine Eq.trans ?_ h
  refine Finset.sum_congr rfl fun b' _ => ?_
  have h1 := lbasis_mul_e_eq hsym ρ hρ b.1 b'
  have h2 : lbasisSeqElt (Q := Q) ρ b' * e b.1 =
      if b'.1 = b.1 then lbasisSeqElt (Q := Q) ρ b' else 0 := by
    rw [lbasisSeqElt, mul_assoc, e_mul_e]
    split_ifs <;> simp
  rw [h2]
  split_ifs with h'
  · rw [← lbasis_eq_lbasisSeqElt hsym ρ hρ b.1 b' h']
  · rw [smul_zero]

include hsym hρ in
theorem span_lbasisSeqElt :
    ⊤ ≤ Submodule.span k (Set.range (lbasisSeqElt (k := k) (Q := Q) ρ)) := by
  classical
  intro x _
  rw [← mul_one x, ← sum_e, Finset.mul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  set B := lbasis hsym (ρ i) (hρ i)
  have hx : x * e i = ∑ b ∈ (B.repr (x * e i)).support, B.repr (x * e i) b • (B b * e i) := by
    conv_lhs => rw [← e_mul_self, ← mul_assoc, ← B.linearCombination_repr (x * e i)]
    rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => smul_mul_assoc _ _ _
  rw [hx]
  refine Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ ?_
  rw [lbasis_mul_e_eq hsym ρ hρ i b]
  split_ifs
  · exact Submodule.subset_span ⟨b, rfl⟩
  · exact Submodule.zero_mem _

/-- **KL I, Theorem 2.5, dots on top, words chosen per loading**: for reduced words `ρ_i w`
depending on the bottom loading `i`, the elements `x^d ψ_{ρ_i w} 1_i` form a basis of
`R(κ)`. -/
noncomputable def lbasisSeq : Module.Basis (Seq κ × Perm (Fin m) × (Fin m →₀ ℕ)) k
    (KLRAlgebra k Q κ) :=
  Module.Basis.mk (linearIndependent_lbasisSeqElt hsym ρ hρ) (span_lbasisSeqElt hsym ρ hρ)

theorem lbasisSeq_apply (b : Seq κ × Perm (Fin m) × (Fin m →₀ ℕ)) :
    lbasisSeq hsym ρ hρ b = pol (monomial b.2.2 1) * ψw (ρ b.1 b.2.1) * e b.1 :=
  Module.Basis.mk_apply _ _ _

end KLR.KLRAlgebra

namespace Stendhal

open KLR StendhalAlgebraAllOrders

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)

variable (ρ : KLR.Seq (stendhalWeight ℓ ν) → Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) →
  List ℕ)

/-- The terms `x^u ψ_{ρ_i w} e(i)` with dots on top surviving in `T̃^λ` (`IsTopTerm`), for the
word chosen for the bottom loading `i`. -/
def IsTopTermSeq (b : KLR.Seq μ × Perm (Fin m) × (Fin m →₀ ℕ)) : Prop := IsTopTerm (ρ b.1) b

variable {ρ}

variable (Q Λ) in
/-- The term `x^u ψ_{ρ_i w} e(i)` as an element of `T̃^λ`. -/
noncomputable def topTermSeq (hρ : ∀ i w, wordProd m (ρ i w) = w)
    (b : {b // IsTopTermSeq ρ b}) : StendhalAlgebra k Q Λ ν :=
  topTerm Q Λ (hρ b.1.1) ⟨b.1, b.2⟩

theorem topTermSeq_val (hρ : ∀ i w, wordProd m (ρ i w) = w) (b : {b // IsTopTermSeq ρ b}) :
    (topTermSeq Q Λ hρ b).1 = ofKLR k Q Λ ν (topElt (ρ b.1.1) b.1) :=
  rfl

theorem toKLR_topTermSeq (hρ : ∀ i w, wordProd m (ρ i w) = w) (b : {b // IsTopTermSeq ρ b}) :
    toKLR k Q Λ ν (stendhalValₗ (topTermSeq Q Λ hρ b)) = topElt (ρ b.1.1) b.1 :=
  toKLR_topTerm (hρ b.1.1) ⟨b.1, b.2⟩

/-- The terms with dots on top, words chosen per loading, are linearly independent in `T̃^λ`
for symmetric `Q`. -/
theorem linearIndependent_topTermSeq (hQ : KLRSymm Q)
    (hρ : ∀ i w, IsReduced m (ρ i w) ∧ wordProd m (ρ i w) = w) :
    LinearIndependent k (topTermSeq Q Λ (ν := ν) (fun i w => (hρ i w).2)) := by
  have hB := (KLRAlgebra.lbasisSeq (stendhalQ_symm (Q := Q) (Λ := Λ) hQ) ρ hρ).linearIndependent
  refine LinearIndependent.of_comp ((toKLR k Q Λ ν).toLinearMap ∘ₗ stendhalValₗ) ?_
  have : (⇑((toKLR k Q Λ ν).toLinearMap ∘ₗ stendhalValₗ) ∘
      topTermSeq Q Λ (ν := ν) (fun i w => (hρ i w).2)) =
      KLRAlgebra.lbasisSeq (stendhalQ_symm (Q := Q) (Λ := Λ) hQ) ρ hρ ∘ Subtype.val := by
    funext b
    simp only [Function.comp_apply, LinearMap.coe_comp, AlgHom.toLinearMap_apply,
      KLRAlgebra.lbasisSeq_apply]
    exact toKLR_topTermSeq _ b
  rw [this]
  exact hB.comp _ Subtype.val_injective

/-- The terms with dots on top, words chosen per loading, span `T̃^λ` for symmetric `Q`. -/
theorem span_topTermSeq (hQ : KLRSymm Q)
    (hρ : ∀ i w, IsReduced m (ρ i w) ∧ wordProd m (ρ i w) = w) :
    ⊤ ≤ Submodule.span k (Set.range (topTermSeq Q Λ (ν := ν) (fun i w => (hρ i w).2))) := by
  classical
  intro x _
  have hx' := (Subsemigroup.mem_corner_iff isIdempotentElem_redOrderedIdem).1 x.2
  obtain ⟨y, hy⟩ := ofKLR_surjective (k := k) (Q := Q) (Λ := Λ) (ν := ν) x.1
  let B := KLRAlgebra.lbasisSeq (stendhalQ_symm (Q := Q) (Λ := Λ) hQ) ρ hρ
  have hys : y = ∑ b ∈ (B.repr y).support, B.repr y b • topElt (ρ b.1) b := by
    conv_lhs => rw [← B.linearCombination_repr y]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [KLRAlgebra.lbasisSeq_apply]
    rfl
  have hx : x = ∑ b ∈ (B.repr y).support,
      if h : IsTopTermSeq ρ b then
        B.repr y b • topTermSeq Q Λ (fun i w => (hρ i w).2) ⟨b, h⟩ else 0 := by
    apply stendhalValₗ_injective
    rw [map_sum]
    change x.1 = _
    rw [← hx'.2, ← hx'.1, ← hy]
    conv_lhs => rw [hys]
    rw [map_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_smul, mul_smul_comm, smul_mul_assoc,
      ro_mul_ofKLR_topElt_mul_ro (fun w => (hρ b.1 w).2)]
    by_cases h : IsTopTermSeq ρ b
    · rw [dite_eq_left_of_eq_true (eq_true h),
        ite_eq_left_of_eq_true _ _ (eq_true (show IsTopTerm (ρ b.1) b from h)), map_smul]; rfl
    · rw [dite_eq_right_of_eq_false (eq_false h),
        ite_eq_right_of_eq_false _ _ (eq_false (show ¬ IsTopTerm (ρ b.1) b from h)), smul_zero,
        map_zero]
  rw [hx]
  refine Submodule.sum_mem _ fun b _ => ?_
  split_ifs with h
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  · exact Submodule.zero_mem _

variable (Q Λ) in
/-- **A basis of `T̃^λ` with dots on top, words chosen per loading** (arXiv:1309.3796v3,
Proposition 4.16) for symmetric `Q`: the terms `x^u ψ_{ρ_i w} e(i)` with `IsTopTermSeq`. -/
noncomputable def topBasisSeq (hQ : KLRSymm Q) (ρ : KLR.Seq μ → Perm (Fin m) → List ℕ)
    (hρ : ∀ i w, IsReduced m (ρ i w) ∧ wordProd m (ρ i w) = w) :
    Module.Basis {b // IsTopTermSeq (ν := ν) (ℓ := ℓ) ρ b} k (StendhalAlgebra k Q Λ ν) :=
  Module.Basis.mk (linearIndependent_topTermSeq hQ hρ) (span_topTermSeq hQ hρ)

theorem topBasisSeq_apply (hQ : KLRSymm Q) (ρ : KLR.Seq μ → Perm (Fin m) → List ℕ)
    (hρ : ∀ i w, IsReduced m (ρ i w) ∧ wordProd m (ρ i w) = w)
    (b : {b // IsTopTermSeq (ν := ν) ρ b}) :
    topBasisSeq Q Λ hQ ρ hρ b = topTermSeq Q Λ (fun i w => (hρ i w).2) b :=
  Module.Basis.mk_apply _ _ _

end Stendhal

end Categorification

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.OneBlackFirstPairFiltration
import Categorification.WeightedKLR.RedStrands.OneBlackPairKernel

/-!
# The one-black higher filtration for an arbitrary adjacent pair

Webster, arXiv:1309.3796v2, proof of Lemma 6.8 at (6.21).
A single crossing across a retained red gives a higher projective step.
When the black reaches the omitted red, the two crossings across the pair
give one higher step. These steps construct the retained-kernel filtration.
-/

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLRAlgebra TypeA MulOpposite
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type} [DecidableEq I] [CommRing k] {ℓ : ℕ} {i : I}
variable (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
local notation "ν₁" => (Singleton.singleton i : Multiset I)
local notation "μ" => stendhalWeight ℓ ν₁
local notation "n" => Multiset.card μ


/-- Extract the two exact crossing tests from the uniform one-black tests. -/
theorem nonempty_kernelEquiv_across_pair_of_ordinaryTests
    {s t u : KLR.Seq (stendhalWeight ℓ (Singleton.singleton i : Multiset I))} (j : ℕ)
    (a b : Fin ℓ) {L M : List (Fin ℓ)}
    (hs : redWord s = L ++ a :: b :: M) (word : redWord s = List.finRange ℓ)
    (h₁ : sadj n (j + 1) • s = t) (h₂ : sadj n j • t = u)
    (ho : redWord u = redWord s) (hlt : adjacentBlockRoot a b s < adjacentBlockRoot a b u)
    (hj : j + 2 < n) (ha : s.lbl ⟨j, by omega⟩ = .inr a)
    (hr : s.lbl ⟨j + 1, by omega⟩ = .inr b) (hb : s.lbl ⟨j + 2, hj⟩ = .inl i)
    (hQ : KLRSymm Q) (tests : OrdinaryOneBlackTests Q Λ (i := i)) :
    Nonempty (rIdeal (orderedLoadingIdemAt Q Λ (redWord s) u ho) ≃ₗ[(IsIdempotentElem.Corner
      (isIdempotentElem_violMk_redProj k Q Λ ν₁ (redWord s)))ᵐᵒᵖ]
      blockLoadingKernel Q Λ s a b) := by
  have hsOrdered := (redWord_eq_finRange_iff s).1 word
  have htWord : redWord t = redWord s := by
    rw [← h₁]
    exact redWord_sadj_smul s hj (by rw [hr, hb]; simp)
  have htOrdered := (redWord_eq_finRange_iff t).1 (htWord.trans word)
  have hj' : j + 1 < n := by omega
  have hb' : t.lbl ⟨j + 1, hj'⟩ = .inl i := by
    have e : t.lbl ⟨j + 1, hj'⟩ = s.lbl (sadj n (j + 1) ⟨j + 1, hj'⟩) := by
      rw [← h₁]
      exact sadj_smul_apply (j + 1) s _
    rw [e, sadj_apply_left hj]
    exact hb
  have test₁ : OrdinaryCutCrossingTest Q Λ s (sadj n (j + 1) • s) (j + 1) :=
    tests s hsOrdered (j + 1) hj hb
  have test₂ : OrdinaryCutCrossingTest Q Λ t (sadj n j • t) j :=
    tests t htOrdered j hj' hb'
  exact nonempty_kernelEquiv_of_twoCrossingTests Q Λ j a b hs word h₁ h₂ ho hlt hj ha hr hb hQ
    (h₁ ▸ test₁) (h₂ ▸ test₂)

end Categorification.Stendhal.BraidedStendhalAlgebra

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLRAlgebra TypeA ModuleFiltration MulOpposite
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type} [DecidableEq I] [CommRing k] {ℓ : ℕ} {i : I}
local notation "ν" => (Singleton.singleton i : Multiset I)
local notation "μ" => stendhalWeight ℓ ν
local notation "n" => Multiset.card μ
local notation "C" => {s : Seq μ // redWord s = List.finRange ℓ}
variable (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)

private theorem pairTestAt_of_swap
    (tests : OrdinaryOneBlackTests Q Λ (i := i))
    (s t : C) (j : ℕ) (hj : j + 1 < n)
    (hb : s.1.lbl ⟨j + 1, hj⟩ = .inl i) (ht : sadj n j • s.1 = t.1) :
    OrdinaryCutCrossingTest Q Λ s.1 t.1 j := by
  have test : OrdinaryCutCrossingTest Q Λ s.1 (sadj n j • s.1) j :=
    tests s.1 ((redWord_eq_finRange_iff _).1 s.2) j hj hb
  exact ht ▸ test

private theorem oneBlack_pair_cons_single
    (a b r : Fin ℓ) {L M : List (Fin ℓ)} (s t : C)
    (hs : redWord s.1 = L ++ a :: b :: M)
    (hlt : adjacentBlockRoot a b s.1 < adjacentBlockRoot a b t.1)
    (j : ℕ) (hj : j + 1 < n) (hstep : sadj n j • s.1 = t.1)
    (hr : s.1.lbl ⟨j, by omega⟩ = .inr r) (hb : s.1.lbl ⟨j + 1, hj⟩ = .inl i)
    (hQ : KLRSymm Q) (tests : OrdinaryOneBlackTests Q Λ (i := i))
    {tail : List C} (chain : HigherProjectiveChain Q Λ a b (List.finRange ℓ) t tail) :
    HigherProjectiveChain Q Λ a b (List.finRange ℓ) s (t :: tail) :=
  HigherProjectiveChain.cons_of_oneBlack_ordinary_test Q Λ hs hlt j hj hstep hr hb hQ
    (pairTestAt_of_swap Q Λ tests s t j hj hb hstep) chain

private theorem oneBlack_pair_cons_double
    (a b : Fin ℓ) {L M : List (Fin ℓ)} (s t u : C)
    (hs : redWord s.1 = L ++ a :: b :: M)
    (hlt : adjacentBlockRoot a b s.1 < adjacentBlockRoot a b u.1)
    (j : ℕ) (hj : j + 2 < n)
    (h₁ : sadj n (j + 1) • s.1 = t.1) (h₂ : sadj n j • t.1 = u.1)
    (ha : s.1.lbl ⟨j, by omega⟩ = .inr a) (hr : s.1.lbl ⟨j + 1, by omega⟩ = .inr b)
    (hb : s.1.lbl ⟨j + 2, hj⟩ = .inl i)
    (hQ : KLRSymm Q) (tests : OrdinaryOneBlackTests Q Λ (i := i))
    {tail : List C} (chain : HigherProjectiveChain Q Λ a b (List.finRange ℓ) u tail) :
    HigherProjectiveChain Q Λ a b (List.finRange ℓ) s (u :: tail) := by
  have ho : redWord u.1 = redWord s.1 := u.2.trans s.2.symm
  have h := nonempty_kernelEquiv_across_pair_of_ordinaryTests Q Λ j a b hs s.2
    h₁ h₂ ho hlt hj ha hr hb hQ tests
  refine .cons hlt ?_ chain
  have transport (κ : List (Fin ℓ)) (hκ : redWord s.1 = κ) :
      Nonempty ((rIdeal (orderedLoadingIdemAt Q Λ κ u.1 (ho.trans hκ))) ≃ₗ[
        (IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν κ))ᵐᵒᵖ]
        fixedOrderKernelObj Q Λ a b κ ⟨s.1, hκ⟩) := by
    subst κ
    exact h
  exact transport _ s.2

omit [DecidableEq I] in
private theorem oneBlack_move_black_left
    (s : C) (j : ℕ) (hj : j + 1 < n) {r : Fin ℓ}
    (hr : s.1.lbl ⟨j, by omega⟩ = .inr r)
    (hb : s.1.lbl ⟨j + 1, hj⟩ = .inl i) :
    ∃ t : C, sadj n j • s.1 = t.1 ∧ t.1.lbl ⟨j, by omega⟩ = .inl i := by
  let t : C := ⟨sadj n j • s.1, (redWord_sadj_smul s.1 hj (by rw [hr, hb]; simp)).trans s.2⟩
  refine ⟨t, rfl, ?_⟩
  change (sadj n j • s.1).1 _ = _
  rw [sadj_smul_apply, sadj_apply_left hj]
  exact hb

omit [DecidableEq I] in
private theorem oneBlack_label_before_after_omitted
    (s t : Seq μ) (j : ℕ) (hj : j + 2 < n) (hstep : sadj n (j + 1) • s = t)
    {a : Fin ℓ} (ha : s.lbl ⟨j, by omega⟩ = .inr a) :
    t.lbl ⟨j, by omega⟩ = .inr a := by
  rw [← hstep]
  change (sadj n (j + 1) • s).1 _ = _
  rw [sadj_smul_apply, sadj_apply_of_ne _ (by change j ≠ j + 1; omega)
    (by change j ≠ j + 1 + 1; omega)]
  exact ha

private theorem oneBlack_pair_chain_step
    (a b : Fin ℓ) (hab : a.val + 1 = b.val) {L M : List (Fin ℓ)}
    (hword : List.finRange ℓ = L ++ a :: b :: M)
    (s : C) (p : Fin n) (hp : s.1.lbl p = .inl i) (hk : 1 < p.val)
    (hQ : KLRSymm Q) (tests : OrdinaryOneBlackTests Q Λ (i := i)) :
    ∃ (t : C) (u : Fin n), u.val < p.val ∧ t.1.lbl u = .inl i ∧
      ∀ tail : List C, HigherProjectiveChain Q Λ a b (List.finRange ℓ) t tail →
        HigherProjectiveChain Q Λ a b (List.finRange ℓ) s (t :: tail) := by
  let j := p.val - 1
  have hj : j + 1 < n := by have := p.isLt; omega
  have hpos : (⟨j + 1, hj⟩ : Fin n) = p := Fin.ext (by change j + 1 = p.val; omega)
  have hb : s.1.lbl ⟨j + 1, hj⟩ = .inl i := hpos.symm ▸ hp
  have hn : (⟨j, by omega⟩ : Fin n) ≠ ⟨j + 1, hj⟩ := by
    intro e
    have h := congrArg Fin.val e
    change j = j + 1 at h
    omega
  obtain ⟨r, hr⟩ := oneBlack_hasRed_at_ne s.1 hb hn
  obtain ⟨t, ht, hbt⟩ := oneBlack_move_black_left s j hj hr hb
  have hs : redWord s.1 = L ++ a :: b :: M := s.2.trans hword
  by_cases hrb : r = b
  · subst r
    let l := j - 1
    have hl : l + 2 < n := by
      have := p.isLt
      omega
    have heq : j = l + 1 := by omega
    have hsRed : IsRedOrdered s.1 := (redWord_eq_finRange_iff s.1).1 s.2
    have hr' : s.1.lbl ⟨l + 1, by omega⟩ = .inr b := by
      have H : (⟨l + 1, by omega⟩ : Fin n) = ⟨j, by omega⟩ := Fin.ext heq.symm
      simpa only [H] using hr
    have hb' : s.1.lbl ⟨l + 2, hl⟩ = .inl i := by
      have H : (⟨l + 2, hl⟩ : Fin n) = ⟨j + 1, hj⟩ := Fin.ext (by change l + 2 = j + 1; omega)
      simpa only [H] using hb
    have ha := oneBlack_retainedRed_of_omittedRed_beforeBlack s.1 hsRed hab l hl hr' hb'
    have ht' : sadj n (l + 1) • s.1 = t.1 := by rw [← heq]; exact ht
    have ha' := oneBlack_label_before_after_omitted s.1 t.1 l hl ht' ha
    have hl' : l + 1 < n := by omega
    have hbt' : t.1.lbl ⟨l + 1, hl'⟩ = .inl i := by
      have H : (⟨l + 1, hl'⟩ : Fin n) = ⟨j, by omega⟩ := Fin.ext heq.symm
      simpa only [H] using hbt
    obtain ⟨u, hu, hbu⟩ := oneBlack_move_black_left t l hl' ha' hbt'
    have he := adjacentBlockRoot_oneBlack_eq_sadj_omitted s.1 hs hl hr' hb'
    rw [ht'] at he
    have htw : redWord t.1 = L ++ a :: b :: M := t.2.trans hword
    have hab' : a ≠ b := by
      intro e
      have e' := congrArg Fin.val e
      omega
    have hlt := adjacentBlockRoot_oneBlack_lt_sadj t.1 htw hl' ha' hbt' hab'
    rw [hu] at hlt
    have hlt' := he.trans_lt hlt
    refine ⟨u, ⟨l, by omega⟩, by change l < p.val; omega, hbu, ?_⟩
    intro tail chain
    exact oneBlack_pair_cons_double Q Λ a b s t u hs hlt' l hl ht' hu ha hr' hb' hQ tests chain
  · have hlt := adjacentBlockRoot_oneBlack_lt_sadj s.1 hs hj hr hb hrb
    rw [ht] at hlt
    refine ⟨t, ⟨j, by omega⟩, by change j < p.val; omega, hbt, ?_⟩
    intro tail chain
    exact oneBlack_pair_cons_single Q Λ a b r s t hs hlt j hj ht hr hb hQ tests chain

/-- A canonical adjacent pair gives a finite chain of actual
higher projective identifications at one black. -/
theorem oneBlack_pair_higherProjectiveChain_of_tests
    (a b : Fin ℓ) (hab : a.val + 1 = b.val)
    {L M : List (Fin ℓ)} (hword : List.finRange ℓ = L ++ a :: b :: M)
    (hQ : KLRSymm Q) (tests : OrdinaryOneBlackTests Q Λ (i := i))
    (s : C) (p : Fin n) (hp : s.1.lbl p = .inl i) :
    ∃ tail : List C, HigherProjectiveChain Q Λ a b (List.finRange ℓ) s tail := by
  suffices aux : ∀ k : ℕ, ∀ (s : C) (p : Fin n), s.1.lbl p = .inl i → p.val = k →
      ∃ tail : List C, HigherProjectiveChain Q Λ a b (List.finRange ℓ) s tail from aux _ s p hp rfl
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro s p hp hlen
    by_cases hk : 1 < p.val
    · obtain ⟨t, u, hlt, ht, step⟩ :=
        oneBlack_pair_chain_step Q Λ a b hab hword s p hp hk hQ tests
      obtain ⟨tail, htail⟩ := ih u.val (hlen ▸ hlt) t u ht rfl
      exact ⟨t :: tail, step tail htail⟩
    · have hs : redWord s.1 = L ++ a :: b :: M := s.2.trans hword
      have hsRed : IsRedOrdered s.1 := (redWord_eq_finRange_iff s.1).1 s.2
      exact ⟨[], HigherProjectiveChain.nil_of_maximal Q Λ fun _ hw hlt =>
        isViolated_of_strictly_higher_oneBlack_early hs hsRed hw p hp (le_of_not_gt hk) hlt⟩

end Categorification.Stendhal.BraidedStendhalAlgebra

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR ModuleFiltration
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type} [DecidableEq I] [CommRing k] {ℓ : ℕ} {i : I}
local notation "ν" => (Singleton.singleton i : Multiset I)
local notation "μ" => stendhalWeight ℓ ν
local notation "C" => {s : Seq μ // redWord s = List.finRange ℓ}

/-- The consecutive entries of a canonical red word have consecutive values. -/
private theorem canonicalAdjacentRedValues {ℓ : ℕ} {a b : Fin ℓ} {L M : List (Fin ℓ)}
    (hword : List.finRange ℓ = L ++ a :: b :: M) : a.val + 1 = b.val := by
  have len := congrArg List.length hword
  simp only [List.length_finRange, List.length_append, List.length_cons] at len
  have h₀ : L.length < (List.finRange ℓ).length := by rw [List.length_finRange]; omega
  have h₁ : L.length + 1 < (List.finRange ℓ).length := by rw [List.length_finRange]; omega
  have ha : (List.finRange ℓ)[L.length]? = some a := by
    rw [hword, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  have hb : (List.finRange ℓ)[L.length + 1]? = some b := by
    rw [hword, List.getElem?_append_right (Nat.le_succ _)]
    rw [show L.length.succ - L.length = 1 by omega]
    rfl
  rw [List.getElem?_eq_getElem h₀, List.getElem_finRange] at ha
  rw [List.getElem?_eq_getElem h₁, List.getElem_finRange] at hb
  have ea := congrArg Fin.val (Option.some.inj ha)
  have eb := congrArg Fin.val (Option.some.inj hb)
  change L.length = a.val at ea
  change L.length + 1 = b.val at eb
  omega

/-- The actual kernel has a finite higher partial-standard filtration for any
adjacent pair in the canonical red order, given the ordinary crossing tests. -/
theorem oneBlack_pair_hasFiltration_of_tests
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
    (a b : Fin ℓ) {L M : List (Fin ℓ)}
    (hword : List.finRange ℓ = L ++ a :: b :: M)
    (hQ : KLRSymm Q) (tests : OrdinaryOneBlackTests Q Λ (i := i)) (s : C) :
    ∃ tail : List C,
      HasFiltration (fun t : C => blockPartialStandardAt Q Λ t.1 a b (List.finRange ℓ) t.2)
        tail (fixedOrderKernelObj Q Λ a b (List.finRange ℓ) s) := by
  have hm : (Sum.inl i : I ⊕ Fin ℓ) ∈ μ := by simp [stendhalWeight]
  rw [← show Finset.univ.val.map s.1.lbl = μ from s.1.2, Multiset.mem_map] at hm
  obtain ⟨p, _, hp⟩ := hm
  obtain ⟨tail, chain⟩ :=
    oneBlack_pair_higherProjectiveChain_of_tests Q Λ a b (canonicalAdjacentRedValues hword) hword hQ tests s p hp
  exact ⟨tail, HigherProjectiveChain.hasFiltration Q Λ a b (List.finRange ℓ) chain⟩

end Categorification.Stendhal.BraidedStendhalAlgebra

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR ModuleFiltration QuantumGroup KL3.Diagram
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type} [DecidableEq I] [Field k] {ℓ : ℕ} {D : CartanDatum I}
local notation "QL" => CL.qCL (CL.CLScalars.kl : CL.CLScalars D k)

/-- The one-black kernel for any adjacent pair in canonical red order has an
actual finite higher partial-standard filtration at standard parameters. -/
theorem oneBlack_pair_hasFiltration_standard
    (hR : IsRouquierQ D QL) (hQ : KLRSymm QL) (i : I) (Λ : Fin ℓ → I →₀ ℕ)
    (a b : Fin ℓ) {L M : List (Fin ℓ)} (hword : List.finRange ℓ = L ++ a :: b :: M)
    (s : {s : Seq (stendhalWeight ℓ ({i} : Multiset I)) // redWord s = List.finRange ℓ}) :
    ∃ tail : List {t : Seq (stendhalWeight ℓ ({i} : Multiset I)) // redWord t = List.finRange ℓ},
      HasFiltration (fun t => blockPartialStandardAt QL Λ t.1 a b (List.finRange ℓ) t.2)
        tail (fixedOrderKernelObj QL Λ a b (List.finRange ℓ) s) := by
  have tests : OrdinaryOneBlackTests QL Λ (i := i) :=
    oneBlack_crossing_injective_standard hR hQ i Λ
  exact oneBlack_pair_hasFiltration_of_tests QL Λ a b hword hQ tests s

end Categorification.Stendhal.BraidedStendhalAlgebra

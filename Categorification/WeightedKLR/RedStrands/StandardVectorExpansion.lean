/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LoadingVectorExpansion
import Categorification.WeightedKLR.RedStrands.CoarseAssignment
import Categorification.WeightedKLR.RedStrands.PhiWordsLabels
import Categorification.KLR.GradedBasis
import Categorification.WeightedKLR.RedStrands.RootStandardEndRouquier

/-!
# Webster's Lemma 5.19

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, Lemma 5.19:
for a red-ordered loading `(i, κ)`,

`v^κ_i = ∑_{φ ∈ Φ} q^{-deg x_φ} s^{κφ}_{iφ}`,

where `v^κ_i` is the vector of the loading in `V^{λ_1} ⊗ ⋯ ⊗ V^{λ_ℓ}` (lowering by `F_i` through
the coproduct at each black strand), `s^κ_i = F_{i_{κ(2)}} ⋯ F_{i_1} v_{λ_1} ⊗ ⋯` is the pure
tensor of its blocks (Webster's notation before Proposition 5.6), `Φ` is the set of block
assignments that put no black strand left of every red strand, `(iφ, κφ)` is the bottom of
the diagram `x_φ` and `deg x_φ = deg(ψ_{ρφ} e(i, κ))` its degree for the grading of
Definition 4.4.

## Main definitions

* `FirstWeight.standardVector`: Webster's `s^κ_i` of a loading.

## Main results

* `FirstWeight.assignVector_eq_standardVector_phiBottom`: the assignment vector of `φ` is
  `s^{κφ}_{iφ}`.
* `FirstWeight.crossExp_eq_degW`: the crossing exponent of `φ` is `deg x_φ`.
* `FirstWeight.tensorWordUndivided_eq_sum_standardVector`: Lemma 5.19.
-/

noncomputable section
namespace Categorification.Stendhal.FirstWeight

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop KLR TypeA Equiv
open scoped TensorProduct

local notation "𝕍" => (RatFunc.X : RatFunc ℚ)
local notation "𝕂" => RatFunc ℚ

variable {I : Type} [DecidableEq I] {ℓ : ℕ} {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)

section Blocks

variable {m' : ℕ}

/-- The positions of the black letters that `h` assigns to block `r + 1`, in order. -/
def blockPos (lbl : Fin m' → I ⊕ Fin ℓ) (h : Fin m' → ℕ) (r : ℕ) : List (Fin m') :=
  (List.finRange m').filter fun p => (lbl p).isRight = false ∧ h p = r + 1

omit [DecidableEq I] in
theorem blockWord_eq_filterMap (lbl : Fin m' → I ⊕ Fin ℓ) (h : Fin m' → ℕ) (r : ℕ) :
    blockWord lbl h r = (blockPos lbl h r).filterMap fun p => (lbl p).getLeft? := by
  rw [blockWord, blockPos, List.ofFn_eq_map]
  generalize List.finRange m' = L
  induction L with
  | nil => rfl
  | cons p L ih =>
    rw [List.map_cons, List.flatten_cons, ih, List.filter_cons]
    unfold blockLetter
    rcases hp : lbl p with i | r'
    · by_cases hh : h p = r + 1 <;> simp [hp, hh]
    · simp

end Blocks

section Bottom

omit [DecidableEq I] in
/-- `φ` keeps the order of the black strands it puts in one block. -/
theorem phiPerm_lt_of_block {s : Seq μ} (g : Fin m → ℕ) {p q : Fin m} (hpq : p < q)
    (hp : (s.lbl p).isRight = false) (hq : (s.lbl q).isRight = false) (h : g p = g q) :
    phiPerm s g p < phiPerm s g q := by
  refine (keyPerm_lt_iff (assignKey s.lbl g)).2 (.inr ⟨?_, hpq⟩)
  rw [assignKey_black g hp, assignKey_black g hq, h]

omit [DecidableEq I] in
theorem blockPos_phiBottom {s : Seq μ} (hs : IsRedOrdered s) {g : Fin m → ℕ} (hg : g ∈ assignments s.lbl)
    (r : ℕ) :
    blockPos (phiBottom s g).lbl (redsBefore (phiBottom s g).lbl) r =
      (blockPos s.lbl g r).map (phiPerm s g) := by
  refine List.Pairwise.eq_of_mem_iff (r := fun a b : Fin m => a < b) ?_ ?_ fun q => ?_
  · exact (List.pairwise_lt_finRange _).filter _
  · refine List.Pairwise.map _ (fun {p q} (hpq : phiPerm s g p < phiPerm s g q) => ?_) ?_
    · exact hpq
    · refine ((List.pairwise_lt_finRange _).filter _).imp_of_mem fun {p q} hp hq hpq => ?_
      have hp' := of_decide_eq_true (List.mem_filter.1 hp).2
      have hq' := of_decide_eq_true (List.mem_filter.1 hq).2
      exact phiPerm_lt_of_block g hpq hp'.1 hq'.1 (hp'.2.trans hq'.2.symm)
  · obtain ⟨p, rfl⟩ := (phiPerm s g).surjective q
    simp only [blockPos, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq,
      List.mem_map, EmbeddingLike.apply_eq_iff_eq, exists_eq_right, lbl_smul_apply]
    constructor
    · rintro ⟨hb, hr⟩
      exact ⟨hb, (redsBefore_phiBottom hs hg hb).symm.trans hr⟩
    · rintro ⟨hb, hr⟩
      exact ⟨hb, (redsBefore_phiBottom hs hg hb).trans hr⟩

omit [DecidableEq I] in
theorem blockWord_phiBottom {s : Seq μ} (hs : IsRedOrdered s) {g : Fin m → ℕ}
    (hg : g ∈ assignments s.lbl) (r : ℕ) :
    blockWord (phiBottom s g).lbl (redsBefore (phiBottom s g).lbl) r = blockWord s.lbl g r := by
  rw [blockWord_eq_filterMap, blockWord_eq_filterMap, blockPos_phiBottom hs hg, List.filterMap_map]
  congr 1
  funext p
  simp only [Function.comp_apply, lbl_smul_apply]

omit [DecidableEq I] in
/-- The crossing exponent of `g` is the degree of `ψ_{ρφ} e(s)` (for Webster's grading or any
other), since `φ` reverses exactly the pairs whose keys it reverses. -/
theorem crossExp_eq_degW {k : Type*} [CommRing k]
    {Q' : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k} (G : KLR.GradingDatum Q')
    {ρ : Perm (Fin m) → List ℕ} (hρ : ∀ w, IsReduced m (ρ w) ∧ wordProd m (ρ w) = w)
    (s : Seq μ) (g : Fin m → ℕ) :
    crossExp G.degΨ s.lbl g = G.degW (ρ (phiPerm s g)) s := by
  rw [GradingDatum.degW_eq_sum_invSet _ (hρ _).1, (hρ _).2, crossExp, invSet, Finset.sum_filter,
    ← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  refine if_congr ⟨fun ⟨h1, h2⟩ => ⟨h1, (keyPerm_lt_iff _).2 (.inl h2)⟩,
    fun ⟨h1, h2⟩ => ⟨h1, ?_⟩⟩ rfl rfl
  rcases (keyPerm_lt_iff _).1 h2 with h | ⟨-, h⟩
  · exact h
  · exact absurd (h.trans h1) (lt_irrefl _)

end Bottom

section Standard

variable {Y : Type*} [AddCommGroup Y] {D : LusztigCartanDatum I} {R : D.RootDatum Y}

/-- **Webster's `s^κ_i`** (arXiv:1309.3796v3, before Proposition 5.6): the pure tensor whose
factor `r` is `F_{i_k} ⋯ F_{i_1} v_{λ_r}` for the black letters `i_1, …, i_k` between the red
letters `r` and `r + 1`. -/
def standardVector (wt : Fin ℓ → Dom R) {m' : ℕ} (lbl : Fin m' → I ⊕ Fin ℓ) : TensorSpace wt :=
  assignVector wt lbl (redsBefore lbl)

/-- The assignment vector of `φ` is `s^{κφ}_{iφ}`. -/
theorem assignVector_eq_standardVector_phiBottom (wt : Fin ℓ → Dom R) {s : Seq μ}
    (hs : IsRedOrdered s) {g : Fin m → ℕ} (hg : g ∈ assignments s.lbl) :
    assignVector wt s.lbl g = standardVector wt (phiBottom s g).lbl := by
  unfold standardVector assignVector
  congr 1
  funext r
  rw [blockWord_phiBottom hs hg]

/-- Lemma 5.19 for a red-ordered loading and any grading whose red/black and black/black
crossing degrees are `⟨λ_j, α̃_i⟩` and `-α_l(α̃_i)`. -/
theorem loweringVector_eq_sum_standardVector (wt : Fin ℓ → Dom R) {k : Type*} [CommRing k]
    {Q' : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k} (G : KLR.GradingDatum Q')
    (hred : ∀ j i, G.degΨ (.inr j) (.inl i) = (wt j).1 (ktilde R i))
    (hblack : ∀ l i, G.degΨ (.inl l) (.inl i) = -R.root l (ktilde R i))
    {ρ : Perm (Fin m) → List ℕ} (hρ : ∀ w, IsReduced m (ρ w) ∧ wordProd m (ρ w) = w)
    {s : Seq μ} (hs : IsRedOrdered s) :
    loweringVector wt (List.ofFn s.lbl) =
      ∑ g ∈ (assignments s.lbl).toFinset.filter (IsNonviolating s.lbl),
        𝕍 ^ (-G.degW (ρ (phiPerm s g)) s) • standardVector wt (phiBottom s g).lbl := by
  rw [loweringVector_ofFn_eq_sum wt G.degΨ hred hblack s.lbl (redIndexed_of_isRedOrdered hs)
    (redCount_ofFn_lbl s).le, ← List.sum_toFinset _ (nodup_assignments _), Finset.sum_filter]
  refine Finset.sum_congr rfl fun g hg => ?_
  rw [List.mem_toFinset] at hg
  rw [expansionTerm, crossExp_eq_degW G hρ, assignVector_eq_standardVector_phiBottom wt hs hg]

end Standard

section Rouquier

omit [DecidableEq I] in
theorem ofFn_loading_lbl (w : TensorWord I ℓ) :
    List.ofFn w.loading.lbl = KLR.KLRAlgebra.expandDiv w.blocks := by
  apply List.ext_getElem (by simpa [stendhalWeight] using (congrArg Multiset.card
    w.blocks_weight).symm)
  intro a h1 h2
  rw [List.getElem_ofFn]
  rfl

variable {Y : Type} [AddCommGroup Y] {C : Categorification.QuantumGroup.CartanDatum I}
  {Rc : C.toLusztig.RootDatum Y} {k : Type} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}

/-- **Webster's Lemma 5.19** (arXiv:1309.3796v3): for a tensor word `w` with boundary loading
`(i, κ)` (red-ordered), `v^κ_i = ∑_{φ ∈ Φ} q^{-deg x_φ} s^{κφ}_{iφ}`. Here `v^κ_i` applies
ordinary powers of `F_i` at the black blocks, `Φ` is the set of block assignments putting no
black strand left of every red strand, `φ • (i, κ)` is the bottom of `x_φ = ψ_{ρφ} e(i, κ)`,
and `deg x_φ` is its degree for the grading of Definition 4.4 with Rouquier parameters. -/
theorem tensorWordUndivided_eq_sum_standardVector (hR : KLR.IsRouquierQ C Q)
    (Λ : Fin ℓ → I →₀ ℕ) (w : TensorWord I ℓ) (wt : Fin ℓ → Dom Rc)
    (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (Rc.coroot i))
    {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ w.content.toMultiset))) → List ℕ}
    (hρ : ∀ τ, IsReduced (Multiset.card (stendhalWeight ℓ w.content.toMultiset)) (ρ τ) ∧
      wordProd _ (ρ τ) = τ) :
    tensorWordUndivided w wt =
      ∑ g ∈ (assignments w.loading.lbl).toFinset.filter (IsNonviolating w.loading.lbl),
        𝕍 ^ (-(StendhalAlgebra.rouquierStendhalGrading hR Λ).degW (ρ (phiPerm w.loading g))
          w.loading) • standardVector wt (phiBottom w.loading g).lbl := by
  have hd : ∀ i, Categorification.QuantumGroup.UDot.di C i = (C.toLusztig.d i : ℤ) := fun i => by
    have h1 := Categorification.QuantumGroup.UDot.two_mul_di C i
    have h2 := Categorification.QuantumGroup.PreF.two_mul_d C i
    omega
  rw [tensorWordUndivided_eq_loweringVector, ← ofFn_loading_lbl]
  refine loweringVector_eq_sum_standardVector wt _ (fun j i => ?_) (fun l i => ?_) hρ
    w.blocks_redOrdered
  · change Categorification.QuantumGroup.UDot.di C i * (Λ j i : ℤ) = _
    rw [ktilde, map_nsmul, hwt, hd, nsmul_eq_mul]
  · change hR.gradingDatum.degΨ l i = _
    rw [KLR.IsRouquierQ.gradingDatum_degΨ, root_ktilde_eq_dot]
    exact congrArg Neg.neg (C.symm l i)

end Rouquier


end Categorification.Stendhal.FirstWeight

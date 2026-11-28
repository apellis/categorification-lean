/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TildePhiCount
import Categorification.WeightedKLR.RedStrands.TildeRelLayers
import Categorification.WeightedKLR.RedStrands.TensorFinite
import Categorification.Algebra.Graded.DegreewiseLayerCount

/-!
# The layers of `T̃^λ e(s)` in a fixed degree

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Corollary 5.23. For any strict order `≺` containing Webster's order (for example a linear
extension of it), the surjection `S̃_{φ • s} → P̃_{⪰φ}/P̃_{≻φ}` (`tildeRelLayerMap_surjective`)
is injective in degree `n - deg x̃_φ`, for a red strand `λ₀` added on the left that is large
relative to the degrees involved (`mem_tildeLeftUpper_of_mul_mem_above`). The argument is
Webster's: in degree `n` the layers have dimension at most that of the standard modules, the
dimension of `P̃_n` is at most the sum of the layers, and the sum of the standard modules is
`dim P̃_n` (`finrank_tilde_lIdeal_grade_eq_sum_of_bound`). So every inequality is an equality.
Route hypothesis: `AllFiniteDeltaInjective`, inherited from `phiLayerEquiv` through the count.

## Main results

* `tildePhiElt_mem_grade`: `x̃_φ` is homogeneous of degree `deg x̃_φ`.
* `finrank_tilde_lIdeal_grade_eq_sum_of_bound`: the count with bounds on `Φ(s)` only.
* `finiteDimensional_stendhalGrade_of_le`: the degree-`j` piece of `T̃^λ` is finite-dimensional
  for `λ₀` large relative to `j`.
* `mem_tildeLeftUpper_of_mul_mem_above`: degreewise injectivity of the layer map.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR DirectSum _root_.Categorification.Graded _root_.Module TypeA Equiv

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Homogeneous

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ' : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ' : Fin ℓ' → I →₀ ℕ) (ν : Multiset I)
  (G' : KLR.GradingDatum (stendhalQ Q Λ'))

local notation "m'" => Multiset.card (stendhalWeight ℓ' ν)

/-- **`x̃_φ` is homogeneous** of the degree of `ψ_{ρ φ} e(s)`. -/
theorem tildePhiElt_mem_grade (ρ : Perm (Fin m') → List ℕ) {s : Seq (stendhalWeight ℓ' ν)}
    (hs : IsRedOrdered s) {g : Fin m' → ℕ} (hg : g ∈ assignments s.lbl) :
    tildePhiElt Q Λ' ρ hs hg ∈ stendhalGrade G' ν (G'.degW (ρ (phiPerm s g)) s) := by
  change StendhalAlgebraAllOrders.e (phiBottom s g) *
      StendhalAlgebraAllOrders.ofKLR k Q Λ' ν (KLRAlgebra.ψw (ρ (phiPerm s g))) *
      StendhalAlgebraAllOrders.e s ∈ allOrdersGrade G' ν _
  have h3 := SetLike.GradedMul.mul_mem (G'.e_mem_grade (phiBottom s g))
    (G'.ψw_mul_e_mem_grade (ρ (phiPerm s g)) s)
  rw [zero_add] at h3
  have h4 := Graded.mem_map_of_mem _ (StendhalAlgebraAllOrders.ofKLR k Q Λ' ν).toLinearMap h3
  simpa [allOrdersGrade, map_mul, mul_assoc, StendhalAlgebraAllOrders.e] using h4

end Homogeneous

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I)
  (G : KLR.GradingDatum (stendhalQ Q Λ))

local notation "μ" => stendhalWeight ℓ ν
local notation "μ'" => stendhalWeight (ℓ + 1) ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "G₀" => restrictFirstRedGrading Q Λ G
local notation "B" => StendhalAlgebra k Q (Λ ∘ Fin.succ) ν

/-- **Finite pieces**: for `λ₀` large relative to `j`, the degree-`j` piece of `T̃^λ` embeds in
the finite-dimensional `T^{(λ₀, λ)}`. -/
theorem finiteDimensional_stendhalGrade_of_le {C : QuantumGroup.CartanDatum I}
    (hR : IsRouquierQ C Q) {c j : ℤ} (hc : ∀ m' < -c, allOrdersGrade G₀ ν m' = ⊥)
    (hΛ : ∀ i ∈ ν, j + 2 * c < Λ 0 i * G.degX (.inl i)) :
    FiniteDimensional k (stendhalGrade G₀ ν j) := by
  have := tensorProductAlgebra_finite (Q := Q) Λ ν hR
  exact Module.Finite.of_injective
    ((prependRed Q Λ ν).toLinearMap.comp (stendhalGrade G₀ ν j).subtype)
    fun x y h => Subtype.ext (prependRed_injOn_degree Q Λ ν G₀ hc hΛ x.2 y.2 h)

/-- The degree-`j` part of a standard module of `T^{(λ₀, λ)}` whose loading does not begin
with `λ₀` is zero. -/
theorem stdGradedRank_eq_zero_of_not_prepend (t' : Seq μ') (ht' : IsRedOrdered t')
    (h : ∀ t, prependRedLoading t ≠ t') (j : ℤ) : stdGradedRank G t' ht' j = 0 := by
  have h0 := seqIdem_eq_zero_of_not_prepend Q Λ ν t' ht' h
  have hbot : (lIdeal (seqIdem Q Λ t' ht')).restrictScalars k ⊓ tensorProductGrade G ν j =
      ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hy' : y * seqIdem Q Λ t' ht' = y := hy.1
    rw [h0, mul_zero] at hy'
    exact (Submodule.mem_bot k).2 hy'.symm
  rw [stdGradedRank, hbot, finrank_bot, Nat.zero_sub]

/-- **Graded dimension identity for `T̃^λ e(s)`, with bounds on `Φ(s)` only** (Webster,
arXiv:1309.3796v3, Corollary 5.23, the count in degree `n`). As
`finrank_tilde_lIdeal_grade_eq_sum_phiIndex`, but the reduced words for `λ₀ s` are chosen
internally and only the degrees `n - deg x̃_φ`, `φ ∈ Φ(s)`, need to be bounded by `N`. Route
hypothesis: `AllFiniteDeltaInjective`, inherited from `phiLayerEquiv`. -/
theorem finrank_tilde_lIdeal_grade_eq_sum_of_bound {C : QuantumGroup.CartanDatum I}
    (hQ : KLRSymm Q) (hR : IsRouquierQ C Q)
    (hall : ∀ (n : ℕ) (Λ' : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ' hQ)
    (ρ₀ : Perm (Fin m) → List ℕ)
    (hρ₀ : ∀ w : Perm (Fin m), TypeA.IsReduced m (ρ₀ w) ∧ TypeA.wordProd m (ρ₀ w) = w)
    {c N n : ℤ} (hc : ∀ m' < -c, allOrdersGrade G₀ ν m' = ⊥)
    (hΛ : ∀ i ∈ ν, N + 2 * c < Λ 0 i * G.degX (.inl i)) (s : Seq μ) (hs : IsRedOrdered s)
    (hnN : n ≤ N) (hN : ∀ g : PhiIndex s, n - GradingDatum.degW G₀ (ρ₀ (phiPerm s g.1)) s ≤ N) :
    finrank k ((lIdeal (StendhalAlgebra.e s hs)).restrictScalars k ⊓ stendhalGrade G₀ ν n :) =
      ∑ g : PhiIndex s, tildeStdGradedRank Q Λ ν G₀ (phiBottom s g.1) (g.isRedOrdered hs)
        (n - GradingDatum.degW G₀ (ρ₀ (phiPerm s g.1)) s) := by
  classical
  let ρ : Perm (Fin (Multiset.card μ')) → List ℕ := fun w => (exists_reduced _ w).choose
  have hρ : ∀ w : Perm (Fin (Multiset.card μ')),
      TypeA.IsReduced (Multiset.card μ') (ρ w) ∧ TypeA.wordProd (Multiset.card μ') (ρ w) = w :=
    fun w => (exists_reduced _ w).choose_spec
  have hle : ∀ j ≤ N, ∀ i ∈ ν, j + 2 * c < Λ 0 i * G.degX (.inl i) :=
    fun j hj i hi => lt_of_le_of_lt (by omega) (hΛ i hi)
  have hs' := (prependRedLoading_ordered_iff s).2 hs
  rw [finrank_lIdeal_grade_prependRed Q Λ ν G hc (hle n hnN) s hs,
    finrank_lIdeal_grade_eq_sum G hQ hR hall ρ hρ hs' n]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image (extPhiIndex s)))
    (fun g' _ hg' => stdGradedRank_eq_zero_of_not_prepend Q Λ ν G _ _ (fun t ht => hg' (by
      obtain ⟨g, hg⟩ := exists_extPhiIndex_of_prepend s g' ⟨t, ht⟩
      exact Finset.mem_image.2 ⟨g, Finset.mem_univ _, hg⟩)) _),
    Finset.sum_image fun g _ g' _ h => extPhiIndex_injective s h]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [degW_phiPerm_extAssign Q Λ ν G hρ hρ₀ s g,
    stdGradedRank_eq_tildeTerm Q Λ ν G hc (hle _ (hN g))]
  exact tildeTerm_of_eq Q Λ ν G₀ (phiBottom_extAssign s g).symm _ _ _

variable {Q Λ ν}

private theorem tildeLeftUpper_le_lIdeal (t : Seq μ) (ht : IsRedOrdered t) :
    tildeLeftUpper Q (Λ ∘ Fin.succ) ν t ht ≤ lIdeal (StendhalAlgebra.e t ht : B) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨t', ht', a, -, rfl⟩
  change _ * _ * _ * _ = _ * _ * _
  rw [mul_assoc _ (StendhalAlgebra.e t ht), stendhalAlgebra_e_mul_e_self]

/-- **Degreewise injectivity of `S̃_{φ • s} → P̃_{≥φ}/P̃_{>φ}`** (Webster, arXiv:1309.3796v3,
proof of Corollary 5.23). Under the hypotheses of `finrank_tilde_lIdeal_grade_eq_sum_of_bound`
(in particular `λ₀` large relative to `N`, with `n ≤ N` and every `n - deg x̃_φ ≤ N`), an element
`y` of `T̃^λ e(φ • s)` of degree `n - deg x̃_φ` with `y x̃_φ ∈ P̃_{≻φ}` lies in `Ũ_{φ • s}`; here
`≺` is any strict order containing Webster's order (for example a linear extension of it). Route
hypothesis: `AllFiniteDeltaInjective`, inherited from `phiLayerEquiv`. -/
theorem mem_tildeLeftUpper_of_mul_mem_above {C : QuantumGroup.CartanDatum I}
    (hQ : KLRSymm Q) (hR : IsRouquierQ C Q)
    (hall : ∀ (n : ℕ) (Λ' : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ' hQ)
    (ρ₀ : Perm (Fin m) → List ℕ)
    (hρ₀ : ∀ w : Perm (Fin m), TypeA.IsReduced m (ρ₀ w) ∧ TypeA.wordProd m (ρ₀ w) = w)
    {c N n : ℤ} (hc : ∀ m' < -c, allOrdersGrade G₀ ν m' = ⊥)
    (hΛ : ∀ i ∈ ν, N + 2 * c < Λ 0 i * G.degX (.inl i)) (s : Seq μ) (hs : IsRedOrdered s)
    (hnN : n ≤ N) (hN : ∀ g : PhiIndex s, n - GradingDatum.degW G₀ (ρ₀ (phiPerm s g.1)) s ≤ N)
    {rel : PhiIndex s → PhiIndex s → Prop} (hirr : ∀ φ, ¬ rel φ φ)
    (htr : ∀ a b c, rel a b → rel b c → rel a c) (hrel : ∀ a b, PhiLT a b → rel a b)
    (g : PhiIndex s) (y : B)
    (hy : y ∈ lIdeal (StendhalAlgebra.e (phiBottom s g.1) (g.isRedOrdered hs) : B))
    (hdeg : y ∈ stendhalGrade G₀ ν (n - GradingDatum.degW G₀ (ρ₀ (phiPerm s g.1)) s))
    (habove : y * tildePhiElt Q (Λ ∘ Fin.succ) ρ₀ hs g.mem ∈
      (tildeRelAbove Q (Λ ∘ Fin.succ) ρ₀ hs rel g).map
        (lIdeal (StendhalAlgebra.e s hs : B)).subtype) :
    y ∈ tildeLeftUpper Q (Λ ∘ Fin.succ) ν (phiBottom s g.1) (g.isRedOrdered hs) := by
  classical
  set ℳ := stendhalGrade G₀ ν
  set d : PhiIndex s → ℤ := fun g => GradingDatum.degW G₀ (ρ₀ (phiPerm s g.1)) s
  have hfin : ∀ j ≤ N, FiniteDimensional k (ℳ j) := fun j hj =>
    finiteDimensional_stendhalGrade_of_le Q Λ ν G hR hc
      fun i hi => lt_of_le_of_lt (by omega) (hΛ i hi)
  have hdN : ∀ g : PhiIndex s, n - d g ≤ N := hN
  have hfn : FiniteDimensional k (ℳ n) := hfin n hnN
  let L := lIdeal (StendhalAlgebra.e s hs : B)
  let Nf : PhiIndex s → Submodule k B :=
    fun g => ((tildePhiSub Q (Λ ∘ Fin.succ) ρ₀ hs g).map L.subtype).restrictScalars k
  have hNspan : ∀ g, Nf g =
      (Submodule.span B {tildePhiElt Q (Λ ∘ Fin.succ) ρ₀ hs g.mem}).restrictScalars k :=
    fun g => by
      change ((Submodule.span B {tildePhiVec Q (Λ ∘ Fin.succ) ρ₀ hs g}).map
        L.subtype).restrictScalars k = _
      rw [Submodule.map_span, Set.image_singleton]
      rfl
  have hNh : ∀ g, IsHomogeneousSubspace ℳ (Nf g) := by
    intro g
    rw [hNspan g]
    refine isHomogeneousSubspace_span ℳ ?_
    rintro _ rfl j
    by_cases hj : d g = j
    · rw [← hj, decompose_of_mem_same _ (tildePhiElt_mem_grade Q (Λ ∘ Fin.succ) ν G₀ ρ₀ hs g.mem)]
      exact Submodule.subset_span rfl
    · rw [decompose_of_mem_ne _ (tildePhiElt_mem_grade Q (Λ ∘ Fin.succ) ν G₀ ρ₀ hs g.mem) hj]
      exact zero_mem _
  have hspan : (⨆ g, Nf g) = L.restrictScalars k := by
    change (⨆ g, ((tildePhiSub Q (Λ ∘ Fin.succ) ρ₀ hs g).map L.subtype).restrictScalars k) = _
    rw [← Submodule.restrictScalars_iSup, ← Submodule.map_iSup,
      iSup_tildePhiSub_eq_top ρ₀ hs hρ₀, Submodule.map_subtype_top]
  have hab : ∀ g, Submodule.above rel Nf g =
      ((tildeRelAbove Q (Λ ∘ Fin.succ) ρ₀ hs rel g).map L.subtype).restrictScalars k := fun g => by
    simp only [Nf, Submodule.above, Submodule.map_iSup, Submodule.restrictScalars_iSup]
  -- the generator data of each layer
  have key : ∀ g : PhiIndex s,
      Submodule.layerRank (k := k) rel (fun g => Nf g ⊓ ℳ n) g +
          finrank k ((tildeLeftUpper Q (Λ ∘ Fin.succ) ν (phiBottom s g.1)
            (g.isRedOrdered hs)).restrictScalars k ⊓ ℳ (n - d g) :) ≤
        finrank k ((lIdeal (StendhalAlgebra.e (phiBottom s g.1) (g.isRedOrdered hs) : B)
          ).restrictScalars k ⊓ ℳ (n - d g) :) ∧
      (Submodule.layerRank (k := k) rel (fun g => Nf g ⊓ ℳ n) g +
          finrank k ((tildeLeftUpper Q (Λ ∘ Fin.succ) ν (phiBottom s g.1)
            (g.isRedOrdered hs)).restrictScalars k ⊓ ℳ (n - d g) :) =
        finrank k ((lIdeal (StendhalAlgebra.e (phiBottom s g.1) (g.isRedOrdered hs) : B)
          ).restrictScalars k ⊓ ℳ (n - d g) :) →
        ∀ x ∈ (lIdeal (StendhalAlgebra.e (phiBottom s g.1) (g.isRedOrdered hs) : B)
          ).restrictScalars k ⊓ ℳ (n - d g),
          LinearMap.mulRight k (tildePhiElt Q (Λ ∘ Fin.succ) ρ₀ hs g.mem) x ∈
            Submodule.above rel Nf g →
          x ∈ (tildeLeftUpper Q (Λ ∘ Fin.succ) ν (phiBottom s g.1)
            (g.isRedOrdered hs)).restrictScalars k) := by
    intro g
    have ht := g.isRedOrdered hs
    have hfd : FiniteDimensional k (ℳ (n - d g)) := hfin _ (hdN g)
    have hμ : ∀ m', ∀ x ∈ ℳ m', LinearMap.mulRight k (tildePhiElt Q (Λ ∘ Fin.succ) ρ₀ hs g.mem)
        x ∈ ℳ (m' + d g) := fun m' x hx =>
      SetLike.GradedMul.mul_mem hx (tildePhiElt_mem_grade Q (Λ ∘ Fin.succ) ν G₀ ρ₀ hs g.mem)
    have hNg : Nf g = ((lIdeal (StendhalAlgebra.e (phiBottom s g.1) ht : B)).restrictScalars
        k).map (LinearMap.mulRight k (tildePhiElt Q (Λ ∘ Fin.succ) ρ₀ hs g.mem)) := by
      rw [hNspan g]
      ext z
      simp only [Submodule.restrictScalars_mem, Submodule.mem_span_singleton, Submodule.mem_map,
        LinearMap.mulRight_apply, smul_eq_mul]
      constructor
      · rintro ⟨a, rfl⟩
        refine ⟨a * StendhalAlgebra.e (phiBottom s g.1) ht, ?_, ?_⟩
        · change _ * _ * _ = _
          rw [mul_assoc, stendhalAlgebra_e_mul_e_self]
        · rw [mul_assoc, e_mul_tildePhiElt]
      · rintro ⟨x, -, rfl⟩
        exact ⟨x, rfl⟩
    refine layerRank_grade_le_of_generator rel hNh g hμ
      (isHomogeneousSubspace_lIdeal_of_mem_zero _ (e_mem_stendhalGrade G₀ ν _ ht))
      (Submodule.restrictScalars_mono k (tildeLeftUpper_le_lIdeal _ ht)) (by rw [hNg])
      ?_ n
    intro x hx
    rw [hab, LinearMap.mulRight_apply, Submodule.restrictScalars_mem]
    have hxL : x ∈ lIdeal (StendhalAlgebra.e (phiBottom s g.1) ht : B) :=
      tildeLeftUpper_le_lIdeal _ ht hx
    have h0 := tildeLeftUpper_smul_eq_zero (Λ := Λ ∘ Fin.succ) (phiBottom s g.1) ht
      (tildeRelLayerGen Q (Λ ∘ Fin.succ) ρ₀ hs rel g)
      (fun t ht' a hlt => tildeRelLayerGen_annihilated ρ₀ hs hρ₀ hrel g t ht' a hlt) hx
    rw [tildeRelLayerGen, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h0
    exact ⟨_, h0, rfl⟩
  -- the sums
  have hcount := finrank_tilde_lIdeal_grade_eq_sum_of_bound Q Λ ν G hQ hR hall ρ₀ hρ₀
    hc hΛ s hs hnN hN
  have hle := finrank_inf_grade_le_sum rel hirr htr hNh hspan n
  have hstd : ∀ g : PhiIndex s, tildeStdGradedRank Q Λ ν G₀ (phiBottom s g.1)
      (g.isRedOrdered hs) (n - d g) =
        finrank k ((lIdeal (StendhalAlgebra.e (phiBottom s g.1) (g.isRedOrdered hs) : B)
          ).restrictScalars k ⊓ ℳ (n - d g) :) -
        finrank k ((tildeLeftUpper Q (Λ ∘ Fin.succ) ν (phiBottom s g.1)
            (g.isRedOrdered hs)).restrictScalars k ⊓ ℳ (n - d g) :) := fun g => rfl
  have hlayer : ∀ g : PhiIndex s, Submodule.layerRank (k := k) rel (fun g => Nf g ⊓ ℳ n) g ≤
      tildeStdGradedRank Q Λ ν G₀ (phiBottom s g.1) (g.isRedOrdered hs) (n - d g) := fun g => by
    rw [hstd]
    have := (key g).1
    omega
  have heq := (Finset.sum_eq_sum_iff_of_le fun g _ => hlayer g).1
    (le_antisymm (Finset.sum_le_sum fun g _ => hlayer g) (by
      change _ ≤ ∑ g : PhiIndex s, Submodule.layerRank (k := k) rel (fun g => Nf g ⊓ ℳ n) g
      have h := hle
      change finrank k ((lIdeal (StendhalAlgebra.e s hs : B)).restrictScalars k ⊓ ℳ n :) ≤ _
        at h
      rw [hcount] at h
      exact h)) g (Finset.mem_univ _)
  have hUle := (key g).1
  have hfd : FiniteDimensional k (ℳ (n - d g)) := hfin _ (hdN g)
  refine (key g).2 (by rw [heq, hstd]; omega) y ⟨hy, hdeg⟩ ?_
  rw [hab, LinearMap.mulRight_apply, Submodule.restrictScalars_mem]
  exact habove

end Categorification.Stendhal

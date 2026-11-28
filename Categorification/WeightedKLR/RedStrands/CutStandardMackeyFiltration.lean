/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlocksStandardBasis
import Categorification.WeightedKLR.RedStrands.BruhatStraightening
import Categorification.WeightedKLR.RedStrands.PartialStandardizationBlocksPlus

/-!
# The Mackey filtration of a partial standardization

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19: the filtration of
`S_+(Z ⊠ N) e_{s,win}` by the number of strands of the first block that pass the window.
Webster's proof does not state this filtration; it is used for the trace half of Lemma 7.19.

In the induced model `𝕊(N) = Ind N / (excluded)` of a cut into two blocks (`CutStandard`), with
bottom blocks of sizes `n'' = |α|` and `|δ|`, fix a top cut at position `n`. The step
`F_c ⊆ 𝕊(N)` (`cutMackeyFilt n c`) is spanned by the classes of `r ⊗ x` with `r` in the step
`c` of the Mackey filtration of KL I, Prop. 2.18 (`KLRAlgebra.mackeyFilt n n'' c`): diagrams
with at most `c` strands from the second bottom block to the top positions `< n`. On a loading
`e(s)` the number `h` of strands of the first bottom block ending at top positions `≥ n` is
`h = n'' - n + c'`, with `c'` the number counted by `mackeyFilt`; so `F_c` is the span of the
diagrams with `h ≤ n'' - n + c`.

* `F_c` is preserved by every affine element that preserves the Mackey filtration
  (`cutMackeyFilt_action`), among them the parabolic subalgebra `R(ν) ⊗ R(ν')` of the top cut
  (`preservesMackeyFilt_castAlg_concat`); this contains the window algebra placed between
  the positions `< n` and `≥ n`;
* `F_c` is natural in `N` (`cutStandardMap_mem_cutMackeyFilt`), monotone and exhaustive
  (`cutMackeyFilt_eq_top`).

For the partial standardization with three blocks `𝕊^{A;M;R}` of `λ⁺` (`PlusStandard`), the
filtration of the outer cut `A | MR` is the filtration of Lemma 7.19: the strands of the first
bottom block are the head strands (`plusMackeyFilt_action`).

Any commutative ring `k`, symmetric `Q`.

## Main definitions

* `KLR.KLRAlgebra.PreservesMackeyFilt`, `Stendhal.indMackeyFilt`, `Stendhal.cutMackeyFilt`,
  `Stendhal.CupCap.plusMackeyFilt`.

## Main results

* `KLR.KLRAlgebra.preservesMackeyFilt_castAlg_concat`, `KLR.KLRAlgebra.mackeyFilt_eq_top`.
* `Stendhal.cutMackeyFilt_action`, `Stendhal.cutStandardMap_mem_cutMackeyFilt`,
  `Stendhal.cutMackeyFilt_mono`, `Stendhal.cutMackeyFilt_eq_top`.
* `Stendhal.CupCap.plusMackeyFilt_action`.
-/

noncomputable section

namespace Categorification

namespace KLR

namespace KLRAlgebra

open Equiv TypeA
open scoped TensorProduct

variable {I : Type*} {k : Type*} [CommRing k] [DecidableEq I]
  {Q : I → I → MvPolynomial (Fin 2) k} {μ : Multiset I}

variable (n n'' : ℕ)

/-- An element preserves every step of the Mackey filtration under left multiplication. -/
def PreservesMackeyFilt (z : KLRAlgebra k Q μ) : Prop :=
  ∀ c y, y ∈ mackeyFilt k Q μ n n'' c → z * y ∈ mackeyFilt k Q μ n n'' c

variable {n n''}

theorem PreservesMackeyFilt.mul {z z' : KLRAlgebra k Q μ} (hz : PreservesMackeyFilt n n'' z)
    (hz' : PreservesMackeyFilt n n'' z') : PreservesMackeyFilt n n'' (z * z') :=
  fun c y hy => by rw [mul_assoc]; exact hz c _ (hz' c y hy)

theorem PreservesMackeyFilt.add {z z' : KLRAlgebra k Q μ} (hz : PreservesMackeyFilt n n'' z)
    (hz' : PreservesMackeyFilt n n'' z') : PreservesMackeyFilt n n'' (z + z') :=
  fun c y hy => by rw [add_mul]; exact add_mem (hz c y hy) (hz' c y hy)

theorem preservesMackeyFilt_e (j : Seq μ) : PreservesMackeyFilt n n'' (e j : KLRAlgebra k Q μ) :=
  fun _ _ hy => e_mul_mem_mackeyFilt j hy

theorem preservesMackeyFilt_pol (q : MvPolynomial (Fin (Multiset.card μ)) k) :
    PreservesMackeyFilt n n'' (pol q : KLRAlgebra k Q μ) :=
  fun _ _ hy => pol_mul_mem_mackeyFilt q hy

/-- A crossing inside one of the top blocks `[0, n)`, `[n, m)`. -/
theorem preservesMackeyFilt_ψ {j : ℕ} (hj : j + 1 < n ∨ n ≤ j) :
    PreservesMackeyFilt n n'' (ψ j : KLRAlgebra k Q μ) :=
  fun _ _ hy => ψ_mul_mem_mackeyFilt hj hy

/-- **The parabolic subalgebra of the top cut preserves the Mackey filtration**:
`ι_{ν,ν'}(t)`, transported to any equal weight. -/
theorem preservesMackeyFilt_castAlg_concat {ν ν' : Multiset I} (h : ν + ν' = μ)
    (t : KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν') :
    PreservesMackeyFilt (Multiset.card ν) n'' (castAlg Q h (concat Q ν ν' t)) := by
  subst h
  exact fun _ _ hy => concat_mul_mem_mackeyFilt t hy

/-- **The Mackey filtration is exhaustive.** -/
theorem mackeyFilt_eq_top (hn : n ≤ Multiset.card μ) (hn'' : n'' ≤ Multiset.card μ) :
    mackeyFilt k Q μ n n'' n = ⊤ := by
  rw [mackeyFilt_eq_stdSpan hn hn'' (canWord _)
    (fun w => ⟨isReduced_canWord _ w, wordProd_canWord _ w⟩) n]
  have : {w : Perm (Fin (Multiset.card μ)) | crossCount n n'' w ≤ n} = Set.univ :=
    Set.eq_univ_of_forall fun w => crossCount_le w hn
  rw [this]
  exact stdSpan_univ_eq_top _ (fun w => ⟨isReduced_canWord _ w, wordProd_canWord _ w⟩)

end KLRAlgebra

end KLR

namespace Stendhal

open KLR KLRAlgebra TypeA MulOpposite
open scoped TensorProduct

section Cut

variable {I k : Type*} [DecidableEq I] [CommRing k] {a r : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (a + r) → I →₀ ℕ) (θ β : Multiset I)

local notation "α" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd r)) (stendhalWeight a θ)
local notation "δ" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd a)) (stendhalWeight r β)
local notation "S" => stendhalQ Q Λ
local notation "D" => cutFactorAlgebra Q Λ θ β

variable (N : Type*) [AddCommGroup N] [Module k N] [Module (cutFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N]

/-- The step `c` of the Mackey filtration of the induced module: the span of `r ⊗ x` with `r` in
the step `c` of the Mackey filtration of KL I, Prop. 2.18, for the top cut at `n`. -/
def indMackeyFilt (n c : ℕ) : Submodule k (CutShuffle Q Λ θ β N) :=
  Submodule.span k {y | ∃ (w : IndBimod S α δ) (x : CutInput Q Λ θ β N),
    (w : KLRAlgebra k S (α + δ)) ∈ mackeyFilt k S (α + δ) n (Multiset.card α) c ∧
      BalancedTensor.tmul w x = y}

variable (hQ : KLRSymm Q)

/-- **The Mackey filtration of a partial standardization**: the image of `indMackeyFilt n c`. -/
def cutMackeyFilt (n c : ℕ) : Submodule k (CutStandard Q Λ θ β N) :=
  (indMackeyFilt Q Λ θ β N n c).map (Submodule.mkQ _)

variable {Q Λ θ β N}

omit [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] in
theorem indMackeyFilt_smul {n : ℕ} {z : KLRAlgebra k S (α + δ)}
    (hz : PreservesMackeyFilt n (Multiset.card α) z) {c : ℕ} {y : CutShuffle Q Λ θ β N}
    (hy : y ∈ indMackeyFilt Q Λ θ β N n c) : z • y ∈ indMackeyFilt Q Λ θ β N n c := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, x, hw, rfl⟩ := hy
    rw [BalancedTensor.smul_tmul']
    exact Submodule.subset_span ⟨z • w, x, hz c _ hw, rfl⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add y y' _ _ h h' => rw [smul_add]; exact add_mem h h'
  | smul c' y _ h => rw [smul_comm]; exact Submodule.smul_mem _ c' h

/-- **Claim A, in the induced model**: every affine element preserving the Mackey filtration of
the top cut at `n`, in particular the parabolic subalgebra of that cut, preserves the filtration
of `𝕊(N)`. -/
theorem cutMackeyFilt_action {n : ℕ} {z : KLRAlgebra k S (α + δ)}
    (hz : PreservesMackeyFilt n (Multiset.card α) z) {c : ℕ} {v : CutStandard Q Λ θ β N}
    (hv : v ∈ cutMackeyFilt Q Λ θ β N n c) :
    cutStandardAction Q Λ θ β N hQ (affineToTensor Q Λ θ β z) v ∈
      cutMackeyFilt Q Λ θ β N n c := by
  obtain ⟨y, hy, rfl⟩ := hv
  rw [cutStandardAction_affineToTensor]
  exact ⟨z • y, indMackeyFilt_smul hz hy, rfl⟩

variable {N' : Type*} [AddCommGroup N'] [Module k N'] [Module (cutFactorAlgebra Q Λ θ β) N']
  [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N']

/-- **The filtration is natural** in the module over the blocks. -/
theorem cutStandardMap_mem_cutMackeyFilt (g : N →ₗ[D] N') {n c : ℕ}
    {v : CutStandard Q Λ θ β N} (hv : v ∈ cutMackeyFilt Q Λ θ β N n c) :
    cutStandardMap Q Λ θ β g v ∈ cutMackeyFilt Q Λ θ β N' n c := by
  obtain ⟨y, hy, rfl⟩ := hv
  refine ⟨cutShuffleMap Q Λ θ β g y, ?_, rfl⟩
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, x, hw, rfl⟩ := hy
    exact Submodule.subset_span ⟨w, cutInputHom Q Λ θ β g x, hw, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add y y' _ _ h h' => rw [map_add]; exact add_mem h h'
  | smul c' y _ h => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ c' h

omit [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] in
theorem indMackeyFilt_mono {n c c' : ℕ} (h : c ≤ c') :
    indMackeyFilt Q Λ θ β N n c ≤ indMackeyFilt Q Λ θ β N n c' :=
  Submodule.span_mono fun _ ⟨w, x, hw, hy⟩ => ⟨w, x, mackeyFilt_mono h hw, hy⟩

omit [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] in
theorem cutMackeyFilt_mono {n c c' : ℕ} (h : c ≤ c') :
    cutMackeyFilt Q Λ θ β N n c ≤ cutMackeyFilt Q Λ θ β N n c' :=
  Submodule.map_mono (indMackeyFilt_mono h)

omit [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] in
theorem indMackeyFilt_eq_top {n : ℕ} (hn : n ≤ Multiset.card (α + δ)) :
    indMackeyFilt Q Λ θ β N n n = ⊤ := by
  have htop := mackeyFilt_eq_top (k := k) (Q := S) (μ := α + δ) (n'' := Multiset.card α) hn
    (by rw [Multiset.card_add]; exact Nat.le_add_right _ _)
  rw [eq_top_iff, ← BalancedTensor.span_tmul_eq_top]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨w, x, rfl⟩
  exact Submodule.subset_span ⟨w, x, htop ▸ Submodule.mem_top, rfl⟩

omit [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] in
/-- **The filtration is exhaustive.** -/
theorem cutMackeyFilt_eq_top {n : ℕ} (hn : n ≤ Multiset.card (α + δ)) :
    cutMackeyFilt Q Λ θ β N n n = ⊤ := by
  rw [cutMackeyFilt, indMackeyFilt_eq_top hn, Submodule.map_top, Submodule.range_mkQ]

end Cut

/-! ### The filtration of the partial standardization `S_+` -/

namespace CupCap

variable {I k : Type*} [DecidableEq I] [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)
  {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ) (j : ℕ) (hj : j ≤ ℓ) (θ β γ : Multiset I)
  (N : Type*) [AddCommGroup N] [Module k N] [Module (PlusFactorAlgebra Q Λ Λc j hj θ β γ) N]
  [IsScalarTower k (PlusFactorAlgebra Q Λ Λc j hj θ β γ) N] (hQ : KLRSymm Q)

local notation "αo" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j))))
  (stendhalWeight j θ)
local notation "δo" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
  (stendhalWeight (2 + (ℓ - j)) (β + γ))

/-- **The filtration of `S_+` by the head strands passing the window**: the Mackey filtration of
the outer cut `A | MR` of the partial standardization with three blocks. -/
def plusMackeyFilt (n c : ℕ) : Submodule k (PlusStandard Q Λ Λc j hj θ β γ N hQ) :=
  cutMackeyFilt Q (plusBlockLabels Λ Λc j hj) θ (β + γ)
    (BlocksMid Q (plusBlockLabels Λ Λc j hj) θ β γ (PlusInput Q Λ Λc j hj θ β γ N) hQ) n c

/-- **Claim A for `S_+`** (Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19): the image in
`T^{λ⁺}` of an affine element preserving the Mackey filtration of the top cut at `n`, in
particular of the parabolic subalgebra of that cut, preserves each step of the filtration of
`S_+` by the head strands passing position `n`. -/
theorem plusMackeyFilt_action {n : ℕ}
    {z : KLRAlgebra k (stendhalQ Q (plusBlockLabels Λ Λc j hj)) (αo + δo)}
    (hz : PreservesMackeyFilt n (Multiset.card αo) z) {c : ℕ}
    {v : PlusStandard Q Λ Λc j hj θ β γ N hQ}
    (hv : v ∈ plusMackeyFilt Q Λ Λc j hj θ β γ N hQ n c) :
    plusStandardAction Q Λ Λc j hj θ β γ N hQ
        (castLabelsTensorProductAlgebra Q (plusBlock_card j hj) (plusLabels Λ Λc j hj)
          (θ + (β + γ)) (affineToTensor Q (plusBlockLabels Λ Λc j hj) θ (β + γ) z)) v ∈
      plusMackeyFilt Q Λ Λc j hj θ β γ N hQ n c := by
  change blocksStandardAction Q (plusBlockLabels Λ Λc j hj) θ β γ _ hQ
    ((castLabelsTensorProductAlgebra Q (plusBlock_card j hj) (plusLabels Λ Λc j hj)
      (θ + (β + γ))).symm (castLabelsTensorProductAlgebra Q (plusBlock_card j hj)
        (plusLabels Λ Λc j hj) (θ + (β + γ))
          (affineToTensor Q (plusBlockLabels Λ Λc j hj) θ (β + γ) z))) v ∈ _
  have e := AlgEquiv.symm_apply_apply (castLabelsTensorProductAlgebra Q (plusBlock_card j hj)
    (plusLabels Λ Λc j hj) (θ + (β + γ))) (affineToTensor Q (plusBlockLabels Λ Λc j hj) θ (β + γ) z)
  rw [e]
  exact cutMackeyFilt_action hQ hz hv

end CupCap

end Stendhal

end Categorification

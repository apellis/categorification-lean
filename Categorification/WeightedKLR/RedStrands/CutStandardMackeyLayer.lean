/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.IdempotentQuotientLayer
import Categorification.WeightedKLR.RedStrands.CutStandardMackeyFiltration
import Categorification.KLR.MackeyIndLayer

/-!
# The layers of the Mackey filtration of a partial standardization

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, Claim B: the passage from the induced
module to the partial standardization. The partial standardization `𝕊(N)` of a cut is the
induced module `Ind N` modulo the kernel of the idempotent `P = Σ e(s)` over the loadings `s`
with the red strands in order (`CutStandard`). The steps `F_c` of the Mackey filtration of
`Ind N` (`indMackeyFilt`) are preserved by `P`, since loading idempotents preserve the Mackey
filtration. Hence the layer `F_c(𝕊) / F_{c-1}(𝕊)` of `𝕊(N)` is the layer of `Ind N` cut down
by `P` (`cutMackeyLayerEquiv`, `cutMackeyLayerRangeEquiv`):

`F_c(𝕊) / F_{c-1}(𝕊) ≅ (F_c / F_{c-1}) / ker P̄ ≅ P̄ (F_c / F_{c-1})`,

and the map from the layer of `Ind N` commutes with every affine element preserving the Mackey
filtration, acting through `T^λ` on `𝕊(N)` (`cutMackeyLayerMap_act`).

Any commutative ring `k`, symmetric `Q`.

## Main definitions

* `Stendhal.indMackeyFiltLower`, `Stendhal.cutMackeyFiltLower`, `Stendhal.cutExcludedIdem`,
  `Stendhal.cutMackeyLayerMap`.

## Main results

* `Stendhal.cutMackeyLayerMap_surjective`, `Stendhal.cutMackeyLayerEquiv`,
  `Stendhal.cutMackeyLayerRangeEquiv`, `Stendhal.cutMackeyLayerMap_act`.
* `Stendhal.indMackeyFilt_eq_indMackeyStep`, `Stendhal.indMackeyFiltLower_eq_indMackeyLower`:
  the steps are those of `KLRAlgebra.indMackeyStep`, so the layer of `Ind N` is
  `KLRAlgebra.IndMackeyLayer`, with the module structure of KL I, Prop. 2.18.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA

variable {I k : Type*} [DecidableEq I] [CommRing k] {a r : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (a + r) → I →₀ ℕ) (θ β : Multiset I)

local notation "α" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd r)) (stendhalWeight a θ)
local notation "δ" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd a)) (stendhalWeight r β)
local notation "S" => stendhalQ Q Λ

variable (N : Type*) [AddCommGroup N] [Module k N] [Module (cutFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N]

/-- The step `F_{c-1}` below `F_c` of the Mackey filtration of the induced module (`⊥` for
`c = 0`). -/
def indMackeyFiltLower (n : ℕ) : ℕ → Submodule k (CutShuffle Q Λ θ β N)
  | 0 => ⊥
  | c + 1 => indMackeyFilt Q Λ θ β N n c

/-- The idempotent `P` of the loadings with the red strands in order, acting on `Ind N`; the
partial standardization is `Ind N / ker P`. -/
abbrev cutExcludedIdem : CutShuffle Q Λ θ β N →ₗ[k] CutShuffle Q Λ θ β N :=
  cutShuffleAction Q Λ θ β N (eSum S (cutOrderedLoadings (a := a) (r := r) θ β))

/-- The step `F_{c-1}(𝕊)` below `F_c(𝕊)` in the partial standardization. -/
abbrev cutMackeyFiltLower (n c : ℕ) : Submodule k (CutStandard Q Λ θ β N) :=
  idemImage (cutExcludedIdem Q Λ θ β N) (indMackeyFiltLower Q Λ θ β N n c)

omit [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] in
theorem cutMackeyFiltLower_succ (n c : ℕ) :
    cutMackeyFiltLower Q Λ θ β N n (c + 1) = cutMackeyFilt Q Λ θ β N n c :=
  rfl

omit [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] in
theorem cutMackeyFiltLower_zero (n : ℕ) : cutMackeyFiltLower Q Λ θ β N n 0 = ⊥ :=
  Submodule.map_bot _

omit [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] in
/-- The steps of the Mackey filtration of the induced module of the cut are those of KL I,
Prop. 2.18, for `Ind N` (`KLRAlgebra.indMackeyStep`). -/
theorem indMackeyFilt_eq_indMackeyStep (n c : ℕ) :
    indMackeyFilt Q Λ θ β N n c = indMackeyStep S α δ (CutInput Q Λ θ β N) n c :=
  rfl

omit [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] in
theorem indMackeyFiltLower_eq_indMackeyLower (n c : ℕ) :
    indMackeyFiltLower Q Λ θ β N n c = indMackeyLower S α δ (CutInput Q Λ θ β N) n c := by
  cases c <;> rfl

variable {Q Λ θ β N}

omit [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] in
theorem preservesMackeyFilt_eSum (n : ℕ) (T : Finset (Seq (α + δ))) :
    PreservesMackeyFilt n (Multiset.card α) (eSum S T : KLRAlgebra k S (α + δ)) := by
  classical
  unfold eSum
  induction T using Finset.induction_on with
  | empty => exact fun c y _ => by rw [Finset.sum_empty, zero_mul]; exact zero_mem _
  | insert s T hs ih =>
    rw [Finset.sum_insert hs]
    exact (preservesMackeyFilt_e s).add ih

omit [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] in
theorem indMackeyFiltLower_smul {n : ℕ} {z : KLRAlgebra k S (α + δ)}
    (hz : PreservesMackeyFilt n (Multiset.card α) z) {c : ℕ} {y : CutShuffle Q Λ θ β N}
    (hy : y ∈ indMackeyFiltLower Q Λ θ β N n c) : z • y ∈ indMackeyFiltLower Q Λ θ β N n c := by
  cases c with
  | zero =>
    change y ∈ (⊥ : Submodule k _) at hy
    rw [Submodule.mem_bot] at hy
    rw [hy, smul_zero]
    exact zero_mem _
  | succ c => exact indMackeyFilt_smul hz hy

omit [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] in
theorem cutExcludedIdem_idem (y : CutShuffle Q Λ θ β N) :
    cutExcludedIdem Q Λ θ β N (cutExcludedIdem Q Λ θ β N y) = cutExcludedIdem Q Λ θ β N y := by
  change (eSum S (cutOrderedLoadings (a := a) (r := r) θ β) : KLRAlgebra k S (α + δ)) •
      ((eSum S (cutOrderedLoadings (a := a) (r := r) θ β) : KLRAlgebra k S (α + δ)) • y) =
    (eSum S (cutOrderedLoadings (a := a) (r := r) θ β) : KLRAlgebra k S (α + δ)) • y
  rw [smul_smul, (eSum_idem _).eq]

variable (Q Λ θ β N)

/-- The map from the layer of `Ind N` to the layer of the partial standardization. -/
abbrev cutMackeyLayerMap (n c : ℕ) :
    SubLayer (indMackeyFilt Q Λ θ β N n c) (indMackeyFiltLower Q Λ θ β N n c) →ₗ[k]
      SubLayer (cutMackeyFilt Q Λ θ β N n c) (cutMackeyFiltLower Q Λ θ β N n c) :=
  idemLayerMap (cutExcludedIdem Q Λ θ β N)

omit [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] in
theorem cutMackeyLayerMap_surjective (n c : ℕ) :
    Function.Surjective (cutMackeyLayerMap Q Λ θ β N n c) :=
  idemLayerMap_surjective _

omit [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] in
theorem cutExcludedIdem_mem (n c : ℕ) :
    ∀ y ∈ indMackeyFilt Q Λ θ β N n c,
      cutExcludedIdem Q Λ θ β N y ∈ indMackeyFilt Q Λ θ β N n c :=
  fun _ hy => indMackeyFilt_smul (preservesMackeyFilt_eSum n _) hy

omit [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] in
theorem cutExcludedIdem_mem_lower (n c : ℕ) :
    ∀ y ∈ indMackeyFiltLower Q Λ θ β N n c,
      cutExcludedIdem Q Λ θ β N y ∈ indMackeyFiltLower Q Λ θ β N n c :=
  fun _ hy => indMackeyFiltLower_smul (preservesMackeyFilt_eSum n _) hy

/-- **Claim B, passage to the partial standardization**: the layer `F_c(𝕊) / F_{c-1}(𝕊)` is the
layer `F_c / F_{c-1}` of `Ind N` modulo the kernel of the idempotent `P` of the ordered
loadings. -/
def cutMackeyLayerEquiv (n c : ℕ) :
    (SubLayer (indMackeyFilt Q Λ θ β N n c) (indMackeyFiltLower Q Λ θ β N n c) ⧸
        LinearMap.ker (subLayerAct (cutExcludedIdem Q Λ θ β N) (cutExcludedIdem_mem Q Λ θ β N n c)
          (cutExcludedIdem_mem_lower Q Λ θ β N n c))) ≃ₗ[k]
      SubLayer (cutMackeyFilt Q Λ θ β N n c) (cutMackeyFiltLower Q Λ θ β N n c) :=
  idemLayerEquiv _ cutExcludedIdem_idem _ _

/-- **Claim B, passage to the partial standardization**, image form: the layer of `𝕊(N)` is
`P̄ (F_c / F_{c-1})`, the layer of `Ind N` cut down by the ordered loadings. -/
def cutMackeyLayerRangeEquiv (n c : ℕ) :
    LinearMap.range (subLayerAct (cutExcludedIdem Q Λ θ β N) (cutExcludedIdem_mem Q Λ θ β N n c)
        (cutExcludedIdem_mem_lower Q Λ θ β N n c)) ≃ₗ[k]
      SubLayer (cutMackeyFilt Q Λ θ β N n c) (cutMackeyFiltLower Q Λ θ β N n c) :=
  idemLayerRangeEquiv _ cutExcludedIdem_idem _ _

variable {Q Λ θ β N} (hQ : KLRSymm Q)

/-- The action on the layer of `Ind N` of an affine element preserving the Mackey filtration. -/
abbrev indLayerAct {n : ℕ} {z : KLRAlgebra k S (α + δ)}
    (hz : PreservesMackeyFilt n (Multiset.card α) z) (c : ℕ) :
    SubLayer (indMackeyFilt Q Λ θ β N n c) (indMackeyFiltLower Q Λ θ β N n c) →ₗ[k]
      SubLayer (indMackeyFilt Q Λ θ β N n c) (indMackeyFiltLower Q Λ θ β N n c) :=
  subLayerAct (DistribSMul.toLinearMap k _ z) (fun _ hy => indMackeyFilt_smul hz hy)
    (fun _ hy => indMackeyFiltLower_smul hz hy)

theorem cutMackeyFiltLower_action {n : ℕ} {z : KLRAlgebra k S (α + δ)}
    (hz : PreservesMackeyFilt n (Multiset.card α) z) {c : ℕ} {v : CutStandard Q Λ θ β N}
    (hv : v ∈ cutMackeyFiltLower Q Λ θ β N n c) :
    cutStandardAction Q Λ θ β N hQ (affineToTensor Q Λ θ β z) v ∈
      cutMackeyFiltLower Q Λ θ β N n c := by
  obtain ⟨y, hy, rfl⟩ :=
    (Submodule.mem_map (f := (LinearMap.ker (cutExcludedIdem Q Λ θ β N)).mkQ)).1 hv
  change cutStandardAction Q Λ θ β N hQ (affineToTensor Q Λ θ β z)
    ((excludedSpace (cutShuffleAction Q Λ θ β N) (cutOrderedLoadings θ β)).mkQ y) ∈ _
  rw [cutStandardAction_affineToTensor]
  exact ⟨z • y, indMackeyFiltLower_smul hz hy, rfl⟩

/-- The action on the layer of `𝕊(N)`, through `T^λ`, of an affine element preserving the Mackey
filtration. -/
abbrev cutLayerAct {n : ℕ} {z : KLRAlgebra k S (α + δ)}
    (hz : PreservesMackeyFilt n (Multiset.card α) z) (c : ℕ) :
    SubLayer (cutMackeyFilt Q Λ θ β N n c) (cutMackeyFiltLower Q Λ θ β N n c) →ₗ[k]
      SubLayer (cutMackeyFilt Q Λ θ β N n c) (cutMackeyFiltLower Q Λ θ β N n c) :=
  subLayerAct (cutStandardAction Q Λ θ β N hQ (affineToTensor Q Λ θ β z))
    (fun _ hv => cutMackeyFilt_action hQ hz hv) (fun _ hv => cutMackeyFiltLower_action hQ hz hv)

/-- **The layer map is linear** for the affine elements preserving the Mackey filtration, among
them the parabolic subalgebra of the top cut. -/
theorem cutMackeyLayerMap_act {n : ℕ} {z : KLRAlgebra k S (α + δ)}
    (hz : PreservesMackeyFilt n (Multiset.card α) z) (c : ℕ)
    (y : SubLayer (indMackeyFilt Q Λ θ β N n c) (indMackeyFiltLower Q Λ θ β N n c)) :
    cutMackeyLayerMap Q Λ θ β N n c (indLayerAct hz c y) =
      cutLayerAct hQ hz c (cutMackeyLayerMap Q Λ θ β N n c y) := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
  exact (cutStandardAction_affineToTensor (N := N) Q Λ θ β hQ z v).symm

end Categorification.Stendhal

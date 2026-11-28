/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlocksStandardBasis
import Categorification.WeightedKLR.RedStrands.CutStandardMackeyTop
import Categorification.KLR.MackeyIdentityShuffle

/-!
# The block-split corner of a partial standardization at a cut

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half, step L5 (the bottom factor
at `S_+`): on the part of `𝕊(N)` whose loadings carry the weight of the first block in the
first positions, only the identity shuffle coordinate survives.

In shuffle coordinates `𝕊(N) ≅ ⊕_u ε_u N` (`cutStandardShuffleEquiv`), a sum `e(T)` of loading
idempotents acts on the coordinate `u` by `∑_{s ∈ T} 1_{u s}`
(`cutStandardShuffleEquiv_action_eSum`). If `1_{u s}` kills `N` for every `u ≠ 1` and `s ∈ T`,
the identity coordinate is a `k`-linear isomorphism from the corner `e(T) 𝕊(N)`
(`cutLoadCorner`) onto `ε_1 N ∩ 1_T N` (`inputLoadCorner`), `cutIdentityCornerEquiv`.

This holds for every set `T` of concatenations `i j` of a loading of the first block and a
loading of the second (`concatIdem_smul_eq_zero_of_ne_one`): for `u ≠ 1` the first strand of the
second block of `u s` comes from the first block of `s`, so it is black, and the loading of the
second block is violated (L1, `cutInput_one_tmul_e_smul_eq_zero`). Webster's proof does not
spell this out. The inverse is the identity-shuffle copy `n ↦ 1 ⊗ n` of the input
(`cutIdentityCornerEquiv_symm_apply`). This extends `cutStandardLoadingFixedEquiv` (one
loading `s` with `1_{u s} = 0` for `u ≠ 1`) to sets of loadings whose shuffles only kill the
input.

Any commutative ring `k`, symmetric `Q`.

## Main definitions

* `Stendhal.cutLoadCorner`, `Stendhal.inputLoadCorner`,
  `Stendhal.cutIdentityCornerEquiv`.

## Main results

* `Stendhal.cutStandardShuffleEquiv_action_eSum`, `Stendhal.concatIdem_smul_eq_zero_of_ne_one`,
  `Stendhal.cutIdentityCornerEquiv_apply`, `Stendhal.cutIdentityCornerEquiv_symm_apply`,
  `Stendhal.cutIdentityCornerEquiv_symm_concat`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA
open scoped TensorProduct

variable {I k : Type*} [DecidableEq I] [CommRing k] {a r : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (a + r) → I →₀ ℕ) (θ β : Multiset I)

local notation "α" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd r)) (stendhalWeight a θ)
local notation "δ" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd a)) (stendhalWeight r β)
local notation "S" => stendhalQ Q Λ
local notation "Sh" => Shuffle (Seq.card_add' α δ)

variable (N : Type*) [AddCommGroup N] [Module k N] [Module (cutFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] (hQ : KLRSymm Q)

/-- **A sum of loading idempotents acts on the shuffle coordinates**: `e(T)` acts on the
coordinate `u` of `𝕊(N)` by `∑_{s ∈ T} 1_{u s}`. -/
theorem cutStandardShuffleEquiv_action_eSum (T : Finset (Seq (α + δ)))
    (w : CutStandard Q Λ θ β N) (u : Sh) :
    (cutStandardShuffleEquiv Q Λ θ β N hQ
        (cutStandardAction Q Λ θ β N hQ (affineToTensor Q Λ θ β (eSum S T)) w) :
          Sh → CutInput Q Λ θ β N) u =
      (∑ s ∈ T, concatIdem (Q := S) (u.1 • s)) •
        (cutStandardShuffleEquiv Q Λ θ β N hQ w : Sh → CutInput Q Λ θ β N) u := by
  rw [eSum, map_sum, map_sum, LinearMap.sum_apply, map_sum,
    Submodule.coe_sum, Finset.sum_apply, Finset.sum_smul]
  exact Finset.sum_congr rfl fun s _ => cutStandardShuffleEquiv_action_e Q Λ θ β hQ s w u

/-- **The corner `e(T) 𝕊(N)`**: the elements fixed by the sum of loading idempotents of `T`. -/
def cutLoadCorner (T : Finset (Seq (α + δ))) : Submodule k (CutStandard Q Λ θ β N) :=
  LinearMap.eqLocus (cutStandardAction Q Λ θ β N hQ (affineToTensor Q Λ θ β (eSum S T)))
    LinearMap.id

theorem mem_cutLoadCorner {T : Finset (Seq (α + δ))} {z : CutStandard Q Λ θ β N} :
    z ∈ cutLoadCorner Q Λ θ β N hQ T ↔
      cutStandardAction Q Λ θ β N hQ (affineToTensor Q Λ θ β (eSum S T)) z = z :=
  Iff.rfl

/-- **The corner `ε_1 N ∩ 1_T N`** of the input, `1_T = ∑_{s ∈ T} 1_s`. -/
def inputLoadCorner (T : Finset (Seq (α + δ))) : Submodule k (CutInput Q Λ θ β N) :=
  LinearMap.eqLocus (cutShuffleIdemMap Q Λ θ β N (shufOne : Sh)) LinearMap.id ⊓
    LinearMap.eqLocus (DistribSMul.toLinearMap k (CutInput Q Λ θ β N)
      (∑ s ∈ T, concatIdem (Q := S) s : TensorKLR S α δ)) LinearMap.id

theorem mem_inputLoadCorner {T : Finset (Seq (α + δ))} {n : CutInput Q Λ θ β N} :
    n ∈ inputLoadCorner Q Λ θ β N T ↔
      cutShuffleIdem Q Λ θ β (shufOne : Sh) • n = n ∧
        (∑ s ∈ T, concatIdem (Q := S) s : TensorKLR S α δ) • n = n :=
  Iff.rfl

variable {Q Λ θ β N hQ}

/-- A coordinate fixed by `e(T)`. -/
theorem coord_eq_of_mem_cutLoadCorner {T : Finset (Seq (α + δ))} {z : CutStandard Q Λ θ β N}
    (hz : z ∈ cutLoadCorner Q Λ θ β N hQ T) (u : Sh) :
    (cutStandardShuffleEquiv Q Λ θ β N hQ z : Sh → CutInput Q Λ θ β N) u =
      (∑ s ∈ T, concatIdem (Q := S) (u.1 • s)) •
        (cutStandardShuffleEquiv Q Λ θ β N hQ z : Sh → CutInput Q Λ θ β N) u := by
  conv_lhs => rw [← (mem_cutLoadCorner Q Λ θ β N hQ).1 hz]
  exact cutStandardShuffleEquiv_action_eSum Q Λ θ β N hQ T z u

/-- The identity coordinate of an element of the corner lies in `ε_1 N ∩ 1_T N`. -/
theorem coord_one_mem_inputLoadCorner {T : Finset (Seq (α + δ))} {z : CutStandard Q Λ θ β N}
    (hz : z ∈ cutLoadCorner Q Λ θ β N hQ T) :
    (cutStandardShuffleEquiv Q Λ θ β N hQ z : Sh → CutInput Q Λ θ β N) (shufOne : Sh) ∈
      inputLoadCorner Q Λ θ β N T := by
  refine (mem_inputLoadCorner Q Λ θ β N).2 ⟨?_, ?_⟩
  · exact (cutShuffleIdem_mem_range_iff Q Λ θ β N _ _).1
      ((cutStandardShuffleEquiv Q Λ θ β N hQ z).2 _ (Set.mem_univ _))
  · have h := coord_eq_of_mem_cutLoadCorner hz (shufOne : Sh)
    rw [show (shufOne : Sh).1 = 1 from rfl] at h
    simp only [one_smul] at h
    exact h.symm

/-- The family supported at the identity shuffle. -/
def oneCoordFamily (n : CutInput Q Λ θ β N) : Sh → CutInput Q Λ θ β N :=
  fun u => if u.1 = 1 then n else 0

theorem oneCoordFamily_mem {T : Finset (Seq (α + δ))} {n : CutInput Q Λ θ β N}
    (hn : n ∈ inputLoadCorner Q Λ θ β N T) :
    oneCoordFamily n ∈ cutShuffleCoords Q Λ θ β N := by
  intro u _
  refine (cutShuffleIdem_mem_range_iff Q Λ θ β N u _).2 ?_
  unfold oneCoordFamily
  split_ifs with hu
  · have hu' : u = (shufOne : Sh) := Subtype.ext hu
    rw [hu']
    exact ((mem_inputLoadCorner Q Λ θ β N).1 hn).1
  · exact smul_zero _

variable (Q Λ θ β N hQ) in
/-- **The identity coordinate on the corner `e(T) 𝕊(N)`**: if `1_{u s}` kills the input for
every shuffle `u ≠ 1` and every `s ∈ T`, the identity coordinate is a `k`-linear isomorphism
`e(T) 𝕊(N) ≅ ε_1 N ∩ 1_T N`. -/
def cutIdentityCornerEquiv (T : Finset (Seq (α + δ)))
    (hT : ∀ u : Sh, u.1 ≠ 1 → ∀ s ∈ T, ∀ n : CutInput Q Λ θ β N,
      concatIdem (Q := S) (u.1 • s) • n = 0) :
    cutLoadCorner Q Λ θ β N hQ T ≃ₗ[k] inputLoadCorner Q Λ θ β N T where
  toFun z := ⟨_, coord_one_mem_inputLoadCorner z.2⟩
  map_add' z z' := Subtype.ext (by
    simp only [Submodule.coe_add, map_add, Pi.add_apply])
  map_smul' c z := Subtype.ext (by
    simp only [Submodule.coe_smul, map_smul, Pi.smul_apply, RingHom.id_apply])
  invFun n := ⟨(cutStandardShuffleEquiv Q Λ θ β N hQ).symm ⟨_, oneCoordFamily_mem n.2⟩, by
    rw [mem_cutLoadCorner]
    apply (cutStandardShuffleEquiv Q Λ θ β N hQ).injective
    apply Subtype.ext
    funext u
    rw [cutStandardShuffleEquiv_action_eSum, LinearEquiv.apply_symm_apply]
    change (∑ s ∈ T, concatIdem (Q := S) (u.1 • s)) • oneCoordFamily (n : CutInput Q Λ θ β N) u =
      oneCoordFamily (n : CutInput Q Λ θ β N) u
    unfold oneCoordFamily
    split_ifs with hu
    · simp only [hu, one_smul]
      exact ((mem_inputLoadCorner Q Λ θ β N).1 n.2).2
    · exact smul_zero _⟩
  left_inv z := by
    apply Subtype.ext
    apply (cutStandardShuffleEquiv Q Λ θ β N hQ).injective
    rw [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    funext u
    change oneCoordFamily _ u = _
    unfold oneCoordFamily
    split_ifs with hu
    · have hu' : u = (shufOne : Sh) := Subtype.ext hu
      rw [hu']
    · rw [coord_eq_of_mem_cutLoadCorner z.2 u, Finset.sum_smul]
      exact (Finset.sum_eq_zero fun s hs => hT u hu s hs _).symm
  right_inv n := by
    apply Subtype.ext
    change (cutStandardShuffleEquiv Q Λ θ β N hQ
      ((cutStandardShuffleEquiv Q Λ θ β N hQ).symm ⟨_, oneCoordFamily_mem n.2⟩) :
        Sh → CutInput Q Λ θ β N) (shufOne : Sh) = n
    rw [LinearEquiv.apply_symm_apply]
    exact ite_eq_left_iff.2 fun h => absurd rfl h

theorem cutIdentityCornerEquiv_apply (T : Finset (Seq (α + δ)))
    (hT : ∀ u : Sh, u.1 ≠ 1 → ∀ s ∈ T, ∀ n : CutInput Q Λ θ β N,
      concatIdem (Q := S) (u.1 • s) • n = 0) (z : cutLoadCorner Q Λ θ β N hQ T) :
    (cutIdentityCornerEquiv Q Λ θ β N hQ T hT z : CutInput Q Λ θ β N) =
      (cutStandardShuffleEquiv Q Λ θ β N hQ z : Sh → CutInput Q Λ θ β N) (shufOne : Sh) :=
  rfl

/-- **The inverse is the identity-shuffle copy of the input**: `n ↦ 1 ⊗ n`. -/
theorem cutIdentityCornerEquiv_symm_apply (T : Finset (Seq (α + δ)))
    (hT : ∀ u : Sh, u.1 ≠ 1 → ∀ s ∈ T, ∀ n : CutInput Q Λ θ β N,
      concatIdem (Q := S) (u.1 • s) • n = 0) (n : inputLoadCorner Q Λ θ β N T) :
    ((cutIdentityCornerEquiv Q Λ θ β N hQ T hT).symm n : CutStandard Q Λ θ β N) =
      cutStandardUnit Q Λ θ β N (n : CutInput Q Λ θ β N) := by
  apply (cutStandardShuffleEquiv Q Λ θ β N hQ).injective
  apply Subtype.ext
  funext u
  rw [cutStandardShuffleEquiv_unit]
  change (cutStandardShuffleEquiv Q Λ θ β N hQ
    ((cutStandardShuffleEquiv Q Λ θ β N hQ).symm ⟨_, oneCoordFamily_mem n.2⟩) :
      Sh → CutInput Q Λ θ β N) u = _
  rw [LinearEquiv.apply_symm_apply]
  change oneCoordFamily (n : CutInput Q Λ θ β N) u = _
  unfold oneCoordFamily
  split_ifs with hu
  · have hu' : u = shufOne := Subtype.ext hu
    rw [hu', Pi.single_eq_same]
  · have hu' : u ≠ shufOne := fun h => hu (by rw [h]; rfl)
    rw [Pi.single_eq_of_ne hu']

/-- **The corner isomorphism is linear for the affine algebra of the two blocks**: on the
identity-shuffle copy, `t ∈ R(α) ⊗ R(δ)` acts through the input. -/
theorem cutIdentityCornerEquiv_symm_concat (T : Finset (Seq (α + δ)))
    (hT : ∀ u : Sh, u.1 ≠ 1 → ∀ s ∈ T, ∀ n : CutInput Q Λ θ β N,
      concatIdem (Q := S) (u.1 • s) • n = 0) (t : TensorKLR S α δ)
    (n : inputLoadCorner Q Λ θ β N T) (htn : t • (n : CutInput Q Λ θ β N) ∈
      inputLoadCorner Q Λ θ β N T) :
    ((cutIdentityCornerEquiv Q Λ θ β N hQ T hT).symm ⟨_, htn⟩ : CutStandard Q Λ θ β N) =
      cutStandardAction Q Λ θ β N hQ (affineToTensor Q Λ θ β (concat S α δ t))
        ((cutIdentityCornerEquiv Q Λ θ β N hQ T hT).symm n) := by
  rw [cutIdentityCornerEquiv_symm_apply, cutIdentityCornerEquiv_symm_apply]
  exact (cutStandardAction_concat_unit Q Λ θ β N hQ t (n : CutInput Q Λ θ β N)).symm

omit [Module k N] [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] in
/-- **Only the identity shuffle survives on a block-split loading**: for `u ≠ 1` and a
concatenation `s = i j` of loadings of the two blocks, `1_{u s}` kills the input of the induced
model, since the second block of `u s` starts with a black strand of the first block. -/
theorem concatIdem_smul_eq_zero_of_ne_one (u : Sh) (hu : u.1 ≠ 1) (s : Seq (α + δ))
    (hs : s ∈ concatSet α δ) (n : CutInput Q Λ θ β N) :
    concatIdem (Q := S) (u.1 • s) • n = 0 := by
  by_cases hc : u.1 • s ∈ concatSet α δ
  · obtain ⟨i', j', hij⟩ := mem_concatSet.1 hc
    obtain ⟨i, j, rfl⟩ := mem_concatSet.1 hs
    have hcard : 0 < Multiset.card δ := by
      by_contra h0
      exact hu (shuffle_eq_one_of_tail_fixed u fun y => absurd y.2 (by omega))
    have hlt := shuffle_first_tail_lt_of_ne_one u hu hcard
    have hval := tail_val_of_append_eq hij ⟨0, hcard⟩
    have hpos : u.1⁻¹ (Seq.posR α ⟨0, hcard⟩) =
        Seq.posL δ ⟨(u.1⁻¹ (Seq.posR α ⟨0, hcard⟩)).val, hlt⟩ := Fin.ext rfl
    rw [hpos, Seq.append_posL] at hval
    have hmemL : i.1 ⟨(u.1⁻¹ (Seq.posR α ⟨0, hcard⟩)).val, hlt⟩ ∈ α := by
      have hm := Multiset.mem_map_of_mem i.1
        (Finset.mem_univ_val (⟨(u.1⁻¹ (Seq.posR α ⟨0, hcard⟩)).val, hlt⟩ : Fin _))
      rwa [i.2] at hm
    have hmemR : j'.1 ⟨0, hcard⟩ ∈ δ := by
      have hm := Multiset.mem_map_of_mem j'.1 (Finset.mem_univ_val (⟨0, hcard⟩ : Fin _))
      rwa [j'.2] at hm
    have hviol : IsViolated j' := by
      refine ⟨hcard, ?_⟩
      change (j'.1 ⟨0, hcard⟩).isLeft
      rw [hval] at hmemR ⊢
      obtain ⟨x, -, hx⟩ := Multiset.mem_map.1 hmemL
      obtain ⟨y, -, hy⟩ := Multiset.mem_map.1 hmemR
      rcases x with b | x
      · rw [← hx]; rfl
      · rcases y with c | y
        · rw [← hx] at hy; exact absurd hy (by simp)
        · rw [← hx] at hy
          have hv := congrArg (fun z => match z with | .inl _ => 0 | .inr t => t.val) hy
          simp only [Sum.map_inr, Fin.val_natAdd, Fin.val_castAdd] at hv
          omega
    rw [← hij, concatIdem_append, show (e i' ⊗ₜ e j' : TensorKLR S α δ) =
      (e i' ⊗ₜ (1 : KLRAlgebra k S δ)) * ((1 : KLRAlgebra k S α) ⊗ₜ e j') by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul], mul_smul,
      cutInput_one_tmul_e_smul_eq_zero j' hviol n, smul_zero]
  · rw [concatIdem_of_not_mem hc, zero_smul]

variable (Q Λ θ β N hQ) in
/-- **The identity coordinate on a block-split corner**: for a set `T` of concatenations of
loadings of the two blocks, `e(T) 𝕊(N) ≅ ε_1 N ∩ 1_T N`. -/
def cutIdentityCornerEquivConcat (T : Finset (Seq (α + δ))) (hT : T ⊆ concatSet α δ) :
    cutLoadCorner Q Λ θ β N hQ T ≃ₗ[k] inputLoadCorner Q Λ θ β N T :=
  cutIdentityCornerEquiv Q Λ θ β N hQ T fun u hu s hs n =>
    concatIdem_smul_eq_zero_of_ne_one u hu s (hT hs) n

end Categorification.Stendhal

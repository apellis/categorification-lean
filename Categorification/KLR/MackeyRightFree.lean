/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.MackeyTopDots
import Categorification.KLR.Crystal.IndDecomp

/-!
# The Mackey filtration in the coordinates of Proposition 2.16

Khovanov–Lauda I (arXiv:0803.4121v2), §2.6, Propositions 2.16 and 2.18. By Proposition 2.16 in
right-module form (`KLRAlgebra.rightFreeEquivOf`), every `r ∈ R(ν + ν') 1_{ν,ν'}` is uniquely
`r = ∑_u ŵ_u^* ι(t_u)`, `u` running over the shuffles of `(ν, ν')` and `ŵ_u^* = ψ_{σ(u)^{rev}}
1_{ν,ν'}`. For a top cut `n`, `r` lies in the step `c` of the Mackey filtration
(`mackeyFilt n |ν| c`: diagrams with at most `c` strands from the bottom block `ν'` to the top
positions `< n`) **if and only if** `t_u = 0` whenever `u⁻¹` has more than `c` such strands
(`KLRAlgebra.mem_mackeyFilt_iff_rightFreeEquivOf_symm`).

The forward direction expands `hflip r ∈ 1_{ν,ν'} R(ν + ν')` in the basis with dots on top
adapted to Proposition 2.16 (`KLRAlgebra.lbasis` for the words `parWord`), whose coordinates
are those of `hflip r` in the basis with dots at the bottom (`basisOfSymm`, words `revWord`);
the latter vanish at permutations with more than `c` crossing strands by the basis form of the
Mackey filtration (`mackeyFilt_eq_stdSpan`). The backward direction is the stability of the
filtration under the right action of `R(ν) ⊗ R(ν')` (`mul_botConcat_mem_mackeyFilt`) and the
subword property of `crossCount` (`TypeA.crossCount_le_of_mem_subProds`).

Symmetric `Q` (`KLRSymm Q`), any commutative ring `k`, any choice `σ` of reduced words for the
shuffles.

## Main results

* `KLRAlgebra.basisOfSymm_repr_eq_zero_of_mem_mackeyFilt`,
  `KLRAlgebra.lbasis_repr_hflip_eq_zero_of_mem_mackeyFilt`.
* `KLRAlgebra.lbasis_repr_indIdxMap`: the coordinates of an element of `1_{ν,ν'} R(ν + ν')` in
  the basis of Proposition 2.16 are its coordinates in the adapted basis with dots on top.
* `KLRAlgebra.hatWRevOf_mem_mackeyFilt`: `ŵ_u^*` lies in the step `crossCount(u⁻¹)`.
* `KLRAlgebra.mem_mackeyFilt_iff_rightFreeEquivOf_symm`.
* `KLRAlgebra.mem_span_tmul_mackeyFilt_iff`: the same description for the induced module
  `Ind N` in its coordinates `indDecompOf`.
-/

noncomputable section

namespace Categorification.KLR

open Equiv MvPolynomial TypeA MulOpposite
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k}

namespace KLRAlgebra

section Basis

variable {μ : Multiset I} (hsym : KLRSymm Q) (ρ : Perm (Fin (Multiset.card μ)) → List ℕ)
  (hρ : ∀ w, IsReduced (Multiset.card μ) (ρ w) ∧ wordProd (Multiset.card μ) (ρ w) = w)

local notation "m" => Multiset.card μ

/-- The coordinates of an element of the step `c` of the Mackey filtration in the basis with
dots at the bottom vanish at permutations with more than `c` crossing strands. -/
theorem basisOfSymm_repr_eq_zero_of_mem_mackeyFilt {n n'' c : ℕ} (hn : n ≤ m) (hn'' : n'' ≤ m)
    {y : KLRAlgebra k Q μ} (hy : y ∈ mackeyFilt k Q μ n n'' c)
    (b : Seq μ × Perm (Fin m) × (Fin m →₀ ℕ)) (hb : c < crossCount n n'' b.2.1) :
    (basisOfSymm hsym ρ hρ).repr y b = 0 := by
  rw [mackeyFilt_eq_stdSpan hn hn'' ρ hρ c, stdSpan] at hy
  have himg : stdElt ρ '' {b : Seq μ × Perm (Fin m) × (Fin m →₀ ℕ) |
      b.2.1 ∈ {w | crossCount n n'' w ≤ c}} =
      (basisOfSymm hsym ρ hρ) '' {b | b.2.1 ∈ {w | crossCount n n'' w ≤ c}} := by
    congr 1
    funext b
    rw [basisOfSymm_apply]
    rfl
  rw [himg, Module.Basis.mem_span_image] at hy
  by_contra hne
  exact absurd (hy (Finsupp.mem_support_iff.2 hne)) (by simpa using hb)

/-- The coordinates of `hflip y` in the basis with dots on top are those of `y` in the basis with
dots at the bottom, at the flipped index. -/
theorem lbasis_repr_hflip (y : KLRAlgebra k Q μ) (b : Seq μ × Perm (Fin m) × (Fin m →₀ ℕ)) :
    (lbasis hsym ρ hρ).repr (hflip y) b =
      (basisOfSymm hsym (revWord ρ) (revWord_spec ρ hρ)).repr y (flipIdx.symm b) := by
  rw [lbasis, Module.Basis.repr_reindex_apply, Module.Basis.map_repr, LinearEquiv.trans_apply]
  congr 2
  rw [LinearEquiv.symm_apply_eq, hflipEquiv_apply]

theorem lbasis_repr_hflip_eq_zero_of_mem_mackeyFilt {n n'' c : ℕ} (hn : n ≤ m) (hn'' : n'' ≤ m)
    {y : KLRAlgebra k Q μ} (hy : y ∈ mackeyFilt k Q μ n n'' c)
    (b : Seq μ × Perm (Fin m) × (Fin m →₀ ℕ)) (hb : c < crossCount n n'' b.2.1⁻¹) :
    (lbasis hsym ρ hρ).repr (hflip y) b = 0 := by
  rw [lbasis_repr_hflip]
  exact basisOfSymm_repr_eq_zero_of_mem_mackeyFilt hsym _ _ hn hn'' hy _ hb

end Basis

section Induction

variable {ν ν' : Multiset I} (hsym : KLRSymm Q)
  (ρ₁ : Perm (Fin (Multiset.card ν)) → List ℕ) (ρ₂ : Perm (Fin (Multiset.card ν')) → List ℕ)
  (σ : Shuffle (Seq.card_add' ν ν') → List ℕ)
  (hρ₁ : ∀ a, IsReduced (Multiset.card ν) (ρ₁ a) ∧ wordProd (Multiset.card ν) (ρ₁ a) = a)
  (hρ₂ : ∀ b, IsReduced (Multiset.card ν') (ρ₂ b) ∧ wordProd (Multiset.card ν') (ρ₂ b) = b)
  (hσ : ∀ u, IsReduced (Multiset.card (ν + ν')) (σ u) ∧
    wordProd (Multiset.card (ν + ν')) (σ u) = u.1)

include hσ in
/-- The `k`-linear form of Proposition 2.16: `freeMap` is the change of basis from the basis of
`Shuffle →₀ R(ν) ⊗ R(ν')` to `inductionBasis`. -/
theorem freeMap_restrictScalars_eq :
    (freeMap (Q := Q) σ).restrictScalars k =
      ((Finsupp.basis (R := k) (ι := Shuffle (Seq.card_add' ν ν'))
        (fun _ => (lbasis (Q := Q) hsym ρ₁ hρ₁).tensorProduct (lbasis (Q := Q) hsym ρ₂ hρ₂))).equiv
          (inductionBasis (Q := Q) hsym ρ₁ ρ₂ σ hρ₁ hρ₂ hσ) sigmaIdxEquiv).toLinearMap := by
  refine (Finsupp.basis (R := k) (ι := Shuffle (Seq.card_add' ν ν'))
    (fun _ => (lbasis (Q := Q) hsym ρ₁ hρ₁).tensorProduct
      (lbasis (Q := Q) hsym ρ₂ hρ₂))).ext fun ⟨u, x⟩ => ?_
  rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply]
  apply Subtype.ext
  simp only [LinearMap.restrictScalars_apply, Finsupp.coe_basis, freeMap,
    Finsupp.linearCombination_single, coe_tensor_smul, Module.Basis.tensorProduct_apply']
  rw [show sigmaIdxEquiv ⟨u, x⟩ = (x, u) from rfl, inductionBasis_apply]
  rfl

include hσ in
/-- The coordinates of `∑_u ι(g_u) ŵ_u` in `inductionBasis` are the coordinates of the `g_u`. -/
theorem inductionBasis_repr_freeMap
    (g : Shuffle (Seq.card_add' ν ν') →₀ KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν')
    (x : Idx ν × Idx ν') (u : Shuffle (Seq.card_add' ν ν')) :
    (inductionBasis (Q := Q) hsym ρ₁ ρ₂ σ hρ₁ hρ₂ hσ).repr (freeMap (Q := Q) σ g) (x, u) =
      ((lbasis (Q := Q) hsym ρ₁ hρ₁).tensorProduct (lbasis (Q := Q) hsym ρ₂ hρ₂)).repr
        (g u) x := by
  have h := LinearMap.congr_fun (freeMap_restrictScalars_eq hsym ρ₁ ρ₂ σ hρ₁ hρ₂ hσ) g
  rw [LinearMap.restrictScalars_apply] at h
  rw [h, LinearEquiv.coe_coe, Module.Basis.equiv, LinearEquiv.trans_apply]
  set B := inductionBasis (Q := Q) hsym ρ₁ ρ₂ σ hρ₁ hρ₂ hσ
  have key : ∀ z, B.repr z (x, u) = (B.reindex sigmaIdxEquiv.symm).repr z ⟨u, x⟩ := fun z => by
    rw [Module.Basis.repr_reindex_apply]; rfl
  rw [key, LinearEquiv.apply_symm_apply, Finsupp.basis_repr]

include hσ in
/-- The coordinates of an element of `1_{ν,ν'} R(ν + ν')` in `inductionBasis` are its
coordinates in the adapted basis with dots on top. -/
theorem lbasis_repr_inductionBasis (y : oneConcatSub (ν := ν) (ν' := ν') (k := k) Q)
    (x : IndIdx ν ν') :
    (lbasis hsym (parWord ρ₁ ρ₂ σ) (parWord_spec ρ₁ ρ₂ σ hρ₁ hρ₂ hσ)).repr y.1 (indIdxMap x) =
      (inductionBasis (Q := Q) hsym ρ₁ ρ₂ σ hρ₁ hρ₂ hσ).repr y x := by
  set B := inductionBasis (Q := Q) hsym ρ₁ ρ₂ σ hρ₁ hρ₂ hσ
  set L := lbasis (Q := Q) hsym (parWord ρ₁ ρ₂ σ) (parWord_spec ρ₁ ρ₂ σ hρ₁ hρ₂ hσ)
  have hB : ∀ x, (B x : KLRAlgebra k Q (ν + ν')) = L (indIdxMap x) := fun x => by
    rw [inductionBasis_apply, ← indElt_eq hsym ρ₁ ρ₂ σ hρ₁ hρ₂ hσ x]
    rfl
  conv_lhs => rw [← B.linearCombination_repr y]
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Submodule.coe_sum, map_sum,
    Finsupp.finsetSum_apply]
  simp only [Submodule.coe_smul, hB, map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
    Finsupp.single_apply, (indIdxMap_injective (ν := ν) (ν' := ν')).eq_iff, smul_eq_mul,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single x
    (fun b _ hb => ite_eq_right_iff.2 fun h => absurd (indIdxMap_injective h) hb)
    (fun hx => by simp only [↓reduceIte]; exact Finsupp.notMem_support_iff.1 hx)]
  simp only [↓reduceIte]

include hσ in
/-- **Proposition 2.16 coordinates in the adapted basis**: for `y ∈ 1_{ν,ν'} R(ν + ν')`, the
coordinate of `y` at `ι(b ⊗ b') ŵ_u` is the coordinate of the `u`-component of `y` at `b ⊗ b'`. -/
theorem lbasis_repr_indIdxMap (y : oneConcatSub (ν := ν) (ν' := ν') (k := k) Q)
    (x : Idx ν × Idx ν') (u : Shuffle (Seq.card_add' ν ν')) :
    (lbasis hsym (parWord ρ₁ ρ₂ σ) (parWord_spec ρ₁ ρ₂ σ hρ₁ hρ₂ hσ)).repr y.1
        (indIdxMap (x, u)) =
      ((lbasis (Q := Q) hsym ρ₁ hρ₁).tensorProduct (lbasis (Q := Q) hsym ρ₂ hρ₂)).repr
        ((freeBasis hsym ρ₁ ρ₂ σ hρ₁ hρ₂ hσ).repr y u) x := by
  rw [lbasis_repr_inductionBasis]
  have hy : y = freeMap (Q := Q) σ ((freeBasis hsym ρ₁ ρ₂ σ hρ₁ hρ₂ hσ).repr y) := by
    exact ((LinearEquiv.ofBijective _ (freeMap_bijective hsym ρ₁ ρ₂ σ hρ₁ hρ₂ hσ)).apply_symm_apply
      y).symm
  conv_lhs => rw [hy]
  exact inductionBasis_repr_freeMap hsym ρ₁ ρ₂ σ hρ₁ hρ₂ hσ _ x u

end Induction

section RightFree

variable {ν ν' : Multiset I} (hsym : KLRSymm Q) {σ : Shuffle (Seq.card_add' ν ν') → List ℕ}
  (hσ : ∀ u, IsReduced (Multiset.card (ν + ν')) (σ u) ∧
    wordProd (Multiset.card (ν + ν')) (σ u) = u.1)

local notation "m" => Multiset.card (ν + ν')

omit [DecidableEq I] in
theorem card_le_card_add (ν ν' : Multiset I) : Multiset.card ν ≤ Multiset.card (ν + ν') := by
  rw [Multiset.card_add]; exact Nat.le_add_right _ _

include hsym hσ in
/-- **The Mackey filtration in the coordinates of Proposition 2.16, forward direction.** -/
theorem rightFreeEquivOf_symm_eq_zero_of_mem_mackeyFilt {n c : ℕ} (hn : n ≤ m)
    {r : IndBimod Q ν ν'}
    (hr : (r : KLRAlgebra k Q (ν + ν')) ∈ mackeyFilt k Q (ν + ν') n (Multiset.card ν) c)
    (u : Shuffle (Seq.card_add' ν ν')) (hu : c < crossCount n (Multiset.card ν) u.1⁻¹) :
    (rightFreeEquivOf ν ν' σ hsym hσ).symm r u = 0 := by
  set g := (rightFreeEquivOf ν ν' σ hsym hσ).symm r
  set g' := g.mapRange (tensorHflip ν ν') (map_zero _)
  have hrg : (r : KLRAlgebra k Q (ν + ν')) = hflip ((freeMap (Q := Q) σ g' : oneConcatSub Q) :
      KLRAlgebra k Q (ν + ν')) := by
    rw [← rightFreeMapOf_eq_hflip_freeMap, ← coe_rightFreeEquivOf (hsym := hsym) hσ,
      LinearEquiv.apply_symm_apply]
  have hmem : hflip (r : KLRAlgebra k Q (ν + ν')) ∈ oneConcatSub (ν := ν) (ν' := ν') Q := by
    rw [hrg, hflip_hflip]; exact (freeMap (Q := Q) σ g').2
  set y : oneConcatSub (ν := ν) (ν' := ν') (k := k) Q := ⟨hflip r, hmem⟩
  have hy : y = freeMap (Q := Q) σ g' := Subtype.ext (by
    change hflip (r : KLRAlgebra k Q (ν + ν')) = _
    rw [hrg, hflip_hflip])
  let ρ₁ : Perm (Fin (Multiset.card ν)) → List ℕ := canWord _
  let ρ₂ : Perm (Fin (Multiset.card ν')) → List ℕ := canWord _
  have hρ₁ : ∀ a, IsReduced (Multiset.card ν) (ρ₁ a) ∧ wordProd (Multiset.card ν) (ρ₁ a) = a :=
    fun a => ⟨isReduced_canWord _ a, wordProd_canWord _ a⟩
  have hρ₂ : ∀ b, IsReduced (Multiset.card ν') (ρ₂ b) ∧ wordProd (Multiset.card ν') (ρ₂ b) = b :=
    fun b => ⟨isReduced_canWord _ b, wordProd_canWord _ b⟩
  have hrep : (freeBasis hsym ρ₁ ρ₂ σ hρ₁ hρ₂ hσ).repr y = g' := by
    rw [hy]
    exact (LinearEquiv.ofBijective _
      (freeMap_bijective hsym ρ₁ ρ₂ σ hρ₁ hρ₂ hσ)).symm_apply_apply g'
  have hzero : g' u = 0 := by
    rw [← hrep]
    refine ((lbasis (Q := Q) hsym ρ₁ hρ₁).tensorProduct
      (lbasis (Q := Q) hsym ρ₂ hρ₂)).ext_elem fun x => ?_
    rw [← lbasis_repr_indIdxMap hsym ρ₁ ρ₂ σ hρ₁ hρ₂ hσ, map_zero, Finsupp.zero_apply]
    refine lbasis_repr_hflip_eq_zero_of_mem_mackeyFilt hsym _ _ hn
      (card_le_card_add ν ν') hr _ ?_
    change c < crossCount n (Multiset.card ν)
      (blockPerm (Seq.card_add' ν ν') x.1.2.1 x.2.2.1 * u.1)⁻¹
    rw [mul_inv_rev, blockPerm_inv, crossCount_mul_blockPerm]
    exact hu
  have : tensorHflip ν ν' (g u) = 0 := by
    rw [← hzero]; rfl
  rw [← tensorHflip_tensorHflip (g u), this, map_zero]

include hσ in
/-- `ŵ_u^* = ψ_{σ(u)^{rev}} 1_{ν,ν'}` lies in the step of the Mackey filtration given by the
crossing strands of `u⁻¹`. -/
theorem hatWRevOf_mem_mackeyFilt {n : ℕ} (hn : n ≤ m) (u : Shuffle (Seq.card_add' ν ν')) :
    hatWRevOf σ u ∈
      mackeyFilt k Q (ν + ν') n (Multiset.card ν) (crossCount n (Multiset.card ν) u.1⁻¹) := by
  have hred : IsReduced m (σ u).reverse := by
    obtain ⟨⟨hv, hl⟩, hw⟩ := hσ u
    refine ⟨validWord_reverse.2 hv, ?_⟩
    rw [List.length_reverse, hl, wordProd_reverse, length_inv]
  have hprod : wordProd m (σ u).reverse = u.1⁻¹ := by rw [wordProd_reverse, (hσ u).2]
  rw [hatWRevOf, oneConcat, eSum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [show (ψw (σ u).reverse * e i : KLRAlgebra k Q (ν + ν')) =
    ψw (σ u).reverse * pol 1 * e i by rw [map_one, mul_one]]
  refine mem_mackeyFilt hred.1 (fun v hv => ?_) 1 i
  have := crossCount_le_of_mem_subProds hn (card_le_card_add ν ν') hred hv
  rwa [hprod] at this

include hσ in
/-- `ŵ_u^* ι(t)` lies in the step of the Mackey filtration given by the crossing strands of
`u⁻¹`. -/
theorem hatWRevOf_mul_concat_mem_mackeyFilt {n : ℕ} (hn : n ≤ m)
    (u : Shuffle (Seq.card_add' ν ν')) (t : TensorKLR Q ν ν') :
    hatWRevOf σ u * concat Q ν ν' t ∈
      mackeyFilt k Q (ν + ν') n (Multiset.card ν) (crossCount n (Multiset.card ν) u.1⁻¹) := by
  have h2 := mul_botConcat_mem_mackeyFilt (Q := Q) (ν := ν) (ν' := ν') (ν'' := ν) (ν''' := ν')
    rfl t (hatWRevOf_mem_mackeyFilt hσ hn u)
  rw [botConcat_apply] at h2
  exact h2

include hsym hσ in
/-- **The Mackey filtration in the coordinates of Proposition 2.16**: `r = ∑_u ŵ_u^* ι(t_u)`
lies in the step `c` of the Mackey filtration of the top cut at `n` iff `t_u = 0` for every
shuffle `u` such that `u⁻¹` has more than `c` strands from the bottom block `ν'` to the top
positions `< n`. -/
theorem mem_mackeyFilt_iff_rightFreeEquivOf_symm {n c : ℕ} (hn : n ≤ m) (r : IndBimod Q ν ν') :
    (r : KLRAlgebra k Q (ν + ν')) ∈ mackeyFilt k Q (ν + ν') n (Multiset.card ν) c ↔
      ∀ u : Shuffle (Seq.card_add' ν ν'), c < crossCount n (Multiset.card ν) u.1⁻¹ →
        (rightFreeEquivOf ν ν' σ hsym hσ).symm r u = 0 := by
  refine ⟨fun hr u hu => rightFreeEquivOf_symm_eq_zero_of_mem_mackeyFilt hsym hσ hn hr u hu,
    fun h => ?_⟩
  rw [← (rightFreeEquivOf ν ν' σ hsym hσ).apply_symm_apply r, coe_rightFreeEquivOf,
    rightFreeMapOf_apply, Finsupp.sum]
  refine Submodule.sum_mem _ fun u hu => ?_
  have hle : crossCount n (Multiset.card ν) u.1⁻¹ ≤ c := by
    by_contra hlt
    exact Finsupp.mem_support_iff.1 hu (h u (not_le.1 hlt))
  exact mackeyFilt_mono hle (hatWRevOf_mul_concat_mem_mackeyFilt hσ hn u _)

include hsym hσ in
/-- **The Mackey filtration of an induced module in the coordinates of Proposition 2.16**: an
element of `Ind N = R(ν + ν') 1_{ν,ν'} ⊗ N` lies in the span of the `r ⊗ x` with `r` in the step
`c` of the Mackey filtration iff its components `n_u` (`indDecompOf`) vanish for every shuffle
`u` such that `u⁻¹` has more than `c` strands from the bottom block `ν'` to the top positions
`< n`. -/
theorem mem_span_tmul_mackeyFilt_iff (N : Type*) [AddCommGroup N] [Module k N]
    [Module (TensorKLR Q ν ν') N] [IsScalarTower k (TensorKLR Q ν ν') N] {n c : ℕ}
    (hn : n ≤ m) (y : Ind Q ν ν' N) :
    y ∈ Submodule.span k {y | ∃ (w : IndBimod Q ν ν') (x : N),
        (w : KLRAlgebra k Q (ν + ν')) ∈ mackeyFilt k Q (ν + ν') n (Multiset.card ν) c ∧
          BalancedTensor.tmul w x = y} ↔
      ∀ u : Shuffle (Seq.card_add' ν ν'), c < crossCount n (Multiset.card ν) u.1⁻¹ →
        indDecompOf σ hsym hσ N y u = 0 := by
  constructor
  · intro hy u hu
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, x, hw, rfl⟩ := hy
      rw [indDecompOf_tmul, rightFreeEquivOf_symm_eq_zero_of_mem_mackeyFilt hsym hσ hn hw u hu,
        zero_smul]
    | zero => rw [map_zero, Pi.zero_apply]
    | add y y' _ _ h h' => rw [map_add, Pi.add_apply, h, h', add_zero]
    | smul a y _ h => rw [map_smul, Pi.smul_apply, h, smul_zero]
  · intro h
    rw [← (indDecompOf σ hsym hσ N).symm_apply_apply y, indDecompOf_symm_apply]
    refine Submodule.sum_mem _ fun u _ => ?_
    by_cases hu : c < crossCount n (Multiset.card ν) u.1⁻¹
    · rw [h u hu, BalancedTensor.tmul_zero]
      exact Submodule.zero_mem _
    · refine Submodule.subset_span ⟨hatWRevSubOf σ u, _, ?_, rfl⟩
      rw [coe_hatWRevSubOf]
      exact mackeyFilt_mono (not_lt.1 hu) (hatWRevOf_mem_mackeyFilt hσ hn u)

end RightFree

end KLRAlgebra

end Categorification.KLR

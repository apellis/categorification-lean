/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.MackeyRes
import Categorification.KLR.ConcatAssoc
import Categorification.Algebra.IdempotentEquiv

/-!
# The shuffle decomposition of induced modules

Khovanov–Lauda I (arXiv:0803.4121v2), §2.6, **Lemma 2.20** (the Shuffle Lemma, TeX lines
1942–1950), ungraded form, in the strong form of a natural decomposition of the underlying
vector space of an induced module.

For an `R(ν) ⊗ R(ν')`-module `N` the induced module is
`Ind N = R(ν + ν') 1_{ν,ν'} ⊗_{R(ν) ⊗ R(ν')} N`. By Proposition 2.16
(`KLRAlgebra.freeMap_bijective`), transported along the horizontal flip, `R(ν + ν') 1_{ν,ν'}` is
a free *right* `R(ν) ⊗ R(ν')`-module with basis `ŵ_u^* = ψ_{σ(u)}^{rev} 1_{ν,ν'}`, `u` running
over the shuffles (minimal length representatives of `(S_n × S_{n'}) \ S_{n + n'}`). Hence

  `Ind N ≅ ⊕_u ŵ_u^* ⊗ N ≅ ⊕_u N`   (as vector spaces),

and the idempotent `1_s` acts on the summand `u` through the idempotent `1_{u s}` of
`R(ν) ⊗ R(ν')` (which is `1_i ⊗ 1_j` if `u s = ij`, and `0` if `u s` is not a concatenation).

## Main results

* `KLRAlgebra.hflip_concat` : the horizontal flip commutes with `ι_{ν,ν'} = concat`:
  `hflip (ι t) = ι (tensorHflip t)`, `tensorHflip = hflip ⊗ hflip`.
* `KLRAlgebra.rightFreeEquiv` : `R(ν + ν') 1_{ν,ν'} ≅ ⊕_u R(ν) ⊗ R(ν')` as vector spaces,
  compatible with the right action (`rightFreeMap_mapRange_mul`) — **Proposition 2.16 for the
  right module structure**.
* `KLRAlgebra.indDecomp` : `Ind N ≃ₗ[k] (Shuffle → N)`, with
  `indDecomp_e_smul` : `(1_s y)_u = 1_{u s} y_u` and `indDecomp_tmul_oneConcat` :
  `1_{ν,ν'} ⊗ n ↦ (n at u = 1)`.
* `KLRAlgebra.finrank_fixSub_ind` : `dim 1_s Ind N = ∑_u dim 1_{u s} N`, and
  `KLRAlgebra.shuffle_lemma_finrank` (**Lemma 2.20, ungraded**):
  `dim 1_s Ind (N₁ ⊠ N₂) = ∑ dim 1_i N₁ · dim 1_j N₂` over the ways `u` of writing `s` as a
  shuffle of `i` and `j` (`ShuffleOf ν ν' s`), i.e. `ch(Ind (N₁ ⊠ N₂)) = ch(N₁) ⧢ ch(N₂)` at
  `q = 1` (uses `finrank_fixSub_extTensor`: `dim (1_i ⊗ 1_j)(N₁ ⊠ N₂) = dim 1_i N₁ · dim 1_j N₂`);
  `KLRAlgebra.exists_shuffle_of_fixSub_ind_ne_bot` : the support form.

Gradings are not addressed here (the paper's Lemma 2.20 is the graded statement, with the
shifts `q^{-deg}` of the shuffles).
-/

noncomputable section

namespace Categorification.KLR

open Equiv MvPolynomial TypeA MulOpposite
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k}

namespace KLRAlgebra

/-! ### The horizontal flip and concatenation -/

section HflipConcat

variable {μ ν ν' : Multiset I}

theorem hflip_eSum (T : Finset (Seq ν)) : hflip (eSum Q T : KLRAlgebra k Q ν) = eSum Q T := by
  simp only [eSum, hflip_sum, hflip_e]

theorem hflip_oneConcat :
    hflip (oneConcat Q ν ν' : KLRAlgebra k Q (ν + ν')) = oneConcat Q ν ν' :=
  hflip_eSum _

/-- A multiplicative `k`-linear map `φ : R(μ) → R(ν)` whose values on `1` and on the generators
are fixed by the horizontal flip commutes with the horizontal flip. -/
theorem hflip_comm_of_gen (φ : KLRAlgebra k Q μ →ₗ[k] KLRAlgebra k Q ν)
    (hφ : ∀ a b, φ (a * b) = φ a * φ b) (h1 : hflip (φ 1) = φ 1)
    (he : ∀ i, hflip (φ (e i)) = φ (e i)) (hx : ∀ a, hflip (φ (x a)) = φ (x a))
    (hψ : ∀ j, j + 1 < Multiset.card μ → hflip (φ (ψ j)) = φ (ψ j)) (a : KLRAlgebra k Q μ) :
    hflip (φ a) = φ (hflip a) := by
  let f : KLRAlgebra k Q μ →ₗ[k] (KLRAlgebra k Q ν)ᵐᵒᵖ :=
    (opLinearEquiv k).toLinearMap ∘ₗ (hflipEquiv k Q ν).toLinearMap ∘ₗ φ
  let g : KLRAlgebra k Q μ →ₗ[k] (KLRAlgebra k Q ν)ᵐᵒᵖ :=
    (opLinearEquiv k).toLinearMap ∘ₗ φ ∘ₗ (hflipEquiv k Q μ).toLinearMap
  have hf : ∀ a, f a = op (hflip (φ a)) := fun a => rfl
  have hg : ∀ a, g a = op (φ (hflip a)) := fun a => rfl
  have hfg : f = g := by
    refine ext_of_mul f g ?_ ?_ ?_ ?_ ?_ ?_
    · intro a b; rw [hf, hf, hf, hφ, hflip_mul, op_mul]
    · intro a b; rw [hg, hg, hg, hflip_mul, hφ, op_mul]
    · rw [hf, hg, hflip_one, h1]
    · intro i; rw [hf, hg, hflip_e, he]
    · intro a; rw [hf, hg, hflip_x, hx]
    · intro j hj; rw [hf, hg, hflip_ψ, hψ j hj]
  have := congrArg unop (LinearMap.congr_fun hfg a)
  rwa [hf, hg, unop_op, unop_op] at this

theorem oneConcat_mul_ψ_left {j : ℕ} (hj : j + 1 < Multiset.card ν) :
    (oneConcat Q ν ν' * ψ j : KLRAlgebra k Q (ν + ν')) = ψ j * oneConcat Q ν ν' := by
  have := oneConcat_mul_ψw (Q := Q) (ν := ν) (ν' := ν') (α := [j]) (α' := [])
    (fun l hl => by simp only [List.mem_singleton] at hl; omega) (fun l hl => by simp at hl)
  simpa [shiftWord] using this

theorem oneConcat_mul_ψ_right {j : ℕ} (hj : j + 1 < Multiset.card ν') :
    (oneConcat Q ν ν' * ψ (Multiset.card ν + j) : KLRAlgebra k Q (ν + ν')) =
      ψ (Multiset.card ν + j) * oneConcat Q ν ν' := by
  have := oneConcat_mul_ψw (Q := Q) (ν := ν) (ν' := ν') (α := []) (α' := [j])
    (fun l hl => by simp at hl) (fun l hl => by simp only [List.mem_singleton] at hl; omega)
  simpa [shiftWord] using this

theorem hflip_concat_tmul_one (a : KLRAlgebra k Q ν) :
    hflip (concat Q ν ν' (a ⊗ₜ 1)) = concat Q ν ν' (hflip a ⊗ₜ 1) := by
  let φ : KLRAlgebra k Q ν →ₗ[k] KLRAlgebra k Q (ν + ν') :=
    (concat Q ν ν').comp ((TensorProduct.mk k _ _).flip 1)
  have hφa : ∀ a, φ a = concat Q ν ν' (a ⊗ₜ 1) := fun a => rfl
  refine hflip_comm_of_gen φ ?_ ?_ ?_ ?_ ?_ a
  · intro a b
    rw [hφa, hφa, hφa, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  · rw [hφa, concat_one_tmul_one, hflip_oneConcat]
  · intro i
    rw [hφa, concat_e_tmul_one, hflip_sum]
    simp only [hflip_e]
  · intro b
    rw [hφa, concat_x_tmul_one, hflip_mul, hflip_oneConcat, hflip_x, oneConcat, x_mul_eSum]
  · intro j hj
    rw [hφa, concat_ψ_tmul_one hj, hflip_mul, hflip_oneConcat, hflip_ψ,
      oneConcat_mul_ψ_left hj]

theorem hflip_concat_one_tmul (b : KLRAlgebra k Q ν') :
    hflip (concat Q ν ν' (1 ⊗ₜ b)) = concat Q ν ν' (1 ⊗ₜ hflip b) := by
  let φ : KLRAlgebra k Q ν' →ₗ[k] KLRAlgebra k Q (ν + ν') :=
    (concat Q ν ν').comp (TensorProduct.mk k _ _ 1)
  have hφa : ∀ b, φ b = concat Q ν ν' (1 ⊗ₜ b) := fun b => rfl
  refine hflip_comm_of_gen φ ?_ ?_ ?_ ?_ ?_ b
  · intro a b
    rw [hφa, hφa, hφa, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  · rw [hφa, concat_one_tmul_one, hflip_oneConcat]
  · intro i
    rw [hφa, concat_one_tmul_e, hflip_sum]
    simp only [hflip_e]
  · intro b
    rw [hφa, concat_one_tmul_x, hflip_mul, hflip_oneConcat, hflip_x, oneConcat, x_mul_eSum]
  · intro j hj
    rw [hφa, concat_one_tmul_ψ hj, hflip_mul, hflip_oneConcat, hflip_ψ,
      oneConcat_mul_ψ_right hj]

variable (ν ν') in
/-- `hflip ⊗ hflip` on `R(ν) ⊗ R(ν')`. -/
def tensorHflip : TensorKLR Q ν ν' →ₗ[k] TensorKLR Q ν ν' :=
  TensorProduct.map (hflipEquiv k Q ν).toLinearMap (hflipEquiv k Q ν').toLinearMap

theorem tensorHflip_tmul (a : KLRAlgebra k Q ν) (b : KLRAlgebra k Q ν') :
    tensorHflip ν ν' (a ⊗ₜ b) = hflip a ⊗ₜ hflip b := rfl

theorem tensorHflip_tensorHflip (t : TensorKLR Q ν ν') :
    tensorHflip ν ν' (tensorHflip ν ν' t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rw [tensorHflip_tmul, tensorHflip_tmul, hflip_hflip, hflip_hflip]
  | add s t hs ht => rw [map_add, map_add, hs, ht]

/-- **The horizontal flip commutes with `ι_{ν,ν'}`.** -/
theorem hflip_concat (t : TensorKLR Q ν ν') :
    hflip (concat Q ν ν' t) = concat Q ν ν' (tensorHflip ν ν' t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    have hab : (a ⊗ₜ[k] b : TensorKLR Q ν ν') = (a ⊗ₜ 1) * (1 ⊗ₜ b) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    have hba : (hflip a ⊗ₜ[k] hflip b : TensorKLR Q ν ν') = (1 ⊗ₜ hflip b) * (hflip a ⊗ₜ 1) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [tensorHflip_tmul, hba, concat_mul, ← hflip_concat_tmul_one, ← hflip_concat_one_tmul,
      ← hflip_mul, ← concat_mul, ← hab]
  | add s t hs ht => rw [map_add, hflip_add, hs, ht, map_add, map_add]

end HflipConcat

/-! ### `R(ν + ν') 1_{ν,ν'}` as a free right `R(ν) ⊗ R(ν')`-module -/

section RightBasis

variable {ν ν' : Multiset I}

/-- The canonical reduced word of a shuffle. -/
def shufWord (u : Shuffle (Seq.card_add' ν ν')) : List ℕ := canWord _ u.1

omit [DecidableEq I] in
theorem shufWord_spec (u : Shuffle (Seq.card_add' ν ν')) :
    IsReduced (Multiset.card (ν + ν')) (shufWord u) ∧
      wordProd (Multiset.card (ν + ν')) (shufWord u) = u.1 :=
  ⟨isReduced_canWord _ u.1, wordProd_canWord _ u.1⟩

/-- The shuffle `1`. -/
def shufOne : Shuffle (Seq.card_add' ν ν') := ⟨1, isShuffle_one _⟩

omit [DecidableEq I] in
theorem shufWord_one : shufWord (shufOne : Shuffle (Seq.card_add' ν ν')) = [] :=
  canWord_one _

/-- `ŵ_u^* = ψ_{σ(u)}^{rev} 1_{ν,ν'}`, the image of `ŵ_u = 1_{ν,ν'} ψ_{σ(u)}` under the
horizontal flip. -/
def hatWRev (u : Shuffle (Seq.card_add' ν ν')) : KLRAlgebra k Q (ν + ν') :=
  ψw (shufWord u).reverse * oneConcat Q ν ν'

theorem hflip_hatW_shufWord (u : Shuffle (Seq.card_add' ν ν')) :
    hflip (hatW shufWord u : KLRAlgebra k Q (ν + ν')) = hatWRev u := by
  rw [hatW, hflip_mul, hflip_ψw, hflip_oneConcat]; rfl

theorem hatWRev_mul_oneConcat (u : Shuffle (Seq.card_add' ν ν')) :
    (hatWRev u * oneConcat Q ν ν' : KLRAlgebra k Q (ν + ν')) = hatWRev u := by
  rw [hatWRev, mul_assoc, oneConcat_idem.eq]

theorem hatWRev_one : (hatWRev shufOne : KLRAlgebra k Q (ν + ν')) = oneConcat Q ν ν' := by
  rw [hatWRev, shufWord_one, List.reverse_nil, ψw_nil, one_mul]

/-- The `k`-linear map `(t_u)_u ↦ ∑_u ŵ_u^* ι(t_u)`. -/
def rightFreeMap :
    (Shuffle (Seq.card_add' ν ν') →₀ TensorKLR Q ν ν') →ₗ[k] KLRAlgebra k Q (ν + ν') :=
  Finsupp.lsum k fun u => (LinearMap.mulLeft k (hatWRev u)).comp (concat Q ν ν')

theorem rightFreeMap_apply (g : Shuffle (Seq.card_add' ν ν') →₀ TensorKLR Q ν ν') :
    rightFreeMap g = g.sum fun u t => hatWRev u * concat Q ν ν' t := by
  rw [rightFreeMap, Finsupp.lsum_apply]; rfl

theorem rightFreeMap_single (u : Shuffle (Seq.card_add' ν ν')) (t : TensorKLR Q ν ν') :
    rightFreeMap (Finsupp.single u t) = hatWRev u * concat Q ν ν' t := by
  rw [rightFreeMap_apply, Finsupp.sum_single_index (by rw [map_zero, mul_zero])]

theorem rightFreeMap_mul_oneConcat (g : Shuffle (Seq.card_add' ν ν') →₀ TensorKLR Q ν ν') :
    rightFreeMap g * oneConcat Q ν ν' = rightFreeMap g := by
  rw [rightFreeMap_apply, Finsupp.sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun u _ => by rw [mul_assoc, concat_mul_oneConcat]

/-- Right linearity: `∑_u ŵ_u^* ι(t_u t) = (∑_u ŵ_u^* ι(t_u)) ι(t)`. -/
theorem rightFreeMap_mapRange_mul (g : Shuffle (Seq.card_add' ν ν') →₀ TensorKLR Q ν ν')
    (t : TensorKLR Q ν ν') :
    rightFreeMap (g.mapRange (· * t) (zero_mul t)) = rightFreeMap g * concat Q ν ν' t := by
  rw [rightFreeMap_apply, rightFreeMap_apply, Finsupp.sum_mapRange_index
    (fun _ => by rw [map_zero, mul_zero]), Finsupp.sum, Finsupp.sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun u _ => by rw [concat_mul, mul_assoc]

theorem mapRange_tensorHflip_tensorHflip (g : Shuffle (Seq.card_add' ν ν') →₀ TensorKLR Q ν ν') :
    (g.mapRange (tensorHflip ν ν') (map_zero _)).mapRange (tensorHflip ν ν') (map_zero _) = g := by
  ext u; simp [tensorHflip_tensorHflip]

theorem hflip_freeMap (g : Shuffle (Seq.card_add' ν ν') →₀ TensorKLR Q ν ν') :
    hflip ((freeMap (Q := Q) shufWord g : oneConcatSub Q) : KLRAlgebra k Q (ν + ν')) =
      rightFreeMap (g.mapRange (tensorHflip ν ν') (map_zero _)) := by
  rw [freeMap, Finsupp.linearCombination_apply, Finsupp.sum, Submodule.coe_sum, hflip_sum,
    rightFreeMap_apply, Finsupp.sum_mapRange_index (fun _ => by rw [map_zero, mul_zero]),
    Finsupp.sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [coe_tensor_smul, hflip_mul, hflip_concat]
  show hflip (hatW shufWord u) * _ = _
  rw [hflip_hatW_shufWord]

section Bijective

variable [IsDomain k] {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)

include hPQ hP in
theorem freeMap_shufWord_bijective :
    Function.Bijective (freeMap (Q := Q) (ν := ν) (ν' := ν') shufWord) :=
  freeMap_bijective hPQ hP (canWord _) (canWord _) shufWord
    (fun a => ⟨isReduced_canWord _ a, wordProd_canWord _ a⟩)
    (fun b => ⟨isReduced_canWord _ b, wordProd_canWord _ b⟩) shufWord_spec

omit [IsDomain k] in
theorem rightFreeMap_eq_hflip_freeMap (g : Shuffle (Seq.card_add' ν ν') →₀ TensorKLR Q ν ν') :
    rightFreeMap g = hflip ((freeMap (Q := Q) shufWord
      (g.mapRange (tensorHflip ν ν') (map_zero _)) : oneConcatSub Q) :
        KLRAlgebra k Q (ν + ν')) := by
  rw [hflip_freeMap, mapRange_tensorHflip_tensorHflip]

include hPQ hP in
theorem rightFreeMap_injective :
    Function.Injective (rightFreeMap (Q := Q) (ν := ν) (ν' := ν')) := by
  intro g g' h
  rw [rightFreeMap_eq_hflip_freeMap, rightFreeMap_eq_hflip_freeMap] at h
  have h2 := (freeMap_shufWord_bijective hPQ hP).1 (Subtype.ext (hflip_injective h))
  rw [← mapRange_tensorHflip_tensorHflip g, h2, mapRange_tensorHflip_tensorHflip]

include hPQ hP in
theorem exists_rightFreeMap_eq {r : KLRAlgebra k Q (ν + ν')} (hr : r * oneConcat Q ν ν' = r) :
    ∃ g, rightFreeMap g = r := by
  have hmem : hflip r ∈ oneConcatSub (ν := ν) (ν' := ν') Q := by
    rw [mem_oneConcatSub, ← hflip_oneConcat, ← hflip_mul, hr]
  obtain ⟨g, hg⟩ := (freeMap_shufWord_bijective (ν := ν) (ν' := ν') hPQ hP).2 ⟨hflip r, hmem⟩
  refine ⟨g.mapRange (tensorHflip ν ν') (map_zero _), ?_⟩
  rw [← hflip_freeMap, hg, hflip_hflip]

/-- `ŵ_u^* ∈ R(ν + ν') 1_{ν,ν'}`. -/
def hatWRevSub (u : Shuffle (Seq.card_add' ν ν')) : IndBimod Q ν ν' :=
  ⟨hatWRev u, hatWRev_mul_oneConcat u⟩

omit [IsDomain k] in
theorem coe_hatWRevSub (u : Shuffle (Seq.card_add' ν ν')) :
    ((hatWRevSub u : IndBimod Q ν ν') : KLRAlgebra k Q (ν + ν')) = hatWRev u := rfl

/-- `rightFreeMap` as a `k`-linear map to `R(ν + ν') 1_{ν,ν'}`. -/
def rightFreeLin :
    (Shuffle (Seq.card_add' ν ν') →₀ TensorKLR Q ν ν') →ₗ[k] IndBimod Q ν ν' where
  toFun g := ⟨rightFreeMap g, rightFreeMap_mul_oneConcat g⟩
  map_add' g g' := Subtype.ext (map_add _ g g')
  map_smul' c g := Subtype.ext (map_smul _ c g)

variable (ν ν') in
/-- **Proposition 2.16, right-module form**: `R(ν + ν') 1_{ν,ν'} ≅ ⊕_u R(ν) ⊗ R(ν')`,
`(t_u)_u ↦ ∑_u ŵ_u^* ι(t_u)`. -/
def rightFreeEquiv :
    (Shuffle (Seq.card_add' ν ν') →₀ TensorKLR Q ν ν') ≃ₗ[k] IndBimod Q ν ν' :=
  LinearEquiv.ofBijective rightFreeLin
    ⟨fun g g' h => rightFreeMap_injective hPQ hP (congrArg Subtype.val h), fun r => by
      obtain ⟨g, hg⟩ := exists_rightFreeMap_eq hPQ hP (Graded.mem_leftIdeal.1 r.2)
      exact ⟨g, Subtype.ext hg⟩⟩

theorem coe_rightFreeEquiv (g : Shuffle (Seq.card_add' ν ν') →₀ TensorKLR Q ν ν') :
    ((rightFreeEquiv ν ν' hPQ hP g : IndBimod Q ν ν') : KLRAlgebra k Q (ν + ν')) =
      rightFreeMap g := rfl

theorem rightFreeEquiv_single_one (u : Shuffle (Seq.card_add' ν ν')) :
    rightFreeEquiv ν ν' hPQ hP (Finsupp.single u 1) = hatWRevSub u := by
  apply Subtype.ext
  rw [coe_rightFreeEquiv, rightFreeMap_single, concat_one, hatWRev_mul_oneConcat]; rfl

theorem rightFreeEquiv_symm_op_smul (r : IndBimod Q ν ν') (t : TensorKLR Q ν ν') :
    (rightFreeEquiv ν ν' hPQ hP).symm (op t • r) =
      ((rightFreeEquiv ν ν' hPQ hP).symm r).mapRange (· * t) (zero_mul t) := by
  apply (rightFreeEquiv ν ν' hPQ hP).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [coe_rightFreeEquiv, rightFreeMap_mapRange_mul, ← coe_rightFreeEquiv,
    LinearEquiv.apply_symm_apply, coe_op_smul, unop_op]

end Bijective

end RightBasis

/-! ### The idempotents `1_t ∈ R(ν) ⊗ R(ν')` -/

section ConcatIdem

variable {ν ν' : Multiset I}

/-- For `t ∈ Seq(ν + ν')`, the idempotent `1_t = ∑_{ij = t} 1_i ⊗ 1_j` of `R(ν) ⊗ R(ν')`: it is
`1_i ⊗ 1_j` if `t = ij` (`concatIdem_append`) and `0` if `t` is not a concatenation. -/
def concatIdem (t : Seq (ν + ν')) : TensorKLR Q ν ν' :=
  ∑ p ∈ Finset.univ.filter (fun p : Seq ν × Seq ν' => p.1.append p.2 = t), e p.1 ⊗ₜ e p.2

theorem concatIdem_append (i : Seq ν) (j : Seq ν') :
    (concatIdem (i.append j) : TensorKLR Q ν ν') = e i ⊗ₜ e j := by
  have : Finset.univ.filter (fun p : Seq ν × Seq ν' => p.1.append p.2 = i.append j) =
      {(i, j)} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      Seq.append_inj, Prod.ext_iff]
  rw [concatIdem, this, Finset.sum_singleton]

theorem concatIdem_of_not_mem {t : Seq (ν + ν')} (ht : t ∉ concatSet ν ν') :
    (concatIdem t : TensorKLR Q ν ν') = 0 := by
  have : Finset.univ.filter (fun p : Seq ν × Seq ν' => p.1.append p.2 = t) = ∅ := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.not_mem_empty, iff_false]
    intro h
    exact ht (mem_concatSet.2 ⟨p.1, p.2, h⟩)
  rw [concatIdem, this, Finset.sum_empty]

theorem concatIdem_idem (t : Seq (ν + ν')) :
    IsIdempotentElem (concatIdem t : TensorKLR Q ν ν') := by
  by_cases ht : t ∈ concatSet ν ν'
  · obtain ⟨i, j, rfl⟩ := mem_concatSet.1 ht
    rw [IsIdempotentElem, concatIdem_append, Algebra.TensorProduct.tmul_mul_tmul, e_mul_self,
      e_mul_self]
  · rw [concatIdem_of_not_mem ht, IsIdempotentElem, mul_zero]

/-- `ι(1_t) = 1_t 1_{ν,ν'}`. -/
theorem concat_concatIdem (t : Seq (ν + ν')) :
    concat Q ν ν' (concatIdem t) = e t * oneConcat Q ν ν' := by
  rw [concatIdem, map_sum, oneConcat_eq, Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [concat_e_tmul_e, e_mul_e]
  split_ifs with h1 h2 h2
  · rw [h1]
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · rfl

end ConcatIdem

/-! ### The decomposition of `Ind N` -/

section IndDecomp

variable {ν ν' : Multiset I} [IsDomain k] {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)
  (N : Type*) [AddCommGroup N] [Module k N] [Module (TensorKLR Q ν ν') N]
  [IsScalarTower k (TensorKLR Q ν ν') N]

/-- The `k`-bilinear map `(r, n) ↦ (t_u(r) n)_u`, `r = ∑_u ŵ_u^* ι(t_u(r))`. -/
def indDecompBil : IndBimod Q ν ν' →ₗ[k] N →ₗ[k] (Shuffle (Seq.card_add' ν ν') → N) :=
  LinearMap.mk₂ k (fun r n u => ((rightFreeEquiv ν ν' hPQ hP).symm r) u • n)
    (fun r r' n => by funext u; simp [add_smul])
    (fun c r n => by funext u; simp [smul_assoc])
    (fun r n n' => by funext u; simp [smul_add])
    (fun c r n => by funext u; simp [smul_comm c])

theorem indDecompBil_apply (r : IndBimod Q ν ν') (n : N) (u : Shuffle (Seq.card_add' ν ν')) :
    indDecompBil hPQ hP N r n u = ((rightFreeEquiv ν ν' hPQ hP).symm r) u • n := rfl

theorem indDecompBil_balanced (r : IndBimod Q ν ν') (t : TensorKLR Q ν ν') (n : N) :
    indDecompBil hPQ hP N (op t • r) n = indDecompBil hPQ hP N r (t • n) := by
  funext u
  rw [indDecompBil_apply, indDecompBil_apply, rightFreeEquiv_symm_op_smul,
    Finsupp.mapRange_apply, mul_smul]

/-- The inverse map `(n_u)_u ↦ ∑_u ŵ_u^* ⊗ n_u`. -/
def indDecompInv : (Shuffle (Seq.card_add' ν ν') → N) →ₗ[k] Ind Q ν ν' N :=
  ∑ u, (BalancedTensor.mkBil k (KLRAlgebra k Q (ν + ν')) (TensorKLR Q ν ν') (IndBimod Q ν ν') N
    (hatWRevSub u)).comp (LinearMap.proj u)

omit [IsDomain k] [IsScalarTower k (TensorKLR Q ν ν') N] in
theorem indDecompInv_apply (g : Shuffle (Seq.card_add' ν ν') → N) :
    indDecompInv N g = ∑ u, (BalancedTensor.tmul (hatWRevSub u) (g u) : Ind Q ν ν' N) := by
  simp [indDecompInv]

/-- **The decomposition `Ind N ≅ ⊕_u N`** (as vector spaces), `ŵ_u^* ⊗ n ↦ (n at u)`. -/
def indDecomp : Ind Q ν ν' N ≃ₗ[k] (Shuffle (Seq.card_add' ν ν') → N) :=
  LinearEquiv.ofLinear (BalancedTensor.lift (indDecompBil hPQ hP N)
      (indDecompBil_balanced hPQ hP N)) (indDecompInv N)
    (by
      apply LinearMap.ext; intro g; funext u'
      rw [LinearMap.comp_apply, indDecompInv_apply, map_sum, Finset.sum_apply,
        Finset.sum_eq_single u']
      · rw [BalancedTensor.lift_tmul, indDecompBil_apply, ← rightFreeEquiv_single_one hPQ hP,
          LinearEquiv.symm_apply_apply, Finsupp.single_eq_same, one_smul, LinearMap.id_apply]
      · intro u _ hu
        rw [BalancedTensor.lift_tmul, indDecompBil_apply, ← rightFreeEquiv_single_one hPQ hP,
          LinearEquiv.symm_apply_apply, Finsupp.single_eq_of_ne hu, zero_smul]
      · simp)
    (by
      apply BalancedTensor.ext
      intro r n
      rw [LinearMap.comp_apply, BalancedTensor.lift_tmul, indDecompInv_apply,
        LinearMap.id_apply]
      simp only [indDecompBil_apply, ← BalancedTensor.op_smul_tmul]
      have hsum : ∀ m : Shuffle (Seq.card_add' ν ν') → IndBimod Q ν ν',
          (∑ u, BalancedTensor.tmul (m u) n : Ind Q ν ν' N) =
            BalancedTensor.tmul (∑ u, m u) n := by
        intro m
        have := map_sum ((BalancedTensor.mkBil k (KLRAlgebra k Q (ν + ν')) (TensorKLR Q ν ν')
          (IndBimod Q ν ν') N).flip n) m Finset.univ
        simp only [LinearMap.flip_apply, BalancedTensor.mkBil_apply] at this
        exact this.symm
      rw [hsum]
      congr 1
      apply Subtype.ext
      rw [Submodule.coe_sum]
      conv_rhs => rw [← (rightFreeEquiv ν ν' hPQ hP).apply_symm_apply r, coe_rightFreeEquiv,
        rightFreeMap_apply, Finsupp.sum_fintype _ _ (fun _ => by rw [map_zero, mul_zero])]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [coe_op_smul, unop_op, coe_hatWRevSub])

theorem indDecomp_tmul (r : IndBimod Q ν ν') (n : N) (u : Shuffle (Seq.card_add' ν ν')) :
    indDecomp hPQ hP N (BalancedTensor.tmul r n) u =
      ((rightFreeEquiv ν ν' hPQ hP).symm r) u • n := rfl

theorem indDecomp_symm_apply (g : Shuffle (Seq.card_add' ν ν') → N) :
    (indDecomp hPQ hP N).symm g =
      ∑ u, (BalancedTensor.tmul (hatWRevSub u) (g u) : Ind Q ν ν' N) :=
  indDecompInv_apply N g

theorem indDecomp_tmul_hatWRevSub (u : Shuffle (Seq.card_add' ν ν')) (n : N) :
    indDecomp hPQ hP N (BalancedTensor.tmul (hatWRevSub u) n) = Pi.single u n := by
  funext u'
  rw [indDecomp_tmul, ← rightFreeEquiv_single_one hPQ hP, LinearEquiv.symm_apply_apply,
    Finsupp.single_apply, Pi.single_apply]
  by_cases h : u' = u
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h, zero_smul]

/-- The element `1_{ν,ν'} ∈ R(ν + ν') 1_{ν,ν'}`. -/
def oneConcatSubBimod : IndBimod Q ν ν' := ⟨oneConcat Q ν ν', oneConcat_idem.eq⟩

omit [IsDomain k] in
theorem oneConcatSubBimod_eq : (oneConcatSubBimod : IndBimod Q ν ν') = hatWRevSub shufOne :=
  Subtype.ext hatWRev_one.symm

/-- The unit `n ↦ 1_{ν,ν'} ⊗ n` corresponds to the summand of the shuffle `u = 1`. -/
theorem indDecomp_tmul_oneConcat (n : N) :
    indDecomp (ν := ν) (ν' := ν') hPQ hP N (BalancedTensor.tmul oneConcatSubBimod n) =
      Pi.single shufOne n := by
  rw [oneConcatSubBimod_eq, indDecomp_tmul_hatWRevSub]

omit [IsDomain k] in
theorem e_mul_hatWRev (s : Seq (ν + ν')) (u : Shuffle (Seq.card_add' ν ν')) :
    (e s * hatWRev u : KLRAlgebra k Q (ν + ν')) =
      hatWRev u * concat Q ν ν' (concatIdem (u.1 • s)) := by
  rw [hatWRev, ← mul_assoc, e_mul_ψw, wordProd_reverse, (shufWord_spec u).2, inv_inv,
    mul_assoc, ← concat_concatIdem, mul_assoc, oneConcat_mul_concat]

omit [IsDomain k] [IsScalarTower k (TensorKLR Q ν ν') N] in
theorem e_smul_tmul_hatWRevSub (s : Seq (ν + ν')) (u : Shuffle (Seq.card_add' ν ν')) (n : N) :
    (e s : KLRAlgebra k Q (ν + ν')) • (BalancedTensor.tmul (hatWRevSub u) n : Ind Q ν ν' N) =
      BalancedTensor.tmul (hatWRevSub u) (concatIdem (Q := Q) (u.1 • s) • n) := by
  rw [BalancedTensor.smul_tmul', ← BalancedTensor.op_smul_tmul]
  congr 1
  apply Subtype.ext
  rw [coe_op_smul, unop_op, Submodule.coe_smul, smul_eq_mul, coe_hatWRevSub, e_mul_hatWRev]

/-- **`1_s` acts on the summand `u` through `1_{u s}`.** -/
theorem indDecomp_e_smul (s : Seq (ν + ν')) (y : Ind Q ν ν' N)
    (u : Shuffle (Seq.card_add' ν ν')) :
    indDecomp hPQ hP N ((e s : KLRAlgebra k Q (ν + ν')) • y) u =
      concatIdem (Q := Q) (u.1 • s) • indDecomp hPQ hP N y u := by
  set g := indDecomp hPQ hP N y
  have hy : y = (indDecomp hPQ hP N).symm g := ((indDecomp hPQ hP N).symm_apply_apply y).symm
  have : (e s : KLRAlgebra k Q (ν + ν')) • y =
      (indDecomp hPQ hP N).symm (fun u => concatIdem (Q := Q) (u.1 • s) • g u) := by
    rw [hy, indDecomp_symm_apply, indDecomp_symm_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl fun u _ => e_smul_tmul_hatWRevSub N s u (g u)
  rw [this, LinearEquiv.apply_symm_apply]

/-- `1_s (Ind N) ≅ ⊕_u 1_{u s} N`. -/
def fixSubIndEquiv (s : Seq (ν + ν')) :
    fixSub k (Ind Q ν ν' N) (e s : KLRAlgebra k Q (ν + ν')) ≃ₗ[k]
      ((u : Shuffle (Seq.card_add' ν ν')) → fixSub k N (concatIdem (Q := Q) (u.1 • s))) where
  toFun y u := ⟨indDecomp (ν := ν) (ν' := ν') hPQ hP N (y : Ind Q ν ν' N) u, by
    rw [mem_fixSub, ← indDecomp_e_smul, mem_fixSub.1 y.2]⟩
  invFun g := ⟨(indDecomp (ν := ν) (ν' := ν') hPQ hP N).symm fun u => (g u : N), by
    rw [mem_fixSub]
    apply (indDecomp (ν := ν) (ν' := ν') hPQ hP N).injective
    funext u
    rw [indDecomp_e_smul, LinearEquiv.apply_symm_apply]
    exact (g u).2⟩
  map_add' y y' := by
    funext u; apply Subtype.ext
    simp only [Submodule.coe_add, map_add, Pi.add_apply]
  map_smul' c y := by
    funext u; apply Subtype.ext
    simp only [Submodule.coe_smul_of_tower, map_smul, Pi.smul_apply, RingHom.id_apply]
  left_inv y := by
    apply Subtype.ext
    exact (indDecomp (ν := ν) (ν' := ν') hPQ hP N).symm_apply_apply (y : Ind Q ν ν' N)
  right_inv g := by
    funext u; apply Subtype.ext
    show indDecomp (ν := ν) (ν' := ν') hPQ hP N
      ((indDecomp (ν := ν) (ν' := ν') hPQ hP N).symm fun u => (g u : N)) u = g u
    rw [LinearEquiv.apply_symm_apply]

theorem fixSubIndEquiv_apply (s : Seq (ν + ν'))
    (y : fixSub k (Ind Q ν ν' N) (e s : KLRAlgebra k Q (ν + ν')))
    (u : Shuffle (Seq.card_add' ν ν')) :
    (fixSubIndEquiv hPQ hP N s y u : N) = indDecomp hPQ hP N (y : Ind Q ν ν' N) u := rfl

include hPQ hP in
/-- **Support form of the Shuffle Lemma**: if `1_s Ind N ≠ 0` then `u s = ij` for a shuffle `u`
and sequences `i`, `j` with `(1_i ⊗ 1_j) N ≠ 0`. -/
theorem exists_shuffle_of_fixSub_ind_ne_bot {s : Seq (ν + ν')}
    (hs : fixSub k (Ind Q ν ν' N) (e s : KLRAlgebra k Q (ν + ν')) ≠ ⊥) :
    ∃ (u : Shuffle (Seq.card_add' ν ν')) (i : Seq ν) (j : Seq ν'),
      u.1 • s = i.append j ∧
        fixSub k N (e i ⊗ₜ[k] e j : TensorKLR Q ν ν') ≠ ⊥ := by
  by_contra hcon
  push_neg at hcon
  apply hs
  rw [eq_bot_iff]
  intro y hy
  have hsub : ∀ (u : Shuffle (Seq.card_add' ν ν'))
      (v : fixSub k N (concatIdem (Q := Q) (ν := ν) (ν' := ν') (u.1 • s))), v = 0 := by
    rintro u ⟨w, hv⟩
    rw [mem_fixSub] at hv
    apply Subtype.ext
    show w = 0
    by_cases hmem : u.1 • s ∈ concatSet ν ν'
    · obtain ⟨i, j, hij⟩ := mem_concatSet.1 hmem
      rw [← hij, concatIdem_append] at hv
      have hv' : w ∈ fixSub k N (e i ⊗ₜ[k] e j : TensorKLR Q ν ν') := hv
      rw [hcon u i j hij.symm] at hv'
      exact (Submodule.mem_bot k).1 hv'
    · rw [concatIdem_of_not_mem hmem, zero_smul] at hv
      exact hv.symm
  have h0 : fixSubIndEquiv hPQ hP N s ⟨y, hy⟩ = 0 := funext fun u => hsub u _
  have := congrArg Subtype.val ((fixSubIndEquiv hPQ hP N s).map_eq_zero_iff.1 h0)
  rw [Submodule.mem_bot]
  exact this

end IndDecomp

/-! ### Lemma 2.20 -/

section Shuffle

variable {K : Type*} [Field K] {Q : I → I → MvPolynomial (Fin 2) K} {ν ν' : Multiset I}
  {P : I → I → MvPolynomial (Fin 2) K}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)
  (N : Type*) [AddCommGroup N] [Module K N] [Module (TensorKLR Q ν ν') N]
  [IsScalarTower K (TensorKLR Q ν ν') N]

include hPQ hP in
/-- Induced modules of finite-dimensional modules are finite-dimensional. -/
theorem finiteDimensional_ind [FiniteDimensional K N] : FiniteDimensional K (Ind Q ν ν' N) :=
  LinearEquiv.finiteDimensional (indDecomp hPQ hP N).symm

include hPQ hP in
/-- **KL I, Lemma 2.20 (Shuffle Lemma), ungraded**: `dim 1_s Ind N = ∑_u dim 1_{u s} N`, the sum
over the shuffles `u`; `1_{u s} = 1_i ⊗ 1_j` if `u s = ij` (`concatIdem_append`) and `0`
otherwise (`concatIdem_of_not_mem`). -/
theorem finrank_fixSub_ind [FiniteDimensional K N] (s : Seq (ν + ν')) :
    Module.finrank K (fixSub K (Ind Q ν ν' N) (e s : KLRAlgebra K Q (ν + ν'))) =
      ∑ u : Shuffle (Seq.card_add' ν ν'),
        Module.finrank K (fixSub K N (concatIdem (Q := Q) (u.1 • s))) := by
  rw [(fixSubIndEquiv hPQ hP N s).finrank_eq, Module.finrank_pi_fintype]

end Shuffle


/-! ### Idempotents on external tensor products -/

section ExtTensorFix

variable {K : Type*} [Field K] {A B : Type*} [Ring A] [Algebra K A] [Ring B] [Algebra K B]
  {M₁ M₂ : Type*} [AddCommGroup M₁] [Module K M₁] [Module A M₁] [IsScalarTower K A M₁]
  [AddCommGroup M₂] [Module K M₂] [Module B M₂] [IsScalarTower K B M₂]

omit [DecidableEq I] in
/-- `(a ⊗ b)(M₁ ⊠ M₂) ≅ a M₁ ⊗ b M₂` for idempotents `a`, `b`: dimensions multiply. -/
theorem finrank_fixSub_extTensor {a : A} {b : B} (ha : IsIdempotentElem a)
    (hb : IsIdempotentElem b) [FiniteDimensional K M₁] [FiniteDimensional K M₂] :
    Module.finrank K (fixSub K (ExtTensor K M₁ M₂) (a ⊗ₜ[K] b)) =
      Module.finrank K (fixSub K M₁ a) * Module.finrank K (fixSub K M₂ b) := by
  let ι : fixSub K M₁ a ⊗[K] fixSub K M₂ b →ₗ[K] ExtTensor K M₁ M₂ :=
    ExtTensor.equivTensor.symm.toLinearMap ∘ₗ
      TensorProduct.map (fixSub K M₁ a).subtype (fixSub K M₂ b).subtype
  have hι : Function.Injective ι :=
    ExtTensor.equivTensor.symm.injective.comp
      (TensorProduct.map_injective_of_flat_flat _ _ (Submodule.injective_subtype _)
        (Submodule.injective_subtype _))
  have hrange : LinearMap.range ι = fixSub K (ExtTensor K M₁ M₂) (a ⊗ₜ[K] b) := by
    apply le_antisymm
    · rintro _ ⟨w, rfl⟩
      rw [mem_fixSub]
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul p q =>
        show (a ⊗ₜ[K] b) • ExtTensor.tmul (p : M₁) (q : M₂) = ExtTensor.tmul (p : M₁) (q : M₂)
        rw [ExtTensor.smul_tmul, mem_fixSub.1 p.2, mem_fixSub.1 q.2]
      | add w w' hw hw' => rw [map_add, smul_add, hw, hw']
    · intro z hz
      rw [← mem_fixSub.1 hz]
      clear hz
      induction z using ExtTensor.induction_on with
      | zero => rw [smul_zero]; exact zero_mem _
      | tmul p q =>
        rw [ExtTensor.smul_tmul]
        exact ⟨⟨a • p, smul_mem_fixSub ha p⟩ ⊗ₜ ⟨b • q, smul_mem_fixSub hb q⟩, rfl⟩
      | add z z' hz hz' => rw [smul_add]; exact add_mem hz hz'
  rw [← hrange, LinearMap.finrank_range_of_inj hι, Module.finrank_tensorProduct]

end ExtTensorFix

/-! ### Lemma 2.20 for external tensor products -/

section ShuffleExt

variable {K : Type*} [Field K] {Q : I → I → MvPolynomial (Fin 2) K} {ν ν' : Multiset I}
  {P : I → I → MvPolynomial (Fin 2) K}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)
  (N₁ : Type*) [AddCommGroup N₁] [Module K N₁] [Module (KLRAlgebra K Q ν) N₁]
  [IsScalarTower K (KLRAlgebra K Q ν) N₁] [FiniteDimensional K N₁]
  (N₂ : Type*) [AddCommGroup N₂] [Module K N₂] [Module (KLRAlgebra K Q ν') N₂]
  [IsScalarTower K (KLRAlgebra K Q ν') N₂] [FiniteDimensional K N₂]

include hPQ hP in
/-- **KL I, Lemma 2.20 (Shuffle Lemma), ungraded**: for `s ∈ Seq(ν + ν')`,
`dim 1_s Ind (N₁ ⊠ N₂) = ∑ dim 1_i N₁ · dim 1_j N₂`, the sum over the ways `u` of writing `s` as a
shuffle of `i ∈ Seq ν` and `j ∈ Seq ν'` (`ShuffleOf ν ν' s`, `(i, j) = u.split`). In terms of
characters at `q = 1`: `ch(Ind (N₁ ⊠ N₂)) = ch(N₁) ⧢ ch(N₂)`. -/
theorem shuffle_lemma_finrank (s : Seq (ν + ν')) :
    Module.finrank K (fixSub K (Ind Q ν ν' (ExtTensor K N₁ N₂)) (e s : KLRAlgebra K Q (ν + ν'))) =
      ∑ u : ShuffleOf ν ν' s, Module.finrank K (fixSub K N₁ (e u.split.1 : KLRAlgebra K Q ν)) *
        Module.finrank K (fixSub K N₂ (e u.split.2 : KLRAlgebra K Q ν')) := by
  classical
  haveI : FiniteDimensional K (ExtTensor K N₁ N₂) :=
    inferInstanceAs (FiniteDimensional K (N₁ ⊗[K] N₂))
  rw [finrank_fixSub_ind hPQ hP,
    ← Fintype.sum_subtype_add_sum_subtype (fun u : Shuffle (Seq.card_add' ν ν') =>
      u.1 • s ∈ concatSet ν ν')]
  have hzero : ∑ u : {u : Shuffle (Seq.card_add' ν ν') // ¬ u.1 • s ∈ concatSet ν ν'},
      Module.finrank K (fixSub K (ExtTensor K N₁ N₂) (concatIdem (Q := Q) (u.1.1 • s))) = 0 := by
    refine Finset.sum_eq_zero fun u _ => ?_
    rw [concatIdem_of_not_mem u.2, Submodule.finrank_eq_zero, eq_bot_iff]
    intro v hv
    rw [mem_fixSub, zero_smul] at hv
    rw [← hv]; exact zero_mem _
  rw [hzero, add_zero]
  refine Finset.sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _)) fun u _ => ?_
  rw [← ShuffleOf.split_spec u, concatIdem_append,
    finrank_fixSub_extTensor (e_mul_self _) (e_mul_self _)]

end ShuffleExt

end KLRAlgebra

end Categorification.KLR

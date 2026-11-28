/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.MackeyIndAssoc
import Categorification.KLR.Crystal.IndDecomp

/-!
# Loadings of the crossing strands in a Mackey layer

Khovanov–Lauda I (arXiv:0803.4121v2), §2.6, Propositions 2.16 and 2.18, used for Webster,
arXiv:1309.3796v3, §7.3, proof of Lemma 7.19 (trace half, the leading layer of the
head-strand filtration).

By Proposition 2.16 in right-module form, every `r ∈ R(ν + ν') 1_{ν,ν'}` is
`r = ∑_u ŵ_u^* ι(t_u)` over the shuffles `u`, and `1_s ŵ_u^* = ŵ_u^* ι(1_{u s})`
(`e_mul_hatWRevOf`). So if, for every shuffle `u`, every way of writing `u • s = i j` has its
second factor `j` in a set `T` of loadings of `ν'`, then
`1_s r = ∑_u ŵ_u^* ι((1 ⊗ 1_T) t'_u)` (`e_mul_eq_sum_tail`): the idempotent `1_T` of the
loadings of the strands of the second block appears to the left of the parabolic part.

In a Mackey layer `MackeyTop_λ ⊗_{R'} (MackeyBot_λ ⊗_{R''} N)` of an induced module
(`MackeyLeftInd`), the parabolic part of the top moves across the tensor product. Hence
`(1_s ⊗ 1) w = 0` for every `w` as soon as the element `(1 ⊗ 1_T) ⊗ 1` of
`R' = R(ν - λ) ⊗ R(λ) ⊗ R(γ) ⊗ R(δ)` annihilates `MackeyBot_λ ⊗_{R''} N`
(`e_tmul_one_smul_mackeyLeftInd_eq_zero`). The annihilation holds when each `1 ⊗ 1_{j v}`,
`j ∈ T`, kills `N` (`quadAlg_tail_smul_eq_zero`): the strands of `λ` are the first strands of
the second bottom block.

Symmetric `Q` (`KLRSymm Q`), any commutative ring `k`.

## Main results

* `KLRAlgebra.e_mul_eq_sum_tail`, `KLRAlgebra.quadAlg_tail_smul_eq_zero`,
  `KLRAlgebra.e_tmul_one_smul_mackeyLeftInd_eq_zero`.
-/

noncomputable section

namespace Categorification.KLR

open Equiv TypeA MulOpposite
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k}

namespace KLRAlgebra

section Tail

variable {ν ν' : Multiset I}

theorem tmul_eSum_mul_concatIdem (s : Seq (ν + ν')) (T : Finset (Seq ν'))
    (hT : ∀ (i : Seq ν) (j : Seq ν'), i.append j = s → j ∈ T) :
    ((1 : KLRAlgebra k Q ν) ⊗ₜ eSum Q T) * (concatIdem s : TensorKLR Q ν ν') = concatIdem s := by
  rw [concatIdem, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, eSum_mul_e]
  split_ifs with h
  · rfl
  · exact absurd (hT p.1 p.2 (Finset.mem_filter.1 hp).2) h

variable (hsym : KLRSymm Q) {σ : Shuffle (Seq.card_add' ν ν') → List ℕ}
  (hσ : ∀ u, IsReduced (Multiset.card (ν + ν')) (σ u) ∧
    wordProd (Multiset.card (ν + ν')) (σ u) = u.1)

include hsym hσ in
/-- **The loadings of the second block on `1_s R(ν + ν') 1_{ν,ν'}`**: if every shuffle `u`
writes `u • s` only as `i j` with `j ∈ T`, then `1_s r = ∑_u ŵ_u^* ι((1 ⊗ 1_T) t_u)`. -/
theorem e_mul_eq_sum_tail (s : Seq (ν + ν')) (T : Finset (Seq ν'))
    (hT : ∀ (u : Shuffle (Seq.card_add' ν ν')) (i : Seq ν) (j : Seq ν'),
      i.append j = u.1 • s → j ∈ T)
    {r : KLRAlgebra k Q (ν + ν')} (hr : r * oneConcat Q ν ν' = r) :
    ∃ (F : Finset (Shuffle (Seq.card_add' ν ν'))) (t : Shuffle (Seq.card_add' ν ν') →
      TensorKLR Q ν ν'), e s * r =
        ∑ u ∈ F, hatWRevOf σ u * concat Q ν ν' (((1 : KLRAlgebra k Q ν) ⊗ₜ eSum Q T) * t u) := by
  obtain ⟨g, rfl⟩ := exists_rightFreeMapOf_eq hsym hσ hr
  refine ⟨g.support, fun u => concatIdem (u.1 • s) * g u, ?_⟩
  rw [rightFreeMapOf_apply, Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← mul_assoc, e_mul_hatWRevOf σ hσ, mul_assoc, ← concat_mul, ← mul_assoc,
    tmul_eSum_mul_concatIdem _ T (hT u)]

include hsym hσ in
/-- `e_mul_eq_sum_tail` for a weight `ν'' = ν + ν'` given up to equality. -/
theorem e_mul_eq_sum_tail_cast {ν'' : Multiset I} (h : ν + ν' = ν'') (s : Seq ν'')
    (T : Finset (Seq ν'))
    (hT : ∀ (u : Shuffle (Seq.card_add' ν ν')) (i : Seq ν) (j : Seq ν'),
      i.append j = u.1 • seqCast h.symm s → j ∈ T)
    {r : KLRAlgebra k Q ν''} (hr : r * castAlg Q h (oneConcat Q ν ν') = r) :
    ∃ (F : Finset (Shuffle (Seq.card_add' ν ν'))) (t : Shuffle (Seq.card_add' ν ν') →
      TensorKLR Q ν ν'), e s * r =
        ∑ u ∈ F, castAlg Q h (hatWRevOf σ u) *
          castAlg Q h (concat Q ν ν' (((1 : KLRAlgebra k Q ν) ⊗ₜ eSum Q T) * t u)) := by
  subst h
  exact e_mul_eq_sum_tail hsym hσ s T hT hr

end Tail

section Positions

variable {ν ν' : Multiset I}

omit [DecidableEq I] in
/-- The tail `j` of `u • s = i j` reads `s` at the positions of the second block under `u`. -/
theorem tail_val_of_append_eq {u : Perm (Fin (Multiset.card (ν + ν')))} {s : Seq (ν + ν')}
    {i : Seq ν} {j : Seq ν'} (h : i.append j = u • s) (b : Fin (Multiset.card ν')) :
    j.1 b = s.1 (u⁻¹ (Seq.posR ν b)) := by
  have := congrArg (fun t : Seq (ν + ν') => t.1 (Seq.posR ν b)) h
  simpa using this

omit [DecidableEq I] in
/-- The positions of the second block under a shuffle increase by at least one at each step. -/
theorem shuffle_tail_add_le (u : Shuffle (Seq.card_add' ν ν')) (y : Fin (Multiset.card ν'))
    (d : ℕ) (hd : y.val + d < Multiset.card ν') :
    (u.1⁻¹ (Seq.posR ν y)).val + d ≤ (u.1⁻¹ (Seq.posR ν ⟨y.val + d, hd⟩)).val := by
  induction d with
  | zero => exact le_of_eq rfl
  | succ d ih =>
    have h1 := ih (by omega)
    have h2 : u.1⁻¹ (Seq.posR ν ⟨y.val + d, by omega⟩) <
        u.1⁻¹ (Seq.posR ν ⟨y.val + (d + 1), hd⟩) :=
      u.2.2 (show (⟨y.val + d, by omega⟩ : Fin (Multiset.card ν')) < ⟨y.val + (d + 1), hd⟩ from
        Fin.mk_lt_mk.2 (by omega))
    rw [Fin.lt_def] at h2
    omega

omit [DecidableEq I] in
/-- The first position of the second block under a shuffle is at most `|ν|`. -/
theorem shuffle_first_tail_le (u : Shuffle (Seq.card_add' ν ν')) (hc : 0 < Multiset.card ν') :
    (u.1⁻¹ (Seq.posR ν ⟨0, hc⟩)).val ≤ Multiset.card ν := by
  have h1 := shuffle_tail_add_le u ⟨0, hc⟩ (Multiset.card ν' - 1) (by simp only; omega)
  have h2 := (u.1⁻¹ (Seq.posR ν ⟨(⟨0, hc⟩ : Fin (Multiset.card ν')).val +
    (Multiset.card ν' - 1), by simp only; omega⟩)).2
  have h3 := Seq.card_add' ν ν'
  omega

omit [DecidableEq I] in
/-- If the second block starts at `|ν|` under a shuffle, it is the last block. -/
theorem shuffle_tail_eq_of_first (u : Shuffle (Seq.card_add' ν ν')) (hc : 0 < Multiset.card ν')
    (h0 : Multiset.card ν ≤ (u.1⁻¹ (Seq.posR ν ⟨0, hc⟩)).val) (y : Fin (Multiset.card ν')) :
    u.1⁻¹ (Seq.posR ν y) = Seq.posR ν y := by
  apply Fin.ext
  have h1 := shuffle_tail_add_le u ⟨0, hc⟩ y.val (by simp only; omega)
  have h2 := shuffle_tail_add_le u y (Multiset.card ν' - 1 - y.val) (by omega)
  have h3 := lt_of_lt_of_eq
    (u.1⁻¹ (Seq.posR ν ⟨y.val + (Multiset.card ν' - 1 - y.val), by omega⟩)).2
    (Seq.card_add' ν ν').symm
  simp only [zero_add, Fin.eta] at h1
  rw [Seq.posR_val]
  omega

omit [DecidableEq I] in
/-- **The first strand of the second block lies left of `p`** under every shuffle `u`, when
either `|ν| < p`, or `|ν| = p` and the labels of `s` after `p` are not the weight `ν'`; so its
label satisfies any property `P` that holds for the labels in `ν'` at positions `< p`. -/
theorem tail_first_of_lt (s : Seq (ν + ν')) (p : ℕ) (P : I → Prop)
    (hs : ∀ a : Fin (Multiset.card (ν + ν')), a.val < p → s.1 a ∈ ν' → P (s.1 a))
    (hpos : Multiset.card ν < p ∨ (Multiset.card ν = p ∧
      (Finset.univ.val.map fun b : Fin (Multiset.card ν') => s.1 (Seq.posR ν b)) ≠ ν'))
    (hc : 0 < Multiset.card ν') (u : Shuffle (Seq.card_add' ν ν')) (i : Seq ν) (j : Seq ν')
    (h : i.append j = u.1 • s) : P (j.1 ⟨0, hc⟩) := by
  have hmem : j.1 ⟨0, hc⟩ ∈ ν' := by
    have hm := Multiset.mem_map_of_mem j.1 (Finset.mem_univ_val (⟨0, hc⟩ : Fin _))
    rwa [j.2] at hm
  rw [tail_val_of_append_eq h] at hmem ⊢
  refine hs _ ?_ hmem
  rcases hpos with hlt | ⟨heq, hne⟩
  · exact lt_of_le_of_lt (shuffle_first_tail_le u hc) hlt
  · by_contra hge
    refine hne (Eq.trans ?_ j.2)
    congr 1
    funext b
    rw [tail_val_of_append_eq h, shuffle_tail_eq_of_first u hc (by omega)]

end Positions

section Layer

variable {ν ν' ν'' ν''' : Multiset I} (q : MackeyQuad ν ν' ν'' ν''')
  (N : Type*) [AddCommGroup N] [Module k N] [Module (TensorKLR Q ν'' ν''') N]
  [IsScalarTower k (TensorKLR Q ν'' ν''') N]

/-- `MackeyBot_λ ⊗_{R''} N`, the right factor of a Mackey layer. -/
local notation "BotN" => BalancedTensor k (QuadAlg Q q) (TensorKLR Q ν'' ν''') (MackeyBot Q q) N

omit [IsScalarTower k (TensorKLR Q ν'' ν''') N] in
/-- **The tail idempotent kills the bottom factor** when each loading `j v` of the second bottom
block with `j ∈ T` kills `N`. -/
theorem quadAlg_tail_smul_eq_zero (T : Finset (Seq q.β))
    (hN : ∀ j ∈ T, ∀ (v : Seq q.δ) (x : N),
      ((1 : KLRAlgebra k Q ν'') ⊗ₜ (e (seqCast q.h₄ (j.append v)) : KLRAlgebra k Q ν''') :
        TensorKLR Q ν'' ν''') • x = 0)
    (y : BotN) :
    ((((1 : KLRAlgebra k Q q.α) ⊗ₜ eSum Q T) ⊗ₜ (1 : TensorKLR Q q.γ q.δ) : QuadAlg Q q) •
      y) = 0 := by
  set r : QuadAlg Q q := ((1 : KLRAlgebra k Q q.α) ⊗ₜ eSum Q T) ⊗ₜ (1 : TensorKLR Q q.γ q.δ)
  set F : KLRAlgebra k Q ν''' := castAlg Q q.h₄ (concat Q q.β q.δ (eSum Q T ⊗ₜ 1)) with hF
  have hr : quadBot q r = castAlg Q q.h₃ (concat Q q.α q.γ 1) ⊗ₜ F := by
    rw [show r = ((1 : KLRAlgebra k Q q.α) ⊗ₜ eSum Q T) ⊗ₜ
      ((1 : KLRAlgebra k Q q.γ) ⊗ₜ (1 : KLRAlgebra k Q q.δ)) from rfl, quadBot_tmul]
    rfl
  have hFF : F * F = F := by
    rw [hF, ← map_mul, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, (eSum_idem _).eq,
      mul_one]
  have hFx : ∀ x : N, ((1 : KLRAlgebra k Q ν'') ⊗ₜ F : TensorKLR Q ν'' ν''') • x = 0 := by
    intro x
    have hsum : F = ∑ j ∈ T, ∑ v : Seq q.δ, (e (seqCast q.h₄ (j.append v)) :
        KLRAlgebra k Q ν''') := by
      rw [hF, eSum, ← sum_e (Q := Q) (ν := q.δ), TensorProduct.sum_tmul, map_sum, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [TensorProduct.tmul_sum, map_sum, map_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [concat_e_tmul_e, castAlg_e]
    rw [hsum, TensorProduct.tmul_sum, Finset.sum_smul]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [TensorProduct.tmul_sum, Finset.sum_smul]
    exact Finset.sum_eq_zero fun v _ => hN j hj v x
  induction y using BalancedTensor.induction_on with
  | zero => rw [smul_zero]
  | add y y' hy hy' => rw [smul_add, hy, hy', add_zero]
  | tmul b x =>
    rw [BalancedTensor.smul_tmul']
    let m : MackeyBot Q q := ⟨quadBot q r, by rw [mem_quadBotSub, ← quadBot_mul, one_mul]⟩
    have hb : r • b = op (b : TensorKLR Q ν'' ν''') • m := rfl
    have hm : m = op ((1 : KLRAlgebra k Q ν'') ⊗ₜ F : TensorKLR Q ν'' ν''') • m := by
      apply Subtype.ext
      change quadBot q r = quadBot q r * ((1 : KLRAlgebra k Q ν'') ⊗ₜ F)
      rw [hr, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hFF]
    rw [hb, BalancedTensor.op_smul_tmul, hm, BalancedTensor.op_smul_tmul, hFx,
      BalancedTensor.tmul_zero]

theorem quadTop_one_eq_tmul :
    (quadTop q 1 : TensorKLR Q ν ν') =
      castAlg Q q.h₁ (oneConcat Q q.α q.β) ⊗ₜ castAlg Q q.h₂ (oneConcat Q q.γ q.δ) := by
  change quadTop q ((1 ⊗ₜ 1) ⊗ₜ (1 ⊗ₜ 1)) = _
  rw [quadTop_tmul]
  simp only [← Algebra.TensorProduct.one_def, concat_one]

variable {N} in
omit [IsScalarTower k (TensorKLR Q ν'' ν''') N] in
/-- **A loading of the top whose second-block strands are all tail-killed kills the layer**:
if every shuffle `u` writes `u • s` only as `i j` with `j ∈ T`, and `(1 ⊗ 1_T) ⊗ 1` kills
`MackeyBot_λ ⊗_{R''} N`, then `1_s ⊗ 1` kills `MackeyTop_λ ⊗_{R'} (MackeyBot_λ ⊗_{R''} N)`. -/
theorem e_tmul_one_smul_mackeyLeftInd_eq_zero (hsym : KLRSymm Q) (s : Seq ν)
    (T : Finset (Seq q.β))
    (hT : ∀ (u : Shuffle (Seq.card_add' q.α q.β)) (i : Seq q.α) (j : Seq q.β),
      i.append j = u.1 • seqCast q.h₁.symm s → j ∈ T)
    (hann : ∀ y : BotN,
      ((((1 : KLRAlgebra k Q q.α) ⊗ₜ eSum Q T) ⊗ₜ (1 : TensorKLR Q q.γ q.δ) : QuadAlg Q q) •
        y) = 0)
    (w : MackeyLeftInd Q N q) :
    ((e s : KLRAlgebra k Q ν) ⊗ₜ (1 : KLRAlgebra k Q ν') : TensorKLR Q ν ν') • w = 0 := by
  set r₀ : QuadAlg Q q :=
    ((1 : KLRAlgebra k Q q.α) ⊗ₜ eSum Q T) ⊗ₜ (1 : TensorKLR Q q.γ q.δ)
  let V : Submodule k (MackeyTop Q q) :=
    { carrier := {t | ∀ y : BotN, (BalancedTensor.tmul t y : MackeyLeftInd Q N q) = 0}
      add_mem' := fun ha hb y => by rw [BalancedTensor.add_tmul, ha, hb, add_zero]
      zero_mem' := fun y => by
        rw [show (0 : MackeyTop Q q) = (0 : k) • (0 : MackeyTop Q q) from (zero_smul _ _).symm,
          BalancedTensor.smul_tmul, zero_smul]
      smul_mem' := fun c t ht y => by rw [BalancedTensor.smul_tmul, ht, smul_zero] }
  have hV : ∀ (Z : MackeyTop Q q) (R : QuadAlg Q q), op (r₀ * R) • Z ∈ V := by
    intro Z R y
    rw [BalancedTensor.op_smul_tmul, mul_smul, hann, BalancedTensor.tmul_zero]
  have hidem : IsIdempotentElem (quadTop q 1 : TensorKLR Q ν ν') := by
    rw [IsIdempotentElem, ← quadTop_mul, mul_one]
  let L : TensorKLR Q ν ν' →ₗ[k] MackeyTop Q q :=
    { toFun := fun X => ⟨((e s : KLRAlgebra k Q ν) ⊗ₜ (1 : KLRAlgebra k Q ν')) * X *
          quadTop q 1, Graded.mul_mem_leftIdeal hidem _⟩
      map_add' := fun X Y => Subtype.ext (by simp only [mul_add, add_mul]; rfl)
      map_smul' := fun c X => Subtype.ext (by
        simp only [mul_smul_comm, smul_mul_assoc, RingHom.id_apply]; rfl) }
  set c' : KLRAlgebra k Q ν' := castAlg Q q.h₂ (oneConcat Q q.γ q.δ)
  have hc' : c' * c' = c' := by rw [← map_mul, oneConcat_idem.eq]
  have hL : ∀ X, L X ∈ V := by
    intro X
    induction X using TensorProduct.inductionOn with
    | add X Y hX hY => rw [map_add]; exact V.add_mem hX hY
    | tmul a b =>
      obtain ⟨F, t, hF⟩ := e_mul_eq_sum_tail_cast hsym shufWord_spec q.h₁ s T hT
        (r := a * castAlg Q q.h₁ (oneConcat Q q.α q.β))
        (by rw [mul_assoc, ← map_mul, oneConcat_idem.eq])
      have h2 : ∀ u, quadTop q (r₀ * (t u ⊗ₜ 1)) = castAlg Q q.h₁ (concat Q q.α q.β
          (((1 : KLRAlgebra k Q q.α) ⊗ₜ eSum Q T) * t u)) ⊗ₜ c' := by
        intro u
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
        change TensorProduct.map _ _ (_ ⊗ₜ _) = _
        rw [TensorProduct.map_tmul]
        simp only [LinearMap.coe_comp, Function.comp_apply, AlgEquiv.toLinearMap_apply]
        rw [concat_one]
      let Z : Shuffle (Seq.card_add' q.α q.β) → MackeyTop Q q := fun u =>
        ⟨castAlg Q q.h₁ (hatWRevOf shufWord u) ⊗ₜ (b * c'), by
          rw [Graded.mem_leftIdeal, quadTop_one_eq_tmul, Algebra.TensorProduct.tmul_mul_tmul,
            ← map_mul, hatWRevOf_mul_oneConcat, mul_assoc, hc']⟩
      have e1 : ((e s : KLRAlgebra k Q ν) ⊗ₜ (1 : KLRAlgebra k Q ν')) * (a ⊗ₜ b) *
          quadTop q 1 = ∑ u ∈ F, (castAlg Q q.h₁ (hatWRevOf shufWord u) ⊗ₜ (b * c') :
            TensorKLR Q ν ν') * quadTop q (r₀ * (t u ⊗ₜ 1)) := by
        rw [quadTop_one_eq_tmul, Algebra.TensorProduct.tmul_mul_tmul,
          Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_assoc, hF, TensorProduct.sum_tmul]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [h2, Algebra.TensorProduct.tmul_mul_tmul, mul_assoc, hc']
      have hL2 : L (a ⊗ₜ b) = ∑ u ∈ F, op (r₀ * (t u ⊗ₜ 1)) • Z u := by
        apply Subtype.ext
        rw [Submodule.coe_sum]
        exact e1
      rw [hL2]
      exact V.sum_mem fun u _ => hV _ _
  induction w using BalancedTensor.induction_on with
  | zero => rw [smul_zero]
  | add w w' hw hw' => rw [smul_add, hw, hw', add_zero]
  | tmul t y =>
    rw [BalancedTensor.smul_tmul']
    have ht : ((e s : KLRAlgebra k Q ν) ⊗ₜ (1 : KLRAlgebra k Q ν') : TensorKLR Q ν ν') • t =
        L t := Subtype.ext (by
      change _ = ((e s : KLRAlgebra k Q ν) ⊗ₜ (1 : KLRAlgebra k Q ν')) *
        (t : TensorKLR Q ν ν') * quadTop q 1
      rw [mul_assoc, Graded.mem_leftIdeal.1 t.2]; rfl)
    rw [ht]
    exact hL t y

end Layer

end KLRAlgebra

end Categorification.KLR

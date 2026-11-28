/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.MackeyTailIdempotent
import Categorification.KLR.MackeyLayerLoading

/-!
# The identity shuffle in a Mackey layer

Khovanov–Lauda I (arXiv:0803.4121v2), §2.6, Propositions 2.16 and 2.18, used for Webster,
arXiv:1309.3796v3, §7.3, proof of Lemma 7.19 (trace half, step L3: the leading piece of the
head-strand filtration).

Let `q` be a Mackey datum and `s` a loading of the first top block `ν`. Write every
`r ∈ R(ν) 1_{α,β}` as `∑_u ŵ_u^* ι(t_u)` over the shuffles `u` (Proposition 2.16 in
right-module form). If, for every shuffle `u ≠ 1`, every way of writing `u • s = i j` has its
second factor in a set `T` of loadings of `β`, and `(1 ⊗ 1_T) ⊗ 1 ∈ R'` kills
`MackeyBot_λ ⊗_{R''} N`, then only the identity shuffle survives: `(1_s ⊗ 1) w` lies in the
`k`-span of the elements `(1 ⊗ b) · (1_{λ} ⊗ y)`, where `1_λ = quadTop 1` is the generator of
`MackeyTop_λ` and `y ∈ MackeyBot_λ ⊗_{R''} N` (`e_tmul_one_smul_mackeyLeftInd_mem_span`).
On these elements the parabolic part `ι_{α,β}(X) ⊗ 1` of `R(ν) ⊗ R(ν')` acts through the
bottom factor, by `X ⊗ 1 ∈ R'` (`castAlg_concat_tmul_one_smul_tmul_mackeyTopOne`).

Webster's proof does not spell this out.

Symmetric `Q` (`KLRSymm Q`), any commutative ring `k`.

## Main results

* `TypeA.shuffle_eq_one_of_tail_fixed`, `KLR.KLRAlgebra.shuffle_first_tail_lt_of_ne_one`.
* `KLR.KLRAlgebra.e_mul_eq_concat_add_sum_tail`: Proposition 2.16 with the identity shuffle
  split off.
* `KLR.KLRAlgebra.e_tmul_one_smul_mackeyLeftInd_mem_span`,
  `KLR.KLRAlgebra.castAlg_concat_tmul_one_smul_tmul_mackeyTopOne`.
* `KLR.KLRAlgebra.indTopAct_e_tmul_mem_iSup_map`: on a Mackey layer, a loading lands in the
  span of the images under `Ξ_λ` of the parts it maps into.
-/

noncomputable section

namespace Categorification.TypeA

open Equiv

/-- **A shuffle fixing every position of the second block is the identity.** -/
theorem shuffle_eq_one_of_tail_fixed {n n' m : ℕ} {h : n + n' = m} (u : Shuffle h)
    (hu : ∀ y : Fin n', u.1⁻¹ (blockEquiv h (Sum.inr y)) = blockEquiv h (Sum.inr y)) :
    u.1 = 1 := by
  have hlt : ∀ x : Fin n, (u.1⁻¹ (blockEquiv h (Sum.inl x))).val < n := by
    intro x
    by_contra hge
    rw [not_lt] at hge
    have hm := (u.1⁻¹ (blockEquiv h (Sum.inl x))).2
    set y : Fin n' := ⟨(u.1⁻¹ (blockEquiv h (Sum.inl x))).val - n, by omega⟩
    have hy : u.1⁻¹ (blockEquiv h (Sum.inl x)) = u.1⁻¹ (blockEquiv h (Sum.inr y)) := by
      rw [hu]; apply Fin.ext; rw [blockEquiv_inr_val]; simp only [y]; omega
    have := (blockEquiv h).injective (u.1⁻¹.injective hy)
    simp at this
  rw [← inv_eq_one]
  ext z
  have hmono : StrictMono (fun z : Fin m => u.1⁻¹ z) := by
    intro z z' hzz'
    obtain ⟨p, rfl⟩ := (blockEquiv h).surjective z
    obtain ⟨p', rfl⟩ := (blockEquiv h).surjective z'
    rcases p with a | b <;> rcases p' with a' | b'
    · exact u.2.1 ((blockEquiv_inl_lt_inl h).mp hzz')
    · show u.1⁻¹ _ < u.1⁻¹ _
      rw [hu, Fin.lt_def, blockEquiv_inr_val]
      have := hlt a; omega
    · exfalso
      rw [Fin.lt_def, blockEquiv_inl_val, blockEquiv_inr_val] at hzz'
      have := a'.2; omega
    · exact u.2.2 ((blockEquiv_inr_lt_inr h).mp hzz')
  have := congrArg (fun e : Fin m ≃o Fin m => (e z : Fin m))
    (Subsingleton.elim (StrictMono.orderIsoOfSurjective _ hmono u.1⁻¹.surjective)
      (OrderIso.refl _))
  simpa using congrArg Fin.val this

end Categorification.TypeA

namespace Categorification.KLR

open Equiv TypeA MulOpposite
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k}

namespace KLRAlgebra

section Positions

variable {ν ν' : Multiset I}

omit [DecidableEq I] in
/-- **Under a shuffle `u ≠ 1`, the second block starts before `|ν|`.** -/
theorem shuffle_first_tail_lt_of_ne_one (u : Shuffle (Seq.card_add' ν ν'))
    (hu : u.1 ≠ 1) (hc : 0 < Multiset.card ν') :
    (u.1⁻¹ (Seq.posR ν ⟨0, hc⟩)).val < Multiset.card ν := by
  by_contra hge
  rw [not_lt] at hge
  exact hu (shuffle_eq_one_of_tail_fixed u fun y => shuffle_tail_eq_of_first u hc hge y)

end Positions

section Split

variable {ν ν' : Multiset I} (hsym : KLRSymm Q) {σ : Shuffle (Seq.card_add' ν ν') → List ℕ}
  (hσ : ∀ u, IsReduced (Multiset.card (ν + ν')) (σ u) ∧
    wordProd (Multiset.card (ν + ν')) (σ u) = u.1)

include hsym hσ in
/-- **Proposition 2.16 with the identity shuffle split off**: if every shuffle `u ≠ 1` writes
`u • s` only as `i j` with `j ∈ T`, then
`1_s r = ι(X) + ∑_u ŵ_u^* ι((1 ⊗ 1_T) t_u)` for `r ∈ R(ν + ν') 1_{ν,ν'}`. -/
theorem e_mul_eq_concat_add_sum_tail (s : Seq (ν + ν')) (T : Finset (Seq ν'))
    (hT : ∀ (u : Shuffle (Seq.card_add' ν ν')), u.1 ≠ 1 → ∀ (i : Seq ν) (j : Seq ν'),
      i.append j = u.1 • s → j ∈ T)
    {r : KLRAlgebra k Q (ν + ν')} (hr : r * oneConcat Q ν ν' = r) :
    ∃ (X : TensorKLR Q ν ν') (F : Finset (Shuffle (Seq.card_add' ν ν')))
      (t : Shuffle (Seq.card_add' ν ν') → TensorKLR Q ν ν'), e s * r = concat Q ν ν' X +
        ∑ u ∈ F, hatWRevOf σ u * concat Q ν ν' (((1 : KLRAlgebra k Q ν) ⊗ₜ eSum Q T) * t u) := by
  classical
  obtain ⟨g, rfl⟩ := exists_rightFreeMapOf_eq hsym hσ hr
  set f : Shuffle (Seq.card_add' ν ν') → KLRAlgebra k Q (ν + ν') := fun u =>
    hatWRevOf σ u * concat Q ν ν' (concatIdem (u.1 • s) * g u) with hf
  have hterm : ∀ u, e s * (hatWRevOf σ u * concat Q ν ν' (g u)) = f u := by
    intro u
    rw [hf, ← mul_assoc, e_mul_hatWRevOf σ hσ, mul_assoc, ← concat_mul]
  have hsum : e s * rightFreeMapOf σ g = ∑ u ∈ insert shufOne g.support, f u := by
    rw [rightFreeMapOf_apply, Finsupp.sum, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun u _ => hterm u]
    refine Finset.sum_subset (Finset.subset_insert _ _) fun u _ hu => ?_
    rw [Finsupp.notMem_support_iff.1 hu, mul_zero, map_zero, mul_zero]
  refine ⟨concatIdem ((shufOne : Shuffle (Seq.card_add' ν ν')).1 • s) * g shufOne,
    (insert shufOne g.support).erase shufOne,
    fun u => concatIdem (u.1 • s) * g u, ?_⟩
  rw [hsum, ← Finset.add_sum_erase _ _ (Finset.mem_insert_self _ _)]
  congr 1
  · show hatWRevOf σ shufOne * _ = _
    rw [hatWRevOf_one hσ, oneConcat_mul_concat]
  · refine Finset.sum_congr rfl fun u hu => ?_
    have hu1 : u.1 ≠ 1 := fun h1 => (Finset.ne_of_mem_erase hu) (Subtype.ext h1)
    show hatWRevOf σ u * concat Q ν ν' (concatIdem (u.1 • s) * g u) = _
    rw [← mul_assoc, tmul_eSum_mul_concatIdem _ T (hT u hu1)]

include hsym hσ in
/-- `e_mul_eq_concat_add_sum_tail` for a weight `ν'' = ν + ν'` given up to equality. -/
theorem e_mul_eq_concat_add_sum_tail_cast {ν'' : Multiset I} (h : ν + ν' = ν'') (s : Seq ν'')
    (T : Finset (Seq ν'))
    (hT : ∀ (u : Shuffle (Seq.card_add' ν ν')), u.1 ≠ 1 → ∀ (i : Seq ν) (j : Seq ν'),
      i.append j = u.1 • seqCast h.symm s → j ∈ T)
    {r : KLRAlgebra k Q ν''} (hr : r * castAlg Q h (oneConcat Q ν ν') = r) :
    ∃ (X : TensorKLR Q ν ν') (F : Finset (Shuffle (Seq.card_add' ν ν')))
      (t : Shuffle (Seq.card_add' ν ν') → TensorKLR Q ν ν'), e s * r =
        castAlg Q h (concat Q ν ν' X) + ∑ u ∈ F, castAlg Q h (hatWRevOf σ u) *
          castAlg Q h (concat Q ν ν' (((1 : KLRAlgebra k Q ν) ⊗ₜ eSum Q T) * t u)) := by
  subst h
  exact e_mul_eq_concat_add_sum_tail hsym hσ s T hT hr

end Split

section Layer

variable {ν ν' ν'' ν''' : Multiset I} (q : MackeyQuad ν ν' ν'' ν''')
  (N : Type*) [AddCommGroup N] [Module k N] [Module (TensorKLR Q ν'' ν''') N]

/-- `MackeyBot_λ ⊗_{R''} N`, the right factor of a Mackey layer. -/
local notation "BotN" => BalancedTensor k (QuadAlg Q q) (TensorKLR Q ν'' ν''') (MackeyBot Q q) N

/-- The generator `1_λ = quadTop 1` of `MackeyTop_λ`. -/
def mackeyTopOne : MackeyTop Q q :=
  ⟨quadTop q 1, by rw [Graded.mem_leftIdeal]; exact quadTop_mul_one q 1⟩

theorem coe_mackeyTopOne : ((mackeyTopOne q : MackeyTop Q q) : TensorKLR Q ν ν') =
    quadTop q 1 := rfl

/-- The `k`-span of the elements `(1 ⊗ b) · (1_λ ⊗ y)` of a Mackey layer: the part coming from
the identity shuffle of the first top block. -/
def mackeyTopOneSpan : Submodule k (MackeyLeftInd Q N q) :=
  Submodule.span k (Set.range fun p : KLRAlgebra k Q ν' × BotN =>
    (((1 : KLRAlgebra k Q ν) ⊗ₜ p.1 : TensorKLR Q ν ν') •
      (BalancedTensor.tmul (mackeyTopOne q) p.2 : MackeyLeftInd Q N q)))

variable {N}

theorem smul_tmul_mackeyTopOne_mem (b : KLRAlgebra k Q ν') (y : BotN) :
    (((1 : KLRAlgebra k Q ν) ⊗ₜ b : TensorKLR Q ν ν') •
      (BalancedTensor.tmul (mackeyTopOne q) y : MackeyLeftInd Q N q)) ∈
        mackeyTopOneSpan q N :=
  Submodule.subset_span ⟨(b, y), rfl⟩

/-- `ι_{α,β}(X) ⊗ c' = 1_λ · (X ⊗ 1)` in `R(ν) ⊗ R(ν')`, where `c' = 1_{γ,δ}`. -/
theorem quadTop_one_mul_quadTop_tmul_one (X : TensorKLR Q q.α q.β) :
    (quadTop q 1 * quadTop q (X ⊗ₜ (1 : TensorKLR Q q.γ q.δ)) : TensorKLR Q ν ν') =
      castAlg Q q.h₁ (concat Q q.α q.β X) ⊗ₜ castAlg Q q.h₂ (oneConcat Q q.γ q.δ) := by
  rw [quadTop_one_eq_tmul]
  change _ * TensorProduct.map _ _ (X ⊗ₜ 1) = _
  rw [TensorProduct.map_tmul]
  simp only [LinearMap.coe_comp, Function.comp_apply, AlgEquiv.toLinearMap_apply]
  rw [concat_one, Algebra.TensorProduct.tmul_mul_tmul, ← map_mul, ← map_mul,
    oneConcat_mul_concat, oneConcat_idem.eq]

/-- **The parabolic part acts through the bottom factor** on the identity-shuffle part:
`(ι_{α,β}(X) ⊗ 1) · (1_λ ⊗ y) = 1_λ ⊗ ((X ⊗ 1) y)`. -/
theorem castAlg_concat_tmul_one_smul_tmul_mackeyTopOne (X : TensorKLR Q q.α q.β) (y : BotN) :
    ((castAlg Q q.h₁ (concat Q q.α q.β X) ⊗ₜ (1 : KLRAlgebra k Q ν') : TensorKLR Q ν ν') •
      (BalancedTensor.tmul (mackeyTopOne q) y : MackeyLeftInd Q N q)) =
      BalancedTensor.tmul (mackeyTopOne q)
        ((X ⊗ₜ (1 : TensorKLR Q q.γ q.δ) : QuadAlg Q q) • y) := by
  rw [BalancedTensor.smul_tmul', ← BalancedTensor.op_smul_tmul]
  congr 1
  apply Subtype.ext
  change _ * quadTop q 1 = quadTop q 1 * quadTop q (X ⊗ₜ 1)
  rw [quadTop_one_mul_quadTop_tmul_one, quadTop_one_eq_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, ← map_mul, one_mul, concat_mul_oneConcat]

/-- `ι_{α,β}(X) ⊗ (b c') = (1 ⊗ b) · 1_λ · (X ⊗ 1)` in `R(ν) ⊗ R(ν')`. -/
theorem tmul_mul_eq_one_tmul_mul_quadTop (X : TensorKLR Q q.α q.β) (b : KLRAlgebra k Q ν') :
    (castAlg Q q.h₁ (concat Q q.α q.β X) ⊗ₜ (b * castAlg Q q.h₂ (oneConcat Q q.γ q.δ)) :
      TensorKLR Q ν ν') = ((1 : KLRAlgebra k Q ν) ⊗ₜ b) *
        (quadTop q 1 * quadTop q (X ⊗ₜ (1 : TensorKLR Q q.γ q.δ))) := by
  rw [quadTop_one_mul_quadTop_tmul_one, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/-- **L3: only the identity shuffle survives.** If every shuffle `u ≠ 1` writes `u • s` only
as `i j` with `j ∈ T`, and `(1 ⊗ 1_T) ⊗ 1` kills `MackeyBot_λ ⊗_{R''} N`, then `(1_s ⊗ 1) w`
lies in the span of the elements `(1 ⊗ b) · (1_λ ⊗ y)`. -/
theorem e_tmul_one_smul_mackeyLeftInd_mem_span (hsym : KLRSymm Q) (s : Seq ν)
    (T : Finset (Seq q.β))
    (hT : ∀ (u : Shuffle (Seq.card_add' q.α q.β)), u.1 ≠ 1 → ∀ (i : Seq q.α) (j : Seq q.β),
      i.append j = u.1 • seqCast q.h₁.symm s → j ∈ T)
    (hann : ∀ y : BotN,
      ((((1 : KLRAlgebra k Q q.α) ⊗ₜ eSum Q T) ⊗ₜ (1 : TensorKLR Q q.γ q.δ) : QuadAlg Q q) •
        y) = 0)
    (w : MackeyLeftInd Q N q) :
    ((e s : KLRAlgebra k Q ν) ⊗ₜ (1 : KLRAlgebra k Q ν') : TensorKLR Q ν ν') • w ∈
      mackeyTopOneSpan q N := by
  set r₀ : QuadAlg Q q :=
    ((1 : KLRAlgebra k Q q.α) ⊗ₜ eSum Q T) ⊗ₜ (1 : TensorKLR Q q.γ q.δ)
  let V : Submodule k (MackeyTop Q q) :=
    { carrier := {t | ∀ y : BotN, (BalancedTensor.tmul t y : MackeyLeftInd Q N q) ∈
        mackeyTopOneSpan q N}
      add_mem' := fun ha hb y => by
        rw [BalancedTensor.add_tmul]; exact add_mem (ha y) (hb y)
      zero_mem' := fun y => by rw [BalancedTensor.zero_tmul]; exact zero_mem _
      smul_mem' := fun c t ht y => by
        rw [BalancedTensor.smul_tmul]; exact Submodule.smul_mem _ c (ht y) }
  have hV : ∀ (Z : MackeyTop Q q) (R : QuadAlg Q q), op (r₀ * R) • Z ∈ V := by
    intro Z R y
    change BalancedTensor.tmul _ y ∈ _
    rw [BalancedTensor.op_smul_tmul, mul_smul, hann, BalancedTensor.tmul_zero]
    exact zero_mem _
  have hV1 : ∀ (X : TensorKLR Q q.α q.β) (b : KLRAlgebra k Q ν'),
      ((1 : KLRAlgebra k Q ν) ⊗ₜ b : TensorKLR Q ν ν') •
        (op (X ⊗ₜ (1 : TensorKLR Q q.γ q.δ) : QuadAlg Q q) • mackeyTopOne q) ∈ V := by
    intro X b y
    change BalancedTensor.tmul _ y ∈ _
    rw [← BalancedTensor.smul_tmul', BalancedTensor.op_smul_tmul]
    exact smul_tmul_mackeyTopOne_mem q _ _
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
      obtain ⟨X₀, F, t, hF⟩ := e_mul_eq_concat_add_sum_tail_cast hsym shufWord_spec q.h₁ s T hT
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
          quadTop q 1 = ((1 : KLRAlgebra k Q ν) ⊗ₜ b) *
            (quadTop q 1 * quadTop q (X₀ ⊗ₜ (1 : TensorKLR Q q.γ q.δ))) +
          ∑ u ∈ F, (castAlg Q q.h₁ (hatWRevOf shufWord u) ⊗ₜ (b * c') :
            TensorKLR Q ν ν') * quadTop q (r₀ * (t u ⊗ₜ 1)) := by
        rw [quadTop_one_eq_tmul, Algebra.TensorProduct.tmul_mul_tmul,
          Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_assoc, hF, TensorProduct.add_tmul,
          TensorProduct.sum_tmul, ← quadTop_one_eq_tmul, ← tmul_mul_eq_one_tmul_mul_quadTop]
        congr 1
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [h2, Algebra.TensorProduct.tmul_mul_tmul, mul_assoc, hc']
      have hL2 : L (a ⊗ₜ b) = ((1 : KLRAlgebra k Q ν) ⊗ₜ b : TensorKLR Q ν ν') •
          (op (X₀ ⊗ₜ (1 : TensorKLR Q q.γ q.δ) : QuadAlg Q q) • mackeyTopOne q) +
          ∑ u ∈ F, op (r₀ * (t u ⊗ₜ 1)) • Z u := by
        apply Subtype.ext
        rw [Submodule.coe_add, Submodule.coe_sum]
        exact e1
      rw [hL2]
      exact V.add_mem (hV1 _ _) (V.sum_mem fun u _ => hV _ _)
  induction w using BalancedTensor.induction_on with
  | zero => rw [smul_zero]; exact zero_mem _
  | add w w' hw hw' => rw [smul_add]; exact add_mem hw hw'
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

section LayerMap

variable {ν ν' ν'' ν''' : Multiset I} (h : ν'' + ν''' = ν + ν')
  (N : Type*) [AddCommGroup N] [Module k N] [Module (TensorKLR Q ν'' ν''') N]
  [IsScalarTower k (TensorKLR Q ν'' ν''') N] (hsym : KLRSymm Q)

include hsym in
/-- **A loading `e(i) ⊗ e(j)` maps the layer into the images of given parts of the surviving
`Ξ_λ`**: if `e(i) ⊗ 1` kills `MackeyTop_λ ⊗_{R'} (MackeyBot_λ ⊗_{R''} N)` for `λ` outside
`P`, and maps it into a submodule `V_λ` for `λ ∈ P`, then `e(i) ⊗ e(j)` maps the `c`-th
layer into the span of the images `Ξ_λ(V_λ)`, `λ ∈ P`. -/
theorem indTopAct_e_tmul_mem_iSup_map {c : ℕ} (i : Seq ν) (j : Seq ν')
    (P : {q : MackeyQuad ν ν' ν'' ν''' // Multiset.card q.β = c} → Prop)
    (V : ∀ q : {q : MackeyQuad ν ν' ν'' ν''' // Multiset.card q.β = c},
      Submodule k (MackeyLeftInd Q N q.1))
    (hk : ∀ q, ¬ P q → ∀ w : MackeyLeftInd Q N q.1,
      ((e i : KLRAlgebra k Q ν) ⊗ₜ (1 : KLRAlgebra k Q ν') : TensorKLR Q ν ν') • w = 0)
    (hV : ∀ q, P q → ∀ w : MackeyLeftInd Q N q.1,
      ((e i : KLRAlgebra k Q ν) ⊗ₜ (1 : KLRAlgebra k Q ν') : TensorKLR Q ν ν') • w ∈ V q)
    (y : IndMackeyLayer Q ν'' ν''' N (Multiset.card ν) c) :
    indTopAct h N c ((e i : KLRAlgebra k Q ν) ⊗ₜ (e j : KLRAlgebra k Q ν')) y ∈
      ⨆ (q) (_ : P q), (V q).map (indMackeyLeftMap (Q := Q) h N q.1 q.2) := by
  have hsplit : ((e i : KLRAlgebra k Q ν) ⊗ₜ (e j : KLRAlgebra k Q ν') : TensorKLR Q ν ν') =
      ((e i : KLRAlgebra k Q ν) ⊗ₜ (1 : KLRAlgebra k Q ν')) *
        (1 * ((1 : KLRAlgebra k Q ν) ⊗ₜ (e j : KLRAlgebra k Q ν'))) := by
    rw [one_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [hsplit, ← indTopAct_mul, ← indTopAct_mul]
  have hmem : indTopAct h N c 1 (indTopAct h N c
      ((1 : KLRAlgebra k Q ν) ⊗ₜ (e j : KLRAlgebra k Q ν')) y) ∈
      ⨆ q : {q : MackeyQuad ν ν' ν'' ν''' // Multiset.card q.β = c},
        LinearMap.range (indMackeyLeftMap (Q := Q) h N q.1 q.2) := by
    rw [iSup_range_indMackeyLeftMap h N hsym shufWord_spec]
    exact ⟨_, rfl⟩
  refine Submodule.iSup_induction _ (motive := fun x => indTopAct h N c
    ((e i : KLRAlgebra k Q ν) ⊗ₜ (1 : KLRAlgebra k Q ν')) x ∈
      ⨆ (q) (_ : P q), (V q).map (indMackeyLeftMap (Q := Q) h N q.1 q.2)) hmem ?_ ?_ ?_
  · rintro q x ⟨w, rfl⟩
    rw [← indMackeyLeftMap_smul]
    by_cases hq : P q
    · exact Submodule.mem_iSup_of_mem q (Submodule.mem_iSup_of_mem hq ⟨_, hV q hq w, rfl⟩)
    · rw [hk q hq w, map_zero]
      exact zero_mem _
  · rw [map_zero]; exact zero_mem _
  · intro x x' hx hx'
    rw [map_add]; exact add_mem hx hx'

end LayerMap

end KLRAlgebra

end Categorification.KLR

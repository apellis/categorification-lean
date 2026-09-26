/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Crystal.SimpleTensor

/-!
# KL I, Lemmas 3.6, 3.7, 3.8

Khovanov–Lauda I (arXiv:0803.4121v2), §3.2 (TeX lines 2104–2146), the analogues of Kleshchev,
*Linear and projective representations of symmetric groups*, Lemmas 5.1.2–5.1.4.

Throughout, `k` is a field, `Q` satisfies the hypotheses of the basis theorem (`hPQ`, `hP`), `ν'`
is a weight all of whose labels are `i` (`hν'`, `n = card ν'`), `L = L(i^n)`
(`KLRAlgebra.KLRRep hν' Q`), and `Δ = Δ_{i^n} = KLRAlgebra.ResSub Q μ ν'`. Modules are ungraded
and finite-dimensional; "irreducible" is `IsSimpleModule` (graded simple modules are simple
by KL I Proposition 2.12, `KLRAlgebra.isSimpleModule_of_isGradedSimple`).

## Main results

* `KLRAlgebra.epsI_ind_le` : `ε_i(Ind (N ⊠ L(i^n))) ≤ ε_i(N) + n` — from the Shuffle Lemma
  (`KLRAlgebra.exists_shuffle_of_fixSub_ind_ne_bot`) and the combinatorics of shuffles
  (`KLRAlgebra.tailLen_le_of_shuffle`).
* `KLRAlgebra.lemma_3_6` (**KL I, Lemma 3.6**): if `M` is irreducible and `N ⊠ L(i^n)` embeds
  in `Δ_{i^n} M` (`N ≠ 0`), then `ε_i(N) + n = ε_i(M)`, i.e. `ε_i(N) = ε_i(M) - n`. (The paper
  assumes `N ⊠ L(i^n)` irreducible; only `N ≠ 0` is used.)
* `KLRAlgebra.indUnitEquiv` (**KL I, Lemma 3.7 (1)**): if `ε_i(N) = 0` then
  `N ⊠ L(i^n) ≅ Δ_{i^n} Ind (N ⊠ L(i^n))` via `y ↦ 1 ⊗ y` (`N` need not be irreducible).
* `KLRAlgebra.lemma_3_7_head` (**Lemma 3.7 (2)**): if moreover `N` is irreducible, then
  `M = Ind (N ⊠ L(i^n))` has a unique maximal submodule `P` (`hd M = M/P` is irreducible,
  `isSimpleModule_iff_isCoatom`) and `ε_i(M/P) = n`;
  `KLRAlgebra.lemma_3_7_other` (**Lemma 3.7 (3)**): every nonzero subquotient `X` of `P` (i.e.
  every composition factor of `M` other than the head) has `ε_i(X) < n`.
* `KLRAlgebra.lemma_3_8` (**KL I, Lemma 3.8**): if `M` is irreducible with nilpotent dots and
  `ε_i(M) = n`, then `Δ_{i^n} M` is irreducible, `Δ_{i^n} M ≅ N ⊠ L(i^n)` with `N = HW(Δ M)`
  irreducible (`hwEquiv`, `isSimpleModule_hwSpace`), and `ε_i(N) = 0`.

The nilpotency of the dots is needed only for Lemma 3.8 (to know that irreducible
`R(μ) ⊗ R(ni)`-modules are of the form `N ⊠ L(i^n)`); it holds for all graded
finite-dimensional modules.
-/

noncomputable section

namespace Categorification.KLR

open Equiv MvPolynomial TypeA MulOpposite Categorification.NilHecke
open scoped TensorProduct

variable {I : Type*} [DecidableEq I]

/-! ### Combinatorics of shuffles and tails -/

section Combinatorics

/-- A strictly monotone map `Fin a → Fin m` increases gaps. -/
theorem strictMono_fin_gap {a m : ℕ} {f : Fin a → Fin m} (hf : StrictMono f) :
    ∀ (d : ℕ) (x : Fin a) (hx : x.val + d < a), (f x).val + d ≤ (f ⟨x.val + d, hx⟩).val
  | 0, x, _ => by simp
  | d + 1, x, hx => by
    have h1 := strictMono_fin_gap hf d x (by omega)
    have h2 : f ⟨x.val + d, by omega⟩ < f ⟨x.val + (d + 1), hx⟩ :=
      hf (Fin.mk_lt_mk.2 (by omega))
    rw [Fin.lt_def] at h2
    omega

theorem strictMono_fin_ge {a m : ℕ} {f : Fin a → Fin m} (hf : StrictMono f) (x : Fin a) :
    x.val ≤ (f x).val := by
  have := strictMono_fin_gap hf x.val ⟨0, by have := x.2; omega⟩ (by simp)
  simp only [zero_add, Fin.eta] at this
  omega

theorem strictMono_fin_le {a m : ℕ} {f : Fin a → Fin m} (hf : StrictMono f) (x : Fin a) :
    (f x).val + (a - 1 - x.val) < m := by
  have := strictMono_fin_gap hf (a - 1 - x.val) x (by have := x.2; omega)
  have h2 := (f ⟨x.val + (a - 1 - x.val), by have := x.2; omega⟩).2
  omega

variable {μ ν' : Multiset I} {i : I}

theorem Seq.apply_ne_of_tailLen_lt {j : Seq μ} (h : Seq.tailLen i j < Multiset.card μ) :
    j.1 ⟨Multiset.card μ - 1 - Seq.tailLen i j, by omega⟩ ≠ i := by
  intro hj
  have : Seq.HasTail i j (Seq.tailLen i j + 1) := by
    refine ⟨by omega, fun a ha => ?_⟩
    by_cases hx : a.val = Multiset.card μ - 1 - Seq.tailLen i j
    · rw [show a = ⟨Multiset.card μ - 1 - Seq.tailLen i j, by omega⟩ from Fin.ext hx]
      exact hj
    · exact Seq.apply_eq_of_le_tailLen (by omega)
  have := Seq.le_tailLen this
  omega

omit [DecidableEq I] in
theorem shuffle_inv_posL_mono (u : Shuffle (Seq.card_add' μ ν')) :
    StrictMono fun x : Fin (Multiset.card μ) => u.1⁻¹ (Seq.posL ν' x) :=
  u.2.1

omit [DecidableEq I] in
theorem shuffle_inv_posR_mono (u : Shuffle (Seq.card_add' μ ν')) :
    StrictMono fun y : Fin (Multiset.card ν') => u.1⁻¹ (Seq.posR μ y) :=
  u.2.2

omit [DecidableEq I] in
theorem smul_seq_apply_inv (u : Perm (Fin (Multiset.card (μ + ν')))) (s : Seq (μ + ν'))
    (a : Fin (Multiset.card (μ + ν'))) : s.1 (u⁻¹ a) = (u • s).1 a := rfl

/-- **Tails under shuffles**: if `u s = j j'` for a shuffle `u`, then the tail of `i`'s of `s` is
at most the tail of `j` plus `card ν'`. -/
theorem tailLen_le_of_shuffle (u : Shuffle (Seq.card_add' μ ν')) {s : Seq (μ + ν')}
    {j : Seq μ} {j' : Seq ν'} (h : u.1 • s = j.append j') :
    Seq.tailLen i s ≤ Seq.tailLen i j + Multiset.card ν' := by
  have hc := Multiset.card_add μ ν'
  by_cases hj : Seq.tailLen i j < Multiset.card μ
  · set x₀ : Fin (Multiset.card μ) := ⟨Multiset.card μ - 1 - Seq.tailLen i j, by omega⟩
    have hx₀ := Seq.apply_ne_of_tailLen_lt hj
    have hs : s.1 (u.1⁻¹ (Seq.posL ν' x₀)) ≠ i := by
      rw [smul_seq_apply_inv, h, Seq.append_posL]; exact hx₀
    have h1 := Seq.add_tailLen_lt hs
    have h2 := strictMono_fin_ge (shuffle_inv_posL_mono u) x₀
    simp only [x₀] at h1 h2
    omega
  · have := Seq.tailLen_le_card (i := i) s
    omega

/-- **Shuffles fixing a tail**: if `s` ends with `card ν'` letters `i`, `u s = j j'` for a shuffle
`u`, and `j` does not end with `i`, then `u = 1`. -/
theorem shuffle_eq_one (u : Shuffle (Seq.card_add' μ ν')) {s : Seq (μ + ν')}
    (hs : Seq.HasTail i s (Multiset.card ν')) {j : Seq μ} {j' : Seq ν'}
    (h : u.1 • s = j.append j') (hj : Seq.tailLen i j = 0) : u.1 = 1 := by
  have hc := Multiset.card_add μ ν'
  have hf := shuffle_inv_posL_mono u
  have hg := shuffle_inv_posR_mono u
  -- the first block is fixed
  have hfx : ∀ x : Fin (Multiset.card μ), (u.1⁻¹ (Seq.posL ν' x)).val = x.val := by
    intro x
    have hx2 := x.2
    have hlt : Seq.tailLen i j < Multiset.card μ := by omega
    have hlast := Seq.apply_ne_of_tailLen_lt (i := i) (j := j) hlt
    have e1 : (⟨Multiset.card μ - 1 - Seq.tailLen i j, by omega⟩ : Fin (Multiset.card μ)) =
        ⟨x.val + (Multiset.card μ - 1 - x.val), by omega⟩ := Fin.ext (by simp only [hj]; omega)
    rw [e1] at hlast
    have hsl : s.1 (u.1⁻¹ (Seq.posL ν' ⟨x.val + (Multiset.card μ - 1 - x.val), by omega⟩)) ≠ i := by
      rw [smul_seq_apply_inv, h, Seq.append_posL]; exact hlast
    have hfl : (u.1⁻¹ (Seq.posL ν' ⟨x.val + (Multiset.card μ - 1 - x.val), by omega⟩)).val <
        Multiset.card μ := by
      by_contra hcon
      exact hsl (hs.2 _ (by omega))
    have hgap := strictMono_fin_gap hf (Multiset.card μ - 1 - x.val) x (by omega)
    have hge := strictMono_fin_ge hf x
    beta_reduce at hgap hge
    omega
  -- hence the second block lies in the second half
  have hgy : ∀ y : Fin (Multiset.card ν'), Multiset.card μ ≤ (u.1⁻¹ (Seq.posR μ y)).val := by
    intro y
    by_contra hcon
    push_neg at hcon
    have hx : u.1⁻¹ (Seq.posL ν' ⟨(u.1⁻¹ (Seq.posR μ y)).val, hcon⟩) = u.1⁻¹ (Seq.posR μ y) :=
      Fin.ext (by rw [hfx])
    have h' := congrArg Fin.val (u.1⁻¹.injective hx)
    simp only [Seq.posL_val, Seq.posR_val] at h'
    omega
  have hgy' : ∀ y : Fin (Multiset.card ν'), (u.1⁻¹ (Seq.posR μ y)).val = Multiset.card μ + y.val := by
    intro y
    have hy2 := y.2
    have hgap0 := strictMono_fin_gap hg y.val ⟨0, by omega⟩ (by simp)
    have e0 : (⟨(⟨0, by omega⟩ : Fin (Multiset.card ν')).val + y.val, by simp⟩ :
      Fin (Multiset.card ν')) = y := Fin.ext (by simp)
    rw [e0] at hgap0
    have hle := strictMono_fin_le hg y
    have h0 := hgy ⟨0, by omega⟩
    beta_reduce at hgap0 hle
    omega
  -- so `u⁻¹ = 1`
  have hinv : u.1⁻¹ = 1 := by
    ext a
    obtain ⟨c, rfl⟩ := (blockEquiv (Seq.card_add' μ ν')).surjective a
    cases c with
    | inl x => exact hfx x
    | inr y => simpa using hgy' y
  rw [← inv_inv u.1, hinv, inv_one]

end Combinatorics

/-- External tensor products of finite-dimensional modules are finite-dimensional. -/
instance instFiniteDimensionalExtTensorKlesh {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W] :
    FiniteDimensional K (ExtTensor K V W) :=
  inferInstanceAs (FiniteDimensional K (V ⊗[K] W))

namespace KLRAlgebra

variable {K : Type*} [Field K] {Q : I → I → MvPolynomial (Fin 2) K} {μ ν' : Multiset I} {i : I}
  (hν' : ∀ a ∈ ν', a = i)
  {P : I → I → MvPolynomial (Fin 2) K}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)
  {N : Type*} [AddCommGroup N] [Module K N] [Module (KLRAlgebra K Q μ) N]
  [IsScalarTower K (KLRAlgebra K Q μ) N]
  {M : Type*} [AddCommGroup M] [Module K M] [Module (KLRAlgebra K Q (μ + ν')) M]
  [IsScalarTower K (KLRAlgebra K Q (μ + ν')) M]

/-! ### `ε_i` of induced modules -/

section EpsInd

omit [DecidableEq I] in
/-- If `a` kills `V` then `a ⊗ b` kills `V ⊠ W`. -/
theorem tmul_smul_extTensor_eq_zero {A B : Type*} [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    {V W : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower K A V]
    [AddCommGroup W] [Module K W] [Module B W] [IsScalarTower K B W] {a : A}
    (ha : ∀ v : V, a • v = 0) (b : B) (y : ExtTensor K V W) : (a ⊗ₜ[K] b) • y = 0 := by
  induction y using ExtTensor.induction_on with
  | zero => rw [smul_zero]
  | tmul v w => rw [ExtTensor.smul_tmul, ha, ExtTensor.zero_tmul]
  | add y y' hy hy' => rw [smul_add, hy, hy', add_zero]

omit [DecidableEq I] in
theorem smul_eq_zero_of_fixSub_eq_bot {A : Type*} [Ring A] [Algebra K A] {V : Type*}
    [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower K A V] {a : A}
    (ha : IsIdempotentElem a) (h : fixSub K V a = ⊥) (v : V) : a • v = 0 := by
  have := smul_mem_fixSub (k := K) ha v
  rwa [h, Submodule.mem_bot] at this

/-- If `(1_j ⊗ 1_{j'})(N ⊠ L) ≠ 0` then `1_j N ≠ 0`. -/
theorem fixSub_ne_bot_of_extTensor {j : Seq μ} {j' : Seq ν'}
    (h : fixSub K (ExtTensor K N (KLRRep hν' Q)) (e j ⊗ₜ[K] e j' : TensorKLR Q μ ν') ≠ ⊥) :
    fixSub K N (e j : KLRAlgebra K Q μ) ≠ ⊥ := by
  intro hb
  apply h
  rw [eq_bot_iff]
  intro y hy
  rw [Submodule.mem_bot, ← mem_fixSub.1 hy]
  exact tmul_smul_extTensor_eq_zero (smul_eq_zero_of_fixSub_eq_bot (e_mul_self j) hb) _ y

include hPQ hP in
/-- `ε_i(Ind (N ⊠ L(i^n))) ≤ ε_i(N) + n` (from the Shuffle Lemma). -/
theorem epsI_ind_le :
    epsI Q (μ + ν') i (Ind Q μ ν' (ExtTensor K N (KLRRep hν' Q))) ≤
      epsI Q μ i N + Multiset.card ν' := by
  rw [epsI_le_iff]
  intro s hs
  obtain ⟨u, j, j', hu, hne⟩ := exists_shuffle_of_fixSub_ind_ne_bot hPQ hP _ hs
  have hj := tailLen_le_epsI (i := i) (fixSub_ne_bot_of_extTensor hν' hne)
  have := tailLen_le_of_shuffle (i := i) u hu
  omega

end EpsInd

/-! ### Lemma 3.6 -/

include hν' hPQ hP in
/-- **KL I, Lemma 3.6** (ungraded): if `M` is irreducible and `f : N ⊠ L(i^n) ↪ Δ_{i^n} M` with
`N ≠ 0`, then `ε_i(N) + n = ε_i(M)`. -/
theorem lemma_3_6 [FiniteDimensional K N] [Nontrivial N]
    [IsSimpleModule (KLRAlgebra K Q (μ + ν')) M]
    (f : ExtTensor K N (KLRRep hν' Q) →ₗ[TensorKLR Q μ ν'] ResSub Q μ ν' M)
    (hf : Function.Injective f) :
    epsI Q μ i N + Multiset.card ν' = epsI Q (μ + ν') i M := by
  apply le_antisymm
  · obtain ⟨j, hj, hjt⟩ := exists_tailLen_eq_epsI (Q := Q) (ν := μ) (i := i) (M := N)
    obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).1 hj
    set y : ExtTensor K N (KLRRep hν' Q) := ExtTensor.tmul w (lMk hν' Q 1)
    have hy0 : y ≠ 0 := extTensor_tmul_ne_zero (A := KLRAlgebra K Q μ) (B := KLRAlgebra K Q ν')
      hw0 (lMk_one_ne_zero hν')
    have hy : (e j ⊗ₜ[K] 1 : TensorKLR Q μ ν') • y = y := by
      rw [ExtTensor.smul_tmul, mem_fixSub.1 hw, one_smul]
    have hv0 : ((f y : ResSub Q μ ν' M) : M) ≠ 0 := fun h0 =>
      hy0 (hf (by rw [map_zero]; exact Subtype.ext h0))
    have hv : (e (j.append (Seq.constSeq hν')) : KLRAlgebra K Q (μ + ν')) •
        ((f y : ResSub Q μ ν' M) : M) = f y := by
      rw [← concat_e_tmul_one_const hν', ← coe_resSub_smul, ← map_smul, hy]
    have h1 := tailLen_le_epsI (i := i) (fixSub_ne_bot_of_smul_ne_zero (by rwa [hv]))
    have h2 := Seq.le_tailLen_append_const hν' (i := i) j
    omega
  · have hf0 : f ≠ 0 := by
      intro h0
      obtain ⟨v, hv⟩ := exists_ne (0 : N)
      exact extTensor_tmul_ne_zero (A := KLRAlgebra K Q μ) (B := KLRAlgebra K Q ν') hv
        (lMk_one_ne_zero hν') (hf (by rw [h0, LinearMap.zero_apply, map_zero]))
    exact (epsI_le_of_surjective (indAdjBwd_surjective hf0)).trans (epsI_ind_le hν' hPQ hP)

/-! ### Lemma 3.7 -/

section Lemma37

include hν' hPQ hP in
/-- **KL I, Lemma 3.7 (1)**: if `ε_i(N) = 0` then `y ↦ 1_{μ,ν'} ⊗ y` is an isomorphism
`N ⊠ L(i^n) ≅ Δ_{i^n} Ind (N ⊠ L(i^n))`. -/
theorem indUnit_bijective (hN : epsI Q μ i N = 0) :
    Function.Bijective (indAdjFwd (LinearMap.id :
      Ind Q μ ν' (ExtTensor K N (KLRRep hν' Q)) →ₗ[KLRAlgebra K Q (μ + ν')] _)) := by
  set D := indDecomp (ν := μ) (ν' := ν') hPQ hP (ExtTensor K N (KLRRep hν' Q))
  constructor
  · intro y y' h
    have h' := congrArg (fun z : ResSub Q μ ν' (Ind Q μ ν' (ExtTensor K N (KLRRep hν' Q))) => D (z : Ind Q μ ν' (ExtTensor K N (KLRRep hν' Q)))) h
    simp only [coe_indAdjFwd_apply, LinearMap.id_apply, D, indDecomp_tmul_oneConcat] at h'
    have := congrFun h' shufOne
    simpa using this
  · intro z
    have hzero : ∀ u : Shuffle (Seq.card_add' μ ν'), u ≠ shufOne →
        D (z : Ind Q μ ν' (ExtTensor K N (KLRRep hν' Q))) u = 0 := by
      intro u hu
      have hz : (z : Ind Q μ ν' (ExtTensor K N (KLRRep hν' Q))) = ∑ s ∈ concatSet μ ν',
          (e s : KLRAlgebra K Q (μ + ν')) • (z : Ind Q μ ν' (ExtTensor K N (KLRRep hν' Q))) := by
        calc (z : Ind Q μ ν' (ExtTensor K N (KLRRep hν' Q))) = oneConcat Q μ ν' • (z : Ind Q μ ν' (ExtTensor K N (KLRRep hν' Q))) := (mem_fixSub.1 z.2).symm
          _ = eSum Q (concatSet μ ν') • (z : Ind Q μ ν' (ExtTensor K N (KLRRep hν' Q))) := rfl
          _ = _ := by rw [eSum, Finset.sum_smul]
      have hsum : ∀ (t : Finset (Seq (μ + ν')))
          (g : Seq (μ + ν') → Ind Q μ ν' (ExtTensor K N (KLRRep hν' Q))),
          D (∑ s ∈ t, g s) = ∑ s ∈ t, D (g s) := fun t g => map_sum D.toLinearMap g t
      rw [hz, hsum, Finset.sum_apply]
      refine Finset.sum_eq_zero fun s hs => ?_
      rw [indDecomp_e_smul]
      by_cases hmem : u.1 • s ∈ concatSet μ ν'
      · obtain ⟨j, j', hjj⟩ := mem_concatSet.1 hmem
        rw [← hjj, concatIdem_append]
        by_cases hj : fixSub K N (e j : KLRAlgebra K Q μ) = ⊥
        · exact tmul_smul_extTensor_eq_zero (smul_eq_zero_of_fixSub_eq_bot (e_mul_self j) hj) _ _
        · exfalso
          have htj : Seq.tailLen i j = 0 := by
            have := tailLen_le_epsI (i := i) hj; omega
          exact hu (Subtype.ext (shuffle_eq_one u ((mem_concatSet_iff_hasTail hν').1 hs)
            hjj.symm htj))
      · rw [concatIdem_of_not_mem hmem, zero_smul]
    refine ⟨D (z : Ind Q μ ν' (ExtTensor K N (KLRRep hν' Q))) shufOne, Subtype.ext ?_⟩
    rw [coe_indAdjFwd_apply, LinearMap.id_apply]
    apply D.injective
    rw [indDecomp_tmul_oneConcat]
    funext u
    by_cases hu : u = shufOne
    · subst hu; rw [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hu, hzero u hu]

/-- **KL I, Lemma 3.7 (1)**: `N ⊠ L(i^n) ≅ Δ_{i^n} Ind (N ⊠ L(i^n))` if `ε_i(N) = 0`. -/
def indUnitEquiv (hN : epsI Q μ i N = 0) :
    ExtTensor K N (KLRRep hν' Q) ≃ₗ[TensorKLR Q μ ν']
      ResSub Q μ ν' (Ind Q μ ν' (ExtTensor K N (KLRRep hν' Q))) :=
  LinearEquiv.ofBijective _ (indUnit_bijective hν' hPQ hP hN)

variable [IsSimpleModule (KLRAlgebra K Q μ) N] [FiniteDimensional K N]
  (hN : epsI Q μ i N = 0)

omit [FiniteDimensional K N] in
include hPQ hP hN in
theorem isSimpleModule_resSub_ind :
    IsSimpleModule (TensorKLR Q μ ν') (ResSub Q μ ν' (Ind Q μ ν' (ExtTensor K N (KLRRep hν' Q)))) := by
  haveI := isSimpleModule_extTensor hν' (Q := Q) (μ := μ) (V := N)
  exact IsSimpleModule.congr (indUnitEquiv hν' hPQ hP hN).symm

omit [FiniteDimensional K N] in
include hPQ hP hN in
/-- **KL I, Lemma 3.7 (3)**, core: `Δ_{i^n} P = 0` for every proper submodule `P` of
`M = Ind (N ⊠ L(i^n))`. -/
theorem oneConcat_smul_eq_zero_of_ne_top
    {P' : Submodule (KLRAlgebra K Q (μ + ν')) (Ind Q μ ν' (ExtTensor K N (KLRRep hν' Q)))}
    (hP' : P' ≠ ⊤) {v : Ind Q μ ν' (ExtTensor K N (KLRRep hν' Q))} (hv : v ∈ P') :
    oneConcat Q μ ν' • v = 0 := by
  haveI := isSimpleModule_resSub_ind hν' hPQ hP hN
  let PΔ := LinearMap.range (resSubMap (μ := μ) (ν' := ν') P'.subtype)
  rcases IsSimpleOrder.eq_bot_or_eq_top PΔ with h | h
  · have hmem : (⟨oneConcat Q μ ν' • v, smul_mem_fixSub oneConcat_idem v⟩ :
        ResSub Q μ ν' (Ind Q μ ν' _)) ∈ PΔ :=
      ⟨⟨⟨oneConcat Q μ ν' • v, P'.smul_mem _ hv⟩, by
        apply Subtype.ext
        show oneConcat Q μ ν' • oneConcat Q μ ν' • v = oneConcat Q μ ν' • v
        rw [smul_smul, oneConcat_idem.eq]⟩, rfl⟩
    rw [h, Submodule.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  · exfalso
    apply hP'
    refine eq_top_of_tmul_oneConcat_mem fun y => ?_
    have hmem : indAdjFwd LinearMap.id y ∈ PΔ := h ▸ Submodule.mem_top
    obtain ⟨w, hw⟩ := hmem
    have := congrArg Subtype.val hw
    rw [coe_resSubMap, coe_indAdjFwd_apply, LinearMap.id_apply] at this
    rw [← this]
    exact (w : P').2

include hPQ hP hN in
/-- **KL I, Lemma 3.7 (2)**: `M = Ind (N ⊠ L(i^n))` (`N` irreducible, `ε_i(N) = 0`) has a unique
maximal submodule `P`, so `hd M = M/P` is irreducible, and `ε_i(M/P) = n`. -/
theorem lemma_3_7_head :
    ∃ P' : Submodule (KLRAlgebra K Q (μ + ν')) (Ind Q μ ν' (ExtTensor K N (KLRRep hν' Q))),
      IsCoatom P' ∧ (∀ P'' : Submodule (KLRAlgebra K Q (μ + ν')) _, IsCoatom P'' → P'' = P') ∧
        epsI Q (μ + ν') i (Ind Q μ ν' (ExtTensor K N (KLRRep hν' Q)) ⧸ P') = Multiset.card ν' := by
  classical
  haveI := isSimpleModule_resSub_ind hν' hPQ hP hN
  haveI := IsSimpleModule.nontrivial (TensorKLR Q μ ν') (ResSub Q μ ν' (Ind Q μ ν' (ExtTensor K N (KLRRep hν' Q))))
  obtain ⟨z, hz⟩ := exists_ne (0 : ResSub Q μ ν' (Ind Q μ ν' (ExtTensor K N (KLRRep hν' Q))))
  have hz' : (z : (Ind Q μ ν' (ExtTensor K N (KLRRep hν' Q)))) ≠ 0 := fun h => hz (Subtype.ext h)
  haveI : Nontrivial (Ind Q μ ν' (ExtTensor K N (KLRRep hν' Q))) := ⟨⟨_, 0, hz'⟩⟩
  haveI : FiniteDimensional K (Ind Q μ ν' (ExtTensor K N (KLRRep hν' Q))) := finiteDimensional_ind hPQ hP _
  haveI : Module.Finite (KLRAlgebra K Q (μ + ν')) (Ind Q μ ν' (ExtTensor K N (KLRRep hν' Q))) :=
    Module.Finite.of_restrictScalars_finite K _ _
  obtain ⟨P', hP', -⟩ := (eq_top_or_exists_le_coatom (⊥ : Submodule (KLRAlgebra K Q (μ + ν')) (Ind Q μ ν' (ExtTensor K N (KLRRep hν' Q))))).resolve_left bot_ne_top
  have hzP : ∀ {P'' : Submodule (KLRAlgebra K Q (μ + ν')) (Ind Q μ ν' (ExtTensor K N (KLRRep hν' Q)))}, P'' ≠ ⊤ → (z : (Ind Q μ ν' (ExtTensor K N (KLRRep hν' Q)))) ∉ P'' := by
    intro P'' hP'' hzP''
    apply hz'
    rw [← mem_fixSub.1 z.2]
    exact oneConcat_smul_eq_zero_of_ne_top hν' hPQ hP hN hP'' hzP''
  refine ⟨P', hP', fun P'' hP'' => ?_, ?_⟩
  · by_cases hne : P'' = P'
    · exact hne
    exfalso
    have htop := hP''.sup_eq_top_of_ne hP' hne
    have hzm : (z : (Ind Q μ ν' (ExtTensor K N (KLRRep hν' Q)))) ∈ P'' ⊔ P' := htop ▸ Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hzm
    apply hz'
    rw [← mem_fixSub.1 z.2, ← hab, smul_add,
      oneConcat_smul_eq_zero_of_ne_top hν' hPQ hP hN hP''.1 ha,
      oneConcat_smul_eq_zero_of_ne_top hν' hPQ hP hN hP'.1 hb, add_zero]
  · haveI : Nontrivial ((Ind Q μ ν' (ExtTensor K N (KLRRep hν' Q))) ⧸ P') := Submodule.Quotient.nontrivial_of_lt_top _ hP'.1.lt_top
    apply le_antisymm
    · have h1 := epsI_le_of_surjective (i := i) (P'.mkQ_surjective)
      have h2 := epsI_ind_le (i := i) (μ := μ) hν' hPQ hP (N := N)
      omega
    · refine (nontrivial_resSub_iff hν').1 ⟨⟨⟨P'.mkQ z, ?_⟩, 0, ?_⟩⟩
      · rw [mem_fixSub, ← map_smul, mem_fixSub.1 z.2]
      · intro h
        have := congrArg Subtype.val h
        simp only [ZeroMemClass.coe_zero, Submodule.mkQ_apply,
          Submodule.Quotient.mk_eq_zero] at this
        exact hzP hP'.1 this

omit [FiniteDimensional K N] in
include hPQ hP hN in
/-- **KL I, Lemma 3.7 (3)**: every nonzero subquotient `X` of the maximal submodule `P` of
`M = Ind (N ⊠ L(i^n))` (i.e. every composition factor of `M` other than `hd M`) has
`ε_i(X) < n`. -/
theorem lemma_3_7_other
    {P' : Submodule (KLRAlgebra K Q (μ + ν')) (Ind Q μ ν' (ExtTensor K N (KLRRep hν' Q)))}
    (hP' : P' ≠ ⊤) (P₁ : Submodule (KLRAlgebra K Q (μ + ν')) (Ind Q μ ν' (ExtTensor K N (KLRRep hν' Q))))
    (h₁ : P₁ ≤ P') (P₂ : Submodule (KLRAlgebra K Q (μ + ν')) P₁) [Nontrivial (P₁ ⧸ P₂)] :
    epsI Q (μ + ν') i (P₁ ⧸ P₂) < Multiset.card ν' := by
  by_contra hcon
  push_neg at hcon
  haveI := (nontrivial_resSub_iff hν' (M := P₁ ⧸ P₂)).2 hcon
  obtain ⟨z, hz⟩ := exists_ne (0 : ResSub Q μ ν' (P₁ ⧸ P₂))
  apply hz
  apply Subtype.ext
  obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ (z : P₁ ⧸ P₂)
  rw [ZeroMemClass.coe_zero, ← mem_fixSub.1 z.2, ← hw, ← Submodule.Quotient.mk_smul]
  have : oneConcat Q μ ν' • w = 0 :=
    Subtype.ext (oneConcat_smul_eq_zero_of_ne_top hν' hPQ hP hN hP' (h₁ w.2))
  rw [this, Submodule.Quotient.mk_zero]

end Lemma37

/-! ### Lemma 3.8 -/

section Lemma38

omit [DecidableEq I] in
theorem smulNilpotent_submodule {A : Type*} [Ring A] {X : Type*} [AddCommGroup X] [Module A X]
    {a : A} (S : Submodule A X) (h : SmulNilpotent a X) : SmulNilpotent a S := by
  obtain ⟨m, hm⟩ := h
  exact ⟨m, fun v => Subtype.ext (by rw [Submodule.coe_smul, hm, ZeroMemClass.coe_zero])⟩

omit [IsScalarTower K (KLRAlgebra K Q (μ + ν')) M] in
/-- Nilpotent dots on `M` give nilpotent dots on `Δ M`. -/
theorem smulNilpotent_resSub [IsScalarTower K (KLRAlgebra K Q (μ + ν')) M]
    (b : Fin (Multiset.card ν'))
    (h : SmulNilpotent (x (Seq.posR μ b) : KLRAlgebra K Q (μ + ν')) M) :
    SmulNilpotent ((1 : KLRAlgebra K Q μ) ⊗ₜ[K] x b : TensorKLR Q μ ν') (ResSub Q μ ν' M) := by
  obtain ⟨m, hm⟩ := h
  have key : ∀ (r : ℕ) (w : ResSub Q μ ν' M),
      ((((1 : KLRAlgebra K Q μ) ⊗ₜ[K] x b : TensorKLR Q μ ν') ^ r • w : ResSub Q μ ν' M) : M) =
        (x (Seq.posR μ b) : KLRAlgebra K Q (μ + ν')) ^ r • (w : M) := by
    intro r
    induction r with
    | zero => intro w; rw [pow_zero, pow_zero, one_smul, one_smul]
    | succ r ih =>
      intro w
      rw [pow_succ, mul_smul, ih, coe_resSub_smul, concat_one_tmul_x, mul_smul, mem_fixSub.1 w.2,
        ← mul_smul, ← pow_succ]
  exact ⟨m, fun w => Subtype.ext (by rw [key, hm, ZeroMemClass.coe_zero])⟩

variable [FiniteDimensional K M] [IsSimpleModule (KLRAlgebra K Q (μ + ν')) M]
  (hnil : ∀ a, SmulNilpotent (x a : KLRAlgebra K Q (μ + ν')) M)


omit [DecidableEq I] in
/-- A surjective image of a simple module is simple (or zero). -/
theorem isSimpleModule_of_surjective {A : Type*} [Ring A] {X Y : Type*} [AddCommGroup X]
    [Module A X] [AddCommGroup Y] [Module A Y] [Nontrivial Y] (hX : IsSimpleModule A X)
    (g : X →ₗ[A] Y) (hg : Function.Surjective g) : IsSimpleModule A Y := by
  have hinj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot]
    refine (IsSimpleOrder.eq_bot_or_eq_top _).resolve_right fun htop => ?_
    obtain ⟨w, hw⟩ := exists_ne (0 : Y)
    obtain ⟨z, rfl⟩ := hg w
    exact hw (LinearMap.mem_ker.1 (htop ▸ Submodule.mem_top))
  exact IsSimpleModule.congr (LinearEquiv.ofBijective g ⟨hinj, hg⟩).symm

omit [FiniteDimensional K M] in
include hν' hPQ hP in
theorem epsI_eq_zero_of_embedding [FiniteDimensional K N] [Nontrivial N]
    (hε : epsI Q (μ + ν') i M = Multiset.card ν')
    (f : ExtTensor K N (KLRRep hν' Q) →ₗ[TensorKLR Q μ ν'] ResSub Q μ ν' M)
    (hf : Function.Injective f) : epsI Q μ i N = 0 := by
  have := lemma_3_6 hν' hPQ hP f hf
  omega

include hν' hPQ hP hnil in
/-- The main step of Lemma 3.8: `Δ_{i^n} M` is irreducible if `M` is and `ε_i(M) = n`. -/
theorem isSimpleModule_resSub_of_epsI_eq (hε : epsI Q (μ + ν') i M = Multiset.card ν') :
    IsSimpleModule (TensorKLR Q μ ν') (ResSub Q μ ν' M) := by
  haveI := IsSimpleModule.nontrivial (KLRAlgebra K Q (μ + ν')) M
  have hnilΔ : ∀ b, SmulNilpotent ((1 : KLRAlgebra K Q μ) ⊗ₜ[K] x b : TensorKLR Q μ ν')
      (ResSub Q μ ν' M) := fun b => smulNilpotent_resSub b (hnil _)
  haveI : Nontrivial (ResSub Q μ ν' M) := (nontrivial_resSub_iff hν').2 hε.ge
  haveI : IsArtinian (TensorKLR Q μ ν') (ResSub Q μ ν' M) := isArtinian_of_tower K inferInstance
  haveI : IsAtomic (Submodule (TensorKLR Q μ ν') (ResSub Q μ ν' M)) :=
    isAtomic_of_orderBot_wellFounded_lt wellFounded_lt
  obtain ⟨S, hSa, -⟩ := (eq_bot_or_exists_atom_le
    (⊤ : Submodule (TensorKLR Q μ ν') (ResSub Q μ ν' M))).resolve_left top_ne_bot
  haveI : IsSimpleModule (TensorKLR Q μ ν') S := isSimpleModule_iff_isAtom.2 hSa
  haveI : FiniteDimensional K S :=
    Module.Finite.of_injective (S.subtype.restrictScalars K) Subtype.val_injective
  have hnilS := fun b => smulNilpotent_submodule S (hnilΔ b)
  haveI := isSimpleModule_hwSpace hν' hPQ hP hnilS
  haveI : Nontrivial (HWSpace Q μ ν' S) := IsSimpleModule.nontrivial (KLRAlgebra K Q μ) _
  haveI : Nontrivial S := IsSimpleModule.nontrivial (TensorKLR Q μ ν') S
  let f := S.subtype ∘ₗ (hwEquiv hν' hPQ hP hnilS).toLinearMap
  have hf : Function.Injective f :=
    Subtype.val_injective.comp (hwEquiv hν' hPQ hP hnilS).injective
  have hN0 := epsI_eq_zero_of_embedding hν' hPQ hP hε f hf
  have hf0 : f ≠ 0 := by
    intro h0
    obtain ⟨s0, hs0⟩ := exists_ne (0 : S)
    apply hs0
    have := LinearMap.congr_fun h0 ((hwEquiv hν' hPQ hP hnilS).symm s0)
    simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
      Submodule.subtype_apply, LinearMap.zero_apply] at this
    exact Subtype.ext this
  have hrg := resSubMap_surjective (μ := μ) (ν' := ν') (indAdjBwd_surjective hf0)
  exact isSimpleModule_of_surjective (isSimpleModule_resSub_ind hν' hPQ hP hN0) _ hrg

include hν' hPQ hP hnil in
/-- **KL I, Lemma 3.8** (ungraded): if `M` is irreducible (with nilpotent dots) and
`ε_i(M) = n`, then `Δ_{i^n} M` is irreducible; it is `N ⊠ L(i^n)` with `N = HW(Δ_{i^n} M)`
irreducible (`hwEquiv`) and `ε_i(N) = 0`. -/
theorem lemma_3_8 (hε : epsI Q (μ + ν') i M = Multiset.card ν') :
    IsSimpleModule (TensorKLR Q μ ν') (ResSub Q μ ν' M) ∧
      IsSimpleModule (KLRAlgebra K Q μ) (HWSpace Q μ ν' (ResSub Q μ ν' M)) ∧
        epsI Q μ i (HWSpace Q μ ν' (ResSub Q μ ν' M)) = 0 := by
  have hnilΔ : ∀ b, SmulNilpotent ((1 : KLRAlgebra K Q μ) ⊗ₜ[K] x b : TensorKLR Q μ ν')
      (ResSub Q μ ν' M) := fun b => smulNilpotent_resSub b (hnil _)
  haveI hΔ := isSimpleModule_resSub_of_epsI_eq hν' hPQ hP hnil hε
  haveI := isSimpleModule_hwSpace hν' hPQ hP hnilΔ
  haveI : Nontrivial (HWSpace Q μ ν' (ResSub Q μ ν' M)) :=
    IsSimpleModule.nontrivial (KLRAlgebra K Q μ) _
  exact ⟨hΔ, inferInstance, epsI_eq_zero_of_embedding hν' hPQ hP hε
    (hwEquiv hν' hPQ hP hnilΔ).toLinearMap (hwEquiv hν' hPQ hP hnilΔ).injective⟩

end Lemma38

end KLRAlgebra

end Categorification.KLR

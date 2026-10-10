/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicSeq
import Categorification.KLR.MackeyResRight

/-!
# `K_1` as a free module: the structure behind Kang–Kashiwara Lemma 4.8

S.-J. Kang, M. Kashiwara, *Categorification of highest weight modules via
Khovanov–Lauda–Rouquier algebras*, arXiv:1102.4677v4, §4.2, Lemma 4.8 (from KL I Prop. 2.16).

* `rfree_injective`, `rfree_span`: `R(ν + ν') 1_{ν,ν'}` is a free right `R(ν) ⊗ R(ν')`-module
  with basis `ψ(ŵ_u)` (`ψ = hflip`, `ŵ_u` the basis of KL I Prop. 2.16 for the canonical reduced
  words), i.e. every element of `R(ν + ν') 1_{ν,ν'}` is uniquely `∑_u ψ(ŵ_u) ι(t_u)`. This is
  the horizontal reflection of `KLRAlgebra.freeBasis`.
* For `ν = {i} + β` (first strand coloured `i`): `R(ν) a^Λ(x_2) R^1(β) e(i, β)` consists exactly of
  the elements `∑_u ψ(ŵ_u) ι(t_u)` with all `t_u ∈ R(i) ⊗ J`, `J` the cyclotomic ideal of `R(β)`
  (`mem_cycL1_iff`). Hence `K_1 e(i, β) ≅ ⊕_u (R(i) ⊗ R^Λ(β))` as right modules; this is KK's
  Lemma 4.8 for `K_1`.

These results use the basis theorem, so they assume (like `KLRAlgebra.freeBasis`) that `k` is a
domain and that `Q` is factorized (`Q_{ab}(u, v) = P_{ba}(u, v) P_{ab}(v, u)`, `P_{ab} ≠ 0`); for
symmetric `Q` with `Q_{ab} ≠ 0` over a domain such a factorization always exists.
-/

namespace Categorification.KLR

open Equiv MvPolynomial TypeA PolyRep
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] [IsDomain k]
  {Q : I → I → MvPolynomial (Fin 2) k} {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)

namespace KLRAlgebra

/-! ### `R(ν + ν') 1_{ν,ν'}` is a free right `R(ν) ⊗ R(ν')`-module -/

section RightFree

variable {ν ν' : Multiset I}

local notation "T" => KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν'

/-- The canonical reduced words of the shuffles. -/
noncomputable abbrev shW (u : Shuffle (Seq.card_add' ν ν')) : List ℕ := canWord _ u.1

/-- The basis element `ψ(ŵ_u) = ψ_{σ(u)^{rev}} 1_{ν,ν'}` of the right free module. -/
noncomputable def rW (u : Shuffle (Seq.card_add' ν ν')) : KLRAlgebra k Q (ν + ν') :=
  hflip (hatW shW u)

omit [IsDomain k] in
theorem rW_mul_oneConcat (u : Shuffle (Seq.card_add' ν ν')) :
    (rW u * oneConcat Q ν ν' : KLRAlgebra k Q (ν + ν')) = rW u := by
  rw [rW, hatW, hflip_mul, hflip_oneConcat_eq, mul_assoc, oneConcat_idem.eq]

omit [IsDomain k] in
/-- The identity shuffle gives `ψ(ŵ_1) = 1_{ν,ν'}`. -/
theorem rW_one : (rW (⟨1, isShuffle_one _⟩ : Shuffle (Seq.card_add' ν ν')) :
    KLRAlgebra k Q (ν + ν')) = oneConcat Q ν ν' := by
  rw [rW, hatW, shW, canWord_one, ψw_nil, mul_one, hflip_oneConcat_eq]

/-- `∑_u ψ(ŵ_u) ι(t_u)`. -/
noncomputable def rFree (t : Shuffle (Seq.card_add' ν ν') → T) : KLRAlgebra k Q (ν + ν') :=
  ∑ u, rW u * concat Q ν ν' (t u)

omit [IsDomain k] in
theorem hflip_freeMap_eq_rFree (t : Shuffle (Seq.card_add' ν ν') → T) :
    hflip ((freeMap (Q := Q) shW (Finsupp.equivFunOnFinite.symm
      (fun u => tflip Q ν ν' (t u))) : KLRAlgebra k Q (ν + ν'))) = rFree t := by
  rw [freeMap, Finsupp.linearCombination_apply, Finsupp.sum_fintype,
    Submodule.coe_sum, hflip_sum, rFree]
  · refine Finset.sum_congr rfl fun u _ => ?_
    rw [coe_tensor_smul, Finsupp.coe_equivFunOnFinite_symm, hflip_mul,
      hflip_concat_eq_tflip, tflip_tflip]
    rfl
  · intro i; exact zero_smul _ _

include hPQ hP in
/-- **Uniqueness** in the right free decomposition. -/
theorem rfree_injective {t : Shuffle (Seq.card_add' ν ν') → T} (h : rFree t = 0) :
    ∀ u, t u = 0 := by
  have hbij := freeMap_bijective (ν := ν) (ν' := ν') hPQ hP (canWord _) (canWord _) shW
    (fun a => ⟨isReduced_canWord _ a, wordProd_canWord _ a⟩)
    (fun b => ⟨isReduced_canWord _ b, wordProd_canWord _ b⟩)
    (fun u => ⟨isReduced_canWord _ u.1, wordProd_canWord _ u.1⟩)
  have h1 : ((freeMap (Q := Q) shW (Finsupp.equivFunOnFinite.symm
      (fun u => tflip Q ν ν' (t u))) : oneConcatSub (ν := ν) (ν' := ν') Q) :
        KLRAlgebra k Q (ν + ν')) = 0 := by
    rw [← hflip_hflip ((freeMap (Q := Q) shW (Finsupp.equivFunOnFinite.symm
      (fun u => tflip Q ν ν' (t u))) : oneConcatSub (ν := ν) (ν' := ν') Q) :
        KLRAlgebra k Q (ν + ν')), hflip_freeMap_eq_rFree, h, hflip_zero]
  have h0 : freeMap (Q := Q) shW (Finsupp.equivFunOnFinite.symm
      (fun u => tflip Q ν ν' (t u))) = 0 := Subtype.ext h1
  have := hbij.1 (h0.trans (map_zero _).symm)
  intro u
  have hu := congrArg (fun f => f u) this
  simp only [Finsupp.coe_equivFunOnFinite_symm, Finsupp.coe_zero, Pi.zero_apply] at hu
  rw [← tflip_tflip (t := t u), hu, map_zero]

include hPQ hP in
/-- **Existence** in the right free decomposition: `r 1_{ν,ν'} = ∑_u ψ(ŵ_u) ι(t_u)`. -/
theorem rfree_span (r : KLRAlgebra k Q (ν + ν')) :
    ∃ t : Shuffle (Seq.card_add' ν ν') → T, r * oneConcat Q ν ν' = rFree t := by
  have hbij := freeMap_bijective (ν := ν) (ν' := ν') hPQ hP (canWord _) (canWord _) shW
    (fun a => ⟨isReduced_canWord _ a, wordProd_canWord _ a⟩)
    (fun b => ⟨isReduced_canWord _ b, wordProd_canWord _ b⟩)
    (fun u => ⟨isReduced_canWord _ u.1, wordProd_canWord _ u.1⟩)
  have hmem : oneConcat Q ν ν' * hflip r ∈ oneConcatSub (ν := ν) (ν' := ν') Q :=
    mem_oneConcatSub.2 (by rw [← mul_assoc, oneConcat_idem.eq])
  obtain ⟨f, hf⟩ := hbij.2 ⟨_, hmem⟩
  refine ⟨fun u => tflip Q ν ν' (f u), ?_⟩
  rw [← hflip_freeMap_eq_rFree]
  have hf' : (Finsupp.equivFunOnFinite.symm fun u => tflip Q ν ν' (tflip Q ν ν' (f u))) = f := by
    ext u; simp
  rw [hf', hf, hflip_mul, hflip_hflip, hflip_oneConcat_eq]

omit [IsDomain k] in
theorem rFree_add (t t' : Shuffle (Seq.card_add' ν ν') → T) :
    rFree (t + t') = rFree t + rFree t' := by
  simp only [rFree, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

omit [IsDomain k] in
theorem rFree_sub (t t' : Shuffle (Seq.card_add' ν ν') → T) :
    rFree (t - t') = rFree t - rFree t' := by
  simp only [rFree, Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]

omit [IsDomain k] in
theorem rFree_zero : rFree (0 : Shuffle (Seq.card_add' ν ν') → T) = 0 := by
  simp [rFree]

omit [IsDomain k] in
theorem rFree_single_one (c : T) :
    rFree (Pi.single (⟨1, isShuffle_one _⟩ : Shuffle (Seq.card_add' ν ν')) c) = concat Q ν ν' c := by
  rw [rFree, Finset.sum_eq_single (⟨1, isShuffle_one _⟩ : Shuffle (Seq.card_add' ν ν'))]
  · rw [Pi.single_eq_same, rW_one, oneConcat_mul_concat]
  · intro u _ hu; rw [Pi.single_eq_of_ne hu, map_zero, mul_zero]
  · simp

omit [IsDomain k] in
theorem rFree_mul_oneConcat (t : Shuffle (Seq.card_add' ν ν') → T) :
    rFree t * oneConcat Q ν ν' = rFree t := by
  rw [rFree, Finset.sum_mul]
  exact Finset.sum_congr rfl fun u _ => by rw [mul_assoc, concat_mul_oneConcat]

include hPQ hP in
/-- Left multiplication preserves the shape `∑_u ψ(ŵ_u) ι(t_u)`, and keeps the `t_u` in any
left ideal of `R(ν) ⊗ R(ν')` containing them. -/
theorem exists_mul_rFree (S : Submodule k T) (hS : ∀ c : T, ∀ t ∈ S, c * t ∈ S)
    (r : KLRAlgebra k Q (ν + ν')) (t : Shuffle (Seq.card_add' ν ν') → T) :
    ∃ t' : Shuffle (Seq.card_add' ν ν') → T, r * rFree t = rFree t' ∧
      ((∀ u, t u ∈ S) → ∀ u, t' u ∈ S) := by
  choose c hc using fun u => rfree_span hPQ hP (r * rW u)
  refine ⟨fun u' => ∑ u, c u u' * t u, ?_, fun ht u' => Submodule.sum_mem _ fun u _ => hS _ _ (ht u)⟩
  have hc' : ∀ u, r * rW u = rFree (c u) := fun u => by
    rw [← hc u, mul_assoc, rW_mul_oneConcat]
  rw [rFree, Finset.mul_sum]
  simp_rw [← mul_assoc, hc', rFree, Finset.sum_mul, map_sum, Finset.mul_sum, concat_mul, mul_assoc]
  exact Finset.sum_comm

end RightFree

/-! ### The first strand: `ν = {i} + β` -/

section FirstStrand

variable (i : I) (β : Multiset I)

local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "Ri" => KLRAlgebra k Q Si
local notation "R" => KLRAlgebra k Q (Si + β)
local notation "T" => KLRAlgebra k Q Si ⊗[k] KLRAlgebra k Q β

omit [IsDomain k] in
instance seqSingleSubsingleton : Subsingleton (Seq Si) := by
  refine ⟨fun s t => Subtype.ext (funext fun a => ?_)⟩
  rw [Multiset.mem_singleton.1 (s.mem a), Multiset.mem_singleton.1 (t.mem a)]

omit [IsDomain k] in
theorem e_single (s : Seq Si) : (e s : Ri) = 1 := by
  rw [← sum_e (k := k) (Q := Q) (ν := Si)]
  exact (Finset.sum_eq_single_of_mem s (Finset.mem_univ s)
    (fun t _ ht => absurd (Subsingleton.elim t s) ht)).symm

omit [IsDomain k] in
theorem concatSet_stable {l : ℕ} (hl : 1 ≤ l) (s : Seq (Si + β)) :
    s ∈ concatSet Si β ↔
      sadj (Multiset.card (Si + β)) l • s ∈ concatSet Si β := by
  by_cases hlm : l + 1 < Multiset.card (Si + β)
  · have hl' : (l - 1) + 1 < Multiset.card β := by
      simp only [Multiset.card_add, Multiset.card_singleton] at hlm; omega
    have hsadj : ∀ (a : Seq Si) (b : Seq β),
        sadj (Multiset.card (Si + β)) l • a.append b = a.append (sadj (Multiset.card β) (l - 1) • b) := by
      intro a b
      have := Seq.sadj_smul_append_right hl' a b
      rwa [Multiset.card_singleton, show 1 + (l - 1) = l by omega] at this
    constructor
    · intro hs
      obtain ⟨a, b, rfl⟩ := mem_concatSet.1 hs
      rw [hsadj]; exact append_mem_concatSet _ _
    · intro hs
      obtain ⟨a, b, hab⟩ := mem_concatSet.1 hs
      have : s = a.append (sadj (Multiset.card β) (l - 1) • b) := by
        rw [← hsadj, hab, sadj_smul_smul]
      rw [this]; exact append_mem_concatSet _ _
  · rw [sadj_of_not_lt hlm, one_smul]

omit [IsDomain k] in
/-- `k[x_1] ⊗ R^1(β)` commutes with `1_{i, β}`. -/
theorem commute_oneConcat_subR1 {w : R} (hw : w ∈ subR1 (k := k) (Q := Q) (Si + β)) :
    w * oneConcat Q Si β = oneConcat Q Si β * w := by
  induction hw using Algebra.adjoin_induction with
  | mem y hy =>
    rcases hy with (⟨b, rfl⟩ | ⟨t, rfl⟩) | ⟨j, hj, rfl⟩
    · exact x_mul_eSum b _
    · rw [oneConcat, e_mul_eSum, eSum_mul_e]
    · exact ψ_mul_eSum_of_stable j _ (concatSet_stable i β hj)
  | algebraMap c => exact Algebra.commutes c _
  | add y z _ _ hy hz => rw [add_mul, mul_add, hy, hz]
  | mul y z _ _ hy hz => rw [mul_assoc, hz, ← mul_assoc, hy, mul_assoc]

omit [DecidableEq I] [IsDomain k] in
theorem posL_single_zero (h : 0 < Multiset.card Si) :
    Seq.posL β (⟨0, h⟩ : Fin (Multiset.card Si)) = ⟨0, by simp⟩ :=
  Fin.ext rfl

omit [DecidableEq I] [IsDomain k] in
theorem posR_single (b : Fin (Multiset.card β)) :
    Seq.posR Si b = ⟨b.val + 1, by simp only [Multiset.card_add, Multiset.card_singleton]; omega⟩ :=
  Fin.ext (by simp [Seq.posR_val, add_comm])

omit [IsDomain k] in
/-- `(k[x_1] ⊗ R^1(β)) 1_{i, β}` lies in the image of `ι : R(i) ⊗ R(β) → R(Si + β)`. -/
theorem exists_concat_of_subR1 {w : R} (hw : w ∈ subR1 (k := k) (Q := Q) (Si + β)) :
    ∃ c : T, w * oneConcat Q Si β = concat Q _ _ c := by
  induction hw using Algebra.adjoin_induction with
  | mem y hy =>
    rcases hy with (⟨⟨b, hb⟩, rfl⟩ | ⟨t, rfl⟩) | ⟨j, hj, rfl⟩
    · by_cases hb0 : b = 0
      · subst hb0
        refine ⟨x ⟨0, by simp⟩ ⊗ₜ 1, ?_⟩
        rw [concat_x_tmul_one, posL_single_zero]
      · refine ⟨1 ⊗ₜ x ⟨b - 1, by simp at hb; omega⟩, ?_⟩
        rw [concat_one_tmul_x, posR_single]
        congr 2; ext; simp; omega
    · by_cases ht : t ∈ concatSet Si β
      · obtain ⟨a, b, rfl⟩ := mem_concatSet.1 ht
        refine ⟨1 ⊗ₜ e b, ?_⟩
        rw [oneConcat, e_mul_eSum, ite_eq_left ht, ← e_single (Q := Q) i a, concat_e_tmul_e]
      · refine ⟨0, ?_⟩
        rw [oneConcat, e_mul_eSum, ite_eq_right ht, map_zero]
    · by_cases hjm : j + 1 < Multiset.card (Si + β)
      · have hj' : (j - 1) + 1 < Multiset.card β := by
          simp only [Multiset.card_add, Multiset.card_singleton] at hjm; omega
        refine ⟨1 ⊗ₜ ψ (j - 1), ?_⟩
        rw [concat_one_tmul_ψ hj', Multiset.card_singleton, show 1 + (j - 1) = j by omega]
      · refine ⟨0, ?_⟩
        rw [ψ_eq_zero j (by omega), zero_mul, map_zero]
  | algebraMap c =>
    refine ⟨algebraMap k T c, ?_⟩
    rw [Algebra.algebraMap_eq_smul_one (A := T), map_smul, concat_one, ← Algebra.smul_def]
  | add y z _ _ hy hz =>
    obtain ⟨c, hc⟩ := hy
    obtain ⟨c', hc'⟩ := hz
    exact ⟨c + c', by rw [add_mul, hc, hc', map_add]⟩
  | mul y z hy' _ hy hz =>
    obtain ⟨c, hc⟩ := hy
    obtain ⟨c', hc'⟩ := hz
    refine ⟨c * c', ?_⟩
    rw [mul_assoc, hc', ← oneConcat_mul_concat, ← mul_assoc, hc, concat_mul]

omit [IsDomain k] in
theorem oneConcat_mem_subR1 :
    (oneConcat Q Si β : R) ∈ subR1 (k := k) (Q := Q) (Si + β) :=
  Subalgebra.sum_mem _ fun t _ => e_mem_subR1 t

omit [IsDomain k] in
/-- `ι(1 ⊗ R(β)) ⊆ k[x_1] ⊗ R^1(β)`. -/
theorem concat_one_tmul_mem_subR1 (b : KLRAlgebra k Q β) :
    concat Q Si β (1 ⊗ₜ b) ∈ subR1 (k := k) (Q := Q) (Si + β) := by
  obtain ⟨w, rfl⟩ := mk_surjective b
  induction w using FreeAlgebra.induction with
  | grade0 r =>
    rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, map_smul,
      ← Algebra.TensorProduct.one_def, concat_one]
    exact Subalgebra.smul_mem _ (oneConcat_mem_subR1 i β) r
  | grade1 g =>
    cases g with
    | idem s' =>
      change concat Q Si β (1 ⊗ₜ e s') ∈ _
      rw [← e_single (Q := Q) i (Classical.arbitrary _), concat_e_tmul_e]
      exact e_mem_subR1 _
    | dot b =>
      change concat Q Si β (1 ⊗ₜ x b) ∈ _
      rw [concat_one_tmul_x]
      exact Subalgebra.mul_mem _ (x_mem_subR1 _) (oneConcat_mem_subR1 i β)
    | cross j =>
      change concat Q Si β (1 ⊗ₜ ψ j) ∈ _
      by_cases hj : j + 1 < Multiset.card β
      · rw [concat_one_tmul_ψ hj]
        exact Subalgebra.mul_mem _ (ψ_mem_subR1 (by simp)) (oneConcat_mem_subR1 i β)
      · rw [ψ_eq_zero j (by omega), TensorProduct.tmul_zero, map_zero]
        exact Subalgebra.zero_mem _
  | mul u v hu hv =>
    rw [map_mul, ← one_mul (1 : KLRAlgebra k Q Si), ← Algebra.TensorProduct.tmul_mul_tmul,
      concat_mul]
    exact Subalgebra.mul_mem _ hu hv
  | add u v hu hv =>
    rw [map_add, TensorProduct.tmul_add, map_add]
    exact Subalgebra.add_mem _ hu hv

instance seqSingleInhabited : Inhabited (Seq Si) :=
  ⟨⟨fun _ => i, by simp⟩⟩

omit [DecidableEq I] [IsDomain k] in
theorem append_single_apply_one (s₀ : Seq Si) (s : Seq β) (h1 : 1 < Multiset.card (Si + β))
    (hβ : 0 < Multiset.card β) : (s₀.append s).1 ⟨1, h1⟩ = s.1 ⟨0, hβ⟩ := by
  rw [Seq.append_apply_ge _ _ _ (by simp)]
  exact lbl_congr s (by simp)

variable (a : I → Polynomial k)

omit [IsDomain k] in
/-- `a^Λ(x_2) 1_{i, β} = ι(1 ⊗ a^Λ(x_1))`. -/
theorem cycAt_one_mul_oneConcat (h1 : 1 < Multiset.card (Si + β))
    (hβ : 0 < Multiset.card β) :
    (cycAt a ⟨1, h1⟩ * oneConcat Q Si β : R) = concat Q Si β (1 ⊗ₜ cycAt a ⟨0, hβ⟩) := by
  apply ext_e
  intro t
  have hL : (cycAt a ⟨1, h1⟩ * oneConcat Q Si β * e t : R) =
      if t ∈ concatSet Si β then cycAt a ⟨1, h1⟩ * e t else 0 := by
    rw [mul_assoc, oneConcat, eSum_mul_e]; split_ifs <;> first | rfl | exact mul_zero _
  have hR : (concat Q Si β (1 ⊗ₜ cycAt a ⟨0, hβ⟩) * e t : R) =
      if t ∈ concatSet Si β then concat Q Si β (1 ⊗ₜ cycAt a ⟨0, hβ⟩) * e t else 0 := by
    conv_lhs => rw [← concat_mul_oneConcat, mul_assoc, oneConcat, eSum_mul_e]
    split_ifs <;> first | rfl | exact mul_zero _
  rw [hL, hR]
  split_ifs with ht
  · obtain ⟨s₀, s, rfl⟩ := mem_concatSet.1 ht
    have hc : (1 ⊗ₜ cycAt a ⟨0, hβ⟩ : T) * (e s₀ ⊗ₜ e s) =
        (pol 1 * ψw [] * e s₀) ⊗ₜ
          (pol (Polynomial.aeval (X ⟨0, hβ⟩) (a (s.1 ⟨0, hβ⟩))) * ψw [] * e s) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, cycAt_mul_e]
      simp only [map_one, ψw_nil, one_mul, mul_one]
    rw [cycAt_mul_e, append_single_apply_one i β s₀ s h1 hβ, ← concat_e_tmul_e, ← concat_mul, hc,
      concat_pol_ψw_e _ _ (fun _ h => by simp at h) (fun _ h => by simp at h)]
    simp only [map_one, one_mul, rename_aeval_X, List.nil_append, shiftWord, List.map_nil,
      ψw_nil, mul_one]
    rw [show (Seq.posR Si ⟨0, hβ⟩ : Fin _) = ⟨1, h1⟩ from Fin.ext (by simp [Seq.posR_val]),
      concat_e_tmul_e]
  · rfl

/-- The cyclotomic part `R(i) ⊗ J` of `R(i) ⊗ R(β)`, `J` the cyclotomic ideal of `R(β)`. -/
noncomputable def tJ : Submodule k T :=
  Submodule.span k {t | ∃ (c : Ri) (j : KLRAlgebra k Q β), j ∈ cycIdeal Q a β ∧ t = c ⊗ₜ j}

omit [IsDomain k] in
theorem mul_mem_tJ {t : T} (ht : t ∈ tJ (Q := Q) i β a) (c : T) : c * t ∈ tJ i β a := by
  induction ht using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c₀, j, hj, rfl⟩ := hy
    induction c using TensorProduct.inductionOn with
    | tmul c₁ c₂ =>
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact Submodule.subset_span ⟨_, _, TwoSidedIdeal.mul_mem_left _ _ _ hj, rfl⟩
    | add c c' hc hc' => rw [add_mul]; exact Submodule.add_mem _ hc hc'
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
  | smul r y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hy

omit [IsDomain k] in
theorem tJ_mul_mem {t : T} (ht : t ∈ tJ (Q := Q) i β a) (c : T) : t * c ∈ tJ i β a := by
  induction ht using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c₀, j, hj, rfl⟩ := hy
    induction c using TensorProduct.inductionOn with
    | tmul c₁ c₂ =>
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact Submodule.subset_span ⟨_, _, TwoSidedIdeal.mul_mem_right _ _ _ hj, rfl⟩
    | add c c' hc hc' => rw [mul_add]; exact Submodule.add_mem _ hc hc'
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [add_mul]; exact Submodule.add_mem _ hy hz
  | smul r y _ hy => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hy

omit [IsDomain k] in
/-- `ι(R(i) ⊗ J) ⊆ R(ν) a^Λ(x_2) R^1(β)`. -/
theorem concat_mem_cycL1 (h1 : 1 < Multiset.card (Si + β)) (hβ : 0 < Multiset.card β) {t : T}
    (ht : t ∈ tJ (Q := Q) i β a) : concat Q Si β t ∈ cycL1 a h1 := by
  have key : ∀ j : KLRAlgebra k Q β, j ∈ cycIdeal Q a β →
      ∀ b' : KLRAlgebra k Q β, concat Q Si β (1 ⊗ₜ (j * b')) ∈ cycL1 a h1 := by
    intro j hj
    induction hj using TwoSidedIdeal.span_induction with
    | mem y hy =>
      obtain ⟨s, rfl⟩ := hy
      intro b'
      rw [cycElt_eq a hβ, mul_assoc, ← one_mul (1 : KLRAlgebra k Q Si),
        ← Algebra.TensorProduct.tmul_mul_tmul, concat_mul, ← cycAt_one_mul_oneConcat i β a h1 hβ,
        mul_assoc, oneConcat_mul_concat]
      exact Submodule.subset_span ⟨_, concat_one_tmul_mem_subR1 i β _, rfl⟩
    | zero => intro b'; rw [zero_mul, TensorProduct.tmul_zero, map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz =>
      intro b'; rw [add_mul, TensorProduct.tmul_add, map_add]; exact Submodule.add_mem _ (hy b') (hz b')
    | neg y _ hy =>
      intro b'; rw [neg_mul, TensorProduct.tmul_neg, map_neg]; exact Submodule.neg_mem _ (hy b')
    | left_absorb c y _ hy =>
      intro b'
      rw [mul_assoc, ← one_mul (1 : KLRAlgebra k Q Si), ← Algebra.TensorProduct.tmul_mul_tmul,
        concat_mul]
      exact Submodule.smul_mem _ _ (hy b')
    | right_absorb c y _ hy => intro b'; rw [mul_assoc]; exact hy (c * b')
  induction ht using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, j, hj, rfl⟩ := hy
    have hk := key j hj 1
    rw [mul_one] at hk
    have hcj : (c ⊗ₜ j : T) = (c ⊗ₜ 1) * (1 ⊗ₜ j) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hcj, concat_mul]
    exact Submodule.smul_mem _ _ hk
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul r y _ hy => rw [map_smul]; exact Submodule.smul_of_tower_mem _ r hy

include hPQ hP in
/-- **KK Lemma 4.8 for `K_1`** (structure): `∑_u ψ(ŵ_u) ι(t_u)` lies in
`R(ν) a^Λ(x_2) R^1(β)` exactly when every `t_u` lies in `R(i) ⊗ J`. So
`K_1 e(i, β) ≅ ⊕_u (R(i) ⊗ R(β)) / (R(i) ⊗ J) = ⊕_u R(i) ⊗ R^Λ(β)`. -/
theorem mem_cycL1_iff (h1 : 1 < Multiset.card (Si + β)) (hβ : 0 < Multiset.card β)
    (t : Shuffle (Seq.card_add' Si β) → T) :
    rFree t ∈ cycL1 a h1 ↔ ∀ u, t u ∈ tJ (Q := Q) i β a := by
  have hcyc : (1 ⊗ₜ cycAt a ⟨0, hβ⟩ : T) ∈ tJ (Q := Q) i β a :=
    Submodule.subset_span ⟨1, _, cycAt_mem_cycIdeal a hβ, rfl⟩
  constructor
  · intro ht
    have key : ∀ z ∈ cycL1 (Q := Q) a h1, ∃ t' : Shuffle (Seq.card_add' Si β) → T,
        (∀ u, t' u ∈ tJ (Q := Q) i β a) ∧ z * oneConcat Q Si β = rFree t' := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨w, hw, rfl⟩ := hy
        obtain ⟨c, hc⟩ := exists_concat_of_subR1 i β hw
        refine ⟨Pi.single ⟨1, isShuffle_one _⟩ ((1 ⊗ₜ cycAt a ⟨0, hβ⟩) * c), ?_, ?_⟩
        · intro u
          by_cases hu : u = ⟨1, isShuffle_one _⟩
          · subst hu; rw [Pi.single_eq_same]; exact tJ_mul_mem i β a hcyc c
          · rw [Pi.single_eq_of_ne hu]; exact Submodule.zero_mem _
        · rw [rFree_single_one, mul_assoc, hc, ← oneConcat_mul_concat, ← mul_assoc,
            cycAt_one_mul_oneConcat i β a h1 hβ, ← concat_mul]
      | zero => exact ⟨0, fun _ => Submodule.zero_mem _, by rw [zero_mul, rFree_zero]⟩
      | add y z _ _ hy hz =>
        obtain ⟨t₁, ht₁, hy⟩ := hy
        obtain ⟨t₂, ht₂, hz⟩ := hz
        exact ⟨t₁ + t₂, fun u => Submodule.add_mem _ (ht₁ u) (ht₂ u), by
          rw [add_mul, hy, hz, rFree_add]⟩
      | smul r y _ hy =>
        obtain ⟨t', ht', hy⟩ := hy
        obtain ⟨t'', ht'', hS⟩ := exists_mul_rFree hPQ hP (tJ (Q := Q) i β a)
          (fun c t ht => mul_mem_tJ i β a ht c) r t'
        exact ⟨t'', hS ht', by rw [smul_eq_mul, mul_assoc, hy, ht'']⟩
    obtain ⟨t', ht', heq⟩ := key _ ht
    rw [rFree_mul_oneConcat] at heq
    have h0 : rFree (t - t') = 0 := by rw [rFree_sub, heq, sub_self]
    intro u
    have := rfree_injective hPQ hP h0 u
    rw [Pi.sub_apply, sub_eq_zero] at this
    rw [this]; exact ht' u
  · intro ht
    exact Submodule.sum_mem _ fun u _ =>
      Submodule.smul_mem _ _ (concat_mem_cycL1 i β a h1 hβ (ht u))

end FirstStrand

end KLRAlgebra

end Categorification.KLR

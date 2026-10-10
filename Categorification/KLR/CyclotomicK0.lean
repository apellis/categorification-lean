/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicSplit

/-!
# The structure of `K_0`: Kang–Kashiwara Lemma 4.8 for `K_0`

S.-J. Kang, M. Kashiwara, *Categorification of highest weight modules via
Khovanov–Lauda–Rouquier algebras*, arXiv:1102.4677v4, Lemma 4.8: `K_0 = R(β + α_i) e(β, i)
⊗_{R(β)} R^Λ(β)` is a free right `R^Λ(β)[t]`-module. Here, for `ν = β + {i}` (the strand of colour
`i` last):

* `mem_cycL0_iff`: `∑_u ψ(ŵ_u) ι(t_u) ∈ R(ν) a^Λ(x_1) R(β)` exactly when every `t_u` lies in
  `J ⊗ R(i)`, `J` the cyclotomic ideal of `R(β)` (the analogue of `mem_cycL1_iff`).
* On `R({i} + β)` (where `P` and `Q` live): the coordinates `coordL : K_0 → ⊕_u R^Λ(β)[t]` and
  their inverse `embL` on `K_0 e(β, i)`, intertwining the right actions (`coordL_act0`,
  `embL_mul_C`): `K_0 e(β, i) ≅ ⊕_{shuffles} R^Λ(β)[t]` as right `R(β)`-modules.

Domain `k`, factorized `Q` (as for the basis theorem).
-/

namespace Categorification.KLR

open Equiv TypeA PolyRep
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]

namespace KLRAlgebra

variable {Q : I → I → MvPolynomial (Fin 2) k}

/-! ### The last strand: `ν = β + {i}` -/

section LastStrand

variable (i : I) (β : Multiset I)

local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "R0" => KLRAlgebra k Q (β + Si)
local notation "T0" => KLRAlgebra k Q β ⊗[k] KLRAlgebra k Q Si

theorem concatSet_stable_left {l : ℕ} (hl : l + 2 < Multiset.card (β + Si)) (s : Seq (β + Si)) :
    s ∈ concatSet β Si ↔ sadj (Multiset.card (β + Si)) l • s ∈ concatSet β Si := by
  have hl' : l + 1 < Multiset.card β := by
    simp only [Multiset.card_add, Multiset.card_singleton] at hl; omega
  constructor
  · intro hs
    obtain ⟨a, b, rfl⟩ := mem_concatSet.1 hs
    rw [Seq.sadj_smul_append_left hl']; exact append_mem_concatSet _ _
  · intro hs
    obtain ⟨a, b, hab⟩ := mem_concatSet.1 hs
    have : s = (sadj (Multiset.card β) l • a).append b := by
      rw [← Seq.sadj_smul_append_left hl', hab, sadj_smul_smul]
    rw [this]; exact append_mem_concatSet _ _

/-- `R(β) ⊗ k[x_m]` commutes with `1_{β, i}`. -/
theorem commute_oneConcat_subR0 {w : R0} (hw : w ∈ subR0 (k := k) (Q := Q) (β + Si)) :
    w * oneConcat Q β Si = oneConcat Q β Si * w := by
  induction hw using Algebra.adjoin_induction with
  | mem y hy =>
    rcases hy with (⟨b, rfl⟩ | ⟨t, rfl⟩) | ⟨j, hj, rfl⟩
    · exact x_mul_eSum b _
    · rw [oneConcat, e_mul_eSum, eSum_mul_e]
    · exact ψ_mul_eSum_of_stable j _ (concatSet_stable_left i β hj)
  | algebraMap c => exact Algebra.commutes c _
  | add y z _ _ hy hz => rw [add_mul, mul_add, hy, hz]
  | mul y z _ _ hy hz => rw [mul_assoc, hz, ← mul_assoc, hy, mul_assoc]

/-- `(R(β) ⊗ k[x_m]) 1_{β, i}` lies in the image of `ι : R(β) ⊗ R(i) → R(β + i)`. -/
theorem exists_concat_of_subR0 {w : R0} (hw : w ∈ subR0 (k := k) (Q := Q) (β + Si)) :
    ∃ c : T0, w * oneConcat Q β Si = concat Q _ _ c := by
  induction hw using Algebra.adjoin_induction with
  | mem y hy =>
    rcases hy with (⟨⟨b, hb⟩, rfl⟩ | ⟨t, rfl⟩) | ⟨j, hj, rfl⟩
    · by_cases hbn : b < Multiset.card β
      · refine ⟨x ⟨b, hbn⟩ ⊗ₜ 1, ?_⟩
        rw [concat_x_tmul_one]
        rfl
      · have hb' : b = Multiset.card β := by
          simp only [Multiset.card_add, Multiset.card_singleton] at hb; omega
        refine ⟨1 ⊗ₜ x ⟨0, by simp⟩, ?_⟩
        rw [concat_one_tmul_x]
        congr 2; ext; simp [Seq.posR_val, hb']
    · by_cases ht : t ∈ concatSet β Si
      · obtain ⟨a, b, rfl⟩ := mem_concatSet.1 ht
        refine ⟨e a ⊗ₜ 1, ?_⟩
        rw [oneConcat, e_mul_eSum, ite_eq_left ht, ← e_single (Q := Q) i b, concat_e_tmul_e]
      · refine ⟨0, ?_⟩
        rw [oneConcat, e_mul_eSum, ite_eq_right ht, map_zero]
    · have hj' : j + 1 < Multiset.card β := by
        simp only [Multiset.card_add, Multiset.card_singleton] at hj; omega
      exact ⟨ψ j ⊗ₜ 1, by rw [concat_ψ_tmul_one hj']⟩
  | algebraMap c =>
    refine ⟨algebraMap k T0 c, ?_⟩
    rw [Algebra.algebraMap_eq_smul_one (A := T0), map_smul, concat_one, ← Algebra.smul_def]
  | add y z _ _ hy hz =>
    obtain ⟨c, hc⟩ := hy
    obtain ⟨c', hc'⟩ := hz
    exact ⟨c + c', by rw [add_mul, hc, hc', map_add]⟩
  | mul y z hy' _ hy hz =>
    obtain ⟨c, hc⟩ := hy
    obtain ⟨c', hc'⟩ := hz
    refine ⟨c * c', ?_⟩
    rw [mul_assoc, hc', ← oneConcat_mul_concat, ← mul_assoc, hc, concat_mul]

/-- `ι(R(β) ⊗ R(i)) ⊆ R(β) ⊗ k[x_m]`. -/
theorem concat_mem_subR0 (t : T0) : concat Q β Si t ∈ subR0 (k := k) (Q := Q) (β + Si) := by
  induction t using TensorProduct.inductionOn with
  | add s t hs ht => rw [map_add]; exact Subalgebra.add_mem _ hs ht
  | tmul b c =>
    have hbc : (b ⊗ₜ c : T0) = (b ⊗ₜ 1) * (1 ⊗ₜ c) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hbc, concat_mul]
    clear hbc
    have hone : concat Q β Si (1 : T0) ∈ subR0 (k := k) (Q := Q) (β + Si) := by
      rw [concat_one]; exact Subalgebra.sum_mem _ fun s _ => e_mem_subR0 s
    refine Subalgebra.mul_mem _ ?_ ?_
    · induction b using klr_induction with
      | hadd u v hu hv => rw [TensorProduct.add_tmul, map_add]; exact Subalgebra.add_mem _ hu hv
      | hmul u v hu hv =>
        rw [show (u * v) ⊗ₜ (1 : KLRAlgebra k Q Si) = ((u ⊗ₜ 1) * (v ⊗ₜ 1) : T0) by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one], concat_mul]
        exact Subalgebra.mul_mem _ hu hv
      | hr r =>
        rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul', map_smul,
          ← Algebra.TensorProduct.one_def]
        exact Subalgebra.smul_mem _ hone r
      | he s =>
        rw [← e_single (Q := Q) i default, concat_e_tmul_e]; exact e_mem_subR0 _
      | hx b => rw [concat_x_tmul_one]; exact Subalgebra.mul_mem _ (x_mem_subR0 _) (by
          rw [← concat_one]; exact hone)
      | hψ j =>
        by_cases hj : j + 1 < Multiset.card β
        · rw [concat_ψ_tmul_one hj]
          exact Subalgebra.mul_mem _ (ψ_mem_subR0 (by simp; omega)) (by rw [← concat_one]; exact hone)
        · rw [ψ_eq_zero j (by omega), TensorProduct.zero_tmul, map_zero]
          exact Subalgebra.zero_mem _
    · rw [← sec_singlePoly (Q := Q) i c, sec]
      induction singlePoly Q i c using Polynomial.induction_on with
      | C r =>
        rw [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, map_smul,
          ← Algebra.TensorProduct.one_def]
        exact Subalgebra.smul_mem _ hone r
      | add p q hp hq =>
        rw [map_add, TensorProduct.tmul_add, map_add]; exact Subalgebra.add_mem _ hp hq
      | monomial n r h =>
        rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X,
          show ∀ u v : KLRAlgebra k Q Si, ((1 : KLRAlgebra k Q β) ⊗ₜ[k] (u * v) : T0) =
              ((1 : KLRAlgebra k Q β) ⊗ₜ[k] u) * ((1 : KLRAlgebra k Q β) ⊗ₜ[k] v) from
            fun u v => by rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one],
          concat_mul, concat_one_tmul_x]
        exact Subalgebra.mul_mem _ h
          (Subalgebra.mul_mem _ (x_mem_subR0 _) (by rw [← concat_one]; exact hone))

variable (a : I → Polynomial k)

/-- `a^Λ(x_1) 1_{β, i} = ι(a^Λ(x_1) ⊗ 1)`. -/
theorem cycAt_zero_mul_oneConcat (h0 : 0 < Multiset.card (β + Si))
    (hβ : 0 < Multiset.card β) :
    (cycAt a ⟨0, h0⟩ * oneConcat Q β Si : R0) = concat Q β Si (cycAt a ⟨0, hβ⟩ ⊗ₜ 1) := by
  apply ext_e
  intro t
  have hL : (cycAt a ⟨0, h0⟩ * oneConcat Q β Si * e t : R0) =
      if t ∈ concatSet β Si then cycAt a ⟨0, h0⟩ * e t else 0 := by
    rw [mul_assoc, oneConcat, eSum_mul_e]; split_ifs <;> first | rfl | exact mul_zero _
  have hR : (concat Q β Si (cycAt a ⟨0, hβ⟩ ⊗ₜ 1) * e t : R0) =
      if t ∈ concatSet β Si then concat Q β Si (cycAt a ⟨0, hβ⟩ ⊗ₜ 1) * e t else 0 := by
    conv_lhs => rw [← concat_mul_oneConcat, mul_assoc, oneConcat, eSum_mul_e]
    split_ifs <;> first | rfl | exact mul_zero _
  rw [hL, hR]
  split_ifs with ht
  · obtain ⟨s, s₀, rfl⟩ := mem_concatSet.1 ht
    have hc : (cycAt a ⟨0, hβ⟩ ⊗ₜ 1 : T0) * (e s ⊗ₜ e s₀) =
        (pol (Polynomial.aeval (MvPolynomial.X ⟨0, hβ⟩) (a (s.1 ⟨0, hβ⟩))) * ψw [] * e s) ⊗ₜ
          (pol 1 * ψw [] * e s₀) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, cycAt_mul_e]
      simp only [map_one, ψw_nil, one_mul, mul_one]
    rw [cycAt_mul_e, Seq.append_apply_lt _ _ _ (by simpa using hβ)]
    conv_rhs => rw [← concat_e_tmul_e, ← concat_mul, hc,
      concat_pol_ψw_e _ _ (fun _ h => by simp at h) (fun _ h => by simp at h)]
    simp only [map_one, mul_one, List.nil_append, shiftWord, List.map_nil, ψw_nil, rename_aeval_X]
    rfl
  · rfl

/-- The cyclotomic part `J ⊗ R(i)` of `R(β) ⊗ R(i)`. -/
noncomputable def tJ0 : Submodule k T0 :=
  Submodule.span k {t | ∃ (j : KLRAlgebra k Q β) (c : KLRAlgebra k Q Si),
    j ∈ cycIdeal Q a β ∧ t = j ⊗ₜ c}

theorem mul_mem_tJ0 {t : T0} (ht : t ∈ tJ0 (Q := Q) i β a) (c : T0) : c * t ∈ tJ0 i β a := by
  induction ht using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, c₀, hj, rfl⟩ := hy
    induction c using TensorProduct.inductionOn with
    | tmul c₁ c₂ =>
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact Submodule.subset_span ⟨_, _, TwoSidedIdeal.mul_mem_left _ _ _ hj, rfl⟩
    | add c c' hc hc' => rw [add_mul]; exact Submodule.add_mem _ hc hc'
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
  | smul r y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hy

theorem tJ0_mul_mem {t : T0} (ht : t ∈ tJ0 (Q := Q) i β a) (c : T0) : t * c ∈ tJ0 i β a := by
  induction ht using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, c₀, hj, rfl⟩ := hy
    induction c using TensorProduct.inductionOn with
    | tmul c₁ c₂ =>
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact Submodule.subset_span ⟨_, _, TwoSidedIdeal.mul_mem_right _ _ _ hj, rfl⟩
    | add c c' hc hc' => rw [mul_add]; exact Submodule.add_mem _ hc hc'
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [add_mul]; exact Submodule.add_mem _ hy hz
  | smul r y _ hy => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hy

/-- `ι(J ⊗ R(i)) ⊆ R(ν) a^Λ(x_1) R(β)`. -/
theorem concat_mem_cycL0 (h0 : 0 < Multiset.card (β + Si)) (hβ : 0 < Multiset.card β) {t : T0}
    (ht : t ∈ tJ0 (Q := Q) i β a) : concat Q β Si t ∈ cycL0 a h0 := by
  have key : ∀ j : KLRAlgebra k Q β, j ∈ cycIdeal Q a β →
      ∀ (b' : KLRAlgebra k Q β) (c : KLRAlgebra k Q Si),
        concat Q β Si ((j * b') ⊗ₜ c) ∈ cycL0 a h0 := by
    intro j hj
    induction hj using TwoSidedIdeal.span_induction with
    | mem y hy =>
      obtain ⟨s, rfl⟩ := hy
      intro b' c
      rw [cycElt_eq a hβ, mul_assoc, ← one_mul c, ← Algebra.TensorProduct.tmul_mul_tmul,
        concat_mul, ← cycAt_zero_mul_oneConcat i β a h0 hβ, mul_assoc, oneConcat_mul_concat]
      exact Submodule.subset_span ⟨_, concat_mem_subR0 i β _, rfl⟩
    | zero =>
      intro b' c; rw [zero_mul, TensorProduct.zero_tmul, map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz =>
      intro b' c; rw [add_mul, TensorProduct.add_tmul, map_add]
      exact Submodule.add_mem _ (hy b' c) (hz b' c)
    | neg y _ hy =>
      intro b' c; rw [neg_mul, TensorProduct.neg_tmul, map_neg]; exact Submodule.neg_mem _ (hy b' c)
    | left_absorb c' y _ hy =>
      intro b' c
      rw [mul_assoc, ← one_mul c, ← Algebra.TensorProduct.tmul_mul_tmul, concat_mul]
      exact Submodule.smul_mem _ _ (hy b' c)
    | right_absorb c' y _ hy => intro b' c; rw [mul_assoc]; exact hy (c' * b') c
  induction ht using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, c, hj, rfl⟩ := hy
    have hk := key j hj 1 c
    rwa [mul_one] at hk
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul r y _ hy => rw [map_smul]; exact Submodule.smul_of_tower_mem _ r hy

variable [IsDomain k] {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * MvPolynomial.rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)

include hPQ hP in
/-- **KK Lemma 4.8 for `K_0`** (structure): `∑_u ψ(ŵ_u) ι(t_u)` lies in `R(ν) a^Λ(x_1) R(β)`
exactly when every `t_u` lies in `J ⊗ R(i)`. So `K_0 e(β, i) ≅ ⊕_u R^Λ(β) ⊗ R(i)`. -/
theorem mem_cycL0_iff (h0 : 0 < Multiset.card (β + Si)) (hβ : 0 < Multiset.card β)
    (t : Shuffle (Seq.card_add' β Si) → T0) :
    rFree t ∈ cycL0 a h0 ↔ ∀ u, t u ∈ tJ0 (Q := Q) i β a := by
  have hcyc : (cycAt a ⟨0, hβ⟩ ⊗ₜ 1 : T0) ∈ tJ0 (Q := Q) i β a :=
    Submodule.subset_span ⟨_, 1, cycAt_mem_cycIdeal a hβ, rfl⟩
  constructor
  · intro ht
    have key : ∀ z ∈ cycL0 (Q := Q) a h0, ∃ t' : Shuffle (Seq.card_add' β Si) → T0,
        (∀ u, t' u ∈ tJ0 (Q := Q) i β a) ∧ z * oneConcat Q β Si = rFree t' := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨w, hw, rfl⟩ := hy
        obtain ⟨c, hc⟩ := exists_concat_of_subR0 i β hw
        refine ⟨Pi.single ⟨1, isShuffle_one _⟩ ((cycAt a ⟨0, hβ⟩ ⊗ₜ 1) * c), ?_, ?_⟩
        · intro u
          by_cases hu : u = ⟨1, isShuffle_one _⟩
          · subst hu; rw [Pi.single_eq_same]; exact tJ0_mul_mem i β a hcyc c
          · rw [Pi.single_eq_of_ne hu]; exact Submodule.zero_mem _
        · rw [rFree_single_one, mul_assoc, hc, ← oneConcat_mul_concat, ← mul_assoc,
            cycAt_zero_mul_oneConcat i β a h0 hβ, ← concat_mul]
      | zero => exact ⟨0, fun _ => Submodule.zero_mem _, by rw [zero_mul, rFree_zero]⟩
      | add y z _ _ hy hz =>
        obtain ⟨t₁, ht₁, hy⟩ := hy
        obtain ⟨t₂, ht₂, hz⟩ := hz
        exact ⟨t₁ + t₂, fun u => Submodule.add_mem _ (ht₁ u) (ht₂ u), by
          rw [add_mul, hy, hz, rFree_add]⟩
      | smul r y _ hy =>
        obtain ⟨t', ht', hy⟩ := hy
        obtain ⟨t'', ht'', hS⟩ := exists_mul_rFree hPQ hP (tJ0 (Q := Q) i β a)
          (fun c t ht => mul_mem_tJ0 i β a ht c) r t'
        exact ⟨t'', hS ht', by rw [smul_eq_mul, mul_assoc, hy, ht'']⟩
    obtain ⟨t', ht', heq⟩ := key _ ht
    rw [rFree_mul_oneConcat] at heq
    have h0' : rFree (t - t') = 0 := by rw [rFree_sub, heq, sub_self]
    intro u
    have := rfree_injective hPQ hP h0' u
    rw [Pi.sub_apply, sub_eq_zero] at this
    rw [this]; exact ht' u
  · intro ht
    exact Submodule.sum_mem _ fun u _ =>
      Submodule.smul_mem _ _ (concat_mem_cycL0 i β a h0 hβ (ht u))

end LastStrand


/-! ### Coordinates on `K_0 e(β, i)` inside `R({i} + β)` -/

section Coord

theorem rFree_smul' {ν ν' : Multiset I} (c : k)
    (t : Shuffle (Seq.card_add' ν ν') → KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν') :
    rFree (c • t) = c • rFree t := by
  simp only [rFree, Pi.smul_apply, map_smul, mul_smul_comm, Finset.smul_sum]

theorem castKLR_mem_cycL0 (a : I → Polynomial k) {μ μ' : Multiset I} (h : μ = μ')
    (h0 : 0 < Multiset.card μ) (h0' : 0 < Multiset.card μ') (z : KLRAlgebra k Q μ) :
    castKLR Q h z ∈ cycL0 a h0' ↔ z ∈ cycL0 a h0 := by
  subst h; rfl

variable [IsDomain k] {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * MvPolynomial.rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)
  (i : I) (β : Multiset I) (a : I → Polynomial k)

local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "T0" => KLRAlgebra k Q β ⊗[k] KLRAlgebra k Q Si
local notation "Rb" => KLRAlgebra k Q β
local notation "R" => KLRAlgebra k Q (Si + β)
local notation "Rl" => CycKLR k Q a β
local notation "Sh0" => Shuffle (Seq.card_add' β Si)

omit [IsDomain k] in
theorem cL_one_eq_cast : cL Q i β 1 = castKLR Q (add_comm β Si) (oneConcat Q β Si) := by
  rw [cL, concat_one_tmul_one]

omit [IsDomain k] in
theorem cL_eq_cast (b : Rb) : cL Q i β b = castKLR Q (add_comm β Si) (concat Q β Si (b ⊗ₜ 1)) :=
  rfl

omit [IsDomain k] in
theorem rFree_mul_concat' (t : Sh0 → T0) (c : T0) :
    rFree t * concat Q β Si c = rFree (fun u => t u * c) := by
  simp only [rFree, Finset.sum_mul, mul_assoc, concat_mul]

variable (Q) in
/-- The coefficients `t` of `z e(β, i) = cast(∑_u ψ(ŵ_u) ι(t_u))`. -/
noncomputable def tcoL (z : R) : Sh0 → T0 :=
  (rfree_span hPQ hP (castKLR Q (add_comm β Si).symm z)).choose

theorem tcoL_spec (z : R) :
    z * cL Q i β 1 = castKLR Q (add_comm β Si) (rFree (tcoL Q hPQ hP i β z)) := by
  rw [tcoL, ← (rfree_span hPQ hP (castKLR Q (add_comm β Si).symm z)).choose_spec, map_mul,
    castKLR_castAlg_symm, cL_one_eq_cast]

theorem tcoL_eq {z : R} {t : Sh0 → T0}
    (h : z * cL Q i β 1 = castKLR Q (add_comm β Si) (rFree t)) : tcoL Q hPQ hP i β z = t := by
  have h' : rFree (tcoL Q hPQ hP i β z) = rFree t := by
    apply (castKLR Q (add_comm β Si)).injective
    rw [← tcoL_spec, h]
  funext u
  have := rfree_injective hPQ hP (t := tcoL Q hPQ hP i β z - t)
    (by rw [rFree_sub, h', sub_self]) u
  rwa [Pi.sub_apply, sub_eq_zero] at this

variable (Q) in
/-- `R(β) ⊗ R(i) → R^Λ(β)[t]`. -/
noncomputable def thetaL0 : T0 →ₐ[k] Polynomial Rl :=
  (thetaL Q i β a).comp (Algebra.TensorProduct.comm k Rb (KLRAlgebra k Q Si)).toAlgHom

omit [IsDomain k] in
theorem thetaL0_apply (t : T0) :
    thetaL0 Q i β a t = thetaL Q i β a (Algebra.TensorProduct.comm k Rb (KLRAlgebra k Q Si) t) :=
  rfl

omit [IsDomain k] in
theorem thetaL0_tmul_one (b : Rb) :
    thetaL0 Q i β a (b ⊗ₜ 1) = Polynomial.C (CycKLR.mk k Q a β b) := by
  rw [thetaL0_apply, Algebra.TensorProduct.comm_tmul, thetaL_one_tmul]

omit [IsDomain k] in
theorem thetaL0_surjective : Function.Surjective (thetaL0 Q i β a) := fun q => by
  obtain ⟨t, ht⟩ := thetaL_surjective i β a q
  exact ⟨(Algebra.TensorProduct.comm k Rb (KLRAlgebra k Q Si)).symm t, by
    rw [thetaL0_apply, AlgEquiv.apply_symm_apply, ht]⟩

omit [IsDomain k] in
theorem comm_mem_tJ_iff (t : T0) :
    Algebra.TensorProduct.comm k Rb (KLRAlgebra k Q Si) t ∈ tJ (Q := Q) i β a ↔
      t ∈ tJ0 (Q := Q) i β a := by
  constructor
  · intro ht
    have key : ∀ y ∈ tJ (Q := Q) i β a,
        (Algebra.TensorProduct.comm k Rb (KLRAlgebra k Q Si)).symm y ∈ tJ0 (Q := Q) i β a := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨c, j, hj, rfl⟩ := hy
        exact Submodule.subset_span ⟨j, c, hj, rfl⟩
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
      | smul r y _ hy => rw [map_smul]; exact Submodule.smul_mem _ r hy
    simpa using key _ ht
  · intro ht
    induction ht using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, c, hj, rfl⟩ := hy
      exact Submodule.subset_span ⟨c, j, hj, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy => rw [map_smul]; exact Submodule.smul_mem _ r hy

omit [IsDomain k] in
theorem thetaL0_eq_zero_iff (t : T0) : thetaL0 Q i β a t = 0 ↔ t ∈ tJ0 (Q := Q) i β a := by
  rw [thetaL0_apply, thetaL_eq_zero_iff, comm_mem_tJ_iff]

variable (Q) in
/-- The coordinates of `z e(β, i)` in `⊕_u R^Λ(β)[t]`. -/
noncomputable def coordLR : R →ₗ[k] (Sh0 → Polynomial Rl) where
  toFun z u := thetaL0 Q i β a (tcoL Q hPQ hP i β z u)
  map_add' z z' := by
    have : tcoL Q hPQ hP i β (z + z') = tcoL Q hPQ hP i β z + tcoL Q hPQ hP i β z' :=
      tcoL_eq hPQ hP i β (by
        rw [add_mul, tcoL_spec hPQ hP i β z, tcoL_spec hPQ hP i β z', rFree_add, map_add])
    funext u; simp only [this, Pi.add_apply, map_add]
  map_smul' c z := by
    have : tcoL Q hPQ hP i β (c • z) = c • tcoL Q hPQ hP i β z :=
      tcoL_eq hPQ hP i β (by rw [smul_mul_assoc, tcoL_spec hPQ hP i β z, rFree_smul', map_smul])
    funext u; simp only [this, Pi.smul_apply, map_smul, RingHom.id_apply]

theorem coordLR_apply (z : R) (u : Sh0) :
    coordLR Q hPQ hP i β a z u = thetaL0 Q i β a (tcoL Q hPQ hP i β z u) := rfl

theorem coordLR_eq_zero (hβ : 0 < Multiset.card β) {z : R}
    (hz : z ∈ cycL0 a (zero_lt_card_single_add i β)) : coordLR Q hPQ hP i β a z = 0 := by
  have hz' : z * cL Q i β 1 ∈ cycL0 a (zero_lt_card_single_add i β) :=
    mul_mem_cycL0 a hz (cL_one_mem_subR0 i β)
  have h0 : 0 < Multiset.card (β + Si) := by rw [add_comm]; exact zero_lt_card_single_add i β
  rw [tcoL_spec hPQ hP i β z, castKLR_mem_cycL0 a _ h0, mem_cycL0_iff i β a hPQ hP h0 hβ] at hz'
  funext u
  exact (thetaL0_eq_zero_iff i β a _).2 (hz' u)

variable (Q) in
/-- The coordinates on `K_0`. -/
noncomputable def coordL (hβ : 0 < Multiset.card β) :
    KZero Q (Si + β) a (zero_lt_card_single_add i β) →ₗ[k] (Sh0 → Polynomial Rl) :=
  ((cycL0 a (zero_lt_card_single_add i β)).restrictScalars k).liftQ (coordLR Q hPQ hP i β a)
      (fun _ hz => LinearMap.mem_ker.2 (coordLR_eq_zero hPQ hP i β a hβ hz)) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv k (cycL0 a _)).symm.toLinearMap

theorem coordL_mk (hβ : 0 < Multiset.card β) (y : R) :
    coordL Q hPQ hP i β a hβ (Submodule.Quotient.mk y) = coordLR Q hPQ hP i β a y := rfl

variable (Q) in
/-- `(t_u)_u ↦ (θ(t_u) mod J)_u`. -/
noncomputable def thetaS0 : (Sh0 → T0) →ₗ[k] (Sh0 → Polynomial Rl) :=
  LinearMap.pi fun u => (thetaL0 Q i β a).toLinearMap ∘ₗ LinearMap.proj u

omit [IsDomain k] in
theorem thetaS0_apply (t : Sh0 → T0) (u : Sh0) : thetaS0 Q i β a t u = thetaL0 Q i β a (t u) :=
  rfl

omit [IsDomain k] in
theorem thetaS0_surjective : Function.Surjective (thetaS0 Q i β a) := fun c =>
  ⟨fun u => (thetaL0_surjective i β a (c u)).choose,
    funext fun u => (thetaL0_surjective i β a (c u)).choose_spec⟩

variable (Q) in
/-- `t ↦ cast(∑_u ψ(ŵ_u) ι(t_u))` in `K_0`. -/
noncomputable def gL : (Sh0 → T0) →ₗ[k] KZero Q (Si + β) a (zero_lt_card_single_add i β) :=
  ((cycL0 a _).mkQ.restrictScalars k) ∘ₗ (castKLR Q (add_comm β Si)).toLinearMap ∘ₗ
    { toFun := rFree, map_add' := rFree_add, map_smul' := rFree_smul' }

include hPQ hP in
theorem ker_thetaS0_le (hβ : 0 < Multiset.card β) :
    LinearMap.ker (thetaS0 Q i β a) ≤ LinearMap.ker (gL Q i β a) := by
  intro t ht
  rw [LinearMap.mem_ker] at ht ⊢
  show Submodule.Quotient.mk (castKLR Q (add_comm β Si) (rFree t)) = 0
  have h0 : 0 < Multiset.card (β + Si) := by rw [add_comm]; exact zero_lt_card_single_add i β
  rw [Submodule.Quotient.mk_eq_zero, castKLR_mem_cycL0 a _ h0, mem_cycL0_iff i β a hPQ hP h0 hβ]
  intro u
  exact (thetaL0_eq_zero_iff i β a _).1 (congrFun ht u)

variable (Q) in
/-- The inverse of the coordinates: `⊕_u R^Λ(β)[t] → K_0 e(β, i)`. -/
noncomputable def embL (hβ : 0 < Multiset.card β) :
    (Sh0 → Polynomial Rl) →ₗ[k] KZero Q (Si + β) a (zero_lt_card_single_add i β) :=
  (LinearMap.ker (thetaS0 Q i β a)).liftQ (gL Q i β a) (ker_thetaS0_le hPQ hP i β a hβ) ∘ₗ
    ((thetaS0 Q i β a).quotKerEquivOfSurjective (thetaS0_surjective i β a)).symm.toLinearMap

theorem embL_thetaS0 (hβ : 0 < Multiset.card β) (t : Sh0 → T0) :
    embL Q hPQ hP i β a hβ (thetaS0 Q i β a t) =
      Submodule.Quotient.mk (castKLR Q (add_comm β Si) (rFree t)) := by
  rw [embL, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]
  rfl

theorem embL_coordL (hβ : 0 < Multiset.card β) (y : R) :
    embL Q hPQ hP i β a hβ (coordL Q hPQ hP i β a hβ (Submodule.Quotient.mk y)) =
      Submodule.Quotient.mk (y * cL Q i β 1) := by
  rw [coordL_mk, show coordLR Q hPQ hP i β a y = thetaS0 Q i β a (tcoL Q hPQ hP i β y) from rfl,
    embL_thetaS0, ← tcoL_spec]

theorem coordL_embL (hβ : 0 < Multiset.card β) (c : Sh0 → Polynomial Rl) :
    coordL Q hPQ hP i β a hβ (embL Q hPQ hP i β a hβ c) = c := by
  obtain ⟨t, rfl⟩ := thetaS0_surjective i β a c
  rw [embL_thetaS0, coordL_mk]
  have : tcoL Q hPQ hP i β (castKLR Q (add_comm β Si) (rFree t)) = t := by
    apply tcoL_eq
    rw [cL_one_eq_cast, ← map_mul, rFree_mul_oneConcat]
  funext u
  rw [coordLR_apply, this, thetaS0_apply]

theorem coordL_act0 (hβ : 0 < Multiset.card β) (b : Rb)
    (w : KZero Q (Si + β) a (zero_lt_card_single_add i β)) :
    coordL Q hPQ hP i β a hβ (act0 Q i β a b w) =
      fun u => coordL Q hPQ hP i β a hβ w u * Polynomial.C (CycKLR.mk k Q a β b) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  have h : tcoL Q hPQ hP i β (y * cL Q i β b) =
      fun u => tcoL Q hPQ hP i β y u * (b ⊗ₜ 1) := by
    apply tcoL_eq
    rw [mul_assoc, ← cL_mul, mul_one, ← one_mul b, cL_mul, ← mul_assoc, tcoL_spec hPQ hP i β y,
      one_mul, cL_eq_cast, ← map_mul, rFree_mul_concat']
  funext u
  rw [act0_mk, coordL_mk, coordL_mk, coordLR_apply, coordLR_apply, h, map_mul, thetaL0_tmul_one]

theorem embL_mul_C (hβ : 0 < Multiset.card β) (b : Rb) (c : Sh0 → Polynomial Rl) :
    embL Q hPQ hP i β a hβ (fun u => c u * Polynomial.C (CycKLR.mk k Q a β b)) =
      act0 Q i β a b (embL Q hPQ hP i β a hβ c) := by
  obtain ⟨t, rfl⟩ := thetaS0_surjective i β a c
  have h : (fun u => thetaS0 Q i β a t u * Polynomial.C (CycKLR.mk k Q a β b)) =
      thetaS0 Q i β a (fun u => t u * (b ⊗ₜ 1)) := by
    funext u; rw [thetaS0_apply, thetaS0_apply, map_mul, thetaL0_tmul_one]
  rw [h, embL_thetaS0, embL_thetaS0, act0_mk, cL_eq_cast, ← map_mul, rFree_mul_concat']

end Coord

end KLRAlgebra

end Categorification.KLR

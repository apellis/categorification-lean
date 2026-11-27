/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PrependRedProjectiveDegree
import Categorification.WeightedKLR.RedStrands.GradedPhiLayers

/-!
# Adding a red strand identifies the standard modules in a fixed degree

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Corollary 5.23. In `T̃^λ` let `Ũ_t` be the left ideal spanned by the `e(t') a e(t)` with `t'`
strictly above `t`, so that `T̃^λ e(t) / Ũ_t` is the left standard module of `T̃^λ`. Adding a
red strand of label `λ₀` on the left does not change black counts to the left of the old red
strands and puts no black strand to the left of the new one, so it preserves Webster's order;
since in `T^{(λ₀, λ)}` only loadings beginning with `λ₀` survive, it maps `Ũ_t` onto `U_{λ₀ t}`
and `T̃^λ e(t)` onto `T^{(λ₀, λ)} e(λ₀ t)`. Being injective in a fixed degree for large `λ₀`,
it identifies the degree-`m` parts of the two standard modules.

## Main definitions

* `tildeLeftUpper`: the left ideal `Ũ_t` of `T̃^λ`.
* `tildeStdGradedRank`: the dimension of the degree-`m` part of `T̃^λ e(t) / Ũ_t`.

## Main results

* `stendhalLT_prependRedLoading_iff`: adding the red strand preserves Webster's order.
* `Graded.finrank_inf_grade_eq_of_map_eq`: a degree-preserving map that is injective in degree
  `n` and maps a homogeneous subspace onto another identifies their degree-`n` parts.
* `tildeStdGradedRank_eq`: `dim (S̃_t)_m = dim (S_{λ₀ t})_m` for large `λ₀`.
-/

noncomputable section

namespace Categorification.Graded

open DirectSum _root_.Module

variable {k B C : Type*} [Field k] [AddCommGroup B] [Module k B] [AddCommGroup C] [Module k C]
  {ℬ : ℤ → Submodule k B} {𝒞 : ℤ → Submodule k C} [Decomposition ℬ] [Decomposition 𝒞]

/-- A degree-preserving map that is injective on degree `n` and maps a homogeneous subspace
`X` onto `Y` identifies `X_n` with `Y_n`. -/
theorem finrank_inf_grade_eq_of_map_eq {f : B →ₗ[k] C} (hf : PreservesGrading ℬ 𝒞 f) {n : ℤ}
    (hinj : Set.InjOn f (ℬ n)) {X : Submodule k B} {Y : Submodule k C}
    (hX : IsHomogeneousSubspace ℬ X) (hXY : X.map f = Y) :
    finrank k (X ⊓ ℬ n :) = finrank k (Y ⊓ 𝒞 n :) := by
  classical
  have hmaps : ∀ x : (X ⊓ ℬ n :), f x ∈ Y ⊓ 𝒞 n := fun x =>
    ⟨hXY ▸ Submodule.mem_map_of_mem x.2.1, hf x.2.2⟩
  let φ : (X ⊓ ℬ n :) →ₗ[k] (Y ⊓ 𝒞 n :) := (f.domRestrict _).codRestrict _ hmaps
  have hinj' : Function.Injective φ := fun x y h =>
    Subtype.ext (hinj x.2.2 y.2.2 (congrArg Subtype.val h))
  have hsurj : Function.Surjective φ := by
    rintro ⟨y, hy1, hy2⟩
    rw [← hXY] at hy1
    obtain ⟨x, hx, rfl⟩ := hy1
    refine ⟨⟨decompose ℬ x n, hX n x hx, (decompose ℬ x n).2⟩, Subtype.ext ?_⟩
    change f (decompose ℬ x n) = f x
    rw [← decompose_map hf, decompose_of_mem_same _ hy2]
  exact (LinearEquiv.ofBijective φ ⟨hinj', hsurj⟩).finrank_eq

section Algebra

variable {A : Type*} [Ring A] [Algebra k A] (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜]

/-- Left multiplication by a degree-zero element commutes with taking components. -/
theorem decompose_mul_of_mem_zero_left {e : A} (he : e ∈ 𝒜 0) (x : A) (n : ℤ) :
    (decompose 𝒜 (e * x) n : A) = e * decompose 𝒜 x n := by
  have hμ : ∀ m, ∀ y ∈ 𝒜 m, LinearMap.mulLeft k e y ∈ 𝒜 (m + 0) := fun m y hy => by
    rw [add_zero, LinearMap.mulLeft_apply]
    simpa using SetLike.GradedMul.mul_mem he hy
  have h := decompose_map_of_shift hμ x n
  rw [LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, sub_zero] at h
  exact h

/-- Right multiplication by a degree-zero element commutes with taking components. -/
theorem decompose_mul_of_mem_zero_right {e : A} (he : e ∈ 𝒜 0) (x : A) (n : ℤ) :
    (decompose 𝒜 (x * e) n : A) = decompose 𝒜 x n * e := by
  have hμ : ∀ m, ∀ y ∈ 𝒜 m, LinearMap.mulRight k e y ∈ 𝒜 (m + 0) := fun m y hy => by
    rw [LinearMap.mulRight_apply]
    exact SetLike.GradedMul.mul_mem hy he
  have h := decompose_map_of_shift hμ x n
  rw [LinearMap.mulRight_apply, LinearMap.mulRight_apply, sub_zero] at h
  exact h

/-- The left ideal `A e` of a degree-zero element is homogeneous. -/
theorem isHomogeneousSubspace_lIdeal_of_mem_zero {e : A} (he : e ∈ 𝒜 0) :
    IsHomogeneousSubspace 𝒜 ((lIdeal e).restrictScalars k) := by
  intro n x hx
  change _ * _ = _
  have hx' : x * e = x := hx
  rw [← decompose_mul_of_mem_zero_right 𝒜 he, hx']

end Algebra

end Categorification.Graded

namespace Categorification.Stendhal

open KLR DirectSum _root_.Categorification.Graded _root_.Module

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Order

variable {I : Type*} [DecidableEq I] {ℓ : ℕ} {ν : Multiset I}

omit [DecidableEq I] in
private theorem firstPosition_lt (a : Fin (Multiset.card (stendhalWeight (ℓ + 1) ν))) :
    ¬ a < firstPosition ℓ ν := by
  intro h
  exact Nat.not_lt_zero _ (show a.val < 0 from h)

theorem blackCount_prependRedLoading_zero (s : Seq (stendhalWeight ℓ ν)) (i : I) :
    blackCount (prependRedLoading s) 0 i = 0 := by
  rw [blackCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro a - ⟨-, h⟩
  exact firstPosition_lt a (h _ (prependRedLoading_head s))

theorem blackCount_prependRedLoading_succ (s : Seq (stendhalWeight ℓ ν)) (r : Fin ℓ) (i : I) :
    blackCount (prependRedLoading s) r.succ i = blackCount s r i := by
  have hlt : ∀ a b : Fin (Multiset.card (stendhalWeight ℓ ν)),
      prependRedPosition a < prependRedPosition b ↔ a < b := fun a b => by
    rw [Fin.lt_def, Fin.lt_def, prependRedPosition_val, prependRedPosition_val]
    omega
  have hred : ∀ b : Fin (Multiset.card (stendhalWeight ℓ ν)),
      (prependRedLoading s).lbl (prependRedPosition b) = .inr r.succ ↔ s.lbl b = .inr r := by
    intro b
    rw [prependRedLoading_lbl]
    constructor
    · intro h
      obtain ⟨q, hq, hqr⟩ := prependRedColor_eq_inr h
      rw [hq, Fin.succ_injective _ hqr]
    · intro h
      rw [h]
      rfl
  symm
  refine Finset.card_bij (fun a _ => prependRedPosition a) ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    refine ⟨by rw [prependRedLoading_lbl, ha.1]; rfl, fun b hb => ?_⟩
    rcases eq_firstPosition_or b with rfl | ⟨b', rfl⟩
    · rw [prependRedLoading_head] at hb
      exact absurd (Sum.inr.inj hb) (Fin.succ_ne_zero r).symm
    · exact (hlt a b').2 (ha.2 b' ((hred b').1 hb))
  · intro a _ b _ h
    exact Fin.ext (by simpa using congrArg Fin.val h)
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    rcases eq_firstPosition_or b with rfl | ⟨a, rfl⟩
    · rw [prependRedLoading_head] at hb
      exact absurd hb.1 (by simp)
    · refine ⟨a, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have h1 := hb.1
      rw [prependRedLoading_lbl] at h1
      refine ⟨?_, fun b' hb' => (hlt a b').1 (hb.2 _ ((hred b').2 hb'))⟩
      cases hc : s.lbl a with
      | inl j => rw [hc] at h1; exact congrArg Sum.inl (Sum.inl.inj h1)
      | inr q => rw [hc] at h1; cases h1

theorem stendhalLE_prependRedLoading_iff (s t : Seq (stendhalWeight ℓ ν)) :
    StendhalLE (prependRedLoading s) (prependRedLoading t) ↔ StendhalLE s t := by
  constructor
  · intro h r i
    have := h r.succ i
    rwa [blackCount_prependRedLoading_succ, blackCount_prependRedLoading_succ] at this
  · intro h r i
    refine Fin.cases ?_ (fun r => ?_) r
    · rw [blackCount_prependRedLoading_zero, blackCount_prependRedLoading_zero]
    · rw [blackCount_prependRedLoading_succ, blackCount_prependRedLoading_succ]
      exact h r i

/-- **Adding a red strand on the left preserves Webster's order.** -/
theorem stendhalLT_prependRedLoading_iff (s t : Seq (stendhalWeight ℓ ν)) :
    StendhalLT (prependRedLoading s) (prependRedLoading t) ↔ StendhalLT s t := by
  rw [StendhalLT, StendhalLT, stendhalLE_prependRedLoading_iff, stendhalLE_prependRedLoading_iff]

end Order

section Upper

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}

variable (Q : I → I → MvPolynomial (Fin 2) k) {ℓ' : ℕ} (Λ' : Fin ℓ' → I →₀ ℕ) (ν : Multiset I)

/-- **The left ideal `Ũ_t` of `T̃^λ`**: spanned by the `e(t') a e(t)` with `t'` strictly above
`t`. The quotient `T̃^λ e(t) / Ũ_t` is the left standard module of `T̃^λ` (Webster,
arXiv:1309.3796v3, Definition 5.1, left form). -/
def tildeLeftUpper (t : Seq (stendhalWeight ℓ' ν)) (ht : IsRedOrdered t) :
    Submodule (StendhalAlgebra k Q Λ' ν) (StendhalAlgebra k Q Λ' ν) :=
  Submodule.span _
    {z | ∃ (t' : Seq (stendhalWeight ℓ' ν)) (ht' : IsRedOrdered t')
      (a : StendhalAlgebra k Q Λ' ν), StendhalLT t t' ∧
        z = StendhalAlgebra.e t' ht' * a * StendhalAlgebra.e t ht}

end Upper

section Compare

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I)
  (G : KLR.GradingDatum (stendhalQ Q Λ))

local notation "μ" => stendhalWeight ℓ ν
local notation "G₀" => restrictFirstRedGrading Q Λ G
local notation "T̃" => StendhalAlgebra k Q (Λ ∘ Fin.succ) ν

/-- `Ũ_t` is homogeneous. -/
theorem isHomogeneousSubspace_tildeLeftUpper (t : Seq μ) (ht : IsRedOrdered t) :
    IsHomogeneousSubspace (stendhalGrade G₀ ν)
      ((tildeLeftUpper Q (Λ ∘ Fin.succ) ν t ht).restrictScalars k) := by
  refine isHomogeneousSubspace_span (stendhalGrade G₀ ν) ?_
  rintro _ ⟨t', ht', a, hlt, rfl⟩ n
  rw [decompose_mul_of_mem_zero_right _ (e_mem_stendhalGrade G₀ ν t ht),
    decompose_mul_of_mem_zero_left _ (e_mem_stendhalGrade G₀ ν t' ht')]
  exact Submodule.subset_span ⟨t', ht', _, hlt, rfl⟩

/-- In `T^{(λ₀, λ)}` the idempotent of a loading not beginning with `λ₀` vanishes. -/
theorem seqIdem_eq_zero_of_not_prepend (t : Seq (stendhalWeight (ℓ + 1) ν))
    (ht : IsRedOrdered t) (hne : ∀ s, prependRedLoading s ≠ t) : seqIdem Q Λ t ht = 0 := by
  have h := orderedQuotient_e_eq_zero Q Λ ν t hne
  rw [orderedQuotient_e] at h
  simpa [ht] using h

/-- Adding the red strand maps `T̃^λ e(t)` onto `T^{(λ₀, λ)} e(λ₀ t)`. -/
theorem map_lIdeal_prependRed (t : Seq μ) (ht : IsRedOrdered t) :
    ((lIdeal (StendhalAlgebra.e t ht)).restrictScalars k).map
        ((prependRed Q Λ ν).toLinearMap.restrictScalars k) =
      (lIdeal (seqIdem Q Λ (prependRedLoading t)
        ((prependRedLoading_ordered_iff t).2 ht))).restrictScalars k := by
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    change _ * _ = _
    rw [← prependRed_e Q Λ ν t ht]
    exact (map_mul (prependRed Q Λ ν) _ _).symm.trans (congrArg _ hy)
  · intro y hy
    obtain ⟨z, rfl⟩ := prependRed_surjective Q Λ ν y
    refine ⟨z * StendhalAlgebra.e t ht, ?_, ?_⟩
    · change _ * _ = _
      rw [mul_assoc, stendhalAlgebra_e_mul_self]
    · change prependRed Q Λ ν (z * _) = _
      rw [map_mul, prependRed_e Q Λ ν t ht]
      exact hy

/-- Adding the red strand maps `Ũ_t` onto `U_{λ₀ t}`. -/
theorem map_tildeLeftUpper_prependRed (t : Seq μ) (ht : IsRedOrdered t) :
    ((tildeLeftUpper Q (Λ ∘ Fin.succ) ν t ht).restrictScalars k).map
        ((prependRed Q Λ ν).toLinearMap.restrictScalars k) =
      (leftUpper Q Λ (prependRedLoading t)
        ((prependRedLoading_ordered_iff t).2 ht)).restrictScalars k := by
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    change prependRed Q Λ ν y ∈ leftUpper Q Λ _ _
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨t', ht', a, hlt, rfl⟩ := hz
      rw [map_mul, map_mul, prependRed_e Q Λ ν t ht, prependRed_e Q Λ ν t' ht']
      exact Submodule.subset_span ⟨_, _, _, (stendhalLT_prependRedLoading_iff t t').2 hlt, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul b x _ hx =>
      rw [smul_eq_mul, map_mul]
      exact Submodule.smul_mem _ _ hx
  · intro y hy
    change y ∈ leftUpper Q Λ _ _ at hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨t'', ht'', a, hlt, rfl⟩ := hz
      by_cases hpre : ∃ t', prependRedLoading t' = t''
      · obtain ⟨t', rfl⟩ := hpre
        have ht' := (prependRedLoading_ordered_iff t').1 ht''
        obtain ⟨b, rfl⟩ := prependRed_surjective Q Λ ν a
        refine ⟨StendhalAlgebra.e t' ht' * b * StendhalAlgebra.e t ht,
          Submodule.subset_span ⟨t', ht', b, (stendhalLT_prependRedLoading_iff t t').1 hlt, rfl⟩,
          ?_⟩
        change prependRed Q Λ ν (_ * _ * _) = _
        rw [map_mul, map_mul, prependRed_e Q Λ ν t ht, prependRed_e Q Λ ν t' ht']
      · push Not at hpre
        rw [seqIdem_eq_zero_of_not_prepend Q Λ ν t'' ht'' hpre, zero_mul, zero_mul]
        exact zero_mem _
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul b x _ hx =>
      obtain ⟨z, hz, rfl⟩ := hx
      obtain ⟨c, rfl⟩ := prependRed_surjective Q Λ ν b
      refine ⟨c * z, Submodule.smul_mem _ c hz, ?_⟩
      change prependRed Q Λ ν (c * z) = _
      rw [map_mul]
      rfl

/-- The dimension of the degree-`m` part of the left standard module `T̃^λ e(t) / Ũ_t` of
`T̃^λ`: `dim (T̃^λ e(t))_m - dim (Ũ_t)_m` (both subspaces are homogeneous). -/
def tildeStdGradedRank (G' : KLR.GradingDatum (stendhalQ Q (Λ ∘ Fin.succ))) (t : Seq μ)
    (ht : IsRedOrdered t) (m : ℤ) : ℕ :=
  finrank k ((lIdeal (StendhalAlgebra.e t ht)).restrictScalars k ⊓ stendhalGrade G' ν m :) -
    finrank k ((tildeLeftUpper Q (Λ ∘ Fin.succ) ν t ht).restrictScalars k ⊓
      stendhalGrade G' ν m :)

/-- **The standard modules agree in a fixed degree** (Webster, arXiv:1309.3796v3, proof of
Corollary 5.23). If the grading of all red orders of `T̃^λ` vanishes below `-c` and
`⟨α_i^∨, λ₀⟩ · deg x_i > m + 2c` for every black label `i`, then `T̃^λ e(t) / Ũ_t` and
`S_{λ₀ t}` have the same dimension in degree `m`. -/
theorem tildeStdGradedRank_eq {c m : ℤ} (hc : ∀ m' < -c, allOrdersGrade G₀ ν m' = ⊥)
    (hΛ : ∀ i ∈ ν, m + 2 * c < Λ 0 i * G.degX (.inl i)) (t : Seq μ) (ht : IsRedOrdered t) :
    tildeStdGradedRank Q Λ ν G₀ t ht m =
      stdGradedRank G (prependRedLoading t) ((prependRedLoading_ordered_iff t).2 ht) m := by
  have hgr : PreservesGrading (stendhalGrade G₀ ν) (tensorProductGrade G ν)
      ((prependRed Q Λ ν).toLinearMap.restrictScalars k) :=
    fun _ _ hx => prependRed_mem_grade Q Λ ν G hx
  have hinj : Set.InjOn ((prependRed Q Λ ν).toLinearMap.restrictScalars k)
      (stendhalGrade G₀ ν m) := prependRed_injOn_degree Q Λ ν G₀ hc hΛ
  rw [tildeStdGradedRank, stdGradedRank,
    finrank_inf_grade_eq_of_map_eq hgr hinj
      (isHomogeneousSubspace_lIdeal_of_mem_zero _ (e_mem_stendhalGrade G₀ ν t ht))
      (map_lIdeal_prependRed Q Λ ν t ht),
    finrank_inf_grade_eq_of_map_eq hgr hinj (isHomogeneousSubspace_tildeLeftUpper Q Λ ν G t ht)
      (map_tildeLeftUpper_prependRed Q Λ ν t ht)]

end Compare

end Categorification.Stendhal

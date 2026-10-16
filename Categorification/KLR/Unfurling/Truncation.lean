/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.Completion
import Categorification.KLR.Spanning
import Categorification.TypeA.Length

/-!
# Evaluating the graded completion where the dots are nilpotent

Webster (arXiv:1603.06311v3, §3.2 and the proof of Lemma label `lem:many-sl2`) lets the
completion `R̂(ν)` act on categorical representations in which the dots act nilpotently:
modulo any power of the dots, a formal sum of homogeneous components is a finite sum. This
file proves the algebraic form of that statement.

If an algebra map `φ : R(ν) → B` kills a power `x_a^M` of every dot, then it kills every
homogeneous element of degree at least an explicit bound `truncBound`
(`map_eq_zero_of_mem_grade`): by KL I, Theorem 2.5 (spanning), such an element is a
combination of elements `ψ_w x^u e_i` of the same degree, and a large degree forces some
exponent `u_a ≥ M`. Consequently `φ` extends to the completion
(`completionLift`): a series `∑_d f_d` is sent to the finite sum `∑_{d < D} φ(f_d)`. The
extension is an algebra map and agrees with `φ` on `R(ν)`.

Only the finitely many labels occurring in `ν` matter, so the index set `I` may be infinite.
Nothing else about the grading is used; in particular the dots need not have positive degree.

## Main definitions and results

* `KLR.GradingDatum.truncBound` : the degree bound.
* `KLR.GradingDatum.map_eq_zero_of_mem_grade` : `φ` kills the homogeneous elements of degree
  `≥ truncBound`.
* `KLR.GradingDatum.completionLift` : the extension `R̂(ν) → B`, an algebra map.
* `KLR.GradingDatum.completionLift_toCompletion` : it extends `φ`.
-/

open Finset MvPolynomial Equiv

namespace Categorification.KLR

open KLRAlgebra HahnSeries TypeA

variable {I : Type*} {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k}

namespace GradingDatum

variable (G : GradingDatum Q) {ν : Multiset I}

local notation "m" => Multiset.card ν

/-- A chosen reduced word for every permutation. -/
noncomputable def redWord (n : ℕ) (w : Perm (Fin n)) : List ℕ := (exists_reduced n w).choose

theorem redWord_spec (n : ℕ) (w : Perm (Fin n)) :
    TypeA.IsReduced n (redWord n w) ∧ wordProd n (redWord n w) = w :=
  (exists_reduced n w).choose_spec

variable [DecidableEq I]

variable (ν) in
/-- A bound for the absolute values of the degrees of crossings between labels of `ν`. -/
def degΨAbs : ℤ := ∑ a ∈ ν.toFinset, ∑ b ∈ ν.toFinset, |G.degΨ a b|

variable (ν) in
/-- A bound for the absolute values of the degrees of dots with labels in `ν`. -/
def degXAbs : ℤ := ∑ a ∈ ν.toFinset, |G.degX a|

theorem degΨ_le {a b : I} (ha : a ∈ ν) (hb : b ∈ ν) : G.degΨ a b ≤ G.degΨAbs ν :=
  (le_abs_self _).trans <| (Finset.single_le_sum (f := fun b => |G.degΨ a b|)
    (fun _ _ => abs_nonneg _) (Multiset.mem_toFinset.2 hb)).trans <|
    Finset.single_le_sum (f := fun a => ∑ b ∈ ν.toFinset, |G.degΨ a b|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Multiset.mem_toFinset.2 ha)

theorem degΨAbs_nonneg : 0 ≤ G.degΨAbs ν :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem degX_le {a : I} (ha : a ∈ ν) : G.degX a ≤ G.degXAbs ν :=
  (le_abs_self _).trans <| Finset.single_le_sum (f := fun a => |G.degX a|)
    (fun _ _ => abs_nonneg _) (Multiset.mem_toFinset.2 ha)

theorem degXAbs_nonneg : 0 ≤ G.degXAbs ν := Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem dψ_le (j : ℕ) (i : Seq ν) : G.dψ j i ≤ G.degΨAbs ν := by
  unfold dψ
  split_ifs
  · exact G.degΨ_le (i.mem _) (i.mem _)
  · exact G.degΨAbs_nonneg

theorem degW_le (ρ : List ℕ) (i : Seq ν) : G.degW ρ i ≤ ρ.length * G.degΨAbs ν := by
  induction ρ with
  | nil => simp [degW]
  | cons j ρ ih =>
    rw [degW, List.length_cons, Nat.cast_succ, add_mul, one_mul, add_comm (_ * _)]
    exact add_le_add (G.dψ_le _ _) ih

/-- The maximal length of the chosen reduced words. -/
noncomputable def redLen (n : ℕ) : ℕ := univ.sup fun w : Perm (Fin n) => (redWord n w).length

variable (ν) in
/-- The degree bound: homogeneous elements of degree `≥ truncBound ν M` lie in the span of
the `ψ_w x^u e_i` with some `u_a ≥ M`. -/
noncomputable def truncBound (M : ℕ) : ℤ :=
  redLen m * G.degΨAbs ν + m * M * G.degXAbs ν + 1

theorem weight_le_of_lt {u : Fin m →₀ ℕ} {M : ℕ} (hu : ∀ a, u a < M) (i : Seq ν) :
    Finsupp.weight (fun a => G.degX (i.lbl a)) u ≤ m * M * G.degXAbs ν := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  calc ∑ a, u a • G.degX (i.lbl a) ≤ ∑ _a : Fin m, (M : ℤ) * G.degXAbs ν := by
        refine Finset.sum_le_sum fun a _ => ?_
        rw [nsmul_eq_mul]
        calc (u a : ℤ) * G.degX (i.lbl a) ≤ u a * G.degXAbs ν :=
              mul_le_mul_of_nonneg_left (G.degX_le (i.mem a)) (Nat.cast_nonneg _)
          _ ≤ M * G.degXAbs ν :=
              mul_le_mul_of_nonneg_right (by exact_mod_cast (hu a).le) G.degXAbs_nonneg
    _ = m * M * G.degXAbs ν := by
        rw [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]

variable {B : Type*} [Ring B] [Algebra k B]

/-- If `φ` kills `x_a^M` for every `a`, it kills every `ψ_w x^u e_i` with some `u_a ≥ M`. -/
theorem map_stdElt_eq_zero (φ : KLRAlgebra k Q ν →ₐ[k] B) {M : ℕ}
    (hφ : ∀ a : Fin m, φ (pol (X a ^ M)) = 0) (ρ : List ℕ) (i : Seq ν)
    {u : Fin m →₀ ℕ} {a : Fin m} (ha : M ≤ u a) :
    φ (ψw ρ * pol (monomial u 1) * e i) = 0 := by
  have hu : monomial u (1 : k) = monomial (u - Finsupp.single a M) 1 * X a ^ M := by
    rw [X_pow_eq_monomial, monomial_mul_monomial, one_mul,
      tsub_add_cancel_of_le (Finsupp.single_le_iff.2 ha)]
  rw [hu, map_mul, map_mul, map_mul, map_mul, hφ]; simp

/-- **Degree bound.** If `φ` kills a power `x_a^M` of every dot, it kills every homogeneous
element of degree at least `truncBound ν M`. -/
theorem map_eq_zero_of_mem_grade (φ : KLRAlgebra k Q ν →ₐ[k] B) {M : ℕ}
    (hφ : ∀ a : Fin m, φ (pol (X a ^ M)) = 0) {d : ℤ} (hd : G.truncBound ν M ≤ d)
    {r : KLRAlgebra k Q ν} (hr : r ∈ G.grade ν d) : φ r = 0 := by
  classical
  -- the degree `d` projection
  let π : KLRAlgebra k Q ν →ₗ[k] KLRAlgebra k Q ν :=
    { toFun := fun s => (G.coaction s).coeff d
      map_add' := fun s t => by rw [map_add]; rfl
      map_smul' := fun c s => by rw [map_smul]; rfl }
  have hπ : ∀ s : KLRAlgebra k Q ν, ∀ d' : ℤ, s ∈ G.grade ν d' →
      π s = if d' = d then s else 0 := fun s d' hs => by
    change (G.coaction s).coeff d = _
    rw [CoactionGrading.apply_of_mem_grade _ hs]
  have hr' : π r = r := by simp [hπ r d hr]
  have hspan := span_eq_top' (k := k) (Q := Q) (ν := ν) (redWord m) (redWord_spec m)
  have hmem : r ∈ Submodule.span k {r : KLRAlgebra k Q ν | ∃ (w : Perm (Fin m))
      (u : Fin m →₀ ℕ) (i : Seq ν), ψw (redWord m w) * pol (monomial u 1) * e i = r} := by
    rw [hspan]; exact Submodule.mem_top
  rw [← hr']
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hmem
  · rintro _ ⟨w, u, i, rfl⟩
    rw [hπ _ _ (G.ψw_mul_pol_monomial_mul_e_mem_grade _ u i)]
    split_ifs with hdeg
    · by_cases hu : ∀ a, u a < M
      · exfalso
        have h1 := G.degW_le (redWord m w) i
        have h2 := G.weight_le_of_lt hu i
        have h3 : ((redWord m w).length : ℤ) * G.degΨAbs ν ≤ redLen m * G.degΨAbs ν :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.le_sup (f := fun w :
            Perm (Fin m) => (redWord m w).length) (mem_univ w)) G.degΨAbs_nonneg
        unfold truncBound at hd
        omega
      · simp only [not_forall, not_lt] at hu
        obtain ⟨a, ha⟩ := hu
        exact map_stdElt_eq_zero φ hφ _ i ha
    · exact map_zero φ
  · rw [map_zero, map_zero]
  · intro x y _ _ hx hy; rw [map_add, map_add, hx, hy, add_zero]
  · intro c x _ hx; rw [map_smul, map_smul, hx, smul_zero]

/-! ### The extension to the completion -/

variable (φ : KLRAlgebra k Q ν →ₐ[k] B) (D : ℤ)

/-- The truncated sum `∑_{b ≤ d < D} φ(f_d)`. -/
noncomputable def truncSum (b : ℤ) (f : HahnSeries ℤ (KLRAlgebra k Q ν)) : B :=
  ∑ d ∈ Ico b D, φ (f.coeff d)

/-- The truncated sum does not depend on the lower limit below the support. -/
theorem truncSum_eq_of_le {b b' : ℤ} (hbb' : b' ≤ b) {f : HahnSeries ℤ (KLRAlgebra k Q ν)}
    (hf : ∀ d < b, f.coeff d = 0) : truncSum φ D b' f = truncSum φ D b f := by
  unfold truncSum
  refine (Finset.sum_subset (fun d hd => ?_) fun d hd hdn => ?_).symm
  · rw [mem_Ico] at hd ⊢; omega
  · rw [mem_Ico] at hd hdn
    rw [hf d (by omega), map_zero]

theorem coeff_eq_zero_of_lt_order' (f : HahnSeries ℤ (KLRAlgebra k Q ν)) :
    ∀ d < f.order, f.coeff d = 0 := fun _ hd => coeff_eq_zero_of_lt_order hd

variable {M : ℕ}

theorem truncBound_pos : 0 < G.truncBound ν M := by
  have := G.degΨAbs_nonneg (ν := ν); have := G.degXAbs_nonneg (ν := ν)
  unfold truncBound
  positivity

theorem order_le_of_ne_zero {f : HahnSeries ℤ (KLRAlgebra k Q ν)} {d : ℤ}
    (hd : f.coeff d ≠ 0) : f.order ≤ d := order_le_of_coeff_ne_zero hd

/-- The coefficients of a product vanish below the sum of the orders. -/
theorem coeff_mul_eq_zero_of_lt (f g : HahnSeries ℤ (KLRAlgebra k Q ν)) {d : ℤ}
    (hd : d < f.order + g.order) : (f * g).coeff d = 0 := by
  rw [HahnSeries.coeff_mul]
  refine Finset.sum_eq_zero fun ij hij => ?_
  rw [Finset.mem_antidiagonal] at hij
  obtain ⟨hi, hj, hij⟩ := hij
  have := order_le_of_ne_zero hi
  have := order_le_of_ne_zero hj
  omega

variable (hφ : ∀ a : Fin (Multiset.card ν), φ (pol (X a ^ M)) = 0)
include hφ

theorem map_coeff_eq_zero (f : G.completion ν) {d : ℤ} (hd : G.truncBound ν M ≤ d) :
    φ (f.1.coeff d) = 0 :=
  G.map_eq_zero_of_mem_grade φ hφ hd (G.coeff_mem_grade f d)

/-- On `R(ν)`, the truncated sum with any lower limit below the support is `φ`. -/
theorem truncSum_toCompletion (a : KLRAlgebra k Q ν) {b : ℤ}
    (hb : ∀ d < b, (G.toCompletion a).1.coeff d = 0) :
    truncSum φ (G.truncBound ν M) b (G.toCompletion a).1 = φ a := by
  classical
  have hc : ∀ d, (G.toCompletion a).1.coeff d =
      (G.coaction a).coeff d := G.coeff_toCompletion a
  conv_rhs => rw [← G.counit a]
  rw [Finsupp.sum, map_sum, truncSum]
  simp_rw [hc]
  set S := (G.coaction a).coeff.support
  have h1 : ∑ d ∈ S ∩ Ico b (G.truncBound ν M), φ ((G.coaction a).coeff d) =
      ∑ d ∈ Ico b (G.truncBound ν M), φ ((G.coaction a).coeff d) :=
    Finset.sum_subset Finset.inter_subset_right fun d hd hd' => by
      have : d ∉ S := fun h => hd' (Finset.mem_inter.2 ⟨h, hd⟩)
      rw [Finsupp.notMem_support_iff.1 this, map_zero]
  have h2 : ∑ d ∈ S ∩ Ico b (G.truncBound ν M), φ ((G.coaction a).coeff d) =
      ∑ d ∈ S, φ ((G.coaction a).coeff d) :=
    Finset.sum_subset Finset.inter_subset_left fun d hd hd' => by
      have hb' : b ≤ d := by
        by_contra h
        exact Finsupp.mem_support_iff.1 hd (by rw [← hc]; exact hb d (by omega))
      have hD : G.truncBound ν M ≤ d := by
        by_contra h
        exact hd' (Finset.mem_inter.2 ⟨hd, Finset.mem_Ico.2 ⟨hb', by omega⟩⟩)
      rw [← hc]
      exact G.map_coeff_eq_zero φ hφ _ hD
  rw [← h1, h2]

theorem truncSum_mul (f g : G.completion ν) :
    truncSum φ (G.truncBound ν M) (f * g).1.order (f * g).1 =
      truncSum φ (G.truncBound ν M) f.1.order f.1 *
        truncSum φ (G.truncBound ν M) g.1.order g.1 := by
  classical
  set D := G.truncBound ν M
  set F : HahnSeries ℤ (KLRAlgebra k Q ν) := f.1
  set H : HahnSeries ℤ (KLRAlgebra k Q ν) := g.1
  have hFH : (f * g).1 = F * H := rfl
  rw [hFH]
  set b := F.order
  set c := H.order
  -- the lower limit `b + c`
  have hlow : truncSum φ D (F * H).order (F * H) = truncSum φ D (b + c) (F * H) := by
    have h₁ : min (F * H).order (b + c) ≤ (F * H).order := min_le_left _ _
    have h₂ : min (F * H).order (b + c) ≤ b + c := min_le_right _ _
    rw [← truncSum_eq_of_le φ D h₁ (coeff_eq_zero_of_lt_order' _),
      truncSum_eq_of_le φ D h₂ fun d hd => coeff_mul_eq_zero_of_lt F H hd]
  rw [hlow]
  have hmulφ : ∀ i j, i + j ∉ Set.Iio D → φ (F.coeff i) * φ (H.coeff j) = 0 := by
    intro i j hij
    rw [← map_mul]
    exact G.map_eq_zero_of_mem_grade φ hφ (not_lt.1 hij)
      (G.mul_mem_grade' (G.coeff_mem_grade f i) (G.coeff_mem_grade g j))
  set T := (Ico b D ×ˢ Ico c D).filter fun p : ℤ × ℤ => p.1 + p.2 < D
  -- the product of the truncated sums
  have hR : truncSum φ D b F * truncSum φ D c H =
      ∑ p ∈ T, φ (F.coeff p.1) * φ (H.coeff p.2) := by
    rw [truncSum, truncSum, Finset.sum_mul_sum, ← Finset.sum_product',
      ← Finset.sum_filter_add_sum_filter_not _ (fun p : ℤ × ℤ => p.1 + p.2 < D)]
    rw [Finset.sum_eq_zero (s := Finset.filter (fun p : ℤ × ℤ => ¬p.1 + p.2 < D) _)
      fun p hp => hmulφ p.1 p.2 (by simpa using (Finset.mem_filter.1 hp).2), add_zero]
  -- the truncated sum of the product
  have hL : truncSum φ D (b + c) (F * H) = ∑ p ∈ T, φ (F.coeff p.1) * φ (H.coeff p.2) := by
    rw [truncSum]
    simp_rw [HahnSeries.coeff_mul, map_sum, map_mul]
    rw [Finset.sum_sigma']
    refine Finset.sum_bij_ne_zero (fun x _ _ => x.2) ?_ ?_ ?_ ?_
    · rintro ⟨d, i, j⟩ hx hne
      simp only [Finset.mem_sigma, Finset.mem_antidiagonal] at hx hne ⊢
      obtain ⟨hd, hi, hj, hsum⟩ := hx
      subst hsum
      rw [Finset.mem_Ico] at hd
      have hi' : b ≤ i := order_le_of_ne_zero hi
      have hj' : c ≤ j := order_le_of_ne_zero hj
      have hiD : i < D := by
        by_contra h
        exact hne (by rw [G.map_coeff_eq_zero φ hφ f (not_lt.1 h), zero_mul])
      have hjD : j < D := by
        by_contra h
        exact hne (by rw [G.map_coeff_eq_zero φ hφ g (not_lt.1 h), mul_zero])
      exact Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨Finset.mem_Ico.2 ⟨hi', hiD⟩,
        Finset.mem_Ico.2 ⟨hj', hjD⟩⟩, hd.2⟩
    · rintro ⟨d, i, j⟩ hx _ ⟨d', i', j'⟩ hx' _ h
      simp only [Finset.mem_sigma, Finset.mem_antidiagonal] at hx hx'
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨-, -, -, h1⟩ := hx
      obtain ⟨-, -, -, h2⟩ := hx'
      subst h1; subst h2; rfl
    · rintro ⟨i, j⟩ hp hne
      rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Ico, Finset.mem_Ico] at hp
      have hi : F.coeff i ≠ 0 := fun h => hne (by simp only; rw [h, map_zero, zero_mul])
      have hj : H.coeff j ≠ 0 := fun h => hne (by simp only; rw [h, map_zero, mul_zero])
      refine ⟨⟨i + j, i, j⟩, ?_, ?_, rfl⟩
      · rw [Finset.mem_sigma, Finset.mem_antidiagonal, Finset.mem_Ico]
        exact ⟨⟨show b + c ≤ i + j by omega, hp.2⟩, hi, hj, rfl⟩
      · simpa using hne
    · intro _ _ _; rfl
  rw [hL, hR]

/-- **The extension of `φ` to the completion.** -/
noncomputable def completionLift : G.completion ν →ₐ[k] B :=
  have hz : ∀ f : HahnSeries ℤ (KLRAlgebra k Q ν), ∀ d < f.order, f.coeff d = 0 :=
    coeff_eq_zero_of_lt_order'
  { toFun := fun f => truncSum φ (G.truncBound ν M) f.1.order f.1
    map_one' := by
      have h1 : (1 : G.completion ν).1 = (G.toCompletion 1).1 := by rw [map_one]
      simp only [h1]
      rw [G.truncSum_toCompletion φ hφ 1 (hz _), map_one]
    map_mul' := fun f g => G.truncSum_mul φ hφ f g
    map_zero' := by simp [truncSum]
    map_add' := fun f g => by
      set F : HahnSeries ℤ (KLRAlgebra k Q ν) := f.1
      set G' : HahnSeries ℤ (KLRAlgebra k Q ν) := g.1
      change truncSum φ _ (F + G').order (F + G') = truncSum φ _ F.order F +
        truncSum φ _ G'.order G'
      have hb₁ : min (min F.order G'.order) (F + G').order ≤ F.order :=
        (min_le_left _ _).trans (min_le_left _ _)
      have hb₂ : min (min F.order G'.order) (F + G').order ≤ G'.order :=
        (min_le_left _ _).trans (min_le_right _ _)
      have hb₃ : min (min F.order G'.order) (F + G').order ≤ (F + G').order := min_le_right _ _
      rw [← truncSum_eq_of_le φ _ hb₁ (hz F), ← truncSum_eq_of_le φ _ hb₂ (hz G'),
        ← truncSum_eq_of_le φ _ hb₃ (hz _), truncSum, truncSum, truncSum,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [coeff_add, map_add]
    commutes' := fun r => by
      have h1 : (algebraMap k (G.completion ν) r).1 =
          (G.toCompletion (algebraMap k (KLRAlgebra k Q ν) r)).1 := by rw [AlgHom.commutes]
      simp only [h1]
      rw [G.truncSum_toCompletion φ hφ _ (hz _), AlgHom.commutes] }

theorem completionLift_apply (f : G.completion ν) :
    G.completionLift φ hφ f =
      truncSum φ (G.truncBound ν M) f.1.order f.1 := rfl

/-- The extension agrees with `φ` on `R(ν)`. -/
theorem completionLift_toCompletion (a : KLRAlgebra k Q ν) :
    G.completionLift φ hφ (G.toCompletion a) = φ a :=
  G.truncSum_toCompletion φ hφ a (coeff_eq_zero_of_lt_order' _)

end GradingDatum

end Categorification.KLR

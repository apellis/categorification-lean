/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Frobenius
import Categorification.KLR.K0Algebra
import Categorification.KLR.Pairing
import Categorification.KLR.KL1Basis

/-!
# Khovanov–Lauda I, Proposition 3.3: properties of the pairing on `K₀(R)`

Khovanov–Lauda I (arXiv:0803.4121v2), §3.1, Proposition 3.3 (`prop-pairing-prop`, TeX lines
1965–2003). The pairing on `K₀(R) = ⨁_ν K₀(R(ν))` is extended from the `K₀(R(ν))` by declaring
different weight spaces orthogonal; it satisfies

1. `(1, 1) = 1`;
2. `([P_i], [P_j]) = δ_{ij} (1 - q²)⁻¹` for `i, j ∈ I`;
3. `(x, y y') = ([Res] x, y ⊗ y')`;
4. `(x x', y) = (x ⊗ x', [Res] y)`.

## The form

We use the repository's form `K0.homForm`, `([P], [Q]) = gdim HOM(P, Q)`
(`Categorification.Algebra.Graded.HomForm`). It is biadditive with
`(q^a x, y) = q^{-a} (x, y)` and `(x, q^a y) = q^a (x, y)`; KL I's form
`gdim (P^ψ ⊗_{R(ν)} Q)` is `(x, y) ↦ homForm x̄ y`, and the two agree on the self-dual modules
`P_i` (in particular on all the values below). `GradingDatum.K0RForm` is the orthogonal sum of the
forms `homForm` on the weight spaces `K₀(R(ν))` of `K₀(R) = GradingDatum.K0R`.

## Main results

* `KL1.K0RForm_one_one` : **(1)** `(1, 1) = 1`.
* `KL1.K0RForm_projP_single` : **(2)** `([P_i], [P_j]) = δ_{ij} (1 - q²)⁻¹`, with
  `(1 - q²)⁻¹ = geomSeries 2` (`one_sub_mul_geomSeries`: `(1 - q²) · geomSeries 2 = 1`);
  `KL1.homForm_projP_single` is the statement inside `K₀(R(i))`.
* `GradingDatum.homForm_indK0` (in `Categorification.KLR.Frobenius`): **(4)**, in the form
  `(x x', y) = (x ⊗ x', [Res] y)` with `x ⊗ x' = K0.extTensor x x' ∈ K₀(R(ν) ⊗ R(ν'))` and
  `[Res] = GradingDatum.resK0`, for all `x`, `x'`, `y`.
* `GradingDatum.homForm_indK0_eq_sum` : **(4), evaluated**: if `[Res] y = ∑_α y_α ⊗ y'_α`, then
  `(x x', y) = ∑_α (x, y_α) (x', y'_α)` for `x`, `x'` in the `ℤ[q, q⁻¹]`-spans of the classes
  `[R(ν) e]` of degree-zero idempotents (e.g. `x = [P_i]`, `x' = [P_j]`: `projP_mem_idemClasses`);
  this uses the product formula `K0.homForm_extTensor_of_mem_span`
  (`Categorification.KLR.ExtTensorK0`).

## Not formalized here

* Statement (3) for `homForm` (induction in the second slot). For the paper's bilinear
  symmetric form `pform` it is `GradingDatum.pform_indK0_right` in `Categorification.KLR.BarK0`
  (for the image of `γ`, i.e. spans of idempotent classes).
* The identification `K₀(R(ν) ⊗ R(ν')) ≅ K₀(R(ν)) ⊗_{ℤ[q, q⁻¹]} K₀(R(ν'))`, needed to view
  `[Res]` as a coproduct `K₀(R) → K₀(R) ⊗ K₀(R)` and to state (3), (4) on all of `K₀(R)`; and the
  graded version of Proposition 2.19 (`Res P_s ≅ ⊕ (P_i ⊠ P_j){…}`), which would supply the
  decomposition hypothesis of `homForm_indK0_eq_sum` for `y = [P_s]`.
* The product formula `(x ⊗ x', y ⊗ y') = (x, y)(x', y')` for arbitrary `x`, `x'` (it is proved
  for `x`, `x'` in the spans of idempotent classes, which contain the image of `γ`).
-/

noncomputable section

namespace Categorification.KLR

open Graded KLRAlgebra TypeA Equiv MvPolynomial
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}

/-! ### The form on `K₀(R) = ⨁_ν K₀(R(ν))` -/

namespace GradingDatum

variable (G : GradingDatum Q) [∀ ν, HasGdim (G.grade ν)]

/-- **The form on `K₀(R) = ⨁_ν K₀(R(ν))`**: the orthogonal sum of the forms
`([P], [Q]) = gdim HOM(P, Q)` on the weight spaces `K₀(R(ν))` (KL I, §3.1: "subspaces
corresponding to different `ν`'s are orthogonal"). -/
def K0RForm : G.K0R →+ G.K0R →+ LaurentSeries ℤ :=
  DirectSum.toAddMonoid fun ν => (K0.homForm (G.grade ν)).compl₂
    (DirectSum.component ℤ (Multiset I) G.K0fam ν).toAddMonoidHom

theorem K0RForm_of_of (ν : Multiset I) (x y : K0 (G.grade ν)) :
    G.K0RForm (DirectSum.of G.K0fam ν x) (DirectSum.of G.K0fam ν y) =
      K0.homForm (G.grade ν) x y := by
  rw [K0RForm, DirectSum.toAddMonoid_of, AddMonoidHom.compl₂_apply, LinearMap.toAddMonoidHom_coe,
    ← DirectSum.apply_eq_component, DirectSum.of_eq_same]

theorem K0RForm_of_of_ne {ν μ : Multiset I} (h : ν ≠ μ) (x : K0 (G.grade ν))
    (y : K0 (G.grade μ)) :
    G.K0RForm (DirectSum.of G.K0fam ν x) (DirectSum.of G.K0fam μ y) = 0 := by
  rw [K0RForm, DirectSum.toAddMonoid_of, AddMonoidHom.compl₂_apply, LinearMap.toAddMonoidHom_coe,
    ← DirectSum.apply_eq_component, DirectSum.of_eq_of_ne _ _ _ (Ne.symm h), map_zero]

end GradingDatum

/-! ### (1) and (2) for the rings of KL I -/

namespace KL1

variable {Γ : SimpleGraph I} [DecidableRel Γ.Adj]

theorem invSet_one (m : ℕ) : invSet m 1 = ∅ :=
  Finset.eq_empty_of_forall_not_mem fun p hp => by
    rw [mem_invSet] at hp
    simp only [Perm.one_apply] at hp
    exact absurd hp.1 (not_lt.2 hp.2.le)

/-- For weights of size at most one, `([P_s], [P_s]) = (1 - q²)^{-|ν|}`. -/
theorem homForm_projP_self_of_card_le_one {ν : Multiset I} (hν : Multiset.card ν ≤ 1)
    (s : Seq ν) :
    K0.homForm ((klGradingDatum k Γ).grade ν) (K0.of ((klGradingDatum k Γ).projP s))
      (K0.of ((klGradingDatum k Γ).projP s)) = geomSeries 2 ^ Multiset.card ν := by
  haveI : Subsingleton (Fin (Multiset.card ν)) := Fin.subsingleton_iff_le_one.2 hν
  have h1 : ∀ w : Perm (Fin (Multiset.card ν)), w = 1 :=
    fun w => Equiv.ext fun a => Subsingleton.elim _ _
  rw [homForm_projP, Finset.sum_eq_single (1 : Perm (Fin (Multiset.card ν)))
    (fun w _ hw => absurd (h1 w) hw) (fun h => absurd (by simp) h), invSet_one,
    Finset.sum_empty, neg_zero, HahnSeries.single_zero_one, one_mul]

/-- **KL I, Proposition 3.3 (2), inside `K₀(R(i))`**: `([P_i], [P_i]) = gdim k[x] = (1 - q²)⁻¹`
for a single vertex `i` (here `s` is the sequence `(i)`, `ν = i`). -/
theorem homForm_projP_single (i : I) (s : Seq ({i} : Multiset I)) :
    K0.homForm ((klGradingDatum k Γ).grade {i}) (K0.of ((klGradingDatum k Γ).projP s))
      (K0.of ((klGradingDatum k Γ).projP s)) = geomSeries 2 := by
  rw [homForm_projP_self_of_card_le_one (by simp) s, Multiset.card_singleton, pow_one]

/-- `(1 - q²) · ([P_i], [P_i]) = 1`, i.e. `([P_i], [P_i]) = (1 - q²)⁻¹` in `ℤ((q))`. -/
theorem one_sub_mul_homForm_projP_single (i : I) (s : Seq ({i} : Multiset I)) :
    (1 - HahnSeries.single 2 1) * K0.homForm ((klGradingDatum k Γ).grade {i})
      (K0.of ((klGradingDatum k Γ).projP s)) (K0.of ((klGradingDatum k Γ).projP s)) = 1 := by
  rw [homForm_projP_single]
  exact one_sub_mul_geomSeries (by norm_num)

/-- **KL I, Proposition 3.3 (2)**: `([P_i], [P_j]) = δ_{ij} (1 - q²)⁻¹` in `K₀(R)`, for the
sequences `s = (i)`, `t = (j)` of length one. -/
theorem K0RForm_projP_single (i j : I) (s : Seq ({i} : Multiset I))
    (t : Seq ({j} : Multiset I)) :
    (klGradingDatum k Γ).K0RForm
        (DirectSum.of (klGradingDatum k Γ).K0fam {i} (K0.of ((klGradingDatum k Γ).projP s)))
        (DirectSum.of (klGradingDatum k Γ).K0fam {j} (K0.of ((klGradingDatum k Γ).projP t))) =
      if i = j then geomSeries 2 else 0 := by
  split_ifs with h
  · subst h
    have hst : s = t := by
      apply Subtype.ext
      funext a
      have ha := Seq.mem s a
      have hb := Seq.mem t a
      rw [Multiset.mem_singleton] at ha hb
      rw [ha, hb]
    subst hst
    rw [GradingDatum.K0RForm_of_of, homForm_projP_single]
  · exact (klGradingDatum k Γ).K0RForm_of_of_ne (by simpa using h) _ _

/-- **KL I, Proposition 3.3 (1)**: `(1, 1) = 1` in `K₀(R)`, where `1 = [R(0)] = [P_∅]`. -/
theorem K0RForm_one_one :
    (klGradingDatum k Γ).K0RForm (1 : (klGradingDatum k Γ).K0R) 1 = 1 := by
  rw [GradingDatum.K0R_one, GradingDatum.K0RForm_of_of,
    GradingDatum.K0_regular_eq_sum, Fintype.sum_unique, homForm_projP_self_of_card_le_one
      (by simp), Multiset.card_zero, pow_zero]

end KL1

/-! ### (4), evaluated on decompositions of `[Res] y` -/

namespace GradingDatum

variable (G : GradingDatum Q) {ν ν' : Multiset I} {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)

/-- The class `[P_s]` is the class of a module `R(ν) e` for a degree-zero idempotent `e`. -/
theorem projP_mem_idemClasses (s : Seq ν) :
    K0.of (G.projP s) ∈ K0.idemClasses (G.grade ν) :=
  ⟨e s, e_mul_self s, G.e_mem_grade s, rfl⟩

/-- **KL I, Proposition 3.3 (4), evaluated**: if `[Res_{ν,ν'}] y = ∑_α y_α ⊗ y'_α`, then
`(x x', y) = ∑_α (x, y_α) (x', y'_α)` for `x`, `x'` in the `ℤ[q, q⁻¹]`-spans of the classes of
modules `R(ν) e`, `R(ν') e'` cut out by degree-zero idempotents (for instance `x = [P_i]`,
`x' = [P_j]`). -/
theorem homForm_indK0_eq_sum [HasGdim (G.grade ν)] [HasGdim (G.grade ν')]
    [HasGdim (G.grade (ν + ν'))] {x : K0 (G.grade ν)} {x' : K0 (G.grade ν')}
    (hx : x ∈ Submodule.span (LaurentPolynomial ℤ) (K0.idemClasses (G.grade ν)))
    (hx' : x' ∈ Submodule.span (LaurentPolynomial ℤ) (K0.idemClasses (G.grade ν')))
    (y : K0 (G.grade (ν + ν'))) {ι : Type*} (s : Finset ι) (z : ι → K0 (G.grade ν))
    (z' : ι → K0 (G.grade ν'))
    (hy : G.resK0 ν ν' hPQ hP y = ∑ α ∈ s, K0.extTensor (G.grade ν) (G.grade ν') (z α) (z' α)) :
    K0.homForm (G.grade (ν + ν')) (G.indK0 ν ν' x x') y =
      ∑ α ∈ s, K0.homForm (G.grade ν) x (z α) * K0.homForm (G.grade ν') x' (z' α) := by
  rw [G.homForm_indK0 hPQ hP, hy, map_sum]
  exact Finset.sum_congr rfl fun α _ => K0.homForm_extTensor_of_mem_span hx hx' _ _

/-- `([P_i] [P_j], y) = ([P_i] ⊗ [P_j], [Res] y)` (Proposition 3.3 (4) for `x = [P_i]`,
`x' = [P_j]`), and `([P_i] ⊗ [P_j], y ⊗ y') = ([P_i], y) ([P_j], y')`. -/
theorem homForm_indK0_projP [HasGdim (G.grade ν)] [HasGdim (G.grade ν')]
    [HasGdim (G.grade (ν + ν'))] (i : Seq ν) (j : Seq ν') (y : K0 (G.grade ν))
    (y' : K0 (G.grade ν')) :
    K0.homForm (tensorGrading (G.grade ν) (G.grade ν'))
        (K0.extTensor (G.grade ν) (G.grade ν') (K0.of (G.projP i)) (K0.of (G.projP j)))
        (K0.extTensor (G.grade ν) (G.grade ν') y y') =
      K0.homForm (G.grade ν) (K0.of (G.projP i)) y *
        K0.homForm (G.grade ν') (K0.of (G.projP j)) y' :=
  K0.homForm_extTensor_ofIdempotent (e_mul_self i) (e_mul_self j) (G.e_mem_grade i)
    (G.e_mem_grade j) y y'

end GradingDatum

end Categorification.KLR

end

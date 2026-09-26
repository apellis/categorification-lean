/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.KL1Basis
import Categorification.KLR.GradedModules
import Categorification.Algebra.Graded.HomogeneousBasis
import Categorification.TypeA.Inversions
import Categorification.Algebra.Graded.GeomSeries

/-!
# The graded basis of `R(ν)` and graded dimensions

Khovanov–Lauda I (arXiv:0803.4121v2), §2.4–2.5. We combine the basis theorem
(`KLRAlgebra.basis`, KL I Theorem 2.5) with the grading (`GradingDatum.grade`):

* **Degrees of basis elements.** `ψ_{ρ w} x^u 1_i` is homogeneous of degree
  `stdDeg = deg(ψ_{ρ w} 1_i) + ∑_a u_a · deg(x_{a,i})` (`stdElt_mem_grade`,
  `basis_mem_grade`), and for a reduced word `ρ` the crossing degree is a sum over the
  inversions of `w`: `deg(ψ_ρ 1_i) = ∑_{(a,b) ∈ inv(w)} degΨ(i_a, i_b)`
  (`degW_eq_sum_invSet`); in particular it does not depend on the choice of reduced word
  (`degW_eq_of_isReduced`).
* **Graded pieces.** If every dot has positive degree (`0 < degX a`; true for KL I, where
  `deg x = 2`), each graded piece `R(ν)_d` is spanned by the finitely many basis elements of
  degree `d` (`grade_eq_span`, `finite_stdDeg_eq`), so it is finite-dimensional with dimension
  their number (`finrank_grade`), and `R(ν)` has a graded dimension (`hasGdim_grade`); the same
  holds for `1_j R(ν) 1_i` (`hasGdim_cornerGrade`) and for the span of any family of basis
  elements (`hasGdim_spanF`).
* **Vanishing in low degrees.** `R(ν)_d = 0` below the minimum of the crossing degrees
  (`grade_eq_bot_of_lt`). For KL I, `deg(ψ_ρ 1_i) ≥ -2 · #{a < b | i_a = i_b} =
  - ∑_c ν_c (ν_c - 1)` (`KL1.neg_two_mul_card_le_degW`, `KL1.two_mul_card_eqPairs`), so
  `R(ν)_d = 0` for `d < - ∑_c ν_c (ν_c - 1)` (`KL1.grade_eq_bot_of_lt`; paper, end of §2.4).
* **Finitely generated modules.** Over a field, every finitely generated graded `R(ν)`-module
  has a graded dimension (`hasGdim_of_finite`, `KL1.hasGdim_of_finite`), hence a character.
* **Graded dimension formula** (`gdim_cornerGrade`):
  `gdim (1_j R(ν) 1_i) = ∑_{w • i = j} q^{deg(ψ_{ρ w} 1_i)} ∏_a (1 - q^{deg(x_{a,i})})⁻¹`,
  where the inverse is the geometric series `geomSeries` (`one_sub_mul_geomSeries`); also in the
  division-free form `gdim_cornerGrade_mul_prod`. The analogous formulas for `R(ν) 1_i` and
  `R(ν)` are `gdim_leftIdeal` and `gdim_grade`. Since `1_j P_i = 1_j R(ν) 1_i`, this is also the
  character of `P_i` (`ch_projP`, `ch_projP_eq_sum`). For KL I:
  `gdim (1_j R(ν) 1_i) = ∑_{w • i = j} q^{- ∑_{(a,b) ∈ inv(w)} i_a · i_b} (1 - q²)^{-m}`
  (`KL1.gdim_cornerGrade`).

All statements are for a field `k` and data `Q` satisfying the hypotheses of the basis theorem;
the KL I specialisations (for a simple graph `Γ`, `klGradingDatum`) are in the namespace `KL1`.
-/

open Equiv MvPolynomial

namespace Categorification.TypeA

variable {m : ℕ}

/-- Outside the pair `{k, k + 1}`, the transposition `s_k` preserves the order of pairs. -/
theorem lt_iff_sadj_lt_of_not_adj {k : ℕ} (hk : k + 1 < m) {a b : Fin m}
    (h₁ : ¬ ((a : ℕ) = k ∧ (b : ℕ) = k + 1)) (h₂ : ¬ ((a : ℕ) = k + 1 ∧ (b : ℕ) = k)) :
    a < b ↔ sadj m k a < sadj m k b := by
  rw [Fin.lt_iff_val_lt_val, Fin.lt_iff_val_lt_val, sadj_val_of_lt hk, sadj_val_of_lt hk]
  have := swapNat_cases k a
  have := swapNat_cases k b
  generalize swapNat k a = x at *
  generalize swapNat k b = y at *
  omega

/-- If `w⁻¹ k < w⁻¹ (k + 1)`, the inversions of `s_k * w` are those of `w` together with the
pair `(w⁻¹ k, w⁻¹ (k + 1))`. -/
theorem invSet_sadj_mul_eq_insert {k : ℕ} (hk : k + 1 < m) {w : Perm (Fin m)}
    (hlt : w⁻¹ ⟨k, by omega⟩ < w⁻¹ ⟨k + 1, hk⟩) :
    invSet m (sadj m k * w) = insert (w⁻¹ ⟨k, by omega⟩, w⁻¹ ⟨k + 1, hk⟩) (invSet m w) := by
  ext ⟨a, b⟩
  rw [Finset.mem_insert, mem_invSet, mem_invSet, Perm.mul_apply, Perm.mul_apply]
  simp only [Prod.mk.injEq]
  by_cases h₁ : (w a : ℕ) = k ∧ (w b : ℕ) = k + 1
  · have ha : a = w⁻¹ ⟨k, by omega⟩ := by rw [Perm.eq_inv_iff_eq]; exact Fin.ext h₁.1
    have hb : b = w⁻¹ ⟨k + 1, hk⟩ := by rw [Perm.eq_inv_iff_eq]; exact Fin.ext h₁.2
    have hwa : w a = ⟨k, by omega⟩ := Fin.ext h₁.1
    have hwb : w b = ⟨k + 1, hk⟩ := Fin.ext h₁.2
    rw [hwa, hwb, sadj_apply_left hk, sadj_apply_right hk]
    simp only [ha, hb, and_self, true_or, iff_true]
    exact ⟨hlt, by simp [Fin.lt_iff_val_lt_val]⟩
  by_cases h₂ : (w a : ℕ) = k + 1 ∧ (w b : ℕ) = k
  · have ha : a = w⁻¹ ⟨k + 1, hk⟩ := by rw [Perm.eq_inv_iff_eq]; exact Fin.ext h₂.1
    have hb : b = w⁻¹ ⟨k, by omega⟩ := by rw [Perm.eq_inv_iff_eq]; exact Fin.ext h₂.2
    rw [ha, hb]
    have hn : ¬ w⁻¹ ⟨k + 1, hk⟩ < w⁻¹ ⟨k, by omega⟩ := lt_asymm hlt
    have hn2 : w⁻¹ ⟨k + 1, hk⟩ ≠ w⁻¹ ⟨k, by omega⟩ := fun h => by
      simpa [Fin.ext_iff] using w⁻¹.injective h
    simp [hn, hn2]
  have hne : ¬ (a = w⁻¹ ⟨k, by omega⟩ ∧ b = w⁻¹ ⟨k + 1, hk⟩) := fun h => h₁ <| by
    rw [h.1, h.2]; simp
  simp only [hne, false_or, lt_iff_sadj_lt_of_not_adj hk (a := w b) (b := w a)
    (fun h => h₂ ⟨h.2, h.1⟩) (fun h => h₁ ⟨h.2, h.1⟩)]

/-- The tail of a reduced word is reduced, and the first letter is an ascent of the
permutation of the tail. -/
theorem IsReduced.tail_and_lt {j : ℕ} {ρ : List ℕ} (h : IsReduced m (j :: ρ)) :
    IsReduced m ρ ∧ ∃ hj : j + 1 < m,
      (wordProd m ρ)⁻¹ ⟨j, by omega⟩ < (wordProd m ρ)⁻¹ ⟨j + 1, hj⟩ := by
  have hv := h.validWord
  have hj : j + 1 < m := hv j List.mem_cons_self
  have hvρ : ValidWord m ρ := fun a ha => hv a (List.mem_cons_of_mem _ ha)
  have hlen := h.length_eq
  rw [wordProd_cons, List.length_cons] at hlen
  have h1 := length_sadj_mul_le j (wordProd m ρ)
  have h2 := length_wordProd_le hvρ
  refine ⟨⟨hvρ, by omega⟩, hj, ?_⟩
  rcases lt_or_gt_of_ne ((wordProd m ρ)⁻¹.injective.ne
    (show (⟨j, by omega⟩ : Fin m) ≠ ⟨j + 1, hj⟩ by simp)) with hlt | hgt
  · exact hlt
  · have := length_sadj_mul_of_gt hj hgt
    omega

end Categorification.TypeA

namespace Categorification.KLR

open TypeA Graded KLRAlgebra

variable {I : Type*} {k : Type*} [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}

namespace GradingDatum

variable (G : GradingDatum Q) {ν : Multiset I}

/-- **The degree of `ψ_ρ 1_i` for a reduced word `ρ`** is the sum of `degΨ (i_a, i_b)` over the
inversions `a < b`, `w b < w a` of `w = wordProd ρ` (the pairs of strands that cross). -/
theorem degW_eq_sum_invSet {ρ : List ℕ} (hρ : IsReduced (Multiset.card ν) ρ) (i : Seq ν) :
    G.degW ρ i = ∑ p ∈ invSet (Multiset.card ν) (wordProd (Multiset.card ν) ρ),
      G.degΨ (i.lbl p.1) (i.lbl p.2) := by
  induction ρ with
  | nil =>
    have : invSet (Multiset.card ν) 1 = ∅ :=
      Finset.card_eq_zero.1 (invCount_one (Multiset.card ν))
    simp [degW, this]
  | cons j ρ ih =>
    obtain ⟨hρ', hj, hlt⟩ := hρ.tail_and_lt
    rw [degW, ih hρ', wordProd_cons, invSet_sadj_mul_eq_insert hj hlt,
      Finset.sum_insert (fun h => by
        have := (mem_invSet.1 h).2
        rw [Perm.apply_inv_self, Perm.apply_inv_self] at this
        exact absurd this (by simp [Fin.lt_iff_val_lt_val])),
      G.dψ_of_lt hj]
    simp only [Seq.lbl, Seq.smul_apply, Perm.inv_def]

/-- The crossing degree of a reduced word depends only on the permutation. -/
theorem degW_eq_of_isReduced {ρ σ : List ℕ} (hρ : IsReduced (Multiset.card ν) ρ)
    (hσ : IsReduced (Multiset.card ν) σ)
    (h : wordProd (Multiset.card ν) ρ = wordProd (Multiset.card ν) σ) (i : Seq ν) :
    G.degW ρ i = G.degW σ i := by
  rw [G.degW_eq_sum_invSet hρ, G.degW_eq_sum_invSet hσ, h]

end GradingDatum

/-! ### Degrees of the basis elements -/

section StdDeg

variable [DecidableEq I] (G : GradingDatum Q) {ν : Multiset I}

namespace GradingDatum

/-- The degree of the standard element `ψ_{ρ w} x^u 1_i` (`b = (i, w, u)`):
`deg(ψ_{ρ w} 1_i) + ∑_a u_a · degX(i_a)`. -/
noncomputable def stdDeg (ρ : Perm (Fin (Multiset.card ν)) → List ℕ)
    (b : Seq ν × Perm (Fin (Multiset.card ν)) × (Fin (Multiset.card ν) →₀ ℕ)) : ℤ :=
  G.degW (ρ b.2.1) b.1 + Finsupp.weight (fun a => G.degX (b.1.lbl a)) b.2.2

/-- **The standard elements are homogeneous**: `ψ_{ρ w} x^u 1_i ∈ R(ν)_{stdDeg}`. -/
theorem stdElt_mem_grade (ρ : Perm (Fin (Multiset.card ν)) → List ℕ)
    (b : Seq ν × Perm (Fin (Multiset.card ν)) × (Fin (Multiset.card ν) →₀ ℕ)) :
    (stdElt ρ b : KLRAlgebra k Q ν) ∈ G.grade ν (G.stdDeg ρ b) :=
  G.ψw_mul_pol_monomial_mul_e_mem_grade _ _ _

variable (ρ : Perm (Fin (Multiset.card ν)) → List ℕ)

omit [DecidableEq I] in
/-- If all dots have positive degree, there are finitely many standard elements of each
degree. -/
theorem finite_stdDeg_eq (hX : ∀ a, 0 < G.degX a) (d : ℤ) :
    {b | G.stdDeg ρ b = d}.Finite := by
  have h : {b | G.stdDeg ρ b = d} ⊆ Set.univ ×ˢ (Set.univ ×ˢ
      ⋃ (i : Seq ν) (w : Perm (Fin (Multiset.card ν))),
        {u | Finsupp.weight (fun a => G.degX (i.lbl a)) u = d - G.degW (ρ w) i}) := by
    rintro ⟨i, w, u⟩ hb
    simp only [Set.mem_setOf_eq, stdDeg] at hb
    simp only [Set.mem_prod, Set.mem_univ, Set.mem_iUnion, Set.mem_setOf_eq, true_and]
    exact ⟨i, w, by omega⟩
  exact (Set.finite_univ.prod (Set.finite_univ.prod (Set.finite_iUnion fun i =>
    Set.finite_iUnion fun w => finite_weight_eq (fun a => hX _) _))).subset h

omit [DecidableEq I] in
/-- The crossing degrees `deg(ψ_{ρ w} 1_i)` are bounded below (there are finitely many). -/
theorem exists_le_degW : ∃ B, ∀ (i : Seq ν) (w : Perm (Fin (Multiset.card ν))),
    B ≤ G.degW (ρ w) i := by
  obtain ⟨B, hB⟩ := (Set.finite_range fun p : Seq ν × Perm (Fin (Multiset.card ν)) =>
    G.degW (ρ p.2) p.1).bddBelow
  exact ⟨B, fun i w => hB ⟨(i, w), rfl⟩⟩

omit [DecidableEq I] in
theorem degW_le_stdDeg (hX : ∀ a, 0 ≤ G.degX a)
    (b : Seq ν × Perm (Fin (Multiset.card ν)) × (Fin (Multiset.card ν) →₀ ℕ)) :
    G.degW (ρ b.2.1) b.1 ≤ G.stdDeg ρ b := by
  have := weight_nonneg (w := fun a => G.degX (b.1.lbl a)) (fun a => hX _) b.2.2
  simp only [stdDeg]
  omega

omit [DecidableEq I] in
/-- The degrees of the standard elements are bounded below. -/
theorem bddBelow_stdDeg (hX : ∀ a, 0 ≤ G.degX a) (S : Set (Seq ν ×
    Perm (Fin (Multiset.card ν)) × (Fin (Multiset.card ν) →₀ ℕ))) :
    BddBelow (G.stdDeg ρ '' S) := by
  obtain ⟨B, hB⟩ := G.exists_le_degW ρ
  exact ⟨B, by rintro _ ⟨b, -, rfl⟩; exact (hB _ _).trans (G.degW_le_stdDeg ρ hX b)⟩

omit [DecidableEq I] in
/-- Counting the standard elements of degree `d` with `(i, w) ∈ F`. -/
theorem natCard_stdDeg_eq (hX : ∀ a, 0 < G.degX a)
    (F : Finset (Seq ν × Perm (Fin (Multiset.card ν)))) (d : ℤ) :
    Nat.card {b | (b.1, b.2.1) ∈ F ∧ G.stdDeg ρ b = d} = ∑ p ∈ F,
      Nat.card {u : Fin (Multiset.card ν) →₀ ℕ |
        Finsupp.weight (fun a => G.degX (p.1.lbl a)) u = d - G.degW (ρ p.2) p.1} := by
  classical
  haveI : ∀ p : F, Finite {u : Fin (Multiset.card ν) →₀ ℕ | Finsupp.weight
      (fun a => G.degX ((p : Seq ν × Perm (Fin (Multiset.card ν))).1.lbl a)) u =
      d - G.degW (ρ (p : Seq ν × Perm (Fin (Multiset.card ν))).2)
        (p : Seq ν × Perm (Fin (Multiset.card ν))).1} :=
    fun p => (finite_weight_eq (fun a => hX _) _).to_subtype
  rw [← Finset.sum_coe_sort F, ← Nat.card_sigma]
  refine Nat.card_congr {
    toFun := fun b => ⟨⟨(b.1.1, b.1.2.1), b.2.1⟩, ⟨b.1.2.2, by
        have h := b.2.2
        simp only [stdDeg] at h
        show _ = _
        dsimp only at h ⊢
        omega⟩⟩
    invFun := fun x => ⟨(x.1.1.1, x.1.1.2, x.2.1), x.1.2, by
      have h := x.2.2
      simp only [Set.mem_setOf_eq] at h
      show _ + _ = _
      dsimp only at h ⊢
      omega⟩
    left_inv := fun b => rfl
    right_inv := fun x => rfl }

/-- The graded pieces `(1_j R(ν) 1_i)_d = R(ν)_d ∩ 1_j R(ν) 1_i` of the corner. -/
def cornerGrade (j i : Seq ν) : ℤ → Submodule k (KLRAlgebra k Q ν) :=
  fun d => G.grade ν d ⊓ corner j i

end GradingDatum

end StdDeg

/-! ### Graded pieces of `R(ν)` -/

section Pieces

variable {k : Type*} [Field k] [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k}
  {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0) (G : GradingDatum Q) {ν : Multiset I}
  (ρ : Perm (Fin (Multiset.card ν)) → List ℕ)
  (hρ : ∀ w, IsReduced (Multiset.card ν) (ρ w) ∧ wordProd (Multiset.card ν) (ρ w) = w)

include hPQ hP hρ

namespace GradingDatum

/-- The basis `ψ_{ρ w} x^u 1_i` of `R(ν)` consists of homogeneous elements of degree
`stdDeg`. -/
theorem basis_mem_grade
    (b : Seq ν × Perm (Fin (Multiset.card ν)) × (Fin (Multiset.card ν) →₀ ℕ)) :
    KLRAlgebra.basis hPQ hP ρ hρ b ∈ G.grade ν (G.stdDeg ρ b) := by
  rw [basis_apply]
  exact G.stdElt_mem_grade ρ b

theorem span_basis_univ :
    Submodule.span k (KLRAlgebra.basis hPQ hP ρ hρ '' Set.univ) = ⊤ := by
  rw [Set.image_univ, Basis.span_eq]

/-- **`R(ν)_d` is spanned by the basis elements of degree `d`.** -/
theorem grade_eq_span (d : ℤ) :
    G.grade ν d = Submodule.span k (KLRAlgebra.basis hPQ hP ρ hρ '' {b | G.stdDeg ρ b = d}) := by
  have h := inf_span_eq (G.grade ν) (G.stdDeg ρ) (G.basis_mem_grade hPQ hP ρ hρ) Set.univ d
  rw [span_basis_univ, inf_top_eq] at h
  rw [h]
  congr 2
  ext b
  simp

/-- **Dimension of the graded pieces**: `dim R(ν)_d` is the number of standard basis elements
of degree `d` (when all dots have positive degree). -/
theorem finrank_grade (hX : ∀ a, 0 < G.degX a) (d : ℤ) :
    Module.finrank k (G.grade ν d) = Nat.card {b | G.stdDeg ρ b = d} := by
  have h := finrank_inf_span (G.grade ν) (G.stdDeg ρ)
    (KLRAlgebra.basis hPQ hP ρ hρ).linearIndependent
    (G.basis_mem_grade hPQ hP ρ hρ) Set.univ d (by simpa using G.finite_stdDeg_eq ρ hX d)
  rw [span_basis_univ, inf_top_eq] at h
  rw [h]
  simp

/-- **`R(ν)` has a graded dimension**: its graded pieces are finite-dimensional and vanish in
sufficiently negative degrees, when all dots have positive degree. -/
theorem hasGdim_grade (hX : ∀ a, 0 < G.degX a) : HasGdim (G.grade ν) := by
  have h := hasGdim_inf_span (G.grade ν) (G.stdDeg ρ) (G.basis_mem_grade hPQ hP ρ hρ) Set.univ
    (fun d => by simpa using G.finite_stdDeg_eq ρ hX d)
    (G.bddBelow_stdDeg ρ (fun a => (hX a).le) _)
  simp only [span_basis_univ, inf_top_eq] at h
  exact h

/-- **Vanishing in low degrees**: `R(ν)_d = 0` if `d` is below every crossing degree
`deg(ψ_{ρ w} 1_i)` (dots of nonnegative degree). -/
theorem grade_eq_bot_of_lt (hX : ∀ a, 0 ≤ G.degX a) {d : ℤ}
    (hd : ∀ (i : Seq ν) (w : Perm (Fin (Multiset.card ν))), d < G.degW (ρ w) i) :
    G.grade ν d = ⊥ := by
  rw [G.grade_eq_span hPQ hP ρ hρ d]
  have : {b | G.stdDeg ρ b = d} = ∅ := Set.eq_empty_iff_forall_not_mem.2 fun b hb => by
    have h1 := G.degW_le_stdDeg ρ hX b
    have h2 := hd b.1 b.2.1
    rw [Set.mem_setOf_eq] at hb
    omega
  rw [this, Set.image_empty, Submodule.span_empty]

/-! #### Spans of families of basis elements -/

/-- The span of the basis elements `ψ_{ρ w} x^u 1_i` with `(i, w) ∈ F`. -/
noncomputable def spanF (F : Finset (Seq ν × Perm (Fin (Multiset.card ν)))) :
    Submodule k (KLRAlgebra k Q ν) :=
  Submodule.span k (KLRAlgebra.basis hPQ hP ρ hρ '' {b | (b.1, b.2.1) ∈ F})

/-- `R(ν)_d ∩ span F` is spanned by the basis elements of degree `d` with `(i, w) ∈ F`, and
the family `d ↦ R(ν)_d ∩ span F` has a graded dimension. -/
theorem hasGdim_spanF (hX : ∀ a, 0 < G.degX a)
    (F : Finset (Seq ν × Perm (Fin (Multiset.card ν)))) :
    HasGdim fun d => (G.grade ν d ⊓ spanF hPQ hP ρ hρ F : Submodule k (KLRAlgebra k Q ν)) :=
  hasGdim_inf_span (G.grade ν) (G.stdDeg ρ) (G.basis_mem_grade hPQ hP ρ hρ) _
    (fun d => (G.finite_stdDeg_eq ρ hX d).subset fun _ hb => hb.2)
    (G.bddBelow_stdDeg ρ (fun a => (hX a).le) _)

/-- **Graded dimension of the span of basis elements with `(i, w) ∈ F`**:
`∑_{(i, w) ∈ F} q^{deg(ψ_{ρ w} 1_i)} ∏_a (1 - q^{deg x_{a,i}})⁻¹`. -/
theorem gdim_spanF (hX : ∀ a, 0 < G.degX a) (F : Finset (Seq ν × Perm (Fin (Multiset.card ν)))) :
    gdim (fun d => (G.grade ν d ⊓ spanF hPQ hP ρ hρ F : Submodule k (KLRAlgebra k Q ν))) =
      ∑ p ∈ F, HahnSeries.single (G.degW (ρ p.2) p.1) 1 *
        ∏ a, geomSeries (G.degX (p.1.lbl a)) := by
  ext d
  rw [spanF, coeff_gdim_inf_span (G.grade ν) (G.stdDeg ρ)
    (KLRAlgebra.basis hPQ hP ρ hρ).linearIndependent (G.basis_mem_grade hPQ hP ρ hρ) _
    (fun d => (G.finite_stdDeg_eq ρ hX d).subset fun _ hb => hb.2)
    (G.bddBelow_stdDeg ρ (fun a => (hX a).le) _) d]
  rw [show {x | x ∈ {b : Seq ν × Perm (Fin (Multiset.card ν)) × (Fin (Multiset.card ν) →₀ ℕ) |
      (b.1, b.2.1) ∈ F} ∧ G.stdDeg ρ x = d} = {b | (b.1, b.2.1) ∈ F ∧ G.stdDeg ρ b = d} from rfl,
    G.natCard_stdDeg_eq ρ hX F d, HahnSeries.coeff_sum, Nat.cast_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← sub_add_cancel d (G.degW (ρ p.2) p.1), HahnSeries.coeff_single_mul_add, one_mul,
    coeff_prod_geomSeries _ (fun a => hX _), add_sub_cancel_right]

theorem spanF_univ : spanF hPQ hP ρ hρ Finset.univ = ⊤ := by
  rw [spanF, ← span_basis_univ hPQ hP ρ hρ]
  congr 2
  ext b
  simp

/-- **Graded dimension of `R(ν)`**:
`gdim R(ν) = ∑_{i, w} q^{deg(ψ_{ρ w} 1_i)} ∏_a (1 - q^{deg x_{a,i}})⁻¹`. -/
theorem gdim_grade (hX : ∀ a, 0 < G.degX a) :
    gdim (G.grade ν) = ∑ i : Seq ν, ∑ w : Perm (Fin (Multiset.card ν)),
      HahnSeries.single (G.degW (ρ w) i) 1 * ∏ a, geomSeries (G.degX (i.lbl a)) := by
  have h := G.gdim_spanF hPQ hP ρ hρ hX Finset.univ
  simp only [spanF_univ, inf_top_eq] at h
  rw [h, ← Finset.univ_product_univ, Finset.sum_product]

/-- The corner `1_j R(ν) 1_i` is the span of the basis elements `ψ_{ρ w} x^u 1_i` with
`w • i = j`. -/
theorem spanF_corner (j i : Seq ν) :
    spanF hPQ hP ρ hρ ({i} ×ˢ Finset.univ.filter fun w => w • i = j) = corner j i := by
  rw [spanF, ← span_cornerElt ρ hρ j i]
  congr 1
  ext r
  simp only [Set.mem_image, Set.mem_setOf_eq, Finset.mem_product, Finset.mem_singleton,
    Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_range]
  constructor
  · rintro ⟨⟨i', w, u⟩, ⟨rfl, hw⟩, rfl⟩
    exact ⟨(⟨w, hw⟩, u), by rw [basis_apply]; rfl⟩
  · rintro ⟨⟨⟨w, hw⟩, u⟩, rfl⟩
    exact ⟨(i, w, u), ⟨rfl, hw⟩, by rw [basis_apply]; rfl⟩

/-- **`1_j R(ν) 1_i` has a graded dimension.** -/
theorem hasGdim_cornerGrade (hX : ∀ a, 0 < G.degX a) (j i : Seq ν) :
    HasGdim (G.cornerGrade j i) := by
  have h := G.hasGdim_spanF hPQ hP ρ hρ hX ({i} ×ˢ Finset.univ.filter fun w => w • i = j)
  simp only [spanF_corner] at h
  exact h

/-- **Graded dimension of `1_j R(ν) 1_i`** (KL I, §2.5):
`gdim (1_j R(ν) 1_i) = ∑_{w • i = j} q^{deg(ψ_{ρ w} 1_i)} ∏_a (1 - q^{deg x_{a,i}})⁻¹`,
where `(1 - q^d)⁻¹ = geomSeries d` (`one_sub_mul_geomSeries`). -/
theorem gdim_cornerGrade (hX : ∀ a, 0 < G.degX a) (j i : Seq ν) :
    gdim (G.cornerGrade j i) = ∑ w ∈ Finset.univ.filter (fun w => w • i = j),
      HahnSeries.single (G.degW (ρ w) i) 1 * ∏ a, geomSeries (G.degX (i.lbl a)) := by
  have h := G.gdim_spanF hPQ hP ρ hρ hX ({i} ×ˢ Finset.univ.filter fun w => w • i = j)
  simp only [spanF_corner] at h
  rw [show G.cornerGrade j i = fun d => G.grade ν d ⊓ corner j i from rfl, h,
    Finset.sum_product, Finset.sum_singleton]

/-- The graded dimension formula without inverses:
`gdim (1_j R(ν) 1_i) · ∏_a (1 - q^{deg x_{a,i}}) = ∑_{w • i = j} q^{deg(ψ_{ρ w} 1_i)}`. -/
theorem gdim_cornerGrade_mul_prod (hX : ∀ a, 0 < G.degX a) (j i : Seq ν) :
    gdim (G.cornerGrade j i) * ∏ a, (1 - HahnSeries.single (G.degX (i.lbl a)) 1) =
      ∑ w ∈ Finset.univ.filter (fun w => w • i = j), HahnSeries.single (G.degW (ρ w) i) 1 := by
  rw [G.gdim_cornerGrade hPQ hP ρ hρ hX, Finset.sum_mul]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [mul_assoc, ← Finset.prod_mul_distrib]
  simp only [mul_comm (geomSeries _), one_sub_mul_geomSeries (hX _), Finset.prod_const_one,
    mul_one]

/-- The left ideal `R(ν) 1_i = P_i` is the span of the basis elements `ψ_{ρ w} x^u 1_i`. -/
theorem spanF_leftIdeal (i : Seq ν) :
    spanF hPQ hP ρ hρ ({i} ×ˢ Finset.univ) =
      (Graded.leftIdeal (e i : KLRAlgebra k Q ν)).restrictScalars k := by
  apply le_antisymm
  · rw [spanF, Submodule.span_le]
    rintro _ ⟨⟨i', w, u⟩, hb, rfl⟩
    simp only [Set.mem_setOf_eq, Finset.mem_product, Finset.mem_singleton, Finset.mem_univ,
      and_true] at hb
    subst hb
    show _ * _ = _
    rw [basis_apply, mul_assoc _ (e i'), e_mul_self]
  · intro r hr
    have hr' : r * e i = r := hr
    rw [← hr']
    clear hr hr'
    have hr2 : r ∈ Submodule.span k (Set.range (KLRAlgebra.basis hPQ hP ρ hρ)) := by
      rw [Basis.span_eq]; trivial
    induction hr2 using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨i', w, u⟩, rfl⟩ := hx
      rw [basis_apply]
      dsimp only
      rw [gen_mul_e]
      split_ifs with h
      · subst h
        exact Submodule.subset_span ⟨(i', w, u), by simp, by rw [basis_apply]⟩
      · exact zero_mem _
    | zero => rw [zero_mul]; exact zero_mem _
    | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
    | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

/-- **Graded dimension of `P_i = R(ν) 1_i`**:
`gdim (R(ν) 1_i) = ∑_w q^{deg(ψ_{ρ w} 1_i)} ∏_a (1 - q^{deg x_{a,i}})⁻¹`. -/
theorem gdim_leftIdeal (hX : ∀ a, 0 < G.degX a) (i : Seq ν) :
    gdim (fun d => (G.grade ν d ⊓ (Graded.leftIdeal (e i : KLRAlgebra k Q ν)).restrictScalars k
      : Submodule k (KLRAlgebra k Q ν))) = ∑ w : Perm (Fin (Multiset.card ν)),
      HahnSeries.single (G.degW (ρ w) i) 1 * ∏ a, geomSeries (G.degX (i.lbl a)) := by
  have h := G.gdim_spanF hPQ hP ρ hρ hX ({i} ×ˢ Finset.univ)
  simp only [spanF_leftIdeal] at h
  rw [h, Finset.sum_product, Finset.sum_singleton]

end GradingDatum

end Pieces

/-! ### The KL I degree bound -/

section KL1Bound

namespace KL1

variable {ν : Multiset I}

/-- The pairs of positions `a < b` carrying equal labels in `i`. -/
def eqPairs [DecidableEq I] (i : Seq ν) : Finset (Fin (Multiset.card ν) × Fin (Multiset.card ν)) :=
  Finset.univ.filter fun p => p.1 < p.2 ∧ i.lbl p.1 = i.lbl p.2

theorem count_eq_card [DecidableEq I] (i : Seq ν) (c : I) :
    ν.count c = (Finset.univ.filter fun a => i.lbl a = c).card := by
  have h := congrArg (Multiset.count c) i.2
  rw [Multiset.count_map] at h
  rw [← h]
  simp only [Finset.card, Finset.filter_val]
  simp only [eq_comm (a := c)]

/-- `2 · #{a < b | i_a = i_b} = ∑_c ν_c (ν_c - 1)`. -/
theorem two_mul_card_eqPairs [DecidableEq I] (i : Seq ν) :
    2 * (eqPairs i).card = ∑ c ∈ ν.toFinset, ν.count c * (ν.count c - 1) := by
  classical
  set D := Finset.univ.filter fun p : Fin (Multiset.card ν) × Fin (Multiset.card ν) =>
    p.1 ≠ p.2 ∧ i.lbl p.1 = i.lbl p.2 with hD
  -- `D` consists of the equal-label pairs and their swaps
  have h1 : D.card = 2 * (eqPairs i).card := by
    rw [← Finset.filter_card_add_filter_neg_card_eq_card (fun p => p.1 < p.2), two_mul]
    congr 1
    · congr 1
      ext p
      simp only [D, eqPairs, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨-, h⟩, hlt⟩; exact ⟨hlt, h⟩
      · rintro ⟨hlt, h⟩; exact ⟨⟨hlt.ne, h⟩, hlt⟩
    · refine Finset.card_nbij' Prod.swap Prod.swap ?_ ?_ (fun _ _ => rfl) (fun _ _ => rfl)
      · intro p hp
        simp only [D, eqPairs, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
          Prod.fst_swap, Prod.snd_swap] at hp ⊢
        exact ⟨lt_of_le_of_ne (not_lt.1 hp.2) (Ne.symm hp.1.1), hp.1.2.symm⟩
      · intro p hp
        simp only [D, eqPairs, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
          Prod.fst_swap, Prod.snd_swap] at hp ⊢
        exact ⟨⟨hp.1.ne', hp.2.symm⟩, not_lt.2 hp.1.le⟩
  -- counting `D` by its first coordinate
  have h2 : D.card = ∑ a, ((Finset.univ.filter fun b => i.lbl b = i.lbl a).card - 1) := by
    rw [hD, Finset.card_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.card_filter]
    have : (Finset.univ.filter fun b => a ≠ b ∧ i.lbl a = i.lbl b) =
        (Finset.univ.filter fun b => i.lbl b = i.lbl a).erase a := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨Ne.symm h1, h2.symm⟩
      · rintro ⟨h1, h2⟩; exact ⟨Ne.symm h1, h2.symm⟩
    rw [this, Finset.card_erase_of_mem (by simp)]
  rw [← h1, h2, ← Finset.sum_fiberwise_of_maps_to (g := i.lbl) (t := ν.toFinset)
    (fun a _ => Multiset.mem_toFinset.2 (i.mem a))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_congr rfl fun a (ha : a ∈ Finset.univ.filter fun a => i.lbl a = c) => by
    rw [(Finset.mem_filter.1 ha).2]]
  rw [Finset.sum_const, smul_eq_mul, ← count_eq_card]

variable {k : Type*} [CommRing k] [DecidableEq I] {Γ : SimpleGraph I} [DecidableRel Γ.Adj]

/-- For KL I, `deg(ψ_ρ 1_i) ≥ -2 · #{a < b | i_a = i_b}` for every reduced word `ρ`: only
crossings of equally labelled strands have negative degree (`-2`), and a reduced word crosses
each pair of strands at most once. -/
theorem neg_two_mul_card_le_degW {ρ : List ℕ} (hρ : IsReduced (Multiset.card ν) ρ) (i : Seq ν) :
    -(2 * ((eqPairs i).card : ℤ)) ≤ (klGradingDatum k Γ).degW ρ i := by
  classical
  rw [(klGradingDatum k Γ).degW_eq_sum_invSet hρ]
  set s := invSet (Multiset.card ν) (wordProd (Multiset.card ν) ρ)
  rw [← Finset.sum_filter_add_sum_filter_not s (fun p => i.lbl p.1 = i.lbl p.2)]
  have hA : ∑ p ∈ s.filter (fun p => i.lbl p.1 = i.lbl p.2),
      (klGradingDatum k Γ).degΨ (i.lbl p.1) (i.lbl p.2) =
      ∑ p ∈ s.filter (fun p => i.lbl p.1 = i.lbl p.2), (-2 : ℤ) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [(Finset.mem_filter.1 hp).2]
    show -cartan Γ _ _ = _
    rw [cartan_self]
  have hB : 0 ≤ ∑ p ∈ s.filter (fun p => ¬ i.lbl p.1 = i.lbl p.2),
      (klGradingDatum k Γ).degΨ (i.lbl p.1) (i.lbl p.2) := by
    refine Finset.sum_nonneg fun p hp => ?_
    have hne := (Finset.mem_filter.1 hp).2
    show 0 ≤ -cartan Γ _ _
    unfold cartan
    rw [if_neg hne]
    split_ifs <;> norm_num
  have hC : (s.filter (fun p => i.lbl p.1 = i.lbl p.2)).card ≤ (eqPairs i).card := by
    refine Finset.card_le_card fun p hp => ?_
    rw [Finset.mem_filter] at hp
    simp only [eqPairs, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨(mem_invSet.1 hp.1).1, hp.2⟩
  rw [hA, Finset.sum_const, nsmul_eq_mul]
  have : ((s.filter (fun p => i.lbl p.1 = i.lbl p.2)).card : ℤ) ≤ (eqPairs i).card := by
    exact_mod_cast hC
  linarith

/-- For KL I, `deg(ψ_ρ 1_i) ≥ - ∑_c ν_c (ν_c - 1)` for every reduced word `ρ`. -/
theorem neg_sum_le_degW {ρ : List ℕ} (hρ : IsReduced (Multiset.card ν) ρ) (i : Seq ν) :
    -(∑ c ∈ ν.toFinset, ((ν.count c * (ν.count c - 1) : ℕ) : ℤ)) ≤
      (klGradingDatum k Γ).degW ρ i := by
  have h := neg_two_mul_card_le_degW (k := k) (Γ := Γ) hρ i
  have h2 := two_mul_card_eqPairs i
  have h3 : (2 * ((eqPairs i).card : ℤ)) = ∑ c ∈ ν.toFinset, ((ν.count c * (ν.count c - 1) : ℕ) : ℤ)
      := by exact_mod_cast h2
  linarith

end KL1

end KL1Bound

/-! ### Graded modules: graded dimensions and characters -/

section Modules

variable {k : Type*} [Field k] [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k}
  {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0) (G : GradingDatum Q) {ν : Multiset I}

namespace GradingDatum

include hPQ hP in
/-- `R(ν)` has a graded dimension (all dots of positive degree). -/
theorem hasGdim_grade' (hX : ∀ a, 0 < G.degX a) : HasGdim (G.grade ν) :=
  G.hasGdim_grade hPQ hP (fun w => canWord _ w)
    (fun w => ⟨isReduced_canWord _ w, wordProd_canWord _ w⟩) hX

include hPQ hP in
/-- **Finitely generated graded `R(ν)`-modules have graded dimensions** (over a field, all dots
of positive degree): their graded pieces are finite-dimensional and vanish in sufficiently
negative degrees. -/
theorem hasGdim_of_finite (hX : ∀ a, 0 < G.degX a) (M : GMod (G.grade ν))
    [Module.Finite (KLRAlgebra k Q ν) M] : HasGdim M.grading :=
  haveI := G.hasGdim_grade' (ν := ν) hPQ hP hX
  Graded.hasGdim_of_finite (G.grade ν) M.grading

include hPQ hP in
/-- Finitely generated graded projective `R(ν)`-modules have graded dimensions. -/
theorem hasGdim_gproj (hX : ∀ a, 0 < G.degX a) (M : GProj (G.grade ν)) :
    HasGdim M.grading :=
  G.hasGdim_of_finite hPQ hP hX M.toGMod

/-- The subspace `1_j (R(ν) 1_i)` of `P_i` is `1_j R(ν) 1_i`. -/
theorem range_idem_leftIdeal (j i : Seq ν) :
    LinearMap.range (((Graded.leftIdeal (e i : KLRAlgebra k Q ν)).subtype.restrictScalars k).comp
      (idemSubspace k (Graded.leftIdeal (e i : KLRAlgebra k Q ν))
        (e j : KLRAlgebra k Q ν)).subtype) =
      corner j i := by
  ext r
  rw [mem_corner_iff]
  constructor
  · rintro ⟨⟨⟨x, hx⟩, hxj⟩, rfl⟩
    have hx' : x * e i = x := hx
    have hxj' : e j * x = x := congrArg Subtype.val hxj
    show e j * x * e i = x
    rw [mul_assoc, hx', hxj']
  · intro h
    refine ⟨⟨⟨r, ?_⟩, Subtype.ext ?_⟩, rfl⟩
    · show r * e i = r
      rw [← h, mul_assoc, e_mul_self]
    · show e j * r = r
      rw [← h, ← mul_assoc, ← mul_assoc, e_mul_self]

/-- **The character of `P_i`**: `ch(P_i, j) = gdim (1_j P_i) = gdim (1_j R(ν) 1_i)`. -/
theorem ch_projP (i j : Seq ν) : G.ch (G.projP i).toGMod j = gdim (G.cornerGrade j i) := by
  refine gdim_eq_of_finrank_eq fun d => ?_
  have h := finrank_comap (G.grade ν)
    (f := ((Graded.leftIdeal (e i : KLRAlgebra k Q ν)).subtype.restrictScalars k).comp
      (idemSubspace k (Graded.leftIdeal (e i : KLRAlgebra k Q ν)) (e j : KLRAlgebra k Q ν)).subtype)
    (Subtype.val_injective.comp Subtype.val_injective) d
  rw [range_idem_leftIdeal] at h
  exact h

include hPQ hP in
/-- **Graded dimension formula for the characters of the `P_i`** (KL I, §2.5):
`ch(P_i, j) = gdim (1_j R(ν) 1_i) = ∑_{w • i = j} q^{deg(ψ_{ρ w} 1_i)}
∏_a (1 - q^{deg x_{a,i}})⁻¹`, for any choice `ρ` of reduced words. -/
theorem ch_projP_eq_sum (ρ : Perm (Fin (Multiset.card ν)) → List ℕ)
    (hρ : ∀ w, IsReduced (Multiset.card ν) (ρ w) ∧ wordProd (Multiset.card ν) (ρ w) = w)
    (hX : ∀ a, 0 < G.degX a) (i j : Seq ν) :
    G.ch (G.projP i).toGMod j = ∑ w ∈ Finset.univ.filter (fun w => w • i = j),
      HahnSeries.single (G.degW (ρ w) i) 1 * ∏ a, geomSeries (G.degX (i.lbl a)) := by
  rw [ch_projP, G.gdim_cornerGrade hPQ hP ρ hρ hX]

end GradingDatum

end Modules

/-! ### KL I -/

section KL1Graded

namespace KL1

variable {k : Type*} [Field k] [DecidableEq I] {Γ : SimpleGraph I} [DecidableRel Γ.Adj]
  {ν : Multiset I}

theorem degX_pos (a : I) : 0 < (klGradingDatum k Γ).degX a := by
  show (0 : ℤ) < 2; norm_num

/-- For KL I, `deg(ψ_ρ 1_i) = - ∑_{(a,b) ∈ inv(w)} i_a · i_b` for any reduced word `ρ` of `w`. -/
theorem degW_eq {ρ : List ℕ} (hρ : IsReduced (Multiset.card ν) ρ) (i : Seq ν) :
    (klGradingDatum k Γ).degW ρ i = -∑ p ∈ invSet (Multiset.card ν) (wordProd (Multiset.card ν) ρ),
      cartan Γ (i.lbl p.1) (i.lbl p.2) := by
  rw [(klGradingDatum k Γ).degW_eq_sum_invSet hρ, ← Finset.sum_neg_distrib]
  rfl

/-- **KL I: `R(ν)` has a graded dimension** (over a field). -/
instance hasGdim_grade : HasGdim ((klGradingDatum k Γ).grade ν) :=
  (klGradingDatum k Γ).hasGdim_grade' (klQ_eq_klP (Γ := Γ) stdOrient_spec)
    (fun a b _ => klP_ne_zero _ a b) degX_pos

/-- **KL I: finitely generated graded `R(ν)`-modules have graded dimensions.** -/
instance hasGdim_of_finite (M : GMod ((klGradingDatum k Γ).grade ν))
    [Module.Finite (R1 k Γ ν) M] : HasGdim M.grading :=
  Graded.hasGdim_of_finite ((klGradingDatum k Γ).grade ν) M.grading

/-- **KL I, end of §2.4**: `R(ν)` is zero in degrees less than `- ∑_i ν_i (ν_i - 1)`. -/
theorem grade_eq_bot_of_lt {d : ℤ}
    (hd : d < -(∑ c ∈ ν.toFinset, ((ν.count c * (ν.count c - 1) : ℕ) : ℤ))) :
    (klGradingDatum k Γ).grade ν d = ⊥ :=
  (klGradingDatum k Γ).grade_eq_bot_of_lt (klQ_eq_klP (Γ := Γ) stdOrient_spec)
    (fun a b _ => klP_ne_zero _ a b) (fun w => canWord _ w)
    (fun w => ⟨isReduced_canWord _ w, wordProd_canWord _ w⟩) (fun a => (degX_pos a).le)
    fun i w => lt_of_lt_of_le hd (neg_sum_le_degW (isReduced_canWord _ w) i)

/-- **KL I: graded dimension of `1_j R(ν) 1_i`**:
`gdim (1_j R(ν) 1_i) = ∑_{w • i = j} q^{- ∑_{(a,b) ∈ inv(w)} i_a · i_b} (1 - q²)^{-m}`. -/
theorem gdim_cornerGrade (j i : Seq ν) :
    gdim ((klGradingDatum k Γ).cornerGrade j i) = ∑ w ∈ Finset.univ.filter (fun w => w • i = j),
      HahnSeries.single (-∑ p ∈ invSet (Multiset.card ν) w, cartan Γ (i.lbl p.1) (i.lbl p.2)) 1 *
        geomSeries 2 ^ Multiset.card ν := by
  rw [(klGradingDatum k Γ).gdim_cornerGrade (klQ_eq_klP (Γ := Γ) stdOrient_spec)
    (fun a b _ => klP_ne_zero _ a b) (fun w => canWord _ w)
    (fun w => ⟨isReduced_canWord _ w, wordProd_canWord _ w⟩) degX_pos]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [degW_eq (isReduced_canWord _ w), wordProd_canWord]
  congr 1
  show ∏ _a : Fin (Multiset.card ν), geomSeries 2 = _
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end KL1

end KL1Graded

end Categorification.KLR

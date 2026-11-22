/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.RedStrands.BraidedStendhal
import Categorification.WeightedKLR.RedStrands.StendhalBasis

/-!
# The basis of `T̃^λ` for symmetric `Q`

This file proves Webster's Proposition 4.16 (arXiv:1309.3796v2) for every symmetric `Q` over
every commutative ring, without the route hypotheses of `stendhalBasis`.

The algebra of Stendhal diagrams with all orders of red strands maps to the KLR algebra of
`stendhalQ Q Λ`: a dot on a red strand goes to zero, and a crossing `ψ_j` goes to `ψ_j` times the
sum of the idempotents whose strands at `j`, `j + 1` are not both red
(`StendhalAlgebraAllOrders.toKLR`). This map sends each Stendhal term `ψ_{ρ w} x^u e(i)` to the
same element of the KLR algebra, so the Stendhal terms are linearly independent by the KLR basis
theorem (KL I, Theorem 2.5, `KLRAlgebra.basisOfSymm`).

## Main results

* `StendhalAlgebraAllOrders.toKLR`: the map to the KLR algebra.
* `linearIndependent_stendhalTerm_of_symm`, `stendhalBasisOfSymm`: Proposition 4.16.
-/

set_option backward.isDefEq.respectTransparency false

namespace Categorification.Stendhal

open MvPolynomial KLR TypeA

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "R" => KLR.KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)

namespace KLRAlgebra

open KLR.KLRAlgebra

/-! ### Pairs of red strands -/

/-- The strands of `i` at positions `j` and `j + 1` are both red. -/
def RedPair (i : Seq μ) (j : ℕ) : Prop :=
  ∃ h : j + 1 < m, (i.lbl ⟨j, by omega⟩).isRight ∧ (i.lbl ⟨j + 1, h⟩).isRight

instance (i : Seq μ) (j : ℕ) : Decidable (RedPair i j) := by
  unfold RedPair; infer_instance

omit [DecidableEq I] in
theorem not_redPair_iff (i : Seq μ) (j : ℕ) :
    ¬ RedPair i j ↔ ∀ h : j + 1 < m, (i.1 ⟨j, by omega⟩).isLeft ∨ (i.1 ⟨j + 1, h⟩).isLeft := by
  simp only [RedPair, not_exists]
  refine forall_congr' fun h => ?_
  change ¬ ((i.1 _).isRight ∧ (i.1 _).isRight) ↔ _
  rcases i.1 ⟨j, by omega⟩ with _ | _ <;> rcases i.1 ⟨j + 1, h⟩ with _ | _ <;> simp

omit [DecidableEq I] in
theorem redPair_sadj_iff (i : Seq μ) (j : ℕ) : RedPair (sadj m j • i) j ↔ RedPair i j := by
  simp only [RedPair]
  refine exists_congr fun h => ?_
  rw [lbl_sadj_left h, lbl_sadj_right h, and_comm]

omit [DecidableEq I] in
theorem redPair_sadj_iff_of_far (i : Seq μ) {j l : ℕ} (hjl : j + 1 < l ∨ l + 1 < j) :
    RedPair (sadj m l • i) j ↔ RedPair i j := by
  simp only [RedPair]
  refine exists_congr fun h => ?_
  rw [lbl_sadj_of_ne i _ (by simp; omega) (by simp; omega),
    lbl_sadj_of_ne i _ (by simp; omega) (by simp; omega)]

omit [DecidableEq I] in
/-- Two distinct positions of `i` carrying red strands carry different labels. -/
theorem lbl_ne_of_redPair {i : Seq μ} {j : ℕ} (h : j + 1 < m)
    (hr : (i.lbl ⟨j, by omega⟩).isRight) :
    i.lbl ⟨j, by omega⟩ ≠ i.lbl ⟨j + 1, h⟩ := fun he =>
  absurd (eq_of_lbl_eq_of_isRight i he hr) (by simp [Fin.ext_iff])

/-! ### The idempotent away from red pairs -/

open Classical in
/-- The sum of the idempotents whose strands at `j`, `j + 1` are not both red. -/
noncomputable def okIdem (j : ℕ) : R :=
  ∑ i ∈ Finset.univ.filter (fun i : Seq μ => ¬ RedPair i j), e i

theorem okIdem_mul_e (j : ℕ) (i : Seq μ) :
    (okIdem j * e i : R) = if RedPair i j then 0 else e i := by
  classical
  simp only [okIdem, Finset.sum_mul, e_mul_e, Finset.sum_ite_eq', Finset.mem_filter,
    Finset.mem_univ, true_and]
  split_ifs <;> simp_all

theorem e_mul_okIdem (j : ℕ) (i : Seq μ) :
    (e i * okIdem j : R) = if RedPair i j then 0 else e i := by
  classical
  simp only [okIdem, Finset.mul_sum, e_mul_e, Finset.sum_ite_eq, Finset.mem_filter,
    Finset.mem_univ, true_and]
  split_ifs <;> simp_all

theorem okIdem_commute_e (j : ℕ) (i : Seq μ) : Commute (okIdem j : R) (e i) := by
  change _ * _ = _ * _
  rw [okIdem_mul_e, e_mul_okIdem]

theorem okIdem_commute_blackDot (j : ℕ) (a : Fin m) : Commute (okIdem j : R) (blackDot a) := by
  classical
  exact Commute.sum_left _ _ _ fun i _ => (blackDot_commute_e a i).symm

theorem okIdem_commute_okIdem (j l : ℕ) : Commute (okIdem j : R) (okIdem l) := by
  classical
  exact Commute.sum_left _ _ _ fun i _ => (okIdem_commute_e l i).symm

theorem okIdem_commute_ψ_of_far {j l : ℕ} (hjl : j + 1 < l ∨ l + 1 < j) :
    Commute (okIdem j : R) (ψ l) := by
  change _ * _ = _ * _
  refine eq_of_forall_mul_e fun i => ?_
  rw [mul_assoc, ψ_mul_e, ← mul_assoc, okIdem_mul_e, mul_assoc, okIdem_mul_e]
  simp only [redPair_sadj_iff_of_far i hjl]
  split_ifs <;> simp [ψ_mul_e]

/-- The crossing `ψ_j` followed by `okIdem j`. -/
noncomputable def okψ (j : ℕ) : R := ψ j * okIdem j

theorem okψ_mul_e (j : ℕ) (i : Seq μ) :
    (okψ j * e i : R) = if RedPair i j then 0 else ψ j * e i := by
  rw [okψ, mul_assoc, okIdem_mul_e]
  split_ifs <;> simp

theorem okψ_eq (j : ℕ) : (okψ j : R) = okIdem j * ψ j := by
  refine eq_of_forall_mul_e fun i => ?_
  rw [okψ_mul_e, mul_assoc, ψ_mul_e, ← mul_assoc, okIdem_mul_e]
  simp only [redPair_sadj_iff]
  split_ifs <;> simp

open Classical in
/-- A word of crossings `okψ` acts on `e(i)` as the word of crossings `ψ`, unless it exchanges two
red strands. -/
theorem okψw_mul_e (ρ : List ℕ) (i : Seq μ) :
    ((ρ.map okψ).prod * e i : R) = if NoRedCross ρ i then ψw ρ * e i else 0 := by
  induction ρ with
  | nil => simp [NoRedCross]
  | cons j ρ ih =>
    rw [List.map_cons, List.prod_cons, mul_assoc, ih]
    simp only [NoRedCross, ← not_redPair_iff]
    by_cases hρ : NoRedCross ρ i
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hρ), ψw_mul_e, ← mul_assoc, okψ_mul_e, ψw_cons]
      by_cases hr : RedPair (wordProd m ρ • i) j
      · simp [hr]
      · simp only [hr, ↓reduceIte, not_false_eq_true, hρ, and_self, mul_assoc, ψw_mul_e]
    · simp [hρ]

/-! ### Three strands -/

private theorem fin_mk_ne {n a b : ℕ} (h : a < n) (hab : a ≠ b) : ((⟨a, h⟩ : Fin n) : ℕ) ≠ b :=
  hab

/-- The strands of `i` at positions `a` and `b` are both red. -/
def BothRed (i : Seq μ) (a b : Fin m) : Prop := (i.lbl a).isRight ∧ (i.lbl b).isRight

omit [DecidableEq I] in
theorem redPair_iff (i : Seq μ) {j : ℕ} (h : j + 1 < m) :
    RedPair i j ↔ BothRed i ⟨j, by omega⟩ ⟨j + 1, h⟩ :=
  ⟨fun ⟨_, h₁, h₂⟩ => ⟨h₁, h₂⟩, fun hr => ⟨h, hr⟩⟩

omit [DecidableEq I] in
theorem redPair_sadj_succ_iff (i : Seq μ) {j : ℕ} (h : j + 2 < m) :
    RedPair (sadj m j • i) (j + 1) ↔ BothRed i ⟨j, by omega⟩ ⟨j + 2, h⟩ := by
  rw [redPair_iff _ (by omega), BothRed, BothRed, lbl_sadj_right (by omega),
    lbl_sadj_of_ne i ⟨j + 1 + 1, _⟩ (fin_mk_ne _ (by omega)) (fin_mk_ne _ (by omega))]

omit [DecidableEq I] in
theorem redPair_sadj_pred_iff (i : Seq μ) {j : ℕ} (h : j + 2 < m) :
    RedPair (sadj m (j + 1) • i) j ↔ BothRed i ⟨j, by omega⟩ ⟨j + 2, h⟩ := by
  rw [redPair_iff _ (by omega), BothRed, BothRed, lbl_sadj_left (by omega),
    lbl_sadj_of_ne i ⟨j, _⟩ (fin_mk_ne _ (by omega)) (fin_mk_ne _ (by omega))]

omit [DecidableEq I] in
theorem noRedCross_cons_iff (j : ℕ) (ρ : List ℕ) (i : Seq μ) :
    NoRedCross (j :: ρ) i ↔ NoRedCross ρ i ∧ ¬ RedPair (wordProd m ρ • i) j := by
  rw [NoRedCross, not_redPair_iff]

omit [DecidableEq I] in
theorem noRedCross_braid_left_iff (i : Seq μ) {j : ℕ} (h : j + 2 < m) :
    NoRedCross [j, j + 1, j] i ↔ ¬ (BothRed i ⟨j, by omega⟩ ⟨j + 1, by omega⟩ ∨
      BothRed i ⟨j, by omega⟩ ⟨j + 2, h⟩ ∨ BothRed i ⟨j + 1, by omega⟩ ⟨j + 2, h⟩) := by
  rw [noRedCross_cons_iff, noRedCross_cons_iff, noRedCross_cons_iff]
  simp only [NoRedCross, wordProd_cons, wordProd_nil, mul_one, one_smul, mul_smul, true_and]
  have hc : RedPair (sadj m (j + 1) • sadj m j • i) j ↔
      BothRed i ⟨j + 1, by omega⟩ ⟨j + 2, h⟩ := by
    rw [redPair_iff _ (by omega), BothRed, BothRed,
      lbl_sadj_of_ne _ ⟨j, _⟩ (fin_mk_ne _ (by omega)) (fin_mk_ne _ (by omega)),
      lbl_sadj_left (by omega), lbl_sadj_left (by omega),
      lbl_sadj_of_ne i ⟨j + 1 + 1, _⟩ (fin_mk_ne _ (by omega)) (fin_mk_ne _ (by omega))]
  rw [redPair_iff _ (by omega), redPair_sadj_succ_iff _ h, hc]
  tauto

omit [DecidableEq I] in
theorem noRedCross_braid_right_iff (i : Seq μ) {j : ℕ} (h : j + 2 < m) :
    NoRedCross [j + 1, j, j + 1] i ↔ ¬ (BothRed i ⟨j, by omega⟩ ⟨j + 1, by omega⟩ ∨
      BothRed i ⟨j, by omega⟩ ⟨j + 2, h⟩ ∨ BothRed i ⟨j + 1, by omega⟩ ⟨j + 2, h⟩) := by
  rw [noRedCross_cons_iff, noRedCross_cons_iff, noRedCross_cons_iff]
  simp only [NoRedCross, wordProd_cons, wordProd_nil, mul_one, one_smul, mul_smul, true_and]
  have ha : RedPair (sadj m j • sadj m (j + 1) • i) (j + 1) ↔
      BothRed i ⟨j, by omega⟩ ⟨j + 1, by omega⟩ := by
    rw [redPair_iff _ (by omega), BothRed, BothRed, lbl_sadj_right (by omega),
      lbl_sadj_of_ne _ ⟨j + 1 + 1, _⟩ (fin_mk_ne _ (by omega)) (fin_mk_ne _ (by omega)),
      lbl_sadj_of_ne i ⟨j, _⟩ (fin_mk_ne _ (by omega))
      (fin_mk_ne _ (by omega)), lbl_sadj_right (by omega)]
  have hc : RedPair i (j + 1) ↔ BothRed i ⟨j + 1, by omega⟩ ⟨j + 2, h⟩ := redPair_iff i h
  rw [hc, redPair_sadj_pred_iff _ h, ha]
  tauto


/-! ### The map on the free algebra -/

/-- The generators of the KLR algebra, with dots on red strands and crossings of two red strands
set to zero. -/
noncomputable def okGen : Gen μ → R
  | .idem i => e i
  | .dot a => blackDot a
  | .cross j => okψ j

/-- The free algebra on the generators maps to `R` through `okGen`. -/
noncomputable def okFree : FreeAlgebra k (Gen μ) →ₐ[k] R :=
  FreeAlgebra.lift k okGen

@[simp] theorem okFree_fe (i : Seq μ) : okFree (Q := Q) (Λ := Λ) (fe k μ i) = e i :=
  FreeAlgebra.lift_ι_apply _ _
@[simp] theorem okFree_fx (a : Fin m) :
    okFree (Q := Q) (Λ := Λ) (fx k μ a) = blackDot a :=
  FreeAlgebra.lift_ι_apply _ _
@[simp] theorem okFree_fψ (j : ℕ) : okFree (Q := Q) (Λ := Λ) (fψ k μ j) = okψ j :=
  FreeAlgebra.lift_ι_apply _ _

theorem okFree_ncEval_fx {n : ℕ} (f : Fin n → Fin m) (p : MvPolynomial (Fin n) k) :
    okFree (Q := Q) (Λ := Λ) (ncEval (fun b => fx k μ (f b)) p) =
      blackFree (ncEval (fun b => fx k μ (f b)) p) := by
  rw [algHom_ncEval, algHom_ncEval]
  simp only [okFree_fx, blackFree_fx]

omit [DecidableEq I] in
theorem not_isRight_of_isLeft {x : I ⊕ Fin ℓ} (h : x.isLeft) : ¬ x.isRight := by
  cases x <;> simp_all

/-- `okFree` respects the KLR relations. -/
theorem okFree_rel {y z : FreeAlgebra k (Gen μ)} (h : KLR.Rel k (stendhalQ Q Λ) μ y z) :
    okFree (Q := Q) (Λ := Λ) y = okFree z := by
  cases h with
  | idem_mul i j =>
    simp only [map_mul, okFree_fe, e_mul_e]
    split_ifs <;> simp
  | idem_sum => simp [map_sum, sum_e]
  | dot_idem a i =>
    simp only [map_mul, okFree_fe, okFree_fx]; exact (blackDot_commute_e a i).eq
  | cross_idem j i =>
    simp only [map_mul, okFree_fe, okFree_fψ]
    rw [okψ_mul_e, okψ_eq, ← mul_assoc, e_mul_okIdem]
    simp only [redPair_sadj_iff]
    split_ifs <;> simp [ψ_mul_e]
  | cross_zero j h => simp only [okFree_fψ, map_zero]; rw [okψ, ψ_eq_zero j h, zero_mul]
  | dot_dot a b =>
    have := blackFree_rel (Q := Q) (Λ := Λ) (KLR.Rel.dot_dot (k := k) (ν := μ) a b)
    simpa only [map_mul, blackFree_fx, okFree_fx] using this
  | cross_cross j l h =>
    simp only [map_mul, okFree_fψ, okψ]
    have c1 := (okIdem_commute_ψ_of_far (Q := Q) (Λ := Λ) (ν := ν) (Or.inl h)).eq
    have c2 := (okIdem_commute_ψ_of_far (Q := Q) (Λ := Λ) (ν := ν) (j := l) (l := j)
      (Or.inr h)).eq
    have c3 := (okIdem_commute_okIdem (Q := Q) (Λ := Λ) (ν := ν) j l).eq
    calc ψ j * okIdem j * (ψ l * okIdem l) = ψ j * ψ l * (okIdem j * okIdem l) := by
          simp only [mul_assoc]; rw [← mul_assoc (okIdem j), c1, mul_assoc]
      _ = ψ l * ψ j * (okIdem l * okIdem j) := by rw [ψ_mul_ψ j l h, c3]
      _ = ψ l * okIdem l * (ψ j * okIdem j) := by
          simp only [mul_assoc]; rw [← mul_assoc (okIdem l), c2, mul_assoc]
  | dot_cross a j h₁ h₂ =>
    have key := blackFree_rel (Q := Q) (Λ := Λ) (KLR.Rel.dot_cross (k := k) (ν := μ) a j h₁ h₂)
    simp only [map_mul, blackFree_fx, blackFree_fψ] at key
    simp only [map_mul, okFree_fx, okFree_fψ, okψ]
    rw [← mul_assoc, key, mul_assoc, ← (okIdem_commute_blackDot j a).eq, mul_assoc]
  | dot_cross_left j h i =>
    have key := blackFree_rel (Q := Q) (Λ := Λ) (KLR.Rel.dot_cross_left (k := k) (ν := μ) j h i)
    simp only [map_mul, map_sub, blackFree_fx, blackFree_fψ, blackFree_fe,
      apply_ite (blackFree (Q := Q) (Λ := Λ)), map_zero] at key
    simp only [map_mul, map_sub, okFree_fx, okFree_fψ, okFree_fe,
      apply_ite (okFree (Q := Q) (Λ := Λ)), map_zero]
    rw [sub_mul, mul_assoc, okψ_mul_e, mul_assoc (okψ j), (blackDot_commute_e _ i).eq,
      ← mul_assoc (okψ j), okψ_mul_e]
    by_cases hr : RedPair i j
    · obtain ⟨_, h1, _⟩ := id hr
      simp [hr, lbl_ne_of_redPair h h1]
    · simp only [hr, ↓reduceIte]
      rw [← key, sub_mul, mul_assoc, mul_assoc (ψ j), (blackDot_commute_e _ i).eq, mul_assoc]
  | dot_cross_right j h i =>
    have key := blackFree_rel (Q := Q) (Λ := Λ)
      (KLR.Rel.dot_cross_right (k := k) (ν := μ) j h i)
    simp only [map_mul, map_sub, blackFree_fx, blackFree_fψ, blackFree_fe,
      apply_ite (blackFree (Q := Q) (Λ := Λ)), map_zero] at key
    simp only [map_mul, map_sub, okFree_fx, okFree_fψ, okFree_fe,
      apply_ite (okFree (Q := Q) (Λ := Λ)), map_zero]
    rw [sub_mul, mul_assoc, (blackDot_commute_e _ i).eq, ← mul_assoc, okψ_mul_e,
      mul_assoc (blackDot _), okψ_mul_e]
    by_cases hr : RedPair i j
    · obtain ⟨_, h1, _⟩ := id hr
      simp [hr, lbl_ne_of_redPair h h1]
    · simp only [hr, ↓reduceIte]
      rw [← key, sub_mul, mul_assoc, mul_assoc (blackDot _), mul_assoc (ψ j),
        (blackDot_commute_e _ i).eq]
  | cross_sq j h i =>
    simp only [map_mul, okFree_fψ, okFree_fe]
    by_cases hr : RedPair i j
    · obtain ⟨_, h1, h2⟩ := id hr
      rw [mul_assoc, okψ_mul_e, apply_ite (okFree (Q := Q) (Λ := Λ))]
      simp only [hr, ↓reduceIte, mul_zero, lbl_ne_of_redPair h h1]
      rcases ha : i.lbl ⟨j, by omega⟩ with a | r
      · simp [ha] at h1
      rcases hb : i.lbl ⟨j + 1, h⟩ with b | t
      · simp [hb] at h2
      simp [stendhalQ, ncEval]
    · have key := blackFree_rel (Q := Q) (Λ := Λ) (KLR.Rel.cross_sq (k := k) (ν := μ) j h i)
      simp only [map_mul, blackFree_fψ, blackFree_fe] at key
      rw [mul_assoc, okψ_mul_e]
      simp only [hr, ↓reduceIte]
      rw [ψ_mul_e, ← mul_assoc, okψ_mul_e]
      simp only [redPair_sadj_iff, hr, ↓reduceIte]
      rw [mul_assoc, ← ψ_mul_e, ← mul_assoc, key, apply_ite (okFree (Q := Q) (Λ := Λ)),
        apply_ite (blackFree (Q := Q) (Λ := Λ))]
      split_ifs
      · simp
      · rw [vec_fx_two, map_mul, map_mul, okFree_ncEval_fx, okFree_fe, blackFree_fe]
  | braid j h i =>
    have key := blackFree_rel (Q := Q) (Λ := Λ) (KLR.Rel.braid (k := k) (ν := μ) j h i)
    simp only [map_mul, map_sub, blackFree_fψ, blackFree_fe] at key
    simp only [map_mul, map_sub, okFree_fψ, okFree_fe]
    have hl := okψw_mul_e (Q := Q) (Λ := Λ) [j, j + 1, j] i
    have hr := okψw_mul_e (Q := Q) (Λ := Λ) [j + 1, j, j + 1] i
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, ψw] at hl hr
    simp only [mul_assoc] at hl hr key ⊢
    rw [sub_mul, mul_assoc, mul_assoc, hl, mul_assoc, mul_assoc, hr]
    by_cases hD : BothRed i ⟨j, by omega⟩ ⟨j + 1, by omega⟩ ∨
        BothRed i ⟨j, by omega⟩ ⟨j + 2, h⟩ ∨ BothRed i ⟨j + 1, by omega⟩ ⟨j + 2, h⟩
    · have n1 : ¬ NoRedCross [j, j + 1, j] i := fun h' => (noRedCross_braid_left_iff i h).1 h' hD
      have n2 : ¬ NoRedCross [j + 1, j, j + 1] i := fun h' =>
        (noRedCross_braid_right_iff i h).1 h' hD
      simp only [n1, n2, ↓reduceIte, sub_zero]
      rw [apply_ite (okFree (Q := Q) (Λ := Λ)), ite_eq_right_iff.2 (fun hc' => absurd hc' ?_),
        map_zero]
      rintro ⟨hc, -⟩
      have h0 : (i.lbl ⟨j, by omega⟩).isLeft :=
        isLeft_of_isRight_eq (by simp [Fin.ext_iff]) hc
      have h2 : (i.lbl ⟨j + 2, h⟩).isLeft := hc ▸ h0
      rcases hD with ⟨h3, -⟩ | ⟨h3, -⟩ | ⟨-, h3⟩
      · exact not_isRight_of_isLeft h0 h3
      · exact not_isRight_of_isLeft h0 h3
      · exact not_isRight_of_isLeft h2 h3
    · have n1 : NoRedCross [j, j + 1, j] i := (noRedCross_braid_left_iff i h).2 hD
      have n2 : NoRedCross [j + 1, j, j + 1] i := (noRedCross_braid_right_iff i h).2 hD
      simp only [n1, n2, ↓reduceIte]
      have e1 : ψ j * (ψ (j + 1) * (ψ j * e i)) - ψ (j + 1) * (ψ j * (ψ (j + 1) * e i)) =
          (ψ j * (ψ (j + 1) * ψ j) - ψ (j + 1) * (ψ j * ψ (j + 1))) * (e i : R) := by
        simp only [sub_mul, mul_assoc]
      rw [e1, key, apply_ite (okFree (Q := Q) (Λ := Λ)),
        apply_ite (blackFree (Q := Q) (Λ := Λ))]
      split_ifs
      · rw [vec_fx_three, map_mul, map_mul, okFree_ncEval_fx, okFree_fe, blackFree_fe]
      · simp

end KLRAlgebra

namespace StendhalAlgebraAllOrders

open KLRAlgebra

variable (k Q Λ ν) in
/-- The map to the KLR algebra of `stendhalQ Q Λ` killing dots on red strands and crossings of
two red strands. -/
noncomputable def toKLR : StendhalAlgebraAllOrders k Q Λ ν →ₐ[k] R :=
  RingQuot.liftAlgHom k ⟨KLRAlgebra.okFree, fun _ _ h => by
    cases h with
    | klr h => exact KLRAlgebra.okFree_rel h
    | red_dot a i h =>
      rw [map_mul, KLRAlgebra.okFree_fx, KLRAlgebra.okFree_fe, KLRAlgebra.blackDot_mul_e',
        map_zero]
      rcases hl : i.lbl a with _ | _
      · simp [hl] at h
      · simp
    | red_cross j h i h₁ h₂ =>
      have hr : KLRAlgebra.RedPair i j := ⟨h, h₁, h₂⟩
      rw [map_mul, KLRAlgebra.okFree_fψ, KLRAlgebra.okFree_fe, KLRAlgebra.okψ_mul_e, map_zero]
      simp only [hr, ↓reduceIte]⟩

theorem toKLR_ofKLR_mk (a : FreeAlgebra k (Gen μ)) :
    toKLR k Q Λ ν (ofKLR k Q Λ ν (KLR.KLRAlgebra.mk k _ _ a)) = KLRAlgebra.okFree a := by
  rw [ofKLR_mk]
  exact RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _

theorem toKLR_ofKLR_e (i : Seq μ) :
    toKLR k Q Λ ν (ofKLR k Q Λ ν (KLR.KLRAlgebra.e i)) = KLR.KLRAlgebra.e i := by
  rw [KLR.KLRAlgebra.e, toKLR_ofKLR_mk, KLRAlgebra.okFree_fe]
  rfl

theorem toKLR_ofKLR_x (a : Fin m) :
    toKLR k Q Λ ν (ofKLR k Q Λ ν (KLR.KLRAlgebra.x a)) = KLRAlgebra.blackDot a := by
  rw [KLR.KLRAlgebra.x, toKLR_ofKLR_mk, KLRAlgebra.okFree_fx]

theorem toKLR_ofKLR_ψ (j : ℕ) :
    toKLR k Q Λ ν (ofKLR k Q Λ ν (KLR.KLRAlgebra.ψ j)) = KLRAlgebra.okψ j := by
  rw [KLR.KLRAlgebra.ψ, toKLR_ofKLR_mk, KLRAlgebra.okFree_fψ]

theorem toKLR_ofKLR_ψw (ρ : List ℕ) :
    toKLR k Q Λ ν (ofKLR k Q Λ ν (KLR.KLRAlgebra.ψw ρ)) = (ρ.map KLRAlgebra.okψ).prod := by
  rw [KLR.KLRAlgebra.ψw, map_list_prod, map_list_prod, List.map_map, List.map_map]
  congr 1
  exact List.map_congr_left fun j _ => toKLR_ofKLR_ψ j

theorem toKLR_ofKLR_pol_mul_e (p : MvPolynomial (Fin m) k) (i : Seq μ) :
    toKLR k Q Λ ν (ofKLR k Q Λ ν (KLR.KLRAlgebra.pol p * KLR.KLRAlgebra.e i)) =
      KLR.KLRAlgebra.pol (KLRAlgebra.blackSubst i p) * KLR.KLRAlgebra.e i := by
  rw [map_mul, map_mul, toKLR_ofKLR_e]
  have := KLR.KLRAlgebra.ncEval_eq_pol (k := k) (Q := stendhalQ Q Λ) (ν := μ) id p
  simp only [rename_id, AlgHom.id_apply] at this
  rw [← this, algHom_ncEval, algHom_ncEval]
  simp only [id, toKLR_ofKLR_x]
  have h2 := KLRAlgebra.ncEval_blackDot_mul_e (Q := Q) (Λ := Λ) id p i
  simpa only [rename_id, AlgHom.id_apply, id] using h2

/-- `toKLR` fixes a KLR basis element with no dot on a red strand and no crossing of two red
strands. -/
theorem toKLR_ofKLR_std (ρ : List ℕ) (u : Fin m →₀ ℕ) (i : Seq μ)
    (hu : ∀ a, (i.lbl a).isRight → u a = 0) (hρ : NoRedCross ρ i) :
    toKLR k Q Λ ν (ofKLR k Q Λ ν
      (KLR.KLRAlgebra.ψw ρ * KLR.KLRAlgebra.pol (monomial u 1) * KLR.KLRAlgebra.e i)) =
      KLR.KLRAlgebra.ψw ρ * KLR.KLRAlgebra.pol (monomial u 1) * KLR.KLRAlgebra.e i := by
  classical
  rw [mul_assoc, map_mul, map_mul, toKLR_ofKLR_ψw, toKLR_ofKLR_pol_mul_e,
    KLRAlgebra.blackSubst_monomial i u hu, ← (e_commute_pol i _).eq, ← mul_assoc,
    okψw_mul_e, ite_eq_left_of_eq_true _ _ (eq_true hρ), mul_assoc, (e_commute_pol i _).eq]

end StendhalAlgebraAllOrders

/-! ### Proposition 4.16 for symmetric `Q` -/

section Basis

open StendhalAlgebraAllOrders Equiv

variable {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}

/-- `toKLR` sends each Stendhal term to the same KLR basis element. -/
theorem toKLR_stendhalTerm (hρ : ∀ w, wordProd m (ρ w) = w)
    (b : {b // IsStendhalTerm (ν := ν) (ℓ := ℓ) ρ b}) :
    toKLR k Q Λ ν (stendhalValₗ (stendhalTerm Q Λ hρ b)) = KLR.KLRAlgebra.stdElt ρ b.1 := by
  change toKLR k Q Λ ν (stendhalTerm Q Λ hρ b).1 = _
  rw [stendhalTerm_val, KLR.KLRAlgebra.stdElt]
  refine toKLR_ofKLR_std _ _ _ (fun a ha => ?_) b.2.2.2.2
  by_contra hu
  exact KLRAlgebra.not_isRight_of_isLeft (b.2.2.2.1 a (Finsupp.mem_support_iff.2 hu)) ha

/-- The Stendhal terms are linearly independent in `T̃^λ` for symmetric `Q`, over every
commutative ring (arXiv:1309.3796v2, Proposition 4.16). -/
theorem linearIndependent_stendhalTerm_of_symm (hQ : KLRSymm Q)
    (hρ : ∀ w, IsReduced m (ρ w) ∧ wordProd m (ρ w) = w) :
    LinearIndependent k (stendhalTerm Q Λ (ν := ν) (fun w => (hρ w).2)) := by
  have hB :=
    (KLR.KLRAlgebra.basisOfSymm (stendhalQ_symm (Q := Q) (Λ := Λ) hQ) ρ hρ).linearIndependent
  refine LinearIndependent.of_comp ((toKLR k Q Λ ν).toLinearMap ∘ₗ stendhalValₗ) ?_
  have : (⇑((toKLR k Q Λ ν).toLinearMap ∘ₗ stendhalValₗ) ∘
      stendhalTerm Q Λ (ν := ν) (fun w => (hρ w).2)) =
      KLR.KLRAlgebra.basisOfSymm (stendhalQ_symm (Q := Q) (Λ := Λ) hQ) ρ hρ ∘ Subtype.val := by
    funext b
    simp only [Function.comp_apply, LinearMap.coe_comp, AlgHom.toLinearMap_apply,
      KLR.KLRAlgebra.basisOfSymm_apply]
    exact toKLR_stendhalTerm _ b
  rw [this]
  exact hB.comp _ Subtype.val_injective

variable (Q Λ) in
/-- **A basis of `T̃^λ`** (arXiv:1309.3796v2, Proposition 4.16) for symmetric `Q`, over every
commutative ring: the Stendhal terms `ψ_{ρ w} x^u e(i)`, for a choice `ρ` of reduced words
(`IsStendhalTerm`). Webster's basis is indexed by loadings; this one is the image of the KLR basis
(KL I, Theorem 2.5). -/
noncomputable def stendhalBasisOfSymm (hQ : KLRSymm Q) (ρ : Perm (Fin m) → List ℕ)
    (hρ : ∀ w, IsReduced m (ρ w) ∧ wordProd m (ρ w) = w) :
    Module.Basis {b // IsStendhalTerm (ν := ν) (ℓ := ℓ) ρ b} k (StendhalAlgebra k Q Λ ν) :=
  Module.Basis.mk (linearIndependent_stendhalTerm_of_symm hQ hρ) (span_stendhalTerm hρ)

theorem stendhalBasisOfSymm_apply (hQ : KLRSymm Q) (ρ : Perm (Fin m) → List ℕ)
    (hρ : ∀ w, IsReduced m (ρ w) ∧ wordProd m (ρ w) = w)
    (b : {b // IsStendhalTerm (ν := ν) (ℓ := ℓ) ρ b}) :
    stendhalBasisOfSymm Q Λ hQ ρ hρ b = stendhalTerm Q Λ (ν := ν) (fun w => (hρ w).2) b :=
  Module.Basis.mk_apply _ _ _

end Basis

end Categorification.Stendhal

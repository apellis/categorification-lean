/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.NilHecke.Basic

/-!
# The nilHecke relations at symbolic width

For every width `n` and every admissible position, the dots `x k n i` and crossings `ψ k n i`
of `NH k` satisfy the nilHecke relations of KL I (arXiv:0803.4121v2), §2.2, Example 3
(indices shifted to start at `0`, products are composition of operators); these are the
relations `NilHecke.mulX_mul_mulX`, …, `NilHecke.dd_mulX_sub_mulX_dd` of
`Categorification.Algebra.NilHecke`:

* `ψ_mul_ψ`: `ψ_i ψ_i = 0`;
* `ψ_braid`: `ψ_i ψ_{i+1} ψ_i = ψ_{i+1} ψ_i ψ_{i+1}`;
* `x_mul_ψ_sub_ψ_mul_x`: `x_i ψ_i - ψ_i x_{i+1} = 1`;
* `ψ_mul_x_sub_x_mul_ψ`: `ψ_i x_i - x_{i+1} ψ_i = 1`;
* `x_mul_x_comm`, `x_mul_ψ_comm`, `ψ_mul_ψ_comm`: far commutativity.

The first four are whiskered defining relations. Far commutativity is not a defining
relation: it is an instance of the interchange law (`interchange_at`). No case analysis on `n`
is involved.
-/

noncomputable section

namespace Categorification.NilHecke.Diagram

open CategoryTheory StringDiagrams

variable (k : Type*) [CommRing k]

/-- `i` strands, used to whisker on the left. -/
def shift (i : ℕ) : Obj sig := ⟨(), List.replicate i ()⟩

theorem whisker_strands {w i n : ℕ} (h : i + w ≤ n) :
    (strands w).whisker (shift i) (List.replicate (n - i - w) ()) = strands n :=
  obj_ext (by simp [strands, shift, Obj.whisker]; omega)

/-- A defining relation, transported to position `i` in width `n`. -/
theorem relation_at (r : Rel) {n i : ℕ} (h : i + r.width ≤ n) :
    (pres k).lin (LinDiagram.cast (LinDiagram.whisker (relation k r) (shift i)
      (List.replicate (n - i - r.width) ()) (Obj.whiskerOK_of_subsingleton _ _ _))
      (whisker_strands h) (whisker_strands h)) = 0 :=
  (pres k).lin_rel_cast r (shift i) _ _ _ _

/-- The interchange law for generators `g` (at position `i`) and `h` (at position `j`,
to the right of `g`) in width `n`. -/
theorem interchange_at (g h : Gen) {n i j : ℕ} (hij : i + g.arity ≤ j) (hn : j + h.arity ≤ n) :
    (pres k).diag (dlay (n := n) (i := i) (g := g) (by omega)) ≫
        (pres k).diag (dlay (n := n) (i := j) (g := h) hn) =
      (pres k).diag (dlay (n := n) (i := j) (g := h) hn) ≫
        (pres k).diag (dlay (n := n) (i := i) (g := g) (by omega)) := by
  let d : InterchangeData sig := ⟨(), g, List.replicate (j - i - g.arity) (), h⟩
  have hx : d.Valid := InterchangeData.valid_of_subsingleton d
  have hd : d.dom.whisker (shift i) (List.replicate (n - j - h.arity) ()) = strands n :=
    obj_ext (by simp [d, InterchangeData.dom, shift, strands, sig]; omega)
  have hc : d.cod.whisker (shift i) (List.replicate (n - j - h.arity) ()) = strands n :=
    obj_ext (by simp [d, InterchangeData.cod, shift, strands, sig]; omega)
  have key := (pres k).diag_interchange d hx (shift i) _
    (Obj.whiskerOK_of_subsingleton _ _ _) hd hc
  have hs : ((d.sign : ℤ) : k) = 1 := by simp [d, InterchangeData.sign, sig]
  rw [hs, one_smul] at key
  rw [← Presentation.diag_comp, ← Presentation.diag_comp]
  refine Eq.trans ?_ (key.trans ?_)
  · apply Presentation.diag_eq_of_layers_eq
    simp [d, dlay, lay, shift, Layer.whisker, InterchangeData.ghDiagram,
      InterchangeData.gh₁, InterchangeData.gh₂, sig]
    omega
  · apply Presentation.diag_eq_of_layers_eq
    simp [d, dlay, lay, shift, Layer.whisker, InterchangeData.hgDiagram,
      InterchangeData.hg₁, InterchangeData.hg₂, sig]
    omega

/-! ## Defining relations -/

theorem ψ_mul_ψ (n i : ℕ) : ψ k n i * ψ k n i = 0 := by
  by_cases h : i + 1 < n
  · have key := relation_at k .crossSq (n := n) (i := i) (by simp [Rel.width]; omega)
    rw [show relation k .crossSq = LinDiagram.of _ from rfl, LinDiagram.whisker_of,
      LinDiagram.cast_of, Presentation.lin_of] at key
    rw [ψ_def k h, End.mul_def, ← Presentation.diag_comp, ← key]
    apply Presentation.diag_eq_of_layers_eq
    simp [dlay, lay, shift, Layer.whisker, Gen.arity, Rel.width]
  · rw [ψ_of_le k (by omega), mul_zero]

theorem ψ_braid (n i : ℕ) :
    ψ k n i * ψ k n (i + 1) * ψ k n i = ψ k n (i + 1) * ψ k n i * ψ k n (i + 1) := by
  by_cases h : i + 2 < n
  · have key := relation_at k .braid (n := n) (i := i) (by simp [Rel.width]; omega)
    rw [show relation k .braid = LinDiagram.of _ - LinDiagram.of _ from rfl,
      LinDiagram.whisker_sub, LinDiagram.whisker_of, LinDiagram.whisker_of, LinDiagram.cast_sub,
      LinDiagram.cast_of, LinDiagram.cast_of, Presentation.lin_sub, Presentation.lin_of,
      Presentation.lin_of, sub_eq_zero] at key
    rw [ψ_def k (show i + 1 < n by omega), ψ_def k h]
    simp only [End.mul_def, ← Presentation.diag_comp]
    convert key using 1 <;> apply Presentation.diag_eq_of_layers_eq <;>
      simp [dlay, lay, shift, Layer.whisker, Gen.arity, Rel.width] <;> omega
  · by_cases h' : i + 1 < n
    · rw [ψ_of_le k (n := n) (i := i + 1) (by omega)]; simp
    · rw [ψ_of_le k (n := n) (i := i) (by omega)]; simp

theorem x_mul_ψ_sub_ψ_mul_x {n i : ℕ} (h : i + 1 < n) :
    x k n i * ψ k n i - ψ k n i * x k n (i + 1) = 1 := by
  have key := relation_at k .slideA (n := n) (i := i) (by simp [Rel.width]; omega)
  rw [show relation k .slideA = LinDiagram.of _ - LinDiagram.of _ - LinDiagram.of _ from rfl,
    LinDiagram.whisker_sub, LinDiagram.whisker_sub, LinDiagram.whisker_of, LinDiagram.whisker_of,
    LinDiagram.whisker_of, LinDiagram.cast_sub, LinDiagram.cast_sub, LinDiagram.cast_of,
    LinDiagram.cast_of, LinDiagram.cast_of, Presentation.lin_sub, Presentation.lin_sub,
    Presentation.lin_of, Presentation.lin_of, Presentation.lin_of, sub_eq_zero] at key
  rw [x_def k (show i < n by omega), x_def k h, ψ_def k h]
  simp only [End.mul_def, ← Presentation.diag_comp, End.one_def]
  refine Eq.trans ?_ (key.trans ?_)
  · congr 1 <;> apply Presentation.diag_eq_of_layers_eq <;>
      simp [dlay, lay, shift, Layer.whisker, Gen.arity, Rel.width]
    all_goals omega
  · refine Eq.trans ?_ ((pres k).diag_id _)
    apply Presentation.diag_eq_of_layers_eq
    simp

theorem ψ_mul_x_sub_x_mul_ψ {n i : ℕ} (h : i + 1 < n) :
    ψ k n i * x k n i - x k n (i + 1) * ψ k n i = 1 := by
  have key := relation_at k .slideB (n := n) (i := i) (by simp [Rel.width]; omega)
  rw [show relation k .slideB = LinDiagram.of _ - LinDiagram.of _ - LinDiagram.of _ from rfl,
    LinDiagram.whisker_sub, LinDiagram.whisker_sub, LinDiagram.whisker_of, LinDiagram.whisker_of,
    LinDiagram.whisker_of, LinDiagram.cast_sub, LinDiagram.cast_sub, LinDiagram.cast_of,
    LinDiagram.cast_of, LinDiagram.cast_of, Presentation.lin_sub, Presentation.lin_sub,
    Presentation.lin_of, Presentation.lin_of, Presentation.lin_of, sub_eq_zero] at key
  rw [x_def k (show i < n by omega), x_def k h, ψ_def k h]
  simp only [End.mul_def, ← Presentation.diag_comp, End.one_def]
  refine Eq.trans ?_ (key.trans ?_)
  · congr 1 <;> apply Presentation.diag_eq_of_layers_eq <;>
      simp [dlay, lay, shift, Layer.whisker, Gen.arity, Rel.width]
    all_goals omega
  · refine Eq.trans ?_ ((pres k).diag_id _)
    apply Presentation.diag_eq_of_layers_eq
    simp

/-! ## Far commutativity (from the interchange law) -/

theorem x_mul_x_comm (n i j : ℕ) : x k n i * x k n j = x k n j * x k n i := by
  wlog hij : i < j generalizing i j
  · rcases Nat.lt_or_ge j i with h | h
    · exact (this j i h).symm
    · rw [show i = j by omega]
  by_cases hj : j < n
  · rw [x_def k (show i < n by omega), x_def k hj, End.mul_def, End.mul_def]
    exact (interchange_at k .dot .dot (n := n) hij hj).symm
  · rw [x_of_le k (show n ≤ j by omega)]; simp

theorem x_mul_ψ_comm {n i j : ℕ} (h : j ≠ i) (h' : j ≠ i + 1) :
    x k n j * ψ k n i = ψ k n i * x k n j := by
  rcases Nat.lt_or_ge j i with hji | hji
  · by_cases hi : i + 1 < n
    · rw [x_def k (show j < n by omega), ψ_def k hi, End.mul_def, End.mul_def]
      exact (interchange_at k .dot .cross (n := n) hji hi).symm
    · rw [ψ_of_le k (show n ≤ i + 1 by omega)]; simp
  · by_cases hj : j < n
    · rw [x_def k hj, ψ_def k (show i + 1 < n by omega), End.mul_def, End.mul_def]
      exact interchange_at k .cross .dot (n := n) (show i + 2 ≤ j by omega) hj
    · rw [x_of_le k (show n ≤ j by omega)]; simp

theorem ψ_mul_ψ_comm {n i j : ℕ} (h : i + 1 < j) : ψ k n i * ψ k n j = ψ k n j * ψ k n i := by
  by_cases hj : j + 1 < n
  · rw [ψ_def k (show i + 1 < n by omega), ψ_def k hj, End.mul_def, End.mul_def]
    exact (interchange_at k .cross .cross (n := n) (show i + 2 ≤ j by omega) hj).symm
  · rw [ψ_of_le k (show n ≤ j + 1 by omega)]; simp

end Categorification.NilHecke.Diagram

end

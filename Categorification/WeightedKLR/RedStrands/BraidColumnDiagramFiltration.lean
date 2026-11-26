/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidColumnFiltration
import Categorification.WeightedKLR.RedStrands.BraidColumnBottomHigherTrace
import Categorification.WeightedKLR.RedStrands.BraidColumnBottomBruhat

/-!
# The diagram filtration of a braid column

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §6.1, proof
of Lemma 6.11, step `p_n → f_n`. For a red-ordered top loading `s` and a red permutation `σ`,
order the eligible bottom-block diagrams `y_w = ψ_{ρ(w)} e(w⁻¹ s)` of the column
`e(s) V e_{σ}` by a linear extension of the dominance–Bruhat refinement
(`exists_braidColumnIndexLinearRefinement`). The images of the multiplication maps by the
`y_w` give a filtration of the column (`span_braidColumnBottomProducts`), and multiplication by
`y_w` descends to a surjection from the loading standard at the bottom `w⁻¹ s` onto the `w`-th
piece, since the standard relations land in the span of the diagrams at strictly higher bottoms
(`braidColumnBottomBlock_mul_violStandardUpper_mem_higher_span`).

## Main results

* `braidColumnIndexList`: the eligible indices in a linear order refining the
  dominance–Bruhat order.
* `hasFiltration_braidColumn`: the filtration of the column by the diagram images, with a
  surjection from the loading standard at each bottom onto the corresponding piece.
-/

namespace Categorification.Stendhal.BraidColumn

open KLR KLRAlgebra TypeA Equiv BraidedStendhalAlgebra ModuleFiltration MvPolynomial

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type} [DecidableEq I] [Field k] {ℓ : ℕ} {ν : Multiset I}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}
local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card μ
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "V" => ViolQuotient k Q Λ ν
local notation "F" => AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν)
local notation "E" => fun κ => violMk k Q Λ ν (redProj k Q Λ ν κ)
local notation "C" => ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν)

omit [Field k] in
/-- The eligible bottom-block indices of the column at the top `s` and red permutation `σ`
(Webster, arXiv:1309.3796v2, proof of Lemma 6.11): the block permutations by `σ` of the
projective wirings of Proposition 5.20. -/
def IsBraidColumnIndex (s : Seq μ) (σ : Perm (Fin ℓ)) (w : Perm (Fin m)) : Prop :=
  ∃ (n : Fin ℓ → ℕ) (hn : (∑ r, (n r + 1)) = m) (φ : Perm (Fin m)),
    ProjectiveBlockIndex s φ ∧
    (∀ r : Fin ℓ, (φ⁻¹ • s).lbl (braidBlockPositions n hn ⟨r, 0⟩) = .inr r) ∧
    w = braidColumnBottomBlockIndex n hn σ φ

/-- A linear order on permutations refining the dominance–Bruhat order of the column. -/
noncomputable def braidColumnOrder (s : Seq μ) : Perm (Fin m) → Perm (Fin m) → Prop :=
  (exists_braidColumnIndexLinearRefinement s).choose

instance braidColumnOrder_isLinearOrder (s : Seq μ) :
    IsLinearOrder (Perm (Fin m)) (braidColumnOrder s) :=
  (exists_braidColumnIndexLinearRefinement s).choose_spec.1

theorem braidColumnOrder_of_earlier (s : Seq μ) {u w : Perm (Fin m)}
    (h : braidColumnIndexEarlier s u w) :
    braidColumnOrder s u w ∧ ¬ braidColumnOrder s w u :=
  (exists_braidColumnIndexLinearRefinement s).choose_spec.2 u w h

open Classical in
/-- **The eligible indices in order** (Webster, arXiv:1309.3796v2, proof of Lemma 6.11). -/
noncomputable def braidColumnIndexList (s : Seq μ) (σ : Perm (Fin ℓ)) : List (Perm (Fin m)) :=
  (Finset.univ.filter (IsBraidColumnIndex s σ)).sort (braidColumnOrder s)

theorem mem_braidColumnIndexList {s : Seq μ} {σ : Perm (Fin ℓ)} {w : Perm (Fin m)} :
    w ∈ braidColumnIndexList s σ ↔ IsBraidColumnIndex s σ w := by
  classical
  simp [braidColumnIndexList]

theorem nodup_braidColumnIndexList (s : Seq μ) (σ : Perm (Fin ℓ)) :
    (braidColumnIndexList s σ).Nodup := by
  classical
  exact Finset.sort_nodup _ _

/-- An index earlier in the dominance–Bruhat order comes earlier in the list. -/
theorem idxOf_lt_of_earlier {s : Seq μ} {σ : Perm (Fin ℓ)} {u w : Perm (Fin m)}
    (hu : u ∈ braidColumnIndexList s σ) (hw : w ∈ braidColumnIndexList s σ)
    (h : braidColumnIndexEarlier s u w) :
    (braidColumnIndexList s σ).idxOf u < (braidColumnIndexList s σ).idxOf w := by
  classical
  set L := braidColumnIndexList s σ
  have hs : L.Pairwise (braidColumnOrder s) := Finset.pairwise_sort _ _
  have hlu := List.idxOf_lt_length_iff.2 hu
  have hlw := List.idxOf_lt_length_iff.2 hw
  obtain ⟨-, hn⟩ := braidColumnOrder_of_earlier s h
  by_contra hc
  rcases (not_lt.1 hc).lt_or_eq with hlt | heq
  · apply hn
    have := List.pairwise_iff_get.1 hs ⟨_, hlw⟩ ⟨_, hlu⟩ hlt
    simpa [List.get_eq_getElem, List.getElem_idxOf] using this
  · have : u = w := by
      rw [← List.getElem_idxOf hlu, ← List.getElem_idxOf hlw]
      simp only [heq]
    subst this
    exact braidColumnIndexEarlier_irrefl s u h

/-- The `i`-th eligible index. -/
noncomputable def braidColumnIndexAt (s : Seq μ) (σ : Perm (Fin ℓ)) (i : ℕ) : Perm (Fin m) :=
  (braidColumnIndexList s σ).getD i 1

theorem F_e_mul_diagram (s : Seq μ) (ρ : Perm (Fin m) → List ℕ) (hρ : IsReducedChoice ρ)
    (w : Perm (Fin m)) :
    F (e s) * F (ψw (ρ w) * e (w⁻¹ • s)) = F (ψw (ρ w) * e (w⁻¹ • s)) := by
  rw [← map_mul, ← mul_assoc, e_mul_ψw, (hρ w).2, mul_assoc, e_mul_e, ite_eq_left rfl]

/-- **Multiplication by the diagram `y_w`** from the corner at its bottom to the column. -/
noncomputable def diagramColumnMul (s : Seq μ) (κ : List (Fin ℓ)) (ρ : Perm (Fin m) → List ℕ)
    (hρ : IsReducedChoice ρ) (w : Perm (Fin m)) :
    violCorner k Q Λ ν (w⁻¹ • s) κ →ₗ[(C κ)ᵐᵒᵖ] violCorner k Q Λ ν s κ where
  toFun x := ⟨F (ψw (ρ w) * e (w⁻¹ • s)) * x.1, mem_violCorner_iff.2
    ⟨by
      change F (e s) * _ = _
      rw [← mul_assoc]
      exact congrArg (· * x.1) (F_e_mul_diagram s ρ hρ w),
     by rw [mul_assoc, (mem_violCorner_iff.1 x.2).2]⟩⟩
  map_add' x x' := Subtype.ext (mul_add _ x.1 x'.1)
  map_smul' c x := Subtype.ext (by
    change _ * (x.1 * c.unop.val) = (_ * x.1) * c.unop.val
    rw [mul_assoc])

/-- The diagram maps indexed by position in the ordered list. -/
noncomputable def diagramColumnMaps (s : Seq μ) (σ : Perm (Fin ℓ)) (ρ : Perm (Fin m) → List ℕ)
    (hρ : IsReducedChoice ρ) (i : ℕ) :
    ModuleCat.of (C ((List.finRange ℓ).map σ))ᵐᵒᵖ
        (violCorner k Q Λ ν ((braidColumnIndexAt s σ i)⁻¹ • s) ((List.finRange ℓ).map σ)) →ₗ[
      (C ((List.finRange ℓ).map σ))ᵐᵒᵖ]
      ModuleCat.of (C ((List.finRange ℓ).map σ))ᵐᵒᵖ
        (violCorner k Q Λ ν s ((List.finRange ℓ).map σ)) :=
  diagramColumnMul s _ ρ hρ (braidColumnIndexAt s σ i)

/-- The elements of the column lying in a submodule of it, as a `k`-submodule of `V`. -/
noncomputable def ambientSubmodule {s : Seq μ} {κ : List (Fin ℓ)}
    (N : Submodule (C κ)ᵐᵒᵖ (violCorner k Q Λ ν s κ)) : Submodule k V where
  carrier := {v | ∃ h : v ∈ violCorner k Q Λ ν s κ, (⟨v, h⟩ : violCorner k Q Λ ν s κ) ∈ N}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨add_mem ha hb, N.add_mem ha' hb'⟩
  zero_mem' := ⟨zero_mem _, N.zero_mem⟩
  smul_mem' := by
    rintro c a ⟨ha, ha'⟩
    refine ⟨Submodule.smul_mem _ c ha, ?_⟩
    have hsm : (⟨c • a, Submodule.smul_mem _ c ha⟩ : violCorner k Q Λ ν s κ) =
        algebraMap k (C κ)ᵐᵒᵖ c • (⟨a, ha⟩ : violCorner k Q Λ ν s κ) := by
      apply Subtype.ext
      rw [violCorner_smul_val, MulOpposite.algebraMap_apply, MulOpposite.unop_op]
      change c • a = a * (algebraMap k _ c * violMk k Q Λ ν (redProj k Q Λ ν κ))
      rw [← mul_assoc, ← Algebra.commutes c a, mul_assoc, (mem_violCorner_iff.1 ha).2,
        ← Algebra.smul_def]
    rw [hsm]
    exact N.smul_mem _ ha'

/-- The diagram product at the `i`-th index lies in the `(i + 1)`-st step. -/
theorem mem_diagramStep_succ {s : Seq μ} {σ : Perm (Fin ℓ)}
    {ρ : Perm (Fin m) → List ℕ} {hρ : IsReducedChoice ρ} (i : ℕ) (w : Perm (Fin m))
    (h : braidColumnIndexAt s σ i = w) (z : V) (hz : z * E ((List.finRange ℓ).map σ) = z) :
    F (ψw (ρ w) * e (w⁻¹ • s)) * z ∈
      ambientSubmodule (diagramStep (diagramColumnMaps (k := k) (Q := Q) (Λ := Λ) s σ ρ hρ)
        (i + 1)) := by
  subst h
  set w := braidColumnIndexAt s σ i
  have hb : F (e (w⁻¹ • s)) * z ∈ violCorner k Q Λ ν (w⁻¹ • s) ((List.finRange ℓ).map σ) :=
    mem_violCorner_iff.2 ⟨by
      change F (e _) * (F (e _) * z) = _
      rw [← mul_assoc, ← map_mul, e_mul_e, ite_eq_left rfl], by rw [mul_assoc, hz]⟩
  have hprod : F (ψw (ρ w) * e (w⁻¹ • s)) * z =
      F (ψw (ρ w) * e (w⁻¹ • s)) * (F (e (w⁻¹ • s)) * z) := by
    rw [← mul_assoc, ← map_mul, mul_assoc, e_mul_e, ite_eq_left rfl]
  rw [hprod]
  exact ⟨(diagramColumnMaps (k := k) (Q := Q) (Λ := Λ) s σ ρ hρ i ⟨_, hb⟩).2,
    Submodule.mem_sup_right ⟨⟨_, hb⟩, rfl⟩⟩

theorem diagramStep_mono {s : Seq μ} {σ : Perm (Fin ℓ)} {ρ : Perm (Fin m) → List ℕ}
    {hρ : IsReducedChoice ρ} {a b : ℕ} (hab : a ≤ b) :
    diagramStep (diagramColumnMaps (k := k) (Q := Q) (Λ := Λ) s σ ρ hρ) a ≤
      diagramStep (diagramColumnMaps (k := k) (Q := Q) (Λ := Λ) s σ ρ hρ) b := by
  induction hab with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans le_sup_left

theorem ambientSubmodule_mono {s : Seq μ} {κ : List (Fin ℓ)}
    {N N' : Submodule (C κ)ᵐᵒᵖ (violCorner k Q Λ ν s κ)} (h : N ≤ N') :
    ambientSubmodule N ≤ ambientSubmodule N' :=
  fun _ ⟨hv, hv'⟩ => ⟨hv, h hv'⟩

/-- An eligible diagram product lies in every step after its position. -/
theorem mem_diagramStep_of_mem_list {s : Seq μ} {σ : Perm (Fin ℓ)}
    {ρ : Perm (Fin m) → List ℕ} {hρ : IsReducedChoice ρ} {w : Perm (Fin m)}
    (hw : w ∈ braidColumnIndexList s σ) {j : ℕ}
    (hj : (braidColumnIndexList s σ).idxOf w < j) (z : V)
    (hz : z * E ((List.finRange ℓ).map σ) = z) :
    F (ψw (ρ w) * e (w⁻¹ • s)) * z ∈
      ambientSubmodule (diagramStep (diagramColumnMaps (k := k) (Q := Q) (Λ := Λ) s σ ρ hρ) j) := by
  have hat : braidColumnIndexAt s σ ((braidColumnIndexList s σ).idxOf w) = w := by
    rw [braidColumnIndexAt, List.getD_eq_getElem _ _ (List.idxOf_lt_length_iff.2 hw),
      List.getElem_idxOf]
  exact ambientSubmodule_mono (diagramStep_mono hj) (mem_diagramStep_succ _ w hat z hz)

theorem braidColumnIndexAt_mem {s : Seq μ} {σ : Perm (Fin ℓ)} {i : ℕ}
    (hi : i < (braidColumnIndexList s σ).length) :
    braidColumnIndexAt s σ i ∈ braidColumnIndexList s σ := by
  rw [braidColumnIndexAt, List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

theorem idxOf_braidColumnIndexAt {s : Seq μ} {σ : Perm (Fin ℓ)} {i : ℕ}
    (hi : i < (braidColumnIndexList s σ).length) :
    (braidColumnIndexList s σ).idxOf (braidColumnIndexAt s σ i) = i := by
  rw [braidColumnIndexAt, List.getD_eq_getElem _ _ hi]
  exact (nodup_braidColumnIndexList s σ).idxOf_getElem i hi

/-- **The diagrams generate the column** (Webster, arXiv:1309.3796v2, proof of Lemma 6.11). -/
theorem diagramStep_length_eq_top (s : Seq μ) (hs : IsRedOrdered s) (σ : Perm (Fin ℓ))
    (ρ : Perm (Fin m) → List ℕ) (hρ : IsReducedChoice ρ) :
    diagramStep (diagramColumnMaps (k := k) (Q := Q) (Λ := Λ) s σ ρ hρ)
      (braidColumnIndexList s σ).length = ⊤ := by
  have hle : Submodule.span k (braidColumnBottomProducts (Q := Q) (Λ := Λ) s σ ρ) ≤
      ambientSubmodule (diagramStep (diagramColumnMaps (k := k) (Q := Q) (Λ := Λ) s σ ρ hρ)
        (braidColumnIndexList s σ).length) := by
    rw [Submodule.span_le]
    rintro _ ⟨n, hn, φ, hφ, hr, -, z, hz, rfl⟩
    have hw : braidColumnBottomBlockIndex n hn σ φ ∈ braidColumnIndexList s σ :=
      mem_braidColumnIndexList.2 ⟨n, hn, φ, hφ, hr, rfl⟩
    exact mem_diagramStep_of_mem_list hw (List.idxOf_lt_length_iff.2 hw) z hz
  refine eq_top_iff.2 fun v _ => ?_
  have hv : (v : V) ∈ Submodule.span k (braidColumnBottomProducts (Q := Q) (Λ := Λ) s σ ρ) := by
    rw [span_braidColumnBottomProducts s hs σ ρ hρ]
    exact v.2
  obtain ⟨_, hv'⟩ := hle hv
  exact hv'

/-- **The standard relations land in the earlier steps** (Webster, arXiv:1309.3796v2, proof of
Lemma 6.11): multiplying an element of the higher trace at the bottom of the `i`-th diagram by
that diagram gives an element of the `i`-th step. -/
theorem diagramColumnMaps_mem_diagramStep (s : Seq μ) (hs : IsRedOrdered s)
    (σ : Perm (Fin ℓ)) (ρ : Perm (Fin m) → List ℕ) (hρ : IsReducedChoice ρ) {i : ℕ}
    (hi : i < (braidColumnIndexList s σ).length)
    (x : violCorner k Q Λ ν ((braidColumnIndexAt s σ i)⁻¹ • s) ((List.finRange ℓ).map σ))
    (hx : x ∈ violStandardUpper (Q := Q) (Λ := Λ) ((braidColumnIndexAt s σ i)⁻¹ • s)
      ((List.finRange ℓ).map σ)) :
    diagramColumnMaps (k := k) (Q := Q) (Λ := Λ) s σ ρ hρ i x ∈
      diagramStep (diagramColumnMaps (k := k) (Q := Q) (Λ := Λ) s σ ρ hρ) i := by
  have hmem := braidColumnBottomBlock_mul_violStandardUpper_mem_higher_span s
    ((braidColumnIndexAt s σ i)⁻¹ • s) hs σ ρ hρ
    (F (ψw (ρ (braidColumnIndexAt s σ i)) * e ((braidColumnIndexAt s σ i)⁻¹ • s)))
    (F_e_mul_diagram s ρ hρ _) x hx
  have hle : Submodule.span k (braidColumnBottomProductsWhere (Q := Q) (Λ := Λ) s σ ρ
      (StendhalLT ((braidColumnIndexAt s σ i)⁻¹ • s))) ≤ ambientSubmodule (diagramStep
        (diagramColumnMaps (k := k) (Q := Q) (Λ := Λ) s σ ρ hρ) i) := by
    rw [Submodule.span_le]
    rintro _ ⟨n, hn, φ, hφ, hr, hlt, z, hz, rfl⟩
    have hw' : braidColumnBottomBlockIndex n hn σ φ ∈ braidColumnIndexList s σ :=
      mem_braidColumnIndexList.2 ⟨n, hn, φ, hφ, hr, rfl⟩
    have hlt' := idxOf_lt_of_earlier hw' (braidColumnIndexAt_mem hi) (Or.inl hlt)
    rw [idxOf_braidColumnIndexAt hi] at hlt'
    exact mem_diagramStep_of_mem_list hw' hlt' z hz
  obtain ⟨_, h⟩ := hle hmem
  exact h

/-- **The diagram filtration of a braid column** (Webster, arXiv:1309.3796v2, §6.1, proof of
Lemma 6.11, step `p_n → f_n`): the images of the ordered eligible diagrams filter the column
`e(s) V e_σ`, and multiplication by the `i`-th diagram is a surjection from the loading standard
at its bottom onto the `i`-th piece. -/
theorem hasFiltration_braidColumn (s : Seq μ) (hs : IsRedOrdered s) (σ : Perm (Fin ℓ))
    (ρ : Perm (Fin m) → List ℕ) (hρ : IsReducedChoice ρ) :
    HasFiltration (fun i => ModuleCat.of (C ((List.finRange ℓ).map σ))ᵐᵒᵖ
        (diagramPiece (diagramColumnMaps (k := k) (Q := Q) (Λ := Λ) s σ ρ hρ) i))
      (List.range (braidColumnIndexList s σ).length).reverse
      (ModuleCat.of (C ((List.finRange ℓ).map σ))ᵐᵒᵖ
        (violCorner k Q Λ ν s ((List.finRange ℓ).map σ))) ∧
    ∀ i, i < (braidColumnIndexList s σ).length →
      ∃ d : ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) ((braidColumnIndexAt s σ i)⁻¹ • s)
          ((List.finRange ℓ).map σ) →ₗ[(C ((List.finRange ℓ).map σ))ᵐᵒᵖ]
          diagramPiece (diagramColumnMaps (k := k) (Q := Q) (Λ := Λ) s σ ρ hρ) i,
        Function.Surjective d :=
  ⟨hasFiltration_diagramColumn _ _ (diagramStep_length_eq_top s hs σ ρ hρ), fun i hi =>
    ⟨standardToDiagramPiece (diagramColumnMaps (k := k) (Q := Q) (Λ := Λ) s σ ρ hρ) i
        (violStandardUpper (Q := Q) (Λ := Λ) ((braidColumnIndexAt s σ i)⁻¹ • s)
          ((List.finRange ℓ).map σ)) (diagramColumnMaps_mem_diagramStep s hs σ ρ hρ hi),
      standardToDiagramPiece_surjective _ _ _ _⟩⟩

end Categorification.Stendhal.BraidColumn

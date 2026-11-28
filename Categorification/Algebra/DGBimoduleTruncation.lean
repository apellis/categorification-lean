/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DegreeZeroHeart

set_option backward.isDefEq.respectTransparency false

/-!
# Good truncation of dg bimodules over rings in degree zero

Let `A`, `B` be rings concentrated in degree `0` and `X` a dg `(A, B)`-bimodule. The good
truncation `τ^{≤ 0} X = (⋯ → X⁻¹ → Z⁰(X) → 0)` of dg-lean (`DG.truncLE`, a left dg
`A`-submodule) is also stable under the right action of `B`, so it is a dg sub-bimodule
(`Categorification.bimoduleTruncLE`); its inclusion is a quasi-isomorphism when
`Hᵏ(X) = 0` for `k > 0`. Its quotient by `τ^{< 0} ⊕ d(X⁻¹)` is the `(A, B)`-bimodule
`H⁰(X)` (`Categorification.bimoduleCohomologyZero`), and the projection
`τ^{≤ 0} X → H⁰(X)` (placed in degree `0`) is a quasi-isomorphism of dg bimodules when
`Hᵏ(X) = 0` for `k < 0` (`Categorification.isQuasiIso_bimoduleCohomologyZeroπ`).

So a dg bimodule `X` whose cohomology is concentrated in degree `0` is connected to the ordinary
bimodule `H⁰(X)` by the zig-zag of bimodule quasi-isomorphisms `X ← τ^{≤ 0} X → H⁰(X)`.

This is used for the bimodule form of B. Webster, *Knot invariants and higher representation
theory*, arXiv:1309.3796v3, proof of Proposition 7.22. The results are generic dg algebra
(dg-lean's `DG/Derived/TStructure.lean` and `DG/Derived/Heart.lean` treat left modules).
-/

open CategoryTheory DG MulOpposite
open scoped DG.DegreeZero

noncomputable section

namespace Categorification

universe u

variable {A B : Type u} [Ring A] [Ring B]
  (X : Type u) [AddCommGroup X] [DGAddCommGroup X] [Module A X] [Module Bᵐᵒᵖ X]
  [DGBimodule A B X]

/-- A ring in degree `0` is concentrated in non-positive degrees (any universe). -/
theorem isNonposGraded_ring_degreeZero (R : Type u) [Ring R] : IsNonposGraded R :=
  isNonposGraded_iff.mpr fun n hn r hr => by
    rcases (InDegreeZero.ring_mem_grading_iff (R := R)).1 hr with h | h
    · exact absurd h hn.ne'
    · exact h

/-! ### The truncation `τ^{≤ 0} X` -/

/-- The good truncation `τ^{≤ 0} X` of a dg `(A, B)`-bimodule, as a left dg `A`-submodule. -/
abbrev bimoduleTruncLE (A B : Type u) [Ring A] [Ring B] (X : Type u) [AddCommGroup X]
    [DGAddCommGroup X] [Module A X] [Module Bᵐᵒᵖ X] [DGBimodule A B X] : DGSubmodule A X :=
  truncLE (isNonposGraded_ring_degreeZero A) X 0

variable {X}

omit [Module A X] [DGBimodule A B X] in
theorem op_smul_mem_ofComponents_truncLE (b : B) {x : X} [DGRightModule B X]
    (hx : x ∈ ofComponents (truncLEComponents X 0)) :
    op b • x ∈ ofComponents (truncLEComponents X 0) := by
  refine induction_on_of_isHomogeneous (isHomogeneous_ofComponents _)
    (P := fun x => op b • x ∈ ofComponents (truncLEComponents X 0)) (by simp [zero_mem]) ?_
    (fun x x' h h' => by simpa only [smul_add] using add_mem h h') hx
  intro k x hxk hxS
  have hb : b ∈ grading (M := B) 0 := DegreeZero.mem_grading_iff.mpr (Or.inl rfl)
  have hbx : op b • x ∈ grading k := by simpa using op_smul_mem_grading hb hxk
  rw [mem_truncLEComponents_iff hxk] at hxS
  rw [mem_truncLEComponents_iff hbx]
  refine ⟨fun h => by rw [hxS.1 h, smul_zero], fun h => ?_⟩
  rw [d_op_smul_of_d_eq_zero hxk (DegreeZero.d_apply b), hxS.2 h, smul_zero]

theorem op_smul_mem_bimoduleTruncLE (b : B) {x : X} (hx : x ∈ bimoduleTruncLE A B X) :
    op b • x ∈ bimoduleTruncLE A B X :=
  op_smul_mem_ofComponents_truncLE b hx

instance bimoduleTruncLE_smul : SMul Bᵐᵒᵖ (bimoduleTruncLE A B X) where
  smul b x := ⟨b • (x : X), op_smul_mem_bimoduleTruncLE b.unop x.2⟩

@[simp]
theorem bimoduleTruncLE_coe_op_smul (b : Bᵐᵒᵖ) (x : bimoduleTruncLE A B X) :
    ((b • x : bimoduleTruncLE A B X) : X) = b • (x : X) := rfl

instance bimoduleTruncLE_module : Module Bᵐᵒᵖ (bimoduleTruncLE A B X) :=
  Subtype.coe_injective.module Bᵐᵒᵖ (AddSubgroupClass.subtype _) fun _ _ => rfl

instance bimoduleTruncLE_dgRightModule : DGRightModule B (bimoduleTruncLE A B X) where
  op_smul_mem' {i j b x} hb hx := by
    change (op b • (x : X)) ∈ grading (j + i)
    exact op_smul_mem_grading hb hx
  d_op_smul' {j x} hx b := Subtype.ext (by
    change d (op b • (x : X)) = op b • d (x : X) + koszulSign j • (op (d b) • (x : X))
    exact d_op_smul (M := X) (show (x : X) ∈ grading j from hx) b)

instance bimoduleTruncLE_smulCommClass : SMulCommClass A Bᵐᵒᵖ (bimoduleTruncLE A B X) where
  smul_comm a b x := Subtype.ext (smul_comm a b (x : X))

instance bimoduleTruncLE_dgBimodule : DGBimodule A B (bimoduleTruncLE A B X) :=
  DGBimodule.mk'

/-- The inclusion `τ^{≤ 0} X → X` is right `B`-linear. -/
theorem bimoduleTruncLE_subtype_op_smul (b : B) (x : bimoduleTruncLE A B X) :
    (bimoduleTruncLE A B X).subtype (op b • x) =
      op b • (bimoduleTruncLE A B X).subtype x := rfl

/-- **The inclusion `τ^{≤ 0} X → X` is a quasi-isomorphism** when `Hᵏ(X) = 0` for `k > 0`. -/
theorem isQuasiIso_bimoduleTruncLE_subtype
    (hX : ∀ k, 0 < k → Subsingleton (cohomology X k)) :
    (bimoduleTruncLE A B X).subtype.IsQuasiIso :=
  DerivedCategory.isQuasiIso_truncLE_subtype (isNonposGraded_ring_degreeZero A) hX

/-- `Hᵏ(τ^{≤ 0} X) = 0` for `k ≠ 0` when `Hᵏ(X) = 0` for `k ≠ 0`. -/
theorem subsingleton_cohomology_bimoduleTruncLE
    (hX : ∀ k, k ≠ 0 → Subsingleton (cohomology X k)) (k : ℤ) (hk : k ≠ 0) :
    Subsingleton (cohomology (bimoduleTruncLE A B X) k) := by
  rcases lt_or_gt_of_ne hk with hk | hk
  · have := hX k hk.ne
    exact (bijective_cohomology_map_truncLE (isNonposGraded_ring_degreeZero A) (M := X)
      hk.le).1.subsingleton
  · exact subsingleton_cohomology_truncLE (isNonposGraded_ring_degreeZero A) hk

/-! ### The cohomology bimodule `H⁰(X)` -/

section CohomologyZero

open DirectSum

variable (A B X)

/-- `τ^{≤ 0} X` is concentrated in non-positive degrees. -/
theorem isNonposGraded_bimoduleTruncLE : IsNonposGraded (bimoduleTruncLE A B X) :=
  isNonposGraded_truncLE_zero (isNonposGraded_ring_degreeZero A)

/-- The submodule `τ^{< 0} ⊕ d(X⁻¹)` of `τ^{≤ 0} X`, the kernel of `τ^{≤ 0} X → H⁰(X)`. -/
abbrev bimoduleCohomologyZeroKer : Submodule A (bimoduleTruncLE A B X) :=
  degreeZeroQuotientSubmodule (isNonposGraded_ring_degreeZero A) (bimoduleTruncLE A B X)
    (isNonposGraded_bimoduleTruncLE A B X)

omit [Module A X] [Module Bᵐᵒᵖ X] [DGBimodule A B X] in
variable {A B} in
theorem op_smul_mem_degreeZeroQuotientComponents {P : Type u} [AddCommGroup P]
    [DGAddCommGroup P] [Module Bᵐᵒᵖ P] [DGRightModule B P] (b : B) {x : P}
    (hx : x ∈ ofComponents (degreeZeroQuotientComponents P)) :
    op b • x ∈ ofComponents (degreeZeroQuotientComponents P) := by
  refine induction_on_of_isHomogeneous (isHomogeneous_ofComponents _)
    (P := fun x => op b • x ∈ ofComponents (degreeZeroQuotientComponents P))
    (by simp [zero_mem]) ?_ (fun x x' h h' => by simpa only [smul_add] using add_mem h h') hx
  intro k x hxk hxS
  have hb : b ∈ DG.grading (M := B) 0 := DegreeZero.mem_grading_iff.mpr (Or.inl rfl)
  have hbx : op b • x ∈ DG.grading k := by simpa using op_smul_mem_grading hb hxk
  rw [mem_degreeZeroQuotientComponents_iff hxk] at hxS
  rw [mem_degreeZeroQuotientComponents_iff hbx]
  rintro rfl
  obtain ⟨y, hy, rfl⟩ := hxS rfl
  exact ⟨op b • y, by simpa using op_smul_mem_grading hb hy,
    d_op_smul_of_d_eq_zero hy (DegreeZero.d_apply b)⟩

variable {A B X} in
theorem op_smul_mem_bimoduleCohomologyZeroKer (b : B) {x : bimoduleTruncLE A B X}
    (hx : x ∈ bimoduleCohomologyZeroKer A B X) : op b • x ∈ bimoduleCohomologyZeroKer A B X :=
  op_smul_mem_degreeZeroQuotientComponents b hx

/-- The kernel of `τ^{≤ 0} X → H⁰(X)` as a submodule for the right action of `B`. -/
def bimoduleCohomologyZeroKerRight : Submodule Bᵐᵒᵖ (bimoduleTruncLE A B X) where
  toAddSubmonoid := (bimoduleCohomologyZeroKer A B X).toAddSubmonoid
  smul_mem' b _ hx := op_smul_mem_bimoduleCohomologyZeroKer b.unop hx

/-- **The cohomology bimodule** `H⁰(X) = Z⁰(X) / d(X⁻¹)` of a dg `(A, B)`-bimodule, as the
quotient of `τ^{≤ 0} X` by `τ^{< 0} ⊕ d(X⁻¹)`. -/
def bimoduleCohomologyZero : Type u :=
  bimoduleTruncLE A B X ⧸ bimoduleCohomologyZeroKer A B X

instance : AddCommGroup (bimoduleCohomologyZero A B X) :=
  inferInstanceAs (AddCommGroup (bimoduleTruncLE A B X ⧸ bimoduleCohomologyZeroKer A B X))

instance : Module A (bimoduleCohomologyZero A B X) :=
  inferInstanceAs (Module A (bimoduleTruncLE A B X ⧸ bimoduleCohomologyZeroKer A B X))

instance : Module Bᵐᵒᵖ (bimoduleCohomologyZero A B X) :=
  inferInstanceAs (Module Bᵐᵒᵖ (bimoduleTruncLE A B X ⧸ bimoduleCohomologyZeroKerRight A B X))

/-- The projection `τ^{≤ 0} X → H⁰(X)`. -/
def bimoduleCohomologyZeroMk : bimoduleTruncLE A B X →ₗ[A] bimoduleCohomologyZero A B X :=
  Submodule.mkQ _

variable {A B X}

theorem bimoduleCohomologyZeroMk_op_smul (b : B) (x : bimoduleTruncLE A B X) :
    bimoduleCohomologyZeroMk A B X (op b • x) = op b • bimoduleCohomologyZeroMk A B X x := rfl

theorem bimoduleCohomologyZeroMk_surjective :
    Function.Surjective (bimoduleCohomologyZeroMk A B X) :=
  Submodule.mkQ_surjective _

theorem bimoduleCohomologyZeroMk_eq_zero_iff {x : bimoduleTruncLE A B X} :
    bimoduleCohomologyZeroMk A B X x = 0 ↔ x ∈ bimoduleCohomologyZeroKer A B X :=
  Submodule.Quotient.mk_eq_zero _

instance : SMulCommClass A Bᵐᵒᵖ (bimoduleCohomologyZero A B X) where
  smul_comm a b y := by
    obtain ⟨x, rfl⟩ := bimoduleCohomologyZeroMk_surjective y
    exact congrArg (bimoduleCohomologyZeroMk A B X) (smul_comm a b x)

variable (A B X)

/-- **The projection `τ^{≤ 0} X → H⁰(X)`**, with `H⁰(X)` placed in degree `0`, as a morphism
of dg `A`-modules; it is right `B`-linear (`bimoduleCohomologyZeroπ_op_smul`). -/
def bimoduleCohomologyZeroπ :
    bimoduleTruncLE A B X →ᵈᵍ[A] InDegreeZero (bimoduleCohomologyZero A B X) where
  toFun x := bimoduleCohomologyZeroMk A B X x
  map_add' := map_add _
  map_smul' := map_smul _
  map_mem' {n x} hx := by
    by_cases hn : n = 0
    · subst hn
      exact (InDegreeZero.mem_grading_iff _).mpr (Or.inl rfl)
    · rw [bimoduleCohomologyZeroMk_eq_zero_iff.mpr
        (mem_degreeZeroQuotientSubmodule_of_ne _ _ hn hx)]
      exact zero_mem _
  map_d' x := (bimoduleCohomologyZeroMk_eq_zero_iff.mpr (degreeZeroQuotient_d_mem x)).trans
    (InDegreeZero.d_apply _ _).symm

variable {A B X}

theorem bimoduleCohomologyZeroπ_op_smul (b : B) (x : bimoduleTruncLE A B X) :
    bimoduleCohomologyZeroπ A B X (op b • x) = op b • bimoduleCohomologyZeroπ A B X x := rfl

omit [Module Bᵐᵒᵖ X] [DGBimodule A B X] in
theorem subsingleton_cohomology_inDegreeZero (N : Type u) [AddCommGroup N] {n : ℤ} (hn : n ≠ 0) :
    Subsingleton (cohomology (InDegreeZero N) n) :=
  subsingleton_cohomology_iff.mpr fun m hm _ => by
    rw [((InDegreeZero.mem_grading_iff _).mp hm).resolve_left hn]
    exact zero_mem _

/-- **The projection `τ^{≤ 0} X → H⁰(X)` is a quasi-isomorphism** when the cohomology of `X` is
concentrated in degree `0`. -/
theorem isQuasiIso_bimoduleCohomologyZeroπ (hX : ∀ k, k ≠ 0 → Subsingleton (cohomology X k)) :
    (bimoduleCohomologyZeroπ A B X).IsQuasiIso := by
  have hP := isNonposGraded_bimoduleTruncLE A B X
  intro k
  by_cases hk : k = 0
  · subst hk
    constructor
    · rw [cohomology.map_injective_iff]
      intro x hx _ hπx
      obtain ⟨y, -, hy⟩ := mem_coboundaries.mp hπx
      rw [InDegreeZero.d_apply] at hy
      exact (mem_degreeZeroQuotientSubmodule_iff _ hP hx).mp
        (bimoduleCohomologyZeroMk_eq_zero_iff.mp hy.symm)
    · rw [cohomology.map_surjective_iff]
      intro y _ _
      obtain ⟨x, hxy⟩ := bimoduleCohomologyZeroMk_surjective (X := X) y
      set x₀ := (decompose (DG.grading (M := bimoduleTruncLE A B X)) x 0 : bimoduleTruncLE A B X)
      have hx₀ : x₀ ∈ DG.grading 0 := SetLike.coe_mem _
      refine ⟨x₀, hx₀, hP.eq_zero one_pos (by simpa using d_mem hx₀), ?_⟩
      have : bimoduleCohomologyZeroπ A B X x₀ = bimoduleCohomologyZeroπ A B X x := by
        rw [← (bimoduleCohomologyZeroπ A B X).coe_decompose_apply,
          decompose_of_mem_same _ ((InDegreeZero.mem_grading_iff _).mpr (Or.inl rfl))]
      rw [this, show bimoduleCohomologyZeroπ A B X x = y from hxy, sub_self]
      exact zero_mem _
  · have := subsingleton_cohomology_bimoduleTruncLE (A := A) (B := B) hX k hk
    have := subsingleton_cohomology_inDegreeZero (bimoduleCohomologyZero A B X) hk
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

end CohomologyZero

end Categorification

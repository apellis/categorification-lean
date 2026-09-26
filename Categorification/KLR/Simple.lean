/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CenterFree
import Categorification.KLR.Grading
import Categorification.Algebra.Graded.Simple
import Categorification.Algebra.AugmentationQuotient

/-!
# Simple graded modules over KLR algebras: KL I, Proposition 2.12

Khovanov–Lauda I (arXiv:0803.4121v2), §2.5, TeX lines 1489–1512:

> **Proposition 2.12.** A simple `R(ν)`-module `S` is finite-dimensional and `Sym⁺(ν)` acts by `0`
> on it. `Hom(S, S{a}) = 0` if `a ≠ 0`, and `S` remains simple when viewed as an `R(ν)`-module
> without the grading.
>
> Hence, `S` is a (graded) module over the finite-dimensional quotient algebra
> `R'(ν) = R(ν) / Sym⁺(ν) R(ν)`. Note that `dim_k R'(ν) = (m!)²`, and, up to isomorphism and
> grading shifts, there are only finitely many simple `R(ν)`-modules.

Here `k` is a field, "simple" means simple in the category of graded `R(ν)`-modules with
degree-preserving maps (`Graded.IsGradedSimple`), and `Sym⁺(ν)` is the kernel of the augmentation
`Sym(ν) → k` (`symNuPlus`), i.e. the invariants without constant term (`mem_symNuPlus_iff`).

We work in the generality of the basis theorem (`k` a field, `Q i j (u, v) = P j i (u, v) ·
P i j (v, u)` with all `P i j ≠ 0`) and of an arbitrary grading datum `G` with dots of positive
degree (`0 < G.degX a`); the statements for the rings of KL I (graded by
`klGradingDatum`, dots of degree `2`) are in the namespace `KL1`.

## Main results

* `KLRAlgebra.smul_eq_zero_of_mem_symNuPlus` : `Sym⁺(ν)` acts by zero on a simple module;
* `KLRAlgebra.finiteDimensional_of_isGradedSimple` : simple modules are finite-dimensional;
* `KLRAlgebra.eq_zero_of_preservesGrading_shift` : `Hom(S, S{a}) = 0` for `a ≠ 0`;
* `KLRAlgebra.isSimpleModule_of_isGradedSimple` : `S` is simple as an ungraded module;
* `KLRAlgebra.symPlusIdeal`, `KLRAlgebra.finrank_quotient_symPlusIdeal` :
  `R'(ν) = R(ν) / Sym⁺(ν) R(ν)` has dimension `(m!)²`; `symPlusIdeal_isTwoSided`;
* `KLRAlgebra.card_le_of_isGradedSimple` : any family of simple modules which are pairwise
  non-isomorphic up to grading shift has at most `(m!)²` members (so there are finitely many
  simple modules up to isomorphism and shift);
* `KLRAlgebra.exists_gradedEquiv_shift_of_linearEquiv` : simple modules that are isomorphic as
  ungraded modules are isomorphic up to a grading shift; `eq_zero_of_gradedEquiv_shift`: the
  shift is unique.
-/

namespace Categorification.KLR

open Equiv MvPolynomial TypeA DirectSum Graded PolyRep

variable {I : Type*} [DecidableEq I] {k : Type*}

namespace KLRAlgebra

/-! ### The augmentation ideal `Sym⁺(ν)` -/

section SymPlus

variable [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}

local notation "m" => Multiset.card ν

variable (k ν) in
/-- The augmentation `Sym(ν) → k`, `f ↦` the constant term of `f_i` (for a fixed `i ∈ Seq ν`;
by invariance it does not depend on `i`, see `mem_symNuPlus_iff`). -/
noncomputable def symNuAug : symNu k ν →ₐ[k] k :=
  (MvPolynomial.aeval fun _ => (0 : k)).comp
    ((Pi.evalAlgHom k (fun _ : Seq ν => MvPolynomial (Fin m) k)
      (Classical.arbitrary (Seq ν))).comp (symNu k ν).val)

omit [DecidableEq I] in
theorem symNuAug_apply (f : symNu k ν) :
    symNuAug k ν f = constantCoeff ((f : Pol k ν) (Classical.arbitrary (Seq ν))) := by
  simp [symNuAug, MvPolynomial.coe_aeval_eq_eval, MvPolynomial.eval_zero]

variable (k ν) in
/-- **`Sym⁺(ν)`** (KL I §2.5): the kernel of the augmentation `Sym(ν) → k`, spanned by the
invariants without constant term. -/
noncomputable def symNuPlus : Ideal (symNu k ν) := RingHom.ker (symNuAug k ν)

theorem constantCoeff_apply_eq (f : symNu k ν) (i j : Seq ν) :
    constantCoeff ((f : Pol k ν) i) = constantCoeff ((f : Pol k ν) j) := by
  obtain ⟨w, rfl⟩ := Seq.exists_smul_eq i j
  rw [f.2 w i, constantCoeff_rename]

/-- `f ∈ Sym⁺(ν)` iff every component `f_i` has zero constant term. -/
theorem mem_symNuPlus_iff {f : symNu k ν} :
    f ∈ symNuPlus k ν ↔ ∀ i, constantCoeff ((f : Pol k ν) i) = 0 := by
  rw [symNuPlus, RingHom.mem_ker, symNuAug_apply]
  exact ⟨fun h i => by rw [constantCoeff_apply_eq f i]; exact h, fun h => h _⟩

variable (k Q ν) in
/-- The two-sided ideal `Sym⁺(ν) R(ν)` of `R(ν)` (generated as a left ideal by the central
elements `polNu f`, `f ∈ Sym⁺(ν)`). -/
noncomputable def symPlusIdeal : Ideal (KLRAlgebra k Q ν) :=
  Submodule.span (KLRAlgebra k Q ν) ((fun f : symNu k ν => polNu (f : Pol k ν)) '' symNuPlus k ν)

theorem polNu_mem_symPlusIdeal {f : symNu k ν} (hf : f ∈ symNuPlus k ν) :
    (polNu (f : Pol k ν) : KLRAlgebra k Q ν) ∈ symPlusIdeal k Q ν :=
  Submodule.subset_span ⟨f, hf, rfl⟩

end SymPlus

/-! ### Degrees -/

section Degrees

variable [Field k] {Q : I → I → MvPolynomial (Fin 2) k} (G : GradingDatum Q) {ν : Multiset I}

local notation "m" => Multiset.card ν

omit [DecidableEq I] in
theorem weight_lbl_nonneg (hG : ∀ a, 0 ≤ G.degX a) (i : Seq ν) (u : Fin m →₀ ℕ) :
    0 ≤ Finsupp.weight (fun a => G.degX (i.lbl a)) u := by
  rw [Finsupp.weight_apply, Finsupp.sum]
  exact Finset.sum_nonneg fun a _ => smul_nonneg (Nat.zero_le _) (hG _)

omit [DecidableEq I] in
theorem weight_lbl_pos (hG : ∀ a, 0 < G.degX a) (i : Seq ν) {u : Fin m →₀ ℕ} (hu : u ≠ 0) :
    0 < Finsupp.weight (fun a => G.degX (i.lbl a)) u := by
  rw [Finsupp.weight_apply, Finsupp.sum]
  refine Finset.sum_pos (fun a ha => ?_) (Finsupp.support_nonempty_iff.2 hu)
  exact smul_pos (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 ha)) (hG _)

/-- `R(ν)` is bounded below: if dots have nonnegative degree, `R(ν)` vanishes in all degrees
below the minimal degree of the elements `ψ_{ρ w} e_i`. -/
theorem exists_grade_eq_bot (hG : ∀ a, 0 ≤ G.degX a) :
    ∃ N : ℤ, ∀ n < N, G.grade ν n = ⊥ := by
  classical
  let ρ : Perm (Fin m) → List ℕ := fun w => canWord m w
  have hρ : ∀ w, IsReduced m (ρ w) ∧ wordProd m (ρ w) = w :=
    fun w => ⟨isReduced_canWord m w, wordProd_canWord m w⟩
  let deg : Seq ν × Perm (Fin m) × (Fin m →₀ ℕ) → ℤ := fun b =>
    G.degW (ρ b.2.1) b.1 + Finsupp.weight (fun a => G.degX (b.1.lbl a)) b.2.2
  have hdeg : ∀ b, stdElt (k := k) (Q := Q) ρ b ∈ G.grade ν (deg b) := fun b =>
    G.ψw_mul_pol_monomial_mul_e_mem_grade _ _ _
  obtain ⟨N, hN⟩ : ∃ N : ℤ, ∀ (i : Seq ν) (w : Perm (Fin m)), N ≤ G.degW (ρ w) i :=
    ⟨Finset.univ.inf' Finset.univ_nonempty (fun q : Seq ν × Perm (Fin m) => G.degW (ρ q.2) q.1),
      fun i w => Finset.inf'_le _ (Finset.mem_univ (i, w))⟩
  refine ⟨N, fun n hn => ?_⟩
  rw [eq_bot_iff]
  intro r hr
  rw [Submodule.mem_bot]
  have hr' : r ∈ Submodule.span k (Set.range (stdElt (k := k) (Q := Q) ρ)) := by
    rw [span_stdElt ρ hρ]; trivial
  rw [← decompose_of_mem_same (G.grade ν) hr]
  clear hr
  induction hr' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    refine decompose_of_mem_ne _ (hdeg b) ?_
    have := hN b.1 b.2.1
    have := weight_lbl_nonneg G hG b.1 b.2.2
    simp only [deg]
    omega
  | zero => simp
  | add x y _ _ hx hy => rw [decompose_add, add_apply, Submodule.coe_add, hx, hy, add_zero]
  | smul c x _ hx => rw [decompose_smul, DirectSum.smul_apply, Submodule.coe_smul, hx, smul_zero]

/-- If dots have positive degree, the homogeneous components of `polNu f` in degrees `≤ 0`
vanish when every `f_i` has zero constant term. -/
theorem decompose_polNu_eq_zero (hG : ∀ a, 0 < G.degX a) {f : Pol k ν}
    (hf : ∀ i, constantCoeff (f i) = 0) {d : ℤ} (hd : d ≤ 0) :
    (decompose (G.grade ν) (polNu f : KLRAlgebra k Q ν) d : KLRAlgebra k Q ν) = 0 := by
  classical
  rw [polNu_apply, decompose_sum, DFinsupp.finset_sum_apply, Submodule.coe_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  have h := mul_pol_mul_e_eq_sum (Q := Q) 1 (f i) i (f i).support subset_rfl
  rw [one_mul] at h
  rw [h, decompose_sum, DFinsupp.finset_sum_apply, Submodule.coe_sum]
  refine Finset.sum_eq_zero fun u hu => ?_
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [MvPolynomial.mem_support_iff, ← constantCoeff_eq, hf i] at hu
    exact hu rfl
  rw [decompose_smul, DirectSum.smul_apply, Submodule.coe_smul, one_mul]
  rw [decompose_of_mem_ne _ (G.pol_monomial_mul_e_mem_grade u i)
    (by have := weight_lbl_pos G hG i hu0; omega), smul_zero]

end Degrees

/-! ### Proposition 2.12 -/

section Prop212

variable [Field k] {Q : I → I → MvPolynomial (Fin 2) k} {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)
  (G : GradingDatum Q) (hG : ∀ a, 0 < G.degX a) {ν : Multiset I}
  {M : Type*} [AddCommGroup M] [Module (KLRAlgebra k Q ν) M] [Module k M]
  [IsScalarTower k (KLRAlgebra k Q ν) M]
  (ℳ : ℤ → Submodule k M) [Decomposition ℳ] [SetLike.GradedSMul (G.grade ν) ℳ]

omit [IsScalarTower k (KLRAlgebra k Q ν) M] in
include hPQ hP hG in
/-- **KL I, Proposition 2.12**: `Sym⁺(ν)` acts by `0` on a simple graded `R(ν)`-module. -/
theorem smul_eq_zero_of_mem_symNuPlus (hS : IsGradedSimple (G.grade ν) ℳ) {f : symNu k ν}
    (hf : f ∈ symNuPlus k ν) (x : M) : (polNu (f : Pol k ν) : KLRAlgebra k Q ν) • x = 0 := by
  obtain ⟨N, hN⟩ := exists_grade_eq_bot (ν := ν) G fun a => (hG a).le
  have hc : ∀ a : KLRAlgebra k Q ν, Commute (polNu (f : Pol k ν)) a := fun a =>
    ((Subalgebra.mem_center_iff.1 (polNu_mem_center hPQ hP f.2)) a).symm
  exact hS.smul_eq_zero_of_commute hN hc
    (fun d hd => decompose_polNu_eq_zero G hG ((mem_symNuPlus_iff).1 hf) hd) x

omit [IsScalarTower k (KLRAlgebra k Q ν) M] in
include hPQ hP hG in
/-- **KL I, Proposition 2.12**: the ideal `Sym⁺(ν) R(ν)` annihilates every simple graded
`R(ν)`-module. -/
theorem smul_eq_zero_of_mem_symPlusIdeal (hS : IsGradedSimple (G.grade ν) ℳ) {r : KLRAlgebra k Q ν}
    (hr : r ∈ symPlusIdeal k Q ν) (x : M) : r • x = 0 := by
  induction hr using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨f, hf, rfl⟩ := hy
    exact smul_eq_zero_of_mem_symNuPlus hPQ hP G hG ℳ hS hf x
  | zero => exact zero_smul _ _
  | add y z _ _ hy hz => rw [add_smul, hy, hz, add_zero]
  | smul a y _ hy => rw [smul_eq_mul, mul_smul, hy, smul_zero]

/-! #### `R'(ν) = R(ν) / Sym⁺(ν) R(ν)` -/

/-- The augmentation of the center `Z(R(ν)) ≅ Sym(ν)` (KL I, Theorem 2.9). -/
noncomputable def centerAug : Subalgebra.center k (KLRAlgebra k Q ν) →ₐ[k] k :=
  (symNuAug k ν).comp (symNuEquivCenter hPQ hP).symm.toAlgHom

theorem centerAug_symNuEquivCenter (f : symNu k ν) :
    centerAug hPQ hP (symNuEquivCenter hPQ hP f) = symNuAug k ν f := by
  simp [centerAug]

omit hPQ hP in
theorem commute_center (z : Subalgebra.center k (KLRAlgebra k Q ν)) (r : KLRAlgebra k Q ν) :
    (z : KLRAlgebra k Q ν) * r = r * z :=
  (Subalgebra.mem_center_iff.1 z.2 r).symm

/-- `Sym⁺(ν) R(ν) = (ker ε) R(ν)` for the augmentation `ε` of the center. -/
theorem symPlusIdeal_restrictScalars :
    (symPlusIdeal k Q ν).restrictScalars k =
      augSubmodule (KLRAlgebra k Q ν) (centerAug hPQ hP (ν := ν)) := by
  ext x
  rw [Submodule.restrictScalars_mem]
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨f, hf, rfl⟩ := hy
      show (polNu (f : Pol k ν) : KLRAlgebra k Q ν) ∈ _
      have : (polNu (f : Pol k ν) : KLRAlgebra k Q ν) =
          (symNuEquivCenter hPQ hP f) • (1 : KLRAlgebra k Q ν) := by
        rw [Subalgebra.smul_def, smul_eq_mul, mul_one, symNuEquivCenter_apply]
      rw [this]
      refine smul_mem_augSubmodule ?_ _
      rw [centerAug_symNuEquivCenter]
      exact hf
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul a y _ hy =>
      rw [smul_eq_mul]
      refine augSubmodule_induction (p := fun y => a * y ∈ _) hy ?_ ?_
      · intro z hz r
        have e1 : a * (z • r) = z • (a * r) := by
          show a * ((z : KLRAlgebra k Q ν) * r) = (z : KLRAlgebra k Q ν) * (a * r)
          rw [← mul_assoc, ← commute_center z a, mul_assoc]
        rw [e1]
        exact smul_mem_augSubmodule hz _
      · intro y y' hy hy'
        rw [mul_add]
        exact add_mem hy hy'
  · intro hx
    refine augSubmodule_induction hx ?_ ?_
    · intro z hz r
      set f := (symNuEquivCenter hPQ hP).symm z
      have hzf : (z : KLRAlgebra k Q ν) = polNu (f : Pol k ν) := by
        rw [← symNuEquivCenter_apply hPQ hP f, AlgEquiv.apply_symm_apply]
      have hf : f ∈ symNuPlus k ν := by
        rw [symNuPlus, RingHom.mem_ker, ← centerAug_symNuEquivCenter hPQ hP f,
          AlgEquiv.apply_symm_apply]
        exact hz
      show (z : KLRAlgebra k Q ν) * r ∈ symPlusIdeal k Q ν
      rw [commute_center z r, hzf]
      exact Submodule.smul_mem _ r (polNu_mem_symPlusIdeal hf)
    · intro y y' hy hy'
      exact add_mem hy hy'

include hPQ hP in
/-- `Sym⁺(ν) R(ν)` is a two-sided ideal, so `R'(ν) = R(ν) / Sym⁺(ν) R(ν)` is a ring. -/
theorem symPlusIdeal_isTwoSided : (symPlusIdeal k Q ν).IsTwoSided := by
  refine ⟨fun b ha => ?_⟩
  induction ha using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨f, hf, rfl⟩ := hy
    rw [← (Subalgebra.mem_center_iff.1 (polNu_mem_center hPQ hP f.2) b), ← smul_eq_mul]
    exact Submodule.smul_mem _ b (polNu_mem_symPlusIdeal hf)
  | zero => rw [zero_mul]; exact zero_mem _
  | add y z _ _ hy hz => rw [add_mul]; exact add_mem hy hz
  | smul a y _ hy => rw [smul_eq_mul, mul_assoc, ← smul_eq_mul]; exact Submodule.smul_mem _ a hy

include hPQ hP in
/-- **KL I, §2.5**: `dim_k R'(ν) = (m!)²`, where `R'(ν) = R(ν) / Sym⁺(ν) R(ν)`. -/
theorem finrank_quotient_symPlusIdeal :
    Module.finrank k (KLRAlgebra k Q ν ⧸ symPlusIdeal k Q ν) = (Multiset.card ν).factorial ^ 2 := by
  classical
  obtain ⟨ι, _, hcard, ⟨b⟩⟩ := exists_centerBasis (ν := ν) hPQ hP
  rw [← (Submodule.Quotient.restrictScalarsEquiv k (symPlusIdeal k Q ν)).finrank_eq,
    symPlusIdeal_restrictScalars hPQ hP, finrank_augQuot b, hcard]

include hPQ hP in
theorem finiteDimensional_quotient_symPlusIdeal_restrictScalars :
    FiniteDimensional k (KLRAlgebra k Q ν ⧸ (symPlusIdeal k Q ν).restrictScalars k) := by
  classical
  obtain ⟨ι, _, -, ⟨b⟩⟩ := exists_centerBasis (ν := ν) hPQ hP
  rw [symPlusIdeal_restrictScalars hPQ hP]
  exact finiteDimensional_augQuot b _

include hPQ hP in
/-- `R'(ν)` is finite-dimensional. -/
theorem finiteDimensional_quotient_symPlusIdeal :
    FiniteDimensional k (KLRAlgebra k Q ν ⧸ symPlusIdeal k Q ν) := by
  haveI := finiteDimensional_quotient_symPlusIdeal_restrictScalars (ν := ν) hPQ hP
  exact Module.Finite.equiv (Submodule.Quotient.restrictScalarsEquiv k (symPlusIdeal k Q ν))

/-! #### The statements of Proposition 2.12 -/

include hPQ hP hG in
/-- **KL I, Proposition 2.12**: a simple graded `R(ν)`-module is finite-dimensional. -/
theorem finiteDimensional_of_isGradedSimple (hS : IsGradedSimple (G.grade ν) ℳ) :
    FiniteDimensional k M := by
  haveI := finiteDimensional_quotient_symPlusIdeal_restrictScalars (ν := ν) hPQ hP
  exact hS.finiteDimensional ((symPlusIdeal k Q ν).restrictScalars k)
    fun a ha x => smul_eq_zero_of_mem_symPlusIdeal hPQ hP G hG ℳ hS ha x

include hPQ hP hG in
/-- **KL I, Proposition 2.12**: `Hom(S, S{a}) = 0` for `a ≠ 0`: a simple graded `R(ν)`-module
has no nonzero `R(ν)`-linear map `S → S{a}` of degree zero. -/
theorem eq_zero_of_preservesGrading_shift (hS : IsGradedSimple (G.grade ν) ℳ) {a : ℤ} (ha : a ≠ 0)
    {φ : M →ₗ[KLRAlgebra k Q ν] M} (hφ : PreservesGrading ℳ (Graded.shift ℳ a) φ) : φ = 0 := by
  haveI := finiteDimensional_of_isGradedSimple hPQ hP G hG ℳ hS
  exact hS.eq_zero_of_preservesGrading_shift ha hφ

include hPQ hP hG in
/-- **KL I, Proposition 2.12**: a simple graded `R(ν)`-module remains simple as an ungraded
module. -/
theorem isSimpleModule_of_isGradedSimple (hS : IsGradedSimple (G.grade ν) ℳ) :
    IsSimpleModule (KLRAlgebra k Q ν) M := by
  haveI := finiteDimensional_of_isGradedSimple hPQ hP G hG ℳ hS
  exact hS.isSimpleModule

include hPQ hP hG in
/-- **KL I, Proposition 2.12** (summary): a simple graded `R(ν)`-module `S` is finite-dimensional,
`Sym⁺(ν)` acts by zero on it, `Hom(S, S{a}) = 0` for `a ≠ 0`, and `S` is simple as an ungraded
module. -/
theorem prop_2_12 (hS : IsGradedSimple (G.grade ν) ℳ) :
    FiniteDimensional k M ∧
      (∀ f ∈ symNuPlus k ν, ∀ x : M, (polNu (f : Pol k ν) : KLRAlgebra k Q ν) • x = 0) ∧
      (∀ a : ℤ, a ≠ 0 → ∀ φ : M →ₗ[KLRAlgebra k Q ν] M,
        PreservesGrading ℳ (Graded.shift ℳ a) φ → φ = 0) ∧
      IsSimpleModule (KLRAlgebra k Q ν) M :=
  ⟨finiteDimensional_of_isGradedSimple hPQ hP G hG ℳ hS,
    fun _ hf x => smul_eq_zero_of_mem_symNuPlus hPQ hP G hG ℳ hS hf x,
    fun _ ha _ hφ => eq_zero_of_preservesGrading_shift hPQ hP G hG ℳ hS ha hφ,
    isSimpleModule_of_isGradedSimple hPQ hP G hG ℳ hS⟩

/-- A simple graded `R(ν)`-module is a quotient of `R'(ν)`: for any nonzero `v ∈ S`, the map
`R'(ν) → S`, `[r] ↦ r v` is well defined and surjective. -/
noncomputable def quotientToSimple (hS : IsGradedSimple (G.grade ν) ℳ) (v : M) :
    (KLRAlgebra k Q ν ⧸ symPlusIdeal k Q ν) →ₗ[KLRAlgebra k Q ν] M :=
  (symPlusIdeal k Q ν).liftQ (LinearMap.toSpanSingleton _ M v)
    fun _ hr => smul_eq_zero_of_mem_symPlusIdeal hPQ hP G hG ℳ hS hr v

omit [IsScalarTower k (KLRAlgebra k Q ν) M] in
theorem quotientToSimple_mk (hS : IsGradedSimple (G.grade ν) ℳ) (v : M) (r : KLRAlgebra k Q ν) :
    quotientToSimple hPQ hP G hG ℳ hS v (Submodule.Quotient.mk r) = r • v := rfl

omit [IsScalarTower k (KLRAlgebra k Q ν) M] in
theorem quotientToSimple_surjective (hS : IsGradedSimple (G.grade ν) ℳ) {v : M} {j : ℤ}
    (hv : v ∈ ℳ j) (hv0 : v ≠ 0) : Function.Surjective (quotientToSimple hPQ hP G hG ℳ hS v) := by
  intro x
  have : x ∈ Submodule.span (KLRAlgebra k Q ν) {v} := by
    rw [hS.span_singleton_eq_top hv hv0]; trivial
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 this
  exact ⟨Submodule.Quotient.mk r, rfl⟩

end Prop212

/-! ### Finitely many simple modules up to isomorphism and shift -/

section Finite

variable [Field k] {Q : I → I → MvPolynomial (Fin 2) k} {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)
  (G : GradingDatum Q) (hG : ∀ a, 0 < G.degX a) {ν : Multiset I}

omit hPQ hP hG in
/-- Simple graded `R(ν)`-modules which are isomorphic as ungraded modules are isomorphic up to a
grading shift. -/
theorem exists_gradedEquiv_shift_of_linearEquiv
    {M N : Type*} [AddCommGroup M] [Module (KLRAlgebra k Q ν) M] [Module k M]
    [IsScalarTower k (KLRAlgebra k Q ν) M] (ℳ : ℤ → Submodule k M) [Decomposition ℳ]
    [SetLike.GradedSMul (G.grade ν) ℳ]
    [AddCommGroup N] [Module (KLRAlgebra k Q ν) N] [Module k N]
    [IsScalarTower k (KLRAlgebra k Q ν) N] (𝒩 : ℤ → Submodule k N) [Decomposition 𝒩]
    [SetLike.GradedSMul (G.grade ν) 𝒩]
    (hM : IsGradedSimple (G.grade ν) ℳ) (hN : IsGradedSimple (G.grade ν) 𝒩)
    (e : M ≃ₗ[KLRAlgebra k Q ν] N) :
    ∃ c : ℤ, Nonempty (ℳ ≃ᵍ[KLRAlgebra k Q ν] Graded.shift 𝒩 c) := by
  refine hM.exists_gradedEquiv_shift_of_ne_zero hN (f := e.toLinearMap) fun h => ?_
  haveI := hM.nontrivial
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  exact hx (e.injective (by rw [map_zero]; exact LinearMap.congr_fun h x))

include hPQ hP hG in
/-- **KL I, §2.5**: up to isomorphism and grading shift there are only finitely many simple graded
`R(ν)`-modules: any family of simple graded `R(ν)`-modules which are pairwise non-isomorphic up to
grading shift has at most `(m!)² = dim_k R'(ν)` members. -/
theorem card_le_of_isGradedSimple {ι : Type*} (S : ι → Type*) [∀ b, AddCommGroup (S b)]
    [∀ b, Module (KLRAlgebra k Q ν) (S b)] [∀ b, Module k (S b)]
    [∀ b, IsScalarTower k (KLRAlgebra k Q ν) (S b)] (𝒮 : ∀ b, ℤ → Submodule k (S b))
    [∀ b, Decomposition (𝒮 b)] [∀ b, SetLike.GradedSMul (G.grade ν) (𝒮 b)]
    (hS : ∀ b, IsGradedSimple (G.grade ν) (𝒮 b))
    (hne : ∀ b b' (c : ℤ), Nonempty (𝒮 b ≃ᵍ[KLRAlgebra k Q ν] Graded.shift (𝒮 b') c) → b = b') :
    Finite ι ∧ Nat.card ι ≤ (Multiset.card ν).factorial ^ 2 := by
  classical
  haveI := finiteDimensional_quotient_symPlusIdeal (ν := ν) hPQ hP
  have hv : ∀ b, ∃ j, ∃ v ∈ 𝒮 b j, v ≠ 0 := fun b => by
    haveI := (hS b).nontrivial
    exact exists_mem_ne_zero (𝒮 b)
  choose j v hv hv0 using hv
  haveI : ∀ b, IsSimpleModule (KLRAlgebra k Q ν) (S b) := fun b =>
    isSimpleModule_of_isGradedSimple hPQ hP G hG (𝒮 b) (hS b)
  have := card_le_finrank_of_isSimpleModule (k := k) S
    (fun b => quotientToSimple hPQ hP G hG (𝒮 b) (hS b) (v b))
    (fun b => quotientToSimple_surjective hPQ hP G hG (𝒮 b) (hS b) (hv b) (hv0 b))
    (fun b b' ⟨e⟩ => by
      obtain ⟨c, ⟨e'⟩⟩ := exists_gradedEquiv_shift_of_linearEquiv G (𝒮 b) (𝒮 b')
        (hS b) (hS b') e
      exact hne b b' c ⟨e'⟩)
  rwa [finrank_quotient_symPlusIdeal hPQ hP] at this

include hPQ hP hG in
/-- The grading shift in `S ≅ S{a}` is `a = 0` for a simple graded `R(ν)`-module. -/
theorem eq_zero_of_gradedEquiv_shift
    {M : Type*} [AddCommGroup M] [Module (KLRAlgebra k Q ν) M] [Module k M]
    [IsScalarTower k (KLRAlgebra k Q ν) M] (ℳ : ℤ → Submodule k M) [Decomposition ℳ]
    [SetLike.GradedSMul (G.grade ν) ℳ] (hS : IsGradedSimple (G.grade ν) ℳ) {a : ℤ}
    (e : ℳ ≃ᵍ[KLRAlgebra k Q ν] Graded.shift ℳ a) : a = 0 := by
  haveI := finiteDimensional_of_isGradedSimple hPQ hP G hG ℳ hS
  exact hS.eq_zero_of_gradedEquiv_shift e

end Finite

end KLRAlgebra

/-! ### The rings of KL I -/

namespace KL1

open KLRAlgebra

variable [Field k] {Γ : SimpleGraph I} [DecidableRel Γ.Adj] {ν : Multiset I}

theorem klGradingDatum_degX_pos (a : I) : 0 < (klGradingDatum k Γ).degX a := by
  show (0 : ℤ) < 2
  norm_num

/-- **KL I, Proposition 2.12** for the rings `R(ν)` of KL I over a field `k`, graded with dots of
degree `2`: a simple graded `R(ν)`-module `S` is finite-dimensional, `Sym⁺(ν)` acts by zero on it,
`Hom(S, S{a}) = 0` for `a ≠ 0`, and `S` is simple as an ungraded module. -/
theorem prop_2_12 {M : Type*} [AddCommGroup M] [Module (R1 k Γ ν) M] [Module k M]
    [IsScalarTower k (R1 k Γ ν) M] (ℳ : ℤ → Submodule k M) [Decomposition ℳ]
    [SetLike.GradedSMul ((klGradingDatum k Γ).grade ν) ℳ]
    (hS : IsGradedSimple ((klGradingDatum k Γ).grade ν) ℳ) :
    FiniteDimensional k M ∧
      (∀ f ∈ symNuPlus k ν, ∀ x : M, (polNu (f : Pol k ν) : R1 k Γ ν) • x = 0) ∧
      (∀ a : ℤ, a ≠ 0 → ∀ φ : M →ₗ[R1 k Γ ν] M,
        PreservesGrading ℳ (Graded.shift ℳ a) φ → φ = 0) ∧
      IsSimpleModule (R1 k Γ ν) M :=
  KLRAlgebra.prop_2_12 (klQ_eq_klP (Γ := Γ) stdOrient_spec) (fun a b _ => klP_ne_zero _ a b)
    (klGradingDatum k Γ) klGradingDatum_degX_pos ℳ hS

/-- **KL I, §2.5**: `dim_k R'(ν) = (m!)²` for the rings of KL I over a field. -/
theorem finrank_quotient_symPlusIdeal :
    Module.finrank k (R1 k Γ ν ⧸ symPlusIdeal k (klQ Γ) ν) =
      (Multiset.card ν).factorial ^ 2 :=
  KLRAlgebra.finrank_quotient_symPlusIdeal (klQ_eq_klP (Γ := Γ) stdOrient_spec)
    (fun a b _ => klP_ne_zero _ a b)

/-- **KL I, §2.5**: up to isomorphism and grading shift there are at most `(m!)²` simple graded
modules over the rings `R(ν)` of KL I (over a field). -/
theorem card_le_of_isGradedSimple {ι : Type*} (S : ι → Type*) [∀ b, AddCommGroup (S b)]
    [∀ b, Module (R1 k Γ ν) (S b)] [∀ b, Module k (S b)]
    [∀ b, IsScalarTower k (R1 k Γ ν) (S b)] (𝒮 : ∀ b, ℤ → Submodule k (S b))
    [∀ b, Decomposition (𝒮 b)] [∀ b, SetLike.GradedSMul ((klGradingDatum k Γ).grade ν) (𝒮 b)]
    (hS : ∀ b, IsGradedSimple ((klGradingDatum k Γ).grade ν) (𝒮 b))
    (hne : ∀ b b' (c : ℤ), Nonempty (𝒮 b ≃ᵍ[R1 k Γ ν] Graded.shift (𝒮 b') c) → b = b') :
    Finite ι ∧ Nat.card ι ≤ (Multiset.card ν).factorial ^ 2 :=
  KLRAlgebra.card_le_of_isGradedSimple (klQ_eq_klP (Γ := Γ) stdOrient_spec)
    (fun a b _ => klP_ne_zero _ a b) (klGradingDatum k Γ) klGradingDatum_degX_pos S 𝒮 hS hne

end KL1

end Categorification.KLR

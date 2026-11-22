/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.Sl2Categorification.PositiveBasis
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Subobject.ArtinianObject

/-!
# Weak `𝔰𝔩₂`-categorifications

Chuang–Rouquier, *Derived equivalences for symmetric groups and `𝔰𝔩₂`-categorification*,
arXiv:math/0407205v2, §5.1.1, define a weak `𝔰𝔩₂`-categorification of an artinian and
noetherian abelian category `A` as a pair of exact endofunctors `E`, `F`, adjoint on both sides,
whose classes act on `V = ℚ ⊗ K₀(A)` by a locally finite `𝔰𝔩₂`-representation in which the
classes of simple objects are weight vectors.

Here the Grothendieck group enters as data (`K0Data`): a map `cls` from objects to a
`ℚ`-vector space `V`, additive on short exact sequences, sending the simple objects to a basis
(indexed by the isomorphism classes of simple objects) and every object into the cone spanned
by that basis, with integer coordinates. The actual Grothendieck group with its basis of simple
classes is such data.

## Main results

* `WeakSl2.posBasis`: the basis of simple classes satisfies the hypotheses of
  Chuang–Rouquier, Lemma 4.3 (`PosBasis`).
* `K0Data.repr_cls_pos_of_mono_of_epi`: a simple subquotient is a composition factor.
* `WeakSl2.dOf_le_of_mono_E`, `WeakSl2.dOf_le_of_mono_F`: **Chuang–Rouquier, Lemma 5.11**
  (subobject form): if every simple subobject of `M` has `d ≥ r`, so does every simple subobject
  of `E M` and of `F M`.
-/

namespace Categorification.Sl2

open CategoryTheory Limits ZeroObject

universe v u

variable (C : Type u) [Category.{v} C] [Abelian C]

/-- Grothendieck-group data on an abelian category: an additive class map to a `ℚ`-vector space
sending the simple objects to a basis, indexed by their isomorphism classes, and every object
into the cone of that basis. -/
structure K0Data (ι V : Type*) [AddCommGroup V] [Module ℚ V] where
  /-- The basis of simple classes. -/
  B : Module.Basis ι ℚ V
  /-- The class of an object. -/
  cls : C → V
  cls_add : ∀ S : ShortComplex C, S.ShortExact → cls S.X₂ = cls S.X₁ + cls S.X₃
  /-- The index of a simple object. -/
  idx : ∀ S : C, Simple S → ι
  cls_simple : ∀ (S : C) (h : Simple S), cls S = B (idx S h)
  iso_of_idx_eq : ∀ (S T : C) (hS : Simple S) (hT : Simple T), idx S hS = idx T hT →
    Nonempty (S ≅ T)
  /-- A representative simple object of each index. -/
  simple : ι → C
  simple_simple : ∀ i, Simple (simple i)
  idx_simple : ∀ i, idx (simple i) (simple_simple i) = i
  cls_mem_cone : ∀ X, cls X ∈ cone B
  /-- Classes have integer coordinates (multiplicities of composition factors). -/
  cls_int : ∀ X j, ∃ m : ℕ, B.repr (cls X) j = m

variable {C}

namespace K0Data

variable {ι V : Type*} [AddCommGroup V] [Module ℚ V] (K : K0Data C ι V)

lemma cls_of_iso {X Y : C} (e : X ≅ Y) : K.cls X = K.cls Y := by
  have hS : (ShortComplex.mk (0 : (0 : C) ⟶ X) e.hom (by simp)).ShortExact := by
    refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
    exact ShortComplex.exact_of_f_is_kernel _
      (KernelFork.IsLimit.ofMonoOfIsZero _ inferInstance (isZero_zero C))
  have h0 : K.cls (0 : C) = 0 := by
    have hZ : (ShortComplex.mk (0 : (0 : C) ⟶ 0) (0 : (0 : C) ⟶ 0) (by simp)).ShortExact := by
      refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
      · exact ShortComplex.exact_of_isZero_X₂ _ (isZero_zero C)
      · exact (isZero_zero C).mono _
      · exact (isZero_zero C).epi _
    have := K.cls_add _ hZ
    simpa using this
  have := K.cls_add _ hS
  simpa [h0] using this

lemma cls_add_of_epi {X Y : C} (p : X ⟶ Y) [Epi p] :
    K.cls X = K.cls (kernel p) + K.cls Y := by
  have hS : (ShortComplex.mk (kernel.ι p) p (kernel.condition p)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel p))
      inferInstance inferInstance
  exact K.cls_add _ hS

lemma cls_add_of_mono {X Y : C} (s : X ⟶ Y) [Mono s] :
    K.cls Y = K.cls X + K.cls (cokernel s) := by
  have hS : (ShortComplex.mk s (cokernel.π s) (cokernel.condition s)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel s))
      inferInstance inferInstance
  exact K.cls_add _ hS

/-- A simple subobject of a quotient of `X` is a composition factor of `X`. -/
theorem repr_cls_pos_of_mono_of_epi {X Y S : C} [hS : Simple S] (p : X ⟶ Y) [Epi p]
    (s : S ⟶ Y) [Mono s] : 0 < K.B.repr (K.cls X) (K.idx S hS) := by
  rw [K.cls_add_of_epi p, K.cls_add_of_mono s, K.cls_simple S hS]
  have h1 := K.cls_mem_cone (kernel p) (K.idx S hS)
  have h2 := K.cls_mem_cone (cokernel s) (K.idx S hS)
  simp only [map_add, Finsupp.add_apply, Module.Basis.repr_self, Finsupp.single_eq_same]
  linarith

end K0Data

variable (C) in
/-- A weak `𝔰𝔩₂`-categorification (Chuang–Rouquier, §5.1.1), with the Grothendieck group given
as `K0Data`. Exactness of `E` and `F` follows from the two adjunctions. -/
structure WeakSl2 (ι V : Type*) [AddCommGroup V] [Module ℚ V] extends K0Data C ι V where
  /-- The functor `E`. -/
  E : C ⥤ C
  /-- The functor `F`. -/
  F : C ⥤ C
  /-- The adjunction `E ⊣ F`. -/
  adjEF : E ⊣ F
  /-- The adjunction `F ⊣ E`. -/
  adjFE : F ⊣ E
  /-- The class of `E`. -/
  e : Module.End ℚ V
  /-- The class of `F`. -/
  f : Module.End ℚ V
  cls_E : ∀ X, cls (E.obj X) = e (cls X)
  cls_F : ∀ X, cls (F.obj X) = f (cls X)
  sl2 : IsSl2Pair e f
  /-- The weights of the simple classes. -/
  wt : ι → ℤ
  wt_eq : ∀ i, hOp e f (B i) = (wt i : ℚ) • B i
  locFin : ∀ w : V, ∃ U : Submodule ℚ V, FiniteDimensional ℚ U ∧ w ∈ U ∧
    (∀ u ∈ U, e u ∈ U) ∧ (∀ u ∈ U, f u ∈ U)

namespace WeakSl2

variable {ι V : Type*} [AddCommGroup V] [Module ℚ V] (A : WeakSl2 C ι V)

lemma e_basis (i : ι) : A.e (A.B i) = A.cls (A.E.obj (A.simple i)) := by
  rw [A.cls_E, A.cls_simple _ (A.simple_simple i), A.idx_simple]

lemma f_basis (i : ι) : A.f (A.B i) = A.cls (A.F.obj (A.simple i)) := by
  rw [A.cls_F, A.cls_simple _ (A.simple_simple i), A.idx_simple]

/-- The simple classes form a positive basis (the hypotheses of Chuang–Rouquier, Lemma 4.3). -/
theorem posBasis : PosBasis A.B A.e A.f A.wt where
  sl2 := A.sl2
  wt_eq := A.wt_eq
  pos_e i := by rw [A.e_basis]; exact A.cls_mem_cone _
  pos_f i := by rw [A.f_basis]; exact A.cls_mem_cone _
  locFin := A.locFin

/-- The invariant `d` of a simple object. -/
noncomputable def dS (S : C) (hS : Simple S) : ℕ := dOf A.e A.f (A.B (A.idx S hS))

variable [∀ X : C, IsArtinianObject X]

/-- The image of a nonzero morphism `X ⟶ M` contains a simple subobject `S` of `M`, and `S` is
a composition factor of `X`. -/
theorem exists_simple_mono_of_ne_zero {X M : C} (g : X ⟶ M) (hg : g ≠ 0) :
    ∃ (S : C) (hS : Simple S) (s : S ⟶ M), Mono s ∧
      0 < A.B.repr (A.cls X) (A.idx S hS) := by
  have hI : ¬IsZero (image g) := by
    intro h
    exact hg (by rw [← image.fac g, h.eq_of_tgt (factorThruImage g) 0, zero_comp])
  refine ⟨simpleSubobject hI, inferInstance, simpleSubobjectArrow hI ≫ image.ι g,
    inferInstance, ?_⟩
  exact A.repr_cls_pos_of_mono_of_epi (factorThruImage g) (simpleSubobjectArrow hI)

/-- **Chuang–Rouquier, Lemma 5.11**, for `E` and simple subobjects: if every simple subobject
of `M` has `d ≥ r`, then so does every simple subobject of `E M`. -/
theorem dOf_le_of_mono_E {M T : C} {r : ℕ}
    (hM : ∀ (S : C) (hS : Simple S) (s : S ⟶ M), Mono s → r ≤ A.dS S hS)
    (hT : Simple T) (t : T ⟶ A.E.obj M) [Mono t] : r ≤ A.dS T hT := by
  have ht : t ≠ 0 := fun h ↦ id_nonzero T ((cancel_mono t).1 (by simp [h]))
  have hg : (A.adjFE.homEquiv T M).symm t ≠ 0 := by
    intro h
    have : A.E.IsRightAdjoint := A.adjFE.isRightAdjoint
    rw [Equiv.symm_apply_eq, Adjunction.homEquiv_unit, Functor.map_zero, comp_zero] at h
    exact ht h
  obtain ⟨S, hS, s, hs, hpos⟩ := A.exists_simple_mono_of_ne_zero _ hg
  rw [A.cls_F, A.cls_simple T hT] at hpos
  exact (hM S hS s hs).trans (A.posBasis.dOf_le_of_f hpos.ne')

/-- **Chuang–Rouquier, Lemma 5.11**, for `F` and simple subobjects. -/
theorem dOf_le_of_mono_F {M T : C} {r : ℕ}
    (hM : ∀ (S : C) (hS : Simple S) (s : S ⟶ M), Mono s → r ≤ A.dS S hS)
    (hT : Simple T) (t : T ⟶ A.F.obj M) [Mono t] : r ≤ A.dS T hT := by
  have ht : t ≠ 0 := fun h ↦ id_nonzero T ((cancel_mono t).1 (by simp [h]))
  have hg : (A.adjEF.homEquiv T M).symm t ≠ 0 := by
    intro h
    have : A.F.IsRightAdjoint := A.adjEF.isRightAdjoint
    rw [Equiv.symm_apply_eq, Adjunction.homEquiv_unit, Functor.map_zero, comp_zero] at h
    exact ht h
  obtain ⟨S, hS, s, hs, hpos⟩ := A.exists_simple_mono_of_ne_zero _ hg
  rw [A.cls_E, A.cls_simple T hT] at hpos
  exact (hM S hS s hs).trans (A.posBasis.dOf_le_of_e hpos.ne')

end WeakSl2

end Categorification.Sl2

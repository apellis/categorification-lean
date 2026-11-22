/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.Sl2Categorification.WeakCategorification
import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# Classes of exact functors on Grothendieck-group data

On an abelian category whose objects are artinian, with Grothendieck-group data `K : K0Data`,
an exact endofunctor `G` acts on classes: `[G X] = g [X]` for the linear map `g` sending the class
of each simple object `S` to `[G S]` (`K0Data.cls_map`). This is how the classes `e`, `f` of
Chuang–Rouquier's weak `𝔰𝔩₂`-categorifications (arXiv:math/0407205v2, §5.1.1) arise from the
functors `E`, `F`.
-/

set_option backward.isDefEq.respectTransparency false

namespace Categorification.Sl2

open CategoryTheory Limits

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace K0Data

variable {ι V : Type*} [AddCommGroup V] [Module ℚ V] (K : K0Data C ι V)

/-- The total multiplicity of a class: the sum of its coordinates. -/
noncomputable def tot : V →ₗ[ℚ] ℚ :=
  (Finsupp.linearCombination ℚ fun _ : ι => (1 : ℚ)).comp K.B.repr.toLinearMap

lemma tot_basis (j : ι) : K.tot (K.B j) = 1 := by
  simp [tot]

lemma tot_nonneg {v : V} (hv : v ∈ cone K.B) : 0 ≤ K.tot v := by
  simp only [tot, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul, mul_one]
  exact Finset.sum_nonneg fun j _ => hv j

lemma cls_zero_obj {X : C} (hX : IsZero X) : K.cls X = 0 := by
  have hZ : (ShortComplex.mk (0 : X ⟶ X) (0 : X ⟶ X) (by simp)).ShortExact := by
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · exact ShortComplex.exact_of_isZero_X₂ _ hX
    · exact hX.mono _
    · exact hX.epi _
  have := K.cls_add _ hZ
  simpa using this

lemma cls_simple_iso (S : C) (hS : Simple S) :
    Nonempty (S ≅ K.simple (K.idx S hS)) :=
  K.iso_of_idx_eq S _ hS (K.simple_simple _) (K.idx_simple _).symm

lemma exists_tot_cls_eq (X : C) : ∃ n : ℕ, K.tot (K.cls X) = n := by
  classical
  choose g hg using K.cls_int X
  refine ⟨∑ j ∈ (K.B.repr (K.cls X)).support, g j, ?_⟩
  simp only [tot, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul, mul_one, Nat.cast_sum]
  exact Finset.sum_congr rfl fun j _ => hg j

lemma eq_zero_of_tot_eq_zero {v : V} (hv : v ∈ cone K.B) (h : K.tot v = 0) : v = 0 := by
  simp only [tot, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul, mul_one] at h
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hv j).mp h
  have : K.B.repr v = 0 := by
    ext j
    by_cases hj : j ∈ (K.B.repr v).support
    · exact h0 j hj
    · simpa using hj
  simpa using this

/-- If classes detect zero objects, a nonzero object has total multiplicity at least one. -/
lemma one_le_tot_cls (hdet : ∀ X : C, K.cls X = 0 → IsZero X) {X : C} (hX : ¬ IsZero X) :
    1 ≤ K.tot (K.cls X) := by
  obtain ⟨n, hn⟩ := K.exists_tot_cls_eq X
  rcases n with _ | n
  · exact absurd (hdet X (K.eq_zero_of_tot_eq_zero (K.cls_mem_cone X) (by simpa using hn))) hX
  · rw [hn]; exact_mod_cast Nat.succ_pos n

/-- If classes detect zero objects, every object is artinian: classes of a strictly decreasing
chain of subobjects have strictly decreasing total multiplicity. -/
theorem isArtinianObject_of_cls (hdet : ∀ X : C, K.cls X = 0 → IsZero X) (X : C) :
    IsArtinianObject X := by
  rw [isArtinianObject_iff_not_strictAnti]
  intro f hf
  have step : ∀ n, K.tot (K.cls (f (n + 1) : C)) + 1 ≤ K.tot (K.cls (f n : C)) := by
    intro n
    have hle : f (n + 1) ≤ f n := (hf (Nat.lt_succ_self n)).le
    let s := Subobject.ofLE _ _ hle
    have hS : (ShortComplex.mk s (cokernel.π s) (cokernel.condition s)).ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel s))
        inferInstance inferInstance
    have hc : ¬ IsZero (cokernel s) := by
      intro hz
      have : Epi s := Preadditive.epi_of_isZero_cokernel s hz
      have : IsIso s := isIso_of_mono_of_epi s
      refine (hf (Nat.lt_succ_self n)).ne (le_antisymm hle (Subobject.le_of_comm (inv s) ?_))
      rw [IsIso.inv_comp_eq, Subobject.ofLE_arrow]
    have := K.cls_add _ hS
    simp only at this
    rw [this, map_add]
    linarith [K.one_le_tot_cls hdet hc]
  have key : ∀ n : ℕ, K.tot (K.cls (f n : C)) + n ≤ K.tot (K.cls (f 0 : C)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => push_cast; linarith [step n]
  have := key (⌈K.tot (K.cls (f 0 : C))⌉₊ + 1)
  have h0 := K.tot_nonneg (K.cls_mem_cone (f (⌈K.tot (K.cls (f 0 : C))⌉₊ + 1) : C))
  push_cast at this
  linarith [Nat.le_ceil (K.tot (K.cls (f 0 : C)))]

/-- The linear map induced on classes by an exact endofunctor. -/
noncomputable def clsMap (G : C ⥤ C) : Module.End ℚ V :=
  K.B.constr ℚ fun j => K.cls (G.obj (K.simple j))

lemma clsMap_basis (G : C ⥤ C) (j : ι) : K.clsMap G (K.B j) = K.cls (G.obj (K.simple j)) := by
  simp [clsMap]

variable [∀ X : C, IsArtinianObject X] (G : C ⥤ C) [G.PreservesZeroMorphisms]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

lemma cls_map_of_tot_le (g : Module.End ℚ V)
    (hg : ∀ j, g (K.B j) = K.cls (G.obj (K.simple j))) :
    ∀ (n : ℕ) (X : C), K.tot (K.cls X) ≤ n → K.cls (G.obj X) = g (K.cls X) := by
  intro n
  induction n with
  | zero => ?_
  | succ n ih => ?_
  all_goals
    intro X hX
    by_cases h0 : IsZero X
    · rw [K.cls_zero_obj h0, K.cls_zero_obj (G.map_isZero h0), map_zero]
    let S := simpleSubobject h0
    let s : S ⟶ X := simpleSubobjectArrow h0
    have hS : (ShortComplex.mk s (cokernel.π s) (cokernel.condition s)).ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel s))
        inferInstance inferInstance
    have hX' := K.cls_add _ hS
    simp only at hX'
    have hcS : K.cls S = K.B (K.idx S inferInstance) := K.cls_simple S inferInstance
    have htot : K.tot (K.cls X) = 1 + K.tot (K.cls (cokernel s)) := by
      rw [hX', map_add, hcS, tot_basis]
  · have := K.tot_nonneg (K.cls_mem_cone (cokernel s))
    push_cast at hX
    linarith
  · have hc : K.tot (K.cls (cokernel s)) ≤ n := by push_cast at hX; linarith
    have hG := K.cls_add _ (hS.map_of_exact G)
    simp only [ShortComplex.map_X₂, ShortComplex.map_X₁, ShortComplex.map_X₃] at hG
    obtain ⟨e⟩ := K.cls_simple_iso S inferInstance
    rw [hG, ih _ hc, hX', map_add, hcS, hg, K.cls_of_iso (G.mapIso e)]

/-- An exact endofunctor acts on classes through the linear map determined by the classes of
the images of the simple objects. -/
theorem cls_map (g : Module.End ℚ V) (hg : ∀ j, g (K.B j) = K.cls (G.obj (K.simple j)))
    (X : C) : K.cls (G.obj X) = g (K.cls X) :=
  K.cls_map_of_tot_le G g hg _ X (Nat.le_ceil _)

theorem cls_map_clsMap (X : C) : K.cls (G.obj X) = K.clsMap G (K.cls X) :=
  K.cls_map G _ (K.clsMap_basis G) X

end K0Data

end Categorification.Sl2

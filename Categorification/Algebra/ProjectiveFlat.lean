/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.ProjectiveKProjective

set_option backward.isDefEq.respectTransparency false

/-!
# Tensoring with a projective module preserves acyclic dg modules

For a ring `B` (a dg ring concentrated in degree `0`), a projective right `B`-module `P` and an
acyclic dg `B`-module `Y`, the tensor product `P ⊗_B Y` is acyclic. Write `P` as a retract of
the free module on `P`: the coordinates `P ⊗_B Y → (P →₀ Y)`, `m ⊗ y ↦ (p ↦ s(m)_p y)`, commute
with the differentials, so a cocycle of `P ⊗_B Y` has cocycle coordinates, and the
recombination `(p ↦ y_p) ↦ Σ p ⊗ y_p` of primitives of the coordinates is a primitive.

This is the input for computing the derived tensor products of B. Webster, *Knot invariants and
higher representation theory*, arXiv:1309.3796v2, proof of Proposition 6.7, without
resolving the argument: the bimodules of the functors `𝔈_i`, `𝔉_i` are projective as modules
over both rings.

## Main results

* `Categorification.InDegreeZero.isAcyclic_tensorProductOver`: `P ⊗_B Y` is acyclic for `P`
  projective and `Y` acyclic.
-/

open DG DG.DegreeZero MulOpposite

namespace Categorification.InDegreeZero

variable {B : Type*} [Ring B] {P : Type*} [AddCommGroup P] [Module Bᵐᵒᵖ P]
  {Y : Type*} [AddCommGroup Y] [DGAddCommGroup Y] [Module B Y] [DGModule B Y]

/-- The additive map `b ↦ unop b • y`. -/
def opSmulRight (y : Y) : Bᵐᵒᵖ →+ Y where
  toFun b := unop b • y
  map_zero' := by simp
  map_add' b b' := by simp [add_smul]

variable (Y) in
/-- The coordinates `m ⊗ y ↦ (p ↦ s(m)_p • y)` along a section `s` of the free module. -/
noncomputable def coordBilin (s : P →ₗ[Bᵐᵒᵖ] P →₀ Bᵐᵒᵖ) : InDegreeZero P →+ Y →+ (P →₀ Y) where
  toFun m :=
    { toFun y := Finsupp.mapRange.addMonoidHom (opSmulRight y) (s m)
      map_zero' := by ext p; simp [opSmulRight]
      map_add' y y' := by ext p; simp [opSmulRight, smul_add] }
  map_zero' := by ext y p; simp
  map_add' m m' := by ext y p; simp [map_add]

omit [DGAddCommGroup Y] [DGModule B Y] in
theorem coordBilin_balanced (s : P →ₗ[Bᵐᵒᵖ] P →₀ Bᵐᵒᵖ) (a : B) (m : InDegreeZero P) (y : Y) :
    coordBilin Y s (op a • m) y = coordBilin Y s m (a • y) := by
  ext p
  have : s (op a • m) = op a • s (show P from m) := s.map_smul (op a) m
  simp only [coordBilin, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Finsupp.mapRange.addMonoidHom_apply,
    Finsupp.mapRange_apply, opSmulRight]
  rw [show (op a • m : InDegreeZero P) = (op a • (show P from m) : P) from rfl, this,
    Finsupp.smul_apply, smul_eq_mul, unop_mul, unop_op, mul_smul]

/-- The coordinate map `P ⊗_B Y → (P →₀ Y)`. -/
noncomputable def coord (s : P →ₗ[Bᵐᵒᵖ] P →₀ Bᵐᵒᵖ) :
    TensorProductOver B (InDegreeZero P) Y →+ (P →₀ Y) :=
  TensorProductOver.lift (coordBilin Y s) (coordBilin_balanced s)

omit [DGAddCommGroup Y] [DGModule B Y] in
theorem coord_tmul (s : P →ₗ[Bᵐᵒᵖ] P →₀ Bᵐᵒᵖ) (m : InDegreeZero P) (y : Y) (p : P) :
    coord s (TensorProductOver.tmul B m y) p = unop (s m p) • y := rfl

/-- The recombination `(p ↦ y_p) ↦ Σ p ⊗ y_p`. -/
noncomputable def recomb : (P →₀ Y) →+ TensorProductOver B (InDegreeZero P) Y :=
  Finsupp.liftAddHom fun p => TensorProductOver.tmulAddHom B (InDegreeZero P) Y p

omit [DGAddCommGroup Y] [DGModule B Y] in
theorem recomb_coord (s : P →ₗ[Bᵐᵒᵖ] P →₀ Bᵐᵒᵖ)
    (hs : Function.LeftInverse (Finsupp.linearCombination Bᵐᵒᵖ id) s)
    (z : TensorProductOver B (InDegreeZero P) Y) : recomb (coord s z) = z := by
  have : (recomb (B := B) (Y := Y)).comp (coord s) = AddMonoidHom.id _ := by
    refine TensorProductOver.addHom_ext fun m y => ?_
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply, recomb, coord,
      TensorProductOver.lift_tmul, coordBilin, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      Finsupp.mapRange.addMonoidHom_apply, Finsupp.liftAddHom_apply]
    rw [Finsupp.sum_mapRange_index (by simp)]
    simp only [TensorProductOver.tmulAddHom_apply, opSmulRight, AddMonoidHom.coe_mk,
      ZeroHom.coe_mk]
    have key : ∀ p (b : Bᵐᵒᵖ), TensorProductOver.tmul B (p : InDegreeZero P) (unop b • y) =
        TensorProductOver.tmul B ((b • p : P) : InDegreeZero P) y := fun p b => by
      rw [← TensorProductOver.op_smul_tmul, op_unop]
    simp only [key]
    have hm : (((s m).sum fun p b => b • id p : P) : InDegreeZero P) = m := by
      have := hs (show P from m)
      rwa [Finsupp.linearCombination_apply] at this
    conv_rhs => rw [← hm]
    change _ = (TensorProductOver.tmulAddHom B (InDegreeZero P) Y).flip y
      (((s m).sum fun p b => b • id p : P) : InDegreeZero P)
    rw [Finsupp.sum, Finsupp.sum, map_sum]
    rfl
  exact DFunLike.congr_fun this z

theorem coord_mem (s : P →ₗ[Bᵐᵒᵖ] P →₀ Bᵐᵒᵖ) {n : ℤ}
    {z : TensorProductOver B (InDegreeZero P) Y} (hz : z ∈ grading n) (p : P) :
    coord s z p ∈ grading n := by
  refine TensorProductOver.induction_on_mem_grading (P := fun z => coord s z p ∈ grading n)
    (by simp) ?_ ?_ ?_ hz
  · intro i j m y hm hy hij
    rcases (mem_grading_iff P).mp hm with rfl | rfl
    · rw [coord_tmul]
      simpa [← hij] using smul_mem_grading (ring_mem_grading_zero (unop (s m p))) hy
    · rw [TensorProductOver.zero_tmul, map_zero]; exact zero_mem _
  · intro x y hx hy
    rw [map_add, Finsupp.add_apply]; exact add_mem hx hy
  · intro x hx
    rw [map_neg, Finsupp.neg_apply]; exact neg_mem hx

theorem coord_d (s : P →ₗ[Bᵐᵒᵖ] P →₀ Bᵐᵒᵖ) (z : TensorProductOver B (InDegreeZero P) Y)
    (p : P) : coord s (d z) p = d (coord s z p) := by
  induction z using TensorProductOver.induction_on with
  | zero => simp
  | tmul m y =>
    rw [TensorProductOver.d_tmul_of_mem (mem_grading_zero m), d_apply,
      TensorProductOver.zero_tmul, zero_add, koszulSign_zero, one_smul, coord_tmul, coord_tmul,
      d_smul_of_mem_zero (ring_mem_grading_zero _), ring_d_apply, zero_smul, zero_add]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

/-- **Tensoring with a projective module preserves acyclic dg modules**: for a ring `B` in
degree `0`, a projective right `B`-module `P` and an acyclic dg `B`-module `Y`, `P ⊗_B Y` is
acyclic. -/
theorem isAcyclic_tensorProductOver [Module.Projective Bᵐᵒᵖ P] (hY : IsAcyclic Y) :
    IsAcyclic (TensorProductOver B (InDegreeZero P) Y) := by
  classical
  obtain ⟨s, hs⟩ := Module.Projective.out (R := Bᵐᵒᵖ) (P := P)
  refine isAcyclic_iff.mpr fun n z hz hdz => ?_
  have hc : ∀ p, ∃ w ∈ grading (n - 1), d w = coord s z p := fun p =>
    hY.exists_d_eq (coord_mem s hz p) (by rw [← coord_d, hdz, map_zero, Finsupp.zero_apply])
  choose w hw hdw using hc
  have hmem : ∀ p, TensorProductOver.tmul B (p : InDegreeZero P) (w p) ∈ grading (n - 1) :=
    fun p => by
      simpa using TensorProductOver.tmul_mem_grading (mem_grading_zero (p : InDegreeZero P)) (hw p)
  refine ⟨∑ p ∈ (coord s z).support, TensorProductOver.tmul B (p : InDegreeZero P) (w p),
    sum_mem fun p _ => hmem p, ?_⟩
  rw [map_sum]
  conv_rhs => rw [← recomb_coord s hs z]
  simp only [recomb, Finsupp.liftAddHom_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [TensorProductOver.d_tmul_of_mem (mem_grading_zero (p : InDegreeZero P)), d_apply,
    TensorProductOver.zero_tmul, zero_add, koszulSign_zero, one_smul, hdw]
  rfl


theorem d_tmul_inDegreeZero (m : InDegreeZero P) (y : Y) :
    d (TensorProductOver.tmul B m y) = TensorProductOver.tmul B m (d y) := by
  rw [TensorProductOver.d_tmul_of_mem (mem_grading_zero m), d_apply,
    TensorProductOver.zero_tmul, zero_add, koszulSign_zero, one_smul]

omit [DGAddCommGroup Y] [DGModule B Y] in
theorem eq_sum_coord [DecidableEq P] (s : P →ₗ[Bᵐᵒᵖ] P →₀ Bᵐᵒᵖ)
    (hs : Function.LeftInverse (Finsupp.linearCombination Bᵐᵒᵖ id) s)
    (z : TensorProductOver B (InDegreeZero P) Y) :
    z = ∑ p ∈ (coord s z).support, TensorProductOver.tmul B (p : InDegreeZero P) (coord s z p) :=
  (recomb_coord s hs z).symm

theorem coord_mem_cocycles (s : P →ₗ[Bᵐᵒᵖ] P →₀ Bᵐᵒᵖ) {n : ℤ}
    {z : TensorProductOver B (InDegreeZero P) Y} (hz : z ∈ cocycles _ n) (p : P) :
    coord s z p ∈ cocycles Y n := by
  rw [mem_cocycles] at hz ⊢
  exact ⟨coord_mem s hz.1 p, by rw [← coord_d, hz.2, map_zero, Finsupp.zero_apply]⟩

theorem sum_tmul_mem_grading {k : ℤ} (S : Finset P) (v : P → Y) (hv : ∀ p, v p ∈ grading k) :
    (∑ p ∈ S, TensorProductOver.tmul B (p : InDegreeZero P) (v p) :
      TensorProductOver B (InDegreeZero P) Y) ∈ grading k :=
  sum_mem fun p _ => by
    simpa using TensorProductOver.tmul_mem_grading (mem_grading_zero (p : InDegreeZero P)) (hv p)

theorem d_sum_tmul (S : Finset P) (v : P → Y) :
    d (∑ p ∈ S, TensorProductOver.tmul B (p : InDegreeZero P) (v p) :
      TensorProductOver B (InDegreeZero P) Y) =
      ∑ p ∈ S, TensorProductOver.tmul B (p : InDegreeZero P) (d (v p)) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun p _ => d_tmul_inDegreeZero _ _

variable {Y' : Type*} [AddCommGroup Y'] [DGAddCommGroup Y'] [Module B Y'] [DGModule B Y']

omit [DGAddCommGroup Y] [DGModule B Y] [DGAddCommGroup Y'] [DGModule B Y'] in
theorem coord_map (s : P →ₗ[Bᵐᵒᵖ] P →₀ Bᵐᵒᵖ) (g : Y →ₗ[B] Y')
    (z : TensorProductOver B (InDegreeZero P) Y) (p : P) :
    coord s (TensorProductOver.map LinearMap.id g z) p = g (coord s z p) := by
  induction z using TensorProductOver.induction_on with
  | zero => simp
  | tmul m y => simp [TensorProductOver.map_tmul, coord_tmul]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

/-- **Tensoring with a projective module preserves quasi-isomorphisms**: for a ring `B` in
degree `0`, a projective right `B`-module `P` and a quasi-isomorphism `g : Y → Y'` of dg
`B`-modules, `P ⊗_B g` is a quasi-isomorphism. -/
theorem isQuasiIso_lTensor {A : Type*} [Ring A] [Module A P] [SMulCommClass A Bᵐᵒᵖ P]
    [Module.Projective Bᵐᵒᵖ P] {g : Y →ᵈᵍ[B] Y'} (hg : g.IsQuasiIso) :
    (DGModuleHom.lTensor A (InDegreeZero P) g).IsQuasiIso := by
  classical
  obtain ⟨s, hs⟩ := Module.Projective.out (R := Bᵐᵒᵖ) (P := P)
  intro n
  set F := DGModuleHom.lTensor A (InDegreeZero P) g
  have hF : ∀ z, F z = TensorProductOver.map LinearMap.id g.toLinearMap z := fun _ => rfl
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    induction x using cohomology.induction_on with
    | h z =>
    rw [cohomology.map_mk, cohomology.mk_eq_zero_iff] at hx
    obtain ⟨w, hw, hdw⟩ := hx
    have hc := fun p => coord_mem_cocycles s z.2 p
    have hp : ∀ p, ∃ v ∈ grading (n - 1), d v = coord s (z : TensorProductOver B _ Y) p := by
      intro p
      have h0 : cohomology.map g n (cohomology.mk Y n ⟨_, hc p⟩) = 0 := by
        rw [cohomology.map_mk, cohomology.mk_eq_zero_iff]
        refine ⟨coord s w p, coord_mem s hw p, ?_⟩
        rw [← coord_d, hdw]
        exact coord_map s g.toLinearMap _ p
      exact (cohomology.mk_eq_zero_iff _).mp ((injective_iff_map_eq_zero _).mp (hg n).1 _ h0)
    choose v hv hdv using hp
    rw [cohomology.mk_eq_zero_iff]
    refine ⟨∑ p ∈ (coord s (z : TensorProductOver B _ Y)).support,
      TensorProductOver.tmul B (p : InDegreeZero P) (v p), sum_tmul_mem_grading _ _ hv, ?_⟩
    rw [d_sum_tmul]
    simp only [hdv]
    exact (eq_sum_coord s hs _).symm
  · intro x'
    induction x' using cohomology.induction_on with
    | h z' =>
    have hc := fun p => coord_mem_cocycles s z'.2 p
    have hp : ∀ p, ∃ x : cocycles Y n, ∃ u ∈ grading (n - 1),
        d u = g x - coord s (z' : TensorProductOver B _ Y') p := by
      intro p
      obtain ⟨y, hy⟩ := (hg n).2 (cohomology.mk Y' n ⟨_, hc p⟩)
      obtain ⟨x, rfl⟩ := cohomology.mk_surjective Y n y
      rw [cohomology.map_mk, cohomology.mk_eq_mk_iff] at hy
      exact ⟨x, hy⟩
    choose x u hu hdu using hp
    set S := (coord s (z' : TensorProductOver B _ Y')).support
    have hxz : (∑ p ∈ S, TensorProductOver.tmul B (p : InDegreeZero P) (x p : Y) :
        TensorProductOver B (InDegreeZero P) Y) ∈ cocycles _ n := by
      rw [mem_cocycles]
      refine ⟨sum_tmul_mem_grading _ _ fun p => (x p).2.1, ?_⟩
      rw [d_sum_tmul]
      exact Finset.sum_eq_zero fun p _ => by rw [(x p).2.2, TensorProductOver.tmul_zero]
    refine ⟨cohomology.mk _ n ⟨_, hxz⟩, ?_⟩
    rw [cohomology.map_mk, cohomology.mk_eq_mk_iff]
    refine ⟨∑ p ∈ S, TensorProductOver.tmul B (p : InDegreeZero P) (u p),
      sum_tmul_mem_grading _ _ hu, ?_⟩
    rw [d_sum_tmul]
    simp only [hdu, sub_eq_add_neg, TensorProductOver.tmul_add, TensorProductOver.tmul_neg,
      Finset.sum_add_distrib, Finset.sum_neg_distrib]
    congr 1
    · rw [map_sum]; rfl
    · exact congrArg Neg.neg (eq_sum_coord s hs _).symm

end Categorification.InDegreeZero

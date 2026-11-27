/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DG.Category.WeightComparison
import DG.Category.Resolution.KProjective
import DG.Homotopy.KProjective

/-!
# Forgetting the weight grading of dg modules over `C_A`

For a dg ring `A` with an internal grading, a dg module `M` over the dg category
`C_A = DG.WeightCategory A` has the underlying dg `A`-module `⨁ k, M⟨k⟩`
(`DG.CatModule.WeightSum`), which forgets the weight grading. This file shows that forgetting
the weights is compatible with homotopies and preserves K-projectivity, the two inputs for its
derived functor.

* `DG.CatModule.weightSumMapCochain h`: a cochain between dg modules over `C_A` induces a
  cochain between their weight sums, compatibly with the differential of the Hom complexes.
* `DG.CatModule.Homotopic.weightSumMap`: homotopic morphisms have homotopic weight sums.
* `DG.CatModule.weightConst N`: a dg `A`-module `N` as a dg module over `C_A` with the same
  value `N` at every weight, on which `a ∈ A⟨l - k⟩` acts by multiplication. Cochains
  `M ⟶ weightConst N` are cochains `⨁ k, M⟨k⟩ ⟶ N` (`DG.CatModule.weightSumCochain`).
* `DG.CatModule.IsKProjective.weightSum`: the weight sum of a K-projective dg module over `C_A`
  is a K-projective dg `A`-module.

This is the forgetful step used to compare a graded derived braiding functor with the ungraded
one (B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
Definition 6.6, where the braiding functors act on graded modules).
-/

open CategoryTheory DirectSum

universe v u

noncomputable section

namespace DG

namespace CatModule

open WeightCategory

variable {A : Type u} [Ring A] [DGAddCommGroup A] [InternalGrading A] [BigradedDGRing A]

/-! ### Cochains between weight sums -/

section MapCochain

variable {M M' : CatModule.{v} (WeightCategory A)}

/-- The action of a homogeneous element on a summand, written with an arbitrary target index. -/
theorem weightSum_smul_of' (N : CatModule.{v} (WeightCategory A)) {k l : ℤ}
    (f : (⟨k⟩ : WeightCategory A) ⟶ ⟨l⟩) (y : N.obj ⟨k⟩) :
    f.1 • weightSumOf N k y = weightSumOf N l (f • y) := by
  rw [weightSum_smul_of N f.2]
  exact of_act_eq N (show k + (l - k) = l by ring) _ f rfl y

/-- A cochain between dg modules over `C_A`, summed over the weights. -/
def weightSumMapCochain {n : ℤ} (h : Cochain M M' n) :
    DG.Cochain A M.WeightSum M'.WeightSum n where
  toFun := DirectSum.map fun k => h.app ⟨k⟩
  map_zero' := map_zero _
  map_add' := map_add _
  map_mem' j x hx k := by
    change (DirectSum.map (fun k => h.app ⟨k⟩) x) k ∈ _
    rw [DirectSum.map_apply]
    exact h.map_mem (hx k)
  map_smul' {i a} ha x := by
    classical
    change DirectSum.map (fun k => h.app ⟨k⟩) (a • x : M.WeightSum) =
      koszulSign (n * i) • (a • DirectSum.map (fun k => h.app ⟨k⟩) x : M'.WeightSum)
    induction x using DirectSum.induction_on with
    | zero =>
      rw [weightSum_smul_zero, map_zero, weightSum_smul_zero, Units.smul_def]
      exact (zsmul_zero _).symm
    | add x y hx hy =>
      rw [weightSum_smul_add, map_add, hx, hy, map_add, weightSum_smul_add, Units.smul_def,
        Units.smul_def, Units.smul_def, zsmul_add]
    | of k y =>
      rw [← DirectSum.sum_support_decompose (wgrading (M := A)) a, Finset.sum_smul,
        Finset.sum_smul, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      let b := decompose (wgrading (M := A)) a l
      let f : (⟨k⟩ : WeightCategory A) ⟶ ⟨k + l⟩ := homOfMem b.2 k (k + l) (by ring)
      have hf : f ∈ grading i := decompose_wgrading_mem_grading ha l
      change DirectSum.map (fun k => h.app ⟨k⟩) (f.1 • weightSumOf M k y : M.WeightSum) =
        koszulSign (n * i) •
          (f.1 • DirectSum.map (fun k => h.app ⟨k⟩) (weightSumOf M k y) : M'.WeightSum)
      rw [weightSum_smul_of' M f, DirectSum.map_of, DirectSum.map_of, weightSum_smul_of' M' f,
        h.map_smul hf, Units.smul_def, Units.smul_def, map_zsmul]

@[simp]
theorem weightSumMapCochain_of {n : ℤ} (h : Cochain M M' n) (k : ℤ) (y : M.obj ⟨k⟩) :
    weightSumMapCochain h (weightSumOf M k y) = weightSumOf M' k (h.app ⟨k⟩ y) :=
  DirectSum.map_of _ _ _

theorem weightSumMapCochain_ext {n : ℤ} {c c' : DG.Cochain A M.WeightSum M'.WeightSum n}
    (hc : ∀ k (y : M.obj ⟨k⟩), c (weightSumOf M k y) = c' (weightSumOf M k y)) : c = c' := by
  refine DG.Cochain.ext fun x => ?_
  induction x using DirectSum.induction_on with
  | zero => simp
  | of k y => exact hc k y
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem weightSumMapCochain_add {n : ℤ} (h h' : Cochain M M' n) :
    weightSumMapCochain (h + h') = weightSumMapCochain h + weightSumMapCochain h' :=
  weightSumMapCochain_ext fun k y => by
    rw [DG.Cochain.add_apply, weightSumMapCochain_of, weightSumMapCochain_of,
      weightSumMapCochain_of, ← map_add]
    rfl

theorem weightSumMapCochain_ofHom (φ : M ⟶ M') :
    weightSumMapCochain (Cochain.ofHom φ) = DG.Cochain.ofHom (weightSumMap φ) :=
  weightSumMapCochain_ext fun k y => by
    rw [weightSumMapCochain_of, DG.Cochain.ofHom_apply, weightSumMap_of, Cochain.ofHom_apply]

theorem weightSumMapCochain_δ (n m : ℤ) (h : Cochain M M' n) :
    weightSumMapCochain (CatModule.δ n m h) = DG.δ n m (weightSumMapCochain h) := by
  by_cases hnm : n + 1 = m
  · refine weightSumMapCochain_ext fun k y => ?_
    rw [weightSumMapCochain_of, CatModule.δ_apply n m hnm, DG.δ_apply n m hnm, weightSum_d_of,
      weightSumMapCochain_of, weightSumMapCochain_of, weightSum_d_of, map_sub, Units.smul_def,
      Units.smul_def, map_zsmul]
  · rw [CatModule.δ_shape n m hnm, DG.δ_shape n m hnm]
    refine weightSumMapCochain_ext fun k y => ?_
    rw [weightSumMapCochain_of]
    exact map_zero _

/-- Homotopic morphisms of dg modules over `C_A` have homotopic weight sums. -/
theorem Homotopic.weightSumMap {f g : M ⟶ M'} (h : Homotopic f g) :
    DG.Homotopic (CatModule.weightSumMap f) (CatModule.weightSumMap g) := by
  obtain ⟨h⟩ := h
  refine ⟨⟨weightSumMapCochain h.hom, ?_⟩⟩
  rw [← weightSumMapCochain_ofHom, ← weightSumMapCochain_ofHom, h.ofHom_eq,
    weightSumMapCochain_add, weightSumMapCochain_δ]

end MapCochain

/-! ### The constant dg module and K-projectivity -/

section Const

variable (N : Type v) [AddCommGroup N] [DGAddCommGroup N] [Module A N] [DGModule A N]

/-- A dg `A`-module as a dg module over `C_A` with the value `N` at every weight; a morphism
`a ∈ A⟨l - k⟩` acts by multiplication by `a`. -/
abbrev weightConst : CatModule.{v} (WeightCategory A) where
  obj _ := N
  act := AddMonoidHom.mk' (fun f => AddMonoidHom.mk' (fun m => f.1 • m) (_root_.smul_add f.1))
    fun f g => by
      ext m
      exact _root_.add_smul f.1 g.1 m
  act_mem' hf hm := _root_.DG.smul_mem_grading (A := A) (M := N) hf hm
  act_id' _ m := _root_.one_smul A m
  act_comp' f g m := SemigroupAction.mul_smul g.1 f.1 m
  d_act' {k l i f} hf m := by
    change d (f.1 • m) = d f.1 • m + ((koszulSign i : ℤ) • (f.1 • d m))
    rw [_root_.DG.d_smul (A := A) (a := f.1) hf, Units.smul_def]

variable {N}

/-- The dg module `weightConst N` is acyclic when `N` is. -/
theorem isAcyclic_weightConst (hN : DG.IsAcyclic N) : IsAcyclic (weightConst (A := A) N) :=
  fun _ => hN

variable (M : CatModule.{v} (WeightCategory A))

/-- A cochain `M ⟶ weightConst N` is a cochain `⨁ k, M⟨k⟩ ⟶ N`. -/
def weightSumCochain {n : ℤ} (c : Cochain M (weightConst N) n) : DG.Cochain A M.WeightSum N n where
  toFun := DirectSum.toAddMonoid fun k => c.app ⟨k⟩
  map_zero' := map_zero _
  map_add' := map_add _
  map_mem' j x hx := by
    classical
    rw [← DirectSum.sum_support_of x, map_sum]
    refine sum_mem fun k _ => ?_
    rw [DirectSum.toAddMonoid_of]
    exact c.map_mem (hx k)
  map_smul' {i a} ha x := by
    classical
    change DirectSum.toAddMonoid (fun k => c.app ⟨k⟩) (a • x : M.WeightSum) =
      koszulSign (n * i) • (a • DirectSum.toAddMonoid (fun k => c.app ⟨k⟩) x : N)
    induction x using DirectSum.induction_on with
    | zero =>
      rw [weightSum_smul_zero, map_zero, _root_.smul_zero, Units.smul_def]
      exact (zsmul_zero _).symm
    | add x y hx hy =>
      rw [weightSum_smul_add, map_add, hx, hy, map_add, _root_.smul_add, _root_.smul_add]
    | of k y =>
      rw [← DirectSum.sum_support_decompose (wgrading (M := A)) a, Finset.sum_smul,
        Finset.sum_smul, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      let b := decompose (wgrading (M := A)) a l
      let f : (⟨k⟩ : WeightCategory A) ⟶ ⟨k + l⟩ := homOfMem b.2 k (k + l) (by ring)
      have hf : f ∈ grading i := decompose_wgrading_mem_grading ha l
      change DirectSum.toAddMonoid (fun k => c.app ⟨k⟩) (f.1 • weightSumOf M k y : M.WeightSum) =
        koszulSign (n * i) •
          (f.1 • DirectSum.toAddMonoid (fun k => c.app ⟨k⟩) (weightSumOf M k y))
      rw [weightSum_smul_of' M f, DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of,
        c.map_smul hf]
      rfl

variable {M}

@[simp]
theorem weightSumCochain_of {n : ℤ} (c : Cochain M (weightConst N) n) (k : ℤ) (y : M.obj ⟨k⟩) :
    weightSumCochain M c (weightSumOf M k y) = c.app ⟨k⟩ y :=
  DirectSum.toAddMonoid_of _ _ _

omit [DGModule A N] in
theorem weightSumCochain_ext {n : ℤ} {c c' : DG.Cochain A M.WeightSum N n}
    (hc : ∀ k (y : M.obj ⟨k⟩), c (weightSumOf M k y) = c' (weightSumOf M k y)) : c = c' := by
  refine DG.Cochain.ext fun x => ?_
  induction x using DirectSum.induction_on with
  | zero => simp
  | of k y => exact hc k y
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem weightSumCochain_δ (n m : ℤ) (c : Cochain M (weightConst N) n) :
    weightSumCochain M (CatModule.δ n m c) = DG.δ n m (weightSumCochain M c) := by
  by_cases hnm : n + 1 = m
  · refine weightSumCochain_ext fun k y => ?_
    rw [weightSumCochain_of, CatModule.δ_apply n m hnm, DG.δ_apply n m hnm, weightSum_d_of,
      weightSumCochain_of, weightSumCochain_of]
  · rw [CatModule.δ_shape n m hnm, DG.δ_shape n m hnm]
    refine weightSumCochain_ext fun k y => ?_
    rw [weightSumCochain_of]
    rfl

/-- The morphism `M ⟶ weightConst N` restricting a morphism `⨁ k, M⟨k⟩ ⟶ N` to the
summands. -/
def weightSumAdjoint (f : M.WeightSum →ᵈᵍ[A] N) : M ⟶ weightConst N where
  app k := (f.toLinearMap.toAddMonoidHom).comp (weightSumOf M k.as)
  map_mem' {k n m} hm := f.map_mem (DG.DirectSum.of_mem_grading _ _ hm)
  map_d' {k} m := by
    change f (weightSumOf M k.as (d m)) = d (f (weightSumOf M k.as m))
    rw [← weightSum_d_of, f.map_d]
  map_smul' {k l} g m := by
    change f (weightSumOf M l.as (g • m)) = (g.1 • f (weightSumOf M k.as m) : N)
    rw [← weightSum_smul_of' M g, map_smul]

theorem weightSumCochain_ofHom_weightSumAdjoint (f : M.WeightSum →ᵈᵍ[A] N) :
    weightSumCochain M (Cochain.ofHom (weightSumAdjoint f)) = DG.Cochain.ofHom f :=
  weightSumCochain_ext fun _ _ => by rw [weightSumCochain_of]; rfl

/-- **The weight sum of a K-projective dg module over `C_A` is K-projective**: a morphism from
`⨁ k, P⟨k⟩` to an acyclic dg `A`-module `N` restricts to a morphism `P ⟶ weightConst N` into
an acyclic dg module over `C_A`, and a null-homotopy of the latter glues to one of the
former. -/
theorem IsKProjective.weightSum {P : CatModule.{v} (WeightCategory A)} (hP : IsKProjective P) :
    DG.IsKProjective.{v} A P.WeightSum := by
  intro N _ _ _ _ hN f
  obtain ⟨h, hh⟩ := homotopic_zero_iff_exists.mp
    (hP (weightConst N) (isAcyclic_weightConst hN) (weightSumAdjoint f))
  refine DG.homotopic_zero_iff_exists.mpr ⟨weightSumCochain P h, ?_⟩
  rw [← weightSumCochain_ofHom_weightSumAdjoint, hh, weightSumCochain_δ]

end Const

end CatModule

end DG

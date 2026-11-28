/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensorHomology
import Categorification.Algebra.DerivedHomologyShift
import Categorification.Algebra.DegreeZeroHeart
import Categorification.Algebra.TriangleChainHomology
import Categorification.Algebra.DerivedTensorFiltration

/-!
# Tor-acyclicity from acyclic covers

Let `M` be a right `B`-module. A class `𝒞` of left `B`-modules in which every member `Y` has a
cover `0 → K → P → Y → 0` with `K ∈ 𝒞` and `P` Tor-acyclic against `M` (no cohomology of
`M ⊗ᴸ_B P` in any degree) consists of modules Tor-acyclic against `M`: by the long exact
sequence `Tor_{m}(M, Y) ≅ Tor_{m-1}(M, K)` for `m ≥ 1` and `Tor_0(M, Y)` is a quotient of
`Tor_0(M, P) = 0`, so induction on `m` over the whole class gives the vanishing; the covers
need not form a finite resolution.

This is the dimension shift used for the `E²` terms in B. Webster, *Knot invariants and higher
representation theory*, arXiv:1309.3796v3, §7.3, proof of Proposition 7.22: there `𝒞` is the
class of standardizations of finite-dimensional modules over a block, and the covers are the
standardizations of projective covers.

## Main results

* `isZero_derivedTensorHomology_module_of_pos`: `M ⊗ᴸ_B Y` has no cohomology in positive
  degrees for a module `Y`.
* `torAcyclic_of_acyclicCovers`: Tor-acyclicity of a class with acyclic covers.
* `isZero_derivedTensorHomology_of_concentratedCovers`: no higher Tor for a class with covers
  without higher Tor whose `Tor₀` map is injective (the diagonal term).
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated DG DG.DerivedCategory
open scoped DG.DegreeZero

noncomputable section

namespace Categorification

universe w

/-- Cohomology vanishes in a degree where the grading vanishes. -/
theorem subsingleton_cohomology_of_grading {X : Type*} [AddCommGroup X] [DGAddCommGroup X]
    {n : ℤ} (h : ∀ x ∈ grading (M := X) n, x = 0) : Subsingleton (cohomology X n) := by
  refine ⟨fun a b => ?_⟩
  have hz : ∀ c : cohomology X n, c = 0 := fun c => by
    induction c using cohomology.induction_on with
    | h z =>
      rw [cohomology.mk_eq_zero_iff]
      rw [h z.1 z.2.1]
      exact zero_mem _
  rw [hz a, hz b]

section Positive

variable {B : Type} [Ring B] (M : Type) [AddCommGroup M] [Module Bᵐᵒᵖ M]

/-- The tensor product of a module in degree zero with a non-positively graded dg module is
non-positively graded. -/
theorem tensorProductOver_eq_zero_of_pos {X : Type} [AddCommGroup X] [DGAddCommGroup X]
    [Module B X] [DGModule B X] (hX : IsNonposGraded X) {n : ℤ} (hn : 0 < n)
    {y : TensorProductOver B (InDegreeZero M) X} (hy : y ∈ grading n) : y = 0 := by
  refine TensorProductOver.induction_on_mem_grading (P := fun y => y = 0) rfl ?_
    (fun x y hx hy => by rw [hx, hy, add_zero]) (fun x hx => by rw [hx, neg_zero]) hy
  intro i j m p hm hp hij
  rcases (InDegreeZero.mem_grading_iff _).mp hm with hi | hm0
  · rw [hX.eq_zero (by omega) hp, TensorProductOver.tmul_zero]
  · rw [hm0, TensorProductOver.zero_tmul]

end Positive

section Derived

variable {k B : Type} [CommRing k] [Ring B] [HasDerivedCategory.{w, 0} k]
  [HasDerivedCategory.{w, 0} B]
  (M : Type) [AddCommGroup M] [Module k M] [Module Bᵐᵒᵖ M] [SMulCommClass k Bᵐᵒᵖ M]

/-- **No positive Tor**: for a module `Y`, `M ⊗ᴸ_B Y` has no cohomology in positive degrees. -/
theorem isZero_derivedTensorHomology_module_of_pos (Y : ModuleCat.{0} B) {n : ℤ} (hn : 0 < n) :
    IsZero ((homologyFunctor (A := k) k n).obj
      ((derivedTensor.{w} k B M).obj (Q.obj ((degreeZeroModuleFunctor B).obj Y)))) := by
  let P := DGModuleCat.of B (ConnectiveResolution.Colim B (InDegreeZero Y))
  have hB : IsNonposGraded B := isNonposGraded_iff.mpr fun _ hn _ hx =>
    (DegreeZero.mem_grading_iff.mp hx).resolve_left hn.ne'
  have hY : IsNonposGraded (InDegreeZero Y) := isNonposGraded_iff.mpr fun _ hn _ hx =>
    ((InDegreeZero.mem_grading_iff _).mp hx).resolve_left hn.ne'
  have hP : IsKProjective.{0} B P :=
    (ConnectiveResolution.semiFreeFiltration B (InDegreeZero Y)).isKProjective
  let aug : P ⟶ (degreeZeroModuleFunctor B).obj Y :=
    DGModuleCat.ofHom (ConnectiveResolution.π B (InDegreeZero Y))
  have haug : IsIso (Q.map aug) :=
    (isIso_Q_map_iff _).mpr (ConnectiveResolution.isQuasiIso_π B (InDegreeZero Y) hB hY)
  let e : (derivedTensor.{w} k B M).obj (Q.obj ((degreeZeroModuleFunctor B).obj Y)) ≅
      Q.obj ((DGModuleCat.tensorFunctor k (InDegreeZero M)).obj P) :=
    (derivedTensor.{w} k B M).mapIso (asIso (Q.map aug)).symm ≪≫ derivedTensorObjIso hP
  refine IsZero.of_iso ?_ ((homologyFunctor (A := k) k n).mapIso e)
  apply isZero_homology_of_isZero_intHomology
  rw [isZero_homologyFunctor_Q_obj_iff]
  exact subsingleton_cohomology_of_grading fun y hy =>
    tensorProductOver_eq_zero_of_pos M
      (ConnectiveResolution.isNonposGraded_colim B (InDegreeZero Y) hB) hn hy

/-- Tor-acyclicity of a left module against `M`: `M ⊗ᴸ_B Y` has no cohomology. -/
def TorAcyclic (Y : ModuleCat.{0} B) : Prop :=
  ∀ n : ℤ, IsZero ((homologyFunctor (A := k) k n).obj
    ((derivedTensor.{w} k B M).obj (Q.obj ((degreeZeroModuleFunctor B).obj Y))))

/-- **Tor-acyclicity from acyclic covers** (the dimension shift in B. Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.22, without a finite resolution): if every
member `Y` of a class `𝒞` has a short exact sequence `0 → K → P → Y → 0` with `K ∈ 𝒞` and `P`
Tor-acyclic against `M`, then every member of `𝒞` is Tor-acyclic against `M`. -/
theorem torAcyclic_of_acyclicCovers (𝒞 : ModuleCat.{0} B → Prop)
    (hcov : ∀ Y, 𝒞 Y → ∃ S : ShortComplex (ModuleCat.{0} B), S.ShortExact ∧ 𝒞 S.X₁ ∧
      TorAcyclic.{w} (k := k) M S.X₂ ∧ Nonempty (S.X₃ ≅ Y))
    (Y : ModuleCat.{0} B) (hY : 𝒞 Y) : TorAcyclic.{w} (k := k) M Y := by
  -- Nonpositive degrees, by induction on `m` over the whole class.
  have key : ∀ m : ℕ, ∀ Y, 𝒞 Y → IsZero ((homologyFunctor (A := k) k (-(m : ℤ))).obj
      ((derivedTensor.{w} k B M).obj (Q.obj ((degreeZeroModuleFunctor B).obj Y)))) := by
    intro m
    induction m with
    | zero =>
      intro Y hY
      obtain ⟨S, hS, hK, hP, ⟨i⟩⟩ := hcov Y hY
      obtain ⟨δ, hT⟩ := exists_distinguished_of_shortExact
        (S.map (degreeZeroModuleFunctor B)) (degreeZeroModuleFunctor_shortExact _ hS)
      let T := (derivedTensor.{w} k B M).mapTriangle.obj
        (Triangle.mk (Q.map (S.map (degreeZeroModuleFunctor B)).f)
          (Q.map (S.map (degreeZeroModuleFunctor B)).g) δ)
      have hT' : T ∈ distTriang _ := (derivedTensor.{w} k B M).map_distinguished _ hT
      refine IsZero.of_iso ?_ ((homologyFunctor (A := k) k _).mapIso
        ((derivedTensor.{w} k B M).mapIso (Q.mapIso ((degreeZeroModuleFunctor B).mapIso i))).symm)
      obtain ⟨e⟩ := nonempty_linearEquiv_homology_obj₃_of_isZero_obj₂ T hT' hP 0
      have hz := isZero_derivedTensorHomology_module_of_pos.{w} (k := k) M S.X₁
        (n := 0 + 1) (by norm_num)
      have : Subsingleton ((homologyFunctor (A := k) k _).obj T.obj₁) :=
        ModuleCat.isZero_iff_subsingleton.mp hz
      exact ModuleCat.isZero_iff_subsingleton.mpr e.toEquiv.subsingleton
    | succ m ih =>
      intro Y hY
      obtain ⟨S, hS, hK, hP, ⟨i⟩⟩ := hcov Y hY
      obtain ⟨δ, hT⟩ := exists_distinguished_of_shortExact
        (S.map (degreeZeroModuleFunctor B)) (degreeZeroModuleFunctor_shortExact _ hS)
      let T := (derivedTensor.{w} k B M).mapTriangle.obj
        (Triangle.mk (Q.map (S.map (degreeZeroModuleFunctor B)).f)
          (Q.map (S.map (degreeZeroModuleFunctor B)).g) δ)
      have hT' : T ∈ distTriang _ := (derivedTensor.{w} k B M).map_distinguished _ hT
      obtain ⟨e⟩ := nonempty_linearEquiv_homology_obj₃_of_isZero_obj₂ T hT' hP
        (-((m + 1 : ℕ) : ℤ))
      have h1 : -((m + 1 : ℕ) : ℤ) + 1 = -(m : ℤ) := by push_cast; ring
      rw [h1] at e
      have hz := ih S.X₁ hK
      refine IsZero.of_iso ?_ ((homologyFunctor (A := k) k _).mapIso
        ((derivedTensor.{w} k B M).mapIso (Q.mapIso ((degreeZeroModuleFunctor B).mapIso i))).symm)
      have : Subsingleton ((homologyFunctor (A := k) k _).obj T.obj₁) :=
        ModuleCat.isZero_iff_subsingleton.mp hz
      exact ModuleCat.isZero_iff_subsingleton.mpr e.toEquiv.subsingleton
  intro n
  rcases lt_or_ge 0 n with hn | hn
  · exact isZero_derivedTensorHomology_module_of_pos M Y hn
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = -(m : ℤ) := ⟨(-n).toNat, by omega⟩
    exact key m Y hY

noncomputable local instance acyclicCoverShiftSequence :
    (homologyFunctor (A := k) k 0).ShiftSequence ℤ := by
  letI : (DG.HomotopyCategory.homologyFunctor.{0} k k 0).ShiftSequence ℤ := by
    change (DG.HomotopyCategory.forget.{0} k k ⋙
      _root_.HomotopyCategory.homologyFunctor (ModuleCat.{0} k) (ComplexShape.up ℤ)
        0).ShiftSequence ℤ
    infer_instance
  exact Functor.ShiftSequence.induced (homologyFunctorFactorsh k 0) ℤ
    (homologyFunctor k) (homologyFunctorFactorsh k)

/-- In a distinguished triangle with `H⁻¹(obj₂) = 0` and `H⁰(obj₁) → H⁰(obj₂)` mono,
`H⁻¹(obj₃) = 0`. -/
theorem isZero_homology_neg_one_obj₃ (T : Triangle (DerivedCategory.{w, 0} k))
    (hT : T ∈ distTriang _) (h₂ : IsZero ((homologyFunctor (A := k) k (-1)).obj T.obj₂))
    (h₀ : Mono ((homologyFunctor (A := k) k 0).map T.mor₁)) :
    IsZero ((homologyFunctor (A := k) k (-1)).obj T.obj₃) := by
  let F := homologyFunctor (A := k) k 0
  have e (j : ℤ) : F.shift j = homologyFunctor k j := rfl
  rw [← e]
  apply (F.homologySequence_exact₃ T hT (-1) 0 (by norm_num)).isZero_X₂
  · change (F.shift (-1)).map T.mor₂ = 0
    rw [e]
    exact h₂.eq_of_src _ _
  · apply (F.homologySequence_mono_shift_map_mor₁_iff T hT (-1) 0 (by norm_num)).1
    exact h₀

/-- **Tor concentrated in degree zero from covers** (the diagonal dimension shift in
B. Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.22): if every member `Y` of a class
`𝒞` has a short exact sequence `0 → K → P → Y → 0` with `K ∈ 𝒞`, `P` without higher Tor against
`M`, and `Tor₀(M, K) → Tor₀(M, P)` injective, then no member of `𝒞` has higher Tor against
`M`. -/
theorem isZero_derivedTensorHomology_of_concentratedCovers (𝒞 : ModuleCat.{0} B → Prop)
    (hcov : ∀ Y, 𝒞 Y → ∃ S : ShortComplex (ModuleCat.{0} B), S.ShortExact ∧ 𝒞 S.X₁ ∧
      (∀ n : ℤ, n ≠ 0 → IsZero ((homologyFunctor (A := k) k n).obj
        ((derivedTensor.{w} k B M).obj (Q.obj ((degreeZeroModuleFunctor B).obj S.X₂))))) ∧
      Mono ((homologyFunctor (A := k) k 0).map ((derivedTensor.{w} k B M).map
        (Q.map ((degreeZeroModuleFunctor B).map S.f)))) ∧ Nonempty (S.X₃ ≅ Y))
    (Y : ModuleCat.{0} B) (hY : 𝒞 Y) (n : ℤ) (hn : n ≠ 0) :
    IsZero ((homologyFunctor (A := k) k n).obj
      ((derivedTensor.{w} k B M).obj (Q.obj ((degreeZeroModuleFunctor B).obj Y)))) := by
  have key : ∀ m : ℕ, ∀ Y, 𝒞 Y → IsZero ((homologyFunctor (A := k) k (-((m + 1 : ℕ) : ℤ))).obj
      ((derivedTensor.{w} k B M).obj (Q.obj ((degreeZeroModuleFunctor B).obj Y)))) := by
    intro m
    induction m with
    | zero =>
      intro Y hY
      obtain ⟨S, hS, hK, hP, hmono, ⟨i⟩⟩ := hcov Y hY
      obtain ⟨δ, hT⟩ := exists_distinguished_of_shortExact
        (S.map (degreeZeroModuleFunctor B)) (degreeZeroModuleFunctor_shortExact _ hS)
      let T := (derivedTensor.{w} k B M).mapTriangle.obj
        (Triangle.mk (Q.map (S.map (degreeZeroModuleFunctor B)).f)
          (Q.map (S.map (degreeZeroModuleFunctor B)).g) δ)
      have hT' : T ∈ distTriang _ := (derivedTensor.{w} k B M).map_distinguished _ hT
      refine IsZero.of_iso ?_ ((homologyFunctor (A := k) k _).mapIso
        ((derivedTensor.{w} k B M).mapIso (Q.mapIso ((degreeZeroModuleFunctor B).mapIso i))).symm)
      exact isZero_homology_neg_one_obj₃ T hT' (hP (-1) (by norm_num)) hmono
    | succ m ih =>
      intro Y hY
      obtain ⟨S, hS, hK, hP, -, ⟨i⟩⟩ := hcov Y hY
      obtain ⟨δ, hT⟩ := exists_distinguished_of_shortExact
        (S.map (degreeZeroModuleFunctor B)) (degreeZeroModuleFunctor_shortExact _ hS)
      let T := (derivedTensor.{w} k B M).mapTriangle.obj
        (Triangle.mk (Q.map (S.map (degreeZeroModuleFunctor B)).f)
          (Q.map (S.map (degreeZeroModuleFunctor B)).g) δ)
      have hT' : T ∈ distTriang _ := (derivedTensor.{w} k B M).map_distinguished _ hT
      let j : ℤ := -((m + 1 + 1 : ℕ) : ℤ)
      let G := homologyFunctor (A := k) k 0
      have es (j : ℤ) : G.shift j = homologyFunctor k j := rfl
      -- The connecting map `Hʲ(obj₃) → Hʲ⁺¹(obj₁)` is mono since `Hʲ(obj₂) = 0`.
      have hmono : Mono (G.homologySequenceδ T j (j + 1) rfl) :=
        (G.homologySequence_exact₃ T hT' j (j + 1) rfl).mono_g
          (((es j).symm ▸ hP j (by omega) : IsZero ((G.shift j).obj T.obj₂)).eq_of_src _ _)
      have h1 : j + 1 = -((m + 1 : ℕ) : ℤ) := by simp only [j]; push_cast; ring
      have hz : IsZero ((G.shift (j + 1)).obj T.obj₁) := by
        rw [es, h1]; exact ih S.X₁ hK
      refine IsZero.of_iso ?_ ((homologyFunctor (A := k) k _).mapIso
        ((derivedTensor.{w} k B M).mapIso (Q.mapIso ((degreeZeroModuleFunctor B).mapIso i))).symm)
      rw [← es]
      exact IsZero.of_mono (G.homologySequenceδ T j (j + 1) rfl) hz
  rcases lt_or_gt_of_ne hn with hn | hn
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = -((m + 1 : ℕ) : ℤ) := ⟨(-n).toNat - 1, by omega⟩
    exact key m Y hY
  · exact isZero_derivedTensorHomology_module_of_pos M Y hn

end Derived

end Categorification

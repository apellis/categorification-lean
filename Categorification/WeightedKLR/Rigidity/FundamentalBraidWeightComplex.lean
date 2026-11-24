/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.FundamentalBraidHomologyWeight
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
/-! # The resolution-degree and physical-weight pieces of the fundamental positive braid

Webster, arXiv:1309.3796v2, Proposition 7.11. Both mixed crossings in the
tensored resolution act homogeneously between the translated loading cuts. -/

noncomputable section
namespace Categorification.Stendhal.FundamentalCorner
open KLR KLRAlgebra BraidedStendhalAlgebra QuantumGroup CategoryTheory DirectSum
local notation "ν" => ({()} : Multiset Unit)
local notation "μ" => stendhalWeight 2 ν
local notation "C" => CartanDatum.ofGraph (⊥ : SimpleGraph Unit)
local notation "Cut" s:arg => violCorner ℚ Q wt ν s [1,0]
local notation "S" => fundamentalBraidCutComplex
private abbrev D := stendhalGradingDatum wt fundamentalBraidParameters.gradingDatum (UDot.di C)
  (fun i => (fundamentalBraidParameters.gradingDatum_degX i).trans (UDot.two_mul_di C i).symm)
private abbrev V := violAuxiliaryGrade («ν» := ν) D
variable {H : Type*} [AddCommGroup H] [Module ℂ H] [Module.Finite ℂ H]
  (P : Matrix.Realization (UDot.A C) ℂ H)
local notation "G" s:arg => figureFiveCutGrade (Λ := wt) C fundamentalBraidParameters
  (weightPairing C P) (fun _ => braidFundamentalWeight P) s 1 0
private theorem cross_weight {s t : Seq μ} (f : Cut s →ₗ[ℚ] Cut t)
    (hf : ∀ z, (f z).val = braidProject (ψ 1) * z.val)
    (hd : D.dψ 1 s = 1) (a : ℂ) :
    Graded.PreservesGrading (Graded.shift (G s) (a + 1)) (Graded.shift (G t) a) f := by
  intro w z hz
  let d := fun n : ℤ => (n : ℂ) + (2 - weightPairing C P (braidFundamentalWeight P) (braidFundamentalWeight P))
  change z ∈ Function.extend d (violCornerAuxiliaryGrade (Λ := wt) C fundamentalBraidParameters s [1,0]) ⊥ (w - (a + 1)) at hz
  change f z ∈ Function.extend d (violCornerAuxiliaryGrade (Λ := wt) C fundamentalBraidParameters t [1,0]) ⊥ (w - a)
  by_cases hw : ∃ n, d n = w - (a + 1)
  · obtain ⟨n,hn⟩ := hw
    have hdi : Function.Injective d := fun _ _ h => Int.cast_injective (add_right_cancel h)
    have hm : d (1 + n) = w - a := by dsimp [d] at hn ⊢; rw [Int.cast_add, Int.cast_one]; linear_combination hn
    rw [← hn,hdi.extend_apply] at hz
    rw [← hm,hdi.extend_apply]
    have hp := D.ψ_mul_e_mem_grade' 1 s
    rw [hd] at hp
    have hc : braidProject (ψ 1 * e s) ∈ V 1 := Graded.mem_map_of_mem _ (violMk ℚ Q wt ν).toLinearMap
      (Graded.mem_map_of_mem _ (ofKLR ℚ Q wt ν).toLinearMap hp)
    have hl := (mem_violCorner_iff.mp z.property).1
    change braidProject (e s) * z.val = z.val at hl
    change (f z).val ∈ V (1 + n)
    rw [hf,← hl,← mul_assoc,← map_mul]
    exact SetLike.GradedMul.mul_mem hc (show z.val ∈ V n from hz)
  · rw [Function.extend_apply' _ _ _ hw] at hz
    rw [(Submodule.mem_bot ℚ).mp hz,map_zero]
    exact zero_mem _

private theorem d_middle : D.dψ 1 middle = 1 := by
  change UDot.di C () * (wt 1 () : ℤ) = 1
  rw [show UDot.di C () = 1 from rfl]
  simp [wt]

private theorem d_terminal : D.dψ 1 terminal = 1 := by
  change UDot.di C () * (wt 1 () : ℤ) = 1
  rw [show UDot.di C () = 1 from rfl]
  simp [wt]

local notation "W₂" => Graded.shift (G middle) 2
local notation "W₁" => Graded.shift (G terminal) 1
local notation "W₀" => Graded.shift (G middle) 0

/-- Both consecutive mixed crossings preserve total physical weight after the
source projective shifts two, one, and zero. -/
theorem fundamentalBraidCutComplex_preservesWeight :
    Graded.PreservesGrading W₂ W₁ (S).f.hom ∧ Graded.PreservesGrading W₁ W₀ (S).g.hom := by
  constructor
  · have h := cross_weight P (s := middle) (t := terminal) (S).f.hom (fun _ => rfl) d_middle 1
    rw [show (1 : ℂ) + 1 = 2 from by norm_num] at h
    exact h
  · have h := cross_weight P (s := terminal) (t := middle) (S).g.hom (fun _ => rfl) d_terminal 0
    rw [zero_add] at h
    exact h

private def weightMap {X Y : Type*} [AddCommGroup X] [Module ℚ X] [AddCommGroup Y] [Module ℚ Y]
    {A : ℂ → Submodule ℚ X} {B : ℂ → Submodule ℚ Y} (f : X →ₗ[ℚ] Y)
    (hf : Graded.PreservesGrading A B f) (w : ℂ) : A w →ₗ[ℚ] B w :=
  (f.domRestrict _).codRestrict _ (fun x => hf x.property)

private def weightF (w : ℂ) : W₂ w →ₗ[ℚ] W₁ w :=
  weightMap (S).f.hom (fundamentalBraidCutComplex_preservesWeight P).1 w

private def weightG (w : ℂ) : W₁ w →ₗ[ℚ] W₀ w :=
  weightMap (S).g.hom (fundamentalBraidCutComplex_preservesWeight P).2 w

/-- The balanced loading-cut complex in total physical weight `w`. -/
def fundamentalBraidWeightComplex (w : ℂ) : ShortComplex (ModuleCat ℚ) where
  X₁ := ModuleCat.of ℚ (W₂ w)
  X₂ := ModuleCat.of ℚ (W₁ w)
  X₃ := ModuleCat.of ℚ (W₀ w)
  f := ModuleCat.ofHom (weightF P w)
  g := ModuleCat.ofHom (weightG P w)
  zero := by
    apply ModuleCat.hom_ext
    exact LinearMap.ext fun (z : W₂ w) => Subtype.ext ((S).moduleCat_zero_apply z.val)

private local instance physicalDecomposition (s : Seq μ) : Decomposition (G s) :=
  (isInternal_figureFiveCutGrade _ _ _ _ _ _ _).chooseDecomposition

private theorem liftWeight {X Y : Type*} [AddCommGroup X] [Module ℚ X] [AddCommGroup Y] [Module ℚ Y]
    {A : ℂ → Submodule ℚ X} {B : ℂ → Submodule ℚ Y} [Decomposition A] [Decomposition B]
    {f : X →ₗ[ℚ] Y} (hf : Graded.PreservesGrading A B f) {w : ℂ} {z : Y} (hz : z ∈ B w)
    {y : X} (hy : f y = z) : ∃ m : A w, f m.val = z := by
  classical
  refine ⟨decompose A y w,?_⟩
  rw [← Graded.decompose_map hf,hy,decompose_of_mem_same _ hz]

local notation "W" w:arg => fundamentalBraidWeightComplex P w

/-- An ordinary crossing boundary of specified physical weight has a preimage
under the crossing at that same physical weight. -/
theorem fundamentalBraidWeightComplex_reflectBoundary {w : ℂ} (z : (W w).X₂)
    (h : ∃ y : (S).X₁, (S).f y = z.val) : ∃ x : (W w).X₁, (W w).f x = z := by
  obtain ⟨y,hy⟩ := h
  obtain ⟨m,hm⟩ := liftWeight (fundamentalBraidCutComplex_preservesWeight P).1 z.property hy
  exact ⟨m,Subtype.ext hm⟩

/-- Each physical weight has zero homology in the two end resolution degrees. -/
theorem fundamentalBraidWeightComplex_ends (w : ℂ) :
    Function.Injective (W w).f ∧ Function.Surjective (W w).g := by
  constructor
  · intro x y h
    exact Subtype.ext (fundamentalBraidCutComplex_ends.1 (congrArg Subtype.val h))
  · intro z
    obtain ⟨y,hy⟩ := fundamentalBraidCutComplex_ends.2 z.val
    obtain ⟨m,hm⟩ := liftWeight (fundamentalBraidCutComplex_preservesWeight P).2 z.property hy
    exact ⟨m,Subtype.ext hm⟩

/-- The fundamental braid complex is exact in every total physical weight other
than three halves. Boundaries have preimages in the specified weight. -/
theorem fundamentalBraidWeightComplex_exact {w : ℂ} (hw : w ≠ 3 / 2) : (W w).Exact := by
  apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
  intro z
  constructor
  · intro hz
    have hc : (S).g z.val = 0 := congrArg Subtype.val hz
    have hb : ∃ y, (S).f y = z.val := by
      by_contra h
      exact hw ((fundamentalBraidHomology_weight_iff P w).mp ⟨z.val,z.property,hc,h⟩)
    exact fundamentalBraidWeightComplex_reflectBoundary P z hb
  · rintro ⟨y,rfl⟩
    exact (W w).moduleCat_zero_apply _

private theorem cycle_grade :
    fundamentalBraidCycle ∈ W₁ (3 / 2) := by
  have he : fundamentalBraidCycle = fundamentalBraidMiddleClass := by
    apply Subtype.ext
    simp [fundamentalBraidCycle_val,fundamentalBraidMiddleClass,ψw]
  rw [he]
  exact (fundamentalBraidMiddleClass_resolutionWeight P _).mpr rfl

/-- In the exceptional physical weight the degree-one homology is a rational
line generated by the terminal-to-crossed-middle diagram. -/
def fundamentalBraidWeightComplex_homologyIso :
    (W (3 / 2)).homology ≅ ModuleCat.of ℚ ℚ := by
  let v : (W (3 / 2)).X₂ := ⟨fundamentalBraidCycle,cycle_grade P⟩
  apply scalarHomologyIsoOfSpanningCycle _ v (Subtype.ext fundamentalBraidCycle_closed)
  · intro a m hm
    have hc : (S).f m.val = a • fundamentalBraidCycle := congrArg Subtype.val hm
    have h := (fundamentalBraidCycle_boundary_iff _ ((S).moduleCat_zero_apply m.val)).mp ⟨m.val,rfl⟩
    rw [hc] at h
    change (a • fundamentalBraidCycle.val) * braidProject (e crossedMiddle) = 0 at h
    rw [smul_mul_assoc,fundamentalBraidCycle_supported] at h
    exact (smul_eq_zero.mp h).resolve_right fundamentalBraidCycle_ne_zero
  · intro z hz
    have hc : (S).g z.val = 0 := congrArg Subtype.val hz
    obtain ⟨a,y,hy⟩ := fundamentalBraidCycle_mod_boundaries z.val hc
    have hw : a • fundamentalBraidCycle - z.val ∈ W₁ (3 / 2) :=
      (W₁ (3 / 2)).sub_mem ((W₁ (3 / 2)).smul_mem a (cycle_grade P)) z.property
    obtain ⟨m,hm⟩ := liftWeight (fundamentalBraidCutComplex_preservesWeight P).1 hw hy
    exact ⟨a,m,Subtype.ext hm⟩

end Categorification.Stendhal.FundamentalCorner

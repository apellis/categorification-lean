/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Loadings.Tree
import Categorification.WeightedKLR.LocalSimple
import Categorification.WeightedKLR.Mackey.MiddleCorner
import Categorification.WeightedKLR.Induction.Restriction
import Categorification.WeightedKLR.RedStrands.Reduced
import Categorification.KLR.Cor319
import Mathlib.LinearAlgebra.Matrix.Module

/-!
# Simple modules for the zero weighting

Supporting the weighted analogue of Khovanov–Lauda I, arXiv:0803.4121v2,
§3.2, Corollary 3.19, needed for Webster, arXiv:1209.2463v4, §2.4,
Theorem 2.19, roadmap A. At zero weighting, each chamber has an evenly spaced
representative. Matrix amplification realizes the ordinary KLR module on the
family of chamber components without choosing a Morita equivalence.
-/

noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace Categorification

open scoped Matrix.Module

/-- Matrix amplification preserves simplicity of modules. This is the module
argument used for the zero-weight case of Webster Theorem 2.19, roadmap A. -/
theorem isSimpleModule_matrix {R M ι : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [IsSimpleModule R M] [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    IsSimpleModule (Matrix ι ι R) (ι → M) := by
  classical
  have := IsSimpleModule.nontrivial R M
  refine isSimpleModule_iff_toSpanSingleton_surjective.2 ⟨inferInstance, ?_⟩
  intro v hv w
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by simpa [funext_iff] using hv
  choose a ha using fun i => IsSimpleModule.toSpanSingleton_surjective R hj (w i)
  refine ⟨fun i l => if l = j then a i else 0, ?_⟩
  ext i
  change (∑ l, (if l = j then a i else 0) • v l) = w i
  have hai : a i • v j = w i := ha i
  simpa only [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    using hai

namespace WeightedKLR

open GalleryAlgebra MvPolynomial

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [Field k] {Γ : WeightedGraph I 𝕜 k}
  {ν : Multiset I}

namespace GalleryAlgebra

private theorem spacedEntry_mem_corner (a : SpacedAlgebra k Γ ν) (i j : KLR.Seq ν) :
    a.1 i j ∈ Subsemigroup.corner (rankIdem k Γ ν.toFinsupp) := by
  apply cornerSpace_mem_corner (KLR.Seq.spacedChamber Γ i).toFull_isRankOrdered
    (KLR.Seq.spacedChamber Γ j).toFull_isRankOrdered
    (x := ⟨a.1 i j, ?_⟩)
  rw [mem_cornerSpace_iff, SpacedAlgebra.e_mul, SpacedAlgebra.mul_e]

private def spacedEntry (a : SpacedAlgebra k Γ ν) (i j : KLR.Seq ν) :
    WeightedKLRAlgebra k Γ ν.toFinsupp := ⟨a.1 i j, spacedEntry_mem_corner a i j⟩

/-- The evenly spaced loading algebra as a matrix corner over Webster's algebra. -/
def spacedMatrixHom : SpacedAlgebra k Γ ν →ₙ+*
    Matrix (KLR.Seq ν) (KLR.Seq ν) (WeightedKLRAlgebra k Γ ν.toFinsupp) where
  toFun a i j := spacedEntry a i j
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' a b := by
    funext i j
    apply Subtype.ext
    change (∑ l, a.1 i l * b.1 l j) =
      (∑ l, spacedEntry a i l * spacedEntry b l j).1
    exact (map_sum (IsIdempotentElem.cornerVal (R := k)
      (isIdempotentElem_rankIdem (k := k) (Γ := Γ) (ν := ν.toFinsupp)))
        (fun l => spacedEntry a i l * spacedEntry b l j) Finset.univ).symm

theorem spacedMatrixHom_one :
    (spacedMatrixHom (1 : SpacedAlgebra k Γ ν)) = Matrix.diagonal
      (fun i : KLR.Seq ν => rankE k (KLR.Seq.spacedChamber Γ i).toFull_isRankOrdered) := by
  funext i j
  apply Subtype.ext
  change spacedIdem k Γ ν i j = _
  by_cases h : i = j
  · subst h
    simp only [spacedIdem, Matrix.diagonal_apply_eq]
    rfl
  · simp only [spacedIdem, Matrix.diagonal_apply_ne _ h]
    rfl

/-- Sandwiching an arbitrary matrix over Webster's algebra into the evenly
spaced loading corner. -/
def spacedSandwich (a : Matrix (KLR.Seq ν) (KLR.Seq ν)
    (WeightedKLRAlgebra k Γ ν.toFinsupp)) : SpacedAlgebra k Γ ν :=
  ⟨spacedIdem k Γ ν * Matrix.of (fun i j => (a i j).1) * spacedIdem k Γ ν, _, rfl⟩

theorem spacedMatrixHom_spacedSandwich (a : Matrix (KLR.Seq ν) (KLR.Seq ν)
    (WeightedKLRAlgebra k Γ ν.toFinsupp)) :
    spacedMatrixHom (spacedSandwich a) = spacedMatrixHom (1 : SpacedAlgebra k Γ ν) * a *
      spacedMatrixHom (1 : SpacedAlgebra k Γ ν) := by
  rw [spacedMatrixHom_one]
  funext i j
  apply Subtype.ext
  change (spacedIdem k Γ ν * Matrix.of (fun i j => (a i j).1) * spacedIdem k Γ ν) i j =
    ((Matrix.diagonal (fun i : KLR.Seq ν =>
      rankE k (KLR.Seq.spacedChamber Γ i).toFull_isRankOrdered) * a *
        Matrix.diagonal (fun i : KLR.Seq ν =>
          rankE k (KLR.Seq.spacedChamber Γ i).toFull_isRankOrdered)) i j).1
  simp only [spacedIdem, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rfl

end GalleryAlgebra

open InductionAlong

variable (hS : Γ.Standing) (hD : Γ.Dagger) (hE : ∀ e, Γ.head e ≠ Γ.tail e)
  (hl : ∀ i, Γ.loop i = none)

/-- The ordinary KLR algebra acts on the matrix family of weighted chamber components. -/
def ordinaryKLRMatrixHom : KLR.KLRAlgebra k Γ.klrQ ν →ₙ+*
    Matrix (KLR.Seq ν) (KLR.Seq ν) (WeightedKLRAlgebra k Γ ν.toFinsupp) :=
  spacedMatrixHom.comp (spacedEquiv hS hD hE hl).toAlgHom.toRingHom.toNonUnitalRingHom

theorem ordinaryKLRMatrixHom_one :
    ordinaryKLRMatrixHom hS hD hE hl (1 : KLR.KLRAlgebra k Γ.klrQ ν) =
      Matrix.diagonal (fun i : KLR.Seq ν =>
        rankE k (KLR.Seq.spacedChamber Γ i).toFull_isRankOrdered) := by
  change spacedMatrixHom ((spacedEquiv hS hD hE hl) 1) = _
  rw [map_one, spacedMatrixHom_one]

theorem ordinaryKLRMatrixHom_smul (c : k) (a : KLR.KLRAlgebra k Γ.klrQ ν) :
    ordinaryKLRMatrixHom hS hD hE hl (c • a) = c • ordinaryKLRMatrixHom hS hD hE hl a := by
  change spacedMatrixHom ((spacedEquiv hS hD hE hl) (c • a)) = _
  rw [map_smul]
  funext i j
  apply Subtype.ext
  rfl

theorem ordinaryKLRMatrixHom_sandwich (a : Matrix (KLR.Seq ν) (KLR.Seq ν)
    (WeightedKLRAlgebra k Γ ν.toFinsupp)) : ∃ r : KLR.KLRAlgebra k Γ.klrQ ν,
    ordinaryKLRMatrixHom hS hD hE hl r = ordinaryKLRMatrixHom hS hD hE hl 1 * a *
      ordinaryKLRMatrixHom hS hD hE hl 1 := by
  refine ⟨(spacedEquiv hS hD hE hl).symm (spacedSandwich a), ?_⟩
  change spacedMatrixHom ((spacedEquiv hS hD hE hl)
      ((spacedEquiv hS hD hE hl).symm (spacedSandwich a))) =
    spacedMatrixHom ((spacedEquiv hS hD hE hl) 1) * a *
      spacedMatrixHom ((spacedEquiv hS hD hE hl) 1)
  rw [AlgEquiv.apply_symm_apply, map_one, spacedMatrixHom_spacedSandwich]

private theorem rankE_mul_reducedDot_val {C : FullChamber Γ ν.toFinsupp}
    (hC : C.IsRankOrdered) (s : Strand ν.toFinsupp) :
    (rankE k hC * reducedDot k Γ ν.toFinsupp s).1 = e C * poly (X s) := by
  change e C * (rankIdem k Γ ν.toFinsupp * poly (X s) * rankIdem k Γ ν.toFinsupp) = _
  rw [← mul_assoc, ← mul_assoc, e_mul_rankIdem, ite_eq_left hC,
    e_mul_poly, mul_assoc, e_mul_rankIdem, ite_eq_left hC, ← e_mul_poly]

private theorem reducedDot_commute_rankE {C : FullChamber Γ ν.toFinsupp}
    (hC : C.IsRankOrdered) (s : Strand ν.toFinsupp) :
    Commute (reducedDot k Γ ν.toFinsupp s) (rankE k hC) := by
  apply Subtype.ext
  rw [rankE_mul_reducedDot_val]
  change rankIdem k Γ ν.toFinsupp * poly (X s) * rankIdem k Γ ν.toFinsupp * e C = _
  rw [mul_assoc, rankIdem_mul_e, ite_eq_left hC, mul_assoc, ← e_mul_poly, ← mul_assoc,
    rankIdem_mul_e, ite_eq_left hC]

theorem ordinaryKLRMatrixHom_dot (a : Fin ν.card) :
    ordinaryKLRMatrixHom hS hD hE hl (KLR.KLRAlgebra.x a) = Matrix.diagonal
      (fun i : KLR.Seq ν => rankE k (KLR.Seq.spacedChamber Γ i).toFull_isRankOrdered *
        reducedDot k Γ ν.toFinsupp (i.strandAt a)) := by
  change spacedMatrixHom (spacedHom k hS hD hE hl (KLR.KLRAlgebra.x a)) = _
  rw [KLR.KLRAlgebra.x, spacedHom_mk]
  change spacedMatrixHom (spacedFreeHom k Γ ν (FreeAlgebra.ι k (.dot a))) = _
  rw [spacedFreeHom, FreeAlgebra.lift_ι_apply]
  funext i j
  apply Subtype.ext
  change (spacedIdem k Γ ν * genMat k Γ (.dot a) * spacedIdem k Γ ν) i j = _
  simp only [genMat, spacedIdem, Matrix.diagonal_mul_diagonal]
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.diagonal_apply_eq, rankE_mul_reducedDot_val]
    rw [e_mul_poly, mul_assoc, e_mul_e, ite_eq_left rfl, ← e_mul_poly]
  · simp only [Matrix.diagonal_apply_ne _ hij]
    rfl

section Module

variable {M : Type*} [AddCommGroup M] [Module k M]
  [Module (WeightedKLRAlgebra k Γ ν.toFinsupp) M]
  [IsScalarTower k (WeightedKLRAlgebra k Γ ν.toFinsupp) M]
  [IsSimpleModule (WeightedKLRAlgebra k Γ ν.toFinsupp) M]

omit [Module k M] [IsScalarTower k (WeightedKLRAlgebra k Γ ν.toFinsupp) M]
  [IsSimpleModule (WeightedKLRAlgebra k Γ ν.toFinsupp) M] in
theorem ordinaryRestriction_fixed_component
    (v : Res (ordinaryKLRMatrixHom (ν := ν) hS hD hE hl) (KLR.Seq ν → M)) (i : KLR.Seq ν) :
    rankE k (KLR.Seq.spacedChamber Γ i).toFull_isRankOrdered • v.val i = v.val i := by
  have h := congrFun v.prop i
  rw [ordinaryKLRMatrixHom_one] at h
  simpa only [Matrix.Module.smul_apply, Matrix.diagonal_apply, ite_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true] using h

omit [Module k M] [IsScalarTower k (WeightedKLRAlgebra k Γ ν.toFinsupp) M]
  [IsSimpleModule (WeightedKLRAlgebra k Γ ν.toFinsupp) M] in
theorem ordinaryRestriction_dot_component
    (v : Res (ordinaryKLRMatrixHom (ν := ν) hS hD hE hl) (KLR.Seq ν → M))
    (a : Fin ν.card) (i : KLR.Seq ν) :
    ((KLR.KLRAlgebra.x a : KLR.KLRAlgebra k Γ.klrQ ν) • v).val i =
      reducedDot k Γ ν.toFinsupp (i.strandAt a) • v.val i := by
  change (ordinaryKLRMatrixHom hS hD hE hl (KLR.KLRAlgebra.x a) • v.val) i = _
  rw [ordinaryKLRMatrixHom_dot]
  simp only [Matrix.Module.smul_apply, Matrix.diagonal_apply, ite_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← (reducedDot_commute_rankE _ _).eq, mul_smul,
    ordinaryRestriction_fixed_component]

include hS hD hE hl in
omit [Module k M] [IsScalarTower k (WeightedKLRAlgebra k Γ ν.toFinsupp) M] in
theorem exists_fixed_ne_zero_matrix (h0 : ∀ e, Γ.weight e = 0) :
    ∃ v : KLR.Seq ν → M, v ≠ 0 ∧ ordinaryKLRMatrixHom (ν := ν) hS hD hE hl 1 • v = v := by
  classical
  have := IsSimpleModule.nontrivial (WeightedKLRAlgebra k Γ ν.toFinsupp) M
  obtain ⟨v, hv⟩ := exists_ne (0 : M)
  obtain ⟨C, hCv⟩ : ∃ C : RankChamber Γ ν.toFinsupp, rankE k C.2 • v ≠ 0 := by
    by_contra h
    have hz : ∀ C : RankChamber Γ ν.toFinsupp, rankE k C.2 • v = 0 := by simpa using h
    apply hv
    calc
      v = (1 : WeightedKLRAlgebra k Γ ν.toFinsupp) • v := (one_smul _ _).symm
      _ = 0 := by rw [one_eq_sum_rankE, Finset.sum_smul]; simp only [hz, Finset.sum_const_zero]
  obtain ⟨i, hi⟩ := exists_spacedFull_eq h0 C
  have hval : rankE k (KLR.Seq.spacedChamber Γ i).toFull_isRankOrdered = rankE k C.2 :=
    Subtype.ext (congrArg e hi)
  refine ⟨Pi.single i (rankE k C.2 • v), ?_, ?_⟩
  · intro h
    have := congrFun h i
    apply hCv
    simpa only [Pi.single_eq_same, Pi.zero_apply] using this
  · rw [ordinaryKLRMatrixHom_one]
    ext j
    by_cases hj : j = i
    · subst hj
      simp only [Matrix.Module.smul_apply, Matrix.diagonal_apply, ite_smul, zero_smul,
        Finset.sum_ite_eq, Finset.mem_univ, ite_true, Pi.single_eq_same]
      rw [hval, ← mul_smul, rankE_mul_rankE]
    · simp [Matrix.Module.smul_apply, Matrix.diagonal_apply, hj]

include hS hD hE hl in
/-- Scalar endomorphisms for finite-dimensional simple modules with nilpotent
dots at zero weighting. This is the zero-weight intermediate weighted case of
KL I arXiv:0803.4121v2, §3.2, Corollary 3.19, using Webster
arXiv:1209.2463v4, Proposition 2.14 and the zero-weight loading comparison
in the proof of Corollary 2.16. It supports Theorem 2.19, roadmap A;
the zero-weight hypothesis is an extra hypothesis of this intermediate result. -/
theorem exists_eq_smul_of_isSimpleModule_zeroWeight [FiniteDimensional k M]
    (h0 : ∀ e, Γ.weight e = 0)
    (hnil : ∀ s : Strand ν.toFinsupp, KLR.SmulNilpotent (reducedDot k Γ ν.toFinsupp s) M)
    (ψ : M →ₗ[WeightedKLRAlgebra k Γ ν.toFinsupp] M) : ∃ c : k, ∀ m, ψ m = c • m := by
  classical
  let φ := ordinaryKLRMatrixHom (ν := ν) hS hD hE hl
  let N := Res φ (KLR.Seq ν → M)
  have hunit := exists_fixed_ne_zero_matrix (ν := ν) (M := M) hS hD hE hl h0
  have := isSimpleModule_matrix (R := WeightedKLRAlgebra k Γ ν.toFinsupp) (M := M)
    (ι := KLR.Seq ν)
  have : IsSimpleModule (KLR.KLRAlgebra k Γ.klrQ ν) N :=
    Res.isSimpleModule_of_corner_action hunit (fun a => by
      obtain ⟨r, hr⟩ := ordinaryKLRMatrixHom_sandwich hS hD hE hl a
      refine ⟨r, fun v => ?_⟩
      change φ r • v.val = φ 1 • (a • v.val)
      rw [hr, mul_smul, mul_smul, v.prop])
  let : Module k N := Module.compHom N (algebraMap k (KLR.KLRAlgebra k Γ.klrQ ν))
  have : IsScalarTower k (KLR.KLRAlgebra k Γ.klrQ ν) N := IsScalarTower.of_compHom _ _ _
  have hval_smul : ∀ (c : k) (v : N), (c • v).val = c • v.val := by
    intro c v
    change φ (algebraMap k (KLR.KLRAlgebra k Γ.klrQ ν) c) • v.val = c • v.val
    rw [Algebra.algebraMap_eq_smul_one, ordinaryKLRMatrixHom_smul, smul_assoc, v.prop]
  let L : N →ₗ[k] (KLR.Seq ν → M) :=
    { toFun := Res.val
      map_add' := Res.val_add
      map_smul' := hval_smul }
  have : FiniteDimensional k N := FiniteDimensional.of_injective L (fun _ _ h => Res.ext h)
  have hpower : ∀ (n : ℕ) (a : Fin ν.card) (v : N) (i : KLR.Seq ν),
      (((KLR.KLRAlgebra.x a : KLR.KLRAlgebra k Γ.klrQ ν) ^ n) • v).val i =
        (reducedDot k Γ ν.toFinsupp (i.strandAt a)) ^ n • v.val i := by
    intro n
    induction n with
    | zero => intro a v i; simp
    | succ n ih =>
      intro a v i
      rw [pow_succ', mul_smul, ordinaryRestriction_dot_component, ih,
        ← mul_smul, ← pow_succ']
  choose bound hbound using hnil
  let B := Finset.univ.sup bound
  have hnilB : ∀ (s : Strand ν.toFinsupp) (m : M),
      (reducedDot k Γ ν.toFinsupp s) ^ B • m = 0 := by
    intro s m
    have hs : bound s ≤ B := Finset.le_sup (Finset.mem_univ s)
    rw [← Nat.sub_add_cancel hs, pow_add, mul_smul, hbound, smul_zero]
  have hnilN : ∀ a, KLR.SmulNilpotent
      (KLR.KLRAlgebra.x a : KLR.KLRAlgebra k Γ.klrQ ν) N := by
    intro a
    refine ⟨B, fun v => Res.ext (funext fun i => ?_)⟩
    rw [hpower, hnilB]
    rfl
  have hEnd : ∀ f : N →ₗ[KLR.KLRAlgebra k Γ.klrQ ν] N,
      ∃ c : k, ∀ v : N, (f v).val = c • v.val := by
    intro f
    obtain ⟨c, hc⟩ := KLR.KLRAlgebra.exists_eq_smul_of_isSimpleModule
      (Q := Γ.klrQ) (P := Γ.edgeProd) (fun _ _ _ => rfl)
      (fun a b _ => hS.edgeProd_ne_zero a b) hnilN f
    refine ⟨c, fun v => ?_⟩
    rw [hc, hval_smul]
  obtain ⟨c, hc⟩ := Res.exists_eq_smul_of_scalar_endomorphisms hunit hEnd
    (ψ.mapMatrixModule (KLR.Seq ν))
  refine ⟨c, fun m => ?_⟩
  let i : KLR.Seq ν := Classical.choice inferInstance
  have h := congrFun (hc (Pi.single i m)) i
  simpa only [LinearMap.mapMatrixModule_apply, LinearMap.compLeft_apply,
    Function.comp_apply, Pi.single_eq_same, Pi.smul_apply] using h

end Module

include hS hD hE hl in
/-- The finitely supported weight indexing of the zero-weight scalar theorem,
used by the local-chart argument for Webster arXiv:1209.2463v4,
Theorem 2.19, roadmap A. The proof and hypotheses are those of
`exists_eq_smul_of_isSimpleModule_zeroWeight`; only the indexing changes. -/
theorem exists_eq_smul_of_isSimpleModule_zeroWeight_finsupp {ρ : I →₀ ℕ}
    {M : Type*} [AddCommGroup M] [Module k M] [Module (WeightedKLRAlgebra k Γ ρ) M]
    [IsScalarTower k (WeightedKLRAlgebra k Γ ρ) M]
    [IsSimpleModule (WeightedKLRAlgebra k Γ ρ) M] [FiniteDimensional k M]
    (h0 : ∀ e, Γ.weight e = 0)
    (hnil : ∀ s : Strand ρ, KLR.SmulNilpotent (reducedDot k Γ ρ s) M)
    (ψ : M →ₗ[WeightedKLRAlgebra k Γ ρ] M) : ∃ c : k, ∀ m, ψ m = c • m := by
  obtain ⟨μ, rfl⟩ : ∃ μ : Multiset I, μ.toFinsupp = ρ :=
    ⟨ρ.toMultiset, Finsupp.toMultiset_toFinsupp ρ⟩
  exact exists_eq_smul_of_isSimpleModule_zeroWeight hS hD hE hl h0 hnil ψ

end WeightedKLR
end Categorification

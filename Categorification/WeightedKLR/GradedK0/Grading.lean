/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.MiddleGraded
import Categorification.Algebra.Graded.HomogeneousBasis

/-!
# The graded algebra `W_ν` and its graded dimension

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.1 (the grading
of the standing hypothesis) and Theorem 2.8 (the basis theorem). Webster's algebra `W_ν` is the
corner `e A_ν e` of the gallery algebra at the degree-zero idempotent `e = rankIdem`; its grading
`GradingDatum.klrGrade` is the restriction of the grading of `A_ν`.

* `Graded.cornerGrading`, `Graded.cornerGradedAlgebra`: the corner `e A e` of a graded algebra at
  an idempotent of degree zero is a graded algebra, graded by restriction.
* `GradingDatum.instGradedAlgebraKlrGrade`: `W_ν` is a graded algebra, for every grading datum.
* `GalleryAlgebra.hasGdim_grade`, `GalleryAlgebra.hasGdim_klrGrade`: over a field, under
  Webster's hypotheses (the standing hypothesis and `(†)`, no loops of weight `0` with
  non-unit `P`), the graded pieces of `A_ν` and of `W_ν` for the grading of the standing
  hypothesis are finite-dimensional and vanish in sufficiently negative degrees. This is read
  off from the homogeneous basis of Theorem 2.8: dots have degree `2 d_i > 0`.

## Conventions

The grading datum of the standing hypothesis (`WeightedGraph.Standing.gradingDatum`) uses the
doubled normalization: all degrees are twice Webster's.
-/

namespace Categorification.Graded

open DirectSum

variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A] (𝒜 : ℤ → Submodule k A)
  {E : A} (he : IsIdempotentElem E)

/-- The grading of the corner `E A E`, restricted from `A`. -/
noncomputable def cornerGrading : ℤ → Submodule k he.Corner :=
  comap 𝒜 (IsIdempotentElem.cornerVal (R := k) he)

@[simp] theorem mem_cornerGrading {n : ℤ} {x : he.Corner} :
    x ∈ cornerGrading 𝒜 he n ↔ x.1 ∈ 𝒜 n := Iff.rfl

variable [GradedAlgebra 𝒜]

theorem isInternal_cornerGrading (he0 : E ∈ 𝒜 0) : IsInternal (cornerGrading 𝒜 he) := by
  classical
  refine isInternal_comap 𝒜 _ (fun x y h => Subtype.ext h) fun x d => ?_
  obtain ⟨y, hy⟩ := x.2
  refine ⟨⟨_, (decompose 𝒜 y d : A), rfl⟩, ?_⟩
  change E * (decompose 𝒜 y d : A) * E = (decompose 𝒜 x.1 d : A)
  rw [← hy, coe_decompose_mul_of_right_mem_zero 𝒜 he0,
    coe_decompose_mul_of_left_mem_zero 𝒜 he0]

/-- **The corner of a graded algebra at an idempotent of degree zero is a graded algebra**,
graded by restriction. -/
@[instance_reducible] noncomputable def cornerGradedAlgebra (he0 : E ∈ 𝒜 0) :
    GradedAlgebra (cornerGrading 𝒜 he) :=
  { (isInternal_cornerGrading 𝒜 he he0).chooseDecomposition with
    one_mem := he0
    mul_mem := fun _ _ x _ hx hy =>
      (SetLike.GradedMul.mul_mem (A := 𝒜) (show x.1 ∈ 𝒜 _ from hx) hy :) }

section Comap

variable {k M N : Type*} [Field k] [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

/-- A grading pulled back along an injective linear map inherits a graded dimension. -/
theorem HasGdim.comap (ℳ : ℤ → Submodule k M) [HasGdim ℳ] {f : N →ₗ[k] M}
    (hf : Function.Injective f) : HasGdim (Graded.comap ℳ f) where
  finiteDimensional d := FiniteDimensional.of_injective
    ((f.restrict fun _ hx => hx) : Graded.comap ℳ f d →ₗ[k] ℳ d)
    fun x y h => Subtype.ext (hf (congrArg Subtype.val h))
  bddBelow := HasGdim.bddBelow (ℳ := ℳ) |>.mono fun d (hd : Graded.comap ℳ f d ≠ ⊥)
      (h : ℳ d = ⊥) => hd <| by
    rw [eq_bot_iff]
    intro x hx
    have hx' : f x ∈ ℳ d := hx
    rw [h, Submodule.mem_bot] at hx'
    rw [Submodule.mem_bot]
    exact hf (by rw [hx', map_zero])

end Comap

end Categorification.Graded

namespace Categorification.WeightedKLR

open FullChamber GalleryAlgebra _root_.Categorification.Graded

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜]

attribute [local instance] ColPerm.fintype

section Ring

variable {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}

theorem rankIdem_mem_grade (G : GradingDatum Γ) (ν : I →₀ ℕ) :
    rankIdem k Γ ν ∈ G.grade ν 0 :=
  Submodule.sum_mem _ fun C _ => G.e_mem_grade C

theorem GradingDatum.klrGrade_eq_cornerGrading (G : GradingDatum Γ) (ν : I →₀ ℕ) :
    G.klrGrade ν = cornerGrading (G.grade ν) isIdempotentElem_rankIdem := rfl

/-- **`W_ν` is a graded algebra**: the corner of the graded gallery algebra at the degree-zero
idempotent `rankIdem`, for every grading datum. -/
noncomputable instance GradingDatum.instGradedAlgebraKlrGrade (G : GradingDatum Γ)
    (ν : I →₀ ℕ) : GradedAlgebra (G.klrGrade ν) :=
  cornerGradedAlgebra (G.grade ν) isIdempotentElem_rankIdem (rankIdem_mem_grade G ν)

end Ring

/-! ### Graded dimension -/

section Field

variable {k : Type*} [Field k] {Γ : WeightedGraph I 𝕜 k}

/-- For positive weights there are finitely many monomials of each weighted degree. -/
theorem finite_setOf_weight_eq {σ : Type*} [Finite σ] {w : σ → ℤ} (hw : ∀ a, 0 < w a)
    (e : ℤ) : {u : σ →₀ ℕ | Finsupp.weight w u = e}.Finite := by
  have := Fintype.ofFinite σ
  refine ((Set.Finite.pi (t := fun _ : σ => Set.Iic e.toNat) fun _ =>
    Set.finite_Iic _).image Finsupp.equivFunOnFinite.symm).subset ?_
  intro u hu
  refine ⟨u, fun a _ => ?_, by simp⟩
  rw [Set.mem_ofPred_eq, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at hu
  have hle : u a • w a ≤ ∑ b, u b • w b :=
    Finset.single_le_sum (f := fun b => u b • w b)
      (fun b _ => nsmul_nonneg (hw b).le _) (Finset.mem_univ a)
  have h1 : (u a : ℤ) ≤ u a • w a := by
    rw [nsmul_eq_mul]; nlinarith [hw a, (u a).cast_nonneg (α := ℤ)]
  simp only [Set.mem_Iic]
  omega

theorem weight_nonneg_of_nonneg {σ : Type*} [Finite σ] {w : σ → ℤ} (hw : ∀ a, 0 ≤ w a)
    (u : σ →₀ ℕ) : 0 ≤ Finsupp.weight w u := by
  have := Fintype.ofFinite σ
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  exact Finset.sum_nonneg fun b _ => nsmul_nonneg (hw b) _

variable {ν : I →₀ ℕ} (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hS : Γ.Standing)

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem WeightedGraph.Standing.wt_pos (s : Strand ν) : 0 < hS.gradingDatum.wt s := by
  have := hS.choose_spec.1 s.1
  change (0 : ℤ) < 2 * (hS.symm s.1 : ℤ)
  have h : 0 < hS.symm s.1 := this
  omega

namespace GalleryAlgebra

include hD hZ

/-- **`A_ν` has a graded dimension** over a field, for the grading of Webster's standing
hypothesis and under Webster's hypotheses (arXiv:1209.2463v4, §2.1 and Theorem 2.8): its graded
pieces are finite-dimensional and vanish in sufficiently negative degrees. -/
theorem hasGdim_grade : HasGdim (hS.gradingDatum.grade ν) := by
  classical
  obtain ⟨P, hP, -⟩ := exists_span_segGallery (k := k) (ν := ν) hD hZ
  set G := hS.gradingDatum
  let b := basisOfSegments hP hD hZ hS.psymm hS.isRegular_factor hS.isRegular_loopFactor'
  let deg : FullChamber Γ ν × FullChamber Γ ν × ColPerm ν × (Strand ν →₀ ℕ) → ℤ :=
    fun x => G.segDeg P x.1 x.2.1 + Finsupp.weight G.wt x.2.2.2
  have hdeg : ∀ x, b x ∈ G.grade ν (deg x) := fun x =>
    G.basisOfSegments_mem_grade hP hD hZ hS.psymm hS.isRegular_factor
      hS.isRegular_loopFactor' x.1 x.2.1 x.2.2.1 x.2.2.2
  obtain ⟨B, hB⟩ := (Set.finite_range fun p : FullChamber Γ ν × FullChamber Γ ν =>
    G.segDeg P p.1 p.2).bddBelow
  have h := hasGdim_inf_span (G.grade ν) deg hdeg Set.univ (fun d => by
      have hsub : {x | x ∈ Set.univ ∧ deg x = d} ⊆ Set.univ ×ˢ (Set.univ ×ˢ (Set.univ ×ˢ
          ⋃ p : FullChamber Γ ν × FullChamber Γ ν,
            {u | Finsupp.weight G.wt u = d - G.segDeg P p.1 p.2})) := by
        rintro ⟨C, E, g, m⟩ ⟨-, hx⟩
        simp only [Set.mem_prod, Set.mem_univ, Set.mem_iUnion, Set.mem_ofPred_eq, true_and]
        exact ⟨(C, E), by simp only [deg] at hx; dsimp only; omega⟩
      exact (Set.finite_univ.prod (Set.finite_univ.prod (Set.finite_univ.prod
        (Set.finite_iUnion fun _ =>
          finite_setOf_weight_eq (WeightedGraph.Standing.wt_pos hS) _)))).subset hsub)
    ⟨B, by
      rintro _ ⟨x, -, rfl⟩
      have h1 : B ≤ G.segDeg P x.1 x.2.1 := hB ⟨(x.1, x.2.1), rfl⟩
      have h2 : 0 ≤ Finsupp.weight G.wt x.2.2.2 :=
        weight_nonneg_of_nonneg (fun s => (WeightedGraph.Standing.wt_pos hS (ν := ν) s).le) _
      simp only [deg]
      omega⟩
  have hspan : Submodule.span k (b '' Set.univ) = ⊤ := by
    rw [Set.image_univ, b.span_eq]
  simp only [hspan, inf_top_eq] at h
  exact h

/-- **`W_ν` has a graded dimension** over a field, for the grading of Webster's standing
hypothesis and under Webster's hypotheses (arXiv:1209.2463v4, §2.1 and Theorem 2.8). -/
theorem hasGdim_klrGrade : HasGdim (hS.gradingDatum.klrGrade ν) :=
  have := hasGdim_grade (ν := ν) hD hZ hS
  HasGdim.comap _ (fun _ _ h => Subtype.ext h)

end GalleryAlgebra

end Field

end Categorification.WeightedKLR

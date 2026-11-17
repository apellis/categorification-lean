/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.MultiplicityFreeSimple
import Categorification.WeightedKLR.RedStrands.ViolatingComparison
import Categorification.WeightedKLR.Local.StarRelabel

/-!
# Chamber support of a weighted KLR module

For the local-chamber argument toward Webster, arXiv:1209.2463v4, Theorem 2.19,
roadmap A, we use full labelled chambers even though modules are defined over the
rank-ordered corner. A chamber is in the support when some diagram factoring
through it has nonzero action. This definition is invariant under relabelling,
and agrees with nonzero action of the chamber idempotent for rank-ordered chambers.
It avoids extending the module to the full gallery algebra.
-/

noncomputable section

namespace Categorification.WeightedKLR.GalleryAlgebra

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [Field k] {Γ : WeightedGraph I 𝕜 k}
  {ν : I →₀ ℕ} (M : Type*) [AddCommGroup M] [Module (WeightedKLRAlgebra k Γ ν) M]

/-- A full chamber is supported if a diagram through it acts nontrivially. -/
def chamberSupport : Set (FullChamber Γ ν) :=
  {C | ∃ x y : GalleryAlgebra k Γ ν, ∃ m : M,
    colourSymCornerProjection (x * e C * y) • m ≠ 0}

variable {M}

theorem sandwich_smul_eq_zero_of_not_mem_chamberSupport {C : FullChamber Γ ν}
    (hC : C ∉ chamberSupport M) (x y : GalleryAlgebra k Γ ν) (m : M) :
    colourSymCornerProjection (x * e C * y) • m = 0 := by
  by_contra h
  exact hC ⟨x, y, m, h⟩

theorem mem_chamberSupport_smul_iff (g : ColPerm ν) (C : FullChamber Γ ν) :
    g • C ∈ chamberSupport M ↔ C ∈ chamberSupport M := by
  have hforward : ∀ (g : ColPerm ν) (C : FullChamber Γ ν),
      C ∈ chamberSupport M → g • C ∈ chamberSupport M := by
    intro g C hC
    obtain ⟨x, y, m, hm⟩ := hC
    refine ⟨x * r g⁻¹ (g • C), r g C * y, m, ?_⟩
    have he := e_eq_r_mul_e_mul_r (k := k) g C
    have he' : (x * r g⁻¹ (g • C)) * e (g • C) * (r g C * y) = x * e C * y := by
      rw [he]
      simp only [mul_assoc]
    rwa [he']
  constructor
  · intro h
    simpa only [inv_smul_smul] using hforward g⁻¹ (g • C) h
  · exact hforward g C

theorem colourSymCornerProjection_rankE {C : FullChamber Γ ν} (hC : C.IsRankOrdered) :
    colourSymCornerProjection (e C : GalleryAlgebra k Γ ν) = rankE k hC := by
  apply Subtype.ext
  change rankIdem k Γ ν * e C * rankIdem k Γ ν = e C
  rw [rankIdem_mul_e, ite_eq_left hC, e_mul_rankIdem, ite_eq_left hC]

theorem colourSymCornerProjection_coe (a : WeightedKLRAlgebra k Γ ν) :
    colourSymCornerProjection a.1 = a := by
  apply Subtype.ext
  have ha := (Subsemigroup.mem_corner_iff isIdempotentElem_rankIdem).1 a.2
  change rankIdem k Γ ν * a.1 * rankIdem k Γ ν = a.1
  rw [ha.1, ha.2]

theorem colourSymCornerProjection_sandwich_rankE {C : FullChamber Γ ν}
    (hC : C.IsRankOrdered) (x y : GalleryAlgebra k Γ ν) :
    colourSymCornerProjection (x * e C * y) =
      colourSymCornerProjection x * rankE k hC * colourSymCornerProjection y := by
  apply Subtype.ext
  change rankIdem k Γ ν * (x * e C * y) * rankIdem k Γ ν =
    (rankIdem k Γ ν * x * rankIdem k Γ ν) * e C *
      (rankIdem k Γ ν * y * rankIdem k Γ ν)
  symm
  calc
    _ = rankIdem k Γ ν * x * (rankIdem k Γ ν * e C * rankIdem k Γ ν) * y *
        rankIdem k Γ ν := by simp only [mul_assoc]
    _ = _ := by
      rw [rankIdem_mul_e, ite_eq_left hC, e_mul_rankIdem, ite_eq_left hC]
      simp only [mul_assoc]

/-- A factorization through an unsupported chamber kills the module, including
when the intermediate chamber is not rank-ordered. -/
theorem smul_eq_zero_of_factor_unsupported {C : FullChamber Γ ν}
    (hC : C ∉ chamberSupport M) (a : WeightedKLRAlgebra k Γ ν)
    (x y : GalleryAlgebra k Γ ν) (ha : a.1 = x * e C * y) (m : M) : a • m = 0 := by
  have hp : colourSymCornerProjection (x * e C * y) = a := by
    rw [← ha]
    exact colourSymCornerProjection_coe a
  rw [← hp]
  exact sandwich_smul_eq_zero_of_not_mem_chamberSupport hC x y m

theorem mem_chamberSupport_of_rankE_smul_ne_zero {C : FullChamber Γ ν}
    (hC : C.IsRankOrdered) {m : M} (hm : rankE k hC • m ≠ 0) :
    C ∈ chamberSupport M := by
  refine ⟨1, 1, m, ?_⟩
  simpa only [one_mul, mul_one, colourSymCornerProjection_rankE hC] using hm

theorem rankE_smul_eq_zero_of_not_mem_chamberSupport {C : FullChamber Γ ν}
    (hC : C.IsRankOrdered) (h : C ∉ chamberSupport M) (m : M) : rankE k hC • m = 0 := by
  by_contra hm
  exact h (mem_chamberSupport_of_rankE_smul_ne_zero hC hm)

theorem mem_chamberSupport_rank_iff {C : FullChamber Γ ν} (hC : C.IsRankOrdered) :
    C ∈ chamberSupport M ↔ ∃ m : M, rankE k hC • m ≠ 0 := by
  constructor
  · rintro ⟨x, y, m, hm⟩
    by_contra h
    have hz : ∀ m : M, rankE k hC • m = 0 := by simpa using h
    apply hm
    rw [colourSymCornerProjection_sandwich_rankE hC, mul_smul, mul_smul, hz, smul_zero]
  · rintro ⟨m, hm⟩
    exact mem_chamberSupport_of_rankE_smul_ne_zero hC hm

theorem chamberSupport_nonempty [Nontrivial M] : (chamberSupport M (Γ := Γ) (ν := ν)).Nonempty := by
  classical
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  obtain ⟨C, hC⟩ : ∃ C : RankChamber Γ ν, rankE k C.2 • m ≠ 0 := by
    by_contra h
    have hz : ∀ C : RankChamber Γ ν, rankE k C.2 • m = 0 := by simpa using h
    apply hm
    calc
      m = (1 : WeightedKLRAlgebra k Γ ν) • m := (one_smul _ _).symm
      _ = 0 := by rw [one_eq_sum_rankE, Finset.sum_smul]; simp only [hz, Finset.sum_const_zero]
  exact ⟨C.1, mem_chamberSupport_of_rankE_smul_ne_zero C.2 hC⟩

/-- A supported rank-ordered chamber has a point of minimum squared norm among
all closed supported chambers. -/
theorem exists_chamberSupport_minimum [Nontrivial M] :
    ∃ p : Strand ν → 𝕜, ∃ C : FullChamber Γ ν, C ∈ chamberSupport M ∧
      C.IsRankOrdered ∧ C.Incident p ∧
      ∀ D : FullChamber Γ ν, D ∈ chamberSupport M → ∀ x : Strand ν → 𝕜, D.Incident x →
        Geometry.squaredNorm p ≤ Geometry.squaredNorm x := by
  exact exists_rankOrdered_support_squaredNorm_minimum (chamberSupport M (Γ := Γ) (ν := ν))
    chamberSupport_nonempty (fun g C hC => (mem_chamberSupport_smul_iff g C).2 hC)

/-- Insert the chamber idempotent at a prefix of a gallery word. -/
theorem galList_factor_prefix (C : FullChamber Γ ν) (w : List (Hyp Γ ν)) (j : ℕ) :
    galList k C w = galList k (C.flips (w.take j)) (w.drop j) *
      e (C.flips (w.take j)) * galList k C (w.take j) := by
  rw [galList_mul_e, ← galList_append, List.take_append_drop]

/-- An unsupported prefix annihilates every weighted diagram containing that gallery. -/
theorem smul_eq_zero_of_galList_prefix_unsupported (C : FullChamber Γ ν)
    (w : List (Hyp Γ ν)) (j : ℕ) (hC : C.flips (w.take j) ∉ chamberSupport M)
    (a : WeightedKLRAlgebra k Γ ν) (x y : GalleryAlgebra k Γ ν)
    (ha : a.1 = x * galList k C w * y) (m : M) : a • m = 0 := by
  apply smul_eq_zero_of_factor_unsupported hC a
    (x * galList k (C.flips (w.take j)) (w.drop j)) (galList k C (w.take j) * y) ?_ m
  rw [ha, galList_factor_prefix C w j]
  simp only [mul_assoc]

end Categorification.WeightedKLR.GalleryAlgebra

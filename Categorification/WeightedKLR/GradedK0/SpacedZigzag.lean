/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.GradedK0.SpacedEntries
import Categorification.KLR.KL2.K0Relations

/-!
# Transport of a Serre zigzag to weighted loading projectives

Supporting the map from the positive quantum group to graded projective `K₀` in B. Webster,
*Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.4, Theorem 2.19,
roadmap C, using Proposition 2.14. A homogeneous contracting zigzag on ordinary sequence
projectives transports to weighted loading projectives entry by entry. The telescoping
argument is KL II, arXiv:0804.2080v1, §3, Proposition 6 and Corollary 7, and is used for
Rouquier's arXiv:0812.5023v1, §4.1.1, Proposition 4.2. The source zigzag identities remain
explicit inputs of this supporting transport lemma. The target loading idempotents are
allowed to coincide for different sequence indices.
-/

noncomputable section

namespace Categorification.WeightedKLR.GradingDatum

open GalleryAlgebra Categorification.Graded LaurentPolynomial _root_.Finset

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}
  {ν : Multiset I}

/-- A sequence-supported homogeneous zigzag gives the same alternating relation among
weighted loading projectives. Distinct sequence tags need not give distinct weighted chambers. -/
theorem sum_neg_one_pow_smul_of_spaced_zigzag (G : GradingDatum Γ)
    (hS : Γ.Standing) (hD : Γ.Dagger) (hne : ∀ e, Γ.head e ≠ Γ.tail e)
    (hl : ∀ i, Γ.loop i = none)
    {N : ℕ} (tag : ℕ → KLR.Seq ν)
    {E Gp Gm : ℕ → KLR.KLRAlgebra k Γ.klrQ ν} {dg sh : ℕ → ℤ}
    (hE : ∀ n, n ≤ N → IsIdempotentElem (E n))
    (hE0 : ∀ n, n ≤ N → E n ∈ (G.toKLRGrading hne hl).grade ν 0)
    (hER : ∀ n, n ≤ N → E n * KLR.KLRAlgebra.e (tag n) = E n)
    (hpR : ∀ n, n ≤ N → Gp n * KLR.KLRAlgebra.e (tag n) = Gp n)
    (hmR : ∀ n, n ≤ N → Gm n * KLR.KLRAlgebra.e (tag n) = Gm n)
    (hsum : ∀ n, n ≤ N → Gp n + Gm n = E n)
    (hpm : ∀ n, n ≤ N → Gp n * Gm n = 0)
    (hmp : ∀ n, n ≤ N → Gm n * Gp n = 0)
    (hpE : ∀ n, n ≤ N → Gp n * E n = Gp n)
    (hmE : ∀ n, n ≤ N → Gm n * E n = Gm n)
    (hxy : ∀ n, n < N → ∃ x y : KLR.KLRAlgebra k Γ.klrQ ν,
      x ∈ (G.toKLRGrading hne hl).grade ν (dg n) ∧
      y ∈ (G.toKLRGrading hne hl).grade ν (-dg n) ∧
      x * KLR.KLRAlgebra.e (tag (n + 1)) = x ∧
      y * KLR.KLRAlgebra.e (tag n) = y ∧ x * y = Gp n ∧ y * x = Gm (n + 1))
    (hGm : Gm 0 = 0) (hGp : Gp N = 0)
    (hsh : ∀ n, n < N → sh (n + 1) = sh n + dg n)
    (P : ℕ → K0 (G.klrGrade ν.toFinsupp))
    (hP : ∀ n (hn : n ≤ N), P n = K0.of (GProj.ofIdempotent
      (spacedEntryMap hS hD hne hl (tag n) (tag n) (E n))
      (isIdempotentElem_spacedEntryMap hS hD hne hl (hE n hn) (hER n hn))
      (G.spacedEntryMap_mem_klrGrade hS hD hne hl (hE0 n hn) (tag n) (tag n)))) :
    ∑ n ∈ range (N + 1), ((-1 : LaurentPolynomial ℤ) ^ n * T (-sh n)) • P n = 0 := by
  let F := spacedEntryMap (ν := ν) hS hD hne hl
  refine Graded.K0.sum_neg_one_pow_smul_of_zigzag
    (E := fun n => F (tag n) (tag n) (E n))
    (Gp := fun n => F (tag n) (tag n) (Gp n))
    (Gm := fun n => F (tag n) (tag n) (Gm n)) (dg := dg)
    (fun n hn => isIdempotentElem_spacedEntryMap hS hD hne hl (hE n hn) (hER n hn))
    (fun n hn => G.spacedEntryMap_mem_klrGrade hS hD hne hl (hE0 n hn) _ _)
    (fun n hn => by rw [← map_add, hsum n hn])
    (fun n hn => ?_) (fun n hn => ?_) (fun n hn => ?_) (fun n hn => ?_)
    (fun n hn => ?_) (by simp only [hGm, map_zero]) (by simp only [hGp, map_zero])
    hsh P hP
  · rw [← spacedEntryMap_mul_of_right_support hS hD hne hl (Gm n) (hpR n hn), hpm n hn,
      map_zero]
  · rw [← spacedEntryMap_mul_of_right_support hS hD hne hl (Gp n) (hmR n hn), hmp n hn,
      map_zero]
  · rw [← spacedEntryMap_mul_of_right_support hS hD hne hl (E n) (hpR n hn), hpE n hn]
  · rw [← spacedEntryMap_mul_of_right_support hS hD hne hl (E n) (hmR n hn), hmE n hn]
  · obtain ⟨x, y, hx, hy, hxR, hyR, hxy, hyx⟩ := hxy n hn
    refine ⟨F (tag n) (tag (n + 1)) x, F (tag (n + 1)) (tag n) y,
      G.spacedEntryMap_mem_klrGrade hS hD hne hl hx _ _,
      G.spacedEntryMap_mem_klrGrade hS hD hne hl hy _ _, ?_, ?_⟩
    · rw [← spacedEntryMap_mul_of_right_support hS hD hne hl y hxR, hxy]
    · rw [← spacedEntryMap_mul_of_right_support hS hD hne hl x hyR, hyx]

end Categorification.WeightedKLR.GradingDatum

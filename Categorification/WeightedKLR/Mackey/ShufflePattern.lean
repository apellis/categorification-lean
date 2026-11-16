/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.ShuffleSubquotient

/-!
# The shuffle element depends only on the strands sent into the first block

A step of the proof of B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, Theorem 2.19 (the Mackey filtration of §2.4). The shuffle element `ψ^W_g`
between rank-ordered chambers (`GalleryAlgebra.rankShuffleElt`) is built from a relabelling `g`
of the strands. Here it is shown that `ψ^W_g` depends on `g` only through the set of strands
`t` with `g t` in the first block `ν₁`: relabellings with the same such set give the same
element, hence the same map `x ⊗ y ↦ [e D ι(x) ψ^W_g ι(y) e C]` into the subquotients of the
filtration.

The key input is that relabellings between rank-ordered chambers are trivial: a relabelling
preserving colours and the order of the strands of each colour is the identity
(`FullChamber.eq_one_of_isRankOrdered_smul`).

## Main results

* `FullChamber.eq_one_of_isRankOrdered_smul`: if `A` and `ρ • A` are rank-ordered, `ρ = 1`.
* `GalleryAlgebra.rankShuffleElt_eq_of_isLeft_iff`: `ψ^W_g = ψ^W_{g'}` when `g` and `g'` send the
  same strands into the first block.
* `GalleryAlgebra.shuffleInductionMap_eq_of_isLeft_iff`: the corresponding maps into the
  subquotient agree.
-/

namespace Categorification.WeightedKLR

open MvPolynomial Equiv FullChamber Segment Pointwise GalleryAlgebra Juxtapose

open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

namespace FullChamber

omit [DecidableEq I] in
/-- A relabelling between two rank-ordered chambers preserves the order of the ranks of the
strands of each colour. -/
theorem lt_iff_of_isRankOrdered_smul {A : FullChamber Γ ν} (hA : A.IsRankOrdered)
    {ρ : ColPerm ν} (hρ : (ρ • A).IsRankOrdered) {s t : Strand ν} (hc : s.1 = t.1) :
    s.2.val < t.2.val ↔ (ρ.1 s).2.val < (ρ.1 t).2.val := by
  have hc' : (ρ.1 s).1 = (ρ.1 t).1 := by rw [colPerm_apply_fst, colPerm_apply_fst, hc]
  have h1 := strandLt_iff_of_isRankOrdered hA (s := s) (t := t)
  have h2 := strandLt_iff_of_isRankOrdered hρ (s := ρ.1 s) (t := ρ.1 t)
  rw [strandLt_smul] at h2
  simp only [hc, hc', true_and] at h1 h2
  exact h1.symm.trans h2

omit [DecidableEq I] in
/-- **Relabellings between rank-ordered chambers are trivial.** If `A` and `ρ • A` are both
rank-ordered, then `ρ = 1`. -/
theorem eq_one_of_isRankOrdered_smul {A : FullChamber Γ ν} (hA : A.IsRankOrdered)
    {ρ : ColPerm ν} (hρ : (ρ • A).IsRankOrdered) : ρ = 1 := by
  refine Subtype.ext (Equiv.ext fun s => ?_)
  obtain ⟨i, a⟩ := s
  let f : Fin (ν i) → Fin (ν i) := fun b =>
    ⟨(ρ.1 ⟨i, b⟩).2.val,
      lt_of_lt_of_eq (ρ.1 ⟨i, b⟩).2.isLt (by rw [colPerm_apply_fst])⟩
  have hf : StrictMono f := fun b b' h =>
    (lt_iff_of_isRankOrdered_smul hA hρ (s := ⟨i, b⟩) (t := ⟨i, b'⟩) rfl).1 h
  have h := congrArg Fin.val (hf.apply_eq (x := a))
  exact Strand.ext_of (colPerm_apply_fst ρ ⟨i, a⟩) h

end FullChamber

namespace GalleryAlgebra

variable {ν' ν'' ν₁ ν₂ : I →₀ ℕ}

/-- `ψ^W_g` written with the relabelling `u g` onto its rank-ordered top end. -/
theorem rankShuffleElt_eq_r_mul (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν) (hD : Γ.Dagger)
    (hZ : Γ.NoZeroLoops) (g : ColPerm ν) (C : FullChamber Γ ν) :
    rankShuffleElt k hν' hν₁ hD hZ g C =
      r (blockSort hν₁ (g • shuffleTop (fun t => decide ((g.1 t).IsLeft ν₁)) C) * g)
          (shuffleTop (fun t => decide ((g.1 t).IsLeft ν₁)) C) *
        galList k (shuffleBot (fun t => decide (t.IsLeft ν'))
            (fun t => decide ((g.1 t).IsLeft ν₁)) C)
          (shuffleWord hD hZ (fun t => decide (t.IsLeft ν'))
            (fun t => decide ((g.1 t).IsLeft ν₁)) C) *
        r (blockSort hν' (shuffleBot (fun t => decide (t.IsLeft ν'))
            (fun t => decide ((g.1 t).IsLeft ν₁)) C))⁻¹
          (blockSort hν' (shuffleBot (fun t => decide (t.IsLeft ν'))
              (fun t => decide ((g.1 t).IsLeft ν₁)) C) •
            shuffleBot (fun t => decide (t.IsLeft ν'))
              (fun t => decide ((g.1 t).IsLeft ν₁)) C) := by
  rw [rankShuffleElt, shuffleElt, ← mul_assoc, r_mul_r]

/-- The relabelling `u g` onto the rank-ordered top end depends only on the strands sent into
the first block. -/
theorem blockSort_mul_eq_of_isLeft_iff (hν₁ : ν₁ + ν₂ = ν) {g g' : ColPerm ν}
    (hY : (fun t => decide ((g.1 t).IsLeft ν₁)) = fun t => decide ((g'.1 t).IsLeft ν₁))
    (C : FullChamber Γ ν) :
    blockSort hν₁ (g • shuffleTop (fun t => decide ((g.1 t).IsLeft ν₁)) C) * g =
      blockSort hν₁ (g' • shuffleTop (fun t => decide ((g'.1 t).IsLeft ν₁)) C) * g' := by
  have hT : shuffleTop (fun t => decide ((g'.1 t).IsLeft ν₁)) C =
      shuffleTop (fun t => decide ((g.1 t).IsLeft ν₁)) C := by rw [← hY]
  have ha := isRankOrdered_rankShuffleTop (k := k) hν₁ g C
  have hb := isRankOrdered_rankShuffleTop (k := k) hν₁ g' C
  rw [rankShuffleTop, smul_smul] at ha hb
  rw [hT] at hb ⊢
  set T := shuffleTop (fun t => decide ((g.1 t).IsLeft ν₁)) C
  set a := blockSort hν₁ (g • T) * g
  set b := blockSort hν₁ (g' • T) * g'
  have h1 : b * a⁻¹ = 1 := by
    refine eq_one_of_isRankOrdered_smul ha ?_
    rwa [smul_smul, inv_mul_cancel_right]
  exact (mul_inv_eq_one.1 h1).symm

/-- **`ψ^W_g` depends only on the strands sent into the first block.** If `g` and `g'` send the
same strands into the block `ν₁`, then `ψ^W_g = ψ^W_{g'}`. -/
theorem rankShuffleElt_eq_of_isLeft_iff (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν)
    (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) {g g' : ColPerm ν}
    (h : ∀ t, (g.1 t).IsLeft ν₁ ↔ (g'.1 t).IsLeft ν₁) (C : FullChamber Γ ν) :
    rankShuffleElt k hν' hν₁ hD hZ g C = rankShuffleElt k hν' hν₁ hD hZ g' C := by
  have hY : (fun t => decide ((g.1 t).IsLeft ν₁)) = fun t => decide ((g'.1 t).IsLeft ν₁) :=
    funext fun t => decide_eq_decide.2 (h t)
  rw [rankShuffleElt_eq_r_mul, rankShuffleElt_eq_r_mul,
    blockSort_mul_eq_of_isLeft_iff (k := k) (Γ := Γ) hν₁ hY C, hY]

variable {P : FullChamber Γ ν → FullChamber Γ ν → (Strand ν → 𝕜) × (Strand ν → 𝕜)}
  (hP : ∀ C E, IsChamberSegment C E (P C E)) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
  (hΓ : Γ.PSymm) (hW : ∀ w : Wall Γ ν, IsRegular (w.factor (k := k)))
  (hL : ∀ (Q : MvPolynomial (Fin 2) k) (a b : Strand ν), Γ.loop a.1 = some Q → a ≠ b →
    a.1 = b.1 → IsRegular (loopFactor Q a b))

/-- **The maps into the subquotient depend only on the strands sent into the first block.** -/
theorem shuffleInductionMap_eq_of_isLeft_iff (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν)
    {D C : FullChamber Γ ν} (hC : C.IsRankOrdered) (hD' : D.IsRankOrdered)
    (S' : Set (I → ℕ)) {S : Set (I → ℕ)} (hS : IsLowerSet S) {g g' : ColPerm ν}
    (hg : shuffleType ν' ν₁ g ∈ S) (hg' : shuffleType ν' ν₁ g' ∈ S)
    (h : ∀ t, (g.1 t).IsLeft ν₁ ↔ (g'.1 t).IsLeft ν₁) :
    shuffleInductionMap k hP hD hZ hΓ hW hL hν' hν₁ hC hD' S' hS hg =
      shuffleInductionMap k hP hD hZ hΓ hW hL hν' hν₁ hC hD' S' hS hg' := by
  refine LinearMap.ext fun z => ?_
  rw [shuffleInductionMap_apply, shuffleInductionMap_apply]
  congr 2
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    rw [shuffleInductionAux_tmul, shuffleInductionAux_tmul,
      rankShuffleElt_eq_of_isLeft_iff hν' hν₁ hD hZ h C]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

end GalleryAlgebra

end Categorification.WeightedKLR

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.TypeTensor
import Categorification.WeightedKLR.Mackey.Swap
import Categorification.WeightedKLR.Induction.Graded

/-!
# The degree of the shuffle element of a shuffle type

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.4, proof of
Theorem 2.19 (after Khovanov–Lauda, arXiv:0803.4121v2, Proposition 2.18): the subquotient of the
Mackey filtration of shuffle type `μ` is the balanced tensor product shifted by the degree of the
diagram exchanging the two middle blocks. This file computes that shift on representatives.

Let `B` be a four-block chamber for the sets of strands `X` (the first block) and `Z` (moved to
the left by the shuffle). Its strands fall into four blocks `a = X ∩ Z`, `b = X \ Z`,
`c = Z \ X`, `d` (the rest), in this order from left to right. The chamber `shuffleTop Z B`
differs from `B` exactly on the hyperplanes joining a strand of `b` with a strand of `c`
(`FullChamber.shuffleTop_ne_iff_of_shuffleBot_eq`). The four-block shuffle element is a relabelling
(degree `0`) after a minimal gallery from `B` to `shuffleTop Z B`, which crosses each of these
hyperplanes once. So it is homogeneous of degree
`∑_{s ∈ b, t ∈ c} pairDeg (label s) (label t)` (`GalleryAlgebra.fourShuffle_mem_grade`), and so
is the sum `ψ_μ` over all four-block chambers (`GalleryAlgebra.typeShuffle_mem_grade`). Hence the
representative `e D ι(x) ψ_μ ι(y) e C` of the class of `x ⊗ y` in the subquotient has degree
`deg x + deg y + ∑_{s ∈ b, t ∈ c} pairDeg (label s) (label t)`
(`GalleryAlgebra.typeInductionAux_mem_grade`). For the four-block layout `a b c d` this sum is
`∑_{i, j} b_i c_j pairDeg i j` (`GradingDatum.shuffleDeg_middleLeft`).

The statement is about representatives; the grading of the subquotient and the graded form of
the corner isomorphism are in `Categorification/WeightedKLR/Mackey/MiddleGraded.lean`.

## Conventions

The grading datum `GradingDatum.ofStanding` of Webster's standing hypothesis gives a dot of
colour `i` degree `2 d_i`, so our degrees are twice those of Webster's v4 grading, and the shift
`∑ pairDeg` is `-(b · c)` for the symmetric form `i · j = ⟨i, j⟩ + ⟨j, i⟩`, that is twice
Webster's `-⟨μ, μ'⟩` read with the symmetric pairing of roots. As recorded in
`Categorification/WeightedKLR/Mackey/Swap.lean`, the shift printed as `-⟨μ, μ'⟩` in the proof
of Theorem 2.19 needs this symmetric pairing; it is wrong for the non-symmetric form of §2.4.

## Main results

* `GradingDatum.galDeg_eq_sum_of_goodWord`: a minimal gallery has the degree of the hyperplanes
  separating its ends.
* `GradingDatum.sum_hypDeg_joins`: the hyperplanes joining two disjoint sets of strands have
  total degree `∑ pairDeg`.
* `GalleryAlgebra.fourShuffle_mem_grade`, `GalleryAlgebra.typeShuffle_mem_grade`: the degree of
  the shuffle elements.
* `GalleryAlgebra.typeInductionAux_mem_grade`: the degree shift of `x ⊗ y ↦ e D ι(x) ψ_μ ι(y) e C`.
* `GradingDatum.shuffleDeg_middleLeft`: the shift for the four-block layout, in terms of dimension
  vectors.
-/

namespace Categorification.WeightedKLR

open FullChamber GalleryAlgebra Juxtapose

open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

namespace GradingDatum

variable (G : GradingDatum Γ)

omit [IsStrictOrderedRing 𝕜] in
/-- **The degree of a minimal gallery** is the sum of the degrees of the hyperplanes on which its
two ends differ. -/
theorem galDeg_eq_sum_of_goodWord {C : FullChamber Γ ν} {w : List (Hyp Γ ν)}
    (hw : GoodWord C.1 w) :
    G.galDeg C w =
      ∑ h ∈ Finset.univ.filter (fun h => (C.flips w).1 h ≠ C.1 h), G.hypDeg h := by
  rw [G.galDeg_of_goodWord hw, ← List.sum_toFinset _ hw.1]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext h
  simp only [List.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hw.mem_iff h

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem sum_wall (F : Γ.E → Strand ν → Strand ν → ℤ) :
    ∑ w : Wall Γ ν, F w.edge w.src w.tgt =
      ∑ e, ∑ s, ∑ t, if s.label = Γ.head e ∧ t.label = Γ.tail e ∧ s ≠ t then F e s t else 0 := by
  let F' : Γ.E × Strand ν × Strand ν → ℤ := fun x => F x.1 x.2.1 x.2.2
  have h : ∑ w : Wall Γ ν, F' w.1 = ∑ x ∈ Finset.univ.filter (fun x :
      Γ.E × Strand ν × Strand ν =>
        x.2.1.label = Γ.head x.1 ∧ x.2.2.label = Γ.tail x.1 ∧ x.2.1 ≠ x.2.2), F' x :=
    (Finset.sum_subtype (F := (inferInstance : Fintype (Wall Γ ν))) _ (fun x => by simp) F').symm
  change ∑ w : Wall Γ ν, F' w.1 = _
  rw [h, Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Fintype.sum_prod_type]

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem sum_diag (F : Strand ν → Strand ν → ℤ) :
    ∑ d : Diag ν, F d.fst d.snd =
      ∑ s, ∑ t, if s.1 = t.1 ∧ s.2.val < t.2.val then F s t else 0 := by
  let F' : Strand ν × Strand ν → ℤ := fun x => F x.1 x.2
  have h : ∑ d : Diag ν, F' d.1 = ∑ x ∈ Finset.univ.filter (fun x : Strand ν × Strand ν =>
      x.1.1 = x.2.1 ∧ x.1.2.val < x.2.2.val), F' x :=
    (Finset.sum_subtype (F := (inferInstance : Fintype (Diag ν))) _ (fun x => by simp) F').symm
  change ∑ d : Diag ν, F' d.1 = _
  rw [h, Finset.sum_filter, Fintype.sum_prod_type]

theorem diag_add_diag_swap {s t : Strand ν} (hst : s ≠ t) (f : I → ℤ) :
    ((if s.1 = t.1 ∧ s.2.val < t.2.val then f s.label else 0) +
        if t.1 = s.1 ∧ t.2.val < s.2.val then f t.label else 0) =
      if s.label = t.label then f s.label else 0 := by
  have hl : s.label = t.label ↔ s.1 = t.1 := Subtype.ext_iff.symm
  by_cases h1 : s.1 = t.1
  · have hne : s.2.val ≠ t.2.val := fun h2 => hst (Strand.ext_of h1 h2)
    have hlab : s.label = t.label := hl.2 h1
    rcases lt_or_gt_of_ne hne with h | h
    · simp [h1, h, hlab, not_lt.2 h.le]
    · simp [h1, h, hlab, not_lt.2 h.le]
  · simp [h1, hl, Ne.symm h1]

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- **The hyperplanes joining two disjoint sets of strands.** For disjoint sets `P`, `Q` of
strands, the hyperplanes with one strand in `P` and the other in `Q` have total degree
`∑_{s ∈ P, t ∈ Q} pairDeg (label s) (label t)`. -/
theorem sum_hypDeg_joins (P Q : Strand ν → Prop) [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ s, P s → ¬ Q s) :
    ∑ h ∈ Finset.univ.filter (fun h : Hyp Γ ν => (P h.lo ∧ Q h.hi) ∨ (Q h.lo ∧ P h.hi)),
        G.hypDeg h =
      ∑ s ∈ Finset.univ.filter P, ∑ t ∈ Finset.univ.filter Q, G.pairDeg s.label t.label := by
  rw [Finset.sum_filter, Fintype.sum_sum_type]
  have hw := sum_wall (Γ := Γ) (ν := ν) fun e s t =>
    if (P s ∧ Q t) ∨ (Q s ∧ P t) then G.wall e else 0
  have hd := sum_diag (ν := ν) fun s t =>
    if (P s ∧ Q t) ∨ (Q s ∧ P t) then G.cross s.label else 0
  change (∑ w : Wall Γ ν, if (P w.src ∧ Q w.tgt) ∨ (Q w.src ∧ P w.tgt) then G.wall w.edge
      else 0) + (∑ d : Diag ν, if (P d.fst ∧ Q d.snd) ∨ (Q d.fst ∧ P d.snd)
      then G.cross d.fst.label else 0) = _
  rw [hw, hd, Finset.sum_comm, ← Finset.sum_add_distrib]
  set A : Strand ν → Strand ν → ℤ := fun s t =>
    (∑ e, if s.label = Γ.head e ∧ t.label = Γ.tail e ∧ s ≠ t then
      (if (P s ∧ Q t) ∨ (Q s ∧ P t) then G.wall e else 0) else 0) +
    if s.1 = t.1 ∧ s.2.val < t.2.val then
      (if (P s ∧ Q t) ∨ (Q s ∧ P t) then G.cross s.label else 0) else 0 with hA
  have h1 : ∀ s, (∑ e, ∑ t, if s.label = Γ.head e ∧ t.label = Γ.tail e ∧ s ≠ t then
      (if (P s ∧ Q t) ∨ (Q s ∧ P t) then G.wall e else 0) else 0) +
      (∑ t, if s.1 = t.1 ∧ s.2.val < t.2.val then
        (if (P s ∧ Q t) ∨ (Q s ∧ P t) then G.cross s.label else 0) else 0) = ∑ t, A s t := by
    intro s
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl fun s _ => h1 s]
  have h2 : ∀ s t, A s t = (if P s ∧ Q t then A s t else 0) + if Q s ∧ P t then A s t else 0 := by
    intro s t
    by_cases hp : P s ∧ Q t
    · have : ¬ (Q s ∧ P t) := fun h => hPQ s hp.1 h.1
      simp [hp, this]
    · by_cases hq : Q s ∧ P t
      · simp [hp, hq]
      · simp [hA, hp, hq]
  rw [Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => h2 s t]
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun s t => if Q s ∧ P t then A s t else 0), ← Finset.sum_add_distrib]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_filter, ← Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero,
    add_zero]
  by_cases hPs : P s
  · rw [ite_eq_left hPs, Finset.sum_filter]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases hQt : Q t
    · have hst : s ≠ t := fun h => hPQ s hPs (h ▸ hQt)
      have hQs : ¬ Q s := hPQ s hPs
      have hPt : ¬ P t := fun h => hPQ t h hQt
      simp only [hA, hPs, hQt, hQs, hPt, and_self, and_true, or_false, false_or,
        ite_true, ne_eq, hst, Ne.symm hst, not_false_eq_true]
      rw [add_add_add_comm, diag_add_diag_swap hst, GradingDatum.pairDeg]
    · simp [hQt]
  · simp [hPs]

/-- **The degree of a shuffle** of the strands `X` past the strands `Z`: the total degree
`∑ pairDeg` of the pairs of a strand in `X \ Z` and a strand in `Z \ X`. -/
def shuffleDeg (X Z : Strand ν → Bool) : ℤ :=
  ∑ s ∈ Finset.univ.filter (fun s => X s = true ∧ Z s = false),
    ∑ t ∈ Finset.univ.filter (fun t => X t = false ∧ Z t = true), G.pairDeg s.label t.label

end GradingDatum

namespace FullChamber

omit [DecidableEq I] in
/-- **Where a four-block chamber and its shuffle differ.** If `B` is separated by `X` and, inside
the blocks of `X`, by `Z`, then `B` and `shuffleTop Z B` differ exactly on the hyperplanes joining
a strand of `X \ Z` with a strand of `Z \ X`. -/
theorem shuffleTop_ne_iff_of_shuffleBot_eq {X Z : Strand ν → Bool} {B : FullChamber Γ ν}
    (hB : shuffleBot X Z B = B) (h : Hyp Γ ν) :
    (shuffleTop Z B).1 h ≠ B.1 h ↔
      ((X h.lo = true ∧ Z h.lo = false) ∧ (X h.hi = false ∧ Z h.hi = true)) ∨
        ((X h.lo = false ∧ Z h.lo = true) ∧ (X h.hi = true ∧ Z h.hi = false)) := by
  have e : (shuffleBot X Z B).1 h = B.1 h := by rw [hB]
  rw [shuffleBot_apply, shuffleTop_apply] at e
  rw [shuffleTop_apply]
  generalize X h.lo = a₁ at *
  generalize X h.hi = a₂ at *
  generalize Z h.lo = b₁ at *
  generalize Z h.hi = b₂ at *
  generalize B.1 h = c at *
  revert e
  cases a₁ <;> cases a₂ <;> cases b₁ <;> cases b₂ <;> cases c <;> decide

end FullChamber

namespace GalleryAlgebra

variable (G : GradingDatum Γ)

/-- **The degree of a four-block shuffle element.** For `B` separated by `X` and, inside the
blocks of `X`, by `Z`, the shuffle element `fourShuffle Z B` is homogeneous of degree
`∑_{s ∈ X \ Z, t ∈ Z \ X} pairDeg (label s) (label t)`. -/
theorem fourShuffle_mem_grade (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) {X Z : Strand ν → Bool}
    {B : FullChamber Γ ν} (hB : shuffleBot X Z B = B) :
    fourShuffle k hD hZ Z B ∈ G.grade ν (G.shuffleDeg X Z) := by
  obtain ⟨hw, hfw⟩ := (exists_goodWord hD hZ B (shuffleTop Z B)).choose_spec
  set w := (exists_goodWord hD hZ B (shuffleTop Z B)).choose
  have hd : G.shuffleDeg X Z = 0 + G.galDeg B w := by
    rw [zero_add, G.galDeg_eq_sum_of_goodWord hw, hfw, GradingDatum.shuffleDeg,
      ← G.sum_hypDeg_joins (fun s => X s = true ∧ Z s = false)
        (fun s => X s = false ∧ Z s = true) (fun s hs hs' => by simp_all)]
    refine Finset.sum_congr (Finset.filter_congr fun h _ => ?_) fun _ _ => rfl
    exact (shuffleTop_ne_iff_of_shuffleBot_eq hB h).symm
  rw [hd, fourShuffle]
  exact CoactionGrading.mul_mem_grade _ (G.r_mem_grade _ _) (G.galList_mem_grade B w)

/-- **The degree of the shuffle element of a shuffle type**: `typeShuffle X Z` is homogeneous of
degree `∑_{s ∈ X \ Z, t ∈ Z \ X} pairDeg (label s) (label t)`. -/
theorem typeShuffle_mem_grade (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (X Z : Strand ν → Bool) :
    typeShuffle k hD hZ X Z ∈ G.grade ν (G.shuffleDeg X Z) := by
  classical
  rw [typeShuffle]
  exact Submodule.sum_mem _ fun B hB => fourShuffle_mem_grade G hD hZ (Finset.mem_filter.1 hB).2.2

theorem castGallery_mem_grade {μ : I →₀ ℕ} (h : ν = μ) {d : ℤ} {x : GalleryAlgebra k Γ ν}
    (hx : x ∈ G.grade ν d) : castGallery k Γ h x ∈ G.grade μ d := by
  subst h
  exact hx

variable {ν₁ ν₂ : I →₀ ℕ}

/-- `ι(x ⊗ y)`, read in `W_ν` along `ν₁ + ν₂ = ν`, has degree `deg x + deg y`. -/
theorem inductionVal_tmul_mem_grade (hν : ν₁ + ν₂ = ν) {d₁ d₂ : ℤ}
    {x : WeightedKLRAlgebra k Γ ν₁} {y : WeightedKLRAlgebra k Γ ν₂}
    (hx : x.1 ∈ G.grade ν₁ d₁) (hy : y.1 ∈ G.grade ν₂ d₂) :
    inductionVal k hν (x ⊗ₜ y) ∈ G.grade ν (d₁ + d₂) := by
  rw [inductionVal_apply]
  exact castGallery_mem_grade G hν (Juxtapose.inductionMap_tmul_mem_grade G hx hy)

variable {ν' ν'' : I →₀ ℕ}

/-- **The degree shift of the Mackey subquotient, on representatives** (Webster,
arXiv:1209.2463v4, proof of Theorem 2.19). For homogeneous `x₁, x₂, y₁, y₂`, the representative
`e D ι(x₁ ⊗ x₂) ψ_μ ι(y₁ ⊗ y₂) e C` of the class of `(x₁ ⊗ x₂) ⊗ (y₁ ⊗ y₂)` has degree
`deg x₁ + deg x₂ + δ + (deg y₁ + deg y₂)`, where `δ` is the total degree `∑ pairDeg` of the pairs
of a strand of `ν'` not in `Z` and a strand of `Z` not in `ν'`. In Webster's grading the shift
is half of `δ` (see the module docstring). -/
theorem typeInductionAux_mem_grade (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hν' : ν' + ν'' = ν)
    (hν₁ : ν₁ + ν₂ = ν) (D C : FullChamber Γ ν) (Z : Strand ν → Bool) {d₁ d₂ d₃ d₄ : ℤ}
    {x₁ : WeightedKLRAlgebra k Γ ν₁} {x₂ : WeightedKLRAlgebra k Γ ν₂}
    {y₁ : WeightedKLRAlgebra k Γ ν'} {y₂ : WeightedKLRAlgebra k Γ ν''}
    (hx₁ : x₁.1 ∈ G.grade ν₁ d₁) (hx₂ : x₂.1 ∈ G.grade ν₂ d₂)
    (hy₁ : y₁.1 ∈ G.grade ν' d₃) (hy₂ : y₂.1 ∈ G.grade ν'' d₄) :
    typeInductionAux k hD hZ hν' hν₁ D C Z ((x₁ ⊗ₜ x₂) ⊗ₜ (y₁ ⊗ₜ y₂)) ∈
      G.grade ν (d₁ + d₂ + G.shuffleDeg (fun t => decide (t.IsLeft ν')) Z + (d₃ + d₄)) := by
  rw [typeInductionAux_tmul]
  have := CoactionGrading.mul_mem_grade _ (CoactionGrading.mul_mem_grade _
    (CoactionGrading.mul_mem_grade _ (CoactionGrading.mul_mem_grade _ (G.e_mem_grade D)
      (inductionVal_tmul_mem_grade G hν₁ hx₁ hx₂))
      (typeShuffle_mem_grade G hD hZ (fun t => decide (t.IsLeft ν')) Z))
    (inductionVal_tmul_mem_grade G hν' hy₁ hy₂)) (G.e_mem_grade C)
  rwa [zero_add, add_zero] at this

end GalleryAlgebra

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Summing a function of the colour over a set of strands counts its strands of each
colour. -/
theorem Strand.sum_filter_label (P : Strand ν → Prop) [DecidablePred P] (F : I → ℤ) :
    ∑ s ∈ Finset.univ.filter P, F s.label =
      ∑ i : ν.support,
        ((Finset.univ.filter fun s : Strand ν => s.1 = i ∧ P s).card : ℤ) * F i := by
  rw [← Finset.sum_fiberwise (Finset.univ.filter P) (fun s => s.1)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.filter_filter, Finset.sum_congr rfl (g := fun _ => F i), Finset.sum_const,
    nsmul_eq_mul]
  · congr 3
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_comm]
  · intro s hs
    simp only [Finset.mem_filter] at hs
    simp only [Strand.label, hs.2.2]

namespace Juxtapose

variable (a b c d : I →₀ ℕ)

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- The strands of `middleLeft a b c d`: the blocks `a` and `c`, by rank. -/
theorem middleLeft_apply (s : Strand (a + b + (c + d))) :
    middleLeft a b c d s = decide ((s.2 : ℕ) < a s.1 ∨
      (a s.1 + b s.1 ≤ s.2 ∧ (s.2 : ℕ) < a s.1 + b s.1 + c s.1)) := by
  unfold middleLeft blockLeft
  by_cases h : s.IsLeft (a + b)
  · rw [ite_eq_left h, decide_eq_decide]
    unfold Strand.IsLeft at h
    simp only [Finsupp.coe_add, Pi.add_apply] at h ⊢
    omega
  · rw [ite_eq_right h, decide_eq_decide]
    unfold Strand.IsLeft at h
    simp only [Finsupp.coe_add, Pi.add_apply] at h ⊢
    omega

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem isLeft_add_iff (s : Strand (a + b + (c + d))) :
    s.IsLeft (a + b) ↔ (s.2 : ℕ) < a s.1 + b s.1 := by
  unfold Strand.IsLeft
  simp only [Finsupp.coe_add, Pi.add_apply]

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- The block `b` of the four-block layout has `b_i` strands of colour `i`. -/
theorem card_filter_middleLeft_false (i : (a + b + (c + d)).support) :
    (Finset.univ.filter fun s : Strand (a + b + (c + d)) =>
      s.1 = i ∧ (decide (s.IsLeft (a + b)) = true ∧ middleLeft a b c d s = false)).card =
      b i := by
  have hle : a i + b i ≤ (a + b + (c + d)) i := by simp only [Finsupp.coe_add, Pi.add_apply]; omega
  rw [Finset.filter_congr (q := fun s : Strand (a + b + (c + d)) =>
      s.1 = i ∧ a i ≤ s.2.val ∧ s.2.val < a i + b i ∧ True) ?_,
    card_filter_colour i (a i) (a i + b i) hle]
  · rw [Finset.filter_true_of_mem fun r hr => ⟨by simp at hr; omega, trivial⟩, Nat.card_Ico]
    omega
  · rintro s -
    simp only [middleLeft_apply, decide_eq_true_iff, decide_eq_false_iff_not, isLeft_add_iff]
    constructor
    · rintro ⟨rfl, h1, h2⟩
      exact ⟨rfl, by omega, by omega, trivial⟩
    · rintro ⟨rfl, h1, h2, -⟩
      exact ⟨rfl, by omega, by omega⟩

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- The block `c` of the four-block layout has `c_i` strands of colour `i`. -/
theorem card_filter_middleLeft_true (i : (a + b + (c + d)).support) :
    (Finset.univ.filter fun s : Strand (a + b + (c + d)) =>
      s.1 = i ∧ (decide (s.IsLeft (a + b)) = false ∧ middleLeft a b c d s = true)).card =
      c i := by
  have hle : a i + b i + c i ≤ (a + b + (c + d)) i := by
    simp only [Finsupp.coe_add, Pi.add_apply]; omega
  rw [Finset.filter_congr (q := fun s : Strand (a + b + (c + d)) =>
      s.1 = i ∧ a i + b i ≤ s.2.val ∧ s.2.val < a i + b i + c i ∧ True) ?_,
    card_filter_colour i (a i + b i) (a i + b i + c i) hle]
  · rw [Finset.filter_true_of_mem fun r hr => ⟨by simp at hr; omega, trivial⟩, Nat.card_Ico]
    omega
  · rintro s -
    simp only [middleLeft_apply, decide_eq_true_iff, decide_eq_false_iff_not, isLeft_add_iff]
    constructor
    · rintro ⟨rfl, h1, h2⟩
      exact ⟨rfl, by omega, by omega, trivial⟩
    · rintro ⟨rfl, h1, h2, -⟩
      exact ⟨rfl, by omega, by omega⟩

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- **The degree shift of the four-block layout** `a b c d`, in terms of dimension vectors:
moving the block `c` past the block `b` has degree `∑_{i, j} b_i c_j pairDeg i j`. -/
theorem _root_.Categorification.WeightedKLR.GradingDatum.shuffleDeg_middleLeft
    (G : GradingDatum Γ) :
    G.shuffleDeg (fun t => decide (t.IsLeft (a + b))) (middleLeft a b c d) =
      ∑ i : (a + b + (c + d)).support, ∑ j : (a + b + (c + d)).support,
        (b i * c j : ℤ) * G.pairDeg i j := by
  unfold GradingDatum.shuffleDeg
  simp only [Strand.sum_filter_label _ (G.pairDeg _), card_filter_middleLeft_true]
  rw [Strand.sum_filter_label _ fun i => ∑ j : (a + b + (c + d)).support,
    (c j : ℤ) * G.pairDeg i j]
  simp only [card_filter_middleLeft_false, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Juxtapose

end Categorification.WeightedKLR

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.Degree
import Categorification.WeightedKLR.Induction.Juxtapose

/-!
# Exchanging two juxtaposed blocks of strands

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.4, proof of
Theorem 2.19, which follows M. Khovanov, A. Lauda, *A diagrammatic approach to categorification
of quantum groups I*, arXiv:0803.4121v2, Proposition 2.18. The subquotients of the Mackey
filtration are twisted by the diagram that moves a block of strands past another block, and
they are shifted by its degree. This file computes that degree.

Juxtaposing configurations `p'` of `ν'` and `p''` of `ν''` with the second block translated by
`c` gives a configuration of `ν' + ν''` (`Juxtapose.juxt`). For `c` large the second block is far
to the right (the chamber `Juxtapose.chamber C' C''`); for `-c` large it is far to the left
(`Juxtapose.swapChamber C' C''`). The two chambers differ exactly on the hyperplanes joining a
strand of `ν'` with a strand of `ν''` (`Juxtapose.IsCross`). By `GradingDatum.segDeg_eq_sum`, the
straight gallery between them has degree the sum of the degrees of these hyperplanes, which is
`∑_{a ∈ ν', b ∈ ν''} pairDeg (label a) (label b)` (`Juxtapose.segDeg_chamber_swapChamber`), where

  `pairDeg i j = ∑_{e : j → i} wall e + ∑_{e : i → j} wall e + δ_{ij} cross i`

is symmetric in `i, j` (`GradingDatum.pairDeg_comm`). For the grading of Webster's standing
hypothesis (`WeightedGraph.Standing.gradingDatum`: a dot of colour `i` has degree `2 d_i`, a wall
of `e` degree `d_{head e} c_e`), unfolding the definitions gives `pairDeg i j = -(i · j)` for
Webster's symmetric form `i · j = ⟨i, j⟩ + ⟨j, i⟩` of §2.4, loops included. So the exchange of
blocks of dimension vectors `μ, μ'` has degree `-(μ · μ')` in either order, as in
Khovanov–Lauda's Proposition 2.18. The shift printed as `-⟨μ, μ'⟩` in the proof of Webster's
Theorem 2.19 is right when `⟨-, -⟩` is read as the symmetric pairing of roots used in §2.1 (where
`⟨α_i, α_i⟩` is the degree of a dot, so `⟨α_i, α_j⟩ = i · j`), and wrong for the non-symmetric
form `⟨j, i⟩` defined in §2.4: for one edge `e : 0 → 1` with `d = c_e = 1`, the exchange of one
strand of each colour crosses one wall, of degree `1`, in both orders, while `⟨α_1, α_0⟩ = 0`
for the form of §2.4.

## Main results

* `Juxtapose.swapChamber`, `Juxtapose.swapChamber_ne_iff`.
* `GradingDatum.pairDeg`, `GradingDatum.pairDeg_comm`.
* `Juxtapose.sum_cross_hypDeg`, `Juxtapose.segDeg_chamber_swapChamber`.
-/

namespace Categorification.WeightedKLR

open FullChamber Segment GalleryAlgebra

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}
  {ν' ν'' : I →₀ ℕ}

namespace GradingDatum

variable (G : GradingDatum Γ)

/-- The degree of the crossing of a strand of colour `i` with a strand of colour `j`: the degrees
of the walls of the edges between `i` and `j`, in both directions, and of the diagonal if
`i = j`. -/
def pairDeg (i j : I) : ℤ :=
  ((∑ e, if i = Γ.head e ∧ j = Γ.tail e then G.wall e else 0) +
    ∑ e, if j = Γ.head e ∧ i = Γ.tail e then G.wall e else 0) +
  if i = j then G.cross i else 0

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem pairDeg_comm (i j : I) : G.pairDeg i j = G.pairDeg j i := by
  unfold pairDeg
  by_cases h : i = j
  · subst h; rfl
  · simp only [h, Ne.symm h, ↓reduceIte]; ring

end GradingDatum

namespace Juxtapose

/-- Whether a strand of `ν' + ν''` comes from `ν''`. -/
noncomputable def IsRight (t : Strand (ν' + ν'')) : Bool := ((strandEquiv ν' ν'').symm t).isRight

omit [DecidableEq I] in
@[simp] theorem isRight_inl (a : Strand ν') : IsRight (inlStrand ν' ν'' a) = false := by
  simp [IsRight]

omit [DecidableEq I] in
@[simp] theorem isRight_inr (b : Strand ν'') : IsRight (inrStrand ν' ν'' b) = true := by
  simp [IsRight]

/-- A hyperplane of `ν' + ν''` joining a strand of `ν'` with a strand of `ν''`. -/
def IsCross (h : Hyp Γ (ν' + ν'')) : Prop := IsRight h.lo ≠ IsRight h.hi

noncomputable instance (h : Hyp Γ (ν' + ν'')) : Decidable (IsCross h) := by
  unfold IsCross; infer_instance

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem juxt_eq (p' : Strand ν' → 𝕜) (p'' : Strand ν'' → 𝕜) (c : 𝕜) (t : Strand (ν' + ν'')) :
    juxt p' p'' c t = juxt p' p'' 0 t + if IsRight t then c else 0 := by
  unfold juxt IsRight
  rcases (strandEquiv ν' ν'').symm t with a | b <;> simp

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- The value of a hyperplane at a juxtaposition is affine in the separation. -/
theorem val_juxt (p' : Strand ν' → 𝕜) (p'' : Strand ν'' → 𝕜) (c : 𝕜) (h : Hyp Γ (ν' + ν'')) :
    h.val (juxt p' p'' c) = h.val (juxt p' p'' 0) +
      ((if IsRight h.hi then c else 0) - if IsRight h.lo then c else 0) := by
  rw [Hyp.val_eq, Hyp.val_eq, juxt_eq p' p'' c h.hi, juxt_eq p' p'' c h.lo]
  ring

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- The value of a hyperplane that is not a cross hyperplane does not depend on the
separation. -/
theorem val_juxt_of_not_isCross (p' : Strand ν' → 𝕜) (p'' : Strand ν'' → 𝕜) (c c' : 𝕜)
    {h : Hyp Γ (ν' + ν'')} (hh : ¬ IsCross h) :
    h.val (juxt p' p'' c) = h.val (juxt p' p'' c') := by
  rw [val_juxt p' p'' c, val_juxt p' p'' c']
  unfold IsCross at hh
  rw [not_not] at hh
  rw [hh]
  ring

omit [DecidableEq I] in
theorem abs_cst_lt_bound (p' : Strand ν' → 𝕜) (p'' : Strand ν'' → 𝕜) (a : Strand ν')
    (b : Strand ν'') (h : Hyp Γ (ν' + ν'')) : |p' a| + |p'' b| + |h.cst| < bound Γ p' p'' := by
  rcases h with w | d
  · exact lt_bound_wall p' p'' a b w.edge
  · simpa [Hyp.cst] using lt_bound_diag (Γ := Γ) p' p'' a b

omit [DecidableEq I] in
/-- At separation `0`, a cross hyperplane has value of absolute value less than `bound`. -/
theorem abs_val_juxt_zero_lt (p' : Strand ν' → 𝕜) (p'' : Strand ν'' → 𝕜)
    {h : Hyp Γ (ν' + ν'')} (hh : IsCross h) : |h.val (juxt p' p'' 0)| < bound Γ p' p'' := by
  unfold IsCross IsRight at hh
  rw [Hyp.val_eq]
  unfold juxt
  rcases hl : (strandEquiv ν' ν'').symm h.lo with a | b <;>
    rcases hr : (strandEquiv ν' ν'').symm h.hi with a' | b' <;> rw [hl, hr] at hh <;>
    simp only [Sum.isRight_inl, Sum.isRight_inr, ne_eq, not_true_eq_false] at hh <;>
    simp only [Sum.elim_inl, Sum.elim_inr, add_zero]
  · have := abs_cst_lt_bound p' p'' a b' h
    calc |p'' b' - p' a - h.cst| ≤ |p'' b'| + |p' a| + |h.cst| := by
          have := abs_sub (p'' b' - p' a) h.cst
          have := abs_sub (p'' b') (p' a)
          linarith
      _ < _ := by linarith
  · have := abs_cst_lt_bound p' p'' a' b h
    calc |p' a' - p'' b - h.cst| ≤ |p' a'| + |p'' b| + |h.cst| := by
          have := abs_sub (p' a' - p'' b) h.cst
          have := abs_sub (p' a') (p'' b)
          linarith
      _ < _ := by linarith

omit [DecidableEq I] in
/-- A cross hyperplane takes nonzero values of opposite signs at separations `c` and `-c`, for
`c ≥ bound`. -/
theorem val_juxt_neg_of_isCross (p' : Strand ν' → 𝕜) (p'' : Strand ν'' → 𝕜) {c : 𝕜}
    (hc : bound Γ p' p'' ≤ c) {h : Hyp Γ (ν' + ν'')} (hh : IsCross h) :
    h.val (juxt p' p'' (-c)) ≠ 0 ∧
      (0 < h.val (juxt p' p'' (-c)) ↔ ¬ 0 < h.val (juxt p' p'' c)) := by
  have hb := abs_val_juxt_zero_lt p' p'' hh
  have h1 := neg_abs_le (h.val (juxt p' p'' 0))
  have h2 := le_abs_self (h.val (juxt p' p'' 0))
  rw [val_juxt p' p'' (-c), val_juxt p' p'' c]
  unfold IsCross at hh
  rcases hlo : IsRight h.lo <;> rcases hhi : IsRight h.hi <;> rw [hlo, hhi] at hh <;>
    simp only [ne_eq, not_true_eq_false] at hh <;>
    simp only [Bool.false_eq_true, ↓reduceIte, sub_zero, zero_sub]
  · refine ⟨by linarith, ?_⟩
    constructor <;> intro _ <;> linarith
  · refine ⟨by linarith, ?_⟩
    constructor <;> intro _ <;> linarith

omit [DecidableEq I] in
theorem isGeneric_juxt_neg {p' : Strand ν' → 𝕜} {p'' : Strand ν'' → 𝕜} (hp' : IsGeneric Γ p')
    (hp'' : IsGeneric Γ p'') {c : 𝕜} (hc : bound Γ p' p'' ≤ c) :
    IsGeneric Γ (juxt p' p'' (-c)) := by
  intro h
  by_cases hh : IsCross h
  · exact (val_juxt_neg_of_isCross p' p'' hc hh).1
  · rw [val_juxt_of_not_isCross p' p'' (-c) c hh]
    exact isGeneric_juxt hp' hp'' hc h

/-- The chamber of `ν' + ν''` with a configuration of `C''` far to the left of a configuration
of `C'`: the target of the diagram exchanging the two blocks of strands. -/
noncomputable def swapChamber (C' : FullChamber Γ ν') (C'' : FullChamber Γ ν'') :
    FullChamber Γ (ν' + ν'') :=
  .ofPoint (juxt (point C') (point C'') (-bound Γ (point C') (point C'')))
    (isGeneric_juxt_neg (isGeneric_point C') (isGeneric_point C'') le_rfl)

omit [DecidableEq I] in
/-- The juxtaposed chamber `C' ∘ C''` and the exchanged chamber differ exactly on the cross
hyperplanes. -/
theorem swapChamber_ne_iff (C' : FullChamber Γ ν') (C'' : FullChamber Γ ν'')
    (h : Hyp Γ (ν' + ν'')) : (chamber C' C'').1 h ≠ (swapChamber C' C'').1 h ↔ IsCross h := by
  show fullSigns _ h ≠ fullSigns _ h ↔ _
  by_cases hh : IsCross h
  · refine iff_of_true ?_ hh
    have := (val_juxt_neg_of_isCross (point C') (point C'') le_rfl hh).2
    simp only [fullSigns, ne_eq, decide_eq_decide]
    tauto
  · refine iff_of_false ?_ hh
    simp only [fullSigns, ne_eq, not_not]
    rw [val_juxt_of_not_isCross (point C') (point C'') _ (-bound Γ (point C') (point C'')) hh]

omit [DecidableEq I] in
@[simp] theorem label_inlStrand (a : Strand ν') : (inlStrand ν' ν'' a).label = a.label := rfl

omit [DecidableEq I] in
@[simp] theorem label_inrStrand (b : Strand ν'') : (inrStrand ν' ν'' b).label = b.label := rfl

omit [DecidableEq I] in
theorem sum_strand {M : Type*} [AddCommMonoid M] (g : Strand (ν' + ν'') → M) :
    ∑ t, g t = ∑ a, g (inlStrand ν' ν'' a) + ∑ b, g (inrStrand ν' ν'' b) := by
  rw [← (strandEquiv ν' ν'').sum_comp, Fintype.sum_sum_type]
  rfl

omit [DecidableEq I] in
theorem inlStrand_fst_eq_iff (a : Strand ν') (b : Strand ν'') :
    (inlStrand ν' ν'' a).1 = (inrStrand ν' ν'' b).1 ↔ a.label = b.label := by
  rw [Subtype.ext_iff]
  rfl

omit [DecidableEq I] in
theorem diag_inl_inr_iff (a : Strand ν') (b : Strand ν'') :
    ((inlStrand ν' ν'' a).1 = (inrStrand ν' ν'' b).1 ∧
      (inlStrand ν' ν'' a).2.val < (inrStrand ν' ν'' b).2.val) ↔ a.label = b.label := by
  rw [inlStrand_fst_eq_iff]
  refine ⟨And.left, fun h => ⟨h, ?_⟩⟩
  show a.2.val < ν' (b.1 : I) + b.2.val
  have : ν' (a.1 : I) = ν' (b.1 : I) := by
    have h' : (a.1 : I) = (b.1 : I) := h
    rw [h']
  have := a.2.2
  omega

omit [DecidableEq I] in
theorem not_diag_inr_inl (a : Strand ν') (b : Strand ν'') :
    ¬ ((inrStrand ν' ν'' b).1 = (inlStrand ν' ν'' a).1 ∧
      (inrStrand ν' ν'' b).2.val < (inlStrand ν' ν'' a).2.val) := by
  rintro ⟨h, hr⟩
  have h' : (b.1 : I) = (a.1 : I) := congrArg Subtype.val h
  have : ν' (a.1 : I) = ν' (b.1 : I) := by rw [h']
  have hr' : ν' (b.1 : I) + b.2.val < a.2.val := hr
  have := a.2.2
  omega

variable (G : GradingDatum Γ)

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem sum_wall_isCross :
    ∑ w : Wall Γ (ν' + ν''), (if IsCross (Sum.inl w : Hyp Γ (ν' + ν'')) then G.wall w.edge else 0)
      = ∑ e, ∑ a : Strand ν', ∑ b : Strand ν'',
        ((if a.label = Γ.head e ∧ b.label = Γ.tail e then G.wall e else 0) +
          if b.label = Γ.head e ∧ a.label = Γ.tail e then G.wall e else 0) := by
  let F : Γ.E × Strand (ν' + ν'') × Strand (ν' + ν'') → ℤ := fun x =>
    if IsRight x.2.1 ≠ IsRight x.2.2 then G.wall x.1 else 0
  have h1 : ∑ w : Wall Γ (ν' + ν''),
      (if IsCross (Sum.inl w : Hyp Γ (ν' + ν'')) then G.wall w.edge else 0) =
      ∑ w : Wall Γ (ν' + ν''), F w.1 := rfl
  have h2 : ∑ w : Wall Γ (ν' + ν''), F w.1 = ∑ x ∈ Finset.univ.filter (fun x :
      Γ.E × Strand (ν' + ν'') × Strand (ν' + ν'') =>
        x.2.1.label = Γ.head x.1 ∧ x.2.2.label = Γ.tail x.1 ∧ x.2.1 ≠ x.2.2), F x :=
    (Finset.sum_subtype (F := (inferInstance : Fintype (Wall Γ (ν' + ν'')))) _
      (fun x => by simp) F).symm
  rw [h1, h2, Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Fintype.sum_prod_type, sum_strand]
  simp only [sum_strand, F, isRight_inl, isRight_inr, label_inlStrand, label_inrStrand,
    ne_eq, not_true_eq_false, Bool.false_eq_true, not_false_eq_true, ite_false, ite_true,
    Bool.true_eq_false, ite_self, Finset.sum_const_zero, zero_add, add_zero,
    inlStrand_ne_inrStrand, (inlStrand_ne_inrStrand _ _ _ _).symm, and_true,
    Finset.sum_add_distrib]
  exact congrArg₂ _ rfl Finset.sum_comm

omit [DecidableEq I] in
@[simp] theorem coe_inlStrand_fst (a : Strand ν') :
    ((inlStrand ν' ν'' a).1 : I) = a.label := rfl

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem sum_diag_isCross :
    ∑ d : Diag (ν' + ν''),
        (if IsCross (Sum.inr d : Hyp Γ (ν' + ν'')) then G.cross d.fst.1 else 0)
      = ∑ a : Strand ν', ∑ b : Strand ν'', if a.label = b.label then G.cross a.label else 0 := by
  let F : Strand (ν' + ν'') × Strand (ν' + ν'') → ℤ := fun x =>
    if IsRight x.1 ≠ IsRight x.2 then G.cross x.1.1 else 0
  have h1 : ∑ d : Diag (ν' + ν''),
      (if IsCross (Sum.inr d : Hyp Γ (ν' + ν'')) then G.cross d.fst.1 else 0) =
      ∑ d : Diag (ν' + ν''), F d.1 := rfl
  have h2 : ∑ d : Diag (ν' + ν''), F d.1 = ∑ x ∈ Finset.univ.filter (fun x :
      Strand (ν' + ν'') × Strand (ν' + ν'') => x.1.1 = x.2.1 ∧ x.1.2.val < x.2.2.val), F x :=
    (Finset.sum_subtype (F := (inferInstance : Fintype (Diag (ν' + ν'')))) _
      (fun x => by simp) F).symm
  rw [h1, h2, Finset.sum_filter, Fintype.sum_prod_type, sum_strand]
  simp only [sum_strand, F, isRight_inl, isRight_inr, coe_inlStrand_fst,
    ne_eq, not_true_eq_false, Bool.false_eq_true, not_false_eq_true, ite_false, ite_true,
    Bool.true_eq_false, ite_self, Finset.sum_const_zero, zero_add, add_zero, diag_inl_inr_iff,
    not_diag_inr_inl]

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- The cross hyperplanes have total degree `∑_{a ∈ ν', b ∈ ν''} pairDeg (label a) (label b)`. -/
theorem sum_cross_hypDeg :
    ∑ h ∈ Finset.univ.filter (IsCross (Γ := Γ) (ν' := ν') (ν'' := ν'')), G.hypDeg h =
      ∑ a : Strand ν', ∑ b : Strand ν'', G.pairDeg a.label b.label := by
  rw [Finset.sum_filter, Fintype.sum_sum_type]
  rw [show (∑ w : Wall Γ (ν' + ν''), if IsCross (Sum.inl w : Hyp Γ (ν' + ν''))
      then G.hypDeg (Sum.inl w) else 0) = _ from sum_wall_isCross G,
    show (∑ d : Diag (ν' + ν''), if IsCross (Sum.inr d : Hyp Γ (ν' + ν''))
      then G.hypDeg (Sum.inr d) else 0) = _ from sum_diag_isCross G]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [GradingDatum.pairDeg, Finset.sum_add_distrib]

/-- **Degree of the exchange of two blocks of strands.** The straight gallery from the
juxtaposition `C' ∘ C''` to the chamber in which the block `C''` lies to the left of `C'` has
degree `∑_{a ∈ ν', b ∈ ν''} pairDeg (label a) (label b)`, for any chamber segment between
them. -/
theorem segDeg_chamber_swapChamber
    (P : FullChamber Γ (ν' + ν'') → FullChamber Γ (ν' + ν'') →
      (Strand (ν' + ν'') → 𝕜) × (Strand (ν' + ν'') → 𝕜))
    {C' : FullChamber Γ ν'} {C'' : FullChamber Γ ν''}
    (hP : IsChamberSegment (chamber C' C'') (swapChamber C' C'')
      (P (chamber C' C'') (swapChamber C' C''))) :
    G.segDeg P (chamber C' C'') (swapChamber C' C'') =
      ∑ a : Strand ν', ∑ b : Strand ν'', G.pairDeg a.label b.label := by
  rw [G.segDeg_eq_sum P hP, ← sum_cross_hypDeg G]
  exact Finset.sum_congr (Finset.filter_congr fun h _ => swapChamber_ne_iff C' C'' h)
    fun _ _ => rfl

/-- The gallery in the other direction has the same degree. -/
theorem segDeg_swapChamber_chamber
    (P : FullChamber Γ (ν' + ν'') → FullChamber Γ (ν' + ν'') →
      (Strand (ν' + ν'') → 𝕜) × (Strand (ν' + ν'') → 𝕜))
    {C' : FullChamber Γ ν'} {C'' : FullChamber Γ ν''}
    (hP : IsChamberSegment (swapChamber C' C'') (chamber C' C'')
      (P (swapChamber C' C'') (chamber C' C''))) :
    G.segDeg P (swapChamber C' C'') (chamber C' C'') =
      ∑ a : Strand ν', ∑ b : Strand ν'', G.pairDeg a.label b.label := by
  rw [G.segDeg_eq_sum P hP, ← sum_cross_hypDeg G]
  exact Finset.sum_congr (Finset.filter_congr fun h _ => by
    rw [ne_comm]; exact swapChamber_ne_iff C' C'' h) fun _ _ => rfl

end Juxtapose

end Categorification.WeightedKLR

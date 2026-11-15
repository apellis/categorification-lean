/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.GalleryBasis.Corner

/-!
# Equivalence classes of loadings are connected components

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2, subsection
"Dependence on choice of loadings", Proposition 2.12.

Over `ℝ`, the configurations of weight `ν` that are increasing on the strands of each colour
form the product `D_{v_1} × ⋯ × D_{v_m}` of dominant cones (`dominantCone`). Removing the walls
`H_{e,a,b} = {x_b - x_a = ϑ_e}` (an edge `e`, a strand `a` coloured `h(e)` and a strand `b ≠ a`
coloured `t(e)`) leaves the open set `wallComplement Γ ν`. Proposition 2.12 states that the
equivalence classes of loadings (Definition 2.9, `Loading.Equiv`; the classes are the chambers
`Chamber Γ ν`, `Loading.chamber_eq_iff`) are exactly the connected components of this set.

The walls `x_a - x_a = ϑ_e` of a loop `e` at a single strand are not walls here (`Wall` asks
for `a ≠ b`): for `ϑ_e ≠ 0` (`WeightedGraph.NoZeroLoops`) such a hyperplane is empty, so nothing
is lost. The wall complement contains configurations where two strands of different colours
coincide; Webster's loadings are injective (`Loading`), and every component contains one
(`exists_loading_mem_connectedComponentIn`).

## Main results

* `mem_connectedComponentIn_wallComplement_iff`: two points of the wall complement lie in the
  same component iff they lie on the same side of every wall.
* `Loading.equiv_iff_mem_connectedComponentIn`: two loadings are equivalent iff they lie in the
  same connected component of the wall complement.
* `exists_loading_mem_connectedComponentIn`: every component contains a loading.
* `chamberComponentEquiv`: Proposition 2.12, the bijection between equivalence classes of
  loadings (chambers) and connected components of the wall complement.
-/

namespace Categorification.WeightedKLR

open Set

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {Γ : WeightedGraph I ℝ k}
  {ν : I →₀ ℕ}

variable (ν) in
/-- The product `D_{v_1} × ⋯ × D_{v_m}` of dominant cones: configurations increasing on the
strands of each colour. -/
def dominantCone : Set (Strand ν → ℝ) :=
  {p | ∀ s t : Strand ν, s.1 = t.1 → s.2.val < t.2.val → p s < p t}

variable (Γ ν) in
/-- The complement in `D_{v_1} × ⋯ × D_{v_m}` of the walls `H_{e,a,b} = {x_b - x_a = ϑ_e}`. -/
def wallComplement : Set (Strand ν → ℝ) :=
  {p | p ∈ dominantCone ν ∧ ∀ w : Wall Γ ν, w.val p ≠ 0}

omit [DecidableEq I] in
theorem Loading.pos_mem_wallComplement (B : Loading Γ ν) : B.pos ∈ wallComplement Γ ν :=
  ⟨B.admissible.2.1, B.admissible.2.2⟩

omit [DecidableEq I] in
theorem Wall.val_lineMap (w : Wall Γ ν) (p q : Strand ν → ℝ) (t : ℝ) :
    w.val ((1 - t) • p + t • q) = (1 - t) * w.val p + t * w.val q := by
  simp only [Wall.val, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

omit [DecidableEq I] in
theorem Wall.continuous_val (w : Wall Γ ν) : Continuous (w.val (Γ := Γ)) := by
  unfold Wall.val
  fun_prop

omit [DecidableEq I] in
/-- The segment between two points of the wall complement on the same side of every wall lies in
the wall complement. -/
theorem segment_subset_wallComplement {p q : Strand ν → ℝ} (hp : p ∈ wallComplement Γ ν)
    (hq : q ∈ wallComplement Γ ν) (h : ∀ w : Wall Γ ν, (0 < w.val p ↔ 0 < w.val q)) :
    segment ℝ p q ⊆ wallComplement Γ ν := by
  rintro x ⟨a, b, ha, hb, hab, rfl⟩
  obtain rfl : a = 1 - b := by linarith
  refine ⟨fun s t h₁ h₂ => ?_, fun w => ?_⟩
  · have h₁' := hp.1 s t h₁ h₂
    have h₂' := hq.1 s t h₁ h₂
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases eq_or_lt_of_le hb with hb0 | hb0
    · subst hb0; simpa using h₁'
    · nlinarith
  · rw [Wall.val_lineMap]
    have hwp := hp.2 w
    have hwq := hq.2 w
    rcases lt_or_gt_of_ne hwp with hn | hn
    · have hqn : w.val q < 0 := lt_of_le_of_ne (not_lt.1 fun h' => absurd ((h w).2 h') hn.not_gt) hwq
      rcases eq_or_lt_of_le hb with hb0 | hb0
      · subst hb0; simpa using hwp
      · nlinarith
    · have hqn : 0 < w.val q := (h w).1 hn
      rcases eq_or_lt_of_le hb with hb0 | hb0
      · subst hb0; simpa using hwp
      · nlinarith

omit [DecidableEq I] in
/-- Two points of the wall complement lie in the same connected component iff they lie on the
same side of every wall. -/
theorem mem_connectedComponentIn_wallComplement_iff {p q : Strand ν → ℝ}
    (hp : p ∈ wallComplement Γ ν) (hq : q ∈ wallComplement Γ ν) :
    q ∈ connectedComponentIn (wallComplement Γ ν) p ↔
      ∀ w : Wall Γ ν, (0 < w.val p ↔ 0 < w.val q) := by
  constructor
  · intro hC w
    set C := connectedComponentIn (wallComplement Γ ν) p
    have hpC : p ∈ C := mem_connectedComponentIn hp
    have hCU : C ⊆ wallComplement Γ ν := connectedComponentIn_subset _ _
    have hpre : IsPreconnected C := isPreconnected_connectedComponentIn
    have hf : ContinuousOn (w.val (Γ := Γ)) C := w.continuous_val.continuousOn
    have no_zero : ∀ a ∈ C, ∀ b ∈ C, w.val a < 0 → 0 < w.val b → False := by
      intro a ha b hb ha' hb'
      obtain ⟨x, hx, hx0⟩ := hpre.intermediate_value ha hb hf ⟨ha'.le, hb'.le⟩
      exact (hCU hx).2 w hx0
    constructor
    · intro h'
      rcases lt_or_gt_of_ne (hq.2 w) with hn | hn
      · exact (no_zero q hC p hpC hn h').elim
      · exact hn
    · intro h'
      rcases lt_or_gt_of_ne (hp.2 w) with hn | hn
      · exact (no_zero p hpC q hC hn h').elim
      · exact hn
  · intro h
    exact ((convex_segment p q).isPreconnected.subset_connectedComponentIn
      (left_mem_segment ℝ p q) (segment_subset_wallComplement hp hq h))
      (right_mem_segment ℝ p q)

omit [DecidableEq I] in
/-- Two loadings are equivalent iff they lie in the same connected component of the wall
complement. -/
theorem Loading.equiv_iff_mem_connectedComponentIn (B B' : Loading Γ ν) :
    B.Equiv B' ↔ B'.pos ∈ connectedComponentIn (wallComplement Γ ν) B.pos :=
  (mem_connectedComponentIn_wallComplement_iff B.pos_mem_wallComplement
    B'.pos_mem_wallComplement).symm

/-- Every connected component of the wall complement contains a loading. -/
theorem exists_loading_mem_connectedComponentIn {p : Strand ν → ℝ}
    (hp : p ∈ wallComplement Γ ν) :
    ∃ B : Loading Γ ν, B.pos ∈ connectedComponentIn (wallComplement Γ ν) p := by
  have hgen : IsGeneric Γ p := by
    rintro (w | d)
    · exact hp.2 w
    · simp only [Hyp.val_inr, Diag.val]
      exact sub_ne_zero.2 (ne_of_gt (hp.1 _ _ d.2.1 d.2.2))
  have hrank : (FullChamber.ofPoint p hgen).IsRankOrdered := fun d => by
    simp only [FullChamber.ofPoint, fullSigns, Hyp.val_inr, Diag.val, decide_eq_true_eq,
      sub_pos]
    exact hp.1 _ _ d.2.1 d.2.2
  obtain ⟨c, hc⟩ := Chamber.exists_toFull_eq _ hrank
  obtain ⟨q, hq, hs⟩ := c.2
  refine ⟨⟨q, hq⟩, (mem_connectedComponentIn_wallComplement_iff hp ⟨hq.2.1, hq.2.2⟩).2 ?_⟩
  intro w
  have h1 := congrArg (fun C : FullChamber Γ ν => C.1 (.inl w)) hc
  simp only [Chamber.toFull, FullChamber.ofPoint, fullSigns, Hyp.val_inl] at h1
  rw [← hs] at h1
  simp only [signs] at h1
  exact decide_eq_decide.1 h1.symm

variable (Γ ν) in
/-- The connected components of the wall complement. -/
def WallComponent : Type _ :=
  {S : Set (Strand ν → ℝ) // ∃ p ∈ wallComplement Γ ν, connectedComponentIn (wallComplement Γ ν) p = S}

/-- A loading of a chamber. -/
noncomputable def Chamber.loading (c : Chamber Γ ν) : Loading Γ ν :=
  ⟨c.2.choose, c.2.choose_spec.1⟩

omit [DecidableEq I] in
theorem Chamber.loading_chamber (c : Chamber Γ ν) : c.loading.chamber = c :=
  Subtype.ext c.2.choose_spec.2

variable (Γ ν) in
/-- Webster, arXiv:1209.2463v4, Proposition 2.12: the equivalence classes of loadings (the
chambers) correspond bijectively to the connected components of the complement in
`D_{v_1} × ⋯ × D_{v_m}` of the walls; the class of a loading `B` goes to the component
containing `B`. -/
noncomputable def chamberComponentEquiv : Chamber Γ ν ≃ WallComponent Γ ν :=
  Equiv.ofBijective
    (fun c => ⟨connectedComponentIn (wallComplement Γ ν) c.loading.pos,
      c.loading.pos, c.loading.pos_mem_wallComplement, rfl⟩)
    (by
      constructor
      · intro c c' h
        have h' := congrArg Subtype.val h
        simp only at h'
        have hm : c'.loading.pos ∈ connectedComponentIn (wallComplement Γ ν) c.loading.pos := by
          rw [h']; exact mem_connectedComponentIn c'.loading.pos_mem_wallComplement
        rw [← c.loading_chamber, ← c'.loading_chamber, Loading.chamber_eq_iff]
        exact (Loading.equiv_iff_mem_connectedComponentIn _ _).2 hm
      · rintro ⟨S, p, hp, rfl⟩
        obtain ⟨B, hB⟩ := exists_loading_mem_connectedComponentIn hp
        refine ⟨B.chamber, Subtype.ext ?_⟩
        simp only
        have hB' : B.chamber.loading.pos ∈ connectedComponentIn (wallComplement Γ ν) B.pos :=
          (Loading.equiv_iff_mem_connectedComponentIn _ _).1
            ((Loading.chamber_eq_iff _ _).1 B.chamber.loading_chamber.symm)
        rw [← connectedComponentIn_eq hB', connectedComponentIn_eq hB])

theorem chamberComponentEquiv_loading (B : Loading Γ ν) :
    B.pos ∈ ((chamberComponentEquiv Γ ν B.chamber).1 : Set (Strand ν → ℝ)) := by
  show B.pos ∈ connectedComponentIn (wallComplement Γ ν) B.chamber.loading.pos
  exact (Loading.equiv_iff_mem_connectedComponentIn _ _).1
    ((Loading.chamber_eq_iff _ _).1 B.chamber.loading_chamber)

end Categorification.WeightedKLR

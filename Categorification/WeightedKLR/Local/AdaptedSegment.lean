/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Local.Star

/-!
# Simple segments adapted to a local chamber argument

Supporting geometry for the local-chart proof of Webster,
*Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.4,
Theorem 2.19, roadmap A. The segment basis of Theorem 2.8 can be chosen
subject to finitely many strict affine conditions on an interior point of
the segment. These lemmas prove the required perturbation statements over
an arbitrary ordered field; they are not statements printed in the source.
-/

namespace Categorification.WeightedKLR.Segment

variable {ι 𝕜 H : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [Fintype H] [DecidableEq H] {f : H → (ι → 𝕜) →ᵃ[𝕜] 𝕜}

omit [DecidableEq H] in
/-- Perturb the right endpoint to obtain a simple segment, preserving arbitrary
finitely many strict affine signs, while making a prescribed point of the
segment generic. This supports the adapted basis choice in the local route
to Webster arXiv:1209.2463v4, Theorem 2.19, using the basis of Theorem 2.8. -/
theorem exists_simple_preserving_affine
    (hdist : ∀ h g, h ≠ g → ∃ x, f h x = 0 ∧ f g x ≠ 0)
    {p q : ι → 𝕜} (hp : Generic f p) (hq : Generic f q)
    {κ : Type*} [Fintype κ] (g : κ → (ι → 𝕜) →ᵃ[𝕜] 𝕜)
    (hg : ∀ j, g j q ≠ 0) (t : 𝕜) :
    ∃ q', Simple f p q' ∧ signs f q' = signs f q ∧
      (∀ j, 0 < g j q * g j q') ∧ Generic f (segPt p q' t) := by
  classical
  let fs : H ⊕ κ → (ι → 𝕜) →ᵃ[𝕜] 𝕜 := Sum.elim f g
  let pairs : Set ((ι → 𝕜) →ᵃ[𝕜] 𝕜) :=
    Set.range fun x : {x : H × H // x.1 ≠ x.2} => pairFun f p x.1.1 x.1.2
  let middle : Set ((ι → 𝕜) →ᵃ[𝕜] 𝕜) :=
    Set.range fun h : H => (f h).comp (AffineMap.homothety p t)
  obtain ⟨q', hsign, havoid⟩ := exists_perturb fs q
    (fun j => by cases j with | inl h => exact hq h | inr j => exact hg j)
    (pairs ∪ middle) ((Set.finite_range _).union (Set.finite_range _)) (by
      intro ℓ hℓ
      rcases hℓ with hℓ | hℓ
      · obtain ⟨x, rfl⟩ := hℓ
        exact pairFun_ne_zero hdist hp x.2
      · obtain ⟨h, rfl⟩ := hℓ
        exact ⟨p, by simpa using hp h⟩)
  have hq' : Generic f q' := fun h he => by
    have hs := hsign (Sum.inl h)
    change 0 < f h q * f h q' at hs
    simp [he] at hs
  refine ⟨q', simple_of_pairFun hp hq' (fun h h' hne =>
    havoid _ (Or.inl ⟨⟨(h, h'), hne⟩, rfl⟩)), ?_, ?_, ?_⟩
  · funext h
    simp only [signs]
    exact decide_eq_decide.2 (pos_iff_of_mul_pos (hsign (Sum.inl h))).symm
  · intro j
    exact hsign (Sum.inr j)
  · intro h
    have hav := havoid _ (Or.inr ⟨h, rfl⟩)
    simpa [AffineMap.comp_apply, AffineMap.homothety_apply, segPt,
      vsub_eq_sub, vadd_eq_add, add_comm] using hav

end Categorification.WeightedKLR.Segment

namespace Categorification.WeightedKLR.Segment

variable {ι 𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- The affine map moving toward its argument is the segment parametrization. -/
theorem homothety_apply_eq_segPt (p q : ι → 𝕜) (t : 𝕜) :
    AffineMap.homothety p t q = segPt p q t := by
  simp [AffineMap.homothety_apply, segPt, vsub_eq_sub, vadd_eq_add, add_comm]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Simultaneously moving both endpoints interpolates their midpoint. -/
theorem segPt_midpoint_segPt (x y p q : ι → 𝕜) (t : 𝕜) :
    segPt (segPt x p t) (segPt y q t) (1 / 2 : 𝕜) =
      segPt (segPt x y (1 / 2 : 𝕜)) (segPt p q (1 / 2 : 𝕜)) t := by
  ext i
  simp only [segPt, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

end Categorification.WeightedKLR.Segment

namespace Categorification.WeightedKLR

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}
  {ν : I →₀ ℕ}

open Segment

/-- Choose a simple segment between prescribed chambers while preserving any
finitely many strict affine signs at the midpoint of incident configurations.
Its midpoint is generic. This is the adapted-basis perturbation for the local
route to Webster arXiv:1209.2463v4, §2.4, Theorem 2.19 (A), based on Theorem 2.8. -/
theorem exists_simple_incident_preserving_midpoint
    (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) {C D : FullChamber Γ ν}
    {x y : Strand ν → 𝕜} (hx : C.Incident x) (hy : D.Incident y)
    {κ : Type*} [Fintype κ] (g : κ → (Strand ν → 𝕜) →ᵃ[𝕜] 𝕜)
    (hg : ∀ j, g j (segPt x y (1 / 2 : 𝕜)) ≠ 0) :
    ∃ p q, Simple (hypAff (Γ := Γ)) p q ∧ fullSigns p = C.1 ∧ fullSigns q = D.1 ∧
      IsGeneric Γ (segPt p q (1 / 2 : 𝕜)) ∧
      ∀ j, 0 < g j (segPt x y (1 / 2 : 𝕜)) * g j (segPt p q (1 / 2 : 𝕜)) := by
  classical
  obtain ⟨p₀, hp₀, hC⟩ := C.2
  obtain ⟨q₀, hq₀, hE⟩ := D.2
  obtain ⟨δ, hδ, hsmall⟩ := Segment.exists_pos_small Finset.univ
    (fun j => g j (segPt x y (1 / 2 : 𝕜)))
    (fun j => g j (segPt p₀ q₀ (1 / 2 : 𝕜)) - g j (segPt x y (1 / 2 : 𝕜)))
    (fun j _ => hg j)
  let t := min δ 1 / 2
  have ht0 : 0 < t := div_pos (lt_min hδ zero_lt_one) (by norm_num)
  have htδ : t < δ := by
    have := min_le_left δ 1
    dsimp [t]
    linarith
  have ht1 : t ≤ 1 := by
    have := min_le_right δ 1
    dsimp [t]
    linarith
  let p := segPt x p₀ t
  let q := segPt y q₀ t
  have hp := hx.generic_segPt hp₀ hC ht0 ht1
  have hq := hy.generic_segPt hq₀ hE ht0 ht1
  have hmid : ∀ j, 0 < g j (segPt x y (1 / 2 : 𝕜)) *
      g j (segPt p q (1 / 2 : 𝕜)) := by
    intro j
    dsimp only [p, q]
    rw [segPt_midpoint_segPt, apply_segPt (f := g) j
      (segPt x y (1 / 2 : 𝕜)) (segPt p₀ q₀ (1 / 2 : 𝕜)) t]
    exact hsmall t ht0.le htδ j (Finset.mem_univ j)
  let gm : κ → (Strand ν → 𝕜) →ᵃ[𝕜] 𝕜 :=
    fun j => (g j).comp (AffineMap.homothety p (1 / 2 : 𝕜))
  have hgm : ∀ j, gm j q ≠ 0 := by
    intro j
    change g j (AffineMap.homothety p (1 / 2 : 𝕜) q) ≠ 0
    rw [homothety_apply_eq_segPt]
    exact right_ne_zero_of_mul (ne_of_gt (hmid j))
  obtain ⟨q', hs, hq', hsign, hgen⟩ := exists_simple_preserving_affine
    (hdist hD hZ) hp.1 hq.1 gm hgm (1 / 2 : 𝕜)
  refine ⟨p, q', hs, hp.2, hq'.trans hq.2, hgen, fun j => ?_⟩
  have hsecond : 0 < g j (segPt p q (1 / 2 : 𝕜)) *
      g j (segPt p q' (1 / 2 : 𝕜)) := by
    simpa only [gm, AffineMap.comp_apply, homothety_apply_eq_segPt] using hsign j
  exact mul_pos_of_pos_iff (hg j) (right_ne_zero_of_mul (ne_of_gt hsecond))
    ((pos_iff_of_mul_pos (hmid j)).trans (pos_iff_of_mul_pos hsecond))

end Categorification.WeightedKLR

namespace Categorification.WeightedKLR

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}
  {ν : I →₀ ℕ}

open Segment

/-- A midpoint outside a collection of closed chambers can be preserved while
choosing a simple segment between incident chambers, with generic midpoint.
This is the segment choice used to eliminate unsupported basis galleries in
the local route to Webster arXiv:1209.2463v4, §2.4, Theorem 2.19 (A). -/
theorem exists_simple_incident_midpoint_outside
    (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) {C D : FullChamber Γ ν}
    {x y : Strand ν → 𝕜} (hx : C.Incident x) (hy : D.Incident y)
    (K : Set (FullChamber Γ ν))
    (hout : ∀ E ∈ K, ¬E.Incident (segPt x y (1 / 2 : 𝕜))) :
    ∃ p q, Simple (hypAff (Γ := Γ)) p q ∧ fullSigns p = C.1 ∧ fullSigns q = D.1 ∧
      IsGeneric Γ (segPt p q (1 / 2 : 𝕜)) ∧
      ∀ E ∈ K, ¬E.Incident (segPt p q (1 / 2 : 𝕜)) := by
  classical
  let _ := Fintype.ofFinite K
  have hw : ∀ E : K, ∃ h : Hyp Γ ν,
      if E.1.1 h then h.val (segPt x y (1 / 2 : 𝕜)) < 0
      else 0 < h.val (segPt x y (1 / 2 : 𝕜)) := by
    intro E
    have hE := hout E.1 E.2
    change ¬∀ h : Hyp Γ ν, _ at hE
    obtain ⟨h, hh⟩ := not_forall.1 hE
    refine ⟨h, ?_⟩
    cases hs : E.1.1 h <;>
      simp only [hs, Bool.false_eq_true, ite_false, ite_true] at hh ⊢
    · exact lt_of_not_ge hh
    · exact lt_of_not_ge hh
  let wall : K → Hyp Γ ν := fun E => (hw E).choose
  let g : K → (Strand ν → 𝕜) →ᵃ[𝕜] 𝕜 := fun E =>
    if E.1.1 (wall E) then -(hypAff (wall E)) else hypAff (wall E)
  have hg : ∀ E, 0 < g E (segPt x y (1 / 2 : 𝕜)) := by
    intro E
    have hh := (hw E).choose_spec
    change (if E.1.1 (wall E) then _ else _) at hh
    cases hs : E.1.1 (wall E) <;>
      simp only [g, hs, Bool.false_eq_true, ite_false, ite_true, AffineMap.coe_neg, Pi.neg_apply] at hh ⊢
    · exact hh
    · exact neg_pos.2 hh
  obtain ⟨p, q, hs, hp, hq, hgen, hsign⟩ := exists_simple_incident_preserving_midpoint
    hD hZ hx hy g (fun E => ne_of_gt (hg E))
  refine ⟨p, q, hs, hp, hq, hgen, fun E hE hinc => ?_⟩
  let E' : K := ⟨E, hE⟩
  have hpos := (pos_iff_of_mul_pos (hsign E')).1 (hg E')
  have hweak := hinc (wall E')
  cases ht : E.1 (wall E') <;>
    simp only [g, E', ht, Bool.false_eq_true, ite_false, ite_true,
      AffineMap.coe_neg, Pi.neg_apply] at hpos hweak
  · exact (not_lt_of_ge hweak) hpos
  · exact (not_lt_of_ge hweak) (neg_pos.1 hpos)

end Categorification.WeightedKLR

namespace Categorification.WeightedKLR.Segment

variable {H 𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
private theorem exists_take_lt (w : List H) (time : H → 𝕜) (t : 𝕜)
    (hw : w.Pairwise (fun h g => time h < time g)) :
    ∃ j : ℕ, ∀ h, h ∈ w.take j ↔ h ∈ w ∧ time h < t := by
  induction w with
  | nil => exact ⟨0, by simp⟩
  | cons a w ih =>
    obtain ⟨ha, hw⟩ := List.pairwise_cons.1 hw
    by_cases hat : time a < t
    · obtain ⟨j, hj⟩ := ih hw
      refine ⟨j + 1, fun h => ?_⟩
      by_cases hha : h = a
      · subst h
        simp [List.take_succ_cons, hat]
      · simpa [List.take_succ_cons, hha] using hj h
    · refine ⟨0, fun h => ?_⟩
      simp only [List.take_zero, List.not_mem_nil, false_iff, not_and]
      intro hh ht
      rcases List.mem_cons.1 hh with rfl | hh
      · exact hat ht
      · exact hat ((ha h hh).trans ht)

variable {ι : Type*} [Fintype H] [DecidableEq H]
  {f : H → (ι → 𝕜) →ᵃ[𝕜] 𝕜}

/-- A generic interior point of a simple segment is the chamber of a prefix of
its crossing word. This lets the adapted basis gallery factor through the
unsupported midpoint chamber (Webster Theorem 2.19, local route A). -/
theorem exists_prefix_of_generic_segPt {p q : ι → 𝕜} (hs : Simple f p q)
    {t : 𝕜} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hgen : Generic f (segPt p q t)) :
    ∃ j : ℕ, signs f (segPt p q t) = flipSigns (signs f p) ((word f p q).take j) := by
  have hne : ∀ h, Separates f p q h → crossTime f p q h ≠ t := by
    intro h hh he
    have hz := apply_segPt_crossTime (ne_of_separates hh)
    rw [he] at hz
    exact hgen h hz
  obtain ⟨_, hsign⟩ := signs_segPt hs.1 hs.2.1 ht0 ht1 hne
  obtain ⟨j, hj⟩ := exists_take_lt (word f p q) (crossTime f p q) t (pairwise_word hs)
  refine ⟨j, funext fun h => ?_⟩
  rw [hsign h, flipSigns]
  congr 1
  exact decide_eq_decide.2 (by rw [hj h, mem_word])

end Categorification.WeightedKLR.Segment

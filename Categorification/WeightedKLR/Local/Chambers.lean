/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Local.Star
import Categorification.WeightedKLR.Local.Hyperplanes

/-!
# Chambers of a local linearization

The local-chart argument for roadmap A of Webster,
*Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4,
Theorem 2.19, uses the chambers incident to a configuration. They are the
chambers of the central arrangement formed by the hyperplanes through that
configuration. This file proves that identification over the ordered position
field; it uses neither completeness nor a change of coefficient field.
-/

noncomputable section

namespace Categorification.WeightedKLR.Local

variable {I J : Type*} [DecidableEq I]
  {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}
  {Δ : WeightedGraph J 𝕜 k} {ν : I →₀ ℕ} {μ : J →₀ ℕ}

/-- The discrete data of a local linearization: its strands are reindexed original
strands and its hyperplanes are exactly those through the configuration. The
evaluation identity records the affine-to-linear change of coordinates. -/
structure Linearization (Δ : WeightedGraph J 𝕜 k) (μ : J →₀ ℕ)
    (Γ : WeightedGraph I 𝕜 k) (ν : I →₀ ℕ) (p : Strand ν → 𝕜) where
  strand : Strand μ ≃ Strand ν
  hyp : Hyp Δ μ ≃ {h : Hyp Γ ν // h.val p = 0}
  val_perturb : ∀ (h : Hyp Δ μ) (q : Strand μ → 𝕜) (t : 𝕜),
    (hyp h).1.val (p + t • (q ∘ strand.symm)) = t * h.val q

namespace Linearization

variable {p : Strand ν → 𝕜} (L : Linearization Δ μ Γ ν p)

/-- Local signs on incident hyperplanes, and the forced signs on other hyperplanes. -/
def chamberSigns (C : FullChamber Δ μ) (h : Hyp Γ ν) : Bool :=
  if hh : h.val p = 0 then C.1 (L.hyp.symm ⟨h, hh⟩) else decide (0 < h.val p)

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem chamberSigns_hyp (C : FullChamber Δ μ) (h : Hyp Δ μ) :
    L.chamberSigns C (L.hyp h).1 = C.1 h := by
  simp [chamberSigns, (L.hyp h).2]

/-- A sufficiently small positive local displacement realizes the prescribed signs. -/
theorem exists_chamberPoint (C : FullChamber Δ μ) :
    ∃ q : Strand ν → 𝕜, IsGeneric Γ q ∧ fullSigns q = L.chamberSigns C := by
  classical
  obtain ⟨q, hq, hC⟩ := C.2
  let v : Strand ν → 𝕜 := q ∘ L.strand.symm
  obtain ⟨δ, hδ, hsmall⟩ := Segment.exists_pos_small
    (Finset.univ.filter fun h : Hyp Γ ν => h.val p ≠ 0)
    (fun h => h.val p) (fun h => (hypAff h).linear v)
    (fun h hh => (Finset.mem_filter.1 hh).2)
  let t : 𝕜 := δ / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have htδ : t < δ := by dsimp [t]; linarith
  have he : ∀ h : Hyp Γ ν, if hh : h.val p = 0 then
      h.val (p + t • v) = t * (L.hyp.symm ⟨h, hh⟩).val q
      else 0 < h.val p * h.val (p + t • v) := by
    intro h
    split_ifs with hh
    · simpa only [v, L.hyp.apply_symm_apply] using
        L.val_perturb (L.hyp.symm ⟨h, hh⟩) q t
    · simpa only [← hypAff_apply, AffineMap.apply_add_smul] using
        hsmall t ht.le htδ h (Finset.mem_filter.2 ⟨Finset.mem_univ _, hh⟩)
  refine ⟨p + t • v, ?_, ?_⟩
  · intro h
    have hh := he h
    split_ifs at hh with hz
    · rw [hh]
      exact mul_ne_zero ht.ne' (hq _)
    · exact (mul_pos_iff.1 hh).elim (fun h => h.2.ne') (fun h => h.2.ne)
  · funext h
    have hh := he h
    by_cases hz : h.val p = 0
    · rw [dite_eq_left hz] at hh
      rw [chamberSigns, dite_eq_left hz, fullSigns, hh]
      exact (decide_eq_decide.2 (mul_pos_iff_of_pos_left ht)).trans (congrFun hC _)
    · rw [dite_eq_right hz] at hh
      simp only [chamberSigns, dite_eq_right hz, fullSigns]
      exact decide_eq_decide.2 (Segment.pos_iff_of_mul_pos hh).symm

/-- The original chamber of a local chamber. -/
def chamber (C : FullChamber Δ μ) : FullChamber Γ ν :=
  ⟨L.chamberSigns C, L.exists_chamberPoint C⟩

@[simp] theorem chamber_hyp (C : FullChamber Δ μ) (h : Hyp Δ μ) :
    (L.chamber C).1 (L.hyp h).1 = C.1 h := L.chamberSigns_hyp C h

theorem chamber_injective : Function.Injective L.chamber := by
  intro C D h
  apply Subtype.ext
  funext a
  have h' := congrArg (fun E : FullChamber Γ ν => E.1 (L.hyp a).1) h
  simpa only [L.chamber_hyp] using h'

theorem chamber_incident (C : FullChamber Δ μ) : (L.chamber C).Incident p := by
  intro h
  change (if L.chamberSigns C h then 0 ≤ h.val p else h.val p ≤ 0)
  by_cases hz : h.val p = 0
  · rw [hz]
    split_ifs <;> exact le_rfl
  · simp only [chamberSigns, dite_eq_right hz, decide_eq_true_eq]
    split_ifs with hp
    · exact hp.le
    · exact le_of_not_gt hp

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Translate a point of the original configuration space back to tangent coordinates. -/
theorem val_sub_base (h : Hyp Δ μ) (q : Strand ν → 𝕜) :
    h.val (fun s => q (L.strand s) - p (L.strand s)) = (L.hyp h).1.val q := by
  have hv := L.val_perturb h (fun s => q (L.strand s) - p (L.strand s)) 1
  have he : p + (1 : 𝕜) •
      ((fun s => q (L.strand s) - p (L.strand s)) ∘ L.strand.symm) = q := by
    funext s
    simp
  rw [he, one_mul] at hv
  exact hv.symm

/-- Restrict an original chamber to its incident hyperplanes. -/
def localChamber (C : FullChamber Γ ν) : FullChamber Δ μ := by
  refine ⟨fun h => C.1 (L.hyp h).1, ?_⟩
  obtain ⟨q, hq, hC⟩ := C.2
  refine ⟨fun s => q (L.strand s) - p (L.strand s), ?_, ?_⟩
  · intro h
    rw [L.val_sub_base]
    exact hq _
  · funext h
    change decide (0 < h.val _) = C.1 (L.hyp h).1
    rw [L.val_sub_base]
    exact congrFun hC _

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
@[simp] theorem localChamber_apply (C : FullChamber Γ ν) (h : Hyp Δ μ) :
    (L.localChamber C).1 h = C.1 (L.hyp h).1 := rfl

@[simp] theorem localChamber_chamber (C : FullChamber Δ μ) :
    L.localChamber (L.chamber C) = C := by
  apply Subtype.ext
  funext h
  exact L.chamber_hyp C h

theorem chamber_localChamber (C : FullChamber Γ ν) (hC : C.Incident p) :
    L.chamber (L.localChamber C) = C := by
  apply Subtype.ext
  funext h
  change L.chamberSigns (L.localChamber C) h = C.1 h
  by_cases hh : h.val p = 0
  · simp only [chamberSigns, dite_eq_left hh, localChamber_apply, L.hyp.apply_symm_apply]
  · simp only [chamberSigns, dite_eq_right hh]
    exact (hC.sign_eq h hh).symm

/-- Chambers of the central local arrangement are exactly the original chambers
whose closures contain the base configuration. -/
def chamberEquiv : FullChamber Δ μ ≃ {C : FullChamber Γ ν // C.Incident p} where
  toFun C := ⟨L.chamber C, L.chamber_incident C⟩
  invFun C := L.localChamber C.1
  left_inv C := L.localChamber_chamber C
  right_inv C := Subtype.ext (L.chamber_localChamber C.1 C.2)

/-- Local adjacency is unchanged by adding the fixed signs of nonincident walls. -/
theorem adjacent_chamber_iff (C D : FullChamber Δ μ) (h : Hyp Δ μ) :
    (L.chamber C).Adjacent (L.chamber D) (L.hyp h).1 ↔ C.Adjacent D h := by
  constructor
  · intro ha
    refine ⟨by simpa only [L.chamber_hyp] using ha.1, fun h' hne => ?_⟩
    simpa only [L.chamber_hyp] using ha.2 (L.hyp h').1 fun he =>
      hne (L.hyp.injective (Subtype.ext he))
  · intro ha
    refine ⟨by simpa only [L.chamber_hyp] using ha.1, fun h' hne => ?_⟩
    by_cases hz : h'.val p = 0
    · let a := L.hyp.symm ⟨h', hz⟩
      have he : (L.hyp a).1 = h' := congrArg Subtype.val (L.hyp.apply_symm_apply ⟨h', hz⟩)
      rw [← he, L.chamber_hyp, L.chamber_hyp]
      exact ha.2 a (fun h0 => hne (by simpa [h0] using he.symm))
    · simp only [chamber, chamberSigns, dite_eq_right hz]

theorem not_adjacent_chamber {C D : FullChamber Δ μ}
    (hn : ∀ h, ¬ C.Adjacent D h) (a : Hyp Γ ν) :
    ¬ (L.chamber C).Adjacent (L.chamber D) a := by
  intro ha
  have hz : a.val p = 0 := by
    by_contra hne
    have hsign : (L.chamber C).1 a = (L.chamber D).1 a := by
      simp only [chamber, chamberSigns, dite_eq_right hne]
    exact ha.1 hsign
  let h := L.hyp.symm ⟨a, hz⟩
  have he : (L.hyp h).1 = a := congrArg Subtype.val (L.hyp.apply_symm_apply ⟨a, hz⟩)
  exact hn h ((L.adjacent_chamber_iff C D h).1 (he.symm ▸ ha))

end Linearization

/-- The refined zero-weight graph is the local linearization at the configuration. -/
def linearization (Γ : WeightedGraph I 𝕜 k) (p : Strand ν → 𝕜) :
    Linearization (graph Γ p) (weight p) Γ ν p where
  strand := strandEquiv p
  hyp := hypEquiv p
  val_perturb h q t := hyp_val_perturb p h q t

/-- Embed a chamber of the refined graph into the original chamber star. -/
def chamber (p : Strand ν → 𝕜) :
    FullChamber (graph Γ p) (weight p) → FullChamber Γ ν :=
  (linearization Γ p).chamber

theorem chamber_injective (p : Strand ν → 𝕜) :
    Function.Injective (chamber (Γ := Γ) p) := (linearization Γ p).chamber_injective

@[simp] theorem chamber_hyp (p : Strand ν → 𝕜)
    (C : FullChamber (graph Γ p) (weight p)) (h : Hyp (graph Γ p) (weight p)) :
    (chamber p C).1 (hyp p h) = C.1 h := (linearization Γ p).chamber_hyp C h

theorem chamber_incident (p : Strand ν → 𝕜)
    (C : FullChamber (graph Γ p) (weight p)) : (chamber p C).Incident p :=
  (linearization Γ p).chamber_incident C

/-- The complete chamber-star identification for the refined graph. -/
def chamberEquiv (p : Strand ν → 𝕜) :
    FullChamber (graph Γ p) (weight p) ≃ {C : FullChamber Γ ν // C.Incident p} :=
  (linearization Γ p).chamberEquiv

theorem range_chamber (p : Strand ν → 𝕜) :
    Set.range (chamber (Γ := Γ) p) = {C | C.Incident p} := by
  ext C
  constructor
  · rintro ⟨D, rfl⟩
    exact chamber_incident p D
  · intro hC
    exact ⟨(linearization Γ p).localChamber C,
      (linearization Γ p).chamber_localChamber C hC⟩

theorem adjacent_chamber_iff (p : Strand ν → 𝕜)
    (C D : FullChamber (graph Γ p) (weight p)) (h : Hyp (graph Γ p) (weight p)) :
    (chamber p C).Adjacent (chamber p D) (hyp p h) ↔ C.Adjacent D h :=
  (linearization Γ p).adjacent_chamber_iff C D h

theorem not_adjacent_chamber (p : Strand ν → 𝕜)
    {C D : FullChamber (graph Γ p) (weight p)} (hn : ∀ h, ¬ C.Adjacent D h)
    (a : Hyp Γ ν) : ¬ (chamber p C).Adjacent (chamber p D) a :=
  (linearization Γ p).not_adjacent_chamber hn a

end Categorification.WeightedKLR.Local

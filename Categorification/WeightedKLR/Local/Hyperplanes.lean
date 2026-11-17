/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Local.Graph
import Categorification.WeightedKLR.GallerySpan.Bridge

/-!
# Hyperplanes of the local graph

The colour refinement at a configuration identifies the hyperplanes of the local
zero-weight graph with the original hyperplanes through that configuration.
These are supporting constructions for the local-chart proof of
Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4,
§2.4, Theorem 2.19 (roadmap A), using the arrangement and basis of §2.1–2.2.
They are not claims printed separately in the source.
-/

noncomputable section

namespace Categorification.WeightedKLR.Local

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k]
  {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

/-- A local wall, regarded as a wall of the original graph. -/
def wall (p : Strand ν → 𝕜) (w : Wall (graph Γ p) (weight p)) : Wall Γ ν :=
  ⟨(w.edge.1, strandEquiv p w.src, strandEquiv p w.tgt),
    (strandEquiv_colour p w.src).trans (congrArg Prod.fst w.2.1),
    (strandEquiv_colour p w.tgt).trans (congrArg Prod.fst w.2.2.1),
    fun h => w.2.2.2 ((strandEquiv p).injective h)⟩

omit [IsStrictOrderedRing 𝕜] in
@[simp] theorem wall_edge (p : Strand ν → 𝕜) (w : Wall (graph Γ p) (weight p)) :
    (wall p w).edge = w.edge.1 := rfl

omit [IsStrictOrderedRing 𝕜] in
@[simp] theorem wall_src (p : Strand ν → 𝕜) (w : Wall (graph Γ p) (weight p)) :
    (wall p w).src = strandEquiv p w.src := rfl

omit [IsStrictOrderedRing 𝕜] in
@[simp] theorem wall_tgt (p : Strand ν → 𝕜) (w : Wall (graph Γ p) (weight p)) :
    (wall p w).tgt = strandEquiv p w.tgt := rfl

omit [IsStrictOrderedRing 𝕜] in
/-- Local walls pass through the base configuration. -/
theorem wall_val_base (p : Strand ν → 𝕜) (w : Wall (graph Γ p) (weight p)) :
    (wall p w).val p = 0 := by
  rcases w with ⟨⟨⟨e, i⟩, s, t⟩, hs, ht, _⟩
  have hsc := congrArg Prod.snd hs
  have htc := congrArg Prod.snd ht
  change s.label.2 = (coord p i).1 at hsc
  change t.label.2 = (coord p i).1 + Γ.weight e at htc
  change p (strandEquiv p t) - p (strandEquiv p s) - Γ.weight e = 0
  rw [strandEquiv_coord p t, strandEquiv_coord p s, hsc, htc]
  ring

omit [IsStrictOrderedRing 𝕜] in
/-- The wall embedding loses no edge or strand data. -/
theorem wall_injective (p : Strand ν → 𝕜) :
    Function.Injective (wall (Γ := Γ) p) := by
  intro w v h
  have he : w.edge.1 = v.edge.1 := congrArg Wall.edge h
  have hs : w.src = v.src := (strandEquiv p).injective (congrArg Wall.src h)
  have ht : w.tgt = v.tgt := (strandEquiv p).injective (congrArg Wall.tgt h)
  have hcw := congrArg Prod.snd w.2.1
  have hcv := congrArg Prod.snd v.2.1
  change w.src.label.2 = (coord p w.edge.2).1 at hcw
  change v.src.label.2 = (coord p v.edge.2).1 at hcv
  have hc : w.edge.2 = v.edge.2 := (coord p).injective (Subtype.ext
    (hcw.symm.trans ((congrArg (fun s : Strand (weight p) => s.label.2) hs).trans hcv)))
  apply Subtype.ext
  exact Prod.ext (Prod.ext he hc) (Prod.ext hs ht)

/-- An original wall through the base point, regarded as a local wall. -/
def wallOfZero (p : Strand ν → 𝕜) (w : Wall Γ ν) (hw : w.val p = 0) :
    Wall (graph Γ p) (weight p) := by
  refine ⟨((w.edge, coordIndex p w.src), (strandEquiv p).symm w.src,
    (strandEquiv p).symm w.tgt), ?_, ?_, ?_⟩
  · rw [strandEquiv_symm_label]
    change (w.src.label, p w.src) = (Γ.head w.edge, (coord p (coordIndex p w.src)).1)
    exact Prod.ext w.2.1 (coord_coordIndex p w.src).symm
  · rw [strandEquiv_symm_label]
    change (w.tgt.label, p w.tgt) =
      (Γ.tail w.edge, (coord p (coordIndex p w.src)).1 + Γ.weight w.edge)
    apply Prod.ext w.2.2.1
    rw [coord_coordIndex]
    change p w.tgt - p w.src - Γ.weight w.edge = 0 at hw
    linarith
  · exact fun h => w.2.2.2 ((strandEquiv p).symm.injective h)

@[simp] theorem wall_wallOfZero (p : Strand ν → 𝕜) (w : Wall Γ ν) (hw : w.val p = 0) :
    wall p (wallOfZero p w hw) = w := by
  apply Subtype.ext
  exact Prod.ext rfl (Prod.ext ((strandEquiv p).apply_symm_apply w.src)
    ((strandEquiv p).apply_symm_apply w.tgt))

/-- A local diagonal, regarded as a diagonal of the original strands. -/
def diag (p : Strand ν → 𝕜) (d : Diag (weight p)) : Diag ν :=
  ⟨(strandEquiv p d.fst, strandEquiv p d.snd), by
      apply Subtype.ext
      exact (strandEquiv_colour p d.fst).trans
        ((congrArg (fun a : (weight p).support => a.1.1) d.2.1).trans
          (strandEquiv_colour p d.snd).symm),
    strandEquiv_rank_lt d.2.1 d.2.2⟩

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
@[simp] theorem diag_fst (p : Strand ν → 𝕜) (d : Diag (weight p)) :
    (diag p d).fst = strandEquiv p d.fst := rfl

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
@[simp] theorem diag_snd (p : Strand ν → 𝕜) (d : Diag (weight p)) :
    (diag p d).snd = strandEquiv p d.snd := rfl

omit [IsStrictOrderedRing 𝕜] in
/-- Local diagonals pass through the base configuration. -/
theorem diag_val_base (p : Strand ν → 𝕜) (d : Diag (weight p)) :
    (diag p d).val p = 0 := by
  change p (strandEquiv p d.snd) - p (strandEquiv p d.fst) = 0
  rw [strandEquiv_coord p d.snd, strandEquiv_coord p d.fst]
  exact sub_eq_zero.2 (congrArg (fun a : (weight p).support => a.1.2) d.2.1).symm

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
theorem diag_injective (p : Strand ν → 𝕜) : Function.Injective (diag p) := by
  intro d e h
  apply Subtype.ext
  exact Prod.ext ((strandEquiv p).injective (congrArg Diag.fst h))
    ((strandEquiv p).injective (congrArg Diag.snd h))

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
private theorem strandEquiv_rank_lt_of {p : Strand ν → 𝕜} {s t : Strand (weight p)}
    (hc : s.1 = t.1)
    (hr : (strandEquiv p s).2.val < (strandEquiv p t).2.val) : s.2.val < t.2.val := by
  rcases s with ⟨a, r⟩
  rcases t with ⟨b, u⟩
  dsimp only at hc
  subst b
  exact (strandEquiv_rank_lt_iff p a r u).1 hr

/-- An original diagonal through the base point, regarded as a local diagonal. -/
def diagOfZero (p : Strand ν → 𝕜) (d : Diag ν) (hd : d.val p = 0) : Diag (weight p) := by
  have hc : ((strandEquiv p).symm d.fst).1 = ((strandEquiv p).symm d.snd).1 := by
    apply Subtype.ext
    rw [← Strand.label, ← Strand.label, strandEquiv_symm_label, strandEquiv_symm_label]
    apply Prod.ext
    · exact congrArg Subtype.val d.2.1
    · change p d.fst = p d.snd
      change p d.snd - p d.fst = 0 at hd
      exact (sub_eq_zero.1 hd).symm
  refine ⟨((strandEquiv p).symm d.fst, (strandEquiv p).symm d.snd), hc, ?_⟩
  apply strandEquiv_rank_lt_of hc
  rw [(strandEquiv p).apply_symm_apply, (strandEquiv p).apply_symm_apply]
  exact d.2.2

omit [IsStrictOrderedRing 𝕜] in
@[simp] theorem diagOfZero_fst (p : Strand ν → 𝕜) (d : Diag ν) (hd : d.val p = 0) :
    (diagOfZero p d hd).fst = (strandEquiv p).symm d.fst := rfl

omit [IsStrictOrderedRing 𝕜] in
@[simp] theorem diagOfZero_snd (p : Strand ν → 𝕜) (d : Diag ν) (hd : d.val p = 0) :
    (diagOfZero p d hd).snd = (strandEquiv p).symm d.snd := rfl

omit [IsStrictOrderedRing 𝕜] in
@[simp] theorem diag_diagOfZero (p : Strand ν → 𝕜) (d : Diag ν) (hd : d.val p = 0) :
    diag p (diagOfZero p d hd) = d := by
  apply Subtype.ext
  apply Prod.ext
  · change (diag p (diagOfZero p d hd)).fst = d.fst
    rw [diag_fst, diagOfZero_fst, Equiv.apply_symm_apply]
  · change (diag p (diagOfZero p d hd)).snd = d.snd
    rw [diag_snd, diagOfZero_snd, Equiv.apply_symm_apply]

/-- A local hyperplane, regarded as an original hyperplane through the base point. -/
def hyp (p : Strand ν → 𝕜) : Hyp (graph Γ p) (weight p) → Hyp Γ ν
  | .inl w => .inl (wall p w)
  | .inr d => .inr (diag p d)

omit [IsStrictOrderedRing 𝕜] in
/-- Every hyperplane in the local graph contains the base point. -/
theorem hyp_val_base (p : Strand ν → 𝕜) (h : Hyp (graph Γ p) (weight p)) :
    (hyp p h).val p = 0 := by
  cases h with
  | inl w => exact wall_val_base p w
  | inr d => exact diag_val_base p d

omit [IsStrictOrderedRing 𝕜] in
theorem hyp_injective (p : Strand ν → 𝕜) : Function.Injective (hyp (Γ := Γ) p) := by
  intro h h' he
  cases h with
  | inl w =>
    cases h' with
    | inl v => exact congrArg Sum.inl (wall_injective p (Sum.inl.inj he))
    | inr d => cases he
  | inr d =>
    cases h' with
    | inl w => cases he
    | inr e => exact congrArg Sum.inr (diag_injective p (Sum.inr.inj he))

/-- The local hyperplanes are precisely the original hyperplanes through the point. -/
theorem range_hyp (p : Strand ν → 𝕜) :
    Set.range (hyp (Γ := Γ) p) = {h : Hyp Γ ν | h.val p = 0} := by
  ext h
  constructor
  · rintro ⟨a, rfl⟩
    exact hyp_val_base p a
  · intro hh
    cases h with
    | inl w => exact ⟨.inl (wallOfZero p w hh), congrArg Sum.inl (wall_wallOfZero p w hh)⟩
    | inr d => exact ⟨.inr (diagOfZero p d hh), congrArg Sum.inr (diag_diagOfZero p d hh)⟩

/-- The local hyperplane type identifies with the hyperplanes incident at the point. -/
def hypEquiv (p : Strand ν → 𝕜) :
    Hyp (graph Γ p) (weight p) ≃ {h : Hyp Γ ν // h.val p = 0} :=
  Equiv.ofBijective (fun h => ⟨hyp p h, hyp_val_base p h⟩)
    ⟨fun _ _ h => hyp_injective p (congrArg Subtype.val h), by
      rintro ⟨h, hh⟩
      obtain ⟨a, ha⟩ := (show h ∈ Set.range (hyp (Γ := Γ) p) by rw [range_hyp]; exact hh)
      exact ⟨a, Subtype.ext ha⟩⟩

@[simp] theorem hypEquiv_val (p : Strand ν → 𝕜) (h : Hyp (graph Γ p) (weight p)) :
    (hypEquiv p h).1 = hyp p h := rfl

omit [IsStrictOrderedRing 𝕜] in
@[simp] theorem hyp_lo (p : Strand ν → 𝕜) (h : Hyp (graph Γ p) (weight p)) :
    (hyp p h).lo = strandEquiv p h.lo := by cases h <;> rfl

omit [IsStrictOrderedRing 𝕜] in
@[simp] theorem hyp_hi (p : Strand ν → 𝕜) (h : Hyp (graph Γ p) (weight p)) :
    (hyp p h).hi = strandEquiv p h.hi := by cases h <;> rfl

/-- Affine evaluation near the point is the local linear evaluation, with the
same positive scale on every active hyperplane. -/
theorem hyp_val_perturb (p : Strand ν → 𝕜) (h : Hyp (graph Γ p) (weight p))
    (q : Strand (weight p) → 𝕜) (t : 𝕜) :
    (hyp p h).val (p + t • (q ∘ (strandEquiv p).symm)) = t * h.val q := by
  cases h with
  | inl w =>
    have hb := wall_val_base p w
    change p (strandEquiv p w.tgt) - p (strandEquiv p w.src) - Γ.weight w.edge.1 = 0 at hb
    change (p + t • (q ∘ (strandEquiv p).symm)) (strandEquiv p w.tgt) -
      (p + t • (q ∘ (strandEquiv p).symm)) (strandEquiv p w.src) - Γ.weight w.edge.1 =
      t * (q w.tgt - q w.src - 0)
    simp only [Pi.add_apply, Pi.smul_apply, Function.comp_apply, Equiv.symm_apply_apply, smul_eq_mul]
    linear_combination hb
  | inr d =>
    have hb := diag_val_base p d
    change p (strandEquiv p d.snd) - p (strandEquiv p d.fst) = 0 at hb
    change (p + t • (q ∘ (strandEquiv p).symm)) (strandEquiv p d.snd) -
      (p + t • (q ∘ (strandEquiv p).symm)) (strandEquiv p d.fst) =
      t * (q d.snd - q d.fst)
    simp only [Pi.add_apply, Pi.smul_apply, Function.comp_apply, Equiv.symm_apply_apply, smul_eq_mul]
    linear_combination hb

end Categorification.WeightedKLR.Local

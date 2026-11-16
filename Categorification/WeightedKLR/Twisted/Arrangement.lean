/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.GallerySpan.Blocks
import Categorification.WeightedKLR.Loadings.Shift

/-!
# The arrangement of the twisted algebra

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.5
(the category `P` before Proposition 2.20).

The objects of `P` are pairs of a loading and a weighting `ϑ : E → 𝕜`, and along a morphism the
distance between a ghost and its strand varies linearly from `ϑ₀(e)` to `ϑ₁(e)`. We read a
morphism as a path in the space `Strand ν ⊕ Γ.E → 𝕜` of positions *and* weights, and its
events as the points where it crosses one of the hyperplanes

* `x_b - x_a - ϑ_e = 0` (a wall: the strand `b` meets the ghost of `a` for the edge `e`),
* `x_{s'} - x_s = 0` (a diagonal: two strands of one colour meet).

These are the walls and diagonals `Hyp Γ ν` of the arrangement for a fixed weighting, now with
the weight of the edge as a coordinate. All of them are linear hyperplanes. A strand meeting
its own ghost (a loop of weight `0` at a point of the path) is not an event: there is no
hyperplane for it, and the walls `x_b - x_a - ϑ_e` and `x_a - x_b - ϑ_e` of a loop `e` and
the diagonal `x_a = x_b` meet in a flat of codimension two.

The fibre of this arrangement over a weighting `ϑ` is the arrangement of `Γ.withWeight ϑ`
(`Hyp.twVal_elim`, `FullChamber.toTw`), and every chamber of the big arrangement comes from a
fibre (`TwChamber.exists_eq_toTw`). Unlike the fibres, the big arrangement has distinct
hyperplanes for distinct elements of `Hyp Γ ν`, with no assumption on `Γ` (`twHdist`): the
input of the results on segments in `Segment/*.lean`.

## Main definitions

* `WeightedGraph.withWeight Γ ϑ` (from `Loadings.Shift`): `Γ` with the weights `ϑ`.
* `Hyp.twLin h`: the linear function defining the hyperplane `h` of the big arrangement;
  `Hyp.twVal`, `twAff`.
* `TwGeneric`, `twSigns`, `TwChamber Γ ν`, `TwChamber.Adjacent`.
* `FullChamber.toTw`: the chambers of a fibre as chambers of the big arrangement.

## Main results

* `Hyp.twVal_elim`: the hyperplanes restrict to those of `Γ.withWeight ϑ` over `ϑ`.
* `TwChamber.exists_eq_toTw`: every chamber comes from a fibre.
* `twHdist`: every hyperplane has a point off any other hyperplane.
-/

namespace Categorification.WeightedKLR

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

namespace WeightedGraph

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
@[simp] theorem withWeight_weight (Γ : WeightedGraph I 𝕜 k) (ϑ : Γ.E → 𝕜) :
    (Γ.withWeight ϑ).weight = ϑ := rfl

end WeightedGraph

namespace Hyp

/-- The hyperplane `h` of the big arrangement, as a linear function of positions and weights:
`x_b - x_a - ϑ_e` for a wall, `x_{s'} - x_s` for a diagonal. -/
def twLin : Hyp Γ ν → (Strand ν ⊕ Γ.E → 𝕜) →ₗ[𝕜] 𝕜
  | .inl w => LinearMap.proj (R := 𝕜) (φ := fun _ : Strand ν ⊕ Γ.E => 𝕜) (.inl w.tgt) -
      LinearMap.proj (R := 𝕜) (φ := fun _ : Strand ν ⊕ Γ.E => 𝕜) (.inl w.src) -
      LinearMap.proj (R := 𝕜) (φ := fun _ : Strand ν ⊕ Γ.E => 𝕜) (.inr w.edge)
  | .inr d => LinearMap.proj (R := 𝕜) (φ := fun _ : Strand ν ⊕ Γ.E => 𝕜) (.inl d.snd) -
      LinearMap.proj (R := 𝕜) (φ := fun _ : Strand ν ⊕ Γ.E => 𝕜) (.inl d.fst)

/-- The value of the hyperplane `h` of the big arrangement. -/
def twVal (h : Hyp Γ ν) (z : Strand ν ⊕ Γ.E → 𝕜) : 𝕜 := h.twLin z

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
@[simp] theorem twVal_inl (w : Wall Γ ν) (z : Strand ν ⊕ Γ.E → 𝕜) :
    twVal (.inl w) z = z (.inl w.tgt) - z (.inl w.src) - z (.inr w.edge) := rfl

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
@[simp] theorem twVal_inr (d : Diag ν) (z : Strand ν ⊕ Γ.E → 𝕜) :
    twVal (Γ := Γ) (.inr d) z = z (.inl d.snd) - z (.inl d.fst) := rfl

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
@[simp] theorem twLin_apply (h : Hyp Γ ν) (z : Strand ν ⊕ Γ.E → 𝕜) : h.twLin z = h.twVal z :=
  rfl

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Over the weighting `ϑ`, the hyperplane `h` is the hyperplane `h` of `Γ.withWeight ϑ`. -/
theorem twVal_elim (h : Hyp Γ ν) (p : Strand ν → 𝕜) (ϑ : Γ.E → 𝕜) :
    h.twVal (Sum.elim p ϑ) = Hyp.val (Γ := Γ.withWeight ϑ) h p := by
  rcases h with w | d <;> rfl

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem twVal_eq (h : Hyp Γ ν) (z : Strand ν ⊕ Γ.E → 𝕜) :
    h.twVal z = Hyp.val (Γ := Γ.withWeight (z ∘ Sum.inr)) h (z ∘ Sum.inl) := by
  rw [← twVal_elim, Sum.elim_comp_inl_inr]

/-- The edge coordinate of a hyperplane: the weight of the edge of a wall, `0` for a
diagonal. -/
def edgeVal : Hyp Γ ν → (Γ.E → 𝕜) → 𝕜
  | .inl w, t => t w.edge
  | .inr _, _ => 0

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- The linear function of `h` splits into its linear part on positions and its edge
coordinate. -/
theorem twLin_elim (h : Hyp Γ ν) (y : Strand ν → 𝕜) (t : Γ.E → 𝕜) :
    h.twLin (Sum.elim y t) = (hypAff h).linear y - h.edgeVal t := by
  rcases h with w | d
  · show y w.tgt - y w.src - t w.edge = _
    rw [hypAff_linear_apply]
    rfl
  · show y d.snd - y d.fst = _
    rw [hypAff_linear_apply]
    simp [edgeVal, hi, lo]

end Hyp

/-- The hyperplane `h` of the big arrangement as an affine (in fact linear) function. -/
def twAff (h : Hyp Γ ν) : (Strand ν ⊕ Γ.E → 𝕜) →ᵃ[𝕜] 𝕜 := h.twLin.toAffineMap

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
@[simp] theorem twAff_apply (h : Hyp Γ ν) (z : Strand ν ⊕ Γ.E → 𝕜) : twAff h z = h.twVal z :=
  rfl

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
@[simp] theorem twAff_linear (h : Hyp Γ ν) : (twAff h).linear = h.twLin := rfl

variable (Γ) in
/-- A point of the big arrangement on no hyperplane. -/
def TwGeneric (z : Strand ν ⊕ Γ.E → 𝕜) : Prop := ∀ h : Hyp Γ ν, h.twVal z ≠ 0

/-- The side of each hyperplane of the big arrangement on which a point lies. -/
def twSigns (z : Strand ν ⊕ Γ.E → 𝕜) : Hyp Γ ν → Bool := fun h => decide (0 < h.twVal z)

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem twSigns_twAff (z : Strand ν ⊕ Γ.E → 𝕜) :
    Segment.signs (twAff (Γ := Γ) (ν := ν)) z = twSigns z := rfl

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem generic_twAff_iff (z : Strand ν ⊕ Γ.E → 𝕜) :
    Segment.Generic (twAff (Γ := Γ) (ν := ν)) z ↔ TwGeneric Γ z := Iff.rfl

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem twGeneric_elim_iff (p : Strand ν → 𝕜) (ϑ : Γ.E → 𝕜) :
    TwGeneric Γ (Sum.elim p ϑ) ↔ IsGeneric (Γ.withWeight ϑ) p := by
  simp only [TwGeneric, Hyp.twVal_elim]
  rfl

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem twSigns_elim (p : Strand ν → 𝕜) (ϑ : Γ.E → 𝕜) :
    twSigns (Γ := Γ) (Sum.elim p ϑ) = fullSigns (Γ := Γ.withWeight ϑ) p := by
  funext h
  simp only [twSigns, Hyp.twVal_elim]
  rfl

variable (Γ ν) in
/-- A chamber of the big arrangement: the sign vector of a generic point. -/
def TwChamber : Type _ :=
  {σ : Hyp Γ ν → Bool // ∃ z, TwGeneric Γ z ∧ twSigns z = σ}

instance : DecidableEq (TwChamber Γ ν) := by unfold TwChamber; infer_instance
instance : Finite (TwChamber Γ ν) := by unfold TwChamber; infer_instance
noncomputable instance : Fintype (TwChamber Γ ν) := Fintype.ofFinite _

namespace TwChamber

/-- The chamber of a generic point. -/
def ofPoint (z : Strand ν ⊕ Γ.E → 𝕜) (hz : TwGeneric Γ z) : TwChamber Γ ν :=
  ⟨twSigns z, z, hz, rfl⟩

/-- All strands of each colour are in rank order. -/
def IsRankOrdered (C : TwChamber Γ ν) : Prop := ∀ d : Diag ν, C.1 (.inr d) = true

instance (C : TwChamber Γ ν) : Decidable C.IsRankOrdered := by
  unfold IsRankOrdered; infer_instance

/-- `C'` is obtained from `C` by crossing the single hyperplane `h`. -/
def Adjacent (C C' : TwChamber Γ ν) (h : Hyp Γ ν) : Prop :=
  C.1 h ≠ C'.1 h ∧ ∀ h', h' ≠ h → C.1 h' = C'.1 h'

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem Adjacent.symm {C C' : TwChamber Γ ν} {h : Hyp Γ ν} (hC : Adjacent C C' h) :
    Adjacent C' C h :=
  ⟨fun e => hC.1 e.symm, fun h' hh' => (hC.2 h' hh').symm⟩

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem Adjacent.unique {C C' : TwChamber Γ ν} {h h' : Hyp Γ ν} (hh : C.Adjacent C' h)
    (hh' : C.Adjacent C' h') : h = h' := by
  by_contra hne
  exact hh'.1 (hh.2 h' (Ne.symm hne))

omit [IsStrictOrderedRing 𝕜] in
theorem Adjacent.eq_of_adjacent {C C' C'' : TwChamber Γ ν} {h : Hyp Γ ν}
    (h₁ : Adjacent C C' h) (h₂ : Adjacent C C'' h) : C' = C'' := by
  apply Subtype.ext
  funext h'
  by_cases e : h' = h
  · subst e
    have a := h₁.1
    have b := h₂.1
    cases hC : C.1 h' <;> cases h1 : C'.1 h' <;> cases h2 : C''.1 h' <;> simp_all
  · rw [← h₁.2 h' e, h₂.2 h' e]

end TwChamber

namespace FullChamber

/-- A chamber of the arrangement over the weighting `ϑ` as a chamber of the big arrangement. -/
def toTw {ϑ : Γ.E → 𝕜} (C : FullChamber (Γ.withWeight ϑ) ν) : TwChamber Γ ν :=
  ⟨C.1, by
    obtain ⟨p, hp, hs⟩ := C.2
    exact ⟨Sum.elim p ϑ, (twGeneric_elim_iff p ϑ).2 hp, (twSigns_elim p ϑ).trans hs⟩⟩

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
@[simp] theorem toTw_val {ϑ : Γ.E → 𝕜} (C : FullChamber (Γ.withWeight ϑ) ν) :
    C.toTw.1 = C.1 := rfl

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem toTw_injective {ϑ : Γ.E → 𝕜} :
    Function.Injective (toTw (Γ := Γ) (ν := ν) (ϑ := ϑ)) := fun _ _ h =>
  Subtype.ext (congrArg Subtype.val h :)

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
/-- Adjacency in a fibre is adjacency in the big arrangement. -/
theorem adjacent_toTw_iff {ϑ : Γ.E → 𝕜} {C C' : FullChamber (Γ.withWeight ϑ) ν}
    {h : Hyp Γ ν} : C.toTw.Adjacent C'.toTw h ↔ C.Adjacent C' h := Iff.rfl

end FullChamber

namespace TwChamber

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
/-- Every chamber of the big arrangement comes from the fibre over some weighting. -/
theorem exists_eq_toTw (C : TwChamber Γ ν) :
    ∃ (ϑ : Γ.E → 𝕜) (C₀ : FullChamber (Γ.withWeight ϑ) ν), C₀.toTw = C := by
  obtain ⟨z, hz, hs⟩ := C.2
  have hz' : TwGeneric Γ (Sum.elim (z ∘ Sum.inl) (z ∘ Sum.inr)) := by
    rwa [Sum.elim_comp_inl_inr]
  refine ⟨z ∘ Sum.inr, FullChamber.ofPoint (z ∘ Sum.inl) ((twGeneric_elim_iff _ _).1 hz'), ?_⟩
  apply Subtype.ext
  change fullSigns (Γ := Γ.withWeight (z ∘ Sum.inr)) (z ∘ Sum.inl) = C.1
  rw [← twSigns_elim, Sum.elim_comp_inl_inr, hs]

end TwChamber

/-! ### Distinct hyperplanes of the big arrangement -/

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem Hyp.twVal_single_inl (g : Hyp Γ ν) (s : Strand ν) :
    g.twVal (Pi.single (.inl s) 1) = (hypAff g).linear (Pi.single s 1) := by
  have : (Pi.single (.inl s) 1 : Strand ν ⊕ Γ.E → 𝕜) = Sum.elim (Pi.single s 1) 0 := by
    funext c
    rcases c with c | c <;> simp [Pi.single_apply]
  rw [this, ← twLin_apply, twLin_elim]
  rcases g with w | d <;> simp [edgeVal]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem Hyp.twVal_single_inr (g : Hyp Γ ν) (e : Γ.E) :
    g.twVal (Pi.single (.inr e) 1) = -g.edgeVal (Pi.single e 1) := by
  have : (Pi.single (.inr e) 1 : Strand ν ⊕ Γ.E → 𝕜) = Sum.elim (0 : Strand ν → 𝕜) (Pi.single e 1) := by
    funext c
    rcases c with c | c <;> simp [Pi.single_apply]
  rw [this, ← twLin_apply, twLin_elim]
  simp

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Two diagonals on the same two strands are equal. -/
theorem Diag.eq_of_isPair {d d' : Diag ν} {a b : Strand ν}
    (hp : Hyp.IsPair (Sum.inr d : Hyp Γ ν) a b) (hq : Hyp.IsPair (Sum.inr d' : Hyp Γ ν) a b) :
    d = d' := by
  have h1 : d.fst.2.val < d.snd.2.val := d.2.2
  have h2 : d'.fst.2.val < d'.snd.2.val := d'.2.2
  rcases hp with ⟨p1, p2⟩ | ⟨p1, p2⟩ <;> rcases hq with ⟨q1, q2⟩ | ⟨q1, q2⟩ <;>
    change d.fst = _ at p1 <;> change d.snd = _ at p2 <;> change d'.fst = _ at q1 <;>
    change d'.snd = _ at q2
  · exact Subtype.ext (Prod.ext (p1.trans q1.symm) (p2.trans q2.symm))
  · rw [p1, p2] at h1; rw [q1, q2] at h2; omega
  · rw [p1, p2] at h1; rw [q1, q2] at h2; omega
  · exact Subtype.ext (Prod.ext (p1.trans q1.symm) (p2.trans q2.symm))

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem Hyp.edgeVal_single_ne (g : Hyp Γ ν) {e : Γ.E} (he : ∀ w, g = .inl w → w.edge ≠ e) :
    g.edgeVal (Pi.single e (1 : 𝕜)) = 0 := by
  rcases g with w | d
  · simp [edgeVal, he w rfl]
  · rfl

/-- Every hyperplane of the big arrangement has a point off any other hyperplane; no
assumption on `Γ` is needed. -/
theorem twHdist (h g : Hyp Γ ν) (hne : h ≠ g) :
    ∃ x, twAff h x = 0 ∧ twAff g x ≠ 0 := by
  classical
  simp only [twAff_apply]
  -- `g` is a wall whose edge is not an edge of `h`
  by_cases he : ∃ w', g = .inl w' ∧ ∀ w, h = .inl w → w.edge ≠ w'.edge
  · obtain ⟨w', rfl, he⟩ := he
    refine ⟨Pi.single (.inr w'.edge) 1, ?_, ?_⟩
    · rw [Hyp.twVal_single_inr, Hyp.edgeVal_single_ne h he, neg_zero]
    · simp [Hyp.twVal_single_inr, Hyp.edgeVal]
  push Not at he
  -- `g` has a strand which is not a strand of `h`
  by_cases hs : ∃ s, Hyp.Mem s g ∧ ¬Hyp.Mem s h
  · obtain ⟨s, hs', hs⟩ := hs
    refine ⟨Pi.single (.inl s) 1, ?_, ?_⟩
    · rw [Hyp.twVal_single_inl, Hyp.linear_single_eq_zero hs]
    · rw [Hyp.twVal_single_inl]
      exact Hyp.linear_single_ne_zero hs'
  push Not at hs
  have hp := Hyp.isPair_of_forall_mem hs
  rcases h with w | d <;> rcases g with w' | d'
  · obtain ⟨w₀, e₀, hw⟩ := he w' rfl
    cases Sum.inl_injective e₀
    have hst : w.src ≠ w.tgt := w.2.2.2
    refine ⟨Pi.single (.inl w.tgt) 1 + Pi.single (.inr w.edge) 1, ?_, ?_⟩
    · rw [Hyp.twVal, map_add, Hyp.twLin_apply, Hyp.twLin_apply, Hyp.twVal_single_inl,
        Hyp.twVal_single_inr, hypAff_linear_apply]
      simp [Hyp.edgeVal, Hyp.hi, Hyp.lo, Pi.single_eq_of_ne hst]
    · rcases hp with ⟨p1, p2⟩ | ⟨p1, p2⟩
      · change w.src = w'.src at p1
        change w.tgt = w'.tgt at p2
        exact absurd (congrArg Sum.inl (Subtype.ext (Prod.ext hw (Prod.ext p1 p2)))) hne
      · change w.src = w'.tgt at p1
        change w.tgt = w'.src at p2
        rw [Hyp.twVal, map_add, Hyp.twLin_apply, Hyp.twLin_apply, Hyp.twVal_single_inl,
          Hyp.twVal_single_inr, hypAff_linear_apply]
        simp only [Hyp.hi, Hyp.lo, ← p1, ← p2, Hyp.edgeVal, ← hw, Pi.single_eq_same,
          Pi.single_eq_of_ne hst]
        norm_num
  · have hst : w.src ≠ w.tgt := w.2.2.2
    refine ⟨Pi.single (.inl w.tgt) 1 + Pi.single (.inr w.edge) 1, ?_, ?_⟩
    · rw [Hyp.twVal, map_add, Hyp.twLin_apply, Hyp.twLin_apply, Hyp.twVal_single_inl,
        Hyp.twVal_single_inr, hypAff_linear_apply]
      simp [Hyp.edgeVal, Hyp.hi, Hyp.lo, Pi.single_eq_of_ne hst]
    · rw [Hyp.twVal, map_add, Hyp.twLin_apply, Hyp.twLin_apply, Hyp.twVal_single_inl,
        Hyp.twVal_single_inr, hypAff_linear_apply]
      rcases hp with ⟨p1, p2⟩ | ⟨p1, p2⟩
      · change w.src = d'.fst at p1
        change w.tgt = d'.snd at p2
        simp [Hyp.edgeVal, Hyp.hi, Hyp.lo, ← p1, ← p2, Pi.single_eq_of_ne hst]
      · change w.src = d'.snd at p1
        change w.tgt = d'.fst at p2
        simp [Hyp.edgeVal, Hyp.hi, Hyp.lo, ← p1, ← p2, Pi.single_eq_of_ne hst]
  · obtain ⟨w₀, e₀, -⟩ := he w' rfl
    cases e₀
  · exact absurd (congrArg Sum.inr (Diag.eq_of_isPair (Γ := Γ) (Hyp.isPair_self _) hp)) (Ne.symm hne)

end Categorification.WeightedKLR

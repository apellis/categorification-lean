/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Loading

/-!
# The arrangement of walls and diagonals

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.1
(Definitions 2.3–2.5).

A weighted KLR diagram is a path in the space of configurations `Strand ν → 𝕜`. Its events
are the points where it crosses a *wall* (a strand meets an interacting ghost) or a
*diagonal* (two strands of the same colour meet). Here strands keep their labels along the
path, so a configuration need not be increasing on each colour; the diagram then ends at the
loading obtained by relabelling the strands of each colour by rank.

## Main definitions

* `Diag ν`: the diagonal `x_s = x_{s'}` for strands `s, s'` of one colour with `s` of smaller
  rank; its value at `p` is `p s' - p s`.
* `Hyp Γ ν`: the walls and the diagonals, with `Hyp.val`.
* `IsGeneric p`: `p` lies on no wall and no diagonal.
* `FullChamber Γ ν`: the sign vectors of generic configurations; `FullChamber.IsRankOrdered`
  (every diagonal positive) singles out the chambers of `Chamber Γ ν`.
* `FullChamber.Adjacent C C' h`: `C'` is obtained from `C` by crossing the single
  hyperplane `h`.
-/

namespace Categorification.WeightedKLR

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

variable (ν) in
/-- A diagonal: two strands `s, s'` of the same colour with `rank s < rank s'`. It is the
hyperplane `x_s = x_{s'}`. -/
def Diag : Type _ := {d : Strand ν × Strand ν // d.1.1 = d.2.1 ∧ d.1.2.val < d.2.2.val}

instance : Fintype (Diag ν) := by unfold Diag; infer_instance
instance : DecidableEq (Diag ν) := by unfold Diag; infer_instance

namespace Diag

/-- The strand of smaller rank. -/
def fst (d : Diag ν) : Strand ν := d.1.1
/-- The strand of larger rank. -/
def snd (d : Diag ν) : Strand ν := d.1.2

/-- The value `p s' - p s`; it is positive when the two strands are in rank order. -/
def val (d : Diag ν) (p : Strand ν → 𝕜) : 𝕜 := p d.snd - p d.fst

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem fst_ne_snd (d : Diag ν) : d.fst ≠ d.snd := fun h => (ne_of_lt d.2.2) (by
  rw [fst, snd] at h; rw [h])

end Diag

variable (Γ ν) in
/-- The hyperplanes of the arrangement: walls and diagonals. -/
abbrev Hyp : Type _ := Wall Γ ν ⊕ Diag ν

namespace Hyp

/-- The affine function defining a hyperplane. -/
def val : Hyp Γ ν → (Strand ν → 𝕜) → 𝕜
  | .inl w, p => w.val p
  | .inr d, p => d.val p

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
@[simp] theorem val_inl (w : Wall Γ ν) (p : Strand ν → 𝕜) : val (.inl w) p = w.val p := rfl
omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
@[simp] theorem val_inr (d : Diag ν) (p : Strand ν → 𝕜) : val (Γ := Γ) (.inr d) p = d.val p :=
  rfl

end Hyp

variable (Γ) in
/-- A configuration on no wall and no diagonal. -/
def IsGeneric (p : Strand ν → 𝕜) : Prop := ∀ h : Hyp Γ ν, h.val p ≠ 0

/-- The side of each hyperplane on which a configuration lies. -/
def fullSigns (p : Strand ν → 𝕜) : Hyp Γ ν → Bool := fun h => decide (0 < h.val p)

variable (Γ ν) in
/-- A full chamber: the sign vector of a generic configuration. -/
def FullChamber : Type _ :=
  {σ : Hyp Γ ν → Bool // ∃ p, IsGeneric Γ p ∧ fullSigns p = σ}

instance : DecidableEq (FullChamber Γ ν) := by unfold FullChamber; infer_instance
instance : Finite (FullChamber Γ ν) := by unfold FullChamber; infer_instance
noncomputable instance : Fintype (FullChamber Γ ν) := Fintype.ofFinite _

namespace FullChamber

/-- The full chamber of a generic configuration. -/
def ofPoint (p : Strand ν → 𝕜) (hp : IsGeneric Γ p) : FullChamber Γ ν := ⟨fullSigns p, p, hp, rfl⟩

/-- All strands of each colour are in rank order. -/
def IsRankOrdered (C : FullChamber Γ ν) : Prop := ∀ d : Diag ν, C.1 (.inr d) = true

instance (C : FullChamber Γ ν) : Decidable C.IsRankOrdered := by
  unfold IsRankOrdered; infer_instance

/-- `C'` is obtained from `C` by crossing the single hyperplane `h`. -/
def Adjacent (C C' : FullChamber Γ ν) (h : Hyp Γ ν) : Prop :=
  C.1 h ≠ C'.1 h ∧ ∀ h', h' ≠ h → C.1 h' = C'.1 h'

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem Adjacent.symm {C C' : FullChamber Γ ν} {h : Hyp Γ ν} (hC : Adjacent C C' h) :
    Adjacent C' C h :=
  ⟨fun e => hC.1 e.symm, fun h' hh' => (hC.2 h' hh').symm⟩

omit [IsStrictOrderedRing 𝕜] in
theorem Adjacent.eq_of_adjacent {C C' C'' : FullChamber Γ ν} {h : Hyp Γ ν}
    (h₁ : Adjacent C C' h) (h₂ : Adjacent C C'' h) : C' = C'' := by
  apply Subtype.ext
  funext h'
  by_cases e : h' = h
  · subst e
    have a := h₁.1
    have b := h₂.1
    cases hC : C.1 h' <;> cases h1 : C'.1 h' <;> cases h2 : C''.1 h' <;> simp_all
  · rw [← h₁.2 h' e, h₂.2 h' e]

end FullChamber

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
/-- A rank-ordered configuration on no wall is generic. -/
theorem IsAdmissible.isGeneric {p : Strand ν → 𝕜} (hp : IsAdmissible Γ p) : IsGeneric Γ p := by
  rintro (w | d)
  · exact hp.2.2 w
  · simp only [Hyp.val_inr, Diag.val]
    exact sub_ne_zero.2 (ne_of_gt (hp.2.1 _ _ d.2.1 d.2.2))

/-- The full chamber of a (rank-ordered) chamber. -/
def Chamber.toFull (c : Chamber Γ ν) : FullChamber Γ ν :=
  ⟨fun h => match h with
    | .inl w => c.1 w
    | .inr _ => true, by
    obtain ⟨p, hp, hs⟩ := c.2
    refine ⟨p, hp.isGeneric, ?_⟩
    funext h
    rcases h with w | d
    · rw [← hs]; rfl
    · simp only [fullSigns, Hyp.val_inr, Diag.val, decide_eq_true_eq, sub_pos]
      exact hp.2.1 _ _ d.2.1 d.2.2⟩

omit [DecidableEq I] in
theorem Chamber.toFull_isRankOrdered (c : Chamber Γ ν) : c.toFull.IsRankOrdered := fun _ => rfl

omit [DecidableEq I] in
theorem Chamber.toFull_injective : Function.Injective (Chamber.toFull (Γ := Γ) (ν := ν)) := by
  intro c c' h
  apply Subtype.ext
  funext w
  exact congrArg (fun C : FullChamber Γ ν => C.1 (.inl w)) h

end Categorification.WeightedKLR

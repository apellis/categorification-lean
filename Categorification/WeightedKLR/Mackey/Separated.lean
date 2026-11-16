/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Induction.Juxtapose

/-!
# Separating a set of strands

A construction used in the proof of B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, Theorem 2.19 (the Mackey filtration of §2.4, after Khovanov–Lauda,
arXiv:0803.4121v2, Proposition 2.18): the intermediate chambers of the factorization of a basis
element through the diagram exchanging two blocks of strands.

For a set `X` of strands of `ν` (given by its indicator `X : Strand ν → Bool`) and two full
chambers `P`, `Q`, the chamber `sep X P Q` places the strands of `X` as in `P` and the other
strands as in `Q`, translated far to the right. On a hyperplane joining two strands of `X` it
agrees with `P`, on one joining two strands outside `X` with `Q`, and on a hyperplane joining a
strand of `X` with a strand outside `X` its sign is `X h.lo`: positive exactly when the first
strand of the hyperplane is the one in `X` (`sep_val`). Unlike the juxtaposition of
`Juxtapose.chamber`, this is a construction inside the arrangement of a single dimension vector,
for an arbitrary set of strands.

A chamber is *separated* by `X` (`IsSeparated X C`) if it has these signs on the hyperplanes
between `X` and its complement; then `sep X C C = C` (`sep_self`).

## Main definitions

* `FullChamber.sepSigns X σ τ`: the sign vector described above.
* `FullChamber.sep X P Q`: the full chamber with the signs `sepSigns X P.1 Q.1`.
* `FullChamber.IsSeparated X C`.

## Main results

* `FullChamber.sep_val`, `FullChamber.isSeparated_sep`, `FullChamber.sep_self`.
-/

namespace Categorification.WeightedKLR

open Juxtapose

variable {I : Type*} {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

namespace FullChamber

/-- The configuration `p` on the strands of `X` and `q` translated by `c` on the others. -/
def sepPoint (X : Strand ν → Bool) (p q : Strand ν → 𝕜) (c : 𝕜) : Strand ν → 𝕜 :=
  fun t => if X t then p t else q t + c

variable (Γ) in
/-- A translation beyond which `sepPoint` meets no hyperplane between `X` and its complement. -/
def sepBound (p q : Strand ν → 𝕜) : 𝕜 :=
  1 + ∑ s, |p s| + ∑ s, |q s| + ∑ e, |Γ.weight e|

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem val_sepPoint_of_true {X : Strand ν → Bool} (p q : Strand ν → 𝕜) (c : 𝕜) {h : Hyp Γ ν}
    (hl : X h.lo = true) (hh : X h.hi = true) : h.val (sepPoint X p q c) = h.val p := by
  rw [Hyp.val_eq, Hyp.val_eq]
  simp [sepPoint, hl, hh]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem val_sepPoint_of_false {X : Strand ν → Bool} (p q : Strand ν → 𝕜) (c : 𝕜) {h : Hyp Γ ν}
    (hl : X h.lo = false) (hh : X h.hi = false) : h.val (sepPoint X p q c) = h.val q := by
  rw [Hyp.val_eq, Hyp.val_eq]
  simp only [sepPoint, hl, hh, Bool.false_eq_true, ↓reduceIte]
  ring

theorem abs_cst_le (h : Hyp Γ ν) : |h.cst| ≤ ∑ e, |Γ.weight e| := by
  rcases h with w | d
  · exact Finset.single_le_sum (f := fun e => |Γ.weight e|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ w.edge)
  · simpa [Hyp.cst] using Finset.sum_nonneg fun e _ => abs_nonneg (Γ.weight e)

/-- On a hyperplane between `X` and its complement, `sepPoint` at large translation is nonzero,
with the sign `X h.lo`. -/
theorem val_sepPoint_of_ne {X : Strand ν → Bool} (p q : Strand ν → 𝕜) {c : 𝕜}
    (hc : sepBound Γ p q ≤ c) {h : Hyp Γ ν} (hne : X h.lo ≠ X h.hi) :
    h.val (sepPoint X p q c) ≠ 0 ∧ (0 < h.val (sepPoint X p q c) ↔ X h.lo = true) := by
  have hp : ∀ s, |p s| ≤ ∑ s, |p s| := fun s =>
    Finset.single_le_sum (f := fun s => |p s|) (fun _ _ => abs_nonneg _) (Finset.mem_univ s)
  have hq : ∀ s, |q s| ≤ ∑ s, |q s| := fun s =>
    Finset.single_le_sum (f := fun s => |q s|) (fun _ _ => abs_nonneg _) (Finset.mem_univ s)
  have hw := abs_cst_le h
  have hc' : 1 + ∑ s, |p s| + ∑ s, |q s| + ∑ e, |Γ.weight e| ≤ c := hc
  rw [Hyp.val_eq]
  cases hl : X h.lo <;> cases hh : X h.hi <;> rw [hl, hh] at hne
  · exact absurd rfl hne
  · -- the first strand is outside `X`, the second in `X`
    simp only [sepPoint, hl, hh, Bool.false_eq_true, ↓reduceIte]
    have h1 := le_abs_self (p h.hi)
    have h2 := neg_abs_le (q h.lo)
    have h3 := neg_abs_le h.cst
    have := hp h.hi
    have := hq h.lo
    have hneg : p h.hi - (q h.lo + c) - h.cst < 0 := by linarith
    exact ⟨hneg.ne, iff_of_false (not_lt.2 hneg.le) (by simp)⟩
  · simp only [sepPoint, hl, hh, Bool.false_eq_true, ↓reduceIte]
    have h1 := neg_abs_le (q h.hi)
    have h2 := le_abs_self (p h.lo)
    have h3 := le_abs_self h.cst
    have := hp h.lo
    have := hq h.hi
    have hpos : 0 < q h.hi + c - p h.lo - h.cst := by linarith
    exact ⟨hpos.ne', iff_of_true hpos (by simp)⟩
  · exact absurd rfl hne

/-- The sign vector of `sepPoint`: that of `σ` between strands of `X`, that of `τ` between
strands outside `X`, and `X h.lo` between `X` and its complement. -/
def sepSigns (X : Strand ν → Bool) (σ τ : Hyp Γ ν → Bool) : Hyp Γ ν → Bool := fun h =>
  if X h.lo = X h.hi then (if X h.lo then σ h else τ h) else X h.lo

theorem isGeneric_sepPoint {X : Strand ν → Bool} {p q : Strand ν → 𝕜} (hp : IsGeneric Γ p)
    (hq : IsGeneric Γ q) {c : 𝕜} (hc : sepBound Γ p q ≤ c) : IsGeneric Γ (sepPoint X p q c) := by
  intro h
  by_cases hne : X h.lo = X h.hi
  · cases hl : X h.lo
    · rw [val_sepPoint_of_false p q c hl (hne ▸ hl)]
      exact hq h
    · rw [val_sepPoint_of_true p q c hl (hne ▸ hl)]
      exact hp h
  · exact (val_sepPoint_of_ne p q hc hne).1

theorem fullSigns_sepPoint (X : Strand ν → Bool) (p q : Strand ν → 𝕜) {c : 𝕜}
    (hc : sepBound Γ p q ≤ c) :
    fullSigns (Γ := Γ) (sepPoint X p q c) = sepSigns X (fullSigns p) (fullSigns q) := by
  funext h
  unfold sepSigns
  have hne := val_sepPoint_of_ne (X := X) p q hc (h := h)
  cases hl : X h.lo <;> cases hh : X h.hi
  · simp [fullSigns, val_sepPoint_of_false p q c hl hh]
  · simpa [fullSigns, hl, hh] using (hne (by simp [hl, hh])).2
  · simpa [fullSigns, hl, hh] using (hne (by simp [hl, hh])).2
  · simp [fullSigns, val_sepPoint_of_true p q c hl hh]

/-- **Separating a set of strands.** The full chamber in which the strands of `X` are placed as
in `P` and the other strands as in `Q`, far to the right. -/
noncomputable def sep (X : Strand ν → Bool) (P Q : FullChamber Γ ν) : FullChamber Γ ν :=
  ofPoint (sepPoint X (point P) (point Q) (sepBound Γ (point P) (point Q)))
    (isGeneric_sepPoint (isGeneric_point P) (isGeneric_point Q) le_rfl)

theorem sep_val (X : Strand ν → Bool) (P Q : FullChamber Γ ν) :
    (sep X P Q).1 = sepSigns X P.1 Q.1 := by
  show fullSigns _ = _
  rw [fullSigns_sepPoint X _ _ le_rfl, fullSigns_point, fullSigns_point]

theorem sep_apply (X : Strand ν → Bool) (P Q : FullChamber Γ ν) (h : Hyp Γ ν) :
    (sep X P Q).1 h =
      if X h.lo = X h.hi then (if X h.lo then P.1 h else Q.1 h) else X h.lo := by
  rw [sep_val]
  rfl

/-- A chamber is separated by `X` if on every hyperplane between `X` and its complement it lies
on the side where the strand of `X` is on the left. -/
def IsSeparated (X : Strand ν → Bool) (C : FullChamber Γ ν) : Prop :=
  ∀ h : Hyp Γ ν, X h.lo ≠ X h.hi → C.1 h = X h.lo

theorem isSeparated_sep (X : Strand ν → Bool) (P Q : FullChamber Γ ν) :
    IsSeparated X (sep X P Q) := fun h hne => by
  simp [sep_apply, hne]

theorem sep_self {X : Strand ν → Bool} {C : FullChamber Γ ν} (hC : IsSeparated X C) :
    sep X C C = C := by
  apply Subtype.ext
  funext h
  rw [sep_apply]
  by_cases hne : X h.lo = X h.hi
  · simp only [hne, ↓reduceIte, ite_self]
  · simp only [hne, ↓reduceIte, hC h hne]

end FullChamber

end Categorification.WeightedKLR

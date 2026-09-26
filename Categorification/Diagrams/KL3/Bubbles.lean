/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.Cyclic

/-!
# Dotted bubbles of `U` as traces

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.1.1,
Definition 3.1, eq. (3.4) (label `eq_positivity_bubbles`) and the degree-zero bubble relations.

The dotted bubbles of Definition 3.1 are traces, in the sense of the diagrammatics library
(`Biadjunction.leftTrace`), of powers of dots:

* `ccwReal_eq_leftTrace`: the counterclockwise bubble with `m` dots in the region `λ` is the left
  trace of `m` upward dots for the biadjunction `E_{+i} 1_λ ⊣⊢ E_{-i} 1_{λ+i_X}` (`biadjEF`);
* `cwReal_eq_leftTrace`: the clockwise bubble with `m` dots in the region `λ` is the left trace of
  `m` downward dots for the biadjunction of the strand `E_{-i} 1_λ` (`biadjFE`).

Consequently (with `n = ⟨i, λ⟩`) the relations of eq. (3.4) and the degree-zero relations read:

* `leftTrace_updots_eq_zero`: `tr(x^α) = 0` for `α < -n - 1` (counterclockwise);
* `leftTrace_downdots_eq_zero`: `tr(x^α) = 0` for `α < n - 1` (clockwise);
* `leftTrace_updots_eq_one`: `tr(x^{-n-1}) = 1` for `n ≤ -1`;
* `leftTrace_downdots_eq_one`: `tr(x^{n-1}) = 1` for `n ≥ 1`.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation Biadjunction

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (k : Type w) [CommRing k]

/-- `m` upward dots on `E_{+i} 1_λ`, as a 2-morphism of `U`. -/
def updots (i : I) (lam : X) (m : ℕ) : strandE RD k i lam ⟶ strandE RD k i lam :=
  (pres RD k).diag (dots RD lam [] (up i) [] m)

/-- The strand `E_{-i} 1_λ` (from `λ - i_X` to `λ` in KL III), as a 1-morphism of `U`. -/
abbrev strandF' (i : I) (lam : X) : (⟨sh RD (dn i) + lam⟩ : U RD k) ⟶ ⟨lam⟩ :=
  (pres RD k).colourHom (⟨dn i, lam⟩ : Col I X)

/-- The biadjunction of the downward strand `E_{-i} 1_λ` and its dual, given by the cups and
caps. -/
abbrev biadjFE (i : I) (lam : X) :
    strandF' RD k i lam ⊣⊢ (pres RD k).dualHom (inv RD).toColourDuality.pivotal (strandF' RD k i lam) :=
  biadjColour RD k (strandF' RD k i lam) ⟨dn i, lam⟩ rfl

/-- `m` downward dots on `E_{-i} 1_λ`, as a 2-morphism of `U`. -/
def downdots (i : I) (lam : X) (m : ℕ) : strandF' RD k i lam ⟶ strandF' RD k i lam :=
  (pres RD k).diag (dots RD lam [] (dn i) [] m)

/-- **The counterclockwise dotted bubble is a trace.** The counterclockwise bubble with `m` dots
in the region `λ` (macro `ccbub`) is the left trace of `m` upward dots on `E_{+i} 1_λ`. -/
theorem ccwReal_eq_leftTrace (lam : X) (i : I) (m : ℕ) :
    (pres RD k).diag (ccwReal RD lam i m) = leftTrace (biadjEF RD k i lam) (updots RD k i lam m) := by
  have h₀ : IsDiag (pres RD k) (biadjEF RD k i lam).right.unit
      [⟨sh RD (dn i) + (sh RD (up i) + lam), [], .cup ⟨dn i, sh RD (up i) + lam⟩, []⟩] :=
    ⟨_, rfl, rfl⟩
  have h₁ : IsDiag (pres RD k) (biadjEF RD k i lam).left.counit
      [⟨lam, [], .cap ⟨up i, lam⟩, []⟩] := ⟨_, rfl, rfl⟩
  have h₂ : IsDiag (pres RD k) (updots RD k i lam m)
      (layList RD lam (List.replicate m ([], .dot (up i), []))) := ⟨_, rfl, rfl⟩
  obtain ⟨D, hD, hL⟩ := IsDiag.comp h₀ (IsDiag.comp (IsDiag.whiskerLeft _ h₂) h₁)
  rw [leftTrace, hD]
  refine (pres RD k).diag_eq_of_layers_eq (f := ccwReal RD lam i m) (g := D) ?_
  rw [hL]
  simp only [ccwReal, layers_mkD, layList_append, layList_cons, layList_nil, List.map_append,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.singleton_append,
    layList, List.map_replicate, Layer.wl, lay, strandF_obj]
  simp only [wt_cons, wt_nil, wd_cons, wd_nil, Shape.dom_cup, Shape.dom_cap, Shape.dom_dot,
    List.nil_append, List.append_nil, List.cons_append, Shape.gen, Letter.dual_mk, Bool.not_true,
    Bool.not_false]
  congr 1
  · region_tac
  · congr 2
    · region_tac
    · region_tac

/-- **The clockwise dotted bubble is a trace.** The clockwise bubble with `m` dots in the region
`λ` (macro `cbub`) is the left trace of `m` downward dots on `E_{-i} 1_λ`. -/
theorem cwReal_eq_leftTrace (lam : X) (i : I) (m : ℕ) :
    (pres RD k).diag (cwReal RD lam i m) = leftTrace (biadjFE RD k i lam) (downdots RD k i lam m) := by
  have h₀ : IsDiag (pres RD k) (biadjFE RD k i lam).right.unit
      [⟨sh RD (up i) + (sh RD (dn i) + lam), [], .cup ⟨up i, sh RD (dn i) + lam⟩, []⟩] :=
    ⟨_, rfl, rfl⟩
  have h₁ : IsDiag (pres RD k) (biadjFE RD k i lam).left.counit
      [⟨lam, [], .cap ⟨dn i, lam⟩, []⟩] := ⟨_, rfl, rfl⟩
  have h₂ : IsDiag (pres RD k) (downdots RD k i lam m)
      (layList RD lam (List.replicate m ([], .dot (dn i), []))) := ⟨_, rfl, rfl⟩
  obtain ⟨D, hD, hL⟩ := IsDiag.comp h₀ (IsDiag.comp (IsDiag.whiskerLeft _ h₂) h₁)
  rw [leftTrace, hD]
  refine (pres RD k).diag_eq_of_layers_eq (f := cwReal RD lam i m) (g := D) ?_
  rw [hL]
  simp only [cwReal, layers_mkD, layList_append, layList_cons, layList_nil, List.map_append,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.singleton_append,
    layList, List.map_replicate, Layer.wl, lay, dualHom_obj,
    Signature.ColourDuality.dualWord_cons, Signature.ColourDuality.dualWord_nil,
    Signature.ColourDuality.pivotal_dual, inv_dual]
  simp only [wt_cons, wt_nil, wd_cons, wd_nil, Shape.dom_cup, Shape.dom_cap, Shape.dom_dot,
    List.nil_append, List.append_nil, List.cons_append, Shape.gen, Letter.dual_mk, Bool.not_true,
    Bool.not_false]
  congr 1
  · region_tac
  · congr 2
    · region_tac
    · region_tac

/-- `⟨i, λ⟩`. -/
local notation "n" => ip RD

/-- **KL III (3.4), counterclockwise**: a counterclockwise bubble with `α < -⟨i,λ⟩ - 1` dots
vanishes. -/
theorem leftTrace_updots_eq_zero (i : I) (lam : X) (α : ℕ) (h : (α : ℤ) < -n i lam - 1) :
    leftTrace (biadjEF RD k i lam) (updots RD k i lam α) = 0 := by
  rw [← ccwReal_eq_leftTrace]
  have := (pres RD k).lin_rel_self (.inr (.ccwNeg i lam α h))
  exact this

/-- **KL III (3.4), clockwise**: a clockwise bubble with `α < ⟨i,λ⟩ - 1` dots vanishes. -/
theorem leftTrace_downdots_eq_zero (i : I) (lam : X) (α : ℕ) (h : (α : ℤ) < n i lam - 1) :
    leftTrace (biadjFE RD k i lam) (downdots RD k i lam α) = 0 := by
  rw [← cwReal_eq_leftTrace]
  have := (pres RD k).lin_rel_self (.inr (.cwNeg i lam α h))
  exact this

/-- **KL III, degree-zero counterclockwise bubble**: for `⟨i,λ⟩ ≤ -1`, the counterclockwise
bubble with `-⟨i,λ⟩ - 1` dots is `1`. -/
theorem leftTrace_updots_eq_one (i : I) (lam : X) (h : n i lam ≤ -1) :
    leftTrace (biadjEF RD k i lam) (updots RD k i lam (-n i lam - 1).toNat) = 𝟙 _ := by
  rw [← ccwReal_eq_leftTrace]
  exact ((pres RD k).diag_eq_of_rel (.inr (.ccwOne i lam h)) rfl).trans ((pres RD k).diag_id _)

/-- **KL III, degree-zero clockwise bubble**: for `⟨i,λ⟩ ≥ 1`, the clockwise bubble with
`⟨i,λ⟩ - 1` dots is `1`. -/
theorem leftTrace_downdots_eq_one (i : I) (lam : X) (h : 1 ≤ n i lam) :
    leftTrace (biadjFE RD k i lam) (downdots RD k i lam (n i lam - 1).toNat) = 𝟙 _ := by
  rw [← cwReal_eq_leftTrace]
  exact ((pres RD k).diag_eq_of_rel (.inr (.cwOne i lam h)) rfl).trans ((pres RD k).diag_id _)

end Categorification.KL3.Diagram

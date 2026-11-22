/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.Diagrams.KL3.LocalizationDots
import Categorification.Diagrams.KL3.SymmetryOmega

/-!
# Inverse dots and downward crossings in `U′`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, proof of
Lemma 3.29. The dot slides of KL III (2.5c–d) hold on downward strands with the sign of `ω̃`
(KL III (3.43)) on crossings of equally labelled strands; multiplied by the inverse dots of `U′`
they give the slides of the inverse dots through downward crossings.

## Main results

* `omT`, `omT_dg`: `ω̃` as a linear map between hom spaces of fixed boundary, on diagrams.
* `dg_slideREq_dn`, `dg_slideLEq_dn`, `dg_slideRNe_dn`, `dg_slideLNe_dn`: the dot slides through
  downward crossings in `U`.
* `toLoc_dnCross_comp_inv_dot_right_eq`, `toLoc_dnCross_comp_inv_dot_left_eq`,
  `toLoc_dnCross_comp_inv_dot_right_eq_of_ne`, `toLoc_dnCross_comp_inv_dot_left_eq_of_ne`: the
  inverse dots slide through downward crossings in `U′`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation Omega

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {k : Type w} [CommRing k] [DecidableEq I]

variable (RD k) in
/-- `ω̃` as a linear map `HOM(E_s 1_ν, E_t 1_ν) → HOM(E_{s*} 1_{-ν}, E_{t*} 1_{-ν})`. -/
def omT (ν : X) (s t : List (Letter I)) :
    ((pres RD k).obj (ob RD ν s) ⟶ (pres RD k).obj (ob RD ν t)) →ₗ[k]
      ((pres RD k).obj (ob RD (-ν) (s.map Letter.dual)) ⟶
        (pres RD k).obj (ob RD (-ν) (t.map Letter.dual))) where
  toFun f := TR RD k (trO ν s).symm (trO ν t).symm ((omegaU RD k).map f)
  map_add' f g := by rw [Functor.map_add, map_add]
  map_smul' r f := by rw [Functor.map_smul, map_smul]; rfl

theorem omT_dg (ν : X) {s t : List (Letter I)} (L : List (LayerData I)) (h : SChain s L t) :
    omT RD k ν s t (dg RD k ν s t L) =
      ((Sig.sgnS L : ℤ) : k) • dg RD k (-ν) (s.map Letter.dual) (t.map Letter.dual) (wls L) := by
  change TR RD k (trO ν s).symm (trO ν t).symm ((omegaU RD k).map (dg RD k ν s t L)) = _
  rw [omegaU_dg ν L h, map_smul, TR_TR]

/-! ### Dot slides through downward crossings in `U` -/

variable (RD k) in
/-- **KL III (2.5c) on downward strands**: `x₀ ψ = ψ x₁ - 1` for the downward crossing of two
strands of colour `c` (the image under `ω̃` of `dg_slideREq`, with its sign `-1`). -/
theorem dg_slideREq_dn (μ : X) (c : I) :
    dg RD k μ [dn c, dn c] [dn c, dn c] [([], .dot (dn c), [dn c]), ([], .cross false c c, [])] =
      dg RD k μ [dn c, dn c] [dn c, dn c] [([], .cross false c c, []), ([dn c], .dot (dn c), [])] -
        dg RD k μ [dn c, dn c] [dn c, dn c] [] := by
  have h := congrArg (omT RD k (-μ) [up c, up c] [up c, up c])
    (dg_slideREq (RD := RD) (k := k) (-μ) c)
  rw [map_add, omT_dg _ [([], Shape.dot (up c), [up c]), ([], Shape.cross true c c, [])] (by schain),
    omT_dg _ [([], Shape.cross true c c, []), ([up c], Shape.dot (up c), [])] (by schain),
    omT_dg _ [] rfl, neg_neg] at h
  simp [Sig.sgnS, Sig.sgnSh, wls, ld, shape, Letter.dual] at h
  have h' := congrArg Neg.neg h
  rw [neg_neg, neg_add, neg_neg, ← sub_eq_add_neg] at h'
  exact h'

variable (RD k) in
/-- **KL III (2.5d) on downward strands**: `ψ x₀ = x₁ ψ - 1` for the downward crossing of two
strands of colour `c`. -/
theorem dg_slideLEq_dn (μ : X) (c : I) :
    dg RD k μ [dn c, dn c] [dn c, dn c] [([], .cross false c c, []), ([], .dot (dn c), [dn c])] =
      dg RD k μ [dn c, dn c] [dn c, dn c] [([dn c], .dot (dn c), []), ([], .cross false c c, [])] -
        dg RD k μ [dn c, dn c] [dn c, dn c] [] := by
  have h := congrArg (omT RD k (-μ) [up c, up c] [up c, up c])
    (dg_slideLEq (RD := RD) (k := k) (-μ) c)
  rw [map_add, omT_dg _ [([], Shape.cross true c c, []), ([], Shape.dot (up c), [up c])] (by schain),
    omT_dg _ [([up c], Shape.dot (up c), []), ([], Shape.cross true c c, [])] (by schain),
    omT_dg _ [] rfl, neg_neg] at h
  simp [Sig.sgnS, Sig.sgnSh, wls, ld, shape, Letter.dual] at h
  have h' := congrArg Neg.neg h
  rw [neg_neg, neg_add, neg_neg, ← sub_eq_add_neg] at h'
  exact h'

variable (RD k) in
/-- **KL III (2.5a) on downward strands** (`c ≠ d`): a dot on the left strand below the downward
crossing equals a dot on the right strand above it. -/
theorem dg_slideRNe_dn (μ : X) (c d : I) (h : c ≠ d) :
    dg RD k μ [dn c, dn d] [dn d, dn c] [([], .dot (dn c), [dn d]), ([], .cross false c d, [])] =
      dg RD k μ [dn c, dn d] [dn d, dn c] [([], .cross false c d, []), ([dn d], .dot (dn c), [])] := by
  have e := congrArg (omT RD k (-μ) [up c, up d] [up d, up c])
    (dg_slideRNe (RD := RD) (k := k) (-μ) c d h)
  rw [omT_dg _ [([], Shape.dot (up c), [up d]), ([], Shape.cross true c d, [])] (by schain),
    omT_dg _ [([], Shape.cross true c d, []), ([up d], Shape.dot (up c), [])] (by schain),
    neg_neg] at e
  simp [Sig.sgnS, Sig.sgnSh, wls, ld, shape, Letter.dual, h] at e
  exact e

variable (RD k) in
/-- **KL III (2.5b) on downward strands** (`c ≠ d`): a dot on the right strand above the downward
crossing equals a dot on the left strand below it. -/
theorem dg_slideLNe_dn (μ : X) (c d : I) (h : c ≠ d) :
    dg RD k μ [dn c, dn d] [dn d, dn c] [([], .cross false c d, []), ([], .dot (dn d), [dn c])] =
      dg RD k μ [dn c, dn d] [dn d, dn c] [([dn c], .dot (dn d), []), ([], .cross false c d, [])] := by
  have e := congrArg (omT RD k (-μ) [up c, up d] [up d, up c])
    (dg_slideLNe (RD := RD) (k := k) (-μ) c d h)
  rw [omT_dg _ [([], Shape.cross true c d, []), ([], Shape.dot (up d), [up c])] (by schain),
    omT_dg _ [([up c], Shape.dot (up d), []), ([], Shape.cross true c d, [])] (by schain),
    neg_neg] at e
  simp [Sig.sgnS, Sig.sgnSh, wls, ld, shape, Letter.dual, h] at e
  exact e

/-! ### Sliding inverse dots through downward crossings

As for upward crossings (`toLoc_cross_comp_inv_dot_right_eq` and its variants), with the
downward slides `dg_slideREq_dn`, `dg_slideLEq_dn`, `dg_slideRNe_dn`, `dg_slideLNe_dn`. Below `ψ`
is the downward crossing on two strands and `x₀`, `x₁` are the dots on the left and right strand.
-/

section InverseSlidesDown

variable (RD k)

/-- In `U′`, `ψ x₁⁻¹ = x₀⁻¹ ψ - x₀⁻¹ x₁⁻¹` for an downward crossing of two strands of colour `c`
(composition is diagrammatic, bottom to top). This is `dg_slideREq_dn` multiplied by the inverse
dots (Webster arXiv:1309.3796v2, proof of Lemma 3.29). -/
theorem toLoc_dnCross_comp_inv_dot_right_eq (μ : X) (c : I) :
    haveI : IsIso ((toLoc RD k).map
        (dg RD k μ [dn c, dn c] [dn c, dn c] [([], .dot (dn c), [dn c])])) :=
      isIso_toLoc_dg_dot RD k μ [] (dn c) [dn c]
    haveI : IsIso ((toLoc RD k).map
        (dg RD k μ [dn c, dn c] [dn c, dn c] [([dn c], .dot (dn c), [])])) :=
      isIso_toLoc_dg_dot RD k μ [dn c] (dn c) []
    (toLoc RD k).map (dg RD k μ [dn c, dn c] [dn c, dn c] [([], .cross false c c, [])]) ≫
        CategoryTheory.inv ((toLoc RD k).map
          (dg RD k μ [dn c, dn c] [dn c, dn c] [([dn c], .dot (dn c), [])])) =
      CategoryTheory.inv ((toLoc RD k).map
          (dg RD k μ [dn c, dn c] [dn c, dn c] [([], .dot (dn c), [dn c])])) ≫
          (toLoc RD k).map (dg RD k μ [dn c, dn c] [dn c, dn c] [([], .cross false c c, [])]) -
        CategoryTheory.inv ((toLoc RD k).map
          (dg RD k μ [dn c, dn c] [dn c, dn c] [([], .dot (dn c), [dn c])])) ≫
          CategoryTheory.inv ((toLoc RD k).map
            (dg RD k μ [dn c, dn c] [dn c, dn c] [([dn c], .dot (dn c), [])])) := by
  have : IsIso ((toLoc RD k).map
      (dg RD k μ [dn c, dn c] [dn c, dn c] [([], .dot (dn c), [dn c])])) :=
    isIso_toLoc_dg_dot RD k μ [] (dn c) [dn c]
  have : IsIso ((toLoc RD k).map
      (dg RD k μ [dn c, dn c] [dn c, dn c] [([dn c], .dot (dn c), [])])) :=
    isIso_toLoc_dg_dot RD k μ [dn c] (dn c) []
  have h := dg_slideREq_dn RD k μ c
  have e1 : dg RD k μ [dn c, dn c] [dn c, dn c]
      [([], .dot (dn c), [dn c]), ([], .cross false c c, [])] =
      dg RD k μ [dn c, dn c] [dn c, dn c] [([], .dot (dn c), [dn c])] ≫
        dg RD k μ [dn c, dn c] [dn c, dn c] [([], .cross false c c, [])] :=
    (dg_comp (show SChain [dn c, dn c] [([], .dot (dn c), [dn c])] [dn c, dn c] from ⟨rfl, rfl⟩)
      (show SChain [dn c, dn c] [([], .cross false c c, [])] [dn c, dn c] from ⟨rfl, rfl⟩)).symm
  have e2 : dg RD k μ [dn c, dn c] [dn c, dn c]
      [([], .cross false c c, []), ([dn c], .dot (dn c), [])] =
      dg RD k μ [dn c, dn c] [dn c, dn c] [([], .cross false c c, [])] ≫
        dg RD k μ [dn c, dn c] [dn c, dn c] [([dn c], .dot (dn c), [])] :=
    (dg_comp (show SChain [dn c, dn c] [([], .cross false c c, [])] [dn c, dn c] from ⟨rfl, rfl⟩)
      (show SChain [dn c, dn c] [([dn c], .dot (dn c), [])] [dn c, dn c] from ⟨rfl, rfl⟩)).symm
  rw [e1, e2, dg_nil] at h
  have h' := congrArg (toLoc RD k).map h
  rw [Functor.map_sub, Functor.map_comp, Functor.map_comp, CategoryTheory.Functor.map_id,
    sub_eq_add_neg] at h'
  have := inv_slide _ _ _ _ h'
  rwa [Preadditive.neg_comp, Category.id_comp, Preadditive.comp_neg, ← sub_eq_add_neg] at this

/-- In `U′`, `ψ x₀⁻¹ = x₁⁻¹ ψ + x₁⁻¹ x₀⁻¹` for an downward crossing of two strands of colour `c`
(composition is diagrammatic, bottom to top). This is `dg_slideLEq_dn` multiplied by the inverse
dots (Webster arXiv:1309.3796v2, proof of Lemma 3.29). -/
theorem toLoc_dnCross_comp_inv_dot_left_eq (μ : X) (c : I) :
    haveI : IsIso ((toLoc RD k).map (dg RD k μ [dn c, dn c] [dn c, dn c] [([], .dot (dn c), [dn c])])) :=
      isIso_toLoc_dg_dot RD k μ [] (dn c) [dn c]
    haveI : IsIso ((toLoc RD k).map (dg RD k μ [dn c, dn c] [dn c, dn c] [([dn c], .dot (dn c), [])])) :=
      isIso_toLoc_dg_dot RD k μ [dn c] (dn c) []
    (toLoc RD k).map (dg RD k μ [dn c, dn c] [dn c, dn c] [([], .cross false c c, [])]) ≫ CategoryTheory.inv ((toLoc RD k).map (dg RD k μ [dn c, dn c] [dn c, dn c] [([], .dot (dn c), [dn c])])) =
      CategoryTheory.inv ((toLoc RD k).map (dg RD k μ [dn c, dn c] [dn c, dn c] [([dn c], .dot (dn c), [])])) ≫ (toLoc RD k).map (dg RD k μ [dn c, dn c] [dn c, dn c] [([], .cross false c c, [])]) +
        CategoryTheory.inv ((toLoc RD k).map (dg RD k μ [dn c, dn c] [dn c, dn c] [([dn c], .dot (dn c), [])])) ≫ CategoryTheory.inv ((toLoc RD k).map (dg RD k μ [dn c, dn c] [dn c, dn c] [([], .dot (dn c), [dn c])])) := by
  have : IsIso ((toLoc RD k).map (dg RD k μ [dn c, dn c] [dn c, dn c] [([], .dot (dn c), [dn c])])) :=
    isIso_toLoc_dg_dot RD k μ [] (dn c) [dn c]
  have : IsIso ((toLoc RD k).map (dg RD k μ [dn c, dn c] [dn c, dn c] [([dn c], .dot (dn c), [])])) :=
    isIso_toLoc_dg_dot RD k μ [dn c] (dn c) []
  have h := dg_slideLEq_dn RD k μ c
  have e1 : dg RD k μ [dn c, dn c] [dn c, dn c] [([], .cross false c c, []), ([], .dot (dn c), [dn c])] = (dg RD k μ [dn c, dn c] [dn c, dn c] [([], .cross false c c, [])]) ≫ (dg RD k μ [dn c, dn c] [dn c, dn c] [([], .dot (dn c), [dn c])]) :=
    (dg_comp (show SChain [dn c, dn c] [([], .cross false c c, [])] [dn c, dn c] from ⟨rfl, rfl⟩) (show SChain [dn c, dn c] [([], .dot (dn c), [dn c])] [dn c, dn c] from ⟨rfl, rfl⟩)).symm
  have e2 : dg RD k μ [dn c, dn c] [dn c, dn c] [([dn c], .dot (dn c), []), ([], .cross false c c, [])] = (dg RD k μ [dn c, dn c] [dn c, dn c] [([dn c], .dot (dn c), [])]) ≫ (dg RD k μ [dn c, dn c] [dn c, dn c] [([], .cross false c c, [])]) :=
    (dg_comp (show SChain [dn c, dn c] [([dn c], .dot (dn c), [])] [dn c, dn c] from ⟨rfl, rfl⟩) (show SChain [dn c, dn c] [([], .cross false c c, [])] [dn c, dn c] from ⟨rfl, rfl⟩)).symm
  rw [e1, e2, dg_nil] at h
  have h' := congrArg (toLoc RD k).map h
  rw [Functor.map_sub, Functor.map_comp, Functor.map_comp, CategoryTheory.Functor.map_id] at h'
  have := inv_slide _ _ _ _ (sub_eq_iff_eq_add.mp h'.symm)
  rwa [Category.id_comp] at this

/-- In `U′`, `ψ x₁⁻¹ = x₀⁻¹ ψ` for an downward crossing of strands of colours `c ≠ d`, the inverse dot
being on the strand of colour `c` (Webster arXiv:1309.3796v2, proof of Lemma 3.29). -/
theorem toLoc_dnCross_comp_inv_dot_right_eq_of_ne (μ : X) (c d : I) (h : c ≠ d) :
    haveI : IsIso ((toLoc RD k).map (dg RD k μ [dn c, dn d] [dn c, dn d] [([], .dot (dn c), [dn d])])) :=
      isIso_toLoc_dg_dot RD k μ [] (dn c) [dn d]
    haveI : IsIso ((toLoc RD k).map (dg RD k μ [dn d, dn c] [dn d, dn c] [([dn d], .dot (dn c), [])])) :=
      isIso_toLoc_dg_dot RD k μ [dn d] (dn c) []
    (toLoc RD k).map (dg RD k μ [dn c, dn d] [dn d, dn c] [([], .cross false c d, [])]) ≫ CategoryTheory.inv ((toLoc RD k).map (dg RD k μ [dn d, dn c] [dn d, dn c] [([dn d], .dot (dn c), [])])) =
      CategoryTheory.inv ((toLoc RD k).map (dg RD k μ [dn c, dn d] [dn c, dn d] [([], .dot (dn c), [dn d])])) ≫ (toLoc RD k).map (dg RD k μ [dn c, dn d] [dn d, dn c] [([], .cross false c d, [])]) := by
  have : IsIso ((toLoc RD k).map (dg RD k μ [dn c, dn d] [dn c, dn d] [([], .dot (dn c), [dn d])])) :=
    isIso_toLoc_dg_dot RD k μ [] (dn c) [dn d]
  have : IsIso ((toLoc RD k).map (dg RD k μ [dn d, dn c] [dn d, dn c] [([dn d], .dot (dn c), [])])) :=
    isIso_toLoc_dg_dot RD k μ [dn d] (dn c) []
  have h := dg_slideRNe_dn RD k μ c d h
  have e1 : dg RD k μ [dn c, dn d] [dn d, dn c] [([], .dot (dn c), [dn d]), ([], .cross false c d, [])] = (dg RD k μ [dn c, dn d] [dn c, dn d] [([], .dot (dn c), [dn d])]) ≫ (dg RD k μ [dn c, dn d] [dn d, dn c] [([], .cross false c d, [])]) :=
    (dg_comp (show SChain [dn c, dn d] [([], .dot (dn c), [dn d])] [dn c, dn d] from ⟨rfl, rfl⟩) (show SChain [dn c, dn d] [([], .cross false c d, [])] [dn d, dn c] from ⟨rfl, rfl⟩)).symm
  have e2 : dg RD k μ [dn c, dn d] [dn d, dn c] [([], .cross false c d, []), ([dn d], .dot (dn c), [])] = (dg RD k μ [dn c, dn d] [dn d, dn c] [([], .cross false c d, [])]) ≫ (dg RD k μ [dn d, dn c] [dn d, dn c] [([dn d], .dot (dn c), [])]) :=
    (dg_comp (show SChain [dn c, dn d] [([], .cross false c d, [])] [dn d, dn c] from ⟨rfl, rfl⟩) (show SChain [dn d, dn c] [([dn d], .dot (dn c), [])] [dn d, dn c] from ⟨rfl, rfl⟩)).symm
  rw [e1, e2] at h
  have h' := congrArg (toLoc RD k).map h
  rw [Functor.map_comp, Functor.map_comp] at h'
  have := inv_slide _ 0 _ _ (h'.trans (add_zero _).symm)
  rwa [Limits.zero_comp, Limits.comp_zero, add_zero] at this

/-- In `U′`, `ψ x₀⁻¹ = x₁⁻¹ ψ` for an downward crossing of strands of colours `c ≠ d`, the inverse dot
being on the strand of colour `d` (Webster arXiv:1309.3796v2, proof of Lemma 3.29). -/
theorem toLoc_dnCross_comp_inv_dot_left_eq_of_ne (μ : X) (c d : I) (h : c ≠ d) :
    haveI : IsIso ((toLoc RD k).map (dg RD k μ [dn d, dn c] [dn d, dn c] [([], .dot (dn d), [dn c])])) :=
      isIso_toLoc_dg_dot RD k μ [] (dn d) [dn c]
    haveI : IsIso ((toLoc RD k).map (dg RD k μ [dn c, dn d] [dn c, dn d] [([dn c], .dot (dn d), [])])) :=
      isIso_toLoc_dg_dot RD k μ [dn c] (dn d) []
    (toLoc RD k).map (dg RD k μ [dn c, dn d] [dn d, dn c] [([], .cross false c d, [])]) ≫ CategoryTheory.inv ((toLoc RD k).map (dg RD k μ [dn d, dn c] [dn d, dn c] [([], .dot (dn d), [dn c])])) =
      CategoryTheory.inv ((toLoc RD k).map (dg RD k μ [dn c, dn d] [dn c, dn d] [([dn c], .dot (dn d), [])])) ≫ (toLoc RD k).map (dg RD k μ [dn c, dn d] [dn d, dn c] [([], .cross false c d, [])]) := by
  have : IsIso ((toLoc RD k).map (dg RD k μ [dn d, dn c] [dn d, dn c] [([], .dot (dn d), [dn c])])) :=
    isIso_toLoc_dg_dot RD k μ [] (dn d) [dn c]
  have : IsIso ((toLoc RD k).map (dg RD k μ [dn c, dn d] [dn c, dn d] [([dn c], .dot (dn d), [])])) :=
    isIso_toLoc_dg_dot RD k μ [dn c] (dn d) []
  have h := dg_slideLNe_dn RD k μ c d h
  have e1 : dg RD k μ [dn c, dn d] [dn d, dn c] [([], .cross false c d, []), ([], .dot (dn d), [dn c])] = (dg RD k μ [dn c, dn d] [dn d, dn c] [([], .cross false c d, [])]) ≫ (dg RD k μ [dn d, dn c] [dn d, dn c] [([], .dot (dn d), [dn c])]) :=
    (dg_comp (show SChain [dn c, dn d] [([], .cross false c d, [])] [dn d, dn c] from ⟨rfl, rfl⟩) (show SChain [dn d, dn c] [([], .dot (dn d), [dn c])] [dn d, dn c] from ⟨rfl, rfl⟩)).symm
  have e2 : dg RD k μ [dn c, dn d] [dn d, dn c] [([dn c], .dot (dn d), []), ([], .cross false c d, [])] = (dg RD k μ [dn c, dn d] [dn c, dn d] [([dn c], .dot (dn d), [])]) ≫ (dg RD k μ [dn c, dn d] [dn d, dn c] [([], .cross false c d, [])]) :=
    (dg_comp (show SChain [dn c, dn d] [([dn c], .dot (dn d), [])] [dn c, dn d] from ⟨rfl, rfl⟩) (show SChain [dn c, dn d] [([], .cross false c d, [])] [dn d, dn c] from ⟨rfl, rfl⟩)).symm
  rw [e1, e2] at h
  have h' := congrArg (toLoc RD k).map h.symm
  rw [Functor.map_comp, Functor.map_comp] at h'
  have := inv_slide _ 0 _ _ (h'.trans (add_zero _).symm)
  rwa [Limits.zero_comp, Limits.comp_zero, add_zero] at this

end InverseSlidesDown

end Categorification.KL3.Diagram

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleBlackPresentation
import Categorification.Diagrams.KL3.SlideCalculus

/-!
# A black KL relation between two signed words

Webster, arXiv:1309.3796v2, §4.5, Definition 4.24. A black KL relation can
be reflected and inserted between two arbitrary signed words. The suffix
starts in the right region of the reflected black word.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe w u v
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) {ℓ : ℕ} (Λ : Fin ℓ → X) {k : Type w} [CommRing k]
  (μ : X) (u v : List (DoubleStrand I ℓ)) (s : List (Letter I))

local notation "T" => signature RD Λ
local notation "ν" => endWeight RD Λ μ u
local notation "tail" => colours RD Λ (endWeight RD Λ μ (u ++ blackWord s)) v
local notation "head" => (Obj.nil μ : Obj T)

private theorem blackSuffix_ok :
    (obj RD Λ μ (u ++ blackWord s ++ [])).WhiskerOK head tail := by
  refine ⟨trivial, rfl, ?_⟩
  change (T).ok ((T).endR μ (colours RD Λ μ (u ++ blackWord s ++ []))) tail
  rw [colours_endR, List.append_nil]
  exact colours_ok ..

private theorem blackSuffix_obj :
    (obj RD Λ μ (u ++ blackWord s ++ [])).whisker head tail =
      obj RD Λ μ (u ++ blackWord s ++ v) := by
  apply Obj.ext (x := (obj RD Λ μ (u ++ blackWord s ++ [])).whisker head tail)
    (y := obj RD Λ μ (u ++ blackWord s ++ v))
  · rfl
  · change colours RD Λ μ (u ++ blackWord s ++ []) ++ tail =
      colours RD Λ μ (u ++ blackWord s ++ v)
    rw [List.append_nil]
    exact (colours_append RD Λ μ (u ++ blackWord s) v).symm

private theorem blackSuffix_diag (d : ob RD ν s ⟶ ob RD ν s) :
    Diagram.cast (Diagram.whisker (blackDiagram RD Λ μ u [] d)
      head tail (blackSuffix_ok RD Λ μ u v s)) (blackSuffix_obj RD Λ μ u v s)
        (blackSuffix_obj RD Λ μ u v s) = blackDiagram RD Λ μ u v d := by
  obtain ⟨xs, h, rfl⟩ := exists_mkD RD ν d
  apply Diagram.ext
  rw [Diagram.layers_cast, Diagram.layers_whisker, layers_blackDiagram_mkD, layers_blackDiagram_mkD]
  simp only [List.map_map]
  apply List.map_congr_left
  rintro ⟨a, g, b⟩ hx
  have hw := h.wt_mem RD ν (a, g, b) hx
  have he : u ++ blackWord b ++ (Move.black (Sig.shape g)).bottom ++ blackWord a =
      u ++ blackWord (a ++ g.dom ++ b) := by
    simp [Move.bottom, Sig.shape_dom, blackWord, List.reverse_append, List.append_assoc]
  let ρ := endWeight RD Λ (endWeight RD Λ μ (u ++ blackWord b)) (Move.black (Sig.shape g)).bottom
  have hρ : endWeight RD Λ ρ (blackWord a) = endWeight RD Λ μ (u ++ blackWord s) := by
    rw [show endWeight RD Λ ρ (blackWord a) =
      endWeight RD Λ μ (u ++ blackWord b ++ (Move.black (Sig.shape g)).bottom ++ blackWord a) from
      by simp [ρ, endWeight_append]]
    rw [he]
    simp only [endWeight_append, endWeight_blackWord]
    exact hw
  apply Layer.ext
  · rfl
  · rfl
  · rfl
  · change colours RD Λ ρ (blackWord a ++ []) ++ tail = colours RD Λ ρ (blackWord a ++ v)
    rw [List.append_nil, colours_append, hρ]

private theorem blackSuffix_linear (f : LinDiagram k (ob RD ν s) (ob RD ν s)) :
    LinDiagram.cast (LinDiagram.whisker (blackLinear RD Λ k μ u [] f)
      head tail (blackSuffix_ok RD Λ μ u v s)) (blackSuffix_obj RD Λ μ u v s)
        (blackSuffix_obj RD Λ μ u v s) = blackLinear RD Λ k μ u v f := by
  induction f using Finsupp.induction_linear with
  | zero => simp [LinDiagram.cast, LinDiagram.whisker]
  | add f g hf hg =>
    rw [map_add, map_add, LinDiagram.whisker_add, LinDiagram.cast_add, hf, hg]
  | single d a =>
    have he : (Finsupp.single d a : LinDiagram k _ _) = a • LinDiagram.of d := by
      change Finsupp.single d a = a • Finsupp.single d (1 : k)
      rw [Finsupp.smul_single_one]
    rw [he, map_smul, map_smul, blackLinear_of, blackLinear_of,
      LinDiagram.whisker_smul, LinDiagram.whisker_of, LinDiagram.cast_smul, LinDiagram.cast_of,
      blackSuffix_diag]

/-- A black KL endomorphism relation remains valid between arbitrary signed
prefix and suffix words in Webster's convention. -/
theorem blackContext_lin_eq_of_KL_eq_suffix
    (P : Presentation.{w, max u v} T k) (f g : LinDiagram k (ob RD ν s) (ob RD ν s))
    (h : (pres RD k).lin f = (pres RD k).lin g) :
    (addBlackKLRelations RD Λ P).lin (blackLinear RD Λ k μ u v f) =
    (addBlackKLRelations RD Λ P).lin (blackLinear RD Λ k μ u v g) := by
  let P₁ := addBlackKLRelations RD Λ P
  let e := blackSuffix_obj RD Λ μ u v s
  have he : P₁.lin (blackLinear RD Λ k μ u [] f) =
      P₁.lin (blackLinear RD Λ k μ u [] g) := blackContext_lin_eq_of_KL_eq RD Λ μ u P f g h
  have hh := congrArg (fun m => P₁.castHom e e (P₁.whisk m head tail)) he
  change P₁.castHom e e (P₁.whisk (P₁.lin (blackLinear RD Λ k μ u [] f)) head tail) =
    P₁.castHom e e (P₁.whisk (P₁.lin (blackLinear RD Λ k μ u [] g)) head tail) at hh
  rw [Presentation.whisk_lin, Presentation.whisk_lin,
    LinDiagram.whisk_of_ok _ (blackSuffix_ok RD Λ μ u v s),
    LinDiagram.whisk_of_ok _ (blackSuffix_ok RD Λ μ u v s)] at hh
  unfold Presentation.castHom at hh
  rw [← P₁.lin_cast _ e e, ← P₁.lin_cast _ e e,
    blackSuffix_linear, blackSuffix_linear] at hh
  exact hh

end Categorification.Stendhal.DoubleDiagram

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

universe w u v v₁
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) {ℓ : ℕ} (Λ : Fin ℓ → X) {k : Type w} [CommRing k]
  (μ : X) (u v : List (DoubleStrand I ℓ)) (s : List (Letter I))

local notation "T" => signature RD Λ
local notation "ν" => endWeight RD Λ μ u
variable {τ : X}
local notation "cut" => (fun (w : List (Letter I)) => endWeight RD Λ μ (u ++ blackWord w))
local notation "tail" => colours RD Λ τ v
local notation "head" => (Obj.nil μ : Obj T)

theorem blackSuffix_ok (hs : cut s = τ) :
    (obj RD Λ μ (u ++ blackWord s ++ [])).WhiskerOK head tail := by
  refine ⟨trivial, rfl, ?_⟩
  change (T).ok ((T).endR μ (colours RD Λ μ (u ++ blackWord s ++ []))) tail
  rw [colours_endR, List.append_nil, ← hs]
  exact colours_ok ..

theorem blackSuffix_obj (hs : cut s = τ) :
    (obj RD Λ μ (u ++ blackWord s ++ [])).whisker head tail =
      obj RD Λ μ (u ++ blackWord s ++ v) := by
  apply Obj.ext (x := (obj RD Λ μ (u ++ blackWord s ++ [])).whisker head tail)
    (y := obj RD Λ μ (u ++ blackWord s ++ v))
  · rfl
  · change colours RD Λ μ (u ++ blackWord s ++ []) ++ tail =
      colours RD Λ μ (u ++ blackWord s ++ v)
    rw [List.append_nil, ← hs]
    exact (colours_append RD Λ μ (u ++ blackWord s) v).symm

theorem blackSuffix_diag {t : List (Letter I)} (hs : cut s = τ) (ht : cut t = τ)
    (d : ob RD ν s ⟶ ob RD ν t) :
    Diagram.cast (Diagram.whisker (blackDiagram RD Λ μ u [] d)
      head tail (blackSuffix_ok RD Λ μ u v s hs)) (blackSuffix_obj RD Λ μ u v s hs)
        (blackSuffix_obj RD Λ μ u v t ht) = blackDiagram RD Λ μ u v d := by
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
    rw [List.append_nil, colours_append, hρ, ← hs]

theorem blackSuffix_linear {t : List (Letter I)} (hs : cut s = τ) (ht : cut t = τ)
    (f : LinDiagram k (ob RD ν s) (ob RD ν t)) :
    LinDiagram.cast (LinDiagram.whisker (blackLinear RD Λ k μ u [] f)
      head tail (blackSuffix_ok RD Λ μ u v s hs)) (blackSuffix_obj RD Λ μ u v s hs)
        (blackSuffix_obj RD Λ μ u v t ht) = blackLinear RD Λ k μ u v f := by
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
      blackSuffix_diag RD Λ μ u v s hs ht]

variable (P : Presentation.{w, v₁} (signature RD Λ) k)
  (hP : ∀ r : (pres RD k).Rel, P.lin (blackMirrorLinear RD Λ ((pres RD k).rel r)) = 0)

/-- Reflection of a black KL Hom between arbitrary signed prefix and suffix words.
The cut weight `τ` fixes the region where the suffix starts. -/
def blackRectangleHom (t : List (Letter I)) (hs : cut s = τ) (ht : cut t = τ) :
    ((pres RD k).obj (ob RD ν s) ⟶ (pres RD k).obj (ob RD ν t)) →ₗ[k]
      (P.obj (obj RD Λ μ (u ++ blackWord s ++ v)) ⟶ P.obj (obj RD Λ μ (u ++ blackWord t ++ v))) :=
  (P.castLinearEquiv (blackSuffix_obj RD Λ μ u v s hs) (blackSuffix_obj RD Λ μ u v t ht)).toLinearMap.comp
    ((P.whiskLinearMap _ _ head tail).comp (blackPrefixHom RD Λ μ u P hP))

@[simp] theorem blackRectangleHom_lin (t : List (Letter I)) (hs : cut s = τ) (ht : cut t = τ)
    (f : LinDiagram k (ob RD ν s) (ob RD ν t)) :
    blackRectangleHom RD Λ μ u v s P hP t hs ht ((pres RD k).lin f) = P.lin (blackLinear RD Λ k μ u v f) := by
  let e := blackSuffix_obj RD Λ μ u v (τ := τ)
  change P.castHom (e s hs) (e t ht) (P.whisk (blackPrefixHom RD Λ μ u P hP ((pres RD k).lin f)) head tail) = _
  rw [blackPrefixHom_lin, Presentation.whisk_lin, LinDiagram.whisk_of_ok _ (blackSuffix_ok RD Λ μ u v s hs)]
  unfold Presentation.castHom
  rw [← P.lin_cast _ (e s hs) (e t ht), blackSuffix_linear RD Λ μ u v s hs ht]

theorem blackRectangleHom_comp (t z : List (Letter I)) (hs : cut s = τ) (ht : cut t = τ) (hz : cut z = τ)
    (f : (pres RD k).obj (ob RD ν s) ⟶ (pres RD k).obj (ob RD ν t))
    (g : (pres RD k).obj (ob RD ν t) ⟶ (pres RD k).obj (ob RD ν z)) :
    blackRectangleHom RD Λ μ u v s P hP z hs hz (f ≫ g) =
      blackRectangleHom RD Λ μ u v s P hP t hs ht f ≫ blackRectangleHom RD Λ μ u v t P hP z ht hz g := by
  let e := blackSuffix_obj RD Λ μ u v (τ := τ)
  change P.castHom (e s hs) (e z hz) (P.whisk (blackPrefixHom RD Λ μ u P hP (f ≫ g)) head tail) =
    P.castHom (e s hs) (e t ht) (P.whisk (blackPrefixHom RD Λ μ u P hP f) head tail) ≫
      P.castHom (e t ht) (e z hz) (P.whisk (blackPrefixHom RD Λ μ u P hP g) head tail)
  rw [blackPrefixHom_comp, Presentation.whisk_comp, Presentation.castHom_comp]

theorem blackRectangleHom_id (hs : cut s = τ) :
    blackRectangleHom RD Λ μ u v s P hP s hs hs (𝟙 _) = 𝟙 _ := by
  rw [← (pres RD k).diag_id, ← Presentation.lin_of, blackRectangleHom_lin, blackLinear_of,
    Presentation.lin_of, blackDiagram_id, Presentation.diag_id]

/-- A black KL endomorphism relation remains valid between arbitrary signed
prefix and suffix words in Webster's convention. -/
theorem blackContext_lin_eq_of_KL_eq_suffix
    (base : Presentation.{w, max u v} T k) (f g : LinDiagram k (ob RD ν s) (ob RD ν s))
    (h : (pres RD k).lin f = (pres RD k).lin g) :
    (addBlackKLRelations RD Λ base).lin (blackLinear RD Λ k μ u v f) =
    (addBlackKLRelations RD Λ base).lin (blackLinear RD Λ k μ u v g) := by
  let B := addBlackKLRelations RD Λ base
  have hB : ∀ r : (pres RD k).Rel, B.lin (blackMirrorLinear RD Λ ((pres RD k).rel r)) = 0 :=
    fun r => B.lin_rel_self (.inr r)
  simpa only [blackRectangleHom_lin] using
    congrArg (blackRectangleHom RD Λ μ u v s B hB s rfl rfl) h

end Categorification.Stendhal.DoubleDiagram

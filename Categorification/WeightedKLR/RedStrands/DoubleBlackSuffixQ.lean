/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleBlackPresentationOf
import Categorification.Diagrams.CLQ.SpanningSetElim

/-!
# A black relation of `U_Q(g)` between two signed words

Webster, arXiv:1309.3796v3, §4.4, Definition 4.24, for black strands carrying the relations of
Cautis–Lauda's `U_Q(g)` (`CLQ.pres RD k sc`). The reflection of `DoubleBlackPresentationOf`
specialized to `𝔅 = CLQ.pres RD k sc`, with the arguments in the order of
`blackRectangleHom`, so that the red-strand arguments written for KL III black strands apply
verbatim.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe w u v v₁
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) {ℓ : ℕ} (Λ : Fin ℓ → X) {k : Type w} [CommRing k]
  (sc : CL.CLScalars C k)

local notation "T" => signature RD Λ
local notation "𝔅" => CLQ.pres RD k sc

/-- Adjoin the reflected relations of `U_Q(g)` to a signed presentation. -/
abbrev addBlackKLRelationsQ (base : Presentation.{w, max u v} T k) :
    Presentation.{w, max u v} T k :=
  addBlackRelationsOf RD Λ (𝔅) base

variable (μ : X) (u v : List (DoubleStrand I ℓ)) (s : List (Letter I))

local notation "ν" => endWeight RD Λ μ u
variable {τ : X}
local notation "cut" => (fun (w : List (Letter I)) => endWeight RD Λ μ (u ++ blackWord w))

/-- A black endomorphism relation of `U_Q(g)` remains valid between arbitrary signed prefix and
suffix words. -/
theorem blackContext_lin_eq_of_KL_eq_suffixQ
    (base : Presentation.{w, max u v} T k) (f g : LinDiagram k (ob RD ν s) (ob RD ν s))
    (h : (𝔅).lin f = (𝔅).lin g) :
    (addBlackKLRelationsQ RD Λ sc base).lin (blackLinear RD Λ k μ u v f) =
    (addBlackKLRelationsQ RD Λ sc base).lin (blackLinear RD Λ k μ u v g) :=
  blackContext_lin_eq_of_eq_suffixOf RD Λ (𝔅) (fun r => CLQ.pres_dom_wfQ r) μ u v s base rfl f g h

variable (P : Presentation.{w, v₁} (signature RD Λ) k)
  (hP : ∀ r : (CLQ.pres RD k sc).Rel,
    P.lin (blackMirrorLinear RD Λ ((CLQ.pres RD k sc).rel r)) = 0)

include hP

/-- Reflection of a Hom of `U_Q(g)` between arbitrary signed prefix and suffix words. -/
abbrev blackRectangleHomQ (t : List (Letter I)) (hs : cut s = τ) (ht : cut t = τ) :
    ((𝔅).obj (ob RD ν s) ⟶ (𝔅).obj (ob RD ν t)) →ₗ[k]
      (P.obj (obj RD Λ μ (u ++ blackWord s ++ v)) ⟶ P.obj (obj RD Λ μ (u ++ blackWord t ++ v))) :=
  blackRectangleHomOf RD Λ (𝔅) (fun r => CLQ.pres_dom_wfQ r) μ u P hP v s t hs ht

@[simp] theorem blackRectangleHom_linQ (t : List (Letter I)) (hs : cut s = τ) (ht : cut t = τ)
    (f : LinDiagram k (ob RD ν s) (ob RD ν t)) :
    blackRectangleHomQ RD Λ sc μ u v s P hP t hs ht ((𝔅).lin f) =
      P.lin (blackLinear RD Λ k μ u v f) :=
  blackRectangleHomOf_lin RD Λ (𝔅) (fun r => CLQ.pres_dom_wfQ r) μ u P hP v s t hs ht f

theorem blackRectangleHom_compQ (t z : List (Letter I)) (hs : cut s = τ) (ht : cut t = τ)
    (hz : cut z = τ) (f : (𝔅).obj (ob RD ν s) ⟶ (𝔅).obj (ob RD ν t))
    (g : (𝔅).obj (ob RD ν t) ⟶ (𝔅).obj (ob RD ν z)) :
    blackRectangleHomQ RD Λ sc μ u v s P hP z hs hz (f ≫ g) =
      blackRectangleHomQ RD Λ sc μ u v s P hP t hs ht f ≫
        blackRectangleHomQ RD Λ sc μ u v t P hP z ht hz g :=
  blackRectangleHomOf_comp RD Λ (𝔅) (fun r => CLQ.pres_dom_wfQ r) μ u P hP v s t z hs ht hz f g

theorem blackRectangleHom_idQ (hs : cut s = τ) :
    blackRectangleHomQ RD Λ sc μ u v s P hP s hs hs (𝟙 _) = 𝟙 _ :=
  blackRectangleHomOf_id RD Λ (𝔅) (fun r => CLQ.pres_dom_wfQ r) μ u P hP v s hs

end Categorification.Stendhal.DoubleDiagram

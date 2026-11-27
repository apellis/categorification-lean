/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleBlackSuffix

/-!
# Black relations of an arbitrary black presentation in a signed context

Webster, arXiv:1309.3796v3, §4.4, Definition 4.24. The reflection of black
diagrams into signed words (`blackMirrorInto`, `blackPrefixHom`,
`blackRectangleHom`) only uses that the source presentation has well-formed
relation sources. Here the source is any presentation `𝔅` on the black
signature, for example `U_Q(g)` for general scalars `Q`, rather than the KL III
presentation.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe w u v v₁

variable {I : Type u} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y)
  {ℓ : ℕ} (Λ : Fin ℓ → X) {k : Type w} [CommRing k]

local notation "S" => psig RD
local notation "T" => signature RD Λ
local notation "M" => blackMirror RD Λ

variable (𝔅 : Presentation.{w, max u v} (psig RD) k) (hwf : 𝔅.WFDom)

/-- Adjoin the reflected relations of a black presentation `𝔅` to a signed
presentation. -/
def addBlackRelationsOf (P : Presentation.{w, max u v} T k) : Presentation.{w, max u v} T k :=
  P.addRels 𝔅.Rel ((M).obj ∘ 𝔅.dom) ((M).obj ∘ 𝔅.cod) fun (r : 𝔅.Rel) =>
    blackMirrorLinear RD Λ (𝔅.rel r)

/-- Reflection from a black presentation `𝔅` into any signed presentation
satisfying the reflected relations of `𝔅`. -/
def blackMirrorIntoOf (P : Presentation.{w, v₁} T k)
    (hP : ∀ r : 𝔅.Rel, P.lin (blackMirrorLinear RD Λ (𝔅.rel r)) = 0) :
    𝔅.Presented ⥤ P.Presented :=
  (M).lift 𝔅 (Q := P) (χ := fun _ => 1)
    (by rintro ((c | e) | c | c) <;> rfl) hwf fun r =>
      (freeLift_mirror_map RD Λ P (𝔅.rel r)).trans (hP r)

instance (P : Presentation.{w, v₁} T k) (hP) :
    (blackMirrorIntoOf RD Λ 𝔅 hwf P hP).Additive := by
  unfold blackMirrorIntoOf
  infer_instance

instance (P : Presentation.{w, v₁} T k) (hP) :
    (blackMirrorIntoOf RD Λ 𝔅 hwf P hP).Linear k := by
  unfold blackMirrorIntoOf
  infer_instance

@[simp] theorem blackMirrorIntoOf_lin (P : Presentation.{w, v₁} T k) (hP)
    {a b : Obj S} (f : LinDiagram k a b) :
    (blackMirrorIntoOf RD Λ 𝔅 hwf P hP).map (𝔅.lin f) = P.lin (blackMirrorLinear RD Λ f) := by
  unfold blackMirrorIntoOf
  rw [SigMirror.lift_lin, freeLift_mirror_map]

section Context

variable (μ : X) (u : List (DoubleStrand I ℓ))
variable (P : Presentation.{w, v₁} (signature RD Λ) k)
  (hP : ∀ r : 𝔅.Rel, P.lin (blackMirrorLinear RD Λ (𝔅.rel r)) = 0)

/-- The Hom map of `𝔅` after reflecting to physical order and inserting a fixed
word on the left. -/
def blackPrefixHomOf {s t : List (Letter I)} :
    (𝔅.obj (ob RD (endWeight RD Λ μ u) s) ⟶ 𝔅.obj (ob RD (endWeight RD Λ μ u) t)) →ₗ[k]
    (P.obj (obj RD Λ μ (u ++ blackWord s ++ [])) ⟶
      P.obj (obj RD Λ μ (u ++ blackWord t ++ []))) :=
  (P.castLinearEquiv (mirror_whisker_obj RD Λ μ u s) (mirror_whisker_obj RD Λ μ u t)).toLinearMap.comp
    ((P.whiskLinearMap _ _ (obj RD Λ μ u) []).comp ((blackMirrorIntoOf RD Λ 𝔅 hwf P hP).mapLinearMap k))

@[simp] theorem blackPrefixHomOf_lin {s t : List (Letter I)}
    (f : LinDiagram k (ob RD (endWeight RD Λ μ u) s) (ob RD (endWeight RD Λ μ u) t)) :
    blackPrefixHomOf RD Λ 𝔅 hwf μ u P hP (𝔅.lin f) = P.lin (blackLinear RD Λ k μ u [] f) := by
  change P.castHom (mirror_whisker_obj RD Λ μ u s) (mirror_whisker_obj RD Λ μ u t)
    (P.whisk ((blackMirrorIntoOf RD Λ 𝔅 hwf P hP).map (𝔅.lin f)) (obj RD Λ μ u) []) = _
  rw [blackMirrorIntoOf_lin, Presentation.whisk_lin,
    LinDiagram.whisk_of_ok _ (mirror_whisker_ok RD Λ μ u s)]
  unfold Presentation.castHom
  rw [← P.lin_cast _ (mirror_whisker_obj RD Λ μ u s) (mirror_whisker_obj RD Λ μ u t),
    mirror_whisker_linear]

theorem blackPrefixHomOf_comp {s t z : List (Letter I)}
    (f : 𝔅.obj (ob RD (endWeight RD Λ μ u) s) ⟶ 𝔅.obj (ob RD (endWeight RD Λ μ u) t))
    (g : 𝔅.obj (ob RD (endWeight RD Λ μ u) t) ⟶ 𝔅.obj (ob RD (endWeight RD Λ μ u) z)) :
    blackPrefixHomOf RD Λ 𝔅 hwf μ u P hP (f ≫ g) =
      blackPrefixHomOf RD Λ 𝔅 hwf μ u P hP f ≫ blackPrefixHomOf RD Λ 𝔅 hwf μ u P hP g := by
  let G := blackMirrorIntoOf RD Λ 𝔅 hwf P hP
  let e := mirror_whisker_obj RD Λ μ u
  change P.castHom (e s) (e z) (P.whisk (G.map (f ≫ g)) (obj RD Λ μ u) []) =
    P.castHom (e s) (e t) (P.whisk (G.map f) (obj RD Λ μ u) []) ≫
      P.castHom (e t) (e z) (P.whisk (G.map g) (obj RD Λ μ u) [])
  rw [Functor.map_comp, Presentation.whisk_comp, Presentation.castHom_comp]

theorem blackPrefixHomOf_id (s : List (Letter I)) :
    blackPrefixHomOf RD Λ 𝔅 hwf μ u P hP (𝟙 (𝔅.obj (ob RD (endWeight RD Λ μ u) s))) = 𝟙 _ := by
  change _ = 𝟙 (P.obj (obj RD Λ μ (u ++ blackWord s ++ [])))
  rw [← 𝔅.diag_id, ← Presentation.lin_of, blackPrefixHomOf_lin, blackLinear_of,
    Presentation.lin_of, blackDiagram_id, Presentation.diag_id]

variable (v : List (DoubleStrand I ℓ)) (s : List (Letter I)) {τ : X}

local notation "ν" => endWeight RD Λ μ u
local notation "cut" => (fun (w : List (Letter I)) => endWeight RD Λ μ (u ++ blackWord w))
local notation "tail" => colours RD Λ τ v
local notation "head" => (Obj.nil μ : Obj T)

/-- Reflection of a Hom of `𝔅` between arbitrary signed prefix and suffix
words. The cut weight `τ` fixes the region where the suffix starts. -/
def blackRectangleHomOf (t : List (Letter I)) (hs : cut s = τ) (ht : cut t = τ) :
    (𝔅.obj (ob RD ν s) ⟶ 𝔅.obj (ob RD ν t)) →ₗ[k]
      (P.obj (obj RD Λ μ (u ++ blackWord s ++ v)) ⟶ P.obj (obj RD Λ μ (u ++ blackWord t ++ v))) :=
  (P.castLinearEquiv (blackSuffix_obj RD Λ μ u v s hs)
      (blackSuffix_obj RD Λ μ u v t ht)).toLinearMap.comp
    ((P.whiskLinearMap _ _ head tail).comp (blackPrefixHomOf RD Λ 𝔅 hwf μ u P hP))

@[simp] theorem blackRectangleHomOf_lin (t : List (Letter I)) (hs : cut s = τ) (ht : cut t = τ)
    (f : LinDiagram k (ob RD ν s) (ob RD ν t)) :
    blackRectangleHomOf RD Λ 𝔅 hwf μ u P hP v s t hs ht (𝔅.lin f) =
      P.lin (blackLinear RD Λ k μ u v f) := by
  let e := blackSuffix_obj RD Λ μ u v (τ := τ)
  change P.castHom (e s hs) (e t ht)
    (P.whisk (blackPrefixHomOf RD Λ 𝔅 hwf μ u P hP (𝔅.lin f)) head tail) = _
  rw [blackPrefixHomOf_lin, Presentation.whisk_lin,
    LinDiagram.whisk_of_ok _ (blackSuffix_ok RD Λ μ u v s hs)]
  unfold Presentation.castHom
  rw [← P.lin_cast _ (e s hs) (e t ht), blackSuffix_linear RD Λ μ u v s hs ht]

theorem blackRectangleHomOf_comp (t z : List (Letter I)) (hs : cut s = τ) (ht : cut t = τ)
    (hz : cut z = τ) (f : 𝔅.obj (ob RD ν s) ⟶ 𝔅.obj (ob RD ν t))
    (g : 𝔅.obj (ob RD ν t) ⟶ 𝔅.obj (ob RD ν z)) :
    blackRectangleHomOf RD Λ 𝔅 hwf μ u P hP v s z hs hz (f ≫ g) =
      blackRectangleHomOf RD Λ 𝔅 hwf μ u P hP v s t hs ht f ≫
        blackRectangleHomOf RD Λ 𝔅 hwf μ u P hP v t z ht hz g := by
  let e := blackSuffix_obj RD Λ μ u v (τ := τ)
  change P.castHom (e s hs) (e z hz)
      (P.whisk (blackPrefixHomOf RD Λ 𝔅 hwf μ u P hP (f ≫ g)) head tail) =
    P.castHom (e s hs) (e t ht) (P.whisk (blackPrefixHomOf RD Λ 𝔅 hwf μ u P hP f) head tail) ≫
      P.castHom (e t ht) (e z hz) (P.whisk (blackPrefixHomOf RD Λ 𝔅 hwf μ u P hP g) head tail)
  rw [blackPrefixHomOf_comp, Presentation.whisk_comp, Presentation.castHom_comp]

theorem blackRectangleHomOf_id (hs : cut s = τ) :
    blackRectangleHomOf RD Λ 𝔅 hwf μ u P hP v s s hs hs (𝟙 _) = 𝟙 _ := by
  rw [← 𝔅.diag_id, ← Presentation.lin_of, blackRectangleHomOf_lin, blackLinear_of,
    Presentation.lin_of, blackDiagram_id, Presentation.diag_id]

include hwf in
/-- A relation between two Homs of `𝔅` remains valid after reflection and
insertion between arbitrary signed prefix and suffix words. -/
theorem blackContext_lin_eq_of_eq_suffixOf
    (base : Presentation.{w, max u v} T k) {t : List (Letter I)} (hst : cut s = cut t)
    (f g : LinDiagram k (ob RD ν s) (ob RD ν t)) (h : 𝔅.lin f = 𝔅.lin g) :
    (addBlackRelationsOf RD Λ 𝔅 base).lin (blackLinear RD Λ k μ u v f) =
    (addBlackRelationsOf RD Λ 𝔅 base).lin (blackLinear RD Λ k μ u v g) := by
  let A := addBlackRelationsOf RD Λ 𝔅 base
  have hA : ∀ r : 𝔅.Rel, A.lin (blackMirrorLinear RD Λ (𝔅.rel r)) = 0 :=
    fun r => A.lin_rel_self (.inr r)
  simpa only [blackRectangleHomOf_lin] using
    congrArg (blackRectangleHomOf RD Λ 𝔅 hwf μ u A hA v s t hst rfl) h

end Context

end Categorification.Stendhal.DoubleDiagram

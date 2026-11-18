/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoublePresentationUnion
import Categorification.WeightedKLR.RedStrands.DoubleSingleRedReduction

/-!
# Spanning families under additional signed diagram relations

Webster, arXiv:1309.3796v2, §4.5, proof of Lemma 4.28 uses spanning by
classes of downward diagrams in the quotient of signed diagrams. A
spanning family of raw diagram classes persists after adjoining relations
with the same signed boundaries and rule for violating cuts.
-/

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe u v w w₁ w₂

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}}
  {k : Type w} [CommRing k] {right : X}

local notation "labels" => (Subtype.val ∘ Λ)
local notation "Triple" => DoubleStendhalTriple RD Λ 0 right
private abbrev tripleRawObj (a : Triple) : Obj (signature RD labels) :=
  obj RD labels 0 a.val.word

variable (P : Presentation.{w, w₁} (signature RD (Subtype.val ∘ Λ)) k)
  (P' : Presentation.{w, w₂} (signature RD (Subtype.val ∘ Λ)) k)
  (h : ∀ a b : Obj (signature RD (Subtype.val ∘ Λ)), P.ideal a b ≤ P'.ideal a b)

/-- The class of a raw signed linear diagram in the violating quotient. -/
def violatingEntry (a b : Triple) : LinDiagram k (tripleRawObj a) (tripleRawObj b) →ₗ[k]
    ((violatingFunctor P right).obj a ⟶ (violatingFunctor P right).obj b) :=
  ((violatingFunctor P right).mapLinearMap k (X := a) (Y := b)).comp
    ((InducedCategory.homLinearEquiv (R := k) (F := tripleObj P (right := right))
      (X := a) (Y := b)).symm.toLinearMap.comp (P.linFunctor.mapLinearMap k))

theorem violatingEntry_surjective (a b : Triple) : Function.Surjective (violatingEntry P a b) := by
  intro f
  obtain ⟨⟨g⟩, rfl⟩ := (violatingFunctor P right).map_surjective f
  obtain ⟨d, rfl⟩ := P.lin_surjective g
  exact ⟨d, rfl⟩

private def boundaryExtension : BoundaryCategory (Λ := Λ) P right ⥤
    BoundaryCategory (Λ := Λ) P' right where
  obj a := a
  map f := InducedCategory.homMk ((P.extension P' h).map f.hom)
  map_id _ := InducedCategory.hom_ext ((P.extension P' h).map_id _)
  map_comp f g := InducedCategory.hom_ext ((P.extension P' h).map_comp f.hom g.hom)

private instance : (boundaryExtension (right := right) P P' h).Additive where
  map_add {_ _} {f g} := InducedCategory.hom_ext
    ((P.extension P' h).map_add (f := f.hom) (g := g.hom))

private instance : (boundaryExtension (right := right) P P' h).Linear k where
  map_smul {_ _} f r := InducedCategory.hom_ext ((P.extension P' h).map_smul r f.hom)

/-- Adjoining signed diagram relations induces a linear functor on the
violating quotients, identity on the boundary indices. -/
def violatingExtension : ViolatingCategory (Λ := Λ) P right ⥤ ViolatingCategory (Λ := Λ) P' right :=
  DoubleViolatingQuotient.lift k (tripleObj (Λ := Λ) P (right := right))
    (boundaryExtension P P' h ⋙ violatingFunctor P' right) fun _ ha =>
      DoubleViolatingQuotient.id_eq_zero k (tripleObj (Λ := Λ) P') ha

instance : (violatingExtension (right := right) P P' h).Additive := by
  unfold violatingExtension
  infer_instance

instance : (violatingExtension (right := right) P P' h).Linear k := by
  unfold violatingExtension
  infer_instance

@[simp] theorem violatingExtension_obj (a : Triple) :
    (violatingExtension P P' h).obj ((violatingFunctor P right).obj a) =
      (violatingFunctor P' right).obj a := rfl

@[simp] theorem violatingExtension_map_entry (a b : Triple)
    (d : LinDiagram k (tripleRawObj a) (tripleRawObj b)) :
    (violatingExtension P P' h).map (violatingEntry P a b d) = violatingEntry P' a b d := rfl

/-- The extension functor is surjective on each signed boundary Hom. -/
theorem violatingExtension_map_surjective (a b : Triple) :
    Function.Surjective ((violatingExtension P P' h).map
      (X := (violatingFunctor P right).obj a) (Y := (violatingFunctor P right).obj b)) := by
  intro f
  obtain ⟨d, rfl⟩ := violatingEntry_surjective P' a b f
  exact ⟨violatingEntry P a b d, violatingExtension_map_entry P P' h a b d⟩

private theorem span_image_eq_top_of_surjective {D M N : Type*}
    [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    (F : M →ₗ[k] N) (hF : Function.Surjective F) (f : D → M) (g : D → N)
    (hfg : ∀ d, F (f d) = g d) (A : Set D) (hA : Submodule.span k (f '' A) = ⊤) :
    Submodule.span k (g '' A) = ⊤ := by
  calc
    Submodule.span k (g '' A) = (Submodule.span k (f '' A)).map F := by
      rw [Submodule.map_span, Set.image_image, funext hfg]
    _ = ⊤ := by rw [hA, Submodule.map_top, LinearMap.range_eq_top.mpr hF]

include h in
/-- Raw diagrams whose classes span a signed boundary Hom still span after
adjoining relations. -/
theorem violatingEntry_span_eq_top_of_ideal_le (a b : Triple)
    (A : Set (LinDiagram k (tripleRawObj a) (tripleRawObj b)))
    (hspan : Submodule.span k (violatingEntry P a b '' A) = ⊤) :
    Submodule.span k (violatingEntry P' a b '' A) = ⊤ := by
  exact span_image_eq_top_of_surjective ((violatingExtension P P' h).mapLinearMap k)
    (violatingExtension_map_surjective P P' h a b) (violatingEntry P a b) (violatingEntry P' a b)
    (violatingExtension_map_entry P P' h a b) A hspan

section OneRed

variable {Λ₁ : Fin 1 → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}}

local notation "L" => (Subtype.val ∘ Λ₁)
local notation "red" => ([Sum.inr 0] : List (DoubleStrand I 1))
local notation "μ" => endWeight RD L 0 red

@[simp] theorem violatingExtension_map_singleRedBlackEntry
    (P₁ P₁' : Presentation.{w, max u v} (signature RD (Subtype.val ∘ Λ₁)) k)
    (h₁ : ∀ a b : Obj (signature RD (Subtype.val ∘ Λ₁)), P₁.ideal a b ≤ P₁'.ideal a b)
    (s t : List (Letter I))
    (hs : endWeight RD L 0 (red ++ blackWord s ++ []) = right)
    (ht : endWeight RD L 0 (red ++ blackWord t ++ []) = right)
    (f : LinDiagram k (ob RD μ s) (ob RD μ t)) :
    (violatingExtension P₁ P₁' h₁).map (singleRedBlackEntry P₁ s t hs ht f) =
      singleRedBlackEntry P₁' s t hs ht f := rfl

/-- A spanning family of black diagrams placed to the right of the unique red
strand remains spanning in the larger quotient. -/
theorem singleRedBlackEntry_span_eq_top_of_ideal_le
    (P₁ P₁' : Presentation.{w, max u v} (signature RD (Subtype.val ∘ Λ₁)) k)
    (h₁ : ∀ a b : Obj (signature RD (Subtype.val ∘ Λ₁)), P₁.ideal a b ≤ P₁'.ideal a b)
    (s t : List (Letter I))
    (hs : endWeight RD L 0 (red ++ blackWord s ++ []) = right)
    (ht : endWeight RD L 0 (red ++ blackWord t ++ []) = right)
    (A : Set (LinDiagram k (ob RD μ s) (ob RD μ t)))
    (hspan : Submodule.span k (singleRedBlackEntry P₁ s t hs ht '' A) = ⊤) :
    Submodule.span k (singleRedBlackEntry P₁' s t hs ht '' A) = ⊤ := by
  exact span_image_eq_top_of_surjective ((violatingExtension P₁ P₁' h₁).mapLinearMap k)
    (violatingExtension_map_surjective P₁ P₁' h₁ (singleRedTriple RD s hs) (singleRedTriple RD t ht))
    (singleRedBlackEntry P₁ s t hs ht) (singleRedBlackEntry P₁' s t hs ht)
    (violatingExtension_map_singleRedBlackEntry P₁ P₁' h₁ s t hs ht) A hspan

end OneRed

end Categorification.Stendhal.DoubleDiagram

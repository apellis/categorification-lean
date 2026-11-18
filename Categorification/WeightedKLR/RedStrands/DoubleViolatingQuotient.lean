/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleDiagram
import Mathlib.CategoryTheory.Quotient.Linear
import Mathlib.CategoryTheory.Quotient.Preadditive

/-!
# The violating quotient for double Stendhal diagrams

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
§4.5, Definition 4.27. For a fixed red family and right weight, use the full
category on the signed boundaries with left weight zero. The span of composites
through a boundary whose first strand is black is the vertical ideal generated
by the identities of such boundaries. A horizontal cut through a violating
strand gives a factorization through one of these boundaries.
-/

noncomputable section

namespace Categorification.Stendhal.DoubleViolatingQuotient

open CategoryTheory QuantumGroup QuantumGroup.UDot

variable {I : Type*} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type*}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}} {right : X}
  {A : Type*} [Category* A]
  (k : Type*) [CommRing k] [Preadditive A] [Linear k A]
  (F : DoubleStendhalTriple RD Λ 0 right → A)

/-- The category indexed by the double Stendhal triples with fixed exterior weights. -/
abbrev BoundaryCategory := InducedCategory A F

/-- The span of composites through a triple with a black strand in the first position
(Webster, arXiv:1309.3796v2, §4.5, Definition 4.27). -/
def ideal (x y : BoundaryCategory F) : Submodule k (x ⟶ y) :=
  Submodule.span k {f | ∃ z : BoundaryCategory F, z.val.IsViolated ∧
    ∃ (u : x ⟶ z) (v : z ⟶ y), f = u ≫ v}

theorem comp_mem_ideal {x y z : BoundaryCategory F} (u : x ⟶ y) {f : y ⟶ z}
    (hf : f ∈ ideal k F y z) : u ≫ f ∈ ideal k F x z := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨w, hw, v, g, rfl⟩ := hf
    exact Submodule.subset_span ⟨w, hw, u ≫ v, g, (Category.assoc _ _ _).symm⟩
  | zero => simp
  | add f g _ _ hf hg => rw [Preadditive.comp_add]; exact Submodule.add_mem _ hf hg
  | smul a f _ hf => rw [Linear.comp_smul]; exact Submodule.smul_mem _ a hf

theorem mem_ideal_comp {x y z : BoundaryCategory F} {f : x ⟶ y} (hf : f ∈ ideal k F x y)
    (v : y ⟶ z) : f ≫ v ∈ ideal k F x z := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨w, hw, u, g, rfl⟩ := hf
    exact Submodule.subset_span ⟨w, hw, u, g ≫ v, Category.assoc _ _ _⟩
  | zero => simp
  | add f g _ _ hf hg => rw [Preadditive.add_comp]; exact Submodule.add_mem _ hf hg
  | smul a f _ hf => rw [Linear.smul_comp]; exact Submodule.smul_mem _ a hf

theorem id_mem_ideal {x : BoundaryCategory F} (hx : x.val.IsViolated) :
    𝟙 x ∈ ideal k F x x :=
  Submodule.subset_span ⟨x, hx, 𝟙 x, 𝟙 x, (Category.id_comp _).symm⟩

/-- Every vertical ideal containing the violated boundary identities contains `ideal`. -/
theorem ideal_le (J : (x y : BoundaryCategory F) → Submodule k (x ⟶ y))
    (comp_mem : ∀ {x y z} (u : x ⟶ y) {v : y ⟶ z}, v ∈ J y z → u ≫ v ∈ J x z)
    (mem_comp : ∀ {x y z} {u : x ⟶ y}, u ∈ J x y → ∀ v : y ⟶ z, u ≫ v ∈ J x z)
    (id_mem : ∀ x : BoundaryCategory F, x.val.IsViolated → 𝟙 x ∈ J x x)
    (x y : BoundaryCategory F) : ideal k F x y ≤ J x y := by
  refine Submodule.span_le.mpr ?_
  rintro f ⟨z, hz, u, v, rfl⟩
  change u ≫ v ∈ J x y
  simpa only [Category.comp_id] using mem_comp (comp_mem u (id_mem z hz)) v

/-- Two diagrams represent the same class when their difference belongs to the violating
ideal. -/
def homRel : HomRel (BoundaryCategory F) := fun x y f g => f - g ∈ ideal k F x y

instance : Congruence (homRel k F) where
  equivalence :=
    { refl := fun f => by rw [homRel, sub_self]; exact Submodule.zero_mem _
      symm := fun h => by rw [homRel, ← neg_sub]; exact Submodule.neg_mem _ h
      trans := fun {f g h} hf hg => by
        rw [homRel, ← sub_add_sub_cancel f g h]
        exact Submodule.add_mem _ hf hg }
  comp_left := fun f g g' h => by
    rw [homRel, ← Preadditive.comp_sub]
    exact comp_mem_ideal k F f h
  comp_right := fun g h => by
    rw [homRel, ← Preadditive.sub_comp]
    exact mem_ideal_comp k F h g

private theorem homRel_add : ∀ ⦃x y : BoundaryCategory F⦄ (f₁ f₂ g₁ g₂ : x ⟶ y),
    homRel k F f₁ f₂ → homRel k F g₁ g₂ → homRel k F (f₁ + g₁) (f₂ + g₂) := by
  intro x y f₁ f₂ g₁ g₂ hf hg
  rw [homRel, add_sub_add_comm]
  exact Submodule.add_mem _ hf hg

private theorem homRel_smul : ∀ (a : k) ⦃x y : BoundaryCategory F⦄ (f g : x ⟶ y),
    homRel k F f g → homRel k F (a • f) (a • g) := by
  intro a x y f g h
  rw [homRel, ← smul_sub]
  exact Submodule.smul_mem _ a h

/-- The violating quotient of the category on a double Stendhal fibre
(Webster, arXiv:1309.3796v2, §4.5, Definition 4.27). -/
abbrev Quotient := CategoryTheory.Quotient (homRel k F)

instance : Preadditive (Quotient k F) :=
  CategoryTheory.Quotient.preadditive _ (homRel_add k F)

/-- The projection from the category of double Stendhal diagrams to the violating quotient. -/
abbrev quotient : BoundaryCategory F ⥤ Quotient k F := CategoryTheory.Quotient.functor _

instance : (quotient k F).Additive :=
  CategoryTheory.Quotient.functor_additive _ (homRel_add k F)

instance : Linear k (Quotient k F) :=
  CategoryTheory.Quotient.linear k _ (homRel_smul k F)

instance : (quotient k F).Linear k :=
  CategoryTheory.Quotient.linear_functor k _ (homRel_smul k F)

theorem map_eq_iff {x y : BoundaryCategory F} (f g : x ⟶ y) :
    (quotient k F).map f = (quotient k F).map g ↔ f - g ∈ ideal k F x y :=
  CategoryTheory.Quotient.functor_map_eq_iff _ f g

/-- A morphism is killed by the projection exactly when it is a linear combination of
morphisms factoring through violated boundaries. -/
theorem map_eq_zero_iff {x y : BoundaryCategory F} (f : x ⟶ y) :
    (quotient k F).map f = 0 ↔ f ∈ ideal k F x y := by
  rw [← (quotient k F).map_zero x y, map_eq_iff, sub_zero]

theorem ker_mapLinearMap (x y : BoundaryCategory F) :
    LinearMap.ker ((quotient k F).mapLinearMap k (X := x) (Y := y)) = ideal k F x y := by
  ext f
  exact LinearMap.mem_ker.trans (map_eq_zero_iff k F f)

theorem map_eq_zero_of_factor {x y z : BoundaryCategory F} (hz : z.val.IsViolated)
    (u : x ⟶ z) (v : z ⟶ y) : (quotient k F).map (u ≫ v) = 0 :=
  (map_eq_zero_iff k F _).mpr <| Submodule.subset_span ⟨z, hz, u, v, rfl⟩

theorem id_eq_zero {x : BoundaryCategory F} (hx : x.val.IsViolated) :
    𝟙 ((quotient k F).obj x) = 0 := by
  rw [← (quotient k F).map_id, map_eq_zero_iff]
  exact id_mem_ideal k F hx

section Lift

variable {D : Type*} [Category* D] [Preadditive D] [Linear k D]
  (G : BoundaryCategory F ⥤ D) [G.Additive] [G.Linear k]
  (hG : ∀ x : BoundaryCategory F, x.val.IsViolated → 𝟙 (G.obj x) = 0)

include hG in
private theorem sub_mem_ideal_map_eq (x y : BoundaryCategory F) (f g : x ⟶ y)
    (h : homRel k F f g) : G.map f = G.map g := by
  have hle : ideal k F x y ≤ LinearMap.ker (G.mapLinearMap k) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨z, hz, u, v, rfl⟩
    change G.map (u ≫ v) = 0
    rw [G.map_comp, ← Category.comp_id (G.map u), hG z hz, Limits.comp_zero, Limits.zero_comp]
  have hh : G.map (f - g) = 0 := LinearMap.mem_ker.mp (hle h)
  exact sub_eq_zero.mp (by simpa only [Functor.map_sub] using hh)

/-- A linear functor that kills the violated boundary identities factors through the
violating quotient. -/
def lift : Quotient k F ⥤ D :=
  CategoryTheory.Quotient.lift _ G (sub_mem_ideal_map_eq k F G hG)

@[simp] theorem quotient_comp_lift : quotient k F ⋙ lift k F G hG = G := rfl

instance : (lift k F G hG).Additive := by
  have : (quotient k F ⋙ lift k F G hG).Additive := by rw [quotient_comp_lift]; infer_instance
  exact Functor.additive_of_full_essSurj_comp (quotient k F) _

instance : (lift k F G hG).Linear k := by
  have : (quotient k F ⋙ lift k F G hG).Linear k := by rw [quotient_comp_lift]; infer_instance
  exact Functor.linear_of_full_essSurj_comp (quotient k F) _

end Lift

end Categorification.Stendhal.DoubleViolatingQuotient

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

variable {I : Type*} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type*}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}} {k : Type*} [CommRing k]
  (P : Presentation (signature RD (fun r => (Λ r).val)) k) {right : X}

/-- Realize a triple with left weight zero as a boundary in a presented diagram category. -/
def tripleObj (b : DoubleStendhalTriple RD Λ 0 right) : P.Presented :=
  P.obj (obj RD (fun r => (Λ r).val) 0 b.val.word)

/-- The category on ordered signed words in the specified right weight fibre. -/
abbrev BoundaryCategory (right : X) :=
  DoubleViolatingQuotient.BoundaryCategory (tripleObj P (right := right))

/-- The category on double Stendhal triples after quotienting by the violated boundary
identities (Webster, arXiv:1309.3796v2, §4.5, Definition 4.27). -/
abbrev ViolatingCategory (right : X) :=
  DoubleViolatingQuotient.Quotient k (tripleObj P (right := right))

/-- The projection to the violating quotient of a presented double diagram category. -/
abbrev violatingFunctor (right : X) : BoundaryCategory P right ⥤ ViolatingCategory P right :=
  DoubleViolatingQuotient.quotient k (tripleObj P (right := right))

/-- The cut just above a cup inserted to the left of a double Stendhal boundary. -/
def leftCupBoundary (b : BoundaryCategory P right) (l : Letter I) :
    BoundaryCategory P right :=
  ⟨⟨Sum.inl l :: Sum.inl l.dual :: b.val.word, b.val.redOrder⟩, by
    refine Eq.trans ?_ b.property
    change endWeight RD (fun r => (Λ r).val) 0 ((Move.black (.cup l)).top ++ b.val.word) =
      endWeight RD (fun r => (Λ r).val) 0 ((Move.black (.cup l)).bottom ++ b.val.word)
    simp only [endWeight_append, Move.endWeight_top]⟩

/-- The cup inserted to the left of a double Stendhal boundary. -/
def leftCup (b : BoundaryCategory P right) (l : Letter I) :
    b ⟶ leftCupBoundary P b l :=
  InducedCategory.homMk
    (P.diag (moveDiagram RD (fun r => (Λ r).val) 0 [] (.black (.cup l)) b.val.word))

/-- The cap closing a cup to the left of a double Stendhal boundary. -/
def leftCap (b : BoundaryCategory P right) (l : Letter I) :
    leftCupBoundary P b l ⟶ b :=
  InducedCategory.homMk
    (P.layer (layer RD (fun r => (Λ r).val) 0 [] (.black (.cap l.dual)) b.val.word)
      (layer_valid ..) (by simp [layer_dom, leftCupBoundary, Move.bottom]) (layer_cod ..))

/-- A plain bubble to the left of a boundary vanishes in the violating quotient. Its middle
horizontal cut has a black strand first in either orientation. -/
theorem map_leftBubble_zero (b : BoundaryCategory P right) (l : Letter I) :
    (violatingFunctor P right).map (leftCup P b l ≫ leftCap P b l) = 0 :=
  DoubleViolatingQuotient.map_eq_zero_of_factor k (tripleObj P) ⟨l, rfl⟩ _ _

end Categorification.Stendhal.DoubleDiagram

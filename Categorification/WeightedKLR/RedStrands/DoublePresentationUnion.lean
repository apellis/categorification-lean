/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringDiagrams.Biadjunction.PivotalInclusion

/-!
# Common presentations for the signed diagram relations

Webster, arXiv:1309.3796v2, Definition 4.27 and the proof of Lemma 4.28.
Local reductions can be proved in separate presentations of the same diagram
signature. The union presents their least common quotient and the projection
to any common quotient keeps each raw diagram unchanged.
-/

noncomputable section

namespace StringDiagrams.Presentation

open CategoryTheory

universe u₀ u₁ u₂ w v v'
variable {S : Signature.{u₀,u₁,u₂}} {k : Type w} [CommRing k]
  (P : Presentation.{w,v} S k) (Q : Presentation.{w,v'} S k)

/-- All the displayed relations of `P` have zero class in `Q`. -/
def RelationsHold : Prop := ∀ r : P.Rel, Q.lin (P.rel r) = 0

/-- For a common signature, checking the displayed relations suffices for
inclusion of their tensor ideal. Interchange holds in each presentation. -/
theorem relationsHold_iff_ideal_le : P.RelationsHold Q ↔ ∀ a b : Obj S, P.ideal a b ≤ Q.ideal a b := by
  constructor
  · intro h a b
    apply Submodule.span_le.mpr
    rintro _ ⟨x, l, r, hw, pre, post⟩
    apply Q.comp_mem_ideal
    refine Q.mem_ideal_comp ?_ post
    cases x with
    | user i =>
      change LinDiagram.whisker (P.rel i) l r hw ∈
        Q.ideal ((P.dom i).whisker l r) ((P.cod i).whisker l r)
      have hwh := Q.lin_whisker_eq_zero (h i) l r hw
      simpa only [sub_zero] using (Q.lin_eq_iff _ 0).mp (hwh.trans Q.lin_zero.symm)
    | interchange x hx => exact Q.whisker_rel_mem_ideal (.interchange x hx) l r hw
  · intro h i
    have hmem := (P.lin_eq_iff (P.rel i) 0).mp ((P.lin_rel_self i).trans P.lin_zero.symm)
    exact ((Q.lin_eq_iff (P.rel i) 0).mpr (h _ _ hmem)).trans Q.lin_zero

/-- The quotient functor associated with an inclusion of presentation ideals. -/
def extension (h : ∀ a b : Obj S, P.ideal a b ≤ Q.ideal a b) : P.Presented ⥤ Q.Presented :=
  CategoryTheory.Quotient.lift P.homRel Q.linFunctor fun a b f g hfg =>
    (Q.lin_eq_iff f g).mpr (h a b hfg)

@[simp] theorem lin_comp_extension (h : ∀ a b : Obj S, P.ideal a b ≤ Q.ideal a b) :
    P.linFunctor ⋙ P.extension Q h = Q.linFunctor := rfl

instance (h : ∀ a b : Obj S, P.ideal a b ≤ Q.ideal a b) : (P.extension Q h).Additive := by
  have : P.linFunctor.EssSurj := CategoryTheory.Quotient.essSurj_functor _
  have : (P.linFunctor ⋙ P.extension Q h).Additive := by simp; infer_instance
  exact Functor.additive_of_full_essSurj_comp P.linFunctor _

instance (h : ∀ a b : Obj S, P.ideal a b ≤ Q.ideal a b) : (P.extension Q h).Linear k := by
  have : P.linFunctor.EssSurj := CategoryTheory.Quotient.essSurj_functor _
  have : (P.linFunctor ⋙ P.extension Q h).Linear k := by simp; infer_instance
  exact Functor.linear_of_full_essSurj_comp P.linFunctor _

@[simp] theorem extension_obj (h : ∀ a b : Obj S, P.ideal a b ≤ Q.ideal a b) (a : Obj S) :
    (P.extension Q h).obj (P.obj a) = Q.obj a := rfl

@[simp] theorem extension_map_lin (h : ∀ a b : Obj S, P.ideal a b ≤ Q.ideal a b)
    {a b : Obj S} (d : LinDiagram k a b) :
    (P.extension Q h).map (P.lin d) = Q.lin d := rfl

@[simp] theorem extension_map_diag (h : ∀ a b : Obj S, P.ideal a b ≤ Q.ideal a b)
    {a b : Obj S} (d : a ⟶ b) : (P.extension Q h).map (P.diag d) = Q.diag d := rfl

/-- Checking an extension by a displayed family amounts to checking the base
and the new relations individually. -/
theorem addRels_relationsHold_iff {J : Type v} (dom cod : J → Obj S)
    (rel : ∀ j, LinDiagram k (dom j) (cod j)) :
    (P.addRels J dom cod rel).RelationsHold Q ↔ P.RelationsHold Q ∧ ∀ j, Q.lin (rel j) = 0 := by
  constructor
  · intro h
    exact ⟨fun i => h (.inl i), fun j => h (.inr j)⟩
  · rintro ⟨hP, hJ⟩ (i | j)
    · exact hP i
    · exact hJ j

/-- Adding a displayed family preserves all base relations. -/
theorem relationsHold_addRels {J : Type v} (dom cod : J → Obj S)
    (rel : ∀ j, LinDiagram k (dom j) (cod j)) :
    P.RelationsHold (P.addRels J dom cod rel) :=
  fun i => (P.addRels J dom cod rel).lin_rel_self (.inl i)

variable (P' : Presentation.{w,v} S k)

/-- The presentation whose displayed relations are the two given families. -/
def union : Presentation.{w,v} S k := P.addRels P'.Rel P'.dom P'.cod P'.rel

/-- Checking the union in another presentation is equivalent to checking both
sets of displayed relations there. -/
theorem union_relationsHold_iff :
    (P.union P').RelationsHold Q ↔ P.RelationsHold Q ∧ P'.RelationsHold Q :=
  P.addRels_relationsHold_iff Q P'.dom P'.cod P'.rel

theorem relationsHold_union_left : P.RelationsHold (P.union P') :=
  P.relationsHold_addRels P'.dom P'.cod P'.rel

theorem relationsHold_union_right : P'.RelationsHold (P.union P') :=
  fun i => (P.union P').lin_rel_self (.inr i)

/-- No additional relation ideal is imposed by taking the union. Its tensor
ideal at each pair of boundaries is the sum of the given tensor ideals. -/
theorem union_ideal_eq_sup (a b : Obj S) : (P.union P').ideal a b = P.ideal a b ⊔ P'.ideal a b := by
  apply le_antisymm
  · have hP : P.ideal a b ≤ P.ideal a b ⊔ P'.ideal a b := le_sup_left
    have hP' : P'.ideal a b ≤ P.ideal a b ⊔ P'.ideal a b := le_sup_right
    apply Submodule.span_le.mpr
    rintro _ ⟨x, l, r, hw, pre, post⟩
    cases x with
    | user i =>
      change P.Rel ⊕ P'.Rel at i
      cases i with
      | inl i =>
        exact hP (Submodule.subset_span (IdealGen.intro (P := P) (.user i) l r hw pre post))
      | inr i =>
        exact hP' (Submodule.subset_span (IdealGen.intro (P := P') (.user i) l r hw pre post))
    | interchange x hx =>
      exact hP (Submodule.subset_span (IdealGen.intro (P := P) (.interchange x hx) l r hw pre post))
  · exact sup_le ((P.relationsHold_iff_ideal_le _).mp (P.relationsHold_union_left P') a b)
      ((P'.relationsHold_iff_ideal_le _).mp (P.relationsHold_union_right P') a b)

end StringDiagrams.Presentation

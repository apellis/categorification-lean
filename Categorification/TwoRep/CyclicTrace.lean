/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Bicategory.Adjunction.Mate
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Categorification.TwoRep.RightwardCrossing

/-!
# Closing traces of cyclic 2-morphisms

Let `l ⊣ r` and `r ⊣ l` be a biadjunction in a bicategory. Closing an endomorphism `f` of `l`
on the right, with the unit of `l ⊣ r` and the counit of `r ⊣ l`, gives an endomorphism
`closeTrace A B f` of the identity. This is the trace of Webster, arXiv:1309.3796v3,
Theorem 3.18, which closes a diagram on the right.

A 2-morphism `α : l₁ ⟶ l₂` between two such biadjoint 1-morphisms is *cyclic* when its
two mates `r₂ ⟶ r₁` agree: the right mate along `l ⊣ r` and the left mate along `r ⊣ l`
(`IsCyclic`). Webster's remark after Theorem 3.18 and Remark 3.19 attribute the failure of
symmetry of the trace to the failure of this condition for crossings; conversely,
`closeTrace_comp_comm` shows that the trace is symmetric on cyclic 2-morphisms:
`closeTrace (α ≫ β) = closeTrace (β ≫ α)` whenever `α` is cyclic.

Cyclic 2-morphisms are closed under identities, composition, sums, scalar multiples,
whiskering (for the composite adjunctions) and associators, so cyclicity of the generators of
a 2-category implies cyclicity of every 2-morphism built from them.

## Main declarations

* `TwoRep.closeTrace`, `TwoRep.IsCyclic`;
* `unit_comp_whiskerRight_eq_conj`, `whiskerLeft_comp_counit_eq_conj`: the unit and counit
  identities of a conjugate between two adjunctions;
* `TwoRep.closeTrace_comp_comm`: the trace is symmetric on cyclic 2-morphisms;
* `IsCyclic.id`, `comp`, `add`, `smul`, `zero`, `whiskerLeft`, `whiskerRight`,
  `associator_hom`, `associator_inv`, `eqToHom`: closure properties.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B] {a b : B}

section Mates

variable {l₁ l₂ : a ⟶ b} {r₁ r₂ : b ⟶ a}

/-- **The unit identity of a conjugate.** For `A₁ : l₁ ⊣ r₁`, `A₂ : l₂ ⊣ r₂` and
`α : l₁ ⟶ l₂`, sliding `α` around the unit turns it into its right mate `r₂ ⟶ r₁`. -/
theorem unit_comp_whiskerRight_eq_conj (A₁ : l₁ ⊣ r₁) (A₂ : l₂ ⊣ r₂) (α : l₁ ⟶ l₂) :
    A₁.unit ≫ α ▷ r₁ = A₂.unit ≫ l₂ ◁ conjugateEquiv A₂ A₁ α := by
  rw [conjugateEquiv_apply']
  symm
  calc _ = 𝟙 _ ⊗≫ (A₂.unit ▷ 𝟙 a ≫ (l₂ ≫ r₂) ◁ A₁.unit) ⊗≫ l₂ ◁ r₂ ◁ α ▷ r₁ ⊗≫
        l₂ ◁ A₂.counit ▷ r₁ ⊗≫ 𝟙 _ := by
        bicategory
    _ = 𝟙 _ ⊗≫ (𝟙 a ◁ A₁.unit ≫ A₂.unit ▷ (l₁ ≫ r₁)) ⊗≫ l₂ ◁ r₂ ◁ α ▷ r₁ ⊗≫
        l₂ ◁ A₂.counit ▷ r₁ ⊗≫ 𝟙 _ := by
        rw [whisker_exchange]
    _ = 𝟙 _ ⊗≫ A₁.unit ⊗≫ ((A₂.unit ▷ l₁ ≫ (l₂ ≫ r₂) ◁ α) ▷ r₁) ⊗≫
        l₂ ◁ A₂.counit ▷ r₁ ⊗≫ 𝟙 _ := by
        bicategory
    _ = 𝟙 _ ⊗≫ A₁.unit ⊗≫ ((𝟙 a ◁ α ≫ A₂.unit ▷ l₂) ▷ r₁) ⊗≫
        l₂ ◁ A₂.counit ▷ r₁ ⊗≫ 𝟙 _ := by
        rw [whisker_exchange]
    _ = 𝟙 _ ⊗≫ A₁.unit ⊗≫ α ▷ r₁ ⊗≫ leftZigzag A₂.unit A₂.counit ▷ r₁ ⊗≫ 𝟙 _ := by
        bicategory
    _ = A₁.unit ≫ α ▷ r₁ := by
        rw [A₂.left_triangle]
        bicategory

/-- **The counit identity of a conjugate.** For `B₁ : r₁ ⊣ l₁`, `B₂ : r₂ ⊣ l₂` and
`γ : r₂ ⟶ r₁`, sliding `γ` around the counit turns it into its mate `l₁ ⟶ l₂`. -/
theorem whiskerLeft_comp_counit_eq_conj (B₁ : r₁ ⊣ l₁) (B₂ : r₂ ⊣ l₂) (γ : r₂ ⟶ r₁) :
    l₁ ◁ γ ≫ B₁.counit = conjugateEquiv B₁ B₂ γ ▷ r₂ ≫ B₂.counit := by
  rw [conjugateEquiv_apply']
  symm
  calc _ = 𝟙 _ ⊗≫ l₁ ◁ B₂.unit ▷ r₂ ⊗≫ l₁ ◁ γ ▷ l₂ ▷ r₂ ⊗≫
        (B₁.counit ▷ (l₂ ≫ r₂) ≫ 𝟙 a ◁ B₂.counit) ⊗≫ 𝟙 _ := by
        bicategory
    _ = 𝟙 _ ⊗≫ l₁ ◁ B₂.unit ▷ r₂ ⊗≫ l₁ ◁ γ ▷ l₂ ▷ r₂ ⊗≫
        ((l₁ ≫ r₁) ◁ B₂.counit ≫ B₁.counit ▷ 𝟙 a) ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange]
    _ = 𝟙 _ ⊗≫ l₁ ◁ B₂.unit ▷ r₂ ⊗≫ l₁ ◁ (γ ▷ (l₂ ≫ r₂) ≫ r₁ ◁ B₂.counit) ⊗≫
        B₁.counit := by
        bicategory
    _ = 𝟙 _ ⊗≫ l₁ ◁ B₂.unit ▷ r₂ ⊗≫ l₁ ◁ (r₂ ◁ B₂.counit ≫ γ ▷ 𝟙 a) ⊗≫ B₁.counit := by
        rw [← whisker_exchange]
    _ = 𝟙 _ ⊗≫ l₁ ◁ leftZigzag B₂.unit B₂.counit ⊗≫ l₁ ◁ γ ⊗≫ B₁.counit := by
        bicategory
    _ = l₁ ◁ γ ≫ B₁.counit := by
        rw [B₂.left_triangle]
        bicategory

end Mates

/-- The trace of an endomorphism `f` of `l`, for `l ⊣ r` and `r ⊣ l`: the unit of `l ⊣ r`,
then `f ▷ r`, then the counit of `r ⊣ l`. -/
def closeTrace {l : a ⟶ b} {r : b ⟶ a} (A : l ⊣ r) (B' : r ⊣ l) (f : l ⟶ l) : 𝟙 a ⟶ 𝟙 a :=
  A.unit ≫ f ▷ r ≫ B'.counit

/-- A 2-morphism `α : l₁ ⟶ l₂` between biadjoint 1-morphisms is cyclic when its right mate
(along `A₁ : l₁ ⊣ r₁`, `A₂ : l₂ ⊣ r₂`) is also its left mate (along `B₁ : r₁ ⊣ l₁`,
`B₂ : r₂ ⊣ l₂`). -/
def IsCyclic {l₁ l₂ : a ⟶ b} {r₁ r₂ : b ⟶ a} (A₁ : l₁ ⊣ r₁) (B₁ : r₁ ⊣ l₁) (A₂ : l₂ ⊣ r₂)
    (B₂ : r₂ ⊣ l₂) (α : l₁ ⟶ l₂) : Prop :=
  conjugateEquiv B₁ B₂ (conjugateEquiv A₂ A₁ α) = α

/-- **The closing trace is symmetric on cyclic 2-morphisms.** -/
theorem closeTrace_comp_comm {l₁ l₂ : a ⟶ b} {r₁ r₂ : b ⟶ a} {A₁ : l₁ ⊣ r₁} {B₁ : r₁ ⊣ l₁}
    {A₂ : l₂ ⊣ r₂} {B₂ : r₂ ⊣ l₂} {α : l₁ ⟶ l₂} (hα : IsCyclic A₁ B₁ A₂ B₂ α)
    (β : l₂ ⟶ l₁) : closeTrace A₁ B₁ (α ≫ β) = closeTrace A₂ B₂ (β ≫ α) := by
  unfold closeTrace
  calc A₁.unit ≫ (α ≫ β) ▷ r₁ ≫ B₁.counit
      = (A₁.unit ≫ α ▷ r₁) ≫ β ▷ r₁ ≫ B₁.counit := by
        rw [comp_whiskerRight]; simp only [Category.assoc]
    _ = A₂.unit ≫ (l₂ ◁ conjugateEquiv A₂ A₁ α ≫ β ▷ r₁) ≫ B₁.counit := by
        rw [unit_comp_whiskerRight_eq_conj A₁ A₂]; simp only [Category.assoc]
    _ = A₂.unit ≫ β ▷ r₂ ≫ (l₁ ◁ conjugateEquiv A₂ A₁ α ≫ B₁.counit) := by
        rw [whisker_exchange]; simp only [Category.assoc]
    _ = A₂.unit ≫ (β ≫ α) ▷ r₂ ≫ B₂.counit := by
        rw [whiskerLeft_comp_counit_eq_conj B₁ B₂, hα, comp_whiskerRight]
        simp only [Category.assoc]

section Closure

variable {l₁ l₂ l₃ : a ⟶ b} {r₁ r₂ r₃ : b ⟶ a} {A₁ : l₁ ⊣ r₁} {B₁ : r₁ ⊣ l₁}
  {A₂ : l₂ ⊣ r₂} {B₂ : r₂ ⊣ l₂} {A₃ : l₃ ⊣ r₃} {B₃ : r₃ ⊣ l₃}

theorem IsCyclic.id (A₁ : l₁ ⊣ r₁) (B₁ : r₁ ⊣ l₁) : IsCyclic A₁ B₁ A₁ B₁ (𝟙 l₁) := by
  simp [IsCyclic]

theorem IsCyclic.comp {α : l₁ ⟶ l₂} {β : l₂ ⟶ l₃} (hα : IsCyclic A₁ B₁ A₂ B₂ α)
    (hβ : IsCyclic A₂ B₂ A₃ B₃ β) : IsCyclic A₁ B₁ A₃ B₃ (α ≫ β) := by
  unfold IsCyclic at *
  rw [← conjugateEquiv_comp A₃ A₂ A₁, ← conjugateEquiv_comp B₁ B₂ B₃, hα, hβ]

theorem IsCyclic.congr_adj {α : l₁ ⟶ l₂} {A₁' : l₁ ⊣ r₁} {B₁' : r₁ ⊣ l₁} {A₂' : l₂ ⊣ r₂}
    {B₂' : r₂ ⊣ l₂} (hα : IsCyclic A₁ B₁ A₂ B₂ α) (h₁ : A₁ = A₁') (h₂ : B₁ = B₁')
    (h₃ : A₂ = A₂') (h₄ : B₂ = B₂') : IsCyclic A₁' B₁' A₂' B₂' α := by
  subst h₁ h₂ h₃ h₄; exact hα

variable [∀ a b : B, Preadditive (a ⟶ b)] [AdditiveWhiskering B]

theorem conjugateEquiv_add' (A₁ : l₁ ⊣ r₁) (A₂ : l₂ ⊣ r₂) (α β : l₂ ⟶ l₁) :
    conjugateEquiv A₁ A₂ (α + β) = conjugateEquiv A₁ A₂ α + conjugateEquiv A₁ A₂ β := by
  simp only [conjugateEquiv_apply', AdditiveWhiskering.add_whiskerRight,
    AdditiveWhiskering.whiskerLeft_add, Preadditive.add_comp, Preadditive.comp_add]

theorem conjugateEquiv_zero' (A₁ : l₁ ⊣ r₁) (A₂ : l₂ ⊣ r₂) :
    conjugateEquiv A₁ A₂ (0 : l₂ ⟶ l₁) = 0 := by
  simp only [conjugateEquiv_apply', AdditiveWhiskering.zero_whiskerRight,
    AdditiveWhiskering.whiskerLeft_zero, Limits.zero_comp, Limits.comp_zero]

theorem IsCyclic.add {α β : l₁ ⟶ l₂} (hα : IsCyclic A₁ B₁ A₂ B₂ α)
    (hβ : IsCyclic A₁ B₁ A₂ B₂ β) : IsCyclic A₁ B₁ A₂ B₂ (α + β) := by
  unfold IsCyclic at *
  rw [conjugateEquiv_add', conjugateEquiv_add', hα, hβ]

theorem IsCyclic.zero : IsCyclic A₁ B₁ A₂ B₂ (0 : l₁ ⟶ l₂) := by
  unfold IsCyclic
  rw [conjugateEquiv_zero', conjugateEquiv_zero']

theorem IsCyclic.sum {ι : Type*} (s : Finset ι) {α : ι → (l₁ ⟶ l₂)}
    (h : ∀ i ∈ s, IsCyclic A₁ B₁ A₂ B₂ (α i)) : IsCyclic A₁ B₁ A₂ B₂ (∑ i ∈ s, α i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsCyclic.zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

section Linear

variable {k : Type*} [CommRing k] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k]

omit [AdditiveWhiskering B] in
theorem conjugateEquiv_smul' (A₁ : l₁ ⊣ r₁) (A₂ : l₂ ⊣ r₂) (s : k) (α : l₂ ⟶ l₁) :
    conjugateEquiv A₁ A₂ (s • α) = s • conjugateEquiv A₁ A₂ α := by
  have h₁ : r₁ ◁ (s • α) ▷ r₂ = s • (r₁ ◁ α ▷ r₂) := by
    change (precomp _ r₁).map ((postcomp _ r₂).map (s • α)) = _
    rw [Functor.map_smul, Functor.map_smul]
    rfl
  simp only [conjugateEquiv_apply', h₁, Linear.smul_comp, Linear.comp_smul]

omit [AdditiveWhiskering B] in
theorem IsCyclic.smul {α : l₁ ⟶ l₂} (hα : IsCyclic A₁ B₁ A₂ B₂ α) (s : k) :
    IsCyclic A₁ B₁ A₂ B₂ (s • α) := by
  unfold IsCyclic at *
  rw [conjugateEquiv_smul', conjugateEquiv_smul', hα]

end Linear

end Closure

section Whiskering

variable {c d : B}

/-- Left whiskering by a biadjoint `W` preserves cyclicity, for the composite adjunctions. -/
theorem IsCyclic.whiskerLeft {w : a ⟶ b} {w' : b ⟶ a} (AW : w ⊣ w') (BW : w' ⊣ w)
    {l₁ l₂ : b ⟶ c} {r₁ r₂ : c ⟶ b} {A₁ : l₁ ⊣ r₁} {B₁ : r₁ ⊣ l₁}
    {A₂ : l₂ ⊣ r₂} {B₂ : r₂ ⊣ l₂} {α : l₁ ⟶ l₂} (hα : IsCyclic A₁ B₁ A₂ B₂ α) :
    IsCyclic (AW.comp A₁) (B₁.comp BW) (AW.comp A₂) (B₂.comp BW) (w ◁ α) := by
  unfold IsCyclic at *
  rw [conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight, hα]

/-- Right whiskering by a biadjoint `W` preserves cyclicity, for the composite adjunctions. -/
theorem IsCyclic.whiskerRight {w : b ⟶ c} {w' : c ⟶ b} (AW : w ⊣ w') (BW : w' ⊣ w)
    {l₁ l₂ : a ⟶ b} {r₁ r₂ : b ⟶ a} {A₁ : l₁ ⊣ r₁} {B₁ : r₁ ⊣ l₁}
    {A₂ : l₂ ⊣ r₂} {B₂ : r₂ ⊣ l₂} {α : l₁ ⟶ l₂} (hα : IsCyclic A₁ B₁ A₂ B₂ α) :
    IsCyclic (A₁.comp AW) (BW.comp B₁) (A₂.comp AW) (BW.comp B₂) (α ▷ w) := by
  unfold IsCyclic at *
  rw [conjugateEquiv_whiskerRight, conjugateEquiv_whiskerLeft, hα]

variable {l₁ : a ⟶ b} {r₁ : b ⟶ a} {l₂ : b ⟶ c} {r₂ : c ⟶ b} {l₃ : c ⟶ d} {r₃ : d ⟶ c}
  (A₁ : l₁ ⊣ r₁) (B₁ : r₁ ⊣ l₁) (A₂ : l₂ ⊣ r₂) (B₂ : r₂ ⊣ l₂) (A₃ : l₃ ⊣ r₃) (B₃ : r₃ ⊣ l₃)

theorem conjugateEquiv_associator_inv :
    conjugateEquiv ((A₁.comp A₂).comp A₃) (A₁.comp (A₂.comp A₃)) (α_ l₁ l₂ l₃).inv =
      (α_ r₃ r₂ r₁).inv := by
  have h := conjugateEquiv_comm ((A₁.comp A₂).comp A₃) (A₁.comp (A₂.comp A₃))
    (α := (α_ l₁ l₂ l₃).inv) (β := (α_ l₁ l₂ l₃).hom) (Iso.hom_inv_id _)
  rw [conjugateEquiv_associator_hom] at h
  rw [← cancel_mono (α_ r₃ r₂ r₁).hom, h, Iso.inv_hom_id]

/-- The associator is cyclic. -/
theorem IsCyclic.associator_hom :
    IsCyclic ((A₁.comp A₂).comp A₃) (B₃.comp (B₂.comp B₁)) (A₁.comp (A₂.comp A₃))
      ((B₃.comp B₂).comp B₁) (α_ l₁ l₂ l₃).hom := by
  unfold IsCyclic
  rw [conjugateEquiv_associator_hom, conjugateEquiv_associator_hom]

/-- The inverse associator is cyclic. -/
theorem IsCyclic.associator_inv :
    IsCyclic (A₁.comp (A₂.comp A₃)) ((B₃.comp B₂).comp B₁) ((A₁.comp A₂).comp A₃)
      (B₃.comp (B₂.comp B₁)) (α_ l₁ l₂ l₃).inv := by
  unfold IsCyclic
  rw [conjugateEquiv_associator_inv, conjugateEquiv_associator_inv]

end Whiskering

end Categorification.TwoRep

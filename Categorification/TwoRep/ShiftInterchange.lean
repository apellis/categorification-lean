/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.DividedPower

/-!
# Coherence of the grading shift with horizontal composition

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, §2.1.2 (`sec:categories`): in a graded additive 2-category the composition
functors `Hom(A, B) × Hom(B, C) → Hom(A, C)` are graded, so a 2-morphism of degree `m` on one
factor of a composite and a 2-morphism of degree `n` on the other factor commute, with the two
composites landing in the same shift `⟨m + n⟩` of the composite 1-morphism (the interchange law
for *shifted* 2-morphisms, used tacitly throughout CL §3: e.g. "sliding" an endomorphism of
`E 1_{n-2}` past a dot on `E 1_n` in `E E 1_{n-2}`).

`GradedBicategory B` (`Basic.lean`) only asks that whiskering on either side commutes with the
shift, through the isomorphisms `whiskerLeftShiftIso : f ≫ g⟦n⟧ ≅ (f ≫ g)⟦n⟧` and
`whiskerRightShiftIso : f⟦m⟧ ≫ g ≅ (f ≫ g)⟦m⟧`, with no compatibility between the two. The mixin
`GradedBicategory.ShiftInterchange B` adds the three compatibilities that hold in any graded
2-category in which the shift is a degree shift (sign-free: this is the *even* setting):

* `whiskerRightShiftIso_natural`: `f⟦m⟧ ≫ g ≅ (f ≫ g)⟦m⟧` is natural in `g`;
* `whiskerLeftShiftIso_natural`: `f ≫ g⟦n⟧ ≅ (f ≫ g)⟦n⟧` is natural in `f`;
* `shift_shift`: the two identifications `f⟦m⟧ ≫ g⟦n⟧ ≅ (f ≫ g)⟦n + m⟧` (shifting the left
  factor first or the right factor first) agree.

The consequence used downstream is `shWhisker_exchange`: for `η : f ⟶ f'⟨m⟩` and
`θ : g ⟶ g'⟨n⟩`, `(η ▷ g) ∘ (f' ◁ θ) = (f ◁ θ) ∘ (η ▷ g')` as shifted 2-morphisms
`f ≫ g ⟶ (f' ≫ g')⟨s⟩`, `s = m + n`. Also `shWhiskerRight_comp`/`shWhiskerLeft_comp`
(functoriality of shifted whiskering; these need no coherence) and the vanishing criterion
`shWhiskerRight_eq_zero_iff`.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]

/-- **Coherence of the grading shift with horizontal composition** (CL §2.1.2, the composition
functors are graded): the whiskering shift isomorphisms of `GradedBicategory` are natural in the
other variable and compatible with each other. See the module docstring. -/
class GradedBicategory.ShiftInterchange (B : Type u) [Bicategory.{w, v} B]
    [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B] :
    Prop where
  whiskerRightShiftIso_natural : ∀ {a b c : B} (f : a ⟶ b) {g g' : b ⟶ c} (θ : g ⟶ g') (m : ℤ),
    (whiskerRightShiftIso f g m).hom ≫ (f ◁ θ)⟦m⟧' =
      (f⟦m⟧ ◁ θ) ≫ (whiskerRightShiftIso f g' m).hom
  whiskerLeftShiftIso_natural : ∀ {a b c : B} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (n : ℤ),
    (whiskerLeftShiftIso f g n).hom ≫ (η ▷ g)⟦n⟧' =
      (η ▷ g⟦n⟧) ≫ (whiskerLeftShiftIso f' g n).hom
  shift_shift : ∀ {a b c : B} (f : a ⟶ b) (g : b ⟶ c) (m n : ℤ),
    (whiskerRightShiftIso f (g⟦n⟧) m).hom ≫ (whiskerLeftShiftIso f g n).hom⟦m⟧' ≫
        (shiftFunctorAdd' (a ⟶ c) n m (n + m) rfl).inv.app (f ≫ g) =
      (whiskerLeftShiftIso (f⟦m⟧) g n).hom ≫ (whiskerRightShiftIso f g m).hom⟦n⟧' ≫
        (shiftFunctorAdd' (a ⟶ c) m n (n + m) (add_comm m n)).inv.app (f ≫ g)

section Functoriality

variable {a b c : B}

theorem shWhiskerRight_eq {f g : a ⟶ b} {m : ℤ} (η : ShiftedHom f g m) (h : b ⟶ c) :
    shWhiskerRight η h = (η ▷ h ≫ (whiskerRightShiftIso g h m).hom : f ≫ h ⟶ (g ≫ h)⟦m⟧) :=
  rfl

theorem shWhiskerLeft_eq (f : a ⟶ b) {g h : b ⟶ c} {n : ℤ} (θ : ShiftedHom g h n) :
    shWhiskerLeft f θ = (f ◁ θ ≫ (whiskerLeftShiftIso f h n).hom : f ≫ g ⟶ (f ≫ h)⟦n⟧) :=
  rfl

/-- Shifted right whiskering is functorial. -/
theorem shWhiskerRight_comp {f g g' : a ⟶ b} {m n s : ℤ} (η : ShiftedHom f g m)
    (η' : ShiftedHom g g' n) (h₀ : n + m = s) (h : b ⟶ c) :
    shWhiskerRight (η.comp η' h₀) h = (shWhiskerRight η h).comp (shWhiskerRight η' h) h₀ :=
  ShiftedHom.map_comp η η' h₀ (postcomp a h)

/-- Shifted left whiskering is functorial. -/
theorem shWhiskerLeft_comp (f : a ⟶ b) {g g' g'' : b ⟶ c} {m n s : ℤ} (θ : ShiftedHom g g' m)
    (θ' : ShiftedHom g' g'' n) (h₀ : n + m = s) :
    shWhiskerLeft f (θ.comp θ' h₀) = (shWhiskerLeft f θ).comp (shWhiskerLeft f θ') h₀ :=
  ShiftedHom.map_comp θ θ' h₀ (precomp c f)

/-- `η ▷ h = 0` as a shifted 2-morphism iff `η ▷ h = 0` as a 2-morphism. -/
theorem shWhiskerRight_eq_zero_iff {f g : a ⟶ b} {m : ℤ} (η : ShiftedHom f g m) (h : b ⟶ c) :
    shWhiskerRight η h = 0 ↔ (η ▷ h : f ≫ h ⟶ g⟦m⟧ ≫ h) = 0 := by
  rw [shWhiskerRight_eq]
  constructor
  · intro h0
    have := congrArg (fun φ => φ ≫ (whiskerRightShiftIso g h m).inv) h0
    simpa using this
  · intro h0
    change (η ▷ h) ≫ _ = 0
    rw [h0, zero_comp]

theorem shWhiskerLeft_eq_zero_iff (f : a ⟶ b) {g h : b ⟶ c} {n : ℤ} (θ : ShiftedHom g h n) :
    shWhiskerLeft f θ = 0 ↔ (f ◁ θ : f ≫ g ⟶ f ≫ h⟦n⟧) = 0 := by
  rw [shWhiskerLeft_eq]
  constructor
  · intro h0
    have := congrArg (fun φ => φ ≫ (whiskerLeftShiftIso f h n).inv) h0
    simpa using this
  · intro h0
    change (f ◁ θ) ≫ _ = 0
    rw [h0, zero_comp]

end Functoriality

/-! ## The interchange law for shifted 2-morphisms -/

section Exchange

variable [GradedBicategory.ShiftInterchange B] {a b c : B}

/-- **The interchange law for shifted 2-morphisms**: for `η : f ⟶ f'⟨m⟩` and `θ : g ⟶ g'⟨n⟩`,
`(η ▷ g) ∘ (f' ◁ θ) = (f ◁ θ) ∘ (η ▷ g') : f ≫ g ⟶ (f' ≫ g')⟨s⟩` (`s = m + n`). -/
theorem shWhisker_exchange {f f' : a ⟶ b} {g g' : b ⟶ c} {m n s : ℤ} (η : ShiftedHom f f' m)
    (θ : ShiftedHom g g' n) (h₁ : n + m = s) (h₂ : m + n = s) :
    (shWhiskerRight η g).comp (shWhiskerLeft f' θ) h₁ =
      (shWhiskerLeft f θ).comp (shWhiskerRight η g') h₂ := by
  subst h₁
  have hs : m + n = n + m := h₂
  have e := GradedBicategory.ShiftInterchange.shift_shift f' g' m n
  have N1 := GradedBicategory.ShiftInterchange.whiskerRightShiftIso_natural f' θ m
  have N2 := GradedBicategory.ShiftInterchange.whiskerLeftShiftIso_natural η g' n
  simp only [ShiftedHom.comp, shWhiskerRight_eq, shWhiskerLeft_eq, Functor.map_comp,
    Category.assoc]
  -- move `(f' ◁ θ)⟦m⟧'` past the right-whiskering shift isomorphism, and symmetrically
  rw [reassoc_of% N1, reassoc_of% N2]
  -- the interchange law for unshifted 2-morphisms
  rw [← whisker_exchange_assoc]
  exact congrArg (fun φ => (f ◁ θ) ≫ (η ▷ g'⟦n⟧) ≫ φ) e

end Exchange

end Categorification.TwoRep

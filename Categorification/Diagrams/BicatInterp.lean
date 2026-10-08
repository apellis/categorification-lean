/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringDiagrams.Interpretation
import Mathlib.CategoryTheory.Bicategory.Coherence
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.Bicategory.Adjunction.Mate
import Mathlib.Tactic.CategoryTheory.Bicategory.Basic

/-!
# Interpreting a presented 2-category in a bicategory

`StringDiagrams.Presentation.lift` produces functors from the presented category `P.Presented` of
a presentation `P` on a signature `S` to a *1-category* `D`. To interpret `P` in a bicategory `C`
we fix the two outer regions `s₀`, `t₀` and take for `D` the hom category
`C(M.obj t₀, M.obj s₀)`: words with these outer regions go to composites of the images of their
strands, other objects to `0`. (In Mathlib's diagrammatic order, a word `c₁ c₂ ⋯ c_n`, read from
the left region to the right region, is the composite `c_n ≫ ⋯ ≫ c₁` from the right region to
the left region.)

A *model* `M` of `S` in `C` assigns an object to every region and a 1-morphism to every colour.
Words are interpreted through Mathlib's free bicategory on the quiver of regions and colours
(`FreeBicategory.lift`), so that all the canonical isomorphisms between bracketings of words
(`splitIso`) are images of 2-morphisms of the free bicategory, which is locally thin (Mathlib's
coherence theorem `FreeBicategory.locally_thin`).

## Main definitions

* `RQ S`: the quiver of regions, an arrow `x → y` being a colour from the region `x` on its right
  to the region `y` on its left;
* `fw s w t`: a well-formed word `w` from `s` (to `t`) as a 1-morphism `t ⟶ s` of the free
  bicategory, through the regions named by its strands (the right region of each strand but the
  last, which ends in `t`); `splitIso`: `fw (u ++ w) ≅ fw w ≫ fw u`;
* `Model S C` (with `Model.ofStrand`), `Model.pre`, `Model.word`: a model of `S` in `C` and the
  images of words; a model gives the image of a strand between any two regions equal to its
  right and left regions (`Model.strandAt`), so that no transport along equalities of regions is
  forced on it;
  `GenImg M`: images of the generators, between any regions equal to their left and right
  regions (a layer is split at the regions named by its strands, `coreC`, not at the regions
  computed from its generator, so that equalities of regions such as `λ + i_X - i_X = λ` never
  have to be decided definitionally);
* `objI`, `layerI`, `interp G s₀ t₀`: the interpretation with outer regions `s₀`, `t₀`.

## Main results

* `coreC_whisker`, `mapChain_whisker`: **whiskering** `u ⊗ f ⊗ v` of a diagram is sent to the image
  of `f` whiskered by the images of `v` and `u`, up to images of free 2-morphisms (`midK`);
* `freeLift_whisker_eq_zero`: a linear combination of diagrams killed by the interpretation with
  its own outer regions has all its whiskerings killed by every interpretation;
* `functor_map_gh_eq_hg`: the (even) **interchange law** holds;
* `respects`: hence `P.Respects (interp G s₀ t₀).functor` as soon as every relation of `P` that
  can occur in the hom category of `s₀`, `t₀` is killed with its own outer regions (all generators
  even), so that `Presentation.lift` gives a linear functor from `P.Presented` to
  `C(M.obj t₀, M.obj s₀)`;
* normal forms for checking relations: `mid_conj`, `mid_assoc`, `mid_comp`, `midK_canon`,
  `conj_key`, `exch_key` (interchange), `zig_key`, `zig_key'`, `zag_key'` (zigzags from an
  adjunction), `rot_key`, `rotL_key` (rotations of a generator by a cup and a cap: its mates);
  `hom_of_congr`, `comp_of_congr`, `lift_map₂_eqToHom` for strands whose colours are only
  propositionally equal.

The hom categories of `C` are assumed preadditive with zero objects (and `R`-linear, with linear
whiskering, for the reduction of soundness); these hypotheses are only used to send objects with
other outer regions to `0`.
-/

noncomputable section

namespace Categorification.Diagrams.BicatInterp

open CategoryTheory Bicategory StringDiagrams

universe w₁ w₂ u₀ u₁ u₂ v₁ v₂

variable {S : Signature.{u₀, u₁, u₂}}

/-- The quiver of regions: an arrow `x ⟶ y` is a colour whose right region is `x` and whose left
region is `y`. -/
def RQ (S : Signature.{u₀, u₁, u₂}) : Type u₀ := S.Region

instance (S : Signature.{u₀, u₁, u₂}) : Quiver (RQ S) where
  Hom x y := {c : S.Colour // S.colourTgt c = x ∧ S.colourSrc c = y}

/-- A region as a vertex of the quiver. -/
abbrev rq (x : S.Region) : RQ S := x

/-- The free bicategory on the quiver of regions. -/
abbrev FB (S : Signature.{u₀, u₁, u₂}) := FreeBicategory (RQ S)

/-- A region as an object of the free bicategory. -/
abbrev fo (x : S.Region) : FB S := x

/-- **A well-formed word `w` read from the region `s`**, ending in the region `t`, as a
1-morphism `t ⟶ s` of the free bicategory. The region between two consecutive strands is the
right region of the left one, and the last strand is taken to end in `t` itself, so that no
transport along an equality of regions occurs in a nonempty word. -/
def fw : (s : S.Region) → (w : List S.Colour) → (t : S.Region) → S.ok s w → S.endR s w = t →
    (fo t ⟶ fo s)
  | _, [], _, _, rfl => 𝟙 _
  | s, [c], t, h, e => FreeBicategory.Hom.of (show rq t ⟶ rq s from ⟨c, e, h.1⟩)
  | _, c :: c' :: w, t, h, e =>
    fw (S.colourTgt c) (c' :: w) t h.2 e ≫ FreeBicategory.Hom.of ⟨c, rfl, h.1⟩

theorem fw_nil (s : S.Region) (h : S.ok s []) : fw s [] s h rfl = 𝟙 (fo s) := rfl

theorem fw_single (s : S.Region) (c : S.Colour) (t : S.Region) (h : S.ok s [c])
    (e : S.endR s [c] = t) :
    fw s [c] t h e = FreeBicategory.Hom.of (show rq t ⟶ rq s from ⟨c, e, h.1⟩) :=
  rfl

theorem fw_cons₂ (s : S.Region) (c c' : S.Colour) (w : List S.Colour) (t : S.Region)
    (h : S.ok s (c :: c' :: w)) (e : S.endR s (c :: c' :: w) = t) :
    fw s (c :: c' :: w) t h e =
      fw (S.colourTgt c) (c' :: w) t h.2 e ≫ FreeBicategory.Hom.of ⟨c, rfl, h.1⟩ :=
  rfl

/-- The proof irrelevance of `fw` in its region arguments: equal regions give equal words up to
transport. -/
theorem fw_eq {s t : S.Region} {w w' : List S.Colour} (hw : w = w') (h : S.ok s w)
    (e : S.endR s w = t) (h' : S.ok s w') (e' : S.endR s w' = t) :
    fw s w t h e = fw s w' t h' e' := by
  subst hw; rfl

theorem fw_congr {s : S.Region} {w w' : List S.Colour} {t : S.Region} (hw : w = w')
    (h : S.ok s w) (e : S.endR s w = t) :
    fw s w t h e = fw s w' t (hw ▸ h) (hw ▸ e) := by
  subst hw; rfl

theorem ok_append_of {s : S.Region} {u w : List S.Colour} {m : S.Region} (hu : S.ok s u)
    (hm : S.endR s u = m) (hw : S.ok m w) : S.ok s (u ++ w) := by
  rw [Signature.ok_append, hm]; exact ⟨hu, hw⟩

theorem endR_append_of {s : S.Region} {u w : List S.Colour} {m t : S.Region}
    (hm : S.endR s u = m) (ht : S.endR m w = t) : S.endR s (u ++ w) = t := by
  rw [Signature.endR_append, hm, ht]

/-- **Splitting a word**: `fw (u ++ w) ≅ fw w ≫ fw u` in the free bicategory, for any region `m`
equal to the end of `u`. -/
def splitIso : (s : S.Region) → (u w : List S.Colour) → (m t : S.Region) → (hu : S.ok s u) →
    (hm : S.endR s u = m) → (hw : S.ok m w) → (ht : S.endR m w = t) →
    (fw s (u ++ w) t (ok_append_of hu hm hw) (endR_append_of hm ht) ≅
      fw m w t hw ht ≫ fw s u m hu hm)
  | _, [], _, _, _, _, rfl, _, _ => (ρ_ _).symm
  | _, [_], [], _, _, _, _, _, rfl => (λ_ _).symm
  | _, [_], _ :: _, _, _, _, rfl, _, _ => Iso.refl _
  | _, c :: c' :: u, w, m, t, hu, hm, hw, ht =>
    whiskerRightIso (splitIso (S.colourTgt c) (c' :: u) w m t hu.2 hm hw ht)
      (FreeBicategory.Hom.of ⟨c, rfl, hu.1⟩) ≪≫ α_ _ _ _

/-! ## Models -/

/-- **A model of the signature `S` in a bicategory `C`**: an object for every region and, for
every colour, a 1-morphism from the image of its right region to that of its left region. The
image of a colour is given between any two regions *equal* to its right and left regions
(`strandAt`), so that a model can choose it without transport along these equalities (a model
given by one 1-morphism per colour is `Model.ofStrand`). -/
structure Model (S : Signature.{u₀, u₁, u₂}) (C : Type w₁) [Bicategory.{w₂, v₂} C] where
  /-- The image of a region. -/
  obj : S.Region → C
  /-- The image of a colour, between regions equal to its right and left regions. -/
  strandAt : (c : S.Colour) → (x y : S.Region) → S.colourTgt c = x → S.colourSrc c = y →
    (obj x ⟶ obj y)

/-- The model given by one 1-morphism per colour (transported along equalities of regions). -/
def Model.ofStrand {C : Type w₁} [Bicategory.{w₂, v₂} C] (obj : S.Region → C)
    (strand : (c : S.Colour) → (obj (S.colourTgt c) ⟶ obj (S.colourSrc c))) : Model S C where
  obj := obj
  strandAt c _ _ hx hy := by subst hx hy; exact strand c

variable {C : Type w₁} [Bicategory.{w₂, v₂} C] (M : Model S C)

/-- The model as a prefunctor on the quiver of regions. -/
def Model.pre : Prefunctor (RQ S) C where
  obj := M.obj
  map := fun {x y} c => M.strandAt c.1 x y c.2.1 c.2.2

theorem Model.pre_map_mk (c : S.Colour) {x y : S.Region} (hx : S.colourTgt c = x)
    (hy : S.colourSrc c = y) :
    M.pre.map (⟨c, hx, hy⟩ : rq x ⟶ rq y) = M.strandAt c x y hx hy := rfl

/-- The pseudofunctor from the free bicategory determined by the model. -/
abbrev Model.lift : FB S ⥤ᵖ C := FreeBicategory.lift (B := RQ S) M.pre

/-- **The image of a word**: `M.word s w t : M.obj t ⟶ M.obj s`. -/
abbrev Model.word (s : S.Region) (w : List S.Colour) (t : S.Region) (h : S.ok s w)
    (e : S.endR s w = t) : M.lift.obj (fo t) ⟶ M.lift.obj (fo s) :=
  M.lift.map (fw s w t h e)

theorem lift_map_of {x y : RQ S} (f : x ⟶ y) :
    M.lift.map (FreeBicategory.Hom.of f) = M.pre.map f := rfl

@[simp] theorem lift_map_fw_nil (s : S.Region) (h : S.ok s []) :
    M.lift.map (fw s [] s h rfl) = 𝟙 _ := rfl

theorem lift_map_fw_single (s : S.Region) (c : S.Colour) (t : S.Region) (h : S.ok s [c])
    (e : S.endR s [c] = t) : M.lift.map (fw s [c] t h e) = M.strandAt c t s e h.1 := rfl

theorem lift_map_fw_cons₂ (s : S.Region) (c c' : S.Colour) (w : List S.Colour) (t : S.Region)
    (h : S.ok s (c :: c' :: w)) (e : S.endR s (c :: c' :: w) = t) :
    M.lift.map (fw s (c :: c' :: w) t h e) =
      M.lift.map (fw (S.colourTgt c) (c' :: w) t h.2 e) ≫ M.strandAt c _ _ rfl h.1 := rfl

/-- Free 2-morphisms between parallel 1-morphisms are equal (coherence). -/
theorem free_eq {a b : FB S} {f g : a ⟶ b} (η θ : f ⟶ g) : η = θ :=
  Subsingleton.elim _ _

/-- The images of two parallel free 2-morphisms agree. -/
theorem lift_map₂_eq {a b : FB S} {f g : a ⟶ b} (η θ : f ⟶ g) :
    M.lift.map₂ η = M.lift.map₂ θ := by
  rw [free_eq η θ]


/-! ## The lifted pseudofunctor on structural 2-morphisms -/

section LiftLemmas

variable {a b c d : FB S}

@[simp] theorem lift_map₂_whiskerLeft (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) :
    M.lift.map₂ (f ◁ η) = M.lift.map f ◁ M.lift.map₂ η := by
  induction η using Quot.ind; rfl

@[simp] theorem lift_map₂_whiskerRight {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    M.lift.map₂ (η ▷ h) = M.lift.map₂ η ▷ M.lift.map h := by
  induction η using Quot.ind; rfl

@[simp] theorem lift_map₂_associator_hom (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    M.lift.map₂ (α_ f g h).hom = (α_ (M.lift.map f) (M.lift.map g) (M.lift.map h)).hom := rfl

@[simp] theorem lift_map₂_associator_inv (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    M.lift.map₂ (α_ f g h).inv = (α_ (M.lift.map f) (M.lift.map g) (M.lift.map h)).inv := rfl

@[simp] theorem lift_map₂_leftUnitor_hom (f : a ⟶ b) :
    M.lift.map₂ (λ_ f).hom = (λ_ (M.lift.map f)).hom := rfl

@[simp] theorem lift_map₂_leftUnitor_inv (f : a ⟶ b) :
    M.lift.map₂ (λ_ f).inv = (λ_ (M.lift.map f)).inv := rfl

@[simp] theorem lift_map₂_rightUnitor_hom (f : a ⟶ b) :
    M.lift.map₂ (ρ_ f).hom = (ρ_ (M.lift.map f)).hom := rfl

@[simp] theorem lift_map₂_rightUnitor_inv (f : a ⟶ b) :
    M.lift.map₂ (ρ_ f).inv = (ρ_ (M.lift.map f)).inv := rfl

theorem lift_map_comp (f : a ⟶ b) (g : b ⟶ c) :
    M.lift.map (f ≫ g) = M.lift.map f ≫ M.lift.map g := rfl

end LiftLemmas

/-! ## Normal forms of whiskered 2-morphisms

A 2-morphism `g : F x ⟶ F y` between images of free 1-morphisms, whiskered on both sides by
images of free 1-morphisms, changes only by images of free 2-morphisms when the whiskering
1-morphisms are replaced by isomorphic ones (`mid_conj`) or regrouped (`mid_assoc`). -/

section Mid

variable {a b c d e a' : FB S}

omit M in
/-- Replacing the whiskering 1-morphisms by isomorphic ones, in an arbitrary bicategory. -/
theorem mid_conj_aux {a b c d : C} {P P' : c ⟶ d} {Q Q' : b ⟶ a} {X Y : d ⟶ b} (σ : P ≅ P')
    (τ : Q ≅ Q') (g : X ⟶ Y) :
    P ◁ (g ▷ Q) = (σ.hom ▷ (X ≫ Q) ≫ P' ◁ X ◁ τ.hom) ≫ P' ◁ (g ▷ Q') ≫
      (P' ◁ Y ◁ τ.inv ≫ σ.inv ▷ (Y ≫ Q)) := by
  have h₁ : X ◁ τ.hom ≫ g ▷ Q' ≫ Y ◁ τ.inv = g ▷ Q := by
    rw [whisker_exchange_assoc, ← whiskerLeft_comp, Iso.hom_inv_id, whiskerLeft_id,
      Category.comp_id]
  have h₂ : P' ◁ X ◁ τ.hom ≫ P' ◁ (g ▷ Q') ≫ P' ◁ Y ◁ τ.inv = P' ◁ (g ▷ Q) := by
    rw [← whiskerLeft_comp, ← whiskerLeft_comp, h₁]
  simp only [Category.assoc]
  rw [reassoc_of% h₂, ← whisker_exchange_assoc, ← comp_whiskerRight, Iso.hom_inv_id,
    id_whiskerRight, Category.comp_id]

omit M in
/-- Regrouping the whiskering 1-morphisms, in an arbitrary bicategory. -/
theorem mid_assoc_aux {a b c d e f : C} {A₁ : a ⟶ b} {A₂ : b ⟶ c} {X Y : c ⟶ d} {B₁ : d ⟶ e}
    {B₂ : e ⟶ f} (g : X ⟶ Y) :
    (A₁ ≫ A₂) ◁ (g ▷ (B₁ ≫ B₂)) =
      ((α_ A₁ A₂ (X ≫ B₁ ≫ B₂)).hom ≫ A₁ ◁ (A₂ ◁ (α_ X B₁ B₂).inv ≫ (α_ A₂ (X ≫ B₁) B₂).inv)) ≫
        A₁ ◁ ((A₂ ◁ (g ▷ B₁)) ▷ B₂) ≫
          (A₁ ◁ ((α_ A₂ (Y ≫ B₁) B₂).hom ≫ A₂ ◁ (α_ Y B₁ B₂).hom) ≫
            (α_ A₁ A₂ (Y ≫ B₁ ≫ B₂)).inv) := by
  simp [comp_whiskerLeft, whiskerRight_comp, whisker_assoc]

/-- Two composites `F A ≫ K ≫ F B` with parallel free `A`, `A'` and `B`, `B'` agree. -/
theorem lift_conj_eq {x x' y y' : a ⟶ b} (A A' : x ⟶ x')
    (K : M.lift.map x' ⟶ M.lift.map y') (B B' : y' ⟶ y) :
    M.lift.map₂ A ≫ K ≫ M.lift.map₂ B = M.lift.map₂ A' ≫ K ≫ M.lift.map₂ B' := by
  rw [lift_map₂_eq M A A', lift_map₂_eq M B B']

/-- **A whiskered 2-morphism** `F p ◁ (g ▷ F q)`, typed as a 2-morphism between images of
composites of free 1-morphisms. -/
def midK (p : a ⟶ b) (q : c ⟶ d) {x y : b ⟶ c} (g : M.lift.map x ⟶ M.lift.map y) :
    M.lift.map (p ≫ (x ≫ q)) ⟶ M.lift.map (p ≫ (y ≫ q)) :=
  M.lift.map p ◁ (g ▷ M.lift.map q)

@[simp] theorem midK_id (p : a ⟶ b) (q : c ⟶ d) (x : b ⟶ c) :
    midK M p q (𝟙 (M.lift.map x)) = 𝟙 _ := by
  simp only [midK, id_whiskerRight]; exact whiskerLeft_id _ _

theorem midK_comp (p : a ⟶ b) (q : c ⟶ d) {x y z : b ⟶ c} (k : M.lift.map x ⟶ M.lift.map y)
    (k' : M.lift.map y ⟶ M.lift.map z) :
    midK M p q (k ≫ k') = midK M p q k ≫ midK M p q k' := by
  simp only [midK, comp_whiskerRight]; exact whiskerLeft_comp _ _ _

/-- Replacing the whiskering 1-morphisms by isomorphic ones. -/
theorem mid_conj {p p' : c ⟶ d} {q q' : b ⟶ a} {x y : d ⟶ b} (σ : p ≅ p') (τ : q ≅ q')
    (g : M.lift.map x ⟶ M.lift.map y) :
    midK M p q g =
      M.lift.map₂ (σ.hom ▷ (x ≫ q) ≫ p' ◁ x ◁ τ.hom) ≫ midK M p' q' g ≫
          M.lift.map₂ (p' ◁ y ◁ τ.inv ≫ σ.inv ▷ (y ≫ q)) := by
  simp only [midK, PrelaxFunctor.map₂_comp, lift_map₂_whiskerLeft, lift_map₂_whiskerRight,
    lift_map_comp]
  exact mid_conj_aux (M.lift.map₂Iso σ) (M.lift.map₂Iso τ) g

/-- Regrouping the whiskering 1-morphisms. -/
theorem mid_assoc {a₁ : a ⟶ b} {a₂ : b ⟶ c} {x y : c ⟶ d} {b₁ : d ⟶ e} {b₂ : e ⟶ a'}
    (g : M.lift.map x ⟶ M.lift.map y) :
    midK M (a₁ ≫ a₂) (b₁ ≫ b₂) g =
      M.lift.map₂ ((α_ a₁ a₂ (x ≫ b₁ ≫ b₂)).hom ≫
          a₁ ◁ (a₂ ◁ (α_ x b₁ b₂).inv ≫ (α_ a₂ (x ≫ b₁) b₂).inv)) ≫
        midK M a₁ b₂ (midK M a₂ b₁ g) ≫
          M.lift.map₂ (a₁ ◁ ((α_ a₂ (y ≫ b₁) b₂).hom ≫ a₂ ◁ (α_ y b₁ b₂).hom) ≫
            (α_ a₁ a₂ (y ≫ b₁ ≫ b₂)).inv) := by
  simp only [midK, PrelaxFunctor.map₂_comp, lift_map₂_whiskerLeft,
    lift_map₂_associator_hom, lift_map₂_associator_inv, lift_map_comp]
  exact mid_assoc_aux g

/-- Pulling images of free 2-morphisms out of a whiskered composite. -/
theorem mid_comp {p : a ⟶ b} {q : c ⟶ d} {x x' y y' : b ⟶ c} (φ : x ⟶ x')
    (k : M.lift.map x' ⟶ M.lift.map y') (ψ : y' ⟶ y) :
    midK M p q (M.lift.map₂ φ ≫ k ≫ M.lift.map₂ ψ) =
      M.lift.map₂ (p ◁ (φ ▷ q)) ≫ midK M p q k ≫ M.lift.map₂ (p ◁ (ψ ▷ q)) := by
  simp only [midK, lift_map₂_whiskerLeft, lift_map₂_whiskerRight, comp_whiskerRight]
  exact (whiskerLeft_comp _ _ _).trans (congrArg _ (whiskerLeft_comp _ _ _))

/-- **The whiskering identity in normal form**: a whiskered generator image conjugated by free
2-morphisms, with whiskering 1-morphisms `rv ≅ v ≫ r` and `ul ≅ l ≫ u`, is the generator image
whiskered by `r`, `l`, conjugated by free 2-morphisms, and then whiskered by `v`, `u` and
conjugated by free 2-morphisms. -/
theorem conj_key {a₀ a₁ a₂ a₃ a₄ a₅ : FB S} {v : a₀ ⟶ a₁} {r : a₁ ⟶ a₂} {rv : a₀ ⟶ a₂}
    {x y : a₂ ⟶ a₃} {l : a₃ ⟶ a₄} {u : a₄ ⟶ a₅} {ul : a₃ ⟶ a₅} {P Q : a₀ ⟶ a₅}
    {P' Q' : a₁ ⟶ a₄} (σ : rv ≅ v ≫ r) (τ : ul ≅ l ≫ u) (g : M.lift.map x ⟶ M.lift.map y)
    (A : P ⟶ rv ≫ (x ≫ ul)) (B : rv ≫ (y ≫ ul) ⟶ Q) (A' : P' ⟶ r ≫ (x ≫ l))
    (B' : r ≫ (y ≫ l) ⟶ Q') (φ : P ⟶ v ≫ (P' ≫ u)) (ψ : v ≫ (Q' ≫ u) ⟶ Q) :
    M.lift.map₂ A ≫ midK M rv ul g ≫ M.lift.map₂ B =
      M.lift.map₂ φ ≫ midK M v u (M.lift.map₂ A' ≫ midK M r l g ≫ M.lift.map₂ B') ≫
        M.lift.map₂ ψ := by
  rw [mid_conj M σ τ, mid_comp M, mid_assoc M]
  simp only [Category.assoc, ← PrelaxFunctor.map₂_comp_assoc, ← PrelaxFunctor.map₂_comp]
  exact lift_conj_eq M _ _ _ _ _

omit M in
/-- The interchange law for two whiskered 2-morphisms, in an arbitrary bicategory. -/
theorem exch_aux {o₀ o₁ o₂ o₃ : C} {P Q : o₀ ⟶ o₁} {Mi : o₁ ⟶ o₂} {X Y : o₂ ⟶ o₃} (η : P ⟶ Q)
    (γ : X ⟶ Y) :
    (P ≫ Mi) ◁ (γ ▷ 𝟙 o₃) ≫ ((P ≫ Mi) ◁ (ρ_ Y).hom ≫ (α_ P Mi Y).hom ≫ (λ_ _).inv) ≫
        𝟙 o₀ ◁ (η ▷ (Mi ≫ Y)) =
      ((P ≫ Mi) ◁ (ρ_ X).hom ≫ (α_ P Mi X).hom ≫ (λ_ _).inv) ≫ 𝟙 o₀ ◁ (η ▷ (Mi ≫ X)) ≫
        ((λ_ _).hom ≫ (α_ Q Mi X).inv ≫ (Q ≫ Mi) ◁ (ρ_ X).inv) ≫ (Q ≫ Mi) ◁ (γ ▷ 𝟙 o₃) ≫
          ((Q ≫ Mi) ◁ (ρ_ Y).hom ≫ (α_ Q Mi Y).hom ≫ (λ_ _).inv) := by
  have h1 : (P ≫ Mi) ◁ (γ ▷ 𝟙 o₃) ≫ (P ≫ Mi) ◁ (ρ_ Y).hom =
      (P ≫ Mi) ◁ (ρ_ X).hom ≫ (P ≫ Mi) ◁ γ := by
    rw [← whiskerLeft_comp, ← whiskerLeft_comp, rightUnitor_naturality]
  have h1' : (Q ≫ Mi) ◁ (γ ▷ 𝟙 o₃) ≫ (Q ≫ Mi) ◁ (ρ_ Y).hom =
      (Q ≫ Mi) ◁ (ρ_ X).hom ≫ (Q ≫ Mi) ◁ γ := by
    rw [← whiskerLeft_comp, ← whiskerLeft_comp, rightUnitor_naturality]
  simp only [Category.assoc]
  rw [reassoc_of% h1, reassoc_of% h1', associator_naturality_right_assoc,
    associator_naturality_right_assoc, ← leftUnitor_inv_naturality_assoc,
    ← leftUnitor_inv_naturality, whisker_exchange_assoc]
  simp

/-- The interchange law for images of generators. -/
theorem exch_lift {a₀ a₁ a₂ a₃ : FB S} {hd hc : a₀ ⟶ a₁} {m : a₁ ⟶ a₂} {gd gc : a₂ ⟶ a₃}
    (η : M.lift.map hd ⟶ M.lift.map hc) (γ : M.lift.map gd ⟶ M.lift.map gc) :
    midK M (hd ≫ m) (𝟙 a₃) γ ≫
        M.lift.map₂ ((hd ≫ m) ◁ (ρ_ gc).hom ≫ (α_ hd m gc).hom ≫ (λ_ _).inv) ≫
          midK M (𝟙 a₀) (m ≫ gc) η =
      M.lift.map₂ ((hd ≫ m) ◁ (ρ_ gd).hom ≫ (α_ hd m gd).hom ≫ (λ_ _).inv) ≫
        midK M (𝟙 a₀) (m ≫ gd) η ≫
          M.lift.map₂ ((λ_ _).hom ≫ (α_ hc m gd).inv ≫ (hc ≫ m) ◁ (ρ_ gd).inv) ≫
            midK M (hc ≫ m) (𝟙 a₃) γ ≫
              M.lift.map₂ ((hc ≫ m) ◁ (ρ_ gc).hom ≫ (α_ hc m gc).hom ≫ (λ_ _).inv) := by
  simp only [midK, PrelaxFunctor.map₂_comp, lift_map₂_whiskerLeft, lift_map₂_associator_hom,
    lift_map₂_associator_inv, lift_map₂_leftUnitor_inv, lift_map₂_leftUnitor_hom,
    lift_map₂_rightUnitor_hom, lift_map₂_rightUnitor_inv, lift_map_comp]
  exact exch_aux η γ

/-- Two composites `F A ≫ K ≫ F B ≫ K' ≫ F C` with parallel free `A`, `B`, `C` agree. -/
theorem lift_conj_eq₂ {x x' y y' z w : a ⟶ b} (A A' : x ⟶ x')
    (K : M.lift.map x' ⟶ M.lift.map y) (B B' : y ⟶ y') (K' : M.lift.map y' ⟶ M.lift.map z)
    (D D' : z ⟶ w) :
    M.lift.map₂ A ≫ K ≫ M.lift.map₂ B ≫ K' ≫ M.lift.map₂ D =
      M.lift.map₂ A' ≫ K ≫ M.lift.map₂ B' ≫ K' ≫ M.lift.map₂ D' := by
  rw [lift_map₂_eq M A A', lift_map₂_eq M B B', lift_map₂_eq M D D']

/-- **The interchange law in normal form**: two generator images at disjoint positions, each
whiskered and conjugated by images of free 2-morphisms, can be applied in either order. -/
theorem exch_key {a₀ a₁ a₂ a₃ : FB S} {hd hc : a₀ ⟶ a₁} {m : a₁ ⟶ a₂} {gd gc : a₂ ⟶ a₃}
    (η : M.lift.map hd ⟶ M.lift.map hc) (γ : M.lift.map gd ⟶ M.lift.map gc)
    {r₁ r₄ : a₀ ⟶ a₂} {l₁ l₄ : a₃ ⟶ a₃} {r₂ r₃ : a₀ ⟶ a₀} {l₂ l₃ : a₁ ⟶ a₃}
    (σ₁ : r₁ ≅ hd ≫ m) (τ₁ : l₁ ≅ 𝟙 a₃) (σ₂ : r₂ ≅ 𝟙 a₀) (τ₂ : l₂ ≅ m ≫ gc)
    (σ₃ : r₃ ≅ 𝟙 a₀) (τ₃ : l₃ ≅ m ≫ gd) (σ₄ : r₄ ≅ hc ≫ m) (τ₄ : l₄ ≅ 𝟙 a₃)
    {P Q P₁ Q₁ P₂ Q₂ P₃ Q₃ P₄ Q₄ : a₀ ⟶ a₃}
    (E₀ : P ⟶ P₁) (A₁ : P₁ ⟶ r₁ ≫ (gd ≫ l₁)) (B₁ : r₁ ≫ (gc ≫ l₁) ⟶ Q₁) (E₁ : Q₁ ⟶ P₂)
    (A₂ : P₂ ⟶ r₂ ≫ (hd ≫ l₂)) (B₂ : r₂ ≫ (hc ≫ l₂) ⟶ Q₂) (E₂ : Q₂ ⟶ Q)
    (E₃ : P ⟶ P₃) (A₃ : P₃ ⟶ r₃ ≫ (hd ≫ l₃)) (B₃ : r₃ ≫ (hc ≫ l₃) ⟶ Q₃) (E₄ : Q₃ ⟶ P₄)
    (A₄ : P₄ ⟶ r₄ ≫ (gd ≫ l₄)) (B₄ : r₄ ≫ (gc ≫ l₄) ⟶ Q₄) (E₅ : Q₄ ⟶ Q) :
    M.lift.map₂ E₀ ≫ (M.lift.map₂ A₁ ≫ midK M r₁ l₁ γ ≫ M.lift.map₂ B₁) ≫ M.lift.map₂ E₁ ≫
        (M.lift.map₂ A₂ ≫ midK M r₂ l₂ η ≫ M.lift.map₂ B₂) ≫ M.lift.map₂ E₂ =
      M.lift.map₂ E₃ ≫ (M.lift.map₂ A₃ ≫ midK M r₃ l₃ η ≫ M.lift.map₂ B₃) ≫ M.lift.map₂ E₄ ≫
        (M.lift.map₂ A₄ ≫ midK M r₄ l₄ γ ≫ M.lift.map₂ B₄) ≫ M.lift.map₂ E₅ := by
  rw [mid_conj M σ₁ τ₁, mid_conj M σ₂ τ₂, mid_conj M σ₃ τ₃, mid_conj M σ₄ τ₄]
  simp only [Category.assoc, ← PrelaxFunctor.map₂_comp_assoc, ← PrelaxFunctor.map₂_comp]
  rw [lift_map₂_eq M _ ((hd ≫ m) ◁ (ρ_ gc).hom ≫ (α_ hd m gc).hom ≫ (λ_ _).inv),
    reassoc_of% (exch_lift M η γ)]
  simp only [← PrelaxFunctor.map₂_comp_assoc, ← PrelaxFunctor.map₂_comp]
  exact lift_conj_eq₂ M _ _ _ _ _ _ _ _

/-- Two composites `F A ≫ K ≫ F B ≫ K' ≫ F C` with parallel free `A`, `B`, `C` agree, and a
composite of images of free 2-morphisms is the image of a free 2-morphism. -/
theorem lift_comp_eq {x y z : a ⟶ b} (A : x ⟶ y) (B : y ⟶ z) (D : x ⟶ z) :
    M.lift.map₂ A ≫ M.lift.map₂ B = M.lift.map₂ D := by
  rw [← PrelaxFunctor.map₂_comp, lift_map₂_eq M (A ≫ B) D]

omit M in
/-- The right zigzag of an adjunction, whiskered by units, in an arbitrary bicategory. -/
theorem zig_aux {a b : C} {E : a ⟶ b} {R : b ⟶ a} (η : 𝟙 b ⟶ R ≫ E) (ε : E ≫ R ⟶ 𝟙 a)
    (htri : E ◁ η ≫ (α_ E R E).inv ≫ ε ▷ E = (ρ_ E).hom ≫ (λ_ E).inv) :
    E ◁ (η ▷ 𝟙 b) ≫ (E ◁ (ρ_ (R ≫ E)).hom ≫ (α_ E R E).inv ≫ (λ_ _).inv) ≫
        𝟙 a ◁ (ε ▷ E) =
      E ◁ (λ_ (𝟙 b)).hom ≫ (ρ_ E).hom ≫ (λ_ E).inv ≫ (λ_ (𝟙 a ≫ E)).inv := by
  have h : E ◁ (η ▷ 𝟙 b) ≫ (E ◁ (ρ_ (R ≫ E)).hom ≫ (α_ E R E).inv ≫ (λ_ _).inv) ≫
      𝟙 a ◁ (ε ▷ E) =
      (E ◁ (λ_ (𝟙 b)).hom ≫ (ρ_ E).hom ≫ (ρ_ E).inv) ≫ (E ◁ η ≫ (α_ E R E).inv ≫ ε ▷ E) ≫
        (λ_ (𝟙 a ≫ E)).inv := by
    bicategory
  rw [h, htri]
  bicategory

/-- **The zigzag relation in normal form**: an upward strand `e` with a cup `η` on its left and a
cap `ε` on its right, conjugated by images of free 2-morphisms, is the image of a free
2-morphism, as soon as `η`, `ε` (read through free isomorphisms) satisfy the triangle identity. -/
theorem zig_key {a b : FB S} {e : a ⟶ b} {ρ : b ⟶ a} {p₁ : a ⟶ b} {q₁ d₁ c₁ : b ⟶ b}
    {p₂ d₂ c₂ : a ⟶ a} {q₂ : a ⟶ b} (σp₁ : p₁ ≅ e) (σq₁ : q₁ ≅ 𝟙 b) (σd₁ : d₁ ≅ 𝟙 b)
    (σc₁ : c₁ ≅ ρ ≫ e) (σp₂ : p₂ ≅ 𝟙 a) (σq₂ : q₂ ≅ e) (σd₂ : d₂ ≅ e ≫ ρ) (σc₂ : c₂ ≅ 𝟙 a)
    (g₁ : M.lift.map d₁ ⟶ M.lift.map c₁) (g₂ : M.lift.map d₂ ⟶ M.lift.map c₂)
    (htri : M.lift.map e ◁
        (M.lift.map₂ σd₁.inv ≫ g₁ ≫ M.lift.map₂ σc₁.hom : 𝟙 _ ⟶ M.lift.map ρ ≫ M.lift.map e) ≫
      (α_ _ _ _).inv ≫
        (M.lift.map₂ σd₂.inv ≫ g₂ ≫ M.lift.map₂ σc₂.hom : M.lift.map e ≫ M.lift.map ρ ⟶ 𝟙 _) ▷
          M.lift.map e = (ρ_ _).hom ≫ (λ_ _).inv)
    {P P₁ Q₁ P₂ Q₂ Q : a ⟶ b}
    (E₀ : P ⟶ P₁) (A₁ : P₁ ⟶ p₁ ≫ (d₁ ≫ q₁)) (B₁ : p₁ ≫ (c₁ ≫ q₁) ⟶ Q₁) (E₁ : Q₁ ⟶ P₂)
    (A₂ : P₂ ⟶ p₂ ≫ (d₂ ≫ q₂)) (B₂ : p₂ ≫ (c₂ ≫ q₂) ⟶ Q₂) (E₂ : Q₂ ⟶ Q) (Z : P ⟶ Q) :
    M.lift.map₂ E₀ ≫ (M.lift.map₂ A₁ ≫ midK M p₁ q₁ g₁ ≫ M.lift.map₂ B₁) ≫ M.lift.map₂ E₁ ≫
        (M.lift.map₂ A₂ ≫ midK M p₂ q₂ g₂ ≫ M.lift.map₂ B₂) ≫ M.lift.map₂ E₂ =
      M.lift.map₂ Z := by
  obtain ⟨η, hη⟩ : ∃ η : M.lift.map (𝟙 b) ⟶ M.lift.map (ρ ≫ e),
      η = M.lift.map₂ σd₁.inv ≫ g₁ ≫ M.lift.map₂ σc₁.hom := ⟨_, rfl⟩
  obtain ⟨ε, hε⟩ : ∃ ε : M.lift.map (e ≫ ρ) ⟶ M.lift.map (𝟙 a),
      ε = M.lift.map₂ σd₂.inv ≫ g₂ ≫ M.lift.map₂ σc₂.hom := ⟨_, rfl⟩
  have htri' : M.lift.map e ◁ (η : 𝟙 _ ⟶ M.lift.map ρ ≫ M.lift.map e) ≫ (α_ _ _ _).inv ≫
      (ε : M.lift.map e ≫ M.lift.map ρ ⟶ 𝟙 _) ▷ M.lift.map e = (ρ_ _).hom ≫ (λ_ _).inv := by
    subst hη hε; exact htri
  have hg₁ : g₁ = M.lift.map₂ σd₁.hom ≫ η ≫ M.lift.map₂ σc₁.inv := by
    rw [hη]
    simp only [Category.assoc, ← PrelaxFunctor.map₂_comp, Iso.hom_inv_id, PrelaxFunctor.map₂_id,
      Category.comp_id]
    rw [← PrelaxFunctor.map₂_comp_assoc, Iso.hom_inv_id, PrelaxFunctor.map₂_id, Category.id_comp]
  have hg₂ : g₂ = M.lift.map₂ σd₂.hom ≫ ε ≫ M.lift.map₂ σc₂.inv := by
    rw [hε]
    simp only [Category.assoc, ← PrelaxFunctor.map₂_comp, Iso.hom_inv_id, PrelaxFunctor.map₂_id,
      Category.comp_id]
    rw [← PrelaxFunctor.map₂_comp_assoc, Iso.hom_inv_id, PrelaxFunctor.map₂_id, Category.id_comp]
  have hmid : midK M e (𝟙 b) η ≫
      M.lift.map₂ (e ◁ (ρ_ (ρ ≫ e)).hom ≫ (α_ e ρ e).inv ≫ (λ_ _).inv) ≫ midK M (𝟙 a) e ε =
      M.lift.map₂ (e ◁ (λ_ (𝟙 b)).hom ≫ (ρ_ e).hom ≫ (λ_ e).inv ≫ (λ_ (𝟙 a ≫ e)).inv) := by
    simp only [midK, PrelaxFunctor.map₂_comp, lift_map₂_whiskerLeft, lift_map₂_associator_inv,
      lift_map₂_leftUnitor_hom, lift_map₂_leftUnitor_inv, lift_map₂_rightUnitor_hom, lift_map_comp]
    exact zig_aux η ε htri'
  rw [hg₁, hg₂, mid_comp M, mid_comp M, mid_conj M σp₁ σq₁, mid_conj M σp₂ σq₂]
  simp only [Category.assoc, ← PrelaxFunctor.map₂_comp_assoc, ← PrelaxFunctor.map₂_comp]
  rw [lift_map₂_eq M _ (e ◁ (ρ_ (ρ ≫ e)).hom ≫ (α_ e ρ e).inv ≫ (λ_ _).inv), reassoc_of% hmid]
  simp only [← PrelaxFunctor.map₂_comp]
  exact lift_map₂_eq M _ _

/-- `zig_key` for generator images given by the unit and counit of an adjunction. -/
theorem zig_key' {a b : FB S} {e : a ⟶ b} {ρ : b ⟶ a} {p₁ : a ⟶ b} {q₁ d₁ c₁ : b ⟶ b}
    {p₂ d₂ c₂ : a ⟶ a} {q₂ : a ⟶ b} (σp₁ : p₁ ≅ e) (σq₁ : q₁ ≅ 𝟙 b) (σd₁ : d₁ ≅ 𝟙 b)
    (σc₁ : c₁ ≅ ρ ≫ e) (σp₂ : p₂ ≅ 𝟙 a) (σq₂ : q₂ ≅ e) (σd₂ : d₂ ≅ e ≫ ρ) (σc₂ : c₂ ≅ 𝟙 a)
    (adj : M.lift.map ρ ⊣ M.lift.map e)
    (g₁ : M.lift.map d₁ ⟶ M.lift.map c₁) (g₂ : M.lift.map d₂ ⟶ M.lift.map c₂)
    (hg₁ : M.lift.map₂ σd₁.inv ≫ g₁ ≫ M.lift.map₂ σc₁.hom = adj.unit)
    (hg₂ : M.lift.map₂ σd₂.inv ≫ g₂ ≫ M.lift.map₂ σc₂.hom = adj.counit)
    {P P₁ Q₁ P₂ Q₂ Q : a ⟶ b}
    (E₀ : P ⟶ P₁) (A₁ : P₁ ⟶ p₁ ≫ (d₁ ≫ q₁)) (B₁ : p₁ ≫ (c₁ ≫ q₁) ⟶ Q₁) (E₁ : Q₁ ⟶ P₂)
    (A₂ : P₂ ⟶ p₂ ≫ (d₂ ≫ q₂)) (B₂ : p₂ ≫ (c₂ ≫ q₂) ⟶ Q₂) (E₂ : Q₂ ⟶ Q) (Z : P ⟶ Q) :
    M.lift.map₂ E₀ ≫ (M.lift.map₂ A₁ ≫ midK M p₁ q₁ g₁ ≫ M.lift.map₂ B₁) ≫ M.lift.map₂ E₁ ≫
        (M.lift.map₂ A₂ ≫ midK M p₂ q₂ g₂ ≫ M.lift.map₂ B₂) ≫ M.lift.map₂ E₂ =
      M.lift.map₂ Z := by
  refine zig_key M σp₁ σq₁ σd₁ σc₁ σp₂ σq₂ σd₂ σc₂ g₁ g₂ ?_ E₀ A₁ B₁ E₁ A₂ B₂ E₂ Z
  have h := adj.right_triangle
  simp only [rightZigzag, bicategoricalComp] at h
  have e₁ : (M.lift.map₂ σd₁.inv ≫ g₁ ≫ M.lift.map₂ σc₁.hom :
      𝟙 _ ⟶ M.lift.map ρ ≫ M.lift.map e) = adj.unit := hg₁
  have e₂ : (M.lift.map₂ σd₂.inv ≫ g₂ ≫ M.lift.map₂ σc₂.hom :
      M.lift.map e ≫ M.lift.map ρ ⟶ 𝟙 _) = adj.counit := hg₂
  rw [e₁, e₂, ← h]
  bicategory

omit M in
/-- The left zigzag of an adjunction, whiskered by units, in an arbitrary bicategory. -/
theorem zag_aux {a b : C} {E : a ⟶ b} {R : b ⟶ a} (η : 𝟙 b ⟶ R ≫ E) (ε : E ≫ R ⟶ 𝟙 a)
    (htri : η ▷ R ≫ (α_ R E R).hom ≫ R ◁ ε = (λ_ R).hom ≫ (ρ_ R).inv) :
    𝟙 b ◁ (η ▷ R) ≫ ((λ_ _).hom ≫ (α_ R E R).hom ≫ R ◁ (ρ_ (E ≫ R)).inv) ≫
        R ◁ (ε ▷ 𝟙 a) =
      (λ_ _).hom ≫ (λ_ R).hom ≫ (ρ_ R).inv ≫ R ◁ (λ_ (𝟙 a)).inv := by
  have h : 𝟙 b ◁ (η ▷ R) ≫ ((λ_ _).hom ≫ (α_ R E R).hom ≫ R ◁ (ρ_ (E ≫ R)).inv) ≫
      R ◁ (ε ▷ 𝟙 a) =
      (λ_ _).hom ≫ (η ▷ R ≫ (α_ R E R).hom ≫ R ◁ ε) ≫ R ◁ (λ_ (𝟙 a)).inv := by
    bicategory
  rw [h, htri]
  bicategory

/-- **The other zigzag relation in normal form**: the dual strand `ρ` with a cup on its right and
a cap on its left, for generator images given by the unit and counit of an adjunction
`F ρ ⊣ F e`. -/
theorem zag_key' {a b : FB S} {e : a ⟶ b} {ρ : b ⟶ a} {p₁ d₁ c₁ : b ⟶ b} {q₁ : b ⟶ a}
    {p₂ : b ⟶ a} {q₂ d₂ c₂ : a ⟶ a} (σp₁ : p₁ ≅ 𝟙 b) (σq₁ : q₁ ≅ ρ) (σd₁ : d₁ ≅ 𝟙 b)
    (σc₁ : c₁ ≅ ρ ≫ e) (σp₂ : p₂ ≅ ρ) (σq₂ : q₂ ≅ 𝟙 a) (σd₂ : d₂ ≅ e ≫ ρ) (σc₂ : c₂ ≅ 𝟙 a)
    (adj : M.lift.map ρ ⊣ M.lift.map e)
    (g₁ : M.lift.map d₁ ⟶ M.lift.map c₁) (g₂ : M.lift.map d₂ ⟶ M.lift.map c₂)
    (hg₁ : M.lift.map₂ σd₁.inv ≫ g₁ ≫ M.lift.map₂ σc₁.hom = adj.unit)
    (hg₂ : M.lift.map₂ σd₂.inv ≫ g₂ ≫ M.lift.map₂ σc₂.hom = adj.counit)
    {P P₁ Q₁ P₂ Q₂ Q : b ⟶ a}
    (E₀ : P ⟶ P₁) (A₁ : P₁ ⟶ p₁ ≫ (d₁ ≫ q₁)) (B₁ : p₁ ≫ (c₁ ≫ q₁) ⟶ Q₁) (E₁ : Q₁ ⟶ P₂)
    (A₂ : P₂ ⟶ p₂ ≫ (d₂ ≫ q₂)) (B₂ : p₂ ≫ (c₂ ≫ q₂) ⟶ Q₂) (E₂ : Q₂ ⟶ Q) (Z : P ⟶ Q) :
    M.lift.map₂ E₀ ≫ (M.lift.map₂ A₁ ≫ midK M p₁ q₁ g₁ ≫ M.lift.map₂ B₁) ≫ M.lift.map₂ E₁ ≫
        (M.lift.map₂ A₂ ≫ midK M p₂ q₂ g₂ ≫ M.lift.map₂ B₂) ≫ M.lift.map₂ E₂ =
      M.lift.map₂ Z := by
  obtain ⟨η, hη⟩ : ∃ η : M.lift.map (𝟙 b) ⟶ M.lift.map (ρ ≫ e),
      η = M.lift.map₂ σd₁.inv ≫ g₁ ≫ M.lift.map₂ σc₁.hom := ⟨_, rfl⟩
  obtain ⟨ε, hε⟩ : ∃ ε : M.lift.map (e ≫ ρ) ⟶ M.lift.map (𝟙 a),
      ε = M.lift.map₂ σd₂.inv ≫ g₂ ≫ M.lift.map₂ σc₂.hom := ⟨_, rfl⟩
  have htri : (η : 𝟙 _ ⟶ M.lift.map ρ ≫ M.lift.map e) ▷ M.lift.map ρ ≫ (α_ _ _ _).hom ≫
      M.lift.map ρ ◁ (ε : M.lift.map e ≫ M.lift.map ρ ⟶ 𝟙 _) = (λ_ _).hom ≫ (ρ_ _).inv := by
    have h := adj.left_triangle
    simp only [leftZigzag, bicategoricalComp] at h
    have e₁ : (η : 𝟙 _ ⟶ M.lift.map ρ ≫ M.lift.map e) = adj.unit := hη.trans hg₁
    have e₂ : (ε : M.lift.map e ≫ M.lift.map ρ ⟶ 𝟙 _) = adj.counit := hε.trans hg₂
    rw [e₁, e₂, ← h]
    bicategory
  have hg₁' : g₁ = M.lift.map₂ σd₁.hom ≫ η ≫ M.lift.map₂ σc₁.inv := by
    rw [hη]
    simp only [Category.assoc, ← PrelaxFunctor.map₂_comp, Iso.hom_inv_id, PrelaxFunctor.map₂_id,
      Category.comp_id]
    rw [← PrelaxFunctor.map₂_comp_assoc, Iso.hom_inv_id, PrelaxFunctor.map₂_id, Category.id_comp]
  have hg₂' : g₂ = M.lift.map₂ σd₂.hom ≫ ε ≫ M.lift.map₂ σc₂.inv := by
    rw [hε]
    simp only [Category.assoc, ← PrelaxFunctor.map₂_comp, Iso.hom_inv_id, PrelaxFunctor.map₂_id,
      Category.comp_id]
    rw [← PrelaxFunctor.map₂_comp_assoc, Iso.hom_inv_id, PrelaxFunctor.map₂_id, Category.id_comp]
  have hmid : midK M (𝟙 b) ρ η ≫
      M.lift.map₂ ((λ_ _).hom ≫ (α_ ρ e ρ).hom ≫ ρ ◁ (ρ_ (e ≫ ρ)).inv) ≫ midK M ρ (𝟙 a) ε =
      M.lift.map₂ ((λ_ _).hom ≫ (λ_ ρ).hom ≫ (ρ_ ρ).inv ≫ ρ ◁ (λ_ (𝟙 a)).inv) := by
    simp only [midK, PrelaxFunctor.map₂_comp, lift_map₂_whiskerLeft, lift_map₂_associator_hom,
      lift_map₂_leftUnitor_hom, lift_map₂_leftUnitor_inv, lift_map₂_rightUnitor_inv,
      lift_map_comp]
    exact zag_aux η ε htri
  rw [hg₁', hg₂', mid_comp M, mid_comp M, mid_conj M σp₁ σq₁, mid_conj M σp₂ σq₂]
  simp only [Category.assoc, ← PrelaxFunctor.map₂_comp_assoc, ← PrelaxFunctor.map₂_comp]
  rw [lift_map₂_eq M _ ((λ_ _).hom ≫ (α_ ρ e ρ).hom ≫ ρ ◁ (ρ_ (e ≫ ρ)).inv), reassoc_of% hmid]
  simp only [← PrelaxFunctor.map₂_comp]
  exact lift_map₂_eq M _ _

/-- **Canonical form of a whiskered generator image**: replacing the whiskering 1-morphisms and the
boundary of the generator image by isomorphic ones. -/
theorem midK_canon {a₀ a₁ a₂ a₃ : FB S} {p P : a₀ ⟶ a₁} {q Q : a₂ ⟶ a₃} {d c D Cc : a₁ ⟶ a₂}
    (σp : p ≅ P) (σq : q ≅ Q) (σd : d ≅ D) (σc : c ≅ Cc) (g : M.lift.map d ⟶ M.lift.map c) :
    midK M p q g =
      M.lift.map₂ (σp.hom ▷ (d ≫ q) ≫ P ◁ d ◁ σq.hom ≫ P ◁ (σd.hom ▷ Q)) ≫
        midK M P Q (M.lift.map₂ σd.inv ≫ g ≫ M.lift.map₂ σc.hom) ≫
          M.lift.map₂ (P ◁ (σc.inv ▷ Q) ≫ P ◁ c ◁ σq.inv ≫ σp.inv ▷ (c ≫ q)) := by
  rw [mid_comp M, mid_conj M σp σq]
  simp only [Category.assoc, ← PrelaxFunctor.map₂_comp_assoc, ← PrelaxFunctor.map₂_comp]
  have e₁ : M.lift.map₂ (σp.hom ▷ (d ≫ q) ≫ P ◁ d ◁ σq.hom ≫ P ◁ (σd.hom ▷ Q) ≫
      P ◁ (σd.inv ▷ Q)) = M.lift.map₂ (σp.hom ▷ (d ≫ q) ≫ P ◁ d ◁ σq.hom) :=
    lift_map₂_eq M _ _
  have e₂ : M.lift.map₂ (P ◁ (σc.hom ▷ Q) ≫ P ◁ (σc.inv ▷ Q) ≫ P ◁ c ◁ σq.inv ≫
      σp.inv ▷ (c ≫ q)) = M.lift.map₂ (P ◁ c ◁ σq.inv ≫ σp.inv ▷ (c ≫ q)) :=
    lift_map₂_eq M _ _
  rw [e₁, e₂]

omit M in
/-- The left mate of an endomorphism of `E` under `R ⊣ E`, read as the composite "cup on the
right, `x`, cap on the left" of three whiskered layers, in an arbitrary bicategory. -/
theorem rot_aux {a b : C} {R : a ⟶ b} {E : b ⟶ a} (adj : R ⊣ E) (x : E ⟶ E) :
    𝟙 a ◁ (adj.unit ▷ R) ≫ ((λ_ _).hom ≫ (α_ R E R).hom) ≫ R ◁ (x ▷ R) ≫ R ◁ (ρ_ (E ≫ R)).inv ≫
        R ◁ (adj.counit ▷ 𝟙 b) =
      𝟙 a ◁ ((λ_ R).hom ≫ (ρ_ R).inv) ≫
        𝟙 a ◁ ((Bicategory.conjugateEquiv adj adj).symm x ▷ 𝟙 b) ≫
          ((λ_ _).hom ≫ R ◁ (λ_ (𝟙 b)).inv) := by
  rw [Bicategory.conjugateEquiv_symm_apply']
  bicategory

/-- **The rotation of a generator in normal form**: a strand `r` with a cup (the unit of
`F r ⊣ F e`) on its right, a generator image `x` on the new strand `e`, and the cap (the counit) on
its left, all conjugated by images of free 2-morphisms, equals the left mate of `x` on `r`. -/
theorem rot_key {a b : FB S} {r : a ⟶ b} {e : b ⟶ a} (adj : M.lift.map r ⊣ M.lift.map e)
    (x : M.lift.map e ⟶ M.lift.map e)
    {p₁ d₁ : a ⟶ a} {q₁ : a ⟶ b} {c₁ : a ⟶ a} (σp₁ : p₁ ≅ 𝟙 a) (σq₁ : q₁ ≅ r) (σd₁ : d₁ ≅ 𝟙 a)
    (σc₁ : c₁ ≅ r ≫ e) (g₁ : M.lift.map d₁ ⟶ M.lift.map c₁)
    (hg₁ : M.lift.map₂ σd₁.inv ≫ g₁ ≫ M.lift.map₂ σc₁.hom = adj.unit)
    {p₂ q₂ : a ⟶ b} {d₂ c₂ : b ⟶ a} (σp₂ : p₂ ≅ r) (σq₂ : q₂ ≅ r) (σd₂ : d₂ ≅ e) (σc₂ : c₂ ≅ e)
    (g₂ : M.lift.map d₂ ⟶ M.lift.map c₂)
    (hg₂ : M.lift.map₂ σd₂.inv ≫ g₂ ≫ M.lift.map₂ σc₂.hom = x)
    {p₃ : a ⟶ b} {q₃ d₃ c₃ : b ⟶ b} (σp₃ : p₃ ≅ r) (σq₃ : q₃ ≅ 𝟙 b) (σd₃ : d₃ ≅ e ≫ r)
    (σc₃ : c₃ ≅ 𝟙 b) (g₃ : M.lift.map d₃ ⟶ M.lift.map c₃)
    (hg₃ : M.lift.map₂ σd₃.inv ≫ g₃ ≫ M.lift.map₂ σc₃.hom = adj.counit)
    {p₄ : a ⟶ a} {q₄ : b ⟶ b} {d₄ c₄ : a ⟶ b} (σp₄ : p₄ ≅ 𝟙 a) (σq₄ : q₄ ≅ 𝟙 b) (σd₄ : d₄ ≅ r)
    (σc₄ : c₄ ≅ r) (g₄ : M.lift.map d₄ ⟶ M.lift.map c₄)
    (hg₄ : M.lift.map₂ σd₄.inv ≫ g₄ ≫ M.lift.map₂ σc₄.hom =
      (Bicategory.conjugateEquiv adj adj).symm x)
    {P P₁ Q₁ P₂ Q₂ P₃ Q₃ Q P₄ Q₄ : a ⟶ b}
    (E₀ : P ⟶ P₁) (A₁ : P₁ ⟶ p₁ ≫ (d₁ ≫ q₁)) (B₁ : p₁ ≫ (c₁ ≫ q₁) ⟶ Q₁) (E₁ : Q₁ ⟶ P₂)
    (A₂ : P₂ ⟶ p₂ ≫ (d₂ ≫ q₂)) (B₂ : p₂ ≫ (c₂ ≫ q₂) ⟶ Q₂) (E₂ : Q₂ ⟶ P₃)
    (A₃ : P₃ ⟶ p₃ ≫ (d₃ ≫ q₃)) (B₃ : p₃ ≫ (c₃ ≫ q₃) ⟶ Q₃) (E₃ : Q₃ ⟶ Q)
    (F₀ : P ⟶ P₄) (A₄ : P₄ ⟶ p₄ ≫ (d₄ ≫ q₄)) (B₄ : p₄ ≫ (c₄ ≫ q₄) ⟶ Q₄) (F₁ : Q₄ ⟶ Q) :
    M.lift.map₂ E₀ ≫ (M.lift.map₂ A₁ ≫ midK M p₁ q₁ g₁ ≫ M.lift.map₂ B₁) ≫ M.lift.map₂ E₁ ≫
        (M.lift.map₂ A₂ ≫ midK M p₂ q₂ g₂ ≫ M.lift.map₂ B₂) ≫ M.lift.map₂ E₂ ≫
          (M.lift.map₂ A₃ ≫ midK M p₃ q₃ g₃ ≫ M.lift.map₂ B₃) ≫ M.lift.map₂ E₃ =
      M.lift.map₂ F₀ ≫ (M.lift.map₂ A₄ ≫ midK M p₄ q₄ g₄ ≫ M.lift.map₂ B₄) ≫
        M.lift.map₂ F₁ := by
  rw [midK_canon M σp₁ σq₁ σd₁ σc₁ g₁, hg₁, midK_canon M σp₂ σq₂ σd₂ σc₂ g₂, hg₂,
    midK_canon M σp₃ σq₃ σd₃ σc₃ g₃, hg₃, midK_canon M σp₄ σq₄ σd₄ σc₄ g₄, hg₄]
  simp only [Category.assoc, ← PrelaxFunctor.map₂_comp_assoc, ← PrelaxFunctor.map₂_comp]
  have hmid : midK M (𝟙 a) r (x := 𝟙 a) (y := r ≫ e) adj.unit ≫
      M.lift.map₂ ((λ_ _).hom ≫ (α_ r e r).hom) ≫
      midK M r r x ≫ M.lift.map₂ (r ◁ (ρ_ (e ≫ r)).inv) ≫
        midK M r (𝟙 b) (x := e ≫ r) (y := 𝟙 b) adj.counit =
      M.lift.map₂ (𝟙 a ◁ ((λ_ r).hom ≫ (ρ_ r).inv)) ≫
        midK M (𝟙 a) (𝟙 b) ((Bicategory.conjugateEquiv adj adj).symm x) ≫
          M.lift.map₂ ((λ_ _).hom ≫ r ◁ (λ_ (𝟙 b)).inv) := by
    simp only [midK, PrelaxFunctor.map₂_comp, lift_map₂_whiskerLeft, lift_map₂_associator_hom,
      lift_map₂_leftUnitor_hom, lift_map₂_leftUnitor_inv, lift_map₂_rightUnitor_inv, lift_map_comp]
    exact rot_aux adj x
  rw [lift_map₂_eq M _ ((λ_ _).hom ≫ (α_ r e r).hom),
    lift_map₂_eq M _ (r ◁ (ρ_ (e ≫ r)).inv), reassoc_of% hmid]
  simp only [Category.assoc, ← PrelaxFunctor.map₂_comp_assoc, ← PrelaxFunctor.map₂_comp]
  exact lift_conj_eq M _ _ _ _ _

omit M in
/-- The right mate of an endomorphism of `E` under `E ⊣ R`, read as the composite "cup on the
left, `x`, cap on the right" of three whiskered layers, in an arbitrary bicategory. -/
theorem rotL_aux {a b : C} {E : b ⟶ a} {R : a ⟶ b} (adj : E ⊣ R) (x : E ⟶ E) :
    R ◁ (adj.unit ▷ 𝟙 b) ≫ R ◁ (ρ_ (E ≫ R)).hom ≫ R ◁ (x ▷ R) ≫
        ((α_ R E R).inv ≫ (λ_ _).inv) ≫ 𝟙 a ◁ (adj.counit ▷ R) =
      (R ◁ (λ_ (𝟙 b)).hom ≫ (λ_ (R ≫ 𝟙 b)).inv) ≫
        𝟙 a ◁ ((Bicategory.conjugateEquiv adj adj) x ▷ 𝟙 b) ≫
          𝟙 a ◁ ((ρ_ R).hom ≫ (λ_ R).inv) := by
  rw [Bicategory.conjugateEquiv_apply']
  bicategory

/-- **The rotation of a generator in normal form, on the other side**: a strand `r` with a cup
(the unit of `F e ⊣ F r`) on its left, a generator image `x` on the new strand `e`, and the cap
(the counit) on its right, all conjugated by images of free 2-morphisms, equals the right mate of
`x` on `r`. -/
theorem rotL_key {a b : FB S} {r : a ⟶ b} {e : b ⟶ a} (adj : M.lift.map e ⊣ M.lift.map r)
    (x : M.lift.map e ⟶ M.lift.map e)
    {p₁ : a ⟶ b} {q₁ d₁ c₁ : b ⟶ b} (σp₁ : p₁ ≅ r) (σq₁ : q₁ ≅ 𝟙 b) (σd₁ : d₁ ≅ 𝟙 b)
    (σc₁ : c₁ ≅ e ≫ r) (g₁ : M.lift.map d₁ ⟶ M.lift.map c₁)
    (hg₁ : M.lift.map₂ σd₁.inv ≫ g₁ ≫ M.lift.map₂ σc₁.hom = adj.unit)
    {p₂ q₂ : a ⟶ b} {d₂ c₂ : b ⟶ a} (σp₂ : p₂ ≅ r) (σq₂ : q₂ ≅ r) (σd₂ : d₂ ≅ e) (σc₂ : c₂ ≅ e)
    (g₂ : M.lift.map d₂ ⟶ M.lift.map c₂)
    (hg₂ : M.lift.map₂ σd₂.inv ≫ g₂ ≫ M.lift.map₂ σc₂.hom = x)
    {p₃ d₃ c₃ : a ⟶ a} {q₃ : a ⟶ b} (σp₃ : p₃ ≅ 𝟙 a) (σq₃ : q₃ ≅ r) (σd₃ : d₃ ≅ r ≫ e)
    (σc₃ : c₃ ≅ 𝟙 a) (g₃ : M.lift.map d₃ ⟶ M.lift.map c₃)
    (hg₃ : M.lift.map₂ σd₃.inv ≫ g₃ ≫ M.lift.map₂ σc₃.hom = adj.counit)
    {p₄ : a ⟶ a} {q₄ : b ⟶ b} {d₄ c₄ : a ⟶ b} (σp₄ : p₄ ≅ 𝟙 a) (σq₄ : q₄ ≅ 𝟙 b) (σd₄ : d₄ ≅ r)
    (σc₄ : c₄ ≅ r) (g₄ : M.lift.map d₄ ⟶ M.lift.map c₄)
    (hg₄ : M.lift.map₂ σd₄.inv ≫ g₄ ≫ M.lift.map₂ σc₄.hom =
      Bicategory.conjugateEquiv adj adj x)
    {P P₁ Q₁ P₂ Q₂ P₃ Q₃ Q P₄ Q₄ : a ⟶ b}
    (E₀ : P ⟶ P₁) (A₁ : P₁ ⟶ p₁ ≫ (d₁ ≫ q₁)) (B₁ : p₁ ≫ (c₁ ≫ q₁) ⟶ Q₁) (E₁ : Q₁ ⟶ P₂)
    (A₂ : P₂ ⟶ p₂ ≫ (d₂ ≫ q₂)) (B₂ : p₂ ≫ (c₂ ≫ q₂) ⟶ Q₂) (E₂ : Q₂ ⟶ P₃)
    (A₃ : P₃ ⟶ p₃ ≫ (d₃ ≫ q₃)) (B₃ : p₃ ≫ (c₃ ≫ q₃) ⟶ Q₃) (E₃ : Q₃ ⟶ Q)
    (F₀ : P ⟶ P₄) (A₄ : P₄ ⟶ p₄ ≫ (d₄ ≫ q₄)) (B₄ : p₄ ≫ (c₄ ≫ q₄) ⟶ Q₄) (F₁ : Q₄ ⟶ Q) :
    M.lift.map₂ E₀ ≫ (M.lift.map₂ A₁ ≫ midK M p₁ q₁ g₁ ≫ M.lift.map₂ B₁) ≫ M.lift.map₂ E₁ ≫
        (M.lift.map₂ A₂ ≫ midK M p₂ q₂ g₂ ≫ M.lift.map₂ B₂) ≫ M.lift.map₂ E₂ ≫
          (M.lift.map₂ A₃ ≫ midK M p₃ q₃ g₃ ≫ M.lift.map₂ B₃) ≫ M.lift.map₂ E₃ =
      M.lift.map₂ F₀ ≫ (M.lift.map₂ A₄ ≫ midK M p₄ q₄ g₄ ≫ M.lift.map₂ B₄) ≫
        M.lift.map₂ F₁ := by
  rw [midK_canon M σp₁ σq₁ σd₁ σc₁ g₁, hg₁, midK_canon M σp₂ σq₂ σd₂ σc₂ g₂, hg₂,
    midK_canon M σp₃ σq₃ σd₃ σc₃ g₃, hg₃, midK_canon M σp₄ σq₄ σd₄ σc₄ g₄, hg₄]
  simp only [Category.assoc, ← PrelaxFunctor.map₂_comp_assoc, ← PrelaxFunctor.map₂_comp]
  have hmid : midK M r (𝟙 b) (x := 𝟙 b) (y := e ≫ r) adj.unit ≫
      M.lift.map₂ (r ◁ (ρ_ (e ≫ r)).hom) ≫
      midK M r r x ≫ M.lift.map₂ ((α_ r e r).inv ≫ (λ_ _).inv) ≫
        midK M (𝟙 a) r (x := r ≫ e) (y := 𝟙 a) adj.counit =
      M.lift.map₂ (r ◁ (λ_ (𝟙 b)).hom ≫ (λ_ (r ≫ 𝟙 b)).inv) ≫
        midK M (𝟙 a) (𝟙 b) (Bicategory.conjugateEquiv adj adj x) ≫
          M.lift.map₂ (𝟙 a ◁ ((ρ_ r).hom ≫ (λ_ r).inv)) := by
    simp only [midK, PrelaxFunctor.map₂_comp, lift_map₂_whiskerLeft, lift_map₂_associator_inv,
      lift_map₂_leftUnitor_hom, lift_map₂_leftUnitor_inv, lift_map₂_rightUnitor_hom,
      lift_map_comp]
    exact rotL_aux adj x
  rw [lift_map₂_eq M _ (r ◁ (ρ_ (e ≫ r)).hom),
    lift_map₂_eq M _ ((α_ r e r).inv ≫ (λ_ _).inv), reassoc_of% hmid]
  simp only [Category.assoc, ← PrelaxFunctor.map₂_comp_assoc, ← PrelaxFunctor.map₂_comp]
  exact lift_conj_eq M _ _ _ _ _

end Mid

/-- A transport between images of equal free 1-morphisms is the image of a free 2-morphism. -/
theorem eqToHom_lift {a b : FB S} {f g : a ⟶ b} (h : f = g)
    (e : M.lift.map f = M.lift.map g) : eqToHom e = M.lift.map₂ (eqToHom h) := by
  subst h; rw [eqToHom_refl, eqToHom_refl, PrelaxFunctor.map₂_id]

/-- The image of a transport between equal free 1-morphisms. -/
theorem lift_map₂_eqToHom {a b : FB S} {f g : a ⟶ b} (h : f = g) :
    M.lift.map₂ (eqToHom h) = eqToHom (congrArg M.lift.map h) := by
  subst h; rw [eqToHom_refl, eqToHom_refl, PrelaxFunctor.map₂_id]

omit M in
/-- Generators of the free bicategory given by equal colours are equal. -/
theorem hom_of_congr {x y : RQ S} {f f' : x ⟶ y} (h : f.1 = f'.1) :
    FreeBicategory.Hom.of f = FreeBicategory.Hom.of f' := by
  rw [Subtype.ext h]

omit M in
/-- Composites of two generators through equal regions, with equal colours, are equal. -/
theorem comp_of_congr {x y y' z : RQ S} (hy : y = y') {f : x ⟶ y} {g : y ⟶ z} {f' : x ⟶ y'}
    {g' : y' ⟶ z} (hf : f.1 = f'.1) (hg : g.1 = g'.1) :
    (FreeBicategory.Hom.of f ≫ FreeBicategory.Hom.of g : fo (S := S) x ⟶ fo z) =
      FreeBicategory.Hom.of f' ≫ FreeBicategory.Hom.of g' := by
  subst hy; rw [Subtype.ext hf, Subtype.ext hg]

/-! ## Generator images and layers -/

/-- **Images of the generators** for a model: for every generator `g`, read between any two
regions `a`, `b` equal to its left and right regions (with its boundary words well formed from
`a`), a 2-morphism between the images of its bottom and top boundaries. -/
structure GenImg where
  /-- The image of a generator. -/
  gen : (g : S.Gen) → (a b : S.Region) → S.left g = a → S.right g = b →
    (hd : S.ok a (S.dom g)) → (hde : S.endR a (S.dom g) = b) → (hc : S.ok a (S.cod g)) →
    (hce : S.endR a (S.cod g) = b) →
    (M.word a (S.dom g) b hd hde ⟶ M.word a (S.cod g) b hc hce)

variable {M}

/-- The splitting `fw (left ++ w ++ right) ≅ fw right ≫ (fw w ≫ fw left)` of a boundary word of
a layer read from the region `s`, for `w` the bottom or top boundary of its generator, at regions
`m`, `n` equal to the left and right regions of the generator. -/
def layerSplit (L : Layer S) (s m n t : S.Region) (hl : S.ok s L.left)
    (hm : S.endR s L.left = m) (w : List S.Colour) (hwo : S.ok m w) (hwe : S.endR m w = n)
    (hro : S.ok n L.right) (ht : S.endR n L.right = t) :
    fw s ((L.left ++ w) ++ L.right) t
        (ok_append_of (ok_append_of hl hm hwo) (endR_append_of hm hwe) hro)
        (endR_append_of (endR_append_of hm hwe) ht) ≅
      fw n L.right t hro ht ≫ (fw m w n hwo hwe ≫ fw s L.left m hl hm) :=
  splitIso s (L.left ++ w) L.right n t
      (ok_append_of hl hm hwo) (endR_append_of hm hwe) hro ht ≪≫
    whiskerLeftIso _ (splitIso s L.left w m n hl hm hwo hwe)

theorem Valid.ok_dom_of {L : Layer S} (hv : L.Valid) {m : S.Region} (ha : S.left L.gen = m) :
    S.ok m (S.dom L.gen) := ha ▸ hv.dom_ok

theorem Valid.ok_cod_of {L : Layer S} (hv : L.Valid) {m : S.Region} (ha : S.left L.gen = m) :
    S.ok m (S.cod L.gen) := ha ▸ hv.cod_ok

theorem Valid.dom_end_of {L : Layer S} (hv : L.Valid) {m n : S.Region} (ha : S.left L.gen = m)
    (hb : S.right L.gen = n) : S.endR m (S.dom L.gen) = n := ha ▸ hb ▸ hv.dom_end

theorem Valid.cod_end_of {L : Layer S} (hv : L.Valid) {m n : S.Region} (ha : S.left L.gen = m)
    (hb : S.right L.gen = n) : S.endR m (S.cod L.gen) = n := ha ▸ hb ▸ hv.cod_end

theorem Valid.right_ok_of {L : Layer S} (hv : L.Valid) {n : S.Region} (hb : S.right L.gen = n) :
    S.ok n L.right := hb ▸ hv.right_ok

/-- **The image of a valid layer**, read from the region `s` and split at regions `m`, `n` equal
to the left and right regions of its generator, between the images of its boundary words (with
right region `t`): the generator image whiskered by the images of the strands on either side,
conjugated by the splittings. -/
def core (G : GenImg M) {L : Layer S} (hv : L.Valid) (s m n t : S.Region) (hl : S.ok s L.left)
    (hm : S.endR s L.left = m) (ha : S.left L.gen = m) (hb : S.right L.gen = n)
    (ht : S.endR n L.right = t) :
    M.lift.map (fw s ((L.left ++ S.dom L.gen) ++ L.right) t
        (ok_append_of (ok_append_of hl hm (Valid.ok_dom_of hv ha)) (endR_append_of hm
          (Valid.dom_end_of hv ha hb)) (Valid.right_ok_of hv hb))
        (endR_append_of (endR_append_of hm (Valid.dom_end_of hv ha hb)) ht)) ⟶
      M.lift.map (fw s ((L.left ++ S.cod L.gen) ++ L.right) t
        (ok_append_of (ok_append_of hl hm (Valid.ok_cod_of hv ha)) (endR_append_of hm
          (Valid.cod_end_of hv ha hb)) (Valid.right_ok_of hv hb))
        (endR_append_of (endR_append_of hm (Valid.cod_end_of hv ha hb)) ht)) :=
  M.lift.map₂ (layerSplit L s m n t hl hm (S.dom L.gen) (Valid.ok_dom_of hv ha) (Valid.dom_end_of hv ha hb)
      (Valid.right_ok_of hv hb) ht).hom ≫
    midK M (fw n L.right t (Valid.right_ok_of hv hb) ht) (fw s L.left m hl hm)
      (G.gen L.gen m n ha hb (Valid.ok_dom_of hv ha) (Valid.dom_end_of hv ha hb) (Valid.ok_cod_of hv ha)
        (Valid.cod_end_of hv ha hb)) ≫
    M.lift.map₂ (layerSplit L s m n t hl hm (S.cod L.gen) (Valid.ok_cod_of hv ha) (Valid.cod_end_of hv ha hb)
      (Valid.right_ok_of hv hb) ht).inv

/-- The image of a layer does not depend on the choice of the splitting regions. -/
theorem core_regions (G : GenImg M) {L : Layer S} (hv : L.Valid) (s m n m' n' t : S.Region)
    (hl : S.ok s L.left) (hm : S.endR s L.left = m) (ha : S.left L.gen = m)
    (hb : S.right L.gen = n) (hm' : S.endR s L.left = m') (ha' : S.left L.gen = m')
    (hb' : S.right L.gen = n') (ht : S.endR n L.right = t) (ht' : S.endR n' L.right = t) :
    core G hv s m n t hl hm ha hb ht = core G hv s m' n' t hl hm' ha' hb' ht' := by
  subst ha hb ha' hb'; rfl

/-! ## Admissible objects -/

/-- An object is *admissible* for the outer regions `s₀`, `t₀`: its word is well formed read
from `s₀` and ends in `t₀`, and it starts in `s₀`. -/
abbrev Cond (s₀ t₀ : S.Region) (a : Obj S) : Prop :=
  S.ok s₀ a.word ∧ S.endR s₀ a.word = t₀ ∧ a.start = s₀

namespace Cond

variable {s₀ t₀ : S.Region} {L : Layer S}

theorem left_ok (hv : L.Valid) (h : Cond s₀ t₀ L.dom) : S.ok s₀ L.left := by
  rw [← h.2.2]; exact hv.left_ok

theorem left_end (hv : L.Valid) (h : Cond s₀ t₀ L.dom) : S.endR s₀ L.left = S.left L.gen := by
  rw [← h.2.2]; exact hv.left_end

theorem right_end (hv : L.Valid) (h : Cond s₀ t₀ L.dom) : S.endR (S.right L.gen) L.right = t₀ := by
  have := hv.endR_dom
  simp only [Obj.endR, Layer.dom_start] at this
  have h2 : L.start = s₀ := h.2.2
  rw [← this, h2]; exact h.2.1

theorem cod (hv : L.Valid) (h : Cond s₀ t₀ L.dom) : Cond s₀ t₀ L.cod :=
  ⟨ok_append_of (ok_append_of (h.left_ok hv) (h.left_end hv) hv.cod_ok)
      (endR_append_of (h.left_end hv) hv.cod_end) hv.right_ok,
    endR_append_of (endR_append_of (h.left_end hv) hv.cod_end) (h.right_end hv), h.2.2⟩

theorem chain {a b : Obj S} {ls : List (Layer S)} (hc : Chain a ls b) (h : Cond s₀ t₀ a) :
    Cond s₀ t₀ b := by
  induction ls generalizing a with
  | nil => cases hc; exact h
  | cons L ls ih => exact ih hc.2.2 (Cond.cod hc.1 (hc.2.1 ▸ h))

/-- Whiskering an admissible object. -/
theorem whisker {s t : S.Region} {a u : Obj S} {v : List S.Colour} (h : Cond s t a)
    (hu : S.ok u.start u.word) (hue : S.endR u.start u.word = s) (hvv : S.ok t v) :
    Cond u.start (S.endR t v) (a.whisker u v) :=
  ⟨ok_append_of (ok_append_of hu hue h.1) (endR_append_of hue h.2.1) hvv,
    endR_append_of (endR_append_of hue h.2.1) rfl, rfl⟩

end Cond

/-- The image of a valid layer between the images of its boundary words, for an admissible
bottom boundary. It is split at the regions reached by reading the words (`S.endR s₀ L.left`
and the end of the bottom boundary of the generator read from there), so that images of
generators are taken at the regions named by the strands of the layer. -/
def coreC (G : GenImg M) {s₀ t₀ : S.Region} {L : Layer S} (hv : L.Valid)
    (h : Cond s₀ t₀ L.dom) :
    M.word s₀ L.dom.word t₀ h.1 h.2.1 ⟶ M.word s₀ L.cod.word t₀ (h.cod hv).1 (h.cod hv).2.1 :=
  core G hv s₀ (S.endR s₀ L.left) (S.endR (S.endR s₀ L.left) (S.dom L.gen)) t₀ (h.left_ok hv) rfl
    (h.left_end hv).symm (by rw [h.left_end hv]; exact hv.dom_end.symm)
    (by rw [h.left_end hv, hv.dom_end]; exact h.right_end hv)

theorem coreC_eq (G : GenImg M) {s₀ t₀ : S.Region} {L : Layer S} (hv : L.Valid)
    (h : Cond s₀ t₀ L.dom) :
    coreC G hv h = core G hv s₀ (S.left L.gen) (S.right L.gen) t₀ (h.left_ok hv) (h.left_end hv)
      rfl rfl (h.right_end hv) :=
  core_regions G hv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-! ## The interpretation with fixed outer regions -/

section Interp

open Classical
open CategoryTheory.Limits
open scoped ZeroObject

variable [∀ a b : C, Limits.HasZeroObject (a ⟶ b)]
variable (G : GenImg M) (s₀ t₀ : S.Region)

variable (M) in
/-- The image of an object in the hom category `C(M.obj t₀, M.obj s₀)`: the image of its word if
it is admissible, `0` otherwise. -/
def objI (a : Obj S) : M.lift.obj (fo t₀) ⟶ M.lift.obj (fo s₀) :=
  if h : Cond s₀ t₀ a then M.word s₀ a.word t₀ h.1 h.2.1 else 0

theorem objI_pos {a : Obj S} (h : Cond s₀ t₀ a) :
    objI M s₀ t₀ a = M.word s₀ a.word t₀ h.1 h.2.1 :=
  dite_eq_left h

variable [∀ a b : C, Preadditive (a ⟶ b)]

/-- The image of a valid layer. -/
def layerI (L : Layer S) (hv : L.Valid) : objI M s₀ t₀ L.dom ⟶ objI M s₀ t₀ L.cod :=
  if h : Cond s₀ t₀ L.dom then
    eqToHom (objI_pos s₀ t₀ h) ≫ coreC G hv h ≫ eqToHom (objI_pos s₀ t₀ (h.cod hv)).symm
  else 0

theorem layerI_pos {L : Layer S} (hv : L.Valid) (h : Cond s₀ t₀ L.dom) :
    layerI G s₀ t₀ L hv =
      eqToHom (objI_pos s₀ t₀ h) ≫ coreC G hv h ≫ eqToHom (objI_pos s₀ t₀ (h.cod hv)).symm :=
  dite_eq_left h

/-- **The interpretation** of the free 2-category on `S` in `C(M.obj t₀, M.obj s₀)`. -/
abbrev interp : Interpretation S (M.lift.obj (fo t₀) ⟶ M.lift.obj (fo s₀)) where
  obj := objI M s₀ t₀
  layer L hv := layerI G s₀ t₀ L hv

@[simp] theorem interp_obj (a : Obj S) : (interp G s₀ t₀).obj a = objI M s₀ t₀ a := rfl

@[simp] theorem interp_layer (L : Layer S) (hv : L.Valid) :
    (interp G s₀ t₀).layer L hv = layerI G s₀ t₀ L hv := rfl

end Interp

/-! ## Whiskering -/

section Whisker

variable (G : GenImg M) {s t : S.Region} {u : Obj S} {v : List S.Colour}
  (hu : S.ok u.start u.word) (hue : S.endR u.start u.word = s) (hvv : S.ok t v)

/-- **Whiskering a layer**: the image of `u ⊗ L ⊗ v` is the image of `L`, whiskered by the images
of `v` and `u`, up to images of free 2-morphisms. -/
theorem coreC_whisker {L : Layer S} (hv : L.Valid) (h : Cond s t L.dom)
    (hvw : (L.whisker u v).Valid) (hw' : Cond u.start (S.endR t v) (L.whisker u v).dom)
    (φ : fw u.start (L.whisker u v).dom.word (S.endR t v) hw'.1 hw'.2.1 ⟶
      fw t v (S.endR t v) hvv rfl ≫ (fw s L.dom.word t h.1 h.2.1 ≫ fw u.start u.word s hu hue))
    (ψ : fw t v (S.endR t v) hvv rfl ≫
        (fw s L.cod.word t (h.cod hv).1 (h.cod hv).2.1 ≫ fw u.start u.word s hu hue) ⟶
      fw u.start (L.whisker u v).cod.word (S.endR t v) (hw'.cod hvw).1 (hw'.cod hvw).2.1) :
    coreC G hvw hw' = M.lift.map₂ φ ≫
      midK M (fw t v (S.endR t v) hvv rfl) (fw u.start u.word s hu hue) (coreC G hv h) ≫
        M.lift.map₂ ψ := by
  rw [coreC_eq, coreC_eq]
  exact conj_key M (splitIso (S.right L.gen) L.right v t (S.endR t v) hv.right_ok
    (h.right_end hv) hvv rfl) (splitIso u.start u.word L.left s (S.left L.gen) hu hue
    (h.left_ok hv) (h.left_end hv)) _ _ _ _ _ φ ψ

variable [∀ a b : C, Limits.HasZeroObject (a ⟶ b)] [∀ a b : C, Preadditive (a ⟶ b)]

/-- The splitting of a whiskered admissible word. -/
def splitW (a : Obj S) (ha : Cond s t a) :
    fw u.start (a.whisker u v).word (S.endR t v) (ha.whisker hu hue hvv).1
        (ha.whisker hu hue hvv).2.1 ≅
      fw t v (S.endR t v) hvv rfl ≫ (fw s a.word t ha.1 ha.2.1 ≫ fw u.start u.word s hu hue) :=
  splitIso u.start (u.word ++ a.word) v t (S.endR t v) (ok_append_of hu hue ha.1)
      (endR_append_of hue ha.2.1) hvv rfl ≪≫
    whiskerLeftIso _ (splitIso u.start u.word a.word s t hu hue ha.1 ha.2.1)

/-- **Whiskering a chain of layers**: the image of `u ⊗ f ⊗ v` (for outer regions `u.start` and
the end of `v`), after transport to images of words, is the image of `f` (for outer regions `s`,
`t`) whiskered by the images of `v` and `u`, up to images of free 2-morphisms. -/
theorem mapChain_whisker (ls : List (Layer S)) :
    ∀ (lw : List (Layer S)) (_hl : lw = ls.map (·.whisker u v)) (a a' b : Obj S)
      (_e : a' = a.whisker u v) (hc : Chain a ls b)
      (hcw : Chain a' lw (b.whisker u v)) (ha : Cond s t a)
      (hb : Cond s t b) (hwa : Cond u.start (S.endR t v) a')
      (hwb : Cond u.start (S.endR t v) (b.whisker u v))
      (φ : fw u.start a'.word (S.endR t v) hwa.1 hwa.2.1 ⟶
        fw t v (S.endR t v) hvv rfl ≫ (fw s a.word t ha.1 ha.2.1 ≫ fw u.start u.word s hu hue))
      (ψ : fw t v (S.endR t v) hvv rfl ≫ (fw s b.word t hb.1 hb.2.1 ≫ fw u.start u.word s hu hue) ⟶
        fw u.start (b.whisker u v).word (S.endR t v) hwb.1 hwb.2.1),
      eqToHom (objI_pos u.start (S.endR t v) hwa).symm ≫
          (interp G u.start (S.endR t v)).mapChain a' _ _ hcw ≫
          eqToHom (objI_pos u.start (S.endR t v) hwb) =
        M.lift.map₂ φ ≫
          midK M (fw t v (S.endR t v) hvv rfl) (fw u.start u.word s hu hue)
            (eqToHom (objI_pos s t ha).symm ≫ (interp G s t).mapChain a ls b hc ≫
              eqToHom (objI_pos s t hb)) ≫
          M.lift.map₂ ψ := by
  induction ls with
  | nil =>
    intro lw hl a a' b e hc hcw ha hb hwa hwb φ ψ
    simp only [List.map_nil] at hl
    subst hl
    obtain rfl : a = b := hc
    obtain rfl : a' = a.whisker u v := hcw
    simp only [Interpretation.mapChain, eqToHom_trans, eqToHom_refl, midK_id, Category.id_comp,
      ← PrelaxFunctor.map₂_comp]
    rw [lift_map₂_eq M (φ ≫ ψ) (𝟙 _), PrelaxFunctor.map₂_id]
  | cons L ls ih =>
    intro lw hl a a' b e hc hcw ha hb hwa hwb φ ψ
    cases lw with
    | nil => simp at hl
    | cons Lw lsw => ?_
    simp only [List.map_cons, List.cons.injEq] at hl
    obtain ⟨rfl, hls⟩ := hl
    obtain ⟨hv, rfl, hc'⟩ := hc
    obtain ⟨hvw, hwd, hcw'⟩ := hcw
    have hLw : Cond u.start (S.endR t v) (L.whisker u v).dom := hwd ▸ hwa
    have hcod : Cond s t L.cod := ha.cod hv
    have ec : (L.whisker u v).cod = L.cod.whisker u v := Layer.whisker_cod L u v
    have ed : (L.whisker u v).dom = L.dom.whisker u v := Layer.whisker_dom L u v
    simp only [Interpretation.mapChain, layerI_pos G _ _ hvw hLw, layerI_pos G _ _ hv ha,
      Category.assoc, eqToHom_trans_assoc]
    rw [ih lsw hls L.cod (L.whisker u v).cod b ec hc' hcw' hcod hb (hLw.cod hvw) hwb
      (eqToHom (fw_eq (congrArg Obj.word ec) _ _ _ _) ≫ (splitW hu hue hvv L.cod hcod).hom) ψ,
      coreC_whisker G hu hue hvv hv ha hvw hLw
        (eqToHom (fw_eq (congrArg Obj.word ed) _ _ _ _) ≫ (splitW hu hue hvv L.dom ha).hom)
        ((splitW hu hue hvv L.cod hcod).inv ≫ eqToHom (fw_eq (congrArg Obj.word ec).symm _ _ _ _)),
      eqToHom_lift M (fw_eq (congrArg Obj.word hwd.symm) _ _ _ _)]
    simp only [midK_comp, Category.assoc, eqToHom_refl, Category.id_comp]
    rw [← PrelaxFunctor.map₂_comp_assoc, ← PrelaxFunctor.map₂_comp_assoc,
      lift_map₂_eq M (_ ≫ _) φ, lift_map₂_eq M (_ ≫ _) (𝟙 _), PrelaxFunctor.map₂_id,
      Category.id_comp]

end Whisker

omit M in
/-- Conjugating by transports and back. -/
theorem eq_conj {D : Type*} [Category D] {X X' Y Y' : D} (p : X = X') (q : Y = Y') (k : X ⟶ Y) :
    k = eqToHom p ≫ (eqToHom p.symm ≫ k ≫ eqToHom q) ≫ eqToHom q.symm := by
  subst p q; simp

/-! ## The interchange law -/

section Interchange

open CategoryTheory.Limits
open scoped ZeroObject

variable [∀ a b : C, Limits.HasZeroObject (a ⟶ b)] [∀ a b : C, Preadditive (a ⟶ b)]
  (G : GenImg M)

omit [∀ a b : C, Limits.HasZeroObject (a ⟶ b)] [∀ a b : C, Preadditive (a ⟶ b)] in
theorem eqToHom_word {s t : S.Region} {w w' : List S.Colour} {h : S.ok s w}
    {e : S.endR s w = t} {h' : S.ok s w'} {e' : S.endR s w' = t} (hw : w = w')
    (p : M.word s w t h e = M.word s w' t h' e') :
    eqToHom p = M.lift.map₂ (eqToHom (fw_eq hw h e h' e')) :=
  eqToHom_lift M _ p

set_option backward.isDefEq.respectTransparency false in
/-- **The interchange law** for the interpretation: the two orders of applying two generators at
disjoint positions have the same image. -/
theorem functor_map_gh_eq_hg (x : InterchangeData S) (hx : x.Valid) (s t : S.Region) :
    (interp G s t).functor.map (InterchangeData.ghDiagram hx) =
      (interp G s t).functor.map (InterchangeData.hgDiagram hx) := by
  by_cases hc : Cond s t x.dom
  swap
  · have hz : IsZero ((interp G s t).functor.obj x.dom) := by
      change IsZero (objI M s t x.dom)
      rw [objI, dite_eq_right hc]
      exact isZero_zero _
    exact hz.eq_of_src _ _
  have hgh := (InterchangeData.ghDiagram hx).2
  have hhg := (InterchangeData.hgDiagram hx).2
  have hcod : Cond s t x.cod := Cond.chain hgh hc
  rw [eq_conj (objI_pos s t hc) (objI_pos s t hcod)
      ((interp G s t).functor.map (InterchangeData.ghDiagram hx)),
    eq_conj (objI_pos s t hc) (objI_pos s t hcod)
      ((interp G s t).functor.map (InterchangeData.hgDiagram hx))]
  congr 2
  have c1 : Cond s t x.gh₁.dom := by rw [hgh.2.1]; exact hc
  have c2 : Cond s t x.gh₂.dom := by rw [hgh.2.2.2.1]; exact c1.cod hx.gh₁
  have c3 : Cond s t x.hg₁.dom := by rw [hhg.2.1]; exact hc
  have c4 : Cond s t x.hg₂.dom := by rw [hhg.2.2.2.1]; exact c3.cod hx.hg₁
  simp only [Interpretation.functor_map, InterchangeData.ghDiagram, InterchangeData.hgDiagram,
    Diagram.layers_mk, Interpretation.mapChain, layerI_pos G _ _ hx.gh₁ c1, layerI_pos G _ _ hx.gh₂ c2, layerI_pos G _ _ hx.hg₁ c3,
    layerI_pos G _ _ hx.hg₂ c4, Category.assoc, eqToHom_trans_assoc, eqToHom_trans, coreC_eq]
  rw [eqToHom_word ?e0 _, eqToHom_word ?e1 _, eqToHom_word ?e2 _, eqToHom_word ?e3 _,
    eqToHom_word ?e4 _, eqToHom_word ?e5 _]
  · obtain ⟨start, g, mid, h⟩ := x
    have hs : start = S.left g := hx.gh₁.left_end
    subst hs
    have hst : S.left g = s := hc.2.2
    subst hst
    have ht : S.right h = t := Cond.right_end hx.hg₁ c3
    subst ht
    have m_ok : S.ok (S.right g) mid := ((Signature.ok_append _ _ _).1 hx.gh₁.right_ok).1
    have m_end : S.endR (S.right g) mid = S.left h := by
      have := hx.hg₁.left_end
      change S.endR (S.left g) (S.dom g ++ mid) = S.left h at this
      have hde : S.endR (S.left g) (S.dom g) = S.right g := hx.gh₁.dom_end
      rw [Signature.endR_append, hde] at this
      exact this
    exact exch_key M (G.gen h (S.left h) (S.right h) rfl rfl hx.hg₁.dom_ok hx.hg₁.dom_end hx.hg₁.cod_ok hx.hg₁.cod_end)
      (G.gen g (S.left g) (S.right g) rfl rfl hx.gh₁.dom_ok hx.gh₁.dom_end hx.gh₁.cod_ok hx.gh₁.cod_end)
      (splitIso (S.right g) mid (S.dom h) (S.left h) (S.right h) m_ok m_end hx.hg₁.dom_ok
        hx.hg₁.dom_end)
      (eqToIso (fw_nil (S.left g) trivial))
      (eqToIso (fw_nil (S.right h) trivial))
      (splitIso (S.left g) (S.cod g) mid (S.right g) (S.left h) hx.gh₁.cod_ok hx.gh₁.cod_end
        m_ok m_end)
      (eqToIso (fw_nil (S.right h) trivial))
      (splitIso (S.left g) (S.dom g) mid (S.right g) (S.left h) hx.gh₁.dom_ok hx.gh₁.dom_end
        m_ok m_end)
      (splitIso (S.right g) mid (S.cod h) (S.left h) (S.right h) m_ok m_end hx.hg₁.cod_ok
        hx.hg₁.cod_end)
      (eqToIso (fw_nil (S.left g) trivial)) _ _ _ _ _ _ _ _ _ _ _ _ _ _
  all_goals simp [InterchangeData.gh₁, InterchangeData.gh₂, InterchangeData.hg₁,
    InterchangeData.hg₂, InterchangeData.dom, InterchangeData.cod, Layer.dom, Layer.cod]

end Interchange

/-! ## Linear whiskering and the reduction of soundness to unwhiskered relations -/

section Additive

variable [∀ a b : C, Preadditive (a ⟶ b)] [∀ (a b c : C) (f : a ⟶ b), (precomp c f).Additive]
  [∀ (a b c : C) (g : b ⟶ c), (postcomp a g).Additive]
  {a b c d : FB S} (p : a ⟶ b) (q : c ⟶ d) {x y : b ⟶ c}

theorem midK_add (k k' : M.lift.map x ⟶ M.lift.map y) :
    midK M p q (k + k') = midK M p q k + midK M p q k' := by
  simp only [midK]
  exact ((congrArg (fun η => M.lift.map p ◁ η) ((postcomp _ (M.lift.map q)).map_add
    (f := k) (g := k'))).trans ((precomp _ (M.lift.map p)).map_add))

theorem midK_zero : midK M p q (0 : M.lift.map x ⟶ M.lift.map y) = 0 := by
  simp only [midK]
  exact ((congrArg (fun η => M.lift.map p ◁ η) ((postcomp _ (M.lift.map q)).map_zero _ _)).trans
    ((precomp _ (M.lift.map p)).map_zero _ _))

end Additive

theorem midK_smul {R : Type*} [CommRing R] [∀ a b : C, Preadditive (a ⟶ b)]
    [∀ a b : C, Linear R (a ⟶ b)] [∀ (a b c : C) (f : a ⟶ b), (precomp c f).Linear R]
    [∀ (a b c : C) (g : b ⟶ c), (postcomp a g).Linear R] {a b c d : FB S} (p : a ⟶ b)
    (q : c ⟶ d) {x y : b ⟶ c} (r : R) (k : M.lift.map x ⟶ M.lift.map y) :
    midK M p q (r • k) = r • midK M p q k := by
  simp only [midK]
  exact ((congrArg (fun η => M.lift.map p ◁ η) ((postcomp _ (M.lift.map q)).map_smul r k)).trans
    ((precomp _ (M.lift.map p)).map_smul r _))

section Linear

open CategoryTheory.Limits
open scoped ZeroObject

variable {R : Type*} [CommRing R] [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
  [∀ (a b c : C) (f : a ⟶ b), (precomp c f).Additive]
  [∀ (a b c : C) (g : b ⟶ c), (postcomp a g).Additive]
  [∀ (a b c : C) (f : a ⟶ b), (precomp c f).Linear R]
  [∀ (a b c : C) (g : b ⟶ c), (postcomp a g).Linear R]

variable [∀ a b : C, Limits.HasZeroObject (a ⟶ b)] (G : GenImg M)

set_option backward.isDefEq.respectTransparency false in
/-- **Whiskering kills relations**: if a linear combination of diagrams `f : a ⟶ b` is killed by
the interpretation with the outer regions of `a` (it suffices that this holds when the whiskering
`u ⊗ a ⊗ v` is admissible for the outer regions `s₀`, `t₀`), then its whiskering `u ⊗ f ⊗ v` is
killed by the interpretation with outer regions `s₀`, `t₀`. -/
theorem freeLift_whisker_eq_zero {a b : Obj S} (f : LinDiagram R a b) (s₀ t₀ : S.Region)
    (u : Obj S) (v : List S.Colour) (hw : a.WhiskerOK u v)
    (hf : Cond s₀ t₀ (a.whisker u v) →
      (freeLift R (interp G a.start a.endR).functor).map f = 0) :
    (freeLift R (interp G s₀ t₀).functor).map (LinDiagram.whisker f u v hw) = 0 := by
  by_cases hc : Cond s₀ t₀ (a.whisker u v)
  swap
  · have hz : IsZero ((freeLift R (interp G s₀ t₀).functor).obj (Free.of R (a.whisker u v))) := by
      change IsZero (objI M s₀ t₀ (a.whisker u v))
      rw [objI, dite_eq_right hc]
      exact isZero_zero _
    exact hz.eq_of_src _ _
  have hf₀ := hf hc
  clear hf
  obtain ⟨hok, hend, hst⟩ := hc
  change u.start = s₀ at hst
  subst hst
  have hu : S.ok u.start u.word := hw.1
  have hue : u.endR = a.start := hw.2.1
  have hvv : S.ok a.endR v := hw.2.2
  have hue' : S.endR u.start u.word = a.start := hue
  have hokA : S.ok a.start a.word := by
    simp only [Obj.whisker_word, Signature.ok_append, hue'] at hok
    exact hok.1.2
  have ha : Cond a.start a.endR a := ⟨hokA, rfl, rfl⟩
  have ht₀ : t₀ = S.endR a.endR v := by
    rw [← hend]; simp only [Obj.whisker_word, Signature.endR_append, hue']; rfl
  subst ht₀
  by_cases hb : Cond a.start a.endR b
  swap
  · have : IsEmpty (a ⟶ b) := ⟨fun d => hb (Cond.chain d.2 ha)⟩
    have hf0 : (f : (a ⟶ b) →₀ R) = 0 := Finsupp.ext fun (d : a ⟶ b) => isEmptyElim d
    show (Finsupp.mapDomain (fun d => Diagram.whisker d u v hw) (f : (a ⟶ b) →₀ R)).sum
      (fun d r => r • (interp G u.start (S.endR a.endR v)).functor.map d) = 0
    rw [hf0, Finsupp.mapDomain_zero, Finsupp.sum_zero_index]
  have hwa := ha.whisker hu hue' hvv
  have hwb := hb.whisker hu hue' hvv
  set φ := (splitW hu hue' hvv a ha).hom
  set ψ := (splitW hu hue' hvv b hb).inv
  set Φ : (objI M a.start a.endR a ⟶ objI M a.start a.endR b) →
      (objI M u.start (S.endR a.endR v) (a.whisker u v) ⟶
        objI M u.start (S.endR a.endR v) (b.whisker u v)) := fun k =>
    eqToHom (objI_pos u.start (S.endR a.endR v) hwa) ≫ (M.lift.map₂ φ ≫
      midK M (fw a.endR v (S.endR a.endR v) hvv rfl) (fw u.start u.word a.start hu hue')
        (eqToHom (objI_pos a.start a.endR ha).symm ≫ k ≫ eqToHom (objI_pos a.start a.endR hb)) ≫
      M.lift.map₂ ψ) ≫ eqToHom (objI_pos u.start (S.endR a.endR v) hwb).symm with hΦ
  have key : ∀ d : a ⟶ b, (interp G u.start (S.endR a.endR v)).functor.map
      (Diagram.whisker d u v hw) = Φ ((interp G a.start a.endR).functor.map d) := by
    intro d
    have e : eqToHom (objI_pos u.start (S.endR a.endR v) hwa).symm ≫
        (interp G u.start (S.endR a.endR v)).functor.map (Diagram.whisker d u v hw) ≫
        eqToHom (objI_pos u.start (S.endR a.endR v) hwb) =
        M.lift.map₂ φ ≫
          midK M (fw a.endR v (S.endR a.endR v) hvv rfl) (fw u.start u.word a.start hu hue')
            (eqToHom (objI_pos a.start a.endR ha).symm ≫
              (interp G a.start a.endR).functor.map d ≫ eqToHom (objI_pos a.start a.endR hb)) ≫
          M.lift.map₂ ψ :=
      mapChain_whisker G hu hue' hvv d.1 _ rfl a (a.whisker u v) b rfl d.2
        (Diagram.whisker d u v hw).2 ha hb hwa hwb φ ψ
    rw [hΦ]
    beta_reduce
    rw [← e]
    exact eq_conj _ _ _
  have hΦadd : ∀ k k', Φ (k + k') = Φ k + Φ k' := by
    intro k k'
    simp only [hΦ, Preadditive.add_comp, Preadditive.comp_add, midK_add]
  have hΦsmul : ∀ (r : R) k, Φ (r • k) = r • Φ k := by
    intro r k
    simp only [hΦ, Linear.smul_comp, Linear.comp_smul, midK_smul]
  have hΦzero : Φ 0 = 0 := by
    simp only [hΦ, Limits.zero_comp, Limits.comp_zero, midK_zero]
  let ΦA : (objI M a.start a.endR a ⟶ objI M a.start a.endR b) →+
      (objI M u.start (S.endR a.endR v) (a.whisker u v) ⟶
        objI M u.start (S.endR a.endR v) (b.whisker u v)) :=
    { toFun := Φ, map_zero' := hΦzero, map_add' := hΦadd }
  have hf' : (f : (a ⟶ b) →₀ R).sum (fun d r => r • (interp G a.start a.endR).functor.map d) =
      0 := hf₀
  show (Finsupp.mapDomain (fun d => Diagram.whisker d u v hw) (f : (a ⟶ b) →₀ R)).sum
      (fun d r => r • (interp G u.start (S.endR a.endR v)).functor.map d) = 0
  rw [Finsupp.sum_mapDomain_index]
  rotate_left
  · intro _; exact zero_smul _ _
  · intro _ _ _; exact add_smul _ _ _
  simp only [key, ← hΦsmul]
  have := map_finsuppSum ΦA (f : (a ⟶ b) →₀ R)
    (fun d r => r • (interp G a.start a.endR).functor.map d)
  simp only [ΦA, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
  exact this.symm.trans ((congrArg Φ hf').trans hΦzero)

omit [∀ (a b c : C) (f : a ⟶ b), (precomp c f).Additive]
  [∀ (a b c : C) (g : b ⟶ c), (postcomp a g).Additive]
  [∀ (a b c : C) (f : a ⟶ b), (precomp c f).Linear R]
  [∀ (a b c : C) (g : b ⟶ c), (postcomp a g).Linear R] in
set_option backward.isDefEq.respectTransparency false in
/-- The interchange relation is killed by the interpretation (for generators of even parity). -/
theorem freeLift_interchange_eq_zero (x : InterchangeData S) (hx : x.Valid)
    (hsign : x.sign = 1) (s t : S.Region) :
    (freeLift R (interp G s t).functor).map (InterchangeData.rel R hx) = 0 := by
  rw [InterchangeData.rel, hsign, Int.cast_one, one_smul, Functor.map_sub, freeLift_map_of,
    freeLift_map_of, functor_map_gh_eq_hg, sub_self]

/-- **Soundness of the interpretation in a bicategory**: if every relation of `P`, read with its
own outer regions, is killed by the interpretation (it suffices: whenever some whiskering of it is
admissible for the outer regions `s₀`, `t₀`), and all generators are even, then the
interpretation with outer regions `s₀`, `t₀` respects `P`, so it descends to a linear functor
`P.Presented ⥤ C(M.obj t₀, M.obj s₀)`. -/
theorem respects (P : Presentation S R) (s₀ t₀ : S.Region)
    (hrel : ∀ (i : P.Rel) (u : Obj S) (v : List S.Colour), (P.dom i).WhiskerOK u v →
      Cond s₀ t₀ ((P.dom i).whisker u v) →
      (freeLift R (interp G (P.dom i).start (P.dom i).endR).functor).map (P.rel i) = 0)
    (heven : ∀ g, S.odd g = false) :
    P.Respects (interp G s₀ t₀).functor where
  rel i u v hw := freeLift_whisker_eq_zero G (P.rel i) s₀ t₀ u v hw (hrel i u v hw)
  interchange x hx u v hw := freeLift_whisker_eq_zero G _ s₀ t₀ u v hw fun _ =>
    freeLift_interchange_eq_zero G x hx (by simp [InterchangeData.sign, heven]) _ _

end Linear

end Categorification.Diagrams.BicatInterp

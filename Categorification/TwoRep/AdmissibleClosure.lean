/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqUpWords

/-!
# Properties of admissible evaluations closed under the tensor ideal operations

Let `R` be a property of 2-morphisms of the target bicategory that is closed under linear
combinations, under composition with arbitrary 2-morphisms, and under whiskering by images of
words whose colours satisfy a predicate `A`. Then the property "every admissible component of
`f` satisfies `R`" (`AdmissibleHolds`) of morphisms `f` of the presented category is closed under
the same operations of the presented category: zero, sums, scalar multiples, composition with
arbitrary morphisms, and whiskering by objects and words whose colours satisfy `A`.

This is the form in which the proof of Webster, arXiv:1309.3796v3, Lemma 4.29 (§4.6) uses the
red-negligible 2-morphisms of the cyclotomic action: a relation that holds only up to
red-negligible terms holds up to red-negligible terms in every context.
-/

noncomputable section

namespace Categorification.Diagrams.BicatInterp

open CategoryTheory Bicategory StringDiagrams

variable {S : Signature} {C : Type*} [Bicategory C] {M : Model S C} {k : Type*} [CommRing k]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear k (a ⟶ b)]
  [∀ (a b c : C) (f : a ⟶ b), (precomp c f).Additive]
  [∀ (a b c : C) (g : b ⟶ c), (postcomp a g).Additive]
  [∀ (a b c : C) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : C) (g : b ⟶ c), (postcomp a g).Linear k]
  (G : GenImg M) (P : Presentation S k)
  (hrel : ∀ (i : P.Rel) {s t : S.Region} (ha : Cond s t (P.dom i))
    (hb : Cond s t (P.cod i)), admissibleMap G ha hb (P.rel i) = 0)
  (heven : ∀ g, S.odd g = false)

/-- A quotient morphism out of an admissible object into an inadmissible one is zero. -/
theorem presented_eq_zero_of_not_cond {s t : S.Region} {a b : Obj S} (ha : Cond s t a)
    (hb : ¬ Cond s t b) (f : P.obj a ⟶ P.obj b) : f = 0 := by
  obtain ⟨f, rfl⟩ := P.lin_surjective f
  rw [linDiagram_eq_zero_of_not_cond ha hb f, P.lin_zero]

theorem admissibleQuotientMap_zero {s t : S.Region} {a b : Obj S} (ha : Cond s t a)
    (hb : Cond s t b) :
    admissibleQuotientMap G P hrel heven ha hb (0 : P.obj a ⟶ P.obj b) = 0 := by
  simpa using admissibleQuotientMap_smul G P hrel heven ha hb (0 : k) 0

variable (R : ∀ {s t : S.Region} {F F' : M.lift.obj (fo t) ⟶ M.lift.obj (fo s)},
  (F ⟶ F') → Prop)

/-- Every admissible component of the quotient morphism `f` has the property `R`. -/
def AdmissibleHolds {a b : Obj S} (f : P.obj a ⟶ P.obj b) : Prop :=
  ∀ {s t : S.Region} (ha : Cond s t a) (hb : Cond s t b),
    R (admissibleQuotientMap G P hrel heven ha hb f)

variable {G P hrel heven R}

namespace AdmissibleHolds

variable (hR0 : ∀ {s t : S.Region} {F F' : M.lift.obj (fo t) ⟶ M.lift.obj (fo s)},
  R (0 : F ⟶ F'))
include hR0

theorem zero {a b : Obj S} : AdmissibleHolds G P hrel heven R (0 : P.obj a ⟶ P.obj b) :=
  fun ha hb => by rw [admissibleQuotientMap_zero]; exact hR0

omit hR0 in
theorem add
    (hRadd : ∀ {s t : S.Region} {F F' : M.lift.obj (fo t) ⟶ M.lift.obj (fo s)}
      {θ θ' : F ⟶ F'}, R θ → R θ' → R (θ + θ'))
    {a b : Obj S} {f g : P.obj a ⟶ P.obj b} (hf : AdmissibleHolds G P hrel heven R f)
    (hg : AdmissibleHolds G P hrel heven R g) : AdmissibleHolds G P hrel heven R (f + g) :=
  fun ha hb => by rw [admissibleQuotientMap_add]; exact hRadd (hf ha hb) (hg ha hb)

omit hR0 in
theorem smul
    (hRsmul : ∀ {s t : S.Region} {F F' : M.lift.obj (fo t) ⟶ M.lift.obj (fo s)}
      (r : k) {θ : F ⟶ F'}, R θ → R (r • θ))
    (r : k) {a b : Obj S} {f : P.obj a ⟶ P.obj b} (hf : AdmissibleHolds G P hrel heven R f) :
    AdmissibleHolds G P hrel heven R (r • f) :=
  fun ha hb => by rw [admissibleQuotientMap_smul]; exact hRsmul r (hf ha hb)

theorem comp_left
    (hRpre : ∀ {s t : S.Region} {F F' F'' : M.lift.obj (fo t) ⟶ M.lift.obj (fo s)}
      (η : F ⟶ F') {θ : F' ⟶ F''}, R θ → R (η ≫ θ))
    {a b c : Obj S} (g : P.obj a ⟶ P.obj b) {f : P.obj b ⟶ P.obj c}
    (hf : AdmissibleHolds G P hrel heven R f) : AdmissibleHolds G P hrel heven R (g ≫ f) := by
  intro s t ha hc
  by_cases hb : Cond s t b
  · rw [admissibleQuotientMap_comp G P hrel heven ha hb hc]
    exact hRpre _ (hf hb hc)
  · rw [presented_eq_zero_of_not_cond P ha hb g, Limits.zero_comp,
      admissibleQuotientMap_zero]
    exact hR0

theorem comp_right
    (hRpost : ∀ {s t : S.Region} {F F' F'' : M.lift.obj (fo t) ⟶ M.lift.obj (fo s)}
      {θ : F ⟶ F'} (η : F' ⟶ F''), R θ → R (θ ≫ η))
    {a b c : Obj S} {f : P.obj a ⟶ P.obj b} (g : P.obj b ⟶ P.obj c)
    (hf : AdmissibleHolds G P hrel heven R f) : AdmissibleHolds G P hrel heven R (f ≫ g) := by
  intro s t ha hc
  by_cases hb : Cond s t b
  · rw [admissibleQuotientMap_comp G P hrel heven ha hb hc]
    exact hRpost _ (hf ha hb)
  · rw [presented_eq_zero_of_not_cond P ha hb f, Limits.zero_comp,
      admissibleQuotientMap_zero]
    exact hR0

/-- **Whiskering.** If `R` is stable under composition and under whiskering by images of words
whose colours satisfy `A`, then so is `AdmissibleHolds`. -/
theorem whisk (A : S.Colour → Prop)
    (hRpre : ∀ {s t : S.Region} {F F' F'' : M.lift.obj (fo t) ⟶ M.lift.obj (fo s)}
      (η : F ⟶ F') {θ : F' ⟶ F''}, R θ → R (η ≫ θ))
    (hRpost : ∀ {s t : S.Region} {F F' F'' : M.lift.obj (fo t) ⟶ M.lift.obj (fo s)}
      {θ : F ⟶ F'} (η : F' ⟶ F''), R θ → R (θ ≫ η))
    (hmid : ∀ {s t s' t' : S.Region} (v : List S.Colour) (hv : S.ok t v)
      (hvt : S.endR t v = t') (w : List S.Colour) (hw : S.ok s' w) (hws : S.endR s' w = s)
      {x y : fo t ⟶ fo s} (θ : M.lift.map x ⟶ M.lift.map y),
      (∀ c ∈ v, A c) → (∀ c ∈ w, A c) → R θ → R (midK M (fw t v t' hv hvt) (fw s' w s hw hws) θ))
    {a b : Obj S} {f : P.obj a ⟶ P.obj b} (hf : AdmissibleHolds G P hrel heven R f)
    (u : Obj S) (v : List S.Colour) (hU : ∀ c ∈ u.word, A c) (hV : ∀ c ∈ v, A c) :
    AdmissibleHolds G P hrel heven R (P.whisk f u v) := by
  intro s' t' hwa hwb
  by_cases hw : a.WhiskerOK u v
  swap
  · obtain ⟨g, rfl⟩ := P.lin_surjective f
    rw [P.whisk_lin, LinDiagram.whisk_of_not_ok _ hw, P.lin_zero, admissibleQuotientMap_zero]
    exact hR0
  obtain ⟨hu, hue, hvv⟩ := hw
  obtain ⟨hok, hend, hs'⟩ := id hwa
  change u.start = s' at hs'
  subst hs'
  change S.ok u.start ((u.word ++ a.word) ++ v) at hok
  change S.endR u.start ((u.word ++ a.word) ++ v) = t' at hend
  rw [Signature.ok_append, Signature.ok_append] at hok
  rw [Signature.endR_append, Signature.endR_append] at hend
  change S.endR u.start u.word = a.start at hue
  rw [hue] at hok hend
  have ha : Cond a.start a.endR a := ⟨hok.1.2, rfl, rfl⟩
  by_cases hb : Cond a.start a.endR b
  swap
  · rw [presented_eq_zero_of_not_cond P ha hb f, P.whisk_zero, admissibleQuotientMap_zero]
    exact hR0
  subst hend
  change R (admissibleQuotientMap G P hrel heven (ha.whisker hu hue hvv) (hb.whisker hu hue hvv)
    (P.whisk f u v))
  rw [admissibleQuotientMap_whisk G P hrel heven a.start a.endR ha hb hu hue hvv
    ⟨hu, hue, hvv⟩ f]
  exact hRpre _ (hRpost _ (hmid v hvv rfl u.word hu hue _ hV hU (hf ha hb)))

end AdmissibleHolds

end Categorification.Diagrams.BicatInterp

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.BicatInterpAdmissiblePseudo
import Categorification.TwoRep.PresGrading
import Categorification.TwoRep.RouqUpWords

/-!
# Linearity of the zero-object-free presented pseudofunctor on 2-morphisms

The admissible quotient maps are additive and `k`-linear (`admissibleQuotientMap_add`,
`admissibleQuotientMap_smul`), so the
pseudofunctor `admissiblePseudofunctor` is additive and `k`-linear on 2-morphisms, for the
preadditive and linear structures of the hom categories of `RevBicat P.Bicat`
(`PresGrading.revPreadditive`, `PresGrading.revLinear`).
-/

noncomputable section
namespace Categorification.Diagrams.BicatInterp
open CategoryTheory Bicategory StringDiagrams PresPseudo
universe w₁ w₂ u₀ u₁ u₂ v₂
variable {S : Signature.{u₀, u₁, u₂}} {C : Type w₁} [Bicategory.{w₂, v₂} C]
  {M : Model S C}
variable {k : Type*} [CommRing k] [∀ a b : C, Preadditive (a ⟶ b)]
  [∀ a b : C, Linear k (a ⟶ b)]
  [∀ (a b c : C) (f : a ⟶ b), (precomp c f).Additive]
  [∀ (a b c : C) (g : b ⟶ c), (postcomp a g).Additive]
  [∀ (a b c : C) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : C) (g : b ⟶ c), (postcomp a g).Linear k]
variable (G : GenImg M) {P : Presentation S k}
  (hrel : ∀ (i : P.Rel) {s t : S.Region} (ha : Cond s t (P.dom i))
    (hb : Cond s t (P.cod i)), admissibleMap G ha hb (P.rel i) = 0)

variable [S.IsEven]

/-- The zero-object-free presented pseudofunctor is additive on 2-morphisms. -/
theorem admissiblePseudofunctor_map₂_add {a b : RevBicat P.Bicat} {x y : a ⟶ b}
    (η θ : x ⟶ y) :
    (admissiblePseudofunctor G hrel).map₂ (η + θ) =
      (admissiblePseudofunctor G hrel).map₂ η + (admissiblePseudofunctor G hrel).map₂ θ :=
  admissibleQuotientMap_add G P hrel Signature.IsEven.odd_eq_false _ _ η θ

/-- The zero-object-free presented pseudofunctor is `k`-linear on 2-morphisms. -/
theorem admissiblePseudofunctor_map₂_smul {a b : RevBicat P.Bicat} {x y : a ⟶ b}
    (r : k) (η : x ⟶ y) :
    (admissiblePseudofunctor G hrel).map₂ (r • η) =
      r • (admissiblePseudofunctor G hrel).map₂ η :=
  admissibleQuotientMap_smul G P hrel Signature.IsEven.odd_eq_false _ _ r η

end Categorification.Diagrams.BicatInterp

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.CyclotomicRegionDownQuotientEpi
import Categorification.WeightedKLR.RedStrands.CyclotomicRegionDownBigon
import Categorification.WeightedKLR.RedStrands.DoubleRouquierRedDownMidSame

/-!
# A red strand between two downward strands of the same colour on regions

Webster, arXiv:1309.3796v3, (4.1) read downward with the red strand in the middle, proof of
Theorem 4.25. The quotient crossing `a′` of the region model, whiskered by a downward strand, is
an epimorphism (`regionRedDownQuot_whiskerRight_epi`), so the relation `DownMidSame` holds for
the region model by `downMidSame_of_epi`, from (4.4d), the bigons (4.2) and the dot slide, when
every red polynomial is a monomial `p r i = X ^ n r i` (`regionDownMidSame`).
-/

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Bicategory KLR CyclotomicAction TwoRep QuantumGroup
  Polynomial

universe u v w u₁ u₂ v₂ w₂

/-- A right whiskering by a left adjoint of a transformation with epimorphic components is an
epimorphism. -/
theorem linearCat_whiskerRight_epi {K : Type u₂} [CommRing K]
    {C D E : LinearCat.{u₂, v₂, w₂} K} {F G : C ⟶ D} (η : F ⟶ G) {H : D ⟶ E} {H' : E ⟶ D}
    (adj : Bicategory.Adjunction H H') (hη : ∀ M, Epi (η.hom.app M)) : Epi (η ▷ H) := by
  have := Functor.preservesEpimorphisms_of_adjunction (LinearCat.toAdjunction adj)
  have h : Epi (η ▷ H).hom := by
    rw [LinearCat.whiskerRight_hom]
    have : ∀ M, Epi ((Functor.whiskerRight η.hom H.obj).app M) := fun M =>
      H.obj.map_epi (η.hom.app M)
    exact @NatTrans.epi_of_epi_app _ _ _ _ _ _ _ this
  exact (ObjectProperty.ι _).epi_of_epi_map h

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {ℓ : ℕ} {p : Fin ℓ → I → k[X]}
  {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  (RD : UDot.WeightDatum C X Y) {lam : Fin ℓ → X}
  (hQ : KLRSymm Q)
  (hlead : ∀ j l, j ≠ l →
    ∃ c : k, IsUnit c ∧ (polyInY (Q j l)).leadingCoeff = Polynomial.C c)
  (hp : ∀ r i, (p r i).Monic)
  (hpdeg : ∀ r i, ((p r i).natDegree : ℤ) = RD.pair (RD.iY i) (lam r))
  (hdeg : ∀ i j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))

/-- **The whiskered quotient crossing of the region model is an epimorphism.** -/
theorem regionRedDownQuot_whiskerRight_epi (r : Fin ℓ) (i : I) {μ μi μij ρi T : X}
    (f₁ : μi + RD.iX i = μ) (f₂ : μij + RD.iX i = μi) (hR : μi + lam r = ρi)
    (e₁ : μij + lam r = T) (q : T + RD.iX i = ρi) :
    Epi ((α_ _ _ _).inv ≫ DoubleDiagram.redDownQuot (regionFamily.{u, v, w} RD hQ hlead hp hpdeg hdeg)
        (fun r _ _ h => regionRed Q p RD lam r h)
        (fun r i _ _ _ _ h₁ h₂ h₃ h₄ => regionRedUpIso Q p RD lam r i h₁ h₂ h₃ h₄)
        r i f₂ e₁ hR q ▷ (regionFamily.{u, v, w} RD hQ hlead hp hpdeg hdeg).E i f₁ ≫
      (α_ _ _ _).hom) := by
  rw [regionRedDownQuot_eq RD hQ hlead hp hpdeg hdeg r i f₂ e₁ hR q]
  have := linearCat_whiskerRight_epi
    (regionRedDownQuotient Q p RD lam r i f₂ e₁ hR q)
    ((regionFamily.{u, v, w} RD hQ hlead hp hpdeg hdeg).adj i f₁)
    (regionRedDownQuotient_app_epi RD r i f₂ e₁ hR q)
  refine @epi_comp _ _ _ _ _ _ inferInstance _ (@epi_comp _ _ _ _ _ _ ?_ _ inferInstance)
  exact this

/-- **A red strand between two downward strands of the same colour on regions** (Webster,
arXiv:1309.3796v3, (4.1) read downward with the red strand in the middle, proof of
Theorem 4.25), when every red polynomial is the monomial `p r i = X ^ n r i`. -/
theorem regionDownMidSame (n : Fin ℓ → I → ℕ) (hpr : ∀ r i, p r i = Polynomial.X ^ n r i) :
    DoubleDiagram.DownMidSame (regionFamily.{u, v, w} RD hQ hlead hp hpdeg hdeg)
      (fun r _ _ h => regionRed Q p RD lam r h)
      (fun r i _ _ _ _ h₁ h₂ h₃ h₄ => regionRedUpIso Q p RD lam r i h₁ h₂ h₃ h₄) n :=
  DoubleDiagram.downMidSame_of_epi _ _ _ n (regionDownBigon hQ hlead hdeg hp hpdeg n hpr)
    (regionDownQuotCrossNatural RD hQ hlead hp hpdeg hdeg)
    (fun r i _ _ _ _ h₁ h₂ h₃ h₄ => by
      rw [regionRedDownQuot_eq RD hQ hlead hp hpdeg hdeg r i h₁ h₂ h₃ h₄]
      exact regionRedDownQuotient_dot i hQ hlead hp hpdeg hdeg r h₁ h₂ h₃ h₄)
    (fun r i _ _ _ _ _ f₁ f₂ hR e₁ q =>
      regionRedDownQuot_whiskerRight_epi RD hQ hlead hp hpdeg hdeg r i f₁ f₂ hR e₁ q)

end Categorification.Stendhal

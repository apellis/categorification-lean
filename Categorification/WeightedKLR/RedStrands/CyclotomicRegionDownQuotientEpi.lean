/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongBaseChangeEpi
import Categorification.TwoRep.BlockSumCrossingEpi
import Categorification.WeightedKLR.RedStrands.CyclotomicRegionDownCross

/-!
# The quotient crossing of a red line is an epimorphism

Webster, arXiv:1309.3796v3, §4.6, proof of Theorem 4.25. On each cyclotomic block the
quotient crossing `z ⊗ n ↦ π(z) ⊗ n` of a downward black strand with a red line is induced by
the surjective cyclotomic projection, so it is surjective
(`cyclotomicRedDownQuotient_app_epi`). Assembling through the weight-space blocks
(`globalRedDownQuotient_app_epi`) and the region factors (`regionRedDownQuotient_app_epi`), the
quotient crossing `a′` of the double model of the region family, whiskered by a downward strand,
is an epimorphism (`regionRedDownQuot_whiskerRight_epi`).
-/

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR CyclotomicAction TwoRep QuantumGroup Polynomial InductionAlong

universe u v w u₁

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) {a b : I → k[X]} (hab : ∀ i, a i ∣ b i)

/-- The quotient crossing on a cyclotomic block is an epimorphism. -/
theorem cyclotomicRedDownQuotient_app_epi (i : I) {β γ : Multiset I} (h : {i} + β = γ)
    (M : ModuleCat.{max (max u v) w} (CycKLR k Q a β)) :
    Epi ((cyclotomicRedDownQuotient.{u, v, w} Q hab i h).app M) := by
  rw [cyclotomicRedDownQuotient_eq_baseChange]
  exact baseChange_app_epi _ _ _ (cyclotomicRedProjection_surjective Q hab γ) M

variable {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  (RD : UDot.WeightDatum C X Y)

/-- The quotient crossing on weight spaces is an epimorphism in each component. -/
theorem globalRedDownQuotient_app_epi (Λ δ : X) (i : I) {x x₂ y y₂ : X}
    (hx : x + RD.iX i = x₂) (hy : y + RD.iX i = y₂) (h : y + δ = x) (h₂ : y₂ + δ = x₂)
    (N : (weightSpace.{u, v, w} Q a RD Λ x).carrier) :
    Epi ((globalRedDownQuotient.{u, v, w} Q hab RD Λ δ i hx hy h h₂).hom.app N) := by
  refine pi_epi_of_epi _ fun d' => ?_
  exact blockResCrossApp_epi (blockSucc RD Λ i hx) (blockSucc RD (Λ + δ) i hy)
    (redBlock RD Λ δ h) (redBlock RD Λ δ h₂) (blockSucc_redBlock RD Λ δ i hx hy h h₂)
    (indBlock Q a RD Λ i hx) (indBlock Q b RD (Λ + δ) i hy)
    (redPullbackBlock Q hab RD Λ δ h) (redPullbackBlock Q hab RD Λ δ h₂)
    (fun _ _ hβ => cyclotomicRedDownQuotient.{u, v, w} Q hab i (blockSucc_eq RD (Λ + δ) i hβ))
    (fun d' => (fibreMap_redBlock_bijective RD Λ δ i hx hy h h₂ d').2)
    (fun _ _ _ M => cyclotomicRedDownQuotient_app_epi Q hab i _ M) N d'


/-- The quotient crossing for a red pullback into a highest weight `Λ'` is an epimorphism in
each component. -/
theorem redPullbackAtDownQuotient_app_epi (Λ δ : X) {Λ' : X} (hΛ : Λ + δ = Λ') (i : I)
    {x x₂ y y₂ : X} (hx : x + RD.iX i = x₂) (hy : y + RD.iX i = y₂) (h : y + δ = x)
    (h₂ : y₂ + δ = x₂) (N : (weightSpace.{u, v, w} Q a RD Λ x).carrier) :
    Epi ((redPullbackAtDownQuotient.{u, v, w} Q RD hab Λ δ hΛ i hx hy h h₂).app N) := by
  subst hΛ
  exact globalRedDownQuotient_app_epi Q hab RD Λ δ i hx hy h h₂ N

section Region

variable {Q} {ℓ : ℕ} {p : Fin ℓ → I → k[X]} {lam : Fin ℓ → X}

/-- The quotient crossing on regions is an epimorphism in each component. -/
theorem regionRedDownQuotient_app_epi (r : Fin ℓ) (i : I) {μ μ₁ μ₂ μ₃ : X}
    (h₁ : μ + RD.iX i = μ₁) (h₂ : μ + lam r = μ₂) (h₃ : μ₁ + lam r = μ₃)
    (h₄ : μ₂ + RD.iX i = μ₃) (N : (region.{u, v, w} Q p RD lam μ₂).carrier) :
    Epi ((regionRedDownQuotient.{u, v, w} Q p RD lam r i h₁ h₂ h₃ h₄).hom.app N) := by
  refine pi_epi_of_epi _ fun ν' => ?_
  refine blockResCrossRevApp_epi (fun ν => r ::ₘ ν) (fun ν => r ::ₘ ν) id id
    (fun _ => rfl) (redFactor Q p RD lam r h₂) (redFactor Q p RD lam r h₃)
    (downFactor Q p RD lam i h₄) (downFactor Q p RD lam i h₁)
    (redFactorDownQuotient Q p RD lam r i h₁ h₂ h₃ h₄) (fun _ _ _ _ => Subsingleton.elim _ _)
    ?_ N ν'
  intro ν ν'' hν M
  subst hν
  exact redPullbackAtDownQuotient_app_epi Q (regionPoly_dvd_cons p r ν) RD _ (lam r)
    (regionHighest_cons lam r ν) i h₄ h₁ h₂ h₃ M

end Region

end Categorification.Stendhal

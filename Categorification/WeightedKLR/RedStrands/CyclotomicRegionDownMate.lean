/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.BlockSumCrossingMate
import Categorification.WeightedKLR.RedStrands.CyclotomicRegionFamily
import Categorification.WeightedKLR.RedStrands.CyclotomicRedCrossing
import Categorification.WeightedKLR.RedStrands.DoubleRouquierRed

/-!
# The quotient crossing is the mate of the red/up crossing

Webster, arXiv:1309.3796v3, §4.6, proof of Theorem 4.25. The red/down crossing `a′` of the
cyclotomic representation, the cyclotomic quotient `I^λ E_i ⟶ E_i I^λ`, is the mate of the
red/up crossing `a`, the isomorphism `F_i I^λ ≅ I^λ F_i`, for the adjunction `E_i ⊣ F_i`. This
holds on each block (`cyclotomicRedDownQuotient_mate`), on weight spaces
(`globalRedDownQuotient_mate`) and on the region categories (`regionRedDownQuotient_mate`).
So it is the crossing `a′` of the double model of the region family (`regionRedDownQuot_eq`).
-/

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR CyclotomicAction TwoRep QuantumGroup Polynomial InductionAlong

universe u v w u₁

section Global

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) {a b : I → k[X]} (hab : ∀ i, a i ∣ b i)
  {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  (RD : UDot.WeightDatum C X Y) (Λ δ : X)

/-- The mate identity of the cyclotomic quotient crossing on one block, componentwise. -/
theorem cyclotomicRedDownQuotient_mate_app (i : I) {β γ : Multiset I} (h : {i} + β = γ)
    (M : ModuleCat.{max u v w} (CycKLR k Q a γ)) :
    (indResAdj Q b i h).unit.app
        ((cyclotomicRedPullback.{u, v, w} Q hab β).obj ((res Q a i h).obj M)) ≫
      (res Q b i h).map ((cyclotomicRedDownQuotient Q hab i h).app ((res Q a i h).obj M)) ≫
      (res Q b i h).map ((cyclotomicRedPullback Q hab γ).map ((indResAdj Q a i h).counit.app M)) =
    (cyclotomicRedPullbackResIso Q hab i h).inv.app M := by
  have := congrArg (fun t => NatTrans.app t M) (cyclotomicRedDownQuotient_mate Q hab i h)
  simpa using this

variable (i : I) {x x₂ y y₂ : X} (hx : x + RD.iX i = x₂) (hy : y + RD.iX i = y₂)
  (h : y + δ = x) (h₂ : y₂ + δ = x₂)

/-- **The quotient crossing on weight spaces is the mate of the red/up crossing** (Webster,
arXiv:1309.3796v3, §4.6, proof of Theorem 4.25) for the induction–restriction adjunctions. -/
theorem globalRedDownQuotient_mate :
    Bicategory.mateEquiv (globalAdj Q a RD Λ i hx) (globalAdj Q b RD (Λ + δ) i hy)
      (globalRedDownQuotient.{u, v, w} Q hab RD Λ δ i hx hy h h₂) =
      (globalRedPullbackResIso Q hab RD Λ δ i hx hy h h₂).inv := by
  apply ObjectProperty.hom_ext
  rw [LinearCat.mate_hom]
  refine NatTrans.ext (funext fun N => funext fun β => ?_)
  refine (mateNat_blockResCross_app (blockSucc RD Λ i hx) (blockSucc RD (Λ + δ) i hy)
    (redBlock RD Λ δ h) (redBlock RD Λ δ h₂) (blockSucc_redBlock RD Λ δ i hx hy h h₂)
    (fun _ _ hβ => indResAdj.{u, v, w} Q a i (blockSucc_eq RD Λ i hβ))
    (fun _ _ hβ => indResAdj.{u, v, w} Q b i (blockSucc_eq RD (Λ + δ) i hβ))
    (redPullbackBlock Q hab RD Λ δ h) (redPullbackBlock Q hab RD Λ δ h₂)
    (fun _ _ hβ => cyclotomicRedDownQuotient.{u, v, w} Q hab i
      (blockSucc_eq RD (Λ + δ) i hβ)) N β).trans ?_
  exact cyclotomicRedDownQuotient_mate_app Q hab i _ _

/-- The mate identity for a red pullback into a highest weight `Λ' = Λ + δ`, componentwise. -/
theorem redPullbackAtDownQuotient_mate_app {Λ' : X} (hΛ : Λ + δ = Λ')
    (N : weightSpace.{u, v, w} Q a RD Λ x₂) :
    (LinearCat.toAdjunction (globalAdj Q b RD Λ' i hy)).unit.app
        ((redPullbackAt Q RD hab Λ δ hΛ h).obj ((globalF Q a RD Λ i hx).obj.obj N)) ≫
      (globalF Q b RD Λ' i hy).obj.map
        ((redPullbackAtDownQuotient Q RD hab Λ δ hΛ i hx hy h h₂).app
          ((globalF Q a RD Λ i hx).obj.obj N)) ≫
      (globalF Q b RD Λ' i hy).obj.map ((redPullbackAt Q RD hab Λ δ hΛ h₂).map
        ((LinearCat.toAdjunction (globalAdj Q a RD Λ i hx)).counit.app N)) =
    (redPullbackAtResIso Q RD hab Λ δ hΛ i hx hy h h₂).inv.app N := by
  subst hΛ
  have := congrArg (fun t => t.hom.app N) (globalRedDownQuotient_mate Q hab RD Λ δ i hx hy h h₂)
  rw [LinearCat.mate_hom] at this
  exact this

end Global

section Region

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
  (r : Fin ℓ) (i : I) {μ μ₁ μ₂ μ₃ : X} (h₁ : μ + RD.iX i = μ₁)
  (h₂ : μ + lam r = μ₂) (h₃ : μ₁ + lam r = μ₃) (h₄ : μ₂ + RD.iX i = μ₃)

/-- **The quotient crossing on regions is the mate of the red/up crossing** (Webster,
arXiv:1309.3796v3, §4.6, proof of Theorem 4.25): `a′` is the mate of `a` for the adjunctions
`E_i ⊣ F_i` of the region family. -/
theorem regionRedDownQuotient_mate :
    Bicategory.mateEquiv ((regionFamily.{u, v, w} RD hQ hlead hp hpdeg hdeg).adj i h₄)
      ((regionFamily.{u, v, w} RD hQ hlead hp hpdeg hdeg).adj i h₁)
      (regionRedDownQuotient Q p RD lam r i h₁ h₂ h₃ h₄) =
      (regionRedUpIso Q p RD lam r i h₁ h₂ h₃ h₄).hom := by
  apply ObjectProperty.hom_ext
  erw [LinearCat.mate_hom]
  refine mateNat_blockResCrossRev (fun ν => r ::ₘ ν) (redFactor Q p RD lam r h₂)
    (redFactor Q p RD lam r h₃) (downFactor Q p RD lam i h₄) (downFactor Q p RD lam i h₁)
    (upFactor Q p RD lam i h₄) (upFactor Q p RD lam i h₁)
    (fun ν => LinearCat.toAdjunction
      (globalAdj Q (regionPoly p ν) RD (regionHighest lam ν) i h₄))
    (fun ν => LinearCat.toAdjunction
      (globalAdj Q (regionPoly p ν) RD (regionHighest lam ν) i h₁))
    (redFactorDownQuotient Q p RD lam r i h₁ h₂ h₃ h₄)
    _
    ((regionFamily.{u, v, w} RD hQ hlead hp hpdeg hdeg).adj i h₁).unit.hom (fun _ _ => rfl)
    ((regionFamily.{u, v, w} RD hQ hlead hp hpdeg hdeg).adj i h₄).counit.hom (fun _ _ => rfl) ?_
  intro ν ν' hν N
  subst hν
  dsimp only [redFactorUpIso, Iso.symm_hom, redFactor, upFactor, redFactorDownQuotient]
  have key := redPullbackAtDownQuotient_mate_app Q (regionPoly_dvd_cons p r ν) RD
    (regionHighest lam ν) (lam r) i h₄ h₁ h₂ h₃ (regionHighest_cons lam r ν) N
  convert key using 2

/-- **The red/down crossing `a′` of the region model is the cyclotomic quotient** (Webster,
arXiv:1309.3796v3, §4.6, proof of Theorem 4.25): the mate of the red/up crossing, as in the
double model of the region family, is the quotient crossing `regionRedDownQuotient`. -/
theorem regionRedDownQuot_eq :
    DoubleDiagram.redDownQuot (regionFamily.{u, v, w} RD hQ hlead hp hpdeg hdeg)
        (fun r _ _ h => regionRed Q p RD lam r h)
        (fun r i _ _ _ _ h₁ h₂ h₃ h₄ => regionRedUpIso Q p RD lam r i h₁ h₂ h₃ h₄)
        r i h₁ h₂ h₃ h₄ =
      regionRedDownQuotient Q p RD lam r i h₁ h₂ h₃ h₄ :=
  (Equiv.symm_apply_eq _).2
    (regionRedDownQuotient_mate RD hQ hlead hp hpdeg hdeg r i h₁ h₂ h₃ h₄).symm

end Region

end Categorification.Stendhal

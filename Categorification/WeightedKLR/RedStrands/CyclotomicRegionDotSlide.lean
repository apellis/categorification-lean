/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.BlockSumCrossingNatural
import Categorification.WeightedKLR.RedStrands.CyclotomicRegionDownBigon

/-!
# Upward dots slide through the red/up crossing of the region model

Webster, arXiv:1309.3796v3, (4.4c), in the proof of Theorem 4.25. A dot on a downward black
strand slides through its quotient crossing with a red line: on each block the quotient
`π(z) ⊗ n` of `z ⊗ n` commutes with right multiplication by the last dot, since the cyclotomic
projection sends the dot to the dot (`cyclotomicRedDownQuotient_dot`). Assembling through the
blocks (`globalRedDownQuotient_dot`) and the region factors (`regionRedDownQuotient_dot`) and
taking mates (`DoubleDiagram.upIsoDotNatural_of_redDownQuot_dot`), the red/up crossings of the
region model are natural for upward dots (`regionUpIsoDotNatural`).
-/

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory CategoryTheory.Bicategory QuantumGroup QuantumGroup.UDot TwoRep

universe u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {ℓ : ℕ} {Λ : Fin ℓ → X}
  {B : Type*} [Bicategory B] [∀ a b : B, Preadditive (a ⟶ b)] [AdditiveWhiskering B]
  (S : RouqFamily (B := B) RD)
  (red : (r : Fin ℓ) → {x y : X} → x + Λ r = y → (S.obj y ⟶ S.obj x))
  (upIso : (r : Fin ℓ) → (i : I) → {μ μ₁ μ₂ μ₃ : X} → (h₁ : μ + RD.iX i = μ₁) →
    (h₂ : μ + Λ r = μ₂) → (h₃ : μ₁ + Λ r = μ₃) → (h₄ : μ₂ + RD.iX i = μ₃) →
    (S.F i h₄ ≫ red r h₂ ≅ red r h₃ ≫ S.F i h₁))

/-- **The red/up crossings are natural for upward dots when the red/down quotient crossings
are natural for downward dots** (the converse of `redDownQuot_dot`, by taking mates). -/
theorem upIsoDotNatural_of_redDownQuot_dot
    (hq : ∀ (r : Fin ℓ) (i : I) {μ μ₁ μ₂ μ₃ : X} (h₁ : μ + RD.iX i = μ₁)
      (h₂ : μ + Λ r = μ₂) (h₃ : μ₁ + Λ r = μ₃) (h₄ : μ₂ + RD.iX i = μ₃),
      red r h₂ ◁ S.dot i h₁ ≫ redDownQuot S red upIso r i h₁ h₂ h₃ h₄ =
        redDownQuot S red upIso r i h₁ h₂ h₃ h₄ ≫ S.dot i h₄ ▷ red r h₃) :
    UpIsoDotNatural S red upIso := by
  intro r i μ μ₁ μ₂ μ₃ h₁ h₂ h₃ h₄
  have key := congrArg (mateEquiv (S.adj i h₄) (S.adj i h₁)) (hq r i h₁ h₂ h₃ h₄)
  have e₁ := mateEquiv_conjugateEquiv_vcomp (S.adj i h₄) (S.adj i h₁) (S.adj i h₁)
    (redDownQuot S red upIso r i h₁ h₂ h₃ h₄) (S.dot i h₁)
  have e₂ := conjugateEquiv_mateEquiv_vcomp (S.adj i h₄) (S.adj i h₄) (S.adj i h₁)
    (S.dot i h₄) (redDownQuot S red upIso r i h₁ h₂ h₃ h₄)
  simp only [leftAdjointSquareConjugate.vcomp, rightAdjointSquareConjugate.vcomp,
    leftAdjointConjugateSquare.vcomp, rightAdjointConjugateSquare.vcomp] at e₁ e₂
  rw [e₁, e₂, redDownQuot, Equiv.apply_symm_apply, ← S.dotDn_eq_rightMate,
    ← S.dotDn_eq_rightMate] at key
  exact key.symm

end Categorification.Stendhal.DoubleDiagram

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Bicategory KLR CyclotomicAction TwoRep QuantumGroup Polynomial
  InductionAlong

universe u v w u₁

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) {a b : I → k[X]} (hab : ∀ i, a i ∣ b i)

set_option backward.isDefEq.respectTransparency false in
/-- **The dot slides through the cyclotomic quotient crossing**: the quotient
`z ⊗ n ↦ π(z) ⊗ n` commutes with right multiplication by the last dot. -/
theorem cyclotomicRedDownQuotient_dot (i : I) {β γ : Multiset I} (h : {i} + β = γ) :
    Functor.whiskerLeft (cyclotomicRedPullback.{u, v, w} Q hab β) (dot Q b i h) ≫
        cyclotomicRedDownQuotient Q hab i h =
      cyclotomicRedDownQuotient Q hab i h ≫
        Functor.whiskerRight (dot Q a i h) (cyclotomicRedPullback Q hab γ) := by
  refine NatTrans.ext (funext fun M => ModuleCat.hom_ext (Ind.ext fun z n => ?_))
  change (cyclotomicRedDownQuotient Q hab i h).app M ((dot Q b i h).app _ (Ind.tmul z n)) =
    (dot Q a i h).app M ((cyclotomicRedDownQuotient Q hab i h).app M (Ind.tmul z n))
  rw [cyclotomicRedDownQuotient_tmul]
  have h1 : (dot Q b i h).app ((cyclotomicRedPullback Q hab β).obj M) (Ind.tmul z n) =
      Ind.tmul (cornerMul (intertwines_dotElt Q b i h) z) n := rfl
  have h2 : (dot Q a i h).app M (Ind.tmul (cyclotomicRedCornerProjection Q hab i h z) n) =
      Ind.tmul (cornerMul (intertwines_dotElt Q a i h)
        (cyclotomicRedCornerProjection Q hab i h z)) n := rfl
  rw [h1, h2, cyclotomicRedDownQuotient_tmul]
  refine congrArg (Ind.tmul · n) (Subtype.ext ?_)
  change cyclotomicRedProjection Q hab γ (z.val * dotElt Q b i h) =
    cyclotomicRedProjection Q hab γ z.val * dotElt Q a i h
  rw [map_mul, dotElt, dotElt, cyclotomicRedProjection_mk]

variable {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  (RD : UDot.WeightDatum C X Y) (Λ δ : X)
  (i : I) {x x₂ y y₂ : X} (hx : x + RD.iX i = x₂) (hy : y + RD.iX i = y₂)
  (h : y + δ = x) (h₂ : y₂ + δ = x₂)

/-- **The dot slides through the red/down quotient crossing on weight spaces.** -/
theorem globalRedDownQuotient_dot :
    globalRedPullback.{u, v, w} Q hab RD Λ δ h ◁ globalDot Q b RD (Λ + δ) i hy ≫
        globalRedDownQuotient Q hab RD Λ δ i hx hy h h₂ =
      globalRedDownQuotient Q hab RD Λ δ i hx hy h h₂ ≫
        globalDot Q a RD Λ i hx ▷ globalRedPullback Q hab RD Λ δ h₂ := by
  apply ObjectProperty.hom_ext
  refine NatTrans.ext (funext fun N => funext fun δ' => ?_)
  exact blockResCross_blockSumMap_app (blockSucc RD Λ i hx) (blockSucc RD (Λ + δ) i hy)
    (redBlock RD Λ δ h) (redBlock RD Λ δ h₂) (blockSucc_redBlock RD Λ δ i hx hy h h₂)
    (indBlock Q a RD Λ i hx) (indBlock Q b RD (Λ + δ) i hy)
    (redPullbackBlock Q hab RD Λ δ h) (redPullbackBlock Q hab RD Λ δ h₂)
    (fun _ _ hβ => cyclotomicRedDownQuotient.{u, v, w} Q hab i (blockSucc_eq RD (Λ + δ) i hβ))
    (fun _ _ hβ => dot.{u, v, w} Q a i (blockSucc_eq RD Λ i hβ))
    (fun _ _ hβ => dot.{u, v, w} Q b i (blockSucc_eq RD (Λ + δ) i hβ))
    (fun _ _ hβ => cyclotomicRedDownQuotient_dot Q hab i (blockSucc_eq RD (Λ + δ) i hβ)) N δ'

/-- The dot slides through the red/down quotient crossing of a red pullback into a highest
weight `Λ' = Λ + δ`. -/
theorem redPullbackAtDownQuotient_dot {Λ' : X} (hΛ : Λ + δ = Λ') :
    Functor.whiskerLeft (redPullbackAt.{u, v, w} Q RD hab Λ δ hΛ h)
        (globalDot Q b RD Λ' i hy).hom ≫
        redPullbackAtDownQuotient Q RD hab Λ δ hΛ i hx hy h h₂ =
      redPullbackAtDownQuotient Q RD hab Λ δ hΛ i hx hy h h₂ ≫
        Functor.whiskerRight (globalDot Q a RD Λ i hx).hom
          (redPullbackAt Q RD hab Λ δ hΛ h₂) := by
  subst hΛ
  exact congrArg (fun t => t.hom) (globalRedDownQuotient_dot Q hab RD Λ δ i hx hy h h₂)

section Region

variable {Q RD} {ℓ : ℕ} {p : Fin ℓ → I → k[X]} {lam : Fin ℓ → X}
  (hQ : KLRSymm Q)
  (hlead : ∀ j l, j ≠ l →
    ∃ c : k, IsUnit c ∧ (polyInY (Q j l)).leadingCoeff = Polynomial.C c)
  (hp : ∀ r i, (p r i).Monic)
  (hpdeg : ∀ r i, ((p r i).natDegree : ℤ) = RD.pair (RD.iY i) (lam r))
  (hdeg : ∀ i j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))
  (r : Fin ℓ) {μ μ₁ μ₂ μ₃ : X} (h₁ : μ + RD.iX i = μ₁)
  (h₂ : μ + lam r = μ₂) (h₃ : μ₁ + lam r = μ₃) (h₄ : μ₂ + RD.iX i = μ₃)

/-- **The dot slides through the red/down quotient crossing on regions.** -/
theorem regionRedDownQuotient_dot :
    regionRed Q p RD lam r h₂ ◁ (regionFamily.{u, v, w} RD hQ hlead hp hpdeg hdeg).dot i h₁ ≫
        regionRedDownQuotient Q p RD lam r i h₁ h₂ h₃ h₄ =
      regionRedDownQuotient Q p RD lam r i h₁ h₂ h₃ h₄ ≫
        (regionFamily.{u, v, w} RD hQ hlead hp hpdeg hdeg).dot i h₄ ▷
          regionRed Q p RD lam r h₃ := by
  apply ObjectProperty.hom_ext
  refine NatTrans.ext (funext fun N => funext fun ν' => ?_)
  exact blockResCrossRev_natural_app (fun ν => r ::ₘ ν) (fun ν => r ::ₘ ν) id id
    (fun _ => rfl) (redFactor Q p RD lam r h₂) (redFactor Q p RD lam r h₃)
    (downFactor Q p RD lam i h₄) (downFactor Q p RD lam i h₁)
    (redFactorDownQuotient Q p RD lam r i h₁ h₂ h₃ h₄)
    (fun ν => (globalDot Q (regionPoly p ν) RD (regionHighest lam ν) i h₄).hom)
    (fun ν' => (globalDot Q (regionPoly p ν') RD (regionHighest lam ν') i h₁).hom)
    (fun ν ν' hν => by
      subst hν
      exact redPullbackAtDownQuotient_dot Q (regionPoly_dvd_cons p r ν) RD _ (lam r) i h₄ h₁
        h₂ h₃ (regionHighest_cons lam r ν)) N ν'

/-- **The red/up crossings of the region model are natural for upward dots** (Webster,
arXiv:1309.3796v3, (4.4c), proof of Theorem 4.25). -/
theorem regionUpIsoDotNatural :
    DoubleDiagram.UpIsoDotNatural (regionFamily.{u, v, w} RD hQ hlead hp hpdeg hdeg)
      (fun r _ _ h => regionRed Q p RD lam r h)
      (fun r i _ _ _ _ h₁ h₂ h₃ h₄ => regionRedUpIso Q p RD lam r i h₁ h₂ h₃ h₄) :=
  DoubleDiagram.upIsoDotNatural_of_redDownQuot_dot _ _ _ fun r i _ _ _ _ h₁ h₂ h₃ h₄ => by
    rw [regionRedDownQuot_eq RD hQ hlead hp hpdeg hdeg r i h₁ h₂ h₃ h₄]
    exact regionRedDownQuotient_dot i hQ hlead hp hpdeg hdeg r h₁ h₂ h₃ h₄

end Region

end Categorification.Stendhal

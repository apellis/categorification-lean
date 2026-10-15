/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.GlobalLoc
import Categorification.KLR.CyclotomicAction.GlobalBraidQ
import Categorification.TwoRep.RouqUpKLR

/-!
# The weight-indexed cyclotomic Rouquier family

For a root datum, a weight `Λ` and cyclotomic polynomials `a_i`, the weight spaces of the
cyclotomic KLR algebras `R^Λ(β)` (products of the blocks `R^Λ(β)-mod` of a given weight, objects
of `LinearCat k`) carry a Rouquier family in the sense of Brundan (arXiv:1501.00350v1,
Definition 1.1): `cyclotomicFamily`. Its 1-morphisms are cyclotomic induction and restriction
(Kang–Kashiwara, arXiv:1102.4677v4, §4.2), with the induction–restriction adjunction, the dots
and the crossings (`ψ` for distinct colours, `-ψ` for equal colours). The single-colour
relations are the nil-Hecke relations on weight spaces together with Kang–Kashiwara's
Theorem 5.2 (`globalLoc`). `cyclotomicFamily_upKLR` gives the mixed upward relations
(Brundan (1.2)–(1.4), `TwoRep.RouqUpKLR`) with the KLR polynomials `Q`.

This is the cyclotomic input on the roadmap for KL III Thm. 1.2. The hypotheses are those of
Kang–Kashiwara §3, ungraded: any commutative ring `k`, `KLRSymm Q`, a unit constant leading
coefficient of `Q_jl` (`j ≠ l`) in the second variable, monic `a_j` of degree `⟨h_j, Λ⟩`, and
`deg_v Q_ji = -⟨h_i, α_j⟩` for `j ≠ i`. Brundan's invertibility of the mixed sideways crossings
(1.7) (`TwoRep.BrundanMixedInversion`) is `cyclotomicFamily_mixedInversion`
(`KLR.CyclotomicAction.GlobalMixed`).
-/

namespace Categorification.KLR.CyclotomicAction

open CategoryTheory CategoryTheory.Bicategory TwoRep KLRAlgebra.AbsentColour

universe u v w u₁

noncomputable section

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {a : I → Polynomial k}
  (hQ : KLRSymm Q)
  (hlead : ∀ j l, j ≠ l → ∃ c : k, IsUnit c ∧ (polyInY (Q j l)).leadingCoeff = Polynomial.C c)
  (ha : ∀ j, (a j).Monic)
  {C : QuantumGroup.CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  (RD : QuantumGroup.UDot.WeightDatum C X Y) (Λ : X)
  (hΛ : ∀ i, ((a i).natDegree : ℤ) = RD.pair (RD.iY i) Λ)
  (hdeg : ∀ i j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))

/-- **The weight-indexed cyclotomic Rouquier family** (Kang–Kashiwara, arXiv:1102.4677v4, §4.2
and Theorem 5.2; Brundan, arXiv:1501.00350v1, Definition 1.1, single-colour part): weight
spaces, cyclotomic induction and restriction with their adjunction, dots, crossings, and
Rouquier's local data `globalLoc`. -/
def cyclotomicFamily :
    RouqFamily (B := LinearCat.{v, max (max u v) w, max (max u v) w + 1} k) RD where
  obj := weightSpace.{u, v, w} Q a RD Λ
  E i _ _ h := globalE Q a RD Λ i h
  F i _ _ h := globalF Q a RD Λ i h
  adj i _ _ h := globalAdj Q a RD Λ i h
  dot i _ _ h := globalDot Q a RD Λ i h
  cross i j _ _ _ _ h₁ h₂ h₃ h₄ := globalCross Q a RD Λ i j h₁ h₂ h₃ h₄
  square i _ _ _ h₁ h₂ := globalCross_sq Q a RD Λ i h₁ h₂
  braid i _ _ _ _ h₁ h₂ h₃ := globalCross_sameBraid Q a RD Λ i h₁ h₂ h₃
  loc i _ _ _ h₁ h₂ := globalLoc RD Λ hQ hlead ha hΛ hdeg i h₁ h₂

/-- **The mixed upward relations for the cyclotomic family** (Brundan, arXiv:1501.00350v1,
Definition 1.1, (1.2)–(1.4)) with the KLR polynomials `Q`. -/
theorem cyclotomicFamily_upKLR :
    RouqUpKLR (cyclotomicFamily.{u, v, w} hQ hlead ha RD Λ hΛ hdeg) Q where
  square i j hij _ _ _ _ h₁ h₂ h₃ h₄ := globalCross_square Q a RD Λ hQ i j hij h₁ h₂ h₃ h₄
  slide_left i j hij _ _ _ _ h₁ h₂ h₃ h₄ := globalCross_slide_left Q a RD Λ i j hij h₁ h₂ h₃ h₄
  slide_right i j hij _ _ _ _ h₁ h₂ h₃ h₄ := globalCross_slide_right Q a RD Λ i j hij h₁ h₂ h₃ h₄
  braid i j c hb _ _ _ _ _ _ _ _ e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 :=
    globalCross_braid Q a RD Λ i j c hb e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12
  braidQ i j hij _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ h₆ h₇ :=
    globalCross_braidQ Q a RD Λ i j hij h₁ h₂ h₃ h₄ h₅ h₆ h₇

end

end Categorification.KLR.CyclotomicAction

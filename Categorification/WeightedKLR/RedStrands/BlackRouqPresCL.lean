/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackRouqMixedUpRelations
import Categorification.WeightedKLR.RedStrands.BlackRouqMixedBraidWeight
import Categorification.WeightedKLR.RedStrands.BlackRouqMixedBraidQWeight
import Categorification.KLR.KKScalars

/-!
# The Cautis–Lauda presentation acts on derived categories of `T^λ`-modules

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, Theorem 4.31
(the derived `Ũ` action on `D(T^λ)`), in Brundan's form (arXiv:1501.00350v1, Definition 1.1 and
Theorem 1.2).

* `blackRouqFamily_upKLR`: Webster's derived Rouquier family `blackRouqFamily` satisfies the
  upward KLR relations for distinct colours, Brundan (1.2)–(1.4), with the family's own
  polynomials `Q`: the mixed square and dot slides (`blackRouqCross_mixed_square`,
  `_slide_left`, `_slide_right`) and the two braid relations (`blackRouqCross_braid`,
  `blackRouqCross_braidQ`).
* `blackRouqFamily_brundanUpKLR`: the same relations with Brundan's polynomials of the
  Kang–Kashiwara scalars `kkScalars` of `Q` (`KLR.eq_brundanQ`), for Rouquier polynomials.
* `blackPresCL`: Cautis–Lauda's normalized presentation `presCL` with these scalars acts on the
  weight spaces of the derived categories of right `T^λ`-modules, by a pseudofunctor into
  `LinearCat k` (Brundan, Theorem 1.2; Webster, Theorem 4.31).

The hypotheses are those of `blackRouqFamily`: a presentation `P` with negligible cover
relations and well-founded domains (Webster's Theorem 4.30, `CoverRelsNegligible`, `WFDom`), a
Rouquier polynomial family `Q` over a field (`IsRouquierQ`, which makes induction exact),
`KLRSymm Q`, and the compatibility `hΛ₀` of the weight `Λ₀` with the red labels (a route
hypothesis of `blackRouqFamily`, recorded there). The upward relations and the mixed inversion
(`blackRouqFamily_mixedInversion`) are proved, so no hypothesis on them remains.
-/

namespace Categorification.Stendhal

open CategoryTheory KLR TwoRep QuantumGroup KL3.Diagram CyclotomicAction DoubleDiagram
  StringDiagrams
open scoped Classical

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe u w w₂ u₁

noncomputable section

variable {I : Type u} {k : Type u} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {C : CartanDatum I}
  {hQ : IsRouquierQ C Q}
  {P : Presentation.{u, u}
    (signature (coordinateDatum Λ C) (redWeight (cyclotomicCoverWeightDatum Λ C))) k}
  (hP : CoverRelsNegligible.{u, u, w} Λ C hQ (coverDotCentral Λ C hQ)
    (blockWeight (cyclotomicCoverWeightDatum Λ C) (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 :
      I ⊕ Fin ℓ → ℤ) P)
  (hwf : P.WFDom)
  [∀ β : Multiset I,
    _root_.HasDerivedCategory.{w₂} (ModuleCat.{u} (TensorProductAlgebra k Q Λ β)ᵐᵒᵖ)]
  {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y] {RD : UDot.WeightDatum C X Y} {Λ₀ : X}
  (hΛ₀ : ∀ i, RD.pair (RD.iY i) Λ₀ = ∑ r : Fin ℓ, (Λ r i : ℤ))
  (hsym : KLRSymm Q)

/-- **The upward KLR relations for distinct colours on Webster's derived action** (Brundan,
arXiv:1501.00350v1, Definition 1.1, (1.2)–(1.4); Webster, arXiv:1309.3796v3, Theorem 4.31),
with the polynomials `Q` of the family. -/
theorem blackRouqFamily_upKLR :
    RouqUpKLR (blackRouqFamily hP hwf hsym hΛ₀) Q where
  square i j hij _ _ _ _ h₁ h₂ h₃ h₄ :=
    blackRouqCross_mixed_square Λ hQ RD Λ₀ hsym i j hij h₁ h₂ h₃ h₄
  slide_left i j hij _ _ _ _ h₁ h₂ h₃ h₄ :=
    blackRouqCross_mixed_slide_left Λ hQ RD Λ₀ hsym i j hij h₁ h₂ h₃ h₄
  slide_right i j hij _ _ _ _ h₁ h₂ h₃ h₄ :=
    blackRouqCross_mixed_slide_right Λ hQ RD Λ₀ hsym i j hij h₁ h₂ h₃ h₄
  braid i j c hb _ _ _ _ _ _ _ _ e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 :=
    blackRouqCross_braid Λ hQ RD Λ₀ hsym i j c hb e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12
  braidQ i j hij _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ h₆ h₇ :=
    blackRouqCross_braidQ Λ hQ RD Λ₀ hsym i j hij h₁ h₂ h₃ h₄ h₅ h₆ h₇

/-- The Kang–Kashiwara scalars of a Rouquier polynomial family. -/
abbrev rouquierScalars (hQ : IsRouquierQ C Q) (hsym : KLRSymm Q) : CL.CLScalars C k :=
  kkScalars C hsym fun i j h => hQ.unit_coeff i j h

/-- **Brundan's upward relations for Webster's derived action**, with the Kang–Kashiwara scalars
of `Q` (Brundan, arXiv:1501.00350v1, Definition 1.1; Webster, arXiv:1309.3796v3,
Theorem 4.31). -/
theorem blackRouqFamily_brundanUpKLR :
    BrundanUpKLR (blackRouqFamily hP hwf hsym hΛ₀) (rouquierScalars hQ hsym) :=
  (blackRouqFamily_upKLR hP hwf hΛ₀ hsym).of_eq fun _ _ h =>
    eq_brundanQ C hsym _
      (fun i j hij p q hlt => coeff_eq_zero_of_lt_of_hom C (hQ.homogeneous i j hij) p q hlt) h

/-- **Cautis–Lauda's normalized `U_Q(g)` acts on Webster's derived categories** (Brundan,
arXiv:1501.00350v1, Theorem 1.2; Webster, arXiv:1309.3796v3, Theorem 4.31): the presentation
`presCL` with the Kang–Kashiwara scalars of the Rouquier family `Q` acts on the weight spaces of
the derived categories of right `T^λ`-modules, with `E_i`, `F_i` acting by derived restriction
and induction. The hypotheses are those of `blackRouqFamily`; the upward relations
(`blackRouqFamily_brundanUpKLR`) and the mixed inversion are proved. -/
def blackPresCL : Pseudofunctor (RevBicat (CL.presCL RD k (rouquierScalars hQ hsym)).Bicat)
    (LinearCat k) :=
  blackPresCLPseudofunctorOfUpKLR hP hwf hΛ₀ hsym (rouquierScalars hQ hsym)
    (blackRouqFamily_brundanUpKLR hP hwf hΛ₀ hsym) (fun _ => rfl)
    (kkScalars_s_eq_zero C hsym _ hQ.homogeneous)

end

end Categorification.Stendhal

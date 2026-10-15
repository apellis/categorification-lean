import Categorification.KLR.CyclotomicMixedInversionDescent

/-!
# Consumers of the actual cyclotomic mixed bimodule descent

Both ordered colours, nonempty and empty lower weights, both inverse identities,
and both outer coefficient actions (including their inverses). These are not a
functor-level mate identification or a `BrundanMixedInversion` witness.
-/
noncomputable section
namespace Categorification.TwoRep.CyclotomicMixedDescentExamples
open KLR KLRAlgebra KLRAlgebra.MixedAffine KLRAlgebra.MixedAffine.Lower
open KLRAlgebra.MixedCyclotomic
variable {k : Type*} [CommRing k]
  (Q : Bool → Bool → MvPolynomial (Fin 2) k)
  (a : Bool → Polynomial k)
  (hsym : KLRSymm Q)

example : ({true} : Multiset Bool) ≠ 0 := by simp

def forwardNonempty : QuotientSource Q {true} true false a ≃ₗ[k]
    QuotientCorner Q {true} true false a :=
  quotientTauEquiv Q {true} true false a (by decide) hsym

def reverseNonempty : QuotientSource Q {true} false true a ≃ₗ[k]
    QuotientCorner Q {true} false true a :=
  quotientTauEquiv Q {true} false true a (by decide) hsym

def forwardEmpty : QuotientSource Q 0 true false a ≃ₗ[k] QuotientCorner Q 0 true false a :=
  quotientTauEquiv Q 0 true false a (by decide) hsym

def reverseEmpty : QuotientSource Q 0 false true a ≃ₗ[k] QuotientCorner Q 0 false true a :=
  quotientTauEquiv Q 0 false true a (by decide) hsym

variable (γ : Multiset Bool) (i j : Bool) (hij : i ≠ j)

example (z : QuotientSource Q γ i j a) :
    quotientTauInv Q γ i j a hij hsym (quotientTau Q γ i j a hij hsym z) = z :=
  quotientTauInv_tau Q γ i j a hij hsym z

example (z : QuotientCorner Q γ i j a) :
    quotientTau Q γ i j a hij hsym (quotientTauInv Q γ i j a hij hsym z) = z :=
  quotientTau_tauInv Q γ i j a hij hsym z

example (b : CycKLR k Q a (γ + {j})) (z : QuotientSource Q γ i j a) :
    quotientTau Q γ i j a hij hsym (b • z) =
      quotientCornerLeft Q γ i j a b (quotientTau Q γ i j a hij hsym z) :=
  quotientTau_left Q γ i j a hij hsym b z

example (b : CycKLR k Q a (γ + {i})) (z : QuotientSource Q γ i j a) :
    quotientTau Q γ i j a hij hsym (quotientRightAct Q γ i j a b z) =
      quotientCornerRight Q γ i j a b (quotientTau Q γ i j a hij hsym z) :=
  quotientTau_right Q γ i j a hij hsym b z

example (b : CycKLR k Q a (γ + {j})) (z : QuotientCorner Q γ i j a) :
    quotientTauInv Q γ i j a hij hsym (quotientCornerLeft Q γ i j a b z) =
      b • quotientTauInv Q γ i j a hij hsym z :=
  quotientTauInv_left Q γ i j a hij hsym b z

example (b : CycKLR k Q a (γ + {i})) (z : QuotientCorner Q γ i j a) :
    quotientTauInv Q γ i j a hij hsym (quotientCornerRight Q γ i j a b z) =
      quotientRightAct Q γ i j a b (quotientTauInv Q γ i j a hij hsym z) :=
  quotientTauInv_right Q γ i j a hij hsym b z

example (z : CycKLR k Q a (({false} : Multiset Bool) + {false})) :
    CycKLR.mk k Q a ({false} + {false}) (lastColourProjector {false} false true) * z *
      CycKLR.mk k Q a ({false} + {false}) (oneConcat Q {false} {false}) = 0 :=
  absent_quotient_corner Q a {false} false true (by simp) (by decide) z

example (z : CycKLR k Q a (0 + {true})) :
    CycKLR.mk k Q a (0 + {true}) (lastColourProjector 0 true false) * z *
      CycKLR.mk k Q a (0 + {true}) (oneConcat Q 0 {true}) = 0 :=
  absent_quotient_corner Q a 0 true false (by simp) (by decide) z

end Categorification.TwoRep.CyclotomicMixedDescentExamples

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.CyclotomicRouqCapTrace
import Categorification.WeightedKLR.RedStrands.CyclotomicRedCapTrace

/-!
# The red crossing and the opposite counit

Webster, arXiv:1309.3796v3, §4.5, Theorem 4.25, red cap relation. The opposite counit
`res ⊣ ind` of the cyclotomic action is the Rouquier leftward cap, which acts on the middle
corner tensor by the corner trace (`ConcreteAdjunction.capL_app_tmul`). Along the red
pullback from the cyclotomic parameter `b` to `a`, with `b i = X ^ d * a i`, the upstairs cap
after the last-dot power `d` agrees with the downstairs cap after the cyclotomic projection.
-/

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR KLRAlgebra Polynomial
open Categorification.KLR.KLRAlgebra.AbsentColour
open scoped ModuleCat.Algebra

universe u v w

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (i : I) (γ : Multiset I)
  {a b : I → Polynomial k} (hab : ∀ j, a j ∣ b j)
  (hsym : KLRSymm Q)
  (hQ : ∀ j l : I, j ≠ l → ∃ c : k, IsUnit c ∧ (polyInY (Q j l)).leadingCoeff = C c)
  (ha : ∀ j, (a j).Monic) (hb : ∀ j, (b j).Monic)
  {C₀ : QuantumGroup.CartanDatum I} {W Z : Type*} [AddCommGroup W] [AddCommGroup Z]
  (RD : QuantumGroup.UDot.WeightDatum C₀ W Z) (lower upper : W)
  (hl : ((a i).natDegree : ℤ) = RD.pair (RD.iY i) lower)
  (hu : ((b i).natDegree : ℤ) = RD.pair (RD.iY i) upper)
  (hdeg : ∀ j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))

local notation "Si" => (Singleton.singleton i : Multiset I)

/-- **The red crossing slides past the opposite counit** on middle-corner tensors
(Webster, arXiv:1309.3796v3, §4.5, Theorem 4.25, red cap relation). On the red pullback of
`N`, the upstairs Rouquier leftward cap of `z · y ^ d ⊗ n` equals the downstairs cap of
`π(z) ⊗ n`. -/
theorem redPullback_capL_tmul (d : ℕ) (hi : b i = X ^ d * a i)
    (N : ModuleCat.{max u v w} (CycKLR k Q a (Si + γ)))
    (z : MiddleCyclotomic Q i γ b) (n : N) :
    ((ConcreteAdjunction.loc.{u,v,w} Q i b γ hsym hQ hb RD upper hu hdeg).capL.hom.app
        ((cyclotomicRedPullback.{u,v,w} Q hab (Si + γ)).obj N)).hom
        ((PresentColour.efMiddleEquiv Q i γ b _).symm
          (BalancedTensor.tmul (middleDotPow Q i γ b d z) n)) =
      ((ConcreteAdjunction.loc.{u,v,w} Q i a γ hsym hQ ha RD lower hl hdeg).capL.hom.app N).hom
        ((PresentColour.efMiddleEquiv Q i γ a N).symm
          (BalancedTensor.tmul (middleRedProjection Q i γ hab z) n)) := by
  refine (ConcreteAdjunction.capL_app_tmul Q i b γ hsym hQ hb RD upper hu hdeg
    ((cyclotomicRedPullback.{u,v,w} Q hab (Si + γ)).obj N) _ n).trans ?_
  refine Eq.trans ?_ (ConcreteAdjunction.capL_app_tmul Q i a γ hsym hQ ha RD lower hl hdeg
    N _ n).symm
  rw [← redProjection_oppositeCap Q i γ hab hsym hQ ha hb RD lower upper hl hu hdeg d hi z]
  rfl

end Categorification.Stendhal

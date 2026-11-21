/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.TwoRep.RouqKLRAction

/-!
# Biadjunctions for words in a Rouquier family

For a weight-indexed Rouquier family `S` (Rouquier, arXiv:0812.5023; Webster,
arXiv:1309.3796v2, Theorem 3.17), each generator `E_i` has the right adjoint `F_i` and, given
additive whiskering, the left adjoint `F_i` as well. This file composes these along a weighted
word: the 1-morphism `E_{c_0} ∘ ⋯ ∘ E_{c_{n-1}}` has the 1-morphism
`F_{c_{n-1}} ∘ ⋯ ∘ F_{c_0}` as a right and as a left adjoint. These biadjunctions are the input
for the trace of Webster's Theorem 3.18.

## Main definitions

* `RouqFamily.wcellR`: the reversed word of `F`'s.
* `RouqFamily.wadj`: `wcell ⊣ wcellR`.
* `RouqFamily.wadjL`: `wcellR ⊣ wcell`.
-/

universe u v w u₁

open CategoryTheory Bicategory

noncomputable section

namespace Categorification.TwoRep

open QuantumGroup UDot

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  {I : Type*} {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y}

namespace RouqFamily

variable (S : RouqFamily (B := B) RD) (μ : X)

/-- The reversed word `F_{c_{n-1}} ∘ ⋯ ∘ F_{c_0}` of a valid weighted word, from `μ'` back
to `μ`. -/
def wcellR : (L : List (I × X)) → (μ' : X) → wValid RD μ L μ' → (S.obj μ' ⟶ S.obj μ)
  | [], _, h => eqToHom (congrArg S.obj h).symm
  | (c, _) :: L, _, h => S.F c h.2 ≫ wcellR L _ h.1

/-- The word of `E`'s is left adjoint to the reversed word of `F`'s. -/
def wadj : (L : List (I × X)) → (μ' : X) → (h : wValid RD μ L μ') →
    S.wcell μ L μ' h ⊣ S.wcellR μ L μ' h
  | [], μ', h => by
    change eqToHom (congrArg S.obj h) ⊣ eqToHom (congrArg S.obj h).symm
    subst h
    exact Bicategory.Adjunction.id _
  | (c, ν) :: L, μ', h => (wadj L ν h.1).comp (S.adj c h.2)

variable [AdditiveWhiskering B]

/-- The reversed word of `F`'s is left adjoint to the word of `E`'s. -/
def wadjL : (L : List (I × X)) → (μ' : X) → (h : wValid RD μ L μ') →
    S.wcellR μ L μ' h ⊣ S.wcell μ L μ' h
  | [], μ', h => by
    change eqToHom (congrArg S.obj h).symm ⊣ eqToHom (congrArg S.obj h)
    subst h
    exact Bicategory.Adjunction.id _
  | (c, ν) :: L, μ', h => (S.adjL c h.2).comp (wadjL L ν h.1)

end RouqFamily

end Categorification.TwoRep

end

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackRaising
import Categorification.WeightedKLR.RedStrands.BlackFrobenius
import Categorification.Algebra.Graded.HomForm

/-!
# Graded Hom and black induction on projective classes

Webster, arXiv:1309.3796v2, §4.7, Lemma 4.36. Evaluating a
homogeneous map on the induction generator identifies the Hom form
out of an induced class with the Hom form into raw restriction.
-/

namespace Categorification.Stendhal

open KLR Categorification.Graded

variable {I k : Type*} [DecidableEq I] [Field k] {ℓ : ℕ}
    {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}
    (G : GradingDatum (stendhalQ Q Λ)) (i : I) (ν : Multiset I)
    (C : QuantumGroup.CartanDatum I) (hQ : IsRouquierQ C Q)

local notation "src" => tensorProductGrade G ν
local notation "dst" => tensorProductGrade G ((Singleton.singleton i : Multiset I) + ν)

/-- Frobenius reciprocity for virtual graded projectives in the two
adjacent black weight blocks. -/
theorem homForm_blackInd_blackRes [HasGdim src] [HasGdim dst] (x : K0 src) (y : K0 dst) :
    K0.homForm dst (blackIndK0 G i ν x) y = K0.homForm src x (blackResK0 G i ν C hQ y) := by
  induction y using K0.induction_on with
  | of V =>
    induction x using K0.induction_on with
    | of P =>
      rw [blackIndK0_of,blackResK0_of,K0.homForm_of,K0.homForm_of]
      exact gdim_eq_of_finrank_eq fun d => (homGrade_blackInd_blackRes G i ν P V.toGMod d).finrank_eq
    | zero => simp only [map_zero,AddMonoidHom.zero_apply]
    | add x x' hx hx' => simp only [map_add,AddMonoidHom.add_apply,hx,hx']
    | neg x hx => simp only [map_neg,AddMonoidHom.neg_apply,hx]
  | zero => simp only [map_zero]
  | add y y' hy hy' => simp only [map_add,hy,hy']
  | neg y hy => simp only [map_neg,hy]

end Categorification.Stendhal

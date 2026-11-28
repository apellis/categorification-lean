/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapEFunctor
import Categorification.WeightedKLR.RedStrands.BlackMixedCrossCast
import Categorification.Algebra.InductionAlongResOfEq

/-!
# `K ∘ 𝔈_i ≅ 𝔈_i ∘ K` with `𝔈_i` of `T^{λ⁺}` written by a content equality

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the part for `𝔈_i`. On the `λ⁺` side, appending a black strand to
`T^{λ⁺}_{ν + ν₀}` lands at the content `{i} + (ν + ν₀)`, and the cap bimodule at `{i} + ν` has
right content `({i} + ν) + ν₀`. Restriction along `appendBlackTPAOp` is `blackEOfEq` for the
equality `plusWeight_assoc` (`CupCap.appendBlackTPAOp_eq_ofEq`), so the natural isomorphism
`CupCap.capEOrdIso` takes the form `𝔈_i ⋙ K ≅ K ⋙ 𝔈⁺_i` with `𝔈⁺_i = blackEOfEq`
(`CupCap.capEOrdIsoOfEq`, and the cases `CupCap.capEOrdIsoOfEqMid` (`j < ℓ`) and
`CupCap.capEOrdIsoOfEqTop` (`j = ℓ`)).

Route hypotheses (tracked), as for `CupCap.capEEquivMid` and `CupCap.capEEquivTop`: each piece
`L e(t)` finitely generated over `k` (`hfin`), `Q` symmetric (`hQ`), the cup scalars units
(`hκ`) and the pull-off identities (`hP`, `hPL`).
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory KLR KLRAlgebra MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν₀ : Multiset I}
  {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  {ν : Multiset I} {i : I}

local notation "TA" => TensorProductAlgebra k Q Λ ν
local notation "TAᵢ" => TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν)
local notation "TPp" => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
local notation "TPpᵢ" =>
  TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (((Singleton.singleton i : Multiset I) + ν) + ν₀)
local notation "CB" => CapBimodule k Q Λ Λc j hj ν ν₀ L
local notation "CBᵢ" => CapBimodule k Q Λ Λc j hj ((Singleton.singleton i : Multiset I) + ν) ν₀ L
local notation "OrdK" => ordTensor TPpᵐᵒᵖ TAᵐᵒᵖ (OpBimodule TA CB)
local notation "OrdKᵢ" => ordTensor TPpᵢᵐᵒᵖ TAᵢᵐᵒᵖ (OpBimodule TAᵢ CBᵢ)
local notation "Eᵖ" => blackEOfEq Q (plusLabels Λ Λc j hj) i (plusWeight_assoc ν ν₀ i)

variable (k Q Λ Λc j hj ν ν₀ i) in
/-- Appending a black strand in `T^{λ⁺}` followed by the cast to `({i} + ν) + ν₀` is
`appendBlackOpOfEq` for `plusWeight_assoc`. -/
theorem appendBlackTPAOp_eq_ofEq (b : TPpᵐᵒᵖ) :
    appendBlackTPAOp k Q Λ Λc j hj ν ν₀ i b =
      appendBlackOpOfEq Q (plusLabels Λ Λc j hj) i (plusWeight_assoc ν ν₀ i) b :=
  (castOp_op (plusLabels Λ Λc j hj) (plusWeight_assoc ν ν₀ i)
    (appendBlack Q (plusLabels Λ Λc j hj) i (ν + ν₀) (unop b))).symm

/-- **`K ∘ 𝔈_i ≅ 𝔈_i ∘ K` on right modules** (Webster, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the part for `𝔈_i`), with `𝔈_i` on `T^{λ⁺}` given by `blackEOfEq` along
`plusWeight_assoc`: `c ⊗ m ↦ ι(c) ⊗ m`. -/
def capEOrdIsoOfEq (D : CapAppendData k Q Λ Λc j hj ν₀ L ν i) :
    blackE Q Λ i ν ⋙ OrdK ≅ OrdKᵢ ⋙ Eᵖ :=
  capEOrdIso D ≪≫ Functor.isoWhiskerLeft OrdKᵢ
    (resFunctorIsoOfEq.{0, 0} (appendBlackTPAOp_eq_ofEq k Q Λ Λc j hj ν₀ ν i))

theorem capEOrdIsoOfEq_hom_tmul (D : CapAppendData k Q Λ Λc j hj ν₀ L ν i)
    (X : ModuleCat.{0} (TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν))ᵐᵒᵖ)
    (c : CB) (m : Res (appendBlackOp Q Λ i ν) X) :
    Res.val (((capEOrdIsoOfEq D).hom.app X).hom
        (DG.TensorProductOver.tmul (M := InDegreeZero (OpBimodule TA CB))
          (N := InDegreeZero ((blackE Q Λ i ν).obj X)) TAᵐᵒᵖ c m)) =
      DG.TensorProductOver.tmul (M := InDegreeZero (OpBimodule TAᵢ CBᵢ)) (N := InDegreeZero X)
        TAᵢᵐᵒᵖ (D.iota c) m.val :=
  rfl

section Cases

variable (ν i) {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}
  [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
  (hR' : MidKLRRel j hj Q Λ Λc ((Singleton.singleton i : Multiset I) + ν) ν₀ L hL)
  (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
  (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i')) (hQ : KLRSymm Q)
  (hfin : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Finite k
    (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht))))

/-- **`K ∘ 𝔈_i ≅ 𝔈_i ∘ K` for `j < ℓ`**, with `𝔈_i` on `T^{λ⁺}` given by `blackEOfEq` (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21). Route hypotheses (tracked): `hfin`, `hQ`,
`hκ`, `hP`, `hPL`. -/
def capEOrdIsoOfEqMid (h : j < ℓ) : blackE Q Λ i ν ⋙ OrdK ≅ OrdKᵢ ⋙ Eᵖ :=
  capEOrdIsoOfEq (capAppendDataMid ν i hR hR' hP hPL hκ hQ hfin h)

/-- **`K ∘ 𝔈_i ≅ 𝔈_i ∘ K` for `j = ℓ`**, with `𝔈_i` on `T^{λ⁺}` given by `blackEOfEq` (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21). Route hypotheses (tracked): `hfin`, `hQ`,
`hκ`, `hP`, `hPL`. -/
def capEOrdIsoOfEqTop (h : ¬ j < ℓ) : blackE Q Λ i ν ⋙ OrdK ≅ OrdKᵢ ⋙ Eᵖ :=
  capEOrdIsoOfEq (capAppendDataTop ν i hR hR' hP hPL hκ hQ hfin h)

end Cases

end Categorification.Stendhal.CupCap

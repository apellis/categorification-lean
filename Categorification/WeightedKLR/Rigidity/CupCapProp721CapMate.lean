/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapFDotCap

/-!
# `K ∘ 𝔉_i ≅ 𝔉_i ∘ K` is the mate of `K ∘ 𝔈_i ≅ 𝔈_i ∘ K` on right modules

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21: the compatibility of the two commutation isomorphisms with the units and
counits of `𝔉_i ⊣ 𝔈_i` (induction left adjoint to restriction along appending a black strand), at
the level of module categories. The isomorphism `K ∘ 𝔈_i ≅ 𝔈_i ∘ K` (`CupCap.capEOrdIso`,
`c ⊗ m ↦ ι(c) ⊗ m`) is the mate of the inverse of `K ∘ 𝔉_i ≅ 𝔉_i ∘ K` (`CupCap.capFOrdIso`)
along `𝔉_i ⊣ 𝔈_i` on the two sides (`CupCap.capFOrdIso_inv_mate`), as soon as the inverse
`Φ : 𝔉_i(K_ν) ≅ e' K_{{i} + ν}` of the data of `CupCap.CapFData` sends `1 ⊗ c` to `ι(c)`.
For the two positions of the cap this holds by `CupCap.capFImageEquivMid_unitGen` and
`CupCap.capFImageEquivTop_unitGen` (`CupCap.capFOrdIsoMid_inv_mate`,
`CupCap.capFOrdIsoTop_inv_mate`).

Equivalently, the isomorphisms carry the units and counits of `𝔉_i ⊣ 𝔈_i` on the two sides to
each other (`CupCap.capOrdIso_unit`, `CupCap.capOrdIso_counit`).

Route hypotheses (tracked), as for `CupCap.capAppendDataMid` and `CupCap.capFDataMid`: `hL`,
`hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hR`, `hR'`.

## Main results

* `CupCap.capFOrdIso_inv_mate`: the mate of `(capFOrdIso D').inv` is `(capEOrdIso D).hom`.
* `CupCap.capOrdIso_unit`, `CupCap.capOrdIso_counit`: compatibility with unit and counit.
* `CupCap.capFOrdIsoMid_inv_mate`, `CupCap.capFOrdIsoTop_inv_mate`: the two cases.
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

set_option hygiene false in
local notation "TA" => TensorProductAlgebra k Q Λ ν
set_option hygiene false in
local notation "TAᵢ" => TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν)
set_option hygiene false in
local notation "TPp" => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
set_option hygiene false in
local notation "TPpᵢ" =>
  TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (((Singleton.singleton i : Multiset I) + ν) + ν₀)
set_option hygiene false in
local notation "CB" => CapBimodule k Q Λ Λc j hj ν ν₀ L
set_option hygiene false in
local notation "CBᵢ" => CapBimodule k Q Λ Λc j hj ((Singleton.singleton i : Multiset I) + ν) ν₀ L
set_option hygiene false in
local notation "aT" => appendBlackTPAOp k Q Λ Λc j hj ν ν₀ i
set_option hygiene false in
local notation "OrdK" => ordTensor TPpᵐᵒᵖ TAᵐᵒᵖ (OpBimodule TA CB)
set_option hygiene false in
local notation "OrdKᵢ" => ordTensor TPpᵢᵐᵒᵖ TAᵢᵐᵒᵖ (OpBimodule TAᵢ CBᵢ)

section Generic

variable (D : CapAppendData k Q Λ Λc j hj ν₀ L ν i) (D' : CapFData k Q Λ Λc j hj ν₀ L ν i)

/-- **The mate of `K ∘ 𝔉_i ≅ 𝔉_i ∘ K` is `K ∘ 𝔈_i ≅ 𝔈_i ∘ K`** (Webster, arXiv:1309.3796v3, §7.3,
proof of Proposition 7.21), on right modules: along `𝔉_i ⊣ 𝔈_i` on both sides, the mate of
`(capFOrdIso D').inv : K ⋙ 𝔉_i ⟶ 𝔉_i ⋙ K` is `(capEOrdIso D).hom : 𝔈_i ⋙ K ⟶ K ⋙ 𝔈_i`, provided
`D'.bwd (1 ⊗ c) = D.iota c`. -/
theorem capFOrdIso_inv_mate (hD : ∀ c : CB, D'.bwd (Ind.tmul (unitGen aT) c) = D.iota c) :
    (mateEquiv (blackAdjunction.{0} Q Λ i ν) (InductionAlong.adjunction.{0, 0} aT)
      (TwoSquare.mk _ _ _ _ (capFOrdIso D').inv)).natTrans = (capEOrdIso D).hom := by
  ext X : 2
  refine ModuleCat.hom_ext (LinearMap.toAddMonoidHom_injective
    (DG.TensorProductOver.addHom_ext fun c m => ?_))
  apply InductionAlong.Res.ext
  have hm := InductionAlong.Res.prop (φ := appendBlackOp Q Λ i ν) (M := X) m
  refine Eq.trans ?_ (congrArg (fun x : X => DG.TensorProductOver.tmul
    (M := InDegreeZero (OpBimodule TAᵢ CBᵢ)) (N := InDegreeZero X) TAᵢᵐᵒᵖ (D.iota c) x) hm)
  refine Eq.trans ?_ (congrArg (fun y : CBᵢ => DG.TensorProductOver.tmul
    (M := InDegreeZero (OpBimodule TAᵢ CBᵢ)) (N := InDegreeZero X) TAᵢᵐᵒᵖ y
      (appendBlackOp Q Λ i ν 1 • InductionAlong.Res.val m)) (hD c))
  rfl

variable {D D'} in
/-- **`K ∘ 𝔈_i ≅ 𝔈_i ∘ K` and `K ∘ 𝔉_i ≅ 𝔉_i ∘ K` carry unit to unit** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21): for a right `T^λ_ν`-module `M`,
`K(η_M)` followed by `K ∘ 𝔈_i ≅ 𝔈_i ∘ K` at `𝔉_i M` is the unit at `K M` followed by `𝔈_i` of
the inverse of `K ∘ 𝔉_i ≅ 𝔉_i ∘ K`. -/
theorem capOrdIso_unit (hD : ∀ c : CB, D'.bwd (Ind.tmul (unitGen aT) c) = D.iota c)
    (M : ModuleCat.{0} TAᵐᵒᵖ) :
    (OrdK).map ((blackAdjunction.{0} Q Λ i ν).unit.app M) ≫
        (capEOrdIso D).hom.app ((blackF Q Λ i ν).obj M) =
      (InductionAlong.adjunction.{0, 0} aT).unit.app ((OrdK).obj M) ≫
        (resFunctor.{0, 0} aT).map ((capFOrdIso D').inv.app M) := by
  rw [← capFOrdIso_inv_mate D D' hD]
  exact unit_mateEquiv _ _ _ M

variable {D D'} in
/-- **`K ∘ 𝔈_i ≅ 𝔈_i ∘ K` and `K ∘ 𝔉_i ≅ 𝔉_i ∘ K` carry counit to counit** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21): for a right `T^λ_{{i} + ν}`-module `N`,
`𝔉_i` of `K ∘ 𝔈_i ≅ 𝔈_i ∘ K` at `N` followed by the counit at `K N` is the inverse of
`K ∘ 𝔉_i ≅ 𝔉_i ∘ K` at `𝔈_i N` followed by `K(ε_N)`. -/
theorem capOrdIso_counit (hD : ∀ c : CB, D'.bwd (Ind.tmul (unitGen aT) c) = D.iota c)
    (N : ModuleCat.{0} TAᵢᵐᵒᵖ) :
    (InductionAlong.functor.{0, 0} aT).map ((capEOrdIso D).hom.app N) ≫
        (InductionAlong.adjunction.{0, 0} aT).counit.app ((OrdKᵢ).obj N) =
      (capFOrdIso D').inv.app ((blackE Q Λ i ν).obj N) ≫
        (OrdKᵢ).map ((blackAdjunction.{0} Q Λ i ν).counit.app N) := by
  rw [← capFOrdIso_inv_mate D D' hD]
  exact mateEquiv_counit _ _ _ N

end Generic

/-! ### The two positions of the cap -/

section Cases

variable {k' : Type} [Field k'] {Q' : I → I → MvPolynomial (Fin 2) k'}
  {L' : Type} [AddCommGroup L'] [Module (StendhalAlgebra k' Q' Λc ν₀)ᵐᵒᵖ L']
  [Module k' L'] [IsScalarTower k' (StendhalAlgebra k' Q' Λc ν₀)ᵐᵒᵖ L']
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L'), ¬ IsCapGood ν₀ w →
    op (cupMap k' Q' Λc ν₀ (KLRAlgebra.e w)) • v = 0}
  (hR : MidKLRRel j hj Q' Λ Λc ν ν₀ L' hL)
  (hR' : MidKLRRel j hj Q' Λ Λc ((Singleton.singleton i : Multiset I) + ν) ν₀ L' hL)
  (hP : PullOff k' Q' Λc ν₀ L') (hPL : PullOffLeft k' Q' Λc ν₀ L')
  (hκ : ∀ i', IsUnit (cupScalar Q' ν₀ i')) (hQ : KLRSymm Q')
  (hfin : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Finite k'
    (BalancedTensor.idemPart k' L' (op (StendhalAlgebra.e (k := k') (Q := Q') (Λ := Λc) t ht))))

/-- **The mate of `K ∘ 𝔉_i ≅ 𝔉_i ∘ K` is `K ∘ 𝔈_i ≅ 𝔈_i ∘ K`, for `j < ℓ`** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), on right modules.
Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hR`, `hR'`. -/
theorem capFOrdIsoMid_inv_mate (h : j < ℓ) :
    (mateEquiv (blackAdjunction.{0} Q' Λ i ν)
      (InductionAlong.adjunction.{0, 0} (appendBlackTPAOp k' Q' Λ Λc j hj ν ν₀ i))
      (TwoSquare.mk _ _ _ _ (capFOrdIsoMid hR hR' hP hPL hκ h).inv)).natTrans =
      (capEOrdIsoMid ν i hR hR' hP hPL hκ hQ hfin h).hom :=
  capFOrdIso_inv_mate _ _ (capFImageEquivMid_unitGen hR hR' hP hPL hκ h)

/-- **The mate of `K ∘ 𝔉_i ≅ 𝔉_i ∘ K` is `K ∘ 𝔈_i ≅ 𝔈_i ∘ K`, for `j = ℓ`** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), on right modules.
Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hR`, `hR'`. -/
theorem capFOrdIsoTop_inv_mate (h : ¬ j < ℓ) :
    (mateEquiv (blackAdjunction.{0} Q' Λ i ν)
      (InductionAlong.adjunction.{0, 0} (appendBlackTPAOp k' Q' Λ Λc j hj ν ν₀ i))
      (TwoSquare.mk _ _ _ _ (capFOrdIsoTop hR hR' hP hPL hκ h).inv)).natTrans =
      (capEOrdIsoTop ν i hR hR' hP hPL hκ hQ hfin h).hom :=
  capFOrdIso_inv_mate _ _ (capFImageEquivTop_unitGen hR hR' hP hPL hκ h)

end Cases

end Categorification.Stendhal.CupCap

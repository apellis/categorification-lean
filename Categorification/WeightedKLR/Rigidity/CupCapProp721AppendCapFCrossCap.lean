/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapFCross
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapFDotCap
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCrossMidCap
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCrossTopCap

/-!
# `K ∘ 𝔉_i² ≅ 𝔉_i² ∘ K` and the crossing, for the two positions of the cap

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the compatibility of `K ∘ 𝔉_i² ≅ 𝔉_i² ∘ K` with the same-colour crossing, for
`j < ℓ` and `j = ℓ`. Since `Φ(1 ⊗ c) = ι(c)` (`CupCap.capFImageEquivMid_unitGen`,
`CupCap.capFImageEquivTop_unitGen`), the map `bwd₂(1 ⊗ bwd₁(1 ⊗ ·))` is `ι₂ ∘ ι₁`, so the
compatibility of `ι₂ ∘ ι₁` with the crossings (`CupCap.capIota_two_appendedCross`,
`CupCap.capTopIota_two_appendedCross`) gives that of `CupCap.capFCompIsoOfEq`
(`CupCap.capFCompIsoOfEqMid_cross`, `CupCap.capFCompIsoOfEqTop_cross`).

Route hypotheses (tracked), as for `CupCap.capFDataMid` and `CupCap.capFDataTop`: `hL`, `hκ`,
`hP`, `hPL`, and `hR`, `hR'`, `hR''` (the KLR relations on the models at `ν`, `{i} + ν` and
`{i} + ({i} + ν)`). The symmetry `hQ` of `Q` enters through the crossings `indCrossOfEq`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory KLR KLRAlgebra MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν ν₀ : Multiset I} {i : I}
  {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}
  (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
  (hR' : MidKLRRel j hj Q Λ Λc ((Singleton.singleton i : Multiset I) + ν) ν₀ L hL)
  (hR'' : MidKLRRel j hj Q Λ Λc
    ((Singleton.singleton i : Multiset I) + ((Singleton.singleton i : Multiset I) + ν)) ν₀ L hL)
  (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
  (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i')) (hQ : KLRSymm Q)

set_option hygiene false in
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
set_option hygiene false in
local notation "νᵢᵢ" =>
  ((Singleton.singleton i : Multiset I) + ((Singleton.singleton i : Multiset I) + ν))
set_option hygiene false in
local notation "TA" => TensorProductAlgebra k Q Λ ν
set_option hygiene false in
local notation "TAᵢᵢ" => TensorProductAlgebra k Q Λ νᵢᵢ
set_option hygiene false in
local notation "TPp" => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
set_option hygiene false in
local notation "TPpᵢᵢ" => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (νᵢᵢ + ν₀)
set_option hygiene false in
local notation "CB" => CapBimodule k Q Λ Λc j hj ν ν₀ L
set_option hygiene false in
local notation "CBᵢᵢ" => CapBimodule k Q Λ Λc j hj νᵢᵢ ν₀ L
set_option hygiene false in
local notation "OrdK" => ordTensor TPpᵐᵒᵖ TAᵐᵒᵖ (OpBimodule TA CB)
set_option hygiene false in
local notation "OrdKᵢᵢ" => ordTensor TPpᵢᵢᵐᵒᵖ TAᵢᵢᵐᵒᵖ (OpBimodule TAᵢᵢ CBᵢᵢ)
set_option hygiene false in
local notation "aT₁" => appendBlackTPAOp k Q Λ Λc j hj ν ν₀ i
set_option hygiene false in
local notation "aT₂" => appendBlackTPAOp k Q Λ Λc j hj νᵢ ν₀ i

/-- **`K ∘ 𝔉_i² ≅ 𝔉_i² ∘ K` carries the crossing to the crossing, for `j < ℓ`** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21): `(K ∘ τ) ≫ φ = φ ≫ (τ ∘ K)` for
`φ = CupCap.capFCompIsoOfEq` of `CupCap.capFDataMid` at `ν` and at `{i} + ν`, with `τ` the
crossings `indCrossOfEq`. Route hypotheses (tracked): `hL`, `hκ`, `hP`, `hPL`, `hR`, `hR'`,
`hR''`. -/
theorem capFCompIsoOfEqMid_cross (h : j < ℓ) :
    (Functor.whiskerRight (indCrossOfEq Λ hQ i i rfl rfl rfl rfl) OrdKᵢᵢ :
        (blackF Q Λ i ν ⋙ blackF Q Λ i νᵢ) ⋙ OrdKᵢᵢ ⟶
          (blackF Q Λ i ν ⋙ blackF Q Λ i νᵢ) ⋙ OrdKᵢᵢ) ≫
        (capFCompIsoOfEq (capFDataMid hR hR' hP hPL hκ h)
          (capFDataMid hR' hR'' hP hPL hκ h)).hom =
      (capFCompIsoOfEq (capFDataMid hR hR' hP hPL hκ h)
          (capFDataMid hR' hR'' hP hPL hκ h)).hom ≫ Functor.whiskerLeft OrdK
        (indCrossOfEq (plusLabels Λ Λc j hj) hQ i i (plusWeight_assoc ν ν₀ i)
          (plusWeight_assoc νᵢ ν₀ i) (plusWeight_assoc ν ν₀ i) (plusWeight_assoc νᵢ ν₀ i)) :=
  capFCompIsoOfEq_cross hQ _ _ fun c => by
    change appendedCross Q Λ i ν • (capFImageEquivMid hR' hR'' hP hPL hκ h (Ind.tmul
        (unitGen aT₂) (capFImageEquivMid hR hR' hP hPL hκ h (Ind.tmul (unitGen aT₁) c) :
          CapBimodule k Q Λ Λc j hj νᵢ ν₀ L)) : CBᵢᵢ) =
      _ • (capFImageEquivMid hR' hR'' hP hPL hκ h (Ind.tmul (unitGen aT₂)
        (capFImageEquivMid hR hR' hP hPL hκ h (Ind.tmul (unitGen aT₁) c) :
          CapBimodule k Q Λ Λc j hj νᵢ ν₀ L)) : CBᵢᵢ)
    rw [capFImageEquivMid_unitGen, capFImageEquivMid_unitGen]
    exact capIota_two_appendedCross ν i hR hR' hR'' hP hPL hκ h c

/-- **`K ∘ 𝔉_i² ≅ 𝔉_i² ∘ K` carries the crossing to the crossing, for `j = ℓ`** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21). Route hypotheses (tracked): `hL`, `hκ`,
`hP`, `hPL`, `hR`, `hR'`, `hR''`. -/
theorem capFCompIsoOfEqTop_cross (h : ¬ j < ℓ) :
    (Functor.whiskerRight (indCrossOfEq Λ hQ i i rfl rfl rfl rfl) OrdKᵢᵢ :
        (blackF Q Λ i ν ⋙ blackF Q Λ i νᵢ) ⋙ OrdKᵢᵢ ⟶
          (blackF Q Λ i ν ⋙ blackF Q Λ i νᵢ) ⋙ OrdKᵢᵢ) ≫
        (capFCompIsoOfEq (capFDataTop hR hR' hP hPL hκ h)
          (capFDataTop hR' hR'' hP hPL hκ h)).hom =
      (capFCompIsoOfEq (capFDataTop hR hR' hP hPL hκ h)
          (capFDataTop hR' hR'' hP hPL hκ h)).hom ≫ Functor.whiskerLeft OrdK
        (indCrossOfEq (plusLabels Λ Λc j hj) hQ i i (plusWeight_assoc ν ν₀ i)
          (plusWeight_assoc νᵢ ν₀ i) (plusWeight_assoc ν ν₀ i) (plusWeight_assoc νᵢ ν₀ i)) :=
  capFCompIsoOfEq_cross hQ _ _ fun c => by
    change appendedCross Q Λ i ν • (capFImageEquivTop hR' hR'' hP hPL hκ h (Ind.tmul
        (unitGen aT₂) (capFImageEquivTop hR hR' hP hPL hκ h (Ind.tmul (unitGen aT₁) c) :
          CapBimodule k Q Λ Λc j hj νᵢ ν₀ L)) : CBᵢᵢ) =
      _ • (capFImageEquivTop hR' hR'' hP hPL hκ h (Ind.tmul (unitGen aT₂)
        (capFImageEquivTop hR hR' hP hPL hκ h (Ind.tmul (unitGen aT₁) c) :
          CapBimodule k Q Λ Λc j hj νᵢ ν₀ L)) : CBᵢᵢ)
    rw [capFImageEquivTop_unitGen, capFImageEquivTop_unitGen]
    exact capTopIota_two_appendedCross ν i hR hR' hR'' hP hPL hκ h c

end Categorification.Stendhal.CupCap

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapFDot
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendDotMidCap
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendDotTop

/-!
# `K ∘ 𝔉_i ≅ 𝔉_i ∘ K` and the dot, for the two positions of the cap

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the compatibility of `K ∘ 𝔉_i ≅ 𝔉_i ∘ K` with the dot. The isomorphism
`Φ : 𝔉_i(K_ν) ≅ e' K_{{i} + ν}` of `CupCap.capFDataMid` (`j < ℓ`) and `CupCap.capFDataTop`
(`j = ℓ`) sends a generator `1 ⊗ c` to `ι(c)`, the map of the part for `𝔈_i`
(`CupCap.capFImageEquivMid_unitGen`, `CupCap.capFImageEquivTop_unitGen`, traced through the
model). So the compatibility of `ι` with the dots (`CupCap.capIota_appendedDot`,
`CupCap.capTopIota_appendedDot`) gives that of `CupCap.capFOrdIsoOfEq` with the dots on `𝔉_i`
and `𝔉⁺_i` (`CupCap.capFOrdIsoOfEqMid_dot`, `CupCap.capFOrdIsoOfEqTop_dot`).

Route hypotheses (tracked), as for `CupCap.capFDataMid` and `CupCap.capFDataTop`: `hL` (violated
idempotents act by zero on `L`), `hκ` (the cup scalars are units), `hP`, `hPL` (the pull-off
identities), and `hR`, `hR'` (the KLR relations on the model).

## Main results

* `CupCap.capFImageEquivMid_unitGen`, `CupCap.capFImageEquivTop_unitGen`.
* `CupCap.capFOrdIsoOfEqMid_dot`, `CupCap.capFOrdIsoOfEqTop_dot`.
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
  (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
  (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i'))

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
local notation "aBp" => appendBlackPlusOp Q Λ Λc j hj ν ν₀ i
set_option hygiene false in
local notation "OrdK" => ordTensor TPpᵐᵒᵖ TAᵐᵒᵖ (OpBimodule TA CB)
set_option hygiene false in
local notation "OrdKᵢ" => ordTensor TPpᵢᵐᵒᵖ TAᵢᵐᵒᵖ (OpBimodule TAᵢ CBᵢ)

/-- The inverse of `CupCap.capIndQuotEquiv` on a generator `1 ⊗ c` is the class of `1 ⊗ c`. -/
theorem capIndQuotEquiv_symm_unitGen (c : CB) :
    (capIndQuotEquiv (L := L) (hj := hj) (i := i)).symm (Ind.tmul (unitGen aT) c) =
      Submodule.Quotient.mk (Ind.tmul (unitGen aBp) c) := by
  change Submodule.Quotient.mk
    (Ind.tmul (quotLiftCorner (φ := aBp) plusQuotOp_surjective (unitGen aT)) c) = _
  have h1 := map_quotLiftCorner (φ := aBp) plusQuotOp_surjective appendBlackTPAOp_plusQuotOp
    (unitGen aT)
  have h2 : plusQuotOp k Q Λ Λc j hj ((Singleton.singleton i : Multiset I) + ν) ν₀ (aBp 1) =
      aT 1 :=
    (appendBlackTPAOp_plusQuotOp (1 : (StendhalAlgebra k Q (plusLabels Λ Λc j hj)
      (ν + ν₀))ᵐᵒᵖ)).symm.trans (congrArg aT (map_one _))
  exact mk_tmul_eq (z' := unitGen aBp) (h1.trans h2.symm) c

/-- **`Φ(1 ⊗ c) = ι(c)`**, for `j < ℓ`: the isomorphism `𝔉_i(K_ν) ≅ e' K_{{i} + ν}` sends a
generator to the map `ι` of the part for `𝔈_i`. -/
theorem capFImageEquivMid_unitGen (h : j < ℓ) (c : CB) :
    (capFImageEquivMid hR hR' hP hPL hκ h (Ind.tmul (unitGen aT) c) : CBᵢ) =
      capIota ν i hR hR' hP hPL hκ h c := by
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (capModelRightEquiv hR hP hPL hκ c)
  rw [capFImageEquivMid_coe, capFModelHom_apply, capIndQuotEquiv_symm_unitGen,
    capIndModelEquiv_mk_tmul hR hP hPL hκ _ c y hy.symm]
  apply (capModelRightEquiv hR' hP hPL hκ).injective
  rw [capFPsiMid_mk, capModelRightEquiv_capIota ν i hR hR' hP hPL hκ h c y hy.symm]
  rfl

/-- **`Φ(1 ⊗ c) = ι(c)`**, for `j = ℓ`. -/
theorem capFImageEquivTop_unitGen (h : ¬ j < ℓ) (c : CB) :
    (capFImageEquivTop hR hR' hP hPL hκ h (Ind.tmul (unitGen aT) c) : CBᵢ) =
      capTopIota ν i hR hR' hP hPL hκ h c := by
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (capModelRightEquiv hR hP hPL hκ c)
  rw [capFImageEquivTop_coe, capFModelHom_apply, capIndQuotEquiv_symm_unitGen,
    capIndModelEquiv_mk_tmul hR hP hPL hκ _ c y hy.symm]
  apply (capModelRightEquiv hR' hP hPL hκ).injective
  rw [capFPsiTop_mk, capModelRightEquiv_capTopIota ν i hR hR' hP hPL hκ h c y hy.symm]
  rfl

/-- **`K ∘ 𝔉_i ≅ 𝔉_i ∘ K` carries the dot to the dot, for `j < ℓ`** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21): `(K ∘ x) ≫ φ = φ ≫ (x ∘ K)` for
`φ = CupCap.capFOrdIsoOfEq (CupCap.capFDataMid …)`, with `x` the dots `indDotOfEq` on `𝔉_i` and
`𝔉⁺_i`. Route hypotheses (tracked): `hL`, `hκ`, `hP`, `hPL`, `hR`, `hR'`. -/
theorem capFOrdIsoOfEqMid_dot (h : j < ℓ) :
    (Functor.whiskerRight (indDotOfEq Q Λ i (rfl : ({i} : Multiset I) + ν = _)) OrdKᵢ :
        blackF Q Λ i ν ⋙ OrdKᵢ ⟶ blackF Q Λ i ν ⋙ OrdKᵢ) ≫
        (capFOrdIsoOfEq (capFDataMid hR hR' hP hPL hκ h)).hom =
      (capFOrdIsoOfEq (capFDataMid hR hR' hP hPL hκ h)).hom ≫ Functor.whiskerLeft OrdK
        (indDotOfEq Q (plusLabels Λ Λc j hj) i (plusWeight_assoc ν ν₀ i)) :=
  capFOrdIsoOfEq_dot _ fun c => by
    change appendedDot Q Λ i ν •
        (capFImageEquivMid hR hR' hP hPL hκ h (Ind.tmul (unitGen aT) c) : CBᵢ) =
      _ • (capFImageEquivMid hR hR' hP hPL hκ h (Ind.tmul (unitGen aT) c) : CBᵢ)
    rw [capFImageEquivMid_unitGen]
    exact capIota_appendedDot ν i hR hR' hP hPL hκ h c

/-- **`K ∘ 𝔉_i ≅ 𝔉_i ∘ K` carries the dot to the dot, for `j = ℓ`** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21). Route hypotheses (tracked): `hL`, `hκ`,
`hP`, `hPL`, `hR`, `hR'`. -/
theorem capFOrdIsoOfEqTop_dot (h : ¬ j < ℓ) :
    (Functor.whiskerRight (indDotOfEq Q Λ i (rfl : ({i} : Multiset I) + ν = _)) OrdKᵢ :
        blackF Q Λ i ν ⋙ OrdKᵢ ⟶ blackF Q Λ i ν ⋙ OrdKᵢ) ≫
        (capFOrdIsoOfEq (capFDataTop hR hR' hP hPL hκ h)).hom =
      (capFOrdIsoOfEq (capFDataTop hR hR' hP hPL hκ h)).hom ≫ Functor.whiskerLeft OrdK
        (indDotOfEq Q (plusLabels Λ Λc j hj) i (plusWeight_assoc ν ν₀ i)) :=
  capFOrdIsoOfEq_dot _ fun c => by
    change appendedDot Q Λ i ν •
        (capFImageEquivTop hR hR' hP hPL hκ h (Ind.tmul (unitGen aT) c) : CBᵢ) =
      _ • (capFImageEquivTop hR hR' hP hPL hκ h (Ind.tmul (unitGen aT) c) : CBᵢ)
    rw [capFImageEquivTop_unitGen]
    exact capTopIota_appendedDot ν i hR hR' hP hPL hκ h c

end Categorification.Stendhal.CupCap

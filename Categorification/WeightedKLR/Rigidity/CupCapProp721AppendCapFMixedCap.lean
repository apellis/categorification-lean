/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapFMixed
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapFDotCap
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendMixedCap
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendMixedTopCap

/-!
# `K ∘ 𝔉_a 𝔉_b ≅ 𝔉_a 𝔉_b ∘ K` and the mixed crossing, for the two positions of the cap

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the compatibility of `K ∘ 𝔉 ≅ 𝔉 ∘ K` with the crossing of two strands of
different colours `a ≠ b`, for `j < ℓ` and `j = ℓ`. Since `Φ(1 ⊗ c) = ι(c)`
(`CupCap.capFImageEquivMid_unitGen`, `CupCap.capFImageEquivTop_unitGen`), the hypothesis of
`CupCap.capFCompIsoOfEq'_mixedCross` is the intertwining of the two orders of `ι ∘ ι` by the
mixed crossings (`CupCap.capIota_two_mixedCross`, `CupCap.capTopIota_two_mixedCross`), giving
`CupCap.capFCompIsoOfEq'Mid_mixedCross` and `CupCap.capFCompIsoOfEq'Top_mixedCross`.

Route hypotheses (tracked), as for `CupCap.capFDataMid` and `CupCap.capFDataTop`: `hL`, `hκ`,
`hP`, `hPL`, and the KLR relations on the models at `ν`, `{a} + ν`, `{b} + ν`,
`{a} + ({b} + ν)` and `{b} + ({a} + ν)` (`hR`, `hRa`, `hRb`, `hRab`, `hRba`). The symmetry
`hQ` of `Q` enters through the crossings `indCrossOfEq`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory KLR KLRAlgebra MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν₀ : Multiset I}
  {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}
  (ν : Multiset I) (a b : I)
  (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
  (hRa : MidKLRRel j hj Q Λ Λc ((Singleton.singleton a : Multiset I) + ν) ν₀ L hL)
  (hRb : MidKLRRel j hj Q Λ Λc ((Singleton.singleton b : Multiset I) + ν) ν₀ L hL)
  (hRab : MidKLRRel j hj Q Λ Λc
    ((Singleton.singleton a : Multiset I) + ((Singleton.singleton b : Multiset I) + ν)) ν₀ L hL)
  (hRba : MidKLRRel j hj Q Λ Λc
    ((Singleton.singleton b : Multiset I) + ((Singleton.singleton a : Multiset I) + ν)) ν₀ L hL)
  (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
  (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i')) (hQ : KLRSymm Q)

local notation "νa" => ((Singleton.singleton a : Multiset I) + ν)
local notation "νb" => ((Singleton.singleton b : Multiset I) + ν)
local notation "νab" =>
  ((Singleton.singleton a : Multiset I) + ((Singleton.singleton b : Multiset I) + ν))
local notation "νba" =>
  ((Singleton.singleton b : Multiset I) + ((Singleton.singleton a : Multiset I) + ν))
local notation "TA" μ:max => TensorProductAlgebra k Q Λ μ
local notation "TPp" μ:max => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (μ + ν₀)
local notation "CB" μ:max => CapBimodule k Q Λ Λc j hj μ ν₀ L
local notation "OrdK" μ:max => ordTensor (TPp μ)ᵐᵒᵖ (TA μ)ᵐᵒᵖ (OpBimodule (TA μ) (CB μ))
local notation "aT" μ:max i:max => appendBlackTPAOp k Q Λ Λc j hj μ ν₀ i

/-- **`K ∘ 𝔉_a 𝔉_b ≅ 𝔉_a 𝔉_b ∘ K` carries the crossing of different colours to the crossing,
for `j < ℓ`** (Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21): for `a ≠ b`,
`(K ∘ τ) ≫ φ' = φ ≫ (τ ∘ K)` for `φ`, `φ'` the isomorphisms `CupCap.capFCompIsoOfEq'` of
`CupCap.capFDataMid` for the two orders of appending, and `τ` the crossings `indCrossOfEq` of
`T^λ` and of `T^{λ⁺}`. Route hypotheses (tracked): `hL`, `hκ`, `hP`, `hPL`, `hR`, `hRa`, `hRb`,
`hRab`, `hRba`. -/
theorem capFCompIsoOfEq'Mid_mixedCross (h : j < ℓ) (hab : a ≠ b) :
    (Functor.whiskerRight (indCrossOfEq Λ hQ a b rfl rfl rfl (mixedSwap ν a b)) (OrdK νab) :
        (blackF Q Λ b ν ⋙ blackFOfEq Q Λ a (rfl : ({a} : Multiset I) + _ = νab)) ⋙ OrdK νab ⟶
          (blackF Q Λ a ν ⋙ blackFOfEq Q Λ b (mixedSwap ν a b)) ⋙ OrdK νab) ≫
        (capFCompIsoOfEq' (capFDataMid hR hRa hP hPL hκ h) (capFDataMid hRa hRba hP hPL hκ h)
          (mixedSwap ν a b) (plusWeight_assoc_mixed_swap ν a b)).hom =
      (capFCompIsoOfEq' (capFDataMid hR hRb hP hPL hκ h) (capFDataMid hRb hRab hP hPL hκ h)
          rfl (plusWeight_assoc νb ν₀ a)).hom ≫
        Functor.whiskerLeft (OrdK ν)
          (indCrossOfEq (plusLabels Λ Λc j hj) hQ a b (plusWeight_assoc ν ν₀ b)
            (plusWeight_assoc νb ν₀ a) (plusWeight_assoc ν ν₀ a)
            (plusWeight_assoc_mixed_swap ν a b)) :=
  capFCompIsoOfEq'_mixedCross hQ hab _ _ _ _ (mixedSwap ν a b) _ _ fun c => by
    change castTensorProductAlgebra Q Λ (mixedSwap ν a b) (mixedCrossElem (Q := Q) Λ ν b a) •
        (capFImageEquivMid hRb hRab hP hPL hκ h (Ind.tmul (unitGen (aT νb a))
          (capFImageEquivMid hR hRb hP hPL hκ h (Ind.tmul (unitGen (aT ν b)) c) : CB νb)) :
          CB νab) =
      _ • (mixedSwap ν a b ▸ (capFImageEquivMid hRa hRba hP hPL hκ h
        (Ind.tmul (unitGen (aT νa b))
          (capFImageEquivMid hR hRa hP hPL hκ h (Ind.tmul (unitGen (aT ν a)) c) : CB νa)) :
          CB νba) : CB νab)
    rw [capFImageEquivMid_unitGen, capFImageEquivMid_unitGen, capFImageEquivMid_unitGen,
      capFImageEquivMid_unitGen]
    exact capIota_two_mixedCross hP hPL hκ ν a b hR hRa hRb hRab hRba h _ c

/-- **`K ∘ 𝔉_a 𝔉_b ≅ 𝔉_a 𝔉_b ∘ K` carries the crossing of different colours to the crossing,
for `j = ℓ`** (Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21). Route hypotheses
(tracked): `hL`, `hκ`, `hP`, `hPL`, `hR`, `hRa`, `hRb`, `hRab`, `hRba`. -/
theorem capFCompIsoOfEq'Top_mixedCross (h : ¬ j < ℓ) (hab : a ≠ b) :
    (Functor.whiskerRight (indCrossOfEq Λ hQ a b rfl rfl rfl (mixedSwap ν a b)) (OrdK νab) :
        (blackF Q Λ b ν ⋙ blackFOfEq Q Λ a (rfl : ({a} : Multiset I) + _ = νab)) ⋙ OrdK νab ⟶
          (blackF Q Λ a ν ⋙ blackFOfEq Q Λ b (mixedSwap ν a b)) ⋙ OrdK νab) ≫
        (capFCompIsoOfEq' (capFDataTop hR hRa hP hPL hκ h) (capFDataTop hRa hRba hP hPL hκ h)
          (mixedSwap ν a b) (plusWeight_assoc_mixed_swap ν a b)).hom =
      (capFCompIsoOfEq' (capFDataTop hR hRb hP hPL hκ h) (capFDataTop hRb hRab hP hPL hκ h)
          rfl (plusWeight_assoc νb ν₀ a)).hom ≫
        Functor.whiskerLeft (OrdK ν)
          (indCrossOfEq (plusLabels Λ Λc j hj) hQ a b (plusWeight_assoc ν ν₀ b)
            (plusWeight_assoc νb ν₀ a) (plusWeight_assoc ν ν₀ a)
            (plusWeight_assoc_mixed_swap ν a b)) :=
  capFCompIsoOfEq'_mixedCross hQ hab _ _ _ _ (mixedSwap ν a b) _ _ fun c => by
    change castTensorProductAlgebra Q Λ (mixedSwap ν a b) (mixedCrossElem (Q := Q) Λ ν b a) •
        (capFImageEquivTop hRb hRab hP hPL hκ h (Ind.tmul (unitGen (aT νb a))
          (capFImageEquivTop hR hRb hP hPL hκ h (Ind.tmul (unitGen (aT ν b)) c) : CB νb)) :
          CB νab) =
      _ • (mixedSwap ν a b ▸ (capFImageEquivTop hRa hRba hP hPL hκ h
        (Ind.tmul (unitGen (aT νa b))
          (capFImageEquivTop hR hRa hP hPL hκ h (Ind.tmul (unitGen (aT ν a)) c) : CB νa)) :
          CB νba) : CB νab)
    rw [capFImageEquivTop_unitGen, capFImageEquivTop_unitGen, capFImageEquivTop_unitGen,
      capFImageEquivTop_unitGen]
    exact capTopIota_two_mixedCross hP hPL hκ ν a b hR hRa hRb hRab hRba h _ c

end Categorification.Stendhal.CupCap

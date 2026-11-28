/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendMixedCap
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendMixedTopModel
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCrossTopCap

/-!
# `K ∘ 𝔈_a 𝔈_b ≅ 𝔈_a 𝔈_b ∘ K` and the mixed crossing, for a cap at the right end

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the compatibility of `K ∘ 𝔈 ≅ 𝔈 ∘ K` with the crossing of two strands of
different colours `a ≠ b`, for `j = ℓ`. The model lemma `CupCap.appendTopIota_two_mixedCross`
gives the intertwining of the maps `ι ∘ ι`, which pass the appended strands under the window, for
the two orders of appending (`CupCap.capTopIota_two_mixedCross`), and
`CupCap.capECompIsoOfEq'_mixedCross` gives the compatibility of the isomorphisms with the crossing
(`CupCap.capECompIsoOfEq'Top_mixedCross`).

Route hypotheses (tracked), as for `CupCap.capEEquivTop`: each piece `L e(t)` finitely
generated over `k` (`hfin`), `Q` symmetric (`hQ`), the cup scalars units (`hκ`) and the pull-off
identities (`hP`, `hPL`).
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Cap

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν₀ : Multiset I}
  {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}
  (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
  (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i'))
  (ν : Multiset I) (a b : I)

local notation "νa" => ((Singleton.singleton a : Multiset I) + ν)
local notation "νb" => ((Singleton.singleton b : Multiset I) + ν)
local notation "νab" =>
  ((Singleton.singleton a : Multiset I) + ((Singleton.singleton b : Multiset I) + ν))

variable (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
  (hRa : MidKLRRel j hj Q Λ Λc ((Singleton.singleton a : Multiset I) + ν) ν₀ L hL)
  (hRb : MidKLRRel j hj Q Λ Λc ((Singleton.singleton b : Multiset I) + ν) ν₀ L hL)
  (hRab : MidKLRRel j hj Q Λ Λc
    ((Singleton.singleton a : Multiset I) + ((Singleton.singleton b : Multiset I) + ν)) ν₀ L hL)
  (hRba : MidKLRRel j hj Q Λ Λc
    ((Singleton.singleton b : Multiset I) + ((Singleton.singleton a : Multiset I) + ν)) ν₀ L hL)

/-- **The two orders of `ι ∘ ι` are intertwined by the mixed crossings**, for `j = ℓ`
(arXiv:1309.3796v3, §7.3, proof of Proposition 7.21): the left action of the mixed crossing of
`T^λ` on `ι_a(ι_b(c))` is the right action of the mixed crossing of `T^{λ⁺}` on `ι_b(ι_a(c))`,
transported to `{a} + ({b} + ν)`. Route hypotheses (tracked): `hκ`, `hP`, `hPL`. -/
theorem capTopIota_two_mixedCross (h : ¬ j < ℓ) (hp : (Singleton.singleton b : Multiset I) +
    ((Singleton.singleton a : Multiset I) + (ν + ν₀)) = νab + ν₀)
    (c : CapBimodule k Q Λ Λc j hj ν ν₀ L) :
    castTensorProductAlgebra Q Λ (mixedSwap ν a b) (mixedCrossElem (Q := Q) Λ ν b a) •
        capTopIota νb a hRb hRab hP hPL hκ h (capTopIota ν b hR hRb hP hPL hκ h c) =
      castOp Q (plusLabels Λ Λc j hj) hp
          (op (mixedCrossElem (Q := Q) (plusLabels Λ Λc j hj) (ν + ν₀) b a)) •
        (mixedSwap ν a b ▸
            capTopIota νa b hRa hRba hP hPL hκ h (capTopIota ν a hR hRa hP hPL hκ h c) :
          CapBimodule k Q Λ Λc j hj νab ν₀ L) := by
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (capModelRightEquiv hR hP hPL hκ c)
  have hι := capModelRightEquiv_capTopIota ν b hR hRb hP hPL hκ h c y hy.symm
  have hι' := capModelRightEquiv_capTopIota νb a hRb hRab hP hPL hκ h _ _ hι
  have hκ₁ := capModelRightEquiv_capTopIota ν a hR hRa hP hPL hκ h c y hy.symm
  have hκ₂ := capModelRightEquiv_capTopIota νa b hRa hRba hP hPL hκ h _ _ hκ₁
  have hκ₃ := capModelRightEquiv_cast hP hPL hκ (mixedSwap ν a b) hRba hRab _ _ hκ₂
  rw [castOp_mixedCrossElem_plus_eq ν a b hp, ← capStendhal_smul,
    castTensorProductAlgebra_mixedCrossElem]
  change capLeftLin (j := j) (hj := hj) (Λc := Λc) (ν₀ := ν₀) L
      (orderProjection Q Λ νab
          (-StendhalAlgebraAllOrders.ψ (Multiset.card (stendhalWeight ℓ ν))) *
        appendBlackStendhal Q Λ a νb (appendBlackStendhal Q Λ b ν 1)) _ = _
  apply (capModelRightEquiv hRab hP hPL hκ).injective
  rw [capModelRightEquiv_capLeftLin hRab hP hPL hκ _ _ _ hι', LinearEquiv.map_smul, hκ₃,
    ← Submodule.Quotient.mk_smul, appendTopIota_two_mixedCross ν a b hP hPL hκ h hR hRb hRab]

end Cap

section Iso

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} (ν : Multiset I) {ν₀ : Multiset I} (a b : I)
  {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}
  [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
  (hRa : MidKLRRel j hj Q Λ Λc ((Singleton.singleton a : Multiset I) + ν) ν₀ L hL)
  (hRb : MidKLRRel j hj Q Λ Λc ((Singleton.singleton b : Multiset I) + ν) ν₀ L hL)
  (hRab : MidKLRRel j hj Q Λ Λc
    ((Singleton.singleton a : Multiset I) + ((Singleton.singleton b : Multiset I) + ν)) ν₀ L hL)
  (hRba : MidKLRRel j hj Q Λ Λc
    ((Singleton.singleton b : Multiset I) + ((Singleton.singleton a : Multiset I) + ν)) ν₀ L hL)
  (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
  (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i')) (hQ : KLRSymm Q)
  (hfin : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Finite k
    (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht))))

local notation "νa" => ((Singleton.singleton a : Multiset I) + ν)
local notation "νb" => ((Singleton.singleton b : Multiset I) + ν)
local notation "νab" =>
  ((Singleton.singleton a : Multiset I) + ((Singleton.singleton b : Multiset I) + ν))
local notation "TA" μ:max => TensorProductAlgebra k Q Λ μ
local notation "TPp" μ:max => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (μ + ν₀)
local notation "CB" μ:max => CapBimodule k Q Λ Λc j hj μ ν₀ L
local notation "OrdK" μ:max => ordTensor (TPp μ)ᵐᵒᵖ (TA μ)ᵐᵒᵖ (OpBimodule (TA μ) (CB μ))

open CategoryTheory in
/-- **`K ∘ 𝔈_a 𝔈_b ≅ 𝔈_a 𝔈_b ∘ K` carries the crossing of different colours to the crossing,
for `j = ℓ`** (Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21): for `a ≠ b`,
`(K ∘ τ) ≫ φ' = φ ≫ (τ ∘ K)` for `φ'`, `φ` the isomorphisms `CupCap.capECompIsoOfEq'` of
`CupCap.capAppendDataTop` for the two orders of appending, and `τ` the crossing
`resCrossOfEq` of `T^λ` and of `T^{λ⁺}`. Route hypotheses (tracked): `hfin`, `hQ`, `hκ`, `hP`,
`hPL`. -/
theorem capECompIsoOfEq'Top_mixedCross (h : ¬ j < ℓ) (hab : a ≠ b) :
    Functor.whiskerRight (resCrossOfEq Λ hQ a b rfl rfl rfl (mixedSwap ν a b)) (OrdK ν) ≫
        (capECompIsoOfEq' (capAppendDataTop ν b hR hRb hP hPL hκ hQ hfin h)
          (capAppendDataTop νb a hRb hRab hP hPL hκ hQ hfin h) rfl
          (plusWeight_assoc νb ν₀ a)).hom =
      (capECompIsoOfEq' (capAppendDataTop ν a hR hRa hP hPL hκ hQ hfin h)
          (capAppendDataTop νa b hRa hRba hP hPL hκ hQ hfin h) (mixedSwap ν a b)
          (plusWeight_assoc_mixed_swap ν a b)).hom ≫
        Functor.whiskerLeft (OrdK νab)
          (resCrossOfEq (plusLabels Λ Λc j hj) hQ a b (plusWeight_assoc ν ν₀ b)
            (plusWeight_assoc νb ν₀ a) (plusWeight_assoc ν ν₀ a)
            (plusWeight_assoc_mixed_swap ν a b)) :=
  capECompIsoOfEq'_mixedCross hQ hab _ _ _ _ rfl (mixedSwap ν a b) _ _
    (capTopIota_two_mixedCross hP hPL hκ ν a b hR hRa hRb hRab hRba h _)

end Iso

end Categorification.Stendhal.CupCap

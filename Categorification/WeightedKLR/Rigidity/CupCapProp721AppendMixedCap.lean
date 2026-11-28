/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendMixedModel

/-!
# `K ∘ 𝔈_a 𝔈_b ≅ 𝔈_a 𝔈_b ∘ K` and the mixed crossing, for a cap left of the right end

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the compatibility of `K ∘ 𝔈 ≅ 𝔈 ∘ K` with the crossing of two strands of
different colours `a ≠ b`, for `j < ℓ`. The mixed crossings of `T^λ` and `T^{λ⁺}`, cut by the
idempotents of the two orders of appending, reduce to the crossing times one idempotent
(`CupCap.castTensorProductAlgebra_mixedCrossElem`, `CupCap.castOp_mixedCrossElem_plus_eq`).
The model lemma `CupCap.appendIota_two_mixedCross` then gives the intertwining of the maps
`ι ∘ ι` for the two orders (`CupCap.capIota_two_mixedCross`), and
`CupCap.capECompIsoOfEq'_mixedCross` gives the compatibility of the isomorphisms with the crossing
(`CupCap.capECompIsoOfEq'Mid_mixedCross`).

Route hypotheses (tracked), as for `CupCap.capEEquivMid`: each piece `L e(t)` finitely
generated over `k` (`hfin`), `Q` symmetric (`hQ`), the cup scalars units (`hκ`) and the pull-off
identities (`hP`, `hPL`).
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Generic

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {n : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ' : Fin n → I →₀ ℕ)

theorem castPlusStendhal_orderProjection_neg_ψ {μ μ' : Multiset I} (h : μ = μ') (p : ℕ) :
    castPlusStendhal Q Λ' h (orderProjection Q Λ' μ (-StendhalAlgebraAllOrders.ψ p)) =
      orderProjection Q Λ' μ' (-StendhalAlgebraAllOrders.ψ p) := by
  subst h; rfl

/-- **The mixed crossing of `T^λ`, cast to `{a} + ({b} + ν)`**, is minus the crossing of the two
appended strands times the idempotent of appending first `b`, then `a`. -/
theorem castTensorProductAlgebra_mixedCrossElem (μ : Multiset I) (a b : I) :
    castTensorProductAlgebra Q Λ' (mixedSwap μ a b) (mixedCrossElem (Q := Q) Λ' μ b a) =
      TensorProductAlgebra.mk Q Λ' _
        (orderProjection Q Λ' _
            (-StendhalAlgebraAllOrders.ψ (Multiset.card (stendhalWeight n μ))) *
          appendBlackStendhal Q Λ' a _ (appendBlackStendhal Q Λ' b μ 1)) := by
  rw [mixedCrossElem_eq_mk, castTensorProductAlgebra_mk_stendhal]
  congr 1
  rw [map_mul, map_mul, castPlusStendhal_trans, castPlusStendhal_orderProjection_neg_ψ]
  have key := orderProjection_ψ_mul_appendTwo (Q := Q) Λ' a b μ 1
  set E := appendBlackStendhal Q Λ' a _ (appendBlackStendhal Q Λ' b μ 1)
  set E' := castPlusStendhal Q Λ' (mixedSwap μ a b)
    (appendBlackStendhal Q Λ' b _ (appendBlackStendhal Q Λ' a μ 1))
  have hE' : E' * E' = E' := by
    rw [← map_mul, ← map_mul, ← map_mul, mul_one]
  change E' * _ * E = _
  set X := orderProjection Q Λ' _
    (StendhalAlgebraAllOrders.ψ (Multiset.card (stendhalWeight n μ)))
  rw [map_neg, mul_neg E' X, neg_mul (E' * X) E, neg_mul X E, mul_assoc, key, ← mul_assoc, hE',
    ← key]

end Generic

section Plus

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} (ν : Multiset I) {ν₀ : Multiset I} (a b : I)

local notation "Λ⁺" => plusLabels Λ Λc j hj
local notation "νab" =>
  ((Singleton.singleton a : Multiset I) + ((Singleton.singleton b : Multiset I) + ν))
local notation "aBb" => appendBlackPlus Q Λ Λc j hj ν ν₀ b
local notation "aBa" => appendBlackPlus Q Λ Λc j hj ((Singleton.singleton b : Multiset I) + ν) ν₀ a
local notation "Y" => mixedLastCross k Q Λ Λc j hj ν ν₀ a b

/-- **The mixed crossing of `T^{λ⁺}`, cast to `({a} + ({b} + ν)) + ν₀`**, is the image of minus
`Y` times the idempotent of appending first `b`, then `a`. -/
theorem castOp_mixedCrossElem_plus_eq (h : (Singleton.singleton b : Multiset I) +
    ((Singleton.singleton a : Multiset I) + (ν + ν₀)) = νab + ν₀) :
    castOp Q Λ⁺ h (op (mixedCrossElem (Q := Q) Λ⁺ (ν + ν₀) b a)) =
      plusQuotOp k Q Λ Λc j hj νab ν₀ (op (-(Y * aBa (aBb 1)))) := by
  rw [castOp_mixedCrossElem_plus ν a b h]
  congr 2
  have key := lastCross_mul_appendBlackPlus_mixed (Q := Q) (Λ := Λ) (Λc := Λc) (j := j)
    (hj := hj) (ν₀ := ν₀) ν a b 1
  set E := aBa (aBb 1)
  set E' := castPlusStendhal Q Λ⁺ (congrArg (· + ν₀) (mixedSwap ν a b))
    (appendBlackPlus Q Λ Λc j hj ((Singleton.singleton a : Multiset I) + ν) ν₀ b
      (appendBlackPlus Q Λ Λc j hj ν ν₀ a 1))
  have hE' : E' * E' = E' := by
    rw [← map_mul, ← map_mul, ← map_mul, mul_one]
  change E' * botMap k Q Λ Λc j hj νab ν₀ (-KLRAlgebra.ψ _) * E = _
  rw [map_neg]
  change E' * -Y * E = -(Y * E)
  rw [mul_neg E' Y, neg_mul (E' * Y) E, mul_assoc, key, ← mul_assoc, hE', ← key]

end Plus

section Cap

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν₀ : Multiset I}
  {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}
  (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
  (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i'))

/-- The model of `K^{λ⁺}_λ` along a content equality. -/
theorem capModelRightEquiv_cast {μ μ' : Multiset I} (h : μ = μ')
    (hR₁ : MidKLRRel j hj Q Λ Λc μ ν₀ L hL) (hR₂ : MidKLRRel j hj Q Λ Λc μ' ν₀ L hL)
    (c : CapBimodule k Q Λ Λc j hj μ ν₀ L) (y : MidModel j hj Q Λ Λc μ ν₀ L)
    (hy : capModelRightEquiv hR₁ hP hPL hκ c = Submodule.Quotient.mk y) :
    capModelRightEquiv hR₂ hP hPL hκ (h ▸ c : CapBimodule k Q Λ Λc j hj μ' ν₀ L) =
      Submodule.Quotient.mk (h ▸ y : MidModel j hj Q Λ Λc μ' ν₀ L) := by
  subst h; exact hy

variable (ν : Multiset I) (a b : I)

local notation "νa" => ((Singleton.singleton a : Multiset I) + ν)
local notation "νb" => ((Singleton.singleton b : Multiset I) + ν)
local notation "νab" =>
  ((Singleton.singleton a : Multiset I) + ((Singleton.singleton b : Multiset I) + ν))
local notation "νba" =>
  ((Singleton.singleton b : Multiset I) + ((Singleton.singleton a : Multiset I) + ν))

variable (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
  (hRa : MidKLRRel j hj Q Λ Λc ((Singleton.singleton a : Multiset I) + ν) ν₀ L hL)
  (hRb : MidKLRRel j hj Q Λ Λc ((Singleton.singleton b : Multiset I) + ν) ν₀ L hL)
  (hRab : MidKLRRel j hj Q Λ Λc
    ((Singleton.singleton a : Multiset I) + ((Singleton.singleton b : Multiset I) + ν)) ν₀ L hL)
  (hRba : MidKLRRel j hj Q Λ Λc
    ((Singleton.singleton b : Multiset I) + ((Singleton.singleton a : Multiset I) + ν)) ν₀ L hL)

/-- **The two orders of `ι ∘ ι` are intertwined by the mixed crossings**, for `j < ℓ`
(arXiv:1309.3796v3, §7.3, proof of Proposition 7.21): the left action of the mixed crossing of
`T^λ` on `ι_a(ι_b(c))` is the right action of the mixed crossing of `T^{λ⁺}` on `ι_b(ι_a(c))`,
transported to `{a} + ({b} + ν)`. Route hypotheses (tracked): `hκ`, `hP`, `hPL`. -/
theorem capIota_two_mixedCross (h : j < ℓ) (hp : (Singleton.singleton b : Multiset I) +
    ((Singleton.singleton a : Multiset I) + (ν + ν₀)) = νab + ν₀)
    (c : CapBimodule k Q Λ Λc j hj ν ν₀ L) :
    castTensorProductAlgebra Q Λ (mixedSwap ν a b) (mixedCrossElem (Q := Q) Λ ν b a) •
        capIota νb a hRb hRab hP hPL hκ h (capIota ν b hR hRb hP hPL hκ h c) =
      castOp Q (plusLabels Λ Λc j hj) hp
          (op (mixedCrossElem (Q := Q) (plusLabels Λ Λc j hj) (ν + ν₀) b a)) •
        (mixedSwap ν a b ▸ capIota νa b hRa hRba hP hPL hκ h (capIota ν a hR hRa hP hPL hκ h c) :
          CapBimodule k Q Λ Λc j hj νab ν₀ L) := by
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (capModelRightEquiv hR hP hPL hκ c)
  have hι := capModelRightEquiv_capIota ν b hR hRb hP hPL hκ h c y hy.symm
  have hι' := capModelRightEquiv_capIota νb a hRb hRab hP hPL hκ h _ _ hι
  have hκ₁ := capModelRightEquiv_capIota ν a hR hRa hP hPL hκ h c y hy.symm
  have hκ₂ := capModelRightEquiv_capIota νa b hRa hRba hP hPL hκ h _ _ hκ₁
  have hκ₃ := capModelRightEquiv_cast hP hPL hκ (mixedSwap ν a b) hRba hRab _ _ hκ₂
  rw [castOp_mixedCrossElem_plus_eq ν a b hp, ← capStendhal_smul,
    castTensorProductAlgebra_mixedCrossElem]
  change capLeftLin (j := j) (hj := hj) (Λc := Λc) (ν₀ := ν₀) L
      (orderProjection Q Λ νab
          (-StendhalAlgebraAllOrders.ψ (Multiset.card (stendhalWeight ℓ ν))) *
        appendBlackStendhal Q Λ a νb (appendBlackStendhal Q Λ b ν 1)) _ = _
  apply (capModelRightEquiv hRab hP hPL hκ).injective
  rw [capModelRightEquiv_capLeftLin hRab hP hPL hκ _ _ _ hι', LinearEquiv.map_smul, hκ₃,
    ← Submodule.Quotient.mk_smul, appendIota_two_mixedCross ν a b h hR hRb hRab]

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

omit [DecidableEq I] in
theorem plusWeight_assoc_mixed_swap :
    (Singleton.singleton b : Multiset I) + (νa + ν₀) = νab + ν₀ :=
  (plusWeight_assoc νa ν₀ b).trans (congrArg (· + ν₀) (mixedSwap ν a b))

open CategoryTheory in
/-- **`K ∘ 𝔈_a 𝔈_b ≅ 𝔈_a 𝔈_b ∘ K` carries the crossing of different colours to the crossing,
for `j < ℓ`** (Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21): for `a ≠ b`,
`(K ∘ τ) ≫ φ' = φ ≫ (τ ∘ K)` for `φ'`, `φ` the isomorphisms `CupCap.capECompIsoOfEq'` of
`CupCap.capAppendDataMid` for the two orders of appending, and `τ` the crossing
`resCrossOfEq` of `T^λ` and of `T^{λ⁺}`. Route hypotheses (tracked): `hfin`, `hQ`, `hκ`, `hP`,
`hPL`. -/
theorem capECompIsoOfEq'Mid_mixedCross (h : j < ℓ) (hab : a ≠ b) :
    Functor.whiskerRight (resCrossOfEq Λ hQ a b rfl rfl rfl (mixedSwap ν a b)) (OrdK ν) ≫
        (capECompIsoOfEq' (capAppendDataMid ν b hR hRb hP hPL hκ hQ hfin h)
          (capAppendDataMid νb a hRb hRab hP hPL hκ hQ hfin h) rfl
          (plusWeight_assoc νb ν₀ a)).hom =
      (capECompIsoOfEq' (capAppendDataMid ν a hR hRa hP hPL hκ hQ hfin h)
          (capAppendDataMid νa b hRa hRba hP hPL hκ hQ hfin h) (mixedSwap ν a b)
          (plusWeight_assoc_mixed_swap ν a b)).hom ≫
        Functor.whiskerLeft (OrdK νab)
          (resCrossOfEq (plusLabels Λ Λc j hj) hQ a b (plusWeight_assoc ν ν₀ b)
            (plusWeight_assoc νb ν₀ a) (plusWeight_assoc ν ν₀ a)
            (plusWeight_assoc_mixed_swap ν a b)) :=
  capECompIsoOfEq'_mixedCross hQ hab _ _ _ _ rfl (mixedSwap ν a b) _ _
    (capIota_two_mixedCross hP hPL hκ ν a b hR hRa hRb hRab hRba h _)

end Iso

end Categorification.Stendhal.CupCap

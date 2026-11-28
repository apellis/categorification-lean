/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapEDot

/-!
# `K ∘ 𝔈_i² ≅ 𝔈_i² ∘ K` and the same-colour crossing

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the compatibility of `K ∘ 𝔈_i ≅ 𝔈_i ∘ K` with the crossing on `𝔈_i²`. Two
applications of `CupCap.capEOrdIsoOfEq` give `K ∘ 𝔈_i² ≅ 𝔈_i² ∘ K`
(`CupCap.capECompIsoOfEq`), `c ⊗ m ↦ ι₂(ι₁(c)) ⊗ m`. It carries the crossing on `𝔈_i²`
(`blackCross`) to the crossing on `𝔈⁺_i²` (`resCrossOfEq`) as soon as `ι₂ ∘ ι₁` carries the
left action of the crossing of the two appended strands of `T^λ` to the right action of the
crossing of the two appended strands of `T^{λ⁺}` (`CupCap.capECompIsoOfEq_cross`).

## Main results

* `CupCap.resCrossOfEq_self_app_val`: the same-colour crossing on restrictions along content
  equalities acts by the cast of the crossing of the two appended strands.
* `CupCap.capECompIsoOfEq`, `CupCap.capECompIsoOfEq_cross`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory KLR KLRAlgebra MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Generic

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {n : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ' : Fin n → I →₀ ℕ)

/-- The same-colour crossing on restrictions along content equalities acts by the cast of the
crossing of the two appended strands. -/
theorem resCrossOfEq_self_app_val (hsym : KLRSymm Q) (i : I) {μ β δ : Multiset I}
    (h₁ : ({i} : Multiset I) + μ = β) (h₂ : ({i} : Multiset I) + β = δ)
    (M : ModuleCat.{0} (TensorProductAlgebra k Q Λ' δ)ᵐᵒᵖ)
    (r : Res (appendBlackOpOfEq Q Λ' i h₁) (Res (appendBlackOpOfEq Q Λ' i h₂) M)) :
    (((resCrossOfEq Λ' hsym i i h₁ h₂ h₁ h₂).app M).hom r).val.val =
      castOp Q Λ' (h₁ ▸ h₂ : ({i} : Multiset I) + (({i} : Multiset I) + μ) = δ)
        (op (appendedCross Q Λ' i μ)) • r.val.val := by
  subst h₁ h₂
  rw [resCrossOfEq_self]
  rfl

end Generic

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν₀ : Multiset I}
  {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  {ν : Multiset I} {i : I}

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "νᵢᵢ" =>
  ((Singleton.singleton i : Multiset I) + ((Singleton.singleton i : Multiset I) + ν))
local notation "TA" => TensorProductAlgebra k Q Λ ν
local notation "TAᵢ" => TensorProductAlgebra k Q Λ νᵢ
local notation "TAᵢᵢ" => TensorProductAlgebra k Q Λ νᵢᵢ
local notation "TPp" => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
local notation "TPpᵢ" => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (νᵢ + ν₀)
local notation "TPpᵢᵢ" => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (νᵢᵢ + ν₀)
local notation "CB" => CapBimodule k Q Λ Λc j hj ν ν₀ L
local notation "CBᵢ" => CapBimodule k Q Λ Λc j hj νᵢ ν₀ L
local notation "CBᵢᵢ" => CapBimodule k Q Λ Λc j hj νᵢᵢ ν₀ L
local notation "OrdK" => ordTensor TPpᵐᵒᵖ TAᵐᵒᵖ (OpBimodule TA CB)
local notation "OrdKᵢ" => ordTensor TPpᵢᵐᵒᵖ TAᵢᵐᵒᵖ (OpBimodule TAᵢ CBᵢ)
local notation "OrdKᵢᵢ" => ordTensor TPpᵢᵢᵐᵒᵖ TAᵢᵢᵐᵒᵖ (OpBimodule TAᵢᵢ CBᵢᵢ)
local notation "Eᵖ" => blackEOfEq Q (plusLabels Λ Λc j hj) i (plusWeight_assoc ν ν₀ i)
local notation "Eᵖᵢ" => blackEOfEq Q (plusLabels Λ Λc j hj) i (plusWeight_assoc νᵢ ν₀ i)

/-- **`K ∘ 𝔈_i² ≅ 𝔈_i² ∘ K`** (Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21):
two applications of `CupCap.capEOrdIsoOfEq`, `c ⊗ m ↦ ι₂(ι₁(c)) ⊗ m`. -/
def capECompIsoOfEq (D₁ : CapAppendData k Q Λ Λc j hj ν₀ L ν i)
    (D₂ : CapAppendData k Q Λ Λc j hj ν₀ L νᵢ i) :
    (blackE Q Λ i νᵢ ⋙ blackE Q Λ i ν) ⋙ OrdK ≅ OrdKᵢᵢ ⋙ (Eᵖᵢ ⋙ Eᵖ) :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (capEOrdIsoOfEq D₁) ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (capEOrdIsoOfEq D₂) _ ≪≫
    Functor.associator _ _ _

/-- The crossing of the two appended strands of `T^{λ⁺}`, cast to the content
`({i} + ({i} + ν)) + ν₀`, acting on the right. -/
abbrev capCrossPlusOp : TPpᵢᵢᵐᵒᵖ :=
  castOp Q (plusLabels Λ Λc j hj)
    (plusWeight_assoc ν ν₀ i ▸ plusWeight_assoc νᵢ ν₀ i :
      (Singleton.singleton i : Multiset I) + ((Singleton.singleton i : Multiset I) + (ν + ν₀)) =
        νᵢᵢ + ν₀)
    (op (appendedCross Q (plusLabels Λ Λc j hj) i (ν + ν₀)))

/-- **`K ∘ 𝔈_i² ≅ 𝔈_i² ∘ K` carries the crossing to the crossing** (Webster, arXiv:1309.3796v3,
§7.3, proof of Proposition 7.21): if `ι₂ ∘ ι₁` carries the left action of the crossing of the
two appended strands of `T^λ` to the right action of the crossing of the two appended strands of
`T^{λ⁺}`, then `(K ∘ τ) ≫ φ = φ ≫ (τ ∘ K)` for `φ = CupCap.capECompIsoOfEq D₁ D₂`. -/
theorem capECompIsoOfEq_cross (hQ : KLRSymm Q) (D₁ : CapAppendData k Q Λ Λc j hj ν₀ L ν i)
    (D₂ : CapAppendData k Q Λ Λc j hj ν₀ L νᵢ i)
    (hcross : ∀ c : CB, appendedCross Q Λ i ν • D₂.iota (D₁.iota c) =
      (capCrossPlusOp (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) (ν := ν)
        (i := i)) • D₂.iota (D₁.iota c)) :
    Functor.whiskerRight (blackCross Q Λ i ν) OrdK ≫ (capECompIsoOfEq D₁ D₂).hom =
      (capECompIsoOfEq D₁ D₂).hom ≫ Functor.whiskerLeft OrdKᵢᵢ
        (resCrossOfEq (plusLabels Λ Λc j hj) hQ i i (plusWeight_assoc ν ν₀ i)
          (plusWeight_assoc νᵢ ν₀ i) (plusWeight_assoc ν ν₀ i) (plusWeight_assoc νᵢ ν₀ i)) := by
  refine NatTrans.ext (funext fun X => ?_)
  refine ModuleCat.hom_ext (LinearMap.toAddMonoidHom_injective
    (DG.TensorProductOver.addHom_ext fun c m => Res.ext (Res.ext ?_)))
  change DG.TensorProductOver.tmul (M := InDegreeZero (OpBimodule TAᵢᵢ CBᵢᵢ))
      (N := InDegreeZero X) TAᵢᵢᵐᵒᵖ (D₂.iota (D₁.iota c))
        (op (appendedCross Q Λ i ν) • m.val.val) =
    (((resCrossOfEq (plusLabels Λ Λc j hj) hQ i i (plusWeight_assoc ν ν₀ i)
      (plusWeight_assoc νᵢ ν₀ i) (plusWeight_assoc ν ν₀ i) (plusWeight_assoc νᵢ ν₀ i)).app
        ((OrdKᵢᵢ).obj X)).hom _).val.val
  erw [resCrossOfEq_self_app_val]
  change _ = capCrossPlusOp (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀)
    (ν := ν) (i := i) • DG.TensorProductOver.tmul (M := InDegreeZero (OpBimodule TAᵢᵢ CBᵢᵢ))
      (N := InDegreeZero X) TAᵢᵢᵐᵒᵖ (D₂.iota (D₁.iota c)) m.val.val
  refine (DG.TensorProductOver.op_smul_tmul (A := TAᵢᵢᵐᵒᵖ)
    (M := InDegreeZero (OpBimodule TAᵢᵢ CBᵢᵢ)) (N := InDegreeZero X)
    (op (appendedCross Q Λ i ν)) (D₂.iota (D₁.iota c)) m.val.val).symm.trans ?_
  exact (congrArg (fun y : CBᵢᵢ => DG.TensorProductOver.tmul
    (M := InDegreeZero (OpBimodule TAᵢᵢ CBᵢᵢ)) (N := InDegreeZero X) TAᵢᵢᵐᵒᵖ y m.val.val)
    (hcross (c : CB))).trans rfl

end Categorification.Stendhal.CupCap

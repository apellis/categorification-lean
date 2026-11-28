/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapECast
import Categorification.WeightedKLR.RedStrands.BlackRouqBlocks

/-!
# `K ∘ 𝔈_i ≅ 𝔈_i ∘ K` and the dot

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the part for `𝔈_i`. The natural isomorphism `CupCap.capEOrdIsoOfEq`,
`c ⊗ m ↦ ι(c) ⊗ m`, carries the dot on `𝔈_i` (`blackDot`) to the dot on `𝔈⁺_i`
(`resDotOfEq` along `plusWeight_assoc`) as soon as `ι` carries the left action of the dot on the
appended strand of `T^λ` to the right action of the dot on the appended strand of `T^{λ⁺}`
(`CupCap.capEOrdIsoOfEq_dot`).

## Main results

* `CupCap.resDotOfEq_app_val`: the dot on restriction along a content equality acts by the cast
  of the dot.
* `CupCap.capEOrdIsoOfEq_dot`: the compatibility of `CupCap.capEOrdIsoOfEq` with the dots.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory KLR KLRAlgebra MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Generic

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {n : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ' : Fin n → I →₀ ℕ)

/-- The dot on restriction along a content equality acts by the cast of the dot on the appended
strand. -/
theorem resDotOfEq_app_val (i : I) {μ β : Multiset I} (h : ({i} : Multiset I) + μ = β)
    (M : ModuleCat.{0} (TensorProductAlgebra k Q Λ' β)ᵐᵒᵖ)
    (r : Res (appendBlackOpOfEq Q Λ' i h) M) :
    (((resDotOfEq Q Λ' i h).app M).hom r).val =
      castOp Q Λ' h (op (appendedDot Q Λ' i μ)) • r.val := by
  subst h; rfl

end Generic

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
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

/-- The dot on the appended strand of `T^{λ⁺}`, cast to the content `({i} + ν) + ν₀`, acting on
the right. -/
abbrev capDotPlusOp : TPpᵢᵐᵒᵖ :=
  castOp Q (plusLabels Λ Λc j hj) (plusWeight_assoc ν ν₀ i)
    (op (appendedDot Q (plusLabels Λ Λc j hj) i (ν + ν₀)))

/-- **`K ∘ 𝔈_i ≅ 𝔈_i ∘ K` carries the dot to the dot** (Webster, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.21): if `ι` carries the left action of the dot on the appended strand of `T^λ`
to the right action of the dot on the appended strand of `T^{λ⁺}`, then
`(K ∘ x) ≫ φ = φ ≫ (x ∘ K)` for `φ = CupCap.capEOrdIsoOfEq D`. -/
theorem capEOrdIsoOfEq_dot (D : CapAppendData k Q Λ Λc j hj ν₀ L ν i)
    (hdot : ∀ c : CB, appendedDot Q Λ i ν • D.iota c =
      (capDotPlusOp (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) (ν := ν)
        (i := i)) • D.iota c) :
    Functor.whiskerRight (blackDot Q Λ i ν) OrdK ≫ (capEOrdIsoOfEq D).hom =
      (capEOrdIsoOfEq D).hom ≫ Functor.whiskerLeft OrdKᵢ
        (resDotOfEq Q (plusLabels Λ Λc j hj) i (plusWeight_assoc ν ν₀ i)) := by
  refine NatTrans.ext (funext fun X => ?_)
  refine ModuleCat.hom_ext (LinearMap.toAddMonoidHom_injective
    (DG.TensorProductOver.addHom_ext fun c m => Res.ext ?_))
  change DG.TensorProductOver.tmul (M := InDegreeZero (OpBimodule TAᵢ CBᵢ)) (N := InDegreeZero X)
      TAᵢᵐᵒᵖ (D.iota c) (op (appendedDot Q Λ i ν) • m.val) =
    (((resDotOfEq Q (plusLabels Λ Λc j hj) i (plusWeight_assoc ν ν₀ i)).app
      ((OrdKᵢ).obj X)).hom _).val
  erw [resDotOfEq_app_val]
  change _ = capDotPlusOp (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) (ν := ν)
    (i := i) • DG.TensorProductOver.tmul (M := InDegreeZero (OpBimodule TAᵢ CBᵢ))
      (N := InDegreeZero X) TAᵢᵐᵒᵖ (D.iota c) m.val
  refine (DG.TensorProductOver.op_smul_tmul (A := TAᵢᵐᵒᵖ)
    (M := InDegreeZero (OpBimodule TAᵢ CBᵢ)) (N := InDegreeZero X) (op (appendedDot Q Λ i ν))
    (D.iota c) m.val).symm.trans ?_
  exact (congrArg (fun y : CBᵢ => DG.TensorProductOver.tmul
    (M := InDegreeZero (OpBimodule TAᵢ CBᵢ)) (N := InDegreeZero X) TAᵢᵐᵒᵖ y m.val)
    (hdot (c : CB))).trans rfl

end Categorification.Stendhal.CupCap

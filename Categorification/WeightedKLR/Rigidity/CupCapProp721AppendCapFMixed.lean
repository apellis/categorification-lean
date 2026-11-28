/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongTwistedMate
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapFCross
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapEMixed

/-!
# `K ∘ 𝔉_b 𝔉_a ≅ 𝔉_b 𝔉_a ∘ K` and the crossing of different colours

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the compatibility of `K ∘ 𝔉 ≅ 𝔉 ∘ K` with the crossing of two strands of
different colours `a ≠ b`. The crossing on inductions is the mate of the crossing on restrictions
(`indCrossOfEq`), which for `a ≠ b` acts by minus the cast of the mixed crossing of the two
appended strands, between the two orders of appending; so on the generator `1 ⊗ (1 ⊗ n)` it
multiplies by that element (`CupCap.indCrossOfEq_ne_unitGen`, from
`InductionAlong.conjugateEquiv_symm_twisted_unitGen`). With `CupCap.capFCompIsoOfEq'`, the two
applications of `CupCap.capFOrdIsoOfEq` along a content equality, the compatibility with the
crossing (`CupCap.capFCompIsoOfEq'_mixedCross`) follows from the hypothesis of the part for
`𝔈` (`CupCap.capECompIsoOfEq'_mixedCross`) with `ι ∘ ι` replaced by `bwd(1 ⊗ bwd(1 ⊗ ·))`.

## Main definitions

* `CupCap.capFOrdIsoOfEq'`, `CupCap.capFCompIsoOfEq'`.

## Main results

* `CupCap.indCrossOfEq_ne_unitGen`, `CupCap.capFCompIsoOfEq'_inv_unitGen`.
* `CupCap.capFCompIsoOfEq'_mixedCross`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory KLR KLRAlgebra MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Generic

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {n : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ' : Fin n → I →₀ ℕ)

/-- **The crossing of different colours on inductions, on generators**: for `a ≠ b`,
`indCrossOfEq` sends `1 ⊗ (1 ⊗ n)` (first `b`, then `a` appended) to minus the cast of the mixed
crossing of the two appended strands times `1 ⊗ (1 ⊗ n)` (first `a`, then `b` appended). -/
theorem indCrossOfEq_ne_unitGen (hsym : KLRSymm Q) {a b : I} (hab : a ≠ b)
    {μ β₁ β₂ δ : Multiset I}
    (h₁ : ({b} : Multiset I) + μ = β₁) (h₂ : ({a} : Multiset I) + β₁ = δ)
    (h₃ : ({a} : Multiset I) + μ = β₂) (h₄ : ({b} : Multiset I) + β₂ = δ)
    (N : ModuleCat.{0} (TensorProductAlgebra k Q Λ' μ)ᵐᵒᵖ) (x : N) :
    ((indCrossOfEq Λ' hsym a b h₁ h₂ h₃ h₄).app N).hom
        (Ind.tmul (unitGen (appendBlackOpOfEq Q Λ' a h₂))
          (Ind.tmul (unitGen (appendBlackOpOfEq Q Λ' b h₁)) x)) =
      (-castOp Q Λ' (h₃ ▸ h₄ : ({b} : Multiset I) + (({a} : Multiset I) + μ) = δ)
          (op (mixedCrossElem (Q := Q) Λ' μ b a))) •
        Ind.tmul (unitGen (appendBlackOpOfEq Q Λ' b h₄))
          (Ind.tmul (unitGen (appendBlackOpOfEq Q Λ' a h₃)) x) :=
  conjugateEquiv_symm_twisted_unitGen _ _ _ _ _ (resCrossOfEq Λ' hsym a b h₁ h₂ h₃ h₄)
    (fun M r => (resCrossOfEq_ne_app_val Λ' hsym hab h₁ h₂ h₃ h₄ M r).trans
      (neg_smul _ _).symm) N x

end Generic

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν₀ : Multiset I}
  {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

local notation "TA" μ:max => TensorProductAlgebra k Q Λ μ
local notation "TPp" μ:max => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (μ + ν₀)
local notation "CB" μ:max => CapBimodule k Q Λ Λc j hj μ ν₀ L
local notation "OrdK" μ:max => ordTensor (TPp μ)ᵐᵒᵖ (TA μ)ᵐᵒᵖ (OpBimodule (TA μ) (CB μ))

/-- `K ∘ 𝔉_i ≅ 𝔉_i ∘ K` (`CupCap.capFOrdIsoOfEq`) with the content `{i} + ν` of `T^λ` replaced
by an equal content `β`. -/
def capFOrdIsoOfEq' {ν : Multiset I} {i : I} (D : CapFData k Q Λ Λc j hj ν₀ L ν i)
    {β : Multiset I} (h : ({i} : Multiset I) + ν = β)
    (hp : ({i} : Multiset I) + (ν + ν₀) = β + ν₀) :
    blackFOfEq Q Λ i h ⋙ OrdK β ≅ OrdK ν ⋙ blackFOfEq Q (plusLabels Λ Λc j hj) i hp := by
  subst h
  exact capFOrdIsoOfEq D

theorem capFOrdIsoOfEq'_inv_unitGen {ν : Multiset I} {i : I}
    (D : CapFData k Q Λ Λc j hj ν₀ L ν i) {β : Multiset I} (h : ({i} : Multiset I) + ν = β)
    (hp : ({i} : Multiset I) + (ν + ν₀) = β + ν₀) (X : ModuleCat.{0} (TA ν)ᵐᵒᵖ) (c : CB ν)
    (x : X) :
    ((capFOrdIsoOfEq' D h hp).inv.app X).hom
        (Ind.tmul (unitGen (appendBlackOpOfEq Q (plusLabels Λ Λc j hj) i hp))
          (DG.TensorProductOver.tmul (M := InDegreeZero (OpBimodule (TA ν) (CB ν)))
            (N := InDegreeZero X) (TA ν)ᵐᵒᵖ c x : (OrdK ν).obj X)) =
      DG.TensorProductOver.tmul (M := InDegreeZero (OpBimodule (TA β) (CB β)))
        (N := InDegreeZero ((blackFOfEq Q Λ i h).obj X)) (TA β)ᵐᵒᵖ
        (h ▸ D.bwd (Ind.tmul (unitGen (appendBlackTPAOp k Q Λ Λc j hj ν ν₀ i)) c) : CB β)
        (Ind.tmul (unitGen (appendBlackOpOfEq Q Λ i h)) x) := by
  subst h
  exact capFOrdIsoOfEq_inv_unitGen D X c x

/-- **`K ∘ 𝔉_a 𝔉_b ≅ 𝔉_a 𝔉_b ∘ K`** along a content equality `{a} + ({b} + ν) = δ` (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21): two applications of
`CupCap.capFOrdIsoOfEq`. -/
def capFCompIsoOfEq' {ν : Multiset I} {a b : I} (D₁ : CapFData k Q Λ Λc j hj ν₀ L ν b)
    (D₂ : CapFData k Q Λ Λc j hj ν₀ L (({b} : Multiset I) + ν) a) {δ : Multiset I}
    (h : ({a} : Multiset I) + (({b} : Multiset I) + ν) = δ)
    (hp : ({a} : Multiset I) + ((({b} : Multiset I) + ν) + ν₀) = δ + ν₀) :
    (blackF Q Λ b ν ⋙ blackFOfEq Q Λ a h) ⋙ OrdK δ ≅
      OrdK ν ⋙ (blackFOfEq Q (plusLabels Λ Λc j hj) b (plusWeight_assoc ν ν₀ b) ⋙
        blackFOfEq Q (plusLabels Λ Λc j hj) a hp) :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (capFOrdIsoOfEq' D₂ h hp) ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (capFOrdIsoOfEq D₁) _ ≪≫
    Functor.associator _ _ _

theorem capFCompIsoOfEq'_inv_unitGen {ν : Multiset I} {a b : I}
    (D₁ : CapFData k Q Λ Λc j hj ν₀ L ν b)
    (D₂ : CapFData k Q Λ Λc j hj ν₀ L (({b} : Multiset I) + ν) a) {δ : Multiset I}
    (h : ({a} : Multiset I) + (({b} : Multiset I) + ν) = δ)
    (hp : ({a} : Multiset I) + ((({b} : Multiset I) + ν) + ν₀) = δ + ν₀)
    (X : ModuleCat.{0} (TA ν)ᵐᵒᵖ) (c : CB ν) (x : X) :
    ((capFCompIsoOfEq' D₁ D₂ h hp).inv.app X).hom
        (Ind.tmul (unitGen (appendBlackOpOfEq Q (plusLabels Λ Λc j hj) a hp))
          (Ind.tmul (unitGen (appendBlackOpOfEq Q (plusLabels Λ Λc j hj) b
            (plusWeight_assoc ν ν₀ b)))
          (DG.TensorProductOver.tmul (M := InDegreeZero (OpBimodule (TA ν) (CB ν)))
            (N := InDegreeZero X) (TA ν)ᵐᵒᵖ c x : (OrdK ν).obj X))) =
      DG.TensorProductOver.tmul (M := InDegreeZero (OpBimodule (TA δ) (CB δ)))
        (N := InDegreeZero ((blackFOfEq Q Λ a h).obj ((blackF Q Λ b ν).obj X))) (TA δ)ᵐᵒᵖ
        (h ▸ D₂.bwd (Ind.tmul (unitGen (appendBlackTPAOp k Q Λ Λc j hj
          (({b} : Multiset I) + ν) ν₀ a))
          (D₁.bwd (Ind.tmul (unitGen (appendBlackTPAOp k Q Λ Λc j hj ν ν₀ b)) c))) : CB δ)
        (Ind.tmul (unitGen (appendBlackOpOfEq Q Λ a h))
          (Ind.tmul (unitGen (appendBlackOp Q Λ b ν)) x)) := by
  change ((capFOrdIsoOfEq' D₂ h hp).inv.app ((blackF Q Λ b ν).obj X)).hom
    (Ind.tmul (unitGen (appendBlackOpOfEq Q (plusLabels Λ Λc j hj) a hp))
    (((capFOrdIsoOfEq D₁).inv.app X).hom (Ind.tmul (unitGen (appendBlackOpOfEq Q
      (plusLabels Λ Λc j hj) b (plusWeight_assoc ν ν₀ b)))
      (DG.TensorProductOver.tmul (M := InDegreeZero (OpBimodule (TA ν) (CB ν)))
        (N := InDegreeZero X) (TA ν)ᵐᵒᵖ c x)))) = _
  rw [capFOrdIsoOfEq_inv_unitGen]
  exact capFOrdIsoOfEq'_inv_unitGen D₂ h hp _ _ _

section Mixed

variable {ν : Multiset I} {a b : I}

local notation "νab" =>
  ((Singleton.singleton a : Multiset I) + ((Singleton.singleton b : Multiset I) + ν))
local notation "Λ⁺" => plusLabels Λ Λc j hj

theorem capFCompIsoOfEq'_mixedCross_tmul (D_b : CapFData k Q Λ Λc j hj ν₀ L ν b)
    (D_ba : CapFData k Q Λ Λc j hj ν₀ L (({b} : Multiset I) + ν) a)
    (D_a : CapFData k Q Λ Λc j hj ν₀ L ν a)
    (D_ab : CapFData k Q Λ Λc j hj ν₀ L (({a} : Multiset I) + ν) b)
    (h₄ : ({b} : Multiset I) + (({a} : Multiset I) + ν) = νab)
    (hp₂ : ({a} : Multiset I) + ((({b} : Multiset I) + ν) + ν₀) = νab + ν₀)
    (hp₄ : ({b} : Multiset I) + ((({a} : Multiset I) + ν) + ν₀) = νab + ν₀)
    (hcross : ∀ c : CB ν,
      castTensorProductAlgebra Q Λ h₄ (mixedCrossElem (Q := Q) Λ ν b a) •
          D_ba.bwd (Ind.tmul (unitGen (appendBlackTPAOp k Q Λ Λc j hj
            (({b} : Multiset I) + ν) ν₀ a))
            (D_b.bwd (Ind.tmul (unitGen (appendBlackTPAOp k Q Λ Λc j hj ν ν₀ b)) c))) =
        castOp Q Λ⁺ (plusWeight_assoc ν ν₀ a ▸ hp₄ :
            ({b} : Multiset I) + (({a} : Multiset I) + (ν + ν₀)) = νab + ν₀)
          (op (mixedCrossElem (Q := Q) Λ⁺ (ν + ν₀) b a)) •
          (h₄ ▸ D_ab.bwd (Ind.tmul (unitGen (appendBlackTPAOp k Q Λ Λc j hj
            (({a} : Multiset I) + ν) ν₀ b))
            (D_a.bwd (Ind.tmul (unitGen (appendBlackTPAOp k Q Λ Λc j hj ν ν₀ a)) c))) : CB νab))
    (X : ModuleCat.{0} (TA ν)ᵐᵒᵖ)
    (τ : (blackF Q Λ b ν ⋙ blackFOfEq Q Λ a (rfl : ({a} : Multiset I) + _ = νab)).obj X ⟶
      (blackF Q Λ a ν ⋙ blackFOfEq Q Λ b h₄).obj X)
    (hτ : ∀ x : X, τ.hom (Ind.tmul (unitGen (appendBlackOpOfEq Q Λ a
        (rfl : ({a} : Multiset I) + _ = νab)))
          (Ind.tmul (unitGen (appendBlackOp Q Λ b ν)) x)) =
      (-castOp Q Λ h₄ (op (mixedCrossElem (Q := Q) Λ ν b a))) •
        Ind.tmul (unitGen (appendBlackOpOfEq Q Λ b h₄))
          (Ind.tmul (unitGen (appendBlackOp Q Λ a ν)) x))
    (σ : (blackFOfEq Q Λ⁺ b (plusWeight_assoc ν ν₀ b) ⋙ blackFOfEq Q Λ⁺ a hp₂).obj
        ((OrdK ν).obj X) ⟶
      (blackFOfEq Q Λ⁺ a (plusWeight_assoc ν ν₀ a) ⋙ blackFOfEq Q Λ⁺ b hp₄).obj
        ((OrdK ν).obj X))
    (hσ : ∀ y : (OrdK ν).obj X, σ.hom (Ind.tmul (unitGen (appendBlackOpOfEq Q Λ⁺ a hp₂))
        (Ind.tmul (unitGen (appendBlackOpOfEq Q Λ⁺ b (plusWeight_assoc ν ν₀ b))) y)) =
      (-castOp Q Λ⁺ (plusWeight_assoc ν ν₀ a ▸ hp₄ :
            ({b} : Multiset I) + (({a} : Multiset I) + (ν + ν₀)) = νab + ν₀)
          (op (mixedCrossElem (Q := Q) Λ⁺ (ν + ν₀) b a))) •
        Ind.tmul (unitGen (appendBlackOpOfEq Q Λ⁺ b hp₄))
          (Ind.tmul (unitGen (appendBlackOpOfEq Q Λ⁺ a (plusWeight_assoc ν ν₀ a))) y))
    (c : CB ν) (x : X) :
    ((OrdK νab).map τ).hom (((capFCompIsoOfEq' D_b D_ba rfl hp₂).inv.app X).hom
        (Ind.tmul (unitGen (appendBlackOpOfEq Q Λ⁺ a hp₂))
          (Ind.tmul (unitGen (appendBlackOpOfEq Q Λ⁺ b (plusWeight_assoc ν ν₀ b)))
            (DG.TensorProductOver.tmul (M := InDegreeZero (OpBimodule (TA ν) (CB ν)))
              (N := InDegreeZero X) (TA ν)ᵐᵒᵖ c x)))) =
      ((capFCompIsoOfEq' D_a D_ab h₄ hp₄).inv.app X).hom (σ.hom
        (Ind.tmul (unitGen (appendBlackOpOfEq Q Λ⁺ a hp₂))
          (Ind.tmul (unitGen (appendBlackOpOfEq Q Λ⁺ b (plusWeight_assoc ν ν₀ b)))
            (DG.TensorProductOver.tmul (M := InDegreeZero (OpBimodule (TA ν) (CB ν)))
              (N := InDegreeZero X) (TA ν)ᵐᵒᵖ c x)))) := by
  have hI := capFCompIsoOfEq'_inv_unitGen D_b D_ba rfl hp₂ X c x
  have hJ := capFCompIsoOfEq'_inv_unitGen D_a D_ab h₄ hp₄ X c x
  have hc : (-castTensorProductAlgebra Q Λ h₄ (mixedCrossElem (Q := Q) Λ ν b a)) •
      D_ba.bwd (Ind.tmul (unitGen (appendBlackTPAOp k Q Λ Λc j hj
        (({b} : Multiset I) + ν) ν₀ a))
        (D_b.bwd (Ind.tmul (unitGen (appendBlackTPAOp k Q Λ Λc j hj ν ν₀ b)) c))) =
      (-castOp Q Λ⁺ (plusWeight_assoc ν ν₀ a ▸ hp₄ :
            ({b} : Multiset I) + (({a} : Multiset I) + (ν + ν₀)) = νab + ν₀)
          (op (mixedCrossElem (Q := Q) Λ⁺ (ν + ν₀) b a))) •
        (h₄ ▸ D_ab.bwd (Ind.tmul (unitGen (appendBlackTPAOp k Q Λ Λc j hj
          (({a} : Multiset I) + ν) ν₀ b))
          (D_a.bwd (Ind.tmul (unitGen (appendBlackTPAOp k Q Λ Λc j hj ν ν₀ a)) c))) : CB νab) := by
    rw [neg_smul, neg_smul, hcross c]
  have hco : -castOp Q Λ h₄ (op (mixedCrossElem (Q := Q) Λ ν b a)) =
      op (-castTensorProductAlgebra Q Λ h₄ (mixedCrossElem (Q := Q) Λ ν b a)) := by
    rw [castOp_op, MulOpposite.op_neg]
  refine (congrArg ((OrdK νab).map τ).hom hI).trans ?_
  refine (congrArg (fun t => DG.TensorProductOver.tmul
    (M := InDegreeZero (OpBimodule (TA νab) (CB νab)))
    (N := InDegreeZero ((blackF Q Λ a ν ⋙ blackFOfEq Q Λ b h₄).obj X)) (TA νab)ᵐᵒᵖ
    (D_ba.bwd (Ind.tmul (unitGen (appendBlackTPAOp k Q Λ Λc j hj (({b} : Multiset I) + ν) ν₀ a))
        (D_b.bwd (Ind.tmul (unitGen (appendBlackTPAOp k Q Λ Λc j hj ν ν₀ b)) c)))) t)
    (hτ x)).trans ?_
  refine (congrArg (fun s => DG.TensorProductOver.tmul
    (M := InDegreeZero (OpBimodule (TA νab) (CB νab)))
    (N := InDegreeZero ((blackF Q Λ a ν ⋙ blackFOfEq Q Λ b h₄).obj X)) (TA νab)ᵐᵒᵖ
    (D_ba.bwd (Ind.tmul (unitGen (appendBlackTPAOp k Q Λ Λc j hj (({b} : Multiset I) + ν) ν₀ a))
        (D_b.bwd (Ind.tmul (unitGen (appendBlackTPAOp k Q Λ Λc j hj ν ν₀ b)) c))))
    (s • Ind.tmul (unitGen (appendBlackOpOfEq Q Λ b h₄))
          (Ind.tmul (unitGen (appendBlackOp Q Λ a ν)) x))) hco).trans ?_
  refine ((DG.TensorProductOver.op_smul_tmul (A := (TA νab)ᵐᵒᵖ)
    (M := InDegreeZero (OpBimodule (TA νab) (CB νab)))
    (N := InDegreeZero ((blackF Q Λ a ν ⋙ blackFOfEq Q Λ b h₄).obj X)) _ _ _).symm).trans ?_
  refine (congrArg (fun y : CB νab => DG.TensorProductOver.tmul
    (M := InDegreeZero (OpBimodule (TA νab) (CB νab)))
    (N := InDegreeZero ((blackF Q Λ a ν ⋙ blackFOfEq Q Λ b h₄).obj X)) (TA νab)ᵐᵒᵖ y
    (Ind.tmul (unitGen (appendBlackOpOfEq Q Λ b h₄))
          (Ind.tmul (unitGen (appendBlackOp Q Λ a ν)) x))) hc).trans ?_
  exact Eq.symm ((congrArg ((capFCompIsoOfEq' D_a D_ab h₄ hp₄).inv.app X).hom (hσ _)).trans
    ((LinearMap.map_smul _ _ _).trans ((congrArg (_ • ·) hJ).trans rfl)))

theorem capFCompIsoOfEq'_mixedCross_app (hQ : KLRSymm Q) (hab : a ≠ b)
    (D_b : CapFData k Q Λ Λc j hj ν₀ L ν b)
    (D_ba : CapFData k Q Λ Λc j hj ν₀ L (({b} : Multiset I) + ν) a)
    (D_a : CapFData k Q Λ Λc j hj ν₀ L ν a)
    (D_ab : CapFData k Q Λ Λc j hj ν₀ L (({a} : Multiset I) + ν) b)
    (h₄ : ({b} : Multiset I) + (({a} : Multiset I) + ν) = νab)
    (hp₂ : ({a} : Multiset I) + ((({b} : Multiset I) + ν) + ν₀) = νab + ν₀)
    (hp₄ : ({b} : Multiset I) + ((({a} : Multiset I) + ν) + ν₀) = νab + ν₀)
    (hcross : ∀ c : CB ν,
      castTensorProductAlgebra Q Λ h₄ (mixedCrossElem (Q := Q) Λ ν b a) •
          D_ba.bwd (Ind.tmul (unitGen (appendBlackTPAOp k Q Λ Λc j hj
            (({b} : Multiset I) + ν) ν₀ a))
            (D_b.bwd (Ind.tmul (unitGen (appendBlackTPAOp k Q Λ Λc j hj ν ν₀ b)) c))) =
        castOp Q Λ⁺ (plusWeight_assoc ν ν₀ a ▸ hp₄ :
            ({b} : Multiset I) + (({a} : Multiset I) + (ν + ν₀)) = νab + ν₀)
          (op (mixedCrossElem (Q := Q) Λ⁺ (ν + ν₀) b a)) •
          (h₄ ▸ D_ab.bwd (Ind.tmul (unitGen (appendBlackTPAOp k Q Λ Λc j hj
            (({a} : Multiset I) + ν) ν₀ b))
            (D_a.bwd (Ind.tmul (unitGen (appendBlackTPAOp k Q Λ Λc j hj ν ν₀ a)) c))) : CB νab))
    (X : ModuleCat.{0} (TA ν)ᵐᵒᵖ)
    (y : (OrdK ν ⋙ (blackFOfEq Q Λ⁺ b (plusWeight_assoc ν ν₀ b) ⋙
      blackFOfEq Q Λ⁺ a hp₂)).obj X) :
    ((OrdK νab).map ((indCrossOfEq Λ hQ a b rfl rfl rfl h₄).app X)).hom
        (((capFCompIsoOfEq' D_b D_ba rfl hp₂).inv.app X).hom y) =
      ((capFCompIsoOfEq' D_a D_ab h₄ hp₄).inv.app X).hom
        (((indCrossOfEq Λ⁺ hQ a b (plusWeight_assoc ν ν₀ b) hp₂ (plusWeight_assoc ν ν₀ a)
          hp₄).app ((OrdK ν).obj X)).hom y) := by
  exact ind₂_comp_ext
    (φ₁ := appendBlackOpOfEq Q Λ⁺ b (plusWeight_assoc ν ν₀ b))
    (φ₂ := appendBlackOpOfEq Q Λ⁺ a hp₂)
    (S := InDegreeZero (OpBimodule (TA ν) (CB ν)) × InDegreeZero X)
    (t := fun p => DG.TensorProductOver.tmul (M := InDegreeZero (OpBimodule (TA ν) (CB ν)))
      (N := InDegreeZero X) (TA ν)ᵐᵒᵖ p.1 p.2)
    (fun _ _ h => DG.TensorProductOver.addHom_ext fun m n => h (m, n))
    ((OrdK νab).map ((indCrossOfEq Λ hQ a b rfl rfl rfl h₄).app X)).hom
    ((capFCompIsoOfEq' D_b D_ba rfl hp₂).inv.app X).hom
    ((capFCompIsoOfEq' D_a D_ab h₄ hp₄).inv.app X).hom
    ((indCrossOfEq Λ⁺ hQ a b (plusWeight_assoc ν ν₀ b) hp₂ (plusWeight_assoc ν ν₀ a)
          hp₄).app ((OrdK ν).obj X)).hom
    (fun p => capFCompIsoOfEq'_mixedCross_tmul D_b D_ba D_a D_ab h₄ hp₂ hp₄ hcross X
        ((indCrossOfEq Λ hQ a b rfl rfl rfl h₄).app X)
        (fun x => indCrossOfEq_ne_unitGen Λ hQ hab rfl rfl rfl h₄ X x)
        ((indCrossOfEq Λ⁺ hQ a b (plusWeight_assoc ν ν₀ b) hp₂ (plusWeight_assoc ν ν₀ a)
          hp₄).app ((OrdK ν).obj X))
        (fun y => indCrossOfEq_ne_unitGen Λ⁺ hQ hab _ hp₂ _ hp₄ ((OrdK ν).obj X) y) p.1 p.2) y

/-- **`K ∘ 𝔉_a 𝔉_b ≅ 𝔉_a 𝔉_b ∘ K` carries the crossing of different colours to the crossing**
(Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21): for `a ≠ b`, if
`bwd(1 ⊗ bwd(1 ⊗ ·))` for the two orders of appending is intertwined by the mixed crossings of
the two appended strands of `T^λ` (on the left) and of `T^{λ⁺}` (on the right), then
`(K ∘ τ) ≫ φ' = φ ≫ (τ ∘ K)` for `φ`, `φ'` the isomorphisms `CupCap.capFCompIsoOfEq'` for the
two orders, and `τ` the crossings `indCrossOfEq` of `T^λ` and of `T^{λ⁺}`. -/
theorem capFCompIsoOfEq'_mixedCross (hQ : KLRSymm Q) (hab : a ≠ b)
    (D_b : CapFData k Q Λ Λc j hj ν₀ L ν b)
    (D_ba : CapFData k Q Λ Λc j hj ν₀ L (({b} : Multiset I) + ν) a)
    (D_a : CapFData k Q Λ Λc j hj ν₀ L ν a)
    (D_ab : CapFData k Q Λ Λc j hj ν₀ L (({a} : Multiset I) + ν) b)
    (h₄ : ({b} : Multiset I) + (({a} : Multiset I) + ν) = νab)
    (hp₂ : ({a} : Multiset I) + ((({b} : Multiset I) + ν) + ν₀) = νab + ν₀)
    (hp₄ : ({b} : Multiset I) + ((({a} : Multiset I) + ν) + ν₀) = νab + ν₀)
    (hcross : ∀ c : CB ν,
      castTensorProductAlgebra Q Λ h₄ (mixedCrossElem (Q := Q) Λ ν b a) •
          D_ba.bwd (Ind.tmul (unitGen (appendBlackTPAOp k Q Λ Λc j hj
            (({b} : Multiset I) + ν) ν₀ a))
            (D_b.bwd (Ind.tmul (unitGen (appendBlackTPAOp k Q Λ Λc j hj ν ν₀ b)) c))) =
        castOp Q Λ⁺ (plusWeight_assoc ν ν₀ a ▸ hp₄ :
            ({b} : Multiset I) + (({a} : Multiset I) + (ν + ν₀)) = νab + ν₀)
          (op (mixedCrossElem (Q := Q) Λ⁺ (ν + ν₀) b a)) •
          (h₄ ▸ D_ab.bwd (Ind.tmul (unitGen (appendBlackTPAOp k Q Λ Λc j hj
            (({a} : Multiset I) + ν) ν₀ b))
            (D_a.bwd (Ind.tmul (unitGen (appendBlackTPAOp k Q Λ Λc j hj ν ν₀ a)) c))) : CB νab)) :
    (Functor.whiskerRight (indCrossOfEq Λ hQ a b rfl rfl rfl h₄) (OrdK νab) :
        (blackF Q Λ b ν ⋙ blackFOfEq Q Λ a (rfl : ({a} : Multiset I) + _ = νab)) ⋙ OrdK νab ⟶
          (blackF Q Λ a ν ⋙ blackFOfEq Q Λ b h₄) ⋙ OrdK νab) ≫
        (capFCompIsoOfEq' D_a D_ab h₄ hp₄).hom =
      (capFCompIsoOfEq' D_b D_ba rfl hp₂).hom ≫ Functor.whiskerLeft (OrdK ν)
        (indCrossOfEq Λ⁺ hQ a b (plusWeight_assoc ν ν₀ b) hp₂ (plusWeight_assoc ν ν₀ a) hp₄) := by
  suffices key : (capFCompIsoOfEq' D_b D_ba rfl hp₂).inv ≫
      (Functor.whiskerRight (indCrossOfEq Λ hQ a b rfl rfl rfl h₄) (OrdK νab) :
        (blackF Q Λ b ν ⋙ blackFOfEq Q Λ a (rfl : ({a} : Multiset I) + _ = νab)) ⋙ OrdK νab ⟶
          (blackF Q Λ a ν ⋙ blackFOfEq Q Λ b h₄) ⋙ OrdK νab) =
      Functor.whiskerLeft (OrdK ν)
        (indCrossOfEq Λ⁺ hQ a b (plusWeight_assoc ν ν₀ b) hp₂ (plusWeight_assoc ν ν₀ a) hp₄) ≫
        (capFCompIsoOfEq' D_a D_ab h₄ hp₄).inv from
    (Iso.inv_comp_eq _).1 ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (capFCompIsoOfEq' D_a D_ab h₄ hp₄).hom) key).trans
        ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) (capFCompIsoOfEq' D_a D_ab h₄ hp₄).inv_hom_id).trans
          (Category.comp_id _)))))
  exact NatTrans.ext (funext fun X => ModuleCat.hom_ext (LinearMap.ext
    (capFCompIsoOfEq'_mixedCross_app hQ hab D_b D_ba D_a D_ab h₄ hp₂ hp₄ hcross X)))

end Mixed

end Categorification.Stendhal.CupCap

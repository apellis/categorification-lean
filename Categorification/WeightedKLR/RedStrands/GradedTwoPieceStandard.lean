/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.GradedStandardization
import Categorification.WeightedKLR.RedStrands.TwoPieceStandardEquiv
import Categorification.WeightedKLR.RedStrands.ParabolicStandardExact
import Categorification.WeightedKLR.RedStrands.LeftStandardGFin
import Categorification.KLR.ExtTensorK0Equiv

/-!
# The graded two-piece standard module

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §5.1,
Definition 5.1 and the standardization before Proposition 5.6. For a red-ordered loading `t`
of the first `ℓ` red strands, a black sequence `u`, and graded modules `X ≅ S_t` and
`Z ≅ R^{λ_{ℓ+1}} e(u)` whose generators have degree zero, the graded left standard module
`S_{t λ_{ℓ+1} u}` is isomorphic, as a graded module, to the graded standardization of
`X ⊠ Z` (`twoPieceStandardGradedEquiv`). This is the inductive step identifying the Definition
5.1 standard modules at row loadings with the iterated standardizations of Proposition 5.6.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR KLRAlgebra Categorification.Graded DirectSum
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin (ℓ+1) → I →₀ ℕ)
  (G : GradingDatum (stendhalQ Q Λ)) (hQ : KLRSymm Q) {θ β : Multiset I}

local notation "α" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ)
local notation "δ" => Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ))
  (stendhalWeight 1 β)
local notation "Told" => TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) θ
local notation "Cyc" => CycKLR k Q (fun i => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i) β
local notation "T" => TensorProductAlgebra k Q Λ (θ + β)
local notation "D" => parabolicFactorAlgebra Q Λ θ β

section Unit

variable (N : GFin (tensorGrading (tensorProductGrade (restrictRedGrading Q Λ G) θ)
  (CycKLR.grade (restrictBlackGrading Q Λ G) (Λ (Fin.last ℓ)) β)))

/-- The identity shuffle on a vector of degree `d` has degree `d` in the graded
standardization. -/
theorem parabolicStandardUnit_mem_standardization {d : ℤ} {n : N.carrier} (hn : n ∈ N.grading d) :
    (parabolicStandardUnit Q Λ θ β N.carrier n : (standardizationGFin Λ G θ β hQ N).carrier) ∈
      (standardizationGFin Λ G θ β hQ N).grading d := by
  apply Graded.mem_map_of_mem
  let ℳ : ℤ → Submodule k (ParabolicInput Q Λ θ β N.carrier) := N.grading
  change BalancedTensor.tmul _ _ ∈ G.indGrading α δ ℳ d
  exact (zero_add d) ▸ tmul_mem_balancedGrading
    (show (KLRAlgebra.oneConcatSubBimod : KLRAlgebra.IndBimod (stendhalQ Q Λ) α δ) ∈
      G.bimodGrading α δ 0 from G.oneConcat_mem_grade)
    (show (n : ParabolicInput Q Λ θ β N.carrier) ∈ ℳ d from hn)

end Unit

variable {N N' : Type} [AddCommGroup N] [Module k N] [Module (parabolicFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N] [AddCommGroup N'] [Module k N']
  [Module (parabolicFactorAlgebra Q Λ θ β) N'] [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N']

/-- The map of standardizations sends the identity shuffle on `n` to the identity shuffle on
`g n`. -/
theorem parabolicStandardMap_unit (g : N →ₗ[D] N') (n : N) :
    parabolicStandardMap Q Λ θ β g (parabolicStandardUnit Q Λ θ β N n) =
      parabolicStandardUnit Q Λ θ β N' (g n) :=
  rfl

/-- An isomorphism of modules over the factor algebras induces a `T^λ`-linear isomorphism of
standardizations. -/
def parabolicStandardEquiv (e : N ≃ₗ[D] N') :
    ParabolicStandardT Q Λ θ β N hQ ≃ₗ[T] ParabolicStandardT Q Λ θ β N' hQ :=
  LinearEquiv.ofBijective
    ({ toFun := parabolicStandardMap Q Λ θ β e.toLinearMap
       map_add' := map_add _
       map_smul' := fun t z => parabolicStandardMap_action Q Λ θ β hQ e.toLinearMap t z } :
      ParabolicStandardT Q Λ θ β N hQ →ₗ[T] ParabolicStandardT Q Λ θ β N' hQ)
    ⟨parabolicStandardMap_injective Q Λ θ β hQ _ e.injective,
      parabolicStandardMap_surjective Q Λ θ β hQ _ e.surjective⟩

theorem parabolicStandardEquiv_unit (e : N ≃ₗ[D] N') (n : N) :
    parabolicStandardEquiv Λ hQ e (parabolicStandardUnit Q Λ θ β N n) =
      parabolicStandardUnit Q Λ θ β N' (e n) :=
  rfl

section Layer

variable {t : Seq (stendhalWeight ℓ θ)} (ht : IsRedOrdered t) (u : Seq β)
  (X : GFin (tensorProductGrade (restrictRedGrading Q Λ G) θ))
  (Z : GFin (CycKLR.grade (restrictBlackGrading Q Λ G) (Λ (Fin.last ℓ)) β))
  (φ : KMod (k := k) (ModuleCat.of (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) θ)
    (leftStandard Q (Λ ∘ Fin.castSucc) t ht)) ≃ₗ[TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) θ]
      X.carrier)
  (g : KMod (k := k) (cycProj Q Λ β u) ≃ₗ[CycKLR k Q
    (fun i => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i) β] Z.carrier)

/-- The two-piece standard module `S_{t λ_{ℓ+1} u}` is the standardization of `X ⊠ Z` for
modules `X ≅ S_t` and `Z ≅ R^{λ_{ℓ+1}} e(u)`. -/
def twoPieceStandardLinearEquiv :
    leftStandard Q Λ (twoPieceLoading θ β t u) (isRedOrdered_twoPieceLoading ht u) ≃ₗ[T]
      (standardizationGFin Λ G θ β hQ (X.extTensor Z)).carrier :=
  (twoPieceStandardEquiv Q Λ ht u hQ).symm.trans
    (parabolicStandardEquiv Λ hQ (ExtTensor.congr (k := k) φ g))

theorem twoPieceStandardLinearEquiv_unit :
    twoPieceStandardLinearEquiv Λ G hQ ht u X Z φ g
        (leftStandardUnit Q Λ (twoPieceLoading θ β t u) (isRedOrdered_twoPieceLoading ht u)) =
      parabolicStandardUnit Q Λ θ β (X.extTensor Z).carrier
        (ExtTensor.tmul (φ (leftStandardUnit Q (Λ ∘ Fin.castSucc) t ht)) (g (cycUnit Q Λ u))) := by
  change parabolicStandardEquiv Λ hQ (ExtTensor.congr (k := k) φ g)
    ((twoPieceStandardEquiv Q Λ ht u hQ).symm _) = _
  rw [twoPieceStandardEquiv_symm_unit]
  rfl

/-- **The graded two-piece standard module** (Webster, arXiv:1309.3796v2, Definition 5.1 and
the standardization before Proposition 5.6): if `X ≅ S_t` and `Z ≅ R^{λ_{ℓ+1}} e(u)` send the
generators into degree zero, the graded left standard `S_{t λ_{ℓ+1} u}` is isomorphic to the
graded standardization of `X ⊠ Z`. -/
def twoPieceStandardGradedEquiv
    (hφ : φ (leftStandardUnit Q (Λ ∘ Fin.castSucc) t ht) ∈ X.grading 0)
    (hg : g (cycUnit Q Λ u) ∈ Z.grading 0) :
    gradedLeftStandard G (twoPieceLoading θ β t u) (isRedOrdered_twoPieceLoading ht u) ≃ᵍ[T]
      (standardizationGFin Λ G θ β hQ (X.extTensor Z)).grading :=
  let := (standardizationGFin Λ G θ β hQ (X.extTensor Z)).decomposition
  let := (standardizationGFin Λ G θ β hQ (X.extTensor Z)).gradedSMul
  leftStandardGradedEquiv G _ _ (twoPieceStandardLinearEquiv Λ G hQ ht u X Z φ g) (by
    rw [twoPieceStandardLinearEquiv_unit]
    exact parabolicStandardUnit_mem_standardization Λ G hQ (X.extTensor Z)
      ((zero_add (0 : ℤ)) ▸ tmul_mem_tensorGrading hφ hg))

end Layer

end Categorification.Stendhal

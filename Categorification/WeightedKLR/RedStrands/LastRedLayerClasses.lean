/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.AbsoluteSimple
import Categorification.WeightedKLR.RedStrands.LastRedLayerGrading

/-!
# Indecomposable classes in the source of a last-red layer

Webster, arXiv:1309.3796v2, §4.7, rank bound in Theorem 4.38. For Rouquier
parameters over a field, the indecomposable graded projectives, up to shift,
of the shorter tensor block tensored with the ordinary cyclotomic algebra
are indexed by pairs of indecomposable classes of the two factors.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR Categorification.Graded GProj
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type*} [DecidableEq I] [Field k] {ℓ : ℕ}
    {Q : I → I → MvPolynomial (Fin 2) k} {C : QuantumGroup.CartanDatum I}
    (hQ : IsRouquierQ C Q) (Λ : Fin ℓ → I →₀ ℕ) (θ : Multiset I)
    (μ : I →₀ ℕ) (β : Multiset I)
    (G : GradingDatum (stendhalQ Q Λ)) (H : GradingDatum Q)
local notation "λf" => (fun i : I => (Polynomial.X : Polynomial k) ^ μ i)
local notation "A" => TensorProductAlgebra k Q Λ θ
local notation "B" => CycKLR k Q λf β
local notation "Earlier" => tensorProductGrade G θ
local notation "Final" => CycKLR.grade H μ β
local notation "𝒜" => tensorGrading Earlier Final
local notation "singleRed" => (fun _ : Fin 1 => μ)
local notation "σ" => SingleRed.cyclotomicEquiv Q singleRed β

include hQ in
/-- The final cyclotomic factor is finite-dimensional over the parameter field. -/
theorem lastRedFinal_finite : Module.Finite k B := by
  let := tensorProductAlgebra_finite singleRed β hQ
  exact Module.Finite.of_surjective (σ).symm.toLinearMap (σ).symm.surjective

include hQ in
/-- The tensor-algebra source of the last-red layer is finite-dimensional. -/
theorem lastRedLayerSource_finite : Module.Finite k (A ⊗[k] B) := by
  let := tensorProductAlgebra_finite Λ θ hQ
  let := lastRedFinal_finite hQ μ β
  infer_instance

include hQ in
theorem lastRedLayerSource_hasGdim : HasGdim 𝒜 := by
  let := lastRedLayerSource_finite hQ Λ θ μ β
  exact HasGdim.of_finiteDimensional _

private theorem top_finite {D : Type*} [Ring D] [Algebra k D] [Module.Finite k D]
    {g : ℤ → Submodule k D} [GradedAlgebra g] [HasGdim g] (b : IndecClass g) : Module.Finite k b.top :=
  (IndecClass.isGradedSimple_top b).finiteDimensional (⊥ : Submodule k D)
    (fun x hx y => by rw [(Submodule.mem_bot k).mp hx,zero_smul])

include hQ in
/-- Every endomorphism of a simple module of the final cyclotomic factor is scalar. -/
theorem lastRedFinal_scalar {M : Type*} [AddCommGroup M] [Module k M] [Module B M]
    [IsScalarTower k B M] [IsSimpleModule B M] (f : M →ₗ[B] M) :
    ∃ c : k, ∀ x, f x = c • x := by
  let T := TensorProductAlgebra k Q singleRed β
  let φ : T →ₐ[k] B := (σ).symm.toAlgHom
  let : Module T M := Module.compHom M φ.toRingHom
  let : IsScalarTower k T M := ⟨fun c a x => by
    change φ (c • a) • x = c • (φ a • x)
    rw [map_smul, smul_assoc]⟩
  let : IsSimpleModule T M := isSimpleModule_iff_toSpanSingleton_surjective.mpr
    ⟨IsSimpleModule.nontrivial B M, by
      intro x hx y
      obtain ⟨b,hb⟩ := IsSimpleModule.toSpanSingleton_surjective B hx y
      obtain ⟨a,rfl⟩ := (σ).symm.surjective b
      exact ⟨a,hb⟩⟩
  let g : M →ₗ[T] M := ⟨⟨f,f.map_add⟩, fun t x => f.map_smul (φ t) x⟩
  exact exists_scalar_of_simple singleRed β hQ g

include hQ in
/-- The shift classes of indecomposable graded projectives of the tensor
algebra presenting a layer are indexed by the shift classes for the shorter
tensor algebra and the last-weight cyclotomic algebra (Webster,
arXiv:1309.3796v2, proof of Theorem 4.38). -/
def lastRedLayerSourceIndecClassEquiv : IndecClass 𝒜 ≃ IndecClass Earlier × IndecClass Final := by
  let := tensorProductAlgebra_finite Λ θ hQ
  let := lastRedFinal_finite hQ μ β
  let := lastRedLayerSource_finite hQ Λ θ μ β
  let := HasGdim.of_finiteDimensional Earlier
  let := HasGdim.of_finiteDimensional Final
  apply TensorK0Hyp.indecClassEquiv
  refine ⟨fun b => top_finite b, fun b => top_finite b, ?_, ?_, fun b => top_finite b⟩
  · intro b f
    let := top_finite b
    let := (IndecClass.isGradedSimple_top b).isSimpleModule
    obtain ⟨c,hc⟩ := exists_scalar_of_simple Λ θ hQ f
    exact ⟨c,LinearMap.ext hc⟩
  · intro b f
    let := top_finite b
    let := (IndecClass.isGradedSimple_top b).isSimpleModule
    obtain ⟨c,hc⟩ := lastRedFinal_scalar hQ μ β f
    exact ⟨c,LinearMap.ext hc⟩

end Categorification.Stendhal

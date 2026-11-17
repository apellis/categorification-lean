/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorFinite
import Categorification.KLR.TensorKLRK0
import Categorification.KLR.SymmetricFactorization

/-!
# Absolute irreducibility for the tensor product algebra

Webster, arXiv:1309.3796v2, proof of Lemma 4.37, uses a tensor product of
primitive corners. Over an arbitrary field the residue division algebras
matter. Restriction along the ordinary affine KLR cover identifies the
endomorphisms of a simple red module with the endomorphisms in KL I,
arXiv:0803.4121v2, Corollary 3.19. All affine dots act nilpotently.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR KLRAlgebra Categorification.Graded
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type*} [DecidableEq I] [Field k] {ℓ : ℕ}
    {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin ℓ → I →₀ ℕ) (ν : Multiset I)
    {C : QuantumGroup.CartanDatum I} (hQ : IsRouquierQ C Q)
local notation "T" => TensorProductAlgebra k Q Λ ν
local notation "Aff" => KLRAlgebra k (affineCoverQ Q Λ) (stendhalWeight ℓ ν)
local notation "π" => affineTensorProjection (Q := Q) Λ ν

include hQ in
/-- Every endomorphism of a simple module over the ordered violating quotient
is scalar over the given coefficient field. -/
theorem exists_scalar_of_simple {M : Type*} [AddCommGroup M] [Module k M] [Module T M]
    [IsScalarTower k T M] [IsSimpleModule T M] (f : M →ₗ[T] M) :
    ∃ c : k, ∀ v : M, f v = c • v := by
  classical
  let := tensorProductAlgebra_finite Λ ν hQ
  let : Nontrivial M := IsSimpleModule.nontrivial T M
  obtain ⟨v, hv⟩ := exists_ne (0 : M)
  let : Module.Finite k M := Module.Finite.of_surjective
    ((LinearMap.toSpanSingleton T M v).restrictScalars k) (IsSimpleModule.toSpanSingleton_surjective T hv)
  let : Module Aff M := Module.compHom M (π).toRingHom
  let : IsScalarTower k Aff M := ⟨fun c a u => by
    change π (c • a) • u = c • (π a • u)
    rw [map_smul, smul_assoc]⟩
  let : IsSimpleModule Aff M := isSimpleModule_iff_toSpanSingleton_surjective.mpr ⟨inferInstance, by
    intro m hm y
    obtain ⟨b, hb⟩ := IsSimpleModule.toSpanSingleton_surjective T hm y
    obtain ⟨r, rfl⟩ := affineTensorProjection_surjective (Q := Q) Λ ν b
    exact ⟨r, hb⟩⟩
  have hnil (a : Fin (stendhalWeight ℓ ν).card) : SmulNilpotent (x a : Aff) M := by
    obtain ⟨n, hn⟩ := tensorProjection_dot_nilpotent Λ ν hQ a
    exact ⟨n, fun u => show π ((x a : Aff) ^ n) • u = 0 by rw [map_pow, hn, zero_smul]⟩
  let g : M →ₗ[Aff] M :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun a u => f.map_smul (π a) u }
  have hs := affineCoverQ_symm Λ (fun i j hij => (hQ.symm i j hij).symm)
  have hn := affineCoverQ_ne_zero (Q := Q) Λ (fun i j hij hz => by
    have u := hQ.unit_coeff i j hij
    simp [hz] at u)
  exact KLRAlgebra.exists_eq_smul_of_isSimpleModule (symmP_factor _ hs) (symmP_ne_zero _ hn) hnil g

section External

open GProj
open scoped TensorProduct

private theorem top_finite {B : Type*} [Ring B] [Algebra k B] [Module.Finite k B]
    {ℬ : ℤ → Submodule k B} [GradedAlgebra ℬ] [HasGdim ℬ] (b : IndecClass ℬ) :
    Module.Finite k b.top :=
  (IndecClass.isGradedSimple_top b).finiteDimensional (⊥ : Submodule k B)
    (fun a ha m => by rw [(Submodule.mem_bot k).mp ha, zero_smul])

variable {ℓ' : ℕ} (Λ' : Fin ℓ' → I →₀ ℕ) (ν' : Multiset I)
  (G : GradingDatum (stendhalQ Q Λ)) (G' : GradingDatum (stendhalQ Q Λ'))
local notation "𝒜" => tensorProductGrade G ν
local notation "ℬ" => tensorProductGrade G' ν'

include hQ in
/-- The external product identifies the integral graded projective group for
two independent red blocks with the tensor product of their projective groups.
This supplies the splitness required for last-red strata over an arbitrary field. -/
def blocksK0Equiv : K0 𝒜 ⊗[LaurentPolynomial ℤ] K0 ℬ ≃ₗ[LaurentPolynomial ℤ]
    K0 (tensorGrading 𝒜 ℬ) := by
  let := tensorProductAlgebra_finite Λ ν hQ
  let := tensorProductAlgebra_finite Λ' ν' hQ
  let := HasGdim.of_finiteDimensional 𝒜
  let := HasGdim.of_finiteDimensional ℬ
  apply TensorK0Hyp.extTensorEquiv
  refine ⟨fun b => top_finite b, fun b => top_finite b, ?_, ?_, fun b => top_finite b⟩
  · intro b f
    let := top_finite b
    let := (IndecClass.isGradedSimple_top b).isSimpleModule
    obtain ⟨c, hc⟩ := exists_scalar_of_simple Λ ν hQ f
    exact ⟨c, LinearMap.ext hc⟩
  · intro b f
    let := top_finite b
    let := (IndecClass.isGradedSimple_top b).isSimpleModule
    obtain ⟨c, hc⟩ := exists_scalar_of_simple Λ' ν' hQ f
    exact ⟨c, LinearMap.ext hc⟩

/-- The external product sends a pure tensor to the class obtained by tensoring
the projectives over the coefficient field. -/
@[simp] theorem blocksK0Equiv_tmul (u : K0 𝒜) (v : K0 ℬ) :
    blocksK0Equiv Λ ν hQ Λ' ν' G G' (u ⊗ₜ v) = K0.extTensor 𝒜 ℬ u v := by

  let := tensorProductAlgebra_finite Λ ν hQ
  let := tensorProductAlgebra_finite Λ' ν' hQ
  let := HasGdim.of_finiteDimensional 𝒜
  let := HasGdim.of_finiteDimensional ℬ
  unfold blocksK0Equiv
  apply TensorK0Hyp.extTensorEquiv_tmul

end External

end Categorification.Stendhal

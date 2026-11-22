/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.AbsoluteSimple
import Categorification.WeightedKLR.RedStrands.BoundaryHomReflection
import Categorification.Algebra.TwistedVectorDual
import Categorification.KLR.Crystal.ProportionalCharacter

/-!
# Self-duality of simple modules over the tensor product algebra

Webster, arXiv:1309.3796v2, Proposition 5.11: every simple module `L` over the tensor product
algebra `T^λ` is isomorphic to its dual `L⋆`, the `k`-dual of `L` with the action twisted by
the anti-automorphism `tensorReflect` reflecting diagrams.

Webster's proof compares the characters `dim e(s) L` and uses the uniqueness of simple modules
with given character. Here the comparison is made after restriction along the affine KLR cover
`affineTensorProjection`: the reflection fixes each idempotent `e(s)`, so `L` and `L⋆` have the
same KLR character (`TwistDual.finrank_idemSubspace`), and Khovanov–Lauda, arXiv:0803.4121v2,
Theorem 3.17 (`KLRAlgebra.nonempty_equiv_of_dimCh_proportional`) identifies them.

The statement is ungraded. Webster's grading of `L⋆` and the grading shift of the isomorphism
are not covered here.
-/

set_option backward.isDefEq.respectTransparency false

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

omit [DecidableEq I] in
/-- The fixed subspace of `0` is zero. -/
theorem fixSub_zero {A P : Type*} [Ring A] [Algebra k A] [AddCommGroup P] [Module k P]
    [Module A P] [IsScalarTower k A P] : fixSub k P (0 : A) = ⊥ := by
  ext m
  simp [mem_fixSub, eq_comm]

/-- The affine projection of `1_s` for a red-ordered sequence `s`. -/
theorem affineTensorProjection_e_ordered (s : Seq (stendhalWeight ℓ ν)) (hs : IsRedOrdered s) :
    π (KLRAlgebra.e s) = TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e s hs) := by
  change TensorProductAlgebra.mk Q Λ ν (orderProjection Q Λ ν (affineCover Q Λ ν _)) = _
  rw [affineCover_e]
  exact congrArg _ (Subtype.ext ((StendhalAlgebraAllOrders.e_mul_redOrderedIdem s).trans
    (ite_eq_left hs)))

/-- The affine projection of `1_s` vanishes for a sequence `s` that is not red-ordered. -/
theorem affineTensorProjection_e_not_ordered (s : Seq (stendhalWeight ℓ ν))
    (hs : ¬ IsRedOrdered s) : π (KLRAlgebra.e s) = 0 := by
  change TensorProductAlgebra.mk Q Λ ν (orderProjection Q Λ ν (affineCover Q Λ ν _)) = _
  rw [affineCover_e]
  have : orderProjection Q Λ ν (StendhalAlgebraAllOrders.e s) = 0 :=
    Subtype.ext ((StendhalAlgebraAllOrders.e_mul_redOrderedIdem s).trans (ite_eq_right hs))
  rw [this, map_zero]

include hQ in
/-- A simple module over the tensor product algebra is finite-dimensional. -/
theorem finite_of_isSimpleModule {P : Type*} [AddCommGroup P] [Module k P] [Module T P]
    [IsScalarTower k T P] [IsSimpleModule T P] : Module.Finite k P := by
  let := tensorProductAlgebra_finite Λ ν hQ
  have : Nontrivial P := IsSimpleModule.nontrivial T P
  obtain ⟨v, hv⟩ := exists_ne (0 : P)
  exact Module.Finite.of_surjective ((LinearMap.toSpanSingleton T P v).restrictScalars k)
    (IsSimpleModule.toSpanSingleton_surjective T hv)

/-- Restriction of a simple module along the affine KLR cover is simple. -/
theorem isSimpleModule_compHom {P : Type*} [AddCommGroup P] [Module T P] [IsSimpleModule T P] :
    @IsSimpleModule Aff _ P _ (Module.compHom P (π).toRingHom) := by
  let : Module Aff P := Module.compHom P (π).toRingHom
  refine isSimpleModule_iff_toSpanSingleton_surjective.mpr ⟨?_, ?_⟩
  · have := IsSimpleModule.nontrivial T P
    infer_instance
  · intro m hm y
    obtain ⟨b, hb⟩ := IsSimpleModule.toSpanSingleton_surjective T hm y
    obtain ⟨r, rfl⟩ := affineTensorProjection_surjective (Q := Q) Λ ν b
    exact ⟨r, hb⟩

include hQ in
/-- The dots of the affine KLR cover act nilpotently on every module over the tensor product
algebra. -/
theorem smulNilpotent_compHom (P : Type*) [AddCommGroup P] [Module T P]
    (a : Fin (stendhalWeight ℓ ν).card) :
    @SmulNilpotent Aff _ (x a : Aff) P _ (Module.compHom P (π).toRingHom) := by
  obtain ⟨n, hn⟩ := tensorProjection_dot_nilpotent Λ ν hQ a
  exact ⟨n, fun u => show π ((x a : Aff) ^ n) • u = 0 by rw [map_pow, hn, zero_smul]⟩

universe u

include hQ in
/-- Simple modules over the tensor product algebra with the same dimensions
`dim π(1_s) M` for all sequences `s` are isomorphic. -/
theorem nonempty_equiv_of_finrank_fixSub_eq {M N : Type u}
    [AddCommGroup M] [Module k M] [Module T M] [IsScalarTower k T M] [IsSimpleModule T M]
    [AddCommGroup N] [Module k N] [Module T N] [IsScalarTower k T N] [IsSimpleModule T N]
    (h : ∀ s : Seq (stendhalWeight ℓ ν), Module.finrank k (fixSub k M (π (KLRAlgebra.e s))) =
      Module.finrank k (fixSub k N (π (KLRAlgebra.e s)))) :
    Nonempty (M ≃ₗ[T] N) := by
  classical
  have := finite_of_isSimpleModule Λ ν hQ (P := M)
  have := finite_of_isSimpleModule Λ ν hQ (P := N)
  let : Module Aff M := Module.compHom M (π).toRingHom
  let : Module Aff N := Module.compHom N (π).toRingHom
  have : IsScalarTower k Aff M := ⟨fun c a u => by
    change π (c • a) • u = c • (π a • u)
    rw [map_smul, smul_assoc]⟩
  have : IsScalarTower k Aff N := ⟨fun c a u => by
    change π (c • a) • u = c • (π a • u)
    rw [map_smul, smul_assoc]⟩
  have := isSimpleModule_compHom (Q := Q) Λ ν (P := M)
  have := isSimpleModule_compHom (Q := Q) Λ ν (P := N)
  have hs := affineCoverQ_symm Λ (fun i j hij => (hQ.symm i j hij).symm)
  have hn := affineCoverQ_ne_zero (Q := Q) Λ (fun i j hij hz => by
    have u := hQ.unit_coeff i j hij
    simp [hz] at u)
  obtain ⟨φ⟩ := KLRAlgebra.nonempty_equiv_of_dimCh_proportional (L := M) (L' := N)
    (symmP_factor _ hs) (symmP_ne_zero _ hn) (smulNilpotent_compHom Λ ν hQ M)
    (smulNilpotent_compHom Λ ν hQ N) (m := 1) (n := 1) one_ne_zero
    (fun s => by rw [one_mul, one_mul]; exact h s)
  refine ⟨{ φ.toAddEquiv with map_smul' := fun t u => ?_ }⟩
  obtain ⟨r, rfl⟩ := affineTensorProjection_surjective (Q := Q) Λ ν t
  exact φ.map_smul r u

include hQ in
/-- **Webster, arXiv:1309.3796v2, Proposition 5.11** (ungraded): every simple module over the
tensor product algebra is isomorphic to its dual, twisted by the reflection `tensorReflect`. -/
theorem nonempty_equiv_twistDual {L : Type*} [AddCommGroup L] [Module k L] [Module T L]
    [IsScalarTower k T L] [IsSimpleModule T L] :
    Nonempty (L ≃ₗ[T] TwistDual (tensorReflect (Q := Q) (Λ := Λ) (ν := ν)) L) := by
  classical
  let τ := tensorReflect (Q := Q) (Λ := Λ) (ν := ν)
  have hτ : ∀ a, (τ (τ a).unop).unop = a := unop_tensorReflect_unop_tensorReflect
  have := finite_of_isSimpleModule Λ ν hQ (P := L)
  have := TwistDual.isSimpleModule τ (M := L) hτ
  have := TwistDual.isSimpleModule τ (M := TwistDual τ L) hτ
  -- the twisted dual and its twisted dual lie in the same universe
  obtain ⟨φ⟩ := nonempty_equiv_of_finrank_fixSub_eq Λ ν hQ
    (M := TwistDual τ (TwistDual τ L)) (N := TwistDual τ L) fun s => by
    by_cases ho : IsRedOrdered s
    · rw [affineTensorProjection_e_ordered Λ ν s ho]
      exact TwistDual.finrank_idemSubspace τ (isIdempotentElem_mk_e s ho)
        (unop_tensorReflect_e s ho)
    · rw [affineTensorProjection_e_not_ordered Λ ν s ho]
      rw [fixSub_zero, fixSub_zero, finrank_bot, finrank_bot]
  exact ⟨(TwistDual.doubleDualEquiv τ hτ).trans φ⟩

end Categorification.Stendhal

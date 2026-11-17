/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackInduction
import Categorification.WeightedKLR.RedStrands.TensorFinite
import Categorification.WeightedKLR.RedStrands.Vacuum
import Categorification.Algebra.Graded.HomForm
import Categorification.WeightedKLR.Induction.Restriction

/-!
# Restriction along a rightmost black strand

Webster, arXiv:1309.3796v2, Definition 4.30 and Lemmas 4.35–4.36.
The homogeneous idempotent selecting a terminal black strand acts on every
graded module. Its image is restriction to the lower weight.
-/
noncomputable section
namespace Categorification.Stendhal
open KLR KLRAlgebra Categorification.Graded MulOpposite
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
variable {I k : Type*} [DecidableEq I] [Field k] {ℓ : ℕ}
    {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} (i : I) (ν : Multiset I)
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "T" => TensorProductAlgebra k Q Λ ν
local notation "T'" => TensorProductAlgebra k Q Λ νᵢ
local notation "φ" => appendBlack Q Λ i ν
local notation "Mc" => InductionAlong.Corner (φ : T →ₙ+* T')

/-- The fixed subspace of the idempotent for a terminal black strand of colour `i`. -/
abbrev BlackRes (M : Type*) [AddCommGroup M] [Module k M] [Module T' M] [IsScalarTower k T' M] :=
  ↥(fixSub k M (φ 1))

variable (M : Type*) [AddCommGroup M] [Module k M]
  [Module (TensorProductAlgebra k Q Λ (({i} : Multiset I) + ν)) M]
  [IsScalarTower k (TensorProductAlgebra k Q Λ (({i} : Multiset I) + ν)) M]
instance blackResModule : Module T (BlackRes (Q := Q) (Λ := Λ) i ν M) where
  smul r z := ⟨φ r • z.1, by
    change φ 1 • (φ r • z.1) = φ r • z.1
    rw [smul_smul, ← map_mul, one_mul]⟩
  one_smul z := Subtype.ext z.2
  mul_smul r s z := Subtype.ext (by
    change φ (r * s) • z.1 = φ r • (φ s • z.1)
    rw [map_mul, mul_smul])
  smul_zero r := Subtype.ext (smul_zero _)
  smul_add r z w := Subtype.ext (smul_add _ _ _)
  add_smul r s z := Subtype.ext (by
    change φ (r + s) • z.1 = φ r • z.1 + φ s • z.1
    rw [map_add, add_smul])
  zero_smul z := Subtype.ext (by change φ 0 • z.1 = 0; rw [map_zero, zero_smul])

instance blackResTower : IsScalarTower k T (BlackRes (Q := Q) (Λ := Λ) i ν M) where
  smul_assoc c r z := Subtype.ext (by
    change φ (c • r) • z.1 = c • (φ r • z.1)
    rw [map_smul, smul_assoc])

variable (G : GradingDatum (stendhalQ Q Λ))
local notation "src" => tensorProductGrade G ν
local notation "dst" => tensorProductGrade G νᵢ

/-- Raw graded restriction, defined on every module without assuming preservation of projectives. -/
def blackResMod (V : GMod dst) : GMod src where
  carrier := BlackRes (Q := Q) (Λ := Λ) i ν V.carrier
  module := blackResModule i ν V.carrier
  isScalarTower := blackResTower i ν V.carrier
  grading := idem V.grading (φ 1)
  decomposition := idemDecomposition V.grading (appendBlack_mem_grade Q Λ i ν G SetLike.GradedOne.one_mem)
  gradedSMul := ⟨fun _ _ _ _ hr hz =>
    SetLike.GradedSMul.smul_mem (A := dst) (B := V.grading) (appendBlack_mem_grade Q Λ i ν G hr) hz⟩

/-- Finite generation of right black restriction over the lower tensor product algebra
for all finite-dimensional tensor product modules (Webster, §4.6). -/
theorem finite_blackRes (C : QuantumGroup.CartanDatum I) (hQ : IsRouquierQ C Q)
    [Module.Finite T' M] : Module.Finite T (BlackRes (Q := Q) (Λ := Λ) i ν M) := by
  let := tensorProductAlgebra_finite Λ νᵢ hQ
  have : Module.Finite k M := Module.Finite.trans T' M
  exact Module.Finite.of_restrictScalars_finite k T (BlackRes (Q := Q) (Λ := Λ) i ν M)

/-- To check preservation of projectives on any edge, it suffices to check the
right-black cut of the upper regular module, since every finitely generated
projective is a retract of a finite sum of regular modules
(Webster, arXiv:1309.3796v2, §4.6 and Lemma 4.35). -/
theorem projective_blackRes_of_regular [Module.Finite T' M] [Module.Projective T' M]
    (h : Module.Projective T (BlackRes (Q := Q) (Λ := Λ) i ν T')) :
    Module.Projective T (BlackRes (Q := Q) (Λ := Λ) i ν M) := by
  let : Module.Projective T (InductionAlong.Res (φ : T →ₙ+* T') T') := h
  exact InductionAlong.Res.projective_of_regular (φ : T →ₙ+* T') M

/-- On the edge from one black strand to the vacuum, restriction is projective for
any finite ordered red family, since the vacuum algebra is the ground field
(Webster, arXiv:1309.3796v2, proof of Lemma 4.36). -/
theorem projective_blackRes_zero (M : Type*) [AddCommGroup M] [Module k M]
    [Module (TensorProductAlgebra k Q Λ (({i} : Multiset I) + 0)) M]
    [IsScalarTower k (TensorProductAlgebra k Q Λ (({i} : Multiset I) + 0)) M] :
    Module.Projective (TensorProductAlgebra k Q Λ 0) (BlackRes (Q := Q) (Λ := Λ) i 0 M) := by
  let σ := tensorProductAlgebraZeroEquiv (k := k) Q Λ
  let σr := σ.toRingEquiv
  let := RingHomInvPair.of_ringEquiv σr
  let := RingHomInvPair.of_ringEquiv_symm σr
  let e : BlackRes (Q := Q) (Λ := Λ) i 0 M ≃ₛₗ[(σr : TensorProductAlgebra k Q Λ 0 →+* k)] BlackRes (Q := Q) (Λ := Λ) i 0 M :=
    { Equiv.refl _ with
      map_add' := fun _ _ => rfl
      map_smul' := fun r z => by
        change r • z = σ r • z
        obtain ⟨c, rfl⟩ := σ.symm.surjective r
        have hc : σ.symm c = c • 1 := by
          apply σ.injective
          rw [σ.apply_symm_apply, map_smul, map_one, smul_eq_mul, mul_one]
        rw [hc, smul_assoc, one_smul]
        exact congrArg (fun a : k => a • z) (show c = σ (c • 1) by simp) }
  exact Module.Projective.of_equiv e.symm

/-- Right black restriction to the vacuum as a finitely generated graded projective. -/
def blackResVacuumProj (C : QuantumGroup.CartanDatum I) (hQ : IsRouquierQ C Q)
    (V : GProj (tensorProductGrade G (({i} : Multiset I) + 0))) : GProj (tensorProductGrade G 0) where
  __ := blackResMod i 0 G V.toGMod
  finite := finite_blackRes i 0 V.carrier C hQ
  projective := projective_blackRes_zero i V.carrier

end Categorification.Stendhal

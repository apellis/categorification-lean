/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackRestriction

/-!
# Graded Hom spaces under right black induction and restriction

Webster, arXiv:1309.3796v2, Definition 4.30 and the induction on the number
of black strands in Lemma 4.36. Graded Hom out of the induced projective is
computed in the lower-weight category by the raw idempotent restriction.
-/
noncomputable section
namespace Categorification.Stendhal
open KLR KLRAlgebra Categorification.Graded MulOpposite
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
variable {I k : Type*} [DecidableEq I] [Field k] {ℓ : ℕ}
    {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}
    (G : GradingDatum (stendhalQ Q Λ)) (i : I) (ν : Multiset I)
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "src" => tensorProductGrade G ν
local notation "dst" => tensorProductGrade G νᵢ
local notation "T" => TensorProductAlgebra k Q Λ ν
local notation "T'" => TensorProductAlgebra k Q Λ νᵢ
local notation "φ" => appendBlack Q Λ i ν
local notation "Mc" => InductionAlong.Corner (φ : T →ₙ+* T')
local notation "gen" => InductionAlong.unitGen (φ : T →ₙ+* T')
local notation "cor" => Graded.submodule dst (lIdeal (φ 1))
private local instance blackTower : IsScalarTower k T' Mc where
  smul_assoc c a z := Subtype.ext (smul_mul_assoc c a z.val)

private local instance : IsScalarTower k Tᵐᵒᵖ Mc where
  smul_assoc c r z := Subtype.ext (by
    change z.val * φ (c • r.unop) = c • (z.val * φ r.unop)
    rw [map_smul, mul_smul_comm])

private theorem generator_fixed : φ 1 • gen = gen := Subtype.ext (InductionAlong.unit_mul_unit (φ : T →ₙ+* T'))
private theorem generator_balance (r : T) : op r • gen = φ r • gen := by
  apply Subtype.ext
  change φ 1 * φ r = φ r * φ 1
  rw [← map_mul, ← map_mul, one_mul, mul_one]

variable (P : GProj (tensorProductGrade G ν)) (V : GMod (tensorProductGrade G (({i} : Multiset I) + ν)))
local notation "Ind" => BalancedTensor k T' T Mc P.carrier
local notation "Res" => BlackRes (Q := Q) (Λ := Λ) i ν V.carrier

private def homToRes (f : Ind →ₗ[T'] V.carrier) : P.carrier →ₗ[T] Res where
  toFun n := ⟨f (BalancedTensor.tmul (gen) n), by
    change φ 1 • f _ = f _
    rw [← map_smul, BalancedTensor.smul_tmul', generator_fixed]⟩
  map_add' n n' := Subtype.ext (by simp only [BalancedTensor.tmul_add, map_add, Submodule.coe_add])
  map_smul' r n := Subtype.ext (by
    change f (BalancedTensor.tmul (gen) (r • n)) =
      φ r • f (BalancedTensor.tmul (gen) n)
    rw [← BalancedTensor.op_smul_tmul, generator_balance,
      ← BalancedTensor.smul_tmul', map_smul])

private theorem homToRes_val (f : Ind →ₗ[T'] V.carrier) (n : P.carrier) :
    (homToRes G i ν P V f n).1 = f (BalancedTensor.tmul (gen) n) := rfl

/-- Coefficients act on the left, in their original noncommutative order. -/
private def homFromResBil (g : P.carrier →ₗ[T] Res) : Mc →ₗ[k] P.carrier →ₗ[k] V.carrier :=
  LinearMap.mk₂ k (fun z n => z.1 • (g n).1)
    (fun z w n => by simp only [Submodule.coe_add, add_smul])
    (fun c z n => by
      change (c • z.1) • (g n).1 = c • (z.1 • (g n).1)
      rw [smul_assoc])
    (fun z n n' => by simp only [map_add, Submodule.coe_add, smul_add])
    (fun c z n => by
      rw [LinearMap.map_smul_of_tower, Submodule.coe_smul, smul_comm])

/-- The inverse map descends `z ⊗ n ↦ z • g(n)` through actual right balancing. -/
private def homFromRes (g : P.carrier →ₗ[T] Res) : Ind →ₗ[T'] V.carrier :=
  BalancedTensor.liftB (homFromResBil G i ν P V g)
    (fun z r n => by
      change (z.1 * φ r) • (g n).1 = z.1 • (g (r • n)).1
      rw [map_smul]
      exact mul_smul _ _ _)
    (fun s z n => mul_smul s z.1 (g n).1)

private theorem homFromRes_tmul (g : P.carrier →ₗ[T] Res)
    (z : Mc) (n : P.carrier) :
    homFromRes G i ν P V g (BalancedTensor.tmul z n) = z.1 • (g n).1 := rfl

private theorem homFromRes_homToRes (f : Ind →ₗ[T'] V.carrier) :
    homFromRes G i ν P V (homToRes G i ν P V f) = f :=
  BalancedTensor.extB fun z n => by
    rw [homFromRes_tmul, homToRes_val, ← map_smul, BalancedTensor.smul_tmul']
    congr 2
    exact Subtype.ext z.2

private theorem homToRes_homFromRes (g : P.carrier →ₗ[T] Res) :
    homToRes G i ν P V (homFromRes G i ν P V g) = g :=
  LinearMap.ext fun n => Subtype.ext (by
    rw [homToRes_val, homFromRes_tmul]
    exact (g n).2)

/-- Frobenius reciprocity in degree `d` with unshifted restriction. -/
def homGrade_blackInd_blackRes (d : ℤ) :
    homGrade T' (blackIndProj G i ν P).grading V.grading d ≃ₗ[k]
      homGrade T P.grading (blackResMod i ν G V).grading d where
  toFun f := ⟨homToRes G i ν P V f.1, by
    intro j n hn
    have he : gen ∈ cor 0 :=
      appendBlack_mem_grade Q Λ i ν G SetLike.GradedOne.one_mem
    have ht := @tmul_mem_balancedGrading ℤ _ k T' T Mc P.carrier _ _ _ _ _ _ _
      (blackTower (Q := Q) (Λ := Λ) i ν) _ _ _ _ cor P.grading _ _ _ _ he hn
    rw [zero_add] at ht
    change f.1 (BalancedTensor.tmul (gen) n) ∈ V.grading (j + d)
    exact f.2 (e := j) ht⟩
  invFun g := ⟨homFromRes G i ν P V g.1, by
    intro e y hy
    apply @balancedGrading_map_mem ℤ _ k T' T Mc P.carrier _ _ _ _ _ _ _
      (blackTower (Q := Q) (Λ := Λ) i ν) _ _ _ _ cor P.grading _ _ _
      (fun j => V.grading (j+d)) ((homFromRes G i ν P V g.1).restrictScalars k) _ e y hy
    intro j l r n hr hn
    have h₁ : (g.1 n).1 ∈ V.grading (l+d) := g.2 hn
    have h₂ := SetLike.GradedSMul.smul_mem (A := dst) (B := V.grading)
      (show r.1 ∈ dst j from hr) h₁
    change r.1 • (g.1 n).1 ∈ V.grading ((j+l)+d)
    simpa only [vadd_eq_add,add_assoc] using h₂⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := Subtype.ext (homFromRes_homToRes G i ν P V f.1)
  right_inv g := Subtype.ext (homToRes_homFromRes G i ν P V g.1)

end Categorification.Stendhal

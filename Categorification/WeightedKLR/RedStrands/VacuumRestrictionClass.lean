/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.HomFormPolynomial
import Categorification.WeightedKLR.RedStrands.BlackFrobenius
import Categorification.WeightedKLR.RedStrands.VacuumK0

/-!
# The right-black restriction class in the vacuum block

Webster, arXiv:1309.3796v2, §4.6, Definition 4.30 and §4.7, proof of
Lemma 4.36. The vacuum block is the ground field. Unshifted restriction to
this block has class given by the graded Hom polynomial from the terminal
black projective.
-/

noncomputable section

namespace Categorification.Stendhal

open Categorification.Graded KLR

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type*} [DecidableEq I] [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}
  (G : GradingDatum (stendhalQ Q Λ)) (i : I)

local notation "A" => TensorProductAlgebra k Q Λ (0 : Multiset I)
local notation "B" => TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + 0)
local notation "src" => tensorProductGrade G (0 : Multiset I)
local notation "dst" => tensorProductGrade G ((Singleton.singleton i : Multiset I) + 0)
local notation "reg" => GProj.regular src

private def vacuumHomGrade (W : GProj src) (d : ℤ) :
    homGrade A src W.grading d ≃ₗ[k] W.grading d where
  toFun f := ⟨f.1 1, by simpa using (mem_homGrade.mp f.2) (SetLike.one_mem_graded src)⟩
  invFun w := ⟨LinearMap.toSpanSingleton A W.carrier w,
    mem_homGrade.mpr fun _ _ ha => by
      let := W.gradedSMul
      exact SetLike.GradedSMul.smul_mem ha w.2⟩
  left_inv f := Subtype.ext (LinearMap.ext fun a => by
    change a • f.1 1 = f.1 a
    rw [← map_smul, smul_eq_mul, mul_one])
  right_inv w := Subtype.ext (one_smul A (w : W.carrier))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem vacuum_gdim [HasGdim src] : gdim src = 1 := by
  let e := (tensorProductAlgebraZeroEquiv Q Λ).symm
  ext d
  rw [coeff_gdim, HahnSeries.coeff_one]
  by_cases hd : d = 0
  · subst d
    have htop : src 0 = ⊤ := eq_top_iff.mpr fun a _ => mem_scalarGrade src e a
    rw [htop]
    have h := e.toLinearEquiv.finrank_eq
    simp [← h]
  · have hbot : src d = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro a ha
      by_contra hne
      exact hd (DirectSum.degree_eq_of_mem_mem src ha (mem_scalarGrade src e a) hne)
    simp [hd, hbot]

private theorem vacuum_class_series [Module.Finite k A] [HasGdim src] (W : GProj src) :
    toLaurentSeries (tensorProductVacuumK0Equiv G (K0.of W)) =
      K0.homForm src (K0.of reg) (K0.of W) := by
  let v := tensorProductVacuumK0Equiv G (K0.of W)
  have hv : K0.of W = v • K0.of reg := by
    apply (tensorProductVacuumK0Equiv G).injective
    simp [v]
  calc
    _ = toLaurentSeries v * K0.homForm src (K0.of reg) (K0.of reg) := by
      rw [K0.homForm_of]
      have h := (gdim_eq_of_finrank_eq fun d => (vacuumHomGrade G reg d).finrank_eq)
      change GProj.homGdim reg reg = gdim src at h
      rw [h, vacuum_gdim, mul_one]
    _ = _ := by
      conv_rhs => rw [hv]
      exact (K0.map_smul_of_T (F := K0.homForm src (K0.of reg))
        (fun a x => K0.homForm_T_smul_right a (K0.of reg) x) v (K0.of reg)).symm

/-- The class of raw restriction to the vacuum is the Hom polynomial from the
induced vacuum projective to the original projective. -/
theorem tensorProductVacuumK0Equiv_blackResVacuumProj
    (C : QuantumGroup.CartanDatum I) (hQ : IsRouquierQ C Q)
    (V : GProj dst) :
    tensorProductVacuumK0Equiv G (K0.of (blackResVacuumProj i G C hQ V)) =
      gdimPoly (homGrade B (blackIndProj G i 0 reg).grading V.grading) := by
  let := tensorProductAlgebra_finite Λ (0 : Multiset I) hQ
  let := tensorProductAlgebra_finite Λ ((Singleton.singleton i : Multiset I) + 0) hQ
  let := HasGdim.of_finiteDimensional src
  let W := blackResVacuumProj i G C hQ V
  apply toLaurentSeries_injective
  rw [vacuum_class_series G W, K0.homForm_of, GProj.toLaurentSeries_homGdimPoly]
  exact gdim_eq_of_finrank_eq fun d => (homGrade_blackInd_blackRes G i 0 reg V.toGMod d).finrank_eq.symm

/-- Replace the induced vacuum projective by the left ideal of the
terminal-black cut. -/
theorem tensorProductVacuumK0Equiv_blackResVacuumProj_eq_homGdimPoly
    (C : QuantumGroup.CartanDatum I) (hQ : IsRouquierQ C Q)
    (V : GProj dst) :
    let e := appendBlack Q Λ i 0 1
    let P := GProj.ofIdempotent e
      (InductionAlong.unit_mul_unit (appendBlack Q Λ i 0 : A →ₙ+* B))
      (appendBlack_mem_grade Q Λ i 0 G SetLike.GradedOne.one_mem)
    tensorProductVacuumK0Equiv G (K0.of (blackResVacuumProj i G C hQ V)) =
      gdimPoly (homGrade B P.grading V.grading) := by
  let := tensorProductAlgebra_finite Λ ((Singleton.singleton i : Multiset I) + 0) hQ
  let := HasGdim.of_finiteDimensional dst
  intro e P
  rw [tensorProductVacuumK0Equiv_blackResVacuumProj G i C hQ]
  apply toLaurentSeries_injective
  rw [GProj.toLaurentSeries_homGdimPoly, GProj.toLaurentSeries_homGdimPoly,
    ← K0.homForm_of, ← K0.homForm_of, ← show blackIndK0 G i 0 (K0.of reg) = K0.of P
      from blackIndK0_regular G i 0, blackIndK0_of]

end Categorification.Stendhal

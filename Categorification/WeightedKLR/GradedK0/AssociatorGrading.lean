/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.GradedK0.Associativity
import Categorification.WeightedKLR.GradedK0.AssociatorTensors
import Categorification.WeightedKLR.GradedK0.ResIndChainGrading

/-!
# The graded associator for weighted induction

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4,
§2.4, Definition 2.17 and Theorem 2.19. The associator on pure tensors moves
the left inner coefficient to the outside through the juxtaposition map and
uses degree-zero idempotents on the right. This proves the degree preservation
needed for associativity of graded Grothendieck group multiplication.
-/

noncomputable section

namespace Categorification.WeightedKLR

open GalleryAlgebra Juxtapose Categorification.Graded Categorification.InductionAlong
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}

namespace Juxtapose

section Modules

universe w

variable (a b c : I →₀ ℕ) (M N P : Type w)
  [AddCommGroup M] [Module k M] [Module (WeightedKLRAlgebra k Γ a) M]
  [IsScalarTower k (WeightedKLRAlgebra k Γ a) M]
  [AddCommGroup N] [Module k N] [Module (WeightedKLRAlgebra k Γ b) N]
  [IsScalarTower k (WeightedKLRAlgebra k Γ b) N]
  [AddCommGroup P] [Module k P] [Module (WeightedKLRAlgebra k Γ c) P]
  [IsScalarTower k (WeightedKLRAlgebra k Γ c) P]

private theorem gradedIndAssocLeftScalar_smul
    (d : WeightedKLRAlgebra k Γ (a + b + c))
    (x : GradedInd k Γ (a + b) c (ExtTensor k (GradedInd k Γ a b (ExtTensor k M N)) P)) :
    gradedIndAssocLeftScalar (k := k) (Γ := Γ) a b c M N P (d • x) =
      d • gradedIndAssocLeftScalar (k := k) (Γ := Γ) a b c M N P x := by
  simp only [gradedIndAssocLeftScalar, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply, map_smul]

private theorem gradedIndAssocRightScalar_smul
    (d : WeightedKLRAlgebra k Γ (a + (b + c)))
    (x : GradedInd k Γ a (b + c) (ExtTensor k M (GradedInd k Γ b c (ExtTensor k N P)))) :
    gradedIndAssocRightScalar (k := k) (Γ := Γ) a b c M N P (d • x) =
      d • gradedIndAssocRightScalar (k := k) (Γ := Γ) a b c M N P x := by
  simp only [gradedIndAssocRightScalar, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply, map_smul]

/-- The graded induction associator is semilinear along the dimension-vector
identification of the two target rings. -/
theorem gradedIndAssocEquiv_smul
    (d : WeightedKLRAlgebra k Γ (a + b + c))
    (x : GradedInd k Γ (a + b) c (ExtTensor k (GradedInd k Γ a b (ExtTensor k M N)) P)) :
    gradedIndAssocEquiv (k := k) (Γ := Γ) a b c M N P (d • x) =
      castW k Γ (add_assoc a b c) d • gradedIndAssocEquiv (k := k) (Γ := Γ) a b c M N P x := by
  apply (gradedIndAssocRightScalar (k := k) (Γ := Γ) a b c M N P).injective
  simp only [gradedIndAssocEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    gradedIndAssocLeftScalar_smul, gradedIndAssocRightScalar_smul, indAssocEquiv_smul]

private def gradedIndAssocUnit (m : M) (n : N) (p : P) :
    GradedInd k Γ a (b + c) (ExtTensor k M (GradedInd k Γ b c (ExtTensor k N P))) :=
  BalancedTensor.tmul (k := k) (A := TensorW k Γ a (b + c))
    (B := WeightedKLRAlgebra k Γ (a + (b + c))) (M := GradedIndBimod k Γ a (b + c))
    (unitGen (inductionRingHom k Γ a (b + c)))
    (ExtTensor.tmul (k := k) m
      (BalancedTensor.tmul (k := k) (M := GradedIndBimod k Γ b c)
        (unitGen (inductionRingHom k Γ b c)) (ExtTensor.tmul (k := k) n p) :
          GradedInd k Γ b c (ExtTensor k N P)))

private theorem gradedIndAssocLeftScalar_pure
    (z : GradedIndBimod k Γ (a + b) c) (w : GradedIndBimod k Γ a b)
    (m : M) (n : N) (p : P) :
    gradedIndAssocLeftScalar (k := k) (Γ := Γ) a b c M N P
      (BalancedTensor.tmul (k := k) z (ExtTensor.tmul (k := k)
        (BalancedTensor.tmul (k := k) w (ExtTensor.tmul (k := k) m n) :
          GradedInd k Γ a b (ExtTensor k M N)) p)) =
      IndK.tmul (k := k) (φ := inductionRingHom k Γ (a + b) c) z
        (ExtTensor.tmul (k := k) (P := ind k Γ a b M N)
          (IndK.tmul (k := k) (φ := inductionRingHom k Γ a b) w (ExtTensor.tmul m n)) p) := rfl

private theorem gradedIndAssocRightScalar_unit (m : M) (n : N) (p : P) :
    gradedIndAssocRightScalar (k := k) (Γ := Γ) a b c M N P
      (gradedIndAssocUnit (k := k) (Γ := Γ) a b c M N P m n p) =
    indAssocUnit k (inductionRingHom k Γ b c) (inductionRingHom k Γ a (b + c)) m n p := rfl

private theorem gradedIndAssocEquiv_pure
    (z : GradedIndBimod k Γ (a + b) c) (w : GradedIndBimod k Γ a b)
    (m : M) (n : N) (p : P) :
    gradedIndAssocEquiv (k := k) (Γ := Γ) a b c M N P
      (BalancedTensor.tmul (k := k) z (ExtTensor.tmul (k := k)
        (BalancedTensor.tmul (k := k) w (ExtTensor.tmul (k := k) m n) :
          GradedInd k Γ a b (ExtTensor k M N)) p)) =
    castW k Γ (add_assoc a b c) (z.1 * inductionMap k Γ (a + b) c
      (w.1 ⊗ₜ[k] (1 : WeightedKLRAlgebra k Γ c))) •
      gradedIndAssocUnit (k := k) (Γ := Γ) a b c M N P m n p := by
  let e := gradedIndAssocRightScalar (k := k) (Γ := Γ) a b c M N P
  let d := castW k Γ (add_assoc a b c) (z.1 * inductionMap k Γ (a + b) c
    (w.1 ⊗ₜ[k] (1 : WeightedKLRAlgebra k Γ c)))
  let r := gradedIndAssocUnit (k := k) (Γ := Γ) a b c M N P m n p
  have he := gradedIndAssocRightScalar_smul (k := k) (Γ := Γ) a b c M N P d r
  have hLeft := gradedIndAssocLeftScalar_pure (k := k) (Γ := Γ) a b c M N P z w m n p
  have hRight := gradedIndAssocRightScalar_unit (k := k) (Γ := Γ) a b c M N P m n p
  apply e.injective
  refine (e.apply_symm_apply _).trans ((congrArg (indAssocEquiv k Γ a b c M N P) hLeft).trans ?_)
  refine (indAssoc_pure k (inductionRingHom k Γ a b) (inductionRingHom_smul k Γ a b)
    (inductionRingHom k Γ b c) (inductionRingHom_smul k Γ b c)
    (inductionRingHom k Γ (a + b) c) (inductionRingHom k Γ a (b + c))
    (castW k Γ (add_assoc a b c)) (inductionMap_assoc a b c) z w m n p).trans ?_
  exact (congrArg (d • ·) hRight.symm).trans he.symm

end Modules

end Juxtapose

namespace GradingDatum

variable (G : GradingDatum Γ) {a b c : I →₀ ℕ}
  (P : GProj (G.klrGrade a)) (Q : GProj (G.klrGrade b)) (R : GProj (G.klrGrade c))

private theorem gradedIndAssocEquiv_pure_mem
    {i l pDeg qDeg rDeg : ℤ} {z : GradedIndBimod k Γ (a + b) c}
    {w : GradedIndBimod k Γ a b} {p : P.carrier} {q : Q.carrier} {r : R.carrier}
    (hz : z ∈ G.indBimodGrading (a + b) c i) (hw : w ∈ G.indBimodGrading a b l)
    (hp : p ∈ P.grading pDeg) (hq : q ∈ Q.grading qDeg) (hr : r ∈ R.grading rDeg) :
    gradedIndAssocEquiv (k := k) (Γ := Γ) a b c P.carrier Q.carrier R.carrier
      (BalancedTensor.tmul (k := k) z (ExtTensor.tmul (k := k)
        (BalancedTensor.tmul (k := k) w (ExtTensor.tmul (k := k) p q) :
          GradedInd k Γ a b (ExtTensor k P.carrier Q.carrier)) r)) ∈
      (G.indProj P (G.indProj Q R)).grading (i + ((l + (pDeg + qDeg)) + rDeg)) := by
  rw [gradedIndAssocEquiv_pure]
  have hOne : (1 : WeightedKLRAlgebra k Γ c) ∈ G.klrGrade c 0 :=
    SetLike.GradedOne.one_mem (A := G.klrGrade c)
  have hInner : inductionMap k Γ (a + b) c (w.1 ⊗ₜ[k] (1 : WeightedKLRAlgebra k Γ c))
      ∈ G.klrGrade (a + b + c) l := by
    simpa only [add_zero] using
      G.inductionMap_mem_klrGrade
        (tmul_mem_tensorGrading (ℳ := G.klrGrade (a + b)) (m := w.1) hw hOne)
  have hCoeff := G.castW_mem_klrGrade (add_assoc a b c)
    (SetLike.GradedMul.mul_mem (A := G.klrGrade (a + b + c))
      (show z.1 ∈ G.klrGrade (a + b + c) i from hz) hInner)
  have hUnit₁ : unitGen (inductionRingHom k Γ b c) ∈ G.indBimodGrading b c 0 :=
    G.inductionMap_one_mem_klrGrade
  have hUnit₂ : unitGen (inductionRingHom k Γ a (b + c)) ∈ G.indBimodGrading a (b + c) 0 :=
    G.inductionMap_one_mem_klrGrade
  have hRight := tmul_mem_balancedGrading
    (B := WeightedKLRAlgebra k Γ (b + c)) (A := TensorW k Γ b c)
    (M := GradedIndBimod k Γ b c)
    hUnit₁ (ExtTensor.tmul_mem_grading hq hr)
  have hUnit := tmul_mem_balancedGrading
    (B := WeightedKLRAlgebra k Γ (a + (b + c))) (A := TensorW k Γ a (b + c))
    (M := GradedIndBimod k Γ a (b + c))
    hUnit₂ (ExtTensor.tmul_mem_grading hp hRight)
  have h := (G.indProj P (G.indProj Q R)).gradedSMul.smul_mem hCoeff hUnit
  have hDeg : (i + l) +ᵥ (0 + (pDeg + (0 + (qDeg + rDeg)))) =
      i + ((l + (pDeg + qDeg)) + rDeg) := by simp only [vadd_eq_add, zero_add, add_assoc]
  rw [hDeg] at h
  exact h

/-- The associator preserves degree on triple induction. -/
theorem gradedIndAssocEquiv_mem_grading {d : ℤ} {x : (G.indProj (G.indProj P Q) R).carrier}
    (hx : x ∈ (G.indProj (G.indProj P Q) R).grading d) :
    gradedIndAssocEquiv (k := k) (Γ := Γ) a b c P.carrier Q.carrier R.carrier x ∈
      (G.indProj P (G.indProj Q R)).grading d := by
  let f := (gradedIndAssocEquiv (k := k) (Γ := Γ) a b c P.carrier Q.carrier R.carrier).toLinearMap
  let S := (G.indProj P (G.indProj Q R)).grading
  change f x ∈ S d
  refine balancedGrading_map_mem (ℳ := G.indBimodGrading (a + b) c)
    (𝒩 := ExtTensor.grading (G.indProj P Q).grading R.grading)
    S f (fun i j z t hz ht => ?_) hx
  let F := (BalancedTensor.mk k (WeightedKLRAlgebra k Γ (a + b + c)) (TensorW k Γ (a + b) c)
    (GradedIndBimod k Γ (a + b) c) (ExtTensor k (G.indProj P Q).carrier R.carrier)).restrictScalars k
  let zMap := F.comp (TensorProduct.mk k _ _ z)
  refine ExtTensor.grading_map_mem (G.indProj P Q).grading R.grading (fun l => S (i + l))
    (f.comp zMap) (fun j₁ j₂ u r hu hr => ?_) ht
  let rMap := (f.comp zMap).comp (ExtTensor.mkRight (k := k) (P := (G.indProj P Q).carrier) r)
  refine balancedGrading_map_mem (ℳ := G.indBimodGrading a b)
    (𝒩 := ExtTensor.grading P.grading Q.grading) (fun l => S (i + (l + j₂)))
    rMap (fun l₁ l₂ w v hw hv => ?_) hu
  let H := (BalancedTensor.mk k (WeightedKLRAlgebra k Γ (a + b)) (TensorW k Γ a b)
    (GradedIndBimod k Γ a b) (ExtTensor k P.carrier Q.carrier)).restrictScalars k
  let wMap := H.comp (TensorProduct.mk k _ _ w)
  refine ExtTensor.grading_map_mem P.grading Q.grading (fun l => S (i + ((l₁ + l) + j₂)))
    (rMap.comp wMap) (fun _ _ _ _ hp hq => G.gradedIndAssocEquiv_pure_mem P Q R hz hw hp hq hr) hv

end GradingDatum

end Categorification.WeightedKLR

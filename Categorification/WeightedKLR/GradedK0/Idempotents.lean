/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.GradedK0.Induction

/-!
# Graded induction of principal projectives

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4,
§2.4, Definition 2.17 and the multiplication in Theorem 2.19. For homogeneous
idempotents `e` and `f` of degree zero, induction of `W_ν e ⊠ W_μ f` is the
principal projective of the image of `e ⊗ f` under juxtaposition. The proof
uses the balanced tensor realization over the coefficient ring and carries
no grading shift. It applies over every commutative coefficient ring.
-/

noncomputable section

namespace Categorification.WeightedKLR

open scoped TensorProduct
open MulOpposite Categorification.Graded GalleryAlgebra Juxtapose

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}

namespace GradingDatum

variable (G : GradingDatum Γ) {ν μ : I →₀ ℕ}

section Idempotent

variable {e : WeightedKLRAlgebra k Γ ν} {e' : WeightedKLRAlgebra k Γ μ}

theorem inductionMap_idem (he : IsIdempotentElem e) (he' : IsIdempotentElem e') :
    IsIdempotentElem (inductionMap k Γ ν μ (e ⊗ₜ e')) := by
  rw [IsIdempotentElem, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, he.eq, he'.eq]

theorem inductionMap_mem_grade_zero (he0 : e ∈ G.klrGrade ν 0) (he0' : e' ∈ G.klrGrade μ 0) :
    inductionMap k Γ ν μ (e ⊗ₜ e') ∈ G.klrGrade (ν + μ) 0 := by
  simpa only [add_zero] using G.inductionMap_mem_klrGrade (tmul_mem_tensorGrading he0 he0')

variable (e e') in
/-- The inclusion `W_ν e ⊠ W_μ e' → W_ν ⊗ W_μ`. -/
def idemIncl : ExtTensor k (Graded.leftIdeal e) (Graded.leftIdeal e') →ₗ[TensorW k Γ ν μ]
    TensorW k Γ ν μ :=
  (ExtTensor.selfEquiv k (WeightedKLRAlgebra k Γ ν) (WeightedKLRAlgebra k Γ μ)).toLinearMap ∘ₗ
    ExtTensor.map (Graded.leftIdeal e).subtype (Graded.leftIdeal e').subtype

@[simp] theorem idemIncl_tmul (x : Graded.leftIdeal e) (y : Graded.leftIdeal e') :
    idemIncl e e' (ExtTensor.tmul x y) = (x : WeightedKLRAlgebra k Γ ν) ⊗ₜ (y : WeightedKLRAlgebra k Γ μ) :=
  rfl

theorem idemIncl_mul (n : ExtTensor k (Graded.leftIdeal e) (Graded.leftIdeal e')) :
    idemIncl e e' n * (e ⊗ₜ e') = idemIncl e e' n := by
  induction n using ExtTensor.induction_on with
  | zero => rw [map_zero, zero_mul]
  | tmul x y =>
    rw [idemIncl_tmul, Algebra.TensorProduct.tmul_mul_tmul, Graded.mem_leftIdeal.1 x.2,
      Graded.mem_leftIdeal.1 y.2]
  | add n n' hn hn' => rw [map_add, add_mul, hn, hn']

theorem idemIncl_smul_unit (he : IsIdempotentElem e) (he' : IsIdempotentElem e')
    (n : ExtTensor k (Graded.leftIdeal e) (Graded.leftIdeal e')) :
    idemIncl e e' n • ExtTensor.tmul (k := k) (⟨e, he.eq⟩ : Graded.leftIdeal e)
      (⟨e', he'.eq⟩ : Graded.leftIdeal e') = n := by
  induction n using ExtTensor.induction_on with
  | zero => rw [map_zero, zero_smul]
  | tmul x y =>
    rw [idemIncl_tmul, ExtTensor.smul_tmul]
    congr 1
    · exact Subtype.ext (Graded.mem_leftIdeal.1 x.2)
    · exact Subtype.ext (Graded.mem_leftIdeal.1 y.2)
  | add n n' hn hn' => rw [map_add, add_smul, hn, hn']

variable (e e') in
/-- The bilinear map `(m, n) ↦ m ι(n)` inducing `Ind (W_ν e ⊠ W_μ e') → W_{ν+μ} ι(e ⊗ e')`.
-/
def indIdemBil : GradedIndBimod k Γ ν μ →ₗ[k] ExtTensor k (Graded.leftIdeal e) (Graded.leftIdeal e') →ₗ[k]
    Graded.leftIdeal (inductionMap k Γ ν μ (e ⊗ₜ e')) :=
  LinearMap.mk₂ k (fun m n => ⟨(m : WeightedKLRAlgebra k Γ (ν + μ)) * inductionMap k Γ ν μ (idemIncl e e' n),
      by rw [Graded.mem_leftIdeal, mul_assoc, ← map_mul, idemIncl_mul]⟩)
    (fun m m' n => Subtype.ext (add_mul _ _ _))
    (fun c m n => Subtype.ext (smul_mul_assoc _ _ _))
    (fun m n n' => Subtype.ext (by
      show (m : WeightedKLRAlgebra k Γ (ν + μ)) * inductionMap k Γ ν μ (idemIncl e e' (n + n')) =
        (m : WeightedKLRAlgebra k Γ (ν + μ)) * inductionMap k Γ ν μ (idemIncl e e' n) +
          (m : WeightedKLRAlgebra k Γ (ν + μ)) * inductionMap k Γ ν μ (idemIncl e e' n')
      rw [map_add, map_add, mul_add]))
    (fun c m n => Subtype.ext (by
      show (m : WeightedKLRAlgebra k Γ (ν + μ)) * inductionMap k Γ ν μ (idemIncl e e' (c • n)) =
        c • ((m : WeightedKLRAlgebra k Γ (ν + μ)) * inductionMap k Γ ν μ (idemIncl e e' n))
      rw [LinearMap.map_smul_of_tower, map_smul, mul_smul_comm]))

variable (he : IsIdempotentElem e) (he' : IsIdempotentElem e')

theorem mul_inductionMap_one_of_mem {r : WeightedKLRAlgebra k Γ (ν + μ)}
    (hr : r ∈ Graded.leftIdeal (inductionMap k Γ ν μ (e ⊗ₜ e'))) : r * inductionMap k Γ ν μ 1 = r := by
  have hr' : r * inductionMap k Γ ν μ (e ⊗ₜ e') = r := hr
  rw [← hr', mul_assoc, inductionMap_mul_one]

variable (e e') in
/-- The linear isomorphism `Ind (W_ν e ⊠ W_μ e') ≅ W_{ν+μ} ι(e ⊗ e')`. -/
def indIdemEquiv (he : IsIdempotentElem e) (he' : IsIdempotentElem e') :
    GradedInd k Γ ν μ (ExtTensor k (Graded.leftIdeal e) (Graded.leftIdeal e')) ≃ₗ[WeightedKLRAlgebra k Γ (ν + μ)]
      Graded.leftIdeal (inductionMap k Γ ν μ (e ⊗ₜ e')) :=
  LinearEquiv.ofLinearMap
    (BalancedTensor.liftB (indIdemBil e e')
      (fun m t n => Subtype.ext (by
        show (m : WeightedKLRAlgebra k Γ (ν + μ)) * inductionMap k Γ ν μ t * inductionMap k Γ ν μ (idemIncl e e' n) =
          (m : WeightedKLRAlgebra k Γ (ν + μ)) * inductionMap k Γ ν μ (idemIncl e e' (t • n))
        rw [map_smul, smul_eq_mul, map_mul, mul_assoc]))
      (fun r m n => Subtype.ext (by
        show r * (m : WeightedKLRAlgebra k Γ (ν + μ)) * inductionMap k Γ ν μ (idemIncl e e' n) =
          r * ((m : WeightedKLRAlgebra k Γ (ν + μ)) * inductionMap k Γ ν μ (idemIncl e e' n))
        rw [mul_assoc])))
    { toFun := fun r => BalancedTensor.tmul
        (⟨(r : WeightedKLRAlgebra k Γ (ν + μ)), mul_inductionMap_one_of_mem r.2⟩ : GradedIndBimod k Γ ν μ)
        (ExtTensor.tmul (k := k) (⟨e, he.eq⟩ : Graded.leftIdeal e)
          (⟨e', he'.eq⟩ : Graded.leftIdeal e'))
      map_add' := fun r r' => by
        rw [← BalancedTensor.add_tmul]
        exact congrArg (BalancedTensor.tmul · _) (Subtype.ext rfl)
      map_smul' := fun b r => by
        rw [RingHom.id_apply, BalancedTensor.smul_tmul']
        exact congrArg (BalancedTensor.tmul · _) (Subtype.ext rfl) }
    (LinearMap.ext fun r => Subtype.ext (by
      show (r : WeightedKLRAlgebra k Γ (ν + μ)) * inductionMap k Γ ν μ (e ⊗ₜ e') = r
      exact r.2))
    (BalancedTensor.extB fun m n => by
      show BalancedTensor.tmul (⟨(m : WeightedKLRAlgebra k Γ (ν + μ)) * inductionMap k Γ ν μ (idemIncl e e' n),
          _⟩ : GradedIndBimod k Γ ν μ) _ = BalancedTensor.tmul m n
      rw [show (⟨(m : WeightedKLRAlgebra k Γ (ν + μ)) * inductionMap k Γ ν μ (idemIncl e e' n),
          mul_inductionMap_mem m _⟩ : GradedIndBimod k Γ ν μ) = op (idemIncl e e' n) • m from rfl,
        BalancedTensor.op_smul_tmul, idemIncl_smul_unit he he'])

variable (he0 : e ∈ G.klrGrade ν 0) (he0' : e' ∈ G.klrGrade μ 0)

/-- **`Ind (W_ν e ⊠ W_μ e') ≅ W_{ν+μ} ι(e ⊗ e')`** for degree-zero idempotents `e`, `e'`. -/
def indIdemIso :
    (G.indProj (GProj.ofIdempotent e he he0) (GProj.ofIdempotent e' he' he0')).Iso
      (GProj.ofIdempotent (inductionMap k Γ ν μ (e ⊗ₜ e')) (inductionMap_idem he he')
        (G.inductionMap_mem_grade_zero he0 he0')) :=
  GradedEquiv.ofPreserves (indIdemEquiv e e' he he') fun _ y hy =>
    balancedGrading_map_mem (B := WeightedKLRAlgebra k Γ (ν + μ)) (ℳ := G.indBimodGrading ν μ)
      (Graded.submodule (G.klrGrade (ν + μ)) (Graded.leftIdeal (inductionMap k Γ ν μ (e ⊗ₜ e'))))
      ((indIdemEquiv e e' he he').toLinearMap.restrictScalars k)
      (fun _ _ m n hm hn => by
        have hn' := ExtTensor.grading_map_mem _ _
          (tensorGrading (G.klrGrade ν) (G.klrGrade μ)) ((idemIncl e e').restrictScalars k)
          (fun _ _ x y hx hy => tmul_mem_tensorGrading hx hy) hn
        exact SetLike.GradedMul.mul_mem (A := G.klrGrade (ν + μ)) hm (G.inductionMap_mem_klrGrade hn'))
      (y := y) hy

/-- The product of the principal-projective classes is the class of the image
idempotent, for Webster arXiv:1209.2463v4, Definition 2.17 and Theorem 2.19. -/
theorem indK0_ofIdempotent :
    G.indK0 ν μ (K0.of (GProj.ofIdempotent e he he0)) (K0.of (GProj.ofIdempotent e' he' he0')) =
      K0.of (GProj.ofIdempotent (inductionMap k Γ ν μ (e ⊗ₜ e')) (inductionMap_idem he he')
        (G.inductionMap_mem_grade_zero he0 he0')) := by
  rw [indK0_of]
  exact K0.of_eq_of_iso (G.indIdemIso he he' he0 he0')

end Idempotent

end GradingDatum

end Categorification.WeightedKLR

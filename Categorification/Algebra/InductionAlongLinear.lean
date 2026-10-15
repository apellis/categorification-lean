/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongRes
import Categorification.Algebra.ModuleCatLinear

/-!
# Linearity of induction and restriction along a nonunital map of algebras

Let `A`, `B` be algebras over a commutative ring `k` and `φ : A → B` a nonunital ring map with
`φ (c • 1) = c • φ 1` for `c : k`. Then induction `N ↦ Bφ(1) ⊗_A N` and restriction
`M ↦ φ(1) M` along `φ` are `k`-linear functors between the module categories, which are
`k`-linear by `ModuleCat.linearOverCommRing`.
-/

namespace Categorification.InductionAlong

open CategoryTheory MulOpposite

universe u w v

variable {k : Type v} [CommRing k] {A : Type u} [Ring A] [Algebra k A] {B : Type u} [Ring B]
  [Algebra k B] (φ : A →ₙ+* B)

/-- `φ` is compatible with the `k`-algebra structures: `φ (c • 1) = c • φ 1`. -/
def ScalarCompatible : Prop := ∀ c : k, φ (algebraMap k A c) = algebraMap k B c * φ 1

variable {φ}

/-- **Induction along a scalar-compatible map is `k`-linear.** -/
theorem functor_linear (hφ : ScalarCompatible (k := k) φ) : (functor.{u, w} φ).Linear k where
  map_smul {N N'} f c := ModuleCat.hom_ext (Ind.ext fun z n => by
    change Ind.tmul z (algebraMap k A c • f.hom n) =
      algebraMap k B c • Ind.tmul z (f.hom n)
    rw [← Ind.op_smul_tmul, Ind.smul_tmul]
    congr 1
    apply Subtype.ext
    have hz : z.1 * φ 1 = z.1 := z.2
    change z.1 * φ (algebraMap k A c) = algebraMap k B c * z.1
    rw [hφ c, ← mul_assoc, ← Algebra.commutes, mul_assoc, hz])

/-- **Restriction along a scalar-compatible map is `k`-linear.** -/
theorem resFunctor_linear (hφ : ScalarCompatible (k := k) φ) :
    (resFunctor.{u, w} φ).Linear k where
  map_smul {M M'} f c := ModuleCat.hom_ext (LinearMap.ext fun m => Res.ext (by
    change algebraMap k B c • f.hom m.val = φ (algebraMap k A c) • f.hom m.val
    have hm : φ 1 • f.hom m.val = f.hom m.val := by rw [← map_smul, m.prop]
    rw [hφ c, mul_smul, hm]))

end Categorification.InductionAlong

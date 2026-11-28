/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.UpResolutionTotal
import Categorification.KLR.G0Res

/-!
# External tensor products of resolutions in `C↑`

Let `A`, `B` be finite-dimensional graded algebras over a field `k`. If finite-dimensional graded
modules `M` and `M'` have graded projective resolutions in `C↑` with constants `c` and `c'`, then
`M ⊠ M'` has one over `A ⊗ B` with constant `c + c'` (`GFin.UpResolution.extTensor`): it is the
total complex of the tensor product of the two resolutions, glued by
`GFin.UpResolution.ofResolution`. This is used in B. Webster, *Knot invariants and higher
representation theory*, arXiv:1309.3796v3, proof of Theorem 5.28 (general case), to resolve
`L_1 ⊠ ⋯ ⊠ L_ℓ` before standardizing.

## Main results

* `Graded.tensorGrading_eq_bot` : a tensor product of gradings bounded below is bounded below.
* `GFin.UpResolution.extTensorLeft` : `P ⊠ -` for a graded projective `P` bounded below.
* `GFin.UpResolution.extTensor`.
-/

noncomputable section

namespace Categorification.Graded

open scoped TensorProduct

universe u

theorem tensorGrading_eq_bot {k M N : Type*} [CommRing k] [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] {ℳ : ℤ → Submodule k M} {𝒩 : ℤ → Submodule k N} {p q d : ℤ}
    (hM : ∀ i < p, ℳ i = ⊥) (hN : ∀ j < q, 𝒩 j = ⊥) (hd : d < p + q) :
    tensorGrading ℳ 𝒩 d = ⊥ := by
  rw [eq_bot_iff, tensorGrading, Submodule.span_le]
  rintro _ ⟨i, j, m, n, hij, hm, hn, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_bot]
  by_cases hi : i < p
  · rw [hM i hi, Submodule.mem_bot] at hm
    rw [hm, TensorProduct.zero_tmul]
  · rw [hN j (by omega), Submodule.mem_bot] at hn
    rw [hn, TensorProduct.tmul_zero]

variable {k : Type u} [Field k] {A : Type u} [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}
  [GradedAlgebra 𝒜] {B : Type u} [Ring B] [Algebra k B] {ℬ : ℤ → Submodule k B}
  [GradedAlgebra ℬ]

namespace GFin

namespace UpResolution

variable {M : GFin 𝒜} {M' : GFin ℬ} {c c' : ℤ}

/-- `P ⊠ -` applied to a resolution, for a graded projective `P` vanishing in degrees `< p`. -/
def extTensorLeft (P : GFin 𝒜) [Module.Projective A P.carrier] {p : ℤ}
    (hP : ∀ j < p, P.grading j = ⊥) (R' : UpResolution M' c') :
    UpResolution (P.extTensor M') (c' - p) where
  syz n := P.extTensor (R'.syz n)
  term n := P.extTensor (R'.term n)
  projective n := by
    have := R'.projective n
    exact ExtTensor.projective
  iso := GFin.extTensorCongr (GradedEquiv.refl _) R'.iso
  ses n := GFin.extTensorSESRight P (R'.ses n)
  vanish n j hj := tensorGrading_eq_bot hP (R'.vanish n) (by omega)

/-- **The external tensor product of resolutions in `C↑`.** -/
def extTensor (R : UpResolution M c) (R' : UpResolution M' c') :
    UpResolution (M.extTensor M') (c + c') :=
  (ofResolution (fun n => (R.syz n).extTensor M') (fun n => (R.term n).extTensor M') (c + c')
    (fun n => GFin.extTensorSESLeft (R.ses n) M')
    (fun n => by
      have := R.projective n
      exact (extTensorLeft (R.term n) (p := n - c) (R.vanish n) R').mono (by omega))).congr
    (GFin.extTensorCongr R.iso (GradedEquiv.refl _))

end UpResolution

end GFin

end Categorification.Graded

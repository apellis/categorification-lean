/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorFormOrdered
import Categorification.WeightedKLR.RedStrands.TensorSplit
import Categorification.WeightedKLR.RedStrands.TensorLatticeCoordinates

/-!
# The componentwise form splits along a cut of the red strands

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.7
(Proposition 4.33 in v2: the form on `V^{λ_1} ⊗ ⋯ ⊗ V^{λ_n}` is the componentwise product of
one-factor forms before the intertwiner acts), and §7.3, proof of Proposition 7.20. For the
partial standardization with blocks `λ_1…λ_a; λ_{a+1}…λ_{a+b}` the word character of
`𝕊(X ⊠ Y)` is a product of the characters of the two factors on the two tensor factors of
`TensorSpace λ ≃ TensorSpace (λ_1…λ_a) ⊗ TensorSpace (λ_{a+1}…λ_{a+b})` (`tensorSplit`).
When the factor characters are themselves componentwise forms against vectors `x` and `y`,
the product is the componentwise form against `x ⊗ y`:

* `orderedFactorwise_eq_tensorSplit`: `⟨z', z⟩ = ⟨z'_1, z_1⟩ ⟨z'_2, z_2⟩` on the split;
* `orderedFactorwise_tensorSplit_symm`: the functional of `x ⊗ y` is the product of the
  functionals of `x` and `y` on the split (the generalization of
  `orderedFactorwise_appendTensor`, which splits off one red strand);
* `orderedFactorwise_tensorSplit₃`: the three-block form used for
  `𝕊^{λ_1…λ_j; μ μ*; λ_{j+1}…λ_ℓ}`, with a middle vector `c` in the slot of the pair.
-/

noncomputable section

namespace Categorification.Stendhal.TensorPairing

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF FirstWeight
open scoped TensorProduct

local notation "𝕂" => RatFunc ℚ
local notation "q" => (RatFunc.X : 𝕂)
private local instance cutFormNeZero : NeZero q := ⟨RatFunc.X_ne_zero⟩
variable {I Y : Type*} [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} [Finite I] (hR : R.IsXRegular)

/-- The product of two sesquilinear forms on a tensor product of two spaces, evaluated on a
pair of tensors. -/
def splitProductForm {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module 𝕂 M] [Module 𝕂 N]
    (A : M →ₛₗ[barRingHom] M →ₗ[𝕂] 𝕂) (B : N →ₛₗ[barRingHom] N →ₗ[𝕂] 𝕂) :
    M ⊗[𝕂] N →ₛₗ[barRingHom] M ⊗[𝕂] N →ₗ[𝕂] 𝕂 :=
  (TensorProduct.map₂ A B).compr₂ₛₗ (TensorProduct.lid 𝕂 𝕂).toLinearMap

theorem splitProductForm_tmul {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module 𝕂 M] [Module 𝕂 N] (A : M →ₛₗ[barRingHom] M →ₗ[𝕂] 𝕂)
    (B : N →ₛₗ[barRingHom] N →ₗ[𝕂] 𝕂) (x x' : M) (y y' : N) :
    splitProductForm A B (x ⊗ₜ y) (x' ⊗ₜ y') = A x x' * B y y' := rfl

/-- With the first argument a pure tensor, the product form is the product of the two
functionals. -/
theorem splitProductForm_tmul_left {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module 𝕂 M] [Module 𝕂 N] (A : M →ₛₗ[barRingHom] M →ₗ[𝕂] 𝕂)
    (B : N →ₛₗ[barRingHom] N →ₗ[𝕂] 𝕂) (x : M) (y : N) (t : M ⊗[𝕂] N) :
    splitProductForm A B (x ⊗ₜ y) t =
      factorTensorTest (fun _ : Unit => A x) (fun _ : Unit => B y) () () t := by
  induction t using TensorProduct.inductionOn with
  | tmul a b => rw [splitProductForm_tmul, factorTensorTest_tmul]
  | add s t hs ht => rw [map_add, map_add, hs, ht]

/-- **The componentwise form splits along a cut** of the red strands: for `λ = (λ_1, …,
λ_{a+b})`, the componentwise product of the one-factor forms is the product of the forms of
the two blocks on the split `tensorSplit`. -/
theorem orderedFactorwise_eq_tensorSplit {a b : ℕ} (wt : Fin (a + b) → Dom R)
    (z' z : TensorSpace wt) :
    orderedFactorwise hR wt z' z =
      splitProductForm (orderedFactorwise hR (fun i : Fin a => wt (Fin.castAdd b i)))
        (orderedFactorwise hR (fun i : Fin b => wt (Fin.natAdd a i)))
        (tensorSplit wt z') (tensorSplit wt z) := by
  induction z' using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    induction z using PiTensorProduct.induction_on with
    | smul_tprod c' y =>
      simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, tensorSplit_tprod,
        splitProductForm_tmul, orderedFactorwise_tprod, Fin.prod_univ_add]
    | add z₁ z₂ h₁ h₂ => rw [map_add, map_add, map_add, h₁, h₂]
  | add z₁ z₂ h₁ h₂ => rw [map_add, map_add, LinearMap.add_apply, map_add,
      LinearMap.add_apply, h₁, h₂]

/-- **The functional of a split vector**: the componentwise form against
`tensorSplit⁻¹ (x ⊗ y)` is the product of the forms against `x` and against `y` on the split
of the second argument. With one red strand in the second block this is
`orderedFactorwise_appendTensor`. -/
theorem orderedFactorwise_tensorSplit_symm {a b : ℕ} (wt : Fin (a + b) → Dom R)
    (x : TensorSpace (fun i : Fin a => wt (Fin.castAdd b i)))
    (y : TensorSpace (fun i : Fin b => wt (Fin.natAdd a i))) (z : TensorSpace wt) :
    orderedFactorwise hR wt ((tensorSplit wt).symm (x ⊗ₜ y)) z =
      factorTensorTest (fun _ : Unit => orderedFactorwise hR _ x)
        (fun _ : Unit => orderedFactorwise hR _ y) () () (tensorSplit wt z) := by
  rw [orderedFactorwise_eq_tensorSplit, LinearEquiv.apply_symm_apply,
    splitProductForm_tmul_left]

/-- **The three-block form**: for blocks `λ_1…λ_a; λ_{a+1}…λ_{a+m}; λ_{a+m+1}…λ_{a+m+b}`, the
componentwise form against `x ⊗ c ⊗ y` is the product of the forms against `x`, `c` and `y`
on the iterated split of the second argument. In the proof of Webster's Proposition 7.20 the
middle block is the pair `(μ, μ*)` and `c` is the vector whose form is the class of `L_μ`. -/
theorem orderedFactorwise_tensorSplit₃ {a m b : ℕ} (wt : Fin ((a + m) + b) → Dom R)
    (x : TensorSpace (fun i : Fin a => wt (Fin.castAdd b (Fin.castAdd m i))))
    (c : TensorSpace (fun i : Fin m => wt (Fin.castAdd b (Fin.natAdd a i))))
    (y : TensorSpace (fun i : Fin b => wt (Fin.natAdd (a + m) i))) (z : TensorSpace wt) :
    orderedFactorwise hR wt ((tensorSplit wt).symm
        ((tensorSplit (fun i : Fin (a + m) => wt (Fin.castAdd b i))).symm (x ⊗ₜ c) ⊗ₜ y)) z =
      factorTensorTest
        (fun _ : Unit => factorTensorTest (fun _ : Unit => orderedFactorwise hR _ x)
          (fun _ : Unit => orderedFactorwise hR _ c) () ())
        (fun _ : Unit => orderedFactorwise hR _ y) () ()
        (TensorProduct.map (tensorSplit (fun i : Fin (a + m) => wt (Fin.castAdd b i))).toLinearMap
          LinearMap.id (tensorSplit wt z)) := by
  rw [orderedFactorwise_tensorSplit_symm]
  induction tensorSplit wt z using TensorProduct.inductionOn with
  | tmul u v =>
    rw [factorTensorTest_tmul, TensorProduct.map_tmul, factorTensorTest_tmul,
      LinearMap.id_apply, LinearEquiv.coe_coe, orderedFactorwise_eq_tensorSplit,
      LinearEquiv.apply_symm_apply, splitProductForm_tmul_left]
  | add s t hs ht => rw [map_add, map_add, map_add, hs, ht]

end Categorification.Stendhal.TensorPairing

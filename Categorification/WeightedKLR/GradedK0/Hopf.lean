/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.GradedK0.AntipodeConvolution
import Categorification.WeightedKLR.GradedK0.Braiding
import Categorification.WeightedKLR.GradedK0.TotalCoassociativity
import Categorification.WeightedKLR.GradedK0.Multiplicativity

/-!
# The braided Hopf algebra of weighted projectives

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4,
§2.4, Theorem 2.19, pp. 11–12. The tensor-square algebra uses the braiding on
weight-graded modules, with its Laurent shift given by the crossings between
the inner two tensorands. A coalgebra on the induction algebra, multiplicativity
in that tensor-square algebra, and a degree-preserving two-sided convolution
inverse are the concrete braided Hopf structure. Dimension vectors index the
nonnegative cone in `ℤ[I]`: all other weight components are zero.

The final construction uses a coefficient field and a weighted graph without zero-weight loops
with the standing hypotheses. The graded dimensions and tensor comparisons
come from the standing grading. The corrected recursion and its printed form
are recorded in `GradedK0/Antipode.lean`.
-/

noncomputable section

namespace Categorification.WeightedKLR

open Categorification.Graded
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [Field k] {Γ : WeightedGraph I 𝕜 k}

local notation "L" => LaurentPolynomial ℤ

namespace GradingDatum

variable (G : GradingDatum Γ)

/-- The braided Hopf algebra laws on the weighted induction algebra, in the
homogeneous tensor-product convention of Webster, arXiv:1209.2463v4, §2.4.
`twMul` is the bilinear extension of the scalar-weighted crossing of the two
middle factors. The ordinary coalgebra laws apply to the underlying module. -/
structure BraidedHopfK0 extends Coalgebra L G.K0W where
  /-- The degree-preserving antipode. -/
  antipode : Module.End L G.K0W
  /-- The antipode maps each weight summand to itself. -/
  antipode_homogeneous (ν : I →₀ ℕ) (x : G.K0fam ν) :
    ∃ y : G.K0fam ν, antipode (DirectSum.of G.K0fam ν x) = DirectSum.of G.K0fam ν y
  /-- Only components of bidegree `(a,b)` with `a+b=ν` occur in the coproduct. -/
  comul_homogeneous {a b ν : I →₀ ℕ} (h : ν ≠ a + b) (x : G.K0fam ν) :
    TensorProduct.map (DirectSum.component L _ G.K0fam a) (DirectSum.component L _ G.K0fam b)
        (comul (DirectSum.of G.K0fam ν x)) = 0
  /-- The scalar-valued counit is supported at weight zero. -/
  counit_homogeneous {ν : I →₀ ℕ} (h : ν ≠ 0) (x : G.K0fam ν) :
    counit (DirectSum.of G.K0fam ν x) = 0
  /-- Tensor-square multiplication is multiplication after the middle braiding. -/
  tensor_mul_braided (x y z w : G.K0W) : G.twMul (x ⊗ₜ y) (z ⊗ₜ w) =
    TensorProduct.map (LinearMap.mulLeft L x) (LinearMap.mulRight L w)
      (G.weightBraiding (y ⊗ₜ z))
  /-- The unit tensor acts on the left in the braided tensor-square algebra. -/
  tensor_one_left (z : G.K0W ⊗[L] G.K0W) : G.twMul (1 ⊗ₜ 1) z = z
  /-- The unit tensor acts on the right in the braided tensor-square algebra. -/
  tensor_one_right (z : G.K0W ⊗[L] G.K0W) : G.twMul z (1 ⊗ₜ 1) = z
  /-- The braided tensor-square product is associative. -/
  tensor_assoc (x y z : G.K0W ⊗[L] G.K0W) :
    G.twMul (G.twMul x y) z = G.twMul x (G.twMul y z)
  /-- Restriction preserves the unit. -/
  comul_one : comul 1 = 1 ⊗ₜ[L] 1
  /-- Restriction intertwines induction with the braided tensor-square product. -/
  comul_mul (x y : G.K0W) : comul (x * y) = G.twMul (comul x) (comul y)
  /-- The counit is unital. -/
  counit_one : counit 1 = 1
  /-- The counit is multiplicative. -/
  counit_mul (x y : G.K0W) : counit (x * y) = counit x * counit y
  /-- The antipode is a left convolution inverse. -/
  antipode_left : LinearMap.mul' L G.K0W ∘ₗ antipode.rTensor G.K0W ∘ₗ comul =
    Algebra.linearMap L G.K0W ∘ₗ counit
  /-- The antipode is a right convolution inverse. -/
  antipode_right : LinearMap.mul' L G.K0W ∘ₗ antipode.lTensor G.K0W ∘ₗ comul =
    Algebra.linearMap L G.K0W ∘ₗ counit

variable (hD : Γ.Dagger) (hS : Γ.Standing)
  (hZ : Γ.NoZeroLoops) (hl : ∀ i, Γ.loop i = none)
  [∀ ν : I →₀ ℕ, HasGdim (G.klrGrade ν)]

local notation "Δ" => G.totalCoproduct hD hS hZ hl
local notation "S" => G.antipodeK0 hD hS hZ hl

/-- The restriction coproduct and its weight-zero counit give the ordinary
underlying coalgebra of Webster, §2.4, Theorem 2.19. -/
@[instance_reducible] def K0coalgebra : Coalgebra L G.K0W where
  comul := Δ
  counit := G.counitK0
  coassoc := G.totalCoproduct_coassoc hD hS hZ hl
  rTensor_counit_comp_comul := by
    apply LinearMap.ext
    intro x
    apply (TensorProduct.lid L G.K0W).injective
    exact (G.counitK0_totalCoproduct_left hD hS hZ hl x).trans (one_smul L x).symm
  lTensor_counit_comp_comul := by
    apply LinearMap.ext
    intro x
    apply (TensorProduct.rid L G.K0W).injective
    exact (G.counitK0_totalCoproduct_right hD hS hZ hl x).trans (one_smul L x).symm

/-- The left antipode identity for the weighted restriction coproduct of
Webster, arXiv:1209.2463v4, §2.4, Theorem 2.19. -/
theorem antipodeK0_left :
    LinearMap.mul' L G.K0W ∘ₗ (S).rTensor G.K0W ∘ₗ Δ =
      Algebra.linearMap L G.K0W ∘ₗ G.counitK0 := by
  let _ := G.K0coalgebra hD hS hZ hl
  let e : WithConv (Module.End L G.K0W) := WithConv.toConv LinearMap.id
  let t : WithConv (Module.End L G.K0W) := WithConv.toConv S
  have het : e * t = 1 := WithConv.ext (G.antipodeK0_right hD hS hZ hl)
  have hv : e * (t * e - 1) = 0 := calc
    _ = e * (t * e) - e * 1 := mul_sub e (t * e) 1
    _ = (e * t) * e - e := by rw [mul_assoc e t e, mul_one e]
    _ = 0 := by rw [het, one_mul e, sub_self e]
  have hc : (t * e - 1).ofConv = 0 :=
    G.eq_zero_of_mul_lTensor_total hD hS hZ hl _ (congrArg WithConv.ofConv hv)
  have hte : t * e = 1 := sub_eq_zero.mp (WithConv.ext hc)
  exact congrArg WithConv.ofConv hte

/-- The concrete braided Hopf structure on the weighted induction algebra
for a grading with bounded-below, finite-dimensional graded pieces. -/
def braidedHopfK0 : G.BraidedHopfK0 where
  toCoalgebra := G.K0coalgebra hD hS hZ hl
  antipode := S
  antipode_homogeneous ν x := ⟨_, G.antipodeK0_of hD hS hZ hl ν x⟩
  comul_homogeneous {a b ν} h x := by
    change TensorProduct.map (DirectSum.component L _ G.K0fam a)
      (DirectSum.component L _ G.K0fam b) (Δ (DirectSum.lof L _ G.K0fam ν x)) = 0
    have he := LinearMap.congr_fun (G.component_totalCoproduct hD hS hZ hl a b)
      (DirectSum.lof L _ G.K0fam ν x)
    simpa only [LinearMap.comp_apply, DirectSum.component.of, dite_eq_right h, map_zero] using he
  counit_homogeneous h x := G.counitK0_of_ne h x
  tensor_mul_braided := G.twMul_eq_map_weightBraiding
  tensor_one_left := G.twMul_one_left
  tensor_one_right := G.twMul_one_right
  tensor_assoc := G.twMul_assoc
  comul_one := G.totalCoproduct_one hD hS hZ hl
  comul_mul := G.totalCoproduct_mul hD hS hZ hl
  counit_one := G.counitK0_one
  counit_mul := G.counitK0_mul
  antipode_left := G.antipodeK0_left hD hS hZ hl
  antipode_right := G.antipodeK0_right hD hS hZ hl

end GradingDatum

namespace WeightedGraph.Standing

variable (hS : Γ.Standing) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
  (hl : ∀ i, Γ.loop i = none)

/-- **Webster, arXiv:1209.2463v4, §2.4, Theorem 2.19 (braided Hopf algebra).**
Over a field the standing grading of a weighted graph without zero-weight loops yields a
braided Hopf algebra on the graded Grothendieck group of projectives, with
induction multiplication, restriction coproduct, and the corrected recursive
antipode. This requires no tensor-comparison or graded-dimension hypothesis. -/
def braidedHopfK0 : hS.gradingDatum.BraidedHopfK0 := by
  letI : ∀ ν : I →₀ ℕ, HasGdim (hS.gradingDatum.klrGrade ν) := fun ν =>
    GalleryAlgebra.hasGdim_klrGrade (ν := ν) hD hZ hS
  exact hS.gradingDatum.braidedHopfK0 hD hS hZ hl

/-- On a one-strand weight the antipode of the standing Hopf structure negates
every projective class (Webster, §2.4, proof of Theorem 2.19). -/
theorem braidedHopfK0_antipode_single (i : I) (x : hS.gradingDatum.K0fam (Finsupp.single i 1)) :
    (hS.braidedHopfK0 hD hZ hl).antipode
        (DirectSum.of hS.gradingDatum.K0fam (Finsupp.single i 1) x) =
      -DirectSum.of hS.gradingDatum.K0fam (Finsupp.single i 1) x := by
  let _ : ∀ ν : I →₀ ℕ, HasGdim (hS.gradingDatum.klrGrade ν) := fun ν =>
    GalleryAlgebra.hasGdim_klrGrade (ν := ν) hD hZ hS
  change hS.gradingDatum.antipodeK0 hD hS hZ hl _ = _
  rw [GradingDatum.antipodeK0_of, hS.gradingDatum.antipodeComponent_of_degree_one hD hS hZ hl
    (Finsupp.degree_single i 1), LinearMap.neg_apply, LinearMap.id_apply, map_neg]

end WeightedGraph.Standing

end Categorification.WeightedKLR

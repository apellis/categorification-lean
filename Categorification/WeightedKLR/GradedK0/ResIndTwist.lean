/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.GradedK0.ResIndK0
import Categorification.WeightedKLR.Mackey.ResIndTwist

/-!
# The graded Mackey pieces as twisted `Ind ∘ Res`

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, proof of
Theorem 2.19 (after Khovanov–Lauda, arXiv:0803.4121v2, Proposition 2.18). This is the graded
form of `Mackey/ResIndTwist.lean`.

For a four-block layout `ν' = a + b`, `ν'' = c + d`, `ν₁ = a + c`, `ν₂ = b + d`, the middle
balanced tensor product `ResIndPiece L ⊗_{W_{ν'} ⊗ W_{ν''}} (P ⊠ Q)`, with its unshifted grading
`ResIndPiece.baseGrading`, is the graded module obtained by restricting `P` to `W_a ⊗ W_b` and
`Q` to `W_c ⊗ W_d`, exchanging the middle factors and inducing along `ι_{a,c} ⊗ ι_{b,d}`. The
identification `t ⊗ r ↦ (t ⊗ e) ⊗ r` (`ResIndPiece.resTwistEquiv`) preserves degrees with no
shift, since `e = (ι_{a,b} ⊗ ι_{c,d})(1)` has degree `0`. With the graded Mackey formula
`exists_resK0_indK0_eq_sum_graded` this gives
`Δ_{ν₁;ν₂}(x · y) = ∑ q^{s} (Ind_{a;c} ⊗ Ind_{b;d}) ∘ (exchange) (Δ_{a;b} x ⊠ Δ_{c;d} y)` in the
graded Grothendieck group of `W_{ν₁} ⊗ W_{ν₂}`, with `s = middleShift G a b c d`.

## Main definitions and results

* `Juxtapose.middleIndGProj`: `(W_{a+c} ⊗ W_{b+d}) e' ⊗_{(W_a ⊗ W_b) ⊗ (W_c ⊗ W_d)} N` as a
  finitely generated graded projective module.
* `Juxtapose.middleIndK0`: the `ℤ[q, q⁻¹]`-linear induction from the middle parabolic on graded
  `K₀`.
* `ResIndPiece.map_of_middleIndGProj`: the class of a piece is the transported class of the
  twisted `Ind ∘ Res`.
* `ResIndPiece.twistK0Graded`, `ResIndPiece.tensorGProj_eq_twistK0Graded`.
* `exists_resK0_indK0_eq_sum_twistK0Graded`: the graded Mackey formula in twisted form.
-/

noncomputable section

/-! ### Graded induction along a fixed graded bimodule -/

namespace Categorification.Graded

open BalancedTensor MulOpposite DirectSum

section BalancedInd

universe u' v'

variable {k : Type v'} [Field k] {B : Type u'} [Ring B] [Algebra k B] (ℬ : ℤ → Submodule k B)
  {A : Type u'} [Ring A] [Algebra k A] (𝒜 : ℤ → Submodule k A)
  [GradedAlgebra 𝒜] (M : Type u') [AddCommGroup M] [Module k M] [Module B M]
  [IsScalarTower k B M] [Module Aᵐᵒᵖ M] [SMulCommClass B Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M]
  [Module.Finite B M] [Module.Projective B M]
  (ℳ : ℤ → Submodule k M) [Decomposition ℳ] [SetLike.GradedSMul ℬ ℳ]
  (hM : ∀ ⦃i l : ℤ⦄ ⦃m : M⦄ ⦃a : A⦄, m ∈ ℳ i → a ∈ 𝒜 l → op a • m ∈ ℳ (i + l))

/-- Induction `N ↦ M ⊗_A N` along a graded `(B, A)`-bimodule `M` which is finitely generated
projective over `B`, as a map of finitely generated graded projective modules, with no shift. -/
def balancedIndGProj (N : GProj 𝒜) : GProj ℬ :=
  haveI : Module.Finite B (BalancedTensor k B A M N.carrier) := BalancedTensor.finite
  haveI : Module.Projective B (BalancedTensor k B A M N.carrier) := BalancedTensor.projective
  balancedTensorGProj ℬ 𝒜 N.grading M ℳ hM

variable {ℬ 𝒜 M ℳ hM}

/-- `M ⊗_A N₁ ≅ M ⊗_A N₂` for `N₁ ≅ N₂`. -/
def balancedIndGProjCongr {N₁ N₂ : GProj 𝒜} (e : N₁.Iso N₂) :
    (balancedIndGProj ℬ 𝒜 M ℳ hM N₁).Iso (balancedIndGProj ℬ 𝒜 M ℳ hM N₂) :=
  GradedEquiv.ofPreserves (BalancedTensor.congrRight e.toLinearEquiv) fun _ y hy =>
    mapRight_mem_balancedGrading (B := B) (ℳ := ℳ) e.preservesGrading (y := y) hy

/-- `M ⊗_A (N₁ ⊕ N₂) ≅ (M ⊗_A N₁) ⊕ (M ⊗_A N₂)`. -/
def balancedIndGProjProd (N₁ N₂ : GProj 𝒜) :
    (balancedIndGProj ℬ 𝒜 M ℳ hM (N₁.prod N₂)).Iso
      ((balancedIndGProj ℬ 𝒜 M ℳ hM N₁).prod (balancedIndGProj ℬ 𝒜 M ℳ hM N₂)) :=
  let e := BalancedTensor.prodRight k B A M N₁.carrier N₂.carrier
  GradedEquiv.ofPreserves e fun _ y hy =>
    balancedGrading_map_mem (B := B) (ℳ := ℳ)
      (Graded.prod (balancedIndGProj ℬ 𝒜 M ℳ hM N₁).grading
        (balancedIndGProj ℬ 𝒜 M ℳ hM N₂).grading)
      (e.toLinearMap.restrictScalars k)
      (fun _ _ _ _ hm hn => mem_prod.2
        ⟨tmul_mem_balancedGrading hm (mem_prod.1 hn).1,
          tmul_mem_balancedGrading hm (mem_prod.1 hn).2⟩) (y := y) hy

/-- `M ⊗_A (N{a}) ≅ (M ⊗_A N){a}`. -/
def balancedIndGProjShift (N : GProj 𝒜) (a : ℤ) :
    (balancedIndGProj ℬ 𝒜 M ℳ hM (N.shift a)).Iso ((balancedIndGProj ℬ 𝒜 M ℳ hM N).shift a) :=
  GradedEquiv.ofPreserves (BalancedTensor.congrRight (N.shiftLinearEquiv a)) fun _ y hy => by
    have h := mapRight_mem_balancedGrading (B := B) (ℳ := ℳ)
      (N.shiftLinearEquiv_preservesGrading a) (y := y) hy
    rw [balancedGrading_shift_right] at h
    exact h

variable (ℬ 𝒜 M ℳ hM)

/-- The additive map `K₀(A) → K₀(B)`, `[N] ↦ [M ⊗_A N]`. -/
def balancedIndK0Add : K0 𝒜 →+ K0 ℬ :=
  K0.lift (fun N => K0.of (balancedIndGProj ℬ 𝒜 M ℳ hM N))
    (fun _ _ e => K0.of_eq_of_iso (balancedIndGProjCongr e))
    (fun N₁ N₂ => by rw [K0.of_eq_of_iso (balancedIndGProjProd N₁ N₂), K0.of_prod])

theorem balancedIndK0Add_of (N : GProj 𝒜) :
    balancedIndK0Add ℬ 𝒜 M ℳ hM (K0.of N) = K0.of (balancedIndGProj ℬ 𝒜 M ℳ hM N) :=
  K0.lift_of _ _ _ N

theorem balancedIndK0Add_shift (a : ℤ) (x : K0 𝒜) :
    balancedIndK0Add ℬ 𝒜 M ℳ hM (K0.shiftHom a x) =
      K0.shiftHom a (balancedIndK0Add ℬ 𝒜 M ℳ hM x) := by
  induction x using K0.induction_on with
  | of N =>
    rw [K0.shiftHom_of, balancedIndK0Add_of, balancedIndK0Add_of, K0.shiftHom_of]
    exact K0.of_eq_of_iso (balancedIndGProjShift N a)
  | zero => simp
  | add x x' hx hx' => simp only [map_add, hx, hx']
  | neg x hx => simp only [map_neg, hx]

/-- **Graded induction along `M` on Grothendieck groups**: the `ℤ[q, q⁻¹]`-linear map
`K₀(A) → K₀(B)`, `[N] ↦ [M ⊗_A N]`. -/
def balancedIndK0 : K0 𝒜 →ₗ[LaurentPolynomial ℤ] K0 ℬ where
  toFun := balancedIndK0Add ℬ 𝒜 M ℳ hM
  map_add' := map_add _
  map_smul' := K0.map_smul_of_shift _ (balancedIndK0Add_shift ℬ 𝒜 M ℳ hM)

theorem balancedIndK0_of (N : GProj 𝒜) :
    balancedIndK0 ℬ 𝒜 M ℳ hM (K0.of N) = K0.of (balancedIndGProj ℬ 𝒜 M ℳ hM N) :=
  balancedIndK0Add_of ℬ 𝒜 M ℳ hM N

end BalancedInd

end Categorification.Graded


namespace Categorification.WeightedKLR

open FullChamber GalleryAlgebra Juxtapose MulOpposite Categorification.Graded DirectSum
open scoped TensorProduct

universe u v w

variable {I : Type u} [DecidableEq I] {𝕜 : Type v} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜]

namespace Juxtapose

section CommRing

variable {k : Type w} [CommRing k] {Γ : WeightedGraph I 𝕜 k} (G : GradingDatum Γ)
  {a b c d : I →₀ ℕ}

/-- `(W_{a+c} ⊗ W_{b+d}) e'` is a graded left `W_{a+c} ⊗ W_{b+d}`-module. -/
instance : SetLike.GradedSMul (tensorGrading (G.klrGrade (a + c)) (G.klrGrade (b + d)))
    (middleTopGrading G a b c d) where
  smul_mem _ _ _ _ hz ht :=
    SetLike.GradedMul.mul_mem (A := tensorGrading (G.klrGrade (a + c)) (G.klrGrade (b + d)))
      hz ht

end CommRing

end Juxtapose

namespace GradingDatum

section Field

variable {k : Type w} [Field k] {Γ : WeightedGraph I 𝕜 k} (G : GradingDatum Γ)
  (a b c d : I →₀ ℕ)

/-- **Graded induction from the middle parabolic**:
`(W_{a+c} ⊗ W_{b+d}) e' ⊗_{(W_a ⊗ W_b) ⊗ (W_c ⊗ W_d)} N` as a finitely generated graded projective
`W_{a+c} ⊗ W_{b+d}`-module, induction along `(ι_{a,c} ⊗ ι_{b,d}) ∘ (exchange)`, with no shift. -/
def middleIndGProj (N : GProj (A := MiddleAlg k Γ a b c d) (middleAlgGrading G a b c d)) :
    GProj (tensorGrading (G.klrGrade (a + c)) (G.klrGrade (b + d))) :=
  balancedIndGProj (A := MiddleAlg k Γ a b c d)
    (tensorGrading (G.klrGrade (a + c)) (G.klrGrade (b + d))) (middleAlgGrading G a b c d)
    (MiddleTop k Γ a b c d) (middleTopGrading G a b c d)
    (fun _ _ _ _ ht hr => op_smul_mem_middleTopGrading G ht hr) N

/-- **Graded induction from the middle parabolic on Grothendieck groups**: the
`ℤ[q, q⁻¹]`-linear map `K₀((W_a ⊗ W_b) ⊗ (W_c ⊗ W_d)) → K₀(W_{a+c} ⊗ W_{b+d})`,
`[N] ↦ [(W_{a+c} ⊗ W_{b+d}) e' ⊗ N]`. -/
def middleIndK0 : K0 (A := MiddleAlg k Γ a b c d) (middleAlgGrading G a b c d) →ₗ[LaurentPolynomial ℤ]
    K0 (tensorGrading (G.klrGrade (a + c)) (G.klrGrade (b + d))) :=
  balancedIndK0 (A := MiddleAlg k Γ a b c d)
    (tensorGrading (G.klrGrade (a + c)) (G.klrGrade (b + d))) (middleAlgGrading G a b c d)
    (MiddleTop k Γ a b c d) (middleTopGrading G a b c d)
    (fun _ _ _ _ ht hr => op_smul_mem_middleTopGrading G ht hr)

theorem middleIndK0_of (N : GProj (A := MiddleAlg k Γ a b c d) (middleAlgGrading G a b c d)) :
    G.middleIndK0 a b c d (K0.of N) = K0.of (G.middleIndGProj a b c d N) :=
  balancedIndK0_of _ _ _ _ _ N

end Field

end GradingDatum

end Categorification.WeightedKLR

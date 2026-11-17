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

* `GradingDatum.middleIndGProj`: `(W_{a+c} ⊗ W_{b+d}) e' ⊗_{(W_a ⊗ W_b) ⊗ (W_c ⊗ W_d)} N` as a
  finitely generated graded projective module.
* `GradingDatum.middleIndK0`: the `ℤ[q, q⁻¹]`-linear induction from the middle parabolic on graded
  `K₀`.
* `ResIndPiece.map_of_middleIndGProj`: the class of a piece is the transported class of the
  twisted `Ind ∘ Res`.
* `ResIndPiece.twistK0Graded`, `ResIndPiece.of_tensorGProj_eq_twistK0Graded`.
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

namespace ResIndPiece

open Juxtapose

section Twist

attribute [local instance] InductionAlong.Res.moduleK InductionAlong.Res.isScalarTowerK

variable {k : Type w} [Field k] {Γ : WeightedGraph I 𝕜 k} {ν' ν'' ν₁ ν₂ : I →₀ ℕ}
  (L : ShuffleLayout ν' ν'' ν₁ ν₂) (G : GradingDatum Γ) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
  (hS : Γ.Standing) (P : GProj (G.klrGrade ν')) (Q : GProj (G.klrGrade ν''))

/-- `P` as a graded `W_{a+b}`-module, through `W_{a+b} = W_{ν'}`. -/
abbrev leftResG : GProj (G.klrGrade (L.a + L.b)) :=
  GProj.restrict (castW k Γ L.hab).symm (fun _ _ h => G.castW_mem_klrGrade L.hab h) P

/-- `Q` as a graded `W_{c+d}`-module, through `W_{c+d} = W_{ν''}`. -/
abbrev rightResG : GProj (G.klrGrade (L.c + L.d)) :=
  GProj.restrict (castW k Γ L.hcd).symm (fun _ _ h => G.castW_mem_klrGrade L.hcd h) Q

/-- `P` as an ungraded finitely generated projective module. -/
abbrev fgP : FGProj k (WeightedKLRAlgebra k Γ ν') := FGProj.of P.carrier

/-- `Q` as an ungraded finitely generated projective module. -/
abbrev fgQ : FGProj k (WeightedKLRAlgebra k Γ ν'') := FGProj.of Q.carrier

/-- `Res_{a,b} P ⊠ Res_{c,d} Q` as a graded module over `(W_a ⊗ W_b) ⊗ (W_c ⊗ W_d)`. -/
abbrev resExtG : GProj (A := MiddleAlg k Γ L.a L.b L.c L.d) (middleAlgGrading G L.a L.b L.c L.d) :=
  (G.resGProj L.a L.b hD hZ hS (leftResG L G P)).extTensor
    (G.resGProj L.c L.d hD hZ hS (rightResG L G Q))

/-- `Res_{a,b} P ⊠ Res_{c,d} Q`, from the idempotent truncations to the restrictions. -/
def resExtEquiv : (resExtG L G hD hZ hS P Q).carrier ≃ₗ[MiddleAlg k Γ L.a L.b L.c L.d]
    ExtTensor k (res k Γ L.a L.b (leftRes L (fgP G P)).carrier)
      (res k Γ L.c L.d (rightRes L (fgQ G Q)).carrier) :=
  ExtTensor.congr (resIdemWEquivRes (leftResG L G P).carrier)
    (resIdemWEquivRes (rightResG L G Q).carrier)

/-- The induced module `(W_{a+c} ⊗ W_{b+d}) e' ⊗ (Res_{a,b} P ⊠ Res_{c,d} Q)` and the piece
`ResIndPiece L ⊗ (P ⊠ Q)`, `t ⊗ r ↦ (t ⊗ e) ⊗ r`, as a `k`-linear map. -/
def middleIndPieceG : (G.middleIndGProj L.a L.b L.c L.d (resExtG L G hD hZ hS P Q)).carrier →ₗ[k]
    (tensorGProj L G hD hZ hS (P.extTensor Q)).carrier :=
  (resTwistEquiv L (fgP G P) (fgQ G Q)).toLinearMap ∘ₗ
    ((BalancedTensor.congrRight (k := k)
      (B := WeightedKLRAlgebra k Γ (L.a + L.c) ⊗[k] WeightedKLRAlgebra k Γ (L.b + L.d))
      (M := MiddleTop k Γ L.a L.b L.c L.d) (resExtEquiv L G hD hZ hS P Q)).toLinearMap.restrictScalars k)

theorem middleIndPieceG_bijective : Function.Bijective (middleIndPieceG L G hD hZ hS P Q) :=
  (middleIndPieceEquiv L (fgP G P) (fgQ G Q) (FGProj.of (resExtG L G hD hZ hS P Q).carrier)
    (resExtEquiv L G hD hZ hS P Q)).bijective

theorem middleIndPieceG_smul
    (z : WeightedKLRAlgebra k Γ (L.a + L.c) ⊗[k] WeightedKLRAlgebra k Γ (L.b + L.d))
    (x : (G.middleIndGProj L.a L.b L.c L.d (resExtG L G hD hZ hS P Q)).carrier) :
    middleIndPieceG L G hD hZ hS P Q (z • x) = L.leftEquiv k Γ z • middleIndPieceG L G hD hZ hS P Q x :=
  middleIndPieceEquiv_smul L (fgP G P) (fgQ G Q) (FGProj.of (resExtG L G hD hZ hS P Q).carrier)
    (resExtEquiv L G hD hZ hS P Q) z x

theorem middleIndPieceG_preservesGrading :
    PreservesGrading (G.middleIndGProj L.a L.b L.c L.d (resExtG L G hD hZ hS P Q)).grading
      (tensorGProj L G hD hZ hS (P.extTensor Q)).grading (middleIndPieceG L G hD hZ hS P Q) := by
  intro d x hx
  refine balancedGrading_map_mem _ (middleIndPieceG L G hD hZ hS P Q) (fun i j t r ht hr => ?_) hx
  have hres : resVal L (fgP G P) (fgQ G Q) (resExtEquiv L G hD hZ hS P Q r) ∈
      ExtTensor.grading P.grading Q.grading j :=
    ExtTensor.grading_map_mem _ _ _
      (resVal L (fgP G P) (fgQ G Q) ∘ₗ
        (resExtEquiv L G hD hZ hS P Q).toLinearMap.restrictScalars k)
      (fun _ _ _ _ h1 h2 => ExtTensor.tmul_mem_grading h1 h2) hr
  rw [show i + j = i + 0 + j by rw [add_zero]]
  exact tmul_mem_balancedGrading
    (tmul_mem_balancedGrading ht (Juxtapose.middleBot_one_mem G)) hres

/-- **The piece as an induced module, in graded `K₀`**: transported along
`W_{a+c} ⊗ W_{b+d} ≅ W_{ν₁} ⊗ W_{ν₂}`, the class of
`(W_{a+c} ⊗ W_{b+d}) e' ⊗ (Res_{a,b} P ⊠ Res_{c,d} Q)` is the class of
`ResIndPiece L ⊗ (P ⊠ Q)` with the unshifted grading. -/
theorem map_of_middleIndGProj :
    K0.map (L.leftEquiv k Γ) (fun _ _ h => L.leftEquiv_symm_mem G h)
        (K0.of (G.middleIndGProj L.a L.b L.c L.d (resExtG L G hD hZ hS P Q))) =
      K0.of (tensorGProj L G hD hZ hS (P.extTensor Q)) := by
  let e := AddEquiv.ofBijective (middleIndPieceG L G hD hZ hS P Q).toAddMonoidHom
    (middleIndPieceG_bijective L G hD hZ hS P Q)
  refine K0.map_of_semilinear _ _ _ _ e (middleIndPieceG_smul L G hD hZ hS P Q)
    (fun _ _ hx => middleIndPieceG_preservesGrading L G hD hZ hS P Q hx) (fun d y hy => ?_)
  refine mem_of_injective_of_mem (middleIndPieceG_preservesGrading L G hD hZ hS P Q)
    (middleIndPieceG_bijective L G hD hZ hS P Q).1 ?_
  have : middleIndPieceG L G hD hZ hS P Q (e.symm y) = y := e.apply_symm_apply y
  rw [this]
  exact hy

/-- **The twisted `Ind ∘ Res` on graded `K₀`**: the `ℤ[q, q⁻¹]`-bilinear map
`x, y ↦ (Ind_{a;c} ⊗ Ind_{b;d}) ∘ (exchange) (Δ_{a;b} x ⊠ Δ_{c;d} y)`, from
`K₀(W_{ν'}) × K₀(W_{ν''})` to `K₀(W_{ν₁} ⊗ W_{ν₂})`, with `W_{ν'} = W_{a+b}`,
`W_{ν''} = W_{c+d}` and `W_{a+c} ⊗ W_{b+d} = W_{ν₁} ⊗ W_{ν₂}`. -/
def twistK0Graded : K0 (G.klrGrade ν') →ₗ[LaurentPolynomial ℤ] K0 (G.klrGrade ν'') →ₗ[
    LaurentPolynomial ℤ] K0 (tensorGrading (G.klrGrade ν₁) (G.klrGrade ν₂)) :=
  (((K0.extTensor (tensorGrading (G.klrGrade L.a) (G.klrGrade L.b))
      (tensorGrading (G.klrGrade L.c) (G.klrGrade L.d))).compl₂
      (G.resK0 L.c L.d hD hZ hS ∘ₗ
        K0.map (castW k Γ L.hcd).symm (fun _ _ h => G.castW_mem_klrGrade L.hcd h))).comp
      (G.resK0 L.a L.b hD hZ hS ∘ₗ
        K0.map (castW k Γ L.hab).symm (fun _ _ h => G.castW_mem_klrGrade L.hab h))).compr₂
    (K0.map (L.leftEquiv k Γ) (fun _ _ h => L.leftEquiv_symm_mem G h) ∘ₗ
      G.middleIndK0 L.a L.b L.c L.d)

/-- The class of a graded Mackey piece, with its unshifted grading, is the twisted
`Ind ∘ Res` of `[P]` and `[Q]` (Webster, arXiv:1209.2463v4, proof of Theorem 2.19). -/
theorem of_tensorGProj_eq_twistK0Graded :
    K0.of (tensorGProj L G hD hZ hS (P.extTensor Q)) =
      twistK0Graded L G hD hZ hS (K0.of P) (K0.of Q) := by
  rw [← map_of_middleIndGProj L G hD hZ hS P Q, ← G.middleIndK0_of, ← K0.extTensor_of,
    ← G.resK0_of, ← G.resK0_of]
  simp only [twistK0Graded, LinearMap.compr₂_apply, LinearMap.comp_apply,
    LinearMap.compl₂_apply]
  have h₁ : K0.map (castW k Γ L.hab).symm (fun _ _ h => G.castW_mem_klrGrade L.hab h) (K0.of P) =
      K0.of (leftResG L G P) := K0.map_of _ _ P
  have h₂ : K0.map (castW k Γ L.hcd).symm (fun _ _ h => G.castW_mem_klrGrade L.hcd h) (K0.of Q) =
      K0.of (rightResG L G Q) := K0.map_of _ _ Q
  rw [h₁, h₂]

end Twist

end ResIndPiece

section TwistedMackey

variable {k : Type w} [Field k] {Γ : WeightedGraph I 𝕜 k} {ν' ν'' ν₁ ν₂ : I →₀ ℕ}

/-- **The graded Mackey formula in twisted form** (B. Webster, arXiv:1209.2463v4, proof of
Theorem 2.19; after Khovanov–Lauda, arXiv:0803.4121v2, Proposition 2.18), over a field `k`,
under the standing hypothesis. For `ν₁ + ν₂ = ν' + ν''` there are four-block layouts `L i`
(`ν' = a + b`, `ν'' = c + d`, `ν₁ = a + c`, `ν₂ = b + d`), one for each shuffle type, with
`Δ_{ν₁;ν₂}(x · y) = ∑ᵢ q^{sᵢ} (Ind_{a;c} ⊗ Ind_{b;d}) ∘ (exchange) (Δ_{a;b} x ⊠ Δ_{c;d} y)`
for all `x ∈ K₀(W_{ν'})`, `y ∈ K₀(W_{ν''})`, where `sᵢ = middleShift G a b c d` for the blocks
of `L i`. Weighted KLR algebras of equal dimension vectors are identified by `castW`. -/
theorem exists_resK0_indK0_eq_sum_twistK0Graded (G : GradingDatum Γ) (hD : Γ.Dagger)
    (hZ : Γ.NoZeroLoops) (hS : Γ.Standing) (hν₁ : ν₁ + ν₂ = ν' + ν'') :
    ∃ (n : ℕ) (L : Fin n → ShuffleLayout ν' ν'' ν₁ ν₂),
      Function.Injective (fun i => ⇑(L i).c) ∧
      Set.range (fun i => ⇑(L i).c) = Set.range (shuffleType (ν := ν' + ν'') ν' ν₁) ∧
      ∀ (x : K0 (G.klrGrade ν')) (y : K0 (G.klrGrade ν'')),
        G.resK0 ν₁ ν₂ hD hZ hS (K0.map (castW k Γ hν₁.symm)
            (fun _ _ h => G.castW_symm_mem_klrGrade hν₁.symm h) (G.indK0 ν' ν'' x y)) =
          ∑ i, (LaurentPolynomial.T (middleShift G (L i).a (L i).b (L i).c (L i).d) :
              LaurentPolynomial ℤ) •
            ResIndPiece.twistK0Graded (L i) G hD hZ hS x y := by
  obtain ⟨n, L, hinj, hrange, h⟩ := exists_resK0_indK0_eq_sum_graded (k := k) G hD hZ hS hν₁
  refine ⟨n, L, hinj, hrange, fun x y => ?_⟩
  induction x using K0.induction_on with
  | of P =>
    induction y using K0.induction_on with
    | of Q =>
      rw [h P Q]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ResIndPiece.of_tensorGProj_eq_twistK0Graded]
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy', smul_add, Finset.sum_add_distrib]
    | neg y hy => simp only [map_neg, hy, smul_neg, Finset.sum_neg_distrib]
  | zero => simp
  | add x x' hx hx' =>
    simp only [map_add, LinearMap.add_apply, hx, hx', smul_add, Finset.sum_add_distrib]
  | neg x hx => simp only [map_neg, LinearMap.neg_apply, hx, smul_neg, Finset.sum_neg_distrib]

end TwistedMackey

end Categorification.WeightedKLR

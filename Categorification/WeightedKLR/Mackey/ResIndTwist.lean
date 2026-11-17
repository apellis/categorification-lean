/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.ResIndK0

/-!
# The Mackey pieces as twisted `Ind ∘ Res`

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, proof of
Theorem 2.19 (the Mackey filtration of Khovanov–Lauda, arXiv:0803.4121v2, Proposition 2.18).
For a four-block layout `ν' = a + b`, `ν'' = c + d`, `ν₁ = a + c`, `ν₂ = b + d`
(`ShuffleLayout`), the piece `ResIndPiece L ⊗_{W_{ν'} ⊗ W_{ν''}} (P ⊠ Q)` is the module obtained
from `P` and `Q` by restricting `P` to `W_a ⊗ W_b` and `Q` to `W_c ⊗ W_d`, exchanging the two
middle factors `W_b` and `W_c`, and inducing along `ι_{a,c} ⊗ ι_{b,d}`:
`(W_{a+c} ⊗ W_{b+d}) e' ⊗_{(W_a ⊗ W_b) ⊗ (W_c ⊗ W_d)} (Res_{a,b} P ⊠ Res_{c,d} Q)`, where the
middle algebra acts on `(W_{a+c} ⊗ W_{b+d}) e'` through `(ι_{a,c} ⊗ ι_{b,d}) ∘ (exchange)`
(`Juxtapose.middleTop`).

On Grothendieck groups this gives the Mackey formula in the form
`Δ_{ν₁;ν₂}(x · y) = ∑ (Ind_{a;c} ⊗ Ind_{b;d}) ∘ (exchange) (Δ_{a;b} x ⊠ Δ_{c;d} y)`, the sum
over the shuffle types `c` (`exists_resK0_indK0_eq_sum_twistK0`). The identity is between
ungraded Grothendieck groups, so the grading shift of each term does not appear.

## Main results

* `ProjK0.extTensor`: the external product `K₀(A) × K₀(B) → K₀(A ⊗ B)`, `[P], [Q] ↦ [P ⊠ Q]`.
* `Juxtapose.middleIndK0`: induction `K₀((W_a ⊗ W_b) ⊗ (W_c ⊗ W_d)) → K₀(W_{a+c} ⊗ W_{b+d})`
  along `(ι_{a,c} ⊗ ι_{b,d}) ∘ (exchange)`.
* `Juxtapose.resTwistEquiv`: `(W_{a+c} ⊗ W_{b+d}) e' ⊗ (Res P ⊠ Res Q) ≅ MiddleTensor ⊗ (P ⊠ Q)`.
* `ResIndPiece.twistK0`: `x, y ↦ (Ind ⊗ Ind)(exchange)(Δ_{a;b} x ⊠ Δ_{c;d} y)`.
* `ResIndPiece.tensorK0_eq_twistK0`: the class of the piece is the twisted `Ind ∘ Res`.
* `exists_resK0_indK0_eq_sum_twistK0`: the Mackey formula on Grothendieck groups.
-/

noncomputable section

namespace Categorification

open scoped TensorProduct

/-! ### The external product on `K₀` -/

namespace ProjK0

universe u v

variable {k : Type v} [CommRing k] {A B : Type u} [Ring A] [Algebra k A] [Ring B] [Algebra k B]

/-- `P ⊠ Q` as a finitely generated projective `A ⊗ B`-module. -/
def extTensorProj (P : FGProj k A) (Q : FGProj k B) : FGProj k (A ⊗[k] B) :=
  haveI : Module.Projective (A ⊗[k] B) (ExtTensor k P.carrier Q.carrier) := ExtTensor.projective
  haveI : Module.Finite (A ⊗[k] B) (ExtTensor k P.carrier Q.carrier) := ExtTensor.finite
  FGProj.of (ExtTensor k P.carrier Q.carrier)

/-- **The external product on Grothendieck groups**: `[P], [Q] ↦ [P ⊠ Q]`, biadditive. -/
def extTensor : ProjK0 k A →+ ProjK0 k B →+ ProjK0 k (A ⊗[k] B) :=
  lift₂ (fun P Q => of (extTensorProj P Q))
    (fun _ _ Q e => of_eq_of_iso (ExtTensor.congr (k := k) e (LinearEquiv.refl _ Q.carrier)))
    (fun P _ _ f => of_eq_of_iso (ExtTensor.congr (k := k) (LinearEquiv.refl _ P.carrier) f))
    (fun P P' Q => by
      rw [← of_prod]
      exact of_eq_of_iso (ExtTensor.prodLeft (k := k) (P := P.carrier) (P' := P'.carrier)
        (Q := Q.carrier) (A := A) (B := B)))
    (fun P Q Q' => by
      rw [← of_prod]
      exact of_eq_of_iso (ExtTensor.prodRight (k := k) (P := P.carrier) (Q := Q.carrier)
        (Q' := Q'.carrier) (A := A) (B := B)))

@[simp] theorem extTensor_of (P : FGProj k A) (Q : FGProj k B) :
    extTensor (of P) (of Q) = of (extTensorProj P Q) :=
  lift₂_of _ _ _ _ _ P Q

end ProjK0

namespace WeightedKLR

open FullChamber GalleryAlgebra InductionAlong MulOpposite

universe u v w

variable {I : Type u} [DecidableEq I] {𝕜 : Type v} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type w} [CommRing k] {Γ : WeightedGraph I 𝕜 k}

namespace Juxtapose

/-! ### Restriction of a module, `k`-linearly -/

section ResK

variable {μ μ' : I →₀ ℕ} (M : Type*) [AddCommGroup M] [Module k M]
  [Module (WeightedKLRAlgebra k Γ (μ + μ')) M] [IsScalarTower k (WeightedKLRAlgebra k Γ (μ + μ')) M]

attribute [local instance] Res.moduleK Res.isScalarTowerK

theorem res_val_smulK (c : k) (r : res k Γ μ μ' M) : (c • r).val = c • r.val := by
  change inductionRingHom k Γ μ μ' (algebraMap k _ c) • r.val = c • r.val
  rw [Algebra.algebraMap_eq_smul_one, inductionRingHom_smul, smul_assoc, r.prop]

variable (k Γ μ μ') in
/-- `Res M → M`, `k`-linear. -/
def resValK : res k Γ μ μ' M →ₗ[k] M where
  toFun r := r.val
  map_add' _ _ := rfl
  map_smul' c r := res_val_smulK M c r

variable (k Γ μ μ') in
/-- `M → Res M`, `m ↦ e m`, `k`-linear. -/
def resProjK : M →ₗ[k] res k Γ μ μ' M where
  toFun m := Res.mk (inductionRingHom k Γ μ μ' 1 • m) (by
    rw [smul_smul, ← map_mul, one_mul])
  map_add' m m' := Res.ext (smul_add _ m m')
  map_smul' c m := Res.ext (by
    rw [res_val_smulK, Res.val_mk, Res.val_mk, RingHom.id_apply, smul_comm])

theorem resValK_apply (r : res k Γ μ μ' M) : resValK k Γ μ μ' M r = r.val := rfl

theorem resProjK_val (m : M) :
    (resProjK k Γ μ μ' M m).val = inductionRingHom k Γ μ μ' 1 • m := rfl

theorem resProjK_resValK (r : res k Γ μ μ' M) : resProjK k Γ μ μ' M (resValK k Γ μ μ' M r) = r :=
  Res.ext r.prop

theorem resProjK_smul (x : WeightedKLRAlgebra k Γ μ ⊗[k] WeightedKLRAlgebra k Γ μ') (m : M) :
    resProjK k Γ μ μ' M (inductionRingHom k Γ μ μ' x • m) = x • resProjK k Γ μ μ' M m :=
  Res.ext (by
    rw [Res.val_smul, resProjK_val, resProjK_val, smul_smul, smul_smul, ← map_mul, ← map_mul,
      one_mul, mul_one])

end ResK

/-! ### Restriction of an external product -/

section ResTensor

attribute [local instance] Res.moduleK Res.isScalarTowerK

variable {a b c d : I →₀ ℕ}
  (P : Type*) [AddCommGroup P] [Module k P] [Module (WeightedKLRAlgebra k Γ (a + b)) P]
  [IsScalarTower k (WeightedKLRAlgebra k Γ (a + b)) P]
  (Q : Type*) [AddCommGroup Q] [Module k Q] [Module (WeightedKLRAlgebra k Γ (c + d)) Q]
  [IsScalarTower k (WeightedKLRAlgebra k Γ (c + d)) Q]

variable (k Γ a b c d) in
/-- `Res_{a,b} P ⊠ Res_{c,d} Q → P ⊠ Q`. -/
def resTensorVal : ExtTensor k (res k Γ a b P) (res k Γ c d Q) →ₗ[k] ExtTensor k P Q :=
  ExtTensor.equivTensor.symm.toLinearMap ∘ₗ
    (TensorProduct.map (resValK k Γ a b P) (resValK k Γ c d Q)) ∘ₗ
    ExtTensor.equivTensor.toLinearMap

variable (k Γ a b c d) in
/-- `P ⊠ Q → Res_{a,b} P ⊠ Res_{c,d} Q`, `v ↦ e v`. -/
def resTensorProj : ExtTensor k P Q →ₗ[k] ExtTensor k (res k Γ a b P) (res k Γ c d Q) :=
  ExtTensor.equivTensor.symm.toLinearMap ∘ₗ
    (TensorProduct.map (resProjK k Γ a b P) (resProjK k Γ c d Q)) ∘ₗ
    ExtTensor.equivTensor.toLinearMap

theorem resTensorVal_tmul (p : res k Γ a b P) (q : res k Γ c d Q) :
    resTensorVal k Γ a b c d P Q (ExtTensor.tmul p q) = ExtTensor.tmul p.val q.val := rfl

theorem resTensorProj_tmul (p : P) (q : Q) :
    resTensorProj k Γ a b c d P Q (ExtTensor.tmul p q) =
      ExtTensor.tmul (resProjK k Γ a b P p) (resProjK k Γ c d Q q) := rfl

theorem resTensorVal_smul (m : MiddleAlg k Γ a b c d)
    (r : ExtTensor k (res k Γ a b P) (res k Γ c d Q)) :
    resTensorVal k Γ a b c d P Q (m • r) = middleBot k Γ a b c d m • resTensorVal k Γ a b c d P Q r := by
  induction m using TensorProduct.inductionOn with
  | tmul x y =>
    induction r using ExtTensor.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | tmul p q =>
      rw [ExtTensor.smul_tmul, resTensorVal_tmul, resTensorVal_tmul]
      change ExtTensor.tmul (inductionRingHom k Γ a b x • p.val)
          (inductionRingHom k Γ c d y • q.val) =
        (inductionRingHom k Γ a b x ⊗ₜ[k] inductionRingHom k Γ c d y) • ExtTensor.tmul p.val q.val
      rw [ExtTensor.smul_tmul]
    | add r r' hr hr' => rw [smul_add, map_add, hr, hr', map_add, smul_add]
  | add m m' hm hm' => rw [add_smul, map_add, hm, hm', map_add, add_smul]

theorem resTensorProj_smul (m : MiddleAlg k Γ a b c d) (v : ExtTensor k P Q) :
    resTensorProj k Γ a b c d P Q (middleBot k Γ a b c d m • v) = m • resTensorProj k Γ a b c d P Q v := by
  induction m using TensorProduct.inductionOn with
  | tmul x y =>
    induction v using ExtTensor.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | tmul p q =>
      change resTensorProj k Γ a b c d P Q
          ((inductionRingHom k Γ a b x ⊗ₜ[k] inductionRingHom k Γ c d y) • ExtTensor.tmul p q) = _
      rw [ExtTensor.smul_tmul, resTensorProj_tmul, resTensorProj_tmul, resProjK_smul,
        resProjK_smul, ExtTensor.smul_tmul]
    | add v v' hv hv' => rw [smul_add, map_add, hv, hv', map_add, smul_add]
  | add m m' hm hm' => rw [map_add, add_smul, map_add, hm, hm', add_smul]

theorem resTensorProj_val (r : ExtTensor k (res k Γ a b P) (res k Γ c d Q)) :
    resTensorProj k Γ a b c d P Q (resTensorVal k Γ a b c d P Q r) = r := by
  induction r using ExtTensor.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul p q =>
    rw [resTensorVal_tmul, resTensorProj_tmul]
    exact congrArg₂ ExtTensor.tmul (resProjK_resValK P p) (resProjK_resValK Q q)
  | add r r' hr hr' => rw [map_add, map_add, hr, hr']

theorem resTensorVal_proj (v : ExtTensor k P Q) :
    resTensorVal k Γ a b c d P Q (resTensorProj k Γ a b c d P Q v) = middleBot k Γ a b c d 1 • v := by
  rw [middleBot_one]
  induction v using ExtTensor.induction_on with
  | zero => rw [map_zero, map_zero, smul_zero]
  | tmul p q => rw [resTensorProj_tmul, resTensorVal_tmul, ExtTensor.smul_tmul]; rfl
  | add v v' hv hv' => rw [map_add, map_add, hv, hv', smul_add]

end ResTensor

/-! ### Induction from the middle parabolic -/

section MiddleInd

variable {a b c d : I →₀ ℕ}

variable (a b c d) in
/-- `(W_{a+c} ⊗ W_{b+d}) e' ⊗_{(W_a ⊗ W_b) ⊗ (W_c ⊗ W_d)} N` as a finitely generated
projective `W_{a+c} ⊗ W_{b+d}`-module. -/
def middleIndProj (N : FGProj k (MiddleAlg k Γ a b c d)) :
    FGProj k (WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d)) :=
  haveI : Module.Projective (WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d))
    (BalancedTensor k (WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d))
      (MiddleAlg k Γ a b c d) (MiddleTop k Γ a b c d) N.carrier) := BalancedTensor.projective
  haveI : Module.Finite (WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d))
    (BalancedTensor k (WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d))
      (MiddleAlg k Γ a b c d) (MiddleTop k Γ a b c d) N.carrier) := BalancedTensor.finite
  FGProj.of (BalancedTensor k (WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d))
    (MiddleAlg k Γ a b c d) (MiddleTop k Γ a b c d) N.carrier)

variable (k Γ a b c d) in
/-- **Induction from the middle parabolic on Grothendieck groups**:
`K₀((W_a ⊗ W_b) ⊗ (W_c ⊗ W_d)) → K₀(W_{a+c} ⊗ W_{b+d})`, `[N] ↦ [(W_{a+c} ⊗ W_{b+d}) e' ⊗ N]`,
induction along `(ι_{a,c} ⊗ ι_{b,d}) ∘ (exchange of the middle factors)`. -/
def middleIndK0 : ProjK0 k (MiddleAlg k Γ a b c d) →+
    ProjK0 k (WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d)) :=
  ProjK0.lift (fun N => ProjK0.of (middleIndProj a b c d N))
    (fun _ _ e => ProjK0.of_eq_of_iso (BalancedTensor.congrRight e))
    (fun N N' => by
      rw [← ProjK0.of_prod]
      exact ProjK0.of_eq_of_iso (BalancedTensor.prodRight k _ _ _ _ _))

@[simp] theorem middleIndK0_of (N : FGProj k (MiddleAlg k Γ a b c d)) :
    middleIndK0 k Γ a b c d (ProjK0.of N) = ProjK0.of (middleIndProj a b c d N) :=
  ProjK0.lift_of _ _ _ N

end MiddleInd

end Juxtapose

end WeightedKLR

end Categorification

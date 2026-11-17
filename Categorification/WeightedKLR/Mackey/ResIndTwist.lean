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

/-! ### The unit `e` of `MiddleBot` -/

section MiddleBotUnit

variable {a b c d : I →₀ ℕ}

variable (k Γ a b c d) in
/-- The idempotent `e = (ι_{a,b} ⊗ ι_{c,d})(1)` as an element of `MiddleBot`. -/
def middleBotUnit : MiddleBot k Γ a b c d :=
  ⟨middleBot k Γ a b c d 1, by rw [mem_middleBotSub, ← middleBot_mul, one_mul]⟩

theorem middleBot_smul_middleBotUnit (m : MiddleAlg k Γ a b c d) :
    m • middleBotUnit k Γ a b c d =
      middleBotMulRight (middleBot k Γ a b c d m) (middleBotUnit k Γ a b c d) :=
  Subtype.ext (by
    rw [coe_smul_middleBot, coe_middleBotMulRight, middleBotUnit, ← middleBot_mul,
      ← middleBot_mul, mul_one, one_mul])

theorem middleBotMulRight_middleBotUnit (y : MiddleBot k Γ a b c d) :
    middleBotMulRight y.1 (middleBotUnit k Γ a b c d) = y :=
  Subtype.ext (by rw [coe_middleBotMulRight]; exact y.2)

end MiddleBotUnit

end Juxtapose

/-! ### The piece as a twisted `Ind ∘ Res` -/

namespace ResIndPiece

open Juxtapose

section Twist

attribute [local instance] Res.moduleK Res.isScalarTowerK

variable {ν' ν'' ν₁ ν₂ : I →₀ ℕ} (L : ShuffleLayout ν' ν'' ν₁ ν₂)

theorem op_smul_eq_middleCornerMap
    (w : WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'') (x : ResIndPiece k Γ L) :
    op w • x = middleCornerMap
      (1 : WeightedKLRAlgebra k Γ (L.a + L.c) ⊗[k] WeightedKLRAlgebra k Γ (L.b + L.d))
      ((L.rightEquiv k Γ).symm w) x := rfl

/-- `t ↦ t ⊗ e`. -/
def middleTopUnit : MiddleTop k Γ L.a L.b L.c L.d →ₗ[k] ResIndPiece k Γ L :=
  (BalancedTensor.mkBil k
    (WeightedKLRAlgebra k Γ (L.a + L.c) ⊗[k] WeightedKLRAlgebra k Γ (L.b + L.d))
    (MiddleAlg k Γ L.a L.b L.c L.d) (MiddleTop k Γ L.a L.b L.c L.d)
    (MiddleBot k Γ L.a L.b L.c L.d)).flip (middleBotUnit k Γ L.a L.b L.c L.d)

theorem middleTopUnit_apply (t : MiddleTop k Γ L.a L.b L.c L.d) :
    middleTopUnit L t = BalancedTensor.tmul t (middleBotUnit k Γ L.a L.b L.c L.d) := rfl

theorem op_smul_middleTopUnit (m : MiddleAlg k Γ L.a L.b L.c L.d)
    (t : MiddleTop k Γ L.a L.b L.c L.d) :
    op (L.rightEquiv k Γ (middleBot k Γ L.a L.b L.c L.d m)) • middleTopUnit L t =
      middleTopUnit L (op m • t) := by
  rw [op_smul_eq_middleCornerMap, AlgEquiv.symm_apply_apply, middleTopUnit_apply,
    middleTopUnit_apply, middleCornerMap_tmul, one_smul, BalancedTensor.op_smul_tmul,
    middleBot_smul_middleBotUnit]

theorem middleTopUnit_smul
    (z : WeightedKLRAlgebra k Γ (L.a + L.c) ⊗[k] WeightedKLRAlgebra k Γ (L.b + L.d))
    (t : MiddleTop k Γ L.a L.b L.c L.d) :
    middleTopUnit L (z • t) = L.leftEquiv k Γ z • middleTopUnit L t := by
  rw [smul_left_def, leftAct, middleLeftAct_apply]
  show _ = middleCornerMap ((L.leftEquiv k Γ).symm (L.leftEquiv k Γ z)) 1
    (BalancedTensor.tmul t (middleBotUnit k Γ L.a L.b L.c L.d))
  rw [AlgEquiv.symm_apply_apply, middleCornerMap_tmul, middleTopUnit_apply]
  congr 1
  exact Subtype.ext (mul_one _).symm

variable (P : FGProj k (WeightedKLRAlgebra k Γ ν')) (Q : FGProj k (WeightedKLRAlgebra k Γ ν''))

/-- `P` as a `W_{a+b}`-module. -/
abbrev leftRes : FGProj k (WeightedKLRAlgebra k Γ (L.a + L.b)) :=
  FGProj.restrict (castW k Γ L.hab).symm P

/-- `Q` as a `W_{c+d}`-module. -/
abbrev rightRes : FGProj k (WeightedKLRAlgebra k Γ (L.c + L.d)) :=
  FGProj.restrict (castW k Γ L.hcd).symm Q

/-- `(W_{a+c} ⊗ W_{b+d}) e' ⊗_{(W_a ⊗ W_b) ⊗ (W_c ⊗ W_d)} (Res_{a,b} P ⊠ Res_{c,d} Q)`. -/
abbrev twistTensor : Type _ :=
  BalancedTensor k (WeightedKLRAlgebra k Γ (L.a + L.c) ⊗[k] WeightedKLRAlgebra k Γ (L.b + L.d))
    (MiddleAlg k Γ L.a L.b L.c L.d) (MiddleTop k Γ L.a L.b L.c L.d)
    (ExtTensor k (res k Γ L.a L.b (leftRes L P).carrier) (res k Γ L.c L.d (rightRes L Q).carrier))

/-- `ResIndPiece L ⊗_{W_{ν'} ⊗ W_{ν''}} (P ⊠ Q)`. -/
abbrev pieceTensor : Type _ :=
  BalancedTensor k (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
    (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'') (ResIndPiece k Γ L)
    (ExtTensor k P.carrier Q.carrier)

/-- `P ⊠ Q` over `W_{a+b} ⊗ W_{c+d}` is `P ⊠ Q` over `W_{ν'} ⊗ W_{ν''}`. -/
def extCast : ExtTensor k (leftRes L P).carrier (rightRes L Q).carrier →ₗ[k]
    ExtTensor k P.carrier Q.carrier :=
  LinearMap.id

/-- The inverse of `extCast`. -/
def extCastInv : ExtTensor k P.carrier Q.carrier →ₗ[k]
    ExtTensor k (leftRes L P).carrier (rightRes L Q).carrier :=
  LinearMap.id

theorem extCast_extCastInv (v : ExtTensor k P.carrier Q.carrier) :
    extCast L P Q (extCastInv L P Q v) = v := rfl

theorem extCastInv_extCast (v : ExtTensor k (leftRes L P).carrier (rightRes L Q).carrier) :
    extCastInv L P Q (extCast L P Q v) = v := rfl

/-- `P → leftRes P`, the identity. -/
def toLeftRes (p : P.carrier) : (leftRes L P).carrier := p

/-- `Q → rightRes Q`, the identity. -/
def toRightRes (q : Q.carrier) : (rightRes L Q).carrier := q

theorem smul_toLeftRes (x : WeightedKLRAlgebra k Γ (L.a + L.b)) (p : P.carrier) :
    x • toLeftRes L P p = toLeftRes L P (castW k Γ L.hab x • p) := rfl

theorem smul_toRightRes (y : WeightedKLRAlgebra k Γ (L.c + L.d)) (q : Q.carrier) :
    y • toRightRes L Q q = toRightRes L Q (castW k Γ L.hcd y • q) := rfl

theorem extCast_tmul (p : P.carrier) (q : Q.carrier) :
    extCast L P Q (ExtTensor.tmul (toLeftRes L P p) (toRightRes L Q q)) = ExtTensor.tmul p q :=
  rfl

theorem extCast_smul (w : WeightedKLRAlgebra k Γ (L.a + L.b) ⊗[k] WeightedKLRAlgebra k Γ (L.c + L.d))
    (v : ExtTensor k (leftRes L P).carrier (rightRes L Q).carrier) :
    extCast L P Q (w • v) = L.rightEquiv k Γ w • extCast L P Q v := by
  induction w using TensorProduct.inductionOn with
  | tmul x y =>
    induction v using ExtTensor.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | tmul p q =>
      change extCast L P Q ((x ⊗ₜ[k] y) • ExtTensor.tmul (toLeftRes L P p) (toRightRes L Q q)) =
        _ • extCast L P Q (ExtTensor.tmul (toLeftRes L P p) (toRightRes L Q q))
      rw [ExtTensor.smul_tmul, smul_toLeftRes, smul_toRightRes, extCast_tmul, extCast_tmul,
        ShuffleLayout.rightEquiv, Algebra.TensorProduct.congr_apply,
        Algebra.TensorProduct.map_tmul, ExtTensor.smul_tmul]
      rfl
    | add v v' hv hv' => rw [smul_add, map_add, hv, hv', map_add, smul_add]
  | add w w' hw hw' => rw [add_smul, map_add, hw, hw', map_add, add_smul]

theorem extCastInv_smul (w : WeightedKLRAlgebra k Γ (L.a + L.b) ⊗[k] WeightedKLRAlgebra k Γ (L.c + L.d))
    (v : ExtTensor k P.carrier Q.carrier) :
    extCastInv L P Q (L.rightEquiv k Γ w • v) = w • extCastInv L P Q v :=
  congrArg (extCastInv L P Q) (extCast_smul L P Q w (extCastInv L P Q v)).symm

/-- `Res_{a,b} P ⊠ Res_{c,d} Q → P ⊠ Q`. -/
def resVal : ExtTensor k (res k Γ L.a L.b (leftRes L P).carrier)
    (res k Γ L.c L.d (rightRes L Q).carrier) →ₗ[k] ExtTensor k P.carrier Q.carrier :=
  extCast L P Q ∘ₗ resTensorVal k Γ L.a L.b L.c L.d (leftRes L P).carrier (rightRes L Q).carrier

theorem resVal_smul (m : MiddleAlg k Γ L.a L.b L.c L.d)
    (r : ExtTensor k (res k Γ L.a L.b (leftRes L P).carrier)
      (res k Γ L.c L.d (rightRes L Q).carrier)) :
    resVal L P Q (m • r) =
      L.rightEquiv k Γ (middleBot k Γ L.a L.b L.c L.d m) • resVal L P Q r := by
  rw [resVal, LinearMap.comp_apply, LinearMap.comp_apply, resTensorVal_smul, extCast_smul]

/-- `t ⊗ r ↦ (t ⊗ e) ⊗ r`. -/
def twistToPiece : twistTensor L P Q →ₗ[k] pieceTensor L P Q :=
  BalancedTensor.lift ((BalancedTensor.mkBil k
      (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
      (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'') (ResIndPiece k Γ L)
      (ExtTensor k P.carrier Q.carrier)).compl₁₂ (middleTopUnit L) (resVal L P Q))
    fun t m r => by
      rw [LinearMap.compl₁₂_apply, LinearMap.compl₁₂_apply, BalancedTensor.mkBil_apply,
        BalancedTensor.mkBil_apply, resVal_smul, ← BalancedTensor.op_smul_tmul,
        op_smul_middleTopUnit]

theorem twistToPiece_tmul (t : MiddleTop k Γ L.a L.b L.c L.d)
    (r : ExtTensor k (res k Γ L.a L.b (leftRes L P).carrier)
      (res k Γ L.c L.d (rightRes L Q).carrier)) :
    twistToPiece L P Q (BalancedTensor.tmul t r) =
      BalancedTensor.tmul (middleTopUnit L t) (resVal L P Q r) := rfl

/-- `y, v ↦ e (y v)`. -/
def bilBot : MiddleBot k Γ L.a L.b L.c L.d →ₗ[k] ExtTensor k P.carrier Q.carrier →ₗ[k]
    ExtTensor k (res k Γ L.a L.b (leftRes L P).carrier) (res k Γ L.c L.d (rightRes L Q).carrier) :=
  (((Algebra.lsmul k k (ExtTensor k (leftRes L P).carrier (rightRes L Q).carrier)).toLinearMap ∘ₗ
    (middleBotSub k Γ L.a L.b L.c L.d).subtype).compl₂ (extCastInv L P Q)).compr₂
      (resTensorProj k Γ L.a L.b L.c L.d (leftRes L P).carrier (rightRes L Q).carrier)

/-- `t, y, v ↦ t ⊗ e (y v)`. -/
def pieceBil : MiddleTop k Γ L.a L.b L.c L.d →ₗ[k] MiddleBot k Γ L.a L.b L.c L.d →ₗ[k]
    ExtTensor k P.carrier Q.carrier →ₗ[k] twistTensor L P Q :=
  (LinearMap.llcomp k (ExtTensor k P.carrier Q.carrier)
      (ExtTensor k (res k Γ L.a L.b (leftRes L P).carrier)
        (res k Γ L.c L.d (rightRes L Q).carrier)) (twistTensor L P Q) ∘ₗ
    BalancedTensor.mkBil k
      (WeightedKLRAlgebra k Γ (L.a + L.c) ⊗[k] WeightedKLRAlgebra k Γ (L.b + L.d))
      (MiddleAlg k Γ L.a L.b L.c L.d) (MiddleTop k Γ L.a L.b L.c L.d)
      (ExtTensor k (res k Γ L.a L.b (leftRes L P).carrier)
        (res k Γ L.c L.d (rightRes L Q).carrier))).compl₂ (bilBot L P Q)

theorem pieceBil_apply (t : MiddleTop k Γ L.a L.b L.c L.d) (y : MiddleBot k Γ L.a L.b L.c L.d)
    (v : ExtTensor k P.carrier Q.carrier) :
    pieceBil L P Q t y v = BalancedTensor.tmul t
      (resTensorProj k Γ L.a L.b L.c L.d (leftRes L P).carrier (rightRes L Q).carrier
        (y.1 • extCastInv L P Q v)) := rfl

/-- `t ⊗ y, v ↦ t ⊗ e (y v)`. -/
def pieceLin : MiddleTensor k Γ L.a L.b L.c L.d →ₗ[k] ExtTensor k P.carrier Q.carrier →ₗ[k]
    twistTensor L P Q :=
  BalancedTensor.lift (pieceBil L P Q) fun t m y => LinearMap.ext fun v => by
    rw [pieceBil_apply, pieceBil_apply, BalancedTensor.op_smul_tmul, coe_smul_middleBot,
      mul_smul, resTensorProj_smul]

theorem pieceLin_tmul (t : MiddleTop k Γ L.a L.b L.c L.d) (y : MiddleBot k Γ L.a L.b L.c L.d)
    (v : ExtTensor k P.carrier Q.carrier) :
    pieceLin L P Q (BalancedTensor.tmul t y) v = BalancedTensor.tmul t
      (resTensorProj k Γ L.a L.b L.c L.d (leftRes L P).carrier (rightRes L Q).carrier
        (y.1 • extCastInv L P Q v)) := rfl

theorem pieceLin_middleCornerMap_tmul
    (w : WeightedKLRAlgebra k Γ (L.a + L.b) ⊗[k] WeightedKLRAlgebra k Γ (L.c + L.d))
    (t : MiddleTop k Γ L.a L.b L.c L.d) (y : MiddleBot k Γ L.a L.b L.c L.d)
    (v : ExtTensor k P.carrier Q.carrier) :
    pieceLin L P Q (middleCornerMap
      (1 : WeightedKLRAlgebra k Γ (L.a + L.c) ⊗[k] WeightedKLRAlgebra k Γ (L.b + L.d)) w
        (BalancedTensor.tmul t y)) v =
      pieceLin L P Q (BalancedTensor.tmul t y) (L.rightEquiv k Γ w • v) := by
  rw [middleCornerMap_tmul, one_smul, pieceLin_tmul, pieceLin_tmul, coe_middleBotMulRight,
    extCastInv_smul L P Q w v, mul_smul y.1 w (extCastInv L P Q v)]

theorem pieceLin_middleCornerMap
    (w : WeightedKLRAlgebra k Γ (L.a + L.b) ⊗[k] WeightedKLRAlgebra k Γ (L.c + L.d))
    (x : MiddleTensor k Γ L.a L.b L.c L.d) (v : ExtTensor k P.carrier Q.carrier) :
    pieceLin L P Q (middleCornerMap
      (1 : WeightedKLRAlgebra k Γ (L.a + L.c) ⊗[k] WeightedKLRAlgebra k Γ (L.b + L.d)) w x) v =
        pieceLin L P Q x (L.rightEquiv k Γ w • v) := by
  have h : (LinearMap.applyₗ v ∘ₗ pieceLin L P Q ∘ₗ middleCornerMap
      (1 : WeightedKLRAlgebra k Γ (L.a + L.c) ⊗[k] WeightedKLRAlgebra k Γ (L.b + L.d)) w) =
      LinearMap.applyₗ (L.rightEquiv k Γ w • v) ∘ₗ pieceLin L P Q :=
    BalancedTensor.ext fun t y => pieceLin_middleCornerMap_tmul L P Q w t y v
  exact LinearMap.congr_fun h x

/-- `x ⊗ v ↦ pieceLin x v`. -/
def pieceToTwist : pieceTensor L P Q →ₗ[k] twistTensor L P Q :=
  BalancedTensor.lift (pieceLin L P Q : ResIndPiece k Γ L →ₗ[k] _) fun x w v => by
    rw [op_smul_eq_middleCornerMap]
    exact (pieceLin_middleCornerMap L P Q _ x v).trans (by rw [AlgEquiv.apply_symm_apply]; rfl)

theorem pieceToTwist_tmul (x : ResIndPiece k Γ L) (v : ExtTensor k P.carrier Q.carrier) :
    pieceToTwist L P Q (BalancedTensor.tmul x v) = pieceLin L P Q x v := rfl

theorem pieceToTwist_twistToPiece (x : twistTensor L P Q) :
    pieceToTwist L P Q (twistToPiece L P Q x) = x := by
  induction x using BalancedTensor.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul t r =>
    rw [twistToPiece_tmul, pieceToTwist_tmul, middleTopUnit_apply, pieceLin_tmul]
    show BalancedTensor.tmul t (resTensorProj k Γ L.a L.b L.c L.d (leftRes L P).carrier
      (rightRes L Q).carrier (middleBot k Γ L.a L.b L.c L.d 1 •
        resTensorVal k Γ L.a L.b L.c L.d (leftRes L P).carrier (rightRes L Q).carrier r)) = _
    rw [resTensorProj_smul, one_smul, resTensorProj_val]
  | add x x' hx hx' => rw [map_add, map_add, hx, hx']

theorem twistToPiece_pieceLin (x : MiddleTensor k Γ L.a L.b L.c L.d)
    (v : ExtTensor k P.carrier Q.carrier) :
    twistToPiece L P Q (pieceLin L P Q x v) =
      BalancedTensor.tmul (M := ResIndPiece k Γ L) x v := by
  induction x using BalancedTensor.induction_on with
  | zero =>
    rw [map_zero, LinearMap.zero_apply, map_zero]
    exact (BalancedTensor.zero_tmul (M := ResIndPiece k Γ L) v).symm
  | tmul t y =>
    rw [pieceLin_tmul, twistToPiece_tmul, resVal, LinearMap.comp_apply, resTensorVal_proj,
      ← mul_smul, mem_middleBotSub.1 y.2, extCast_smul L P Q y.1 (extCastInv L P Q v),
      extCast_extCastInv L P Q v,
      ← BalancedTensor.op_smul_tmul, op_smul_eq_middleCornerMap, AlgEquiv.symm_apply_apply,
      middleTopUnit_apply, middleCornerMap_tmul, one_smul, middleBotMulRight_middleBotUnit]
  | add x x' hx hx' =>
    rw [map_add, LinearMap.add_apply, map_add, hx, hx']
    exact (BalancedTensor.add_tmul (M := ResIndPiece k Γ L) _ _ v).symm

theorem twistToPiece_pieceToTwist (x : pieceTensor L P Q) :
    twistToPiece L P Q (pieceToTwist L P Q x) = x := by
  induction x using BalancedTensor.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul m v => exact twistToPiece_pieceLin L P Q m v
  | add x x' hx hx' => rw [map_add, map_add, hx, hx']

/-- **The piece as a twisted `Ind ∘ Res`**: `(W_{a+c} ⊗ W_{b+d}) e' ⊗ (Res P ⊠ Res Q) ≅
ResIndPiece L ⊗_{W_{ν'} ⊗ W_{ν''}} (P ⊠ Q)`, `t ⊗ r ↦ (t ⊗ e) ⊗ r`. -/
def resTwistEquiv : twistTensor L P Q ≃ₗ[k] pieceTensor L P Q :=
  LinearEquiv.ofLinearMap (twistToPiece L P Q) (pieceToTwist L P Q)
    (LinearMap.ext (twistToPiece_pieceToTwist L P Q))
    (LinearMap.ext (pieceToTwist_twistToPiece L P Q))

/-- `resTwistEquiv` is semilinear along `W_{a+c} ⊗ W_{b+d} ≅ W_{ν₁} ⊗ W_{ν₂}`. -/
theorem resTwistEquiv_smul
    (z : WeightedKLRAlgebra k Γ (L.a + L.c) ⊗[k] WeightedKLRAlgebra k Γ (L.b + L.d))
    (x : twistTensor L P Q) :
    resTwistEquiv L P Q (z • x) = L.leftEquiv k Γ z • resTwistEquiv L P Q x := by
  change twistToPiece L P Q (z • x) = L.leftEquiv k Γ z • twistToPiece L P Q x
  induction x using BalancedTensor.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul t r =>
    rw [BalancedTensor.smul_tmul', twistToPiece_tmul, twistToPiece_tmul,
      BalancedTensor.smul_tmul', middleTopUnit_smul]
  | add x x' hx hx' => rw [smul_add, map_add, hx, hx', map_add, smul_add]

end Twist

end ResIndPiece

end WeightedKLR

end Categorification

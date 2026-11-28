/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.MackeyIdentityShuffle

/-!
# The bottom factor of a Mackey layer as a corner of the input

Khovanov–Lauda I (arXiv:0803.4121v2), §2.6, Proposition 2.18, used for Webster,
arXiv:1309.3796v3, §7.3, proof of Lemma 7.19 (trace half, step L3: the leading piece of the
head-strand filtration).

For a Mackey datum `λ`, `MackeyBot_λ = (1_{α,γ} ⊗ 1_{β,δ}) (R(ν'') ⊗ R(ν'''))` is the right
ideal of an idempotent `E = quadBot 1`. Hence `MackeyBot_λ ⊗_{R''} N ≅ E N`, the corner of `N`
cut out by `E` (`botTensorEquiv`), and `R'` acts on `E N` through `quadBot`
(`botTensorEquiv_smul`). With `castAlg_concat_tmul_one_smul_tmul_mackeyTopOne` this shows that
the parabolic part of the first top block acts on the identity-shuffle part of the layer
through its image under `quadBot` acting on `N`.

Webster's proof does not spell this out.

## Main results

* `KLR.KLRAlgebra.botCorner`, `KLR.KLRAlgebra.botTensorEquiv`,
  `KLR.KLRAlgebra.botTensorEquiv_tmul`, `KLR.KLRAlgebra.botTensorEquiv_symm_apply`,
  `KLR.KLRAlgebra.botTensorEquiv_smul`.
-/

noncomputable section

namespace Categorification.KLR

open Equiv TypeA MulOpposite
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k}

namespace KLRAlgebra

variable {ν ν' ν'' ν''' : Multiset I} (q : MackeyQuad ν ν' ν'' ν''')
  (N : Type*) [AddCommGroup N] [Module k N] [Module (TensorKLR Q ν'' ν''') N]
  [IsScalarTower k (TensorKLR Q ν'' ν''') N]

/-- `MackeyBot_λ ⊗_{R''} N`, the right factor of a Mackey layer. -/
local notation "BotN" => BalancedTensor k (QuadAlg Q q) (TensorKLR Q ν'' ν''') (MackeyBot Q q) N

variable (Q) in
/-- The corner `E N` of `N`, `E = quadBot 1 = 1_{α,γ} ⊗ 1_{β,δ}`. -/
def botCorner : Submodule k N where
  carrier := {n | (quadBot (Q := Q) q 1 : TensorKLR Q ν'' ν''') • n = n}
  add_mem' {a b} ha hb := by
    change _ • (a + b) = a + b
    rw [smul_add, show _ • a = a from ha, show _ • b = b from hb]
  zero_mem' := smul_zero _
  smul_mem' c n hn := by
    change _ • (c • n) = c • n
    rw [smul_comm, show _ • n = n from hn]

theorem mem_botCorner {n : N} :
    n ∈ botCorner Q q N ↔ (quadBot (Q := Q) q 1 : TensorKLR Q ν'' ν''') • n = n := Iff.rfl

theorem quadBot_smul_mem_botCorner (r : QuadAlg Q q) (n : N) :
    (quadBot q r : TensorKLR Q ν'' ν''') • n ∈ botCorner Q q N := by
  rw [mem_botCorner, smul_smul, quadBot_one_mul]

variable (Q) in
/-- The generator `E` of `MackeyBot_λ`. -/
def mackeyBotOne : MackeyBot Q q :=
  ⟨quadBot q 1, by rw [mem_quadBotSub, quadBot_one_mul]⟩

variable (Q) in
/-- The action map `MackeyBot_λ ⊗_{R''} N → E N`, `m ⊗ n ↦ m n`. -/
def botTensorMap : BotN →ₗ[k] botCorner Q q N :=
  BalancedTensor.lift
    { toFun := fun m =>
        { toFun := fun n => ⟨(m : TensorKLR Q ν'' ν''') • n, by
            rw [mem_botCorner, smul_smul, m.2]⟩
          map_add' := fun n n' => Subtype.ext (smul_add _ _ _)
          map_smul' := fun c n => Subtype.ext (smul_comm _ c n) }
      map_add' := fun m m' => by ext n; exact add_smul _ _ n
      map_smul' := fun c m => by ext n; exact smul_assoc c (m : TensorKLR Q ν'' ν''') n }
    (fun m a n => Subtype.ext (by
      change ((m : TensorKLR Q ν'' ν''') * a) • n = (m : TensorKLR Q ν'' ν''') • a • n
      rw [mul_smul]))

theorem botTensorMap_tmul (m : MackeyBot Q q) (n : N) :
    (botTensorMap Q q N (BalancedTensor.tmul m n) : N) = (m : TensorKLR Q ν'' ν''') • n := rfl

variable (Q) in
/-- **`MackeyBot_λ ⊗_{R''} N ≅ E N`**, `m ⊗ n ↦ m n`, with inverse `n ↦ E ⊗ n`. -/
def botTensorEquiv : BotN ≃ₗ[k] botCorner Q q N :=
  { botTensorMap Q q N with
    invFun := fun n => BalancedTensor.tmul (mackeyBotOne Q q) (n : N)
    left_inv := fun y => by
      induction y using BalancedTensor.induction_on with
      | zero => simp only [LinearMap.toFun_eq_coe, map_zero, ZeroMemClass.coe_zero,
          BalancedTensor.tmul_zero]
      | add y y' hy hy' =>
        simp only [LinearMap.toFun_eq_coe, map_add, Submodule.coe_add,
          BalancedTensor.tmul_add] at *
        rw [hy, hy']
      | tmul m n =>
        change BalancedTensor.tmul (mackeyBotOne Q q) ((m : TensorKLR Q ν'' ν''') • n) = _
        rw [← BalancedTensor.op_smul_tmul]
        congr 1
        apply Subtype.ext
        change (quadBot (Q := Q) q 1 : TensorKLR Q ν'' ν''') * m = m
        exact m.2
    right_inv := fun n => Subtype.ext n.2 }

theorem botTensorEquiv_tmul (m : MackeyBot Q q) (n : N) :
    (botTensorEquiv Q q N (BalancedTensor.tmul m n) : N) = (m : TensorKLR Q ν'' ν''') • n := rfl

theorem botTensorEquiv_symm_apply (n : botCorner Q q N) :
    (botTensorEquiv Q q N).symm n = BalancedTensor.tmul (mackeyBotOne Q q) (n : N) := rfl

/-- **`R'` acts on `E N` through `quadBot`.** -/
theorem botTensorEquiv_smul (r : QuadAlg Q q) (y : BotN) :
    (botTensorEquiv Q q N (r • y) : N) =
      (quadBot q r : TensorKLR Q ν'' ν''') • (botTensorEquiv Q q N y : N) := by
  induction y using BalancedTensor.induction_on with
  | zero => rw [smul_zero, map_zero, ZeroMemClass.coe_zero, smul_zero]
  | add y y' hy hy' => rw [smul_add, map_add, Submodule.coe_add, hy, hy', map_add,
      Submodule.coe_add, smul_add]
  | tmul m n =>
    rw [BalancedTensor.smul_tmul', botTensorEquiv_tmul, botTensorEquiv_tmul, smul_smul]
    rfl

end KLRAlgebra

end Categorification.KLR

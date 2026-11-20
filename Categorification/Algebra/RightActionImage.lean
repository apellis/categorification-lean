/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The image of a non-unital right action

Let `A` be a `k`-algebra and `K` a `B`-module. A family `act b : K → K` of `B`-linear maps,
`b ∈ A`, which is additive and `k`-linear in `b` and satisfies `act u ∘ act v = act (v u)`, is a
right action of `A` on `K` except that `act 1` need not be the identity. Right multiplication by
`cL b` on Kang–Kashiwara's modules `K_0`, `K_1` and `F^Λ` is of this form, with
`act 1` right multiplication by an idempotent `e(β, i)` or `e(i, β)`.

`act 1` is idempotent, and its image `K e` (`RightAct.Image`) is a right `A`-module
(`Module Aᵐᵒᵖ`) on which `B` acts compatibly. This generalizes the construction of
`F^Λ e(β, i)` in the proof of Kang–Kashiwara, arXiv:1102.4677v4, Theorem 4.5.
-/

open MulOpposite

namespace Categorification

/-- A right action of `A` on the `B`-module `K` by `B`-linear maps, not necessarily unital. -/
structure RightAct (k : Type*) [CommRing k] (B : Type*) [Ring B] [Algebra k B]
    (A : Type*) [Ring A] [Algebra k A] (K : Type*) [AddCommGroup K] [Module k K] [Module B K]
    [IsScalarTower k B K] where
  /-- The action of `b ∈ A`. -/
  act : A → K →ₗ[B] K
  act_act : ∀ u v x, act u (act v x) = act (v * u) x
  act_add : ∀ u v x, act (u + v) x = act u x + act v x
  act_smul : ∀ (r : k) u x, act (r • u) x = r • act u x

namespace RightAct

variable {k : Type*} [CommRing k] {B : Type*} [Ring B] [Algebra k B]
  {A : Type*} [Ring A] [Algebra k A] {K : Type*} [AddCommGroup K] [Module k K] [Module B K]
  [IsScalarTower k B K] (ρ : RightAct k B A K)

theorem act_zero (x : K) : ρ.act 0 x = 0 := by
  rw [← zero_smul k (0 : A), ρ.act_smul, zero_smul]

/-- The image `K e` of `act 1`. -/
def imageSub : Submodule B K := LinearMap.range (ρ.act 1)

/-- The image `K e` of `act 1`, a right `A`-module. -/
abbrev Image : Type _ := ↥ρ.imageSub

theorem act_one_of_mem {x : K} (hx : x ∈ ρ.imageSub) : ρ.act 1 x = x := by
  obtain ⟨y, rfl⟩ := hx
  rw [ρ.act_act, mul_one]

theorem act_mem (b : A) (x : K) : ρ.act b x ∈ ρ.imageSub :=
  ⟨ρ.act b x, by rw [ρ.act_act, mul_one]⟩

/-- The action of `b ∈ A` on `K e`. -/
def actImage (b : A) : ρ.Image →ₗ[B] ρ.Image :=
  (ρ.act b).restrict (fun x _ => ρ.act_mem b x)

@[simp] theorem actImage_apply (b : A) (x : ρ.Image) :
    (ρ.actImage b x : K) = ρ.act b x := rfl

/-- `A → End_B(K e)ᵐᵒᵖ`. -/
def rho : A →+* (Module.End B ρ.Image)ᵐᵒᵖ where
  toFun b := op (ρ.actImage b)
  map_one' := by
    rw [← op_one]; congr 1
    ext x; exact ρ.act_one_of_mem x.2
  map_mul' u v := by
    rw [← op_mul]; congr 1
    ext x
    rw [actImage_apply, Module.End.mul_apply, actImage_apply, actImage_apply, ρ.act_act]
  map_zero' := by
    rw [← op_zero]; congr 1
    ext x; exact ρ.act_zero x
  map_add' u v := by
    rw [← op_add]; congr 1
    ext x; exact ρ.act_add u v x

/-- **The right `A`-module structure** of `K e`. -/
instance instModule : Module Aᵐᵒᵖ ρ.Image :=
  Module.compHom _ ((RingEquiv.opOp (Module.End B ρ.Image)).symm.toRingHom.comp
    (RingHom.op ρ.rho))

theorem op_smul (b : A) (x : ρ.Image) : (op b • x : ρ.Image) = ρ.actImage b x := rfl

theorem coe_op_smul (b : A) (x : ρ.Image) : ((op b • x : ρ.Image) : K) = ρ.act b x := rfl

instance instSMulCommClass : SMulCommClass B Aᵐᵒᵖ ρ.Image where
  smul_comm c a x := by
    induction a using MulOpposite.rec' with
    | h b => rw [op_smul, op_smul, map_smul]

instance instIsScalarTower : IsScalarTower k Aᵐᵒᵖ ρ.Image where
  smul_assoc r a x := by
    induction a using MulOpposite.rec' with
    | h b =>
      show (op (r • b) • x : ρ.Image) = r • (op b • x)
      ext
      rw [coe_op_smul, Submodule.coe_smul_of_tower, coe_op_smul, ρ.act_smul]

section Map

variable {K' : Type*} [AddCommGroup K'] [Module k K'] [Module B K'] [IsScalarTower k B K']
  {ρ' : RightAct k B A K'}

/-- A `k`-linear map intertwining two right actions restricts to their images. -/
def mapImage (f : K →ₗ[k] K') (hf : ∀ b x, f (ρ.act b x) = ρ'.act b (f x)) :
    ρ.Image →ₗ[k] ρ'.Image where
  toFun x := ⟨f x, by rw [← ρ.act_one_of_mem x.2, hf]; exact ρ'.act_mem 1 _⟩
  map_add' x y := by ext; exact f.map_add _ _
  map_smul' r x := by ext; exact f.map_smul r _

@[simp] theorem coe_mapImage (f : K →ₗ[k] K') (hf : ∀ b x, f (ρ.act b x) = ρ'.act b (f x))
    (x : ρ.Image) : (ρ.mapImage f hf x : K') = f x := rfl

theorem mapImage_op_smul (f : K →ₗ[k] K') (hf : ∀ b x, f (ρ.act b x) = ρ'.act b (f x))
    (b : A) (x : ρ.Image) : ρ.mapImage f hf (op b • x) = op b • ρ.mapImage f hf x := by
  ext; exact hf b x

theorem mapImage_smul (f : K →ₗ[k] K') (hf : ∀ b x, f (ρ.act b x) = ρ'.act b (f x))
    (hB : ∀ (c : B) x, f (c • x) = c • f x) (c : B) (x : ρ.Image) :
    ρ.mapImage f hf (c • x) = c • ρ.mapImage f hf x := by
  ext; exact hB c x

end Map

end RightAct

end Categorification

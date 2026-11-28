/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DegreewiseTensor
import Categorification.Algebra.InductionAlongRes

set_option backward.isDefEq.respectTransparency false

/-!
# Induction and restriction along a nonunital ring map as tensor products

Let `φ : A →ₙ+* B` be a nonunital ring map and `e = φ 1`. Induction along `φ` is
`N ↦ B e ⊗_A N` (`InductionAlong.functor`) and restriction is `M ↦ e M`
(`InductionAlong.resFunctor`). Both are ordinary tensor products with bimodules:

* `indOrdIso`: induction is `ordTensor B A (Corner φ)`, the tensor product with the
  `(B, A)`-bimodule `B e`;
* `resOrdIso`: restriction is `ordTensor A B (RCorner φ)`, the tensor product with the
  `(A, B)`-bimodule `e B` (`RCorner φ`).

The bimodule `e B` is a direct summand of `B` as a right `B`-module, so it is projective on
the side over which one tensors (`RCorner.projective`). Hence restriction is exact and its
derived functor is the degreewise tensor product (`resFunctor_preservesFiniteLimits`,
`resFunctor_preservesFiniteColimits`). For induction, `B e` is projective as a right
`A`-module only under a hypothesis on `φ`; given it, induction is exact
(`functor_preservesFiniteLimits`, `functor_preservesFiniteColimits`).
-/

noncomputable section

namespace Categorification.InductionAlong

open CategoryTheory DG MulOpposite

universe u

variable {A B : Type u} [Ring A] [Ring B] (φ : A →ₙ+* B)

/-! ### Induction -/

section Ind

variable (N : ModuleCat.{u} A)

/-- `B e ⊗_A N → Ind N φ`, `z ⊗ n ↦ z ⊗ n`. -/
def indOrdFwd :
    TensorProductOver A (InDegreeZero (Corner φ)) (InDegreeZero N) →+ Ind N φ :=
  TensorProductOver.lift
    (AddMonoidHom.mk' (fun z : InDegreeZero (Corner φ) => AddMonoidHom.mk'
      (fun n : InDegreeZero N => Ind.tmul (z : Corner φ) (n : N))
      (fun n n' => Ind.tmul_add (z : Corner φ) (n : N) (n' : N)))
      (fun z z' => AddMonoidHom.ext fun n => Ind.add_tmul (z : Corner φ) (z' : Corner φ) (n : N)))
    (fun a z n => Ind.op_smul_tmul (z : Corner φ) a (n : N))

/-- `Ind N φ → B e ⊗_A N`, `z ⊗ n ↦ z ⊗ n`. -/
def indOrdBwd :
    Ind N φ →+ TensorProductOver A (InDegreeZero (Corner φ)) (InDegreeZero N) :=
  Ind.liftAdd (fun z n => TensorProductOver.tmul (M := InDegreeZero (Corner φ))
      (N := InDegreeZero N) A (z : InDegreeZero (Corner φ)) (n : InDegreeZero N))
    (fun z z' n => TensorProductOver.add_tmul (A := A) (M := InDegreeZero (Corner φ))
      (N := InDegreeZero N) z z' n)
    (fun z n n' => TensorProductOver.tmul_add (A := A) (M := InDegreeZero (Corner φ))
      (N := InDegreeZero N) z n n')
    (fun z a n => TensorProductOver.op_smul_tmul (A := A) (M := InDegreeZero (Corner φ))
      (N := InDegreeZero N) a z n)

/-- Induction along `φ` is the ordinary tensor product with `B e`, as modules. -/
def indOrdEquiv :
    TensorProductOver A (InDegreeZero (Corner φ)) (InDegreeZero N) ≃ₗ[B] Ind N φ where
  toFun := indOrdFwd φ N
  invFun := indOrdBwd φ N
  map_add' := map_add _
  map_smul' b t := by
    induction t using TensorProductOver.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | tmul z n =>
      change Ind.tmul (b • (z : Corner φ)) (n : N) = b • Ind.tmul (z : Corner φ) (n : N)
      rw [Ind.smul_tmul]
    | add s t hs ht => rw [smul_add, map_add, map_add, hs, ht, smul_add]
  left_inv t := by
    induction t using TensorProductOver.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul z n => rfl
    | add s t hs ht => rw [map_add, map_add, hs, ht]
  right_inv t := by
    induction t using Ind.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul z n => rfl
    | add s t hs ht => rw [map_add, map_add, hs, ht]

/-- **Induction along `φ` is the ordinary tensor product with `B e`**. -/
def indOrdIso : ordTensor B A (Corner φ) ≅ functor.{u, u} φ :=
  NatIso.ofComponents (fun N => (indOrdEquiv φ N).toModuleIso) fun _ =>
    ModuleCat.hom_ext (LinearMap.toAddMonoidHom_injective
      (TensorProductOver.addHom_ext fun _ _ => rfl))

variable [Module.Projective Aᵐᵒᵖ (Corner φ)]

/-- Induction is exact when `B e` is projective as a right `A`-module. -/
theorem functor_preservesFiniteLimits : Limits.PreservesFiniteLimits (functor.{u, u} φ) :=
  Limits.preservesFiniteLimits_of_natIso (indOrdIso φ)

/-- Induction is exact when `B e` is projective as a right `A`-module. -/
theorem functor_preservesFiniteColimits : Limits.PreservesFiniteColimits (functor.{u, u} φ) :=
  Limits.preservesFiniteColimits_of_natIso (indOrdIso φ)

end Ind

/-! ### Restriction -/

/-- The right ideal `e B`, an `(A, B)`-bimodule through `φ`. -/
abbrev RCorner : Type u := ↥(rIdeal (φ 1))

namespace RCorner

variable {φ}

theorem mul_mem (a : A) (z : RCorner φ) : φ a * z.1 ∈ rIdeal (φ 1) := by
  rw [mem_rIdeal, ← mul_assoc, ← map_mul, one_mul]

instance : Module A (RCorner φ) where
  smul a z := ⟨φ a * z.1, mul_mem a z⟩
  one_smul z := Subtype.ext z.2
  mul_smul a b z := Subtype.ext (by
    change φ (a * b) * z.1 = φ a * (φ b * z.1)
    rw [map_mul, mul_assoc])
  smul_zero a := Subtype.ext (mul_zero _)
  smul_add a z w := Subtype.ext (mul_add _ _ _)
  add_smul a b z := Subtype.ext (by
    change φ (a + b) * z.1 = φ a * z.1 + φ b * z.1
    rw [map_add, add_mul])
  zero_smul z := Subtype.ext (by change φ 0 * z.1 = 0; rw [map_zero, zero_mul])

@[simp] theorem smul_val (a : A) (z : RCorner φ) : (a • z).1 = φ a * z.1 := rfl

@[simp] theorem op_smul_val (b : B) (z : RCorner φ) : (op b • z).1 = z.1 * b := rfl

instance : SMulCommClass A Bᵐᵒᵖ (RCorner φ) where
  smul_comm a b z := Subtype.ext (mul_assoc (φ a) z.1 b.unop).symm

variable (φ)

/-- The generator `e` of `e B`. -/
def gen : RCorner φ := ⟨φ 1, unit_mul_unit φ⟩

/-- The inclusion of `e B` into the regular right module. -/
def incl : RCorner φ →ₗ[Bᵐᵒᵖ] Bᵐᵒᵖ where
  toFun z := op z.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The projection `b ↦ e b` of the regular right module onto `e B`. -/
def proj : Bᵐᵒᵖ →ₗ[Bᵐᵒᵖ] RCorner φ where
  toFun b := ⟨φ 1 * b.unop, by rw [mem_rIdeal, ← mul_assoc, unit_mul_unit]⟩
  map_add' a b := Subtype.ext (mul_add _ _ _)
  map_smul' a b := Subtype.ext (by
    change φ 1 * (b.unop * a.unop) = φ 1 * b.unop * a.unop
    rw [mul_assoc])

theorem proj_comp_incl : (proj φ).comp (incl φ) = LinearMap.id :=
  LinearMap.ext fun z => Subtype.ext z.2

/-- `e B` is a projective right `B`-module, a direct summand of `B`. -/
instance projective : Module.Projective Bᵐᵒᵖ (RCorner φ) :=
  Module.Projective.of_split (incl φ) (proj φ) (proj_comp_incl φ)

end RCorner

section Res

variable (M : ModuleCat.{u} B)

/-- `e B ⊗_B M → e M`, `z ⊗ m ↦ z m`. -/
def resOrdFwd :
    TensorProductOver B (InDegreeZero (RCorner φ)) (InDegreeZero M) →+ Res φ M :=
  TensorProductOver.lift
    (AddMonoidHom.mk' (fun z : InDegreeZero (RCorner φ) => AddMonoidHom.mk'
      (fun m : InDegreeZero M => Res.mk ((z : RCorner φ).1 • (m : M)) (by
        rw [smul_smul, (z : RCorner φ).2]))
      (fun m m' => Res.ext (smul_add _ (m : M) (m' : M))))
      (fun z z' => AddMonoidHom.ext fun m => Res.ext (add_smul _ _ (m : M))))
    (fun b z m => Res.ext (mul_smul (z : RCorner φ).1 b (m : M)))

/-- `e M → e B ⊗_B M`, `m ↦ e ⊗ m`. -/
def resOrdBwd :
    Res φ M →+ TensorProductOver B (InDegreeZero (RCorner φ)) (InDegreeZero M) where
  toFun m := TensorProductOver.tmul (M := InDegreeZero (RCorner φ)) (N := InDegreeZero M) B
    (RCorner.gen φ : InDegreeZero (RCorner φ)) (m.val : InDegreeZero M)
  map_zero' := TensorProductOver.tmul_zero (A := B) (M := InDegreeZero (RCorner φ))
    (N := InDegreeZero M) _
  map_add' m m' := TensorProductOver.tmul_add (A := B) (M := InDegreeZero (RCorner φ))
    (N := InDegreeZero M) _ (m.val : InDegreeZero M) (m'.val : InDegreeZero M)

/-- Restriction along `φ` is the ordinary tensor product with `e B`, as modules. -/
def resOrdEquiv :
    TensorProductOver B (InDegreeZero (RCorner φ)) (InDegreeZero M) ≃ₗ[A] Res φ M where
  toFun := resOrdFwd φ M
  invFun := resOrdBwd φ M
  map_add' := map_add _
  map_smul' a t := by
    induction t using TensorProductOver.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | tmul z m =>
      refine Res.ext ?_
      change (φ a * (z : RCorner φ).1) • (m : M) = φ a • ((z : RCorner φ).1 • (m : M))
      rw [mul_smul]
    | add s t hs ht => rw [smul_add, map_add, map_add, hs, ht, smul_add]
  left_inv t := by
    induction t using TensorProductOver.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul z m =>
      change TensorProductOver.tmul (M := InDegreeZero (RCorner φ)) (N := InDegreeZero M) B
        (RCorner.gen φ : InDegreeZero (RCorner φ))
        (((z : RCorner φ).1 • (m : M) : M) : InDegreeZero M) = _
      have h : (op (z : RCorner φ).1 • (RCorner.gen φ : InDegreeZero (RCorner φ)) :
          InDegreeZero (RCorner φ)) = z := Subtype.ext (z : RCorner φ).2
      rw [← TensorProductOver.op_smul_tmul (A := B) (M := InDegreeZero (RCorner φ))
        (N := InDegreeZero M), h]
    | add s t hs ht => rw [map_add, map_add, hs, ht]
  right_inv m := Res.ext m.prop

/-- **Restriction along `φ` is the ordinary tensor product with `e B`**. -/
def resOrdIso : ordTensor A B (RCorner φ) ≅ resFunctor.{u, u} φ :=
  NatIso.ofComponents (fun M => (resOrdEquiv φ M).toModuleIso) fun g =>
    ModuleCat.hom_ext (LinearMap.toAddMonoidHom_injective
      (TensorProductOver.addHom_ext fun _ _ => Res.ext (map_smul g.hom _ _).symm))

/-- Restriction is exact. -/
instance resFunctor_preservesFiniteLimits :
    Limits.PreservesFiniteLimits (resFunctor.{u, u} φ) :=
  Limits.preservesFiniteLimits_of_natIso (resOrdIso φ)

/-- Restriction is exact. -/
instance resFunctor_preservesFiniteColimits :
    Limits.PreservesFiniteColimits (resFunctor.{u, u} φ) :=
  Limits.preservesFiniteColimits_of_natIso (resOrdIso φ)

end Res

end Categorification.InductionAlong

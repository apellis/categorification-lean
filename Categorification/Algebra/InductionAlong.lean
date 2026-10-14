/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.BalancedTensor
import Categorification.Algebra.IdempotentEquiv

/-!
# Induction along a nonunital ring map, and its natural transformations

Let `φ : A →ₙ+* B` be a nonunital ring map (for instance a nonunital map of algebras), so
that `e = φ 1` is an idempotent of `B`. Induction along `φ` is
`Ind N φ = B e ⊗_A N`,
where `A` acts on the right of the left ideal `B e` through `φ`. This is the shape of every
induction functor between KLR algebras or their cyclotomic quotients (Khovanov–Lauda I,
arXiv:0803.4121v2, §2.6; Kang–Kashiwara, arXiv:1102.4677v4, §4.2): the inclusion
`R(β) → R(β + γ)` sends `1` to the idempotent `e(β, γ)`, not to `1`.

The point of this file is that all natural transformations between such inductions which
come from the KLR relations are produced by one construction.

* `Intertwines φ ψ x` : `φ a * x = x * ψ a` for all `a : A`.
* `natMap hx : Ind N φ →ₗ[B] Ind N ψ`, `z ⊗ n ↦ z x ⊗ n`, for `x` intertwining `φ` and `ψ`.
  It is natural in `N` (`natMap_map`), additive in `x` (`natMap_add`, `natMap_sub`, …),
  sends `φ 1` to the identity (`natMap_unit`) and products to composites (`natMap_comp`).
  Hence every identity between products of intertwining elements in `B` is an identity
  between the corresponding maps.
* `compEquiv N φ ψ : Ind (Ind N φ) ψ ≃ₗ[C] Ind N (ψ ∘ φ)` for `ψ : B →ₙ+* C`,
  `z ⊗ (w ⊗ n) ↦ z ψ(w) ⊗ n`. No flatness or projectivity is needed.
* `compEquiv_natMap_outer` and `compEquiv_map_natMap` identify, under `compEquiv`, an element
  map on the outer induction and the image of an element map on the inner induction with
  element maps on the composite (with the elements `x` and `ψ y`).
* `functor φ`, `natTrans hx`, `compIso φ ψ` : the same statements for the induction functors
  `ModuleCat A ⥤ ModuleCat B` (`whiskerLeft_natTrans`, `whiskerRight_natTrans`,
  `compIso_assoc`).

Everything here is ungraded. The tensor product is taken over `ℤ`, and `Ind N φ` is a
definition (not an abbreviation) whose only `ℤ`-module structure is the canonical one of an
abelian group. For an algebra `B` over a commutative ring `k`, the `k`-structures of all
modules involved are determined by their `B`-structures; carrying no second scalar structure
on `Ind N φ` is what lets iterated inductions `Ind (Ind N φ) ψ` and the bundled functors have
literally the same types.
-/

namespace Categorification

open MulOpposite

noncomputable section

namespace InductionAlong

universe u w

/-- An additive map is `ℤ`-linear for any `ℤ`-module structures. -/
def intLinear {M P : Type*} [AddCommGroup M] [AddCommGroup P] [hM : Module ℤ M]
    [hP : Module ℤ P] (f : M →+ P) : M →ₗ[ℤ] P where
  toFun := f
  map_add' := f.map_add
  map_smul' c m := by
    change f (hM.smul c m) = hP.smul c (f m)
    rw [int_smul_eq_zsmul, int_smul_eq_zsmul, map_zsmul]

variable {A : Type u} [Ring A] {B : Type u} [Ring B] {C : Type u} [Ring C]

section Corner

variable (φ : A →ₙ+* B)

theorem unit_mul_unit : φ 1 * φ 1 = φ 1 := by rw [← map_mul, one_mul]

/-- The left ideal `B φ(1)`, a `(B, A)`-bimodule. -/
abbrev Corner : Type u := ↥(lIdeal (φ 1))

theorem mul_mem_corner (z : B) (a : A) : z * φ a ∈ lIdeal (φ 1) := by
  change z * φ a * φ 1 = z * φ a
  rw [mul_assoc, ← map_mul, mul_one]

instance cornerOpModule : Module Aᵐᵒᵖ (Corner φ) where
  smul r z := ⟨z.1 * φ r.unop, mul_mem_corner φ z.1 r.unop⟩
  one_smul z := Subtype.ext z.2
  mul_smul r s z := Subtype.ext (by
    change z.1 * φ (s.unop * r.unop) = (z.1 * φ s.unop) * φ r.unop
    rw [map_mul, mul_assoc])
  smul_zero r := Subtype.ext (zero_mul _)
  smul_add r z w := Subtype.ext (add_mul _ _ _)
  add_smul r s z := Subtype.ext (by
    change z.1 * φ (r.unop + s.unop) = z.1 * φ r.unop + z.1 * φ s.unop
    rw [map_add, mul_add])
  zero_smul z := Subtype.ext (by change z.1 * φ 0 = 0; rw [map_zero, mul_zero])

@[simp] theorem op_smul_val (a : A) (z : Corner φ) : (op a • z).1 = z.1 * φ a := rfl

instance cornerComm : SMulCommClass B Aᵐᵒᵖ (Corner φ) where
  smul_comm b r z := Subtype.ext (mul_assoc b z.1 (φ r.unop)).symm

/-- The generator `φ 1` of the corner. -/
def unitGen : Corner φ := ⟨φ 1, unit_mul_unit φ⟩

end Corner

/-! ### The induced module -/

variable (N : Type w) [AddCommGroup N] [Module A N]

/-- Induction along `φ`: `B φ(1) ⊗_A N`. -/
def Ind (φ : A →ₙ+* B) : Type (max u w) := BalancedTensor ℤ B A (Corner φ) N

instance (φ : A →ₙ+* B) : AddCommGroup (Ind N φ) :=
  inferInstanceAs (AddCommGroup (BalancedTensor ℤ B A (Corner φ) N))

instance (φ : A →ₙ+* B) : Module B (Ind N φ) :=
  inferInstanceAs (Module B (BalancedTensor ℤ B A (Corner φ) N))

namespace Ind

variable {N} {φ : A →ₙ+* B}

/-- The class of `z ⊗ n`. -/
def tmul (z : Corner φ) (n : N) : Ind N φ := BalancedTensor.tmul z n

theorem tmul_add (z : Corner φ) (n n' : N) : tmul z (n + n') = tmul z n + tmul z n' :=
  BalancedTensor.tmul_add z n n'

theorem add_tmul (z z' : Corner φ) (n : N) : tmul (z + z') n = tmul z n + tmul z' n :=
  BalancedTensor.add_tmul z z' n

theorem zero_tmul (n : N) : tmul (0 : Corner φ) n = 0 := BalancedTensor.zero_tmul n

theorem neg_tmul (z : Corner φ) (n : N) : tmul (-z) n = -tmul z n :=
  eq_neg_of_add_eq_zero_left (by rw [← add_tmul, neg_add_cancel, zero_tmul])

theorem tmul_zero (z : Corner φ) : tmul z (0 : N) = 0 := BalancedTensor.tmul_zero z

theorem op_smul_tmul (z : Corner φ) (a : A) (n : N) : tmul (op a • z) n = tmul z (a • n) :=
  BalancedTensor.op_smul_tmul z a n

theorem smul_tmul (b : B) (z : Corner φ) (n : N) : b • tmul z n = tmul (b • z) n :=
  BalancedTensor.smul_tmul' b z n

@[elab_as_elim]
theorem induction_on {motive : Ind N φ → Prop} (t : Ind N φ) (zero : motive 0)
    (tmul : ∀ z n, motive (tmul z n)) (add : ∀ s t, motive s → motive t → motive (s + t)) :
    motive t :=
  BalancedTensor.induction_on (motive := motive) t zero tmul add

theorem ext {P : Type*} [AddCommGroup P] [Module B P] {f g : Ind N φ →ₗ[B] P}
    (h : ∀ z n, f (tmul z n) = g (tmul z n)) : f = g := by
  ext t
  induction t using induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul z n => exact h z n
  | add s t hs ht => rw [map_add, map_add, hs, ht]

/-- Linear maps out of an iterated induction agree once they agree on `z ⊗ (w ⊗ n)`. -/
theorem ext₂ {C : Type u} [Ring C] {ψ : B →ₙ+* C} {P : Type*} [AddCommGroup P] [Module C P]
    {f g : Ind (Ind N φ) ψ →ₗ[C] P}
    (h : ∀ z w n, f (tmul z (tmul w n)) = g (tmul z (tmul w n))) : f = g :=
  ext fun z t => by
    induction t using induction_on with
    | zero => rw [tmul_zero, map_zero, map_zero]
    | tmul w n => exact h z w n
    | add s t hs ht => rw [tmul_add, map_add, map_add, hs, ht]

variable {P : Type*} [AddCommGroup P]

/-- The bilinear map attached to a biadditive function. -/
def bil (f : Corner φ → N → P) (hl : ∀ z z' n, f (z + z') n = f z n + f z' n)
    (hr : ∀ z n n', f z (n + n') = f z n + f z n') : Corner φ →ₗ[ℤ] N →ₗ[ℤ] P :=
  intLinear (AddMonoidHom.mk' (fun z => intLinear (AddMonoidHom.mk' (f z) (hr z)))
    fun z z' => LinearMap.ext fun n => hl z z' n)

/-- **Universal property** (additive version): a balanced biadditive function. -/
def liftAdd (f : Corner φ → N → P) (hl : ∀ z z' n, f (z + z') n = f z n + f z' n)
    (hr : ∀ z n n', f z (n + n') = f z n + f z n')
    (hb : ∀ z (a : A) n, f (op a • z) n = f z (a • n)) : Ind N φ →+ P :=
  (BalancedTensor.lift (B := B) (bil f hl hr) hb).toAddMonoidHom

@[simp] theorem liftAdd_tmul (f : Corner φ → N → P) (hl hr hb) (z : Corner φ) (n : N) :
    liftAdd f hl hr hb (tmul z n) = f z n := rfl

/-- **Universal property** (`B`-linear version). -/
def lift [Module B P] (f : Corner φ → N → P) (hl : ∀ z z' n, f (z + z') n = f z n + f z' n)
    (hr : ∀ z n n', f z (n + n') = f z n + f z n')
    (hb : ∀ z (a : A) n, f (op a • z) n = f z (a • n))
    (hB : ∀ (b : B) z n, f (b • z) n = b • f z n) : Ind N φ →ₗ[B] P where
  toFun := liftAdd f hl hr hb
  map_add' := map_add _
  map_smul' b t := by
    induction t using induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | tmul z n => rw [smul_tmul, liftAdd_tmul, liftAdd_tmul, hB, RingHom.id_apply]
    | add s t hs ht => rw [smul_add, map_add, map_add, hs, ht, smul_add]

@[simp] theorem lift_tmul [Module B P] (f : Corner φ → N → P) (hl hr hb hB) (z : Corner φ)
    (n : N) : lift f hl hr hb hB (tmul z n) = f z n := rfl

variable {N' N'' : Type w} [AddCommGroup N'] [Module A N'] [AddCommGroup N''] [Module A N'']

/-- Functoriality in the module. -/
def map (g : N →ₗ[A] N') : Ind N φ →ₗ[B] Ind N' φ :=
  lift (fun z n => tmul z (g n)) (fun z z' n => add_tmul z z' (g n))
    (fun z n n' => by rw [map_add, tmul_add]) (fun z a n => by rw [op_smul_tmul, map_smul])
    (fun b z n => (smul_tmul b z (g n)).symm)

@[simp] theorem map_tmul (g : N →ₗ[A] N') (z : Corner φ) (n : N) :
    map g (tmul z n) = tmul z (g n) := rfl

theorem map_id : map (LinearMap.id : N →ₗ[A] N) = (LinearMap.id : Ind N φ →ₗ[B] Ind N φ) :=
  ext fun _ _ => rfl

theorem map_comp (g : N →ₗ[A] N') (g' : N' →ₗ[A] N'') :
    map (φ := φ) (g'.comp g) = (map g').comp (map g) :=
  ext fun _ _ => rfl

end Ind

/-! ### Element maps -/

/-- `x` intertwines `φ` and `ψ`: `φ a * x = x * ψ a` for every `a`. -/
def Intertwines (φ ψ : A →ₙ+* B) (x : B) : Prop := ∀ a : A, φ a * x = x * ψ a

namespace Intertwines

variable {φ ψ χ : A →ₙ+* B} {x y : B}

theorem unit (φ : A →ₙ+* B) : Intertwines φ φ (φ 1) := fun a => by
  rw [← map_mul, ← map_mul, mul_one, one_mul]

theorem mul (hx : Intertwines φ ψ x) (hy : Intertwines ψ χ y) : Intertwines φ χ (x * y) :=
  fun a => by rw [← mul_assoc, hx a, mul_assoc, hy a, mul_assoc]

theorem add (hx : Intertwines φ ψ x) (hy : Intertwines φ ψ y) : Intertwines φ ψ (x + y) :=
  fun a => by rw [mul_add, add_mul, hx a, hy a]

theorem sub (hx : Intertwines φ ψ x) (hy : Intertwines φ ψ y) : Intertwines φ ψ (x - y) :=
  fun a => by rw [mul_sub, sub_mul, hx a, hy a]

theorem neg (hx : Intertwines φ ψ x) : Intertwines φ ψ (-x) :=
  fun a => by rw [mul_neg, neg_mul, hx a]

theorem zero : Intertwines φ ψ 0 := fun a => by rw [mul_zero, zero_mul]

/-- Composing with a further nonunital map. -/
theorem map (θ : B →ₙ+* C) (hx : Intertwines φ ψ x) :
    Intertwines (θ.comp φ) (θ.comp ψ) (θ x) :=
  fun a => by simp only [NonUnitalRingHom.comp_apply, ← map_mul, hx a]

/-- Precomposing with a nonunital map. -/
theorem comp {φ' ψ' : B →ₙ+* C} {x : C} (hx : Intertwines φ' ψ' x) (θ : A →ₙ+* B) :
    Intertwines (φ'.comp θ) (ψ'.comp θ) x := fun a => hx (θ a)

end Intertwines

variable {N}

section NatMap

variable {φ ψ χ : A →ₙ+* B}

theorem mul_mem_of_intertwines {x : B} (hx : Intertwines φ ψ x) (z : Corner φ) :
    z.1 * x ∈ lIdeal (ψ 1) := by
  change z.1 * x * ψ 1 = z.1 * x
  rw [mul_assoc, ← hx 1, ← mul_assoc, z.2]

/-- Right multiplication by an intertwining element, on corners. -/
def cornerMul {x : B} (hx : Intertwines φ ψ x) (z : Corner φ) : Corner ψ :=
  ⟨z.1 * x, mul_mem_of_intertwines hx z⟩

/-- **The natural transformation of induction given by an intertwining element**:
`z ⊗ n ↦ z x ⊗ n`. -/
def natMap {x : B} (hx : Intertwines φ ψ x) : Ind N φ →ₗ[B] Ind N ψ :=
  Ind.lift (fun z n => Ind.tmul (cornerMul hx z) n)
    (fun z z' n => by
      rw [← Ind.add_tmul]; congr 1; exact Subtype.ext (add_mul _ _ _))
    (fun z n n' => Ind.tmul_add _ n n')
    (fun z a n => by
      rw [← Ind.op_smul_tmul]
      congr 1
      exact Subtype.ext (by
        change z.1 * φ a * x = z.1 * x * ψ a
        rw [mul_assoc, hx a, mul_assoc]))
    (fun b z n => by
      rw [Ind.smul_tmul]; congr 1; exact Subtype.ext (mul_assoc b z.1 x))

@[simp] theorem natMap_tmul {x : B} (hx : Intertwines φ ψ x) (z : Corner φ) (n : N) :
    natMap hx (Ind.tmul z n) = Ind.tmul (cornerMul hx z) n := rfl

/-- Products of elements give composites of maps. -/
theorem natMap_comp {x y : B} (hx : Intertwines φ ψ x) (hy : Intertwines ψ χ y) :
    (natMap (N := N) hy).comp (natMap hx) = natMap (hx.mul hy) :=
  Ind.ext fun z n => by
    rw [LinearMap.comp_apply, natMap_tmul, natMap_tmul, natMap_tmul]
    congr 1
    exact Subtype.ext (mul_assoc _ _ _)

/-- `φ 1` gives the identity. -/
theorem natMap_unit (φ : A →ₙ+* B) :
    natMap (N := N) (Intertwines.unit φ) = LinearMap.id :=
  Ind.ext fun z n => by
    rw [natMap_tmul, LinearMap.id_apply]
    exact congrArg (Ind.tmul · n) (Subtype.ext z.2)

/-- Only `φ 1 * x` matters. -/
theorem natMap_eq_of_unit_mul {x y : B} (hx : Intertwines φ ψ x) (hy : Intertwines φ ψ y)
    (h : φ 1 * x = φ 1 * y) : natMap (N := N) hx = natMap hy :=
  Ind.ext fun z n => by
    rw [natMap_tmul, natMap_tmul]
    congr 1
    exact Subtype.ext (by
      change z.1 * x = z.1 * y
      rw [← z.2, mul_assoc, h, ← mul_assoc, z.2])

/-- The map depends only on the element. -/
theorem natMap_congr {x y : B} (hx : Intertwines φ ψ x) (h : x = y) :
    natMap (N := N) hx = natMap (N := N) (h ▸ hx : Intertwines φ ψ y) := by
  subst h; rfl

theorem natMap_add {x y : B} (hx : Intertwines φ ψ x) (hy : Intertwines φ ψ y) :
    natMap (N := N) (hx.add hy) = natMap hx + natMap hy :=
  Ind.ext fun z n => by
    rw [natMap_tmul, LinearMap.add_apply, natMap_tmul, natMap_tmul, ← Ind.add_tmul]
    congr 1
    exact Subtype.ext (mul_add _ _ _)

theorem natMap_zero : natMap (N := N) (Intertwines.zero : Intertwines φ ψ 0) = 0 :=
  Ind.ext fun z n => by
    rw [natMap_tmul, LinearMap.zero_apply, ← Ind.zero_tmul n]
    congr 1
    exact Subtype.ext (mul_zero _)

theorem natMap_neg {x : B} (hx : Intertwines φ ψ x) :
    natMap (N := N) hx.neg = -natMap hx :=
  Ind.ext fun z n => by
    rw [natMap_tmul, LinearMap.neg_apply, natMap_tmul, eq_neg_iff_add_eq_zero,
      ← Ind.add_tmul, ← Ind.zero_tmul n]
    congr 1
    exact Subtype.ext (by
      change z.1 * -x + z.1 * x = 0
      rw [mul_neg, neg_add_cancel])

theorem natMap_sub {x y : B} (hx : Intertwines φ ψ x) (hy : Intertwines φ ψ y) :
    natMap (N := N) (hx.sub hy) = natMap hx - natMap hy :=
  Ind.ext fun z n => by
    rw [natMap_tmul, LinearMap.sub_apply, natMap_tmul, natMap_tmul,
      sub_eq_add_neg (Ind.tmul (cornerMul hx z) n), ← Ind.neg_tmul, ← Ind.add_tmul]
    congr 1
    exact Subtype.ext (by
      change z.1 * (x - y) = z.1 * x + -(z.1 * y)
      rw [mul_sub, sub_eq_add_neg])

variable {N' : Type w} [AddCommGroup N'] [Module A N']

/-- Element maps are natural in the module. -/
theorem natMap_map {x : B} (hx : Intertwines φ ψ x) (g : N →ₗ[A] N') :
    (natMap hx).comp (Ind.map g) = (Ind.map g).comp (natMap (N := N) hx) :=
  Ind.ext fun _ _ => rfl

end NatMap

/-! ### Composite inductions -/

section Comp

variable (φ : A →ₙ+* B) (ψ : B →ₙ+* C)

theorem comp_mem (z : Corner ψ) (w : Corner φ) : z.1 * ψ w.1 ∈ lIdeal ((ψ.comp φ) 1) := by
  change z.1 * ψ w.1 * ψ (φ 1) = z.1 * ψ w.1
  rw [mul_assoc, ← map_mul, w.2]

/-- The product `z ψ(w)` in the composite corner. -/
def compMul (z : Corner ψ) (w : Corner φ) : Corner (ψ.comp φ) :=
  ⟨z.1 * ψ w.1, comp_mem φ ψ z w⟩

/-- The inner map `w ⊗ n ↦ z ψ(w) ⊗ n`, for fixed `z`. -/
def compInner (z : Corner ψ) : Ind N φ →+ Ind N (ψ.comp φ) :=
  Ind.liftAdd (fun w n => Ind.tmul (compMul φ ψ z w) n)
    (fun w w' n => by
      rw [← Ind.add_tmul]; congr 1
      exact Subtype.ext (by
        change z.1 * ψ (w.1 + w'.1) = z.1 * ψ w.1 + z.1 * ψ w'.1
        rw [map_add, mul_add]))
    (fun w n n' => Ind.tmul_add _ n n')
    (fun w a n => by
      rw [← Ind.op_smul_tmul]
      congr 1
      exact Subtype.ext (by
        change z.1 * ψ (w.1 * φ a) = z.1 * ψ w.1 * ψ (φ a)
        rw [map_mul, mul_assoc]))

@[simp] theorem compInner_tmul (z : Corner ψ) (w : Corner φ) (n : N) :
    compInner φ ψ z (Ind.tmul w n) = Ind.tmul (compMul φ ψ z w) n := rfl

theorem compInner_add (z z' : Corner ψ) (t : Ind N φ) :
    compInner φ ψ (z + z') t = compInner φ ψ z t + compInner φ ψ z' t := by
  induction t using Ind.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, add_zero]
  | tmul w n =>
    rw [compInner_tmul, compInner_tmul, compInner_tmul, ← Ind.add_tmul]
    congr 1
    exact Subtype.ext (add_mul _ _ _)
  | add s t hs ht => rw [map_add, map_add, map_add, hs, ht]; abel

theorem compInner_smul (z : Corner ψ) (b : B) (t : Ind N φ) :
    compInner φ ψ (op b • z) t = compInner φ ψ z (b • t) := by
  induction t using Ind.induction_on with
  | zero => rw [smul_zero, map_zero, map_zero]
  | tmul w n =>
    rw [Ind.smul_tmul, compInner_tmul, compInner_tmul]
    congr 1
    exact Subtype.ext (by
      change z.1 * ψ b * ψ w.1 = z.1 * ψ (b * w.1)
      rw [map_mul, mul_assoc])
  | add s t hs ht => rw [smul_add, map_add, map_add, hs, ht]

theorem compInner_smul_left (c : C) (z : Corner ψ) (t : Ind N φ) :
    compInner φ ψ (c • z) t = c • compInner φ ψ z t := by
  induction t using Ind.induction_on with
  | zero => rw [map_zero, map_zero, smul_zero]
  | tmul w n =>
    rw [compInner_tmul, compInner_tmul, Ind.smul_tmul]
    congr 1
    exact Subtype.ext (mul_assoc c z.1 _)
  | add s t hs ht => rw [map_add, map_add, hs, ht, smul_add]

/-- The forward comparison `z ⊗ (w ⊗ n) ↦ z ψ(w) ⊗ n`. -/
def compForward : Ind (Ind N φ) ψ →ₗ[C] Ind N (ψ.comp φ) :=
  Ind.lift (fun z t => compInner φ ψ z t) (fun z z' t => compInner_add φ ψ z z' t)
    (fun _ t t' => map_add _ t t') (fun z b t => compInner_smul φ ψ z b t)
    (fun c z t => compInner_smul_left φ ψ c z t)

@[simp] theorem compForward_tmul_tmul (z : Corner ψ) (w : Corner φ) (n : N) :
    compForward φ ψ (Ind.tmul z (Ind.tmul w n)) = Ind.tmul (compMul φ ψ z w) n := rfl

theorem inv_mem (y : Corner (ψ.comp φ)) : y.1 ∈ lIdeal (ψ 1) := by
  change y.1 * ψ 1 = y.1
  have h : y.1 * ψ (φ 1) = y.1 := y.2
  rw [← h, mul_assoc, ← map_mul, mul_one]

/-- The element `y` of the composite corner, in the outer corner. -/
def outer (y : Corner (ψ.comp φ)) : Corner ψ := ⟨y.1, inv_mem φ ψ y⟩

/-- The inverse comparison `y ⊗ n ↦ y ⊗ (φ 1 ⊗ n)`. -/
def compBackward : Ind N (ψ.comp φ) →ₗ[C] Ind (Ind N φ) ψ :=
  Ind.lift (fun y n => Ind.tmul (outer φ ψ y) (Ind.tmul (unitGen φ) n))
    (fun y y' n => by rw [← Ind.add_tmul]; rfl)
    (fun y n n' => by rw [Ind.tmul_add, Ind.tmul_add])
    (fun y a n => by
      have h1 : outer φ ψ (op a • y) = op (φ a) • outer φ ψ y := rfl
      have h2 : (op a • unitGen φ : Corner φ) = φ a • unitGen φ := Subtype.ext (by
        change φ 1 * φ a = φ a * φ 1
        rw [← map_mul, ← map_mul, mul_one, one_mul])
      rw [h1, Ind.op_smul_tmul, ← Ind.op_smul_tmul (unitGen φ), h2, Ind.smul_tmul])
    (fun c y n => by rw [Ind.smul_tmul]; rfl)

@[simp] theorem compBackward_tmul (y : Corner (ψ.comp φ)) (n : N) :
    compBackward φ ψ (Ind.tmul y n) = Ind.tmul (outer φ ψ y) (Ind.tmul (unitGen φ) n) := rfl

variable (N) in
/-- **Induction along a composite**: `Ind_ψ (Ind_φ N) ≅ Ind_{ψ ∘ φ} N`. -/
def compEquiv : Ind (Ind N φ) ψ ≃ₗ[C] Ind N (ψ.comp φ) :=
  LinearEquiv.ofLinearMap (compForward φ ψ) (compBackward φ ψ)
    (Ind.ext fun y n => by
      rw [LinearMap.comp_apply, compBackward_tmul, compForward_tmul_tmul, LinearMap.id_apply]
      congr 1
      exact Subtype.ext y.2)
    (Ind.ext fun z t => by
      rw [LinearMap.comp_apply, LinearMap.id_apply]
      induction t using Ind.induction_on with
      | zero => rw [Ind.tmul_zero, map_zero, map_zero]
      | tmul w n =>
        rw [compForward_tmul_tmul, compBackward_tmul]
        have h1 : outer φ ψ (compMul φ ψ z w) = op w.1 • z := rfl
        rw [h1, Ind.op_smul_tmul, Ind.smul_tmul]
        congr 2
        exact Subtype.ext (by change w.1 * φ 1 = w.1; exact w.2)
      | add s t hs ht => rw [Ind.tmul_add, map_add, map_add, hs, ht])

@[simp] theorem compEquiv_tmul_tmul (z : Corner ψ) (w : Corner φ) (n : N) :
    compEquiv N φ ψ (Ind.tmul z (Ind.tmul w n)) = Ind.tmul (compMul φ ψ z w) n := rfl

/-- `compEquiv` is natural in the module. -/
theorem compEquiv_map {N' : Type w} [AddCommGroup N'] [Module A N'] (g : N →ₗ[A] N') :
    (compEquiv N' φ ψ).toLinearMap.comp (Ind.map (Ind.map g)) =
      (Ind.map g).comp (compEquiv N φ ψ).toLinearMap :=
  Ind.ext fun z t => by
    induction t using Ind.induction_on with
    | zero => rw [Ind.tmul_zero, map_zero, map_zero]
    | tmul w n => rfl
    | add s t hs ht => rw [Ind.tmul_add, map_add, map_add, hs, ht]

/-- An element map on the outer induction is the same element map on the composite. -/
theorem compEquiv_natMap_outer {ψ' : B →ₙ+* C} {x : C} (hx : Intertwines ψ ψ' x) :
    (compEquiv N φ ψ').toLinearMap.comp (natMap hx) =
      (natMap (hx.comp φ)).comp (compEquiv N φ ψ).toLinearMap :=
  Ind.ext fun z t => by
    induction t using Ind.induction_on with
    | zero => rw [Ind.tmul_zero, map_zero, map_zero]
    | tmul w n =>
      change Ind.tmul (compMul φ ψ' (cornerMul hx z) w) n =
        Ind.tmul (cornerMul (hx.comp φ) (compMul φ ψ z w)) n
      congr 1
      exact Subtype.ext (by
        change z.1 * x * ψ' w.1 = z.1 * ψ w.1 * x
        rw [mul_assoc, ← hx w.1, mul_assoc])
    | add s t hs ht => rw [Ind.tmul_add, map_add, map_add, hs, ht]

/-- The image of an inner element map under the outer induction is the element map of its
image. -/
theorem compEquiv_map_natMap {φ' : A →ₙ+* B} {y : B} (hy : Intertwines φ φ' y) :
    (compEquiv N φ' ψ).toLinearMap.comp (Ind.map (natMap hy)) =
      (natMap (hy.map ψ)).comp (compEquiv N φ ψ).toLinearMap :=
  Ind.ext fun z t => by
    induction t using Ind.induction_on with
    | zero => rw [Ind.tmul_zero, map_zero, map_zero]
    | tmul w n =>
      change Ind.tmul (compMul φ' ψ z (cornerMul hy w)) n =
        Ind.tmul (cornerMul (hy.map ψ) (compMul φ ψ z w)) n
      congr 1
      exact Subtype.ext (by
        change z.1 * ψ (w.1 * y) = z.1 * ψ w.1 * ψ y
        rw [map_mul, mul_assoc])
    | add s t hs ht => rw [Ind.tmul_add, map_add, map_add, hs, ht]

end Comp

/-! ### Bundled functors -/

section Functor

open CategoryTheory

variable (φ : A →ₙ+* B)

/-- Induction along `φ` as a functor between module categories. -/
def functor : ModuleCat.{max u w} A ⥤ ModuleCat.{max u w} B where
  obj N := ModuleCat.of B (Ind N φ)
  map f := ModuleCat.ofHom (Ind.map f.hom)
  map_id _ := ModuleCat.hom_ext Ind.map_id
  map_comp f g := ModuleCat.hom_ext (Ind.map_comp f.hom g.hom)

variable {φ}

/-- **An intertwining element gives a natural transformation of inductions**:
`z ⊗ n ↦ z x ⊗ n`. -/
def natTrans {ψ : A →ₙ+* B} {x : B} (hx : Intertwines φ ψ x) :
    functor.{u, w} φ ⟶ functor ψ where
  app _ := ModuleCat.ofHom (natMap hx)
  naturality _ _ f := ModuleCat.hom_ext (natMap_map hx f.hom)

@[simp] theorem natTrans_app_tmul {ψ : A →ₙ+* B} {x : B} (hx : Intertwines φ ψ x)
    (N : ModuleCat.{max u w} A) (z : Corner φ) (n : N) :
    (natTrans.{u, w} hx).app N (Ind.tmul z n) = (Ind.tmul (cornerMul hx z) n : Ind N ψ) := rfl

theorem natTrans_comp {ψ χ : A →ₙ+* B} {x y : B} (hx : Intertwines φ ψ x)
    (hy : Intertwines ψ χ y) :
    natTrans.{u, w} hx ≫ natTrans hy = natTrans (hx.mul hy) := by
  ext N : 2
  exact ModuleCat.hom_ext (natMap_comp hx hy)

theorem natTrans_unit (φ : A →ₙ+* B) : natTrans.{u, w} (Intertwines.unit φ) = 𝟙 _ := by
  ext N : 2
  exact ModuleCat.hom_ext (natMap_unit φ)

theorem natTrans_congr {ψ : A →ₙ+* B} {x y : B} (hx : Intertwines φ ψ x) (h : x = y) :
    natTrans.{u, w} hx = natTrans (h ▸ hx : Intertwines φ ψ y) := by
  subst h; rfl

theorem natTrans_eq_of_unit_mul {ψ : A →ₙ+* B} {x y : B} (hx : Intertwines φ ψ x)
    (hy : Intertwines φ ψ y) (h : φ 1 * x = φ 1 * y) :
    natTrans.{u, w} hx = natTrans hy := by
  ext N : 2
  exact ModuleCat.hom_ext (natMap_eq_of_unit_mul hx hy h)

theorem natTrans_add {ψ : A →ₙ+* B} {x y : B} (hx : Intertwines φ ψ x)
    (hy : Intertwines φ ψ y) : natTrans.{u, w} (hx.add hy) = natTrans hx + natTrans hy := by
  ext N : 2
  exact ModuleCat.hom_ext (natMap_add hx hy)

theorem natTrans_zero {ψ : A →ₙ+* B} :
    natTrans.{u, w} (Intertwines.zero : Intertwines φ ψ 0) = 0 := by
  ext N : 2
  exact ModuleCat.hom_ext natMap_zero

theorem natTrans_neg {ψ : A →ₙ+* B} {x : B} (hx : Intertwines φ ψ x) :
    natTrans.{u, w} hx.neg = -natTrans hx := by
  ext N : 2
  exact ModuleCat.hom_ext (natMap_neg hx)

theorem natTrans_sub {ψ : A →ₙ+* B} {x y : B} (hx : Intertwines φ ψ x)
    (hy : Intertwines φ ψ y) : natTrans.{u, w} (hx.sub hy) = natTrans hx - natTrans hy := by
  ext N : 2
  exact ModuleCat.hom_ext (natMap_sub hx hy)

variable (φ) (ψ : B →ₙ+* C)

/-- **Induction along a composite**, as a natural isomorphism of functors. -/
def compIso : functor.{u, w} φ ⋙ functor ψ ≅ functor (ψ.comp φ) :=
  NatIso.ofComponents (fun N => (compEquiv N φ ψ).toModuleIso)
    (fun f => ModuleCat.hom_ext (compEquiv_map φ ψ f.hom))

@[simp] theorem compIso_hom_app_tmul_tmul (N : ModuleCat.{max u w} A) (z : Corner ψ)
    (w : Corner φ) (n : N) :
    (compIso.{u, w} φ ψ).hom.app N (Ind.tmul z (Ind.tmul w n)) =
      (Ind.tmul (compMul φ ψ z w) n : Ind N (ψ.comp φ)) := rfl

/-- Under `compIso`, an element map on the outer induction is the same element on the
composite. -/
theorem whiskerLeft_natTrans {ψ' : B →ₙ+* C} {x : C} (hx : Intertwines ψ ψ' x) :
    Functor.whiskerLeft (functor.{u, w} φ) (natTrans hx) ≫ (compIso φ ψ').hom =
      (compIso φ ψ).hom ≫ natTrans (hx.comp φ) := by
  ext N : 2
  exact ModuleCat.hom_ext (compEquiv_natMap_outer φ ψ hx)

/-- Under `compIso`, the outer induction of an element map on the inner induction is the
element map of the image of the element. -/
theorem whiskerRight_natTrans {φ' : A →ₙ+* B} {y : B} (hy : Intertwines φ φ' y) :
    Functor.whiskerRight (natTrans.{u, w} hy) (functor ψ) ≫ (compIso φ' ψ).hom =
      (compIso φ ψ).hom ≫ natTrans (hy.map ψ) := by
  ext N : 2
  exact ModuleCat.hom_ext (compEquiv_map_natMap φ ψ hy)

/-- The two identifications of a triple composite agree. -/
theorem compIso_assoc {D : Type u} [Ring D] (θ : C →ₙ+* D) :
    (Functor.associator (functor.{u, w} φ) (functor ψ) (functor θ)).hom ≫
        Functor.whiskerLeft (functor φ) (compIso ψ θ).hom ≫ (compIso φ (θ.comp ψ)).hom =
      Functor.whiskerRight (compIso φ ψ).hom (functor θ) ≫ (compIso (ψ.comp φ) θ).hom := by
  ext N : 2
  refine ModuleCat.hom_ext (Ind.ext₂ fun z y t => ?_)
  induction t using Ind.induction_on with
  | zero => erw [Ind.tmul_zero, Ind.tmul_zero, map_zero]
  | tmul w n =>
    change Ind.tmul _ n = Ind.tmul _ n
    congr 1
    exact Subtype.ext (by
      change z.1 * θ y.1 * θ (ψ w.1) = z.1 * θ (y.1 * ψ w.1)
      rw [map_mul, mul_assoc])
  | add s t hs ht => erw [Ind.tmul_add, Ind.tmul_add, map_add, map_add, hs, ht]

end Functor

end InductionAlong

end

end Categorification

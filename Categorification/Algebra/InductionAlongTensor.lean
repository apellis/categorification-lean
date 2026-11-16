/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongRes
import Categorification.Algebra.ExternalTensor

/-!
# Induction along nonunital maps of algebras: scalars, transport and external tensor products

Let `k` be a commutative ring and `φ : A → B` a nonunital ring map, with `B` a `k`-algebra.
These are the general facts about `Ind N φ = B φ(1) ⊗_A N` and `Res φ M = φ(1) M` behind the
monoidality of induction and comonoidality of restriction for (weighted) KLR algebras
(B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.4,
Proposition 2.18; Khovanov–Lauda I, arXiv:0803.4121v2, Proposition 3.1).

## Main definitions and results

* `IndK k N φ`: the induced module `Ind N φ` with the `k`-module structure through `B`, so that
  it can again be used as a factor of an external tensor product. It is a separate definition,
  so `Ind N φ` keeps its canonical `ℤ`-module structure.
* `Ind.transport`: induction is compatible with ring isomorphisms `a : A ≃ A'`, `c : B ≃ B'`
  intertwining `φ` and `φ'`, and an `a`-semilinear isomorphism `N ≃ N'`.
* `tensorLeft φ`, `tensorRight φ`: the nonunital maps `φ ⊗ id : A ⊗ C → B ⊗ C` and
  `id ⊗ φ : C ⊗ A → C ⊗ B` of a `k`-linear `φ`.
* `extIndLeft`: `Ind_φ X ⊠ P ≅ Ind_{φ ⊗ id} (X ⊠ P)`; `extIndRight`:
  `P ⊠ Ind_φ X ≅ Ind_{id ⊗ φ} (P ⊠ X)`.
-/

namespace Categorification

open MulOpposite
open scoped TensorProduct

noncomputable section

namespace InductionAlong

universe u w

/-! ### The `k`-module structure of an induced module -/

section Scalar

variable (k : Type*) [CommRing k] {A : Type u} [Ring A] {B : Type u} [Ring B] [Algebra k B]
  (N : Type w) [AddCommGroup N] [Module A N] (φ : A →ₙ+* B)

/-- `Ind N φ` with the `k`-module structure through `B`. For `k = ℤ` this structure is
propositionally, not definitionally, equal to the canonical one; this is why it lives on a
separate definition. -/
def IndK (k : Type*) [CommRing k] [Algebra k B] (N : Type w) [AddCommGroup N] [Module A N]
    (φ : A →ₙ+* B) : Type (max u w) :=
  Ind N φ

instance : AddCommGroup (IndK k N φ) := inferInstanceAs (AddCommGroup (Ind N φ))

instance : Module B (IndK k N φ) := inferInstanceAs (Module B (Ind N φ))

instance : Module k (IndK k N φ) := Module.compHom _ (algebraMap k B)

instance : IsScalarTower k B (IndK k N φ) where
  smul_assoc c b x := by
    change (c • b) • x = algebraMap k B c • (b • x)
    rw [Algebra.smul_def, mul_smul]

theorem IndK.algebraMap_smul (c : k) (x : IndK k N φ) : algebraMap k B c • x = c • x := rfl

variable {k N φ} in
/-- The element `z ⊗ n` of `IndK k N φ`. -/
def IndK.tmul (z : Corner φ) (n : N) : IndK k N φ := Ind.tmul z n

variable {N φ} in
/-- Scalars of `k` pass through the tensor sign when `φ` is `k`-linear. -/
theorem Ind.tmul_algebraMap_smul [Algebra k A] [Module k N] [IsScalarTower k A N]
    (hφ : ∀ (c : k) (t : A), φ (c • t) = c • φ t) (z : Corner φ) (c : k) (n : N) :
    Ind.tmul z (c • n) = algebraMap k B c • Ind.tmul z n := by
  have h1 : c • n = algebraMap k A c • n := by
    rw [Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]
  have h2 : (op (algebraMap k A c) • z : Corner φ) = algebraMap k B c • z := Subtype.ext (by
    change z.1 * φ (algebraMap k A c) = algebraMap k B c * z.1
    rw [Algebra.algebraMap_eq_smul_one, hφ, mul_smul_comm, z.2, Algebra.smul_def])
  rw [h1, ← Ind.op_smul_tmul, h2, Ind.smul_tmul]

end Scalar

/-! ### Transport along ring isomorphisms -/

section Transport

variable {A : Type u} [Ring A] {B : Type u} [Ring B] {A' : Type u} [Ring A'] {B' : Type u}
  [Ring B'] {φ : A →ₙ+* B} {φ' : A' →ₙ+* B'} (a : A ≃+* A') (c : B ≃+* B')
  (h : ∀ t, φ' (a t) = c (φ t))

include h

theorem transport_mem (z : Corner φ) : c z.1 ∈ lIdeal (φ' 1) := by
  change c z.1 * φ' 1 = c z.1
  rw [← map_one a, h, ← map_mul, z.2]

/-- The corner `B φ(1)` mapped by `c` to `B' φ'(1)`. -/
def transportCorner (z : Corner φ) : Corner φ' := ⟨c z.1, transport_mem a c h z⟩

theorem transportCorner_op_smul (t : A) (z : Corner φ) :
    transportCorner a c h (op t • z) = op (a t) • transportCorner a c h z :=
  Subtype.ext (by
    change c (z.1 * φ t) = c z.1 * φ' (a t)
    rw [map_mul, h])

theorem transport_symm (t : A') : φ (a.symm t) = c.symm (φ' t) := by
  rw [← c.symm_apply_apply (φ (a.symm t)), ← h, a.apply_symm_apply]

variable {N : Type w} [AddCommGroup N] [Module A N] {N' : Type w} [AddCommGroup N']
  [Module A' N'] (e : N ≃+ N') (he : ∀ (t : A) n, e (t • n) = a t • e n)

include he

/-- **Transport of induction** along ring isomorphisms intertwining `φ` and `φ'` and a
semilinear isomorphism of modules: `z ⊗ n ↦ c(z) ⊗ e(n)`. -/
def Ind.transportHom : Ind N φ →+ Ind N' φ' :=
  Ind.liftAdd (fun z n => Ind.tmul (transportCorner a c h z) (e n))
    (fun z z' n => by
      rw [show transportCorner a c h (z + z') =
        transportCorner a c h z + transportCorner a c h z' from Subtype.ext (map_add c _ _),
        Ind.add_tmul])
    (fun z n n' => by rw [map_add, Ind.tmul_add])
    (fun z t n => by rw [transportCorner_op_smul, Ind.op_smul_tmul, he])

theorem Ind.transportHom_tmul (z : Corner φ) (n : N) :
    Ind.transportHom a c h e he (Ind.tmul z n) =
      Ind.tmul (transportCorner a c h z) (e n) := rfl

theorem Ind.transportHom_smul (b : B) (x : Ind N φ) :
    Ind.transportHom a c h e he (b • x) = c b • Ind.transportHom a c h e he x := by
  induction x using Ind.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul z n =>
    rw [Ind.smul_tmul, Ind.transportHom_tmul, Ind.transportHom_tmul, Ind.smul_tmul]
    congr 1
    exact Subtype.ext (map_mul c b z.1)
  | add s t hs ht => rw [smul_add, map_add, map_add, hs, ht, smul_add]

omit h in
theorem transport_symm_smul (t : A') (n : N') : e.symm (t • n) = a.symm t • e.symm n := by
  apply e.injective
  rw [e.apply_symm_apply, he, a.apply_symm_apply, e.apply_symm_apply]

/-- `Ind.transportHom` as an additive isomorphism; it is semilinear along `c`
(`Ind.transport_smul`). -/
def Ind.transport : Ind N φ ≃+ Ind N' φ' where
  toFun := Ind.transportHom a c h e he
  invFun := Ind.transportHom a.symm c.symm (transport_symm a c h) e.symm
    (transport_symm_smul a e he)
  left_inv x := by
    induction x using Ind.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul z n =>
      rw [Ind.transportHom_tmul, Ind.transportHom_tmul, e.symm_apply_apply]
      congr 1
      exact Subtype.ext (c.symm_apply_apply z.1)
    | add s t hs ht => rw [map_add, map_add, hs, ht]
  right_inv x := by
    induction x using Ind.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul z n =>
      rw [Ind.transportHom_tmul, Ind.transportHom_tmul, e.apply_symm_apply]
      congr 1
      exact Subtype.ext (c.apply_symm_apply z.1)
    | add s t hs ht => rw [map_add, map_add, hs, ht]
  map_add' := map_add _

theorem Ind.transport_tmul (z : Corner φ) (n : N) :
    Ind.transport a c h e he (Ind.tmul z n) = Ind.tmul (transportCorner a c h z) (e n) := rfl

theorem Ind.transport_smul (b : B) (x : Ind N φ) :
    Ind.transport a c h e he (b • x) = c b • Ind.transport a c h e he x :=
  Ind.transportHom_smul a c h e he b x

end Transport

/-! ### Tensoring a nonunital map with the identity -/

section TensorMap

variable (k : Type*) [CommRing k] {A : Type u} [Ring A] [Algebra k A] {B : Type u} [Ring B]
  [Algebra k B] (C : Type u) [Ring C] [Algebra k C] (φ : A →ₙ+* B)
  (hφ : ∀ (c : k) (t : A), φ (c • t) = c • φ t)

/-- `φ` as a `k`-linear map. -/
def linearOf : A →ₗ[k] B where
  toFun := φ
  map_add' := map_add φ
  map_smul' := hφ

/-- `φ ⊗ id : A ⊗ C → B ⊗ C`. -/
def tensorLeft : A ⊗[k] C →ₙ+* B ⊗[k] C where
  toFun := TensorProduct.map (linearOf k φ hφ) LinearMap.id
  map_mul' x y := by
    induction x using TensorProduct.inductionOn with
    | tmul a c =>
      induction y using TensorProduct.inductionOn with
      | tmul a' c' =>
        simp only [Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.map_tmul, LinearMap.id_apply]
        congr 1
        exact map_mul φ a a'
      | add y y' hy hy' => rw [mul_add, map_add, hy, hy', map_add, mul_add]
    | add x x' hx hx' => rw [add_mul, map_add, hx, hx', map_add, add_mul]
  map_zero' := map_zero _
  map_add' := map_add _

theorem tensorLeft_tmul (t : A) (c : C) :
    tensorLeft k C φ hφ (t ⊗ₜ c) = φ t ⊗ₜ c := rfl

/-- `id ⊗ φ : C ⊗ A → C ⊗ B`. -/
def tensorRight : C ⊗[k] A →ₙ+* C ⊗[k] B where
  toFun := TensorProduct.map LinearMap.id (linearOf k φ hφ)
  map_mul' x y := by
    induction x using TensorProduct.inductionOn with
    | tmul c a =>
      induction y using TensorProduct.inductionOn with
      | tmul c' a' =>
        simp only [Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.map_tmul, LinearMap.id_apply]
        congr 1
        exact map_mul φ a a'
      | add y y' hy hy' => rw [mul_add, map_add, hy, hy', map_add, mul_add]
    | add x x' hx hx' => rw [add_mul, map_add, hx, hx', map_add, add_mul]
  map_zero' := map_zero _
  map_add' := map_add _

theorem tensorRight_tmul (c : C) (t : A) :
    tensorRight k C φ hφ (c ⊗ₜ t) = c ⊗ₜ φ t := rfl

end TensorMap

/-! ### Induction and external tensor products -/

section ExtInd

universe w'

variable (k : Type*) [CommRing k] {A : Type u} [Ring A] [Algebra k A] {B : Type u} [Ring B]
  [Algebra k B] (C : Type u) [Ring C] [Algebra k C] (φ : A →ₙ+* B)
  (hφ : ∀ (c : k) (t : A), φ (c • t) = c • φ t)
  (X : Type w) [AddCommGroup X] [Module k X] [Module A X] [IsScalarTower k A X]
  (P : Type w') [AddCommGroup P] [Module k P] [Module C P] [IsScalarTower k C P]

theorem tensorLeft_one : tensorLeft k C φ hφ 1 = φ 1 ⊗ₜ[k] (1 : C) := rfl

theorem tensorLeft_smul (c : k) (t : A ⊗[k] C) :
    tensorLeft k C φ hφ (c • t) = c • tensorLeft k C φ hφ t :=
  LinearMap.map_smul (TensorProduct.map (linearOf k φ hφ) LinearMap.id) c t

variable {k C φ hφ} in
/-- The element `z ⊗ 1` of the corner of `φ ⊗ id`. -/
def leftCorner (z : Corner φ) : Corner (tensorLeft k C φ hφ) :=
  ⟨z.1 ⊗ₜ[k] (1 : C), by
    change z.1 ⊗ₜ[k] (1 : C) * tensorLeft k C φ hφ 1 = z.1 ⊗ₜ[k] (1 : C)
    rw [tensorLeft_one, Algebra.TensorProduct.tmul_mul_tmul, z.2, mul_one]⟩

theorem leftCorner_add (z z' : Corner φ) :
    leftCorner (C := C) (hφ := hφ) (z + z') = leftCorner z + leftCorner z' :=
  Subtype.ext (TensorProduct.add_tmul _ _ _)

theorem leftCorner_op_smul (a : A) (z : Corner φ) :
    leftCorner (C := C) (hφ := hφ) (op a • z) = op (a ⊗ₜ[k] (1 : C)) • leftCorner z :=
  Subtype.ext (by
    change (z.1 * φ a) ⊗ₜ[k] (1 : C) = z.1 ⊗ₜ[k] (1 : C) * (φ a ⊗ₜ[k] (1 : C))
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one])

theorem leftCorner_smul (b : B) (z : Corner φ) :
    leftCorner (C := C) (hφ := hφ) (b • z) = (b ⊗ₜ[k] (1 : C)) • leftCorner z :=
  Subtype.ext (by
    change (b * z.1) ⊗ₜ[k] (1 : C) = b ⊗ₜ[k] (1 : C) * z.1 ⊗ₜ[k] (1 : C)
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one])

variable {X P}

/-- For fixed `p`, the map `z ⊗ x ↦ (z ⊗ 1) ⊗ (x ⊗ p)`. -/
def extIndLeftInner (p : P) : Ind X φ →+ Ind (ExtTensor k X P) (tensorLeft k C φ hφ) :=
  Ind.liftAdd (fun z x => Ind.tmul (leftCorner z) (ExtTensor.tmul x p))
    (fun z z' x => by rw [leftCorner_add, Ind.add_tmul])
    (fun z x x' => by rw [ExtTensor.add_tmul, Ind.tmul_add])
    (fun z a x => by
      rw [leftCorner_op_smul, Ind.op_smul_tmul, ExtTensor.smul_tmul, one_smul])

theorem extIndLeftInner_tmul (p : P) (z : Corner φ) (x : X) :
    extIndLeftInner k C φ hφ p (Ind.tmul z x) =
      Ind.tmul (leftCorner z) (ExtTensor.tmul x p) := rfl

theorem extIndLeftInner_smul (p : P) (b : B) (y : Ind X φ) :
    extIndLeftInner k C φ hφ p (b • y) =
      (b ⊗ₜ[k] (1 : C)) • extIndLeftInner k C φ hφ p y := by
  induction y using Ind.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul z x =>
    rw [Ind.smul_tmul, extIndLeftInner_tmul, extIndLeftInner_tmul, leftCorner_smul,
      Ind.smul_tmul]
  | add s t hs ht => rw [smul_add, map_add, map_add, hs, ht, smul_add]

theorem extIndLeftInner_smul_right (c : C) (p : P) (y : Ind X φ) :
    extIndLeftInner k C φ hφ (c • p) y =
      ((1 : B) ⊗ₜ[k] c) • extIndLeftInner k C φ hφ p y := by
  induction y using Ind.induction_on with
  | zero => rw [map_zero, map_zero, smul_zero]
  | tmul z x =>
    rw [extIndLeftInner_tmul, extIndLeftInner_tmul, Ind.smul_tmul]
    have h1 : (ExtTensor.tmul x (c • p) : ExtTensor k X P) =
        ((1 : A) ⊗ₜ[k] c) • ExtTensor.tmul x p := by
      rw [ExtTensor.smul_tmul, one_smul]
    have h2 : (op ((1 : A) ⊗ₜ[k] c) • leftCorner z : Corner (tensorLeft k C φ hφ)) =
        ((1 : B) ⊗ₜ[k] c) • leftCorner z := Subtype.ext (by
      change z.1 ⊗ₜ[k] (1 : C) * (φ 1 ⊗ₜ[k] c) = (1 : B) ⊗ₜ[k] c * z.1 ⊗ₜ[k] (1 : C)
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, z.2,
        one_mul, one_mul, mul_one])
    rw [h1, ← Ind.op_smul_tmul, h2]
  | add s t hs ht => rw [map_add, map_add, hs, ht, smul_add]

theorem extIndLeftInner_add_right (p p' : P) (y : Ind X φ) :
    extIndLeftInner k C φ hφ (p + p') y =
      extIndLeftInner k C φ hφ p y + extIndLeftInner k C φ hφ p' y := by
  induction y using Ind.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, add_zero]
  | tmul z x =>
    rw [extIndLeftInner_tmul, extIndLeftInner_tmul, extIndLeftInner_tmul, ExtTensor.tmul_add,
      Ind.tmul_add]
  | add s t hs ht => rw [map_add, map_add, map_add, hs, ht]; abel

theorem extIndLeftInner_scalar_right (c : k) (p : P) (y : Ind X φ) :
    extIndLeftInner k C φ hφ (c • p) y =
      algebraMap k (B ⊗[k] C) c • extIndLeftInner k C φ hφ p y := by
  induction y using Ind.induction_on with
  | zero => rw [map_zero, map_zero, smul_zero]
  | tmul z x =>
    rw [extIndLeftInner_tmul, extIndLeftInner_tmul, ExtTensor.tmul_smul]
    exact Ind.tmul_algebraMap_smul k (tensorLeft_smul k C φ hφ) _ c _
  | add s t hs ht => rw [map_add, map_add, hs, ht, smul_add]

theorem extIndLeftInner_smul_smul (b : B) (c : C) (p : P) (y : Ind X φ) :
    extIndLeftInner k C φ hφ (c • p) (b • y) = (b ⊗ₜ[k] c) • extIndLeftInner k C φ hφ p y := by
  rw [extIndLeftInner_smul, extIndLeftInner_smul_right, ← mul_smul,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- The forward map `(z ⊗ x) ⊗ p ↦ (z ⊗ 1) ⊗ (x ⊗ p)` as a `k`-linear map. -/
def extIndLeftFwdK :
    ExtTensor k (IndK k X φ) P →ₗ[k] IndK k (ExtTensor k X P) (tensorLeft k C φ hφ) :=
  ExtTensor.lift (LinearMap.mk₂ k
    (fun (y : IndK k X φ) (p : P) =>
      (show IndK k (ExtTensor k X P) (tensorLeft k C φ hφ) from extIndLeftInner k C φ hφ p y))
    (fun y y' p => map_add (extIndLeftInner k C φ hφ p) y y')
    (fun c y p => by
      have h := extIndLeftInner_smul k C φ hφ p (algebraMap k B c) y
      rw [← Algebra.TensorProduct.algebraMap_apply] at h
      exact h)
    (fun y p p' => extIndLeftInner_add_right k C φ hφ p p' y)
    (fun c y p => extIndLeftInner_scalar_right k C φ hφ c p y))

theorem extIndLeftFwdK_tmul (y : IndK k X φ) (p : P) :
    extIndLeftFwdK k C φ hφ (ExtTensor.tmul y p) = extIndLeftInner k C φ hφ p y := rfl

/-- The forward map of `extIndLeft`. -/
def extIndLeftFwd :
    ExtTensor k (IndK k X φ) P →ₗ[B ⊗[k] C] IndK k (ExtTensor k X P) (tensorLeft k C φ hφ) where
  toFun := extIndLeftFwdK k C φ hφ
  map_add' := map_add _
  map_smul' t x := ExtTensor.smul_eq_induction (map_add _) (map_zero _)
    (fun b c y p => by
      rw [ExtTensor.smul_tmul, extIndLeftFwdK_tmul, extIndLeftFwdK_tmul]
      exact extIndLeftInner_smul_smul k C φ hφ b c p y) t x

/-- `extIndLeftFwd` with values in `Ind`, for computations. -/
def extIndLeftFwdAdd :
    ExtTensor k (IndK k X φ) P →+ Ind (ExtTensor k X P) (tensorLeft k C φ hφ) :=
  (extIndLeftFwd k C φ hφ).toAddMonoidHom

theorem extIndLeftFwdAdd_tmul_tmul (z : Corner φ) (x : X) (p : P) :
    extIndLeftFwdAdd k C φ hφ (ExtTensor.tmul (k := k) (P := IndK k X φ) (Ind.tmul z x) p) =
      Ind.tmul (leftCorner z) (ExtTensor.tmul x p) := rfl

theorem extIndLeftFwdAdd_smul (b : B ⊗[k] C) (v : ExtTensor k (IndK k X φ) P) :
    extIndLeftFwdAdd k C φ hφ (b • v) = b • extIndLeftFwdAdd k C φ hφ v :=
  (extIndLeftFwd k C φ hφ).map_smul b v

omit [Algebra k A] [Module k X] [IsScalarTower k A X] in
theorem extTmul_zero (p : P) :
    ExtTensor.tmul (k := k) (P := IndK k X φ) (0 : Ind X φ) p = 0 :=
  ExtTensor.zero_tmul (P := IndK k X φ) p

omit [Algebra k A] [Module k X] [IsScalarTower k A X] in
theorem extTmul_add (s t : Ind X φ) (p : P) :
    ExtTensor.tmul (k := k) (P := IndK k X φ) (s + t) p =
      ExtTensor.tmul (k := k) (P := IndK k X φ) s p +
        ExtTensor.tmul (k := k) (P := IndK k X φ) t p :=
  ExtTensor.add_tmul (P := IndK k X φ) s t p

/-- The map `x ⊗ p ↦ (φ 1 ⊗ x) ⊗ p`. -/
def extIndLeftUnit : ExtTensor k X P →ₗ[k] ExtTensor k (IndK k X φ) P :=
  ExtTensor.lift (LinearMap.mk₂ k
    (fun (x : X) (p : P) =>
      ExtTensor.tmul (k := k) (P := IndK k X φ) (Ind.tmul (unitGen φ) x) p)
    (fun x x' p => by rw [Ind.tmul_add, extTmul_add])
    (fun c x p => by
      rw [Ind.tmul_algebraMap_smul k hφ]
      exact (ExtTensor.smul_tmul' (P := IndK k X φ) c (Ind.tmul (unitGen φ) x) p).symm)
    (fun x p p' => ExtTensor.tmul_add _ _ _)
    (fun c x p => ExtTensor.tmul_smul _ _ _))

theorem extIndLeftUnit_tmul (x : X) (p : P) :
    extIndLeftUnit k φ hφ (ExtTensor.tmul x p) =
      ExtTensor.tmul (k := k) (P := IndK k X φ) (Ind.tmul (unitGen φ) x) p := rfl

omit [Module k X] [IsScalarTower k A X] in
theorem unitGen_tmul_smul (a : A) (x : X) :
    (Ind.tmul (unitGen φ) (a • x) : Ind X φ) = φ a • Ind.tmul (unitGen φ) x := by
  rw [← Ind.op_smul_tmul, Ind.smul_tmul]
  congr 1
  exact Subtype.ext (by
    change φ 1 * φ a = φ a * φ 1
    rw [← map_mul, ← map_mul, mul_one, one_mul])

theorem extIndLeftUnit_smul (t : A ⊗[k] C) (w : ExtTensor k X P) :
    extIndLeftUnit k φ hφ (t • w) = tensorLeft k C φ hφ t • extIndLeftUnit k φ hφ w := by
  induction t using TensorProduct.inductionOn with
  | tmul a c =>
    induction w using ExtTensor.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | tmul x p =>
      rw [ExtTensor.smul_tmul, extIndLeftUnit_tmul, extIndLeftUnit_tmul, tensorLeft_tmul,
        unitGen_tmul_smul]
      exact (ExtTensor.smul_tmul (P := IndK k X φ) (φ a) c (Ind.tmul (unitGen φ) x) p).symm
    | add w w' hw hw' => rw [smul_add, map_add, map_add, hw, hw', smul_add]
  | add t t' ht ht' => rw [add_smul, map_add, ht, ht', map_add, add_smul]

/-- The backward map of `extIndLeft`: `y ⊗ (x ⊗ p) ↦ y · ((φ 1 ⊗ x) ⊗ p)`. -/
def extIndLeftBwd :
    Ind (ExtTensor k X P) (tensorLeft k C φ hφ) →ₗ[B ⊗[k] C] ExtTensor k (IndK k X φ) P :=
  Ind.lift (fun y w => y.1 • extIndLeftUnit k φ hφ w)
    (fun y y' w => add_smul _ _ _)
    (fun y w w' => by rw [map_add, smul_add])
    (fun y t w => by
      change (y.1 * tensorLeft k C φ hφ t) • _ = _
      rw [mul_smul, extIndLeftUnit_smul])
    (fun s y w => mul_smul _ _ _)

theorem extIndLeftBwd_tmul (y : Corner (tensorLeft k C φ hφ)) (w : ExtTensor k X P) :
    extIndLeftBwd k C φ hφ (Ind.tmul y w) = y.1 • extIndLeftUnit k φ hφ w := rfl

theorem extIndLeftBwd_fwd (v : ExtTensor k (IndK k X φ) P) :
    extIndLeftBwd k C φ hφ (extIndLeftFwdAdd k C φ hφ v) = v := by
  induction v using ExtTensor.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul y p =>
    induction y using Ind.induction_on with
    | zero => rw [extTmul_zero, map_zero, map_zero]
    | tmul z x =>
      rw [extIndLeftFwdAdd_tmul_tmul, extIndLeftBwd_tmul, extIndLeftUnit_tmul]
      change (z.1 ⊗ₜ[k] (1 : C)) • _ = _
      refine (ExtTensor.smul_tmul (P := IndK k X φ) z.1 (1 : C) (Ind.tmul (unitGen φ) x) p).trans
        ?_
      rw [one_smul]
      congr 1
      exact (Ind.smul_tmul z.1 (unitGen φ) x).trans
        (congrArg (fun w => Ind.tmul w x) (Subtype.ext z.2))
    | add s t hs ht => rw [extTmul_add, map_add, map_add, hs, ht]
  | add v v' hv hv' => rw [map_add, map_add, hv, hv']

theorem extIndLeftFwd_bwd (v : Ind (ExtTensor k X P) (tensorLeft k C φ hφ)) :
    extIndLeftFwdAdd k C φ hφ (extIndLeftBwd k C φ hφ v) = v := by
  induction v using Ind.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul y w =>
    induction w using ExtTensor.induction_on with
    | zero => rw [Ind.tmul_zero, map_zero, map_zero]
    | tmul x p =>
      rw [extIndLeftBwd_tmul, extIndLeftUnit_tmul, extIndLeftFwdAdd_smul,
        extIndLeftFwdAdd_tmul_tmul, Ind.smul_tmul]
      congr 1
      exact Subtype.ext (by
        change y.1 * (φ 1 ⊗ₜ[k] (1 : C)) = y.1
        rw [← tensorLeft_one]
        exact y.2)
    | add w w' hw hw' => rw [Ind.tmul_add, map_add, map_add, hw, hw']
  | add v v' hv hv' => rw [map_add, map_add, hv, hv']

variable (X P) in
/-- **Induction commutes with external tensor products** on the left:
`Ind_φ X ⊠ P ≅ Ind_{φ ⊗ id} (X ⊠ P)`, `(z ⊗ x) ⊗ p ↦ (z ⊗ 1) ⊗ (x ⊗ p)`. This is the
module-level step behind the associativity of induction in Webster, *Weighted
Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.4, Proposition 2.18. -/
def extIndLeft :
    ExtTensor k (IndK k X φ) P ≃ₗ[B ⊗[k] C] IndK k (ExtTensor k X P) (tensorLeft k C φ hφ) :=
  { extIndLeftFwd k C φ hφ with
    invFun := extIndLeftBwd k C φ hφ
    left_inv := extIndLeftBwd_fwd k C φ hφ
    right_inv := extIndLeftFwd_bwd k C φ hφ }

theorem extIndLeft_tmul_tmul (z : Corner φ) (x : X) (p : P) :
    extIndLeft k C φ hφ X P (ExtTensor.tmul (k := k) (P := IndK k X φ) (Ind.tmul z x) p) =
      Ind.tmul (leftCorner z) (ExtTensor.tmul x p) := rfl


theorem tensorRight_one : tensorRight k C φ hφ 1 = (1 : C) ⊗ₜ[k] φ 1 := rfl

theorem tensorRight_smul (c : k) (t : C ⊗[k] A) :
    tensorRight k C φ hφ (c • t) = c • tensorRight k C φ hφ t :=
  LinearMap.map_smul (TensorProduct.map LinearMap.id (linearOf k φ hφ)) c t

variable {k C φ hφ} in
/-- The element `1 ⊗ z` of the corner of `id ⊗ φ`. -/
def rightCorner (z : Corner φ) : Corner (tensorRight k C φ hφ) :=
  ⟨(1 : C) ⊗ₜ[k] z.1, by
    change (1 : C) ⊗ₜ[k] z.1 * tensorRight k C φ hφ 1 = (1 : C) ⊗ₜ[k] z.1
    rw [tensorRight_one, Algebra.TensorProduct.tmul_mul_tmul, z.2, mul_one]⟩

theorem rightCorner_add (z z' : Corner φ) :
    rightCorner (C := C) (hφ := hφ) (z + z') = rightCorner z + rightCorner z' :=
  Subtype.ext (TensorProduct.tmul_add _ _ _)

theorem rightCorner_op_smul (a : A) (z : Corner φ) :
    rightCorner (C := C) (hφ := hφ) (op a • z) = op ((1 : C) ⊗ₜ[k] a) • rightCorner z :=
  Subtype.ext (by
    change (1 : C) ⊗ₜ[k] (z.1 * φ a) = (1 : C) ⊗ₜ[k] z.1 * ((1 : C) ⊗ₜ[k] φ a)
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one])

theorem rightCorner_smul (b : B) (z : Corner φ) :
    rightCorner (C := C) (hφ := hφ) (b • z) = ((1 : C) ⊗ₜ[k] b) • rightCorner z :=
  Subtype.ext (by
    change (1 : C) ⊗ₜ[k] (b * z.1) = (1 : C) ⊗ₜ[k] b * (1 : C) ⊗ₜ[k] z.1
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one])


/-- For fixed `p`, the map `z ⊗ x ↦ (1 ⊗ z) ⊗ (p ⊗ x)`. -/
def extIndRightInner (p : P) : Ind X φ →+ Ind (ExtTensor k P X) (tensorRight k C φ hφ) :=
  Ind.liftAdd (fun z x => Ind.tmul (rightCorner z) (ExtTensor.tmul p x))
    (fun z z' x => by rw [rightCorner_add, Ind.add_tmul])
    (fun z x x' => by rw [ExtTensor.tmul_add, Ind.tmul_add])
    (fun z a x => by
      rw [rightCorner_op_smul, Ind.op_smul_tmul, ExtTensor.smul_tmul, one_smul])

theorem extIndRightInner_tmul (p : P) (z : Corner φ) (x : X) :
    extIndRightInner k C φ hφ p (Ind.tmul z x) =
      Ind.tmul (rightCorner z) (ExtTensor.tmul p x) := rfl

theorem extIndRightInner_smul (p : P) (b : B) (y : Ind X φ) :
    extIndRightInner k C φ hφ p (b • y) =
      ((1 : C) ⊗ₜ[k] b) • extIndRightInner k C φ hφ p y := by
  induction y using Ind.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul z x =>
    rw [Ind.smul_tmul, extIndRightInner_tmul, extIndRightInner_tmul, rightCorner_smul,
      Ind.smul_tmul]
  | add s t hs ht => rw [smul_add, map_add, map_add, hs, ht, smul_add]

theorem extIndRightInner_smul_left (c : C) (p : P) (y : Ind X φ) :
    extIndRightInner k C φ hφ (c • p) y =
      (c ⊗ₜ[k] (1 : B)) • extIndRightInner k C φ hφ p y := by
  induction y using Ind.induction_on with
  | zero => rw [map_zero, map_zero, smul_zero]
  | tmul z x =>
    rw [extIndRightInner_tmul, extIndRightInner_tmul, Ind.smul_tmul]
    have h1 : (ExtTensor.tmul (c • p) x : ExtTensor k P X) =
        (c ⊗ₜ[k] (1 : A)) • ExtTensor.tmul p x := by
      rw [ExtTensor.smul_tmul, one_smul]
    have h2 : (op (c ⊗ₜ[k] (1 : A)) • rightCorner z : Corner (tensorRight k C φ hφ)) =
        (c ⊗ₜ[k] (1 : B)) • rightCorner z := Subtype.ext (by
      change (1 : C) ⊗ₜ[k] z.1 * (c ⊗ₜ[k] φ 1) = c ⊗ₜ[k] (1 : B) * (1 : C) ⊗ₜ[k] z.1
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, z.2,
        one_mul, one_mul, mul_one])
    rw [h1, ← Ind.op_smul_tmul, h2]
  | add s t hs ht => rw [map_add, map_add, hs, ht, smul_add]

theorem extIndRightInner_add_left (p p' : P) (y : Ind X φ) :
    extIndRightInner k C φ hφ (p + p') y =
      extIndRightInner k C φ hφ p y + extIndRightInner k C φ hφ p' y := by
  induction y using Ind.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, add_zero]
  | tmul z x =>
    rw [extIndRightInner_tmul, extIndRightInner_tmul, extIndRightInner_tmul, ExtTensor.add_tmul,
      Ind.tmul_add]
  | add s t hs ht => rw [map_add, map_add, map_add, hs, ht]; abel

theorem extIndRightInner_scalar_left (c : k) (p : P) (y : Ind X φ) :
    extIndRightInner k C φ hφ (c • p) y =
      algebraMap k (C ⊗[k] B) c • extIndRightInner k C φ hφ p y := by
  induction y using Ind.induction_on with
  | zero => rw [map_zero, map_zero, smul_zero]
  | tmul z x =>
    rw [extIndRightInner_tmul, extIndRightInner_tmul, ← ExtTensor.smul_tmul']
    exact Ind.tmul_algebraMap_smul k (tensorRight_smul k C φ hφ) _ c _
  | add s t hs ht => rw [map_add, map_add, hs, ht, smul_add]

theorem extIndRightInner_smul_smul (c : C) (b : B) (p : P) (y : Ind X φ) :
    extIndRightInner k C φ hφ (c • p) (b • y) = (c ⊗ₜ[k] b) • extIndRightInner k C φ hφ p y := by
  rw [extIndRightInner_smul, extIndRightInner_smul_left, ← mul_smul,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- The forward map `p ⊗ (z ⊗ x) ↦ (1 ⊗ z) ⊗ (p ⊗ x)` as a `k`-linear map. -/
def extIndRightFwdK :
    ExtTensor k P (IndK k X φ) →ₗ[k] IndK k (ExtTensor k P X) (tensorRight k C φ hφ) :=
  ExtTensor.lift (LinearMap.mk₂ k
    (fun (p : P) (y : IndK k X φ) =>
      (show IndK k (ExtTensor k P X) (tensorRight k C φ hφ) from extIndRightInner k C φ hφ p y))
    (fun p p' y => extIndRightInner_add_left k C φ hφ p p' y)
    (fun c p y => extIndRightInner_scalar_left k C φ hφ c p y)
    (fun p y y' => map_add (extIndRightInner k C φ hφ p) y y')
    (fun c p y => by
      have h := extIndRightInner_smul k C φ hφ p (algebraMap k B c) y
      rw [← Algebra.TensorProduct.algebraMap_apply'] at h
      exact h))

theorem extIndRightFwdK_tmul (p : P) (y : IndK k X φ) :
    extIndRightFwdK k C φ hφ (ExtTensor.tmul p y) = extIndRightInner k C φ hφ p y := rfl

/-- The forward map of `extIndRight`. -/
def extIndRightFwd :
    ExtTensor k P (IndK k X φ) →ₗ[C ⊗[k] B] IndK k (ExtTensor k P X) (tensorRight k C φ hφ) where
  toFun := extIndRightFwdK k C φ hφ
  map_add' := map_add _
  map_smul' t x := ExtTensor.smul_eq_induction (map_add _) (map_zero _)
    (fun c b p y => by
      rw [ExtTensor.smul_tmul, extIndRightFwdK_tmul, extIndRightFwdK_tmul]
      exact extIndRightInner_smul_smul k C φ hφ c b p y) t x

/-- `extIndRightFwd` with values in `Ind`, for computations. -/
def extIndRightFwdAdd :
    ExtTensor k P (IndK k X φ) →+ Ind (ExtTensor k P X) (tensorRight k C φ hφ) :=
  (extIndRightFwd k C φ hφ).toAddMonoidHom

theorem extIndRightFwdAdd_tmul_tmul (z : Corner φ) (x : X) (p : P) :
    extIndRightFwdAdd k C φ hφ (ExtTensor.tmul (k := k) (Q := IndK k X φ) p (Ind.tmul z x)) =
      Ind.tmul (rightCorner z) (ExtTensor.tmul p x) := rfl

theorem extIndRightFwdAdd_smul (b : C ⊗[k] B) (v : ExtTensor k P (IndK k X φ)) :
    extIndRightFwdAdd k C φ hφ (b • v) = b • extIndRightFwdAdd k C φ hφ v :=
  (extIndRightFwd k C φ hφ).map_smul b v

omit [Algebra k A] [Module k X] [IsScalarTower k A X] in
theorem extTmul_zero_right (p : P) :
    ExtTensor.tmul (k := k) (Q := IndK k X φ) p (0 : Ind X φ) = 0 :=
  ExtTensor.tmul_zero (Q := IndK k X φ) p

omit [Algebra k A] [Module k X] [IsScalarTower k A X] in
theorem extTmul_add_right (p : P) (s t : Ind X φ) :
    ExtTensor.tmul (k := k) (Q := IndK k X φ) p (s + t) =
      ExtTensor.tmul (k := k) (Q := IndK k X φ) p s +
        ExtTensor.tmul (k := k) (Q := IndK k X φ) p t :=
  ExtTensor.tmul_add (Q := IndK k X φ) p s t

/-- The map `p ⊗ x ↦ p ⊗ (φ 1 ⊗ x)`. -/
def extIndRightUnit : ExtTensor k P X →ₗ[k] ExtTensor k P (IndK k X φ) :=
  ExtTensor.lift (LinearMap.mk₂ k
    (fun (p : P) (x : X) => ExtTensor.tmul (k := k) (Q := IndK k X φ) p (Ind.tmul (unitGen φ) x))
    (fun p p' x => ExtTensor.add_tmul _ _ _)
    (fun c p x => (ExtTensor.smul_tmul' c p _).symm)
    (fun p x x' => by rw [Ind.tmul_add, extTmul_add_right])
    (fun c p x => by
      rw [Ind.tmul_algebraMap_smul k hφ]
      exact ExtTensor.tmul_smul (Q := IndK k X φ) c p (Ind.tmul (unitGen φ) x)))

theorem extIndRightUnit_tmul (p : P) (x : X) :
    extIndRightUnit k φ hφ (ExtTensor.tmul p x) =
      ExtTensor.tmul (k := k) (Q := IndK k X φ) p (Ind.tmul (unitGen φ) x) := rfl

theorem extIndRightUnit_smul (t : C ⊗[k] A) (w : ExtTensor k P X) :
    extIndRightUnit k φ hφ (t • w) = tensorRight k C φ hφ t • extIndRightUnit k φ hφ w := by
  induction t using TensorProduct.inductionOn with
  | tmul c a =>
    induction w using ExtTensor.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | tmul p x =>
      rw [ExtTensor.smul_tmul, extIndRightUnit_tmul, extIndRightUnit_tmul, tensorRight_tmul,
        unitGen_tmul_smul]
      exact (ExtTensor.smul_tmul (Q := IndK k X φ) c (φ a) p (Ind.tmul (unitGen φ) x)).symm
    | add w w' hw hw' => rw [smul_add, map_add, map_add, hw, hw', smul_add]
  | add t t' ht ht' => rw [add_smul, map_add, ht, ht', map_add, add_smul]

/-- The backward map of `extIndRight`: `y ⊗ (p ⊗ x) ↦ y · (p ⊗ (φ 1 ⊗ x))`. -/
def extIndRightBwd :
    Ind (ExtTensor k P X) (tensorRight k C φ hφ) →ₗ[C ⊗[k] B] ExtTensor k P (IndK k X φ) :=
  Ind.lift (fun y w => y.1 • extIndRightUnit k φ hφ w)
    (fun y y' w => add_smul _ _ _)
    (fun y w w' => by rw [map_add, smul_add])
    (fun y t w => by
      change (y.1 * tensorRight k C φ hφ t) • _ = _
      rw [mul_smul, extIndRightUnit_smul])
    (fun s y w => mul_smul _ _ _)

theorem extIndRightBwd_tmul (y : Corner (tensorRight k C φ hφ)) (w : ExtTensor k P X) :
    extIndRightBwd k C φ hφ (Ind.tmul y w) = y.1 • extIndRightUnit k φ hφ w := rfl

theorem extIndRightBwd_fwd (v : ExtTensor k P (IndK k X φ)) :
    extIndRightBwd k C φ hφ (extIndRightFwdAdd k C φ hφ v) = v := by
  induction v using ExtTensor.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul p y =>
    induction y using Ind.induction_on with
    | zero => rw [extTmul_zero_right, map_zero, map_zero]
    | tmul z x =>
      rw [extIndRightFwdAdd_tmul_tmul, extIndRightBwd_tmul, extIndRightUnit_tmul]
      change ((1 : C) ⊗ₜ[k] z.1) • _ = _
      refine (ExtTensor.smul_tmul (Q := IndK k X φ) (1 : C) z.1 p (Ind.tmul (unitGen φ) x)).trans
        ?_
      rw [one_smul]
      congr 1
      exact (Ind.smul_tmul z.1 (unitGen φ) x).trans
        (congrArg (fun w => Ind.tmul w x) (Subtype.ext z.2))
    | add s t hs ht => rw [extTmul_add_right, map_add, map_add, hs, ht]
  | add v v' hv hv' => rw [map_add, map_add, hv, hv']

theorem extIndRightFwd_bwd (v : Ind (ExtTensor k P X) (tensorRight k C φ hφ)) :
    extIndRightFwdAdd k C φ hφ (extIndRightBwd k C φ hφ v) = v := by
  induction v using Ind.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul y w =>
    induction w using ExtTensor.induction_on with
    | zero => rw [Ind.tmul_zero, map_zero, map_zero]
    | tmul p x =>
      rw [extIndRightBwd_tmul, extIndRightUnit_tmul, extIndRightFwdAdd_smul,
        extIndRightFwdAdd_tmul_tmul, Ind.smul_tmul]
      congr 1
      exact Subtype.ext (by
        change y.1 * ((1 : C) ⊗ₜ[k] φ 1) = y.1
        rw [← tensorRight_one]
        exact y.2)
    | add w w' hw hw' => rw [Ind.tmul_add, map_add, map_add, hw, hw']
  | add v v' hv hv' => rw [map_add, map_add, hv, hv']

variable (X P) in
/-- **Induction commutes with external tensor products** on the right:
`P ⊠ Ind_φ X ≅ Ind_{id ⊗ φ} (P ⊠ X)`, `p ⊗ (z ⊗ x) ↦ (1 ⊗ z) ⊗ (p ⊗ x)`. This is the
module-level step behind the associativity of induction in Webster, *Weighted
Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.4, Proposition 2.18. -/
def extIndRight :
    ExtTensor k P (IndK k X φ) ≃ₗ[C ⊗[k] B] IndK k (ExtTensor k P X) (tensorRight k C φ hφ) :=
  { extIndRightFwd k C φ hφ with
    invFun := extIndRightBwd k C φ hφ
    left_inv := extIndRightBwd_fwd k C φ hφ
    right_inv := extIndRightFwd_bwd k C φ hφ }

theorem extIndRight_tmul_tmul (z : Corner φ) (x : X) (p : P) :
    extIndRight k C φ hφ X P (ExtTensor.tmul (k := k) (Q := IndK k X φ) p (Ind.tmul z x)) =
      Ind.tmul (rightCorner z) (ExtTensor.tmul p x) := rfl

end ExtInd

end InductionAlong

end

end Categorification

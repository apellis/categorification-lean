/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongTensor

/-!
# Induction along a map of one tensor factor

Let `φ : A → B` be a `k`-linear nonunital ring map and `ψ : A ⊗ C → B ⊗ C` a nonunital ring
map with `ψ (a ⊗ c) = φ a ⊗ c` (for instance `tensorLeft k C φ hφ`). For a left
`A ⊗ C`-module `N`, write `N|_A` for `N` viewed as an `A`-module through `a ↦ a ⊗ 1`
(`LeftFactorRes`). Then induction along `ψ` only sees the `A`-module `N|_A`:
`(B ⊗ C)ψ(1) ⊗_{A ⊗ C} N ≅ Bφ(1) ⊗_A N|_A` as `k`-modules, by `z ⊗ c ⊗ n ↦ z ⊗ (1 ⊗ c) n`
(`indLeftFactorEquiv`).

These identifications reduce the factor-wise functors `₁Fᵢ`, `₂Fᵢ` of Webster,
*Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5 (before
Proposition 5.5), on modules over `T^{λ₁} ⊗ T^{λ₂}`, to induction over one factor; this is used
in the dimension count of the proof of Proposition 5.5.
-/

namespace Categorification

open MulOpposite
open scoped TensorProduct

noncomputable section

namespace InductionAlong

universe u w

/-! ### The first factor -/

section LeftFactor

variable (k : Type*) [CommRing k] (A : Type u) [Ring A] [Algebra k A] (C : Type u) [Ring C]
  [Algebra k C] (N : Type w) [AddCommGroup N] [Module k N] [Module (A ⊗[k] C) N]
  [IsScalarTower k (A ⊗[k] C) N]

/-- `N` viewed as an `A`-module through `a ↦ a ⊗ 1`. -/
@[nolint unusedArguments]
def LeftFactorRes (k : Type*) [CommRing k] (A : Type u) [Ring A] [Algebra k A] (C : Type u)
    [Ring C] [Algebra k C] (N : Type w) : Type w := N

instance : AddCommGroup (LeftFactorRes k A C N) := inferInstanceAs (AddCommGroup N)

instance : Module k (LeftFactorRes k A C N) := inferInstanceAs (Module k N)

instance : Module A (LeftFactorRes k A C N) :=
  Module.compHom N (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[k] C)

variable {k A C N}

/-- The identification of `N` with `N|_A`. -/
def toLeftFactorRes : N ≃ₗ[k] LeftFactorRes k A C N := LinearEquiv.refl k N

omit [IsScalarTower k (A ⊗[k] C) N] in
theorem smul_toLeftFactorRes (a : A) (n : N) :
    a • toLeftFactorRes (k := k) (A := A) (C := C) n =
      toLeftFactorRes (k := k) (A := A) (C := C) ((a ⊗ₜ[k] (1 : C)) • n) := rfl

instance : IsScalarTower k A (LeftFactorRes k A C N) where
  smul_assoc c a x := by
    change ((c • a) ⊗ₜ[k] (1 : C)) • (show N from x) = c • ((a ⊗ₜ[k] (1 : C)) • (show N from x))
    rw [← TensorProduct.smul_tmul', smul_assoc]

variable {B : Type u} [Ring B] [Algebra k B] (φ : A →ₙ+* B)
  (hφ : ∀ (c : k) (t : A), φ (c • t) = c • φ t)
  (ψ : A ⊗[k] C →ₙ+* B ⊗[k] C) (hψ : ∀ (a : A) (c : C), ψ (a ⊗ₜ c) = φ a ⊗ₜ c)

include hφ hψ in
theorem leftFactor_map_smul (c : k) (t : A ⊗[k] C) : ψ (c • t) = c • ψ t := by
  induction t using TensorProduct.inductionOn with
  | tmul a x => rw [TensorProduct.smul_tmul', hψ, hψ, hφ, TensorProduct.smul_tmul']
  | add s t hs ht => rw [smul_add, map_add, map_add, hs, ht, smul_add]

/-- The corner element `b φ(1)`. -/
def leftFactorCorner (b : B) : Corner φ := ⟨b * φ 1, mul_mem_corner φ b 1⟩

/-- For fixed `b`, `c`: `n ↦ b φ(1) ⊗ (1 ⊗ c) n`. -/
def leftFactorInner (b : B) (c : C) : N →ₗ[k] IndK k (LeftFactorRes k A C N) φ where
  toFun n := IndK.tmul (leftFactorCorner φ b) (toLeftFactorRes (k := k) (A := A) (C := C)
    (((1 : A) ⊗ₜ[k] c) • n))
  map_add' n n' := by
    rw [smul_add, map_add]
    exact Ind.tmul_add _ _ _
  map_smul' r n := by
    rw [smul_comm, map_smul, RingHom.id_apply]
    exact Ind.tmul_algebraMap_smul k hφ _ r _

/-- The bilinear map `(b ⊗ c, n) ↦ b φ(1) ⊗ (1 ⊗ c) n`. -/
def leftFactorFwdLin : B ⊗[k] C →ₗ[k] N →ₗ[k] IndK k (LeftFactorRes k A C N) φ :=
  TensorProduct.lift (LinearMap.mk₂ k (fun b c => leftFactorInner φ hφ b c)
    (fun b b' c => LinearMap.ext fun n => by
      change IndK.tmul _ _ = IndK.tmul _ _ + IndK.tmul _ _
      have : leftFactorCorner φ (b + b') = leftFactorCorner φ b + leftFactorCorner φ b' :=
        Subtype.ext (add_mul b b' (φ 1))
      rw [this]
      exact Ind.add_tmul _ _ _)
    (fun r b c => LinearMap.ext fun n => by
      rw [LinearMap.smul_apply]
      change IndK.tmul _ _ = r • IndK.tmul _ _
      have : leftFactorCorner φ (r • b) = algebraMap k B r • leftFactorCorner φ b :=
        Subtype.ext (by
          change (r • b) * φ 1 = algebraMap k B r * (b * φ 1)
          rw [Algebra.smul_def, mul_assoc])
      rw [this, ← IndK.algebraMap_smul]
      exact (Ind.smul_tmul _ _ _).symm)
    (fun b c c' => LinearMap.ext fun n => by
      change IndK.tmul _ _ = IndK.tmul _ _ + IndK.tmul _ _
      rw [TensorProduct.tmul_add, add_smul, map_add]
      exact Ind.tmul_add _ _ _)
    (fun r b c => LinearMap.ext fun n => by
      rw [LinearMap.smul_apply]
      change IndK.tmul _ _ = r • IndK.tmul _ _
      rw [TensorProduct.tmul_smul, smul_assoc, map_smul, ← IndK.algebraMap_smul]
      exact Ind.tmul_algebraMap_smul k hφ _ r _))

theorem leftFactorFwdLin_tmul (b : B) (c : C) (n : N) :
    leftFactorFwdLin φ hφ (b ⊗ₜ c) n = IndK.tmul (leftFactorCorner φ b)
      (toLeftFactorRes (k := k) (A := A) (C := C) (((1 : A) ⊗ₜ[k] c) • n)) := rfl

include hψ in
theorem leftFactorFwdLin_mul (y : B ⊗[k] C) (t : A ⊗[k] C) (n : N) :
    leftFactorFwdLin φ hφ (y * ψ t) n = leftFactorFwdLin φ hφ y (t • n) := by
  induction y using TensorProduct.inductionOn with
  | add y y' hy hy' => rw [add_mul, map_add, map_add, LinearMap.add_apply,
      LinearMap.add_apply, hy, hy']
  | tmul b c =>
    induction t using TensorProduct.inductionOn with
    | add t t' ht ht' => rw [map_add, mul_add, map_add, LinearMap.add_apply, ht, ht',
        add_smul, map_add]
    | tmul a c' =>
      rw [hψ, Algebra.TensorProduct.tmul_mul_tmul, leftFactorFwdLin_tmul,
        leftFactorFwdLin_tmul]
      have h1 : leftFactorCorner φ (b * φ a) = op a • leftFactorCorner φ b := Subtype.ext (by
        change b * φ a * φ 1 = b * φ 1 * φ a
        rw [mul_assoc, mul_assoc, ← map_mul, ← map_mul, mul_one, one_mul])
      have h2 : ((1 : A) ⊗ₜ[k] c) • (a ⊗ₜ[k] c') • n =
          (a ⊗ₜ[k] (1 : C)) • ((1 : A) ⊗ₜ[k] (c * c')) • n := by
        rw [← mul_smul, ← mul_smul, Algebra.TensorProduct.tmul_mul_tmul,
          Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, one_mul]
      rw [h1, h2]
      exact Ind.op_smul_tmul _ _ _

/-- The forward map `Ind_ψ N → Ind_φ N|_A`. -/
def indLeftFactorFwd : Ind N ψ →+ IndK k (LeftFactorRes k A C N) φ :=
  Ind.liftAdd (fun z n => leftFactorFwdLin φ hφ z.1 n)
    (fun z z' n => by
      change leftFactorFwdLin φ hφ (z.1 + z'.1) n = _
      rw [map_add, LinearMap.add_apply])
    (fun z n n' => map_add _ n n')
    (fun z t n => leftFactorFwdLin_mul φ hφ ψ hψ z.1 t n)

theorem indLeftFactorFwd_tmul (z : Corner ψ) (n : N) :
    indLeftFactorFwd φ hφ ψ hψ (Ind.tmul z n) = leftFactorFwdLin φ hφ z.1 n := rfl

include hψ in
theorem leftFactor_one : ψ 1 = φ 1 ⊗ₜ[k] (1 : C) := by
  rw [Algebra.TensorProduct.one_def, hψ]

/-- The corner element `z ⊗ 1` of `ψ`. -/
def leftFactorUp (z : Corner φ) : Corner ψ :=
  ⟨z.1 ⊗ₜ[k] (1 : C), by
    change z.1 ⊗ₜ[k] (1 : C) * ψ 1 = z.1 ⊗ₜ[k] (1 : C)
    rw [leftFactor_one φ ψ hψ, Algebra.TensorProduct.tmul_mul_tmul, z.2, mul_one]⟩

/-- The backward map `Ind_φ N|_A → Ind_ψ N`. -/
def indLeftFactorBwd : IndK k (LeftFactorRes k A C N) φ →+ Ind N ψ :=
  Ind.liftAdd (fun z x => Ind.tmul (leftFactorUp φ ψ hψ z) (toLeftFactorRes.symm x))
    (fun z z' x => by
      have : leftFactorUp φ ψ hψ (z + z') = leftFactorUp φ ψ hψ z + leftFactorUp φ ψ hψ z' :=
        Subtype.ext (TensorProduct.add_tmul _ _ _)
      rw [this, Ind.add_tmul])
    (fun z x x' => by rw [map_add, Ind.tmul_add])
    (fun z a x => by
      have : leftFactorUp φ ψ hψ (op a • z) = op (a ⊗ₜ[k] (1 : C)) • leftFactorUp φ ψ hψ z :=
        Subtype.ext (by
          change (z.1 * φ a) ⊗ₜ[k] (1 : C) = z.1 ⊗ₜ[k] (1 : C) * ψ (a ⊗ₜ[k] (1 : C))
          rw [hψ, Algebra.TensorProduct.tmul_mul_tmul, mul_one])
      rw [this, Ind.op_smul_tmul]
      rfl)

omit [IsScalarTower k (A ⊗[k] C) N] in
theorem indLeftFactorBwd_tmul (z : Corner φ) (x : LeftFactorRes k A C N) :
    indLeftFactorBwd φ ψ hψ (Ind.tmul z x) =
      Ind.tmul (leftFactorUp φ ψ hψ z) (toLeftFactorRes.symm x) := rfl

theorem indLeftFactorBwd_fwdLin (y : B ⊗[k] C) (n : N) :
    indLeftFactorBwd φ ψ hψ (leftFactorFwdLin φ hφ y n) =
      Ind.tmul ⟨y * ψ 1, mul_mem_corner ψ y 1⟩ n := by
  induction y using TensorProduct.inductionOn with
  | add y y' hy hy' =>
    rw [map_add, LinearMap.add_apply]
    change indLeftFactorBwd φ ψ hψ (leftFactorFwdLin φ hφ y n + leftFactorFwdLin φ hφ y' n) = _
    rw [map_add, hy, hy', ← Ind.add_tmul]
    congr 1
    exact Subtype.ext (add_mul y y' (ψ 1)).symm
  | tmul b c =>
    rw [leftFactorFwdLin_tmul]
    change Ind.tmul (leftFactorUp φ ψ hψ (leftFactorCorner φ b)) (((1 : A) ⊗ₜ[k] c) • n) = _
    rw [← Ind.op_smul_tmul]
    congr 1
    apply Subtype.ext
    change (b * φ 1) ⊗ₜ[k] (1 : C) * ψ ((1 : A) ⊗ₜ[k] c) = b ⊗ₜ[k] c * ψ 1
    rw [hψ, leftFactor_one φ ψ hψ, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, mul_assoc, ← map_mul, mul_one]

theorem indLeftFactorBwd_fwd (t : Ind N ψ) :
    indLeftFactorBwd φ ψ hψ (indLeftFactorFwd φ hφ ψ hψ t) = t := by
  induction t using Ind.induction_on with
  | zero => simp only [map_zero]
  | tmul z n =>
    rw [indLeftFactorFwd_tmul, indLeftFactorBwd_fwdLin]
    congr 1
    exact Subtype.ext z.2
  | add s t hs ht => rw [map_add, map_add, hs, ht]

theorem indLeftFactorFwd_bwd (t : IndK k (LeftFactorRes k A C N) φ) :
    indLeftFactorFwd φ hφ ψ hψ (indLeftFactorBwd φ ψ hψ t) = t := by
  induction t using Ind.induction_on with
  | zero =>
    exact (congrArg (indLeftFactorFwd φ hφ ψ hψ) (map_zero (indLeftFactorBwd φ ψ hψ))).trans
      (map_zero _)
  | tmul z x =>
    rw [indLeftFactorBwd_tmul, indLeftFactorFwd_tmul]
    change leftFactorFwdLin φ hφ (z.1 ⊗ₜ[k] (1 : C)) _ = _
    rw [leftFactorFwdLin_tmul, ← Algebra.TensorProduct.one_def, one_smul]
    change Ind.tmul _ x = Ind.tmul z x
    congr 1
    exact Subtype.ext z.2
  | add s t hs ht =>
    exact (congrArg (indLeftFactorFwd φ hφ ψ hψ) (map_add (indLeftFactorBwd φ ψ hψ) s t)).trans
      ((map_add _ _ _).trans (congrArg₂ (· + ·) hs ht))

theorem indLeftFactorFwd_algebraMap_smul (r : k) (t : Ind N ψ) :
    indLeftFactorFwd φ hφ ψ hψ (algebraMap k (B ⊗[k] C) r • t) =
      r • indLeftFactorFwd φ hφ ψ hψ t := by
  induction t using Ind.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul z n =>
    rw [← Ind.tmul_algebraMap_smul k (leftFactor_map_smul φ hφ ψ hψ), indLeftFactorFwd_tmul,
      indLeftFactorFwd_tmul, map_smul]
  | add s t hs ht => rw [smul_add, map_add, map_add, hs, ht, smul_add]

/-- **Induction along a map of the first factor**: `Ind_ψ N ≅ Ind_φ N|_A` as `k`-modules. -/
def indLeftFactorEquiv : IndK k N ψ ≃ₗ[k] IndK k (LeftFactorRes k A C N) φ where
  toFun := indLeftFactorFwd φ hφ ψ hψ
  invFun := indLeftFactorBwd φ ψ hψ
  map_add' := map_add _
  map_smul' r t := indLeftFactorFwd_algebraMap_smul φ hφ ψ hψ r t
  left_inv := indLeftFactorBwd_fwd φ hφ ψ hψ
  right_inv := indLeftFactorFwd_bwd φ hφ ψ hψ

theorem indLeftFactorEquiv_tmul (z : Corner ψ) (n : N) :
    indLeftFactorEquiv φ hφ ψ hψ (IndK.tmul z n) = leftFactorFwdLin φ hφ z.1 n := rfl

include hφ hψ in
theorem finrank_indLeftFactor :
    Module.finrank k (IndK k N ψ) = Module.finrank k (IndK k (LeftFactorRes k A C N) φ) :=
  (indLeftFactorEquiv φ hφ ψ hψ).finrank_eq

end LeftFactor

end InductionAlong

end

end Categorification

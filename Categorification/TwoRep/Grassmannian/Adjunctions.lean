/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.Grassmannian.Graded

/-!
# Induction and restriction bimodules

For a graded commutative algebra `A`, the algebra `A` is a graded `(k, A)`-bimodule `up A e` and a
graded `(A, k)`-bimodule `down A e` (offset `e`). These are the 1-morphisms of the
cohomology-of-Grassmannians model of the categorified irreducible `sl₂`-module of highest weight
`2` (S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, Definition 1.2; the model is built in `Grassmannian/StrongSl2.lean`).

## Main definitions

* `GrAlg.unit k`: the ground field in degree `0`; `GrAlg.trivial k`: the zero algebra;
  `GrAlg.dual k`: the dual numbers `k[x]/(x²)` with `x` in degree `2` (the cohomology of `ℙ¹`);
* `GBim.up`, `GBim.down`;
* `GBim.upDownAdj`: `up A e ⊣ down A g` for `e + g = 0` (unit `1 ↦ 1 ⊗ 1`, counit the
  multiplication);
* `GBim.downUpAdj`: `down (dual k) e ⊣ up (dual k) g` for `e + g = -2` (unit
  `1 ↦ 1 ⊗ x + x ⊗ 1`, counit the trace `a + b x ↦ b`).
-/

noncomputable section

namespace Categorification.TwoRep.Grassmannian

open CategoryTheory CategoryTheory.Limits TensorProduct Bicategory

universe u

variable {k : Type u} [Field k]

/-! ### The algebras -/

namespace GrAlg

variable (k) in
/-- The ground field, in degree `0`. -/
def unit : GrAlg k where
  carrier := k
  deg := 0
  deg_mul _ _ := by simp

variable (k) in
/-- The identification of `k` with the carrier of `unit k`. -/
def unitEquiv : k ≃ₐ[k] (unit k).carrier := AlgEquiv.refl

@[simp] theorem unit_deg (c : (unit k).carrier) : (unit k).deg c = 0 := rfl

variable (k) in
/-- The zero algebra. -/
def trivial : GrAlg k where
  carrier := PUnit
  deg := 0
  deg_mul _ _ := Subsingleton.elim _ _

/-- The degree derivation of the dual numbers: `a + b x ↦ 2 b x`. -/
def dualDeg : DualNumber k →ₗ[k] DualNumber k :=
  (2 : k) • (TrivSqZeroExt.inrHom k k ∘ₗ TrivSqZeroExt.sndHom k k)

@[simp] theorem dualDeg_fst (a : DualNumber k) : (dualDeg a).fst = 0 := by simp [dualDeg]

@[simp] theorem dualDeg_snd (a : DualNumber k) : (dualDeg a).snd = 2 * a.snd := by simp [dualDeg]

theorem dualDeg_eps : dualDeg (DualNumber.eps : DualNumber k) = (2 : k) • DualNumber.eps := by
  ext <;> simp

variable (k) in
/-- The dual numbers `k[x]/(x²)` with `x` in degree `2`: the cohomology ring of `ℙ¹`. -/
def dual : GrAlg k where
  carrier := DualNumber k
  finite := inferInstanceAs (Module.Finite k (k × k))
  deg := dualDeg
  deg_mul a b := by ext <;> simp; ring

variable (k) in
/-- The identification of `k[x]/(x²)` with the carrier of `dual k`. -/
def dualEquiv : DualNumber k ≃ₐ[k] (dual k).carrier := AlgEquiv.refl

@[simp] theorem dual_deg (a : DualNumber k) : (dual k).deg (dualEquiv k a) = dualEquiv k (dualDeg a) :=
  rfl

end GrAlg

/-! ### The bimodules -/

namespace GBim

variable {A B : GrAlg k}

theorem D_apply (X : GBim A B) (x : X) : X.D x = X.deg x + X.off • x := by
  simp [D]

/-- `A` as a graded `(k, A)`-bimodule with offset `e`. -/
def up (A : GrAlg k) (e : ℤ) : GBim (GrAlg.unit k) A where
  carrier := A
  actL := (Algebra.ofId k (Module.End k A)).comp (GrAlg.unitEquiv k).symm.toAlgHom
  actR := Algebra.lmul k A
  comm a b := LinearMap.ext fun x => by
    obtain ⟨a, rfl⟩ := (GrAlg.unitEquiv k).surjective a
    simp
  deg := A.deg
  deg_actL a := LinearMap.ext fun x => by
    obtain ⟨a, rfl⟩ := (GrAlg.unitEquiv k).surjective a
    simp
  deg_actR a := LinearMap.ext fun x => by simp [A.deg_mul, add_comm]
  off := e

/-- `A` as a graded `(A, k)`-bimodule with offset `e`. -/
def down (A : GrAlg k) (e : ℤ) : GBim A (GrAlg.unit k) where
  carrier := A
  actL := Algebra.lmul k A
  actR := (Algebra.ofId k (Module.End k A)).comp (GrAlg.unitEquiv k).symm.toAlgHom
  comm a b := LinearMap.ext fun x => by
    obtain ⟨b, rfl⟩ := (GrAlg.unitEquiv k).surjective b
    simp
  deg := A.deg
  deg_actL a := LinearMap.ext fun x => by simp [A.deg_mul, add_comm]
  deg_actR a := LinearMap.ext fun x => by
    obtain ⟨a, rfl⟩ := (GrAlg.unitEquiv k).surjective a
    simp
  off := e

section upDown

variable (A : GrAlg k) (e : ℤ)

/-- The identification of `A` with the carrier of `up A e`. -/
def upEquiv : A ≃ₗ[k] (up A e).carrier := LinearEquiv.refl k A

/-- The identification of `A` with the carrier of `down A e`. -/
def downEquiv : A ≃ₗ[k] (down A e).carrier := LinearEquiv.refl k A

@[simp] theorem up_actL (c : k) (x : A) :
    (up A e).actL (GrAlg.unitEquiv k c) (upEquiv A e x) = upEquiv A e (c • x) := rfl
@[simp] theorem up_actR (b x : A) : (up A e).actR b (upEquiv A e x) = upEquiv A e (b * x) := rfl
@[simp] theorem up_D (x : A) :
    (up A e).D (upEquiv A e x) = upEquiv A e (A.deg x) + e • upEquiv A e x := D_apply _ _
@[simp] theorem down_actL (b x : A) :
    (down A e).actL b (downEquiv A e x) = downEquiv A e (b * x) := rfl
@[simp] theorem down_actR (c : k) (x : A) :
    (down A e).actR (GrAlg.unitEquiv k c) (downEquiv A e x) = downEquiv A e (c • x) := rfl
@[simp] theorem down_D (x : A) :
    (down A e).D (downEquiv A e x) = downEquiv A e (A.deg x) + e • downEquiv A e x :=
  D_apply _ _

@[simp] theorem unit_id_D (c : k) :
    (id (GrAlg.unit k)).D (idEquiv _ (GrAlg.unitEquiv k c)) = 0 := by
  rw [id_D, GrAlg.unit_deg, map_zero]

end upDown

@[simp] theorem bicategory_id₁ (A : GrAlg k) : 𝟙 A = id A := rfl

@[simp] theorem bicategory_comp₁ {C : GrAlg k} (f : A ⟶ B) (g : B ⟶ C) : f ≫ g = comp f g := rfl

@[simp] theorem bicategory_comp₂_val {f g h : A ⟶ B} (η : f ⟶ g) (θ : g ⟶ h) :
    (η ≫ θ).1 = θ.1 ∘ₗ η.1 := rfl

/-! ### `up A e ⊣ down A g` -/

section upDownAdj

variable (A : GrAlg k) {e g : ℤ}

/-- The unit `1 ↦ 1 ⊗ 1`. -/
def upDownUnit (h : e + g = 0) : id (GrAlg.unit k) ⟶ comp (up A e) (down A g) :=
  mkHom (LinearMap.toSpanSingleton k _ (tmk (up A e) (down A g) (upEquiv A e 1 ⊗ₜ downEquiv A g 1)) ∘ₗ
      ((GrAlg.unitEquiv k).toLinearEquiv.trans (idEquiv _)).symm.toLinearMap)
    (fun a x => by
      obtain ⟨x, rfl⟩ := ((GrAlg.unitEquiv k).toLinearEquiv.trans (idEquiv _)).surjective x
      obtain ⟨a, rfl⟩ := (GrAlg.unitEquiv k).surjective a
      simp [mul_smul, mul_comm a x]
      rw [← map_smul, smul_tmul'])
    (fun a x => by
      obtain ⟨x, rfl⟩ := ((GrAlg.unitEquiv k).toLinearEquiv.trans (idEquiv _)).surjective x
      obtain ⟨a, rfl⟩ := (GrAlg.unitEquiv k).surjective a
      simp [tmul_smul, mul_smul, mul_comm a x])
    (fun x => by
      obtain ⟨x, rfl⟩ := ((GrAlg.unitEquiv k).toLinearEquiv.trans (idEquiv _)).surjective x
      simp [GrAlg.deg_one, smul_tmul', tmul_smul]
      rw [← smul_add, ← map_add, ← add_tmul, ← add_smul, h, zero_smul, zero_tmul, map_zero,
        smul_zero])

/-- The counit, the multiplication `x ⊗ y ↦ x y`. -/
def upDownCounit (h : e + g = 0) : comp (down A g) (up A e) ⟶ id A :=
  mkHomₗ (cdesc ((idEquiv A).toLinearMap ∘ₗ TensorProduct.lift ((LinearMap.mul k A).compl₁₂
      (downEquiv A g).symm.toLinearMap (upEquiv A e).symm.toLinearMap))
      (fun c x y => by
        obtain ⟨x, rfl⟩ := (downEquiv A g).surjective x
        obtain ⟨y, rfl⟩ := (upEquiv A e).surjective y
        obtain ⟨c, rfl⟩ := (GrAlg.unitEquiv k).surjective c
        simp))
    (fun a => comp_ext fun x y => by
      obtain ⟨x, rfl⟩ := (downEquiv A g).surjective x
      obtain ⟨y, rfl⟩ := (upEquiv A e).surjective y
      simp [mul_assoc])
    (fun a => comp_ext fun x y => by
      obtain ⟨x, rfl⟩ := (downEquiv A g).surjective x
      obtain ⟨y, rfl⟩ := (upEquiv A e).surjective y
      simp [mul_left_comm])
    (comp_ext fun x y => by
      obtain ⟨x, rfl⟩ := (downEquiv A g).surjective x
      obtain ⟨y, rfl⟩ := (upEquiv A e).surjective y
      simp only [comp_D_tmk, down_D, up_D, map_add, map_zsmul, LinearMap.comp_apply, cdesc_tmk,
        lift.tmul, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
        LinearMap.mul_apply', id_D, A.deg_mul, tmul_add, add_tmul, smul_tmul', tmul_smul,
        LinearMap.smul_apply, map_zsmul]
      obtain rfl : e = -g := by omega
      rw [neg_smul]
      abel)

/-- **`up A e ⊣ down A g`** for `e + g = 0`. -/
def upDownAdj (h : e + g = 0) : Bicategory.Adjunction (B := GrAlg k) (up A e) (down A g) where
  unit := upDownUnit A h
  counit := upDownCounit A h
  left_triangle := by
    apply hom_ext
    refine comp_ext_idL fun c x => ?_
    obtain ⟨x, rfl⟩ := (upEquiv A e).surjective x
    obtain ⟨c, rfl⟩ := (GrAlg.unitEquiv k).surjective c
    simp only [leftZigzag, bicategoricalComp, upDownUnit, upDownCounit, bicategory_comp₂_val,
      LinearMap.comp_apply, GrAlg.bicategory_whiskerRight, GrAlg.bicategory_whiskerLeft,
      GrAlg.bicategory_associator, BicategoricalCoherence.assoc_iso]
    dsimp only [bicategory_id₁, bicategory_comp₁]
    simp
    rw [← smul_tmul', map_smul, map_smul, map_smul, assocHomₗ_tmk, cmap_tmk]
    congr 1
    simp only [cdesc_tmk, LinearMap.comp_apply, LinearMap.id_apply, lift.tmul,
      LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.mul_apply', one_mul]
    rw [show upEquiv A e x = (up A e).actR x (upEquiv A e 1) by simp, tmk_actR_one]
  right_triangle := by
    apply hom_ext
    refine comp_ext_idR fun x c => ?_
    obtain ⟨x, rfl⟩ := (downEquiv A g).surjective x
    obtain ⟨c, rfl⟩ := (GrAlg.unitEquiv k).surjective c
    simp [rightZigzag, bicategoricalComp, upDownUnit, upDownCounit]
    rw [show downEquiv A g x = (down A g).actL x (downEquiv A g 1) by simp, tmk_one_actL]

end upDownAdj

/-! ### `down (dual k) e ⊣ up (dual k) g` -/

section downUpAdj

variable {e g : ℤ}

local notation "𝔻" => GrAlg.dual k

/-- The element `1 ⊗ x + x ⊗ 1` of `down 𝔻 e ⊗ up 𝔻 g`. -/
def frobT (e g : ℤ) : (comp (down 𝔻 e) (up 𝔻 g)).carrier :=
  tmk _ _ (downEquiv 𝔻 e 1 ⊗ₜ upEquiv 𝔻 g (GrAlg.dualEquiv k DualNumber.eps)) +
    tmk _ _ (downEquiv 𝔻 e (GrAlg.dualEquiv k DualNumber.eps) ⊗ₜ upEquiv 𝔻 g 1)

theorem cast_add_add_two (h : e + g = -2) : (e : k) + g + 2 = 0 := by
  have := congrArg (Int.cast : ℤ → k) (show e + g + 2 = 0 by omega)
  push_cast at this
  exact this

theorem frobT_central_eps :
    (comp (down 𝔻 e) (up 𝔻 g)).actL (GrAlg.dualEquiv k DualNumber.eps) (frobT e g) =
      (comp (down 𝔻 e) (up 𝔻 g)).actR (GrAlg.dualEquiv k DualNumber.eps) (frobT e g) := by
  simp only [frobT, map_add, comp_actL_tmk, comp_actR_tmk, down_actL, up_actR, ← map_mul,
    DualNumber.eps_mul_eps, map_zero, mul_one, tmul_zero, zero_tmul, add_zero, zero_add]

theorem frobT_central (a : 𝔻) :
    (comp (down 𝔻 e) (up 𝔻 g)).actL a (frobT e g) = (comp (down 𝔻 e) (up 𝔻 g)).actR a (frobT e g) := by
  obtain ⟨a, rfl⟩ := (GrAlg.dualEquiv k).surjective a
  have ha : GrAlg.dualEquiv k a = a.fst • 1 + a.snd • GrAlg.dualEquiv k DualNumber.eps := by
    apply (GrAlg.dualEquiv k).symm.injective
    ext <;> simp
  rw [ha]
  simp only [map_add, map_smul, map_one, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply, frobT_central_eps]

theorem frobT_D (h : e + g = -2) : (comp (down 𝔻 e) (up 𝔻 g)).D (frobT e g) = 0 := by
  have h' := cast_add_add_two (k := k) h
  simp only [frobT, map_add, comp_D_tmk, down_D, up_D, GrAlg.deg_one, GrAlg.dual_deg,
    GrAlg.dualDeg_eps, map_smul, map_zero, zero_add, add_tmul, tmul_add, ← smul_tmul', tmul_smul,
    ← Int.cast_smul_eq_zsmul k]
  set a := tmk (down 𝔻 e) (up 𝔻 g) (downEquiv 𝔻 e 1 ⊗ₜ upEquiv 𝔻 g (GrAlg.dualEquiv k DualNumber.eps))
  set b := tmk (down 𝔻 e) (up 𝔻 g) (downEquiv 𝔻 e (GrAlg.dualEquiv k DualNumber.eps) ⊗ₜ upEquiv 𝔻 g 1)
  linear_combination (norm := module) h' • a + h' • b

/-- The unit `a ↦ a (1 ⊗ x + x ⊗ 1)`. -/
def downUpUnit (h : e + g = -2) : id 𝔻 ⟶ comp (down 𝔻 e) (up 𝔻 g) :=
  mkHom (LinearMap.applyₗ (frobT e g) ∘ₗ (comp (down 𝔻 e) (up 𝔻 g)).actL.toLinearMap ∘ₗ
      (idEquiv 𝔻).symm.toLinearMap)
    (fun a x => by
      obtain ⟨x, rfl⟩ := (idEquiv 𝔻).surjective x
      simp)
    (fun a x => by
      obtain ⟨x, rfl⟩ := (idEquiv 𝔻).surjective x
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, id_actR, LinearEquiv.symm_apply_apply,
        AlgHom.toLinearMap_apply, LinearMap.applyₗ_apply_apply]
      rw [mul_comm, map_mul, Module.End.mul_apply, frobT_central, ← Module.End.mul_apply,
        (comp (down 𝔻 e) (up 𝔻 g)).comm, Module.End.mul_apply])
    (fun x => by
      obtain ⟨x, rfl⟩ := (idEquiv 𝔻).surjective x
      simp [D_actL_apply, frobT_D h])

/-- The trace `x ⊗ y ↦ (x y)₁` (the coefficient of `x` in `x y`). -/
def traceₗ (e g : ℤ) : (comp (up 𝔻 g) (down 𝔻 e)).carrier →ₗ[k] (id (GrAlg.unit k)).carrier :=
  cdesc (TensorProduct.lift (LinearMap.mk₂ k (fun x y => idEquiv _ (GrAlg.unitEquiv k
      ((GrAlg.dualEquiv k).symm ((upEquiv 𝔻 g).symm x * (downEquiv 𝔻 e).symm y)).snd))
      (fun _ _ _ => by simp [add_mul, -TrivSqZeroExt.snd_mul, -map_mul])
      (fun _ _ _ => by simp [-TrivSqZeroExt.snd_mul, -map_mul]; rw [← smul_eq_mul, map_smul, map_smul])
      (fun _ _ _ => by simp [mul_add, -TrivSqZeroExt.snd_mul, -map_mul])
      (fun _ _ _ => by simp [-TrivSqZeroExt.snd_mul, -map_mul]; rw [← smul_eq_mul, map_smul, map_smul])))
    (fun b x y => by
      obtain ⟨x, rfl⟩ := (upEquiv 𝔻 g).surjective x
      obtain ⟨y, rfl⟩ := (downEquiv 𝔻 e).surjective y
      simp [mul_assoc, mul_left_comm _ b, -TrivSqZeroExt.snd_mul, -map_mul])

@[simp] theorem traceₗ_tmk (x y : DualNumber k) :
    traceₗ e g (tmk _ _ (upEquiv 𝔻 g (GrAlg.dualEquiv k x) ⊗ₜ downEquiv 𝔻 e (GrAlg.dualEquiv k y))) =
      idEquiv _ (GrAlg.unitEquiv k (x * y).snd) := rfl

/-- The counit, the trace `x ⊗ y ↦ (x y)₁`. -/
def downUpCounit (h : e + g = -2) : comp (up 𝔻 g) (down 𝔻 e) ⟶ id (GrAlg.unit k) :=
  mkHomₗ (traceₗ e g)
    (fun c => comp_ext fun x y => by
      obtain ⟨x, rfl⟩ := ((GrAlg.dualEquiv k).toLinearEquiv.trans (upEquiv 𝔻 g)).surjective x
      obtain ⟨y, rfl⟩ := ((GrAlg.dualEquiv k).toLinearEquiv.trans (downEquiv 𝔻 e)).surjective y
      obtain ⟨c, rfl⟩ := (GrAlg.unitEquiv k).surjective c
      simp only [LinearEquiv.trans_apply, AlgEquiv.toLinearEquiv_apply, LinearMap.comp_apply,
        comp_actL_tmk, up_actL, ← map_smul, traceₗ_tmk, id_actL, ← map_mul]
      simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_smul, TrivSqZeroExt.fst_smul, smul_eq_mul,
        op_smul_eq_mul]
      ring_nf)
    (fun c => comp_ext fun x y => by
      obtain ⟨x, rfl⟩ := ((GrAlg.dualEquiv k).toLinearEquiv.trans (upEquiv 𝔻 g)).surjective x
      obtain ⟨y, rfl⟩ := ((GrAlg.dualEquiv k).toLinearEquiv.trans (downEquiv 𝔻 e)).surjective y
      obtain ⟨c, rfl⟩ := (GrAlg.unitEquiv k).surjective c
      simp only [LinearEquiv.trans_apply, AlgEquiv.toLinearEquiv_apply, LinearMap.comp_apply,
        comp_actR_tmk, down_actR, ← map_smul, traceₗ_tmk, id_actR, ← map_mul]
      simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_smul, TrivSqZeroExt.fst_smul, smul_eq_mul,
        op_smul_eq_mul]
      ring_nf)
    (comp_ext fun x y => by
      obtain ⟨x, rfl⟩ := ((GrAlg.dualEquiv k).toLinearEquiv.trans (upEquiv 𝔻 g)).surjective x
      obtain ⟨y, rfl⟩ := ((GrAlg.dualEquiv k).toLinearEquiv.trans (downEquiv 𝔻 e)).surjective y
      have h' := cast_add_add_two (k := k) h
      simp only [LinearEquiv.trans_apply, AlgEquiv.toLinearEquiv_apply, LinearMap.comp_apply,
        comp_D_tmk, up_D, down_D, GrAlg.dual_deg, ← Int.cast_smul_eq_zsmul k, map_add, tmul_add,
        add_tmul, ← smul_tmul', tmul_smul, map_smul, traceₗ_tmk, unit_id_D]
      simp only [← map_smul, ← map_add]
      rw [LinearEquiv.map_eq_zero_iff, map_eq_zero_iff _ (GrAlg.unitEquiv k).injective]
      simp only [TrivSqZeroExt.snd_mul, GrAlg.dualDeg_fst, GrAlg.dualDeg_snd, smul_eq_mul,
        op_smul_eq_mul]
      linear_combination (x.fst * y.snd + x.snd * y.fst) * h')

theorem tmk_unit_up (s : k) (y : 𝔻) :
    tmk (id (GrAlg.unit k)) (up 𝔻 g) (idEquiv _ (GrAlg.unitEquiv k s) ⊗ₜ upEquiv 𝔻 g y) =
      tmk (id (GrAlg.unit k)) (up 𝔻 g) (idEquiv _ 1 ⊗ₜ upEquiv 𝔻 g (s • y)) := by
  rw [← up_actL, tmk_one_actL]

theorem tmk_down_unit (y : 𝔻) (s : k) :
    tmk (down 𝔻 e) (id (GrAlg.unit k)) (downEquiv 𝔻 e y ⊗ₜ idEquiv _ (GrAlg.unitEquiv k s)) =
      tmk (down 𝔻 e) (id (GrAlg.unit k)) (downEquiv 𝔻 e (s • y) ⊗ₜ idEquiv _ 1) := by
  rw [← down_actR, tmk_actR_one]

/-- **`down (dual k) e ⊣ up (dual k) g`** for `e + g = -2`: `H*(P¹)` is a Frobenius algebra over
`k` with trace the coefficient of `x`. -/
def downUpAdj (h : e + g = -2) :
    Bicategory.Adjunction (B := GrAlg k) (down 𝔻 e) (up 𝔻 g) where
  unit := downUpUnit h
  counit := downUpCounit h
  left_triangle := by
    apply hom_ext
    refine comp_ext_idL fun a x => ?_
    obtain ⟨x, rfl⟩ := ((GrAlg.dualEquiv k).toLinearEquiv.trans (downEquiv 𝔻 e)).surjective x
    obtain ⟨a, rfl⟩ := (GrAlg.dualEquiv k).surjective a
    simp only [leftZigzag, bicategoricalComp, downUpUnit, downUpCounit, bicategory_comp₂_val,
      LinearMap.comp_apply, GrAlg.bicategory_whiskerRight, GrAlg.bicategory_whiskerLeft,
      GrAlg.bicategory_associator, BicategoricalCoherence.assoc_iso]
    dsimp only [bicategory_id₁, bicategory_comp₁]
    simp [frobT]
    simp only [← map_mul, assocHomₗ_tmk, map_add, add_tmul, cmap_tmk, LinearMap.id_apply,
      traceₗ_tmk, tmk_down_unit]
    rw [show upEquiv 𝔻 g (1 : (GrAlg.dual k).carrier) = upEquiv 𝔻 g (GrAlg.dualEquiv k 1) by
      rw [map_one (GrAlg.dualEquiv k)], traceₗ_tmk, tmk_down_unit, ← map_add, ← add_tmul, ← map_add]
    congr 3
    apply (GrAlg.dualEquiv k).symm.injective
    simp only [map_add, map_smul, AlgEquiv.symm_apply_apply]
    ext <;> simp <;> ring
  right_triangle := by
    apply hom_ext
    refine comp_ext_idR fun x c => ?_
    obtain ⟨x, rfl⟩ := ((GrAlg.dualEquiv k).toLinearEquiv.trans (upEquiv 𝔻 g)).surjective x
    obtain ⟨c, rfl⟩ := (GrAlg.dualEquiv k).surjective c
    simp only [rightZigzag, bicategoricalComp, downUpUnit, downUpCounit, bicategory_comp₂_val,
      LinearMap.comp_apply, GrAlg.bicategory_whiskerRight, GrAlg.bicategory_whiskerLeft]
    dsimp only [bicategory_id₁, bicategory_comp₁]
    simp [frobT]
    simp only [← map_mul, assocInvₗ_tmk, map_add, tmul_add, cmap_tmk, LinearMap.id_apply,
      traceₗ_tmk, tmk_unit_up]
    rw [← map_add, ← tmul_add, ← map_add]
    congr 3
    apply (GrAlg.dualEquiv k).symm.injective
    simp only [map_add, map_smul, map_one, AlgEquiv.symm_apply_apply]
    ext <;> simp <;> ring

end downUpAdj

end GBim

end Categorification.TwoRep.Grassmannian

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensorHomology

/-!
# Degree-zero cohomology of derived tensor on right modules

The ordinary balanced tensor in right-module order is the swapped opposite-ring
tensor used by the DG functor. This gives the degree-zero comparison in
Webster, arXiv:1309.3796v2, Lemma 6.8, proof of (6.21).
-/

open CategoryTheory DG DG.DerivedCategory MulOpposite
open scoped DG.DegreeZero

noncomputable section

namespace Categorification

variable {k B M N : Type*} [CommRing k] [Ring B] [Algebra k B]
  [AddCommGroup M] [Module k M] [Module B M] [IsScalarTower k B M] [SMulCommClass B k M]
  [AddCommGroup N] [Module k N] [Module Bᵐᵒᵖ N] [SMulCommClass k Bᵐᵒᵖ N]

private def flipTo : TensorProductOver Bᵐᵒᵖ (OpBimodule B M) N →+ BalancedTensor k k B N M :=
  TensorProductOver.lift
    { toFun := fun m => ((BalancedTensor.mkBil k k B N M).flip m).toAddMonoidHom
      map_zero' := by
        ext n
        exact map_zero (BalancedTensor.mkBil k k B N M n)
      map_add' := by
        intro m m'
        ext n
        exact map_add (BalancedTensor.mkBil k k B N M n) m m'  }
    (by
      intro b m n
      change BalancedTensor.tmul n (b.unop • (m : M)) = BalancedTensor.tmul (b • n) (m : M)
      exact (BalancedTensor.op_smul_tmul n b.unop (m : M)).symm)

private def flipFrom (hN : ∀ (c : k) (n : N), op (algebraMap k B c) • n = c • n) :
    BalancedTensor k k B N M →+ TensorProductOver Bᵐᵒᵖ (OpBimodule B M) N :=
  let f : N →ₗ[k] M →ₗ[k] TensorProductOver Bᵐᵒᵖ (OpBimodule B M) N :=
    { toFun := fun n =>
      { toFun := fun m => TensorProductOver.tmul (M := OpBimodule B M) Bᵐᵒᵖ (m : OpBimodule B M) n
        map_add' := fun m m' => TensorProductOver.add_tmul (M := OpBimodule B M) m m' n
        map_smul' := fun c m => by
          change TensorProductOver.tmul (M := OpBimodule B M) Bᵐᵒᵖ (c • (m : OpBimodule B M)) n = _
          exact (TensorProductOver.smul_tmul (M := OpBimodule B M) c m n).symm }
      map_add' := by intro n n'; ext m; exact TensorProductOver.tmul_add (M := OpBimodule B M) m n n'
      map_smul' := fun c n => by
        ext m
        change TensorProductOver.tmul (M := OpBimodule B M) Bᵐᵒᵖ (m : OpBimodule B M) (c • n) =
          c • TensorProductOver.tmul (M := OpBimodule B M) Bᵐᵒᵖ (m : OpBimodule B M) n
        rw [← hN c n, ← TensorProductOver.op_smul_tmul (M := OpBimodule B M) (op (algebraMap k B c)) m n]
        change TensorProductOver.tmul (M := OpBimodule B M) Bᵐᵒᵖ ((algebraMap k B c) • m : M) n = _
        have hc : (algebraMap k B c) • m = c • m := IsScalarTower.algebraMap_smul B c m
        exact (congrArg (fun y : M => TensorProductOver.tmul (M := OpBimodule B M) Bᵐᵒᵖ
          (y : OpBimodule B M) n) hc).trans (TensorProductOver.smul_tmul (M := OpBimodule B M) c m n).symm }
  (BalancedTensor.lift f (by
      intro n b m
      change TensorProductOver.tmul (M := OpBimodule B M) Bᵐᵒᵖ (m : OpBimodule B M) (op b • n) =
        TensorProductOver.tmul (M := OpBimodule B M) Bᵐᵒᵖ ((b • m : M) : OpBimodule B M) n
      exact (TensorProductOver.op_smul_tmul (M := OpBimodule B M) (op b) (m : OpBimodule B M) n).symm)).toAddMonoidHom

/-- The ordinary right tensor identifies with the opposite-ring tensor
by exchanging the two entries of every pure tensor. -/
def rightTensorFlipAddEquiv (hN : ∀ (c : k) (n : N), op (algebraMap k B c) • n = c • n) :
    TensorProductOver Bᵐᵒᵖ (OpBimodule B M) N ≃+ BalancedTensor k k B N M where
  __ := flipTo
  invFun := flipFrom hN
  left_inv := by
    intro x
    change flipFrom hN (flipTo x) = x
    induction x using TensorProductOver.induction_on with
    | zero => simp
    | tmul m n => rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  right_inv := by
    intro x
    change flipTo (flipFrom hN x) = x
    induction x using BalancedTensor.induction_on with
    | zero => simp
    | tmul n m => rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]

@[simp] theorem rightTensorFlipAddEquiv_tmul (hN : ∀ (c : k) (n : N),
    op (algebraMap k B c) • n = c • n) (m : OpBimodule B M) (n : N) :
    rightTensorFlipAddEquiv hN (TensorProductOver.tmul (M := OpBimodule B M) Bᵐᵒᵖ m n) = BalancedTensor.tmul n (m : M) :=
  rfl


section Derived

universe w u v

variable {k : Type v} {C C' X N P : Type u} [CommRing k] [Ring C] [Algebra k C] [Ring C']
  [HasDerivedCategory.{w, u} Cᵐᵒᵖ] [HasDerivedCategory.{w, u} C'ᵐᵒᵖ]
  [AddCommGroup X] [Module k X] [Module C X] [IsScalarTower k C X] [SMulCommClass C k X]
  [Module C'ᵐᵒᵖ X] [SMulCommClass C C'ᵐᵒᵖ X]
  [AddCommGroup N] [Module k N] [Module Cᵐᵒᵖ N] [SMulCommClass k Cᵐᵒᵖ N]
  [AddCommGroup P] [Module k P] [Module Cᵐᵒᵖ P] [SMulCommClass k Cᵐᵒᵖ P]

set_option backward.isDefEq.respectTransparency false in
/-- Injectivity of ordinary right tensoring implies the degree-zero derived monomorphism. -/
theorem mono_derivedRightTensorHomology_of_balanced
    (hN : ∀ (c : k) (n : N), op (algebraMap k C c) • n = c • n)
    (hP : ∀ (c : k) (p : P), op (algebraMap k C c) • p = c • p)
    (f : DGModuleCat.of Cᵐᵒᵖ (InDegreeZero N) ⟶ DGModuleCat.of Cᵐᵒᵖ (InDegreeZero P))
    (μ : BalancedTensor k k C N X →+ BalancedTensor k k C P X)
    (hμ : ∀ (n : N) (x : X), μ (BalancedTensor.tmul n x) = BalancedTensor.tmul (f n) x)
    (hinj : Function.Injective μ) :
    Mono ((DG.DerivedCategory.homologyFunctor ℤ 0).map ((derivedRightTensor C C' X).map (Q.map f))) := by
  let eN := rightTensorFlipAddEquiv (M := X) hN
  let eP := rightTensorFlipAddEquiv (M := X) hP
  let τ : TensorProductOver Cᵐᵒᵖ (InDegreeZero (OpBimodule C X)) (InDegreeZero N) →+
      TensorProductOver Cᵐᵒᵖ (InDegreeZero (OpBimodule C X)) (InDegreeZero P) :=
    eP.symm.toAddMonoidHom.comp (μ.comp eN.toAddMonoidHom)
  let H := DG.DerivedCategory.homologyFunctor (A := C'ᵐᵒᵖ) ℤ 0
  let g := H.map ((derivedRightTensor C C' X).map (Q.map f))
  let eX := derivedTensorHomologyIsoOrdinary (A := C'ᵐᵒᵖ) (B := Cᵐᵒᵖ) (M := OpBimodule C X) N
  let eY := derivedTensorHomologyIsoOrdinary (A := C'ᵐᵒᵖ) (B := Cᵐᵒᵖ) (M := OpBimodule C X) P
  have hτ : ∀ (x : InDegreeZero (OpBimodule C X)) (n : InDegreeZero N),
      τ (TensorProductOver.tmul Cᵐᵒᵖ x n) = TensorProductOver.tmul Cᵐᵒᵖ x (f n) := by
    intro x n
    change eP.symm (μ (eN (TensorProductOver.tmul Cᵐᵒᵖ x n))) =
      TensorProductOver.tmul Cᵐᵒᵖ x (f n)
    apply eP.injective
    rw [AddEquiv.apply_symm_apply]
    exact hμ n x
  have := mono_tensorHomologyQ_of_balanced (A := C'ᵐᵒᵖ) (B := Cᵐᵒᵖ)
    (M := OpBimodule C X) (N := N) (P := P) f τ hτ
    (eP.symm.injective.comp (hinj.comp eN.injective))
  have : Mono (g ≫ eY.hom) := by
    rw [show g ≫ eY.hom = eX.hom ≫ H.map
      (Q.map ((DGModuleCat.tensorFunctor C'ᵐᵒᵖ (InDegreeZero (OpBimodule C X))).map f)) from
        derivedTensorHomologyIsoOrdinary_naturality (A := C'ᵐᵒᵖ) (B := Cᵐᵒᵖ)
          (M := OpBimodule C X) (X := N) (Y := P) f]
    infer_instance
  exact mono_of_mono g eY.hom

end Derived

end Categorification

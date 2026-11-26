/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedRightTensorHomology

/-!
# Injectivity of the ordinary tensor from the derived tensor in degree zero

The converse of `mono_derivedRightTensorHomology_of_balanced`: when the derived right tensor of
a module map is injective in degree zero, so is the ordinary balanced tensor of that map. With
the dimension shift of `DerivedKernelShift`, this turns vanishing of the derived braid of a
module outside degree zero into exactness of the ordinary braid on its resolutions (Webster,
arXiv:1309.3796v2, §6.1, proof of Corollary 6.10).

## Main results

* `Categorification.injective_of_mono_tensorHomologyQ`
* `Categorification.injective_of_mono_derivedRightTensorHomology`
* `Categorification.injective_of_mono_derivedTensorHomology`
* `Categorification.epi_derivedRightTensorHomology_of_surjective`
-/

open CategoryTheory DG DG.DerivedCategory MulOpposite
open scoped DG.DegreeZero

noncomputable section

namespace Categorification

section LocalizedTensorHomology

universe w u

variable {A : Type u} [Ring A] [HasDerivedCategory.{w, u} A]

variable {B M N P : Type u} [Ring B]
  [AddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]
  [AddCommGroup N] [Module B N] [AddCommGroup P] [Module B P]

set_option backward.isDefEq.respectTransparency false in
/-- A balanced map with the pure-tensor formula of a module map is injective when the degree-zero
cohomology of the localized tensor map is a monomorphism. -/
theorem injective_of_mono_tensorHomologyQ
    (f : DGModuleCat.of B (InDegreeZero N) ⟶ DGModuleCat.of B (InDegreeZero P))
    (μ : TensorProductOver B (InDegreeZero M) (InDegreeZero N) →+
      TensorProductOver B (InDegreeZero M) (InDegreeZero P))
    (hμ : ∀ (m : InDegreeZero M) (n : InDegreeZero N),
      μ (TensorProductOver.tmul B m n) = TensorProductOver.tmul B m (f n))
    (hmono : Mono ((DG.DerivedCategory.homologyFunctor ℤ 0).map
      (Q.map ((DGModuleCat.tensorFunctor A (InDegreeZero M)).map f)))) :
    Function.Injective μ := by
  let eX := tensorHomologyQEquiv (A := A) (B := B) (M := M) (N := N)
  let eY := tensorHomologyQEquiv (A := A) (B := B) (M := M) (N := P)
  let H := (DG.DerivedCategory.homologyFunctor ℤ 0).map
    (Q.map ((DGModuleCat.tensorFunctor A (InDegreeZero M)).map f))
  have h : (H.hom.toAddMonoidHom.comp eX.toAddMonoidHom) = eY.toAddMonoidHom.comp μ := by
    apply TensorProductOver.addHom_ext
    intro m n
    change H (eX (TensorProductOver.tmul B m n)) = eY (μ (TensorProductOver.tmul B m n))
    rw [hμ]
    exact tensorHomologyQEquiv_tmul_naturality (A := A) f m n
  have comm (z : TensorProductOver B (InDegreeZero M) (InDegreeZero N)) :
      H (eX z) = eY (μ z) := DFunLike.congr_fun h z
  have hH : Function.Injective H := (ModuleCat.mono_iff_injective H).mp hmono
  intro x y hxy
  apply eX.injective
  apply hH
  rw [comm, comm, hxy]

set_option backward.isDefEq.respectTransparency false in
/-- A surjective balanced map with the pure-tensor formula of a module map makes the degree-zero
cohomology of the localized tensor map an epimorphism. -/
theorem epi_tensorHomologyQ_of_surjective
    (f : DGModuleCat.of B (InDegreeZero N) ⟶ DGModuleCat.of B (InDegreeZero P))
    (μ : TensorProductOver B (InDegreeZero M) (InDegreeZero N) →+
      TensorProductOver B (InDegreeZero M) (InDegreeZero P))
    (hμ : ∀ (m : InDegreeZero M) (n : InDegreeZero N),
      μ (TensorProductOver.tmul B m n) = TensorProductOver.tmul B m (f n))
    (hsurj : Function.Surjective μ) :
    Epi ((DG.DerivedCategory.homologyFunctor ℤ 0).map
      (Q.map ((DGModuleCat.tensorFunctor A (InDegreeZero M)).map f))) := by
  let eX := tensorHomologyQEquiv (A := A) (B := B) (M := M) (N := N)
  let eY := tensorHomologyQEquiv (A := A) (B := B) (M := M) (N := P)
  let H := (DG.DerivedCategory.homologyFunctor ℤ 0).map
    (Q.map ((DGModuleCat.tensorFunctor A (InDegreeZero M)).map f))
  have h : (H.hom.toAddMonoidHom.comp eX.toAddMonoidHom) = eY.toAddMonoidHom.comp μ := by
    apply TensorProductOver.addHom_ext
    intro m n
    change H (eX (TensorProductOver.tmul B m n)) = eY (μ (TensorProductOver.tmul B m n))
    rw [hμ]
    exact tensorHomologyQEquiv_tmul_naturality (A := A) f m n
  have comm (z : TensorProductOver B (InDegreeZero M) (InDegreeZero N)) :
      H (eX z) = eY (μ z) := DFunLike.congr_fun h z
  apply (ModuleCat.epi_iff_surjective H).mpr
  intro y
  obtain ⟨y, rfl⟩ := eY.surjective y
  obtain ⟨x, rfl⟩ := hsurj y
  exact ⟨eX x, comm x⟩

end LocalizedTensorHomology

section Derived

universe w u v

variable {k : Type v} {C C' X N P : Type u} [CommRing k] [Ring C] [Algebra k C] [Ring C']
  [HasDerivedCategory.{w, u} Cᵐᵒᵖ] [HasDerivedCategory.{w, u} C'ᵐᵒᵖ]
  [AddCommGroup X] [Module k X] [Module C X] [IsScalarTower k C X] [SMulCommClass C k X]
  [Module C'ᵐᵒᵖ X] [SMulCommClass C C'ᵐᵒᵖ X]
  [AddCommGroup N] [Module k N] [Module Cᵐᵒᵖ N] [SMulCommClass k Cᵐᵒᵖ N]
  [AddCommGroup P] [Module k P] [Module Cᵐᵒᵖ P] [SMulCommClass k Cᵐᵒᵖ P]

set_option backward.isDefEq.respectTransparency false in
/-- If the derived right tensor of a module map is injective in degree zero, then so is the
ordinary balanced tensor of the map. -/
theorem injective_of_mono_derivedRightTensorHomology
    (hN : ∀ (c : k) (n : N), op (algebraMap k C c) • n = c • n)
    (hP : ∀ (c : k) (p : P), op (algebraMap k C c) • p = c • p)
    (f : DGModuleCat.of Cᵐᵒᵖ (InDegreeZero N) ⟶ DGModuleCat.of Cᵐᵒᵖ (InDegreeZero P))
    (μ : BalancedTensor k k C N X →+ BalancedTensor k k C P X)
    (hμ : ∀ (n : N) (x : X), μ (BalancedTensor.tmul n x) = BalancedTensor.tmul (f n) x)
    (hmono : Mono ((DG.DerivedCategory.homologyFunctor ℤ 0).map
      ((derivedRightTensor C C' X).map (Q.map f)))) :
    Function.Injective μ := by
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
  have hsq : g ≫ eY.hom = eX.hom ≫ H.map
      (Q.map ((DGModuleCat.tensorFunctor C'ᵐᵒᵖ (InDegreeZero (OpBimodule C X))).map f)) :=
    derivedTensorHomologyIsoOrdinary_naturality (A := C'ᵐᵒᵖ) (B := Cᵐᵒᵖ)
      (M := OpBimodule C X) (X := N) (Y := P) f
  have : Mono (eX.hom ≫ H.map
      (Q.map ((DGModuleCat.tensorFunctor C'ᵐᵒᵖ (InDegreeZero (OpBimodule C X))).map f))) := by
    rw [← hsq]
    infer_instance
  have hm : Mono (H.map
      (Q.map ((DGModuleCat.tensorFunctor C'ᵐᵒᵖ (InDegreeZero (OpBimodule C X))).map f))) := by
    have h' := mono_comp (inv eX.hom) (eX.hom ≫ H.map
      (Q.map ((DGModuleCat.tensorFunctor C'ᵐᵒᵖ (InDegreeZero (OpBimodule C X))).map f)))
    rwa [IsIso.inv_hom_id_assoc] at h'
  have hτi := injective_of_mono_tensorHomologyQ (A := C'ᵐᵒᵖ) (B := Cᵐᵒᵖ)
    (M := OpBimodule C X) (N := N) (P := P) f τ hτ hm
  intro x y hxy
  apply eN.symm.injective
  apply hτi
  change eP.symm (μ (eN (eN.symm x))) = eP.symm (μ (eN (eN.symm y)))
  rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, hxy]

set_option backward.isDefEq.respectTransparency false in
/-- If the ordinary balanced tensor of a module map is surjective, its derived right tensor is
an epimorphism in degree zero. -/
theorem epi_derivedRightTensorHomology_of_surjective
    (hN : ∀ (c : k) (n : N), op (algebraMap k C c) • n = c • n)
    (hP : ∀ (c : k) (p : P), op (algebraMap k C c) • p = c • p)
    (f : DGModuleCat.of Cᵐᵒᵖ (InDegreeZero N) ⟶ DGModuleCat.of Cᵐᵒᵖ (InDegreeZero P))
    (μ : BalancedTensor k k C N X →+ BalancedTensor k k C P X)
    (hμ : ∀ (n : N) (x : X), μ (BalancedTensor.tmul n x) = BalancedTensor.tmul (f n) x)
    (hsurj : Function.Surjective μ) :
    Epi ((DG.DerivedCategory.homologyFunctor ℤ 0).map
      ((derivedRightTensor C C' X).map (Q.map f))) := by
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
  have hτs : Function.Surjective τ :=
    eP.symm.surjective.comp (hsurj.comp eN.surjective)
  have he := epi_tensorHomologyQ_of_surjective (A := C'ᵐᵒᵖ) (B := Cᵐᵒᵖ)
    (M := OpBimodule C X) (N := N) (P := P) f τ hτ hτs
  have hsq : g ≫ eY.hom = eX.hom ≫ H.map
      (Q.map ((DGModuleCat.tensorFunctor C'ᵐᵒᵖ (InDegreeZero (OpBimodule C X))).map f)) :=
    derivedTensorHomologyIsoOrdinary_naturality (A := C'ᵐᵒᵖ) (B := Cᵐᵒᵖ)
      (M := OpBimodule C X) (X := N) (Y := P) f
  have h₁ : Epi (g ≫ eY.hom) := by rw [hsq]; infer_instance
  have h₂ := epi_comp (g ≫ eY.hom) (inv eY.hom)
  rwa [Category.assoc, IsIso.hom_inv_id, Category.comp_id] at h₂

end Derived

section BalancedHomologyMap

universe w u

variable {k A B M N P : Type u} [CommRing k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  [HasDerivedCategory.{w, u} A] [HasDerivedCategory.{w, u} B]
  [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M] [Module Bᵐᵒᵖ M]
  [SMulCommClass A Bᵐᵒᵖ M] [AddCommGroup N] [Module k N] [Module B N] [IsScalarTower k B N]
  [AddCommGroup P] [Module k P] [Module B P] [IsScalarTower k B P]

set_option backward.isDefEq.respectTransparency false in
/-- If the derived tensor of a module map is injective in degree zero, then so is the ordinary
balanced tensor of the map. The converse of `mono_derivedTensorHomology_of_ordinaryBalanced`. -/
theorem injective_of_mono_derivedTensorHomology
    (hM : ∀ (c : k) (m : M), op (algebraMap k B c) • m = c • m)
    (f : DGModuleCat.of B (InDegreeZero N) ⟶ DGModuleCat.of B (InDegreeZero P))
    (μ : BalancedTensor k A B M N →+ BalancedTensor k A B M P)
    (hμ : ∀ (m : M) (n : N), μ (BalancedTensor.tmul m n) = BalancedTensor.tmul m (f n))
    (hmono : Mono ((DG.DerivedCategory.homologyFunctor ℤ 0).map
      ((derivedTensor A B M).map (Q.map f)))) :
    Function.Injective μ := by
  let H := DG.DerivedCategory.homologyFunctor (A := A) ℤ 0
  let eX := derivedTensorHomologyIsoOrdinary (A := A) (B := B) (M := M) N
  let eY := derivedTensorHomologyIsoOrdinary (A := A) (B := B) (M := M) P
  have hsq : H.map ((derivedTensor A B M).map (Q.map f)) ≫ eY.hom = eX.hom ≫ H.map
      (Q.map ((DGModuleCat.tensorFunctor A (InDegreeZero M)).map f)) :=
    derivedTensorHomologyIsoOrdinary_naturality f
  have h₁ : Mono (eX.hom ≫ H.map
      (Q.map ((DGModuleCat.tensorFunctor A (InDegreeZero M)).map f))) := by
    rw [← hsq]
    infer_instance
  have hm : Mono (H.map (Q.map ((DGModuleCat.tensorFunctor A (InDegreeZero M)).map f))) := by
    have h' := mono_comp (inv eX.hom) (eX.hom ≫ H.map
      (Q.map ((DGModuleCat.tensorFunctor A (InDegreeZero M)).map f)))
    rwa [IsIso.inv_hom_id_assoc] at h'
  let cN := ordinaryBalancedTensorAddEquiv (A := A) (N := N) hM
  let cP := ordinaryBalancedTensorAddEquiv (A := A) (N := P) hM
  let τ : TensorProductOver B (InDegreeZero M) (InDegreeZero N) →+
      TensorProductOver B (InDegreeZero M) (InDegreeZero P) :=
    cP.symm.toAddMonoidHom.comp (μ.comp cN.toAddMonoidHom)
  have hτ : ∀ (m : InDegreeZero M) (n : InDegreeZero N),
      τ (TensorProductOver.tmul B m n) = TensorProductOver.tmul B m (f n) := by
    intro m n
    change cP.symm (μ (cN (TensorProductOver.tmul B m n))) = TensorProductOver.tmul B m (f n)
    apply cP.injective
    rw [AddEquiv.apply_symm_apply]
    exact hμ _ _
  have hτi := injective_of_mono_tensorHomologyQ (A := A) (B := B) (M := M) (N := N) (P := P)
    f τ hτ hm
  intro x y hxy
  apply cN.symm.injective
  apply hτi
  change cP.symm (μ (cN (cN.symm x))) = cP.symm (μ (cN (cN.symm y)))
  rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, hxy]

end BalancedHomologyMap

end Categorification

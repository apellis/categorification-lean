/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensorCompComparison
import Categorification.Algebra.ExactDerivedTensor
import Categorification.Algebra.DerivedTensorDegreeZero
import Categorification.Algebra.DerivedTensorFiltration
import Categorification.Algebra.DerivedTensorProjective

/-!
# Derived tensor products with induced modules killed by the coefficient

Let `A`, `B`, `C` be rings, `M` an `(A, B)`-bimodule and `N` a `(B, C)`-bimodule which is
projective as a right `C`-module. If `Tor^B_{>0}(M, N) = 0` and `M ⊗_B N = 0`, then
`M ⊗ᴸ_B (N ⊗_C X) = 0` for every dg `C`-module `X`
(`isZero_derivedTensor_obj_tensor_of_torVanishing`): the derived tensor products compose
(`derivedTensorCompIsoOfTorVanishing`) and the composite has zero coefficient.

The typical case is `N = B e` for an idempotent `e` killing `M` (`M e = 0`), with `B e` a right
module over an algebra acting on the right of `B e`, for example a corner of `B`. Then every module
`N ⊗_C W` induced from a `C`-module `W` is `Tor`-orthogonal to `M`
(`isZero_derivedTensorHomology_induced_of_idempotent`), and so is every module with a finite
filtration by such induced modules (`isZero_derivedTensorHomology_of_hasFiltration_induced`).

This is the vanishing on the layers of the left-module form of the trace half of B. Webster,
*Knot invariants and higher representation theory*, arXiv:1309.3796v3, Lemma 7.19: there `M`
is a module over the window algebra which is killed by the idempotents of the two end loadings.
-/

open CategoryTheory CategoryTheory.Limits DG DG.DerivedCategory MulOpposite
open scoped DG.DegreeZero

noncomputable section

namespace Categorification

universe w u

section Subsingleton

variable {A C : Type u} [Ring A] [Ring C] [HasDerivedCategory.{w, u} A]
  [HasDerivedCategory.{w, u} C]

/-- The derived tensor product with a zero dg bimodule is zero. -/
theorem isZero_dgDerivedTensor_obj_of_subsingleton {Z : Type u} [AddCommGroup Z]
    [DGAddCommGroup Z] [Module A Z] [Module Cᵐᵒᵖ Z] [DGBimodule A C Z] [Subsingleton Z]
    (X : DerivedCategory.{w, u} C) : IsZero ((dgDerivedTensor.{w} A C Z).obj X) := by
  obtain ⟨P, hP⟩ := DG.HomotopyCategory.quotient_obj_surjective
    ((DG.HomotopyCategory.subcategoryKProjective C).ι.obj
      ((kProjectiveEquivalence.{w} C).inverse.obj X))
  have hT : Subsingleton (TensorProductOver C Z P) := by
    have h0 : ∀ z : TensorProductOver C Z P, z = 0 := fun z => by
      induction z using TensorProductOver.induction_on with
      | zero => rfl
      | tmul m p =>
        rw [show m = 0 from Subsingleton.elim m 0]
        exact TensorProductOver.zero_tmul p
      | add x y hx hy => rw [hx, hy, add_zero]
    exact ⟨fun x y => (h0 x).trans (h0 y).symm⟩
  have h0 : IsZero ((DGModuleCat.tensorFunctor A Z).obj P) :=
    @DGModuleCat.isZero_of_subsingleton _ _ _ _ hT
  change IsZero (Qh.obj ((DG.HomotopyCategory.tensorFunctor A Z).obj
    ((DG.HomotopyCategory.subcategoryKProjective C).ι.obj
      ((kProjectiveEquivalence.{w} C).inverse.obj X))))
  rw [← hP]
  exact (Qh.map_isZero ((DG.HomotopyCategory.quotient A).map_isZero h0)).of_iso
    (Qh.mapIso ((DG.HomotopyCategory.tensorFunctorQuotientIso A Z).app P))

end Subsingleton

section TorVanishing

open TensorProductOver.RightAction

variable {A B C : Type u} [Ring A] [Ring B] [Ring C] (M N : Type u) [AddCommGroup M]
  [Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M] [AddCommGroup N] [Module B N]
  [Module Cᵐᵒᵖ N] [SMulCommClass B Cᵐᵒᵖ N] [Module.Projective Cᵐᵒᵖ N]
  [HasDerivedCategory.{u, u} A] [HasDerivedCategory.{u, u} B] [HasDerivedCategory.{u, u} C]

/-- **Induced modules killed by the coefficient**: for `N` projective as a right `C`-module,
`Tor^B_{>0}(M, N) = 0` and `M ⊗_B N = 0` give `M ⊗ᴸ_B (N ⊗_C X) = 0` for every dg
`C`-module `X`. -/
theorem isZero_derivedTensor_obj_tensor_of_torVanishing
    (hv : ∀ n : ℤ, n ≠ 0 → IsZero ((homologyFunctor (A := A) ℤ n).obj
      ((derivedTensor.{u} A B M).obj (Q.obj (DGModuleCat.of B (InDegreeZero N))))))
    (hz : Subsingleton (TensorProductOver B (InDegreeZero M) (InDegreeZero N)))
    (X : DGModuleCat.{u} C) :
    IsZero ((derivedTensor.{u} A B M).obj
      (Q.obj ((DGModuleCat.tensorFunctor B (InDegreeZero N)).obj X))) :=
  (isZero_dgDerivedTensor_obj_of_subsingleton (A := A) (C := C) (Q.obj X)).of_iso
    ((derivedTensor.{u} A B M).mapIso ((QCompDerivedTensorIso.{u} B C N).app X).symm ≪≫
      (derivedTensorCompIsoOfTorVanishing A B C M N hv).app (Q.obj X))

/-- The ordinary-module form of `isZero_derivedTensor_obj_tensor_of_torVanishing`: a module
`Y` isomorphic to `N ⊗_C W` for a `C`-module `W` has `M ⊗ᴸ_B Y = 0`. -/
theorem isZero_derivedTensor_induced_of_torVanishing
    (hv : ∀ n : ℤ, n ≠ 0 → IsZero ((homologyFunctor (A := A) ℤ n).obj
      ((derivedTensor.{u} A B M).obj (Q.obj (DGModuleCat.of B (InDegreeZero N))))))
    (hz : Subsingleton (TensorProductOver B (InDegreeZero M) (InDegreeZero N)))
    (Y : ModuleCat.{u} B) (W : Type u) [AddCommGroup W] [Module C W]
    (e : Y ≃ₗ[B] TensorProductOver C (InDegreeZero N) (InDegreeZero W)) :
    IsZero ((derivedTensor.{u} A B M).obj (Q.obj ((degreeZeroModuleFunctor B).obj Y))) := by
  let e' : InDegreeZero (Y : Type u) ≃ᵈᵍ[B]
      TensorProductOver C (InDegreeZero N) (InDegreeZero W) :=
    DGModuleEquiv.ofDegreeZero e
      (fun {n x} hx hn => ((InDegreeZero.mem_grading_iff (m := x)).mp hx).resolve_left hn)
      (fun x => InDegreeZero.d_apply (m := x)) TensorProductOver.mem_grading_zero_inDegreeZero
      TensorProductOver.d_inDegreeZero
  exact (isZero_derivedTensor_obj_tensor_of_torVanishing M N hv hz
    (DGModuleCat.of C (InDegreeZero W))).of_iso
      ((derivedTensor.{u} A B M).mapIso (Q.mapIso e'.toDGModuleCatIso))

end TorVanishing

section Idempotent

variable {B : Type u} [Ring B]

/-- A right module killed by an idempotent `e`, tensored with a left module generated by an
element `g = e g`, is zero. -/
theorem subsingleton_tensorProductOver_of_generator {M N : Type u} [AddCommGroup M]
    [Module Bᵐᵒᵖ M] [AddCommGroup N] [Module B N] {e : B} {g : N} (hg : e • g = g)
    (hN : ∀ x : N, ∃ b : B, x = b • g) (hM : ∀ m : M, op e • m = 0) :
    Subsingleton (TensorProductOver B (InDegreeZero M) (InDegreeZero N)) := by
  have h0 : ∀ z : TensorProductOver B (InDegreeZero M) (InDegreeZero N), z = 0 := fun z => by
    induction z using TensorProductOver.induction_on with
    | zero => rfl
    | tmul m x =>
      obtain ⟨b, rfl⟩ := hN x
      change TensorProductOver.tmul B m (b • g) = 0
      rw [← TensorProductOver.op_smul_tmul, ← hg, ← TensorProductOver.op_smul_tmul]
      have h1 : (op e • op b • m : InDegreeZero M) = 0 := hM (op b • m)
      rw [h1, TensorProductOver.zero_tmul]
    | add x y hx hy => rw [hx, hy, add_zero]
  exact ⟨fun x y => (h0 x).trans (h0 y).symm⟩

end Idempotent

section Induced

variable {A B C : Type} [Ring A] [Ring B] [Ring C] (M N : Type) [AddCommGroup M]
  [Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M] [AddCommGroup N] [Module B N]
  [Module Cᵐᵒᵖ N] [SMulCommClass B Cᵐᵒᵖ N] [Module.Projective Cᵐᵒᵖ N] [Module.Projective B N]
  [HasDerivedCategory.{0, 0} A] [HasDerivedCategory.{0, 0} B] [HasDerivedCategory.{0, 0} C]

/-- **Modules induced from a summand killed by `M`**: let `N` be projective on both sides and
generated as a left `B`-module by an element `g = e g`, where the idempotent `e` kills `M`
(`M e = 0`; for `N = B e`, `g = e`). Then `M ⊗ᴸ_B Y` vanishes in every degree for every
`Y ≅ N ⊗_C W`. -/
theorem isZero_derivedTensorHomology_induced_of_idempotent {e : B} {g : N} (hg : e • g = g)
    (hN : ∀ x : N, ∃ b : B, x = b • g) (hM : ∀ m : M, op e • m = 0)
    (Y : ModuleCat.{0} B) (W : Type) [AddCommGroup W] [Module C W]
    (eY : Y ≃ₗ[B] TensorProductOver C (InDegreeZero N) (InDegreeZero W)) (n : ℤ) :
    IsZero ((homologyFunctor (A := A) ℤ n).obj
      ((derivedTensor.{0} A B M).obj (Q.obj ((degreeZeroModuleFunctor B).obj Y)))) :=
  (homologyFunctor ℤ n).map_isZero (isZero_derivedTensor_induced_of_torVanishing M N
    (fun j hj => isZero_derivedTensor_homology_of_projective M N j hj)
    (subsingleton_tensorProductOver_of_generator hg hN hM) Y W eY)

/-- **Filtrations by induced modules**: with `M`, `N`, `e`, `g` as in
`isZero_derivedTensorHomology_induced_of_idempotent`, a module `Y` with a finite filtration
whose layers are induced modules `N ⊗_C W c` has `M ⊗ᴸ_B Y` vanishing in every degree. -/
theorem isZero_derivedTensorHomology_of_hasFiltration_induced {ι : Type*}
    {L : ι → ModuleCat.{0} B} {m : List ι} {Y : ModuleCat.{0} B}
    (h : ModuleFiltration.HasFiltration L m Y) {e : B} {g : N} (hg : e • g = g)
    (hN : ∀ x : N, ∃ b : B, x = b • g) (hM : ∀ m : M, op e • m = 0)
    (W : ι → ModuleCat.{0} C)
    (hL : ∀ c ∈ m, Nonempty (L c ≃ₗ[B] TensorProductOver C (InDegreeZero N)
      (InDegreeZero (W c)))) (n : ℤ) :
    IsZero ((homologyFunctor (A := A) ℤ n).obj
      ((derivedTensor.{0} A B M).obj (Q.obj ((degreeZeroModuleFunctor B).obj Y)))) :=
  h.isZero_derivedHomology (derivedTensor.{0} A B M) n fun c hc =>
    isZero_derivedTensorHomology_induced_of_idempotent M N hg hN hM (L c) (W c)
      (hL c hc).some n

end Induced

end Categorification

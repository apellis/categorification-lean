/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.RightDualFiltration

/-!
# Dualizing a filtration by sub-bimodules

A bimodule is encoded as a module over a ring `R` through two commuting ring maps
`Bᵐᵒᵖ → R` and `A → R` (`DualEnvelope`); for `R = A ⊗ Bᵐᵒᵖ` these are the two inclusions, and
the submodules of an `R`-module are its sub-bimodules. A filtration over `R` with layers that are
projective right `B`-modules dualizes to a filtration of the duals `Y^∨ = Hom_{Bᵐᵒᵖ}(Y, B)`, as
right `A`-modules (`Aᵐᵒᵖ`-modules), with the layers `(L c)^∨` in the reverse order
(`HasFiltration.envelopeDual`). The filtration steps of the dual are stable under the second
action because the steps of `Y` are.

This is the dualization of the filtration of a partial standardization by sub-bimodules used in
B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Lemma 7.19, where the dual is then a left module over the window algebra.
-/

universe u

open MulOpposite

namespace Categorification

/-- Two commuting actions on `R`-modules: a right `B`-action through `Bᵐᵒᵖ → R` and a left
`A`-action through `A → R`. -/
structure DualEnvelope (R A B : Type u) [Ring R] [Ring A] [Ring B] where
  /-- The right action. -/
  right : Bᵐᵒᵖ →+* R
  /-- The left action. -/
  left : A →+* R
  comm : ∀ a b, left a * right b = right b * left a

namespace DualEnvelope

variable {R A B : Type u} [Ring R] [Ring A] [Ring B] (P : DualEnvelope R A B)

/-- An `R`-module seen through the two actions of `P`. -/
@[nolint unusedArguments]
def Res (_P : DualEnvelope R A B) (Y : Type u) : Type u := Y

variable {X Y Z : Type u} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
  [Module R X] [Module R Y] [Module R Z]

instance : AddCommGroup (P.Res Y) := inferInstanceAs (AddCommGroup Y)

instance : Module Bᵐᵒᵖ (P.Res Y) := Module.compHom Y P.right

instance : Module A (P.Res Y) := Module.compHom Y P.left

/-- The identification of `P.Res Y` with `Y`. -/
def toRes : Y ≃+ P.Res Y := AddEquiv.refl Y

theorem right_smul (b : Bᵐᵒᵖ) (y : Y) : b • P.toRes y = P.toRes (P.right b • y) := rfl

theorem left_smul (a : A) (y : Y) : a • P.toRes y = P.toRes (P.left a • y) := rfl

instance : SMulCommClass A Bᵐᵒᵖ (P.Res Y) where
  smul_comm a b y := by
    let y' : Y := y
    have h : P.left a • P.right b • y' = P.right b • P.left a • y' := by
      rw [smul_smul, smul_smul, P.comm]
    exact h

/-- An `R`-linear map as a right linear map. -/
def resMap (f : X →ₗ[R] Y) : P.Res X →ₗ[Bᵐᵒᵖ] P.Res Y where
  toFun x := f x
  map_add' x x' := f.map_add x x'
  map_smul' b x := f.map_smul (P.right b) x

theorem resMap_left (f : X →ₗ[R] Y) (a : A) (x : P.Res X) :
    P.resMap f (a • x) = a • P.resMap f x := f.map_smul (P.left a) x

/-- An `R`-linear equivalence as a right linear equivalence. -/
def resEquiv (e : X ≃ₗ[R] Y) : P.Res X ≃ₗ[Bᵐᵒᵖ] P.Res Y :=
  LinearEquiv.ofLinearMap (P.resMap e.toLinearMap) (P.resMap e.symm.toLinearMap)
    (LinearMap.ext fun y => e.apply_symm_apply (y : Y))
    (LinearMap.ext fun x => e.symm_apply_apply (x : X))

/-- The dual of an `R`-module, as a right `A`-module. -/
abbrev dualObj (Y : ModuleCat.{u} R) : ModuleCat.{u} Aᵐᵒᵖ :=
  ModuleCat.of Aᵐᵒᵖ (RightDualModule B (P.Res Y))

/-- The dual of an `R`-linear map, as a right `A`-linear map. -/
def dualMap {X Y : ModuleCat.{u} R} (f : X →ₗ[R] Y) : P.dualObj Y →ₗ[Aᵐᵒᵖ] P.dualObj X where
  toFun := RightDualModule.rightDualMap (P.resMap f)
  map_add' := map_add _
  map_smul' a χ := by
    rw [RingHom.id_apply]
    refine RightDualModule.ext fun x => ?_
    change χ (a.unop • P.resMap f x) = χ (P.resMap f (a.unop • x))
    rw [resMap_left]

theorem dualMap_apply {X Y : ModuleCat.{u} R} (f : X →ₗ[R] Y) (χ : P.dualObj Y) :
    P.dualMap f χ = RightDualModule.rightDualMap (P.resMap f) χ := rfl

theorem resMap_injective {f : X →ₗ[R] Y} (hf : Function.Injective f) :
    Function.Injective (P.resMap f) := hf

theorem resMap_surjective {f : X →ₗ[R] Y} (hf : Function.Surjective f) :
    Function.Surjective (P.resMap f) := hf

theorem resMap_exact {f : X →ₗ[R] Y} {g : Y →ₗ[R] Z} (hfg : Function.Exact f g) :
    Function.Exact (P.resMap f) (P.resMap g) := hfg

end DualEnvelope

namespace ModuleFiltration.HasFiltration

open RightDualModule DualEnvelope

variable {R A B : Type u} [Ring R] [Ring A] [Ring B] (P : DualEnvelope R A B) {ι : Type*}

/-- **The mirrored filtration of the dual of a bimodule.** If an `R`-module `Y` (a bimodule
through `P`) has a filtration over `R` whose layers `L c`, `c ∈ m`, are projective right
`B`-modules, then the dual `Y^∨ = Hom_{Bᵐᵒᵖ}(Y, B)` has a filtration by the right `A`-modules
`(L c)^∨`, with the reversed labels. -/
theorem envelopeDual {L : ι → ModuleCat.{u} R} {m : List ι} {Y : ModuleCat.{u} R}
    (h : HasFiltration L m Y) (hL : ∀ c ∈ m, Module.Projective Bᵐᵒᵖ (P.Res (L c))) :
    HasFiltration (fun c => P.dualObj (L c)) m.reverse (P.dualObj Y) := by
  induction h with
  | zero hY =>
    refine .zero ⟨fun φ ψ => RightDualModule.ext fun y => ?_⟩
    have : Subsingleton (P.Res _) := hY
    rw [Subsingleton.elim y 0, map_zero, map_zero]
  | @cons X Y Z f g m c hf hfg hg _ hZ ih =>
    obtain ⟨e⟩ := hZ
    have := hL c (List.mem_cons_self ..)
    have : Module.Projective Bᵐᵒᵖ (P.Res Z) :=
      Module.Projective.of_equiv (P.resEquiv e).symm
    have hX := ih fun c' hc' => hL c' (List.mem_cons_of_mem _ hc')
    have e' : P.dualObj Z ≃ₗ[Aᵐᵒᵖ] P.dualObj (L c) :=
      LinearEquiv.ofLinearMap (P.dualMap e.symm.toLinearMap) (P.dualMap e.toLinearMap)
        (LinearMap.ext fun χ => RightDualModule.ext fun z => by
          exact congrArg χ (e.apply_symm_apply (P.toRes.symm z)))
        (LinearMap.ext fun χ => RightDualModule.ext fun z => by
          exact congrArg χ (e.symm_apply_apply (P.toRes.symm z)))
    have hW : HasFiltration (fun c => P.dualObj (L c)) [c] (P.dualObj Z) :=
      HasFiltration.single e'
    rw [List.reverse_cons]
    exact HasFiltration.extension hX (X := P.dualObj Z) (Y := P.dualObj Y)
      (P.dualMap g) (P.dualMap f) (rightDualMap_injective (P.resMap_surjective hg))
      (rightDualMap_exact (P.resMap_exact hfg) (P.resMap_surjective hg))
      (rightDualMap_surjective (P.resMap_injective hf) (P.resMap_exact hfg)
        (P.resMap_surjective hg)) hW

end ModuleFiltration.HasFiltration

end Categorification

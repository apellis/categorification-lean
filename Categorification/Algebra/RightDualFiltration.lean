/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.RightDualModule
import Categorification.Algebra.ModuleFiltration

/-!
# Dualizing a filtration with projective layers

For a right `B`-module `Y` (a left `Bᵐᵒᵖ`-module) with a finite filtration whose layers `L c`
are projective right modules, the dual `Y^∨ = Hom_{Bᵐᵒᵖ}(Y, B)` is a left `B`-module with the
mirrored filtration: its layers are the duals `(L c)^∨`, in the reverse order
(`HasFiltration.rightDual`). Each step `0 → X → Y → Z → 0` with `Z` projective splits, so the
dual sequence `0 → Z^∨ → Y^∨ → X^∨ → 0` is exact (`rightDualMap_injective`,
`rightDualMap_exact`, `rightDualMap_surjective`).

The filtration is one of right `B`-modules, so every step is stable under the right action; the
dual filtration is one of left `B`-modules. This is the passage from a filtration of a
partial standardization by right submodules to the mirrored filtration of its dual used in
B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Lemma 7.19.
-/

universe u

open MulOpposite

namespace Categorification

namespace RightDualModule

variable {B : Type*} [Ring B]
  {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
  [Module Bᵐᵒᵖ X] [Module Bᵐᵒᵖ Y] [Module Bᵐᵒᵖ Z]

/-- The dual `f^∨ : Y^∨ → X^∨`, `φ ↦ φ ∘ f`, of a right linear map `f : X → Y`. -/
def rightDualMap (f : X →ₗ[Bᵐᵒᵖ] Y) : RightDualModule B Y →ₗ[B] RightDualModule B X where
  toFun φ := ofLinearMap
    { toFun := fun x => φ (f x)
      map_add' := fun x x' => by rw [map_add, map_add]
      map_smul' := fun c x => by rw [map_smul, map_smul]; rfl }
  map_add' _ _ := ext fun _ => rfl
  map_smul' _ _ := ext fun _ => rfl

@[simp]
theorem rightDualMap_apply (f : X →ₗ[Bᵐᵒᵖ] Y) (φ : RightDualModule B Y) (x : X) :
    rightDualMap f φ x = φ (f x) := rfl

/-- A linear equivalence of right modules dualizes to one of left modules. -/
def rightDualEquiv (e : X ≃ₗ[Bᵐᵒᵖ] Y) : RightDualModule B Y ≃ₗ[B] RightDualModule B X :=
  LinearEquiv.ofLinearMap (rightDualMap e.toLinearMap) (rightDualMap e.symm.toLinearMap)
    (LinearMap.ext fun φ => ext fun x => by simp)
    (LinearMap.ext fun φ => ext fun y => by simp)

/-- The dual of a surjection is injective. -/
theorem rightDualMap_injective {g : Y →ₗ[Bᵐᵒᵖ] Z} (hg : Function.Surjective g) :
    Function.Injective (rightDualMap (B := B) g) := by
  intro φ ψ h
  ext z
  obtain ⟨y, rfl⟩ := hg z
  exact congrArg (fun χ : RightDualModule B Y => χ y) h

variable {f : X →ₗ[Bᵐᵒᵖ] Y} {g : Y →ₗ[Bᵐᵒᵖ] Z}

/-- The dual of a short exact sequence with projective quotient is exact in the middle. -/
theorem rightDualMap_exact [Module.Projective Bᵐᵒᵖ Z] (hfg : Function.Exact f g)
    (hg : Function.Surjective g) :
    Function.Exact (rightDualMap (B := B) g) (rightDualMap (B := B) f) := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property g LinearMap.id hg
  intro φ
  constructor
  · intro hφ
    refine ⟨rightDualMap s φ, ext fun y => ?_⟩
    have hy : y - s (g y) ∈ Set.range f := (hfg _).1 (by
      rw [map_sub, ← LinearMap.comp_apply g s, hs, LinearMap.id_apply, sub_self])
    obtain ⟨x, hx⟩ := hy
    have h0 : φ (f x) = 0 := congrArg (fun χ : RightDualModule B X => χ x) hφ
    rw [rightDualMap_apply, rightDualMap_apply, ← sub_eq_zero, ← map_sub, ← neg_sub, ← hx,
      map_neg, h0, neg_zero]
  · rintro ⟨ψ, rfl⟩
    ext x
    rw [rightDualMap_apply, rightDualMap_apply, (hfg (f x)).2 ⟨x, rfl⟩, map_zero, zero_apply]

/-- The dual of a short exact sequence with projective quotient is surjective on the left. -/
theorem rightDualMap_surjective [Module.Projective Bᵐᵒᵖ Z] (hf : Function.Injective f)
    (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Surjective (rightDualMap (B := B) f) := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property g LinearMap.id hg
  have hsplit : ∃ l, g ∘ₗ l = LinearMap.id := ⟨s, hs⟩
  obtain ⟨r, hr⟩ := ((hfg.split_tfae hf hg).out 1 2).mp hsplit
  intro χ
  refine ⟨rightDualMap r χ, ext fun x => ?_⟩
  rw [rightDualMap_apply, rightDualMap_apply, ← LinearMap.comp_apply r f, hr, LinearMap.id_apply]

end RightDualModule

namespace ModuleFiltration.HasFiltration

open RightDualModule

variable {B : Type u} [Ring B] {ι : Type*}

/-- The dual of a right module, as an object of left modules. -/
abbrev rightDualObj (Y : ModuleCat.{u} Bᵐᵒᵖ) : ModuleCat.{u} B :=
  ModuleCat.of B (RightDualModule B Y)

/-- **The mirrored filtration of the dual.** If a right `B`-module `Y` has a filtration with
projective layers `L c`, `c ∈ m`, then its dual `Y^∨` has a filtration by the left modules
`(L c)^∨` with the reversed labels. -/
theorem rightDual {L : ι → ModuleCat.{u} Bᵐᵒᵖ} {m : List ι} {Y : ModuleCat.{u} Bᵐᵒᵖ}
    (h : HasFiltration L m Y) (hL : ∀ c ∈ m, Module.Projective Bᵐᵒᵖ (L c)) :
    HasFiltration (fun c => rightDualObj (L c)) m.reverse (rightDualObj Y) := by
  induction h with
  | zero hY =>
    refine .zero ⟨fun φ ψ => ext fun y => ?_⟩
    rw [Subsingleton.elim y 0, map_zero, map_zero]
  | @cons X Y Z f g m c hf hfg hg _ hZ ih =>
    obtain ⟨e⟩ := hZ
    have := hL c (List.mem_cons_self ..)
    have : Module.Projective Bᵐᵒᵖ Z := Module.Projective.of_equiv e.symm
    have hX := ih fun c' hc' => hL c' (List.mem_cons_of_mem _ hc')
    have hW : HasFiltration (fun c => rightDualObj (L c)) [c] (rightDualObj Z) :=
      HasFiltration.single (rightDualEquiv e.symm)
    rw [List.reverse_cons]
    exact HasFiltration.extension hX (X := rightDualObj Z) (Y := rightDualObj Y)
      (rightDualMap g) (rightDualMap f) (rightDualMap_injective hg)
      (rightDualMap_exact hfg hg) (rightDualMap_surjective hf hfg hg) hW

end ModuleFiltration.HasFiltration

end Categorification

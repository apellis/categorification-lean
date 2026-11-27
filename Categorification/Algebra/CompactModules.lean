/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.ExtShortExact
import DG.Derived.Perfect

set_option backward.isDefEq.respectTransparency false

/-!
# Compact modules in the derived category

A finitely generated projective module, placed in degree `0`, is compact in `D(R)`
(`isCompact_of_projective`), and so is a module with a finite resolution by finitely generated
projectives (`isCompact_of_shortExact`). This is how the cuts `e(t) V e_κ`, which have finite
resolutions by projectives, are compact in Webster, arXiv:1309.3796v3, proof of Theorem 6.15.
-/

noncomputable section

namespace Categorification

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated DG DG.DerivedCategory
open scoped DG.DegreeZero

variable {R : Type} [Ring R] [HasDerivedCategory.{0, 0} R]

/-- A module in degree `0`, as an object of `D(R)`. -/
abbrev moduleObj (M : ModuleCat.{0} R) : DerivedCategory.{0} R :=
  Q.obj ((degreeZeroModuleFunctor R).obj M)

variable (R) in
/-- The regular module in degree `0` is the regular dg module. -/
def regularModuleObjIso : Q.obj (DGModuleCat.of R R) ≅ moduleObj (ModuleCat.of R R) :=
  Q.mapIso (DGModuleCat.isoOfDGModuleEquiv
    { toLinearEquiv := LinearEquiv.refl R R
      map_mem' := fun hx => hx
      map_d' := fun _ => rfl })

variable (R) in
theorem isCompact_regular : IsCompact.{0} (moduleObj (ModuleCat.of R R)) :=
  ((DerivedCategory.compactlyGenerates (A := R)).isCompact ()).of_iso (regularModuleObjIso R).symm

theorem isCompact_moduleObj_of_iso {M N : ModuleCat.{0} R} (e : M ≅ N)
    (h : IsCompact.{0} (moduleObj N)) : IsCompact.{0} (moduleObj M) :=
  h.of_iso (Q.mapIso ((degreeZeroModuleFunctor R).mapIso e))

theorem isCompact_moduleObj_biprod {M N : ModuleCat.{0} R} (hM : IsCompact.{0} (moduleObj M))
    (hN : IsCompact.{0} (moduleObj N)) : IsCompact.{0} (moduleObj (M ⊞ N)) := by
  have : (degreeZeroModuleFunctor R ⋙ Q).Additive := Functor.instAdditiveComp _ _
  have := preservesBinaryBiproduct_of_preservesBiproduct (degreeZeroModuleFunctor R ⋙ Q) M N
  exact (hM.biprod hN).of_iso ((degreeZeroModuleFunctor R ⋙ Q).mapBiprod M N)

variable (R) in
theorem isCompact_pi (n : ℕ) : IsCompact.{0} (moduleObj (ModuleCat.of R (Fin n → R))) := by
  induction n with
  | zero =>
    refine IsCompact.of_isZero ((degreeZeroModuleFunctor R ⋙ Q).map_isZero ?_)
    rw [ModuleCat.isZero_iff_subsingleton]
    infer_instance
  | succ n ih =>
    refine isCompact_moduleObj_of_iso
      ((Fin.consLinearEquiv R (fun _ : Fin (n + 1) => R)).symm.toModuleIso ≪≫
        (ModuleCat.biprodIsoProd (ModuleCat.of R R) (ModuleCat.of R (Fin n → R))).symm) ?_
    exact isCompact_moduleObj_biprod (isCompact_regular R) ih

/-- **A finitely generated projective module is compact in `D(R)`.** -/
theorem isCompact_of_projective (P : ModuleCat.{0} R) [Module.Finite R P]
    [Module.Projective R P] : IsCompact.{0} (moduleObj P) := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R P
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  let Φ := degreeZeroModuleFunctor R ⋙ Q
  refine IsCompact.of_retract ⟨Φ.map (ModuleCat.ofHom s), Φ.map (ModuleCat.ofHom π), ?_⟩
    (isCompact_pi R n)
  rw [← Φ.map_comp]
  have : ModuleCat.ofHom s ≫ ModuleCat.ofHom π = 𝟙 P := ModuleCat.hom_ext hs
  rw [this, Φ.map_id]
  rfl

/-- **Compactness is two-out-of-three along short exact sequences**: the cokernel of a map of
compact modules with compact source and target in a short exact sequence is compact. -/
theorem isCompact_of_shortExact (S : ShortComplex (ModuleCat.{0} R)) (hS : S.ShortExact)
    (h₁ : IsCompact.{0} (moduleObj S.X₁)) (h₂ : IsCompact.{0} (moduleObj S.X₂)) :
    IsCompact.{0} (moduleObj S.X₃) := by
  obtain ⟨δ, hT⟩ := exists_distinguished_of_shortExact_module S hS
  exact IsCompact.ext₃ _ hT h₁ h₂

end Categorification

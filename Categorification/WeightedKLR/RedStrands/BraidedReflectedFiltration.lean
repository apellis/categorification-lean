/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.ModuleFiltration
import Categorification.WeightedKLR.RedStrands.BraidedBimoduleFlip
import Categorification.WeightedKLR.RedStrands.BraidedStandardModule

/-!
# Reflected filtrations on braid bimodules

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
§6.1, p. 65, proof of Lemma 6.11, step `f_n → s_n`. A right-standard filtration of
the inverse braid gives a left filtration of the braid by the reflected right standards.
The reflected action is restriction of scalars along the corner anti-involution.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR ModuleFiltration

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}

local notation "C" => ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν)
set_option quotPrecheck false in
local notation "B" κ':arg κ:arg => ↥(braidingBimodule k Q Λ ν κ' κ)

set_option quotPrecheck false in
local notation "reflect" κ:arg =>
  ModuleCat.restrictScalars
    (cornerFlipEquiv (Q := Q) (Λ := Λ) ν κ).symm.toRingHom

/-- In the proof of Webster's Lemma 6.11 (arXiv:1309.3796v2, §6.1, p. 65), reflect a
supplied right-standard filtration of the inverse braid. The subquotients on the left
are the same loading standards with scalars restricted along the corner flip. -/
theorem hasReflectedStandardFiltration_braidingBimodule (κ' κ : List (Fin ℓ))
    {m : List {s : Seq (stendhalWeight ℓ ν) // redWord s = κ' ∧ ¬ IsViolated s}}
    (h : HasFiltration
      (fun s => ModuleCat.of (C κ')ᵐᵒᵖ
        (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) s.val κ')) m
      (ModuleCat.of (C κ')ᵐᵒᵖ (B κ κ'))) :
    HasFiltration
      (fun s => (reflect κ').obj (ModuleCat.of (C κ')ᵐᵒᵖ
        (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) s.val κ'))) m
      (ModuleCat.of (C κ') (B κ' κ)) := by
  let e : ModuleCat.of (C κ') (B κ' κ) ≃ₗ[C κ']
      (reflect κ').obj (ModuleCat.of (C κ')ᵐᵒᵖ (B κ κ')) :=
    { braidingBimoduleFlip κ' κ with
      map_smul' a x := braidingBimoduleFlip_smul_left κ' κ a x }
  exact (h.restrictScalars _).of_equiv e.symm

end Categorification.Stendhal.BraidedStendhalAlgebra

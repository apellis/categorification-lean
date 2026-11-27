/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidedStandardDerived
import Categorification.Algebra.IdempotentGenerators

set_option backward.isDefEq.respectTransparency false

/-!
# The loading projectives generate the derived category of the violated corner

The loading idempotents `e(t)` with red order `κ` sum to the unit of the violated corner at `κ`
(`sum_violLoadingIdem`), so the loading projectives `e(t) T`, in degree `0`, compactly generate
its derived category of right modules (`compactlyGenerates_loadingProjective`). This is the
generation of `D(T^λ)` used in Webster, arXiv:1309.3796v3, proof of Theorem 6.15.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open CategoryTheory DG KLR
open scoped DG.DegreeZero

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "C" => ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν)

/-- The loading idempotents of red order `κ` sum to the unit of the violated corner. -/
theorem sum_violLoadingIdem (κ : List (Fin ℓ)) :
    ∑ t : {t : Seq μ // redWord t = κ}, violLoadingIdem (k := k) (Q := Q) (Λ := Λ) t.2 =
      (1 : C κ) := by
  let v : C κ →+ BraidedStendhalAlgebra.ViolQuotient k Q Λ ν :=
    { toFun := Subtype.val
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hv : Function.Injective v := Subtype.val_injective
  apply hv
  rw [map_sum]
  change ∑ t : {t : Seq μ // redWord t = κ},
      violMk k Q Λ ν (ofKLR k Q Λ ν (KLRAlgebra.e t.1)) = violMk k Q Λ ν (redProj k Q Λ ν κ)
  rw [redProj, redIdem, map_sum, map_sum,
    Finset.sum_subtype (Finset.univ.filter fun i : Seq μ => redWord i = κ)
      (p := fun i : Seq μ => redWord i = κ)
      (fun _ => Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _)))]

/-- **The loading projectives `e(t) T` of red order `κ` compactly generate** the derived category
of right modules over the violated corner at `κ`. -/
theorem compactlyGenerates_loadingProjective (κ : List (Fin ℓ))
    [DG.HasDerivedCategory.{0, 0} (C κ)ᵐᵒᵖ] :
    CompactlyGenerates (fun t : {t : Seq μ // redWord t = κ} =>
      rIdealObj (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) t.2)) :=
  compactlyGenerates_rIdeal (fun t : {t : Seq μ // redWord t = κ} =>
      violLoadingIdem (k := k) (Q := Q) (Λ := Λ) t.2)
    (fun t => isIdempotentElem_violLoadingIdem t.2) (sum_violLoadingIdem κ)

end Categorification.Stendhal.BraidedStendhalAlgebra

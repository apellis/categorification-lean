/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidedStandardModule
import Categorification.Algebra.ModuleFiltration

/-!
# Right standard filtration of a Figure 5 braid column

Webster, arXiv:1309.3796v2, Proposition 6.9 and Lemma 6.11.
For the two-red Figure 5 cuts, the right-linear comparison identifies the
column with its one proposed loading standard for any black content.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR Equiv MulOpposite

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin 2 → I →₀ ℕ} {ν : Multiset I}

local notation "μ" => stendhalWeight 2 ν
local notation "m" => Multiset.card μ
local notation "A" κ:arg => (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ)ᵐᵒᵖ

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

/-- The actual Figure 5 braid column has a right standard filtration with
the upper loading as its single factor. -/
theorem figureFiveColumn_hasStandardFiltration
    {ρ : Perm (Fin m) → List ℕ} (hρ : TypeA.IsReducedChoice ρ) (hQ : KLRSymm Q)
    {s t : Seq μ} {r d : Fin 2} {g : Perm (Fin m)} (h1 : 1 < m)
    (ht₀ : t.lbl ⟨0, by omega⟩ = .inr r) (ht₁ : t.lbl ⟨1, h1⟩ = .inr d)
    (hb : EdgeBraid (show 0 < m by omega) r g s t) :
    ModuleFiltration.HasFiltration
      (fun j : Seq μ => ModuleCat.of (A [r, d])
        (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) j [r, d]))
      [t] (ModuleCat.of (A [r, d]) (violCorner k Q Λ ν s [r, d])) :=
  ModuleFiltration.HasFiltration.single
    (violLoadingStandardEquivBraidCorner hρ hQ h1 ht₀ ht₁ hb).symm

end Categorification.Stendhal.BraidedStendhalAlgebra

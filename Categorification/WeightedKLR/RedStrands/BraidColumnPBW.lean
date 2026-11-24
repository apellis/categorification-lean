/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidedStandardIso

/-!
# PBW spanning diagrams for a braid column

Webster, arXiv:1309.3796v2, Proposition 6.4 and the proof of Lemma 6.11.
Compress the affine basis to a prescribed top loading and bottom red order.
The surviving diagrams span the column after imposing the violating ideal.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra
open KLR KLRAlgebra TypeA Equiv

variable {I k : Type} [DecidableEq I] [CommRing k] {ℓ : ℕ} {ν : Multiset I}
    {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}

local notation "μ" => stendhalWeight ℓ ν
local notation "A" => BraidedStendhalAlgebra k Q Λ ν
local notation "ι" => ofKLR k Q Λ ν

/-- The affine braid column with one prescribed top loading. -/
def affineFixedTopColumn (s : Seq μ) (κ : List (Fin ℓ)) : Submodule k A :=
  LinearMap.range (LinearMap.mulLeft k (ι (e s)) ∘ₗ
    LinearMap.mulRight k (redProj k Q Λ ν κ))

private theorem fixedTopProjection_basis (hQ : KLRSymm Q)
    {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
    (hρ : IsReducedChoice ρ) (s : Seq μ) (κ : List (Fin ℓ))
    (b : BlackIdx (ℓ := ℓ) ν) :
    ι (e s) * (basis (Λ := Λ) hQ ρ hρ b * redProj k Q Λ ν κ) =
      if b.val.2.1 • b.val.1 = s ∧ redWord b.val.1 = κ then basis (Λ := Λ) hQ ρ hρ b else 0 := by
  by_cases hk : redWord b.val.1 = κ
  · rw [basis_mul_redProj hQ ρ hρ, ite_eq_left hk, e_mul_basis hQ ρ hρ]
    simp [hk]
  · rw [basis_mul_redProj hQ ρ hρ, ite_eq_right hk, mul_zero]
    simp [hk]

/-- The fixed-top affine column has the compressed Proposition 6.4 basis. -/
def affineFixedTopColumnBasis (hQ : KLRSymm Q)
    {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
    (hρ : IsReducedChoice ρ) (s : Seq μ) (κ : List (Fin ℓ)) :
    Module.Basis {b : BlackIdx (ℓ := ℓ) ν //
      b.val.2.1 • b.val.1 = s ∧ redWord b.val.1 = κ} k
      (affineFixedTopColumn (Q := Q) (Λ := Λ) s κ) := by
  classical
  exact WeightedKLR.basisRangeOfApply (basis (Λ := Λ) hQ ρ hρ)
    (LinearMap.mulLeft k (ι (e s)) ∘ₗ LinearMap.mulRight k (redProj k Q Λ ν κ))
    (fun b => b.val.2.1 • b.val.1 = s ∧ redWord b.val.1 = κ)
    (fixedTopProjection_basis hQ hρ s κ)

/-- Every actual fixed-top column is the image of the affine one. -/
def affineFixedTopColumnQuotient (s : Seq μ) (κ : List (Fin ℓ)) :
    affineFixedTopColumn (Q := Q) (Λ := Λ) s κ →ₗ[k] violCorner k Q Λ ν s κ :=
  ((violMk k Q Λ ν).toLinearMap.comp
    (affineFixedTopColumn (Q := Q) (Λ := Λ) s κ).subtype).codRestrict _ (by
      rintro ⟨_, a, rfl⟩
      exact ⟨a, rfl⟩)

theorem affineFixedTopColumnQuotient_surjective (s : Seq μ) (κ : List (Fin ℓ)) :
    Function.Surjective (affineFixedTopColumnQuotient (Q := Q) (Λ := Λ) s κ) := by
  rintro ⟨_, a, rfl⟩
  exact ⟨⟨_, a, rfl⟩, rfl⟩

/-- The actual column is spanned by the images of the affine fixed-top
basis. The quotient can impose relations among these images. -/
theorem span_violFixedTopColumn (hQ : KLRSymm Q)
    {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
    (hρ : IsReducedChoice ρ) (s : Seq μ) (κ : List (Fin ℓ)) :
    Submodule.span k (Set.range (fun b => affineFixedTopColumnQuotient (Q := Q) (Λ := Λ) s κ
      (affineFixedTopColumnBasis (Λ := Λ) hQ hρ s κ b))) = ⊤ := by
  let f := affineFixedTopColumnQuotient (Q := Q) (Λ := Λ) s κ
  change Submodule.span k (Set.range (f ∘ affineFixedTopColumnBasis (Λ := Λ) hQ hρ s κ)) = ⊤
  rw [Set.range_comp, ← Submodule.map_span, Module.Basis.span_eq, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (affineFixedTopColumnQuotient_surjective (Q := Q) (Λ := Λ) s κ)

end Categorification.Stendhal.BraidedStendhalAlgebra

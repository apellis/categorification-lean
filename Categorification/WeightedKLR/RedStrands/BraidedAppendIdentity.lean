/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidedRelabelAppend
import Categorification.WeightedKLR.RedStrands.BraidedViolatedIdentity

set_option backward.isDefEq.respectTransparency false

/-!
# The identity corner and the appended black strand

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §6.1. At the
red order `λ_1, …, λ_ℓ` the corner of the quotient of the braided Stendhal algebra by violated
idempotents is the tensor product algebra `T^λ` (`violCornerEquiv`). Appending a black strand
at the right on braided diagrams (`appendViol`) corresponds under this isomorphism to Webster's
map `T^λ → T^λ` adjoining a black strand (`Stendhal.appendBlack`, §4.6). With the relabelling
results of `BraidedRelabelAppend`, this identifies the functors `𝔈_i` on braided diagrams at
every red order with Webster's `𝔈_i`.

## Main results

* `BraidedStendhalAlgebra.toAllOrders_appendBlackAlg`: imposing the vanishing of red crossings
  commutes with appending a black strand.
* `BraidedStendhalAlgebra.appendViol_mem_corner`: appending preserves the identity corner.
* `BraidedStendhalAlgebra.violCornerEquiv_appendViol`: the square with `Stendhal.appendBlack`
  commutes.
-/

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA Equiv

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (i : I) (ν : Multiset I)

local notation "μ" => stendhalWeight ℓ ν
local notation "σᵢ" => (Singleton.singleton (Sum.inl i) : Multiset (I ⊕ Fin ℓ))
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "S" => stendhalQ Q Λ

namespace BraidedStendhalAlgebra

/-- On a KLR diagram, appending the black strand is concatenation with a straight strand. -/
theorem appendBlackAlg_ofKLR (z : KLRAlgebra k S μ) :
    appendBlackAlg Q Λ i ν (ofKLR k Q Λ ν z) =
      ofKLR k Q Λ νᵢ (castKLR S (stendhalWeight_addBlack i ν) (concat S μ σᵢ (z ⊗ₜ 1))) := by
  rw [appendBlackAlg_apply, appendBlackValue_apply, appendBlack_ofKLR]
  change appendAmbient Q Λ i ν (((blockL μ σᵢ).hom S z).val) = _
  rw [concat_tmul, map_one, Corner.val_one, Corner.val_mul_E]
  rfl

/-- Imposing the vanishing of red crossings commutes with appending a black strand. -/
theorem toAllOrders_appendBlackAlg (z : BraidedStendhalAlgebra k Q Λ ν) :
    toAllOrders k Q Λ νᵢ (appendBlackAlg Q Λ i ν z) =
      Stendhal.appendBlackValue Q Λ i ν (toAllOrders k Q Λ ν z) := by
  obtain ⟨z, rfl⟩ := ofKLR_surjective (k := k) (Q := Q) (Λ := Λ) (ν := ν) z
  rw [appendBlackAlg_ofKLR, toAllOrders_ofKLR, toAllOrders_ofKLR]
  exact (appendBlackAllOrders_ofKLR_val Q Λ i ν z).symm

local notation "P" => redProj k Q Λ ν (List.finRange ℓ)
local notation "P'" => redProj k Q Λ νᵢ (List.finRange ℓ)

/-- Appending a black strand preserves the corner at the red order `λ_1, …, λ_ℓ`. -/
theorem appendBlackAlg_mem_corner {x : BraidedStendhalAlgebra k Q Λ ν}
    (hx : x ∈ Subsemigroup.corner P) :
    appendBlackAlg Q Λ i ν x ∈ Subsemigroup.corner P' := by
  obtain ⟨r, rfl⟩ := hx
  refine ⟨appendIdem Q Λ i ν * appendBlackAlg Q Λ i ν r * appendIdem Q Λ i ν, ?_⟩
  simp only [map_mul, appendBlackAlg_apply, appendBlackValue_redProj]
  have hc := redProj_commute_appendIdem Q Λ i ν (List.finRange ℓ)
  calc P' * (appendIdem Q Λ i ν * appendBlackValue Q Λ i ν r * appendIdem Q Λ i ν) * P' =
      P' * appendIdem Q Λ i ν * appendBlackValue Q Λ i ν r * (appendIdem Q Λ i ν * P') := by
        simp only [mul_assoc]
    _ = _ := by rw [← hc.eq]

/-- Appending a black strand preserves the corner of the quotient by violated idempotents at the
red order `λ_1, …, λ_ℓ`. -/
theorem appendViol_mem_corner {x : ViolQuotient k Q Λ ν}
    (hx : x ∈ Subsemigroup.corner (violMk k Q Λ ν P)) :
    appendViol Q Λ i ν x ∈ Subsemigroup.corner (violMk k Q Λ νᵢ P') := by
  obtain ⟨r, rfl⟩ := hx
  obtain ⟨r, rfl⟩ := violMk_surjective (k := k) (Q := Q) (Λ := Λ) (ν := ν) r
  obtain ⟨w, hw⟩ := appendBlackAlg_mem_corner Q Λ i ν (x := P * r * P) ⟨r, rfl⟩
  refine ⟨violMk k Q Λ νᵢ w, ?_⟩
  change violMk k Q Λ νᵢ P' * violMk k Q Λ νᵢ w * violMk k Q Λ νᵢ P' =
    appendViol Q Λ i ν (violMk k Q Λ ν P * violMk k Q Λ ν r * violMk k Q Λ ν P)
  change P' * w * P' = _ at hw
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, appendViol_violMk, hw]

end BraidedStendhalAlgebra

namespace BraidedStendhalAlgebra

variable {Q Λ i ν}
  {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  {ρ' : Perm (Fin (Multiset.card (stendhalWeight ℓ ({i} + ν)))) → List ℕ}
  (hρ : IsReducedChoice ρ) (hρ' : IsReducedChoice ρ') (hQ : KLRSymm Q)

/-- **Appending a black strand on `B_e` is Webster's `T^λ → T^λ` adjoining a black strand**
(arXiv:1309.3796v2, §4.6 and §6.1): `violCornerEquiv` intertwines `appendViol` with
`Stendhal.appendBlack`. -/
theorem violCornerEquiv_appendViol
    (x : (isIdempotentElem_violRedProj k Q Λ ν).Corner) :
    violCornerEquiv hρ' hQ ⟨appendViol Q Λ i ν x.1, appendViol_mem_corner Q Λ i ν x.2⟩ =
      Stendhal.appendBlack Q Λ i ν (violCornerEquiv hρ hQ x) := by
  obtain ⟨y, rfl⟩ := violCornerHom_surjective x
  have hy : (⟨appendViol Q Λ i ν (violCornerHom k Q Λ ν y).1,
      appendViol_mem_corner Q Λ i ν (violCornerHom k Q Λ ν y).2⟩ :
        (isIdempotentElem_violRedProj k Q Λ νᵢ).Corner) =
      violCornerHom k Q Λ νᵢ ⟨appendBlackAlg Q Λ i ν y.1, appendBlackAlg_mem_corner Q Λ i ν y.2⟩ :=
    Subtype.ext rfl
  rw [hy, violCornerEquiv_violCornerHom, violCornerEquiv_violCornerHom, Stendhal.appendBlack_mk]
  congr 1
  exact Subtype.ext (toAllOrders_appendBlackAlg Q Λ i ν y.1)

end BraidedStendhalAlgebra

end Categorification.Stendhal

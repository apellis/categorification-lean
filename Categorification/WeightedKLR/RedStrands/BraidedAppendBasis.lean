/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidedAppendBlack

set_option backward.isDefEq.respectTransparency false

/-!
# Appending a black strand to the standard basis

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §6.1,
proof of Proposition 6.7. The map adding a straight black strand at the right sends the
diagrams `ψ_ρ x^u e(s)` of Proposition 6.4 to the diagrams `ψ_ρ x^{u} e(s i)`.

## Main results

* `appendBlackAlg`: the map as a non-unital `k`-algebra map.
* `appendBlackValue_std`: its value on a diagram `ψ_ρ x^u e(s)`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA MvPolynomial

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (i : I) (ν : Multiset I)

local notation "μ" => stendhalWeight ℓ ν
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "B" => BraidedStendhalAlgebra k Q Λ νᵢ

theorem castKLR_pol' {Q' : I → I → MvPolynomial (Fin 2) k} {μ₁ μ₂ : Multiset I} (h : μ₁ = μ₂)
    (p : MvPolynomial (Fin (Multiset.card μ₁)) k) :
    castKLR Q' h (pol p) = pol (rename (Fin.cast (congrArg Multiset.card h)) p) := by
  subst h
  simp only [castKLR_rfl]
  exact congrArg pol (rename_id_apply p).symm

theorem castKLR_ψw' {Q' : I → I → MvPolynomial (Fin 2) k} {μ₁ μ₂ : Multiset I} (h : μ₁ = μ₂)
    (L : List ℕ) : castKLR Q' h (ψw L) = ψw L := by
  subst h; rfl

namespace BraidedStendhalAlgebra

/-- Appending a black strand, as a non-unital `k`-algebra map. -/
def appendBlackAlg : BraidedStendhalAlgebra k Q Λ ν →ₙₐ[k] B :=
  { appendBlackValue Q Λ i ν with
    map_smul' := fun c z => by
      change (appendBlack Q Λ i ν (c • z)).val = c • (appendBlack Q Λ i ν z).val
      rw [map_smul]
      exact KLR.Corner.val_smul _ _ }

theorem appendBlackAlg_apply (z : BraidedStendhalAlgebra k Q Λ ν) :
    appendBlackAlg Q Λ i ν z = appendBlackValue Q Λ i ν z := rfl

theorem appendBlack_ofKLR_pol (p : MvPolynomial (Fin (Multiset.card μ)) k) :
    (appendBlack Q Λ i ν (ofKLR k Q Λ ν (pol p))).val =
      ofKLR k Q Λ νᵢ (pol (rename (appendPos i ν) p)) * appendIdem Q Λ i ν := by
  rw [appendBlack_ofKLR]
  change appendAmbient Q Λ i ν (((blockL μ _).hom _) (pol p)).val = _
  rw [BlockEmb.hom_pol, val_polCorner, map_mul]
  congr 1
  change ofKLR k Q Λ νᵢ (castKLR _ (stendhalWeight_addBlack i ν) (pol _)) = _
  rw [castKLR_pol', rename_rename]
  congr 2

theorem appendBlack_ofKLR_ψw {L : List ℕ} (hL : ValidWord (Multiset.card μ) L) :
    (appendBlack Q Λ i ν (ofKLR k Q Λ ν (ψw L))).val =
      ofKLR k Q Λ νᵢ (ψw L) * appendIdem Q Λ i ν := by
  rw [appendBlack_ofKLR]
  change appendAmbient Q Λ i ν (((blockL μ _).hom _) (ψw L)).val = _
  rw [BlockEmb.val_hom_ψw _ hL, map_mul, blockL_o]
  congr 1
  change ofKLR k Q Λ νᵢ (castKLR _ (stendhalWeight_addBlack i ν) _) = _
  rw [castKLR_ψw']
  congr 2
  simp

theorem appendIdem_commute_pol (q : MvPolynomial (Fin (Multiset.card (stendhalWeight ℓ νᵢ))) k) :
    Commute (appendIdem Q Λ i ν) (ofKLR k Q Λ νᵢ (pol q)) := by
  rw [appendIdem_eq_sum]
  exact Commute.sum_left _ _ _ fun s _ =>
    ((e_commute_pol _ q).map (ofKLR k Q Λ νᵢ).toRingHom)

/-- Appending a black strand to a standard diagram `ψ_L x^p e(s)`. -/
theorem appendBlackValue_std {L : List ℕ} (hL : ValidWord (Multiset.card μ) L)
    (p : MvPolynomial (Fin (Multiset.card μ)) k) (s : Seq μ) :
    appendBlackValue Q Λ i ν (ofKLR k Q Λ ν (ψw L * pol p * e s)) =
      ofKLR k Q Λ νᵢ (ψw L * pol (rename (appendPos i ν) p) * e (appendBlackLoading i ν s)) := by
  have hE := KLR.Corner.E_mul_val (appendBlack Q Λ i ν (ofKLR k Q Λ ν (e s)))
  rw [appendBlack_ofKLR_e] at hE
  rw [appendBlackValue_apply, map_mul (ofKLR k Q Λ ν), map_mul (ofKLR k Q Λ ν),
    map_mul (appendBlack Q Λ i ν), map_mul (appendBlack Q Λ i ν), KLR.Corner.val_mul,
    KLR.Corner.val_mul, appendBlack_ofKLR_ψw Q Λ i ν hL, appendBlack_ofKLR_pol,
    appendBlack_ofKLR_e, map_mul (ofKLR k Q Λ νᵢ), map_mul (ofKLR k Q Λ νᵢ)]
  simp only [mul_assoc]
  rw [hE, ← mul_assoc (appendIdem Q Λ i ν), (appendIdem_commute_pol Q Λ i ν _).eq, mul_assoc,
    hE]

end BraidedStendhalAlgebra

end Categorification.Stendhal

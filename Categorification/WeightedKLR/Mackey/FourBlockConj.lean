/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.FourBlockSwap

/-!
# Local conjugacy of the juxtapositions in the two layouts

A step of the proof of B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, Theorem 2.19, towards the comparison of the juxtaposition of four diagrams
in the layout `a b c d` with the juxtaposition of the same diagrams in the layout `a c b d`:
local conjugacy of sums over families of chamber embeddings that are conjugate on a common
subfamily.

## Main results

* `ChamberEmbedding.isLocalConj_sum_toHom_of_injective`: sums over families of chamber
  embeddings that are conjugate on a common subfamily and avoid the chamber families elsewhere
  are locally conjugate.
-/

namespace Categorification.WeightedKLR

open FullChamber GalleryAlgebra

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

attribute [local instance] ColPerm.fintype

variable (hΓ : Γ.PSymm)

namespace GalleryAlgebra.IsLocalConj

variable {hΓ} {Q : Type*} {χ χ' : Q → FullChamber Γ ν} {ρ : ColPerm ν}

/-- An element whose blocks avoid the family `χ` is locally conjugate to `0`. -/
theorem zero_left {w : GalleryAlgebra k Γ ν}
    (hw : ∀ D C, blockOp k hΓ D C w ≠ 0 → (∀ q, χ q ≠ D) ∧ ∀ q, χ q ≠ C) :
    IsLocalConj k hΓ χ χ' ρ 0 w := by
  refine ⟨fun D C hDC => ?_, fun D C hDC => absurd (by simp) hDC, fun q q' => ?_⟩
  · obtain ⟨hD, hC⟩ := hw D C hDC
    exact ⟨fun ⟨q, hq⟩ => absurd hq (hD q), fun ⟨q, hq⟩ => absurd hq (hC q)⟩
  · have h0 : blockOp k hΓ (χ q) (χ q') w = 0 := by
      by_contra h
      exact (hw _ _ h).1 q rfl
    simp [h0]

/-- An element whose blocks avoid the family `χ'` is locally conjugate to `0`. -/
theorem zero_right {w : GalleryAlgebra k Γ ν}
    (hw : ∀ D C, blockOp k hΓ D C w ≠ 0 → (∀ q, χ' q ≠ D) ∧ ∀ q, χ' q ≠ C) :
    IsLocalConj k hΓ χ χ' ρ w 0 := by
  refine ⟨fun D C hDC => absurd (by simp) hDC, fun D C hDC => ?_, fun q q' => ?_⟩
  · obtain ⟨hD, hC⟩ := hw D C hDC
    exact ⟨fun ⟨q, hq⟩ => absurd hq (hD q), fun ⟨q, hq⟩ => absurd hq (hC q)⟩
  · have h0 : blockOp k hΓ (χ' q) (χ' q') w = 0 := by
      by_contra h
      exact (hw _ _ h).1 q rfl
    simp [h0]

end GalleryAlgebra.IsLocalConj

namespace ChamberEmbedding

variable {ν₀ : I →₀ ℕ}

/-- The blocks of the image of a chamber embedding lie at its chambers. -/
theorem blockOp_toHom_ne_zero {J : ChamberEmbedding Γ ν₀ ν} {D C : FullChamber Γ ν}
    {y : GalleryAlgebra k Γ ν₀} (h : blockOp k hΓ D C (J.toHom y) ≠ 0) :
    (∃ A, J.chamber A = D) ∧ ∃ A, J.chamber A = C := by
  have hc := (J.isConjOn_galleryHom hΓ (J' := J) (ρ := 1) (fun _ => rfl) y).1 D C
  by_contra hn
  rw [not_and_or] at hn
  refine h (hc ?_)
  rcases hn with hn | hn
  · exact Or.inl fun A hA => hn ⟨A, hA⟩
  · exact Or.inr fun A hA => hn ⟨A, hA⟩

open Classical in
/-- Splitting a sum along an injection. -/
theorem sum_eq_sum_comp_add_sum_filter {V X : Type*} [Fintype V] [Fintype X] {j : X → V}
    (hj : Function.Injective j) (f : V → GalleryAlgebra k Γ ν) :
    ∑ v, f v = ∑ x, f (j x) + ∑ v ∈ Finset.univ.filter (· ∉ Set.range j), f v := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ Set.range j)]
  congr 1
  have himg : Finset.univ.filter (· ∈ Set.range j) = Finset.univ.map ⟨j, hj⟩ := by
    ext v
    simp
  rw [himg, Finset.sum_map]
  rfl

variable {Q : Type*} {χ χ' : Q → FullChamber Γ ν} {ρ : ColPerm ν}

/-- **Sums over families of chamber embeddings conjugate on a subfamily.** Let `J u`, `J' u'` be
families of chamber embeddings, and `ι`, `ι'` injections of a common index set `X` such that the
embeddings `J (ι x)` and `J' (ι' x)` differ by `ρ` and match the families `χ`, `χ'`. If the
chambers of the embeddings outside the images of `ι` and `ι'` avoid `χ` and `χ'`, then the sums
`∑ u', J' u' (y)` and `∑ u, J u (y)` are locally conjugate along `ρ`. -/
theorem isLocalConj_sum_toHom_of_injective {U U' X : Type*} [Fintype U] [Fintype U'] [Fintype X]
    {J : U → ChamberEmbedding Γ ν₀ ν} {J' : U' → ChamberEmbedding Γ ν₀ ν} {ι : X → U}
    {ι' : X → U'} (hι : Function.Injective ι) (hι' : Function.Injective ι')
    (hρ : ∀ x s, (J' (ι' x)).toFun s = ρ.1 ((J (ι x)).toFun s))
    (hmatch : ∀ x q C, χ q = (J (ι x)).chamber C ↔ χ' q = (J' (ι' x)).chamber C)
    (hclosed : ∀ x C C', (∃ q, χ q = (J (ι x)).chamber C) → ∃ q, χ q = (J (ι x)).chamber C')
    (hout : ∀ u, u ∉ Set.range ι → ∀ q C, χ q ≠ (J u).chamber C)
    (hout' : ∀ u, u ∉ Set.range ι' → ∀ q C, χ' q ≠ (J' u).chamber C)
    (y : GalleryAlgebra k Γ ν₀) :
    IsLocalConj k hΓ χ χ' ρ (∑ u, (J' u).toHom y) (∑ u, (J u).toHom y) := by
  classical
  rw [sum_eq_sum_comp_add_sum_filter hι, sum_eq_sum_comp_add_sum_filter hι']
  have hmain := isLocalConj_sum_toHom hΓ (J := J ∘ ι) (J' := J' ∘ ι') hρ hmatch hclosed y
  have hrest : IsLocalConj k hΓ χ χ' ρ 0
      (∑ u ∈ Finset.univ.filter (· ∉ Set.range ι), (J u).toHom y) := by
    rw [← Finset.sum_const_zero (s := Finset.univ.filter (· ∉ Set.range ι))]
    refine IsLocalConj.sum _ fun u hu => IsLocalConj.zero_left fun D C hDC => ?_
    have hu' := (Finset.mem_filter.1 hu).2
    obtain ⟨⟨A, rfl⟩, ⟨A', rfl⟩⟩ := blockOp_toHom_ne_zero hΓ hDC
    exact ⟨fun q => hout u hu' q A, fun q => hout u hu' q A'⟩
  have hrest' : IsLocalConj k hΓ χ χ' ρ
      (∑ u ∈ Finset.univ.filter (· ∉ Set.range ι'), (J' u).toHom y) 0 := by
    rw [← Finset.sum_const_zero (s := Finset.univ.filter (· ∉ Set.range ι'))]
    refine IsLocalConj.sum _ fun u hu => IsLocalConj.zero_right fun D C hDC => ?_
    have hu' := (Finset.mem_filter.1 hu).2
    obtain ⟨⟨A, rfl⟩, ⟨A', rfl⟩⟩ := blockOp_toHom_ne_zero hΓ hDC
    exact ⟨fun q => hout' u hu' q A, fun q => hout' u hu' q A'⟩
  simpa using (hmain.add hrest).add hrest'

end ChamberEmbedding

end Categorification.WeightedKLR

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.Filtration

/-!
# Bases of the subquotients of the Mackey filtration

The subquotients of the Mackey filtration of B. Webster, *Weighted Khovanov–Lauda–Rouquier
algebras*, arXiv:1209.2463v4, §2.4 (proof of Theorem 2.19, which follows Khovanov–Lauda,
arXiv:0803.4121v2, Proposition 2.18). For sets `S' ⊆ S` of shuffle types, the quotient of the
step `mackeyFilt D C S` by the step `mackeyFilt D C S'` is free, with basis the classes of the
elements `b(g, m)` of the basis of Theorem 2.8 whose relabelling `g` has shuffle type in `S` but
not in `S'` (`GalleryAlgebra.mackeySubquotientBasis`). Taking `S' = S \ {μ}` gives the strict
step of shuffle type `μ`.

## Main definitions

* `Module.Basis.quotientSpanImage b s`: the basis of `M ⧸ span (b '' s)` given by the classes of
  the remaining basis vectors.
* `GalleryAlgebra.mackeySubquotientBasis`: the basis of a subquotient of the filtration.
-/

namespace Module.Basis

variable {ι R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The quotient of a free module by the span of part of a basis is free on the classes of the
remaining basis vectors. -/
noncomputable def quotientSpanImage (b : Basis ι R M) (s : Set ι) :
    Basis (sᶜ : Set ι) R (M ⧸ Submodule.span R (b '' s)) :=
  have hc : IsCompl (Submodule.span R (b '' s)) (Submodule.span R (b '' sᶜ)) :=
    b.linearIndependent.isCompl_span_image b.span_eq isCompl_compl
  Basis.mk (v := fun j => Submodule.Quotient.mk (b j.1))
    (by
      have := (b.linearIndependent.comp _ Subtype.val_injective).map
        (f := (Submodule.span R (b '' s)).mkQ) (by
          rw [Submodule.ker_mkQ, Set.range_comp, Subtype.range_coe]
          exact hc.disjoint.symm)
      exact this)
    (by
      rintro x -
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      have hy : y ∈ Submodule.span R (b '' s) ⊔ Submodule.span R (b '' sᶜ) := by
        rw [hc.codisjoint.eq_top]
        trivial
      obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hy
      have hu0 : (Submodule.Quotient.mk u : M ⧸ Submodule.span R (b '' s)) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).2 hu
      rw [Submodule.Quotient.mk_add, hu0, zero_add]
      have hmap := Submodule.mem_map_of_mem (f := (Submodule.span R (b '' s)).mkQ) hw
      rw [Submodule.map_span, ← Set.image_comp] at hmap
      refine Submodule.span_mono ?_ hmap
      rintro _ ⟨j, hj, rfl⟩
      exact ⟨⟨j, hj⟩, rfl⟩)

@[simp]
theorem quotientSpanImage_apply (b : Basis ι R M) (s : Set ι) (j : (sᶜ : Set ι)) :
    b.quotientSpanImage s j = Submodule.Quotient.mk (b j.1) := by
  unfold quotientSpanImage
  exact Basis.mk_apply _ _ _

end Module.Basis

namespace Categorification.WeightedKLR

open GalleryAlgebra

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

attribute [local instance] ColPerm.fintype

namespace GalleryAlgebra

variable {P : FullChamber Γ ν → FullChamber Γ ν → (Strand ν → 𝕜) × (Strand ν → 𝕜)}
  (hP : ∀ C E, IsChamberSegment C E (P C E)) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
  (hΓ : Γ.PSymm) (hW : ∀ w : Wall Γ ν, IsRegular (w.factor (k := k)))
  (hL : ∀ (Q : MvPolynomial (Fin 2) k) (a b : Strand ν), Γ.loop a.1 = some Q → a ≠ b →
    a.1 = b.1 → IsRegular (loopFactor Q a b))

/-- Inside the step `S`, the step `S' ⊆ S` is spanned by the basis vectors of shuffle type in
`S'`. -/
theorem comap_mackeyFilt_eq_span (ν' ν₁ : I →₀ ℕ) (D C : FullChamber Γ ν) {S' S : Set (I → ℕ)}
    (h : S' ⊆ S) :
    (mackeyFilt k hP hD hZ hΓ hW hL ν' ν₁ D C S').comap
        (mackeyFilt k hP hD hZ hΓ hW hL ν' ν₁ D C S).subtype =
      Submodule.span k (mackeyFiltBasis hP hD hZ hΓ hW hL ν' ν₁ D C S ''
        {i | shuffleType ν' ν₁ i.1.1 ∈ S'}) := by
  refine Submodule.map_injective_of_injective
    (mackeyFilt k hP hD hZ hΓ hW hL ν' ν₁ D C S).injective_subtype ?_
  rw [Submodule.map_comap_eq, Submodule.range_subtype,
    inf_eq_right.2 (mackeyFilt_mono hP hD hZ hΓ hW hL ν' ν₁ D C h), Submodule.map_span,
    ← Set.image_comp]
  unfold mackeyFilt
  congr 1
  ext x
  simp only [Set.mem_range, Set.mem_image, Function.comp_apply,
    Submodule.subtype_apply]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨⟨i.1, h i.2⟩, i.2, mackeyFiltBasis_apply hP hD hZ hΓ hW hL ν' ν₁ D C S _⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i.1, hi⟩, (mackeyFiltBasis_apply hP hD hZ hΓ hW hL ν' ν₁ D C S _).symm⟩

variable (k) in
/-- **Subquotients of the Mackey filtration.** For `S' ⊆ S`, the quotient of the step `S` by
the step `S'` of the filtration of `e D * A * e C`. -/
abbrev MackeySubquotient (ν' ν₁ : I →₀ ℕ) (D C : FullChamber Γ ν) (S' S : Set (I → ℕ)) :=
  mackeyFilt k hP hD hZ hΓ hW hL ν' ν₁ D C S ⧸
    (mackeyFilt k hP hD hZ hΓ hW hL ν' ν₁ D C S').comap
      (mackeyFilt k hP hD hZ hΓ hW hL ν' ν₁ D C S).subtype

/-- **Bases of the subquotients of the Mackey filtration.** For `S' ⊆ S`, the quotient of the
step `S` by the step `S'` is free, with basis the classes of the elements `b(g, m)` of shuffle
type in `S` but not in `S'`. -/
noncomputable def mackeySubquotientBasis (ν' ν₁ : I →₀ ℕ) (D C : FullChamber Γ ν)
    {S' S : Set (I → ℕ)} (h : S' ⊆ S) :
    Module.Basis ({i | shuffleType ν' ν₁ i.1.1 ∈ S'}ᶜ :
        Set {i : ColPerm ν × (Strand ν →₀ ℕ) // shuffleType ν' ν₁ i.1 ∈ S}) k
      (MackeySubquotient k hP hD hZ hΓ hW hL ν' ν₁ D C S' S) :=
  ((mackeyFiltBasis hP hD hZ hΓ hW hL ν' ν₁ D C S).quotientSpanImage _).map
    (Submodule.quotEquivOfEq _ _ (comap_mackeyFilt_eq_span hP hD hZ hΓ hW hL ν' ν₁ D C h).symm)

theorem mackeySubquotientBasis_apply (ν' ν₁ : I →₀ ℕ) (D C : FullChamber Γ ν)
    {S' S : Set (I → ℕ)} (h : S' ⊆ S)
    (j : ({i | shuffleType ν' ν₁ i.1.1 ∈ S'}ᶜ :
        Set {i : ColPerm ν × (Strand ν →₀ ℕ) // shuffleType ν' ν₁ i.1 ∈ S})) :
    mackeySubquotientBasis hP hD hZ hΓ hW hL ν' ν₁ D C h j =
      Submodule.Quotient.mk (mackeyFiltBasis hP hD hZ hΓ hW hL ν' ν₁ D C S j.1) := by
  rw [mackeySubquotientBasis, Module.Basis.map_apply, Module.Basis.quotientSpanImage_apply]
  rfl

/-- **Only occurring shuffle types contribute.** If every shuffle type of `S` that occurs lies
in `S'`, the subquotient `S / S'` is zero; in particular the strict step of a shuffle type that
no relabelling has vanishes. -/
theorem subsingleton_mackeySubquotient (ν' ν₁ : I →₀ ℕ) (D C : FullChamber Γ ν)
    {S' S : Set (I → ℕ)} (h : S' ⊆ S) (hS : S ∩ Set.range (shuffleType (ν := ν) ν' ν₁) ⊆ S') :
    Subsingleton (MackeySubquotient k hP hD hZ hΓ hW hL ν' ν₁ D C S' S) := by
  have : IsEmpty ({i | shuffleType ν' ν₁ i.1.1 ∈ S'}ᶜ :
      Set {i : ColPerm ν × (Strand ν →₀ ℕ) // shuffleType ν' ν₁ i.1 ∈ S}) :=
    ⟨fun j => j.2 (hS ⟨j.1.2, j.1.1.1, rfl⟩)⟩
  exact (mackeySubquotientBasis hP hD hZ hΓ hW hL ν' ν₁ D C h).repr.toEquiv.subsingleton

end GalleryAlgebra

end Categorification.WeightedKLR

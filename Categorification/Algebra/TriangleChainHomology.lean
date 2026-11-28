/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DG.Derived.DimensionShift
import DG.Homotopy.Comparison

/-!
# Cohomology along a finite chain of distinguished triangles

A finite resolution `0 → M_N → ⋯ → M_1 → M_0 → X → 0` of a module gives, through its syzygies
`Ω_0 = X` and `0 → Ω_{i+1} → M_i → Ω_i → 0`, a chain of distinguished triangles
`Ω_{i+1} → M_i → Ω_i → Ω_{i+1}[1]` with `Ω_{N+1} = 0`. This file records such a chain in any
pretriangulated category (`TriangleChain`), its image under a triangulated functor
(`TriangleChain.map`), and the dévissage of cohomology in the derived category of a commutative
ring `R` along it:

* if every term `M_i` with `i ≥ a` has no cohomology, neither has `Ω_a`
  (`TriangleChain.isZero_homology_syz`);
* if every term except `M_{i₀}` has no cohomology, then `Hⁿ(X) ≅ H^{n + i₀}(M_{i₀})`
  (`TriangleChain.nonempty_linearEquiv_homology`).

This replaces the spectral sequence of a filtered complex whose `E²` page has a single nonzero
term, as in B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
§7.3, proof of Proposition 7.22, where the resolution of Proposition 7.8 is tensored with a
second such resolution.

## Main definitions and results

* `TriangleChain`, `TriangleChain.map`.
* `nonempty_linearEquiv_homology_obj₃_of_isZero_obj₂`,
  `nonempty_linearEquiv_homology_obj₂_of_isZero_obj₁`,
  `nonempty_linearEquiv_homology_obj₁_of_isZero_obj₃`: the three isomorphisms of the long exact
  sequence of a distinguished triangle with one acyclic vertex.
* `TriangleChain.isZero_homology_syz`, `TriangleChain.nonempty_linearEquiv_homology`.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

noncomputable section

namespace Categorification

universe w

/-- A finite chain of distinguished triangles `Ω_{i+1} → M_i → Ω_i → Ω_{i+1}[1]`, `i ≤ N`, with
`Ω_{N+1} = 0`: the triangles of the syzygies of a resolution of `Ω_0` of length `N` by the
terms `M_i`. -/
structure TriangleChain (C : Type*) [Category C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] where
  /-- The length `N` of the resolution. -/
  length : ℕ
  /-- The terms `M_i` of the resolution. -/
  term : ℕ → C
  /-- The syzygies `Ω_i`; `Ω_0` is the resolved object. -/
  syz : ℕ → C
  /-- The inclusion `Ω_{i+1} → M_i`. -/
  ι : ∀ i, syz (i + 1) ⟶ term i
  /-- The projection `M_i → Ω_i`. -/
  π : ∀ i, term i ⟶ syz i
  /-- The connecting morphism `Ω_i → Ω_{i+1}[1]`. -/
  δ : ∀ i, syz i ⟶ (syz (i + 1))⟦(1 : ℤ)⟧
  dist : ∀ i ≤ length, Triangle.mk (ι i) (π i) (δ i) ∈ distTriang C
  isZero_syz : IsZero (syz (length + 1))

namespace TriangleChain

variable {C D : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [Category D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- The image of a chain of distinguished triangles under a triangulated functor. -/
def map (c : TriangleChain C) (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] :
    TriangleChain D where
  length := c.length
  term i := F.obj (c.term i)
  syz i := F.obj (c.syz i)
  ι i := F.map (c.ι i)
  π i := F.map (c.π i)
  δ i := F.map (c.δ i) ≫ (F.commShiftIso (1 : ℤ)).hom.app (c.syz (i + 1))
  dist i hi := F.map_distinguished _ (c.dist i hi)
  isZero_syz := F.map_isZero c.isZero_syz

@[simp] theorem map_length (c : TriangleChain C) (F : C ⥤ D) [F.CommShift ℤ]
    [F.IsTriangulated] : (c.map F).length = c.length := rfl

@[simp] theorem map_term (c : TriangleChain C) (F : C ⥤ D) [F.CommShift ℤ]
    [F.IsTriangulated] (i : ℕ) : (c.map F).term i = F.obj (c.term i) := rfl

@[simp] theorem map_syz (c : TriangleChain C) (F : C ⥤ D) [F.CommShift ℤ]
    [F.IsTriangulated] (i : ℕ) : (c.map F).syz i = F.obj (c.syz i) := rfl

end TriangleChain

section Homology

open DG DG.DerivedCategory
open scoped DG.DegreeZero

variable {R : Type} [CommRing R] [HasDerivedCategory.{w, 0} R]

noncomputable local instance chainShiftSequence :
    (homologyFunctor (A := R) R 0).ShiftSequence ℤ := by
  letI : (DG.HomotopyCategory.homologyFunctor.{0} R R 0).ShiftSequence ℤ := by
    change (DG.HomotopyCategory.forget.{0} R R ⋙
      _root_.HomotopyCategory.homologyFunctor (ModuleCat.{0} R) (ComplexShape.up ℤ)
        0).ShiftSequence ℤ
    infer_instance
  exact Functor.ShiftSequence.induced (homologyFunctorFactorsh R 0) ℤ
    (homologyFunctor R) (homologyFunctorFactorsh R)

/-- In a distinguished triangle whose middle vertex is acyclic, the connecting morphism
`Hʲ(obj₃) → Hʲ⁺¹(obj₁)` is an isomorphism. -/
theorem nonempty_linearEquiv_homology_obj₃_of_isZero_obj₂
    (T : Triangle (DerivedCategory.{w, 0} R)) (hT : T ∈ distTriang _)
    (h₂ : ∀ j : ℤ, IsZero ((homologyFunctor R j).obj T.obj₂)) (j : ℤ) :
    Nonempty ((homologyFunctor R j).obj T.obj₃ ≃ₗ[R]
      (homologyFunctor R (j + 1)).obj T.obj₁) := by
  let G := homologyFunctor (A := R) R 0
  let φ := G.homologySequenceδ T j (j + 1) rfl
  have hmono : Mono φ :=
    (G.homologySequence_exact₃ T hT j (j + 1) rfl).mono_g ((h₂ j).eq_of_src _ _)
  have hepi : Epi φ :=
    (G.homologySequence_exact₁ T hT j (j + 1) rfl).epi_f ((h₂ (j + 1)).eq_of_tgt _ _)
  have : IsIso φ := isIso_of_mono_of_epi φ
  exact ⟨(asIso φ).toLinearEquiv⟩

/-- In a distinguished triangle whose first vertex is acyclic, the second morphism induces
isomorphisms `Hʲ(obj₂) ≅ Hʲ(obj₃)`. -/
theorem nonempty_linearEquiv_homology_obj₂_of_isZero_obj₁
    (T : Triangle (DerivedCategory.{w, 0} R)) (hT : T ∈ distTriang _)
    (h₁ : ∀ j : ℤ, IsZero ((homologyFunctor R j).obj T.obj₁)) (j : ℤ) :
    Nonempty ((homologyFunctor R j).obj T.obj₂ ≃ₗ[R]
      (homologyFunctor R j).obj T.obj₃) := by
  let G := homologyFunctor (A := R) R 0
  let φ := (G.shift j).map T.mor₂
  have hmono : Mono φ :=
    (G.homologySequence_exact₂ T hT j).mono_g ((h₁ j).eq_of_src _ _)
  have hepi : Epi φ :=
    (G.homologySequence_exact₃ T hT j (j + 1) rfl).epi_f ((h₁ (j + 1)).eq_of_tgt _ _)
  have : IsIso φ := isIso_of_mono_of_epi φ
  exact ⟨(asIso φ).toLinearEquiv⟩

/-- In a distinguished triangle whose third vertex is acyclic, the first morphism induces
isomorphisms `Hʲ(obj₁) ≅ Hʲ(obj₂)`. -/
theorem nonempty_linearEquiv_homology_obj₁_of_isZero_obj₃
    (T : Triangle (DerivedCategory.{w, 0} R)) (hT : T ∈ distTriang _)
    (h₃ : ∀ j : ℤ, IsZero ((homologyFunctor R j).obj T.obj₃)) (j : ℤ) :
    Nonempty ((homologyFunctor R j).obj T.obj₁ ≃ₗ[R]
      (homologyFunctor R j).obj T.obj₂) := by
  let G := homologyFunctor (A := R) R 0
  let φ := (G.shift j).map T.mor₁
  have hmono : Mono φ :=
    (G.homologySequence_exact₁ T hT (j - 1) j (by lia)).mono_g ((h₃ (j - 1)).eq_of_src _ _)
  have hepi : Epi φ :=
    (G.homologySequence_exact₂ T hT j).epi_f ((h₃ j).eq_of_tgt _ _)
  have : IsIso φ := isIso_of_mono_of_epi φ
  exact ⟨(asIso φ).toLinearEquiv⟩

namespace TriangleChain

variable (c : TriangleChain (DerivedCategory.{w, 0} R))

/-- **Vanishing along a chain**: if the terms `M_i`, `a ≤ i ≤ N`, have no cohomology, neither
has the syzygy `Ω_a`. -/
theorem isZero_homology_syz {a : ℕ} (ha : a ≤ c.length + 1)
    (h : ∀ i, a ≤ i → i ≤ c.length → ∀ n : ℤ, IsZero ((homologyFunctor R n).obj (c.term i)))
    (n : ℤ) :
    IsZero ((homologyFunctor R n).obj (c.syz a)) := by
  obtain ⟨d, hd⟩ : ∃ d, a + d = c.length + 1 := ⟨c.length + 1 - a, by lia⟩
  induction d generalizing a n with
  | zero =>
    simp only [add_zero] at hd
    subst hd
    exact (homologyFunctor R n).map_isZero c.isZero_syz
  | succ d ih =>
    have hal : a ≤ c.length := by lia
    have h₁ := fun n => ih (a := a + 1) (by lia) (fun i hi hil => h i (by lia) hil) n (by lia)
    let G := homologyFunctor (A := R) R 0
    let T := Triangle.mk (c.ι a) (c.π a) (c.δ a)
    exact (G.homologySequence_exact₃ T (c.dist a hal) n (n + 1) rfl).isZero_X₂
      ((h a le_rfl hal n).eq_of_src _ _) ((h₁ (n + 1)).eq_of_tgt _ _)

/-- Dimension shifting along the acyclic terms below `i`: `Hⁿ(Ω_0) ≅ H^{n+i}(Ω_i)`. -/
theorem nonempty_linearEquiv_homology_syz {i₀ : ℕ}
    (h : ∀ i, i < i₀ → ∀ n : ℤ, IsZero ((homologyFunctor R n).obj (c.term i)))
    (hi₀ : i₀ ≤ c.length) :
    ∀ i ≤ i₀, ∀ n m : ℤ, m = n + i →
      Nonempty ((homologyFunctor R n).obj (c.syz 0) ≃ₗ[R]
        (homologyFunctor R m).obj (c.syz i)) := by
  intro i hi
  induction i with
  | zero =>
    intro n m hm
    simp only [Nat.cast_zero, add_zero] at hm
    subst hm
    exact ⟨LinearEquiv.refl R _⟩
  | succ i ih =>
    intro n m hm
    obtain ⟨e₁⟩ := ih (by lia) n (n + i) rfl
    let T := Triangle.mk (c.ι i) (c.π i) (c.δ i)
    obtain ⟨e₂⟩ := nonempty_linearEquiv_homology_obj₃_of_isZero_obj₂ T (c.dist i (by lia))
      (h i (by lia)) (n + i)
    have hm' : n + i + 1 = m := by rw [hm]; push_cast; ring
    exact ⟨e₁.trans (hm' ▸ e₂)⟩

/-- **Dévissage along a chain with one non-acyclic term**: if every term except `M_{i₀}` has no
cohomology, then `Hⁿ(Ω_0) ≅ H^{n + i₀}(M_{i₀})` for every `n`. -/
theorem nonempty_linearEquiv_homology {i₀ : ℕ} (hi₀ : i₀ ≤ c.length)
    (h : ∀ i ≤ c.length, i ≠ i₀ → ∀ n : ℤ, IsZero ((homologyFunctor R n).obj (c.term i)))
    (n : ℤ) :
    Nonempty ((homologyFunctor R n).obj (c.syz 0) ≃ₗ[R]
      (homologyFunctor R (n + i₀)).obj (c.term i₀)) := by
  obtain ⟨e₁⟩ := c.nonempty_linearEquiv_homology_syz (i₀ := i₀)
    (fun i hi => h i (by lia) (by lia)) hi₀ i₀ le_rfl n (n + i₀) rfl
  have hz := c.isZero_homology_syz (a := i₀ + 1) (by lia)
    (fun i hi hil => h i hil (by lia))
  let T := Triangle.mk (c.ι i₀) (c.π i₀) (c.δ i₀)
  obtain ⟨e₂⟩ := nonempty_linearEquiv_homology_obj₂_of_isZero_obj₁ T (c.dist i₀ hi₀) hz
    (n + i₀)
  exact ⟨e₁.trans e₂.symm⟩

/-- Concentration along a chain: if every term except `M_{i₀}` has no cohomology and `M_{i₀}`
has cohomology only in degree `d`, then `Ω_0` has cohomology only in degree `d - i₀`. -/
theorem isZero_homology_of_concentrated {i₀ : ℕ} (hi₀ : i₀ ≤ c.length)
    (h : ∀ i ≤ c.length, i ≠ i₀ → ∀ n : ℤ, IsZero ((homologyFunctor R n).obj (c.term i)))
    {d : ℤ}
    (hd : ∀ n : ℤ, n ≠ d → IsZero ((homologyFunctor R n).obj (c.term i₀))) (n : ℤ)
    (hn : n ≠ d - i₀) :
    IsZero ((homologyFunctor R n).obj (c.syz 0)) := by
  obtain ⟨e⟩ := c.nonempty_linearEquiv_homology hi₀ h n
  exact (hd (n + i₀) (by lia)).of_iso (LinearEquiv.toModuleIso e)

end TriangleChain

end Homology

end Categorification

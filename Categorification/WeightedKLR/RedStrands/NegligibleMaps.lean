/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Group.Subgroup.Lattice

/-!
# Morphisms factoring through central natural endomorphisms

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29. The diagrams of
the double tensor product act through the cyclotomic action of an enlarged
Cartan datum. There the red dots, whose colours occur once, act by central
natural endomorphisms, and the projection to the tensor product algebra kills
them. A morphism is negligible for a set `E` of natural endomorphisms of the
identity if it is a sum of morphisms of the form `h ≫ η.app N`, `η ∈ E`.
Negligible morphisms form an ideal for composition, additive functors that
intertwine the endomorphisms preserve them, and functors killing the
endomorphisms kill them.
-/

namespace Categorification.Stendhal

open CategoryTheory

universe v₁ v₂ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] [Preadditive 𝒞]
  {𝒟 : Type u₂} [Category.{v₂} 𝒟] [Preadditive 𝒟]

/-- Morphisms `M ⟶ N` that are sums of morphisms factoring through `η.app N`
for some `η ∈ E`. -/
def negligible (E : Set (𝟭 𝒞 ⟶ 𝟭 𝒞)) (M N : 𝒞) : AddSubgroup (M ⟶ N) :=
  AddSubgroup.closure {g | ∃ η ∈ E, ∃ h : M ⟶ N, g = h ≫ η.app N}

variable {E : Set (𝟭 𝒞 ⟶ 𝟭 𝒞)}

theorem comp_mem_negligible (η : 𝟭 𝒞 ⟶ 𝟭 𝒞) (hη : η ∈ E) {M N : 𝒞} (h : M ⟶ N) :
    h ≫ η.app N ∈ negligible E M N :=
  AddSubgroup.subset_closure ⟨η, hη, h, rfl⟩

/-- Negligible morphisms are closed under precomposition. -/
theorem negligible_comp_left {L M N : 𝒞} (g : L ⟶ M) {f : M ⟶ N}
    (hf : f ∈ negligible E M N) : g ≫ f ∈ negligible E L N := by
  induction hf using AddSubgroup.closure_induction with
  | mem f hf =>
    obtain ⟨η, hη, h, rfl⟩ := hf
    rw [← Category.assoc]
    exact comp_mem_negligible η hη _
  | zero => simp
  | add f f' _ _ hf hf' => simpa using (negligible E L N).add_mem hf hf'
  | neg f _ hf => simpa using (negligible E L N).neg_mem hf

/-- Negligible morphisms are closed under postcomposition. -/
theorem negligible_comp_right {L M N : 𝒞} {f : L ⟶ M} (g : M ⟶ N)
    (hf : f ∈ negligible E L M) : f ≫ g ∈ negligible E L N := by
  induction hf using AddSubgroup.closure_induction with
  | mem f hf =>
    obtain ⟨η, hη, h, rfl⟩ := hf
    have hn : η.app M ≫ g = g ≫ η.app N := (η.naturality g).symm
    rw [Category.assoc, hn, ← Category.assoc]
    exact comp_mem_negligible η hη _
  | zero => simp
  | add f f' _ _ hf hf' => simpa using (negligible E L N).add_mem hf hf'
  | neg f _ hf => simpa using (negligible E L N).neg_mem hf

/-- An additive functor carrying each endomorphism in `E` to one in `E'`
carries negligible morphisms to negligible morphisms. -/
theorem map_mem_negligible {E' : Set (𝟭 𝒟 ⟶ 𝟭 𝒟)} (F : 𝒞 ⥤ 𝒟) [F.Additive]
    (hF : ∀ η ∈ E, ∃ η' ∈ E', ∀ N, F.map (η.app N) = η'.app (F.obj N))
    {M N : 𝒞} {f : M ⟶ N} (hf : f ∈ negligible E M N) :
    F.map f ∈ negligible E' (F.obj M) (F.obj N) := by
  induction hf using AddSubgroup.closure_induction with
  | mem f hf =>
    obtain ⟨η, hη, h, rfl⟩ := hf
    obtain ⟨η', hη', he⟩ := hF η hη
    rw [F.map_comp, he]
    exact comp_mem_negligible η' hη' _
  | zero => simp
  | add f f' _ _ hf hf' => simpa using (negligible E' _ _).add_mem hf hf'
  | neg f _ hf => simpa using (negligible E' _ _).neg_mem hf

/-- An additive functor killing every endomorphism in `E` kills every
negligible morphism. -/
theorem map_eq_zero_of_mem_negligible (F : 𝒞 ⥤ 𝒟) [F.Additive]
    (hF : ∀ η ∈ E, ∀ N, F.map (η.app N) = 0)
    {M N : 𝒞} {f : M ⟶ N} (hf : f ∈ negligible E M N) : F.map f = 0 := by
  induction hf using AddSubgroup.closure_induction with
  | mem f hf =>
    obtain ⟨η, hη, h, rfl⟩ := hf
    rw [F.map_comp, hF η hη, Limits.comp_zero]
  | zero => exact F.map_zero _ _
  | add f f' _ _ hf hf' => rw [F.map_add, hf, hf', add_zero]
  | neg f _ hf => rw [F.map_neg, hf, neg_zero]

/-- Conjugating by isomorphisms preserves negligibility. -/
theorem negligible_conj {M M' N N' : 𝒞} (eM : M' ≅ M) (eN : N ≅ N') {f : M ⟶ N}
    (hf : f ∈ negligible E M N) : eM.hom ≫ f ≫ eN.hom ∈ negligible E M' N' :=
  negligible_comp_left _ (negligible_comp_right _ hf)

end Categorification.Stendhal

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KLR.MatEnd

/-!
# Matrices of morphisms along a functor and an injective reindexing

Let `F : C ⥤ D` be a `k`-linear functor, `X : ι → C` and `Y : κ → D` finite families, and
`e : ι → κ` injective with `F (X i) = Y (e i)`. Applying `F` entrywise and placing the entry
`(i, j)` at `(e i, e j)` gives a map `MatEnd X → MatEnd Y`. It is additive, `k`-linear and
multiplicative, and sends `1` to the idempotent `∑ i, single (e i) (e i) 𝟙`, so it is a
homomorphism of non-unital `k`-algebras (`MatEnd.mapEmb`).

This is the matrix form of a functor sending a finite sum of objects onto a summand of a
finite sum of objects, used for the action of `Fᵢ` on all-down boundaries in Webster,
*Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5, Proposition 5.3.
-/

noncomputable section

namespace Categorification.KLR.Diagram

open CategoryTheory Preadditive

namespace MatEnd

variable (k : Type*) [CommRing k] {C : Type*} [Category C] [Preadditive C] [Linear k C]
  {D : Type*} [Category D] [Preadditive D] [Linear k D]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {X : ι → C} {Y : κ → D} (F : C ⥤ D) [F.Additive] [F.Linear k] {e : ι → κ}
  (he : Function.Injective e) (h : ∀ i, F.obj (X i) = Y (e i))

/-- Transport of a morphism `X i ⟶ X j` along `F` to `Y (e i) ⟶ Y (e j)`. -/
def conjF {i j : ι} (f : X i ⟶ X j) : Y (e i) ⟶ Y (e j) :=
  eqToHom (h i).symm ≫ F.map f ≫ eqToHom (h j)

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [F.Additive] [Linear k C]
  [Linear k D] [Preadditive C] [Preadditive D] in
theorem conjF_comp {i j l : ι} (f : X i ⟶ X j) (g : X j ⟶ X l) :
    conjF F h (f ≫ g) = conjF F h f ≫ conjF F h g := by
  simp [conjF]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Linear k C] [Linear k D] in
theorem conjF_zero {i j : ι} : conjF F h (0 : X i ⟶ X j) = 0 := by
  simp [conjF]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Linear k C] [Linear k D] in
theorem conjF_add {i j : ι} (f g : X i ⟶ X j) :
    conjF F h (f + g) = conjF F h f + conjF F h g := by
  simp [conjF]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [F.Additive] in
theorem conjF_smul {i j : ι} (r : k) (f : X i ⟶ X j) :
    conjF F h (r • f) = r • conjF F h f := by
  simp [conjF, F.map_smul]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [F.Additive] [Linear k C]
  [Linear k D] [Preadditive C] [Preadditive D] in
theorem conjF_id (i : ι) : conjF F h (𝟙 (X i)) = 𝟙 _ := by
  simp [conjF]

variable {k} in
/-- Entrywise application of `F`, with the entry `(i, j)` placed at `(e i, e j)`. -/
def mapEmb (f : MatEnd X) : MatEnd Y :=
  ∑ i, ∑ j, single (e i) (e j) (conjF F h (f i j))

omit [Linear k C] [Linear k D] [F.Linear k] in
theorem mapEmb_add (f g : MatEnd X) : mapEmb F h (f + g) = mapEmb F h f + mapEmb F h g := by
  simp only [mapEmb, add_apply, conjF_add, single_add, Finset.sum_add_distrib]

omit [F.Additive] in
theorem mapEmb_smul (r : k) (f : MatEnd X) : mapEmb F h (r • f) = r • mapEmb F h f := by
  simp only [mapEmb, smul_apply, conjF_smul, single_smul, Finset.smul_sum]

omit [Linear k C] [Linear k D] [F.Linear k] in
theorem mapEmb_zero : mapEmb F h (0 : MatEnd X) = 0 := by
  simp [mapEmb, conjF_zero]

omit [Linear k C] [Linear k D] [F.Linear k] in
theorem mapEmb_single (i j : ι) (f : X i ⟶ X j) :
    mapEmb F h (single i j f) = single (e i) (e j) (conjF F h f) := by
  rw [mapEmb, Finset.sum_eq_single i, Finset.sum_eq_single j]
  · rw [single_apply_self]
  · intro j' _ hj'
    rw [single_apply_of_ne _ (fun h' => hj' h'.2), conjF_zero, single_zero]
  · simp
  · intro i' _ hi'
    exact Finset.sum_eq_zero fun j' _ => by
      rw [single_apply_of_ne _ (fun h' => hi' h'.1), conjF_zero, single_zero]
  · simp

omit [Linear k C] [Linear k D] [F.Linear k] in
theorem mapEmb_one : mapEmb F h (1 : MatEnd X) = ∑ i, single (e i) (e i) (𝟙 _) := by
  let m : MatEnd X →+ MatEnd Y := ⟨⟨mapEmb F h, mapEmb_zero F h⟩, mapEmb_add F h⟩
  change m 1 = _
  rw [one_eq_sum_single, map_sum]
  exact Finset.sum_congr rfl fun i _ => by
    change mapEmb F h _ = _
    rw [mapEmb_single, conjF_id]

include he in
omit [Linear k C] [Linear k D] [F.Linear k] in
private theorem mapEmb_single_mul_single (i j j' l : ι) (f : X i ⟶ X j) (g : X j' ⟶ X l) :
    mapEmb F h (single j' l g * single i j f) =
      mapEmb F h (single j' l g) * mapEmb F h (single i j f) := by
  rw [mapEmb_single, mapEmb_single]
  by_cases hj : j = j'
  · subst hj
    rw [single_mul_single, single_mul_single, mapEmb_single, conjF_comp]
  · rw [single_mul_single_of_ne _ _ hj, single_mul_single_of_ne _ _ (he.ne hj), mapEmb_zero]

include he in
omit [Linear k C] [Linear k D] [F.Linear k] in
theorem mapEmb_mul (f g : MatEnd X) : mapEmb F h (f * g) = mapEmb F h f * mapEmb F h g := by
  let m : MatEnd X →+ MatEnd Y := ⟨⟨mapEmb F h, mapEmb_zero F h⟩, mapEmb_add F h⟩
  change m (f * g) = m f * m g
  rw [eq_sum_single f, eq_sum_single g]
  simp only [Finset.sum_mul, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j' _ => ?_
  exact mapEmb_single_mul_single F he h _ _ _ _ _ _

/-- Entrywise application of `F` along `e`, as a homomorphism of non-unital `k`-algebras. -/
def mapEmbHom : MatEnd X →ₙₐ[k] MatEnd Y where
  toFun := mapEmb F h
  map_smul' := mapEmb_smul k F h
  map_zero' := mapEmb_zero F h
  map_add' := mapEmb_add F h
  map_mul' := mapEmb_mul F he h

include he in
omit [Linear k C] [Linear k D] [F.Linear k] [Preadditive C] [DecidableEq ι] [F.Additive] in
theorem mapEmb_apply_emb (f : MatEnd X) (i j : ι) :
    mapEmb F h f (e i) (e j) = conjF F h (f i j) := by
  rw [mapEmb, sum_apply, Finset.sum_eq_single i, sum_apply, Finset.sum_eq_single j,
    single_apply_self]
  · intro j' _ hj'
    exact single_apply_of_ne _ (fun h' => hj' (he h'.2.symm))
  · simp
  · intro i' _ hi'
    rw [sum_apply]
    exact Finset.sum_eq_zero fun j' _ => single_apply_of_ne _ (fun h' => hi' (he h'.1.symm))
  · simp

omit [Linear k C] [Linear k D] [F.Linear k] [Preadditive C] [DecidableEq ι] [F.Additive] in
theorem mapEmb_apply_of_left {a : κ} (ha : ∀ i, e i ≠ a) (f : MatEnd X) (b : κ) :
    mapEmb F h f a b = 0 := by
  rw [mapEmb, sum_apply]
  exact Finset.sum_eq_zero fun i _ => by
    rw [sum_apply]
    exact Finset.sum_eq_zero fun j _ => single_apply_of_ne _ (fun h' => ha i h'.1.symm)

omit [Linear k C] [Linear k D] [F.Linear k] [Preadditive C] [DecidableEq ι] [F.Additive] in
theorem mapEmb_apply_of_right {b : κ} (hb : ∀ j, e j ≠ b) (f : MatEnd X) (a : κ) :
    mapEmb F h f a b = 0 := by
  rw [mapEmb, sum_apply]
  exact Finset.sum_eq_zero fun i _ => by
    rw [sum_apply]
    exact Finset.sum_eq_zero fun j _ => single_apply_of_ne _ (fun h' => hb j h'.2.symm)

include he in
omit [Linear k C] [Linear k D] [F.Linear k] in
/-- Right multiplication by the image of `1` keeps the rows indexed by the image of `e`. -/
theorem mul_mapEmb_one_apply_emb (g : MatEnd Y) (i : ι) (b : κ) :
    (g * mapEmb F h 1) (e i) b = g (e i) b := by
  rw [mul_apply, Finset.sum_eq_single (e i)]
  · rw [mapEmb_apply_emb F he h, one_apply_self, conjF_id, Category.id_comp]
  · intro c _ hc
    by_cases hc' : ∃ j, e j = c
    · obtain ⟨j, rfl⟩ := hc'
      rw [mapEmb_apply_emb F he h, one_apply_of_ne (fun h' => hc (congrArg e h').symm),
        conjF_zero, Limits.zero_comp]
    · rw [mapEmb_apply_of_right F h (fun j hj => hc' ⟨j, hj⟩), Limits.zero_comp]
  · simp

omit [Linear k C] [Linear k D] [F.Linear k] [F.Additive] in
/-- Right multiplication by the image of `1` kills the rows outside the image of `e`. -/
theorem mul_mapEmb_one_apply_of_left (g : MatEnd Y) {a : κ} (ha : ∀ i, e i ≠ a) (b : κ) :
    (g * mapEmb F h 1) a b = 0 := by
  rw [mul_apply]
  exact Finset.sum_eq_zero fun c _ => by
    rw [mapEmb_apply_of_left F h ha, Limits.zero_comp]

end MatEnd

end Categorification.KLR.Diagram

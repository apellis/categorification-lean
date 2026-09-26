/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The endomorphism algebra of a finite direct sum, as matrices

For a `k`-linear category `C` and a finite family of objects `X : ι → C`, `MatEnd X` is the
`k`-algebra `⨁_{i, j} Hom(X i, X j)` of matrices of morphisms, with multiplication given by
composition: `(f * g) i l = ∑ j, g i j ≫ f j l` (so `f * g` is "`g` first, then `f`", as for
`CategoryTheory.End`). It is the endomorphism algebra of the biproduct `⨁ i, X i`, without
requiring biproducts to exist in `C`.

## Main definitions

* `MatEnd X` with its `Ring` and `Algebra k` structures.
* `MatEnd.single i j f`: the matrix with the single nonzero entry `f : X i ⟶ X j`;
  `single_mul_single`, `single_mul_single_of_ne`, `one_eq_sum_single`, `eq_sum_single`.
-/

noncomputable section

namespace Categorification.KLR.Diagram

open CategoryTheory Preadditive

variable (k : Type*) [CommRing k] {C : Type*} [Category C] [Preadditive C] [Linear k C]
  {ι : Type*}

/-- Matrices of morphisms between the members of a finite family of objects. -/
@[nolint unusedArguments]
def MatEnd (_X : ι → C) : Type _ := ∀ i j : ι, _X i ⟶ _X j

namespace MatEnd

variable {k} {X : ι → C}

instance : AddCommGroup (MatEnd X) := inferInstanceAs (AddCommGroup (∀ i j : ι, X i ⟶ X j))
instance : Module k (MatEnd X) := inferInstanceAs (Module k (∀ i j : ι, X i ⟶ X j))

instance : CoeFun (MatEnd X) (fun _ => ∀ i j : ι, X i ⟶ X j) := ⟨id⟩

omit [Preadditive C] in
@[ext] theorem ext {f g : MatEnd X} (h : ∀ i j, f i j = g i j) : f = g := funext fun i =>
  funext fun j => h i j

@[simp] theorem add_apply (f g : MatEnd X) (i j : ι) : (f + g) i j = f i j + g i j := rfl
@[simp] theorem sub_apply (f g : MatEnd X) (i j : ι) : (f - g) i j = f i j - g i j := rfl
@[simp] theorem neg_apply (f : MatEnd X) (i j : ι) : (-f) i j = -f i j := rfl
@[simp] theorem zero_apply (i j : ι) : (0 : MatEnd X) i j = 0 := rfl
@[simp] theorem smul_apply (r : k) (f : MatEnd X) (i j : ι) : (r • f) i j = r • f i j := rfl

theorem sum_apply {α : Type*} (s : Finset α) (f : α → MatEnd X) (i j : ι) :
    (∑ a ∈ s, f a) i j = ∑ a ∈ s, f a i j := by
  induction s using Finset.cons_induction with
  | empty => rfl
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, add_apply, ih]

variable [Fintype ι] [DecidableEq ι]

instance : Mul (MatEnd X) := ⟨fun f g i l => ∑ j, g i j ≫ f j l⟩

instance : One (MatEnd X) := ⟨fun i j => if h : i = j then eqToHom (congrArg X h) else 0⟩

omit [DecidableEq ι] in
theorem mul_apply (f g : MatEnd X) (i l : ι) : (f * g) i l = ∑ j, g i j ≫ f j l := rfl

omit [Fintype ι] in
theorem one_apply (i j : ι) :
    (1 : MatEnd X) i j = if h : i = j then eqToHom (congrArg X h) else 0 := rfl

omit [Fintype ι] in
@[simp] theorem one_apply_self (i : ι) : (1 : MatEnd X) i i = 𝟙 _ := by simp [one_apply]

omit [Fintype ι] in
theorem one_apply_of_ne {i j : ι} (h : i ≠ j) : (1 : MatEnd X) i j = 0 := by
  simp [one_apply, h]

omit [DecidableEq ι] in
private theorem mul_assoc' (f g h : MatEnd X) : f * g * h = f * (g * h) := by
  ext i l
  simp only [mul_apply, comp_sum, sum_comp, Category.assoc]
  exact Finset.sum_comm

private theorem one_mul' (f : MatEnd X) : 1 * f = f := by
  ext i l
  simp only [mul_apply, one_apply, comp_dite, Limits.comp_zero]
  rw [Finset.sum_dite_eq' Finset.univ l]
  simp

private theorem mul_one' (f : MatEnd X) : f * 1 = f := by
  ext i l
  simp only [mul_apply, one_apply, dite_comp, Limits.zero_comp]
  rw [Finset.sum_dite_eq Finset.univ i]
  simp

instance : Ring (MatEnd X) :=
  { (inferInstance : AddCommGroup (MatEnd X)) with
    mul := (· * ·)
    one := 1
    mul_assoc := mul_assoc'
    one_mul := one_mul'
    mul_one := mul_one'
    left_distrib := fun f g h => by
      ext i l; simp only [mul_apply, add_apply, add_comp, Finset.sum_add_distrib]
    right_distrib := fun f g h => by
      ext i l; simp only [mul_apply, add_apply, comp_add, Finset.sum_add_distrib]
    zero_mul := fun f => by ext i l; simp [mul_apply]
    mul_zero := fun f => by ext i l; simp [mul_apply] }

instance : Algebra k (MatEnd X) :=
  Algebra.ofModule
    (fun r f g => by
      ext i l; simp only [mul_apply, smul_apply, Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => Linear.comp_smul _ _ _ _ _ _)
    (fun r f g => by
      ext i l; simp only [mul_apply, smul_apply, Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => Linear.smul_comp _ _ _ _ _ _)

/-! ### Matrix units -/

/-- The matrix whose only nonzero entry is `f : X i ⟶ X j`, at `(i, j)`. -/
def single (i j : ι) (f : X i ⟶ X j) : MatEnd X := fun i' j' =>
  if h : i' = i ∧ j' = j then eqToHom (congrArg X h.1) ≫ f ≫ eqToHom (congrArg X h.2.symm)
  else 0

omit [Fintype ι] in
@[simp] theorem single_apply_self (i j : ι) (f : X i ⟶ X j) :
    single i j f i j = f := by
  simp [single]

omit [Fintype ι] in
theorem single_apply_of_ne {i j i' j' : ι} (f : X i ⟶ X j) (h : ¬ (i' = i ∧ j' = j)) :
    single i j f i' j' = 0 := by
  simp [single, h]

omit [Fintype ι] in
theorem single_apply (i j : ι) (f : X i ⟶ X j) (i' j' : ι) :
    single i j f i' j' = if h : i' = i ∧ j' = j then
      eqToHom (congrArg X h.1) ≫ f ≫ eqToHom (congrArg X h.2.symm) else 0 := rfl

@[simp] theorem single_zero (i j : ι) : single i j (0 : X i ⟶ X j) = 0 := by
  ext i' j'; simp [single_apply]

theorem single_add (i j : ι) (f g : X i ⟶ X j) :
    single i j (f + g) = single i j f + single i j g := by
  ext i' j'; simp only [single_apply, add_apply]; split_ifs <;> simp

theorem single_sub (i j : ι) (f g : X i ⟶ X j) :
    single i j (f - g) = single i j f - single i j g := by
  ext i' j'; simp only [single_apply, sub_apply]; split_ifs <;> simp

omit [Fintype ι] in
theorem single_neg (i j : ι) (f : X i ⟶ X j) :
    single i j (-f) = -single i j f := by
  ext i' j'; simp only [single_apply, neg_apply]; split_ifs <;> simp

theorem single_smul (i j : ι) (r : k) (f : X i ⟶ X j) :
    single i j (r • f) = r • single i j f := by
  ext i' j'; simp only [single_apply, smul_apply]; split_ifs <;> simp

theorem single_sum {α : Type*} (s : Finset α) (i j : ι) (f : α → (X i ⟶ X j)) :
    single i j (∑ a ∈ s, f a) = ∑ a ∈ s, single i j (f a) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, single_add, ih]

/-- The matrix unit `single i j` as a linear map. -/
def singleₗ (k : Type*) [CommRing k] [Linear k C] (i j : ι) : (X i ⟶ X j) →ₗ[k] MatEnd X where
  toFun := single i j
  map_add' := single_add i j
  map_smul' r f := single_smul i j r f

@[simp] theorem singleₗ_apply (i j : ι) (f : X i ⟶ X j) :
    singleₗ k i j f = single i j f := rfl

theorem single_mul_single (i j l : ι) (f : X i ⟶ X j) (g : X j ⟶ X l) :
    single j l g * single i j f = single i l (f ≫ g) := by
  ext i' l'
  rw [mul_apply]
  by_cases hi : i' = i
  · subst hi
    by_cases hl : l' = l
    · subst hl
      rw [Finset.sum_eq_single j]
      · simp
      · intro j' _ hj'; rw [single_apply_of_ne _ (fun h => hj' h.2), Limits.zero_comp]
      · simp
    · rw [single_apply_of_ne _ (fun h => hl h.2)]
      exact Finset.sum_eq_zero fun j' _ => by
        rw [single_apply_of_ne (i' := j') (j' := l') g (fun h => hl h.2), Limits.comp_zero]
  · rw [single_apply_of_ne _ (fun h => hi h.1)]
    exact Finset.sum_eq_zero fun j' _ => by
      rw [single_apply_of_ne (i' := i') f (fun h => hi h.1), Limits.zero_comp]

theorem single_mul_single_of_ne {i j j' l : ι} (f : X i ⟶ X j) (g : X j' ⟶ X l) (h : j ≠ j') :
    single j' l g * single i j f = 0 := by
  ext i' l'
  rw [mul_apply, zero_apply]
  refine Finset.sum_eq_zero fun m _ => ?_
  by_cases hm : m = j
  · subst hm; rw [single_apply_of_ne (i' := m) g (fun h' => h h'.1), Limits.comp_zero]
  · rw [single_apply_of_ne (j' := m) f (fun h' => hm h'.2), Limits.zero_comp]

omit [Fintype ι] in
theorem single_eqToHom {i j j' : ι} (f : X i ⟶ X j) (h : j = j') :
    single i j' (f ≫ eqToHom (congrArg X h)) = single i j f := by
  subst h; simp

omit [Fintype ι] in
theorem single_eqToHom_left {i i' j : ι} (f : X i ⟶ X j) (h : i' = i) :
    single i' j (eqToHom (congrArg X h) ≫ f) = single i j f := by
  subst h; simp

theorem one_eq_sum_single : (1 : MatEnd X) = ∑ i, single i i (𝟙 (X i)) := by
  ext i j
  rw [sum_apply, Finset.sum_eq_single i]
  · by_cases h : i = j
    · subst h; simp
    · rw [one_apply_of_ne h, single_apply_of_ne _ (fun h' => h h'.2.symm)]
  · intro b _ hb; exact single_apply_of_ne _ (fun h => hb h.1.symm)
  · simp

theorem eq_sum_single (f : MatEnd X) : f = ∑ i, ∑ j, single i j (f i j) := by
  ext i' j'
  rw [sum_apply, Finset.sum_eq_single i', sum_apply, Finset.sum_eq_single j']
  · simp
  · intro b _ hb; exact single_apply_of_ne _ (fun h => hb h.2.symm)
  · simp
  · intro b _ hb
    rw [sum_apply]
    exact Finset.sum_eq_zero fun c _ => single_apply_of_ne _ (fun h => hb h.1.symm)
  · simp

end MatEnd

end Categorification.KLR.Diagram

end

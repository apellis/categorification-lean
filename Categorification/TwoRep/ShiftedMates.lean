/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.GradedHomAdjunction

/-!
# Shifted mates of endomorphisms

For an explicit adjunction `u ⊣ v`, close a shifted endomorphism of `u` with the counit,
then apply the shifted adjunction bijection. This defines the shifted endomorphism of `v`
needed to transport upward dots to downward dots. The degree is unchanged; vertical
composition is reversed, with the degree equality explicitly commuted.

The proofs use ordinary conjugate mates in the actual finite-sum graded-Hom bicategory.
The adjunction is an explicit input; no new adjunction, boundedness, low-weight foothold,
or cyclicity theorem is asserted.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Bicategory

universe w v u

private theorem conjugate_eq_close {D : Type*} [Bicategory D] {a b : D}
    {u : a ⟶ b} {v : b ⟶ a} (adj : u ⊣ v) (f : u ⟶ u) :
    Θ₀ adj (v ◁ f ≫ adj.counit) ≫ (λ_ v).hom =
      Bicategory.conjugateEquiv adj adj f := by
  rw [Bicategory.conjugateEquiv_apply']
  dsimp only [Θ₀]
  bicategory

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [GradedBicategory.ShiftCoherence B]

open GradedHomBicat

variable {a b : B} {u : a ⟶ b} {v : b ⟶ a} (adj : u ⊣ v)

/-- Close a shifted endomorphism of the left adjoint with the counit. -/
def εsh {d : ℤ} (f : ShiftedHom u u d) : ShiftedHom (v ≫ u) (𝟙 b) d :=
  (shWhiskerLeft v f).comp (ShiftedHom.mk₀ (0 : ℤ) rfl adj.counit) (zero_add d)

/-- The degree-preserving right mate under the given adjunction. -/
def mateSh {d : ℤ} (f : ShiftedHom u u d) : ShiftedHom v v d :=
  (Θsh adj (εsh adj f)).comp (ShiftedHom.mk₀ (0 : ℤ) rfl (λ_ v).hom) (zero_add d)

/-- The construction is precisely the published cap-to-endomorphism bijection. -/
theorem mateSh_eq_shiftedEndEquiv {d : ℤ} (f : ShiftedHom u u d) :
    mateSh adj f = shiftedEndEquiv adj d (εsh adj f) := by
  simp [mateSh, shiftedEndEquiv, shiftedHomEquiv, ShiftedHom.comp_mk₀,
    Iso.homCongr]

/-- Homogeneous inclusion identifies the construction with ordinary conjugate mates. -/
theorem of₂_mateSh {d : ℤ} (f : ShiftedHom u u d) :
    of₂ d (mateSh adj f) =
      Bicategory.conjugateEquiv (mapAdjunction adj) (mapAdjunction adj) (of₂ d f) := by
  rw [mateSh, ← of₂_comp_of₂, of₂_Θsh, εsh, ← of₂_comp_of₂,
    ← incl₂_eq_of₂, ← incl₂_eq_of₂, ← whiskerLeft_of₂, ← leftUnitor_hom_eq]
  exact conjugate_eq_close (mapAdjunction adj) (of₂ d f)

/-- Identity is preserved (the identity has degree zero). -/
@[simp] theorem mateSh_mk₀_id :
    mateSh adj (ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 u)) =
      ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 v) := by
  apply of₂_injective 0
  rw [of₂_mateSh, ← incl₂_eq_of₂, ← incl₂_eq_of₂, incl₂_id, incl₂_id,
    Bicategory.conjugateEquiv_id]

/-- Mates reverse composition. `f.comp g` has degree `e + d`, whereas the reversed
composition has degree `d + e`, so its degree witness is commuted explicitly. -/
theorem mateSh_comp {d e s : ℤ} (f : ShiftedHom u u d) (g : ShiftedHom u u e)
    (h : e + d = s) :
    mateSh adj (f.comp g h) =
      (mateSh adj g).comp (mateSh adj f) ((add_comm d e).trans h) := by
  apply of₂_injective s
  rw [of₂_mateSh, ← of₂_comp_of₂, ← of₂_comp_of₂, of₂_mateSh, of₂_mateSh,
    Bicategory.conjugateEquiv_comp]

section Additive

omit [GradedBicategory.ShiftCoherence B]

/-- The mate is additive in every integer degree. -/
theorem mateSh_add {d : ℤ} (f g : ShiftedHom u u d) :
    mateSh adj (f + g) = mateSh adj f + mateSh adj g := by
  have hL : shWhiskerLeft v (f + g) = shWhiskerLeft v f + shWhiskerLeft v g :=
    ShiftedHom.map_add f g (precomp b v)
  have hε : εsh adj (f + g) = εsh adj f + εsh adj g := by
    unfold εsh
    rw [hL, ShiftedHom.add_comp]
  have hR : shWhiskerRight (εsh adj f + εsh adj g) v =
      shWhiskerRight (εsh adj f) v + shWhiskerRight (εsh adj g) v :=
    ShiftedHom.map_add (εsh adj f) (εsh adj g) (postcomp b v)
  unfold mateSh
  rw [hε]
  unfold Θsh
  rw [hR, ShiftedHom.comp_add, ShiftedHom.add_comp]

/-- Mates form an additive map degree by degree. -/
def mateShAddHom (d : ℤ) : ShiftedHom u u d →+ ShiftedHom v v d :=
  AddMonoidHom.mk' (mateSh adj) (mateSh_add adj)

@[simp] theorem mateSh_zero (d : ℤ) : mateSh adj (0 : ShiftedHom u u d) = 0 :=
  (mateShAddHom adj d).map_zero

@[simp] theorem mateSh_neg {d : ℤ} (f : ShiftedHom u u d) :
    mateSh adj (-f) = -mateSh adj f :=
  (mateShAddHom adj d).map_neg f

theorem mateSh_sub {d : ℤ} (f g : ShiftedHom u u d) :
    mateSh adj (f - g) = mateSh adj f - mateSh adj g :=
  (mateShAddHom adj d).map_sub f g

end Additive

/-- A nonzero homogeneous endomorphism has a nonzero mate; no finiteness is needed. -/
theorem mateSh_injective (d : ℤ) :
    Function.Injective (mateSh adj : ShiftedHom u u d → ShiftedHom v v d) := by
  intro f g h
  apply of₂_injective d
  apply (Bicategory.conjugateEquiv (mapAdjunction adj) (mapAdjunction adj)).injective
  rw [← of₂_mateSh, ← of₂_mateSh, h]

@[simp] theorem mateSh_eq_zero_iff {d : ℤ} (f : ShiftedHom u u d) :
    mateSh adj f = 0 ↔ f = 0 := by
  rw [← mateSh_zero adj d, (mateSh_injective adj d).eq_iff]

section Linear

variable (k : Type*) [Field k] [∀ a b : B, Linear k (a ⟶ b)]
  [GradedBicategory.IsLinear B k]

omit [GradedBicategory.ShiftCoherence B] in
/-- Scalar compatibility uses the explicit linearity of whiskering and shifts. -/
theorem mateSh_smul (r : k) {d : ℤ} (f : ShiftedHom u u d) :
    mateSh adj (r • f) = r • mateSh adj f := by
  have hL : shWhiskerLeft v (r • f) = r • shWhiskerLeft v f :=
    ShiftedHom.map_smul r f (precomp b v)
  have hε : εsh adj (r • f) = r • εsh adj f := by
    unfold εsh
    rw [hL, ShiftedHom.smul_comp]
  have hR : shWhiskerRight (r • εsh adj f) v = r • shWhiskerRight (εsh adj f) v :=
    ShiftedHom.map_smul r (εsh adj f) (postcomp b v)
  unfold mateSh
  rw [hε]
  unfold Θsh
  rw [hR, ShiftedHom.comp_smul, ShiftedHom.smul_comp]

/-- The mate map as a linear map in each integer degree. -/
def mateShLinearMap (d : ℤ) : ShiftedHom u u d →ₗ[k] ShiftedHom v v d where
  toFun := mateSh adj
  map_add' := mateSh_add adj
  map_smul' := fun r f => mateSh_smul adj k r f

end Linear

end Categorification.TwoRep

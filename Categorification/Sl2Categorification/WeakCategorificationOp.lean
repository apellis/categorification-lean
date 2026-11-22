/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.Sl2Categorification.WeakCategorification
import Mathlib.CategoryTheory.Abelian.Opposite
import Mathlib.CategoryTheory.Abelian.Subobject
import Mathlib.CategoryTheory.Adjunction.Opposites
import Mathlib.CategoryTheory.Subobject.NoetherianObject

/-!
# The opposite weak `𝔰𝔩₂`-categorification

Chuang–Rouquier, arXiv:math/0407205v2, §5.1.1, note that the opposite category of a weak
`𝔰𝔩₂`-categorification carries a weak `𝔰𝔩₂`-categorification. We construct it
(`WeakSl2.op`) and deduce the quotient form of **Chuang–Rouquier, Lemma 5.11**
(`WeakSl2.dOf_le_of_epi_E`, `WeakSl2.dOf_le_of_epi_F`): if every simple quotient of `M` has
`d ≥ r`, so does every simple quotient of `E M` and of `F M`.
-/

namespace Categorification.Sl2

open CategoryTheory Limits Opposite

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- An object of an abelian category is simple if and only if its opposite is. -/
theorem simple_op_iff (X : C) : Simple (op X) ↔ Simple X := by
  constructor
  · intro h
    refine simple_of_cosimple X fun {Z} g hg ↦ ?_
    have : Mono g.op := inferInstance
    rw [← isIso_op_iff, Simple.mono_isIso_iff_nonzero g.op]
    constructor
    · intro h1 h2; exact h1 (by rw [h2]; rfl)
    · intro h1 h2; exact h1 (Quiver.Hom.op_inj (by rw [h2]; rfl))
  · intro h
    refine ⟨fun {Y} g hg ↦ ?_⟩
    have : Epi g.unop := inferInstance
    rw [← isIso_unop_iff]
    constructor
    · intro hi h0
      have h1 : g.unop = 0 := by rw [h0]; rfl
      rw [h1] at hi
      exact id_nonzero X (by rw [← IsIso.hom_inv_id (0 : X ⟶ unop Y), zero_comp])
    · intro h0
      exact isIso_of_epi_of_nonzero (fun h1 ↦ h0 (Quiver.Hom.unop_inj (by rw [h1]; rfl)))

/-- The opposite of a Noetherian object is Artinian. -/
theorem isArtinianObject_op (X : C) [IsNoetherianObject X] : IsArtinianObject (op X) := by
  let e := Abelian.subobjectIsoSubobjectOp X
  let φ : Subobject (op X) → Subobject X := fun y ↦ e.symm (OrderDual.toDual y)
  have hwf : WellFoundedLT (Subobject (op X)) :=
    Subrelation.wf (fun {a b} h ↦ show φ b < φ a from
      e.symm.lt_iff_lt.mpr (OrderDual.toDual_lt_toDual.mpr h)) (InvImage.wf φ wellFounded_gt)
  exact ⟨hwf⟩

namespace K0Data

variable {ι V : Type*} [AddCommGroup V] [Module ℚ V] (K : K0Data C ι V)

/-- Grothendieck-group data on the opposite category. -/
def op : K0Data Cᵒᵖ ι V where
  B := K.B
  cls X := K.cls X.unop
  cls_add S hS := by
    exact (K.cls_add S.unop hS.unop).trans (add_comm _ _)
  idx S h := K.idx S.unop ((simple_op_iff S.unop).mp h)
  cls_simple S h := K.cls_simple _ _
  iso_of_idx_eq S T hS hT h := ⟨(Classical.choice (K.iso_of_idx_eq _ _ _ _ h)).op.symm⟩
  simple i := Opposite.op (K.simple i)
  simple_simple i := (simple_op_iff _).mpr (K.simple_simple i)
  idx_simple i := K.idx_simple i
  cls_mem_cone X := K.cls_mem_cone X.unop

end K0Data

namespace WeakSl2

variable {ι V : Type*} [AddCommGroup V] [Module ℚ V] (A : WeakSl2 C ι V)

/-- The opposite weak `𝔰𝔩₂`-categorification (Chuang–Rouquier, §5.1.1). -/
def op : WeakSl2 Cᵒᵖ ι V where
  toK0Data := A.toK0Data.op
  E := A.E.op
  F := A.F.op
  adjEF := A.adjFE.op
  adjFE := A.adjEF.op
  e := A.e
  f := A.f
  cls_E X := A.cls_E X.unop
  cls_F X := A.cls_F X.unop
  sl2 := A.sl2
  wt := A.wt
  wt_eq := A.wt_eq
  locFin := A.locFin

variable [∀ X : C, IsNoetherianObject X]

/-- **Chuang–Rouquier, Lemma 5.11**, for `E` and simple quotients: if every simple quotient of
`M` has `d ≥ r`, then so does every simple quotient of `E M`. -/
theorem dOf_le_of_epi_E {M T : C} {r : ℕ}
    (hM : ∀ (S : C) (hS : Simple S) (q : M ⟶ S), Epi q → r ≤ A.dS S hS)
    (hT : Simple T) (q : A.E.obj M ⟶ T) [Epi q] : r ≤ A.dS T hT := by
  have : ∀ X : Cᵒᵖ, IsArtinianObject X := fun X ↦ isArtinianObject_op X.unop
  have : Mono (show Opposite.op T ⟶ A.op.E.obj (Opposite.op M) from q.op) :=
    op_mono_of_epi q
  exact A.op.dOf_le_of_mono_E (M := Opposite.op M) (fun S hS s _ ↦ hM S.unop _ s.unop inferInstance)
    ((simple_op_iff T).mpr hT) q.op

/-- **Chuang–Rouquier, Lemma 5.11**, for `F` and simple quotients. -/
theorem dOf_le_of_epi_F {M T : C} {r : ℕ}
    (hM : ∀ (S : C) (hS : Simple S) (q : M ⟶ S), Epi q → r ≤ A.dS S hS)
    (hT : Simple T) (q : A.F.obj M ⟶ T) [Epi q] : r ≤ A.dS T hT := by
  have : ∀ X : Cᵒᵖ, IsArtinianObject X := fun X ↦ isArtinianObject_op X.unop
  have : Mono (show Opposite.op T ⟶ A.op.F.obj (Opposite.op M) from q.op) :=
    op_mono_of_epi q
  exact A.op.dOf_le_of_mono_F (M := Opposite.op M) (fun S hS s _ ↦ hM S.unop _ s.unop inferInstance)
    ((simple_op_iff T).mpr hT) q.op

end WeakSl2

end Categorification.Sl2

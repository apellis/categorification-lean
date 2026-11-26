/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.CornerBimodule
import Categorification.WeightedKLR.RedStrands.BraidFiltrationDimension

/-!
# Filtration from ordered braid column generators

Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.11, step `p_n → f_n`,
defines successive steps by the images of multiplication by ordered diagrams.
When the images span the column and each standard relation maps into an earlier
step, the successive quotients receive surjective maps from the corresponding
standards. This module constructs the filtration and these surjections using
those two inputs.
-/

namespace Categorification.Stendhal.BraidColumn

open ModuleFiltration

/-- Multiplication by a diagram supported on the intermediate loading on its
right, as a map of right modules over the bottom corner. The same formula
applies in the quotient by violated idempotents. -/
def diagramMul {R : Type*} [Ring R] {e f g : R} (hg : IsIdempotentElem g)
    (y : cornerBimodule e f) :
    cornerBimodule f g →ₗ[hg.Cornerᵐᵒᵖ] cornerBimodule e g where
  toFun x := ⟨y.val * x.val, by
    exact ⟨by rw [← mul_assoc, y.prop.1], by rw [mul_assoc, x.prop.2]⟩⟩
  map_add' x x' := Subtype.ext (mul_add y.val x.val x'.val)
  map_smul' r x := Subtype.ext (mul_assoc y.val x.val r.unop.val).symm

variable {A : Type*} [Ring A] {P : ℕ → ModuleCat A} {D : ModuleCat A}

/-- The first `n` diagram images in an ordered column. -/
def diagramStep (y : ∀ i, P i →ₗ[A] D) : ℕ → Submodule A D
  | 0 => ⊥
  | i + 1 => diagramStep y i ⊔ LinearMap.range (y i)

/-- The successive factors of the filtration by ordered diagram images. -/
abbrev diagramPiece (y : ∀ i, P i →ₗ[A] D) (i : ℕ) :=
  (diagramStep y (i + 1)) ⧸ (diagramStep y i).comap (diagramStep y (i + 1)).subtype

private def diagramPieceMap (y : ∀ i, P i →ₗ[A] D) (i : ℕ) :
    P i →ₗ[A] diagramPiece y i :=
  Submodule.mkQ _ ∘ₗ (y i).codRestrict _ (fun x => Submodule.mem_sup_right ⟨x, rfl⟩)

/-- Multiplication by the next diagram descends from the proposed standard once
its relations map into the earlier filtration step. -/
def standardToDiagramPiece (y : ∀ i, P i →ₗ[A] D) (i : ℕ) (U : Submodule A (P i))
    (h : ∀ x ∈ U, y i x ∈ diagramStep y i) :
    (P i ⧸ U) →ₗ[A] diagramPiece y i :=
  U.liftQ (diagramPieceMap y i) (fun x hx => by
    exact (Submodule.Quotient.mk_eq_zero _).mpr (h x hx))

/-- The map from the standard onto the next diagram piece in Webster's
arXiv:1309.3796v2, §6.1, Lemma 6.11, proof of `p_n → f_n`. -/
theorem standardToDiagramPiece_surjective (y : ∀ i, P i →ₗ[A] D) (i : ℕ)
    (U : Submodule A (P i)) (h : ∀ x ∈ U, y i x ∈ diagramStep y i) :
    Function.Surjective (standardToDiagramPiece y i U h) := by
  intro z
  obtain ⟨v, rfl⟩ := (Submodule.mkQ_surjective _) z
  obtain ⟨a, ha, _, ⟨b, rfl⟩, hab⟩ := Submodule.mem_sup.mp v.2
  refine ⟨U.mkQ b, ?_⟩
  change Submodule.Quotient.mk (⟨y i b, Submodule.mem_sup_right ⟨b, rfl⟩⟩ :
    diagramStep y (i + 1)) = Submodule.Quotient.mk v
  rw [Submodule.Quotient.eq]
  change y i b - (v : D) ∈ diagramStep y i
  rw [← hab, sub_add_eq_sub_sub_swap, sub_self, zero_sub]
  exact neg_mem ha

private theorem hasFiltration_diagramStep (y : ∀ i, P i →ₗ[A] D) (n : ℕ) :
    HasFiltration (fun i => ModuleCat.of A (diagramPiece y i))
      (List.range n).reverse (ModuleCat.of A (diagramStep y n)) := by
  induction n with
  | zero => exact .zero (show Subsingleton (⊥ : Submodule A D) from inferInstance)
  | succ i ih =>
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append]
    let hle : diagramStep y i ≤ diagramStep y (i + 1) := le_sup_left
    let U := (diagramStep y i).comap (diagramStep y (i + 1)).subtype
    refine .cons (Submodule.inclusion hle) U.mkQ _ i
      (Submodule.inclusion_injective hle) ?_ U.mkQ_surjective ih ⟨LinearEquiv.refl _ _⟩
    intro z
    change U.mkQ z = 0 ↔ z ∈ Set.range (Submodule.inclusion hle)
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨fun hz => ⟨⟨z.val, hz⟩, rfl⟩, fun ⟨w, hw⟩ => hw ▸ w.prop⟩

/-- The ordered diagram images give a filtration of the braid column once the
first `n` diagrams generate it. Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.11. -/
theorem hasFiltration_diagramColumn (y : ∀ i, P i →ₗ[A] D) (n : ℕ)
    (hTop : diagramStep y n = ⊤) :
    HasFiltration (fun i => ModuleCat.of A (diagramPiece y i)) (List.range n).reverse D := by
  let f : diagramStep y n →ₗ[A] D := (diagramStep y n).subtype
  exact (hasFiltration_diagramStep y n).of_equiv
    (LinearEquiv.ofBijective f ⟨Subtype.val_injective, fun x => ⟨⟨x, hTop ▸ trivial⟩, rfl⟩⟩)

/-- Modifying a diagram by elements of earlier steps preserves the filtration.
For a reduced-word change the hypothesis is the triangular straightening statement
in the proof of Webster's Lemma 6.11, arXiv:1309.3796v2, §6.1. -/
theorem diagramStep_eq_of_sub_mem (y z : ∀ i, P i →ₗ[A] D) (n : ℕ)
    (h : ∀ i < n, ∀ x, y i x - z i x ∈ diagramStep y i) :
    diagramStep y n = diagramStep z n := by
  induction n with
  | zero => rfl
  | succ i ih =>
    have heq := ih (fun j hj => h j (Nat.lt_succ_of_lt hj))
    have hdiff x := h i (Nat.lt_succ_self i) x
    apply le_antisymm <;> apply sup_le
    · exact heq.le.trans le_sup_left
    · rintro _ ⟨x, rfl⟩
      rw [← sub_add_cancel (y i x) (z i x)]
      exact Submodule.add_mem_sup (heq ▸ hdiff x) ⟨x, rfl⟩
    · exact heq.ge.trans le_sup_left
    · rintro _ ⟨x, rfl⟩
      rw [← sub_add_cancel (z i x) (y i x)]
      exact Submodule.add_mem_sup (by simpa only [neg_sub] using neg_mem (hdiff x)) ⟨x, rfl⟩

open scoped ModuleCat.Algebra

/-- The diagram filtration has the proposed standard modules as its pieces
when the dimension identity in Webster's Lemma 6.11 holds. The inputs are
generation by the ordered diagrams, reduction of their standard relations to
earlier steps, and the dimension sum. -/
theorem hasStandardFiltration_diagramColumn {k : Type*} [Field k] [Algebra k A]
    [FiniteDimensional k D] (y : ∀ i, P i →ₗ[A] D) (n : ℕ) (U : ∀ i, Submodule A (P i))
    (hTop : diagramStep y n = ⊤) (hRel : ∀ i, ∀ x ∈ U i, y i x ∈ diagramStep y i)
    (hFinite : ∀ i, FiniteDimensional k (ModuleCat.of A (P i ⧸ U i)))
    (hDim : Module.finrank k D =
      (((List.range n).reverse).map fun i =>
        Module.finrank k (ModuleCat.of A (P i ⧸ U i))).sum) :
    HasFiltration (fun i => ModuleCat.of A (P i ⧸ U i)) (List.range n).reverse D :=
  (hasFiltration_diagramColumn y n hTop).of_surjective_factors
    (fun i => standardToDiagramPiece y i (U i) (hRel i))
    hFinite (fun i => standardToDiagramPiece_surjective y i (U i) (hRel i)) hDim

end Categorification.Stendhal.BraidColumn

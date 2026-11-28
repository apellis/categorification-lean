/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.HalfTwistEquivalence
import Categorification.WeightedKLR.RedStrands.BraidingFunctorRelabel
import Categorification.WeightedKLR.RedStrands.BraidingFunctorCompose

set_option backward.isDefEq.respectTransparency false

/-!
# The braiding functors are equivalences

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
Theorem 6.15: every braiding functor `𝔅(κ', κ)` between red orders is an equivalence of
derived categories (`isEquivalence_braidingFunctor`).

Webster's argument: the half twist `𝔅_{w₀}` is an equivalence
(`isEquivalence_braidingFunctor_halfTwist`), and it factors through every braiding functor on
the left and on the right. Here, for the red orders `(1, …, ℓ)`, `u` and `w₀`, the lengths of
`u` and `u⁻¹ w₀` add, so `𝔅((1, …, ℓ), u) ⋙ 𝔅(u, w₀) ≅ 𝔅((1, …, ℓ), w₀)`
(Lemma 6.12, `braidingFunctorCompIsoOfLengthAdd`). Relabelling the red strands by `u`
(`isEquivalence_braidingFunctor_of_relabel_comp`) carries `𝔅(u, w₀)` to
`𝔅^{λ ∘ u}((1, …, ℓ), u⁻¹ w₀)`, which is followed by a braiding functor to an equivalence
in the same way. So `𝔅(u, w₀)` has a left and a right inverse, hence is an equivalence, and then
so is `𝔅((1, …, ℓ), u)` (`isEquivalence_braidingFunctor_finRange`). A last relabelling gives
every pair of red orders.

Route hypotheses: those of the half twist, namely the injectivity hypothesis of Lemma 6.8
inside `RowFigureFiveHypotheses`, at the Khovanov–Lauda scalars.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open CategoryTheory KLR Equiv
open scoped List DG.DegreeZero

theorem map_revPerm_finRange (n : ℕ) :
    (List.finRange n).map (Fin.revPerm : Perm (Fin n)) = (List.finRange n).reverse := by
  rw [List.finRange_reverse]
  rfl

/-- In the red order `w₀ = (ℓ, …, 1)` every pair of red strands is inverted. -/
theorem lt_of_sublist_map_revPerm {n : ℕ} {x y : Fin n}
    (h : [x, y] <+ (List.finRange n).map (Fin.revPerm : Perm (Fin n))) : y < x := by
  rw [map_revPerm_finRange] at h
  have h' : [y, x] <+ List.finRange n := by simpa using List.reverse_sublist.2 h
  exact List.pairwise_pair.1 ((List.pairwise_lt_finRange n).sublist h')

/-- A pair of red strands in the order `w₀ = (ℓ, …, 1)` is in the reverse order in
`(1, …, ℓ)`. -/
theorem sublist_finRange_of_sublist_map_revPerm {n : ℕ} {x y : Fin n}
    (h : [x, y] <+ (List.finRange n).map (Fin.revPerm : Perm (Fin n))) :
    [y, x] <+ List.finRange n := by
  rw [map_revPerm_finRange] at h
  simpa using List.reverse_sublist.2 h

section KhovanovLauda

open QuantumGroup KL3.Diagram
open scoped Classical

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra

variable {I : Type} {k : Type} [Field k] (C : CartanDatum I)
  (hQ : IsRouquierQ C (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k))) {ℓ : ℕ}
  {Y : Type*} [AddCommGroup Y] [Finite I]
  {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular)
  [∀ (Ω : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I),
    Module.Finite k (TensorProductAlgebra k (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Ω ν)]
  [∀ (Ω : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I) (κ₀ : List (Fin (ℓ + 1))),
    DG.HasDerivedCategory.{0, 0} (ViolOrderCorner (k := k)
      (Q := CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) (Λ := Ω) (ν := ν) κ₀)]
  [∀ (Ω : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I) (κ₀ : List (Fin (ℓ + 1))),
    DG.HasDerivedCategory.{0, 0} (ViolOrderCorner (k := k)
      (Q := CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) (Λ := Ω) (ν := ν) κ₀)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{0, 0} ℤ]
  (H : ∀ (n m : ℕ), n + 2 + m = ℓ + 1 → ∀ (Ω : Fin (n + 2 + m) → I →₀ ℕ)
    (u : Fin (n + 2 + m) → List I) (hu : u (FirstWeight.rightPos n m) = []),
    FirstWeight.RowFigureFiveHypotheses C hQ Ω u hu)

local notation "QL" => CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)
local notation "fin" => List.finRange (ℓ + 1)
local notation "w₀" => (Fin.revPerm : Perm (Fin (ℓ + 1)))

include hQ hR H in
/-- The half twist `𝔅((1, …, ℓ), w₀)` is an equivalence, for `ℓ ≥ 2` red strands. -/
theorem isEquivalence_braidingFunctor_revPerm (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I)
    (wt : Fin (ℓ + 1) → LieLean.QuantumGroup.GrandLoop.Dom R)
    (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i)) (hw : w₀ ≠ 1) :
    (braidingFunctor.{0} k QL Λ ν fin ((fin).map w₀)).IsEquivalence :=
  isEquivalence_braidingFunctor_halfTwist C hQ Λ ν w₀ hR H wt hwt hw fun t ht =>
    isRedReversed_of_redWord_reverse t (ht.trans (map_revPerm_finRange _))

include hQ hR H in
/-- **Webster, Theorem 6.15, from the red order `(1, …, ℓ)`** (arXiv:1309.3796v3): for every
permutation `u` of the red strands, `𝔅((1, …, ℓ), u)` is an equivalence. Route hypotheses:
those of the half twist (`isEquivalence_braidingFunctor_halfTwist`). -/
theorem isEquivalence_braidingFunctor_finRange (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I)
    (wt : Fin (ℓ + 1) → LieLean.QuantumGroup.GrandLoop.Dom R)
    (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i)) (u : Perm (Fin (ℓ + 1))) :
    (braidingFunctor.{0} k QL Λ ν fin ((fin).map u)).IsEquivalence := by
  by_cases hu1 : u = 1
  · subst hu1
    rw [Perm.coe_one, List.map_id]
    exact isEquivalence_braidingFunctor_self _
  have hw : w₀ ≠ 1 := by
    intro h
    apply hu1
    have h0 : Fin.rev (0 : Fin (ℓ + 1)) = 0 := by
      rw [← Fin.revPerm_apply, h, Perm.one_apply]
    have hℓ : ℓ = 0 := by simpa [Fin.ext_iff] using h0
    subst hℓ
    exact Equiv.ext fun x => Subsingleton.elim (α := Fin 1) _ _
  have hL : ∀ τ : Perm (Fin (ℓ + 1)), ∀ x y, [x, y] <+ (fin).map ⇑(τ * (τ⁻¹ * w₀)) →
      [y, x] <+ (fin).map τ → [y, x] <+ fin := fun τ x y h _ => by
    rw [mul_inv_cancel_left] at h
    exact sublist_finRange_of_sublist_map_revPerm h
  by_cases huw : u = w₀
  · subst huw
    exact isEquivalence_braidingFunctor_revPerm C hQ hR H Λ ν wt hwt hw
  have hs : u⁻¹ * w₀ ≠ 1 := fun h => huw (inv_mul_eq_one.1 h)
  have hv : (u⁻¹ * w₀)⁻¹ * w₀ ≠ 1 := fun h => hu1 (inv_eq_one.1 (mul_eq_right.1
    (inv_mul_eq_one.1 h)))
  have hE₁ : (braidingFunctor.{0} k QL Λ ν fin ((fin).map ⇑(u * (u⁻¹ * w₀)))).IsEquivalence := by
    rw [mul_inv_cancel_left]
    exact isEquivalence_braidingFunctor_revPerm C hQ hR H Λ ν wt hwt hw
  have hE₂ : (braidingFunctor.{0} k QL (Λ ∘ u) ν fin
      ((fin).map ⇑((u⁻¹ * w₀) * ((u⁻¹ * w₀)⁻¹ * w₀)))).IsEquivalence := by
    rw [mul_inv_cancel_left]
    exact isEquivalence_braidingFunctor_revPerm C hQ hR H (Λ ∘ u) ν (wt ∘ u)
      (fun r i => hwt (u r) i) hw
  have h₁ := Functor.isEquivalence_of_iso
    (FirstWeight.braidingFunctorCompIsoOfLengthAdd C hQ hR H Λ wt hwt ν u (u⁻¹ * w₀) hs
      (hL u)).symm
  have h₂ := Functor.isEquivalence_of_iso
    (FirstWeight.braidingFunctorCompIsoOfLengthAdd C hQ hR H (Λ ∘ u) (wt ∘ u)
      (fun r i => hwt (u r) i) ν (u⁻¹ * w₀) ((u⁻¹ * w₀)⁻¹ * w₀) hv (hL (u⁻¹ * w₀))).symm
  have hG : (braidingFunctor.{0} k QL Λ ν ((fin).map u)
      ((fin).map ⇑(u * (u⁻¹ * w₀)))).IsEquivalence :=
    isEquivalence_braidingFunctor_of_relabel_comp u (κ' := fin) (κ := (fin).map ⇑(u⁻¹ * w₀)) rfl
      (by rw [List.map_map]; rfl) _ h₁ _ h₂
  exact Functor.isEquivalence_of_comp_right _
    (braidingFunctor.{0} k QL Λ ν ((fin).map u) ((fin).map ⇑(u * (u⁻¹ * w₀))))

include hQ hR H in
/-- **Webster, Theorem 6.15** (arXiv:1309.3796v3): every braiding functor `𝔅(κ', κ)` between
red orders is an equivalence of derived categories. Route hypotheses: those of the half twist
(`isEquivalence_braidingFunctor_halfTwist`), at the Khovanov–Lauda scalars. -/
theorem isEquivalence_braidingFunctor (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I)
    (wt : Fin (ℓ + 1) → LieLean.QuantumGroup.GrandLoop.Dom R)
    (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i)) {κ' κ : List (Fin (ℓ + 1))}
    (h' : κ'.Perm fin) (h : κ.Perm fin) :
    (braidingFunctor.{0} k QL Λ ν κ' κ).IsEquivalence := by
  obtain ⟨σ, rfl⟩ := exists_perm_eq_map_finRange h'
  obtain ⟨τ, rfl⟩ := exists_perm_eq_map_finRange h
  exact isEquivalence_braidingFunctor_relabel σ (κ' := fin) (κ := (fin).map ⇑(σ⁻¹ * τ)) rfl
    (by rw [List.map_map]; congr 1; ext x; simp)
    (isEquivalence_braidingFunctor_finRange C hQ hR H (Λ ∘ σ) ν (wt ∘ σ)
      (fun r i => hwt (σ r) i) _)

end KhovanovLauda

end Categorification.Stendhal.BraidedStendhalAlgebra

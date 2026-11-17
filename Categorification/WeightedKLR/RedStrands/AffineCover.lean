/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.StendhalGrading
import Categorification.KLR.Symmetries

/-!
# An affine KLR cover of the red diagram algebra

For the integral spanning question in Webster, arXiv:1309.3796v2, Lemma 4.37,
replace the zero polynomial between distinct red colours by the sum of the two
dot variables. Red dots vanish in the diagram algebra, and each red label
occurs exactly once. Consequently the affine KLR relations still hold there.
-/

noncomputable section
namespace Categorification.Stendhal
open KLR MvPolynomial StendhalAlgebraAllOrders
open scoped Matrix

variable {I k : Type*} [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)

/-- Affine parameters with a nonzero polynomial for each pair of red colours. -/
def affineCoverQ (a b : I ⊕ Fin ℓ) : MvPolynomial (Fin 2) k :=
  match a, b with
  | .inr _, .inr _ => X 0 + X 1
  | _, _ => stendhalQ Q Λ a b

variable [DecidableEq I] (ν : Multiset I)
local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card μ
local notation "π" => RingQuot.mkAlgHom k (Rel k Q Λ ν)

omit [DecidableEq I] in
private theorem eq_of_red_label {s : Seq μ} {a b : Fin m} {r : Fin ℓ}
    (ha : s.lbl a = .inr r) (hb : s.lbl b = .inr r) : a = b := by
  classical
  let F := Finset.univ.filter (fun c => Sum.inr r = s.lbl c)
  have hc : F.card = 1 := by
    change (Finset.univ.val.filter (fun c => Sum.inr r = s.lbl c)).card = 1
    rw [← Multiset.count_map, show Finset.univ.val.map s.lbl = μ from s.2]
    rw [stendhalWeight, Multiset.count_add, Multiset.count_map_eq_count' Sum.inr _ Sum.inr_injective]
    simp
  exact Finset.card_le_one_iff.mp hc.le (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha.symm⟩)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb.symm⟩)

private theorem cover_rel {a b} (h : KLR.Rel k (affineCoverQ Q Λ) μ a b) : π a = π b := by
  cases h with
  | cross_sq j hj s =>
    have orig := RingQuot.mkAlgHom_rel k (Rel.klr (Λ := Λ) (Q := Q) (ν := ν)
      (KLR.Rel.cross_sq j hj s))
    apply orig.trans
    by_cases he : s.lbl ⟨j, by omega⟩ = s.lbl ⟨j + 1, hj⟩
    · simp [he]
    simp only [ite_eq_right he]
    cases ha : s.lbl ⟨j, by omega⟩ with
    | inl i => cases s.lbl ⟨j + 1, hj⟩ <;> rfl
    | inr r =>
      cases hb : s.lbl ⟨j + 1, hj⟩ with
      | inl i => rfl
      | inr t =>
        let pos : Fin 2 → Fin m := ![⟨j, by omega⟩, ⟨j+1, hj⟩]
        have hev (p : MvPolynomial (Fin 2) k) :
            π (ncEval ![fx k μ ⟨j, by omega⟩, fx k μ ⟨j+1, hj⟩] p) =
            ofKLR k Q Λ ν (KLRAlgebra.pol (rename pos p)) := by
          rw [← ofKLR_mk, ncEval_map, ← KLRAlgebra.ncEval_eq_pol]
          congr 2
        have hid : π (fe k μ s) = e s := (ofKLR_mk _).symm
        simp only [stendhalQ, affineCoverQ, map_mul, hev, hid, map_zero, map_add,
          rename_X, KLRAlgebra.pol_X]
        have h₀ : (x (pos 0) * e s : StendhalAlgebraAllOrders k Q Λ ν) = 0 :=
          x_mul_e_of_red _ s (by change (s.lbl ⟨j, _⟩).isRight; simp [ha])
        have h₁ : (x (pos 1) * e s : StendhalAlgebraAllOrders k Q Λ ν) = 0 :=
          x_mul_e_of_red _ s (by change (s.lbl ⟨j+1, _⟩).isRight; simp [hb])
        have hz : (0 * e s : StendhalAlgebraAllOrders k Q Λ ν) =
            (x (pos 0) + x (pos 1)) * e s := by rw [zero_mul, add_mul, h₀, h₁, add_zero]
        exact hz
  | braid j hj s =>
    have orig := RingQuot.mkAlgHom_rel k (Rel.klr (Λ := Λ) (Q := Q) (ν := ν)
      (KLR.Rel.braid j hj s))
    apply orig.trans
    split_ifs with he
    · cases ha : s.lbl ⟨j, by omega⟩ with
      | inl _ => cases s.lbl ⟨j+1, by omega⟩ <;> rfl
      | inr r =>
        have hab := eq_of_red_label ν ha (he.1.symm.trans ha)
        have := congrArg Fin.val hab
        simp only at this
        omega
    · rfl
  | idem_mul s t => exact RingQuot.mkAlgHom_rel k (Rel.klr (.idem_mul s t))
  | idem_sum => exact RingQuot.mkAlgHom_rel k (Rel.klr .idem_sum)
  | dot_idem a s => exact RingQuot.mkAlgHom_rel k (Rel.klr (.dot_idem a s))
  | cross_idem j s => exact RingQuot.mkAlgHom_rel k (Rel.klr (.cross_idem j s))
  | cross_zero j h => exact RingQuot.mkAlgHom_rel k (Rel.klr (.cross_zero j h))
  | dot_dot a b => exact RingQuot.mkAlgHom_rel k (Rel.klr (.dot_dot a b))
  | cross_cross j t h => exact RingQuot.mkAlgHom_rel k (Rel.klr (.cross_cross j t h))
  | dot_cross a j h h' => exact RingQuot.mkAlgHom_rel k (Rel.klr (.dot_cross a j h h'))
  | dot_cross_left j h s => exact RingQuot.mkAlgHom_rel k (Rel.klr (.dot_cross_left j h s))
  | dot_cross_right j h s => exact RingQuot.mkAlgHom_rel k (Rel.klr (.dot_cross_right j h s))

/-- The affine algebra maps onto the Stendhal algebra with all red orders. -/
def affineCover : KLRAlgebra k (affineCoverQ Q Λ) μ →ₐ[k] StendhalAlgebraAllOrders k Q Λ ν :=
  RingQuot.liftAlgHom k ⟨π, fun _ _ => cover_rel Q Λ ν⟩

theorem affineCover_surjective : Function.Surjective (affineCover Q Λ ν) := by
  intro y
  obtain ⟨a, rfl⟩ := RingQuot.mkAlgHom_surjective k (Rel k Q Λ ν) y
  exact ⟨KLRAlgebra.mk k _ _ a, RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _⟩

end Categorification.Stendhal

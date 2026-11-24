/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockCrossingOrder
import Categorification.WeightedKLR.RedStrands.BlockQuotientCoordinates

/-!
# Order and loading support of quotient coordinates

In the partially standardized row for Webster's Lemma 6.8 a coefficient on the
global uncrossed upper red order has the corresponding ordered upper block
support. The bottom loading acts by its indexed lower block projector.
-/

noncomputable section
namespace Categorification.Stendhal.RedBlock
open KLR KLRAlgebra BraidedStendhalAlgebra

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
    (L M : List (Fin ℓ × Multiset I)) (f : Fin 2 ↪ Fin ℓ) (β : Multiset I) {ν : Multiset I}
local notation "row" => adjacentRow L M f β
local notation "μ" => stendhalWeight ℓ ν
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "P" => projection Q Λ row
local notation "α" => fun r i => boundaryCount (cut (f 0) (f 1) r) i row
local notation "κ" => L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst
local notation "J" => blockUpperIdeal k Q Λ ν (f 0) (f 1) α κ
local notation "π" => AlgHom.comp (RingCon.mkₐ k (TwoSidedIdeal.ringCon J))
  (AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν))
local notation "E" => orderedIdem Q Λ (fun _ => 1) row
local notation "p" => redIdem k Q Λ (ν := ν) κ

local notation "S" => affineStackBlocks Q Λ L M f β

/-- For an uncrossed, nonviolated placed upper loading, the row quotient is
precisely the quotient by the higher ideal indexed by that loading. -/
theorem blockUpperIdeal_placed (h : weightSum row = μ) (u : Loadings row)
    (ho : UncrossedLoading row u) (hv : ¬ Violated row u) :
    let t := Seq.cast h (place row u)
    blockUpperIdeal k Q Λ ν (f 0) (f 1) (adjacentBlockRoot (f 0) (f 1) t) (redWord t) = J := by
  intro t
  have ht : redWord t = κ := (uncrossedLoading_iff L M f β h u).1 ho
  have aligned := aligned_adjacent L M f β (ht ▸ redWord_nodup t)
  have eq : adjacentBlockRoot (f 0) (f 1) t = α := by
    funext r i
    have cast_count {w w' : Multiset (I ⊕ Fin ℓ)} (e : w = w') (s : Seq w) (C : Finset (Fin ℓ)) :
        blockBlackCount (Seq.cast e s) C i = blockBlackCount s C i := by subst w'; rfl
    exact (cast_count h (place row u) (cut (f 0) (f 1) r)).trans (count_place_of_not_violated r i u aligned hv)
  rw [eq, ht]

/-- Stacked upper diagrams and bottom loading projectors act on coordinates of
every quotient class. -/
theorem quotientCoordinate_actions (h : weightSum row = μ)
    (G : (J).ringCon.Quotient →ₗ[k] quotients Q Λ row) (bottom : Seq μ → diagrams Q Λ row)
    (hmul : ∀ a y, G (π (S h a * y)) = P a * G (π y))
    (hbottom : ∀ y s, G (π (y * e s)) = G (π y) * P (bottom s))
    (z : (J).ringCon.Quotient) :
    (∀ a, G (π (S h a) * z) = P a * G z) ∧
      ∀ s : Seq μ, G (z * π (e s)) = G z * P (bottom s) := by
  have onto : Function.Surjective π :=
    (RingCon.mkₐ_surjective («α» := k) (TwoSidedIdeal.ringCon J)).comp
      (violMk_surjective.comp ofKLR_surjective)
  obtain ⟨y, rfl⟩ := onto z
  exact ⟨fun a => (congrArg G (map_mul π _ _).symm).trans (hmul a y),
    fun s => (congrArg G (map_mul π _ _).symm).trans (hbottom y s)⟩

/-- Upper and lower support of a quotient class pass to its coordinate. -/
theorem quotientCoordinate_support_of_fixed (h : weightSum row = μ)
    (G : (J).ringCon.Quotient →ₗ[k] quotients Q Λ row) (bottom : Seq μ → diagrams Q Λ row)
    (hmul : ∀ a y, G (π (S h a * y)) = P a * G (π y))
    (hbottom : ∀ y s, G (π (y * e s)) = G (π y) * P (bottom s))
    (a : diagrams Q Λ row) (z : (J).ringCon.Quotient)
    (s : Seq μ) (hl : π (S h a) * z = z) (hr : z * π (e s) = z) :
    P a * G z = G z ∧ G z * P (bottom s) = G z := by
  obtain ⟨left, right⟩ := quotientCoordinate_actions Q Λ L M f β h G bottom hmul hbottom z
  exact ⟨(left a).symm.trans (congrArg G hl), (right s).symm.trans (congrArg G hr)⟩

/-- Fixing the global uncrossed upper red order suffices for a coordinate to be
fixed by the product of the local ordered upper projectors. -/
theorem quotientCoordinate_support_of_redOrder (h : weightSum row = μ)
    (G : (J).ringCon.Quotient →ₗ[k] quotients Q Λ row) (bottom : Seq μ → diagrams Q Λ row)
    (hmul : ∀ a y, G (π (S h a * y)) = P a * G (π y))
    (hbottom : ∀ y s, G (π (y * e s)) = G (π y) * P (bottom s))
    (z : (J).ringCon.Quotient) (s : Seq μ)
    (hl : π p * z = z) (hr : z * π (e s) = z) :
    P E * G z = G z ∧ G z * P (bottom s) = G z := by
  obtain ⟨left, right⟩ := quotientCoordinate_actions Q Λ L M f β h G bottom hmul hbottom z
  refine ⟨(left E).symm.trans ?_, (right s).symm.trans (congrArg G hr)⟩
  rw [← (affineStackBlocks_orderedIdem Q Λ L M f β h).2, map_mul π, mul_assoc, hl, left, map_one, one_mul]

/-- A source class cut by an upper loading in the prescribed red order and a
lower loading has both coefficient supports. -/
theorem quotientCoordinate_support_of_redLoading (h : weightSum row = μ)
    (G : (J).ringCon.Quotient →ₗ[k] quotients Q Λ row) (bottom : Seq μ → diagrams Q Λ row)
    (hmul : ∀ a y, G (π (S h a * y)) = P a * G (π y))
    (hbottom : ∀ y s, G (π (y * e s)) = G (π y) * P (bottom s))
    (z : (J).ringCon.Quotient) (t s : Seq μ)
    (ho : redWord t = κ) (hl : π (e t) * z = z) (hr : z * π (e s) = z) :
    P E * G z = G z ∧ G z * P (bottom s) = G z := by
  apply quotientCoordinate_support_of_redOrder Q Λ L M f β h G bottom hmul hbottom z s _ hr
  calc π p * z = π p * (π (e t) * z) := congrArg (π p * ·) hl.symm
       _ = z := by rw [← mul_assoc, ← map_mul π, redIdem_mul_e, ite_eq_left ho, hl]

/-- A representative already multiplied by the upper ordered and lower loading
projectors has those supports in each coordinate. -/
theorem quotientCoordinate_ordered_rep_support (h : weightSum row = μ)
    (G : (J).ringCon.Quotient →ₗ[k] quotients Q Λ row) (bottom : Seq μ → diagrams Q Λ row)
    (hmul : ∀ a y, G (π (S h a * y)) = P a * G (π y))
    (hbottom : ∀ y s, G (π (y * e s)) = G (π y) * P (bottom s))
    (y : R) (s : Seq μ) :
    let z := π (S h E * y * e s)
    P E * G z = G z ∧ G z * P (bottom s) = G z := by
  intro z
  apply quotientCoordinate_support_of_redOrder Q Λ L M f β h G bottom hmul hbottom z s
  · change π p * π (S h E * y * e s) = _
    rw [← map_mul π, ← mul_assoc p, ← mul_assoc p]
    have hl : p * S h E = S h E := by
      rw [← (affineStackBlocks_orderedIdem Q Λ L M f β h).1, ← mul_assoc, redIdem_mul_redIdem]
    rw [hl]
  · change π (S h E * y * e s) * π (e s) = _
    rw [← map_mul π, mul_assoc _ (e s), e_mul_self]

end Categorification.Stendhal.RedBlock

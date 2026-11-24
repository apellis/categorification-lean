/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockCrossingCoordinates

/-!
# Parabolic coordinates on the partially standardized quotient

Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8 after (6.21).
The projected coordinates vanish on the two-sided ideals of globally violated
and higher source loadings and hence define linear maps on the quotient.
-/

noncomputable section
namespace Categorification.Stendhal.RedBlock
open KLR KLRAlgebra BraidedStendhalAlgebra

private theorem zero_on_ideal_of_zero_on_triples {k A D : Type*} [CommRing k]
    [Ring A] [Algebra k A] [AddCommGroup D] [Module k D] (F : A →ₗ[k] D) {S : Set A}
    (hS : ∀ s ∈ S, ∀ x y, F (x * s * y) = 0) {z : A}
    (hz : z ∈ TwoSidedIdeal.span S) : F z = 0 := by
  suffices h : ∀ x y, F (x * z * y) = 0 by simpa only [one_mul, mul_one] using h 1 1
  induction hz using TwoSidedIdeal.span_induction with
  | mem s hs => exact hS s hs
  | zero => intro x y; rw [mul_zero, zero_mul, map_zero]
  | add a b _ _ h₁ h₂ => intro x y; rw [mul_add, add_mul, map_add, h₁, h₂, add_zero]
  | neg a _ h => intro x y; rw [mul_neg, neg_mul, map_neg, h, neg_zero]
  | left_absorb a z _ h => intro x y; simpa only [mul_assoc] using h (x * a) y
  | right_absorb a z _ h => intro x y; simpa only [mul_assoc] using h x (a * y)

private def descendLinear {k A B D : Type*} [CommRing k]
    [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B] [AddCommGroup D] [Module k D]
    (q : A →ₗ[k] B) (hq : Function.Surjective q) (F : A →ₗ[k] D)
    (hF : LinearMap.ker q ≤ LinearMap.ker F) : B →ₗ[k] D :=
  ((LinearMap.ker q).liftQ F hF).comp (q.quotKerEquivOfSurjective hq).symm.toLinearMap

private theorem descendLinear_apply {k A B D : Type*} [CommRing k]
    [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B] [AddCommGroup D] [Module k D]
    (q : A →ₗ[k] B) (hq : Function.Surjective q) (F : A →ₗ[k] D)
    (hF : LinearMap.ker q ≤ LinearMap.ker F) (x : A) :
    descendLinear q hq F hF (q x) = F x := by
  simp only [descendLinear, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]

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
local notation "raw" => ofKLR k Q Λ ν
local notation "secB" => toKLR k Q Λ ν
local notation "mk" => violMk k Q Λ ν
local notation "q" => RingCon.mkₐ k (TwoSidedIdeal.ringCon J)

/-- Projected parabolic coordinates descend through global violations and through
higher source loadings (Webster v2, Lemma 6.8, proof after (6.21)). -/
private theorem exists_quotientBlockCoordinate (g : R →ₗ[k] diagrams Q Λ row)
    (hsec : ∀ y, g (secB (raw y)) = g y)
    (hbad : ∀ (y : R) (s : Seq μ) (z : R),
      (IsViolated s ∨ (redWord s = κ ∧ α < adjacentBlockRoot (f 0) (f 1) s)) →
      P (g (y * e s * z)) = 0) :
    ∃ G : (J).ringCon.Quotient →ₗ[k] quotients Q Λ row,
      ∀ y : R, G (q (mk (raw y))) = P (g y) := by
  let F := (P).toLinearMap.comp (g.comp (secB).toLinearMap)
  have F_raw (y : R) : F (raw y) = P (g y) := congrArg P (hsec y)
  have F_viol : LinearMap.ker (mk).toLinearMap ≤ LinearMap.ker F := by
    intro r hr
    change F r = 0
    apply zero_on_ideal_of_zero_on_triples F _ ((violMk_eq_zero_iff r).1 hr)
    rintro _ ⟨s, hs, rfl⟩ a b
    obtain ⟨y,rfl⟩ := ofKLR_surjective a
    obtain ⟨z,rfl⟩ := ofKLR_surjective b
    rw [← map_mul raw, ← map_mul raw, F_raw]
    exact hbad y s z (Or.inl hs)
  let G₀ := descendLinear (mk).toLinearMap violMk_surjective F F_viol
  have G₀_raw (y : R) : G₀ (mk (raw y)) = P (g y) :=
    (descendLinear_apply (mk).toLinearMap violMk_surjective F F_viol _).trans (F_raw y)
  let π := (mk).comp raw
  have surjπ : Function.Surjective π := violMk_surjective.comp ofKLR_surjective
  have G₀_high : LinearMap.ker (q).toLinearMap ≤ LinearMap.ker G₀ := by
    intro r hr
    change q r = 0 at hr
    change G₀ r = 0
    have hJ : r ∈ J := by
      change (J).ringCon.mk' r = 0 at hr
      rwa [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk'] at hr
    apply zero_on_ideal_of_zero_on_triples G₀ _ hJ
    rintro _ ⟨s, ho, hs, rfl⟩ a b
    obtain ⟨y,rfl⟩ := surjπ a
    obtain ⟨z,rfl⟩ := surjπ b
    change G₀ (π y * π (KLRAlgebra.e s) * π z) = 0
    rw [← map_mul π, ← map_mul π]
    change G₀ (mk (raw (y * KLRAlgebra.e s * z))) = 0
    rw [G₀_raw]
    exact hbad y s z (Or.inr ⟨ho, hs⟩)
  let G := descendLinear (q).toLinearMap (RingCon.mkₐ_surjective («α» := k) (TwoSidedIdeal.ringCon J)) G₀ G₀_high
  exact ⟨G, fun y =>
    (descendLinear_apply (q).toLinearMap (RingCon.mkₐ_surjective («α» := k) (TwoSidedIdeal.ringCon J)) G₀ G₀_high _).trans (G₀_raw y)⟩

/-- The parabolic coordinates read the quotient by red dots, global violations and
higher source loadings. Reconstruction is by stacking the original coordinate
representatives. Webster v2, Lemma 6.8, proof of the kernel test (6.21). -/
theorem exists_blockStack_quotient_coordinates (hQ : KLRSymm Q)
    (h : weightSum row = stendhalWeight ℓ ν) :
    let S := affineStackBlocks Q Λ L M f β h
    ∃ n, ∃ (g : Fin n → R →ₗ[k] diagrams Q Λ row) (w : Fin n → R)
      (G : Fin n → (J).ringCon.Quotient →ₗ[k] quotients Q Λ row),
      (∀ j y, G j (q (mk (raw y))) = P (g j y)) ∧
      (∀ y, q (mk (raw (S 1 * y))) = ∑ j, q (mk (raw (S (g j y) * w j)))) := by
  classical
  obtain ⟨n, g, w, _, _, _, hsec, _, hbad, rebuild⟩ :=
    exists_blockStack_coordinates_with_bottom Q Λ hQ L M f β h
  have desc (j : Fin n) :=
    exists_quotientBlockCoordinate Q Λ L M f β (g j) (hsec j) (hbad j)
  choose G hG using desc
  refine ⟨n, g, w, G, hG, ?_⟩
  intro y
  have hr := congrArg ((q).comp mk) (rebuild y)
  simpa only [map_sum, AlgHom.comp_apply] using hr

end Categorification.Stendhal.RedBlock

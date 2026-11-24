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
theorem exists_blockStack_filtered_quotient_coordinates (hQ : KLRSymm Q)
    (h : weightSum row = stendhalWeight ℓ ν) :
    let S := affineStackBlocks Q Λ L M f β h
    ∃ n, ∃ (index : Fin n ≃ ShuffleIndex row) (g : Fin n → R →ₗ[k] diagrams Q Λ row) (w : Fin n → R)
      (G : Fin n → (J).ringCon.Quotient →ₗ[k] quotients Q Λ row)
      (bottom : Fin n → Seq μ → diagrams Q Λ row),
      (∀ j y, G j (q (mk (raw y))) = P (g j y)) ∧
      (∀ j, w j = S 1 * ψw (shuffleWord row (index j))) ∧
      (∀ j y n, y ∈ filt k (stendhalQ Q Λ) μ n →
        G j (q (mk (raw y))) ∈ (blockShuffleFilt Q Λ row (index j) n).map (P).toLinearMap) ∧
      (∀ j x y, G j (q (mk (raw (S x * y)))) = P x * G j (q (mk (raw y)))) ∧
      (∀ j y s, G j (q (mk (raw (y * e s)))) = G j (q (mk (raw y))) * P (bottom j s)) ∧
      (∀ j s, bottom j s = 0 ∨ ∃ v : Loadings row,
        ShuffleLoading row (Seq.cast h.symm s) v ∧ bottom j s = loadingIdem Q Λ row v) ∧
      (∀ j y, g j (S 1 * y) = g j y) ∧
      (∀ j, G j (q (mk (raw (w j)))) = 1) ∧
      (∀ i j, i ≠ j → G i (q (mk (raw (w j)))) = 0) ∧
      (∀ y, q (mk (raw (S 1 * y))) = ∑ j, q (mk (raw (S (g j y) * w j)))) := by
  classical
  obtain ⟨n, index, g, w, bottom, hfil, hw, hmul, hbottom, hsec, hself, hother,
      hloading, hbad, rebuild⟩ :=
    exists_blockStack_coordinates_with_filtered_shuffle_words Q Λ hQ L M f β h
  have desc (j : Fin n) :=
    exists_quotientBlockCoordinate Q Λ L M f β (g j) (hsec j) (hbad j)
  choose G hG using desc
  refine ⟨n, index, g, w, G, bottom, hG, hw, ?_, ?_, ?_, hloading, ?_, ?_, ?_, ?_⟩
  · intro j y n hy
    rw [hG]
    exact ⟨g j y, hfil j y n hy, rfl⟩
  · intro j x y
    rw [hG, hmul, map_mul, hG]
  · intro j y s
    rw [hG, hbottom, map_mul, hG]
  · intro j y
    rw [hmul, one_mul]
  · intro j
    rw [hG, hself, map_one]
  · intro i j hij
    rw [hG, hother _ _ hij, map_zero]
  · intro y
    have hr := congrArg ((q).comp mk) (rebuild y)
    simpa only [map_sum, AlgHom.comp_apply] using hr

/-- The parabolic coordinates read the quotient by red dots, global violations and
higher source loadings. Reconstruction is by stacking the original coordinate
representatives. Webster v2, Lemma 6.8, proof of the kernel test (6.21). -/
theorem exists_blockStack_quotient_coordinates (hQ : KLRSymm Q)
    (h : weightSum row = stendhalWeight ℓ ν) :
    let S := affineStackBlocks Q Λ L M f β h
    ∃ n, ∃ (g : Fin n → R →ₗ[k] diagrams Q Λ row) (w : Fin n → R)
      (G : Fin n → (J).ringCon.Quotient →ₗ[k] quotients Q Λ row),
      (∀ j y, G j (q (mk (raw y))) = P (g j y)) ∧
      (∀ j y, g j (S 1 * y) = g j y) ∧
      (∀ j, G j (q (mk (raw (w j)))) = 1) ∧
      (∀ i j, i ≠ j → G i (q (mk (raw (w j)))) = 0) ∧
      (∀ y, q (mk (raw (S 1 * y))) = ∑ j, q (mk (raw (S (g j y) * w j)))) := by
  obtain ⟨n, _, g, w, G, _, hG, _, _, _, _, _, h⟩ :=
    exists_blockStack_filtered_quotient_coordinates Q Λ L M f β hQ h
  exact ⟨n, g, w, G, hG, h⟩

/-- The descended coordinates separate the source-order block column. This uses
reconstruction and the external block-algebra action on that column. -/
theorem exists_blockColumn_coordinate_embedding (hQ : KLRSymm Q)
    (h : weightSum row = stendhalWeight ℓ ν) :
    ∃ n, ∃ F : blockColumn Q Λ L M f β h →ₗ[k] (Fin n → quotients Q Λ row),
      Function.Injective F := by
  classical
  obtain ⟨n, g, w, G, hG, hunit, _, _, rebuild⟩ :=
    exists_blockStack_quotient_coordinates Q Λ L M f β hQ h
  let N := blockColumn Q Λ L M f β h
  let F := stackBlocks Q Λ L M f β h
  let π := (mk).comp raw
  let eκ : R := redIdem k Q Λ κ
  let p := mk (redProj k Q Λ ν κ)
  let S := affineStackBlocks Q Λ L M f β h
  let read : N →ₗ[k] (Fin n → quotients Q Λ row) :=
    LinearMap.pi fun j => (G j).comp (N).subtype
  refine ⟨n, read, (LinearMap.ker_eq_bot (f := read)).1 (LinearMap.ker_eq_bot'.2 ?_)⟩
  intro x hx
  have surjπ : Function.Surjective π := violMk_surjective.comp ofKLR_surjective
  obtain ⟨v, hv⟩ := x.2
  obtain ⟨y, rfl⟩ := surjπ v
  let z := y * eκ
  have rep : x.1 = q (π (S 1 * z)) := by
    change q (F 1 * (π y * p)) = x.1 at hv
    rw [← hv, map_mul π (S 1) z, map_mul π y eκ]
    rfl
  have coeff_zero (j : Fin n) : P (g j z) = 0 := by
    have hc := congrFun hx j
    change G j x.1 = 0 at hc
    rw [rep] at hc
    change G j (q (mk (raw (S 1 * z)))) = 0 at hc
    rwa [hG, hunit] at hc
  have sum_rep : x.1 = ∑ j, q (F (g j z) * π (w j)) := by
    calc
      _ = q (π (S 1 * z)) := rep
      _ = ∑ j, q (π (S (g j z) * w j)) := rebuild z
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        rw [map_mul π]
        rfl
  have right_fixed : x.1 * q p = x.1 := by
    change q (F 1 * (π y * p)) = x.1 at hv
    have hp : IsIdempotentElem p := bottomIdempotent Q Λ L M f
    rw [← hv, ← map_mul (q), mul_assoc, mul_assoc, hp.eq]
  apply Subtype.ext
  change x.1 = 0
  rw [← right_fixed, sum_rep, Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro j _
  let u : N := ⟨q (F 1 * (π (w j) * p)), ⟨π (w j), rfl⟩⟩
  have act := blockProductAction_projection Q Λ L M f β h (g j z) u
  have act_zero : blockProductAction Q Λ L M f β h (P (g j z)) u = 0 := by
    calc
      _ = blockProductAction Q Λ L M f β h 0 u :=
        congrArg (fun v : quotients Q Λ row => blockProductAction Q Λ L M f β h v u)
          (coeff_zero j)
      _ = 0 := LinearMap.congr_fun (map_zero (blockProductAction Q Λ L M f β h)) u
  calc
    _ = q (F (g j z)) * u.1 := by
      change q (F (g j z) * π (w j)) * q p =
        q (F (g j z)) * q (F 1 * (π (w j) * p))
      rw [← map_mul (q), ← map_mul (q), mul_assoc _ (π (w j)) p,
        ← mul_assoc (F (g j z)) (F 1), ← map_mul F, mul_one]
    _ = _ := act.symm
    _ = 0 := congrArg (fun v : N => v.1) act_zero

end Categorification.Stendhal.RedBlock

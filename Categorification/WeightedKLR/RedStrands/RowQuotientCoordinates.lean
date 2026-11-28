/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockQuotientCoordinates

/-!
# Parabolic coordinates on a standard quotient, for any row

Webster, arXiv:1309.3796v3, §6.1, proof of Lemma 6.9 (v2: Lemma 6.8). The quotient
coordinates of `BlockQuotientCoordinates` for an arbitrary row of red blocks and the ideal
`blockUpperIdeal a b α κ`, given that every compatible shuffle of a bad source loading has a
violated block. With `a = b` the cuts are singletons (`cut a a r = {r}`) and the quotient is a
full standard module; this is the input for the matching argument on the cube of the
injectivity proof.

* `exists_rowStack_quotient_coordinates_with_indexed_projectors`.
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
    (row : List (RedBlock I ℓ)) (a b : Fin ℓ) (α : Fin ℓ → I → ℕ) (κ : List (Fin ℓ))
    {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "P" => projection Q Λ row
local notation "J" => blockUpperIdeal k Q Λ ν a b α κ
local notation "raw" => ofKLR k Q Λ ν
local notation "secB" => toKLR k Q Λ ν
local notation "mk" => violMk k Q Λ ν
local notation "q" => RingCon.mkₐ k (TwoSidedIdeal.ringCon J)

/-- Projected parabolic coordinates descend through global violations and through
higher source loadings (Webster v2, Lemma 6.8, proof after (6.21)). -/
private theorem exists_quotientRowCoordinate (g : R →ₗ[k] diagrams Q Λ row)
    (hsec : ∀ y, g (secB (raw y)) = g y)
    (hbad : ∀ (y : R) (s : Seq μ) (z : R),
      (IsViolated s ∨ (redWord s = κ ∧ α < adjacentBlockRoot a b s)) →
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

omit [DecidableEq I] in
private theorem cast_back_seq {w w' : Multiset (I ⊕ Fin ℓ)} (hw : w = w') (t : KLR.Seq w') :
    Seq.cast hw (Seq.cast hw.symm t) = t := by subst w'; rfl

/-- **Bad loadings of an aligned row.** If the red order `κ` is the red order of every
nonviolated loading of an aligned row, then every compatible shuffle of a globally violated
loading, or of a loading of order `κ` above the boundary counts of the row in the cuts of `a`
and `b`, has a violated block (Webster, arXiv:1309.3796v3, proof of Lemma 6.9). -/
theorem violated_of_aligned_shuffleLoading (hal : Aligned a b row)
    (h : weightSum row = stendhalWeight ℓ ν)
    (hκ : ∀ v : Loadings row, ¬ Violated row v → redWord (Seq.cast h (place row v)) = κ)
    (s : Seq μ)
    (hs : IsViolated s ∨ (redWord s = κ ∧
      (fun r i => boundaryCount (cut a b r) i row) < adjacentBlockRoot a b s))
    (v : Loadings row) (hv : ShuffleLoading row (Seq.cast h.symm s) v) : Violated row v := by
  rcases hs with hglobal | ⟨ho, hhigh⟩
  · apply violated_of_shuffleLoading_global row _ v hv
    have cast_violated {w w' : Multiset (I ⊕ Fin ℓ)} (hww : w = w') (t : Seq w)
        (ht : IsViolated t) : IsViolated (Seq.cast hww t) := by
      subst w'
      simpa using ht
    exact cast_violated h.symm s hglobal
  · by_contra hn
    apply hn
    apply violated_of_shuffleLoading_higher h hal _ v hv
    · rw [cast_back_seq, ho, hκ v hn]
    · rwa [cast_back_seq]

/-- **Quotient coordinates for any row** (Webster, arXiv:1309.3796v3, proof of Lemma 6.9;
v2: Lemma 6.8, after (6.21)). The parabolic coordinates of the juxtaposed-top column descend
to the quotient by global violations and by the loadings of order `κ` above `α` in the cuts of
`a` and `b`, provided every compatible shuffle of such a loading has a violated block. -/
theorem exists_rowStack_quotient_coordinates_with_indexed_projectors (hQ : KLRSymm Q)
    (h : weightSum row = stendhalWeight ℓ ν)
    (hbad : ∀ s : Seq μ, (IsViolated s ∨ (redWord s = κ ∧ α < adjacentBlockRoot a b s)) →
      ∀ v : Loadings row, ShuffleLoading row (Seq.cast h.symm s) v → Violated row v) :
    let S := rowStack Q Λ row h
    ∃ n, ∃ (index : Fin n ≃ ShuffleIndex row) (g : Fin n → R →ₗ[k] diagrams Q Λ row) (w : Fin n → R)
      (G : Fin n → (J).ringCon.Quotient →ₗ[k] quotients Q Λ row)
      (bottom : Fin n → Seq μ → diagrams Q Λ row),
      (∀ j y, G j (q (mk (raw y))) = P (g j y)) ∧
      (∀ j, w j = S 1 * ψw (shuffleWord row (index j))) ∧
      (∀ j y n, y ∈ filt k (stendhalQ Q Λ) μ n →
        G j (q (mk (raw y))) ∈ (blockShuffleFilt Q Λ row (index j) n).map (P).toLinearMap) ∧
      (∀ j x y, G j (q (mk (raw (S x * y)))) = P x * G j (q (mk (raw y)))) ∧
      (∀ j y s, G j (q (mk (raw (y * e s)))) = G j (q (mk (raw y))) * P (bottom j s)) ∧
      (∀ j s, IndexedLoadingProjector Q Λ row (index j) (Seq.cast h.symm s) (bottom j s)) ∧
      (∀ j y, g j (S 1 * y) = g j y) ∧
      (∀ j, G j (q (mk (raw (w j)))) = 1) ∧
      (∀ i j, i ≠ j → G i (q (mk (raw (w j)))) = 0) ∧
      (∀ y, q (mk (raw (S 1 * y))) = ∑ j, q (mk (raw (S (g j y) * w j)))) := by
  classical
  obtain ⟨n, index, g, w, bottom, hfil, hw, hmul, hbottom, hsec, hself, hother,
      hloading, hbad, rebuild⟩ :=
    exists_rowStack_coordinates_with_indexed_projectors Q Λ hQ row h _ hbad
  have desc (j : Fin n) :=
    exists_quotientRowCoordinate Q Λ row a b α κ (g j) (hsec j) (hbad j)
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

end Categorification.Stendhal.RedBlock

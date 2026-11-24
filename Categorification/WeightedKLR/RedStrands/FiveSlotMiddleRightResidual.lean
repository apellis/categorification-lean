/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.AffineHigherKernelMap
import Categorification.WeightedKLR.RedStrands.FiveSlotMiddleRightHigher
import Categorification.WeightedKLR.RedStrands.FiveSlotLastRedSquare
import Categorification.WeightedKLR.RedStrands.FiveSlotMiddleRightCrossing
import Categorification.WeightedKLR.RedStrands.FiveSlotPrincipalHigherDerived
import Categorification.WeightedKLR.RedStrands.FiveSlotAllTops
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The residual higher quotient at the middle-right loading

Webster, arXiv:1309.3796v2, proof of Lemma 6.8 at (6.21).
After quotienting out the central-crossing image, the nearby partial standard
maps surjectively onto the remaining higher quotient. Its injectivity is
equivalent to saturation of the nearby kernel against the central crossing.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLRAlgebra TypeA
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Module

variable {A P P' M : Type} [Ring A]
  [AddCommGroup P] [Module A P] [AddCommGroup P'] [Module A P']
  [AddCommGroup M] [Module A M]

private theorem quotient_map_of_two_images
    (first : P →ₗ[A] M) (second : P' →ₗ[A] M) (N : Submodule A P')
    (vanish : ∀ x ∈ N, ∃ y : P, first y = second x)
    (gen : ∀ x : M, ∃ y : P, ∃ z : P', first y + second z = x) :
    ∃ f : (P' ⧸ N) →ₗ[A] (M ⧸ first.range), Function.Surjective f ∧
      (Function.Injective f ↔ ∀ x : P', (∃ y : P, first y = second x) → x ∈ N) := by
  let G := first.range.mkQ.comp second
  have hker : N ≤ LinearMap.ker G := by
    intro x hx
    obtain ⟨y, hy⟩ := vanish x hx
    exact (Submodule.Quotient.mk_eq_zero first.range).2 ⟨y, hy⟩
  refine ⟨N.liftQ G hker, ?_, ?_⟩
  · intro q
    obtain ⟨x, rfl⟩ := first.range.mkQ_surjective q
    obtain ⟨y, z, hz⟩ := gen x
    use N.mkQ z
    change N.liftQ G hker (Submodule.Quotient.mk z) = first.range.mkQ x
    rw [Submodule.liftQ_apply]
    change first.range.mkQ (second z) = first.range.mkQ x
    have hz₀ : first.range.mkQ (first y) = 0 := (Submodule.Quotient.mk_eq_zero first.range).2 ⟨y, rfl⟩
    rw [← hz, map_add, hz₀, zero_add]
  · constructor
    · intro injective x hx
      apply (Submodule.Quotient.mk_eq_zero N).1
      apply injective
      rw [map_zero, Submodule.liftQ_apply]
      exact (Submodule.Quotient.mk_eq_zero first.range).2 hx
    · intro sat
      apply LinearMap.ker_eq_bot.1
      apply Submodule.ker_liftQ_eq_bot
      intro x hx
      exact sat x ((Submodule.Quotient.mk_eq_zero first.range).1 hx)

end Module

variable {k : Type} [CommRing k] (Q : Unit → Unit → MvPolynomial (Fin 2) k)
  (Λ : Fin 3 → Unit →₀ ℕ)

local notation "ν₀" => ({()} + {()} : Multiset Unit)
local notation "μ₀" => stendhalWeight 3 ν₀
local notation "N" => Multiset.card μ₀
local notation "rightMiddle" => sadj N 2 • fixedTopFourExitCut 2
local notation "central" => fixedTopFourExitCut 1
local notation "nearby" => sadj N 2 • fixedTopFourExitCut 0
local notation "κ" => redWord rightMiddle
local notation "T" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν₀ κ)
local notation "K" => blockLoadingKernel Q Λ rightMiddle 1 2
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ₀
local notation "V" => ViolQuotient k Q Λ ν₀
local notation "F" => AlgHom.comp (violMk k Q Λ ν₀) (ofKLR k Q Λ ν₀)
local notation "E" => violMk k Q Λ ν₀ (redProj k Q Λ ν₀ κ)
local notation "p" => fun s : Seq μ₀ => F (e s)
local notation "c₁" => (ψ 1 * e central : R)
local notation "c₂" => (ψw [3, 2, 1] * e nearby : R)

private theorem central_order : redWord central = κ := by decide
private theorem nearby_order : redWord nearby = κ := by decide

private theorem central_higher : adjacentBlockRoot 1 2 rightMiddle < adjacentBlockRoot 1 2 central := by
  apply lt_of_le_not_ge
  · intro r i
    fin_cases r <;> cases i <;> decide
  · intro h
    exact (by decide : ¬ adjacentBlockRoot 1 2 central 1 () ≤ adjacentBlockRoot 1 2 rightMiddle 1 ())
      (h 1 ())

private theorem nearby_higher : adjacentBlockRoot 1 2 rightMiddle < adjacentBlockRoot 1 2 nearby := by
  apply lt_of_le_not_ge
  · intro r i
    fin_cases r <;> cases i <;> decide
  · intro h
    exact (by decide : ¬ adjacentBlockRoot 1 2 nearby 1 () ≤ adjacentBlockRoot 1 2 rightMiddle 1 ())
      (h 1 ())

private theorem central_left : AffineLeftFixed Q Λ rightMiddle c₁ := by
  have step : sadj N 1 • central = rightMiddle := by decide +kernel
  change (e rightMiddle : R) * (ψ 1 * e central) = ψ 1 * e central
  simp only [ψ_mul_e, step, ← mul_assoc, e_mul_self]

private theorem central_right : AffineRightFixed Q Λ central c₁ := by
  change (ψ 1 * e central : R) * e central = ψ 1 * e central
  rw [mul_assoc, e_mul_self]

private theorem nearby_left : AffineLeftFixed Q Λ rightMiddle c₂ := by
  have step : wordProd N [3, 2, 1] • nearby = rightMiddle := by decide +kernel
  change (e rightMiddle : R) * (ψw [3, 2, 1] * e nearby) = ψw [3, 2, 1] * e nearby
  rw [← step, ← mul_assoc, e_mul_ψw, inv_smul_smul, mul_assoc, e_mul_self]

private theorem nearby_right : AffineRightFixed Q Λ nearby c₂ := by
  change (ψw [3, 2, 1] * e nearby : R) * e nearby = ψw [3, 2, 1] * e nearby
  rw [mul_assoc, e_mul_self]

local notation "d₁" => orderedLoadingIdemAt Q Λ κ central central_order
local notation "d₂" => orderedLoadingIdemAt Q Λ κ nearby nearby_order
local notation "P₁" => rIdeal d₁
local notation "P₂" => rIdeal d₂
local notation "K₂" => blockLoadingKernelAt Q Λ nearby 1 2 κ nearby_order

/-- Multiplication by the central crossing, with the higher loading
projective as its source. -/
def fiveSlotMiddleRight_centralMap : P₁ →ₗ[Tᵐᵒᵖ] K :=
  affineIntoKernelMap Q Λ 1 2 central_order central_higher c₁ (central_right Q Λ)

/-- The second word from the nearby loading gives a second projective map. -/
def fiveSlotMiddleRight_nearbyMap : P₂ →ₗ[Tᵐᵒᵖ] K :=
  affineIntoKernelMap Q Λ 1 2 nearby_order nearby_higher c₂ (nearby_right Q Λ)

theorem fiveSlotMiddleRight_centralMap_eq_crossing :
    fiveSlotMiddleRight_centralMap Q Λ =
      crossingIntoKernelMap Q Λ 1 2 central_order central_higher 1 := rfl

local notation "f₁" => fiveSlotMiddleRight_centralMap Q Λ
local notation "f₂" => fiveSlotMiddleRight_nearbyMap Q Λ
local notation "J₁" => LinearMap.range f₁

private theorem centralMap_val (u : P₁) : (f₁ u).1.1.1 = F c₁ * u.1.1 :=
  affineIntoKernelMap_val Q Λ 1 2 central_order central_higher c₁ (central_left Q Λ) (central_right Q Λ) u

private theorem nearbyMap_val (u : P₂) : (f₂ u).1.1.1 = F c₂ * u.1.1 :=
  affineIntoKernelMap_val Q Λ 1 2 nearby_order nearby_higher c₂ (nearby_left Q Λ) (nearby_right Q Λ) u

private theorem mem_nearby_kernel {ω : List (Fin 3)} (hω : redWord nearby = ω)
    (u : rIdeal (orderedLoadingIdemAt Q Λ ω nearby hω)) :
    u ∈ blockLoadingKernelAt Q Λ nearby 1 2 ω hω ↔
      u.1.1 ∈ blockUpperIdeal k Q Λ ν₀ 1 2 (adjacentBlockRoot 1 2 nearby) ω := by
  subst ω
  rfl

private theorem nearby_kernel_maps_into_central (hQ : KLRSymm Q) (x : P₂) (hx : x ∈ K₂) :
    ∃ a : P₁, f₁ a = f₂ x := by
  have hxJ : x.1.1 ∈ blockUpperIdeal k Q Λ ν₀ 1 2
      (adjacentBlockRoot 1 2 nearby) (redWord nearby) := by
    rw [nearby_order]
    exact (mem_nearby_kernel Q Λ nearby_order x).1 hx
  have xl : p nearby * x.1.1 = x.1.1 := congrArg (fun u : T => u.1) x.2
  obtain ⟨z, hz⟩ := fiveSlotMiddleRight_second_factors_higher_nearby Q Λ hQ x.1.1 hxJ xl
  let a₀ : T := ⟨E * z * E, z, rfl⟩
  have idem : IsIdempotentElem d₁ := by
    apply Subtype.ext
    change p central * p central = p central
    rw [← map_mul, e_mul_self]
  let a : P₁ := rIdealProj idem a₀
  have h₁ : F c₁ * p central = F c₁ := by
    rw [← map_mul]
    exact congrArg F (central_right Q Λ)
  have hpE : p central * E = p central := by
    change violMk k Q Λ ν₀ (ofKLR k Q Λ ν₀ (e central)) * E = _
    rw [← map_mul, e_mul_redProj, ite_eq_left central_order]
    rfl
  have h₁E : F c₁ * E = F c₁ := by
    rw [← h₁, mul_assoc, hpE]
  have xr : x.1.1 * E = x.1.1 :=
    CornerEndomorphism.corner_mul_right
      (isIdempotentElem_violMk_redProj k Q Λ ν₀ κ) x.1
  have hrep : f₁ a = f₂ x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rw [centralMap_val, nearbyMap_val]
    change F c₁ * (p central * (E * z * E)) = F c₂ * x.1.1
    calc
      _ = (F c₁ * p central * E) * z * E := by simp only [mul_assoc]
      _ = (F c₂ * x.1.1) * E := by rw [h₁, h₁E, ← hz]
      _ = _ := by rw [mul_assoc, xr]
  exact ⟨a, hrep⟩

private theorem middleRight_generated_by_maps (hQ : KLRSymm Q) (x : K) :
    ∃ u : P₁, ∃ v : P₂, f₁ u + f₂ v = x := by
  obtain ⟨a, b, ha, hb, hx⟩ := fiveSlotMiddleRight_blockLoadingKernel_two_factors Q Λ hQ x
  let u : P₁ := ⟨a, Subtype.ext ha⟩
  let v : P₂ := ⟨b, Subtype.ext hb⟩
  have sum : f₁ u + f₂ v = x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    change (f₁ u).1.1.1 + (f₂ v).1.1.1 = x.1.1.1
    exact (congrArg₂ (fun a b : V => a + b)
      (centralMap_val Q Λ u) (nearbyMap_val Q Λ v)).trans hx.symm
  exact ⟨u, v, sum⟩

/-- The actual nearby higher partial standard surjects onto the remainder
of the middle-right higher kernel after the central crossing. -/
theorem fiveSlotMiddleRight_residual_quotient_of_nearby (hQ : KLRSymm Q) :
    ∃ f : (blockPartialStandardAt Q Λ nearby 1 2 κ nearby_order) →ₗ[Tᵐᵒᵖ] (K ⧸ J₁),
      Function.Surjective f ∧
      (Function.Injective f ↔ ∀ x : P₂, (∃ y : P₁, f₁ y = f₂ x) → x ∈ K₂) := by
  let : AddCommGroup P₁ := Submodule.addCommGroup _
  let : Module Tᵐᵒᵖ P₁ := Submodule.module _
  let : AddCommGroup P₂ := Submodule.addCommGroup _
  let : Module Tᵐᵒᵖ P₂ := Submodule.module _
  change ∃ f : (P₂ ⧸ K₂) →ₗ[Tᵐᵒᵖ] (K ⧸ J₁), Function.Surjective f ∧
    (Function.Injective f ↔ ∀ x : P₂, (∃ y : P₁, f₁ y = f₂ x) → x ∈ K₂)
  exact quotient_map_of_two_images (A := Tᵐᵒᵖ) (P := P₁) (P' := P₂) (M := K)
    f₁ f₂ K₂ (nearby_kernel_maps_into_central Q Λ hQ) (middleRight_generated_by_maps Q Λ hQ)

section ResidualSaturation

local notation "ν" => ν₀
local notation "n" => N
local notation "A" => nearby
local notation "D" => sadj n 1 • A
local notation "δ" => F (ψ 1 * e A)
local notation "τ" => F (ψ 2 * e D)
local notation "X" => -F (x (⟨3, by decide⟩ : Fin n))
local notation "Y" => F (x (⟨2, by decide⟩ : Fin n))

private theorem dividedSquare : τ * τ = (0 : V) := by
  rw [← map_mul]
  suffices h : (ψ 2 * e D : R) * (ψ 2 * e D) = 0 by rw [h, map_zero]
  have hfix : sadj n 2 • D = D := by decide +kernel
  have h := KLRAlgebra.ψ_sq (Q := stendhalQ Q Λ) 2 (by decide : 2 + 1 < n) D
  rw [ite_eq_left (by decide)] at h
  have hd : (e D : R) * (ψ 2 * e D) = ψ 2 * e D := by
    simp only [ψ_mul_e, hfix, ← mul_assoc, e_mul_self]
  calc
    _ = ψ 2 * (ψ 2 * e D) := by rw [mul_assoc, hd]
    _ = 0 := by rwa [← mul_assoc]

private theorem earlierCrossing_dot : δ * X = X * δ := by
  rw [mul_neg, neg_mul, ← map_mul F, ← map_mul F]
  apply congrArg (fun a : R => -F a)
  rw [mul_assoc, ← x_mul_e, ← mul_assoc,
    ← x_mul_ψ (Q := stendhalQ Q Λ) (⟨3, by decide⟩ : Fin n) 1 (by decide) (by decide), mul_assoc]

private theorem earlierCrossing_left : p D * δ = δ := by
  rw [← map_mul]
  apply congrArg F
  simp only [ψ_mul_e, ← mul_assoc, e_mul_self]

private theorem divided_dot : τ * X = p D - Y * τ := by
  rw [mul_neg, ← map_mul F, ← map_mul F, ← map_sub F, ← map_neg F]
  apply congrArg F
  have h := dot_cross_left (Q := stendhalQ Q Λ) (k := k) 2 (by decide : 2 + 1 < n) D
  rw [ite_eq_left (by decide), sub_mul] at h
  have hh : -(ψ 2 * x (⟨3, by decide⟩ : Fin n) * e D : R) = e D - x (⟨2, by decide⟩ : Fin n) * ψ 2 * e D := by
    calc
      _ = (x (⟨2, by decide⟩ : Fin n) * ψ 2 * e D -
        ψ 2 * x (⟨3, by decide⟩ : Fin n) * e D) -
        x (⟨2, by decide⟩ : Fin n) * ψ 2 * e D := by abel
      _ = _ := by rw [h]
  have move : ((ψ 2 * e D) * x (⟨3, by decide⟩ : Fin n) : R) =
      ψ 2 * x (⟨3, by decide⟩ : Fin n) * e D := by
    rw [mul_assoc, ← x_mul_e, ← mul_assoc]
  rw [move]
  simpa only [mul_assoc] using hh

/-- Once the commuting square for the independent red crossings is
Cartesian, the remaining same-color overlap is controlled by the
nilHecke square-zero relation and the dot commutator. -/
theorem fiveSlotMiddleRight_divided_overlap_mem
    (J : TwoSidedIdeal V)
    (hker : ∀ y : V, p A * y = y → y * violMk k Q Λ ν (redProj k Q Λ ν (redWord A)) = y →
      τ * (δ * y) = 0 → y ∈ J)
    (y z : V) (hy : p A * y = y) (hz : p A * z = z)
    (hyr : y * violMk k Q Λ ν (redProj k Q Λ ν (redWord A)) = y)
    (hzr : z * violMk k Q Λ ν (redProj k Q Λ ν (redWord A)) = z)
    (hoverlap : τ * (δ * y) = δ * z) : y ∈ J := by
  have hzero : τ * (δ * z) = 0 := by
    rw [← hoverlap, ← mul_assoc, dividedSquare Q Λ, zero_mul]
  have hZ : z ∈ J := hker z hz hzr hzero
  have hdot : τ * (δ * (X * z)) = δ * z := by
    rw [← mul_assoc δ, earlierCrossing_dot Q Λ, mul_assoc X, ← mul_assoc τ,
      divided_dot Q Λ, sub_mul, ← mul_assoc (p D), earlierCrossing_left Q Λ,
      mul_assoc Y, hzero, mul_zero, sub_zero]
  have hsub : τ * (δ * (y - X * z)) = 0 := by
    rw [mul_sub, mul_sub, hoverlap, hdot, sub_self]
  have hcomm : p A * X = X * p A := by
    rw [mul_neg, neg_mul, ← map_mul F, ← map_mul F, x_mul_e]
  have hfix : p A * (y - X * z) = y - X * z := by
    rw [mul_sub, hy, ← mul_assoc, hcomm, mul_assoc, hz]
  have hfixr : (y - X * z) * violMk k Q Λ ν (redProj k Q Λ ν (redWord A)) = y - X * z := by
    rw [sub_mul, hyr, mul_assoc, hzr]
  have hd : X * z ∈ J := TwoSidedIdeal.mul_mem_left _ _ _ hZ
  simpa only [sub_add_cancel] using J.add_mem (hker _ hfix hfixr hsub) hd

local notation "C" => fixedTopFourExitCut 1
local notation "B" => sadj n 3 • D
local notation "β" => F (ψ 3 * e D)
local notation "β'" => F (ψ 3 * e B)
local notation "c" => F (ψ 1 * e C)
local notation "α'" => F (ψ 3 * e C)

private theorem inverseLastCrossing (weight : Λ 2 () = 0) : β' * β = p D := by
  rw [← map_mul F]
  refine congrArg F ?_
  have hd : (e B : R) * (ψ 3 * e D) = ψ 3 * e D := by
    simp only [ψ_mul_e, ← mul_assoc, e_mul_self]
  have labels₀ : (D).lbl ⟨3, by decide⟩ = Sum.inl () := by decide
  have labels₁ : (D).lbl ⟨4, by decide⟩ = Sum.inr 2 := by decide
  have h := KLRAlgebra.ψ_sq (Q := stendhalQ Q Λ) (k := k) 3 (by decide : 3 + 1 < n) D
  have dots : (![x (⟨3, by decide⟩ : Fin n), x (⟨4, by decide⟩ : Fin n)] : Fin 2 → R) =
      fun a => x (![⟨3, by decide⟩, ⟨4, by decide⟩] a) := by
    funext a
    fin_cases a <;> rfl
  rw [labels₀, labels₁, ite_eq_right (by decide), stendhalQ_inl_inr, weight, pow_zero,
    dots, ncEval_eq_pol, map_one, map_one, one_mul] at h
  rw [mul_assoc, hd, ← mul_assoc, h]

private theorem oppositeCrossings_commute : β' * c = δ * α' := by
  rw [← map_mul F, ← map_mul F]
  refine congrArg F ?_
  have hBC : sadj n 1 • C = B := by decide +kernel
  have hCA : sadj n 3 • C = A := by decide +kernel
  have hc : (e B : R) * (ψ 1 * e C) = ψ 1 * e C := by
    simp only [ψ_mul_e, hBC, ← mul_assoc, e_mul_self]
  have ha : (e A : R) * (ψ 3 * e C) = ψ 3 * e C := by
    simp only [ψ_mul_e, hCA, ← mul_assoc, e_mul_self]
  rw [mul_assoc, hc, mul_assoc, ha, ← mul_assoc, ← mul_assoc,
    ψ_mul_ψ (Q := stendhalQ Q Λ) 1 3 (by decide)]

private theorem oppositeCrossing_left : p A * α' = α' := by
  rw [← map_mul]
  apply congrArg F
  have ha : sadj n 3 • C = A := by decide +kernel
  simp only [ψ_mul_e, ha, ← mul_assoc, e_mul_self]

/-- At weight zero on the last red strand, its crossing has explicit inverse.
Thus overlap after the final crossing is already overlap before it. -/
theorem fiveSlotMiddleRight_overlap_before_lastRed_zeroWeight (weight : Λ 2 () = 0)
    (u v : V) (hfixed : p D * u = u)
    (hr : v * violMk k Q Λ ν (redProj k Q Λ ν (redWord A)) = v)
    (h : β * u = c * v) :
    ∃ z : V, p A * z = z ∧
      z * violMk k Q Λ ν (redProj k Q Λ ν (redWord A)) = z ∧ u = δ * z := by
  refine ⟨α' * v, ?_, ?_, ?_⟩
  · rw [← mul_assoc, oppositeCrossing_left Q Λ]
  · rw [mul_assoc, hr]
  calc
    u = (β' * β) * u := by rw [inverseLastCrossing Q Λ weight, hfixed]
    _ = δ * (α' * v) := by
      rw [mul_assoc, h, ← mul_assoc, oppositeCrossings_commute Q Λ, mul_assoc]

open FiveSlotFlag

local notation "leftExtreme" => fixedTopFourExitCut 0
local notation "J₂" => blockUpperIdeal k Q Λ ν 1 2 (adjacentBlockRoot 1 2 A) (redWord A)
local notation "Eₐ" => violMk k Q Λ ν (redProj k Q Λ ν (redWord A))

private theorem nearbySecondCrossing_factor : τ * δ = F (ψw [2, 1] * e A) := by
  rw [← map_mul F]
  apply congrArg F
  simpa only [List.cons_append, List.nil_append, ψw_cons, ψw_nil, mul_one] using
    cut_word_mul Q Λ [2] [1] A D (by decide +kernel)

private theorem nearbySecondCrossing_mem_higher (hQ : KLRSymm Q)
    (y : V) (hl : p A * y = y) (hr : y * Eₐ = y) (h0 : τ * (δ * y) = 0) :
    y ∈ J₂ := by
  rw [← mul_assoc, nearbySecondCrossing_factor Q Λ] at h0
  have he : redWord A = redWord leftExtreme := by decide
  obtain ⟨z, hz, _, rfl⟩ := fiveSlotLastRed_secondCrossing_mem_leftExtremeImage Q Λ hQ
    y hl (by simpa only [redProj, he, AlgHom.comp_apply] using hr) h0
  have higher : adjacentBlockRoot 1 2 A < adjacentBlockRoot 1 2 leftExtreme := by
    apply lt_of_le_not_ge
    · intro r i
      fin_cases r <;> cases i <;> decide
    · intro h
      exact (by decide : ¬ adjacentBlockRoot 1 2 leftExtreme 1 () ≤ adjacentBlockRoot 1 2 A 1 ())
        (h 1 ())
  have hi : p leftExtreme ∈ J₂ := TwoSidedIdeal.subset_span ⟨leftExtreme, he.symm, higher, rfl⟩
  rw [← hz]
  exact TwoSidedIdeal.mul_mem_left _ _ _ (TwoSidedIdeal.mul_mem_right _ _ _ hi)

private theorem middleRightSecond_factor : β * (τ * δ) = F c₂ := by
  rw [nearbySecondCrossing_factor Q Λ, ← map_mul F]
  apply congrArg F
  simpa only [List.cons_append, List.nil_append, ψw_cons, ψw_nil, mul_one] using
    cut_word_mul Q Λ [3] [2, 1] A D (by decide +kernel)

/-- The crossing-square overlap identifies the residual higher kernel with
the nearby partial standard. -/
theorem fiveSlotMiddleRight_residual_equiv_of_crossing_overlap (hQ : KLRSymm Q)
    (square : ∀ u v : V, p D * u = u → u * Eₐ = u → p C * v = v → v * Eₐ = v →
      β * u = c * v →
      ∃ z : V, p A * z = z ∧ z * Eₐ = z ∧ u = δ * z) :
    Nonempty ((blockPartialStandardAt Q Λ nearby 1 2 κ nearby_order) ≃ₗ[Tᵐᵒᵖ] (K ⧸ J₁)) := by
  obtain ⟨f, hsurj, hinj⟩ := fiveSlotMiddleRight_residual_quotient_of_nearby Q Λ hQ
  refine ⟨LinearEquiv.ofBijective f ⟨hinj.2 ?_, hsurj⟩⟩
  intro y hy
  obtain ⟨z, hz⟩ := hy
  have hrep : c * z.1.1 = F c₂ * y.1.1 :=
    (centralMap_val Q Λ z).symm.trans ((congrArg (fun a : K => a.1.1.1) hz).trans
      (nearbyMap_val Q Λ y))
  have hyl : p A * y.1.1 = y.1.1 := congrArg Subtype.val y.2
  have hyr : y.1.1 * Eₐ = y.1.1 := by
    have he : redWord A = κ := by decide
    simpa only [he] using CornerEndomorphism.corner_mul_right _ y.1
  have hzl : p C * z.1.1 = z.1.1 := congrArg Subtype.val z.2
  have hzr : z.1.1 * Eₐ = z.1.1 := by
    have he : redWord A = κ := by decide
    simpa only [he] using CornerEndomorphism.corner_mul_right _ z.1
  have hfixed : p D * (τ * (δ * y.1.1)) = τ * (δ * y.1.1) := by
    have he : p D * τ = τ := by
      rw [← map_mul F]
      apply congrArg F
      have hfix : sadj n 2 • D = D := by decide +kernel
      simp only [ψ_mul_e, hfix, ← mul_assoc, e_mul_self]
    rw [← mul_assoc, he]
  obtain ⟨b, hbl, hbr, hoverlap⟩ :=
    square _ _ hfixed (by simp only [mul_assoc, hyr]) hzl hzr (by
      rw [← mul_assoc τ, ← mul_assoc β, middleRightSecond_factor Q Λ, hrep])
  change y.1.1 ∈ J₂
  exact fiveSlotMiddleRight_divided_overlap_mem Q Λ J₂
    (nearbySecondCrossing_mem_higher Q Λ hQ) _ _ hyl hbl hyr hbr hoverlap

/-- The actual residual higher kernel at the middle-right loading is the
nearby partial standard. -/
theorem fiveSlotMiddleRight_residual_equiv (hQ : KLRSymm Q) :
    Nonempty ((blockPartialStandardAt Q Λ nearby 1 2 κ nearby_order) ≃ₗ[Tᵐᵒᵖ] (K ⧸ J₁)) := by
  apply fiveSlotMiddleRight_residual_equiv_of_crossing_overlap Q Λ hQ
  intro u v hu hur hv hvr rel
  have hD : D = fiveSlotRightLoading 2 := by decide +kernel
  have hA : A = fiveSlotHigherLoading 2 := by decide +kernel
  have hE : Eₐ = F (redIdem k Q Λ (redWord (fixedTopFourExitCut 0))) := by
    have order : redWord A = redWord (fixedTopFourExitCut 0) := by decide
    simpa only [redProj, AlgHom.comp_apply] using
      congrArg (fun w => F (redIdem k Q Λ w)) order
  have h := FiveSlotFlag.fiveSlotLastRed_square_reflects_earlierCrossing Q Λ hQ u v
    (by simpa only [hD] using hu) hv
    (by simpa only [hE] using hur) (by simpa only [hE] using hvr)
    (by simpa only [← hD, ψw_cons, ψw_nil, mul_one] using rel)
  obtain ⟨z, hleft, hright, hvalue⟩ := h
  exact ⟨z, by simpa only [hA] using hleft, by simpa only [hE] using hright,
    by simpa only [hA] using hvalue⟩

/-- For a weight-zero final red strand, the residual higher layer at the
middle-right loading is the actual nearby partial standard. -/
theorem fiveSlotMiddleRight_residual_equiv_of_lastWeight_zero (hQ : KLRSymm Q)
    (weight : Λ 2 () = 0) :
    Nonempty ((blockPartialStandardAt Q Λ nearby 1 2 κ nearby_order) ≃ₗ[Tᵐᵒᵖ] (K ⧸ J₁)) :=
  fiveSlotMiddleRight_residual_equiv_of_crossing_overlap Q Λ hQ
    (fun u v hu _ _ hv h =>
      fiveSlotMiddleRight_overlap_before_lastRed_zeroWeight Q Λ weight u v hu hv h)

end ResidualSaturation

set_option backward.isDefEq.respectTransparency false in
/-- The central projective embeds as the first piece, and the second
subquotient is the nearby partial standard. -/
theorem fiveSlotMiddleRight_kernel_twoLayer_of_residual
    (residual : Nonempty ((blockPartialStandardAt Q Λ nearby 1 2 κ nearby_order) ≃ₗ[Tᵐᵒᵖ] (K ⧸ J₁)))
    (injective : Function.Injective f₁) :
    ModuleFiltration.HasFiltration
      (fun b : Bool => if b then ModuleCat.of Tᵐᵒᵖ P₁ else
        blockPartialStandardAt Q Λ nearby 1 2 κ nearby_order)
      [false, true] (ModuleCat.of Tᵐᵒᵖ K) := by
  let L := fun b : Bool => if b then ModuleCat.of Tᵐᵒᵖ P₁ else
    blockPartialStandardAt Q Λ nearby 1 2 κ nearby_order
  let Z := ModuleCat.of Tᵐᵒᵖ (K ⧸ J₁)
  obtain ⟨equiv⟩ := residual
  have hexact : Function.Exact f₁ (J₁).mkQ := by
    intro y
    exact Submodule.Quotient.mk_eq_zero J₁
  exact ModuleFiltration.HasFiltration.cons (L := L) (Z := Z) f₁ (J₁).mkQ [true] false
    injective hexact (J₁).mkQ_surjective
    (ModuleFiltration.HasFiltration.single (LinearEquiv.refl _ _)) ⟨equiv.symm⟩

/-- The two-step kernel filtration at zero final red weight. -/
theorem fiveSlotMiddleRight_kernel_twoLayer_of_lastWeight_zero (hQ : KLRSymm Q)
    (weight : Λ 2 () = 0) (injective : Function.Injective f₁) :
    ModuleFiltration.HasFiltration
      (fun b : Bool => if b then ModuleCat.of Tᵐᵒᵖ P₁ else
        blockPartialStandardAt Q Λ nearby 1 2 κ nearby_order)
      [false, true] (ModuleCat.of Tᵐᵒᵖ K) :=
  fiveSlotMiddleRight_kernel_twoLayer_of_residual Q Λ
    (fiveSlotMiddleRight_residual_equiv_of_lastWeight_zero Q Λ hQ weight) injective

universe w

section Derived

open CategoryTheory CategoryTheory.Limits DG DG.DerivedCategory
open scoped DG.DegreeZero
attribute [local instance 1200] Ring.toIntAlgebra

variable (target : List (Fin 3))

local notation "U" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν₀ target)
local notation "Braid" => braidingFunctor k Q Λ ν₀ κ target

set_option backward.isDefEq.respectTransparency false in
/-- The two-step kernel filtration gives concentration when the nearby
partial standard is concentrated and the ordinary balanced test is known. -/
private theorem fiveSlotMiddleRight_partialStandard_braid_homology_vanish_of_residual_layers
    (residual : Nonempty ((blockPartialStandardAt Q Λ nearby 1 2 κ nearby_order) ≃ₗ[Tᵐᵒᵖ] (K ⧸ J₁)))
    (injective : Function.Injective f₁)
    [HasDerivedCategory.{w, 0}
      (isIdempotentElem_violMk_redProj k Q Λ ν₀ κ).Cornerᵐᵒᵖ]
    [HasDerivedCategory.{w, 0}
      (isIdempotentElem_violMk_redProj k Q Λ ν₀ target).Cornerᵐᵒᵖ]
    (hnearby : ∀ j : ℤ, j ≠ 0 → IsZero ((homologyFunctor (A := Uᵐᵒᵖ) ℤ j).obj
      ((Braid).obj (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor Tᵐᵒᵖ).obj
        (blockPartialStandardAt Q Λ nearby 1 2 κ nearby_order))))))
    (hbal : Function.Injective (blockKernelTensorInclusion Q Λ rightMiddle 1 2 target))
    (j : ℤ) (hn : j ≠ 0) :
    IsZero ((homologyFunctor (A := Uᵐᵒᵖ) ℤ j).obj ((Braid).obj
      (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor Tᵐᵒᵖ).obj
        (blockLoadingShortComplex Q Λ rightMiddle 1 2).X₃)))) := by
  apply blockPartialStandard_braid_homology_vanish Q Λ rightMiddle 1 2 target
    (fiveSlotMiddleRight_kernel_twoLayer_of_residual Q Λ residual injective) _ hbal j hn
  intro b _ i hi
  cases b
  · exact hnearby i hi
  · exact blockLoadingProjective_braid_homology_vanish Q Λ central target i hi

set_option backward.isDefEq.respectTransparency false in
theorem fiveSlotMiddleRight_partialStandard_braid_homology_vanish_of_layers
    (hQ : KLRSymm Q) (weight : Λ 2 () = 0) (injective : Function.Injective f₁)
    [HasDerivedCategory.{w, 0}
      (isIdempotentElem_violMk_redProj k Q Λ ν₀ κ).Cornerᵐᵒᵖ]
    [HasDerivedCategory.{w, 0}
      (isIdempotentElem_violMk_redProj k Q Λ ν₀ target).Cornerᵐᵒᵖ]
    (hnearby : ∀ j : ℤ, j ≠ 0 → IsZero ((homologyFunctor (A := Uᵐᵒᵖ) ℤ j).obj
      ((Braid).obj (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor Tᵐᵒᵖ).obj
        (blockPartialStandardAt Q Λ nearby 1 2 κ nearby_order))))))
    (hbal : Function.Injective (blockKernelTensorInclusion Q Λ rightMiddle 1 2 target))
    (j : ℤ) (hn : j ≠ 0) :
    IsZero ((homologyFunctor (A := Uᵐᵒᵖ) ℤ j).obj ((Braid).obj
      (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor Tᵐᵒᵖ).obj
        (blockLoadingShortComplex Q Λ rightMiddle 1 2).X₃)))) :=
  fiveSlotMiddleRight_partialStandard_braid_homology_vanish_of_residual_layers Q Λ target
    (fiveSlotMiddleRight_residual_equiv_of_lastWeight_zero Q Λ hQ weight) injective hnearby hbal j hn

end Derived

section Standard

open CategoryTheory CategoryTheory.Limits DG DG.DerivedCategory QuantumGroup KL3.Diagram
open scoped DG.DegreeZero
attribute [local instance 1200] Ring.toIntAlgebra

variable {k₀ : Type} [Field k₀] (datum : CartanDatum Unit) (weights : Fin 3 → Unit →₀ ℕ)

local notation "Qstd" => CL.qCL (CL.CLScalars.kl : CL.CLScalars datum k₀)
local notation "exchanged" => ([0, 2, 1] : List (Fin 3))
local notation "Source" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k₀ Qstd weights ν₀ κ)
local notation "Target" => IsIdempotentElem.Corner
  (isIdempotentElem_violMk_redProj k₀ Qstd weights ν₀ exchanged)

set_option backward.isDefEq.respectTransparency false in
private theorem fiveSlotMiddleRight_partialStandard_braid_homology_vanish_standard_of_residual
    [HasDerivedCategory.{w, 0} Sourceᵐᵒᵖ] [HasDerivedCategory.{w, 0} Targetᵐᵒᵖ]
    (residual : Nonempty ((blockPartialStandardAt Qstd weights nearby 1 2 κ nearby_order)
      ≃ₗ[Sourceᵐᵒᵖ] (blockLoadingKernel Qstd weights rightMiddle 1 2 ⧸
        LinearMap.range (fiveSlotMiddleRight_centralMap Qstd weights)))) (j : ℤ) (hn : j ≠ 0) :
    IsZero ((homologyFunctor (A := Targetᵐᵒᵖ) ℤ j).obj
      ((braidingFunctor k₀ Qstd weights ν₀ κ exchanged).obj
        (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor Sourceᵐᵒᵖ).obj
          (blockLoadingShortComplex Qstd weights rightMiddle 1 2).X₃)))) := by
  have hr : IsRouquierQ datum Qstd :=
    ⟨fun i j h => (h (Subsingleton.elim i j)).elim,
      fun i j h => (h (Subsingleton.elim i j)).elim,
      fun i j h => (h (Subsingleton.elim i j)).elim⟩
  have hq : KLRSymm Qstd := fun i j h => (h (Subsingleton.elim i j)).elim
  have hinj : Function.Injective (fiveSlotMiddleRight_centralMap Qstd weights) := by
    rw [fiveSlotMiddleRight_centralMap_eq_crossing]
    exact fiveSlotMiddleRight_higherCrossingMap_injective_standard hr hq weights
  apply fiveSlotMiddleRight_partialStandard_braid_homology_vanish_of_residual_layers Qstd weights
    exchanged residual hinj _ _ j hn
  · intro i hi
    exact fiveSlotNextRetainedPartialStandard_braid_homology_vanish_exchanged
      (C₀ := datum) (F₀ := k₀) weights i hi
  · exact fiveSlot_blockKernelTensorInclusion_injective_standard_allTops datum weights rightMiddle (by decide)

set_option backward.isDefEq.respectTransparency false in
/-- The actual middle-right partial standard has no nonzero-degree braid
homology at standard parameters when the final red weight is zero. -/
theorem fiveSlotMiddleRight_partialStandard_braid_homology_vanish_zero_final_standard
    [HasDerivedCategory.{w, 0} Sourceᵐᵒᵖ] [HasDerivedCategory.{w, 0} Targetᵐᵒᵖ]
    (weight : weights 2 () = 0) (j : ℤ) (hn : j ≠ 0) :
    IsZero ((homologyFunctor (A := Targetᵐᵒᵖ) ℤ j).obj
      ((braidingFunctor k₀ Qstd weights ν₀ κ exchanged).obj
        (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor Sourceᵐᵒᵖ).obj
          (blockLoadingShortComplex Qstd weights rightMiddle 1 2).X₃)))) := by
  have hq : KLRSymm Qstd := fun i j h => (h (Subsingleton.elim i j)).elim
  exact fiveSlotMiddleRight_partialStandard_braid_homology_vanish_standard_of_residual datum weights
    (fiveSlotMiddleRight_residual_equiv_of_lastWeight_zero Qstd weights hq weight) j hn

set_option backward.isDefEq.respectTransparency false in
/-- The actual middle-right partial standard has no nonzero-degree braid
homology at standard parameters for arbitrary red weights. -/
theorem fiveSlotMiddleRight_partialStandard_braid_homology_vanish_standard
    [HasDerivedCategory.{w, 0} Sourceᵐᵒᵖ] [HasDerivedCategory.{w, 0} Targetᵐᵒᵖ]
    (j : ℤ) (hn : j ≠ 0) :
    IsZero ((homologyFunctor (A := Targetᵐᵒᵖ) ℤ j).obj
      ((braidingFunctor k₀ Qstd weights ν₀ κ exchanged).obj
        (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor Sourceᵐᵒᵖ).obj
          (blockLoadingShortComplex Qstd weights rightMiddle 1 2).X₃)))) := by
  have hq : KLRSymm Qstd := fun i j h => (h (Subsingleton.elim i j)).elim
  exact fiveSlotMiddleRight_partialStandard_braid_homology_vanish_standard_of_residual datum weights
    (fiveSlotMiddleRight_residual_equiv Qstd weights hq) j hn

end Standard


end Categorification.Stendhal.BraidedStendhalAlgebra

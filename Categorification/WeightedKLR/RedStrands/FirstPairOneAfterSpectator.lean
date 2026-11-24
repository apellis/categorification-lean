/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockKernelColumn
import Categorification.WeightedKLR.RedStrands.FirstPairTerminalSpectator
import Categorification.WeightedKLR.RedStrands.RightPairQuotientLift

/-!
# One black beyond the final spectator with the first two reds paired

Webster, arXiv:1309.3796v2, Lemma 6.8 at (6.21).
With two equal black strands, each of the two loadings with one black
beyond the final spectator has a one-generator higher kernel.
-/

noncomputable section

namespace Categorification.KLR.KLRAlgebra

open KLR TypeA Equiv MvPolynomial

variable {I k : Type*} [DecidableEq I] [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}

local notation "n" => Multiset.card ν
local notation "R" => KLRAlgebra k Q ν

/-- A right descent common to all strand matchings supplies a single
right crossing that generates the entire affine diagram column. -/
theorem exists_singleExitColumn_coefficient (hQ : KLRSymm Q) (s t : Seq ν)
    (p : ℕ) (hp : p + 1 < n)
    (descent : ∀ w : Perm (Fin n), w • s = t →
      w ⟨p+1,hp⟩ < w ⟨p,by omega⟩) (z : R) :
    ∃ c : R, e t * z * e s = c * (ψ p * e s) := by
  classical
  let ρ (w : Perm (Fin n)) := if hw : w • s = t then
    canWord n (w * sadj n p) ++ [p] else canWord n w
  have hρ : IsReducedChoice ρ := by
    intro w
    dsimp only [ρ]
    split_ifs with hw
    · have word : wordProd n (canWord n (w * sadj n p) ++ [p]) = w := by
        rw [wordProd_append, wordProd_canWord, wordProd_singleton, mul_assoc, sadj_mul_self, mul_one]
      refine ⟨⟨validWord_append.2 ⟨(isReduced_canWord _ _).1, by simp [ValidWord,hp]⟩, ?_⟩, word⟩
      rw [word, List.length_append, List.length_singleton, (isReduced_canWord _ _).2,
        wordProd_canWord, length_mul_sadj_of_gt hp (descent w hw)]
    · exact ⟨isReduced_canWord _ _, wordProd_canWord _ _⟩
  let B := lbasis (k := k) («μ» := ν) hQ ρ hρ
  induction B.mem_span z using Submodule.span_induction with
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a+b, by rw [mul_add, add_mul, ha, hb, add_mul]⟩
  | smul a x _ hx =>
    obtain ⟨c,hc⟩ := hx
    exact ⟨a • c, by rw [mul_smul_comm, smul_mul_assoc, hc, smul_mul_assoc]⟩
  | mem x hx =>
    obtain ⟨⟨s',w,dots⟩,rfl⟩ := hx
    rw [show B (s',w,dots) = _ from lbasis_apply .., mul_assoc, mul_assoc _ (e s'), e_mul_e]
    by_cases eq : s' = s
    · subst s'
      rw [ite_eq_left rfl]
      by_cases hw : w • s = t
      · refine ⟨e t * pol (monomial dots 1) * ψw (canWord n (w * sadj n p)), ?_⟩
        simp only [ρ, dite_eq_left hw, ψw_append, ψw_cons, ψw_nil, mul_one, mul_assoc]
      · have cut := e_mul_pol_ψw_e (Q := Q) (monomial dots (1 : k)) (ρ w) s
        rw [(hρ w).2] at cut
        refine ⟨0, ?_⟩
        rw [← cut, ← mul_assoc, e_mul_e, ite_eq_right (Ne.symm hw), zero_mul, zero_mul]
    · exact ⟨0, by simp only [ite_eq_right eq, mul_zero, zero_mul]⟩

end Categorification.KLR.KLRAlgebra

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLRAlgebra TypeA Equiv
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

local notation "ν" => ({()} + {()} : Multiset Unit)
local notation "μ" => stendhalWeight 3 ν
local notation "N" => Multiset.card μ

/-- The two surviving loadings with one black strand to the right of the final red. -/
def firstPairOneAfterSpectator : Bool → Seq μ
  | false => Seq.ofList [.inr 0, .inl (), .inr 1, .inr 2, .inl ()] (by decide)
  | true => Seq.ofList [.inr 0, .inr 1, .inl (), .inr 2, .inl ()] (by decide)

local notation "lower" => firstPairOneAfterSpectator
local notation "upper" => fun side => sadj N 3 • lower side

private theorem firstPairOneAfter_order (side : Bool) : redWord (lower side) = List.finRange 3 := by
  cases side <;> decide

private theorem firstPairOneAfter_upper_order (side : Bool) : redWord (upper side) = redWord (lower side) := by
  cases side <;> decide

private theorem firstPairOneAfter_strict (side : Bool) :
    adjacentBlockRoot 0 1 (lower side) < adjacentBlockRoot 0 1 (upper side) := by
  apply lt_of_le_not_ge
  · intro r i
    fin_cases r <;> cases i <;> cases side <;> decide
  · intro h
    have impossible : ¬ adjacentBlockRoot 0 1 (upper side) 2 () ≤
        adjacentBlockRoot 0 1 (lower side) 2 () := by
      cases side <;> decide
    exact impossible (h 2 ())

private theorem firstPairOneAfter_descent (side : Bool) (s : Seq μ)
    (order : redWord s = redWord (lower side))
    (higher : adjacentBlockRoot 0 1 (lower side) < adjacentBlockRoot 0 1 s)
    (survives : ¬ IsViolated s) (w : Perm (Fin N)) (hw : w • lower side = s) :
    w ⟨4, by decide⟩ < w ⟨3, by decide⟩ := by
  have count : 1 < adjacentBlockRoot 0 1 s 2 () := by
    apply lt_of_not_ge
    intro tooLow
    apply higher.not_ge
    intro r i
    cases i
    have word := order.trans (firstPairOneAfter_order side)
    fin_cases r
    · change adjacentBlockRoot 0 1 s 0 () ≤ adjacentBlockRoot 0 1 (lower side) 0 ()
      rw [firstPair_merged_root_eq_zero s word survives 0 (Or.inl rfl)]
      exact Nat.zero_le _
    · change adjacentBlockRoot 0 1 s 1 () ≤ adjacentBlockRoot 0 1 (lower side) 1 ()
      rw [firstPair_merged_root_eq_zero s word survives 1 (Or.inr rfl)]
      exact Nat.zero_le _
    · change adjacentBlockRoot 0 1 s 2 () ≤ adjacentBlockRoot 0 1 (lower side) 2 ()
      have hcount : adjacentBlockRoot 0 1 (lower side) 2 () = 1 := by cases side <;> decide
      rwa [hcount]
  have test : ∀ (side : Bool) (v : Perm (Fin N)),
      1 < adjacentBlockRoot 0 1 (v • lower side) 2 () →
      v ⟨4, by decide⟩ < v ⟨3, by decide⟩ := by decide +kernel
  exact test side w (hw.symm ▸ count)

variable {k : Type} [CommRing k] (Q : Unit → Unit → MvPolynomial (Fin 2) k)
  (Λ : Fin 3 → Unit →₀ ℕ) (side : Bool)

local notation "A" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "V" => ViolQuotient k Q Λ ν
local notation "F" => AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν)
local notation "proj" => fun s : Seq μ => F (e s)
local notation "cross" => F (ψ 3 * e (upper side))
local notation "J" => blockUpperIdeal k Q Λ ν 0 1 (adjacentBlockRoot 0 1 (lower side)) (redWord (lower side))

private theorem firstPairOneAfter_cross_right :
    cross * proj (upper side) = cross := by
  rw [← map_mul F, mul_assoc, e_mul_self]

private theorem firstPairOneAfter_cross_left :
    proj (lower side) * cross = cross := by
  rw [← map_mul F]
  apply congrArg F
  have step : sadj N 3 • upper side = lower side := by cases side <;> decide +kernel
  simp only [ψ_mul_e, step, ← mul_assoc, e_mul_self]

private theorem firstPairOneAfter_affine_factor (hQ : KLRSymm Q) (s : Seq μ)
    (order : redWord s = redWord (lower side))
    (higher : adjacentBlockRoot 0 1 (lower side) < adjacentBlockRoot 0 1 s)
    (survives : ¬ IsViolated s) (x : A) :
    ∃ y : A, e (lower side) * x * e s = (ψ 3 * e (upper side)) * y := by
  obtain ⟨z,hz⟩ := exists_singleExitColumn_coefficient (stendhalQ_symm Q Λ hQ)
    (lower side) s 3 (by decide) (firstPairOneAfter_descent side s order higher survives) (hflip x)
  have flip : hflip (ψ 3 * e (lower side) : A) = ψ 3 * e (upper side) := by
    simp only [hflip_mul, hflip_ψ, hflip_e, e_mul_ψ]
  exact ⟨hflip z, by
    simpa only [hflip_mul, hflip_e, hflip_hflip, flip, mul_assoc] using congrArg hflip hz⟩

private theorem firstPairOneAfter_higherGenerator (hQ : KLRSymm Q) (s : Seq μ)
    (order : redWord s = redWord (lower side))
    (higher : adjacentBlockRoot 0 1 (lower side) < adjacentBlockRoot 0 1 s) (a : V) :
    ∃ y : V, proj (upper side) * y = y ∧ cross * y = proj (lower side) * a * proj s := by
  by_cases hv : IsViolated s
  · exact ⟨0, by rw [mul_zero], by rw [show proj s = 0 from violMk_e hv, mul_zero, mul_zero]⟩
  obtain ⟨x,hx⟩ := (violMk_surjective (Q := Q) (Λ := Λ)).comp
    (ofKLR_surjective (Q := Q) (Λ := Λ)) a
  obtain ⟨y,hy⟩ := firstPairOneAfter_affine_factor Q Λ side hQ s order higher hv x
  have image := congrArg F hy
  simp only [map_mul F, show F x = a from hx] at image
  refine ⟨proj (upper side) * F y, ?_, ?_⟩
  · rw [← mul_assoc, ← map_mul F, e_mul_self]
  · rw [← mul_assoc, firstPairOneAfter_cross_right Q Λ side]
    simpa only [map_mul F, mul_assoc] using image.symm

/-- Both one-after-spectator higher kernels are generated by the
crossing from the corresponding terminal loading. -/
theorem firstPairOneAfter_blockKernel_principal (hQ : KLRSymm Q)
    (x : V) (hx : x ∈ J) (left : proj (lower side) * x = x) :
    ∃ y : V, proj (upper side) * y = y ∧ cross * y = x := by
  unfold blockUpperIdeal at hx
  have cut : ∀ a b : V, ∃ y : V, proj (upper side) * y = y ∧ cross * y = proj (lower side) * a * x * b := by
    refine TwoSidedIdeal.span_induction
      (p := fun z _ => ∀ a b : V, ∃ y : V, proj (upper side) * y = y ∧ cross * y =
        proj (lower side) * a * z * b) ?_ ?_ ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨s, hs, hh, rfl⟩ a b
      obtain ⟨y, hy, hval⟩ := firstPairOneAfter_higherGenerator Q Λ side hQ s hs hh a
      exact ⟨y * b, by rw [← mul_assoc, hy], by rw [← mul_assoc, hval]⟩
    · intro a b
      exact ⟨0, by rw [mul_zero], by rw [mul_zero, mul_zero, zero_mul]⟩
    · intro u v _ _ hu hv a b
      obtain ⟨y,hy,ey⟩ := hu a b
      obtain ⟨z,hz,ez⟩ := hv a b
      exact ⟨y+z, by rw [mul_add,hy,hz], by rw [mul_add,ey,ez,mul_add,add_mul]⟩
    · intro u _ hu a b
      obtain ⟨y,hy,ey⟩ := hu a b
      exact ⟨-y, by rw [mul_neg,hy], by rw [mul_neg,ey,mul_neg,neg_mul]⟩
    · intro a u _ hu b d
      simpa only [mul_assoc] using hu (b*a) d
    · intro b u _ hu a d
      simpa only [mul_assoc] using hu a (b*d)
  obtain ⟨y,hy,h⟩ := cut 1 1
  exact ⟨y,hy,by simpa only [mul_one,left] using h⟩

/-- The principal higher kernel is projective once the ordinary right-corner
crossing test is injective. -/
theorem firstPairOneAfter_blockKernel_projective_of_cancellation (hQ : KLRSymm Q)
    (cancel : ∀ y : V, proj (upper side) * y = y →
      y * F (redIdem k Q Λ (redWord (lower side))) = y → cross * y = 0 → y = 0) :
    Module.Projective
      (isIdempotentElem_violMk_redProj k Q Λ ν (redWord (lower side))).Cornerᵐᵒᵖ
      (blockLoadingKernel Q Λ (lower side) 0 1) := by
  have hp : proj (upper side) ∈ J :=
    TwoSidedIdeal.subset_span ⟨upper side, firstPairOneAfter_upper_order side,
      firstPairOneAfter_strict side, rfl⟩
  have hc : cross ∈ J := (firstPairOneAfter_cross_right Q Λ side) ▸
    TwoSidedIdeal.mul_mem_left _ _ _ hp
  exact blockLoadingKernel_projective_of_principal_factor Q Λ (lower side) 0 1
    (upper side) (firstPairOneAfter_upper_order side) cross hc
    (firstPairOneAfter_cross_left Q Λ side) (firstPairOneAfter_cross_right Q Λ side)
    (firstPairOneAfter_blockKernel_principal Q Λ side hQ)
    (by simpa only [redProj, AlgHom.comp_apply] using cancel)

/-- On a cancellative principal crossing, the actual higher kernel is one
partial-standard layer indexed by the corresponding terminal spectator loading. -/
theorem firstPairOneAfter_blockKernel_hasHigherSingle_of_cancellation (hQ : KLRSymm Q)
    (cancel : ∀ y : V, proj (upper side) * y = y →
      y * F (redIdem k Q Λ (redWord (lower side))) = y → cross * y = 0 → y = 0) :
    ModuleFiltration.HasFiltration
      (fun _ : Unit => blockPartialStandardAt Q Λ (upper side) 0 1 (redWord (lower side))
        (firstPairOneAfter_upper_order side)) [()]
      (ModuleCat.of
        (isIdempotentElem_violMk_redProj k Q Λ ν (redWord (lower side))).Cornerᵐᵒᵖ
        (blockLoadingKernel Q Λ (lower side) 0 1)) := by
  have hp : proj (upper side) ∈ J :=
    TwoSidedIdeal.subset_span ⟨upper side, firstPairOneAfter_upper_order side,
      firstPairOneAfter_strict side, rfl⟩
  have hc : cross ∈ J := (firstPairOneAfter_cross_right Q Λ side) ▸
    TwoSidedIdeal.mul_mem_left _ _ _ hp
  have crossEquiv := blockLoadingKernel_equiv_projective_of_principal_factor Q Λ (lower side) 0 1
    (upper side) (firstPairOneAfter_upper_order side) cross hc
    (firstPairOneAfter_cross_left Q Λ side) (firstPairOneAfter_cross_right Q Λ side)
    (firstPairOneAfter_blockKernel_principal Q Λ side hQ)
    (by simpa only [redProj, AlgHom.comp_apply] using cancel)

  have order : redWord (upper side) = List.finRange 3 :=
    (firstPairOneAfter_upper_order side).trans (firstPairOneAfter_order side)
  have lastLabel : (upper side).lbl ⟨4, by decide⟩ = Sum.inr (2 : Fin 3) := by
    cases side <;> decide
  have terminal : ∀ (p : Fin N) (i : Unit), (upper side).lbl p = Sum.inl i →
      p < redPos (upper side) 2 := by
    rw [← eq_redPos lastLabel]
    cases side <;> decide +kernel
  have equiv := blockPartialStandardAt_equiv_projective Q Λ (upper side) 0 1 (redWord (lower side))
    (firstPairOneAfter_upper_order side)
    (firstPair_terminal_higher_isViolated (upper side) · order terminal)
  exact ModuleFiltration.HasFiltration.single (crossEquiv.symm.trans equiv.symm)

end Categorification.Stendhal.BraidedStendhalAlgebra

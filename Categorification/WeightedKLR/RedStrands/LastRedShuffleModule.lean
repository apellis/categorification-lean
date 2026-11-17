/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Crystal.IndDecomp
import Categorification.WeightedKLR.RedStrands.TensorProjection

/-!
# Induction and the last-red shuffle

Webster, arXiv:1309.3796v2, §5, Theorem 5.8. The induction module used to
detect the last-red corner has affine shuffle coordinates. Here we use the
freedom to choose reduced words in Khovanov–Lauda I, arXiv:0803.4121v2,
Proposition 2.16 and Lemma 2.20, including at descending red crossings.
-/

noncomputable section
namespace Categorification.Stendhal
open KLR KLRAlgebra TypeA MulOpposite
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {ν ν' : Multiset I}
  (hs : KLRSymm Q)
  (N : Type*) [AddCommGroup N] [Module k N] [Module (TensorKLR Q ν ν') N]
  [IsScalarTower k (TensorKLR Q ν ν') N]

local notation "A" => KLRAlgebra k Q (ν + ν')
local notation "B" => TensorKLR Q ν ν'
local notation "Sh" => Shuffle (Seq.card_add' ν ν')
local notation "M" => Ind Q ν ν' N

private def flipToInd : oneConcatSub (ν := ν) (ν' := ν') Q →ₗ[k] IndBimod Q ν ν' where
  toFun a := ⟨hflip (a : A), by
    have h := congrArg (fun y : A => hflip y) (mem_oneConcatSub.mp a.2)
    rwa [hflip_mul, hflip_oneConcat] at h⟩
  map_add' x y := Subtype.ext (hflip_add _ _)
  map_smul' c x := Subtype.ext (hflip_smul _ _)

private theorem flipToInd_surjective : Function.Surjective (flipToInd (ν := ν) (ν' := ν') (Q := Q)) := by
  intro r
  refine ⟨⟨hflip (r : A), mem_oneConcatSub.mpr ?_⟩, Subtype.ext (hflip_hflip _)⟩
  have h := congrArg (fun y : A => hflip y) r.2
  rwa [hflip_mul, hflip_oneConcat] at h

private theorem flipToInd_smul (t : B) (x : oneConcatSub (ν := ν) (ν' := ν') Q) :
    flipToInd (t • x) = op (tensorHflip ν ν' t) • flipToInd x := by
  apply Subtype.ext
  change hflip ((t • x : oneConcatSub Q) : A) = hflip (x : A) * concat Q ν ν' (tensorHflip ν ν' t)
  rw [coe_tensor_smul, hflip_mul, hflip_concat]

/-- The identity-shuffle inclusion of the input parabolic module. -/
def indShuffleUnit (n : N) : M := BalancedTensor.tmul oneConcatSubBimod n

/-- The linear identity-shuffle inclusion. -/
def indShuffleUnitLinear : N →ₗ[k] M :=
  ((BalancedTensor.mk k A B (IndBimod Q ν ν') N).restrictScalars k).comp
    (TensorProduct.mk k (IndBimod Q ν ν') N oneConcatSubBimod)

include hs in
/-- The identity shuffle identifies its input module with a subspace of
the affine induced module (KL I, Lemma 2.20). -/
theorem indShuffleUnit_injective : Function.Injective (indShuffleUnit (Q := Q) (ν := ν) (ν' := ν') N) := by
  intro x y he
  have h := congrArg (fun z : M => indDecomp hs N z shufOne) he
  simpa [indShuffleUnit, indDecomp_tmul_oneConcat] using h

omit [IsScalarTower k (TensorKLR Q ν ν') N] in
include hs in
/-- For any choice of reduced lifts, the corresponding shuffle translates
of the identity-shuffle copy of the parabolic module additively span induction. -/
theorem indShuffle_induction (σ : Sh → List ℕ)
    (hσ : ∀ u, IsReduced (ν+ν').card (σ u) ∧ wordProd (ν+ν').card (σ u) = u.1)
    {P : M → Prop} (hz : P 0) (ha : ∀ a b, P a → P b → P (a+b))
    (ht : ∀ u n, P ((ψw (σ u).reverse : A) • indShuffleUnit (Q := Q) (ν := ν) (ν' := ν') N n)) (z : M) : P z := by
  induction z using BalancedTensor.induction_on with
  | zero => exact hz
  | add a b ha' hb' => exact ha _ _ ha' hb'
  | tmul r n =>
    obtain ⟨b,rfl⟩ := flipToInd_surjective r
    obtain ⟨g,rfl⟩ := (freeMap_bijective hs (canWord _) (canWord _) σ
      (fun a => ⟨isReduced_canWord _ a, wordProd_canWord _ a⟩)
      (fun a => ⟨isReduced_canWord _ a, wordProd_canWord _ a⟩) hσ).surjective b
    induction g using Finsupp.induction with
    | zero => simpa using hz
    | single_add u t f hu hne ih =>
      rw [map_add, map_add, BalancedTensor.add_tmul]
      apply ha _ _ _ ih
      rw [freeMap, Finsupp.linearCombination_single, flipToInd_smul, BalancedTensor.op_smul_tmul]
      have h : flipToInd (hatWSub σ u : oneConcatSub Q) =
          (ψw (σ u).reverse : A) • (oneConcatSubBimod : IndBimod Q ν ν') := by
        apply Subtype.ext
        change hflip (oneConcat Q ν ν' * ψw (σ u) : A) = ψw (σ u).reverse * oneConcat Q ν ν'
        rw [hflip_mul, hflip_ψw, hflip_oneConcat]
      rw [h, ← BalancedTensor.smul_tmul']
      exact ht _ _


omit [IsScalarTower k (TensorKLR Q ν ν') N] in
/-- Juxtaposed affine diagrams act on the identity shuffle through the
parabolic module. -/
theorem concat_smul_indShuffleUnit (t : B) (n : N) :
    (concat Q ν ν' t : A) • indShuffleUnit (Q := Q) (ν := ν) (ν' := ν') N n = indShuffleUnit (Q := Q) (ν := ν) (ν' := ν') N (t • n) := by
  rw [indShuffleUnit, BalancedTensor.smul_tmul', indShuffleUnit, ← BalancedTensor.op_smul_tmul]
  congr 1
  apply Subtype.ext
  change concat Q ν ν' t * oneConcat Q ν ν' = oneConcat Q ν ν' * concat Q ν ν' t
  rw [concat_mul_oneConcat, oneConcat_mul_concat]

omit [IsScalarTower k (TensorKLR Q ν ν') N] in
/-- Boundary idempotents on the identity shuffle recover precisely the
two component loadings. -/
theorem idem_smul_indShuffleUnit (s : Seq (ν+ν')) (n : N) :
    (e s : A) • indShuffleUnit (Q := Q) (ν := ν) (ν' := ν') N n = indShuffleUnit (Q := Q) (ν := ν) (ν' := ν') N (concatIdem (Q := Q) s • n) := by
  rw [← concat_smul_indShuffleUnit]
  simp only [indShuffleUnit, BalancedTensor.smul_tmul']
  congr 1
  apply Subtype.ext
  change e s * oneConcat Q ν ν' = concat Q ν ν' (concatIdem s) * oneConcat Q ν ν'
  rw [concat_mul_oneConcat, concat_concatIdem]

omit [IsScalarTower k (TensorKLR Q ν ν') N] in
private theorem idem_smul_shuffleWord (s : Seq (ν+ν')) (w : List ℕ) (n : N) :
    (e s : A) • ((ψw w : A) • indShuffleUnit (Q := Q) (ν := ν) (ν' := ν') N n) =
      (ψw w : A) • indShuffleUnit (Q := Q) (ν := ν) (ν' := ν') N (concatIdem (Q := Q) ((wordProd (ν+ν').card w)⁻¹ • s) • n) := by
  rw [← mul_smul, e_mul_ψw, mul_smul, idem_smul_indShuffleUnit]

omit [IsScalarTower k (TensorKLR Q ν ν') N] in
include hs in
/-- At a descending crossing between two groups, choose a reduced shuffle
whose last letter is that crossing. If its quadratic polynomial vanishes,
the crossing into the sector with fewer inversions vanishes on induction.
The alternative in the hypothesis says the corresponding boundary space of
the input vanishes. -/
theorem indShuffle_crossing_eq_zero (s : Seq (ν+ν')) (j : ℕ)
    (hquad : (ψ j * ψ j * e (sadj (ν+ν').card j • s) : A) = 0)
    (hwords : ∀ u : Sh, ∃ w : List ℕ, IsReduced (ν+ν').card w ∧
      wordProd (ν+ν').card w = u.1 ∧ ((∀ n : N, concatIdem (Q := Q) (u.1 • s) • n = 0) ∨
        ∃ v, w = v ++ [j])) (z : M) :
    (ψ j * e s : A) • z = 0 := by
  classical
  choose σ hσ using hwords
  induction z using indShuffle_induction hs N σ (fun u => ⟨(hσ u).1, (hσ u).2.1⟩) with
  | hz => exact smul_zero _
  | ha a b ha hb => rw [smul_add, ha, hb, add_zero]
  | ht u n =>
    rcases (hσ u).2.2 with h | ⟨v, hv⟩
    · rw [mul_smul, idem_smul_shuffleWord, wordProd_reverse, (hσ u).2.1, inv_inv, h,
        indShuffleUnit, BalancedTensor.tmul_zero, smul_zero, smul_zero]
    · rw [hv, List.reverse_append, List.reverse_singleton, List.singleton_append, ψw_cons,
        mul_smul (ψ j : A) (ψw _), ← mul_smul, mul_assoc (ψ j : A), e_mul_ψ, ← mul_assoc,
        hquad, zero_smul]


omit [DecidableEq I] in
private theorem uniqueLabel_smul (s : Seq (ν+ν')) (a : Fin (ν+ν').card)
    (h : ∀ b, s.lbl b = s.lbl a → b = a) (w : Equiv.Perm (Fin (ν+ν').card)) :
    ∀ b, (w • s).lbl b = (w • s).lbl (w a) → b = w a := by
  intro b hb
  change s.lbl (w.symm b) = s.lbl (w.symm (w a)) at hb
  rw [w.symm_apply_apply] at hb
  exact w.symm_apply_eq.mp (h _ hb)

private theorem uniqueDot_slide (s : Seq (ν+ν')) (a : Fin (ν+ν').card)
    (h : ∀ b, s.lbl b = s.lbl a → b = a) (j : ℕ) :
    (x a * e s * ψ j : A) =
      ψ j * (x (sadj (ν+ν').card j a) * e (sadj (ν+ν').card j • s)) := by
  rw [mul_assoc, e_mul_ψ, ← mul_assoc, ← mul_assoc]
  by_cases hj : j+1 < (ν+ν').card
  · let p : Fin (ν+ν').card := ⟨j, by omega⟩
    let p' : Fin (ν+ν').card := ⟨j+1, hj⟩
    have hpp : p ≠ p' := by simp [p, p', Fin.ext_iff]
    simp only [sadj, hj, ↓reduceDIte]
    let t := Equiv.swap p p' • s
    by_cases h₀ : a = p
    · subst a
      have hn : t.lbl p ≠ t.lbl p' := by
        change s.lbl ((Equiv.swap p p').symm p) ≠ s.lbl ((Equiv.swap p p').symm p')
        simpa using fun he => hpp.symm (h p' he)
      rw [Equiv.swap_apply_left]
      have hslide := dot_cross_left (Q := Q) j hj t
      rw [ite_eq_right (show t.lbl ⟨j, by omega⟩ ≠ t.lbl ⟨j+1,hj⟩ from hn), sub_mul] at hslide
      exact sub_eq_zero.mp hslide
    · by_cases h₁ : a = p'
      · subst a
        have hn : t.lbl p ≠ t.lbl p' := by
          change s.lbl ((Equiv.swap p p').symm p) ≠ s.lbl ((Equiv.swap p p').symm p')
          simpa using fun he => hpp (h p he.symm)
        rw [Equiv.swap_apply_right]
        have hslide := dot_cross_right (Q := Q) j hj t
        rw [ite_eq_right (show t.lbl ⟨j, by omega⟩ ≠ t.lbl ⟨j+1,hj⟩ from hn), sub_mul] at hslide
        exact (sub_eq_zero.mp hslide).symm
      · rw [Equiv.swap_apply_of_ne_of_ne h₀ h₁, x_mul_ψ a j
          (fun hv => h₀ (Fin.ext hv)) (fun hv => h₁ (Fin.ext hv))]
  · simp [ψ_eq_zero (Q := Q) (ν := ν+ν') j (by omega)]

/-- A dot on a strand of unique colour slides across every crossing word
without a nilHecke correction. -/
theorem uniqueDot_slide_word (s : Seq (ν+ν')) (a : Fin (ν+ν').card)
    (h : ∀ b, s.lbl b = s.lbl a → b = a) (w : List ℕ) :
    (x a * e s * ψw w : A) = ψw w *
      (x ((wordProd (ν+ν').card w)⁻¹ a) * e ((wordProd (ν+ν').card w)⁻¹ • s)) := by
  induction w generalizing s a with
  | nil => simp [ψw, wordProd]
  | cons j w ih =>
    rw [ψw_cons, ← mul_assoc, uniqueDot_slide s a h, mul_assoc,
      ih _ _ (uniqueLabel_smul s a h _), ← mul_assoc]
    simp [wordProd, mul_smul]

omit [IsScalarTower k (TensorKLR Q ν ν') N] in
include hs in
/-- Vanishing of dots on colours occurring only once is preserved under
parabolic induction. The input hypothesis is checked on the inducing
module before any shuffle. -/
theorem indShuffle_dot_eq_zero (r : I)
    (hmult : ∀ (s : Seq (ν+ν')) (a b), s.lbl a = r → s.lbl b = r → a = b)
    (hunit : ∀ (s : Seq (ν+ν')) (a), s.lbl a = r → ∀ n : N,
      (x a * e s : A) • indShuffleUnit (Q := Q) (ν := ν) (ν' := ν') N n = 0)
    (s : Seq (ν+ν')) (a : Fin (ν+ν').card) (ha : s.lbl a = r) (z : M) :
    (x a * e s : A) • z = 0 := by
  induction z using indShuffle_induction hs N shufWord shufWord_spec with
  | hz => exact smul_zero _
  | ha x y hx hy => rw [smul_add, hx, hy, add_zero]
  | ht u n =>
    rw [← mul_smul, uniqueDot_slide_word s a (fun b hb => hmult _ _ _ (hb.trans ha) ha),
      mul_smul, hunit, smul_zero]
    let v := wordProd (ν+ν').card (shufWord u).reverse
    change s.lbl (v (v.symm a)) = r
    rw [v.apply_symm_apply, ha]


section Identity

include hs in
/-- A boundary projector supported only on the identity shuffle has image
contained in the inducing module. -/
theorem indShuffle_eSum_mem_unit (F : Finset (Seq (ν+ν')))
    (hoff : ∀ (s : Seq (ν+ν')), s ∈ F → ∀ (u : Sh), u ≠ shufOne →
      ∀ x : N, concatIdem (Q := Q) (u.1 • s) • x = 0) (z : M) :
    ∃ n : N, eSum Q F • z = indShuffleUnit (Q := Q) (ν := ν) (ν' := ν') N n := by
  classical
  let d := indDecomp (ν := ν) (ν' := ν') hs N
  refine ⟨d (eSum Q F • z) shufOne, d.injective ?_⟩
  funext u
  rw [show d (indShuffleUnit (Q := Q) (ν := ν) (ν' := ν') N (d (eSum Q F • z) shufOne)) = _ from indDecomp_tmul_oneConcat hs N _]
  by_cases hu : u = shufOne
  · subst u; simp
  · rw [Pi.single_eq_of_ne hu]
    rw [eSum, Finset.sum_smul, map_sum, Finset.sum_apply]
    exact Finset.sum_eq_zero fun s hs' => (indDecomp_e_smul hs N s z u).trans (hoff s hs' u hu _)

omit [IsScalarTower k (TensorKLR Q ν ν') N] in
/-- Every input vector lies in a chosen boundary sum if the other
boundary idempotents vanish on the input. -/
theorem indShuffle_eSum_unit (F : Finset (Seq (ν+ν')))
    (hoff : ∀ s, s ∉ F → ∀ n : N, concatIdem (Q := Q) s • n = 0) (n : N) :
    eSum Q F • indShuffleUnit (Q := Q) (ν := ν) (ν' := ν') N n =
      indShuffleUnit (Q := Q) (ν := ν) (ν' := ν') N n := by
  classical
  rw [eSum, Finset.sum_smul]
  calc ∑ s ∈ F, (e s : A) • indShuffleUnit N n =
        ∑ s : Seq (ν+ν'), (e s : A) • indShuffleUnit N n := by
          apply Finset.sum_subset (Finset.subset_univ F)
          intro s _ h
          rw [idem_smul_indShuffleUnit, hoff _ h, indShuffleUnit, BalancedTensor.tmul_zero]
       _ = _ := by rw [← Finset.sum_smul, sum_e, one_smul]

end Identity

end Categorification.Stendhal

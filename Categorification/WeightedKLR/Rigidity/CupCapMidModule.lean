/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidRelSimple

/-!
# The bimodule structure on the model of a cap after `λ_j`

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17. The diagrams of the generators of the KLR
algebra of `λ` (`CupCap.midGenImage`) define a map out of the free algebra into the sliding
diagrams of `λ⁺`. When the KLR relations hold on the model (`CupCap.MidKLRRel`: each relation acts
alike on the model), it descends to an algebra map from the KLR algebra of `λ` into the
endomorphisms of the model. Dots on red strands and crossings of two red strands act by zero, so
it factors through `T̃^λ`; the unit of `T̃^λ` acts as the identity. Together with the right
action of `T̃^{λ⁺}` this makes the model a `T̃^λ`–`T̃^{λ⁺}` bimodule.

## Main definitions

* `CupCap.midFree`: the generators placed above the maximum, on the free algebra.
* `CupCap.MidKLRRel`: the KLR relations hold on the model.
* `CupCap.midKLRAct`: the action of the KLR algebra of `λ`.
* `CupCap.midLeftAlg`: the action of `T̃^λ`.
* `CupCap.midEnvAlg`: the bimodule structure.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite InductionAlong

section Order

variable {I : Type*} {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ} {ν ν₀ : Multiset I}

/-- A loading below the cap generators keeps the order of the red strands of `λ`. -/
theorem isRedOrdered_of_insertSeq' {s : Seq (stendhalWeight ℓ ν)} {n : ℕ}
    (hn : n ≤ Multiset.card (stendhalWeight ℓ ν))
    {t : Seq (Multiset.map (cupColour (I := I) j hj) (stendhalWeight 2 ν₀))}
    (h : IsRedOrdered (insertSeq (j := j) (hj := hj) s n hn t)) : IsRedOrdered s := by
  intro a b r r' hab ha hb
  have h1 := insertSeq_lbl_old (j := j) (hj := hj) (ν₀ := ν₀) s n hn t a
  have h2 := insertSeq_lbl_old (j := j) (hj := hj) (ν₀ := ν₀) s n hn t b
  rw [ha] at h1
  rw [hb] at h2
  have hlt := h _ _ (oldRed j hj r) (oldRed j hj r') (by
    rw [Fin.lt_def] at hab ⊢
    simp only [Fin.val_cast, insertPos_inl_val]
    split_ifs <;> omega) h1 h2
  rw [Fin.lt_def] at hlt ⊢
  simp only [oldRed, insertPos_inl_val] at hlt
  split_ifs at hlt <;> omega

end Order

section Free

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)

variable (j hj Q Λ Λc ν ν₀) in
/-- **The generators of `λ` placed above the maximum**, on the free algebra. -/
def midFree : FreeAlgebra k (Gen (stendhalWeight ℓ ν)) →ₐ[k] midSlidesSub j hj Q Λ Λc ν ν₀ :=
  FreeAlgebra.lift k (midGenImage j hj Q Λ Λc ν ν₀)

theorem midFree_fe (t : Seq (stendhalWeight ℓ ν)) :
    (midFree j hj Q Λ Λc ν ν₀ (fe k _ t)).val = midIdem j hj Q Λ Λc ν ν₀ t := by
  simp [midFree, midGenImage]

theorem midFree_fx (a : Fin m) :
    (midFree j hj Q Λ Λc ν ν₀ (fx k _ a)).val = midDot j hj Q Λ Λc ν ν₀ a := by
  simp [midFree, midGenImage]

theorem midFree_fψ (p : ℕ) :
    (midFree j hj Q Λ Λc ν ν₀ (fψ k _ p)).val = midCross j hj Q Λ Λc ν ν₀ p := by
  simp [midFree, midGenImage]

theorem midFree_ncEval {n : ℕ} (y : Fin n → FreeAlgebra k (Gen (stendhalWeight ℓ ν)))
    (P : MvPolynomial (Fin n) k) :
    (midFree j hj Q Λ Λc ν ν₀ (ncEval y P)).val =
      ncEval (fun a => (midFree j hj Q Λ Λc ν ν₀ (y a)).val) P := by
  rw [← Subalgebra.coe_val, ncEval_map, ncEval_map]

end Free

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Model

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Rλ" => KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)
local notation "T" => StendhalAlgebra k Q Λ ν
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
local notation "E" s:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s (midPos j s) (midPos_le j s))
local notation "bot" => botMap k Q Λ Λc j hj ν ν₀
local notation "σ" => midStendhal j hj Q Λ Λc ν ν₀
local notation "μ" => midMapKLR j hj Q Λ Λc ν ν₀

variable (L : Type*) [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)

variable (j hj Q Λ Λc ν ν₀) in
/-- **The KLR relations of `λ` hold on the model**: the two sides of each defining relation act
alike. -/
def MidKLRRel : Prop :=
  ∀ a b, KLR.Rel k (stendhalQ Q Λ) (stendhalWeight ℓ ν) a b →
    MidRel j hj Q Λ Λc ν ν₀ L hL (midFree j hj Q Λ Λc ν ν₀ a).val
      (midFree j hj Q Λ Λc ν ν₀ b).val

variable {L hL}

/-- **The action of the KLR algebra of `λ` on the model.** -/
def midKLRAct (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) :
    Rλ →ₐ[k] Module.End k (MidModel j hj Q Λ Λc ν ν₀ L) :=
  RingQuot.liftAlgHom k ⟨(midEndAlg L hL).comp (midFree j hj Q Λ Λc ν ν₀),
    fun a b h => midEndAlg_eq_of_midRel (hR a b h)⟩

theorem midKLRAct_mk (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
    (a : FreeAlgebra k (Gen (stendhalWeight ℓ ν))) :
    midKLRAct hR (KLRAlgebra.mk k _ _ a) = midEndAlg L hL (midFree j hj Q Λ Λc ν ν₀ a) :=
  RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _

theorem midEnd_eq_zero_of_midRel {Y : Rp} (hY : MidSlides j hj Q Λ Λc ν ν₀ Y)
    (h : MidRel j hj Q Λ Λc ν ν₀ L hL Y 0) : midEnd L hL hY = 0 := by
  have h0 : MidSlides j hj Q Λ Λc ν ν₀ (0 : Rp) := by
    simpa using MidSlides.smul (0 : k) (MidSlides.one (j := j) (hj := hj) (Q := Q) (Λ := Λ)
      (Λc := Λc) (ν := ν) (ν₀ := ν₀))
  rw [h hY h0]
  ext y
  rw [midEnd_eq_of_eq hL h0 (MidSlides.smul (0 : k) MidSlides.one) (zero_smul k (1 : Rp)).symm,
    midEnd_smul, zero_smul]
  · rfl
  · exact MidSlides.one

theorem midKLRAct_eq_zero (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
    (a : FreeAlgebra k (Gen (stendhalWeight ℓ ν)))
    (h : MidRel j hj Q Λ Λc ν ν₀ L hL (midFree j hj Q Λ Λc ν ν₀ a).val 0) :
    midKLRAct hR (KLRAlgebra.mk k _ _ a) = 0 := by
  rw [midKLRAct_mk]
  ext y
  rw [midEndAlg_apply, midEnd_eq_zero_of_midRel _ h]
  rfl

theorem redRelations_midKLRAct (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) :
    RedRelations (midKLRAct hR).toNonUnitalAlgHom where
  red_dot a s ha := by
    change midKLRAct hR (KLRAlgebra.x a * KLRAlgebra.e s) = 0
    rw [KLRAlgebra.x, KLRAlgebra.e, ← map_mul]
    refine midKLRAct_eq_zero hR _ ?_
    rw [map_mul, Subalgebra.coe_mul, midFree_fx, midFree_fe]
    exact midRel_red_dot a s ha
  red_cross p hp s ha hb := by
    change midKLRAct hR (KLRAlgebra.ψ p * KLRAlgebra.e s) = 0
    rw [KLRAlgebra.ψ, KLRAlgebra.e, ← map_mul]
    refine midKLRAct_eq_zero hR _ ?_
    rw [map_mul, Subalgebra.coe_mul, midFree_fψ, midFree_fe]
    exact midRel_red_cross p hp s ha hb

open Classical in
/-- The red-ordered loadings of `λ` give the identity on the model. -/
theorem midRel_redOrdered :
    MidRel j hj Q Λ Λc ν ν₀ L hL
      (∑ s ∈ Finset.univ.filter (fun s : Seq (stendhalWeight ℓ ν) => IsRedOrdered s),
        midIdem j hj Q Λ Λc ν ν₀ s) 1 := by
  classical
  refine MidRel.of_midElt_eq ?_
  have hsplit : (∑ s : Seq (stendhalWeight ℓ ν), midIdem j hj Q Λ Λc ν ν₀ s) =
      (∑ s ∈ Finset.univ.filter (fun s : Seq (stendhalWeight ℓ ν) => IsRedOrdered s),
        midIdem j hj Q Λ Λc ν ν₀ s) +
      ∑ s ∈ Finset.univ.filter (fun s : Seq (stendhalWeight ℓ ν) => ¬ IsRedOrdered s),
        midIdem j hj Q Λ Λc ν ν₀ s :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hbad : ∀ s : Seq (stendhalWeight ℓ ν), ¬ IsRedOrdered s →
      bot (midIdem j hj Q Λ Λc ν ν₀ s) * σ 1 = 0 := fun s hs => by
    rw [midStendhal_one_eq_bot, ← map_mul, midIdem, eSum_mul_midMapKLR,
      botMap_insertMap_redOrderedKLR, eSum_insertSet]
    exact (map_sum _ _ _).trans (Finset.sum_eq_zero fun w _ =>
      botMap_e_of_not Q Λ Λc (fun h => hs (isRedOrdered_of_insertSeq' _ h)))
  have hall : bot (∑ s : Seq (stendhalWeight ℓ ν), midIdem j hj Q Λ Λc ν ν₀ s) * σ 1 = σ 1 := by
    rw [show (∑ s : Seq (stendhalWeight ℓ ν), midIdem j hj Q Λ Λc ν ν₀ s) = μ 1 from
      (midMapKLR_one (j := j) (hj := hj) (Q := Q) (Λ := Λ) (Λc := Λc) (ν := ν)
        (ν₀ := ν₀)).symm, midStendhal_one_eq_bot, ← map_mul, ← midMapKLR_mul, one_mul]
  have hB : bot 1 * σ 1 = σ 1 := by
    rw [show (bot 1 : Tp) = 1 from map_one (botMap k Q Λ Λc j hj ν ν₀), one_mul]
  rw [hsplit] at hall
  simp only [map_add, add_mul, map_sum, Finset.sum_mul] at hall
  rw [Finset.sum_eq_zero (s := Finset.univ.filter fun s => ¬ IsRedOrdered s)
    fun s hs => hbad s (Finset.mem_filter.1 hs).2, add_zero] at hall
  rw [midElt, midElt, mul_assoc, mul_assoc, hB, map_sum, Finset.sum_mul, hall]

theorem midKLRAct_redOrderedKLR (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) :
    midKLRAct hR (redOrderedKLR k Q Λ ν) = 1 := by
  classical
  have h : redOrderedKLR k Q Λ ν = KLRAlgebra.mk k _ _
      (∑ s ∈ Finset.univ.filter (fun s : Seq (stendhalWeight ℓ ν) => IsRedOrdered s),
        fe k _ s) := by
    rw [redOrderedKLR, map_sum]; rfl
  rw [h, midKLRAct_mk, ← map_one (midEndAlg L hL)]
  refine midEndAlg_eq_of_midRel ?_
  rw [map_sum]
  simp only [AddSubmonoidClass.coe_finsetSum, midFree_fe, OneMemClass.coe_one]
  convert midRel_redOrdered (L := L) (hL := hL) (j := j) (hj := hj) (Q := Q) (Λ := Λ)
    (Λc := Λc) (ν := ν) (ν₀ := ν₀)

/-- The action of a diagram of `λ` commutes with the right action of `T̃^{λ⁺}`. -/
theorem midKLRAct_smul (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (z : Rλ) (b : Tpᵐᵒᵖ)
    (y : MidModel j hj Q Λ Λc ν ν₀ L) : midKLRAct hR z (b • y) = b • midKLRAct hR z y := by
  obtain ⟨a, rfl⟩ := KLRAlgebra.mk_surjective z
  rw [midKLRAct_mk, midEndAlg_apply, midEndAlg_apply, LinearMap.map_smul]

variable (L hL) in
/-- **The action of `T̃^λ` on the model.** -/
def midLeftAlg (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) :
    T →ₐ[k] Module.End k (MidModel j hj Q Λ Λc ν ν₀ L) where
  toFun z := stendhalLift (redRelations_midKLRAct hR) z
  map_one' := by
    change allOrdersLift (redRelations_midKLRAct hR)
      (StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν) = 1
    exact (congrArg (allOrdersLift (redRelations_midKLRAct hR))
      (ofKLR_redOrderedKLR Q Λ ν).symm).trans
      ((allOrdersLift_ofKLR _ _).trans (midKLRAct_redOrderedKLR hR))
  map_mul' z z' := map_mul _ z z'
  map_zero' := map_zero _
  map_add' z z' := map_add _ z z'
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul]
    change c • allOrdersLift (redRelations_midKLRAct hR)
      (StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν) = _
    rw [(congrArg (allOrdersLift (redRelations_midKLRAct hR))
      (ofKLR_redOrderedKLR Q Λ ν).symm).trans
      ((allOrdersLift_ofKLR _ _).trans (midKLRAct_redOrderedKLR hR)),
      Algebra.algebraMap_eq_smul_one]

theorem midLeftAlg_smul (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (z : T) (b : Tpᵐᵒᵖ)
    (y : MidModel j hj Q Λ Λc ν ν₀ L) :
    midLeftAlg L hL hR z (b • y) = b • midLeftAlg L hL hR z y := by
  obtain ⟨w, hw⟩ := StendhalAlgebraAllOrders.ofKLR_surjective (k := k) (Q := Q) (Λ := Λ)
    (ν := ν) z.val
  change allOrdersLift (redRelations_midKLRAct hR) z.val (b • y) =
    b • allOrdersLift (redRelations_midKLRAct hR) z.val y
  rw [← hw, allOrdersLift_ofKLR]
  exact midKLRAct_smul hR w b y

variable (L) in
/-- The right action of `T̃^{λ⁺}` on the model, as an algebra map. -/
def midRightAlg : Tpᵐᵒᵖ →ₐ[k] Module.End k (MidModel j hj Q Λ Λc ν ν₀ L) :=
  Algebra.lsmul k k (MidModel j hj Q Λ Λc ν ν₀ L)

variable (L hL) in
/-- **The bimodule structure on the model**, given the KLR relations on it. -/
def midEnvAlg (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) :
    Env k Q Λ Λc j hj ν ν₀ →+* Module.End k (MidModel j hj Q Λ Λc ν ν₀ L) :=
  (Algebra.TensorProduct.lift (midLeftAlg L hL hR) (midRightAlg L) fun z b =>
    LinearMap.ext fun y => by
      rw [Module.End.mul_apply, Module.End.mul_apply]
      exact midLeftAlg_smul hR z b y).toRingHom

theorem midEnvAlg_mk (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (a : T) (b : Tp)
    (y : MidModel j hj Q Λ Λc ν ν₀ L) :
    midEnvAlg L hL hR (Env.mk a b) y = midLeftAlg L hL hR a (op b • y) := rfl

end Model

end Categorification.Stendhal.CupCap

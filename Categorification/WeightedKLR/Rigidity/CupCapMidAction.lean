/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidSlides
import Categorification.WeightedKLR.Rigidity.CupCapSlidingLeft

/-!
# Endomorphisms of the model of a cap after `λ_j` given by diagrams above the maximum

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17. Let `L` be a right `T̃^{(μ,μ*)}`-module
supported on the loadings `μ ⋯ μ*`. A diagram `Y` of `λ⁺` placed above the elements of the model
`L ⊗ e T̃^{λ⁺}` (`CupCap.MidModel`) gives an endomorphism of the right `T̃^{λ⁺}`-module, as soon as
the diagrams at the maximum slide through `Y` up to diagrams in which a strand leaves the window
at the top (`CupCap.MidSlides`): `CupCap.midEnd`. These endomorphisms compose as the diagrams
multiply (`CupCap.midEnd_mul`).

The diagrams representing the generators of `T̃^λ` slide: idempotents, dots and crossings away
from the red strand `λ_{j+1}` commute with the diagrams at the maximum, and a crossing of `λ_{j+1}`
with a black strand is that crossing in `λ⁺` composed with the passage of the black strand under
the maximum (`CupCap.midCross`), through which the diagrams at the maximum slide
(`CupCap.slides`, `CupCap.slidesLeft`).

## Main definitions

* `CupCap.midExit`: the diagrams in which a strand leaves the window at the top.
* `CupCap.MidSlides`: the diagrams through which the diagrams at the maximum slide.
* `CupCap.midEnd`: the endomorphism of the model given by a sliding diagram.
* `CupCap.midIdem`, `CupCap.midDot`, `CupCap.midCross`: the generators of `T̃^λ`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite InductionAlong

section Slides

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} (j : ℕ) (hj : j ≤ ℓ)
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  (ν ν₀ : Multiset I)

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Rc" => KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)
local notation "ι" => insertMap (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc
local notation "E" s:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s (midPos j s) (midPos_le j s))
local notation "μ" => midMapKLR j hj Q Λ Λc ν ν₀

/-- The diagrams in which a strand at the maximum leaves the window at `midPos s` at the top,
for all loadings `s` of `λ`. -/
def midExit : Submodule k Rp :=
  ⨆ s : Seq (stendhalWeight ℓ ν), exitSpan Q Λ Λc j hj s (midPos j s) (midPos_le j s)

/-- **The diagrams through which the diagrams at the maximum slide**, up to diagrams in which a
strand leaves the window at the top. -/
def MidSlides (Y : Rp) : Prop := ∀ w : Rc, Y * μ w - μ w * Y ∈ midExit j hj Q Λ Λc ν ν₀

variable {j hj Q Λ Λc ν ν₀}

theorem mem_midExit (s : Seq (stendhalWeight ℓ ν)) {y : Rp}
    (hy : y ∈ exitSpan Q Λ Λc j hj s (midPos j s) (midPos_le j s)) :
    y ∈ midExit j hj Q Λ Λc ν ν₀ :=
  (le_iSup (fun s => exitSpan Q Λ Λc j hj s (midPos j s) (midPos_le j s)) s) hy

theorem midExit_mul_right {y : Rp} (hy : y ∈ midExit j hj Q Λ Λc ν ν₀) (r : Rp) :
    y * r ∈ midExit j hj Q Λ Λc ν ν₀ := by
  refine Submodule.iSup_induction _ (motive := fun y => y * r ∈ midExit j hj Q Λ Λc ν ν₀) hy
    (fun s y hy => mem_midExit s (exitSpan_mul_right s _ hy r)) ?_ ?_
  · rw [zero_mul]; exact zero_mem _
  · intro y y' h h'; rw [add_mul]; exact add_mem h h'

theorem insertMap_eq_midMapKLR_mul (s : Seq (stendhalWeight ℓ ν)) (z : Rc) :
    ι s (midPos j s) (midPos_le j s) z = μ z * E s := by
  rw [← insertMap_one Q Λ Λc s (midPos_le j s), midMapKLR_mul_insertMap, mul_one]

theorem midMapKLR_mul_mem_midExit {z : Rc} (hz : z ∈ capNull (k := k) Q Λc ν₀) (r : Rp) :
    μ z * r ∈ midExit j hj Q Λ Λc ν ν₀ := by
  rw [midMapKLR, Finset.sum_mul]
  exact Submodule.sum_mem _ fun s _ => mem_midExit s (mem_exitSpan s _ hz r)

theorem MidSlides.mul_mem {Y : Rp} (hY : MidSlides j hj Q Λ Λc ν ν₀ Y) {y : Rp}
    (hy : y ∈ midExit j hj Q Λ Λc ν ν₀) : Y * y ∈ midExit j hj Q Λ Λc ν ν₀ := by
  refine Submodule.iSup_induction _ (motive := fun y => Y * y ∈ midExit j hj Q Λ Λc ν ν₀) hy
    (fun s y hy => ?_) ?_ ?_
  · induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨z, hz, r, rfl⟩ := hy
      rw [insertMap_eq_midMapKLR_mul, mul_assoc,
        show Y * (μ z * (E s * r)) = (Y * μ z - μ z * Y) * (E s * r) + μ z * (Y * (E s * r)) by
          noncomm_ring]
      exact add_mem (midExit_mul_right (hY z) _) (midMapKLR_mul_mem_midExit hz _)
    | zero => rw [mul_zero]; exact zero_mem _
    | add y y' _ _ h h' => rw [mul_add]; exact add_mem h h'
    | smul c y _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h
  · rw [mul_zero]; exact zero_mem _
  · intro y y' h h'; rw [mul_add]; exact add_mem h h'

theorem MidSlides.one : MidSlides j hj Q Λ Λc ν ν₀ (1 : Rp) := fun w => by
  rw [one_mul, mul_one, sub_self]; exact zero_mem _

theorem MidSlides.add {Y Y' : Rp} (hY : MidSlides j hj Q Λ Λc ν ν₀ Y)
    (hY' : MidSlides j hj Q Λ Λc ν ν₀ Y') : MidSlides j hj Q Λ Λc ν ν₀ (Y + Y') := fun w => by
  convert add_mem (hY w) (hY' w) using 1; noncomm_ring

theorem MidSlides.smul (c : k) {Y : Rp} (hY : MidSlides j hj Q Λ Λc ν ν₀ Y) :
    MidSlides j hj Q Λ Λc ν ν₀ (c • Y) := fun w => by
  rw [smul_mul_assoc, mul_smul_comm, ← smul_sub]; exact Submodule.smul_mem _ c (hY w)

theorem MidSlides.mul {Y Y' : Rp} (hY : MidSlides j hj Q Λ Λc ν ν₀ Y)
    (hY' : MidSlides j hj Q Λ Λc ν ν₀ Y') : MidSlides j hj Q Λ Λc ν ν₀ (Y * Y') := fun w => by
  rw [show Y * Y' * μ w - μ w * (Y * Y') = Y * (Y' * μ w - μ w * Y') + (Y * μ w - μ w * Y) * Y' by
    noncomm_ring]
  exact add_mem (hY.mul_mem (hY' w)) (midExit_mul_right (hY w) Y')

theorem MidSlides.sum {ι' : Type*} (S : Finset ι') {Y : ι' → Rp}
    (hY : ∀ a ∈ S, MidSlides j hj Q Λ Λc ν ν₀ (Y a)) :
    MidSlides j hj Q Λ Λc ν ν₀ (∑ a ∈ S, Y a) := fun w => by
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Submodule.sum_mem _ fun a ha => hY a ha w

end Slides

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Model

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Rc" => KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
local notation "bot" => botMap k Q Λ Λc j hj ν ν₀
local notation "σ" => midStendhal j hj Q Λ Λc ν ν₀
local notation "μ" => midMapKLR j hj Q Λ Λc ν ν₀

theorem sandwich_comm {R : Type*} [Ring R] (e b y : R) (he : e * e = e) (hc : e * b = b * e) :
    e * y * e * (e * b) - e * b * (e * y * e) = e * (y * b - b * y) * e := by
  have h1 : e * y * e * (e * b) = e * y * b * e := by
    rw [show e * y * e * (e * b) = e * y * (e * e) * b by noncomm_ring, he, mul_assoc (e * y) e b,
      hc]
    noncomm_ring
  have h2 : e * b * (e * y * e) = e * b * y * e := by
    rw [show e * b * (e * y * e) = e * b * e * y * e by noncomm_ring, mul_assoc e b e, ← hc,
      ← mul_assoc, he]
  rw [h1, h2]
  noncomm_ring

variable (j hj Q Λ Λc ν ν₀) in
/-- The element `e · Y · e` of `T̃^{λ⁺}`, in the opposite ring. -/
def midElt (Y : Rp) : Tpᵐᵒᵖ := op (σ 1 * bot Y * σ 1)

theorem midStendhal_one_mul_self : σ 1 * σ 1 = σ 1 := by rw [← map_mul, one_mul]

theorem midStendhal_one_eq_bot : σ 1 = bot (μ (redOrderedKLR k Q Λc ν₀)) := by
  rw [midStendhal_one_eq_midBot, midBot_apply]

theorem midElt_unit (Y : Rp) :
    midElt j hj Q Λ Λc ν ν₀ Y * midOp j hj Q Λ Λc ν ν₀ 1 = midElt j hj Q Λ Λc ν ν₀ Y := by
  rw [midElt, midOp_apply, unop_one, ← op_mul, ← mul_assoc, ← mul_assoc,
    midStendhal_one_mul_self]

variable (L : Type*) [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

variable (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
  op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)

include hL in
theorem midElt_mem_nullIdeal {y : Rp} (hy : y ∈ midExit j hj Q Λ Λc ν ν₀) :
    midElt j hj Q Λ Λc ν ν₀ y ∈ nullIdeal L (midOp j hj Q Λ Λc ν ν₀) := by
  have h : midElt j hj Q Λ Λc ν ν₀ y = op (σ 1) * op (σ 1 * bot y) := by
    rw [midElt, ← op_mul]
  rw [h]
  refine mul_mem_nullIdeal _ ?_
  refine Submodule.iSup_induction _
    (motive := fun y => op (σ 1 * bot y) ∈ nullIdeal L (midOp j hj Q Λ Λc ν ν₀)) hy
    (fun s y hy => exitSpan_midPos_mem_nullIdeal L hL s hy) ?_ ?_
  · rw [map_zero, mul_zero, op_zero]; exact zero_mem _
  · intro y y' h h'; rw [map_add, mul_add, op_add]; exact add_mem h h'

theorem midElt_sub (Y Y' : Rp) :
    midElt j hj Q Λ Λc ν ν₀ Y - midElt j hj Q Λ Λc ν ν₀ Y' =
      midElt j hj Q Λ Λc ν ν₀ (Y - Y') := by
  rw [midElt, midElt, midElt, ← op_sub, map_sub, mul_sub, sub_mul]

include hL in
/-- **A sliding diagram intertwines the diagrams at the maximum**, on `L`. -/
theorem intertwinesOn_midElt {Y : Rp} (hY : MidSlides j hj Q Λ Λc ν ν₀ Y) :
    IntertwinesOn L (midOp j hj Q Λ Λc ν ν₀) (midOp j hj Q Λ Λc ν ν₀)
      (midElt j hj Q Λ Λc ν ν₀ Y) where
  unit := midElt_unit Y
  slide a z v := by
    refine IntertwinesOn.slide_of_mem_nullIdeal _ ?_ z v
    obtain ⟨w, hw⟩ := cupMap_surjective Q Λc a.unop
    obtain rfl : a = op (cupMap k Q Λc ν₀ w) := by rw [hw, op_unop]
    have hc := (commute_midStendhal_one_midBot (j := j) (hj := hj) (Λ := Λ) (ν := ν) w).eq
    have key : midOp j hj Q Λ Λc ν ν₀ (op (cupMap k Q Λc ν₀ w)) * midElt j hj Q Λ Λc ν ν₀ Y -
        midElt j hj Q Λ Λc ν ν₀ Y * midOp j hj Q Λ Λc ν ν₀ (op (cupMap k Q Λc ν₀ w)) =
        midElt j hj Q Λ Λc ν ν₀ (Y * μ w - μ w * Y) := by
      rw [midOp_apply, unop_op, midStendhal_cupMap', midElt, ← op_mul, ← op_mul, ← op_sub,
        midElt, map_sub, map_mul, map_mul, ← midBot_apply]
      rw [midBot_apply] at hc
      congr 1
      exact sandwich_comm _ _ _ midStendhal_one_mul_self hc
    rw [key]
    exact midElt_mem_nullIdeal L hL (hY w)

variable {L}

/-- Elements of the corner whose difference lies in the null ideal give the same map. -/
theorem natMapOn_eq_of_sub_mem {x x' : Tpᵐᵒᵖ}
    (hx : IntertwinesOn L (midOp j hj Q Λ Λc ν ν₀) (midOp j hj Q Λ Λc ν ν₀) x)
    (hx' : IntertwinesOn L (midOp j hj Q Λ Λc ν ν₀) (midOp j hj Q Λ Λc ν ν₀) x')
    (h : x - x' ∈ nullIdeal L (midOp j hj Q Λ Λc ν ν₀)) : natMapOn hx = natMapOn hx' :=
  Ind.ext fun z v => by
    rw [natMapOn_tmul, natMapOn_tmul]
    have hz := mul_mem_nullIdeal z.1 h
    have hsplit : cornerMulOf hx.unit z =
        ⟨z.1 * (x - x'), mem_lIdeal_of_mem_nullIdeal hz⟩ + cornerMulOf hx'.unit z :=
      Subtype.ext (by simp [mul_sub])
    rw [hsplit, Ind.add_tmul, tmul_eq_zero_of_mem_nullIdeal hz, zero_add]

variable (L) in
/-- **The endomorphism of the model given by a sliding diagram** `Y`: `Z ⊗ v ↦ e Y e Z ⊗ v`. -/
def midEnd {Y : Rp} (hY : MidSlides j hj Q Λ Λc ν ν₀ Y) :
    MidModel j hj Q Λ Λc ν ν₀ L →ₗ[Tpᵐᵒᵖ] MidModel j hj Q Λ Λc ν ν₀ L :=
  natMapOn (intertwinesOn_midElt L hL hY)

theorem midEnd_tmul {Y : Rp} (hY : MidSlides j hj Q Λ Λc ν ν₀ Y) (Z : Tp) (v : L) :
    midEnd L hL hY (Ind.tmul (midGen j hj Q Λ Λc ν ν₀ Z) v) =
      Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (bot Y * σ 1 * Z)) v := by
  rw [midEnd, natMapOn_tmul]
  congr 1
  apply Subtype.ext
  change op (σ 1 * Z) * op (σ 1 * bot Y * σ 1) = op (σ 1 * (bot Y * σ 1 * Z))
  rw [← op_mul]
  congr 1
  rw [← mul_assoc (σ 1 * bot Y * σ 1), mul_assoc (σ 1 * bot Y), midStendhal_one_mul_self]
  simp only [mul_assoc]

/-- Sliding diagrams differing by diagrams in which a strand leaves the window give the same
endomorphism. -/
theorem midEnd_congr {Y Y' : Rp} (hY : MidSlides j hj Q Λ Λc ν ν₀ Y)
    (hY' : MidSlides j hj Q Λ Λc ν ν₀ Y') (h : Y - Y' ∈ midExit j hj Q Λ Λc ν ν₀) :
    midEnd L hL hY = midEnd L hL hY' :=
  natMapOn_eq_of_sub_mem _ _ (by rw [midElt_sub]; exact midElt_mem_nullIdeal L hL h)

theorem midEnd_eq_of_eq {Y Y' : Rp} (hY : MidSlides j hj Q Λ Λc ν ν₀ Y)
    (hY' : MidSlides j hj Q Λ Λc ν ν₀ Y') (h : Y = Y') :
    midEnd L hL hY = midEnd L hL hY' := by
  subst h; rfl

/-- **The endomorphisms compose as the diagrams multiply.** -/
theorem midEnd_mul {Y Y' : Rp} (hY : MidSlides j hj Q Λ Λc ν ν₀ Y)
    (hY' : MidSlides j hj Q Λ Λc ν ν₀ Y') :
    midEnd L hL (hY.mul hY') = (midEnd L hL hY).comp (midEnd L hL hY') := by
  rw [midEnd, midEnd, midEnd, natMapOn_comp]
  refine natMapOn_eq_of_sub_mem _ _ ?_
  have h : midElt j hj Q Λ Λc ν ν₀ (Y * Y') -
      midElt j hj Q Λ Λc ν ν₀ Y' * midElt j hj Q Λ Λc ν ν₀ Y =
      -midElt j hj Q Λ Λc ν ν₀ ((Y * μ (redOrderedKLR k Q Λc ν₀) -
        μ (redOrderedKLR k Q Λc ν₀) * Y) * Y') := by
    rw [midElt, midElt, midElt, midElt, ← op_mul, ← op_sub, ← op_neg]
    congr 1
    simp only [map_mul, map_sub, ← midStendhal_one_eq_bot]
    have he := midStendhal_one_mul_self (j := j) (hj := hj) (Q := Q) (Λ := Λ) (Λc := Λc)
      (ν := ν) (ν₀ := ν₀)
    generalize σ 1 = e at he ⊢
    generalize bot Y = A
    generalize bot Y' = B
    have h1 : e * A * e * (e * B * e) = e * A * e * B * e := by
      rw [show e * A * e * (e * B * e) = e * A * (e * e) * B * e by noncomm_ring, he]
    have h2 : e * ((A * e - e * A) * B) * e = e * A * e * B * e - e * A * B * e := by
      rw [show e * ((A * e - e * A) * B) * e = e * A * e * B * e - e * e * A * B * e by
        simp only [sub_mul, mul_sub, mul_assoc], he]
    rw [h1, h2, neg_sub]
    simp only [mul_assoc]
  rw [h]
  exact neg_mem (midElt_mem_nullIdeal L hL (midExit_mul_right (hY _) _))

theorem midEnd_add {Y Y' : Rp} (hY : MidSlides j hj Q Λ Λc ν ν₀ Y)
    (hY' : MidSlides j hj Q Λ Λc ν ν₀ Y') :
    midEnd L hL (hY.add hY') = midEnd L hL hY + midEnd L hL hY' :=
  Ind.ext fun z v => by
    rw [LinearMap.add_apply, midEnd, midEnd, midEnd, natMapOn_tmul, natMapOn_tmul, natMapOn_tmul,
      ← Ind.add_tmul]
    congr 1
    apply Subtype.ext
    change z.1 * midElt j hj Q Λ Λc ν ν₀ (Y + Y') =
      z.1 * midElt j hj Q Λ Λc ν ν₀ Y + z.1 * midElt j hj Q Λ Λc ν ν₀ Y'
    rw [← mul_add, midElt, midElt, midElt, ← op_add, map_add, mul_add, add_mul]

theorem midEnd_one : midEnd L hL (MidSlides.one (j := j) (hj := hj) (Q := Q) (Λ := Λ)
    (Λc := Λc) (ν := ν) (ν₀ := ν₀)) = LinearMap.id :=
  Ind.ext fun z v => by
    rw [midEnd, natMapOn_tmul, LinearMap.id_apply]
    congr 1
    apply Subtype.ext
    change z.1 * op (σ 1 * bot 1 * σ 1) = z.1
    have hz : z.1 * op (σ 1) = z.1 := z.2
    calc z.1 * op (σ 1 * bot 1 * σ 1) = z.1 * op (σ 1) := by
          congr 1
          rw [show (bot 1 : Tp) = 1 from map_one (botMap k Q Λ Λc j hj ν ν₀), mul_one,
            midStendhal_one_mul_self]
      _ = z.1 := hz

end Model

end Categorification.Stendhal.CupCap

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LeftStandardParameterTransport
import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleBalancedGrading

/-!
# The transported ordered cover of the label-two middle standard

At the middle loading, the transported augmentation is the literal
quotient map and preserves the parabolic grading. This supplies the
degree-zero augmentation for the supported resolution used in Webster
§8.2.
-/

noncomputable section

set_option maxHeartbeats 2400000
set_option maxRecDepth 2048

namespace Categorification.Stendhal.LabelTwo

open KLR Categorification.ModuleFiltration

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

private theorem transportedQuotient_on_idem {A B I : Type} [Ring A] [Ring B]
    {S : I → ModuleCat A} {e : I → A} {e' : I → B} {above : I → I → Prop}
    (D : OrderedStandardCovers S e above) (σ : A ≃+* B)
    (h : (fun i => σ (e i)) = e') (i : I)
    (he : IsIdempotentElem (e i)) (he' : IsIdempotentElem (e' i)) :
    let D' : OrderedStandardCovers
      (fun j => (ModuleCat.restrictScalars σ.symm.toRingHom).obj (S j)) e' above :=
      h ▸ D.transport σ
    D'.quotient i ⟨e' i, he'.eq⟩ = D.quotient i ⟨e i, he.eq⟩ := by
  subst e'
  let x : lIdeal (e i) := ⟨σ.symm (σ (e i)), by
    change σ.symm (σ (e i)) * e i = σ.symm (σ (e i))
    simp only [RingEquiv.symm_apply_apply, he.eq]⟩
  change D.quotient i x = D.quotient i ⟨e i, he.eq⟩
  exact congrArg (D.quotient i) (Subtype.ext (σ.symm_apply_apply _))

variable (k : Type) [Field k]

local notation "ν₂" => (({()} : Multiset Unit) + {()})
local notation "A₂" => TensorProductAlgebra k (parameter k) weights ν₂
local notation "I₂" => {s : KLR.Seq (stendhalWeight 2 ν₂) // IsRedOrdered s}
set_option quotPrecheck false in
local notation "l₂" => (⟨loading, loading_ordered⟩ : I₂)

variable {qSrc : Unit → Unit → MvPolynomial (Fin 2) k}
  (σ : TensorProductAlgebra k qSrc weights (({()} : Multiset Unit) + {()}) ≃+*
    TensorProductAlgebra k (parameter k) weights (({()} : Multiset Unit) + {()}))
  (hσ : ∀ (t : KLR.Seq (stendhalWeight 2 (({()} : Multiset Unit) + {()}))) (ht : IsRedOrdered t),
    σ (seqIdem qSrc weights t ht) = seqIdem (parameter k) weights t ht)

local notation "A₀" => TensorProductAlgebra k qSrc weights ν₂
set_option quotPrecheck false in
local notation "Std₀" => fun t : I₂ => ModuleCat.of A₀ (leftStandard qSrc weights t.1 t.2)
set_option quotPrecheck false in
local notation "U₀" t:arg =>
  (leftUpper qSrc weights t.1 t.2).comap
    (lIdeal (seqIdem qSrc weights t.1 t.2)).subtype
local notation "e₂" => seqIdem (parameter k) weights loading loading_ordered
local notation "g₂" => leftStandardUnit (parameter k) weights loading loading_ordered
local notation "g₀" => leftStandardUnit qSrc weights loading loading_ordered

/-- On the actual middle loading, the augmentation transported from the source
parameter sends the standard generator to its quotient class. -/
theorem middleOrderedCoversTransport_quotient
    (hU : ∀ t : I₂, ∃ m : List I₂, (∀ v ∈ m, StendhalLT t.1 v.1) ∧
      HasFiltration Std₀ m (ModuleCat.of A₀ (U₀ t)))
    (x : lIdeal e₂) :
    (orderedStandardCoversTransport weights σ hσ hU).quotient l₂ x =
      (Submodule.Quotient.mk x : Standard k) := by
  let D₀ := orderedStandardCovers qSrc weights hU
  let heq : (fun t : I₂ => σ (seqIdem qSrc weights t.1 t.2)) =
      (fun t : I₂ => seqIdem (parameter k) weights t.1 t.2) :=
    funext fun t => hσ t.1 t.2
  let D₁ : OrderedStandardCovers
      (fun t => (ModuleCat.restrictScalars σ.symm.toRingHom).obj (Std₀ t))
      (fun t => seqIdem (parameter k) weights t.1 t.2)
      (fun s t => StendhalLT s.1 t.1) :=
    heq ▸ D₀.transport σ
  let L := leftStandardRestrictedEquiv weights σ.symm
    (fun t ht => (σ.symm_apply_eq).mpr (hσ t ht).symm) loading loading_ordered
  let u : lIdeal e₂ := ⟨e₂, seqIdem_mul_self (parameter k) weights loading loading_ordered⟩
  have hgen : D₁.quotient l₂ u = g₀ :=
    transportedQuotient_on_idem D₀ σ heq l₂
      (seqIdem_mul_self qSrc weights loading loading_ordered)
      (seqIdem_mul_self (parameter k) weights loading loading_ordered)
  have hunit : L g₂ = g₀ := by
    have hz (t : KLR.Seq (stendhalWeight 2 ν₂)) (ht : IsRedOrdered t)
        (a : A₂) (hlt : StendhalLT loading t) :
        (seqIdem (parameter k) weights t ht * a) •
            (show (ModuleCat.restrictScalars σ.symm.toRingHom).obj (Std₀ l₂) from g₀) = 0 := by
      change σ.symm (seqIdem (parameter k) weights t ht * a) • g₀ = 0
      rw [map_mul, show σ.symm (seqIdem (parameter k) weights t ht) = seqIdem qSrc weights t ht from
        (σ.symm_apply_eq).mpr (hσ t ht).symm, mul_smul,
        seqIdem_smul_leftStandard_eq_zero qSrc weights loading_ordered ht hlt]
    change leftStandardLift loading loading_ordered
      (show (ModuleCat.restrictScalars σ.symm.toRingHom).obj (Std₀ l₂) from g₀) hz g₂ = _
    refine leftStandardLift_unit loading loading_ordered _ ?_ _
    change σ.symm e₂ • g₀ = g₀
    rw [show σ.symm e₂ = seqIdem qSrc weights loading loading_ordered from
      (σ.symm_apply_eq).mpr (hσ loading loading_ordered).symm]
    exact (leftStandard_mk_eq_smul_unit loading loading_ordered
      ⟨seqIdem qSrc weights loading loading_ordered,
        seqIdem_mul_self qSrc weights loading loading_ordered⟩).symm
  let D := orderedStandardCoversTransport weights σ hσ hU
  have hu : D.quotient l₂ u = g₂ := by
    change L.symm (D₁.quotient l₂ u) = g₂
    exact (L.symm_apply_eq).mpr (hgen.trans hunit.symm)
  have hx : (x.val : A₂) • u = x := Subtype.ext x.property
  calc
    D.quotient l₂ x = D.quotient l₂ ((x.val : A₂) • u) := congrArg _ hx.symm
    _ = x.val • g₂ := by rw [map_smul, hu]
    _ = _ := (leftStandard_mk_eq_smul_unit loading loading_ordered x).symm

/-- The actual ordered augmentation preserves the middle parabolic grade. -/
theorem middleOrderedCoversTransport_quotient_mem_grade
    (hU : ∀ t : I₂, ∃ m : List I₂, (∀ v ∈ m, StendhalLT t.1 v.1) ∧
      HasFiltration Std₀ m (ModuleCat.of A₀ (U₀ t)))
    {j : ℤ} {x : lIdeal e₂} (hx : x.val ∈ middleTensorGrade k (labelTwoGradingDatum k) j) :
    (orderedStandardCoversTransport weights σ hσ hU).quotient l₂ x ∈
      middleStandardGrade k (labelTwoGradingDatum k) j := by
  rw [middleOrderedCoversTransport_quotient]
  exact middleStandardQuotient_mem_grade k hx

end Categorification.Stendhal.LabelTwo

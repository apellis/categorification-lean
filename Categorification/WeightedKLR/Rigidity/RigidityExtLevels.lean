/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.RigidityExtDualStandard
import Categorification.WeightedKLR.Rigidity.StandardizationAdjunction

/-!
# Loadings by the position of the last red strand

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.1, proof
of Proposition 7.8. The standard modules are graded by the number of black strands right of the
last red strand, equivalently by the position `p` of the last red strand. We record which modules
are killed by the loading idempotents `e(s)` whose last red strand sits after (`KilledAfter`) or
at (`KilledAt`) a given position.

## Main results

* `lbl_of_word_eq_websterWord`: the loading of the term `i_T` of the resolution of
  Proposition 7.6 has its last red strand at position `|t| + |T|`.
* `killedAfter_stdLayerModule`: the standardization of a module over the factor algebra of the
  split `θ + β` is killed by the loadings whose last red strand is after position `|θ| + ℓ`.
* `KilledAfter.starDual`, `KilledAt.starDual`: duals keep these properties.
-/

noncomputable section
namespace Categorification

namespace Stendhal

open KLR KLRAlgebra CategoryTheory

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance] ModuleCat.moduleOfAlgebraModule
  ModuleCat.isScalarTower_of_algebra_moduleCat

section Words

variable {I : Type} {ℓ : ℕ}

theorem length_pickIn (u : List I) {T : Multiset ℕ} (hT : T ≤ Multiset.range u.length) :
    (pickIn u T).length = Multiset.card T := by
  classical
  have h1 : (pickIn u T).length =
      ((List.range u.length).filter (fun i => decide (i ∈ T))).length := by
    rw [pickIn, List.length_map]
    have : ((u.zip (List.range u.length)).filter (fun p => decide (p.2 ∈ T))).map Prod.snd =
        (List.range u.length).filter (fun i => decide (i ∈ T)) := by
      change List.map Prod.snd (List.filter ((fun i => decide (i ∈ T)) ∘ Prod.snd) _) = _
      rw [← List.filter_map, List.map_snd_zip (by simp)]
    rw [← this, List.length_map]
  rw [h1]
  have h2 : (((List.range u.length).filter (fun i => decide (i ∈ T)) : List ℕ) : Multiset ℕ) =
      T := by
    refine (Multiset.Nodup.ext (Multiset.coe_nodup.mpr ((List.nodup_range).filter _))
      (Multiset.nodup_of_le hT (Multiset.nodup_range _))).mpr fun a => ?_
    simp only [Multiset.mem_coe, List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨Multiset.mem_range.mp (Multiset.mem_of_le hT h), h⟩⟩
  rw [← Multiset.coe_card, h2]

theorem getElem_websterWord (t : List (I ⊕ Fin (ℓ + 1))) (u : List I) (T : Multiset ℕ)
    (h : t.length + (pickIn u T).length < (websterWord t u T).length) :
    (websterWord t u T)[t.length + (pickIn u T).length] = Sum.inr (Fin.last ℓ) := by
  simp only [websterWord, List.append_assoc]
  rw [List.getElem_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getElem_append_right (by simp)]
  simp

variable {ν : Multiset I}

/-- **The last red strand of `i_T`** (Proposition 7.6) sits at position `|t| + |T|`. -/
theorem lbl_of_word_eq_websterWord {t : List (I ⊕ Fin (ℓ + 1))} {u : List I} {j : ℕ}
    {s : Seq (stendhalWeight (ℓ + 1) ν)} (hs : s.word ∈ websterWords t u j)
    (a : Fin (Multiset.card (stendhalWeight (ℓ + 1) ν))) (ha : a.val = t.length + j) :
    s.lbl a = Sum.inr (Fin.last ℓ) := by
  obtain ⟨T, hT, hw⟩ := Multiset.mem_map.1 hs
  obtain ⟨hle, hcard⟩ := Multiset.mem_powersetCard.1 hT
  have hlen := length_pickIn u hle
  have hidx : a.val = t.length + (pickIn u T).length := by rw [hlen, hcard, ha]
  have hlt : t.length + (pickIn u T).length < (websterWord t u T).length := by
    rw [← hidx, hw, Seq.length_word]; exact a.2
  have key : (websterWord t u T)[t.length + (pickIn u T).length]? =
      some (Sum.inr (Fin.last ℓ)) := by
    rw [List.getElem?_eq_getElem hlt, getElem_websterWord]
  rw [← hidx, hw, List.getElem?_eq_getElem (by simp), Option.some_inj] at key
  simpa [Seq.word, List.getElem_ofFn] using key

end Words

variable {I : Type} {k : Type} [DecidableEq I] [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin (ℓ + 1) → I →₀ ℕ} {ν : Multiset I}

local notation "T" => TensorProductAlgebra k Q Λ ν
local notation "σT" => (tensorFlipRingEquiv (Q := Q) (Λ := Λ) ν : T ≃+* Tᵐᵒᵖ)

variable (Q Λ) in
/-- `Y` is killed by every loading idempotent `e(s)` whose last red strand is after position
`p`. -/
def KilledAfter (p : ℕ) (Y : ModuleCat.{0} (TensorProductAlgebra k Q Λ ν)) : Prop :=
  ∀ (s : Seq (stendhalWeight (ℓ + 1) ν)) (hs : IsRedOrdered s)
    (a : Fin (Multiset.card (stendhalWeight (ℓ + 1) ν))), p < a.val →
    s.lbl a = Sum.inr (Fin.last ℓ) → ∀ y : Y, loadingIdem Q Λ s hs • y = 0

variable (Q Λ) in
/-- `Y` is killed by every loading idempotent `e(s)` whose last red strand is at position `p`. -/
def KilledAt (p : ℕ) (Y : ModuleCat.{0} (TensorProductAlgebra k Q Λ ν)) : Prop :=
  ∀ (s : Seq (stendhalWeight (ℓ + 1) ν)) (hs : IsRedOrdered s)
    (a : Fin (Multiset.card (stendhalWeight (ℓ + 1) ν))), a.val = p →
    s.lbl a = Sum.inr (Fin.last ℓ) → ∀ y : Y, loadingIdem Q Λ s hs • y = 0

/-- A module killed after `p` and at `p` is killed after `p - 1`. -/
theorem KilledAfter.of_killedAt {p : ℕ} {Y : ModuleCat.{0} T} (h₁ : KilledAfter Q Λ (p + 1) Y)
    (h₂ : KilledAt Q Λ (p + 1) Y) : KilledAfter Q Λ p Y := by
  intro s hs a ha hr y
  rcases Nat.lt_or_ge (p + 1) a.val with h | h
  · exact h₁ s hs a h hr y
  · exact h₂ s hs a (by omega) hr y

theorem KilledAfter.mono {p q : ℕ} (hpq : p ≤ q) {Y : ModuleCat.{0} T}
    (h : KilledAfter Q Λ p Y) : KilledAfter Q Λ q Y :=
  fun s hs a ha hr y => h s hs a (by omega) hr y

/-- A loading idempotent killing `Y` kills its dual. -/
theorem loadingIdem_smul_starDual {Y : ModuleCat.{0} T} {s : Seq (stendhalWeight (ℓ + 1) ν)}
    {hs : IsRedOrdered s} (h : ∀ y : Y, loadingIdem Q Λ s hs • y = 0)
    (φ : starDualObj k σT Y) : loadingIdem Q Λ s hs • φ = 0 := by
  refine LinearMap.ext fun y => ?_
  change StarDual.toDual (σ := σT) (φ : StarDual k σT Y)
    (StarDual.bar σT (loadingIdem Q Λ s hs) • y) = 0
  rw [tensorFlip_loadingIdem s hs, h y, map_zero]

theorem KilledAfter.starDual {p : ℕ} {Y : ModuleCat.{0} T} (h : KilledAfter Q Λ p Y) :
    KilledAfter Q Λ p (starDualObj k σT Y) :=
  fun s hs a ha hr => loadingIdem_smul_starDual (h s hs a ha hr)

theorem KilledAt.starDual {p : ℕ} {Y : ModuleCat.{0} T} (h : KilledAt Q Λ p Y) :
    KilledAt Q Λ p (starDualObj k σT Y) :=
  fun s hs a ha hr => loadingIdem_smul_starDual (h s hs a ha hr)

/-- A module killed after `p` is killed by the ideal of smaller suffixes at `p`. -/
theorem KilledAfter.smul_eq_zero {p : Fin (Multiset.card (stendhalWeight (ℓ + 1) ν))}
    {Y : ModuleCat.{0} T} (h : KilledAfter Q Λ p.val Y) {x : T}
    (hx : x ∈ smallerSuffixIdeal Q Λ p) (y : Y) : x • y = 0 := by
  have hJ : smallerSuffixIdeal Q Λ p ≤ TwoSidedIdeal.ker
      (Algebra.lsmul k k Y : T →ₐ[k] Module.End k Y).toRingHom := by
    refine TwoSidedIdeal.span_le.mpr ?_
    rintro _ ⟨s, hs, a, hpa, hr, rfl⟩
    exact (TwoSidedIdeal.mem_ker _).mpr (LinearMap.ext fun y => h s hs a hpa hr y)
  exact LinearMap.congr_fun ((TwoSidedIdeal.mem_ker _).mp (hJ hx)) y

variable (Q Λ) (hQ : KLRSymm Q)

/-- **Standardizations are killed after their last red position**: the standardization of a
module over the factor algebra of `θ + β` is killed by the loadings whose last red strand is
after position `|θ| + ℓ`. -/
theorem killedAfter_stdLayerModule (c : StdLayer Q Λ ν) :
    KilledAfter Q Λ (Multiset.card c.θ + ℓ) (stdLayerModule Q Λ hQ c) := by
  obtain ⟨θ, β, h, M⟩ := c
  subst h
  intro s hs a ha hr y
  have hK := killedByLevel_parabolicStandardT Q Λ θ β hQ M.carrier
  refine hK _ (TwoSidedIdeal.subset_span ⟨s, hs, a, ?_, hr, rfl⟩) y
  change Multiset.card θ + ℓ < a.val
  exact ha

end Stendhal

end Categorification

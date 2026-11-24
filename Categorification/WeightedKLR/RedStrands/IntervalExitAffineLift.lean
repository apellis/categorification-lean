/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.IntervalColumnSpan
import Categorification.WeightedKLR.RedStrands.FiniteExitAffineLift

/-!
# Affine lifting through the exchanged red interval

Webster, arXiv:1309.3796v2, §6.1, Proposition 6.4 and the cut after (6.21).
The interval spanning result gives the uniform finite exit family needed for the
lift through the global violation.
-/
noncomputable section
open scoped BigOperators
namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLRAlgebra TypeA Equiv
variable {I k : Type} [DecidableEq I] [CommRing k] {ℓ : ℕ} {ν : Multiset I}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card μ
local notation "A" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "B" => BraidedStendhalAlgebra k Q Λ ν
local notation "raw" => ofKLR k Q Λ ν

/-- Interval exit permutations indexed independently of the choice of upper loading. -/
abbrev IntervalExit (s t : Seq μ) (q p : Fin m) :=
  {v : Perm (Fin m) // (∀ j, j < q ∨ p < j → v j = j) ∧
    redWord (v • s) = redWord t ∧ (v q : ℕ) = v p + 1}

noncomputable instance (s t : Seq μ) (q p : Fin m) : Fintype (IntervalExit s t q p) :=
  Fintype.ofFinite _

/-- The interval exits generate every affine column at the fixed upper red order. -/
theorem intervalExit_generate (hQ : KLRSymm Q)
    (s t : Seq μ) {q p : Fin m} {a b : Fin ℓ} {L M : List (Fin ℓ)}
    (hq : s.lbl q = .inr a) (hp : s.lbl p = .inr b)
    (hs : redWord s = L ++ a :: b :: M) (ht : redWord t = L ++ b :: a :: M)
    (v : Seq μ) (hv : redWord v = redWord t) (z : B) :
    ∃ c : IntervalExit s t q p → B,
      raw (e v) * z * raw (e s) =
        ∑ i, c i * raw (ψw (canWord m i.val) * e s) := by
  classical
  obtain ⟨a, rfl⟩ := ofKLR_surjective (Q := Q) (Λ := Λ) z
  have h := mem_span_interval_crossing_column Q Λ hQ s v hq hp hs (hv.trans ht) a
  suffices H : ∀ y ∈ Submodule.span k {y : A | ∃ (x : A) (w : Perm (Fin m)),
      (∀ j, j < q ∨ p < j → w j = j) ∧ redWord (w • s) = redWord v ∧
      (w q : ℕ) = w p + 1 ∧ e v * x * e (w • s) = x ∧
      y = x * (ψw (canWord m w) * e s)},
      ∃ c : IntervalExit s t q p → B,
        raw y = ∑ i, c i * raw (ψw (canWord m i.val) * e s) by
    simpa only [map_mul] using H _ h
  intro y hy
  induction hy using Submodule.span_induction with
  | zero => exact ⟨fun _ => 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨d, hd⟩ := hy
    refine ⟨fun i => c i + d i, ?_⟩
    simp only [map_add, hc, hd, add_mul, Finset.sum_add_distrib]
  | smul r x _ hx =>
    obtain ⟨c, hc⟩ := hx
    refine ⟨fun i => r • c i, ?_⟩
    simp only [map_smul, hc, smul_mul_assoc, Finset.smul_sum]
  | mem _ hy =>
    obtain ⟨x, w, hw, hr, ha, _, rfl⟩ := hy
    let i : IntervalExit s t q p := ⟨w, hw, hr.trans hv, ha⟩
    refine ⟨fun j => if j = i then raw x else 0, ?_⟩
    rw [Finset.sum_eq_single i]
    · simp only [map_mul, i, ite_true]
    · intro j _ hj
      simp only [ite_eq_right hj, zero_mul]
    · exact fun h => (h (Finset.mem_univ i)).elim

/-- A relation among the interval exits lifts to the affine algebra with its original
coefficients after projection through the global violation. -/
theorem exists_intervalExitRelation_affine_lift (hQ : KLRSymm Q)
    (s t : Seq μ) {q p : Fin m} {a b : Fin ℓ} {L M : List (Fin ℓ)}
    (hq : s.lbl q = .inr a) (hp : s.lbl p = .inr b)
    (hs : redWord s = L ++ a :: b :: M) (ht : redWord t = L ++ b :: a :: M)
    (x : IntervalExit s t q p → ViolQuotient k Q Λ ν)
    (support : ∀ i, violMk k Q Λ ν (raw (e t)) * x i *
      violMk k Q Λ ν (raw (e (i.val • s))) = x i)
    (hzero : ∑ i, x i * violMk k Q Λ ν (raw (ψw (canWord m i.val) * e s)) = 0) :
    ∃ c : IntervalExit s t q p → B,
      (∀ i, violMk k Q Λ ν (raw (e t) * c i * raw (e (i.val • s))) = x i) ∧
      ∑ i, (raw (e t) * c i * raw (e (i.val • s))) *
        raw (ψw (canWord m i.val) * e s) = 0 := by
  have hw (i : IntervalExit s t q p) : wordProd m (canWord m i.val) • s = i.val • s := by
    rw [wordProd_canWord]
  have hc := exists_finiteExitRelation_affine_lift Q Λ s t
    (fun i : IntervalExit s t q p => canWord m i.val) hQ
    (intervalExit_generate Q Λ hQ s t hq hp hs ht) x
    (by simpa only [hw] using support) hzero
  simpa only [hw] using hc

end Categorification.Stendhal.BraidedStendhalAlgebra

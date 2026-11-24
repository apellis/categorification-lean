/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.InterleavedColumn

/-!
# Affine lifting for finite exit families

Webster, arXiv:1309.3796v2, §6.1, Proposition 6.4 and the cut after (6.21).
An exit family that generates every column of a given upper red order also generates
its globally violated part with violated coefficients. Consequently a relation among
the exits in the globally violated quotient admits affine coefficients with the exact
prescribed projections.
-/
noncomputable section
open scoped BigOperators
namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLRAlgebra TypeA Equiv
variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {ν : Multiset I}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) {ι : Type*}

local notation "μ" => stendhalWeight ℓ ν
local notation "A" => BraidedStendhalAlgebra k Q Λ ν
local notation "V" => ViolQuotient k Q Λ ν
local notation "raw" => ofKLR k Q Λ ν
local notation "mk" => violMk k Q Λ ν
local notation "p" => fun z : KLR.Seq μ => raw (e z)

variable (s t : KLR.Seq (stendhalWeight ℓ ν)) (words : ι → List ℕ)

local notation "q" => fun i : ι => ((wordProd (Multiset.card μ) (words i) • s) : KLR.Seq μ)
local notation "leg" => fun i : ι => raw (ψw (words i) * e s)

private theorem finite_exit_support (i : ι) :
    p (q i) * leg i = leg i ∧ leg i * p s = leg i := by
  constructor
  · rw [← map_mul, ← mul_assoc, e_mul_ψw, inv_smul_smul, mul_assoc, e_mul_self]
  · rw [← map_mul, mul_assoc, e_mul_self]

variable [Fintype ι]

/-- Generation only at globally violated intermediate loadings suffices to decompose
a globally violated element using globally violated coefficients. Webster v2, §6.1, Proposition 6.4 and the cut after (6.21). -/
theorem exists_violated_finite_exits_of_violated_generation (hQ : KLRSymm Q)
    (generate : ∀ v : KLR.Seq μ, IsViolated v → redWord v = redWord t → ∀ z : A,
      ∃ c : ι → A, p v * z * p s = ∑ i, c i * leg i)
    (z : A) (hz : mk z = 0) :
    ∃ c : ι → A, (∀ i, mk (c i) = 0) ∧ p t * z * p s = ∑ i, c i * leg i := by
  let choices : IsReducedChoice (canWord (Multiset.card μ)) := fun w =>
    ⟨isReduced_canWord _ w, wordProd_canWord _ w⟩
  have hv := redProj_mul_mem_violSpan choices hQ (redWord t) ((violMk_eq_zero_iff z).1 hz)
  suffices H : ∀ v ∈ violSpan k Q Λ ν (redWord t),
      ∃ c : ι → A, (∀ i, mk (c i) = 0) ∧ p t * v * p s = ∑ i, c i * leg i by
    have cut : p t * redProj k Q Λ ν (redWord t) = p t :=
      (e_mul_redProj _ _).trans (ite_eq_left rfl)
    simpa only [← mul_assoc, cut] using H _ hv
  intro v hv
  induction hv using Submodule.span_induction with
  | zero => exact ⟨fun _ => 0, fun _ => map_zero _, by simp⟩
  | add v w _ _ hv hw =>
    obtain ⟨c, hc, hvc⟩ := hv
    obtain ⟨d, hd, hwd⟩ := hw
    refine ⟨fun i => c i + d i, fun i => by rw [map_add, hc, hd, zero_add], ?_⟩
    rw [mul_add, add_mul, hvc, hwd, ← Finset.sum_add_distrib]
    simp only [add_mul]
  | smul r v _ hv =>
    obtain ⟨c, hc, hvc⟩ := hv
    refine ⟨fun i => r • c i, fun i => by rw [map_smul, hc, smul_zero], ?_⟩
    rw [mul_smul_comm, smul_mul_assoc, hvc, Finset.smul_sum]
    simp only [smul_mul_assoc]
  | mem v hv =>
    obtain ⟨u,i,d,hi,ho,rfl⟩ := hv
    obtain ⟨c,he⟩ := generate i hi ho d
    let g := p t * u * p i
    have hg : mk g = 0 := by simp only [g,map_mul,violMk_e hi,mul_zero]
    have hc : g * (p i * d * p s) = p t * (u * p i * d) * p s := by
      simp only [g,mul_assoc,← mul_assoc (p i) (p i),← map_mul raw,e_mul_self]
    refine ⟨fun i => g * c i, fun i => by rw [map_mul,hg,zero_mul], ?_⟩
    rw [← hc, he, Finset.mul_sum]
    simp only [mul_assoc]

/-- If a finite family of exit words generates the columns with the prescribed upper
red order, then it also generates their globally violated part with globally violated
coefficients. Webster v2, §6.1, Proposition 6.4 and the cut after (6.21). -/
theorem exists_violated_finite_exits (hQ : KLRSymm Q)
    (generate : ∀ v : KLR.Seq μ, redWord v = redWord t → ∀ z : A,
      ∃ c : ι → A, p v * z * p s = ∑ i, c i * leg i)
    (z : A) (hz : mk z = 0) :
    ∃ c : ι → A, (∀ i, mk (c i) = 0) ∧ p t * z * p s = ∑ i, c i * leg i :=
  exists_violated_finite_exits_of_violated_generation Q Λ s t words hQ
    (fun v _ => generate v) z hz

/-- A relation for a finite exit family in the globally violated quotient lifts with
its prescribed coefficients to a relation before quotienting. Thus every prescribed
higher mark remains on its exit coefficient. The family only needs to generate the affine columns at violated intermediate loadings. Webster v2, §6.1, after (6.21). -/
theorem exists_finiteExitRelation_affine_lift_of_violated_generation (hQ : KLRSymm Q)
    (generate : ∀ v : KLR.Seq μ, IsViolated v → redWord v = redWord t → ∀ z : A,
      ∃ c : ι → A, p v * z * p s = ∑ i, c i * leg i)
    (x : ι → V)
    (support : ∀ i, mk (p t) * x i * mk (p (q i)) = x i)
    (hzero : ∑ i, x i * mk (leg i) = 0) :
    ∃ c : ι → A, (∀ i, mk (p t * c i * p (q i)) = x i) ∧
      ∑ i, (p t * c i * p (q i)) * leg i = 0 := by
  classical
  choose a ha using fun i => violMk_surjective (x i)
  obtain ⟨b,hb,he⟩ := exists_violated_finite_exits_of_violated_generation Q Λ s t words hQ generate
    (∑ i, a i * leg i) (by simpa only [map_sum,map_mul,ha] using hzero)
  have right : (∑ i, a i * leg i) * p s = ∑ i, a i * leg i := by
    rw [Finset.sum_mul]
    simp only [mul_assoc, (finite_exit_support Q Λ s words _).2]
  have h : p t * (∑ i, a i * leg i) = ∑ i, b i * leg i := by
    rwa [mul_assoc, right] at he
  have idem : p t * p t = p t := by rw [← map_mul,e_mul_self]
  refine ⟨fun i => a i - b i, fun i => ?_, ?_⟩
  · simpa only [map_mul,map_sub,ha,hb,sub_zero] using support i
  · simp only [mul_assoc, (finite_exit_support Q Λ s words _).1]
    rw [← Finset.mul_sum]
    simp only [sub_mul]
    rw [Finset.sum_sub_distrib, ← h, mul_sub, ← mul_assoc, idem, sub_self]

/-- A relation for a finite exit family in the globally violated quotient lifts with
its prescribed coefficients to a relation before quotienting. Thus every prescribed
higher mark remains on its exit coefficient. The hypothesis on generation must be
proved separately for the family of exits. Webster v2, §6.1, after (6.21). -/
theorem exists_finiteExitRelation_affine_lift (hQ : KLRSymm Q)
    (generate : ∀ v : KLR.Seq μ, redWord v = redWord t → ∀ z : A,
      ∃ c : ι → A, p v * z * p s = ∑ i, c i * leg i)
    (x : ι → V)
    (support : ∀ i, mk (p t) * x i * mk (p (q i)) = x i)
    (hzero : ∑ i, x i * mk (leg i) = 0) :
    ∃ c : ι → A, (∀ i, mk (p t * c i * p (q i)) = x i) ∧
      ∑ i, (p t * c i * p (q i)) * leg i = 0 :=
  exists_finiteExitRelation_affine_lift_of_violated_generation Q Λ s t words hQ
    (fun v _ => generate v) x support hzero

end Categorification.Stendhal.BraidedStendhalAlgebra

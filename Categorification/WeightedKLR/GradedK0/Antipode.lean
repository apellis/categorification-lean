/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.GradedK0.Algebra
import Categorification.WeightedKLR.TensorSimple
import Mathlib.Data.Finsupp.Antidiagonal
import Mathlib.Data.Finsupp.Weight

/-!
# The antipode recursion on weighted projective classes

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4,
§2.4, Theorem 2.19, proof on p. 12. The printed formula applies the antipode
to the right tensorand but excludes a zero *right* weight. To isolate the
unknown in the right convolution equation, one must exclude a zero *left*
weight and apply induction multiplication to the resulting tensor. Separating
both endpoint terms gives `S(x) = -x - ∑ m(id ⊗ S) Δ_{a,b}(x)` in positive
weight, with `a,b ≠ 0` in the sum. In weight zero the map is the identity.

The recursion decreases the total number of strands. It uses the weighted
restriction coproduct and induction on every weight, including weights in which
the quantum-group map need not generate the Grothendieck group.
-/

noncomputable section

namespace Categorification.WeightedKLR

open Categorification.Graded
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [Field k] {Γ : WeightedGraph I 𝕜 k}

namespace GradingDatum

local notation "LP" => LaurentPolynomial ℤ

/-- Decompositions into two positive weights, indexing the reduced coproduct. -/
def properSplits (ν : I →₀ ℕ) : Finset ((I →₀ ℕ) × (I →₀ ℕ)) :=
  (Finset.HasAntidiagonal.antidiagonal ν).filter fun p => p.1 ≠ 0 ∧ p.2 ≠ 0

@[simp] theorem mem_properSplits {ν : I →₀ ℕ} {p : (I →₀ ℕ) × (I →₀ ℕ)} :
    p ∈ properSplits ν ↔ p.1 + p.2 = ν ∧ p.1 ≠ 0 ∧ p.2 ≠ 0 := by
  simp [properSplits]

/-- A proper split has strictly fewer strands in its right factor. -/
theorem properSplits_degree_right {ν : I →₀ ℕ} {p : (I →₀ ℕ) × (I →₀ ℕ)}
    (hp : p ∈ properSplits ν) : p.2.degree < ν.degree := by
  obtain ⟨he, h, _⟩ := mem_properSplits.mp hp
  rw [← he, map_add]
  exact Nat.lt_add_of_pos_left (Nat.pos_of_ne_zero fun hz => h ((Finsupp.degree_eq_zero_iff _).mp hz))

variable (G : GradingDatum Γ) (hD : Γ.Dagger) (hS : Γ.Standing)
  (hZ : Γ.NoZeroLoops) (hl : ∀ i, Γ.loop i = none)
  [∀ ν, HasGdim (G.klrGrade ν)]

/-- Restriction to the two factors of a particular weight decomposition,
followed by the two indicated endomorphisms and induction multiplication. -/
def convolutionTerm {a b ν : I →₀ ℕ} (h : a + b = ν)
    (f : Module.End LP (G.K0fam a)) (g : Module.End LP (G.K0fam b)) :
    Module.End LP (G.K0fam ν) := by
  subst ν
  exact G.indK0Tensor a b ∘ₗ TensorProduct.map f g ∘ₗ
    G.coproductK0 hD hZ hS a b (G.tensorK0Hyp hD hS hZ hl a b)

/-- Webster's antipode recursion, using only strictly smaller right weights in
the reduced coproduct (arXiv:1209.2463v4, §2.4, proof of Theorem 2.19, p. 12). -/
def antipodeComponent (ν : I →₀ ℕ) : Module.End LP (G.K0fam ν) :=
  if ν = 0 then LinearMap.id else
    -LinearMap.id - ∑ p ∈ (properSplits ν).attach,
      G.convolutionTerm hD hS hZ hl (mem_properSplits.mp p.property).1 LinearMap.id
        (antipodeComponent p.val.2)
termination_by ν.degree
decreasing_by exact properSplits_degree_right p.property

@[simp] theorem antipodeComponent_zero :
    G.antipodeComponent hD hS hZ hl 0 = LinearMap.id := by
  rw [antipodeComponent]
  simp

/-- The induction formula in positive weight (Webster, Theorem 2.19, p. 12,
with the endpoint and multiplication corrections documented above). -/
theorem antipodeComponent_of_ne {ν : I →₀ ℕ} (hν : ν ≠ 0) :
    G.antipodeComponent hD hS hZ hl ν = -LinearMap.id - ∑ p ∈ (properSplits ν).attach,
      G.convolutionTerm hD hS hZ hl (mem_properSplits.mp p.property).1 LinearMap.id
        (G.antipodeComponent hD hS hZ hl p.val.2) := by
  rw [antipodeComponent, ite_eq_right hν]

/-- The linear endomorphism of weighted graded `K₀` given by the corrected
recursion of Webster, arXiv:1209.2463v4, §2.4, proof of Theorem 2.19. -/
def antipodeK0 : Module.End LP G.K0W :=
  DirectSum.toModule LP _ _ fun ν =>
    DirectSum.lof LP _ G.K0fam ν ∘ₗ G.antipodeComponent hD hS hZ hl ν

theorem antipodeK0_of (ν : I →₀ ℕ) (x : G.K0fam ν) :
    G.antipodeK0 hD hS hZ hl (DirectSum.of G.K0fam ν x) =
      DirectSum.of G.K0fam ν (G.antipodeComponent hD hS hZ hl ν x) := by
  rw [antipodeK0, ← DirectSum.lof_eq_of LP, DirectSum.toModule_lof]
  rfl

/-- On the unit class the recursion fixes `[W₀]`. -/
@[simp] theorem antipodeK0_one : G.antipodeK0 hD hS hZ hl 1 = 1 := by
  rw [G.K0W_one, antipodeK0_of, antipodeComponent_zero, LinearMap.id_apply]

/-- Every one-strand class is negated. There is no proper decomposition of a
weight with one strand. -/
theorem antipodeComponent_of_degree_one {ν : I →₀ ℕ} (hν : ν.degree = 1) :
    G.antipodeComponent hD hS hZ hl ν = -LinearMap.id := by
  have hn : ν ≠ 0 := by rintro rfl; simp at hν
  have hempty : properSplits ν = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hlt := properSplits_degree_right hp
    have hz : p.2.degree = 0 := by omega
    exact (mem_properSplits.mp hp).2.2 ((Finsupp.degree_eq_zero_iff _).mp hz)
  rw [antipodeComponent_of_ne G hD hS hZ hl hn]
  rw [sub_eq_self]
  rw [Finset.attach_eq_empty_iff.mpr hempty, Finset.sum_empty]

end GradingDatum

end Categorification.WeightedKLR

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.GradedK0.Antipode
import Categorification.WeightedKLR.GradedK0.TotalCoproduct
import Categorification.WeightedKLR.GradedK0.CounitLaws
import Mathlib.RingTheory.Coalgebra.Convolution

/-!
# Convolution identities for the weighted antipode

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4,
§2.4, proof of Theorem 2.19, p. 12. Splitting off the endpoint restrictions
identifies the right convolution equation with the induction on the number of
strands. Convolution by the identity is injective by the same induction.
-/

noncomputable section

namespace Categorification.WeightedKLR.GradingDatum

open Categorification.Graded
open scoped TensorProduct
open Finset.HasAntidiagonal (antidiagonal mem_antidiagonal)

variable {I : Type*} [DecidableEq I]

private theorem sum_splits {M : Type*} [AddCommMonoid M] {ν : I →₀ ℕ} (hν : ν ≠ 0)
    (F : ∀ a b : I →₀ ℕ, a + b = ν → M) :
    ∑ p ∈ (antidiagonal ν).attach, F p.val.1 p.val.2 (mem_antidiagonal.mp p.property) =
      F 0 ν (zero_add ν) + (F ν 0 (add_zero ν) +
        ∑ p ∈ (properSplits ν).attach, F p.val.1 p.val.2 (mem_properSplits.mp p.property).1) := by
  classical
  let l : ↥(antidiagonal ν) := ⟨(0, ν), mem_antidiagonal.mpr (zero_add ν)⟩
  let r : ↥(antidiagonal ν) := ⟨(ν, 0), mem_antidiagonal.mpr (add_zero ν)⟩
  have hrl : r ≠ l := fun h => hν (congrArg (fun q : ↥(antidiagonal ν) => q.val.1) h)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_attach _ l),
    ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hrl, Finset.mem_attach _ r⟩)]
  congr 1
  congr 1
  symm
  refine Finset.sum_bij (fun p _ => ⟨p.val, mem_antidiagonal.mpr (mem_properSplits.mp p.2).1⟩)
    (fun p _ => ?_) (fun p _ q _ h => Subtype.ext (congrArg (fun z : ↥(antidiagonal ν) => z.val) h))
    (fun q hq => ?_) (fun _ _ => rfl)
  · obtain ⟨_, ha, hb⟩ := mem_properSplits.mp p.2
    exact Finset.mem_erase.mpr ⟨fun h => hb (congrArg (fun z : ↥(antidiagonal ν) => z.val.2) h),
      Finset.mem_erase.mpr ⟨fun h => ha (congrArg (fun z : ↥(antidiagonal ν) => z.val.1) h),
      Finset.mem_attach _ _⟩⟩
  · obtain ⟨hr, hq⟩ := Finset.mem_erase.mp hq
    obtain ⟨hl, _⟩ := Finset.mem_erase.mp hq
    have he := mem_antidiagonal.mp q.2
    have ha : q.val.1 ≠ 0 := fun h => hl (Subtype.ext (Prod.ext h (by simpa [h] using he)))
    have hb : q.val.2 ≠ 0 := fun h => hr (Subtype.ext (Prod.ext (by simpa [h] using he) h))
    exact ⟨⟨q.val, mem_properSplits.mpr ⟨he, ha, hb⟩⟩, Finset.mem_attach _ _, rfl⟩

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  {k : Type*} [Field k] {Γ : WeightedGraph I 𝕜 k}
  (G : GradingDatum Γ) (hD : Γ.Dagger) (hS : Γ.Standing)
  (hne : ∀ e, Γ.head e ≠ Γ.tail e) (hl : ∀ i, Γ.loop i = none)
  [∀ ν : I →₀ ℕ, HasGdim (G.klrGrade ν)]

local notation "L" => LaurentPolynomial ℤ
local notation "ι" => DirectSum.lof L _ G.K0fam
local notation "Δ" => G.totalCoproduct hD hS hne hl
local notation "Δs" => G.splitCoproduct hD hS hne hl
local notation "S" => G.antipodeK0 hD hS hne hl

private def rightTerm (F : Module.End L G.K0W) (a b : I →₀ ℕ) :
    G.K0fam a ⊗[L] G.K0fam b →ₗ[L] G.K0W :=
  LinearMap.mul' L G.K0W ∘ₗ TensorProduct.map (ι a) (F ∘ₗ ι b)

omit [∀ ν : I →₀ ℕ, HasGdim (G.klrGrade ν)] in
private theorem rightTerm_tmul (F : Module.End L G.K0W) (a b : I →₀ ℕ)
    (x : G.K0fam a) (y : G.K0fam b) :
    G.rightTerm F a b (x ⊗ₜ y) = ι a x * F (ι b y) := rfl

private theorem rightTerm_antipode {a b ν : I →₀ ℕ} (h : a + b = ν) (x : G.K0fam ν) :
    G.rightTerm S a b (Δs a b h x) = ι ν (G.convolutionTerm hD hS hne hl h LinearMap.id
      (G.antipodeComponent hD hS hne hl b) x) := by
  subst ν
  let z := Δs a b rfl x
  change G.rightTerm S a b z =
    ι (a + b) (G.indK0Tensor a b (TensorProduct.map LinearMap.id
      (G.antipodeComponent hD hS hne hl b) z))
  induction z using TensorProduct.inductionOn with
  | tmul u v =>
    rw [rightTerm_tmul, TensorProduct.map_tmul, G.indK0Tensor_tmul]
    change DirectSum.of G.K0fam a u * S (DirectSum.of G.K0fam b v) = _
    rw [antipodeK0_of, G.K0W_of_mul_of]
    rfl
  | add u v hu hv => simp only [map_add, hu, hv]

private theorem mul_rTensor_total (F : Module.End L G.K0W) (ν : I →₀ ℕ) (x : G.K0fam ν) :
    LinearMap.mul' L G.K0W (F.lTensor G.K0W (Δ (ι ν x))) =
      ∑ p ∈ (antidiagonal ν).attach,
        G.rightTerm F p.val.1 p.val.2 (Δs _ _ (mem_antidiagonal.mp p.property) x) := by
  rw [totalCoproduct_lof, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro p _
  let z := Δs p.val.1 p.val.2 (mem_antidiagonal.mp p.property) x
  change LinearMap.mul' L G.K0W
    (F.lTensor G.K0W (TensorProduct.map (ι p.val.1) (ι p.val.2) z)) = G.rightTerm F _ _ z
  induction z using TensorProduct.inductionOn with
  | tmul u v => rfl
  | add u v hu hv => simp only [map_add, hu, hv]

private theorem mul_lTensor_total_zero (F : Module.End L G.K0W) (x : G.K0fam 0) :
    LinearMap.mul' L G.K0W (F.lTensor G.K0W (Δ (ι 0 x))) = F (ι 0 x) := by
  rw [mul_rTensor_total]
  let zz : ↥(antidiagonal (0 : I →₀ ℕ)) := ⟨(0, 0), mem_antidiagonal.mpr (zero_add 0)⟩
  rw [Finset.sum_eq_single zz]
  · change G.rightTerm F 0 0 (Δs 0 0 _ x) = _
    rw [G.splitCoproduct_zero_left, rightTerm_tmul]
    exact one_mul _
  · intro p _ hp
    have he := add_eq_zero.mp (mem_antidiagonal.mp p.property)
    exact (hp (Subtype.ext (Prod.ext he.1 he.2))).elim
  · exact fun h => (h (Finset.mem_attach _ zz)).elim

private theorem mul_lTensor_total_ne (F : Module.End L G.K0W) {ν : I →₀ ℕ} (hn : ν ≠ 0)
    (x : G.K0fam ν) :
    LinearMap.mul' L G.K0W (F.lTensor G.K0W (Δ (ι ν x))) =
      F (ι ν x) + (ι ν x * F 1 + ∑ p ∈ (properSplits ν).attach,
        G.rightTerm F p.val.1 p.val.2 (Δs _ _ (mem_properSplits.mp p.property).1 x)) := by
  rw [mul_rTensor_total, sum_splits hn (fun a b h => G.rightTerm F a b (Δs a b h x)),
    G.splitCoproduct_zero_left, G.splitCoproduct_zero_right, rightTerm_tmul, rightTerm_tmul]
  change 1 * _ + _ = _
  rw [one_mul]
  rfl

private theorem mul_lTensor_antipode_ne {ν : I →₀ ℕ} (hn : ν ≠ 0) (x : G.K0fam ν) :
    LinearMap.mul' L G.K0W ((S).lTensor G.K0W (Δ (ι ν x))) = 0 := by
  rw [mul_lTensor_total_ne G hD hS hne hl S hn, G.antipodeK0_one, mul_one]
  simp_rw [rightTerm_antipode]
  rw [show S (ι ν x) = ι ν (G.antipodeComponent hD hS hne hl ν x) from
    G.antipodeK0_of hD hS hne hl ν x, antipodeComponent_of_ne G hD hS hne hl hn]
  simp only [LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.id_apply, LinearMap.sum_apply,
    map_sub, map_neg, map_sum]
  abel

omit [∀ ν : I →₀ ℕ, HasGdim (G.klrGrade ν)] in
private theorem rightTerm_zero_of (F : Module.End L G.K0W) (a b : I →₀ ℕ)
    (hb : ∀ y : G.K0fam b, F (ι b y) = 0) (z : G.K0fam a ⊗[L] G.K0fam b) :
    G.rightTerm F a b z = 0 := by
  induction z using TensorProduct.inductionOn with
  | tmul u v => rw [rightTerm_tmul, hb, mul_zero]
  | add u v hu hv => rw [map_add, hu, hv, add_zero]

private theorem eq_zero_of_mul_lTensor_total (F : Module.End L G.K0W)
    (hf : LinearMap.mul' L G.K0W ∘ₗ F.lTensor G.K0W ∘ₗ Δ = 0) : F = 0 := by
  have hv (ν : I →₀ ℕ) (x : G.K0fam ν) :
      LinearMap.mul' L G.K0W (F.lTensor G.K0W (Δ (ι ν x))) = 0 :=
    LinearMap.congr_fun hf (ι ν x)
  have hzero (x : G.K0fam 0) : F (ι 0 x) = 0 :=
    (G.mul_lTensor_total_zero hD hS hne hl F x).symm.trans (hv 0 x)
  have hone : F 1 = 0 := hzero G.K0one
  have allWeights : ∀ n (ν : I →₀ ℕ), ν.degree = n → ∀ x : G.K0fam ν, F (ι ν x) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro ν hdeg x
      by_cases hn : ν = 0
      · subst ν
        exact hzero x
      · have h := hv ν x
        rw [G.mul_lTensor_total_ne hD hS hne hl F hn, hone, mul_zero, zero_add] at h
        have hz : ∀ p : ↥(properSplits ν), G.rightTerm F p.val.1 p.val.2
            (Δs _ _ (mem_properSplits.mp p.property).1 x) = 0 := by
          intro p
          apply G.rightTerm_zero_of
          apply ih _ _ _ rfl
          exact (properSplits_degree_right p.property).trans_eq hdeg
        simpa only [Finset.sum_eq_zero fun p _ => hz p, add_zero] using h
  apply DirectSum.linearMap_ext
  intro ν
  apply LinearMap.ext
  intro x
  exact allWeights _ ν rfl x

/-- The right convolution identity for the corrected antipode of Webster's
Theorem 2.19. The finite recursion supplies the cancellation in every positive
weight, while weight zero identifies with the Laurent polynomial ring. -/
theorem antipodeK0_right :
    LinearMap.mul' L G.K0W ∘ₗ (S).lTensor G.K0W ∘ₗ Δ = Algebra.linearMap L G.K0W ∘ₗ G.counitK0 := by
  apply DirectSum.linearMap_ext
  intro ν
  apply LinearMap.ext
  intro x
  change LinearMap.mul' L G.K0W ((S).lTensor G.K0W (Δ (ι ν x))) =
    algebraMap L G.K0W (G.counitK0 (DirectSum.of G.K0fam ν x))
  by_cases hn : ν = 0
  · subst ν
    rw [G.mul_lTensor_total_zero hD hS hne hl, G.counitK0_of_zero]
    change S (DirectSum.of G.K0fam 0 x) = _
    rw [antipodeK0_of, antipodeComponent_zero, LinearMap.id_apply, K0W_of_zero_eq_algebraMap]
  · rw [G.mul_lTensor_antipode_ne hD hS hne hl hn, G.counitK0_of_ne hn, map_zero]

/-- The left convolution identity follows from the right one in the convolution
ring. This intermediate statement takes the coalgebra laws through the given
instance and identifies its two structure maps with weighted restriction and
the weight-zero counit. -/
theorem antipodeK0_left_of_coalgebra [Coalgebra L G.K0W]
    (hd : Coalgebra.comul (R := L) (A := G.K0W) = Δ)
    (hcounit : Coalgebra.counit (R := L) (A := G.K0W) = G.counitK0) :
    LinearMap.mul' L G.K0W ∘ₗ (S).rTensor G.K0W ∘ₗ Δ =
      Algebra.linearMap L G.K0W ∘ₗ Coalgebra.counit := by
  let e : WithConv (Module.End L G.K0W) := WithConv.toConv LinearMap.id
  let t : WithConv (Module.End L G.K0W) := WithConv.toConv S
  have het : e * t = 1 := by
    apply WithConv.ext
    change LinearMap.mul' L G.K0W ∘ₗ (S).lTensor G.K0W ∘ₗ Coalgebra.comul = _
    rw [hd]
    change _ = Algebra.linearMap L G.K0W ∘ₗ Coalgebra.counit
    rw [hcounit, G.antipodeK0_right hD hS hne hl]
  have hv : e * (t * e - 1) = 0 := calc
    _ = e * (t * e) - e * 1 := mul_sub e (t * e) 1
    _ = (e * t) * e - e := by rw [mul_assoc e t e, mul_one e]
    _ = 0 := by rw [het, one_mul e, sub_self e]
  have hc : (t * e - 1).ofConv = 0 := by
    apply G.eq_zero_of_mul_lTensor_total hD hS hne hl
    rw [← hd]
    exact congrArg WithConv.ofConv hv
  have hte : t * e = 1 := sub_eq_zero.mp (WithConv.ext hc)
  rw [← hd]
  exact congrArg WithConv.ofConv hte

end Categorification.WeightedKLR.GradingDatum

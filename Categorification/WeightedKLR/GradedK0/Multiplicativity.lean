/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.GradedK0.MackeyMultiplication

/-!
# Multiplicativity of the total restriction coproduct

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4,
§2.4, Theorem 2.19. Summing the graded Mackey formula over output weights
gives the braided multiplication rule for the coproduct on the direct sum.
-/

noncomputable section

namespace Categorification.WeightedKLR

open Juxtapose Categorification.Graded
open scoped TensorProduct

variable {I : Type*} [DecidableEq I]

private abbrev WeightSplit (ν : I →₀ ℕ) := ↥(Finset.HasAntidiagonal.antidiagonal ν)

private theorem WeightSplit.sum_eq {ν : I →₀ ℕ} (s : WeightSplit ν) : s.1.1 + s.1.2 = ν :=
  Finset.HasAntidiagonal.mem_antidiagonal.mp s.2

private def weightSplit (a b : I →₀ ℕ) {ν : I →₀ ℕ} (h : a + b = ν) : WeightSplit ν :=
  ⟨(a, b), Finset.HasAntidiagonal.mem_antidiagonal.mpr h⟩

private theorem shuffleType_mem_of_layout {μ ν p q : I →₀ ℕ} (l : ShuffleLayout μ ν p q) :
    ⇑l.c ∈ Set.range (shuffleType (ν := μ + ν) μ p) := by
  rcases l with ⟨a, b, c, d, rfl, rfl, rfl, rfl⟩
  exact ⟨middleSwap a b c d, shuffleType_middleSwap⟩

private def layoutInputs {μ ν p q : I →₀ ℕ} (l : ShuffleLayout μ ν p q) :
    WeightSplit μ × WeightSplit ν :=
  (weightSplit l.a l.b l.hab, weightSplit l.c l.d l.hcd)

private theorem layoutInputs_bijective {μ ν : I →₀ ℕ} (n : WeightSplit (μ + ν) → ℕ)
    (l : (s : WeightSplit (μ + ν)) → Fin (n s) → ShuffleLayout μ ν s.1.1 s.1.2)
    (hi : ∀ s, Function.Injective (fun i => ⇑(l s i).c))
    (hr : ∀ s, Set.range (fun i => ⇑(l s i).c) = Set.range (shuffleType (ν := μ + ν) μ s.1.1)) :
    Function.Bijective (fun t : (s : WeightSplit (μ + ν)) × Fin (n s) =>
      layoutInputs (l t.1 t.2)) := by
  constructor
  · rintro ⟨s,i⟩ ⟨t,j⟩ h
    have ha := congrArg (fun u : WeightSplit μ × WeightSplit ν => u.1.1.1) h
    have hb := congrArg (fun u : WeightSplit μ × WeightSplit ν => u.1.1.2) h
    have hc := congrArg (fun u : WeightSplit μ × WeightSplit ν => u.2.1.1) h
    have hd := congrArg (fun u : WeightSplit μ × WeightSplit ν => u.2.1.2) h
    change (l s i).a = (l t j).a at ha
    change (l s i).b = (l t j).b at hb
    change (l s i).c = (l t j).c at hc
    change (l s i).d = (l t j).d at hd
    have hst : s = t := Subtype.ext <| Prod.ext
      ((l s i).hac.symm.trans ((congrArg₂ (· + ·) ha hc).trans (l t j).hac))
      ((l s i).hbd.symm.trans ((congrArg₂ (· + ·) hb hd).trans (l t j).hbd))
    subst t
    exact congrArg (Sigma.mk s) (hi s (congrArg DFunLike.coe hc))
  · rintro ⟨u,v⟩
    let s := weightSplit (u.1.1 + v.1.1) (u.1.2 + v.1.2)
      (by rw [add_add_add_comm, u.sum_eq, v.sum_eq])
    let t : ShuffleLayout μ ν s.1.1 s.1.2 :=
      ⟨u.1.1, u.1.2, v.1.1, v.1.2, u.sum_eq, v.sum_eq, rfl, rfl⟩
    obtain ⟨i, he⟩ := (hr s).symm ▸ shuffleType_mem_of_layout t
    have hc : (l s i).c = v.1.1 := DFunLike.coe_injective he
    have ha : (l s i).a = u.1.1 := add_right_cancel <| by
      simpa only [hc] using (show (l s i).a + (l s i).c = u.1.1 + v.1.1 from (l s i).hac)
    have hb : (l s i).b = u.1.2 := add_left_cancel <| by
      simpa only [ha] using (l s i).hab.trans u.sum_eq.symm
    have hd : (l s i).d = v.1.2 := add_left_cancel <| by
      simpa only [hc] using (l s i).hcd.trans v.sum_eq.symm
    exact ⟨⟨s, i⟩, Prod.ext (Subtype.ext (Prod.ext ha hb)) (Subtype.ext (Prod.ext hc hd))⟩

namespace GradingDatum

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  {k : Type*} [Field k] {Γ : WeightedGraph I 𝕜 k} (G : GradingDatum Γ)
  (hD : Γ.Dagger) (hS : Γ.Standing)
  (hZ : Γ.NoZeroLoops) (hl : ∀ i, Γ.loop i = none)
  [∀ ν : I →₀ ℕ, HasGdim (G.klrGrade ν)]

local notation "L" => LaurentPolynomial ℤ
local notation "Δ" => G.totalCoproduct hD hS hZ hl
local notation "δ" => G.splitCoproduct hD hS hZ hl

private def splitTerm {ν : I →₀ ℕ} (x : G.K0fam ν) (s : WeightSplit ν) :
    G.K0W ⊗[L] G.K0W :=
  G.tensorLof s.1.1 s.1.2 (δ s.1.1 s.1.2 s.sum_eq x)

local notation "R" => G.splitTerm hD hS hZ hl

private theorem totalCoproduct_of_eq_sum {ν : I →₀ ℕ} (x : G.K0fam ν) :
    Δ (DirectSum.of G.K0fam ν x) = ∑ s : WeightSplit ν, R x s :=
  G.totalCoproduct_lof hD hS hZ hl ν x

private theorem splitCoproduct_eq_cast {μ a b : I →₀ ℕ} (h : a + b = μ) (x : G.K0fam μ) :
    δ a b h x = G.coproductK0 hD hZ hS a b
      (G.tensorK0Hyp hD hS hZ hl a b)
      (K0.map (castW k Γ h).symm (fun _ _ hx => G.castW_mem_klrGrade h hx) x) := by
  subst μ
  unfold splitCoproduct
  congr 1
  exact (G.map_castW_rfl x).symm

private theorem splitCoproduct_eq_cast_symm {μ a b : I →₀ ℕ} (h : a + b = μ) (x : G.K0fam μ) :
    δ a b h x = G.coproductK0 hD hZ hS a b
      (G.tensorK0Hyp hD hS hZ hl a b)
      (K0.map (castW k Γ h.symm) (fun _ _ hx => G.castW_symm_mem_klrGrade h.symm hx) x) := by
  subst μ
  exact G.splitCoproduct_eq_cast hD hS hZ hl rfl x

private theorem exists_splitTerm_indK0 {μ ν : I →₀ ℕ} (s : WeightSplit (μ + ν))
    (x : G.K0fam μ) (y : G.K0fam ν) :
    ∃ (n : ℕ) (l : Fin n → ShuffleLayout μ ν s.1.1 s.1.2),
      Function.Injective (fun i => ⇑(l i).c) ∧
      Set.range (fun i => ⇑(l i).c) = Set.range (shuffleType (ν := μ + ν) μ s.1.1) ∧
      R (G.indK0 μ ν x y) s =
        ∑ i, G.twMul (R x (layoutInputs (l i)).1) (R y (layoutInputs (l i)).2) := by
  classical
  obtain ⟨n, l, hi, hr, h⟩ :=
    exists_coproductK0_indK0_eq_sum_graded G hD hS hZ hl s.sum_eq
  refine ⟨n, l, hi, hr, ?_⟩
  unfold splitTerm
  rw [splitCoproduct_eq_cast_symm, h x y, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  change _ = G.twMul
    (G.tensorLof (l i).a (l i).b (δ _ _ (l i).hab x))
    (G.tensorLof (l i).c (l i).d (δ _ _ (l i).hcd y))
  rw [twMul_tensorLof, splitCoproduct_eq_cast, splitCoproduct_eq_cast]

private theorem totalCoproduct_of_mul_of {μ ν : I →₀ ℕ} (x : G.K0fam μ) (y : G.K0fam ν) :
    Δ (DirectSum.of G.K0fam μ x * DirectSum.of G.K0fam ν y) =
      G.twMul (Δ (DirectSum.of G.K0fam μ x)) (Δ (DirectSum.of G.K0fam ν y)) := by
  classical
  choose n l hi hr h using fun s : WeightSplit (μ + ν) =>
    G.exists_splitTerm_indK0 hD hS hZ hl s x y
  let f (p : WeightSplit μ × WeightSplit ν) := G.twMul (R x p.1) (R y p.2)
  have reindex := (layoutInputs_bijective n l hi hr).sum_comp f
  rw [Fintype.sum_sigma, Fintype.sum_prod_type] at reindex
  simp only [K0W_of_mul_of, totalCoproduct_of_eq_sum, h, map_sum, LinearMap.sum_apply]
  exact reindex.trans Finset.sum_comm

/-- The restriction coproduct is multiplicative for the twisted product on the
tensor square (Webster, arXiv:1209.2463v4, §2.4, Theorem 2.19). -/
theorem totalCoproduct_mul (x y : G.K0W) :
    Δ (x * y) = G.twMul (Δ x) (Δ y) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [add_mul, map_add, LinearMap.add_apply, hx, hx']
  | of μ x =>
    induction y using DirectSum.induction_on with
    | zero => simp
    | add y y' hy hy' => simp only [mul_add, map_add, hy, hy']
    | of ν y => exact G.totalCoproduct_of_mul_of hD hS hZ hl x y

end GradingDatum
end Categorification.WeightedKLR

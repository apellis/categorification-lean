/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqBubbles
import Categorification.TwoRep.ModelSl2Curls

/-!
# Actual fake bubbles in the Rouquier interpretation

The unchanged recursive CL bubbles map to the local Rouquier bubbles for every integer
label. Positive coefficients of the two Grassmannian series are inverse; the unused
zeroth coefficient of the defining sequence need not be replaced. This treats real labels,
formal negative labels, the identity coefficient, and labels below the degree bound.
Actual clockwise diagrams correspond to local `ccw`, and conversely, at the same outer
weight. No scalar normalization is needed for these comparisons.

Cautis–Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, §2.6 (fake bubbles). Used by both actual curl consumers in `RouqCurls`.
-/

noncomputable section
namespace Categorification.TwoRep
open CategoryTheory CategoryTheory.Bicategory
open QuantumGroup UDot KL3.Diagram StringDiagrams Diagrams.BicatInterp
universe w v u u₁
namespace RouqLoc
variable {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [AdditiveWhiskering B]
  {a b c : B} {E₁ : a ⟶ b} {R₁ : b ⟶ a} {E₂ : b ⟶ c} {R₂ : c ⟶ b}
  {adj₁ : E₁ ⊣ R₁} {adj₂ : E₂ ⊣ R₂} {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂}
  {τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂} {h : ℤ} (L : RouqLoc adj₁ adj₂ x₁ x₂ τ h)

omit [AdditiveWhiskering B] in
private theorem ccw_below {j : ℤ} (hj : j < h - 1) : L.ccw j = 0 := by
  by_cases hh : 0 < h
  · exact L.ccw_of_lt hh hj
  · exact L.ccw_of_neg_of_lt (by omega) hj
omit [AdditiveWhiskering B] in
private theorem cw_below {j : ℤ} (hj : j < -h - 1) : L.cw j = 0 := by
  by_cases hh : h < 0
  · exact L.cw_of_lt hh hj
  · exact L.cw_of_neg_of_lt (by omega) hj
omit [AdditiveWhiskering B] in
private theorem ccw_boundary : L.ccw (h - 1) = 𝟙 _ := by
  by_cases hh : 0 < h
  · exact L.ccw_self hh
  · exact L.ccw_of_neg_of_eq (by omega) rfl
omit [AdditiveWhiskering B] in
private theorem cw_boundary : L.cw (-h - 1) = 𝟙 _ := by
  by_cases hh : h < 0
  · exact L.cw_self hh
  · exact L.cw_of_neg_of_eq (by omega) rfl

private theorem grass_coeff (n : ℕ) :
    ∑ j ∈ Finset.range (n + 2), L.ccw (h - 1 + j) ≫
      L.cw (-h - 1 + (n + 1 : ℕ) - j) = 0 := by
  have hg := L.infGrass n (min h 0 - 1) (n + h.natAbs + 3) (by omega) (by
    have : h ≤ (h.natAbs : ℤ) := Int.le_natAbs
    have : -h ≤ (h.natAbs : ℤ) := by simpa only [Int.natCast_natAbs] using (neg_le_abs h)
    omega)
  have hw := sum_range_window
    (fun r : ℤ => L.ccw r ≫ L.cw ((n : ℤ) - 1 - r))
    (lo := min h 0 - 1) (K := n + h.natAbs + 3) (lo' := h - 1) (K' := n + 2)
    (by
      intro r hr
      rcases hr with hr | hr
      · rw [L.ccw_below hr, Limits.zero_comp]
      · rw [L.cw_below (by omega), Limits.comp_zero])
    (by omega) (by
      have : h ≤ (h.natAbs : ℤ) := Int.le_natAbs
      have : -h ≤ (h.natAbs : ℤ) := by simpa only [Int.natCast_natAbs] using (neg_le_abs h)
      omega)
  rw [hw] at hg
  convert hg using 2 with j
  congr 2
  omega

private theorem cw_grassInv (n : ℕ) :
    L.cw (-h - 1 + n) =
      Categorification.TwoRep.grassInv (A := End (𝟙 b)) (fun a : ℕ => L.ccw (h - 1 + a)) n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero =>
      rw [Nat.cast_zero, add_zero, Categorification.TwoRep.grassInv_zero]
      exact L.cw_boundary
    | succ n =>
      rw [Categorification.TwoRep.grassInv_succ]
      have hg := L.grass_coeff n
      rw [Finset.sum_range_succ'] at hg
      simp only [Nat.cast_zero, add_zero, sub_zero, L.ccw_boundary, Category.id_comp] at hg
      apply eq_neg_iff_add_eq_zero.mpr
      rw [add_comm]
      convert hg using 1
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [← ih (n - j) (by omega)]
      change L.cw (-h - 1 + (n - j : ℕ)) ≫ L.ccw (h - 1 + (j + 1 : ℕ)) = _
      rw [Bicategory.endId_comm]
      congr 2
      omega
private theorem grass_coeff_rev (n : ℕ) :
    ∑ j ∈ Finset.range (n + 2), L.cw (-h - 1 + j) ≫
      L.ccw (h - 1 + (n + 1 : ℕ) - j) = 0 := by
  have hg := L.grass_coeff n
  rw [← Finset.sum_range_reflect] at hg
  convert hg using 1
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  rw [Bicategory.endId_comm]
  congr 2 <;> omega

private theorem ccw_grassInv (n : ℕ) :
    L.ccw (h - 1 + n) =
      Categorification.TwoRep.grassInv (A := End (𝟙 b)) (fun a : ℕ => L.cw (-h - 1 + a)) n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero =>
      rw [Nat.cast_zero, add_zero, Categorification.TwoRep.grassInv_zero]
      exact L.ccw_boundary
    | succ n =>
      rw [Categorification.TwoRep.grassInv_succ]
      have hg := L.grass_coeff_rev n
      rw [Finset.sum_range_succ'] at hg
      simp only [Nat.cast_zero, add_zero, sub_zero, L.cw_boundary, Category.id_comp] at hg
      apply eq_neg_iff_add_eq_zero.mpr
      rw [add_comm]
      convert hg using 1
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [← ih (n - j) (by omega)]
      change L.ccw (h - 1 + (n - j : ℕ)) ≫ L.cw (-h - 1 + (j + 1 : ℕ)) = _
      rw [Bicategory.endId_comm]
      congr 2
      omega
end RouqLoc

variable {k : Type*} [CommRing k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [AdditiveWhiskering B]
  {I : Type*} {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y}
namespace RouqFamily
variable (S : RouqFamily (B := B) RD) (Sc : CL.CLScalars C k)
attribute [local irreducible] KL3.Diagram.sh

/-- The original linear interpretation on endomorphisms of the empty word. -/
def bubbleHom (μ : X) : LEnd RD k (ob RD μ []) →+* End (𝟙 (S.obj μ)) where
  toFun := admissibleMap (S.genImg Sc) (bubbleNil μ).property (bubbleNil μ).property
  map_one' := by
    change admissibleMap (S.genImg Sc) _ _ (LinDiagram.of (𝟙 _)) = _
    erw [admissibleMap_of]
    exact (S.interp Sc μ μ).map_id (bubbleNil μ)
  map_mul' f g := by
    exact admissibleMap_comp (S.genImg Sc) (bubbleNil μ).property
      (bubbleNil μ).property (bubbleNil μ).property g f
  map_zero' := map_zero _
  map_add' := map_add _

private theorem bubble_cwReal_at (i : I) {a b c : X}
    (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX i = c) (n : ℕ) :
    S.bubbleHom Sc b (LinDiagram.of (cwReal RD b i n)) = (S.loc i h₁ h₂).ccw n := by
  obtain rfl : a = sh RD (dn i) + b := by rw [sh_dn]; exact (eq_sub_iff_add_eq.mpr h₁).trans (sub_eq_neg_add b _)
  subst c
  change admissibleMap (S.genImg Sc) _ _ (LinDiagram.of _) = _
  erw [admissibleMap_of, bubble_cwReal]

private theorem bubble_ccwReal_at (i : I) {a b c : X}
    (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX i = c) (n : ℕ) :
    S.bubbleHom Sc b (LinDiagram.of (ccwReal RD b i n)) = (S.loc i h₁ h₂).cw n := by
  obtain rfl : a = b - RD.iX i := eq_sub_iff_add_eq.mpr h₁
  obtain rfl : c = sh RD (up i) + b := by rw [sh_up]; exact h₂.symm.trans (add_comm _ _)
  change admissibleMap (S.genImg Sc) _ _ (LinDiagram.of _) = _
  erw [admissibleMap_of, bubble_ccwReal]

/-- Every actual clockwise CL bubble, including fake labels, is the local `ccw`. -/
theorem bubble_cwL (i : I) {a b c : X}
    (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX i = c) (m : ℤ) :
    S.bubbleHom Sc b (KL3.Diagram.cwL RD k b i m) = (S.loc i h₁ h₂).ccw m := by
  unfold KL3.Diagram.cwL
  split_ifs with hm hd
  · rw [S.bubble_cwReal_at Sc i h₁ h₂, Int.toNat_of_nonneg hm]
  · rw [StrongSl2.map_grassInv]
    have he : m = RD.pair (RD.iY i) b - 1 + (m + 1 - ip RD i b).toNat := by
      change 0 ≤ m + 1 - RD.pair (RD.iY i) b at hd
      change m = RD.pair (RD.iY i) b - 1 + (m + 1 - RD.pair (RD.iY i) b).toNat
      omega
    conv_rhs => rw [he, (S.loc i h₁ h₂).ccw_grassInv]
    apply congrFun (Categorification.TwoRep.grassInv_congr ?_)
    intro j hj
    unfold KL3.Diagram.ccwR
    have hj0 : 0 ≤ -ip RD i b - 1 + (j : ℤ) := by omega
    rw [ite_eq_left hj0, S.bubble_ccwReal_at Sc i h₁ h₂, Int.toNat_of_nonneg hj0]
  · rw [map_zero]
    symm
    apply RouqLoc.ccw_below
    change ¬0 ≤ m + 1 - RD.pair (RD.iY i) b at hd
    omega

/-- Every actual counterclockwise CL bubble, including fake labels, is the local `cw`. -/
theorem bubble_ccwL (i : I) {a b c : X}
    (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX i = c) (m : ℤ) :
    S.bubbleHom Sc b (KL3.Diagram.ccwL RD k b i m) = (S.loc i h₁ h₂).cw m := by
  unfold KL3.Diagram.ccwL
  split_ifs with hm hd
  · rw [S.bubble_ccwReal_at Sc i h₁ h₂, Int.toNat_of_nonneg hm]
  · rw [StrongSl2.map_grassInv]
    have he : m = -RD.pair (RD.iY i) b - 1 + (m + 1 + ip RD i b).toNat := by
      change 0 ≤ m + 1 + RD.pair (RD.iY i) b at hd
      change m = -RD.pair (RD.iY i) b - 1 + (m + 1 + RD.pair (RD.iY i) b).toNat
      omega
    conv_rhs => rw [he, (S.loc i h₁ h₂).cw_grassInv]
    apply congrFun (Categorification.TwoRep.grassInv_congr ?_)
    intro j hj
    unfold KL3.Diagram.cwR
    have hj0 : 0 ≤ ip RD i b - 1 + (j : ℤ) := by omega
    rw [ite_eq_left hj0, S.bubble_cwReal_at Sc i h₁ h₂, Int.toNat_of_nonneg hj0]
  · rw [map_zero]
    symm
    apply RouqLoc.cw_below
    change ¬0 ≤ m + 1 + RD.pair (RD.iY i) b at hd
    omega

end RouqFamily
end Categorification.TwoRep

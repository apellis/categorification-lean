/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.Grassmannian
import Categorification.Diagrams.KL3.MoreBubbleSlides

/-!
# Bubble slides in all degrees (fake bubbles included)

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.1.2,
Propositions 3.3 and 3.4.

The bubble slides of `BubbleSlidesProp` and `MoreBubbleSlides` are proved there when the bubble
on the left-hand side is a real bubble. Here they are extended to all degrees (the bubble on the
left-hand side may be a fake bubble), using the infinite Grassmannian relation in all degrees
(`grassmannian`): the counterclockwise and clockwise bubbles on either side of a strand are
mutually inverse power series, and a slide identity for one family in all degrees implies the
slide identity for the inverse family (`transfer_left`, `transfer_right`). In each case one of the
two families consists of real bubbles in all positive degrees.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

/-! ## Convolution of sequences -/

section Conv

variable {A : Type*} [Ring A]

/-- The convolution `(u ⋆ w)_d = ∑_{a ≤ d} u_a w_{d-a}` (coefficients of a product of power
series). -/
def sconv (u w : ℕ → A) (d : ℕ) : A := ∑ a ∈ Finset.range (d + 1), u a * w (d - a)

theorem sconv_eq_coeff (u w : ℕ → A) (d : ℕ) :
    sconv u w d = PowerSeries.coeff A d (PowerSeries.mk u * PowerSeries.mk w) := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => PowerSeries.coeff A a (PowerSeries.mk u) * PowerSeries.coeff A b (PowerSeries.mk w))]
  simp [sconv]

theorem mk_sconv (u w : ℕ → A) :
    PowerSeries.mk (sconv u w) = PowerSeries.mk u * PowerSeries.mk w := by
  ext d; rw [PowerSeries.coeff_mk, sconv_eq_coeff]

theorem sconv_assoc (u τ w : ℕ → A) (d : ℕ) : sconv (sconv u τ) w d = sconv u (sconv τ w) d := by
  rw [sconv_eq_coeff, sconv_eq_coeff, mk_sconv, mk_sconv, mul_assoc]

/-- A left inverse series of a series with constant term `1` is unique. -/
theorem inv_unique_left (w X Y : ℕ → A) (hw : w 0 = 1)
    (hX : ∀ d, sconv X w d = if d = 0 then 1 else 0) (hY : ∀ d, sconv Y w d = if d = 0 then 1 else 0) :
    ∀ d, X d = Y d := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    have e₁ := hX d
    have e₂ := hY d
    rw [sconv, Finset.sum_range_succ, Nat.sub_self, hw, mul_one] at e₁ e₂
    have : ∑ a ∈ Finset.range d, X a * w (d - a) = ∑ a ∈ Finset.range d, Y a * w (d - a) :=
      Finset.sum_congr rfl fun a ha => by rw [ih a (Finset.mem_range.1 ha)]
    rw [this] at e₁
    exact add_left_cancel (e₁.trans e₂.symm)

/-- A right inverse series of a series with constant term `1` is unique. -/
theorem inv_unique_right (u X Y : ℕ → A) (hu : u 0 = 1)
    (hX : ∀ d, sconv u X d = if d = 0 then 1 else 0) (hY : ∀ d, sconv u Y d = if d = 0 then 1 else 0) :
    ∀ d, X d = Y d := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    have e₁ := hX d
    have e₂ := hY d
    rw [sconv, Finset.sum_range_succ', hu, one_mul, Nat.sub_zero] at e₁ e₂
    have : ∑ a ∈ Finset.range d, u (a + 1) * X (d - (a + 1)) =
        ∑ a ∈ Finset.range d, u (a + 1) * Y (d - (a + 1)) :=
      Finset.sum_congr rfl fun a ha => by
        rw [ih (d - (a + 1)) (by have := Finset.mem_range.1 ha; omega)]
    rw [this] at e₁
    exact add_left_cancel (e₁.trans e₂.symm)

/-- **Transfer of a slide to the inverse family**, left form: if `u w = 1`, `u' w' = 1`,
`w' = τ w` and `w₀ = 1`, then `u = u' τ`. -/
theorem transfer_left (u w u' w' τ : ℕ → A) (hG : ∀ d, sconv u w d = if d = 0 then 1 else 0)
    (hG' : ∀ d, sconv u' w' d = if d = 0 then 1 else 0) (hT : ∀ β, w' β = sconv τ w β)
    (hw : w 0 = 1) : ∀ α, u α = sconv u' τ α :=
  inv_unique_left w u (sconv u' τ) hw hG fun d => by
    rw [sconv_assoc, ← hG' d]
    exact Finset.sum_congr rfl fun a _ => by rw [hT]

/-- **Transfer of a slide to the inverse family**, right form: if `u w = 1`, `u' w' = 1`,
`u = u' τ` and `u'₀ = 1`, then `w' = τ w`. -/
theorem transfer_right (u w u' w' τ : ℕ → A) (hG : ∀ d, sconv u w d = if d = 0 then 1 else 0)
    (hG' : ∀ d, sconv u' w' d = if d = 0 then 1 else 0) (hA : ∀ α, u α = sconv u' τ α)
    (hu' : u' 0 = 1) : ∀ β, w' β = sconv τ w β :=
  inv_unique_right u' w' (sconv τ w) hu' hG' fun d => by
    rw [← sconv_assoc, ← hG d]
    exact Finset.sum_congr rfl fun a _ => by rw [hA]

theorem sconv_two_right (u : ℕ → A) (t₀ t₁ : A) (α : ℕ) :
    sconv u (fun e => if e = 0 then t₀ else if e = 1 then t₁ else 0) α =
      u α * t₀ + (if α = 0 then 0 else u (α - 1) * t₁) := by
  rw [sconv, Finset.sum_range_succ, Nat.sub_self, if_pos rfl, add_comm]
  congr 1
  rcases α with _ | α
  · simp
  · rw [Finset.sum_range_succ, show α + 1 - α = 1 by omega, if_neg (by omega), if_pos rfl,
      if_neg (by omega), Nat.add_sub_cancel]
    rw [Finset.sum_eq_zero fun a ha => ?_, zero_add]
    have := Finset.mem_range.1 ha
    rw [if_neg (by omega), if_neg (by omega), mul_zero]

theorem sconv_two_left (w : ℕ → A) (t₀ t₁ : A) (β : ℕ) :
    sconv (fun e => if e = 0 then t₀ else if e = 1 then t₁ else 0) w β =
      t₀ * w β + (if β = 0 then 0 else t₁ * w (β - 1)) := by
  rw [sconv, Finset.sum_range_succ', if_pos rfl, Nat.sub_zero, add_comm]
  congr 1
  rcases β with _ | β
  · simp
  · rw [Finset.sum_range_succ', if_neg (by omega), if_pos rfl, if_neg (by omega),
      show β + 1 - (0 + 1) = β by omega]
    rw [Finset.sum_eq_zero fun a ha => ?_, zero_add]
    rw [if_neg (by omega), if_neg (by omega), zero_mul]

end Conv

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (k : Type w) [CommRing k]

theorem lin_ccwL_eq_zero (ν : X) (i : I) (m : ℤ) (h : m + 1 + ip RD i ν < 0) :
    (pres RD k).lin (ccwL RD k ν i m) = 0 := ccwU_eq_zero RD k ν i m h

theorem lin_cwL_eq_zero (ν : X) (i : I) (m : ℤ) (h : m + 1 - ip RD i ν < 0) :
    (pres RD k).lin (cwL RD k ν i m) = 0 := cwU_eq_zero RD k ν i m h

/-! ## Bubbles of degree zero -/

theorem ccwU_deg0 (ρ : X) (i : I) : ccwU RD k ρ i (-ip RD i ρ - 1) = 𝟙 _ := by
  by_cases h : ip RD i ρ ≤ -1
  · have e : -ip RD i ρ - 1 = (((-ip RD i ρ - 1).toNat : ℕ) : ℤ) := by omega
    rw [e, ccwU_of_nonneg, dg_ccwOne RD k ρ i h, dg_nil]
  · rw [ccwU, ccwL, if_neg (by omega), if_pos (by omega),
      show (-ip RD i ρ - 1 + 1 + ip RD i ρ).toNat = 0 by omega, grassInv_zero]
    exact (pres RD k).lin_id _

theorem cwU_deg0 (ρ : X) (i : I) : cwU RD k ρ i (ip RD i ρ - 1) = 𝟙 _ := by
  by_cases h : 1 ≤ ip RD i ρ
  · have e : ip RD i ρ - 1 = (((ip RD i ρ - 1).toNat : ℕ) : ℤ) := by omega
    rw [e, cwU_of_nonneg, dg_cwOne RD k ρ i h, dg_nil]
  · rw [cwU, cwL, if_neg (by omega), if_pos (by omega),
      show (ip RD i ρ - 1 + 1 - ip RD i ρ).toNat = 0 by omega, grassInv_zero]
    exact (pres RD k).lin_id _

/-- The infinite Grassmannian relation in all degrees, including degree `0`. -/
theorem grassmannian_all (ρ : X) (i : I) (d : ℕ) :
    ∑ j ∈ Finset.range (d + 1),
      ccwU RD k ρ i (-ip RD i ρ - 1 + j) ≫ cwU RD k ρ i (ip RD i ρ - 1 + ((d : ℤ) - j)) =
      if d = 0 then 𝟙 _ else 0 := by
  rcases d with _ | d
  · simp only [zero_add, Finset.sum_range_one, Nat.cast_zero, add_zero, sub_self, if_true]
    rw [ccwU_deg0, cwU_deg0, Category.comp_id]
  · rw [if_neg (by omega)]
    exact grassmannian RD k ρ i (d + 1) (by omega)

/-! ## Placed bubbles as ring elements -/

theorem bubRU_comp (lam : X) (l : Letter I) (β γ : End ((pres RD k).obj (ob RD lam []))) :
    bubRU RD k lam l (β ≫ γ) = bubRU RD k lam l β ≫ bubRU RD k lam l γ :=
  (plcL_comp RD k lam [l] [] rfl rfl β γ).symm

theorem bubLU_comp (μ : X) (l : Letter I)
    (β γ : End ((pres RD k).obj (ob RD (wt RD μ [l]) []))) :
    bubLU RD k μ l (β ≫ γ) = bubLU RD k μ l β ≫ bubLU RD k μ l γ :=
  (plcL_comp RD k μ [] [l] rfl rfl β γ).symm

theorem bubRU_id (lam : X) (l : Letter I) : bubRU RD k lam l (𝟙 _) = 𝟙 _ := by
  rw [bubRU, ← dg_nil, plcL_dg_nil]; exact dg_nil lam [l]

theorem bubLU_zero (μ : X) (l : Letter I) :
    bubLU RD k μ l (0 : End ((pres RD k).obj (ob RD (wt RD μ [l]) []))) = 0 := map_zero _

theorem bubRU_zero (lam : X) (l : Letter I) :
    bubRU RD k lam l (0 : End ((pres RD k).obj (ob RD lam []))) = 0 := map_zero _

theorem bubLU_id (μ : X) (l : Letter I) : bubLU RD k μ l (𝟙 _) = 𝟙 _ := by
  rw [bubLU, ← dg_nil, plcL_dg]; exact dg_nil μ [l]

section Seq

variable (lam : X) (i : I) (l : Letter I)

/-- The counterclockwise bubbles of degree index `a` to the right of the strand `l`. -/
abbrev cRs (a : ℕ) : End ((pres RD k).obj (ob RD lam [l])) :=
  bubRU RD k lam l (ccwU RD k lam i (-ip RD i lam - 1 + a))

/-- The clockwise bubbles of degree index `b` to the right of the strand `l`. -/
abbrev wRs (b : ℕ) : End ((pres RD k).obj (ob RD lam [l])) :=
  bubRU RD k lam l (cwU RD k lam i (ip RD i lam - 1 + b))

/-- The counterclockwise bubbles of degree index `a` to the left of the strand `l`. -/
abbrev cLs (a : ℕ) : End ((pres RD k).obj (ob RD lam [l])) :=
  bubLU RD k lam l (ccwU RD k (wt RD lam [l]) i (-ip RD i (wt RD lam [l]) - 1 + a))

/-- The clockwise bubbles of degree index `b` to the left of the strand `l`. -/
abbrev wLs (b : ℕ) : End ((pres RD k).obj (ob RD lam [l])) :=
  bubLU RD k lam l (cwU RD k (wt RD lam [l]) i (ip RD i (wt RD lam [l]) - 1 + b))

theorem sconv_cRs_wRs (d : ℕ) :
    sconv (cRs RD k lam i l) (wRs RD k lam i l) d = if d = 0 then 1 else 0 := by
  have h := congrArg (plcL RD k lam [l] [] [] []) (grassmannian_all RD k lam i d)
  rw [map_sum] at h
  rw [sconv]
  simp only [End.mul_def]
  refine Eq.trans (Finset.sum_congr rfl fun a ha => ?_) (h.trans ?_)
  · have := Finset.mem_range.1 ha
    rw [← bubRU_comm, ← bubRU_comp]
    congr 3
    push_cast [Nat.cast_sub (by omega : a ≤ d)]; ring
  · split_ifs
    · exact bubRU_id RD k lam l
    · exact map_zero _

theorem sconv_cLs_wLs (d : ℕ) :
    sconv (cLs RD k lam i l) (wLs RD k lam i l) d = if d = 0 then 1 else 0 := by
  have h := congrArg (plcL RD k lam [] [l] [] []) (grassmannian_all RD k (wt RD lam [l]) i d)
  rw [map_sum] at h
  rw [sconv]
  simp only [End.mul_def]
  refine Eq.trans (Finset.sum_congr rfl fun a ha => ?_) (h.trans ?_)
  · have := Finset.mem_range.1 ha
    rw [← bubLU_comm, ← bubLU_comp]
    congr 3
    push_cast [Nat.cast_sub (by omega : a ≤ d)]; ring
  · split_ifs
    · exact bubLU_id RD k lam l
    · exact map_zero _

theorem cRs_zero : cRs RD k lam i l 0 = 1 := by
  simp only [cRs, Nat.cast_zero, add_zero]; rw [ccwU_deg0]; exact bubRU_id RD k lam l

theorem wRs_zero : wRs RD k lam i l 0 = 1 := by
  simp only [wRs, Nat.cast_zero, add_zero]; rw [cwU_deg0]; exact bubRU_id RD k lam l

theorem cLs_zero : cLs RD k lam i l 0 = 1 := by
  simp only [cLs, Nat.cast_zero, add_zero]; rw [ccwU_deg0]; exact bubLU_id RD k lam l

theorem wLs_zero : wLs RD k lam i l 0 = 1 := by
  simp only [wLs, Nat.cast_zero, add_zero]; rw [cwU_deg0]; exact bubLU_id RD k lam l

end Seq

/-! ## The case `i = j` -/

section Same

variable (lam : X) (i : I)

/-- The coefficients `(e + 1) x^e` of `1/(1 - x t)²`. -/
abbrev τsame (e : ℕ) : End ((pres RD k).obj (ob RD lam [up i])) :=
  (e + 1) • dotsU RD k lam (up i) e

theorem slideA_same_real (α : ℕ) (hα : 0 ≤ -ip RD i lam - 1 + α) :
    cRs RD k lam i (up i) α = sconv (cLs RD k lam i (up i)) (τsame RD k lam i) α := by
  have h := prop33_ccw_same RD k lam i α hα
  rw [lin_bubR_eq] at h
  rw [cRs, h, sconv]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  have := Finset.mem_range.1 hℓ
  rw [lin_bubL_eq, End.mul_def, τsame, Linear.smul_comp, bubLU_comm,
    show α + 1 - ℓ = α - ℓ + 1 by omega]

theorem slideB_same_real (β : ℕ) (hβ : 0 ≤ ip RD i (wt RD lam [up i]) - 1 + β) :
    wLs RD k lam i (up i) β = sconv (τsame RD k lam i) (wRs RD k lam i (up i)) β := by
  have h := prop33_cw_same RD k lam i β hβ
  rw [lin_bubL_eq] at h
  rw [wLs, h, sconv, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  have := Finset.mem_range.1 hℓ
  rw [lin_bubR_eq, End.mul_def, τsame, Linear.comp_smul, show β + 1 - 1 - ℓ = β - ℓ by omega,
    show β - (β - ℓ) = ℓ by omega, show β + 1 - (β - ℓ) = ℓ + 1 by omega]

theorem slides_same (lam : X) (i : I) :
    (∀ α, cRs RD k lam i (up i) α = sconv (cLs RD k lam i (up i)) (τsame RD k lam i) α) ∧
      ∀ β, wLs RD k lam i (up i) β = sconv (τsame RD k lam i) (wRs RD k lam i (up i)) β := by
  have hN : ip RD i (wt RD lam [up i]) = 2 + ip RD i lam := by rw [ip_wt_up, A_self]
  by_cases hn : 0 ≤ ip RD i lam
  · have hB : ∀ β, wLs RD k lam i (up i) β = sconv (τsame RD k lam i) (wRs RD k lam i (up i)) β :=
      fun β => slideB_same_real RD k lam i β (by omega)
    exact ⟨transfer_left _ _ _ _ _ (sconv_cRs_wRs RD k lam i (up i)) (sconv_cLs_wLs RD k lam i (up i))
      hB (wRs_zero RD k lam i (up i)), hB⟩
  · have hA : ∀ α, cRs RD k lam i (up i) α = sconv (cLs RD k lam i (up i)) (τsame RD k lam i) α :=
      fun α => slideA_same_real RD k lam i α (by omega)
    exact ⟨hA, transfer_right _ _ _ _ _ (sconv_cRs_wRs RD k lam i (up i))
      (sconv_cLs_wLs RD k lam i (up i)) hA (cLs_zero RD k lam i (up i))⟩

end Same

/-- **KL III Proposition 3.3, first display, `i = j`, all degrees**: for every `α ≥ 0`
(the bubble on the left-hand side may be a fake bubble),
`ccw_{-⟨i,λ⟩-1+α} ⊗ E_i = ∑_{ℓ=0}^{α} (α + 1 - ℓ) (E_i ⊗ ccw_{-⟨i,λ+i_X⟩-1+ℓ}) x^{α-ℓ}`. -/
theorem prop33_ccw_same_all (lam : X) (i : I) (α : ℕ) :
    (pres RD k).lin (bubR RD k lam [up i] (ccwL RD k lam i (-ip RD i lam - 1 + α))) =
      ∑ ℓ ∈ Finset.range (α + 1), (α + 1 - ℓ) •
        ((pres RD k).lin (bubL RD k lam [up i]
            (ccwL RD k (wt RD lam [up i]) i (-ip RD i (wt RD lam [up i]) - 1 + ℓ))) ≫
          dotsU RD k lam (up i) (α - ℓ)) := by
  rw [lin_bubR_eq]
  refine ((slides_same RD k lam i).1 α).trans ?_
  rw [sconv]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  have := Finset.mem_range.1 hℓ
  rw [lin_bubL_eq, End.mul_def, τsame, Linear.smul_comp, bubLU_comm,
    show α + 1 - ℓ = α - ℓ + 1 by omega]

/-- **KL III Proposition 3.3, second display, `i = j`, all degrees**: for every `α ≥ 0`,
`E_i ⊗ cw_{⟨i,λ+i_X⟩-1+α} = ∑_{ℓ=0}^{α} (α + 1 - ℓ) (cw_{⟨i,λ⟩-1+ℓ} ⊗ E_i) x^{α-ℓ}`. -/
theorem prop33_cw_same_all (lam : X) (i : I) (α : ℕ) :
    (pres RD k).lin (bubL RD k lam [up i]
        (cwL RD k (wt RD lam [up i]) i (ip RD i (wt RD lam [up i]) - 1 + α))) =
      ∑ ℓ ∈ Finset.range (α + 1), (α + 1 - ℓ) •
        ((pres RD k).lin (bubR RD k lam [up i] (cwL RD k lam i (ip RD i lam - 1 + ℓ))) ≫
          dotsU RD k lam (up i) (α - ℓ)) := by
  rw [lin_bubL_eq]
  refine ((slides_same RD k lam i).2 α).trans ?_
  rw [sconv, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  have := Finset.mem_range.1 hℓ
  rw [lin_bubR_eq, End.mul_def, τsame, Linear.comp_smul, show α + 1 - 1 - ℓ = α - ℓ by omega,
    show α - (α - ℓ) = ℓ by omega, show α + 1 - ℓ = α - ℓ + 1 by omega]

/-! ## The case `i · j = -1` -/

section Adj

variable (lam : X) (i j : I)

/-- The coefficients of `1 + x t` (dots on the strand `j`). -/
abbrev τadj (e : ℕ) : End ((pres RD k).obj (ob RD lam [up j])) :=
  if e = 0 then 1 else if e = 1 then dotsU RD k lam (up j) 1 else 0

theorem slideA_adj_real (hij : C.dot i j = -1) (α : ℕ) (hα : 0 ≤ -ip RD i lam - 1 + α) :
    cRs RD k lam i (up j) α = sconv (cLs RD k lam i (up j)) (τadj RD k lam j) α := by
  have hn : ip RD i (wt RD lam [up j]) = -1 + ip RD i lam := by
    rw [ip_wt_up, A_of_dot_neg_one hij]
  have h := prop33_ccw_adj RD k lam i j hij α hα
  rw [lin_bubR_eq, lin_bubL_eq, lin_bubL_eq] at h
  rw [cRs, h]; unfold τadj; rw [sconv_two_right, mul_one]
  congr 1
  split_ifs with h0
  · subst h0
    rw [Nat.cast_zero, add_zero, lin_ccwL_eq_zero RD k _ i _ (by omega)]
    rw [bubLU_zero, Limits.zero_comp]
  · rw [End.mul_def, ← bubLU_comm]
    congr 3
    push_cast [Nat.cast_sub (by omega : 1 ≤ α)]; ring_nf

theorem slideB_adj_real (hij : C.dot i j = -1) (β : ℕ)
    (hβ : 0 ≤ ip RD i (wt RD lam [up j]) - 1 + β) :
    wLs RD k lam i (up j) β = sconv (τadj RD k lam j) (wRs RD k lam i (up j)) β := by
  have hn : ip RD i (wt RD lam [up j]) = -1 + ip RD i lam := by
    rw [ip_wt_up, A_of_dot_neg_one hij]
  have h := prop33_cw_adj RD k lam i j hij β hβ
  rw [lin_bubL_eq, lin_bubR_eq, lin_bubR_eq] at h
  rw [wLs, h]; unfold τadj; rw [sconv_two_left, one_mul, add_comm]
  congr 1
  split_ifs with h0
  · subst h0
    rw [Nat.cast_zero, add_zero, lin_cwL_eq_zero RD k _ i _ (by omega)]
    rw [bubRU_zero, Limits.zero_comp]
  · rw [End.mul_def]
    congr 3
    push_cast [Nat.cast_sub (by omega : 1 ≤ β)]; ring_nf

theorem slides_adj (hij : C.dot i j = -1) :
    (∀ α, cRs RD k lam i (up j) α = sconv (cLs RD k lam i (up j)) (τadj RD k lam j) α) ∧
      ∀ β, wLs RD k lam i (up j) β = sconv (τadj RD k lam j) (wRs RD k lam i (up j)) β := by
  have hn : ip RD i (wt RD lam [up j]) = -1 + ip RD i lam := by
    rw [ip_wt_up, A_of_dot_neg_one hij]
  by_cases h1 : 1 ≤ ip RD i lam
  · have hB : ∀ β, wLs RD k lam i (up j) β = sconv (τadj RD k lam j) (wRs RD k lam i (up j)) β := by
      intro β
      rcases β with _ | β
      · unfold τadj; simp [sconv_two_left, wLs_zero, wRs_zero]
      · exact slideB_adj_real RD k lam i j hij _ (by push_cast; omega)
    exact ⟨transfer_left _ _ _ _ _ (sconv_cRs_wRs RD k lam i (up j))
      (sconv_cLs_wLs RD k lam i (up j)) hB (wRs_zero RD k lam i (up j)), hB⟩
  · have hA : ∀ α, cRs RD k lam i (up j) α = sconv (cLs RD k lam i (up j)) (τadj RD k lam j) α := by
      intro α
      rcases α with _ | α
      · unfold τadj; simp [sconv_two_right, cRs_zero, cLs_zero]
      · exact slideA_adj_real RD k lam i j hij _ (by push_cast; omega)
    exact ⟨hA, transfer_right _ _ _ _ _ (sconv_cRs_wRs RD k lam i (up j))
      (sconv_cLs_wLs RD k lam i (up j)) hA (cLs_zero RD k lam i (up j))⟩

end Adj

/-- **KL III Proposition 3.3, first display, `i · j = -1`, all degrees**: for every `α ≥ 0`,
`ccw_{-⟨i,λ⟩-1+α} ⊗ E_j = E_j ⊗ ccw_{-⟨i,λ+j_X⟩-1+α} + (E_j ⊗ ccw_{-⟨i,λ+j_X⟩-2+α}) x_j`. -/
theorem prop33_ccw_adj_all (lam : X) (i j : I) (hij : C.dot i j = -1) (α : ℕ) :
    (pres RD k).lin (bubR RD k lam [up j] (ccwL RD k lam i (-ip RD i lam - 1 + α))) =
      (pres RD k).lin (bubL RD k lam [up j]
          (ccwL RD k (wt RD lam [up j]) i (-ip RD i (wt RD lam [up j]) - 1 + α))) +
        (pres RD k).lin (bubL RD k lam [up j]
            (ccwL RD k (wt RD lam [up j]) i (-ip RD i (wt RD lam [up j]) - 2 + α))) ≫
          dotsU RD k lam (up j) 1 := by
  rw [lin_bubR_eq, lin_bubL_eq, lin_bubL_eq]
  refine ((slides_adj RD k lam i j hij).1 α).trans ?_
  unfold τadj; rw [sconv_two_right, mul_one]
  congr 1
  split_ifs with h0
  · subst h0
    rw [Nat.cast_zero, add_zero, lin_ccwL_eq_zero RD k _ i _ (by omega)]
    rw [bubLU_zero, Limits.zero_comp]
  · rw [End.mul_def, ← bubLU_comm]
    congr 3
    omega

/-- **KL III Proposition 3.3, second display, `i · j = -1`, all degrees**: for every `α ≥ 0`,
`E_j ⊗ cw_{⟨i,λ+j_X⟩-1+α} = (cw_{⟨i,λ⟩-1+α-1} ⊗ E_j) x_j + cw_{⟨i,λ⟩-1+α} ⊗ E_j`. -/
theorem prop33_cw_adj_all (lam : X) (i j : I) (hij : C.dot i j = -1) (α : ℕ) :
    (pres RD k).lin (bubL RD k lam [up j]
        (cwL RD k (wt RD lam [up j]) i (ip RD i (wt RD lam [up j]) - 1 + α))) =
      (pres RD k).lin (bubR RD k lam [up j] (cwL RD k lam i (ip RD i lam - 1 + α - 1))) ≫
          dotsU RD k lam (up j) 1 +
        (pres RD k).lin (bubR RD k lam [up j] (cwL RD k lam i (ip RD i lam - 1 + α))) := by
  rw [lin_bubL_eq, lin_bubR_eq, lin_bubR_eq]
  refine ((slides_adj RD k lam i j hij).2 α).trans ?_
  unfold τadj; rw [sconv_two_left, one_mul, add_comm]
  congr 1
  split_ifs with h0
  · subst h0
    rw [Nat.cast_zero, add_zero, lin_cwL_eq_zero RD k _ i _ (by omega)]
    rw [bubRU_zero, Limits.zero_comp]
  · rw [End.mul_def]
    simp only [wRs]
    congr 3
    omega

/-! ## The case `i · j = 0` -/

section Orth

variable (lam : X) (i j : I)

/-- The coefficients of the unit series. -/
abbrev τorth (e : ℕ) : End ((pres RD k).obj (ob RD lam [up j])) :=
  if e = 0 then 1 else if e = 1 then 0 else 0

theorem sconv_τorth_right (u : ℕ → End ((pres RD k).obj (ob RD lam [up j]))) (α : ℕ) :
    sconv u (τorth RD k lam j) α = u α := by
  unfold τorth; rw [sconv_two_right]; simp

theorem sconv_τorth_left (w : ℕ → End ((pres RD k).obj (ob RD lam [up j]))) (β : ℕ) :
    sconv (τorth RD k lam j) w β = w β := by
  unfold τorth; rw [sconv_two_left]; simp

theorem slides_orth (hij : C.dot i j = 0) :
    (∀ α, cRs RD k lam i (up j) α = cLs RD k lam i (up j) α) ∧
      ∀ β, wLs RD k lam i (up j) β = wRs RD k lam i (up j) β := by
  have hn : ip RD i (wt RD lam [up j]) = ip RD i lam := by
    rw [ip_wt_up, A_of_dot_zero hij, zero_add]
  by_cases h1 : 1 ≤ ip RD i lam
  · have hB : ∀ β, wLs RD k lam i (up j) β = sconv (τorth RD k lam j) (wRs RD k lam i (up j)) β := by
      intro β
      rw [sconv_τorth_left, wLs, wRs, hn]
      have h := prop33_cw_orth RD k lam i j hij β (by omega)
      rw [lin_bubL_eq, lin_bubR_eq] at h
      exact h
    have hA := transfer_left _ _ _ _ _ (sconv_cRs_wRs RD k lam i (up j))
      (sconv_cLs_wLs RD k lam i (up j)) hB (wRs_zero RD k lam i (up j))
    exact ⟨fun α => (hA α).trans (sconv_τorth_right RD k lam j _ α),
      fun β => (hB β).trans (sconv_τorth_left RD k lam j _ β)⟩
  · have hA : ∀ α, cRs RD k lam i (up j) α = sconv (cLs RD k lam i (up j)) (τorth RD k lam j) α := by
      intro α
      rw [sconv_τorth_right]
      rcases α with _ | α
      · rw [cRs_zero, cLs_zero]
      · rw [cRs, cLs, hn]
        have h := prop33_ccw_orth RD k lam i j hij (α + 1) (by push_cast; omega)
        rw [lin_bubL_eq, lin_bubR_eq] at h
        exact h
    have hB := transfer_right _ _ _ _ _ (sconv_cRs_wRs RD k lam i (up j))
      (sconv_cLs_wLs RD k lam i (up j)) hA (cLs_zero RD k lam i (up j))
    exact ⟨fun α => (hA α).trans (sconv_τorth_right RD k lam j _ α),
      fun β => (hB β).trans (sconv_τorth_left RD k lam j _ β)⟩

end Orth

/-- **KL III Proposition 3.3, first display, `i · j = 0`, all degrees**: for every `α ≥ 0`,
`ccw_{-⟨i,λ⟩-1+α} ⊗ E_j = E_j ⊗ ccw_{-⟨i,λ⟩-1+α}`. -/
theorem prop33_ccw_orth_all (lam : X) (i j : I) (hij : C.dot i j = 0) (α : ℕ) :
    (pres RD k).lin (bubR RD k lam [up j] (ccwL RD k lam i (-ip RD i lam - 1 + α))) =
      (pres RD k).lin (bubL RD k lam [up j] (ccwL RD k (wt RD lam [up j]) i (-ip RD i lam - 1 + α))) := by
  have hn : ip RD i (wt RD lam [up j]) = ip RD i lam := by
    rw [ip_wt_up, A_of_dot_zero hij, zero_add]
  have h := (slides_orth RD k lam i j hij).1 α
  rw [cRs, cLs, hn] at h
  rw [lin_bubR_eq, lin_bubL_eq]
  exact h

/-- **KL III Proposition 3.3, second display, `i · j = 0`, all degrees**: for every `α ≥ 0`,
`E_j ⊗ cw_{⟨i,λ⟩-1+α} = cw_{⟨i,λ⟩-1+α} ⊗ E_j`. -/
theorem prop33_cw_orth_all (lam : X) (i j : I) (hij : C.dot i j = 0) (α : ℕ) :
    (pres RD k).lin (bubL RD k lam [up j] (cwL RD k (wt RD lam [up j]) i (ip RD i lam - 1 + α))) =
      (pres RD k).lin (bubR RD k lam [up j] (cwL RD k lam i (ip RD i lam - 1 + α))) := by
  have hn : ip RD i (wt RD lam [up j]) = ip RD i lam := by
    rw [ip_wt_up, A_of_dot_zero hij, zero_add]
  have h := (slides_orth RD k lam i j hij).2 α
  rw [wLs, wRs, hn] at h
  rw [lin_bubR_eq, lin_bubL_eq]
  exact h

/-! ## Proposition 3.4 in all degrees -/

theorem cw_left_expand_all (lam : X) (i : I) (α c : ℕ) :
    (pres RD k).lin (bubL RD k lam [up i]
        (cwL RD k (wt RD lam [up i]) i (ip RD i lam + 1 + ((α : ℤ) - c)))) ≫
        dotsU RD k lam (up i) c =
      ∑ ℓ ∈ Finset.range (α + 1 - c), (α + 1 - c - ℓ) •
        (bubRU RD k lam (up i) (cwU RD k lam i (ip RD i lam - 1 + ℓ)) ≫
          dotsU RD k lam (up i) (α - ℓ)) := by
  have hN : ip RD i (wt RD lam [up i]) = 2 + ip RD i lam := by rw [ip_wt_up, A_self]
  by_cases hc : c ≤ α
  · have e : ip RD i lam + 1 + ((α : ℤ) - c) = ip RD i (wt RD lam [up i]) - 1 + ((α - c : ℕ) : ℤ) := by
      rw [hN]; push_cast [Nat.cast_sub hc]; ring
    rw [e, prop33_cw_same_all, Preadditive.sum_comp, show α - c + 1 = α + 1 - c by omega]
    refine Finset.sum_congr rfl fun ℓ hℓ => ?_
    have := Finset.mem_range.1 hℓ
    rw [Linear.smul_comp, Category.assoc, dotsU_add, lin_bubR_eq,
      show α - c - ℓ + c = α - ℓ by omega]
  · rw [lin_bubL_eq, lin_cwL_eq_zero RD k _ i _ (by omega), bubLU_zero, Limits.zero_comp,
      show α + 1 - c = 0 by omega, Finset.sum_range_zero]

theorem ccw_right_expand_all (lam : X) (i : I) (α c : ℕ) :
    (pres RD k).lin (bubR RD k lam [up i] (ccwL RD k lam i (-ip RD i lam - 1 + ((α : ℤ) - c)))) ≫
        dotsU RD k lam (up i) c =
      ∑ j ∈ Finset.range (α + 1 - c), (α + 1 - c - j) •
        (bubLU RD k lam (up i) (ccwU RD k (wt RD lam [up i]) i
            (-ip RD i (wt RD lam [up i]) - 1 + j)) ≫ dotsU RD k lam (up i) (α - j)) := by
  by_cases hc : c ≤ α
  · have e : -ip RD i lam - 1 + ((α : ℤ) - c) = -ip RD i lam - 1 + ((α - c : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hc]; ring
    rw [e, prop33_ccw_same_all, Preadditive.sum_comp, show α - c + 1 = α + 1 - c by omega]
    refine Finset.sum_congr rfl fun ℓ hℓ => ?_
    have := Finset.mem_range.1 hℓ
    rw [Linear.smul_comp, Category.assoc, dotsU_add, lin_bubL_eq,
      show α - c - ℓ + c = α - ℓ by omega]
  · rw [lin_bubR_eq, lin_ccwL_eq_zero RD k _ i _ (by omega), bubRU_zero, Limits.zero_comp,
      show α + 1 - c = 0 by omega, Finset.sum_range_zero]

/-- **KL III Proposition 3.4, first display, `i = j`, all degrees**: for every `α ≥ 0`,
`cw_{⟨i,λ⟩-1+α} ⊗ E_i = (E_i ⊗ cw_{⟨i,λ⟩+1+(α-2)}) x² - 2 (E_i ⊗ cw_{⟨i,λ⟩+1+(α-1)}) x +
E_i ⊗ cw_{⟨i,λ⟩+1+α}`. -/
theorem prop34_cw_same_all (lam : X) (i : I) (α : ℕ) :
    (pres RD k).lin (bubR RD k lam [up i] (cwL RD k lam i (ip RD i lam - 1 + α))) =
      (pres RD k).lin (bubL RD k lam [up i]
          (cwL RD k (wt RD lam [up i]) i (ip RD i lam + 1 + ((α : ℤ) - 2)))) ≫
          dotsU RD k lam (up i) 2 -
        2 • ((pres RD k).lin (bubL RD k lam [up i]
          (cwL RD k (wt RD lam [up i]) i (ip RD i lam + 1 + ((α : ℤ) - 1)))) ≫
          dotsU RD k lam (up i) 1) +
        (pres RD k).lin (bubL RD k lam [up i]
          (cwL RD k (wt RD lam [up i]) i (ip RD i lam + 1 + α))) := by
  have h₀ := cw_left_expand_all RD k lam i α 0
  simp only [Nat.cast_zero, sub_zero, dotsU_zero, Category.comp_id, Nat.sub_zero] at h₀
  have h₂ := cw_left_expand_all RD k lam i α 2
  have h₁ := cw_left_expand_all RD k lam i α 1
  simp only [Nat.cast_ofNat, Nat.cast_one] at h₂ h₁
  rw [h₂, h₁, h₀, show α + 1 - 2 = α - 1 by omega, show α + 1 - 1 = α by omega]
  have h := second_difference (fun ℓ => bubRU RD k lam (up i) (cwU RD k lam i (ip RD i lam - 1 + ℓ)) ≫
    dotsU RD k lam (up i) (α - ℓ)) α
  simp only [Nat.sub_self, dotsU_zero, Category.comp_id] at h
  rw [lin_bubR_eq, h.symm]

/-- **KL III Proposition 3.4, second display, `i = j`, all degrees**: for every `α ≥ 0`,
`E_i ⊗ ccw_{-⟨i,λ+i_X⟩-1+α} = (ccw_{-⟨i,λ⟩-1+(α-2)} ⊗ E_i) x² -
2 (ccw_{-⟨i,λ⟩-1+(α-1)} ⊗ E_i) x + ccw_{-⟨i,λ⟩-1+α} ⊗ E_i`. -/
theorem prop34_ccw_same_all (lam : X) (i : I) (α : ℕ) :
    (pres RD k).lin (bubL RD k lam [up i]
        (ccwL RD k (wt RD lam [up i]) i (-ip RD i (wt RD lam [up i]) - 1 + α))) =
      (pres RD k).lin (bubR RD k lam [up i] (ccwL RD k lam i (-ip RD i lam - 1 + ((α : ℤ) - 2)))) ≫
          dotsU RD k lam (up i) 2 -
        2 • ((pres RD k).lin (bubR RD k lam [up i]
          (ccwL RD k lam i (-ip RD i lam - 1 + ((α : ℤ) - 1)))) ≫ dotsU RD k lam (up i) 1) +
        (pres RD k).lin (bubR RD k lam [up i] (ccwL RD k lam i (-ip RD i lam - 1 + α))) := by
  have h₀ := ccw_right_expand_all RD k lam i α 0
  simp only [Nat.cast_zero, sub_zero, dotsU_zero, Category.comp_id, Nat.sub_zero] at h₀
  have h₂ := ccw_right_expand_all RD k lam i α 2
  have h₁ := ccw_right_expand_all RD k lam i α 1
  simp only [Nat.cast_ofNat, Nat.cast_one] at h₂ h₁
  rw [h₂, h₁, h₀, show α + 1 - 2 = α - 1 by omega, show α + 1 - 1 = α by omega]
  have h := second_difference (fun j => bubLU RD k lam (up i) (ccwU RD k (wt RD lam [up i]) i
    (-ip RD i (wt RD lam [up i]) - 1 + j)) ≫ dotsU RD k lam (up i) (α - j)) α
  simp only [Nat.sub_self, dotsU_zero, Category.comp_id] at h
  rw [lin_bubL_eq, h.symm]

/-- **KL III Proposition 3.4, first display, `i · j = -1`, all degrees**: for every `α ≥ 0`,
`cw_{⟨i,λ⟩-1+α} ⊗ E_j = ∑_{f=0}^{α} (-1)^f (E_j ⊗ cw_{⟨i,λ+j_X⟩-1+(α-f)}) x_j^f`. -/
theorem prop34_cw_adj_all (lam : X) (i j : I) (hij : C.dot i j = -1) (α : ℕ) :
    (pres RD k).lin (bubR RD k lam [up j] (cwL RD k lam i (ip RD i lam - 1 + α))) =
      ∑ f ∈ Finset.range (α + 1), ((-1 : ℤ) ^ f) •
        ((pres RD k).lin (bubL RD k lam [up j]
            (cwL RD k (wt RD lam [up j]) i (ip RD i (wt RD lam [up j]) - 1 + ((α - f : ℕ) : ℤ)))) ≫
          dotsU RD k lam (up j) f) := by
  induction α with
  | zero =>
    have h := prop33_cw_adj_all RD k lam i j hij 0
    rw [show ip RD i lam - 1 + ((0 : ℕ) : ℤ) - 1 = ip RD i lam - 2 by push_cast; ring,
      lin_bubR_eq RD k lam (up j) (cwL RD k lam i (ip RD i lam - 2)),
      lin_cwL_eq_zero RD k lam i _ (by omega), bubRU_zero, Limits.zero_comp, zero_add] at h
    rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, one_smul, dotsU_zero,
      Category.comp_id, Nat.sub_zero]
    exact h.symm
  | succ α ih =>
    have h := prop33_cw_adj_all RD k lam i j hij (α + 1)
    have e : ip RD i lam - 1 + ((α + 1 : ℕ) : ℤ) - 1 = ip RD i lam - 1 + (α : ℤ) := by push_cast; ring
    rw [e, ih] at h
    rw [eq_sub_of_add_eq' h.symm, Preadditive.sum_comp, Finset.sum_range_succ' _ (α + 1),
      pow_zero, one_smul, Nat.sub_zero, dotsU_zero, Category.comp_id, sub_eq_add_neg,
      ← Finset.sum_neg_distrib, add_comm (∑ _ ∈ _, _)]
    congr 1
    refine Finset.sum_congr rfl fun f hf => ?_
    have := Finset.mem_range.1 hf
    rw [Linear.smul_comp, Category.assoc, dotsU_add, pow_succ, mul_neg_one, neg_smul]
    rw [show α + 1 - (f + 1) = α - f by omega]

/-- **KL III Proposition 3.4, second display, `i · j = -1`, all degrees**: for every `α ≥ 0`,
`E_j ⊗ ccw_{-⟨i,λ+j_X⟩-1+α} = ∑_{f=0}^{α} (-1)^f (ccw_{-⟨i,λ⟩-1+(α-f)} ⊗ E_j) x_j^f`. -/
theorem prop34_ccw_adj_all (lam : X) (i j : I) (hij : C.dot i j = -1) (α : ℕ) :
    (pres RD k).lin (bubL RD k lam [up j]
        (ccwL RD k (wt RD lam [up j]) i (-ip RD i (wt RD lam [up j]) - 1 + α))) =
      ∑ f ∈ Finset.range (α + 1), ((-1 : ℤ) ^ f) •
        ((pres RD k).lin (bubR RD k lam [up j]
            (ccwL RD k lam i (-ip RD i lam - 1 + ((α - f : ℕ) : ℤ)))) ≫
          dotsU RD k lam (up j) f) := by
  have hn' : ip RD i (wt RD lam [up j]) = -1 + ip RD i lam := by
    rw [ip_wt_up, A_of_dot_neg_one hij]
  induction α with
  | zero =>
    have h := prop33_ccw_adj_all RD k lam i j hij 0
    rw [show -ip RD i (wt RD lam [up j]) - 2 + ((0 : ℕ) : ℤ) = -ip RD i (wt RD lam [up j]) - 2 by
        push_cast; ring,
      lin_bubL_eq RD k lam (up j) (ccwL RD k _ i (-ip RD i (wt RD lam [up j]) - 2)),
      lin_ccwL_eq_zero RD k _ i _ (by omega), bubLU_zero, Limits.zero_comp, add_zero] at h
    rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, one_smul, dotsU_zero,
      Category.comp_id, Nat.sub_zero]
    exact h.symm
  | succ α ih =>
    have h := prop33_ccw_adj_all RD k lam i j hij (α + 1)
    have e : -ip RD i (wt RD lam [up j]) - 2 + ((α + 1 : ℕ) : ℤ) =
        -ip RD i (wt RD lam [up j]) - 1 + (α : ℤ) := by push_cast; ring
    rw [e, ih] at h
    rw [eq_sub_of_add_eq h.symm, Preadditive.sum_comp, Finset.sum_range_succ' _ (α + 1),
      pow_zero, one_smul, Nat.sub_zero, dotsU_zero, Category.comp_id, sub_eq_add_neg,
      ← Finset.sum_neg_distrib, add_comm (∑ _ ∈ _, _)]
    congr 1
    refine Finset.sum_congr rfl fun f hf => ?_
    have := Finset.mem_range.1 hf
    rw [Linear.smul_comp, Category.assoc, dotsU_add, pow_succ, mul_neg_one, neg_smul]
    rw [show α + 1 - (f + 1) = α - f by omega]

end Categorification.KL3.Diagram

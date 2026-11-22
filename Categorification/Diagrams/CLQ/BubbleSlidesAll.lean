/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CLQ.Grassmannian
import Categorification.Diagrams.CLQ.MoreBubbleSlides
import Categorification.Diagrams.KL3.BubbleSlidesAll

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

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram.CLQ

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

/-! ## Convolution of sequences -/

section Conv

variable {A : Type*} [Ring A]











end Conv

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k] (sc : CL.CLScalars C k)

theorem lin_ccwL_eq_zero (ν : X) (i : I) (m : ℤ) (h : m + 1 + ip RD i ν < 0) :
    (pres RD k sc).lin (ccwL RD k ν i m) = 0 := ccwU_eq_zero RD k sc ν i m h

theorem lin_cwL_eq_zero (ν : X) (i : I) (m : ℤ) (h : m + 1 - ip RD i ν < 0) :
    (pres RD k sc).lin (cwL RD k ν i m) = 0 := cwU_eq_zero RD k sc ν i m h

/-! ## Bubbles of degree zero -/

theorem ccwU_deg0 (ρ : X) (i : I) : NF.ccwU (pres RD k sc) ρ i (-ip RD i ρ - 1) = 𝟙 _ := by
  by_cases h : ip RD i ρ ≤ -1
  · have e : -ip RD i ρ - 1 = (((-ip RD i ρ - 1).toNat : ℕ) : ℤ) := by omega
    rw [e, NF.ccwU_of_nonneg, dg_ccwOne RD k sc ρ i h, NF.dg_nil]
  · rw [NF.ccwU, ccwL, ite_eq_right (by omega), ite_eq_left (by omega),
      show (-ip RD i ρ - 1 + 1 + ip RD i ρ).toNat = 0 by omega, grassInv_zero]
    exact (pres RD k sc).lin_id _

theorem cwU_deg0 (ρ : X) (i : I) : NF.cwU (pres RD k sc) ρ i (ip RD i ρ - 1) = 𝟙 _ := by
  by_cases h : 1 ≤ ip RD i ρ
  · have e : ip RD i ρ - 1 = (((ip RD i ρ - 1).toNat : ℕ) : ℤ) := by omega
    rw [e, NF.cwU_of_nonneg, dg_cwOne RD k sc ρ i h, NF.dg_nil]
  · rw [NF.cwU, cwL, ite_eq_right (by omega), ite_eq_left (by omega),
      show (ip RD i ρ - 1 + 1 - ip RD i ρ).toNat = 0 by omega, grassInv_zero]
    exact (pres RD k sc).lin_id _

/-- The infinite Grassmannian relation in all degrees, including degree `0`. -/
theorem grassmannian_all (ρ : X) (i : I) (d : ℕ) :
    ∑ j ∈ Finset.range (d + 1),
      NF.ccwU (pres RD k sc) ρ i (-ip RD i ρ - 1 + j) ≫ NF.cwU (pres RD k sc) ρ i (ip RD i ρ - 1 + ((d : ℤ) - j)) =
      if d = 0 then 𝟙 _ else 0 := by
  rcases d with _ | d
  · simp only [zero_add, Finset.sum_range_one, Nat.cast_zero, add_zero, sub_self, ite_true]
    rw [ccwU_deg0, cwU_deg0, Category.comp_id]
  · rw [ite_eq_right (by omega)]
    exact grassmannian RD k sc ρ i (d + 1) (by omega)

/-! ## Placed bubbles as ring elements -/

theorem bubRU_comp (lam : X) (l : Letter I) (β γ : End ((pres RD k sc).obj (ob RD lam []))) :
    NF.bubRU (pres RD k sc) lam l (β ≫ γ) = NF.bubRU (pres RD k sc) lam l β ≫ NF.bubRU (pres RD k sc) lam l γ :=
  (NF.plcL_comp (pres RD k sc) lam [l] [] rfl rfl β γ).symm

theorem bubLU_comp (μ : X) (l : Letter I)
    (β γ : End ((pres RD k sc).obj (ob RD (wt RD μ [l]) []))) :
    NF.bubLU (pres RD k sc) μ l (β ≫ γ) = NF.bubLU (pres RD k sc) μ l β ≫ NF.bubLU (pres RD k sc) μ l γ :=
  (NF.plcL_comp (pres RD k sc) μ [] [l] rfl rfl β γ).symm

theorem bubRU_id (lam : X) (l : Letter I) : NF.bubRU (pres RD k sc) lam l (𝟙 _) = 𝟙 _ := by
  rw [NF.bubRU, ← NF.dg_nil, NF.plcL_dg_nil]; exact NF.dg_nil lam [l]

theorem bubLU_zero (μ : X) (l : Letter I) :
    NF.bubLU (pres RD k sc) μ l (0 : End ((pres RD k sc).obj (ob RD (wt RD μ [l]) []))) = 0 := map_zero _

theorem bubRU_zero (lam : X) (l : Letter I) :
    NF.bubRU (pres RD k sc) lam l (0 : End ((pres RD k sc).obj (ob RD lam []))) = 0 := map_zero _

theorem bubLU_id (μ : X) (l : Letter I) : NF.bubLU (pres RD k sc) μ l (𝟙 _) = 𝟙 _ := by
  rw [NF.bubLU, ← NF.dg_nil, NF.plcL_dg]; exact NF.dg_nil μ [l]

section Seq

variable (lam : X) (i : I) (l : Letter I)

/-- The counterclockwise bubbles of degree index `a` to the right of the strand `l`. -/
abbrev cRs (a : ℕ) : End ((pres RD k sc).obj (ob RD lam [l])) :=
  NF.bubRU (pres RD k sc) lam l (NF.ccwU (pres RD k sc) lam i (-ip RD i lam - 1 + a))

/-- The clockwise bubbles of degree index `b` to the right of the strand `l`. -/
abbrev wRs (b : ℕ) : End ((pres RD k sc).obj (ob RD lam [l])) :=
  NF.bubRU (pres RD k sc) lam l (NF.cwU (pres RD k sc) lam i (ip RD i lam - 1 + b))

/-- The counterclockwise bubbles of degree index `a` to the left of the strand `l`. -/
abbrev cLs (a : ℕ) : End ((pres RD k sc).obj (ob RD lam [l])) :=
  NF.bubLU (pres RD k sc) lam l (NF.ccwU (pres RD k sc) (wt RD lam [l]) i (-ip RD i (wt RD lam [l]) - 1 + a))

/-- The clockwise bubbles of degree index `b` to the left of the strand `l`. -/
abbrev wLs (b : ℕ) : End ((pres RD k sc).obj (ob RD lam [l])) :=
  NF.bubLU (pres RD k sc) lam l (NF.cwU (pres RD k sc) (wt RD lam [l]) i (ip RD i (wt RD lam [l]) - 1 + b))

theorem sconv_cRs_wRs (d : ℕ) :
    sconv (cRs RD k sc lam i l) (wRs RD k sc lam i l) d = if d = 0 then 1 else 0 := by
  have h := congrArg (NF.plcL (pres RD k sc) lam [l] [] [] []) (grassmannian_all RD k sc lam i d)
  rw [map_sum] at h
  rw [sconv]
  simp only [End.mul_def]
  refine Eq.trans (Finset.sum_congr rfl fun a ha => ?_) (h.trans ?_)
  · have := Finset.mem_range.1 ha
    rw [← NF.bubRU_comm, ← bubRU_comp]
    congr 3
    push_cast [Nat.cast_sub (by omega : a ≤ d)]; ring
  · split_ifs
    · exact bubRU_id RD k sc lam l
    · exact map_zero _

theorem sconv_cLs_wLs (d : ℕ) :
    sconv (cLs RD k sc lam i l) (wLs RD k sc lam i l) d = if d = 0 then 1 else 0 := by
  have h := congrArg (NF.plcL (pres RD k sc) lam [] [l] [] []) (grassmannian_all RD k sc (wt RD lam [l]) i d)
  rw [map_sum] at h
  rw [sconv]
  simp only [End.mul_def]
  refine Eq.trans (Finset.sum_congr rfl fun a ha => ?_) (h.trans ?_)
  · have := Finset.mem_range.1 ha
    rw [← NF.bubLU_comm, ← bubLU_comp]
    congr 3
    push_cast [Nat.cast_sub (by omega : a ≤ d)]; ring
  · split_ifs
    · exact bubLU_id RD k sc lam l
    · exact map_zero _

theorem cRs_zero : cRs RD k sc lam i l 0 = 1 := by
  simp only [cRs, Nat.cast_zero, add_zero]; rw [ccwU_deg0]; exact bubRU_id RD k sc lam l

theorem wRs_zero : wRs RD k sc lam i l 0 = 1 := by
  simp only [wRs, Nat.cast_zero, add_zero]; rw [cwU_deg0]; exact bubRU_id RD k sc lam l

theorem cLs_zero : cLs RD k sc lam i l 0 = 1 := by
  simp only [cLs, Nat.cast_zero, add_zero]; rw [ccwU_deg0]; exact bubLU_id RD k sc lam l

theorem wLs_zero : wLs RD k sc lam i l 0 = 1 := by
  simp only [wLs, Nat.cast_zero, add_zero]; rw [cwU_deg0]; exact bubLU_id RD k sc lam l

end Seq

/-! ## The case `i = j` -/

section Same

variable (lam : X) (i : I)

/-- The coefficients `(e + 1) x^e` of `1/(1 - x t)²`. -/
abbrev τsame (e : ℕ) : End ((pres RD k sc).obj (ob RD lam [up i])) :=
  (e + 1) • NF.dotsU (pres RD k sc) lam (up i) e

theorem slideA_same_real (α : ℕ) (hα : 0 ≤ -ip RD i lam - 1 + α) :
    cRs RD k sc lam i (up i) α = sconv (cLs RD k sc lam i (up i)) (τsame RD k sc lam i) α := by
  have h := prop33_ccw_same RD k sc lam i α hα
  rw [lin_bubR_eq] at h
  rw [cRs, h, sconv]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  have := Finset.mem_range.1 hℓ
  rw [lin_bubL_eq, End.mul_def, τsame, Linear.smul_comp, NF.bubLU_comm,
    show α + 1 - ℓ = α - ℓ + 1 by omega]

theorem slideB_same_real (β : ℕ) (hβ : 0 ≤ ip RD i (wt RD lam [up i]) - 1 + β) :
    wLs RD k sc lam i (up i) β = sconv (τsame RD k sc lam i) (wRs RD k sc lam i (up i)) β := by
  have h := prop33_cw_same RD k sc lam i β hβ
  rw [lin_bubL_eq] at h
  rw [wLs, h, sconv, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  have := Finset.mem_range.1 hℓ
  rw [lin_bubR_eq, End.mul_def, τsame, Linear.comp_smul, show β + 1 - 1 - ℓ = β - ℓ by omega,
    show β - (β - ℓ) = ℓ by omega, show β + 1 - (β - ℓ) = ℓ + 1 by omega]

theorem slides_same (lam : X) (i : I) :
    (∀ α, cRs RD k sc lam i (up i) α = sconv (cLs RD k sc lam i (up i)) (τsame RD k sc lam i) α) ∧
      ∀ β, wLs RD k sc lam i (up i) β = sconv (τsame RD k sc lam i) (wRs RD k sc lam i (up i)) β := by
  have hN : ip RD i (wt RD lam [up i]) = 2 + ip RD i lam := by rw [ip_wt_up, A_self]
  by_cases hn : 0 ≤ ip RD i lam
  · have hB : ∀ β, wLs RD k sc lam i (up i) β = sconv (τsame RD k sc lam i) (wRs RD k sc lam i (up i)) β :=
      fun β => slideB_same_real RD k sc lam i β (by omega)
    exact ⟨transfer_left _ _ _ _ _ (sconv_cRs_wRs RD k sc lam i (up i)) (sconv_cLs_wLs RD k sc lam i (up i))
      hB (wRs_zero RD k sc lam i (up i)), hB⟩
  · have hA : ∀ α, cRs RD k sc lam i (up i) α = sconv (cLs RD k sc lam i (up i)) (τsame RD k sc lam i) α :=
      fun α => slideA_same_real RD k sc lam i α (by omega)
    exact ⟨hA, transfer_right _ _ _ _ _ (sconv_cRs_wRs RD k sc lam i (up i))
      (sconv_cLs_wLs RD k sc lam i (up i)) hA (cLs_zero RD k sc lam i (up i))⟩

end Same

/-- **KL III Proposition 3.3, first display, `i = j`, all degrees**: for every `α ≥ 0`
(the bubble on the left-hand side may be a fake bubble),
`ccw_{-⟨i,λ⟩-1+α} ⊗ E_i = ∑_{ℓ=0}^{α} (α + 1 - ℓ) (E_i ⊗ ccw_{-⟨i,λ+i_X⟩-1+ℓ}) x^{α-ℓ}`. -/
theorem prop33_ccw_same_all (lam : X) (i : I) (α : ℕ) :
    (pres RD k sc).lin (bubR RD k lam [up i] (ccwL RD k lam i (-ip RD i lam - 1 + α))) =
      ∑ ℓ ∈ Finset.range (α + 1), (α + 1 - ℓ) •
        ((pres RD k sc).lin (bubL RD k lam [up i]
            (ccwL RD k (wt RD lam [up i]) i (-ip RD i (wt RD lam [up i]) - 1 + ℓ))) ≫
          NF.dotsU (pres RD k sc) lam (up i) (α - ℓ)) := by
  rw [lin_bubR_eq]
  refine ((slides_same RD k sc lam i).1 α).trans ?_
  rw [sconv]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  have := Finset.mem_range.1 hℓ
  rw [lin_bubL_eq, End.mul_def, τsame, Linear.smul_comp, NF.bubLU_comm,
    show α + 1 - ℓ = α - ℓ + 1 by omega]

/-- **KL III Proposition 3.3, second display, `i = j`, all degrees**: for every `α ≥ 0`,
`E_i ⊗ cw_{⟨i,λ+i_X⟩-1+α} = ∑_{ℓ=0}^{α} (α + 1 - ℓ) (cw_{⟨i,λ⟩-1+ℓ} ⊗ E_i) x^{α-ℓ}`. -/
theorem prop33_cw_same_all (lam : X) (i : I) (α : ℕ) :
    (pres RD k sc).lin (bubL RD k lam [up i]
        (cwL RD k (wt RD lam [up i]) i (ip RD i (wt RD lam [up i]) - 1 + α))) =
      ∑ ℓ ∈ Finset.range (α + 1), (α + 1 - ℓ) •
        ((pres RD k sc).lin (bubR RD k lam [up i] (cwL RD k lam i (ip RD i lam - 1 + ℓ))) ≫
          NF.dotsU (pres RD k sc) lam (up i) (α - ℓ)) := by
  rw [lin_bubL_eq]
  refine ((slides_same RD k sc lam i).2 α).trans ?_
  rw [sconv, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  have := Finset.mem_range.1 hℓ
  rw [lin_bubR_eq, End.mul_def, τsame, Linear.comp_smul, show α + 1 - 1 - ℓ = α - ℓ by omega,
    show α - (α - ℓ) = ℓ by omega, show α + 1 - ℓ = α - ℓ + 1 by omega]

/-! ## The case `i · j = -1` -/

section Adj

variable (lam : X) (i j : I)





end Adj



/-! ## The case `i · j = 0` -/

section Orth

variable (lam : X) (i j : I)





end Orth



/-! ## Proposition 3.4 in all degrees -/

theorem cw_left_expand_all (lam : X) (i : I) (α c : ℕ) :
    (pres RD k sc).lin (bubL RD k lam [up i]
        (cwL RD k (wt RD lam [up i]) i (ip RD i lam + 1 + ((α : ℤ) - c)))) ≫
        NF.dotsU (pres RD k sc) lam (up i) c =
      ∑ ℓ ∈ Finset.range (α + 1 - c), (α + 1 - c - ℓ) •
        (NF.bubRU (pres RD k sc) lam (up i) (NF.cwU (pres RD k sc) lam i (ip RD i lam - 1 + ℓ)) ≫
          NF.dotsU (pres RD k sc) lam (up i) (α - ℓ)) := by
  have hN : ip RD i (wt RD lam [up i]) = 2 + ip RD i lam := by rw [ip_wt_up, A_self]
  by_cases hc : c ≤ α
  · have e : ip RD i lam + 1 + ((α : ℤ) - c) = ip RD i (wt RD lam [up i]) - 1 + ((α - c : ℕ) : ℤ) := by
      rw [hN]; push_cast [Nat.cast_sub hc]; ring
    rw [e, prop33_cw_same_all, Preadditive.sum_comp, show α - c + 1 = α + 1 - c by omega]
    refine Finset.sum_congr rfl fun ℓ hℓ => ?_
    have := Finset.mem_range.1 hℓ
    rw [Linear.smul_comp, Category.assoc, NF.dotsU_add, lin_bubR_eq,
      show α - c - ℓ + c = α - ℓ by omega]
  · rw [lin_bubL_eq, lin_cwL_eq_zero RD k sc _ i _ (by omega), bubLU_zero, Limits.zero_comp,
      show α + 1 - c = 0 by omega, Finset.sum_range_zero]

theorem ccw_right_expand_all (lam : X) (i : I) (α c : ℕ) :
    (pres RD k sc).lin (bubR RD k lam [up i] (ccwL RD k lam i (-ip RD i lam - 1 + ((α : ℤ) - c)))) ≫
        NF.dotsU (pres RD k sc) lam (up i) c =
      ∑ j ∈ Finset.range (α + 1 - c), (α + 1 - c - j) •
        (NF.bubLU (pres RD k sc) lam (up i) (NF.ccwU (pres RD k sc) (wt RD lam [up i]) i
            (-ip RD i (wt RD lam [up i]) - 1 + j)) ≫ NF.dotsU (pres RD k sc) lam (up i) (α - j)) := by
  by_cases hc : c ≤ α
  · have e : -ip RD i lam - 1 + ((α : ℤ) - c) = -ip RD i lam - 1 + ((α - c : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hc]; ring
    rw [e, prop33_ccw_same_all, Preadditive.sum_comp, show α - c + 1 = α + 1 - c by omega]
    refine Finset.sum_congr rfl fun ℓ hℓ => ?_
    have := Finset.mem_range.1 hℓ
    rw [Linear.smul_comp, Category.assoc, NF.dotsU_add, lin_bubL_eq,
      show α - c - ℓ + c = α - ℓ by omega]
  · rw [lin_bubR_eq, lin_ccwL_eq_zero RD k sc _ i _ (by omega), bubRU_zero, Limits.zero_comp,
      show α + 1 - c = 0 by omega, Finset.sum_range_zero]

/-- **KL III Proposition 3.4, first display, `i = j`, all degrees**: for every `α ≥ 0`,
`cw_{⟨i,λ⟩-1+α} ⊗ E_i = (E_i ⊗ cw_{⟨i,λ⟩+1+(α-2)}) x² - 2 (E_i ⊗ cw_{⟨i,λ⟩+1+(α-1)}) x +
E_i ⊗ cw_{⟨i,λ⟩+1+α}`. -/
theorem prop34_cw_same_all (lam : X) (i : I) (α : ℕ) :
    (pres RD k sc).lin (bubR RD k lam [up i] (cwL RD k lam i (ip RD i lam - 1 + α))) =
      (pres RD k sc).lin (bubL RD k lam [up i]
          (cwL RD k (wt RD lam [up i]) i (ip RD i lam + 1 + ((α : ℤ) - 2)))) ≫
          NF.dotsU (pres RD k sc) lam (up i) 2 -
        2 • ((pres RD k sc).lin (bubL RD k lam [up i]
          (cwL RD k (wt RD lam [up i]) i (ip RD i lam + 1 + ((α : ℤ) - 1)))) ≫
          NF.dotsU (pres RD k sc) lam (up i) 1) +
        (pres RD k sc).lin (bubL RD k lam [up i]
          (cwL RD k (wt RD lam [up i]) i (ip RD i lam + 1 + α))) := by
  have h₀ := cw_left_expand_all RD k sc lam i α 0
  simp only [Nat.cast_zero, sub_zero, NF.dotsU_zero, Category.comp_id, Nat.sub_zero] at h₀
  have h₂ := cw_left_expand_all RD k sc lam i α 2
  have h₁ := cw_left_expand_all RD k sc lam i α 1
  simp only [Nat.cast_ofNat, Nat.cast_one] at h₂ h₁
  rw [h₂, h₁, h₀, show α + 1 - 2 = α - 1 by omega, show α + 1 - 1 = α by omega]
  have h := second_difference (fun ℓ => NF.bubRU (pres RD k sc) lam (up i) (NF.cwU (pres RD k sc) lam i (ip RD i lam - 1 + ℓ)) ≫
    NF.dotsU (pres RD k sc) lam (up i) (α - ℓ)) α
  simp only [Nat.sub_self, NF.dotsU_zero, Category.comp_id] at h
  rw [lin_bubR_eq, h.symm]

/-- **KL III Proposition 3.4, second display, `i = j`, all degrees**: for every `α ≥ 0`,
`E_i ⊗ ccw_{-⟨i,λ+i_X⟩-1+α} = (ccw_{-⟨i,λ⟩-1+(α-2)} ⊗ E_i) x² -
2 (ccw_{-⟨i,λ⟩-1+(α-1)} ⊗ E_i) x + ccw_{-⟨i,λ⟩-1+α} ⊗ E_i`. -/
theorem prop34_ccw_same_all (lam : X) (i : I) (α : ℕ) :
    (pres RD k sc).lin (bubL RD k lam [up i]
        (ccwL RD k (wt RD lam [up i]) i (-ip RD i (wt RD lam [up i]) - 1 + α))) =
      (pres RD k sc).lin (bubR RD k lam [up i] (ccwL RD k lam i (-ip RD i lam - 1 + ((α : ℤ) - 2)))) ≫
          NF.dotsU (pres RD k sc) lam (up i) 2 -
        2 • ((pres RD k sc).lin (bubR RD k lam [up i]
          (ccwL RD k lam i (-ip RD i lam - 1 + ((α : ℤ) - 1)))) ≫ NF.dotsU (pres RD k sc) lam (up i) 1) +
        (pres RD k sc).lin (bubR RD k lam [up i] (ccwL RD k lam i (-ip RD i lam - 1 + α))) := by
  have h₀ := ccw_right_expand_all RD k sc lam i α 0
  simp only [Nat.cast_zero, sub_zero, NF.dotsU_zero, Category.comp_id, Nat.sub_zero] at h₀
  have h₂ := ccw_right_expand_all RD k sc lam i α 2
  have h₁ := ccw_right_expand_all RD k sc lam i α 1
  simp only [Nat.cast_ofNat, Nat.cast_one] at h₂ h₁
  rw [h₂, h₁, h₀, show α + 1 - 2 = α - 1 by omega, show α + 1 - 1 = α by omega]
  have h := second_difference (fun j => NF.bubLU (pres RD k sc) lam (up i) (NF.ccwU (pres RD k sc) (wt RD lam [up i]) i
    (-ip RD i (wt RD lam [up i]) - 1 + j)) ≫ NF.dotsU (pres RD k sc) lam (up i) (α - j)) α
  simp only [Nat.sub_self, NF.dotsU_zero, Category.comp_id] at h
  rw [lin_bubL_eq, h.symm]



end Categorification.KL3.Diagram.CLQ

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.FundamentalBraidCorners

/-!
# Spanning diagrams of the fundamental crossed corners

In the fundamental type A₁ calculation of Webster, arXiv:1309.3796v2,
Proposition 7.11, the crossing bigon and the violating relation bound the
number of dots on the unique black strand in the crossed bimodule.
-/

noncomputable section
namespace Categorification.Stendhal.FundamentalCorner
open KLR KLRAlgebra TypeA Equiv MvPolynomial BraidedStendhalAlgebra
local notation "ν" => ({()} : Multiset Unit)
local notation "μ" => stendhalWeight 2 ν
local notation "R" => KLRAlgebra ℚ (stendhalQ Q wt) μ
local notation "V" => ViolQuotient ℚ Q wt ν

private theorem redBlackBigon (j : ℕ) (h : j + 1 < Multiset.card μ) (s : Seq μ) (r : Fin 2)
    (hr : s.lbl ⟨j,by omega⟩ = .inr r) (hi : s.lbl ⟨j+1,h⟩ = .inl ()) :
    (ψ j * ψ j * e s : R) = x ⟨j+1,h⟩ * e s := by
  have key := KLRAlgebra.ψ_sq (Q := stendhalQ Q wt) j h s
  have hv : (![KLRAlgebra.x ⟨j, by omega⟩, KLRAlgebra.x ⟨j+1,h⟩] : Fin 2 → R) =
      fun a => KLRAlgebra.x (![⟨j,by omega⟩,⟨j+1,h⟩] a) := by
    funext a; fin_cases a <;> rfl
  rw [hi,hr] at key
  simp only [reduceCtorEq,↓reduceIte] at key
  rw [stendhalQ_inr_inl,hv,KLRAlgebra.ncEval_eq_pol] at key
  simpa [wt,rename_X,pol_X] using key

private theorem middleDot (s : Seq μ) (r : Fin 2)
    (hr : s.lbl ⟨0,by decide⟩ = .inr r) (hi : s.lbl ⟨1,by decide⟩ = .inl ())
    (hv : IsViolated (sadj (Multiset.card μ) 0 • s)) :
    braidProject (x ⟨1,by decide⟩ * e s) = 0 := by
  rw [← redBlackBigon 0 (by decide) s r hr hi, mul_assoc, ψ_mul_e, map_mul,map_mul]
  rw [show braidProject (e (sadj (Multiset.card μ) 0 • s)) = 0 from violMk_e hv,zero_mul,mul_zero]

private theorem crossedMiddleDot :
    braidProject (x ⟨1,by decide⟩ * e crossedMiddle) = 0 :=
  middleDot crossedMiddle 1 rfl rfl (by unfold IsViolated; decide +kernel)

private theorem firstMiddleDot :
    braidProject (x ⟨1,by decide⟩ * e middle) = 0 :=
  middleDot middle 0 rfl rfl (by unfold IsViolated; decide +kernel)

private theorem bottomDoubleDot :
    braidProject (x ⟨2,by decide⟩ ^ 2 * e crossedTerminal) = 0 := by
  let b : Fin (Multiset.card μ) := ⟨2,by decide⟩
  let c : Fin (Multiset.card μ) := ⟨1,by decide⟩
  have sl : (x b * ψ 1 : R) = ψ 1 * x c :=
    (x_mul_ψ_of_nodup (by simp [stendhalWeight] : Multiset.Nodup μ) b 1).trans (by rfl)
  have he : sadj (Multiset.card μ) 1 • crossedTerminal = crossedMiddle := by decide +kernel
  change braidProject (x b ^ 2 * e crossedTerminal) = 0
  rw [pow_two,mul_assoc,← redBlackBigon 1 (by decide) crossedTerminal 0 rfl rfl,
    ← mul_assoc,← mul_assoc,sl,mul_assoc,mul_assoc,ψ_mul_e,he,← mul_assoc (x c),map_mul,map_mul]
  rw [show braidProject (x c * e crossedMiddle) = 0 from crossedMiddleDot,zero_mul,mul_zero]

private theorem corner_span (s t : Seq μ) (γ : List ℕ) (hγ : IsReduced (Multiset.card μ) γ)
    (ht : wordProd (Multiset.card μ) γ • s = t) (b : Fin (Multiset.card μ))
    (hr : ∀ p, p ≠ b → (s.lbl p).isRight) (d : ℕ)
    (hz : braidProject (ψw γ * x b ^ d * e s) = 0) (z : V) :
    braidProject (e t) * z * braidProject (e s) ∈ Submodule.span ℚ
      (Set.range fun n : Fin d => braidProject (ψw γ * x b ^ (n : ℕ) * e s)) := by
  have hp := fundamentalBraidCorner_mem_span s t γ hγ ht z
  refine (Submodule.span_le.mpr ?_) hp
  rintro _ ⟨u,rfl⟩
  change braidProject (ψw γ * pol (monomial u 1) * e s) ∈ _
  by_cases hu : ∃ p, p ≠ b ∧ u p ≠ 0
  · obtain ⟨p,hpb,hpu⟩ := hu
    have h0 := ofKLR_std_eq_zero (k := ℚ) (Q := Q) (Λ := wt) γ u s p (hr p hpb) hpu
    have hh : braidProject (ψw γ * pol (monomial u 1) * e s) = 0 :=
      (congrArg (violMk ℚ Q wt ν) h0).trans (map_zero _)
    rw [hh]
    exact Submodule.zero_mem _
  have hmono : u = Finsupp.single b (u b) := by
    apply Finsupp.support_subset_singleton.mp
    intro p hp
    by_contra h
    exact hu ⟨p,by simpa using h,Finsupp.mem_support_iff.mp hp⟩
  rw [hmono,← X_pow_eq_monomial,map_pow,pol_X]
  by_cases hlt : u b < d
  · exact Submodule.subset_span ⟨⟨u b,hlt⟩,rfl⟩
  obtain ⟨n,hn⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hlt)
  have hc : Commute (x b : R) (e s) := x_mul_e b s
  rw [hn,pow_add,mul_assoc,mul_assoc,(hc.pow_left n).eq,
    ← mul_assoc (x b ^ d), ← mul_assoc, map_mul,← mul_assoc (ψw γ) (x b ^ d) (e s),hz,zero_mul]
  exact Submodule.zero_mem _

private theorem reducedSmall (γ : List ℕ) (hm : ∀ j ∈ γ, j + 1 < 3)
    (hl : γ.length = invCount 3 (wordProd 3 γ)) : IsReduced (Multiset.card μ) γ := by
  constructor
  · exact hm
  · rw [length_eq_invCount]
    exact hl

private theorem middleEndDot :
    braidProject (ψw [1,0] * x ⟨2,by decide⟩ * e crossedTerminal) = 0 := by
  let c : Fin (Multiset.card μ) := ⟨1,by decide⟩
  have htop : wordProd (Multiset.card μ) [1,0] • crossedTerminal = middle := by decide +kernel
  have sl := x_mul_ψw_of_nodup (k := ℚ) (Q := stendhalQ Q wt)
    (by simp [stendhalWeight] : Multiset.Nodup μ) c [1,0]
  have hb : (wordProd (Multiset.card μ) [1,0])⁻¹ c = ⟨2,by decide⟩ := by decide +kernel
  rw [hb] at sl
  rw [← sl,mul_assoc,ψw_mul_e,htop,← mul_assoc,map_mul,show braidProject (x c * e middle) = 0 from firstMiddleDot,zero_mul]

/-- For the two fundamental red strands in Webster v2, Proposition 7.11,
both mixed corners across their interchange are spanned by the undotted
crossing diagram. -/
theorem fundamentalBraid_mixed_span (z : V) :
    (∃ a : ℚ, braidProject (e middle) * z * braidProject (e crossedTerminal) =
      a • braidProject (ψ 1 * ψ 0 * e crossedTerminal)) ∧
    (∃ a : ℚ, braidProject (e terminal) * z * braidProject (e crossedMiddle) =
      a • braidProject (ψ 0 * ψ 1 * e crossedMiddle)) := by
  have h₁ := corner_span crossedTerminal middle [1,0] (reducedSmall _ (by decide) (by decide +kernel))
    (by decide +kernel) ⟨2,by decide⟩ (by decide +kernel) 1 (by simpa only [pow_one] using middleEndDot) z
  have h₂ := corner_span crossedMiddle terminal [0,1] (reducedSmall _ (by decide) (by decide +kernel))
    (by decide +kernel) ⟨1,by decide⟩ (by decide +kernel) 1 (by
      rw [pow_one,mul_assoc,map_mul,crossedMiddleDot,mul_zero]) z
  rw [Set.range_unique] at h₁ h₂
  constructor
  · obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp h₁
    exact ⟨a,by simpa [ψw] using ha.symm⟩
  · obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp h₂
    exact ⟨a,by simpa [ψw] using ha.symm⟩

/-- Each terminal-to-terminal diagram across the red crossing in the
fundamental calculation of Webster v2, Proposition 7.11, is a linear
combination of the crossing and its single black-dot decoration. -/
theorem fundamentalBraid_terminal_span (z : V) :
    ∃ a b : ℚ, braidProject (e terminal) * z * braidProject (e crossedTerminal) =
      a • braidProject (ψ 0 * e crossedTerminal) +
      b • braidProject (ψ 0 * x ⟨2,by decide⟩ * e crossedTerminal) := by
  have h := corner_span crossedTerminal terminal [0] (reducedSmall _ (by decide) (by decide +kernel))
    (by decide +kernel) ⟨2,by decide⟩ (by decide +kernel) 2 (by
      rw [mul_assoc,map_mul,bottomDoubleDot,mul_zero]) z
  apply (exists_congr fun _ => exists_congr fun _ => eq_comm).mp
  apply Submodule.mem_span_pair.mp
  refine (Submodule.span_le.mpr ?_) h
  rintro _ ⟨i,rfl⟩
  apply Submodule.subset_span
  fin_cases i <;> simp [ψw]

/-- Left multiplication by the mixed crossing on the two fundamental
terminal generators and the mixed generator in Webster v2, Proposition 7.11.
The terminal corner complex has successive matrices `(0,1)ᵀ` and `(1,0)`. -/
theorem fundamentalBraid_terminal_differentials :
    braidProject (ψ 1) * braidProject (ψ 1 * ψ 0 * e crossedTerminal) =
      braidProject (ψ 0 * x ⟨2,by decide⟩ * e crossedTerminal) ∧
    braidProject (ψ 1) * braidProject (ψ 0 * e crossedTerminal) =
      braidProject (ψ 1 * ψ 0 * e crossedTerminal) ∧
    braidProject (ψ 1) * braidProject (ψ 0 * x ⟨2,by decide⟩ * e crossedTerminal) = 0 := by
  have he : sadj (Multiset.card μ) 0 • crossedTerminal = terminal := by decide +kernel
  have hb : (ψ 1 * ψ 1 * e terminal : R) = x ⟨2,by decide⟩ * e terminal :=
    redBlackBigon 1 (by decide) terminal 1 rfl rfl
  have slide : (x ⟨2,by decide⟩ * ψ 0 : R) = ψ 0 * x ⟨2,by decide⟩ :=
    x_mul_ψ _ _ (by decide) (by decide)
  constructor
  · rw [← map_mul,← mul_assoc,← mul_assoc]
    apply congrArg braidProject
    calc
      ψ 1 * ψ 1 * ψ 0 * e crossedTerminal = ψ 1 * ψ 1 * (e terminal * ψ 0) := by rw [mul_assoc,ψ_mul_e,he]
      _ = x ⟨2,by decide⟩ * (e terminal * ψ 0) := by rw [← mul_assoc,hb,mul_assoc]
      _ = ψ 0 * x ⟨2,by decide⟩ * e crossedTerminal := by rw [← he,← ψ_mul_e,← mul_assoc,slide]
  constructor
  · rw [← map_mul,← mul_assoc]
  · rw [← map_mul,← mul_assoc,← mul_assoc]
    simpa [ψw] using middleEndDot

end Categorification.Stendhal.FundamentalCorner

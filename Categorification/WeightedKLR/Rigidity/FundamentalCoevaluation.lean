/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CoevaluationTrace
import Categorification.WeightedKLR.RedStrands.FundamentalCorner
import Categorification.WeightedKLR.RedStrands.FirstWeightBoundary
import Categorification.WeightedKLR.RedStrands.FundamentalPrefixCorners
import Categorification.WeightedKLR.Induction.Restriction
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Abelian.Projective.Dimension

/-!
# The simple head of the terminal loading projective

For two fundamental type A₁ factors over `ℚ`, this file computes the
simple quotient of the projective at the terminal loading. The general
cut-trace criterion is modeled on Webster, arXiv:1309.3796v2, Lemma 7.3.
-/

noncomputable section

namespace Categorification.Stendhal.FundamentalCorner

open KLR StendhalAlgebraAllOrders TypeA Equiv MulOpposite

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

local notation "ν" => ({()} : Multiset Unit)
local notation "μ" => stendhalWeight 2 ν
local notation "T" => TensorProductAlgebra ℚ Q wt ν
local notation "ρ" => canWord (Multiset.card μ)
local notation "π" => project.comp (ofKLR ℚ Q wt ν)

private abbrev black : Fin (Multiset.card μ) := ⟨2, by decide⟩

/-- The loading idempotent with the black strand after both reds. -/
abbrev terminalIdem : T := project (e terminal)

/-- The loading idempotent with the black strand between the reds. -/
abbrev middleIdem : T := project (e middle)

local notation "p" => terminalIdem
local notation "q" => middleIdem
local notation "d" => project (x black * e terminal)

private theorem hp : IsIdempotentElem p := IsIdempotentElem.map (by simp [IsIdempotentElem, e_mul_e]) project
private theorem hq : IsIdempotentElem q := IsIdempotentElem.map (by simp [IsIdempotentElem, e_mul_e]) project

private theorem p_ord : p = TensorProductAlgebra.mk Q wt ν
    (StendhalAlgebra.e terminal terminal_ordered) := by
  apply congrArg (TensorProductAlgebra.mk Q wt ν)
  apply Subtype.ext
  exact (e_mul_redOrderedIdem terminal).trans (ite_eq_left terminal_ordered)

private theorem middleOrdered : IsRedOrdered middle := by
  unfold IsRedOrdered
  decide +kernel

private theorem q_ord : q = TensorProductAlgebra.mk Q wt ν
    (StendhalAlgebra.e middle middleOrdered) := by
  apply congrArg (TensorProductAlgebra.mk Q wt ν)
  apply Subtype.ext
  exact (e_mul_redOrderedIdem middle).trans (ite_eq_left middleOrdered)

/-- The two surviving loading idempotents sum to the unit in the one-black block. -/
theorem terminalIdem_add_middleIdem : p + q = 1 := by
  classical
  have hsum : (∑ s : Seq μ, project (e s)) = 1 := by
    change (∑ s : Seq μ, π (KLRAlgebra.e s)) = 1
    rw [← map_sum, KLRAlgebra.sum_e, map_one]
  have hf (s : Seq μ) : project (e s) = (if s = terminal then p else 0) +
      (if s = middle then q else 0) := by
    by_cases ht : s = terminal
    · subst s
      simp only [eq_self, ↓reduceIte, show terminal ≠ middle by decide +kernel, add_zero]
    by_cases hm : s = middle
    · subst s
      simp only [eq_self, ↓reduceIte, show middle ≠ terminal by decide +kernel, zero_add]
    simp only [ht, hm, ↓reduceIte, add_zero]
    by_cases ho : IsRedOrdered s
    · have hv : IsViolated s := by
        have hclass : ∀ t : Seq μ, IsRedOrdered t → ¬ IsViolated t →
            t = terminal ∨ t = middle := by
          intro t ht hv
          obtain ⟨r, hr⟩ := (FirstWeight.boundaryEquiv () 2).surjective ⟨t, ht, hv⟩
          have hr' : (FirstWeight.boundaryAt () 2 r).val = t := congrArg Subtype.val hr
          fin_cases r
          · exact Or.inr (hr'.symm.trans (by
              apply Subtype.ext
              funext j
              fin_cases j <;> rfl))
          · exact Or.inl (hr'.symm.trans (by
              apply Subtype.ext
              funext j
              fin_cases j <;> rfl))
        exact not_not.mp (fun hn => (hclass s ho hn).elim ht hm)
      change (StendhalAlgebra.violatedIdeal ℚ Q wt ν).ringCon.mk' (orderProjection Q wt ν (e s)) = 0
      rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']
      refine TwoSidedIdeal.subset_span ⟨s, ho, hv, Subtype.ext ?_⟩
      exact (e_mul_redOrderedIdem s).trans (ite_eq_left ho)
    · change TensorProductAlgebra.mk Q wt ν (orderProjection Q wt ν (e s)) = 0
      rw [show orderProjection Q wt ν (e s) = 0 by
        apply Subtype.ext
        exact (e_mul_redOrderedIdem s).trans (ite_eq_right ho), map_zero]
  rw [Finset.sum_congr rfl (fun s _ => hf s), Finset.sum_add_distrib] at hsum
  simpa only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] using hsum

private theorem nilWord : ρ 1 = [] :=
  List.length_eq_zero_iff.mp (by rw [length_canWord, length_one])

private theorem dot_pow (n : ℕ) (hn : 2 ≤ n) :
    project (x black ^ n * e terminal) = 0 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm, pow_add, mul_assoc, map_mul, dot_sq_zero, mul_zero]

private theorem diagSpan (a : T) : p * a * p ∈ Submodule.span ℚ ({p, d} : Set T) := by
  classical
  let W := Submodule.span ℚ ({p, d} : Set T)
  have ha : a ∈ Submodule.span ℚ (Set.range (tensorProductTerm wordSpec Q wt)) := by
    rw [span_tensorProductTerm wordSpec Q wt]
    trivial
  induction ha using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨b, rfl⟩ := hz
    let term := tensorProductTerm wordSpec Q wt b
    have hL : p * term = if b.1.2.1 • b.1.1 = terminal then term else 0 := by
      rw [p_ord]
      unfold term tensorProductTerm
      rw [← map_mul, e_mul_stendhalTerm]
      split_ifs <;> simp only [map_zero]
    have hR : term * p = if b.1.1 = terminal then term else 0 := by
      rw [p_ord]
      unfold term tensorProductTerm
      rw [← map_mul, stendhalTerm_mul_e]
      split_ifs <;> simp only [map_zero]
    rw [show tensorProductTerm wordSpec Q wt b = term from rfl, hL]
    split_ifs with htop
    · rw [hR]
      split_ifs with hbot
      · have hw : b.1.2.1 = 1 :=
          NonInteracting.smul_left_injective (by simp [stendhalWeight]) b.1.1
            (by rw [one_smul, htop, hbot])
        let n := b.1.2.2 black
        have hs : b.1.2.2 = Finsupp.single black n := by
          apply Finsupp.support_subset_singleton.mp
          intro j hj
          have h := b.2.2.2.1 j hj
          change (b.1.1.lbl j).isLeft = true at h
          rw [hbot] at h
          have hblack : ∀ j : Fin (Multiset.card μ), (terminal.lbl j).isLeft → j = black := by
            decide +kernel
          exact Finset.mem_singleton.mpr (hblack j h)
        have ix : b.1 = (terminal, 1, Finsupp.single black n) := Prod.ext hbot (Prod.ext hw hs)
        have ht : term = project (x black ^ n * e terminal) := by
          change TensorProductAlgebra.mk Q wt ν (stendhalTerm Q wt (fun w => (wordSpec w).2) b) = _
          have hh : term = π (KLRAlgebra.stdElt ρ b.1) := by
            apply congrArg (TensorProductAlgebra.mk Q wt ν)
            apply Subtype.ext
            exact ((Subsemigroup.mem_corner_iff isIdempotentElem_redOrderedIdem).mp
              (stendhalTerm Q wt (fun w => (wordSpec w).2) b).2).2.symm
          change term = _
          rw [hh, ix]
          simp only [KLRAlgebra.stdElt, nilWord, KLRAlgebra.ψw, List.map_nil, List.prod_nil,
            one_mul, ← MvPolynomial.X_pow_eq_monomial, map_mul, map_pow, KLRAlgebra.pol_X, x, e]
          rfl
        rw [ht]
        by_cases hn : 2 ≤ n
        · rw [dot_pow n hn]
          exact W.zero_mem
        · interval_cases n
          · rw [pow_zero, one_mul]
            exact Submodule.subset_span (by left; rfl)
          · rw [pow_one]
            exact Submodule.subset_span (by right; rfl)
      · exact W.zero_mem
    · rw [zero_mul]
      exact W.zero_mem
  | zero => rw [mul_zero, zero_mul]; exact W.zero_mem
  | add x y _ _ hx hy => simpa only [mul_add, add_mul] using W.add_mem hx hy
  | smul c x _ hx => simpa only [mul_smul_comm, smul_mul_assoc] using W.smul_mem c hx

private theorem d_left : p * d = d := by
  rw [← map_mul, ← mul_assoc]
  have he : e terminal * (e terminal : StendhalAlgebraAllOrders ℚ Q wt ν) = e terminal := by
    simp [e_mul_e]
  have hc : (e terminal : StendhalAlgebraAllOrders ℚ Q wt ν) * x black = x black * e terminal := by
    simpa only [← map_mul, e, x] using congrArg (ofKLR ℚ Q wt ν)
      (KLRAlgebra.e_mul_x (Q := stendhalQ Q wt) black terminal)
  rw [hc, mul_assoc, he]

private theorem d_right : d * p = d := by
  rw [← map_mul, mul_assoc, e_mul_e, ite_eq_left rfl]

private theorem d_mul_d : d * d = 0 := by
  rw [← map_mul]
  have hc : (e terminal : StendhalAlgebraAllOrders ℚ Q wt ν) * x black = x black * e terminal := by
    simpa only [← map_mul, e, x] using congrArg (ofKLR ℚ Q wt ν)
      (KLRAlgebra.e_mul_x (Q := stendhalQ Q wt) black terminal)
  rw [← mul_assoc _ (x black) (e terminal), mul_assoc (x black) (e terminal), hc,
    mul_assoc (x black) (x black * e terminal) (e terminal),
    mul_assoc (x black) (e terminal) (e terminal), e_mul_e, ite_eq_left rfl,
    ← mul_assoc, ← pow_two]
  exact dot_sq_zero

private theorem terminalNotViolated : ¬ IsViolated terminal := by
  unfold IsViolated
  decide +kernel

/-- The one-dimensional representation supported on the loading with the
single black strand to the right of both fundamental reds. -/
def terminalCharacter : T →ₐ[ℚ] ℚ :=
  FirstWeight.boundaryCharacter Q wt (by intro r; simp [wt])
    terminal terminal_ordered terminalNotViolated

@[simp] theorem terminalCharacter_terminalIdem : terminalCharacter p = 1 := by
  simp [terminalCharacter, p_ord, FirstWeight.boundaryCharacter_e]

@[simp] theorem terminalCharacter_middleIdem : terminalCharacter q = 0 := by
  simp [terminalCharacter, q_ord, FirstWeight.boundaryCharacter_e,
    show middle ≠ terminal by decide +kernel]

private theorem character_dot : terminalCharacter d = 0 := by
  have h := congrArg terminalCharacter d_mul_d
  simpa only [map_mul, map_zero, mul_eq_zero, or_self] using h

/-- The trace of the middle loading in the terminal projective. -/
abbrev fundamentalCutTrace : Submodule Tᵐᵒᵖ (rIdeal p) :=
  coevaluationTrace (fun _ : Unit => q)

private theorem dot_mem_trace : (⟨d, d_left⟩ : rIdeal p) ∈ fundamentalCutTrace := by
  have hswap : sadj (Multiset.card μ) 1 • terminal = middle := by decide +kernel
  obtain ⟨z, hz, heq⟩ := bigon_mem_coevaluationTrace Q wt ν (fun _ : Unit => q)
    terminal 1 (by decide) () 1 rfl rfl () (by
      rw [hswap]
      rfl)
  have hval : z.val = d := by
    rw [e, x, ← map_mul]
    simp only [wt, Finsupp.single_eq_same, pow_one] at heq
    exact heq.trans (by rfl)
  exact (Subtype.ext hval : z = ⟨d, d_left⟩) ▸ hz

private theorem right_corner_coordinates (x : rIdeal p) :
    ∃ b : ℚ, x.val * p = terminalCharacter x.val • p + b • d := by
  obtain ⟨a, b, h⟩ := Submodule.mem_span_pair.mp (diagSpan x.val)
  rw [x.property] at h
  have ha := congrArg terminalCharacter h
  rw [map_add, map_smul, map_smul, character_dot, smul_zero, add_zero,
    map_mul, terminalCharacter_terminalIdem, mul_one, smul_eq_mul, mul_one] at ha
  exact ⟨b, ha ▸ h.symm⟩

/-- For the two fundamental representations over `ℚ`, the kernel of the
terminal loading character on the terminal projective is exactly the
trace of the loading between the two red strands. -/
theorem mem_fundamentalCutTrace_iff (x : rIdeal p) :
    x ∈ fundamentalCutTrace ↔ terminalCharacter x.val = 0 := by
  constructor
  · intro hx
    exact coevaluationTrace_le_characterKernel _ terminalCharacter.toRingHom
      (fun _ => terminalCharacter_middleIdem) hx
  · intro hx
    obtain ⟨b, hb⟩ := right_corner_coordinates x
    rw [hx, zero_smul, zero_add] at hb
    let y : rIdeal p := ⟨x.val * q, by change p * (x.val * q) = x.val * q; rw [← mul_assoc, x.property]⟩
    have hy : y ∈ fundamentalCutTrace := Submodule.subset_span
      ⟨(), by change (x.val * q) * q = x.val * q; rw [mul_assoc, hq.eq]⟩
    have hd : b • (⟨d, d_left⟩ : rIdeal p) ∈ fundamentalCutTrace := by
      let c := op (algebraMap ℚ T b)
      have hc : c • (⟨d, d_left⟩ : rIdeal p) = b • (⟨d, d_left⟩ : rIdeal p) := by
        apply Subtype.ext
        change d * algebraMap ℚ T b = b • d
        exact (Algebra.commutes b d).symm.trans (Algebra.smul_def b d).symm
      exact hc ▸ fundamentalCutTrace.smul_mem c dot_mem_trace
    have hsum : b • (⟨d, d_left⟩ : rIdeal p) + y = x := by
      apply Subtype.ext
      change b • d + x.val * q = x.val
      rw [← hb, ← mul_add, terminalIdem_add_middleIdem, mul_one]
    exact hsum ▸ fundamentalCutTrace.add_mem hd hy

/-- Any terminal ideal vector with nonzero character generates the terminal ideal. -/
theorem exists_mul_eq_terminalIdem (x : rIdeal p) (hx : terminalCharacter x.val ≠ 0) :
    ∃ z : T, x.val * z = p := by
  let a := terminalCharacter x.val
  obtain ⟨b, hb⟩ := right_corner_coordinates x
  let v : T := a⁻¹ • p + (-(a⁻¹ * a⁻¹ * b)) • d
  refine ⟨p * v, ?_⟩
  rw [← mul_assoc, hb]
  change (a • p + b • d) * v = p
  dsimp only [v]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hp.eq, d_left,
    d_right, d_mul_d, smul_zero, add_zero, smul_add, smul_smul]
  have h₀ : a⁻¹ * a = 1 := inv_mul_cancel₀ hx
  have h₁ : a⁻¹ * b + (-(a⁻¹ * a⁻¹ * b)) * a = 0 := by
    rw [neg_mul, show a⁻¹ * a⁻¹ * b * a = (a⁻¹ * a) * (a⁻¹ * b) by ring,
      h₀, one_mul, add_neg_cancel]
  rw [h₀, one_smul, add_assoc, ← add_smul, h₁, zero_smul, add_zero]

/-- The coefficient of the terminal generator in the simple quotient. -/
def terminalCoefficient : rIdeal p →ₗ[ℚ] ℚ where
  toFun z := terminalCharacter z.val
  map_add' x y := terminalCharacter.map_add x.val y.val
  map_smul' c x := terminalCharacter.toLinearMap.map_smul c x.val

/-- The coefficient of the terminal generating vector is one. -/
@[simp] theorem terminalCoefficient_generator :
    terminalCoefficient (⟨p, hp.eq⟩ : rIdeal p) = 1 :=
  terminalCharacter_terminalIdem

/-- The coefficient map is surjective onto the ground field. -/
theorem terminalCoefficient_surjective : Function.Surjective terminalCoefficient := by
  intro c
  refine ⟨c • (⟨p, hp.eq⟩ : rIdeal p), ?_⟩
  rw [map_smul, terminalCoefficient_generator, smul_eq_mul, mul_one]

/-- The ground-field coefficient descends precisely through the smaller cut trace. -/
theorem terminalCoefficient_ker :
    LinearMap.ker terminalCoefficient = fundamentalCutTrace.restrictScalars ℚ := by
  ext x
  exact (mem_fundamentalCutTrace_iff x).symm

/-- The cut trace is the unique simple-quotient kernel of the terminal
right loading projective for two fundamental type A₁ factors over `ℚ`. -/
theorem fundamentalCutTrace_eq_iff_simpleQuotient (N : Submodule Tᵐᵒᵖ (rIdeal p)) :
    N = fundamentalCutTrace ↔ IsSimpleModule Tᵐᵒᵖ (rIdeal p ⧸ N) :=
  coevaluationTrace_eq_iff_simpleQuotient hp _ terminalCharacter.toRingHom
    terminalCharacter_terminalIdem (fun _ => terminalCharacter_middleIdem)
    (fun x => (mem_fundamentalCutTrace_iff x).mpr) exists_mul_eq_terminalIdem N

section Resolution

local notation "C" => project (ψ 1)
local notation "u" => C * q
local notation "v" => C * p

private theorem cross_middle : u = p * C := by
  have hswap : sadj (Multiset.card μ) 1 • middle = terminal := by decide +kernel
  have h := congrArg π (KLRAlgebra.ψ_mul_e (Q := stendhalQ Q wt) 1 middle)
  simpa only [hswap, map_mul, AlgHom.comp_apply, ψ, e] using h

/-- The mixed crossing starting at the terminal loading ends at the middle loading. -/
theorem terminalCrossing_eq_middle_mul : v = q * C := by
  have hswap : sadj (Multiset.card μ) 1 • terminal = middle := by decide +kernel
  have h := congrArg π (KLRAlgebra.ψ_mul_e (Q := stendhalQ Q wt) 1 terminal)
  simpa only [hswap, map_mul, AlgHom.comp_apply, ψ, e] using h

/-- Crossing to the middle loading and back gives the terminal black dot. -/
theorem mixedBigon_terminal : u * v = d := by
  have h := ψ_sq_red_black (Q := Q) (Λ := wt) 1 (by decide) terminal () 1 rfl rfl
  simp only [wt, Finsupp.single_eq_same, pow_one] at h
  calc
    u * v = C * C * p := by
      rw [mul_assoc C q v, terminalCrossing_eq_middle_mul, ← mul_assoc q q, hq.eq, ← terminalCrossing_eq_middle_mul, ← mul_assoc]
    _ = d := by rw [← map_mul, ← map_mul, h]

/-- The differential between the two loading projectives is the single mixed
crossing, with terminal loading on top and middle loading on the bottom. -/
def fundamentalResolutionMap : rIdeal q →ₗ[Tᵐᵒᵖ] rIdeal p where
  toFun x := ⟨u * x.val, by
    change p * (u * x.val) = u * x.val
    rw [← mul_assoc, cross_middle, ← mul_assoc, hp.eq]⟩
  map_add' x y := Subtype.ext (mul_add u x.val y.val)
  map_smul' a x := Subtype.ext (mul_assoc u x.val a.unop).symm

/-- The mixed crossing embeds the middle loading projective. -/
theorem fundamentalResolutionMap_injective : Function.Injective fundamentalResolutionMap := by
  apply (injective_iff_map_eq_zero fundamentalResolutionMap).2
  intro x hx
  have h : u * x.val = 0 := congrArg Subtype.val hx
  have ⟨⟨a, ha⟩, _, ⟨b, hb⟩⟩ := fundamental_middle_corner_coordinates x.val
  change q * x.val * q = a • q at ha
  change q * x.val * p = b • v at hb
  rw [x.property] at ha hb
  have hd : u * x.val * p = b • d := by
    rw [mul_assoc, hb, mul_smul_comm, mixedBigon_terminal]
  have hu : u * x.val * q = a • u := by
    rw [mul_assoc, ha, mul_smul_comm, mul_assoc, hq.eq]
  rw [h, zero_mul] at hd hu
  have hdn : d ≠ 0 := dot_ne_zero
  have hun : u ≠ 0 := fun hz => hdn (by rw [← mixedBigon_terminal, hz, zero_mul])
  have ha0 : a = 0 := (smul_eq_zero.mp hu.symm).resolve_right hun
  have hb0 : b = 0 := (smul_eq_zero.mp hd.symm).resolve_right hdn
  apply Subtype.ext
  change x.val = 0
  calc
    x.val = x.val * p + x.val * q := by rw [← mul_add, terminalIdem_add_middleIdem, mul_one]
    _ = 0 := by rw [ha, hb, ha0, hb0, zero_smul, zero_smul, zero_add]

/-- The image of the mixed crossing is exactly the smaller-cut trace. -/
theorem fundamentalResolutionMap_range :
    LinearMap.range fundamentalResolutionMap = fundamentalCutTrace := by
  ext x
  rw [mem_fundamentalCutTrace_iff]
  constructor
  · rintro ⟨y, rfl⟩
    change terminalCharacter (u * y.val) = 0
    rw [map_mul, map_mul, terminalCharacter_middleIdem, mul_zero, zero_mul]
  · intro hx
    obtain ⟨a, ha⟩ := right_corner_coordinates x
    rw [hx, zero_smul, zero_add] at ha
    obtain ⟨b, hb⟩ := (fundamental_middle_corner_coordinates x.val).2.1
    change p * x.val * q = b • u at hb
    rw [x.property] at hb
    let y : rIdeal q := ⟨b • q + a • v, by
      change q * (b • q + a • v) = b • q + a • v
      rw [mul_add, mul_smul_comm, hq.eq, mul_smul_comm, terminalCrossing_eq_middle_mul, ← mul_assoc, hq.eq]⟩
    refine ⟨y, Subtype.ext ?_⟩
    change u * (b • q + a • v) = x.val
    rw [mul_add, mul_smul_comm, mul_assoc C q q, hq.eq, mul_smul_comm, mixedBigon_terminal,
      ← hb, ← ha, ← mul_add, add_comm q p, terminalIdem_add_middleIdem, mul_one]

/-- The fundamental terminal-character simple admits a length-one resolution
by the two loading projectives. This gives a rank-one benchmark for the
projective-resolution method in Webster, arXiv:1309.3796v2, §8.1. -/
theorem fundamentalProjectiveResolution :
    Module.Projective Tᵐᵒᵖ (rIdeal q) ∧
    Module.Projective Tᵐᵒᵖ (rIdeal p) ∧
    Function.Injective fundamentalResolutionMap ∧
    Function.Exact fundamentalResolutionMap fundamentalCutTrace.mkQ ∧
    Function.Surjective fundamentalCutTrace.mkQ := by
  refine ⟨rIdeal_projective hq, rIdeal_projective hp, fundamentalResolutionMap_injective,
    LinearMap.exact_iff.mpr ?_, fundamentalCutTrace.mkQ_surjective⟩
  rw [fundamentalResolutionMap_range, Submodule.ker_mkQ]

/-- The middle loading annihilates the terminal simple. -/
theorem middleIdem_smul_terminalSimple (z : rIdeal p ⧸ fundamentalCutTrace) :
    op q • z = 0 := by
  obtain ⟨x, rfl⟩ := fundamentalCutTrace.mkQ_surjective z
  rw [← map_smul]
  apply (Submodule.Quotient.mk_eq_zero fundamentalCutTrace).mpr
  apply (mem_fundamentalCutTrace_iff _).mpr
  change terminalCharacter (x.val * q) = 0
  rw [map_mul, terminalCharacter_middleIdem, mul_zero]

/-- Applying `Hom(-, L)` to the two-term resolution gives zero in degree
one, since the middle projective is generated on an idempotent killing `L`. -/
theorem fundamentalMiddleHom_eq_zero
    (f : rIdeal q →ₗ[Tᵐᵒᵖ] (rIdeal p ⧸ fundamentalCutTrace)) : f = 0 := by
  let g : rIdeal q := ⟨q, hq.eq⟩
  have hg : op q • g = g := Subtype.ext hq.eq
  have hfg : f g = 0 := by
    calc
      f g = f (op q • g) := congrArg f hg.symm
      _ = op q • f g := f.map_smul _ _
      _ = 0 := middleIdem_smul_terminalSimple _
  ext x
  have hx : op x.val • g = x := Subtype.ext x.property
  rw [← hx, map_smul, hfg, smul_zero, LinearMap.zero_apply]

open CategoryTheory

/-- The terminal simple as a right module. -/
abbrev fundamentalTerminalSimple : ModuleCat.{0} Tᵐᵒᵖ :=
  ModuleCat.of Tᵐᵒᵖ (rIdeal p ⧸ fundamentalCutTrace)

/-- The mixed-crossing resolution, packaged as a short complex. -/
def fundamentalResolution : ShortComplex (ModuleCat.{0} Tᵐᵒᵖ) :=
  ShortComplex.mk (ModuleCat.ofHom fundamentalResolutionMap)
    (ModuleCat.ofHom fundamentalCutTrace.mkQ)
    (by ext x; exact fundamentalProjectiveResolution.2.2.2.1.apply_apply_eq_zero x)

/-- The mixed-crossing complex is short exact. -/
theorem fundamentalResolution_shortExact : fundamentalResolution.ShortExact := by
  let : Mono fundamentalResolution.f :=
    (ModuleCat.mono_iff_injective _).2 fundamentalResolutionMap_injective
  let : Epi fundamentalResolution.g :=
    (ModuleCat.epi_iff_surjective _).2 fundamentalCutTrace.mkQ_surjective
  exact ⟨(ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2
    fundamentalProjectiveResolution.2.2.2.1⟩

/-- The terminal simple has no self-extensions in positive degrees. -/
theorem fundamentalTerminalSimple_ext_eq_zero (n : ℕ) (hn : 0 < n)
    (x : Abelian.Ext fundamentalTerminalSimple fundamentalTerminalSimple n) : x = 0 := by
  let : Module.Projective Tᵐᵒᵖ (rIdeal q) := rIdeal_projective hq
  let : Module.Projective Tᵐᵒᵖ (rIdeal p) := rIdeal_projective hp
  let : Projective fundamentalResolution.X₁ := by
    change Projective (ModuleCat.of Tᵐᵒᵖ (rIdeal q))
    infer_instance
  let : Projective fundamentalResolution.X₂ := by
    change Projective (ModuleCat.of Tᵐᵒᵖ (rIdeal p))
    infer_instance
  by_cases h : n = 1
  · subst n
    obtain ⟨y, hy⟩ := Abelian.Ext.contravariant_sequence_exact₃
      fundamentalResolution_shortExact fundamentalTerminalSimple x
      (Abelian.Ext.eq_zero_of_hasProjectiveDimensionLT _ 1 (by rfl)) (Nat.add_zero 1)
    have hy0 : Abelian.Ext.homEquiv₀ y = 0 := by
      ext z
      exact LinearMap.congr_fun
        (fundamentalMiddleHom_eq_zero (Abelian.Ext.homEquiv₀ y).hom) z
    rw [← Abelian.Ext.mk₀_homEquiv₀_apply y, hy0, Abelian.Ext.mk₀_zero,
      Abelian.Ext.comp_zero] at hy
    exact hy.symm
  · let : HasProjectiveDimensionLT fundamentalTerminalSimple 2 :=
      fundamentalResolution_shortExact.hasProjectiveDimensionLT_X₃ 1 inferInstance inferInstance
    exact Abelian.Ext.eq_zero_of_hasProjectiveDimensionLT x 2 (by omega)

end Resolution

end Categorification.Stendhal.FundamentalCorner

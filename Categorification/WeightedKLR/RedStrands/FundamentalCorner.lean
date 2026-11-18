/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FirstWeightProjectives
import Categorification.WeightedKLR.RedStrands.OrderProjection
import Mathlib.LinearAlgebra.Matrix.Notation
import Categorification.KLR.DividedPowerIdempotents
/-!
# The terminal corner with two fundamental red strands

For the first black weight of the tensor square of the fundamental sl₂ module,
the two red-ordered, nonviolating words act on a three-dimensional space.
Crossing the last two strands sends the first basis vector to the second and
the second to the third. Squaring this crossing detects the terminal black dot
in Webster’s violating quotient (arXiv:1309.3796v2, (4.2) and Lemma 4.36).
-/

noncomputable section
namespace Categorification.Stendhal.FundamentalCorner
open KLR StendhalAlgebraAllOrders TypeA Matrix
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

/-- Two fundamental red weights in type A₁. -/
abbrev wt (_ : Fin 2) : Unit →₀ ℕ := Finsupp.single () 1
/-- The type A₁ KLR polynomial. -/
abbrev Q := KLR.klQ (k := ℚ) (⊥ : SimpleGraph Unit)
local notation "μ" => stendhalWeight 2 ({()} : Multiset Unit)
local notation "M" => Matrix (Fin 3) (Fin 3) ℚ
/-- The terminal sequence, with the black strand to the right of both reds. -/
def terminal : Seq μ := KLRAlgebra.Seq.ofList [.inr 0,.inr 1,.inl ()] (by decide)
/-- The black strand between the two fundamental red strands. -/
def middle : Seq μ := KLRAlgebra.Seq.ofList [.inr 0,.inl (),.inr 1] (by decide)
private def idemM (s : Seq μ) : M := if s = terminal then !![1,0,0;0,0,0;0,0,1]
    else if s = middle then !![0,0,0;0,1,0;0,0,0] else 0
private def dotM (a : Fin (Multiset.card μ)) : M := if a.val = 2 then !![0,0,0;0,0,0;1,0,0] else 0
private def crossM (j : ℕ) : M := if j = 1 then !![0,0,0;1,0,0;0,1,0] else 0
private def gen : Gen μ → M
  | .idem s => idemM s
  | .dot a => dotM a
  | .cross j => crossM j

private noncomputable local instance enumSeq : Fintype (Seq μ) :=
  inferInstanceAs (Fintype {f : Fin (Multiset.card μ) → Unit ⊕ Fin 2 // Finset.univ.val.map f = μ})

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

private theorem respects {x y : FreeAlgebra ℚ (Gen μ)} (h : Rel ℚ Q wt {()} x y) :
    FreeAlgebra.lift ℚ gen x = FreeAlgebra.lift ℚ gen y := by
  cases h with
  | red_dot a s hr =>
    simp only [map_mul,map_zero,fe,fx,FreeAlgebra.lift_ι_apply,gen]
    revert hr s a
    decide +kernel +revert
  | red_cross j hj i h₁ h₂ =>
    simp only [map_mul,map_zero,fe,fψ,FreeAlgebra.lift_ι_apply,gen]
    change j + 1 < 3 at hj
    have hle : j ≤ 1 := by omega
    interval_cases j <;> revert h₁ h₂ i <;> decide +kernel +revert
  | klr h =>
    cases h with
    | idem_mul s t =>
      simp only [map_mul,fe,apply_ite,map_zero,FreeAlgebra.lift_ι_apply,gen]
      revert s t
      decide +kernel +revert
    | idem_sum =>
      simp only [map_sum,fe,map_one,FreeAlgebra.lift_ι_apply,gen]
      rw [Subsingleton.elim (Seq.instFintype : Fintype (Seq μ)) enumSeq]
      decide +kernel +revert
    | dot_idem a s =>
      simp only [map_mul,fx,fe,FreeAlgebra.lift_ι_apply,gen]
      revert a s
      decide +kernel +revert
    | cross_idem j s =>
      simp only [map_mul,fψ,fe,FreeAlgebra.lift_ι_apply,gen]
      by_cases h : j = 1
      · subst j
        revert s
        decide +kernel +revert
      · simp [crossM,h]
    | cross_zero j hj =>
      simp [fψ,gen,crossM,show j ≠ 1 by change 3 ≤ j + 1 at hj; omega]
    | dot_dot a b =>
      simp only [map_mul,fx,FreeAlgebra.lift_ι_apply,gen]
      revert a b
      decide +kernel +revert
    | cross_cross j l h =>
      by_cases hj : j = 1
      · simp [fψ,gen,crossM,show l ≠ 1 by omega]
      · simp [fψ,gen,crossM,hj]
    | dot_cross a j h₁ h₂ =>
      simp only [map_mul,fψ,fx,FreeAlgebra.lift_ι_apply,gen]
      by_cases hj : j = 1
      · subst j
        clear h₁ h₂
        revert a
        decide +kernel +revert
      · simp [crossM,hj]
    | dot_cross_left j hj s | dot_cross_right j hj s =>
      simp only [map_mul,map_sub,apply_ite,map_zero,fe,fψ,fx,FreeAlgebra.lift_ι_apply,gen]
      change j + 1 < 3 at hj
      have hle : j ≤ 1 := by omega
      interval_cases j <;> revert s <;> decide +kernel +revert
    | braid j hj s =>
      have hij : j = 0 := by change j + 2 < 3 at hj; omega
      subst j
      have hn (s : Seq μ) : s.lbl ⟨0,by decide⟩ ≠ s.lbl ⟨2,by decide⟩ := by
        revert s
        decide +kernel +revert
      simp [hn, fψ,gen,crossM]
    | cross_sq j hj s =>
      have hle : j ≤ 1 := by change j + 1 < 3 at hj; omega
      simp only [map_mul, apply_ite, map_zero, fe, fψ, fx, FreeAlgebra.lift_ι_apply, gen, ncEval_map]
      have hEval (a b : M) (c t : Unit ⊕ Fin 2) :
          ncEval ![a,b] (stendhalQ Q wt c t) =
            match c,t with
            | .inl _, .inl _ => 1
            | .inl _, .inr _ => a
            | .inr _, .inl _ => b
            | _, _ => 0 := by
        cases c <;> cases t
        · simpa only [stendhalQ, Q, KLR.klQ, SimpleGraph.bot_adj, ite_false] using
            (NonInteracting.ncEval_one (k := ℚ) ![a,b])
        all_goals
          simp [stendhalQ, wt, MvPolynomial.X,
            List.ofFn_succ, ncEval]
      interval_cases j <;>
        try simp_rw [show ∀ (a b : Fin (Multiset.card μ)),
          (fun r => FreeAlgebra.lift ℚ gen (![fx ℚ μ a, fx ℚ μ b] r)) = ![dotM a, dotM b]
          from fun a b => funext fun r => by fin_cases r <;> simp [fx,gen], hEval]
      all_goals revert s
      all_goals decide +kernel +revert

private def evalAll : StendhalAlgebraAllOrders ℚ Q wt {()} →ₐ[ℚ] M :=
  RingQuot.liftAlgHom ℚ ⟨FreeAlgebra.lift ℚ gen, fun _ _ h => respects h⟩

private theorem evalAll_mk (z : FreeAlgebra ℚ (Gen μ)) :
    evalAll (RingQuot.mkAlgHom ℚ (Rel ℚ Q wt {()}) z) = FreeAlgebra.lift ℚ gen z :=
  RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _

private theorem evalAll_e (s : Seq μ) : evalAll (e s) = idemM s := by
  rw [e, KLRAlgebra.e, ofKLR_mk, evalAll_mk]
  simp [fe,gen]

private theorem evalAll_x (a : Fin (Multiset.card μ)) : evalAll (x a) = dotM a := by
  rw [x, KLRAlgebra.x, ofKLR_mk, evalAll_mk]
  simp [fx,gen]

theorem terminal_ordered : IsRedOrdered terminal := by unfold IsRedOrdered; decide +kernel
private theorem middle_ordered : IsRedOrdered middle := by unfold IsRedOrdered; decide +kernel
private theorem evalAll_order : evalAll (redOrderedIdem ℚ Q wt {()}) = 1 := by
  classical
  rw [redOrderedIdem, map_sum]
  simp_rw [evalAll_e]
  have hind (s : Seq μ) :
      idemM s = (if s = terminal then idemM terminal else 0) +
        (if s = middle then idemM middle else 0) := by
    by_cases h : s = terminal
    · subst s
      simp [show terminal ≠ middle by decide +kernel]
    by_cases h' : s = middle
    · subst s
      simp [show middle ≠ terminal by decide +kernel]
    · simp [idemM,h,h']
  rw [Finset.sum_congr rfl (fun s _ => hind s)]
  rw [Finset.sum_add_distrib]
  simp [terminal_ordered,middle_ordered]
  decide +kernel

private def evalCorner : StendhalAlgebra ℚ Q wt {()} →ₐ[ℚ] M where
  toFun z := evalAll z.1
  map_one' := evalAll_order
  map_mul' _ _ := map_mul _ _ _
  map_zero' := map_zero _
  map_add' _ _ := map_add _ _ _
  commutes' c := by
    change evalAll (c • redOrderedIdem ℚ Q wt {()}) = _
    rw [map_smul, evalAll_order, Algebra.smul_def,mul_one]

private def eval : TensorProductAlgebra ℚ Q wt {()} →ₐ[ℚ] M :=
  (StendhalAlgebra.violatedIdeal ℚ Q wt {()}).ringCon.liftₐ evalCorner (by
    apply (TwoSidedIdeal.ringCon_le_iff (J := TwoSidedIdeal.ker evalCorner.toRingHom)).mp
    apply TwoSidedIdeal.span_le.2
    rintro _ ⟨s, _, hv, rfl⟩
    apply (TwoSidedIdeal.mem_ker _).mpr
    change evalAll (e s) = 0
    rw [evalAll_e]
    obtain ⟨h,hv⟩ := hv
    by_cases hs : s = terminal
    · subst s
      exact Bool.noConfusion hv
    by_cases hm : s = middle
    · subst s
      exact Bool.noConfusion hv
    simp [idemM,hs,hm])

/-- The map from diagrams in all red orders to the tensor product algebra. -/
abbrev project := (TensorProductAlgebra.mk Q wt {()}).comp (orderProjection Q wt {()})

private theorem eval_project (z : StendhalAlgebraAllOrders ℚ Q wt {()}) : eval (project z) = evalAll z := by
  change evalCorner (orderProjection Q wt {()} z) = _
  change evalAll (z * redOrderedIdem ℚ Q wt {()}) = _
  rw [map_mul,evalAll_order,mul_one]

/-- The terminal black dot survives in the violating quotient. -/
theorem dot_ne_zero : project (x ⟨2,by decide⟩ * e terminal) ≠ 0 := by
  intro h
  have he := congrArg eval h
  rw [eval_project, map_mul, evalAll_x,evalAll_e,map_zero] at he
  have hn : dotM ⟨2,of_decide_eq_true rfl⟩ * idemM terminal ≠ 0 := by decide +kernel
  exact hn he

private abbrev A := StendhalAlgebraAllOrders ℚ Q wt {()}
private abbrev T := TensorProductAlgebra ℚ Q wt {()}
private abbrev x₂ : A := x ⟨2, by decide⟩
private abbrev x₁ : A := x ⟨1, by decide⟩
private abbrev vword : Seq μ := sadj (Multiset.card μ) 0 • middle

private theorem kills_violated : project (e vword) = 0 := by
  let J := StendhalAlgebra.violatedIdeal ℚ Q wt {()}
  change J.ringCon.mk' (orderProjection Q wt {()} (e vword)) = 0
  rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']
  have ho : IsRedOrdered vword := by unfold IsRedOrdered; decide +kernel
  apply TwoSidedIdeal.subset_span
  refine ⟨vword, ho, ⟨by decide, by decide +kernel⟩, Subtype.ext ?_⟩
  change (e vword * redOrderedIdem ℚ Q wt {()} : A) = e vword
  simp [e_mul_redOrderedIdem,ho]

private theorem cross_e (j : ℕ) (s : Seq μ) :
    (ψ j * e s : A) = e (sadj (Multiset.card μ) j • s) * ψ j := by
  exact (map_mul _ _ _).symm.trans
    ((congrArg (ofKLR ℚ Q wt {()}) (KLRAlgebra.ψ_mul_e j s)).trans (map_mul _ _ _))

private theorem dot_comm (s : Seq μ) : Commute x₂ (e s) :=
  (show Commute (KLRAlgebra.x ⟨2,by decide⟩) (KLRAlgebra.e s :
    KLRAlgebra ℚ (stendhalQ Q wt) μ) from KLRAlgebra.x_mul_e _ _).map _

/-- The dot between the two red strands factors through a violated sequence. -/
theorem middle_dot_zero : project (x₁ * e middle) = 0 := by
  have h := ψ_sq_red_black (Q := Q) (Λ := wt) 0 (by decide) middle () 0 rfl rfl
  simp only [wt, Finsupp.single_eq_same, pow_one] at h
  rw [← h, mul_assoc, cross_e, map_mul, map_mul,kills_violated,zero_mul,mul_zero]

/-- Two dots on the terminal black strand vanish: the successive mixed bigons
factor through a word with the black strand left of both reds. -/
theorem dot_sq_zero : project (x₂ ^ 2 * e terminal) = 0 := by
  have h := ψ_sq_red_black (Q := Q) (Λ := wt) 1 (by decide) terminal () 1 rfl rfl
  have hm := ψ_sq_black_red (Q := Q) (Λ := wt) 1 (by decide) middle () 1 rfl rfl
  simp only [wt, Finsupp.single_eq_same, pow_one] at h hm
  have he : (e terminal * e terminal : A) = e terminal := by simp [e_mul_e]
  have hs : sadj (Multiset.card μ) 1 • terminal = middle := by decide +kernel
  have hx : (x₂ ^ 2 * e terminal : A) = (x₂ * e terminal) * (x₂ * e terminal) := by
    rw [pow_two, mul_assoc x₂ (e terminal), ← mul_assoc (e terminal), ← (dot_comm terminal).eq,
      mul_assoc x₂ (e terminal), he, mul_assoc]
  rw [hx, ← h]
  calc
    _ = project (ψ 1 * (ψ 1 * ψ 1 * e middle) * (ψ 1 * e terminal)) := by
      congr 1
      simp only [mul_assoc]
      rw [show (e terminal * (ψ 1 * (ψ 1 * e terminal)) : A) = ψ 1 * (ψ 1 * e terminal) by
        rw [← mul_assoc (ψ 1), h, ← mul_assoc, ← (dot_comm terminal).eq, mul_assoc, he]]
      rw [show (e middle * (ψ 1 * e terminal) : A) = ψ 1 * e terminal by
        rw [cross_e, hs, ← mul_assoc]; simp [e_mul_e]]
    _ = 0 := by rw [hm, map_mul, map_mul, middle_dot_zero,mul_zero,zero_mul]

end Categorification.Stendhal.FundamentalCorner

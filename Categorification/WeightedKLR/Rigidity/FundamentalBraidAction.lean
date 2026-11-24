/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.FundamentalBraidCorners

/-!
# The surviving matrix coefficients of the fundamental braid

In Webster, arXiv:1309.3796v2, Proposition 7.11, the braid applied
to the middle character is computed from the three projective terms
of its resolution. This representation detects the nonzero classes in
the off-order diagram corners entering that calculation.
-/

noncomputable section
namespace Categorification.Stendhal.FundamentalCorner
open KLR KLRAlgebra TypeA Matrix Equiv BraidedStendhalAlgebra MvPolynomial
local notation "ν" => ({()} : Multiset Unit)
local notation "μ" => stendhalWeight 2 ν
local notation "V" => ViolQuotient ℚ Q wt ν
private abbrev States := Fin 6
private abbrev Coords := States → ℚ
private abbrev Endo := Module.End ℚ Coords

private def select (p : States → Option States) : Endo where
  toFun z i := (p i).elim 0 z
  map_add' x y := by funext i; cases h : p i <;> simp [h]
  map_smul' c z := by funext i; cases h : p i <;> simp [h]

private def loadingAt : States → Seq μ := ![terminal,middle,terminal,crossedTerminal,crossedMiddle,crossedTerminal]
private def idemAction (s : Seq μ) : Endo := select fun i => if loadingAt i = s then some i else none
private def dotAction (a : Fin (Multiset.card μ)) : Endo :=
  if a.val = 2 then select ![none,none,some 0,none,none,some 3] else 0
private def crossingAction (j : ℕ) : Endo :=
  if j = 0 then select ![some 3,none,some 5,none,none,none]
  else if j = 1 then select ![none,some 0,some 1,none,some 3,some 4] else 0
private def generator : Gen μ → Endo
  | .idem s => idemAction s
  | .dot a => dotAction a
  | .cross j => crossingAction j

private noncomputable local instance enumerate : Fintype (Seq μ) :=
  inferInstanceAs (Fintype {f : Fin (Multiset.card μ) → Unit ⊕ Fin 2 // Finset.univ.val.map f = μ})

private theorem end_ext {a b : Endo} (h : ∀ i j : States, a (Pi.single i 1) j = b (Pi.single i 1) j) : a = b := by
  apply (Pi.basisFun ℚ States).ext
  intro i
  rw [Pi.basisFun_apply]
  exact _root_.funext (h i)

private theorem end_ext_iff {a b : Endo} : a = b ↔ ∀ i j : States, a (Pi.single i 1) j = b (Pi.single i 1) j :=
  ⟨fun h => h ▸ fun _ _ => rfl, end_ext⟩

private theorem respects {x y : FreeAlgebra ℚ (Gen μ)} (h : BraidedRel ℚ Q wt ν x y) :
    FreeAlgebra.lift ℚ generator x = FreeAlgebra.lift ℚ generator y := by
  cases h with
  | red_dot a s hr =>
    simp only [map_mul,map_zero,fe,fx,FreeAlgebra.lift_ι_apply,generator]
    apply end_ext
    revert hr s a
    decide +kernel +revert
  | klr h =>
    cases h with
    | idem_mul s t =>
      simp only [map_mul,fe,apply_ite,map_zero,FreeAlgebra.lift_ι_apply,generator,end_ext_iff]
      revert s t
      decide +kernel +revert
    | idem_sum =>
      simp only [map_sum,fe,map_one,FreeAlgebra.lift_ι_apply,generator]
      rw [Subsingleton.elim (Seq.instFintype : Fintype (Seq μ)) enumerate]
      apply end_ext
      decide +kernel +revert
    | dot_idem a s =>
      simp only [map_mul,fx,fe,FreeAlgebra.lift_ι_apply,generator]
      apply end_ext
      revert a s
      decide +kernel +revert
    | cross_idem j s =>
      simp only [map_mul,fψ,fe,FreeAlgebra.lift_ι_apply,generator]
      by_cases hj : j ≤ 1
      · interval_cases j <;> apply end_ext <;> revert s <;> decide +kernel +revert
      · simp [crossingAction,show j ≠ 0 by omega,show j ≠ 1 by omega]
    | cross_zero j hj =>
      change 3 ≤ j + 1 at hj
      simp [fψ,generator,crossingAction,show j ≠ 0 by omega,show j ≠ 1 by omega]
    | dot_dot a b =>
      simp only [map_mul,fx,FreeAlgebra.lift_ι_apply,generator]
      apply end_ext
      revert a b
      decide +kernel +revert
    | cross_cross j l h =>
      by_cases hj : j ≤ 1
      · have hl : l ≠ 0 ∧ l ≠ 1 := by omega
        simp [fψ,generator,crossingAction,hl.1,hl.2]
      · simp [fψ,generator,crossingAction,show j ≠ 0 by omega,show j ≠ 1 by omega]
    | dot_cross a j h₁ h₂ =>
      simp only [map_mul,fψ,fx,FreeAlgebra.lift_ι_apply,generator]
      by_cases hj : j ≤ 1
      · interval_cases j <;> apply end_ext <;> revert h₁ h₂ a <;> decide +kernel +revert
      · simp [crossingAction,show j ≠ 0 by omega,show j ≠ 1 by omega]
    | dot_cross_left j hj s | dot_cross_right j hj s =>
      simp only [map_mul,map_sub,apply_ite,map_zero,fe,fψ,fx,FreeAlgebra.lift_ι_apply,generator]
      change j + 1 < 3 at hj
      have hle : j ≤ 1 := by omega
      interval_cases j <;> simp only [end_ext_iff] <;> revert s <;> decide +kernel +revert
    | braid j hj s =>
      have he : j = 0 := by change j+2 < 3 at hj; omega
      subst j
      have hn (t : Seq μ) : t.lbl ⟨0,by decide⟩ ≠ t.lbl ⟨2,by decide⟩ := by revert t; decide +kernel +revert
      simp only [hn,map_mul,map_sub,fe,fψ,FreeAlgebra.lift_ι_apply,generator]
      apply end_ext
      revert s
      decide +kernel +revert
    | cross_sq j hj s =>
      have hle : j ≤ 1 := by change j + 1 < 3 at hj; omega
      simp only [map_mul,apply_ite,map_zero,fe,fψ,fx,FreeAlgebra.lift_ι_apply,generator,ncEval_map]
      have hEval (a b : Endo) (c t : Unit ⊕ Fin 2) :
          ncEval ![a,b] (stendhalQ Q wt c t) =
            match c,t with
            | .inl _, .inl _ => 1
            | .inl _, .inr _ => a
            | .inr _, .inl _ => b
            | _, _ => 0 := by
        cases c <;> cases t
        · simpa only [stendhalQ,Q,KLR.klQ,SimpleGraph.bot_adj,ite_false] using
            (NonInteracting.ncEval_one (k := ℚ) ![a,b])
        all_goals simp [stendhalQ,wt,MvPolynomial.X,List.ofFn_succ,ncEval]
      interval_cases j <;> try simp_rw [show ∀ a b : Fin (Multiset.card μ),
        (fun r => FreeAlgebra.lift ℚ generator (![fx ℚ μ a,fx ℚ μ b] r)) = ![dotAction a,dotAction b]
        from fun a b => funext fun r => by fin_cases r <;> simp [fx,generator], hEval]
      all_goals simp only [end_ext_iff]
      all_goals revert s
      all_goals decide +kernel +revert

private def affineAction : BraidedStendhalAlgebra ℚ Q wt ν →ₐ[ℚ] Endo :=
  RingQuot.liftAlgHom ℚ ⟨FreeAlgebra.lift ℚ generator, fun _ _ h => respects h⟩

private theorem affineAction_mk (z : FreeAlgebra ℚ (Gen μ)) :
    affineAction (RingQuot.mkAlgHom ℚ (BraidedRel ℚ Q wt ν) z) = FreeAlgebra.lift ℚ generator z :=
  RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _

private theorem affineAction_e (s : Seq μ) :
    affineAction (BraidedStendhalAlgebra.ofKLR ℚ Q wt ν (e s)) = idemAction s := by
  rw [e,ofKLR_mk,affineAction_mk]
  simp [fe,generator]

private def quotientAction : V →ₐ[ℚ] Endo := (violIdeal ℚ Q wt ν).ringCon.liftₐ affineAction (by
  apply (TwoSidedIdeal.ringCon_le_iff (J := TwoSidedIdeal.ker affineAction.toRingHom)).mp
  apply TwoSidedIdeal.span_le.mpr
  rintro _ ⟨s,hs,rfl⟩
  apply (TwoSidedIdeal.mem_ker _).mpr
  change affineAction _ = 0
  rw [affineAction_e]
  apply end_ext
  unfold IsViolated at hs
  revert hs s
  decide +kernel +revert)

private theorem action_e (s : Seq μ) :
    quotientAction (braidProject (e s)) = idemAction s := affineAction_e s

private theorem action_ψ (j : ℕ) :
    quotientAction (braidProject (ψ j)) = crossingAction j := by
  change affineAction (BraidedStendhalAlgebra.ofKLR ℚ Q wt ν (ψ j)) = _
  rw [ψ,ofKLR_mk,affineAction_mk]
  simp [fψ,generator]

private theorem action_x (a : Fin (Multiset.card μ)) :
    quotientAction (braidProject (x a)) = dotAction a := by
  change affineAction (BraidedStendhalAlgebra.ofKLR ℚ Q wt ν (x a)) = _
  rw [x,ofKLR_mk,affineAction_mk]
  simp [fx,generator]

private def entry (i j : States) : V →ₗ[ℚ] ℚ where
  toFun z := quotientAction z (Pi.single i 1) j
  map_add' a b := by rw [map_add]; rfl
  map_smul' c a := by rw [map_smul]; rfl

/-- The two terminal braid classes from Webster v2, Proposition 7.11's
fundamental resolution calculation, with zero dots and one dot. -/
def terminalBraidClasses : Fin 2 → V :=
  ![braidProject (ψ 0 * e crossedTerminal),braidProject (ψ 0 * x ⟨2,by decide⟩ * e crossedTerminal)]

private theorem terminalEntries (u : Fin 2) :
    entry 3 0 (terminalBraidClasses u) = (if u = 0 then 1 else 0) ∧
    entry 3 2 (terminalBraidClasses u) = (if u = 1 then 1 else 0) := by
  fin_cases u
  · change entry 3 0 (braidProject (ψ 0 * e crossedTerminal)) = 1 ∧
      entry 3 2 (braidProject (ψ 0 * e crossedTerminal)) = 0
    simp only [entry,LinearMap.coe_mk,AddHom.coe_mk,map_mul,action_ψ,action_e]
    decide +kernel
  · change entry 3 0 (braidProject (ψ 0 * x ⟨2,by decide⟩ * e crossedTerminal)) = 0 ∧
      entry 3 2 (braidProject (ψ 0 * x ⟨2,by decide⟩ * e crossedTerminal)) = 1
    simp only [entry,LinearMap.coe_mk,AddHom.coe_mk,map_mul,action_ψ,action_e,action_x]
    decide +kernel

/-- The undotted and dotted terminal-to-terminal classes across the red
crossing are linearly independent (Webster v2, Proposition 7.11, type A₁). -/
theorem fundamentalBraid_terminal_linearIndependent : LinearIndependent ℚ terminalBraidClasses := by
  apply Fintype.linearIndependent_iff.mpr
  intro c h u
  fin_cases u
  · simpa [Fin.sum_univ_two, (terminalEntries _).1] using congrArg (entry 3 0) h
  · simpa [Fin.sum_univ_two, (terminalEntries _).2] using congrArg (entry 3 2) h

/-- Each middle-to-terminal term in the resolution across a red crossing
has a surviving undotted crossing diagram (Webster v2, Proposition 7.11). -/
theorem fundamentalBraid_mixed_ne_zero :
    braidProject (ψ 1 * ψ 0 * e crossedTerminal) ≠ 0 ∧
    braidProject (ψ 0 * ψ 1 * e crossedMiddle) ≠ 0 := by
  have h₁ : entry 3 1 (braidProject (ψ 1 * ψ 0 * e crossedTerminal)) = 1 := by
    simp only [entry,LinearMap.coe_mk,AddHom.coe_mk,map_mul,action_ψ,action_e]
    decide +kernel
  have h₂ : entry 4 2 (braidProject (ψ 0 * ψ 1 * e crossedMiddle)) = 1 := by
    simp only [entry,LinearMap.coe_mk,AddHom.coe_mk,map_mul,action_ψ,action_e]
    decide +kernel
  constructor <;> intro h
  · simp [h] at h₁
  · simp [h] at h₂

end Categorification.Stendhal.FundamentalCorner

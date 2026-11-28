/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleBlackActionAdditiveQ
import Categorification.Diagrams.CLQ.RouquierInversionUp
import Categorification.TwoRep.CompletionSumInv
import Categorification.WeightedKLR.RedStrands.DoubleCLBlackAction

/-!
# Rouquier's invertibility conditions in the black action

Brundan, arXiv:1501.00350v1, (1.8) and (1.9), for the black action of Cautis–Lauda's `U_Q(g)`
(arXiv:1111.1431v3, Definition 1.1, `r = 1`; `CLQ.pres RD k sc`) on the violating quotients
(Webster, arXiv:1309.3796v3, §4.5, Theorem 4.28). The action of a 2-morphism (`blackMapQ`) is
additive and functorial, so the explicit inverses of `CLQ.sumInvTo_sigmaUp` and
`CLQ.sumInvFrom_sigmaUp` (Khovanov–Lauda, arXiv:0807.3250v1, Proposition 3.25, for the
adjunction `E_i ⊣ F_i` of the downward strands) pass to the black action
(`blackSumInvTo_sigmaUpQ`, `blackSumInvFrom_sigmaUpQ`) and to its additive idempotent
completion (`blackCompletedSumInvTo_sigmaUpQ`, `blackCompletedSumInvFrom_sigmaUpQ`).
-/

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams TwoRep

universe u v

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}} {k : Type*} [CommRing k]
  {sc : KL3.Diagram.CL.CLScalars C k}
  (P : Presentation (signature RD (fun r => (Λ r).val)) k)
  (hP : ∀ r : (CLQ.pres RD k sc).Rel,
    P.lin (blackMirrorLinear RD (fun r => (Λ r).val) ((CLQ.pres RD k sc).rel r)) = 0)

theorem blackMap_negQ {μ ν : X} {s t : List (Letter I)} (hs : wt RD μ s = ν)
    (ht : wt RD μ t = ν)
    (ψ : (CLQ.pres RD k sc).obj (ob RD μ s) ⟶ (CLQ.pres RD k sc).obj (ob RD μ t)) :
    blackMapQ P hP hs ht (-ψ) = -blackMapQ P hP hs ht ψ := by
  refine eq_neg_of_add_eq_zero_left ?_
  rw [← blackMap_addQ, neg_add_cancel, blackMap_zeroQ]

section Inversion

variable (i : I) (lam : X)

local notation "Sto" hn => CLQ.sumInvTo_sigmaUp (RD := RD) (k := k) (sc := sc) i lam hn
local notation "Sfrom" hn => CLQ.sumInvFrom_sigmaUp (RD := RD) (k := k) (sc := sc) i lam hn

/-- **Brundan (1.8) for `E_i ⊣ F_i` in the black action** (`⟨i, λ⟩ ≤ 0`): the image of
`CLQ.sumInvTo_sigmaUp`. -/
def blackSumInvTo_sigmaUpQ (hn : ip RD i lam ≤ 0) :
    SumInvTo (blackMapQ P hP (wt_dn_up RD i lam) (wt_up_dn RD i lam)
        (-NF.dg (CLQ.pres RD k sc) lam [dn i, up i] [up i, dn i] (CLQ.sigmaUpLs i)))
      (fun m => blackMapQ P hP (wt_dn_up RD i lam) (wt_nil RD lam) (CLQ.capUp RD k sc i lam m))
      (-ip RD i lam).toNat where
  f' := blackMapQ P hP _ _ (Sto hn).f'
  g' m := blackMapQ P hP _ _ ((Sto hn).g' m)
  total := by
    rw [← blackMap_idQ P hP (wt_dn_up RD i lam), ← (Sto hn).total, blackMap_addQ, blackMap_sumQ,
      blackMap_compQ P hP _ (wt_up_dn RD i lam)]
    congr 1
    exact Finset.sum_congr rfl fun m _ => (blackMap_compQ P hP _ (wt_nil RD lam) _ _ _).symm
  ff := by
    rw [← blackMap_compQ, (Sto hn).ff, blackMap_idQ]
  fg m hm := by
    rw [← blackMap_compQ, (Sto hn).fg m hm, blackMap_zeroQ]
  gf m hm := by
    rw [← blackMap_compQ, (Sto hn).gf m hm, blackMap_zeroQ]
  gg m m' hm hm' := by
    rw [← blackMap_compQ, (Sto hn).gg m m' hm hm']
    split_ifs
    · exact blackMap_idQ P hP _
    · exact blackMap_zeroQ P hP _ _

/-- **Brundan (1.9) for `E_i ⊣ F_i` in the black action** (`⟨i, λ⟩ ≥ 0`): the image of
`CLQ.sumInvFrom_sigmaUp`. -/
def blackSumInvFrom_sigmaUpQ (hn : 0 ≤ ip RD i lam) :
    SumInvFrom (blackMapQ P hP (wt_dn_up RD i lam) (wt_up_dn RD i lam)
        (-NF.dg (CLQ.pres RD k sc) lam [dn i, up i] [up i, dn i] (CLQ.sigmaUpLs i)))
      (fun m => blackMapQ P hP (wt_nil RD lam) (wt_up_dn RD i lam) (CLQ.cupUp RD k sc i lam m))
      (ip RD i lam).toNat where
  f' := blackMapQ P hP _ _ (Sfrom hn).f'
  g' m := blackMapQ P hP _ _ ((Sfrom hn).g' m)
  total := by
    rw [← blackMap_idQ P hP (wt_up_dn RD i lam), ← (Sfrom hn).total, blackMap_addQ,
      blackMap_sumQ, blackMap_compQ P hP _ (wt_dn_up RD i lam)]
    congr 1
    exact Finset.sum_congr rfl fun m _ => (blackMap_compQ P hP _ (wt_nil RD lam) _ _ _).symm
  ff := by
    rw [← blackMap_compQ, (Sfrom hn).ff, blackMap_idQ]
  fg m hm := by
    rw [← blackMap_compQ, (Sfrom hn).fg m hm, blackMap_zeroQ]
  gf m hm := by
    rw [← blackMap_compQ, (Sfrom hn).gf m hm, blackMap_zeroQ]
  gg m m' hm hm' := by
    rw [← blackMap_compQ, (Sfrom hn).gg m m' hm hm']
    split_ifs
    · exact blackMap_idQ P hP _
    · exact blackMap_zeroQ P hP _ _

/-- Brundan (1.8) in the completed black action: `blackSumInvTo_sigmaUpQ` on additive
idempotent completions. -/
def blackCompletedSumInvTo_sigmaUpQ (hn : ip RD i lam ≤ 0) :=
  (blackSumInvTo_sigmaUpQ P hP i lam hn).completion

/-- Brundan (1.9) in the completed black action: `blackSumInvFrom_sigmaUpQ` on additive
idempotent completions. -/
def blackCompletedSumInvFrom_sigmaUpQ (hn : 0 ≤ ip RD i lam) :=
  (blackSumInvFrom_sigmaUpQ P hP i lam hn).completion

end Inversion

end Categorification.Stendhal.DoubleDiagram

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleBlackActionAdditive
import Categorification.Diagrams.KL3.Decompositions

/-!
# The commutation relations of `𝒰` in the black action

Webster, arXiv:1309.3796v3, §4.5, Theorem 4.28, applied to the decompositions of
Khovanov–Lauda, arXiv:0807.3250v1, Propositions 3.25 and 3.26. The action of a
Khovanov–Lauda 2-morphism on the violating quotients (`blackMap`) is additive and
functorial, so the decomposition data of Proposition 3.25 and the inverse sideways crossings
of Proposition 3.26 pass to the black action on each violating quotient:

* for `n = ⟨i, λ⟩ ≥ 0`, the action of `E_i F_i 1_λ` decomposes as the action of
  `F_i E_i 1_λ` plus `n` copies of the identity (`blackSumDecompEF`);
* for `n ≤ 0`, the action of `F_i E_i 1_λ` decomposes as the action of `E_i F_i 1_λ` plus
  `-n` copies of the identity (`blackSumDecompFE`);
* for `i ≠ j`, the actions of `E_i F_j 1_μ` and `F_j E_i 1_μ` are isomorphic
  (`blackCrossIso`).

These are decompositions in the preadditive category of functors between violating
quotients. They are the input for the `𝒰` commutation relations on modules used in the proof
of Proposition 5.5. The ungraded morphisms of `U` are used; the degree shifts of KL III (3.60)
play no role here.
-/

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe u v

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}} {k : Type*} [CommRing k]
  (P : Presentation (signature RD (fun r => (Λ r).val)) k)
  (hP : ∀ r : (pres RD k).Rel,
    P.lin (blackMirrorLinear RD (fun r => (Λ r).val) ((pres RD k).rel r)) = 0)

section Commutation

variable (i : I) (lam : X)

/-- `E_i F_i 1_λ ≅ F_i E_i 1_λ ⊕ 1_λ^{⊕ ⟨i, λ⟩}` in the black action, for `⟨i, λ⟩ ≥ 0`
(KL III Proposition 3.25, first case, through Webster's Theorem 4.28). -/
def blackSumDecompEF (hn : 0 ≤ ip RD i lam) :
    SumDecomp (blackAct P [up i, dn i] (wt_up_dn RD i lam))
      (blackAct P [dn i, up i] (wt_dn_up RD i lam))
      (fun _ : Fin (ip RD i lam).toNat => blackAct P [] (wt_nil RD lam)) where
  a0 := blackMap P hP _ _ (-dg RD k lam [up i, dn i] [dn i, up i] (crosslL i i))
  b0 := blackMap P hP _ _ (dg RD k lam [dn i, up i] [up i, dn i] (crossrL i i))
  a s := blackMap P hP _ _ (alphaEF RD k i lam s)
  b s := blackMap P hP _ _ (betaEF RD k i lam s)
  total := by
    rw [← blackMap_comp, ← blackMap_id P hP (wt_up_dn RD i lam), ← total_EF i lam,
      blackMap_add, blackMap_sum, Finset.sum_range]
    congr 1
    exact Finset.sum_congr rfl fun s _ => (blackMap_comp P hP _ _ _ _ _).symm
  b0_a0 := by rw [← blackMap_comp, b0a0_EF i lam hn, blackMap_id]
  b_a0 s := by rw [← blackMap_comp, ba0_EF i lam s s.2, blackMap_zero]
  b_a_self s := by
    rw [← blackMap_comp, ba_EF i lam s s s.2 s.2]
    simp only [↓reduceIte, blackMap_id]
  b_a_ne s t hst := by
    rw [← blackMap_comp, ba_EF i lam s t s.2 t.2]
    simp only [Fin.val_inj, hst, ↓reduceIte, blackMap_zero]

/-- `F_i E_i 1_λ ≅ E_i F_i 1_λ ⊕ 1_λ^{⊕ -⟨i, λ⟩}` in the black action, for `⟨i, λ⟩ ≤ 0`
(KL III Proposition 3.25, second case, through Webster's Theorem 4.28). -/
def blackSumDecompFE (hn : ip RD i lam ≤ 0) :
    SumDecomp (blackAct P [dn i, up i] (wt_dn_up RD i lam))
      (blackAct P [up i, dn i] (wt_up_dn RD i lam))
      (fun _ : Fin (-ip RD i lam).toNat => blackAct P [] (wt_nil RD lam)) where
  a0 := blackMap P hP _ _ (-dg RD k lam [dn i, up i] [up i, dn i] (crossrL i i))
  b0 := blackMap P hP _ _ (dg RD k lam [up i, dn i] [dn i, up i] (crosslL i i))
  a s := blackMap P hP _ _ (alphaFE RD k i lam s)
  b s := blackMap P hP _ _ (betaFE RD k i lam s)
  total := by
    rw [← blackMap_comp, ← blackMap_id P hP (wt_dn_up RD i lam), ← total_FE i lam,
      blackMap_add, blackMap_sum, Finset.sum_range]
    congr 1
    exact Finset.sum_congr rfl fun s _ => (blackMap_comp P hP _ _ _ _ _).symm
  b0_a0 := by rw [← blackMap_comp, b0a0_FE i lam hn, blackMap_id]
  b_a0 s := by rw [← blackMap_comp, ba0_FE i lam s s.2, blackMap_zero]
  b_a_self s := by
    rw [← blackMap_comp, ba_FE i lam s s s.2 s.2]
    simp only [↓reduceIte, blackMap_id]
  b_a_ne s t hst := by
    rw [← blackMap_comp, ba_FE i lam s t s.2 t.2]
    simp only [Fin.val_inj, hst, ↓reduceIte, blackMap_zero]

/-- For `i ≠ j`, the actions of `E_i F_j 1_μ` and `F_j E_i 1_μ` are isomorphic, by the
sideways crossings (KL III Proposition 3.26, through Webster's Theorem 4.28). -/
def blackCrossIso (i j : I) (h : i ≠ j) (μ : X) :
    blackAct P [up i, dn j] (rfl : wt RD μ [up i, dn j] = _) ≅
      blackAct P [dn j, up i] (wt_dn_up_eq RD i j μ) where
  hom := blackMap P hP _ _ ((pres RD k).diag (crossl RD i j μ))
  inv := blackMap P hP _ _ ((pres RD k).diag (crossr RD i j μ))
  hom_inv_id := by rw [← blackMap_comp, crossl_comp_crossr RD k i j h μ, blackMap_id]
  inv_hom_id := by rw [← blackMap_comp, crossr_comp_crossl RD k i j h μ, blackMap_id]

end Commutation

end Categorification.Stendhal.DoubleDiagram

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleBlackActionAdditiveQ
import Categorification.Diagrams.CLQ.Decompositions

/-!
# The commutation relations of `𝒰` in the black action

Webster, arXiv:1309.3796v3, §4.5, Theorem 4.28, applied to the decompositions of
Khovanov–Lauda, arXiv:0807.3250v1, Propositions 3.25 and 3.26. The action of a
Khovanov–Lauda 2-morphism on the violating quotients (`blackMapQ`) is additive and
functorial, so the decomposition data of Proposition 3.25 and the inverse sideways crossings
of Proposition 3.26 pass to the black action on each violating quotient:

* for `n = ⟨i, λ⟩ ≥ 0`, the action of `E_i F_i 1_λ` decomposes as the action of
  `F_i E_i 1_λ` plus `n` copies of the identity (`blackSumDecompEFQ`);
* for `n ≤ 0`, the action of `F_i E_i 1_λ` decomposes as the action of `E_i F_i 1_λ` plus
  `-n` copies of the identity (`blackSumDecompFEQ`);
* for `i ≠ j`, the actions of `E_i F_j 1_μ` and `F_j E_i 1_μ` are isomorphic
  (`blackCrossIsoQ`).

These are decompositions in the preadditive category of functors between violating
quotients. They are the input for the `𝒰` commutation relations on modules used in the proof
of Proposition 5.5. The ungraded morphisms of `U` are used; the degree shifts of KL III (3.60)
play no role here.

This is the version of `BlackCommutation` in which the black strands carry the relations of
Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, Definition 1.1, `r = 1`; `CLQ.pres RD k sc`) instead
of the KL III relations. Each declaration carries the suffix `Q`.
-/

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe u v

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}} {k : Type*} [CommRing k] {sc : KL3.Diagram.CL.CLScalars C k}
  (P : Presentation (signature RD (fun r => (Λ r).val)) k)
  (hP : ∀ r : (CLQ.pres RD k sc).Rel,
    P.lin (blackMirrorLinear RD (fun r => (Λ r).val) ((CLQ.pres RD k sc).rel r)) = 0)

section Commutation

variable (i : I) (lam : X)

/-- `E_i F_i 1_λ ≅ F_i E_i 1_λ ⊕ 1_λ^{⊕ ⟨i, λ⟩}` in the black action, for `⟨i, λ⟩ ≥ 0`
(KL III Proposition 3.25, first case, through Webster's Theorem 4.28). -/
def blackSumDecompEFQ (hn : 0 ≤ ip RD i lam) :
    SumDecomp (blackAct P [up i, dn i] (wt_up_dn RD i lam))
      (blackAct P [dn i, up i] (wt_dn_up RD i lam))
      (fun _ : Fin (ip RD i lam).toNat => blackAct P [] (wt_nil RD lam)) where
  a0 := blackMapQ P hP _ _ (-NF.dg (CLQ.pres RD k sc) lam [up i, dn i] [dn i, up i] (crosslL i i))
  b0 := blackMapQ P hP _ _ (NF.dg (CLQ.pres RD k sc) lam [dn i, up i] [up i, dn i] (crossrL i i))
  a s := blackMapQ P hP _ _ (CLQ.alphaEF RD k sc i lam s)
  b s := blackMapQ P hP _ _ (CLQ.betaEF RD k sc i lam s)
  total := by
    rw [← blackMap_compQ, ← blackMap_idQ P hP (wt_up_dn RD i lam), ← CLQ.total_EF i lam,
      blackMap_addQ, blackMap_sumQ, Finset.sum_range]
    congr 1
    exact Finset.sum_congr rfl fun s _ => (blackMap_compQ P hP _ _ _ _ _).symm
  b0_a0 := by rw [← blackMap_compQ, CLQ.b0a0_EF i lam hn, blackMap_idQ]
  b_a0 s := by rw [← blackMap_compQ, CLQ.ba0_EF i lam s s.2, blackMap_zeroQ]
  b_a_self s := by
    rw [← blackMap_compQ, CLQ.ba_EF i lam s s s.2 s.2]
    simp only [↓reduceIte, blackMap_idQ]
  b_a_ne s t hst := by
    rw [← blackMap_compQ, CLQ.ba_EF i lam s t s.2 t.2]
    simp only [Fin.val_inj, hst, ↓reduceIte, blackMap_zeroQ]

/-- `F_i E_i 1_λ ≅ E_i F_i 1_λ ⊕ 1_λ^{⊕ -⟨i, λ⟩}` in the black action, for `⟨i, λ⟩ ≤ 0`
(KL III Proposition 3.25, second case, through Webster's Theorem 4.28). -/
def blackSumDecompFEQ (hn : ip RD i lam ≤ 0) :
    SumDecomp (blackAct P [dn i, up i] (wt_dn_up RD i lam))
      (blackAct P [up i, dn i] (wt_up_dn RD i lam))
      (fun _ : Fin (-ip RD i lam).toNat => blackAct P [] (wt_nil RD lam)) where
  a0 := blackMapQ P hP _ _ (-NF.dg (CLQ.pres RD k sc) lam [dn i, up i] [up i, dn i] (crossrL i i))
  b0 := blackMapQ P hP _ _ (NF.dg (CLQ.pres RD k sc) lam [up i, dn i] [dn i, up i] (crosslL i i))
  a s := blackMapQ P hP _ _ (CLQ.alphaFE RD k sc i lam s)
  b s := blackMapQ P hP _ _ (CLQ.betaFE RD k sc i lam s)
  total := by
    rw [← blackMap_compQ, ← blackMap_idQ P hP (wt_dn_up RD i lam), ← CLQ.total_FE i lam,
      blackMap_addQ, blackMap_sumQ, Finset.sum_range]
    congr 1
    exact Finset.sum_congr rfl fun s _ => (blackMap_compQ P hP _ _ _ _ _).symm
  b0_a0 := by rw [← blackMap_compQ, CLQ.b0a0_FE i lam hn, blackMap_idQ]
  b_a0 s := by rw [← blackMap_compQ, CLQ.ba0_FE i lam s s.2, blackMap_zeroQ]
  b_a_self s := by
    rw [← blackMap_compQ, CLQ.ba_FE i lam s s s.2 s.2]
    simp only [↓reduceIte, blackMap_idQ]
  b_a_ne s t hst := by
    rw [← blackMap_compQ, CLQ.ba_FE i lam s t s.2 t.2]
    simp only [Fin.val_inj, hst, ↓reduceIte, blackMap_zeroQ]

/-- For `i ≠ j`, the actions of `E_i F_j 1_μ` and `F_j E_i 1_μ` are isomorphic, by the
sideways crossings (KL III Proposition 3.26, through Webster's Theorem 4.28). -/
def blackCrossIsoQ (i j : I) (h : i ≠ j) (μ : X) :
    blackAct P [up i, dn j] (rfl : wt RD μ [up i, dn j] = _) ≅
      blackAct P [dn j, up i] (wt_dn_up_eq RD i j μ) where
  hom := blackMapQ P hP _ _ ((CLQ.pres RD k sc).diag (crossl RD i j μ))
  inv := blackMapQ P hP _ _ ((((sc.t j i)⁻¹ : kˣ) : k) • (CLQ.pres RD k sc).diag (crossr RD i j μ))
  hom_inv_id := by rw [← blackMap_compQ, CLQ.crossl_comp_smul_crossr RD k sc i j h μ, blackMap_idQ]
  inv_hom_id := by rw [← blackMap_compQ, CLQ.smul_crossr_comp_crossl RD k sc i j h μ, blackMap_idQ]

end Commutation

end Categorification.Stendhal.DoubleDiagram

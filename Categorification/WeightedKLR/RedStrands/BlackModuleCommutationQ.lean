/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackCommutationQ
import Categorification.WeightedKLR.RedStrands.DoubleBlackRestrictionQ
import Categorification.TwoRep.CompletionSumDecomp
import Categorification.Algebra.HomTensorDecomp

/-!
# The commutation relations of `𝒰` on module functors of the black action

Webster, arXiv:1309.3796v3, §4.5, Theorem 4.28, and the commutation relations used in the
proof of Proposition 5.5. For an object `O` of the completed violating quotient and a right
`End O`-module `N`, a word `s` of the black action gives the right `End O`-module
`(O ⟶ s O) ⊗_{End O} N`. The decompositions of the black action
(`blackSumDecompEFQ`, `blackSumDecompFEQ`, `blackCrossIsoQ`) pass first to completions
(`TwoRep.completionSumDecomp`) and then to these modules (`HomTensor.sumDecompModule`):

* for `n = ⟨i, λ⟩ ≥ 0`, the module of `E_i F_i 1_λ` decomposes as the module of `F_i E_i 1_λ`
  plus `n` copies of the module of the empty word (`blackModuleSumDecompEFQ`);
* for `n ≤ 0`, symmetrically (`blackModuleSumDecompFEQ`);
* for `i ≠ j`, the modules of `E_i F_j 1_μ` and `F_j E_i 1_μ` are isomorphic
  (`blackModuleCrossIsoQ`).

The coefficients are `ℤ`, so these hold for every module `N`, not only for projective ones.

This is the version of `BlackModuleCommutation` in which the black strands carry the relations of
Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, Definition 1.1, `r = 1`; `CLQ.pres RD k sc`) instead
of the KL III relations. Each declaration carries the suffix `Q`.
-/

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory CategoryTheory.Idempotents QuantumGroup QuantumGroup.UDot KL3.Diagram
  StringDiagrams TwoRep

universe u v w

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}} {k : Type*} [CommRing k] {sc : KL3.Diagram.CL.CLScalars C k}
  (P : Presentation (signature RD (fun r => (Λ r).val)) k)
  (hP : ∀ r : (CLQ.pres RD k sc).Rel,
    P.lin (blackMirrorLinear RD (fun r => (Λ r).val) ((CLQ.pres RD k sc).rel r)) = 0)

variable (i : I) (lam : X) (O : Karoubi (Mat_ (ViolatingCategory P lam)))
  (N : Type w) [AddCommGroup N] [Module (End O)ᵐᵒᵖ N]

/-- `E_i F_i 1_λ ≅ F_i E_i 1_λ ⊕ 1_λ^{⊕ ⟨i, λ⟩}` on modules, for `⟨i, λ⟩ ≥ 0`. -/
def blackModuleSumDecompEFQ (hn : 0 ≤ ip RD i lam) :
    SumDecomp
      (HomTensor.tensorObj O O N (completionMap (blackAct P [up i, dn i] (wt_up_dn RD i lam))))
      (HomTensor.tensorObj O O N (completionMap (blackAct P [dn i, up i] (wt_dn_up RD i lam))))
      (fun _ : Fin (ip RD i lam).toNat =>
        HomTensor.tensorObj O O N (completionMap (blackAct P [] (wt_nil RD lam)))) :=
  HomTensor.sumDecompModule O O N (completionSumDecomp (blackSumDecompEFQ P hP i lam hn))

/-- `F_i E_i 1_λ ≅ E_i F_i 1_λ ⊕ 1_λ^{⊕ -⟨i, λ⟩}` on modules, for `⟨i, λ⟩ ≤ 0`. -/
def blackModuleSumDecompFEQ (hn : ip RD i lam ≤ 0) :
    SumDecomp
      (HomTensor.tensorObj O O N (completionMap (blackAct P [dn i, up i] (wt_dn_up RD i lam))))
      (HomTensor.tensorObj O O N (completionMap (blackAct P [up i, dn i] (wt_up_dn RD i lam))))
      (fun _ : Fin (-ip RD i lam).toNat =>
        HomTensor.tensorObj O O N (completionMap (blackAct P [] (wt_nil RD lam)))) :=
  HomTensor.sumDecompModule O O N (completionSumDecomp (blackSumDecompFEQ P hP i lam hn))

/-- For `i ≠ j`, the modules `(O' ⟶ E_i F_j O) ⊗ N` and `(O' ⟶ F_j E_i O) ⊗ N` are isomorphic. -/
def blackModuleCrossIsoQ (j : I) (h : i ≠ j)
    (O' : Karoubi (Mat_ (ViolatingCategory P (wt RD lam [up i, dn j])))) :
    HomTensor.tensorObj O O' N (completionMap (blackAct P [up i, dn j]
        (rfl : wt RD lam [up i, dn j] = _))) ≅
      HomTensor.tensorObj O O' N (completionMap (blackAct P [dn j, up i]
        (wt_dn_up_eq RD i j lam))) :=
  HomTensor.natModuleIso O O' N (completionIso (blackCrossIsoQ P hP i j h lam))

end Categorification.Stendhal.DoubleDiagram

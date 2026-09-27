/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.GammaLiftKLR3
import Categorification.Diagrams.CL.Specialize

/-!
# `Γ_N` respects the KLR relations of `U_Q(sl_{m+1})`

Cautis–Lauda arXiv:1111.1431v3, §2.3 (`sec:KLR`), for the `sl_n` scalars
`CL.Sln.slnScalars` (`t_{ij} = i - j` for adjacent `i, j`, `s = 0`, `r = 1`): every relation
`klr μ r` of `CL.presCL (slRootDatum m) K (CL.Sln.slnScalars K m)`, i.e. the KLR relation `r`
(`CL.relationR` with `Q = qCL`, `r_i = 1`) placed on upward strands with rightmost region `μ`, is
sent to `0` by the bimodule evaluation `evalB` (whiskered on the right by any word, from any start
region). The polynomial `Q_{ij} = qCL` of the `sl_n` scalars is KL III's signed `Q^τ_{ij}` for
`i ≠ j` (`CL.Sln.qCL_sln_of_ne`), which is the polynomial of the path model
(`Signed.gammaCross_sq`, `Signed.braidQ_signed`).
-/

noncomputable section

namespace Categorification.Flag

open StringDiagrams Categorification.KL3.Diagram CategoryTheory

universe u

variable {K : Type u} [Field K] {m : ℕ} {N : ℕ}

local notation "RD" => slRootDatum m

/-- **`Γ_N` respects the KLR relations on upward strands** (`klr μ r`, `sl_n` scalars). -/
theorem evalB_klr (dnScal : Fin m → Fin m → K) (μ s : Wt m) (r : KLR.Diagram.Rel (Fin m))
    (v : List (psig RD).Colour)
    (ha : WOK N s ((ob RD μ (ups (KLR.Diagram.Rel.dom r).word)).word ++ v))
    (hb : WOK N s ((ob RD μ (ups (KLR.Diagram.Rel.cod r).word)).word ++ v)) :
    evalB K N dnScal s v ha hb (upLin RD K μ (CL.relationR K (CL.qCL (CL.Sln.slnScalars K m))
      (fun c => ((CL.Sln.slnScalars K m).r c : K)) r)) = 0 := by
  have hr : ∀ c, ((CL.Sln.slnScalars K m).r c : K) = 1 := fun _ => rfl
  cases r with
  | sqEq c => exact evalB_klr_sqEq dnScal _ _ c μ s v ha hb
  | sqNe c d h => exact evalB_klr_sqNe dnScal _ _ c d h (CL.Sln.qCL_sln_of_ne K h) μ s v ha hb
  | slideLEq c => exact evalB_klr_slideLEq dnScal _ _ hr c μ s v ha hb
  | slideLNe c d h => exact evalB_klr_slideLNe dnScal _ _ c d h μ s v ha hb
  | slideREq c => exact evalB_klr_slideREq dnScal _ _ hr c μ s v ha hb
  | slideRNe c d h => exact evalB_klr_slideRNe dnScal _ _ c d h μ s v ha hb
  | braid c d e h => exact evalB_klr_braid dnScal _ _ c d e h μ s v ha hb
  | braidQ c d h =>
    exact evalB_klr_braidQ dnScal _ _ hr c d h (CL.Sln.qCL_sln_of_ne K h) μ s v ha hb

end Categorification.Flag

end

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.GammaLiftZig
import Categorification.Flag.GammaLiftKLR
import Categorification.Flag.GammaLiftCycR
import Categorification.Flag.GammaLiftCycL
import Categorification.Flag.GammaLiftDownup
import Categorification.Flag.GammaLiftBubbleRel
import Categorification.Flag.GammaLiftCurlRel
import Categorification.Flag.GammaLiftDecompRel
import Categorification.Diagrams.CL.Sigma

/-!
# The 2-representation `Γ_N` of `U_Q(sl_{m+1})` on the flag 2-category

KL III, arXiv:0807.3250v1, §6 (Definition 6.2, Theorem 6.11: the 2-functor `Γ_N` from `U` to
`Flag_N`), with the scalars of Cautis–Lauda's `U_Q(sl_n)` (arXiv:1111.1431v3, Definition 1.1 with
`t_{ij} = i - j` for adjacent `i, j`, `CL.Sln.slnScalars`), and through the isomorphism `Σ`
(`CL.Sln.sigmaEquivPres`) from KL III's `U(sl_n)` itself.

The functor `gammaFunctor` (`Categorification.Flag.GammaTarget`) sends the free 2-category on the
generators of `U` to `K`-modules (each hom-category separately, the target module of an object
being `Γ_N` of the 1-morphism, i.e. the path bimodule, or `0` if some region is not a composition
of `N`). It kills the interchange law (`gamma_interchange`), and here we check that it kills every
relation of `CL.presCL (slRootDatum m) K (CL.Sln.slnScalars K m)`, whiskered on both sides
(`gammaN_hP`, the hypothesis of `gamma_respects`): the zigzags (`evalB_zigL`, `evalB_zigR`), dot
cyclicity (`evalB_cycDotR`, `evalB_cycDotL`), bubbles (`evalB_presCL_cwNeg`, …), curls
(`evalB_presCL_curlR`, `evalB_presCL_curlL`), the decompositions of `1_{EF}`, `1_{FE}`
(`evalB_presCL_decompEF`, `evalB_presCL_decompFE`), the `Q`-cyclicity of crossings
(`evalB_cycCrossR`, `evalB_cycCrossL`), the mixed relations (`evalB_presCL_downupEF`,
`evalB_presCL_downupFE`) and the KLR relations on upward strands (`evalB_klr`). The downward
crossing `F_j F_i → F_i F_j` is sent to `t_{ji}^{-1}` times KL III's (6.9) (`gammaDn`).

## Main definitions

* `gammaN_hP`: every relation of `U_Q(sl_{m+1})` is killed;
* `GammaN K m N : (CL.presCL (slRootDatum m) K (CL.Sln.slnScalars K m)).Presented ⥤ ModuleCat K`:
  **`Γ_N` on CL's `U_Q(sl_{m+1})`** (`gammaLift`);
* `GammaN_KL3 K m N : (pres (slRootDatum m) K).Presented ⥤ ModuleCat K`: the composite with
  `Σ : U(sl_{m+1}) ≅ U_Q(sl_{m+1})`, i.e. `Γ_N` on KL III's `U(sl_{m+1})`.
-/

noncomputable section

namespace Categorification.Flag

open StringDiagrams Categorification.KL3.Diagram CategoryTheory

universe u

variable {K : Type u} [Field K] {m : ℕ} {N : ℕ}

local notation "RD" => slRootDatum m

local notation "PCL" => CL.presCL (slRootDatum m) K (CL.Sln.slnScalars K m)

variable (K N m) in
/-- **`Γ_N` kills every relation of `U_Q(sl_{m+1})`** (whiskered on the right by any word, from
the start region of the relation; the left whiskering is handled by `gamma_respects`). -/
theorem gammaN_hP : ∀ (r : (PCL).Rel) (s : Wt m), s = ((PCL).dom r).start →
    ∀ (v : List (psig RD).Colour) (ha : WOK N s (((PCL).dom r).word ++ v))
      (hb : WOK N s (((PCL).cod r).word ++ v)),
      evalB K N (gammaDn K m) s v ha hb ((PCL).rel r) = 0
  | .inl (.inl e), _, _, _, _, _ => e.elim
  | .inl (.inr (.inl c)), s, hs, v, ha, hb => evalB_zigL (gammaDn K m) c s hs v ha hb
  | .inl (.inr (.inr c)), s, hs, v, ha, hb => evalB_zigR (gammaDn K m) c s hs v ha hb
  | .inr (.cycDotR i μ), s, hs, v, ha, hb => evalB_cycDotR (gammaDn K m) i μ s hs v ha hb
  | .inr (.cycDotL i μ), s, hs, v, ha, hb => evalB_cycDotL (gammaDn K m) i μ s hs v ha hb
  | .inr (.cwNeg i lam α h), s, hs, v, ha, hb =>
    evalB_presCL_cwNeg (gammaDn K m) i lam α h s hs v ha hb
  | .inr (.ccwNeg i lam α h), s, hs, v, ha, hb =>
    evalB_presCL_ccwNeg (gammaDn K m) i lam α h s hs v ha hb
  | .inr (.cwOne i lam h), s, hs, v, ha, hb => evalB_presCL_cwOne (gammaDn K m) i lam h s hs v ha hb
  | .inr (.ccwOne i lam h), s, hs, v, ha, hb =>
    evalB_presCL_ccwOne (gammaDn K m) i lam h s hs v ha hb
  | .inr (.curlR i lam), s, hs, v, ha, hb => evalB_presCL_curlR (gammaDn K m) i lam s hs v ha hb
  | .inr (.curlL i μ), s, hs, v, ha, hb => evalB_presCL_curlL (gammaDn K m) i μ s hs v ha hb
  | .inr (.decompEF i lam), s, hs, v, ha, hb =>
    evalB_presCL_decompEF (gammaDn K m) i lam s hs v ha hb
  | .inr (.decompFE i lam), s, hs, v, ha, hb =>
    evalB_presCL_decompFE (gammaDn K m) i lam s hs v ha hb
  | .inr (.cycCrossR j i μ), s, hs, v, ha, hb => evalB_cycCrossR j i μ s hs v ha hb
  | .inr (.cycCrossL j i μ), s, hs, v, ha, hb => evalB_cycCrossL j i μ s hs v ha hb
  | .inr (.downupEF i j h μ), s, hs, v, ha, hb => evalB_presCL_downupEF i j h μ s hs v ha hb
  | .inr (.downupFE i j h μ), s, hs, v, ha, hb => evalB_presCL_downupFE i j h μ s hs v ha hb
  | .inr (.klr μ r), s, _, v, ha, hb => evalB_klr (gammaDn K m) μ s r v ha hb

variable (K N m) in
/-- **The 2-representation `Γ_N` of Cautis–Lauda's `U_Q(sl_{m+1})`** (with the `sl_n` scalars
`t_{ij} = i - j` for adjacent `i, j`) on the flag 2-category `Flag_N` of KL III §5, on each
hom-category, with values in `K`-modules. -/
def GammaN : (PCL).Presented ⥤ ModuleCat.{u} K :=
  gammaLift K N (gammaDn K m) (PCL) (gammaN_hP K m N)

variable (K N m) in
/-- **The 2-representation `Γ_N` of KL III's `U(sl_{m+1})`** (Definition 3.1): `GammaN` composed
with the isomorphism `Σ : U(sl_{m+1}) ≅ U_Q(sl_{m+1})` (`CL.Sln.sigmaEquivPres`). -/
def GammaN_KL3 : (pres (slRootDatum m) K).Presented ⥤ ModuleCat.{u} K :=
  (CL.Sln.sigmaEquivPres K m).functor ⋙ GammaN K m N

end Categorification.Flag

end

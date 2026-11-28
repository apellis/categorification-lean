/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721DotDirectTrace
import Categorification.WeightedKLR.Rigidity.CupCapProp721TraceShiftF
import Categorification.WeightedKLR.Rigidity.CupCapProp721TraceShiftCrossDirect
import Categorification.WeightedKLR.Rigidity.CupCapProp721MixedCrossMateDirect

/-!
# Proposition 7.21: the quantum trace and the generators

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3,
Proposition 7.21, for the quantum trace `𝕋` of Definition 7.18 with its homological shift. This
module collects the statements proved so far that the isomorphisms `𝔈_i ⋙ 𝕋 ≅ 𝕋 ⋙ 𝔈_i` and
`𝔉_i ⋙ 𝕋 ≅ 𝕋 ⋙ 𝔉_i` carry the dots and crossings on `𝔈⁺`, `𝔉⁺` to those on `𝔈`, `𝔉`. It adds
no declarations: each statement is proved once, in the module named.

## `𝔈` side

* Dot, direct form (`CupCap.dgPlusDot` to `CupCap.dgBlackDot`):
  `CupCap.capEQuantumTraceShiftIso_dgDot`.
* Crossing of equal colours, direct form (`CupCap.dgPlusCross` to `CupCap.dgBlackCross`):
  `CupCap.capEQuantumTraceShiftIso_dgCross`.
* Crossing of different colours, direct form (`CupCap.dgPlusMixedCross` to
  `CupCap.dgMixedCross`): `CupCap.capEQuantumTraceShiftIsoMid_dgMixedCross`,
  `CupCap.capEQuantumTraceShiftIsoTop_dgMixedCross`. They are derived from the mate form
  (`CupCap.capEQuantumTraceShiftIsoMid_mixedCross`,
  `CupCap.capEQuantumTraceShiftIsoTop_mixedCross`, for the conjugates
  `CupCap.dgPlusEMixedCrossMate`, `CupCap.dgBlackEMixedCrossMate` of the crossings
  `CupCap.dgPlusFMixedCross`, `CupCap.dgBlackFMixedCross` on `𝔉⁺_a 𝔉⁺_b`, `𝔉_a 𝔉_b`) by
  `CupCap.dgPlusEMixedCrossMate_eq_dgPlusMixedCross` and
  `CupCap.dgBlackEMixedCrossMate_eq_dgMixedCross`.

## `𝔉` side (mate form throughout)

The shift of `𝔉_i` is the one induced by `𝔈_i ⊣ 𝔉_i` (`CupCap.derivedBlackFAdjointCommShift`),
and the dots and crossings on `𝔉` are conjugates of those on `𝔈`.

* Dot: `CupCap.capFQuantumTraceShiftIso_dot` (for `CupCap.dgPlusFDotMate`,
  `CupCap.dgBlackFDotMate`).
* Crossing of equal colours: `CupCap.capFQuantumTraceShiftIso_crossing` (for
  `CupCap.dgPlusFCrossMate`, `CupCap.dgBlackFCrossMate`).
* Crossing of different colours: `CupCap.capFQuantumTraceShiftIsoMid_mixedCross`,
  `CupCap.capFQuantumTraceShiftIsoTop_mixedCross` (for `CupCap.dgPlusFMixedCrossMate`,
  `CupCap.dgBlackFMixedCrossMate`).

The identification of these conjugates with the directly defined crossings on `𝔉` and the
agreement of the induced shift of `𝔉_i` with its derived tensor shift are open.

Route hypotheses (tracked): `hL`, `hQ`, `hκ`, `hP`, `hPL`, `hfin`, `hproj` as for
`CupCap.capEDerivedIso`; `C`, `hRq : IsRouquierQ C Q` is Webster's setting for Theorem 4.31.
-/

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.QuantumGroup.GabberKacStatement
import Categorification.KLR.Theorem321
import Categorification.KLR.KL2.Theorem8

/-!
# KL I and KL II headline theorems from the canonical Gabber–Kac statement

Thin wrappers: the KL I and KL II isomorphism theorems, whose Gabber–Kac hypotheses are
`PreF.GabberKac (KL.C Γ).dot vQ (KL.C Γ).c` (KL I) and `C.GabberKac vQ C.c` (KL II), restated
with the single canonical hypothesis `CartanDatum.QuantumGabberKac` (Lusztig, *Introduction to
quantum groups*, Theorem 33.1.3(a); see `Categorification.QuantumGroup.GabberKacStatement`).

* `QuantumGroup.KL.gabberKac_of_quantumGabberKac` — the KL I form of the hypothesis;
* `KLR.KLGamma.theorem_1_1_of_quantumGabberKac`, `KLR.KLGamma.gammaIntEquiv_of_quantumGabberKac`,
  `KLR.KLGamma.theorem_3_21_of_quantumGabberKac` — Khovanov–Lauda I (arXiv:0803.4121v2),
  Theorem 1.1 and Theorem 3.21;
* `KLR.KL2Gamma.theorem_8_of_quantumGabberKac`, `KLR.KL2Gamma.gammaInt2Equiv_of_quantumGabberKac`
  — Khovanov–Lauda II (arXiv:0804.2080), Theorem 8.
-/

noncomputable section

namespace Categorification.QuantumGroup.KL

variable {I : Type*} [DecidableEq I] (Γ : SimpleGraph I) [DecidableRel Γ.Adj]

/-- The KL I form `PreF.GabberKac (KL.C Γ).dot vQ (KL.C Γ).c` of the Gabber–Kac hypothesis
follows from the canonical statement for the Cartan datum of `Γ`. -/
theorem gabberKac_of_quantumGabberKac (h : (KL.C Γ).QuantumGabberKac) :
    PreF.GabberKac (KL.C Γ).dot vQ (KL.C Γ).c :=
  (KLR.KLGamma.gabberKac_iff Γ).1 h

end Categorification.QuantumGroup.KL

namespace Categorification.KLR.KLGamma

open Graded QuantumGroup

variable {I : Type*} [DecidableEq I] (k : Type*) [Field k] (Γ : SimpleGraph I)
  [DecidableRel Γ.Adj]

/-- **KL I, Theorem 1.1** (arXiv:0803.4121v2): `γ : _𝒜 f → K₀(R)` is bijective, from the
canonical quantum Gabber–Kac statement (Lusztig 33.1.3(a)) for the Cartan datum of `Γ`. -/
theorem theorem_1_1_of_quantumGabberKac (hGK : (KL.C Γ).QuantumGabberKac) :
    Function.Bijective (gammaInt' k Γ (KL.gabberKac_of_quantumGabberKac Γ hGK)) :=
  theorem_1_1 k Γ _

/-- **KL I, Theorem 1.1**: the ring isomorphism `γ : _𝒜 f ≅ K₀(R)`, from the canonical quantum
Gabber–Kac statement. -/
def gammaIntEquiv_of_quantumGabberKac (hGK : (KL.C Γ).QuantumGabberKac) :
    KL.Af Γ ≃+* (klGradingDatum k Γ).K0R :=
  gammaIntEquiv k Γ (KL.gabberKac_of_quantumGabberKac Γ hGK)

/-- **KL I, Theorem 3.21**, from the canonical quantum Gabber–Kac statement. -/
theorem theorem_3_21_of_quantumGabberKac (hGK : (KL.C Γ).QuantumGabberKac)
    {L L' : List (ℤ × List (I × ℕ))} (hrel : relSum Γ L = relSum Γ L') (μ : Multiset I)
    {ν : Multiset I} (P : GProj ((klGradingDatum k Γ).grade ν)) :
    Nonempty ((sumF k Γ μ P L).Iso (sumF k Γ μ P L')) :=
  theorem_3_21 k Γ (KL.gabberKac_of_quantumGabberKac Γ hGK) hrel μ P

end Categorification.KLR.KLGamma

namespace Categorification.KLR.KL2Gamma

open QuantumGroup KL2

variable {I : Type*} [DecidableEq I] (k : Type*) [Field k] (C : CartanDatum I)

/-- **KL II, Theorem 8** (arXiv:0804.2080): `γ : _𝒜 f → K₀(R)` is bijective, from the canonical
quantum Gabber–Kac statement (Lusztig 33.1.3(a)) for `C`. -/
theorem theorem_8_of_quantumGabberKac (hGK : C.QuantumGabberKac) :
    Function.Bijective (gammaInt2' k C hGK.gabberKac) :=
  theorem_8 k C hGK.gabberKac

/-- **KL II, Theorem 8**: the ring isomorphism `γ : _𝒜 f ≅ K₀(R)`, from the canonical quantum
Gabber–Kac statement. -/
def gammaInt2Equiv_of_quantumGabberKac (hGK : C.QuantumGabberKac) :
    C.Af ≃+* (klGradingDatum2 k C).K0R :=
  gammaInt2Equiv k C hGK.gabberKac

end Categorification.KLR.KL2Gamma

end

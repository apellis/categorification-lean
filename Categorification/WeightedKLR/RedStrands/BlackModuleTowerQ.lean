/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackModuleTower
import Categorification.WeightedKLR.RedStrands.DoubleCLBlackActionQ
import Categorification.CategoryTheory.PiShift
import Categorification.WeightedKLR.RedStrands.BlackModuleResIndAdjunctionQ
import Categorification.WeightedKLR.RedStrands.TensorIntegrable

/-!
# `Eᵢ` and `Fᵢ` on the modules along an `i`-string

Fix a colour `i` and a weight `ν₀`. The weights `ν₀, {i} + ν₀, {i} + ({i} + ν₀), …`
(`stringWeight`) form the `i`-string through `ν₀`, and the right modules over the tensor
product algebras `T^λ` at these weights form the product category `StringModules`. Webster's
`Fᵢ` and `Eᵢ` (arXiv:1309.3796v2, §4.6) move along the string and assemble to endofunctors
`stringF`, `stringE` of it, adjoint on both sides at standard Khovanov–Lauda black scalars
(`stringFEAdj` from `Fᵢ ⊣ Eᵢ`, `stringEFAdjQ` from Theorem 4.31). This is the category of
Chuang–Rouquier's weak `𝔰𝔩₂`-categorification along one string (arXiv:math/0407205v2,
§5.1.1), used by Webster in §5. The string is finite: the algebras vanish far out
(`subsingleton_stringWeight`).

This is the version of `BlackModuleTower` in which the black strands carry the relations of
Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, Definition 1.1, `r = 1`; `CLQ.pres RD k sc`) instead
of the KL III relations. Each declaration carries the suffix `Q`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory

universe u

section Generic

variable {I : Type u} [DecidableEq I] {k : Type u} [CommRing k] {sc : KL3.Diagram.CL.CLScalars C k} {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (i : I) (ν₀ : Multiset I)

end Generic

section CL

open CategoryTheory.Idempotents QuantumGroup QuantumGroup.UDot StringDiagrams KLR TwoRep
  CyclotomicAction DoubleDiagram KL3.Diagram

open scoped Classical

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type u} {ℓ : ℕ} (i : I) (ν₀ : Multiset I) {Λ : Fin ℓ → I →₀ ℕ} {C : CartanDatum I}
  {k : Type u} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {hQ : IsRouquierQ C Q}

local notation "RDc" => coordinateDatum Λ C
local notation "KL" => blackScalarsQ Λ C hQ

variable {P : Presentation.{u, u}
    (signature (coordinateDatum Λ C) (redWeight (cyclotomicCoverWeightDatum Λ C))) k}
  (hP : CoverRelsNegligible.{u, u, u} Λ C hQ (coverDotCentral Λ C hQ)
    (blockWeight (cyclotomicCoverWeightDatum Λ C) (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 :
      I ⊕ Fin ℓ → ℤ) P)
  (hwf : P.WFDom)

/-- `Eᵢ ⊣ Fᵢ` along the string, at standard Khovanov–Lauda black scalars (Webster,
arXiv:1309.3796v3, Theorem 4.31). -/
def stringEFAdjQ :
    stringE (Q) Λ i ν₀ ⊣ stringF (Q) Λ i ν₀ :=
  PiShift.downUpAdj fun m => clBlackResIndAdjunctionQ hP hwf i (stringWeight i ν₀ m)

end CL

end Categorification.Stendhal

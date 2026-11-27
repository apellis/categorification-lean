/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackModuleTowerFinite
import Categorification.WeightedKLR.RedStrands.DoubleCLBlackActionQ
import Categorification.Algebra.InductionAlongFinite
import Categorification.Algebra.ModuleTower
import Categorification.WeightedKLR.RedStrands.BlackModuleTowerQ
import Categorification.WeightedKLR.RedStrands.TensorFinite
import Mathlib.CategoryTheory.Adjunction.Restrict

/-!
# `Eᵢ` and `Fᵢ` on finitely generated modules along an `i`-string

Over a field, the tensor product algebras `T^λ` are finite-dimensional
(`tensorProductAlgebra_finite`), hence noetherian, and Webster's `Fᵢ` and `Eᵢ`
(arXiv:1309.3796v2, §4.6) preserve finite generation (`InductionAlong.Ind.finite`,
`InductionAlong.Res.finite`). So the functors `stringF`, `stringE` along an `i`-string
restrict to the abelian category `FGStringModules` of families of finitely generated modules,
with both adjunctions (`fgStringFEAdj`, and `fgStringEFAdjQ` at black scalars of a Kang–Kashiwara family). This is the abelian category of Chuang–Rouquier's weak `𝔰𝔩₂`-categorification along
one string (arXiv:math/0407205v2, §5.1.1).

This is the version of `BlackModuleTowerFinite` in which the black strands carry the relations of
Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, Definition 1.1, `r = 1`; `CLQ.pres RD k sc`) instead
of the KL III relations. Each declaration carries the suffix `Q`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe u

section Generic

variable {I : Type u} [DecidableEq I] {k : Type u} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin ℓ → I →₀ ℕ) {C : QuantumGroup.CartanDatum I}
  (hQ : KLR.IsRouquierQ C Q) (i : I) (ν₀ : Multiset I)

variable [∀ m, IsNoetherianRing (StringAlg (Q := Q) Λ i ν₀ m)]

end Generic

section CL

open CategoryTheory.Idempotents QuantumGroup QuantumGroup.UDot StringDiagrams KLR TwoRep
  CyclotomicAction DoubleDiagram KL3.Diagram

open scoped Classical

variable {I : Type u} {ℓ : ℕ} (i : I) (ν₀ : Multiset I) {Λ : Fin ℓ → I →₀ ℕ} {C : CartanDatum I}
  {k : Type u} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {hQ : IsRouquierQ C Q}

local notation "KL" => blackScalarsQ Λ C hQ

variable {P : Presentation.{u, u}
    (signature (coordinateDatum Λ C) (redWeight (cyclotomicCoverWeightDatum Λ C))) k}
  (hP : CoverRelsNegligible.{u, u, u} Λ C hQ (coverDotCentral Λ C hQ)
    (blockWeight (cyclotomicCoverWeightDatum Λ C) (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 :
      I ⊕ Fin ℓ → ℤ) P)
  (hwf : P.WFDom)

include hP hwf in
/-- `Eᵢ ⊣ Fᵢ` on finitely generated modules along the string, at standard Khovanov–Lauda
black scalars (Webster, arXiv:1309.3796v3, Theorem 4.31). -/
def fgStringEFAdjQ (hR : KLR.IsRouquierQ C (Q))
    [∀ m, IsNoetherianRing (StringAlg (Q := Q) Λ i ν₀ m)] :
    fgStringE (k := k) (Q := Q) (C := C) Λ hR i ν₀ ⊣
      fgStringF (k := k) (Q := Q) Λ i ν₀ :=
  (stringEFAdjQ i ν₀ hP hwf).restrictFullyFaithful
    (ModuleTower.towerFinite _).fullyFaithfulι (ModuleTower.towerFinite _).fullyFaithfulι
    (Iso.refl _) (Iso.refl _)

end CL

end Categorification.Stendhal

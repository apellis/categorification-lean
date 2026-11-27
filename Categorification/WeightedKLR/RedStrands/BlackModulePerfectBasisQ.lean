/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackModuleSimpleHeadQ
import Categorification.WeightedKLR.RedStrands.DoubleCLBlackActionQ
import Categorification.Sl2Categorification.PerfectBasis

/-!
# Simple `T^λ`-modules form a perfect basis

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
Theorem 5.14: the classes of simple `T^λ`-modules form a perfect basis in the sense of
Berenstein–Kazhdan (arXiv:math/0601391v3, Definition 5.30), with crystal operators given by the
heads of `Eᵢ` (Proposition 5.12).

Here this is stated for the weak `𝔰𝔩₂`-categorification along an `i`-string through `ν₀ ∌ i`
(`fgStringWeakSl2Q`), i.e. for one colour `i` at a time, which is how Definition 5.30 is phrased:
the operator `ẽᵢ` sends the class of a simple `L` to the class of the head of `Eᵢ L`. The
generic statement is `Sl2.WeakSl2.isPerfectBasis`.

This is the version of `BlackModulePerfectBasis` in which the black strands carry the relations of
Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, Definition 1.1, `r = 1`; `CLQ.pres RD k sc`) instead
of the KL III relations. Each declaration carries the suffix `Q`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory Limits _root_.Module QuantumGroup QuantumGroup.UDot KL3.Diagram DoubleDiagram
  CategoryTheory.Idempotents StringDiagrams KLR TwoRep CyclotomicAction InductionAlong

open scoped Classical

universe u

variable {I : Type u} {ℓ : ℕ} (i : I) (ν₀ : Multiset I) {Λ : Fin ℓ → I →₀ ℕ}
  {C : CartanDatum I} {k : Type u} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {hQ : IsRouquierQ C Q}

local notation "KL" => blackScalarsQ Λ C hQ
local notation "Str" => StringAlg (k := k) (Q := Q) Λ i ν₀

/-- **Webster, arXiv:1309.3796v2, Theorem 5.14** (for the colour `i`): the classes of the simple
modules along an `i`-string through `ν₀ ∌ i` form a perfect basis for `eᵢ` (Berenstein–Kazhdan,
arXiv:math/0601391v3, Definition 5.30), whose crystal operator sends `L` to the head of `Eᵢ L`:
`ẽᵢ L = S` exactly when `S` is a quotient of `Eᵢ L`. -/
theorem fgString_isPerfectBasisQ (hR : KLR.IsRouquierQ C (Q))
    [∀ m, IsNoetherianRing (Str m)] [∀ m, IsArtinianRing (Str m)] (hi : i ∉ ν₀) :
    let A := fgStringWeakSl2Q i ν₀
      (coverRelsNegligible_noRelations.{u, u, u} (Λ := Λ) (C := C) (hQ := hR)
        (hc := coverDotCentral Λ C hR)
        (o := (blockWeight (cyclotomicCoverWeightDatum Λ C)
          (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 : I ⊕ Fin ℓ → ℤ)))
      (wfDom_noRelations.{u, u, u, u, u}
        (signature (coordinateDatum Λ C) (redWeight (cyclotomicCoverWeightDatum Λ C))) k) hR hi
    ∃ et : ModuleTower.K0Index Str → Option (ModuleTower.K0Index Str),
      Sl2.IsPerfectBasis A.B A.e et ∧
        ∀ b c, et b = some c ↔ ∃ p : A.E.obj (A.simple b) ⟶ A.simple c, Epi p := by
  intro A
  have : A.E.Additive := fgStringE_additive Λ hR i ν₀
  have : A.F.Additive := fgStringF_additive (k := k) (Q := Q) Λ i ν₀
  obtain ⟨B, hB⟩ := exists_subsingleton_stringAlg (k := k) Λ hR i ν₀
  have := ModuleTower.isArtinianObject hB
  have := ModuleTower.isNoetherianObject hB
  have : A.E.Linear k := fgStringE_linear (k := k) Λ hR i ν₀
  have : A.F.Linear k := fgStringF_linear (k := k) (Q := Q) Λ i ν₀
  let DE := fgStringNilHecke Λ hR i ν₀
  let adj := fgStringEFAdjQ i ν₀
    (coverRelsNegligible_noRelations.{u, u, u} (Λ := Λ) (C := C) (hQ := hR)
      (hc := coverDotCentral Λ C hR)
      (o := (blockWeight (cyclotomicCoverWeightDatum Λ C)
        (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 : I ⊕ Fin ℓ → ℤ)))
    (wfDom_noRelations.{u, u, u, u, u}
      (signature (coordinateDatum Λ C) (redWeight (cyclotomicCoverWeightDatum Λ C))) k) hR
  obtain ⟨N, hN⟩ := exists_fgStringNilHecke_X_pow_eq_zero Λ hR i ν₀
  refine ⟨A.eTilde, ?_, ?_⟩
  · exact A.isPerfectBasis DE (DE.dual adj) k
      (Sl2.NilHeckeData.isNilpotent_app_of_pow_eq_zero hN)
      (Sl2.NilHeckeData.isNilpotent_app_of_pow_eq_zero
        (Sl2.NilHeckeData.dual_X_pow_eq_zero DE adj hN))
      (fun S _ => fgString_finrank_end_simple Λ hR i ν₀ S)
  · exact A.eTilde_eq_some_iff DE (DE.dual adj) k
      (Sl2.NilHeckeData.isNilpotent_app_of_pow_eq_zero hN)
      (Sl2.NilHeckeData.isNilpotent_app_of_pow_eq_zero
        (Sl2.NilHeckeData.dual_X_pow_eq_zero DE adj hN))
      (fun S _ => fgString_finrank_end_simple Λ hR i ν₀ S)

end Categorification.Stendhal

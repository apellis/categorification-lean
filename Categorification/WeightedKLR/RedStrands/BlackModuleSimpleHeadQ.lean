/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackModuleSimpleHead
import Categorification.WeightedKLR.RedStrands.DoubleCLBlackActionQ
import Categorification.WeightedKLR.RedStrands.BlackModuleTowerSl2Q
import Categorification.WeightedKLR.RedStrands.BlackNilHeckeNilpotent
import Categorification.WeightedKLR.RedStrands.AbsoluteSimple
import Categorification.Sl2Categorification.SimpleHead
import Categorification.Sl2Categorification.NilHeckeLift
import Categorification.CategoryTheory.PiShiftLinear
import Categorification.Algebra.InductionAlongLinear
import Categorification.Algebra.DualRightModule
import Categorification.Algebra.ModuleTowerEnd

/-!
# Simple heads of `Eᵢ L` and `Fᵢ L`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
Proposition 5.12: for a simple module `L` over `T^λ`, the heads of `Fᵢ L` and `Eᵢ L` are
simple.

The proof is Chuang–Rouquier's (arXiv:math/0407205v2, Proposition 5.20) applied to the weak
`𝔰𝔩₂`-categorification along an `i`-string (`fgStringWeakSl2Q`):
* `Eᵢ` and `Fᵢ` are `k`-linear (`fgStringE_linear`, `fgStringF_linear`);
* the dot on the newest black strand gives a nil-Hecke action on `Eᵢ` whose dot is nilpotent
  (`fgStringNilHecke`, `fgStringNilHecke_X_pow_eq_zero`), and its mate is one on `Fᵢ`;
* every endomorphism of a simple module is a scalar (`fgString_finrank_end_simple`), by passing
  to the `k`-dual left module (`DualRightModule.exists_scalar_of_dual`) and the absolute
  irreducibility of simple `T^λ`-modules (`exists_scalar_of_simple`).

The main results are `fgString_head_EQ` and `fgString_head_FQ`: any two simple quotients of
`Eᵢ U` (resp. `Fᵢ U`) for `U` simple are isomorphic compatibly with the quotient maps.

This is the version of `BlackModuleSimpleHead` in which the black strands carry the relations of
Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, Definition 1.1, `r = 1`; `CLQ.pres RD k sc`) instead
of the KL III relations. Each declaration carries the suffix `Q`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory Limits _root_.Module MulOpposite QuantumGroup QuantumGroup.UDot KL3.Diagram
  DoubleDiagram

universe u

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Linear

variable {I : Type u} [DecidableEq I] {k : Type u} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (i : I)

end Linear

section Generic

variable {I : Type u} [DecidableEq I] {k : Type u} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin ℓ → I →₀ ℕ)
  {C : QuantumGroup.CartanDatum I}
  (hQ : KLR.IsRouquierQ C Q) (i : I) (ν₀ : Multiset I)
  [∀ m, IsNoetherianRing (StringAlg (Q := Q) Λ i ν₀ m)]

end Generic

section CL

open CategoryTheory.Idempotents StringDiagrams KLR TwoRep CyclotomicAction InductionAlong

open scoped Classical

variable {I : Type u} {ℓ : ℕ} (i : I) (ν₀ : Multiset I) {Λ : Fin ℓ → I →₀ ℕ}
  {C : CartanDatum I} {k : Type u} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {hQ : IsRouquierQ C Q}

local notation "KL" => blackScalarsQ Λ C hQ
local notation "Str" => StringAlg (k := k) (Q := Q) Λ i ν₀

/-- **Webster, arXiv:1309.3796v2, Proposition 5.12, for `Eᵢ`**: for `U` simple, any two simple
quotients of `Eᵢ U` are isomorphic compatibly with the quotient maps, so the head of `Eᵢ U` is
simple. This is Chuang–Rouquier, arXiv:math/0407205v2, Proposition 5.20, for the weak
`𝔰𝔩₂`-categorification along an `i`-string through `ν₀ ∌ i`. -/
theorem fgString_head_EQ (hR : KLR.IsRouquierQ C (Q))
    [∀ m, IsNoetherianRing (Str m)] [∀ m, IsArtinianRing (Str m)] (hi : i ∉ ν₀)
    {U : ModuleTower.FGTower Str} (hU : Simple U) {S₁ S₂ : ModuleTower.FGTower Str}
    [Simple S₁] [Simple S₂]
    (q₁ : (fgStringE Λ hR i ν₀).obj U ⟶ S₁)
    (q₂ : (fgStringE Λ hR i ν₀).obj U ⟶ S₂)
    [Epi q₁] [Epi q₂] :
    ∃ e : S₁ ≅ S₂, q₁ ≫ e.hom = q₂ := by
  have hP := coverRelsNegligible_noRelations.{u, u, u} (Λ := Λ) (C := C) (hQ := hR)
    (hc := coverDotCentral Λ C hR)
    (o := (blockWeight (cyclotomicCoverWeightDatum Λ C)
      (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 : I ⊕ Fin ℓ → ℤ))
  have hwf := wfDom_noRelations.{u, u, u, u, u}
    (signature (coordinateDatum Λ C) (redWeight (cyclotomicCoverWeightDatum Λ C))) k
  have : ∀ i j, i ≠ j → Q i j = Q i j := fun _ _ _ => rfl
  let A := fgStringWeakSl2Q i ν₀ hP hwf hR hi
  have : A.E.Additive := fgStringE_additive Λ hR i ν₀
  have : A.F.Additive := fgStringF_additive (k := k) (Q := Q) Λ i ν₀
  obtain ⟨B, hB⟩ := exists_subsingleton_stringAlg (k := k) Λ hR i ν₀
  have := ModuleTower.isArtinianObject hB
  have := ModuleTower.isNoetherianObject hB
  have : A.E.Linear k := fgStringE_linear (k := k) Λ hR i ν₀
  have : A.F.Linear k := fgStringF_linear (k := k) (Q := Q) Λ i ν₀
  let DE := fgStringNilHecke Λ hR i ν₀
  let adj := fgStringEFAdjQ i ν₀ hP hwf hR
  obtain ⟨N, hN⟩ := exists_fgStringNilHecke_X_pow_eq_zero Λ hR i ν₀
  exact A.exists_iso_of_epi_E DE (DE.dual adj) k
    (Sl2.NilHeckeData.isNilpotent_app_of_pow_eq_zero hN)
    (Sl2.NilHeckeData.isNilpotent_app_of_pow_eq_zero
      (Sl2.NilHeckeData.dual_X_pow_eq_zero DE adj hN))
    (fun S _ => fgString_finrank_end_simple Λ hR i ν₀ S) hU q₁ q₂

/-- **Webster, arXiv:1309.3796v2, Proposition 5.12, for `Fᵢ`**: for `U` simple, any two simple
quotients of `Fᵢ U` are isomorphic compatibly with the quotient maps, so the head of `Fᵢ U` is
simple (Chuang–Rouquier, arXiv:math/0407205v2, Proposition 5.20). -/
theorem fgString_head_FQ (hR : KLR.IsRouquierQ C (Q))
    [∀ m, IsNoetherianRing (Str m)] [∀ m, IsArtinianRing (Str m)] (hi : i ∉ ν₀)
    {U : ModuleTower.FGTower Str} (hU : Simple U) {S₁ S₂ : ModuleTower.FGTower Str}
    [Simple S₁] [Simple S₂]
    (q₁ : (fgStringF (k := k) (Q := Q) Λ i ν₀).obj U ⟶ S₁)
    (q₂ : (fgStringF (k := k) (Q := Q) Λ i ν₀).obj U ⟶ S₂)
    [Epi q₁] [Epi q₂] :
    ∃ e : S₁ ≅ S₂, q₁ ≫ e.hom = q₂ := by
  have hP := coverRelsNegligible_noRelations.{u, u, u} (Λ := Λ) (C := C) (hQ := hR)
    (hc := coverDotCentral Λ C hR)
    (o := (blockWeight (cyclotomicCoverWeightDatum Λ C)
      (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 : I ⊕ Fin ℓ → ℤ))
  have hwf := wfDom_noRelations.{u, u, u, u, u}
    (signature (coordinateDatum Λ C) (redWeight (cyclotomicCoverWeightDatum Λ C))) k
  have : ∀ i j, i ≠ j → Q i j = Q i j := fun _ _ _ => rfl
  let A := fgStringWeakSl2Q i ν₀ hP hwf hR hi
  have : A.E.Additive := fgStringE_additive Λ hR i ν₀
  have : A.F.Additive := fgStringF_additive (k := k) (Q := Q) Λ i ν₀
  obtain ⟨B, hB⟩ := exists_subsingleton_stringAlg (k := k) Λ hR i ν₀
  have := ModuleTower.isArtinianObject hB
  have := ModuleTower.isNoetherianObject hB
  have : A.E.Linear k := fgStringE_linear (k := k) Λ hR i ν₀
  have : A.F.Linear k := fgStringF_linear (k := k) (Q := Q) Λ i ν₀
  let DE := fgStringNilHecke Λ hR i ν₀
  let adj := fgStringEFAdjQ i ν₀ hP hwf hR
  obtain ⟨N, hN⟩ := exists_fgStringNilHecke_X_pow_eq_zero Λ hR i ν₀
  exact A.exists_iso_of_epi_F DE (DE.dual adj) k
    (Sl2.NilHeckeData.isNilpotent_app_of_pow_eq_zero hN)
    (Sl2.NilHeckeData.isNilpotent_app_of_pow_eq_zero
      (Sl2.NilHeckeData.dual_X_pow_eq_zero DE adj hN))
    (fun S _ => fgString_finrank_end_simple Λ hR i ν₀ S) hU q₁ q₂

end CL

end Categorification.Stendhal

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackModuleTowerSl2
import Categorification.WeightedKLR.RedStrands.DoubleCLBlackActionQ
import Categorification.Algebra.ModuleTowerSl2
import Categorification.WeightedKLR.RedStrands.BlackModuleTowerFiniteQ
import Categorification.WeightedKLR.RedStrands.BlackModuleEFTransportQ
import Categorification.WeightedKLR.RedStrands.BlackModuleEFOutsideContentCLQ
import Categorification.WeightedKLR.RedStrands.CoordinateWeightPairing

/-!
# A weak `𝔰𝔩₂`-categorification along an `i`-string

For a black content `ν₀` with `i ∉ ν₀`, Webster's functors `Fᵢ` and `Eᵢ` (arXiv:1309.3796v2,
§4.6) on the finitely generated modules over the tensor product algebras `T^λ` along the
`i`-string through `ν₀`, at standard Khovanov–Lauda black scalars, form a weak
`𝔰𝔩₂`-categorification in the sense of Chuang–Rouquier (arXiv:math/0407205v2, §5.1.1)
(`fgStringWeakSl2Q`). The simple modules at level `m` have weight `⟨i, λ - ν_m⟩`, the pairing of
`i` with the weight of the content `ν_m = i^m + ν₀` (`stringWt`). The relation
`[Eᵢ Fᵢ M] - [Fᵢ Eᵢ M] = ⟨i, λ - ν_m⟩ [M]` comes from Webster's Theorem 4.31 in the form
`clBlackModuleEFEquivQ`, `clBlackModuleFEEquivQ` and, at the bottom of the string,
`clBlackModuleEFEquivOfNotMemQ`. This is the setting of Webster's Proposition 5.12 and of his use
of Chuang–Rouquier's results in §5.

This is the version of `BlackModuleTowerSl2` in which the black strands carry the relations of
Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, Definition 1.1, `r = 1`; `CLQ.pres RD k sc`) instead
of the KL III relations. Each declaration carries the suffix `Q`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory Limits QuantumGroup QuantumGroup.UDot KL3.Diagram DoubleDiagram

universe u v

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Weight

variable {I : Type u} {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (C : CartanDatum I) (i : I)
  (ν₀ : Multiset I)

end Weight

section Factors

variable {R : Type*} [Ring R] {Y M N : Type v} [AddCommGroup Y] [Module R Y] [AddCommGroup M]
  [Module R M] [AddCommGroup N] [Module R N]

end Factors

section Generic

variable {I : Type u} [DecidableEq I] {k : Type u} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin ℓ → I →₀ ℕ) {C : CartanDatum I}
  (hQ : KLR.IsRouquierQ C Q) (i : I) (ν₀ : Multiset I)

end Generic

section CL

open CategoryTheory.Idempotents StringDiagrams KLR TwoRep CyclotomicAction InductionAlong

open scoped Classical

variable {I : Type u} {ℓ : ℕ} (i : I) (ν₀ : Multiset I) {Λ : Fin ℓ → I →₀ ℕ}
  {C : CartanDatum I} {k : Type u} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {hQ : IsRouquierQ C Q}

local notation "KL" => blackScalarsQ Λ C hQ
local notation "Str" => StringAlg (k := k) (Q := Q) Λ i ν₀

variable {P : Presentation.{u, u}
    (signature (coordinateDatum Λ C) (redWeight (cyclotomicCoverWeightDatum Λ C))) k}
  (hP : CoverRelsNegligible.{u, u, u} Λ C hQ (coverDotCentral Λ C hQ)
    (blockWeight (cyclotomicCoverWeightDatum Λ C) (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 :
      I ⊕ Fin ℓ → ℤ) P)
  (hwf : P.WFDom)

set_option hygiene false in
local notation "Ef" => fgStringE (k := k) (Q := Q) (C := C) Λ hR i ν₀
local notation "Ff" => fgStringF (k := k) (Q := Q) Λ i ν₀

include hP hwf in
/-- **`[Eᵢ Fᵢ M] - [Fᵢ Eᵢ M] = ⟨i, λ - ν_m⟩ [M]`** along the `i`-string through `ν₀ ∌ i`
(Webster, arXiv:1309.3796v3, Theorem 4.31), on composition factors at each level. -/
theorem fgString_compositionFactors_EF_sub_FEQ (hR : KLR.IsRouquierQ C (Q))
    [∀ m, IsNoetherianRing (Str m)] [∀ m, IsArtinianRing (Str m)] (hi : i ∉ ν₀)
    (X : ModuleTower.FGTower Str) (n : ℕ)
    (c : Module.SimpleClass.{u, u} (Str n)) :
    (Module.compositionFactors (Str n)
        (((Ef).obj ((Ff).obj X)).obj n) c : ℤ) -
      Module.compositionFactors (Str n)
        (((Ff).obj ((Ef).obj X)).obj n) c =
      stringWt Λ C i ν₀ n * Module.compositionFactors (Str n) (X.obj n) c := by
  have hM := ModuleTower.isFiniteLength_obj (A := Str) X n
  cases n with
  | zero =>
    have hz : IsZero (((Ff).obj ((Ef).obj X)).obj 0) :=
      fgStringF_isZero_zero (k := k) (Q := Q) Λ i ν₀ ((Ef).obj X)
    have : Subsingleton (((Ff).obj ((Ef).obj X)).obj 0) := ModuleCat.subsingleton_of_isZero hz
    have h0 : Module.compositionFactors (Str 0) (((Ff).obj ((Ef).obj X)).obj 0) = 0 :=
      Module.compositionFactors_of_subsingleton
    rw [h0, Finsupp.coe_zero, Pi.zero_apply, Nat.cast_zero, sub_zero]
    have e := clBlackModuleEFEquivOfNotMemQ hP hwf i ν₀ (X.obj 0) hi
    have := compositionFactors_of_equiv_pi (Y := (((Ef).obj ((Ff).obj X)).obj 0)) e hM c
    have h0' : 0 ≤ ip (coordinateDatum Λ C) i (downRightWeight (coordinateDatum Λ C)
        (coordinateRedWeights Λ C) ν₀) := stringWt_zero_nonneg Λ C i ν₀ hi
    rw [Fintype.card_fin, Int.toNat_of_nonneg h0'] at this
    exact this
  | succ m =>
    have hN := ModuleTower.isFiniteLength_obj (A := Str) ((Ff).obj ((Ef).obj X)) (m + 1)
    have hY := ModuleTower.isFiniteLength_obj (A := Str) ((Ef).obj ((Ff).obj X)) (m + 1)
    have h' : stringWt Λ C i ν₀ (m + 1) = ip (coordinateDatum Λ C) i (downRightWeight
        (coordinateDatum Λ C) (coordinateRedWeights Λ C) ({i} + stringWeight i ν₀ m)) := rfl
    rw [h']
    by_cases h : 0 ≤ ip (coordinateDatum Λ C) i (downRightWeight
        (coordinateDatum Λ C) (coordinateRedWeights Λ C) ({i} + stringWeight i ν₀ m))
    · have e := clBlackModuleEFEquivQ hP hwf i (stringWeight i ν₀ m) (X.obj (m + 1)) h
      have := compositionFactors_sub_of_equiv_prod (Y := (((Ef).obj ((Ff).obj X)).obj (m + 1)))
        (N := (((Ff).obj ((Ef).obj X)).obj (m + 1))) e hM hN c
      rw [Fintype.card_fin, Int.toNat_of_nonneg h] at this
      exact this
    · have hn := le_of_lt (not_le.mp h)
      have e := clBlackModuleFEEquivQ hP hwf i (stringWeight i ν₀ m) (X.obj (m + 1)) hn
      have := compositionFactors_sub_of_equiv_prod (N := (((Ef).obj ((Ff).obj X)).obj (m + 1)))
        (Y := (((Ff).obj ((Ef).obj X)).obj (m + 1))) e hM hY c
      rw [Fintype.card_fin, Int.toNat_of_nonneg (neg_nonneg.mpr hn)] at this
      rw [← neg_sub]
      refine (congrArg Neg.neg this).trans ?_
      rw [neg_mul, neg_neg]
      rfl

include hP hwf in
/-- **The weak `𝔰𝔩₂`-categorification along an `i`-string** (Webster, arXiv:1309.3796v3,
Theorem 4.31, in the sense of Chuang–Rouquier, arXiv:math/0407205v2, §5.1.1): on finitely
generated modules over the algebras `T^λ_{ν₀ + m i}` (`i ∉ ν₀`), the functors `Eᵢ`, `Fᵢ` are
biadjoint and their classes give an `𝔰𝔩₂`-action on the Grothendieck group in which the simple
modules at level `m` have weight `⟨i, λ - ν₀ - m i⟩`. -/
def fgStringWeakSl2Q (hR : KLR.IsRouquierQ C (Q))
    [∀ m, IsNoetherianRing (Str m)] [∀ m, IsArtinianRing (Str m)] (hi : i ∉ ν₀) :
    Sl2.WeakSl2 (ModuleTower.FGTower Str) (ModuleTower.K0Index Str)
      (ModuleTower.K0Index Str →₀ ℚ) :=
  ModuleTower.weakSl2
    (exists_subsingleton_stringAlg (k := k) Λ hR i ν₀).choose_spec
    (Ef) (Ff) (fgStringEFAdjQ i ν₀ hP hwf hR) (fgStringFEAdj Λ hR i ν₀)
    (stringWt Λ C i ν₀) (stringWt_succ Λ C i ν₀)
    (fgStringE_isZero (k := k) (Q := Q) (C := C) Λ hR i ν₀)
    (fgStringF_isZero_zero (k := k) (Q := Q) Λ i ν₀)
    (fgStringF_isZero (k := k) (Q := Q) Λ i ν₀)
    (fgString_compositionFactors_EF_sub_FEQ i ν₀ hP hwf hR hi)

end CL

end Categorification.Stendhal

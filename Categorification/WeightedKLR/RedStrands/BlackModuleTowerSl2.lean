/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.ModuleTowerSl2
import Categorification.WeightedKLR.RedStrands.BlackModuleTowerFinite
import Categorification.WeightedKLR.RedStrands.BlackModuleEFTransport
import Categorification.WeightedKLR.RedStrands.BlackModuleEFOutsideContentCL
import Categorification.WeightedKLR.RedStrands.CoordinateWeightPairing

/-!
# A weak `𝔰𝔩₂`-categorification along an `i`-string

For a black content `ν₀` with `i ∉ ν₀`, Webster's functors `Fᵢ` and `Eᵢ` (arXiv:1309.3796v2,
§4.6) on the finitely generated modules over the tensor product algebras `T^λ` along the
`i`-string through `ν₀`, at standard Khovanov–Lauda black scalars, form a weak
`𝔰𝔩₂`-categorification in the sense of Chuang–Rouquier (arXiv:math/0407205v2, §5.1.1)
(`fgStringWeakSl2`). The simple modules at level `m` have weight `⟨i, λ - ν_m⟩`, the pairing of
`i` with the weight of the content `ν_m = i^m + ν₀` (`stringWt`). The relation
`[Eᵢ Fᵢ M] - [Fᵢ Eᵢ M] = ⟨i, λ - ν_m⟩ [M]` comes from Webster's Theorem 4.31 in the form
`clBlackModuleEFEquiv`, `clBlackModuleFEEquiv` and, at the bottom of the string,
`clBlackModuleEFEquivOfNotMem`. This is the setting of Webster's Proposition 5.12 and of his use
of Chuang–Rouquier's results in §5.
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

/-- The weight `⟨i, λ - ν_m⟩` of level `m` of the `i`-string through `ν₀`. -/
def stringWt (m : ℕ) : ℤ :=
  ip (coordinateDatum Λ C) i (downRightWeight (coordinateDatum Λ C) (coordinateRedWeights Λ C)
    (stringWeight i ν₀ m))

theorem stringWt_succ (m : ℕ) : stringWt Λ C i ν₀ (m + 1) = stringWt Λ C i ν₀ m - 2 := by
  simp only [stringWt, ip_downRightWeight, stringWeight_succ, Multiset.map_add,
    Multiset.sum_add, Multiset.map_singleton, Multiset.sum_singleton,
    WeightDatum.pair_iY_iX_self]
  ring

theorem stringWt_zero_nonneg (hi : i ∉ ν₀) : 0 ≤ stringWt Λ C i ν₀ 0 :=
  ip_nonneg_of_notMem (RD := coordinateDatum Λ C) (Λ := coordinateRedWeights Λ C) i ν₀ hi

end Weight

section Factors

variable {R : Type*} [Ring R] {Y M N : Type v} [AddCommGroup Y] [Module R Y] [AddCommGroup M]
  [Module R M] [AddCommGroup N] [Module R N]

/-- If `Y ≅ N ⊕ M^ι` with `M`, `N` of finite length and `ι` finite, then
`[Y] - [N] = |ι| [M]`. -/
theorem compositionFactors_sub_of_equiv_prod {ι : Type*} [Fintype ι] (e : Y ≃ₗ[R] N × (ι → M))
    (hM : IsFiniteLength R M) (hN : IsFiniteLength R N) (c : Module.SimpleClass R) :
    (Module.compositionFactors R Y c : ℤ) - Module.compositionFactors R N c =
      Fintype.card ι * Module.compositionFactors R M c := by
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hM
  have hMt : IsFiniteLength R (Fin (Fintype.card ι) → M) :=
    isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  have e' : Y ≃ₗ[R] N × (Fin (Fintype.card ι) → M) := e.trans
    ((LinearEquiv.refl R N).prodCongr (LinearEquiv.funCongrLeft R M (Fintype.equivFin ι).symm))
  rw [Module.compositionFactors_congr e'.symm, Module.compositionFactors_prod hN hMt,
    Module.compositionFactors_pi_fin]
  simp

/-- If `Y ≅ M^ι` with `M` of finite length and `ι` finite, then `[Y] = |ι| [M]`. -/
theorem compositionFactors_of_equiv_pi {ι : Type*} [Fintype ι] (e : Y ≃ₗ[R] (ι → M))
    (hM : IsFiniteLength R M) (c : Module.SimpleClass R) :
    (Module.compositionFactors R Y c : ℤ) = Fintype.card ι * Module.compositionFactors R M c := by
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hM
  have e' : Y ≃ₗ[R] (Fin (Fintype.card ι) → M) :=
    e.trans (LinearEquiv.funCongrLeft R M (Fintype.equivFin ι).symm)
  rw [Module.compositionFactors_congr e'.symm, Module.compositionFactors_pi_fin]
  simp

end Factors

section Generic

variable {I : Type u} [DecidableEq I] {k : Type u} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin ℓ → I →₀ ℕ) {C : CartanDatum I}
  (hQ : KLR.IsRouquierQ C Q) (i : I) (ν₀ : Multiset I)

include hQ in
theorem isArtinianRing_stringAlg (m : ℕ) : IsArtinianRing (StringAlg (Q := Q) Λ i ν₀ m) := by
  have := tensorProductAlgebra_op_finite Λ hQ (stringWeight i ν₀ m)
  exact IsArtinianRing.of_finite k _

include hQ in
theorem exists_subsingleton_stringAlg :
    ∃ N : ℕ, ∀ m, N ≤ m → Subsingleton (StringAlg (Q := Q) Λ i ν₀ m) := by
  obtain ⟨N, hN⟩ := subsingleton_stringWeight Q Λ i ν₀ hQ
  refine ⟨N, fun m hm => ?_⟩
  have := hN m hm
  exact MulOpposite.op_surjective.subsingleton

theorem fgStringE_isZero (X : FGStringModules (Q := Q) Λ i ν₀) (n : ℕ)
    (hX : IsZero (X.obj (n + 1))) : IsZero (((fgStringE Λ hQ i ν₀).obj X).obj n) := by
  have : (blackE Q Λ i (stringWeight i ν₀ n)).IsRightAdjoint :=
    ⟨_, ⟨blackAdjunction Q Λ i (stringWeight i ν₀ n)⟩⟩
  exact (blackE Q Λ i (stringWeight i ν₀ n)).map_isZero hX

theorem fgStringF_isZero_zero (X : FGStringModules (Q := Q) Λ i ν₀) :
    IsZero (((fgStringF Λ i ν₀).obj X).obj 0) :=
  isZero_zero _

theorem fgStringF_isZero (X : FGStringModules (Q := Q) Λ i ν₀) (n : ℕ)
    (hX : IsZero (X.obj n)) : IsZero (((fgStringF Λ i ν₀).obj X).obj (n + 1)) := by
  have : (blackF Q Λ i (stringWeight i ν₀ n)).IsLeftAdjoint :=
    ⟨_, ⟨blackAdjunction Q Λ i (stringWeight i ν₀ n)⟩⟩
  exact (blackF Q Λ i (stringWeight i ν₀ n)).map_isZero hX

end Generic

section CL

open CategoryTheory.Idempotents StringDiagrams KLR TwoRep CyclotomicAction InductionAlong

open scoped Classical

variable {I : Type u} {ℓ : ℕ} (i : I) (ν₀ : Multiset I) {Λ : Fin ℓ → I →₀ ℕ}
  {C : CartanDatum I} {k : Type u} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {hQ : IsRouquierQ C Q}

local notation "KL" => (CL.CLScalars.kl : CL.CLScalars C k)
local notation "Str" => StringAlg (k := k) (Q := CL.qCL KL) Λ i ν₀

variable (hstd : ∀ i j, i ≠ j → Q i j = CL.qCL (CL.CLScalars.kl : CL.CLScalars C k) i j)
  {P : Presentation.{u, u}
    (signature (coordinateDatum Λ C) (redWeight (cyclotomicCoverWeightDatum Λ C))) k}
  (hP : CoverRelsNegligible.{u, u, u} Λ C hQ (coverDotCentral Λ C hQ)
    (blockWeight (cyclotomicCoverWeightDatum Λ C) (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 :
      I ⊕ Fin ℓ → ℤ) P)
  (hwf : P.WFDom)

set_option hygiene false in
local notation "Ef" => fgStringE (k := k) (Q := CL.qCL KL) (C := C) Λ hR i ν₀
local notation "Ff" => fgStringF (k := k) (Q := CL.qCL KL) Λ i ν₀

include hstd hP hwf in
/-- **`[Eᵢ Fᵢ M] - [Fᵢ Eᵢ M] = ⟨i, λ - ν_m⟩ [M]`** along the `i`-string through `ν₀ ∌ i`
(Webster, arXiv:1309.3796v3, Theorem 4.31), on composition factors at each level. -/
theorem fgString_compositionFactors_EF_sub_FE (hR : KLR.IsRouquierQ C (CL.qCL KL))
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
      fgStringF_isZero_zero (k := k) (Q := CL.qCL KL) Λ i ν₀ ((Ef).obj X)
    have : Subsingleton (((Ff).obj ((Ef).obj X)).obj 0) := ModuleCat.subsingleton_of_isZero hz
    have h0 : Module.compositionFactors (Str 0) (((Ff).obj ((Ef).obj X)).obj 0) = 0 :=
      Module.compositionFactors_of_subsingleton
    rw [h0, Finsupp.coe_zero, Pi.zero_apply, Nat.cast_zero, sub_zero]
    have e := clBlackModuleEFEquivOfNotMem hstd hP hwf i ν₀ (X.obj 0) hi
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
    · have e := clBlackModuleEFEquiv hstd hP hwf i (stringWeight i ν₀ m) (X.obj (m + 1)) h
      have := compositionFactors_sub_of_equiv_prod (Y := (((Ef).obj ((Ff).obj X)).obj (m + 1)))
        (N := (((Ff).obj ((Ef).obj X)).obj (m + 1))) e hM hN c
      rw [Fintype.card_fin, Int.toNat_of_nonneg h] at this
      exact this
    · have hn := le_of_lt (not_le.mp h)
      have e := clBlackModuleFEEquiv hstd hP hwf i (stringWeight i ν₀ m) (X.obj (m + 1)) hn
      have := compositionFactors_sub_of_equiv_prod (N := (((Ef).obj ((Ff).obj X)).obj (m + 1)))
        (Y := (((Ff).obj ((Ef).obj X)).obj (m + 1))) e hM hY c
      rw [Fintype.card_fin, Int.toNat_of_nonneg (neg_nonneg.mpr hn)] at this
      rw [← neg_sub]
      refine (congrArg Neg.neg this).trans ?_
      rw [neg_mul, neg_neg]
      rfl

include hstd hP hwf in
/-- **The weak `𝔰𝔩₂`-categorification along an `i`-string** (Webster, arXiv:1309.3796v3,
Theorem 4.31, in the sense of Chuang–Rouquier, arXiv:math/0407205v2, §5.1.1): on finitely
generated modules over the algebras `T^λ_{ν₀ + m i}` (`i ∉ ν₀`), the functors `Eᵢ`, `Fᵢ` are
biadjoint and their classes give an `𝔰𝔩₂`-action on the Grothendieck group in which the simple
modules at level `m` have weight `⟨i, λ - ν₀ - m i⟩`. -/
def fgStringWeakSl2 (hR : KLR.IsRouquierQ C (CL.qCL KL))
    [∀ m, IsNoetherianRing (Str m)] [∀ m, IsArtinianRing (Str m)] (hi : i ∉ ν₀) :
    Sl2.WeakSl2 (ModuleTower.FGTower Str) (ModuleTower.K0Index Str)
      (ModuleTower.K0Index Str →₀ ℚ) :=
  ModuleTower.weakSl2
    (exists_subsingleton_stringAlg (k := k) Λ hR i ν₀).choose_spec
    (Ef) (Ff) (fgStringEFAdj i ν₀ hstd hP hwf hR) (fgStringFEAdj Λ hR i ν₀)
    (stringWt Λ C i ν₀) (stringWt_succ Λ C i ν₀)
    (fgStringE_isZero (k := k) (Q := CL.qCL KL) (C := C) Λ hR i ν₀)
    (fgStringF_isZero_zero (k := k) (Q := CL.qCL KL) Λ i ν₀)
    (fgStringF_isZero (k := k) (Q := CL.qCL KL) Λ i ν₀)
    (fgString_compositionFactors_EF_sub_FE i ν₀ hstd hP hwf hR hi)

end CL

end Categorification.Stendhal

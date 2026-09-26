/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Crystal.Lemma39
import Categorification.KLR.Crystal.Cor312

/-!
# The crystal operators `ẽ_i`, `f̃_i` on simple modules

Khovanov–Lauda I (arXiv:0803.4121v2), §3.2 (TeX lines 2196–2238; Kleshchev's book, §5.2). For an
irreducible `M ∈ R(ν)-mod` define

  `ẽ_i M := soc(e_i M)`,   `f̃_i M := hd Ind_{ν,i} M ⊠ L(i)`.

We work ungraded, over any field, for finite-dimensional modules with nilpotent dots, and for `Q`
satisfying the hypotheses of the basis theorem. The weight `i` is a one-element multiset `ν'` all
of whose labels are `i` (`hν'`, `hν'1 : card ν' = 1`).

## Main definitions

* `KLRAlgebra.crystalESub Q μ ν' M` : the socle (the sum of the simple submodules) of the
  `R(μ)`-module `e_{ν'} M = ResLeft Q μ ν' M`; `KLRAlgebra.CrystalE` : **`ẽ_i M`**.
* `KLRAlgebra.crystalFRad Q μ hν' N` : the radical (the intersection of the maximal submodules) of
  `Ind (N ⊠ L(i^n))`; `KLRAlgebra.CrystalF hν' N` : **`f̃_i N = hd Ind (N ⊠ L(i))`** (for general
  `ν'`, `hd Ind (N ⊠ L(i^n))`).

## Main results

* `KLRAlgebra.isAtom_crystalESub`, `KLRAlgebra.isSimpleModule_crystalE`,
  `KLRAlgebra.epsI_crystalE` : for `ε_i(M) > 0`, `ẽ_i M` is irreducible and
  `ε_i(ẽ_i M) = ε_i(M) - 1`; `KLRAlgebra.crystalESub_eq_bot_iff` : `ẽ_i M = 0 ⟺ ε_i(M) = 0`.
  Hence `ε_i(M) = max {n | ẽ_i^n M ≠ 0}` (iterate).
* `KLRAlgebra.isSimpleModule_crystalF`, `KLRAlgebra.epsI_crystalF` : `f̃_i N` is irreducible and
  `ε_i(f̃_i N) = ε_i(N) + 1` (Lemma 3.9).
* `KLRAlgebra.lemma_3_15` (**KL I, Lemma 3.15**): `f̃_i M ≅ N ⟺ ẽ_i N ≅ M`.
* `KLRAlgebra.cor_3_16_f`, `KLRAlgebra.cor_3_16_e` (**KL I, Corollary 3.16**):
  `f̃_i M ≅ f̃_i N ⟺ M ≅ N`, and for `ε_i(M), ε_i(N) > 0`, `ẽ_i M ≅ ẽ_i N ⟺ M ≅ N`.

Lemma 3.13 is treated (in a one-step "top" form) in `Categorification.KLR.Crystal.Tops`.
Lemma 3.14 (`soc(e_i^n M) ≅ (ẽ_i^n M)^{⊕ [n]!}`) is not formalized here.

The proof of Lemma 3.15 follows Kleshchev's Lemma 5.2.3: `f̃_i M ≅ N` gives
`M ⊠ L(i) ↪ Δ_i N` by adjunction, and `M` is then the unique simple submodule of `e_i N`
(Corollary 3.12); conversely the simple submodule `S` of `Δ_i N` (Proposition 3.10) is
`HW(S) ⊠ L(i)` with `HW(S) = ẽ_i N`, which gives a surjection `Ind (ẽ_i N ⊠ L(i)) ↠ N`.
-/

noncomputable section

namespace Categorification.KLR

open Equiv MvPolynomial TypeA MulOpposite Categorification.NilHecke
open scoped TensorProduct

variable {I : Type*} [DecidableEq I]

namespace KLRAlgebra

variable {K : Type*} [Field K] {Q : I → I → MvPolynomial (Fin 2) K}

/-! ### Definitions -/

section Defs

variable {μ ν' : Multiset I}

variable (Q μ ν') (M : Type*) [AddCommGroup M] [Module K M]
  [Module (KLRAlgebra K Q (μ + ν')) M] [IsScalarTower K (KLRAlgebra K Q (μ + ν')) M] in
/-- The socle of the `R(μ)`-module `e_{ν'} M` (the sum of its simple submodules). For
`ν' = {i}` and `M` irreducible, this is `ẽ_i M`. -/
def crystalESub : Submodule (KLRAlgebra K Q μ) (ResLeft Q μ ν' M) :=
  sSup {S | IsAtom S}

variable (Q μ ν') (M : Type*) [AddCommGroup M] [Module K M]
  [Module (KLRAlgebra K Q (μ + ν')) M] [IsScalarTower K (KLRAlgebra K Q (μ + ν')) M] in
/-- **`ẽ_i M = soc(e_i M)`** (for `ν' = {i}`). -/
abbrev CrystalE : Type _ := crystalESub Q μ ν' M

variable (Q μ) {i : I} (hν' : ∀ a ∈ ν', a = i) (N : Type*) [AddCommGroup N] [Module K N]
  [Module (KLRAlgebra K Q μ) N] [IsScalarTower K (KLRAlgebra K Q μ) N]

/-- The radical (the intersection of the maximal submodules) of `Ind (N ⊠ L(i^n))`. -/
def crystalFRad :
    Submodule (KLRAlgebra K Q (μ + ν')) (Ind Q μ ν' (ExtTensor K N (KLRRep hν' Q))) :=
  sInf {P | IsCoatom P}

/-- **`f̃_i N = hd Ind (N ⊠ L(i))`** (for `ν' = {i}`; for general `ν'`, `hd Ind (N ⊠ L(i^n))`). -/
abbrev CrystalF : Type _ :=
  Ind Q μ ν' (ExtTensor K N (KLRRep hν' Q)) ⧸ crystalFRad Q μ hν' N

end Defs

/-! ### `ẽ_i` -/

section CrystalE

variable {μ ν' : Multiset I} {i : I} (hν' : ∀ a ∈ ν', a = i) (hν'1 : Multiset.card ν' = 1)
  {P : I → I → MvPolynomial (Fin 2) K}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)
  {M : Type*} [AddCommGroup M] [Module K M] [Module (KLRAlgebra K Q (μ + ν')) M]
  [IsScalarTower K (KLRAlgebra K Q (μ + ν')) M] [FiniteDimensional K M]
  [IsSimpleModule (KLRAlgebra K Q (μ + ν')) M]
  (hnil : ∀ a, SmulNilpotent (x a : KLRAlgebra K Q (μ + ν')) M)

instance instFiniteDimensionalResLeft : FiniteDimensional K (ResLeft Q μ ν' M) :=
  inferInstanceAs (FiniteDimensional K (ResSub Q μ ν' M))

omit [FiniteDimensional K M] [IsSimpleModule (KLRAlgebra K Q (μ + ν')) M] in
include hnil in
/-- The dots of `R(μ)` act nilpotently on `e_{ν'} M`. -/
theorem smulNilpotent_resLeft (a : Fin (Multiset.card μ)) :
    SmulNilpotent (x a : KLRAlgebra K Q μ) (ResLeft Q μ ν' M) := by
  obtain ⟨m, hm⟩ := hnil (Seq.posL ν' a)
  have key : ∀ (r : ℕ) (w : ResLeft Q μ ν' M),
      ((ResLeft.toRes ((x a : KLRAlgebra K Q μ) ^ r • w) : ResSub Q μ ν' M) : M) =
        (x (Seq.posL ν' a) : KLRAlgebra K Q (μ + ν')) ^ r •
          ((ResLeft.toRes w : ResSub Q μ ν' M) : M) := by
    intro r
    induction r with
    | zero => intro w; rw [pow_zero, pow_zero, one_smul, one_smul]
    | succ r ih =>
      intro w
      rw [pow_succ, mul_smul, ih, resLeft_toRes_smul, coe_resSub_smul, concat_x_tmul_one,
        mul_smul, mem_fixSub.1 (ResLeft.toRes w).2, ← mul_smul, ← pow_succ]
  exact ⟨m, fun w => resLeft_toRes_injective (Subtype.ext (by
    rw [key, hm]; rfl))⟩

omit [FiniteDimensional K M] [IsSimpleModule (KLRAlgebra K Q (μ + ν')) M] in
include hnil in
/-- The dots of `R(μ)` act nilpotently on `ẽ_i M`. -/
theorem smulNilpotent_crystalE (a : Fin (Multiset.card μ)) :
    SmulNilpotent (x a : KLRAlgebra K Q μ) (CrystalE Q μ ν' M) :=
  smulNilpotent_submodule _ (smulNilpotent_resLeft hnil a)

include hν' hν'1 hPQ hP hnil in
/-- For `ε_i(M) > 0`, every simple submodule of `e_i M` is `ẽ_i M`. -/
theorem crystalESub_eq_of_isAtom {S : Submodule (KLRAlgebra K Q μ) (ResLeft Q μ ν' M)}
    (hS : IsAtom S) : crystalESub Q μ ν' M = S := by
  have hpos : 0 < epsI Q (μ + ν') i M := by
    have := epsI_submodule_resLeft hPQ hP hν' S hS.1
    rw [hν'1] at this
    omega
  refine le_antisymm (sSup_le fun T hT => ?_) (le_sSup hS)
  haveI := isSimpleModule_iff_isAtom.2 hS
  haveI := isSimpleModule_iff_isAtom.2 (show IsAtom T from hT)
  exact (cor_3_12_socle hν' hν'1 hPQ hP hnil hpos T S).le

omit [IsSimpleModule (KLRAlgebra K Q (μ + ν')) M] in
include hν' in
/-- `e_i M` has a simple submodule iff `ε_i(M) > 0`. -/
theorem exists_isAtom_resLeft_iff [Nontrivial M] :
    (∃ S : Submodule (KLRAlgebra K Q μ) (ResLeft Q μ ν' M), IsAtom S) ↔
      Multiset.card ν' ≤ epsI Q (μ + ν') i M := by
  rw [← nontrivial_resSub_iff hν']
  constructor
  · rintro ⟨S, hS⟩
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS.1
    exact ⟨⟨ResLeft.toRes v, 0, fun h => hv0 (resLeft_toRes_injective h)⟩⟩
  · intro h
    haveI : Nontrivial (ResLeft Q μ ν' M) := h
    haveI : IsArtinian (KLRAlgebra K Q μ) (ResLeft Q μ ν' M) :=
      isArtinian_of_tower K inferInstance
    haveI : IsAtomic (Submodule (KLRAlgebra K Q μ) (ResLeft Q μ ν' M)) :=
      isAtomic_of_orderBot_wellFounded_lt wellFounded_lt
    obtain ⟨S, hS, -⟩ := (eq_bot_or_exists_atom_le
      (⊤ : Submodule (KLRAlgebra K Q μ) (ResLeft Q μ ν' M))).resolve_left top_ne_bot
    exact ⟨S, hS⟩

include hν' hν'1 hPQ hP hnil in
/-- **`ẽ_i M` is irreducible** if `ε_i(M) > 0` (Corollary 3.12). -/
theorem isAtom_crystalESub (hpos : 0 < epsI Q (μ + ν') i M) :
    IsAtom (crystalESub Q μ ν' M) := by
  haveI := IsSimpleModule.nontrivial (KLRAlgebra K Q (μ + ν')) M
  obtain ⟨S, hS⟩ := (exists_isAtom_resLeft_iff hν' (M := M)).2 (by rw [hν'1]; exact hpos)
  rw [crystalESub_eq_of_isAtom hν' hν'1 hPQ hP hnil hS]
  exact hS

include hν' hν'1 hPQ hP hnil in
theorem isSimpleModule_crystalE (hpos : 0 < epsI Q (μ + ν') i M) :
    IsSimpleModule (KLRAlgebra K Q μ) (CrystalE Q μ ν' M) :=
  isSimpleModule_iff_isAtom.2 (isAtom_crystalESub hν' hν'1 hPQ hP hnil hpos)

omit [IsSimpleModule (KLRAlgebra K Q (μ + ν')) M] in
include hν' in
/-- `ẽ_i M = 0` if `ε_i(M) = 0`. -/
theorem crystalESub_eq_bot [Nontrivial M] (h0 : epsI Q (μ + ν') i M < Multiset.card ν') :
    crystalESub Q μ ν' M = ⊥ := by
  refine sSup_eq_bot.2 fun S hS => ?_
  exact absurd ((exists_isAtom_resLeft_iff hν' (M := M)).1 ⟨S, hS⟩) (by omega)

include hν' hν'1 hPQ hP hnil in
/-- **`ẽ_i M ≠ 0 ⟺ ε_i(M) > 0`**. -/
theorem crystalESub_ne_bot_iff :
    crystalESub Q μ ν' M ≠ ⊥ ↔ 0 < epsI Q (μ + ν') i M := by
  haveI := IsSimpleModule.nontrivial (KLRAlgebra K Q (μ + ν')) M
  constructor
  · intro h
    by_contra h0
    exact h (crystalESub_eq_bot hν' (by omega))
  · intro h
    exact (isAtom_crystalESub hν' hν'1 hPQ hP hnil h).1

include hν' hν'1 hPQ hP hnil in
/-- **`ε_i(ẽ_i M) = ε_i(M) - 1`** for `ε_i(M) > 0` (Corollary 3.12). -/
theorem epsI_crystalE (hpos : 0 < epsI Q (μ + ν') i M) :
    epsI Q μ i (CrystalE Q μ ν' M) + 1 = epsI Q (μ + ν') i M := by
  haveI := isSimpleModule_crystalE hν' hν'1 hPQ hP hnil hpos
  have := cor_3_12_eps hν' hPQ hP (crystalESub Q μ ν' M)
  rwa [hν'1] at this

end CrystalE

/-! ### `f̃_i` -/

section CrystalF

variable {μ ν' : Multiset I} {i : I} (hν' : ∀ a ∈ ν', a = i)
  {P : I → I → MvPolynomial (Fin 2) K}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)
  {N : Type*} [AddCommGroup N] [Module K N] [Module (KLRAlgebra K Q μ) N]
  [IsScalarTower K (KLRAlgebra K Q μ) N] [FiniteDimensional K N]
  [IsSimpleModule (KLRAlgebra K Q μ) N]
  (hnilN : ∀ a, SmulNilpotent (x a : KLRAlgebra K Q μ) N)

include hν' hPQ hP hnilN in
/-- The radical of `Ind (N ⊠ L(i^n))` is its unique maximal submodule (Lemma 3.9). -/
theorem isCoatom_crystalFRad : IsCoatom (crystalFRad Q μ hν' N) ∧
    ∀ P' : Submodule (KLRAlgebra K Q (μ + ν')) (Ind Q μ ν' (ExtTensor K N (KLRRep hν' Q))),
      IsCoatom P' → P' = crystalFRad Q μ hν' N := by
  obtain ⟨P', hP', huniq, -⟩ := lemma_3_9 hν' hPQ hP hnilN
  have h : crystalFRad Q μ hν' N = P' := by
    refine le_antisymm (sInf_le hP') (le_sInf fun P'' hP'' => (huniq P'' hP'').ge)
  rw [h]
  exact ⟨hP', huniq⟩

include hν' hPQ hP hnilN in
/-- **`f̃_i N` is irreducible** (Lemma 3.9). -/
theorem isSimpleModule_crystalF :
    IsSimpleModule (KLRAlgebra K Q (μ + ν')) (CrystalF Q μ hν' N) :=
  isSimpleModule_iff_isCoatom.2 (isCoatom_crystalFRad hν' hPQ hP hnilN).1

include hν' hPQ hP hnilN in
/-- **`ε_i(f̃_i N) = ε_i(N) + n`** (Lemma 3.9; `n = 1` for `f̃_i`). -/
theorem epsI_crystalF :
    epsI Q (μ + ν') i (CrystalF Q μ hν' N) = epsI Q μ i N + Multiset.card ν' := by
  obtain ⟨P', hP', huniq, heps, -⟩ := lemma_3_9 hν' hPQ hP hnilN
  rw [← heps, ← huniq _ (isCoatom_crystalFRad hν' hPQ hP hnilN).1]

include hν' hPQ hP in
instance instFiniteDimensionalCrystalF : FiniteDimensional K (CrystalF Q μ hν' N) :=
  haveI := finiteDimensional_ind hPQ hP (ExtTensor K N (KLRRep hν' Q)) (Q := Q) (ν := μ)
    (ν' := ν')
  inferInstance

omit [FiniteDimensional K N] [IsSimpleModule (KLRAlgebra K Q μ) N] in
include hν' hPQ hP hnilN in
/-- The dots act nilpotently on `f̃_i N`. -/
theorem smulNilpotent_crystalF (a : Fin (Multiset.card (μ + ν'))) :
    SmulNilpotent (x a : KLRAlgebra K Q (μ + ν')) (CrystalF Q μ hν' N) :=
  smulNilpotent_quotient _ (smulNilpotent_ind_extTensor hPQ hP hnilN (smulNilpotent_klrRep hν') a)

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
include hν' hPQ hP hnilN in
/-- **`f̃_i N` is the only simple quotient of `Ind (N ⊠ L(i^n))`**: a surjection onto a simple
module `L` gives `f̃_i N ≅ L`. -/
theorem nonempty_crystalF_equiv_of_surjective {L : Type*} [AddCommGroup L]
    [Module (KLRAlgebra K Q (μ + ν')) L] [IsSimpleModule (KLRAlgebra K Q (μ + ν')) L]
    (π : Ind Q μ ν' (ExtTensor K N (KLRRep hν' Q)) →ₗ[KLRAlgebra K Q (μ + ν')] L)
    (hπ : Function.Surjective π) :
    Nonempty (CrystalF Q μ hν' N ≃ₗ[KLRAlgebra K Q (μ + ν')] L) := by
  have hc : IsCoatom (LinearMap.ker π) := by
    haveI := IsSimpleModule.congr (π.quotKerEquivOfSurjective hπ)
    exact isSimpleModule_iff_isCoatom.1 inferInstance
  have hk := (isCoatom_crystalFRad hν' hPQ hP hnilN).2 _ hc
  exact ⟨(Submodule.quotEquivOfEq _ _ hk.symm).trans (π.quotKerEquivOfSurjective hπ)⟩

end CrystalF

/-! ### Lemma 3.15 and Corollary 3.16 -/

section Lemma315

variable {μ ν' : Multiset I} {i : I} (hν' : ∀ a ∈ ν', a = i) (hν'1 : Multiset.card ν' = 1)
  {P : I → I → MvPolynomial (Fin 2) K}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)

omit [DecidableEq I] in
theorem finiteDimensional_submodule' {A : Type*} [Ring A] [Algebra K A] {X : Type*}
    [AddCommGroup X] [Module K X] [Module A X] [IsScalarTower K A X] [FiniteDimensional K X]
    (S : Submodule A X) : FiniteDimensional K S :=
  Module.Finite.of_injective (S.subtype.restrictScalars K) Subtype.val_injective

variable {M : Type*} [AddCommGroup M] [Module K M] [Module (KLRAlgebra K Q μ) M]
  [IsScalarTower K (KLRAlgebra K Q μ) M] [FiniteDimensional K M]
  [IsSimpleModule (KLRAlgebra K Q μ) M]
  (hnilM : ∀ a, SmulNilpotent (x a : KLRAlgebra K Q μ) M)
  {N : Type*} [AddCommGroup N] [Module K N] [Module (KLRAlgebra K Q (μ + ν')) N]
  [IsScalarTower K (KLRAlgebra K Q (μ + ν')) N] [FiniteDimensional K N]
  [IsSimpleModule (KLRAlgebra K Q (μ + ν')) N]
  (hnilN : ∀ a, SmulNilpotent (x a : KLRAlgebra K Q (μ + ν')) N)

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
omit [FiniteDimensional K M] in
include hν' hν'1 hPQ hP hnilN in
/-- **KL I, Lemma 3.15**, `⇒`: `f̃_i M ≅ N` implies `ẽ_i N ≅ M`. -/
theorem crystalE_equiv_of_crystalF_equiv
    (ψ : CrystalF Q μ hν' M ≃ₗ[KLRAlgebra K Q (μ + ν')] N) :
    Nonempty (CrystalE Q μ ν' N ≃ₗ[KLRAlgebra K Q μ] M) := by
  haveI := IsSimpleModule.nontrivial (KLRAlgebra K Q μ) M
  haveI := IsSimpleModule.nontrivial (KLRAlgebra K Q (μ + ν')) N
  haveI := isSimpleModule_extTensor hν' (Q := Q) (μ := μ) (V := M)
  let π : Ind Q μ ν' (ExtTensor K M (KLRRep hν' Q)) →ₗ[KLRAlgebra K Q (μ + ν')] N :=
    ψ.toLinearMap ∘ₗ (crystalFRad Q μ hν' M).mkQ
  have hπ : Function.Surjective π :=
    ψ.surjective.comp (crystalFRad Q μ hν' M).mkQ_surjective
  let g := indAdjFwd π
  have hz : indAdjBwd (0 : ExtTensor K M (KLRRep hν' Q) →ₗ[TensorKLR Q μ ν']
      ResSub Q μ ν' N) = 0 := BalancedTensor.extB fun r n => by
    rw [indAdjBwd_tmul, LinearMap.zero_apply, ZeroMemClass.coe_zero, smul_zero,
      LinearMap.zero_apply]
  have hg0 : g ≠ 0 := by
    intro h0
    obtain ⟨v, hv⟩ := exists_ne (0 : N)
    obtain ⟨w, rfl⟩ := hπ v
    apply hv
    have : π = 0 := by
      rw [← indAdjBwd_indAdjFwd π]
      show indAdjBwd g = 0
      rw [h0, hz]
    rw [this, LinearMap.zero_apply]
  have hg : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot]
    exact (IsSimpleOrder.eq_bot_or_eq_top _).resolve_right fun h =>
      hg0 (LinearMap.ker_eq_top.1 h)
  let θ : M →ₗ[KLRAlgebra K Q μ] ResLeft Q μ ν' N :=
    { toFun := fun m => ResLeft.ofRes (g (ExtTensor.tmul m (lMk hν' Q 1)))
      map_add' := fun m m' => by
        rw [ExtTensor.add_tmul, map_add]; rfl
      map_smul' := fun a m => by
        apply resLeft_toRes_injective
        rw [resLeft_toRes_smul]
        show g (ExtTensor.tmul (a • m) (lMk hν' Q 1)) =
          (a ⊗ₜ[K] (1 : KLRAlgebra K Q ν')) • g (ExtTensor.tmul m (lMk hν' Q 1))
        rw [← map_smul, ExtTensor.smul_tmul, one_smul] }
  have hθ : Function.Injective θ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro m hm
    rw [LinearMap.mem_ker] at hm
    rw [Submodule.mem_bot]
    by_contra hm0
    have h1 : g (ExtTensor.tmul m (lMk hν' Q 1)) = 0 := hm
    rw [← map_zero g] at h1
    exact extTensor_tmul_ne_zero (K := K) (A := KLRAlgebra K Q μ) (B := KLRAlgebra K Q ν') hm0
      (lMk_one_ne_zero (K := K) (Q := Q) hν') (hg h1)
  let e₁ := LinearEquiv.ofInjective θ hθ
  haveI : IsSimpleModule (KLRAlgebra K Q μ) (LinearMap.range θ) := IsSimpleModule.congr e₁.symm
  have hat : IsAtom (LinearMap.range θ) := isSimpleModule_iff_isAtom.1 inferInstance
  have heq := crystalESub_eq_of_isAtom hν' hν'1 hPQ hP hnilN hat
  exact ⟨(LinearEquiv.ofEq _ _ heq).trans e₁.symm⟩

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
include hν' hν'1 hPQ hP hnilM hnilN in
/-- **KL I, Lemma 3.15**, `⇐`: `ẽ_i N ≅ M` implies `f̃_i M ≅ N`. -/
theorem crystalF_equiv_of_crystalE_equiv
    (χ : CrystalE Q μ ν' N ≃ₗ[KLRAlgebra K Q μ] M) :
    Nonempty (CrystalF Q μ hν' M ≃ₗ[KLRAlgebra K Q (μ + ν')] N) := by
  haveI := IsSimpleModule.nontrivial (KLRAlgebra K Q μ) M
  haveI := IsSimpleModule.nontrivial (KLRAlgebra K Q (μ + ν')) N
  haveI : Nontrivial (CrystalE Q μ ν' N) := χ.symm.injective.nontrivial
  have hpos : 0 < epsI Q (μ + ν') i N :=
    (crystalESub_ne_bot_iff hν' hν'1 hPQ hP hnilN).1
      (Submodule.nontrivial_iff_ne_bot.1 inferInstance)
  haveI : Nontrivial (ResSub Q μ ν' N) := (nontrivial_resSub_iff hν').2 (by rw [hν'1]; exact hpos)
  haveI : IsArtinian (TensorKLR Q μ ν') (ResSub Q μ ν' N) := isArtinian_of_tower K inferInstance
  haveI : IsAtomic (Submodule (TensorKLR Q μ ν') (ResSub Q μ ν' N)) :=
    isAtomic_of_orderBot_wellFounded_lt wellFounded_lt
  obtain ⟨S₀, hS₀, -⟩ := (eq_bot_or_exists_atom_le
    (⊤ : Submodule (TensorKLR Q μ ν') (ResSub Q μ ν' N))).resolve_left top_ne_bot
  haveI : IsSimpleModule (TensorKLR Q μ ν') S₀ := isSimpleModule_iff_isAtom.2 hS₀
  haveI : FiniteDimensional K S₀ := finiteDimensional_submodule' S₀
  have hnilS₀ := fun b => smulNilpotent_submodule S₀ (smulNilpotent_resSub (μ := μ) b (hnilN _))
  have hHW : IsSimpleModule (KLRAlgebra K Q μ) (HWSpace Q μ ν' S₀) :=
    isSimpleModule_hwSpace hν' hPQ hP (S := S₀) hnilS₀
  let Φ := hwEquiv hν' hPQ hP hnilS₀
  let θ : HWSpace Q μ ν' S₀ →ₗ[KLRAlgebra K Q μ] ResLeft Q μ ν' N :=
    { toFun := fun w => ResLeft.ofRes ((w : S₀) : ResSub Q μ ν' N)
      map_add' := fun w w' => rfl
      map_smul' := fun a w => rfl }
  have hθ : Function.Injective θ := fun w w' h =>
    Subtype.ext (Subtype.ext (resLeft_toRes_injective h))
  let e₁ := LinearEquiv.ofInjective θ hθ
  haveI : IsSimpleModule (KLRAlgebra K Q μ) (LinearMap.range θ) :=
    @IsSimpleModule.congr _ _ _ _ _ _ _ _ e₁.symm hHW
  have hat : IsAtom (LinearMap.range θ) := isSimpleModule_iff_isAtom.1 inferInstance
  have heq := crystalESub_eq_of_isAtom hν' hν'1 hPQ hP hnilN hat
  let ρ : HWSpace Q μ ν' S₀ ≃ₗ[KLRAlgebra K Q μ] M :=
    e₁.trans ((LinearEquiv.ofEq _ _ heq.symm).trans χ)
  let g : ExtTensor K M (KLRRep hν' Q) →ₗ[TensorKLR Q μ ν'] ResSub Q μ ν' N :=
    S₀.subtype ∘ₗ Φ.toLinearMap ∘ₗ (ExtTensor.congr ρ.symm (LinearEquiv.refl _ _)).toLinearMap
  obtain ⟨v, hv⟩ := exists_ne (0 : M)
  have hg0 : g ≠ 0 := by
    intro h0
    have h1 := LinearMap.congr_fun h0 (ExtTensor.tmul v (lMk hν' Q 1))
    rw [LinearMap.zero_apply] at h1
    have h2 : Φ ((ExtTensor.congr ρ.symm (LinearEquiv.refl _ _))
        (ExtTensor.tmul v (lMk hν' Q 1))) = 0 := Subtype.ext h1
    rw [LinearEquiv.map_eq_zero_iff, LinearEquiv.map_eq_zero_iff] at h2
    exact extTensor_tmul_ne_zero (K := K) (A := KLRAlgebra K Q μ) (B := KLRAlgebra K Q ν') hv
      (lMk_one_ne_zero (K := K) (Q := Q) hν') h2
  exact nonempty_crystalF_equiv_of_surjective hν' hPQ hP hnilM (indAdjBwd g)
    (indAdjBwd_surjective hg0)

set_option synthInstance.maxHeartbeats 200000 in
include hν' hν'1 hPQ hP hnilM hnilN in
/-- **KL I, Lemma 3.15**: for irreducible `M ∈ R(ν)-mod` and `N ∈ R(ν + i)-mod`,
`f̃_i M ≅ N ⟺ ẽ_i N ≅ M`. -/
theorem lemma_3_15 :
    Nonempty (CrystalF Q μ hν' M ≃ₗ[KLRAlgebra K Q (μ + ν')] N) ↔
      Nonempty (CrystalE Q μ ν' N ≃ₗ[KLRAlgebra K Q μ] M) :=
  ⟨fun ⟨ψ⟩ => crystalE_equiv_of_crystalF_equiv hν' hν'1 hPQ hP hnilN ψ,
    fun ⟨χ⟩ => crystalF_equiv_of_crystalE_equiv hν' hν'1 hPQ hP hnilM hnilN χ⟩

end Lemma315

section Cor316

variable {μ ν' : Multiset I} {i : I} (hν' : ∀ a ∈ ν', a = i) (hν'1 : Multiset.card ν' = 1)
  {P : I → I → MvPolynomial (Fin 2) K}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
include hν' hν'1 hPQ hP in
/-- **KL I, Corollary 3.16** (first part): for irreducible `M`, `M'`,
`f̃_i M ≅ f̃_i M' ⟺ M ≅ M'`. -/
theorem cor_3_16_f
    {M : Type*} [AddCommGroup M] [Module K M] [Module (KLRAlgebra K Q μ) M]
    [IsScalarTower K (KLRAlgebra K Q μ) M] [FiniteDimensional K M]
    [IsSimpleModule (KLRAlgebra K Q μ) M]
    (hnilM : ∀ a, SmulNilpotent (x a : KLRAlgebra K Q μ) M)
    {M' : Type*} [AddCommGroup M'] [Module K M'] [Module (KLRAlgebra K Q μ) M']
    [IsScalarTower K (KLRAlgebra K Q μ) M'] [FiniteDimensional K M']
    [IsSimpleModule (KLRAlgebra K Q μ) M']
    (hnilM' : ∀ a, SmulNilpotent (x a : KLRAlgebra K Q μ) M') :
    Nonempty (CrystalF Q μ hν' M ≃ₗ[KLRAlgebra K Q (μ + ν')] CrystalF Q μ hν' M') ↔
      Nonempty (M ≃ₗ[KLRAlgebra K Q μ] M') := by
  haveI := isSimpleModule_crystalF hν' hPQ hP hnilM'
  haveI := instFiniteDimensionalCrystalF hν' hPQ hP (μ := μ) (N := M')
  have hnilF := smulNilpotent_crystalF hν' hPQ hP hnilM'
  obtain ⟨χ'⟩ := crystalE_equiv_of_crystalF_equiv hν' hν'1 hPQ hP hnilF
    (LinearEquiv.refl _ _)
  constructor
  · rintro ⟨ψ⟩
    obtain ⟨χ⟩ := crystalE_equiv_of_crystalF_equiv hν' hν'1 hPQ hP hnilF ψ
    exact ⟨χ.symm.trans χ'⟩
  · rintro ⟨φ⟩
    exact crystalF_equiv_of_crystalE_equiv hν' hν'1 hPQ hP hnilM hnilF (χ'.trans φ.symm)

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
include hν' hν'1 hPQ hP in
/-- **KL I, Corollary 3.16** (second part): for irreducible `N`, `N'` with
`ε_i(N), ε_i(N') > 0`, `ẽ_i N ≅ ẽ_i N' ⟺ N ≅ N'`. -/
theorem cor_3_16_e
    {N : Type*} [AddCommGroup N] [Module K N] [Module (KLRAlgebra K Q (μ + ν')) N]
    [IsScalarTower K (KLRAlgebra K Q (μ + ν')) N] [FiniteDimensional K N]
    [IsSimpleModule (KLRAlgebra K Q (μ + ν')) N]
    (hnilN : ∀ a, SmulNilpotent (x a : KLRAlgebra K Q (μ + ν')) N)
    {N' : Type*} [AddCommGroup N'] [Module K N'] [Module (KLRAlgebra K Q (μ + ν')) N']
    [IsScalarTower K (KLRAlgebra K Q (μ + ν')) N'] [FiniteDimensional K N']
    [IsSimpleModule (KLRAlgebra K Q (μ + ν')) N']
    (hnilN' : ∀ a, SmulNilpotent (x a : KLRAlgebra K Q (μ + ν')) N')
    (hpos' : 0 < epsI Q (μ + ν') i N') :
    Nonempty (CrystalE Q μ ν' N ≃ₗ[KLRAlgebra K Q μ] CrystalE Q μ ν' N') ↔
      Nonempty (N ≃ₗ[KLRAlgebra K Q (μ + ν')] N') := by
  haveI := isSimpleModule_crystalE hν' hν'1 hPQ hP hnilN' hpos'
  haveI : FiniteDimensional K (CrystalE Q μ ν' N') := finiteDimensional_submodule' _
  have hnilE := smulNilpotent_crystalE hnilN'
  obtain ⟨ψ'⟩ := crystalF_equiv_of_crystalE_equiv hν' hν'1 hPQ hP hnilE hnilN'
    (LinearEquiv.refl _ _)
  constructor
  · rintro ⟨χ⟩
    obtain ⟨ψ⟩ := crystalF_equiv_of_crystalE_equiv hν' hν'1 hPQ hP hnilE hnilN χ
    exact ⟨ψ.symm.trans ψ'⟩
  · rintro ⟨φ⟩
    exact crystalE_equiv_of_crystalF_equiv hν' hν'1 hPQ hP hnilN (ψ'.trans φ.symm)

end Cor316

end KLRAlgebra

end Categorification.KLR

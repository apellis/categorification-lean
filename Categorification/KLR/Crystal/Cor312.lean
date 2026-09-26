/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Crystal.Socle

/-!
# KL I, Corollary 3.12: the socle of `e_i M`

Khovanov–Lauda I (arXiv:0803.4121v2), §3.2, **Corollary 3.12** (TeX lines 2188–2194; Kleshchev's
book, Corollaries 5.1.7, 5.1.8). For `M ∈ R(ν)-mod` let
`e_i M = Res^{ν-i, i}_{ν-i} Δ_i M`, i.e. `Δ_i M = 1_{ν-i, i} M` viewed as an `R(ν - i)`-module.

> Let `M ∈ R(ν)-mod` be irreducible with `ε_i(M) > 0`. Then `soc(e_i M)` is irreducible and
> `ε_i(soc(e_i M)) = ε_i(M) - 1`. Socles of `e_i M` are pairwise non-isomorphic for different
> `i ∈ I`.

We work ungraded, for finite-dimensional `M` with nilpotent dots. Here `ν = μ + ν'` with
`ν' = {i}` (`card ν' = 1`, all labels `i`), and `e_i M` is `KLRAlgebra.ResLeft Q μ ν' M`.

## Main results

* `KLRAlgebra.ResLeft Q μ ν' M` : `Δ M` as an `R(μ)`-module (`a ↦ a ⊗ 1`); for `ν' = {i}`
  this is `e_i M`.
* `KLRAlgebra.epsI_submodule_resLeft` : every nonzero `R(μ)`-submodule `S` of `e_{i^n} M`
  (`M` irreducible) has `ε_i(S) + n = ε_i(M)`. The inequality `≥` uses the surjection
  `Ind (S ⊠ R(ν')) ↠ M` and the Shuffle Lemma (`epsI_ind_extTensor_le`).
* `KLRAlgebra.cor_3_12_socle` (**KL I, Corollary 3.12**): `soc(e_i M)` is irreducible: any two
  simple `R(μ)`-submodules of `e_i M` coincide; `KLRAlgebra.cor_3_12_eps` :
  `ε_i(soc(e_i M)) = ε_i(M) - 1`.

The proof is the one of Proposition 3.10 (`Categorification.KLR.Crystal.Socle`): a simple
submodule `S` of `e_i M` meets `Δ_{i^ε} M ≅ K ⊠ L(i^ε)` in a nonzero subspace stable under
`R(μ') ⊗ 1` and under the dots of the first `ε - 1` strands of the `i^ε` block; the last dot then
preserves it too, since `x_1 + ⋯ + x_ε ∈ Sym⁺` acts by zero on `L(i^ε)`.

The last assertion of the corollary is automatic here: for `i ≠ i'` the modules `e_i M` and
`e_{i'} M` are modules over the different algebras `R(ν - i)` and `R(ν - i')`, so their socles
cannot be isomorphic. (In Kleshchev's setting all `e_i M` are modules over the same affine Hecke
algebra, and the assertion has content.)
-/

noncomputable section

namespace Categorification.KLR

open Equiv MvPolynomial TypeA MulOpposite Categorification.NilHecke
open scoped TensorProduct

variable {I : Type*} [DecidableEq I]

namespace KLRAlgebra

variable {K : Type*} [Field K] {Q : I → I → MvPolynomial (Fin 2) K}

/-! ### `ε_i` of induced modules, general second factor -/

section EpsIndGeneral

variable {μ ν' : Multiset I} {i : I}
  {N : Type*} [AddCommGroup N] [Module K N] [Module (KLRAlgebra K Q μ) N]
  [IsScalarTower K (KLRAlgebra K Q μ) N]
  {W : Type*} [AddCommGroup W] [Module K W] [Module (KLRAlgebra K Q ν') W]
  [IsScalarTower K (KLRAlgebra K Q ν') W]
  {P : I → I → MvPolynomial (Fin 2) K}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)

theorem fixSub_ne_bot_of_extTensor' {j : Seq μ} {j' : Seq ν'}
    (h : fixSub K (ExtTensor K N W) (e j ⊗ₜ[K] e j' : TensorKLR Q μ ν') ≠ ⊥) :
    fixSub K N (e j : KLRAlgebra K Q μ) ≠ ⊥ := by
  intro hb
  apply h
  rw [eq_bot_iff]
  intro y hy
  rw [Submodule.mem_bot, ← mem_fixSub.1 hy]
  exact tmul_smul_extTensor_eq_zero (smul_eq_zero_of_fixSub_eq_bot (e_mul_self j) hb) _ y

include hPQ hP in
/-- `ε_i(Ind (N ⊠ W)) ≤ ε_i(N) + card ν'` for any `R(ν')`-module `W`. -/
theorem epsI_ind_extTensor_le :
    epsI Q (μ + ν') i (Ind Q μ ν' (ExtTensor K N W)) ≤ epsI Q μ i N + Multiset.card ν' := by
  rw [epsI_le_iff]
  intro s hs
  obtain ⟨u, j, j', hu, hne⟩ := exists_shuffle_of_fixSub_ind_ne_bot hPQ hP _ hs
  have hj := tailLen_le_epsI (i := i) (fixSub_ne_bot_of_extTensor' hne)
  have := tailLen_le_of_shuffle (i := i) u hu
  omega

end EpsIndGeneral

/-! ### `e_{i^n} M` as an `R(μ)`-module -/

section ResLeft

variable {μ ν' : Multiset I}
  {M : Type*} [AddCommGroup M] [Module K M] [Module (KLRAlgebra K Q (μ + ν')) M]
  [IsScalarTower K (KLRAlgebra K Q (μ + ν')) M]

variable (Q μ ν' M) in
/-- `Δ M = 1_{μ,ν'} M` as an `R(μ)`-module, `a ↦ a ⊗ 1` (for `ν' = {i}` this is `e_i M`). -/
def ResLeft : Type _ := ResSub Q μ ν' M

instance : AddCommGroup (ResLeft Q μ ν' M) := inferInstanceAs (AddCommGroup (ResSub Q μ ν' M))

instance : Module K (ResLeft Q μ ν' M) := inferInstanceAs (Module K (ResSub Q μ ν' M))

instance : Module (KLRAlgebra K Q μ) (ResLeft Q μ ν' M) :=
  Module.compHom (ResSub Q μ ν' M)
    (Algebra.TensorProduct.includeLeft : KLRAlgebra K Q μ →ₐ[K] TensorKLR Q μ ν').toRingHom

/-- The identity `ResLeft → ResSub`. -/
def ResLeft.toRes (v : ResLeft Q μ ν' M) : ResSub Q μ ν' M := v

/-- The identity `ResSub → ResLeft`. -/
def ResLeft.ofRes (v : ResSub Q μ ν' M) : ResLeft Q μ ν' M := v

theorem resLeft_toRes_smul (a : KLRAlgebra K Q μ) (v : ResLeft Q μ ν' M) :
    ResLeft.toRes (a • v) = (a ⊗ₜ[K] (1 : KLRAlgebra K Q ν') : TensorKLR Q μ ν') •
      ResLeft.toRes v := rfl

theorem resLeft_toRes_add (v w : ResLeft Q μ ν' M) :
    ResLeft.toRes (v + w) = ResLeft.toRes v + ResLeft.toRes w := rfl

theorem resLeft_toRes_kSmul (c : K) (v : ResLeft Q μ ν' M) :
    ResLeft.toRes (c • v) = c • ResLeft.toRes v := rfl

theorem resLeft_toRes_zero : ResLeft.toRes (0 : ResLeft Q μ ν' M) = 0 := rfl

theorem resLeft_toRes_injective : Function.Injective (ResLeft.toRes (Q := Q) (μ := μ) (ν' := ν')
    (M := M)) := fun _ _ h => h

instance : IsScalarTower K (KLRAlgebra K Q μ) (ResLeft Q μ ν' M) where
  smul_assoc c a v := by
    apply resLeft_toRes_injective
    show ((c • a) ⊗ₜ[K] (1 : KLRAlgebra K Q ν') : TensorKLR Q μ ν') • ResLeft.toRes v =
      c • ((a ⊗ₜ[K] (1 : KLRAlgebra K Q ν') : TensorKLR Q μ ν') • ResLeft.toRes v)
    rw [← TensorProduct.smul_tmul', smul_assoc]

/-- For an `R(μ)`-submodule `S` of `e_{i^n} M`, the map `S ⊠ R(ν') → Δ M`,
`s ⊗ b ↦ (1 ⊗ b) s`. -/
def resLeftExtMap (S : Submodule (KLRAlgebra K Q μ) (ResLeft Q μ ν' M)) :
    ExtTensor K S (KLRAlgebra K Q ν') →ₗ[TensorKLR Q μ ν'] ResSub Q μ ν' M where
  toFun y := TensorProduct.lift (LinearMap.mk₂ K
      (fun (s : S) (b : KLRAlgebra K Q ν') =>
        ((1 : KLRAlgebra K Q μ) ⊗ₜ[K] b : TensorKLR Q μ ν') • ResLeft.toRes (s : ResLeft Q μ ν' M))
      (fun s s' b => by dsimp only; rw [Submodule.coe_add, resLeft_toRes_add, smul_add])
      (fun c s b => by
        dsimp only; rw [Submodule.coe_smul_of_tower, resLeft_toRes_kSmul, smul_comm])
      (fun s b b' => by dsimp only; rw [TensorProduct.tmul_add, add_smul])
      (fun c s b => by dsimp only; rw [TensorProduct.tmul_smul, smul_assoc]))
    (ExtTensor.equivTensor y)
  map_add' y y' := by rw [map_add, map_add]
  map_smul' t y := by
    refine ExtTensor.smul_eq_induction (F := fun y => TensorProduct.lift (LinearMap.mk₂ K
      (fun (s : S) (b : KLRAlgebra K Q ν') =>
        ((1 : KLRAlgebra K Q μ) ⊗ₜ[K] b : TensorKLR Q μ ν') • ResLeft.toRes (s : ResLeft Q μ ν' M))
      (fun s s' b => by dsimp only; rw [Submodule.coe_add, resLeft_toRes_add, smul_add])
      (fun c s b => by
        dsimp only; rw [Submodule.coe_smul_of_tower, resLeft_toRes_kSmul, smul_comm])
      (fun s b b' => by dsimp only; rw [TensorProduct.tmul_add, add_smul])
      (fun c s b => by dsimp only; rw [TensorProduct.tmul_smul, smul_assoc])) (ExtTensor.equivTensor y))
      (fun y y' => by simp only [map_add]) (by simp only [map_zero]) ?_ t y
    intro a b s b'
    rw [ExtTensor.smul_tmul]
    show ((1 : KLRAlgebra K Q μ) ⊗ₜ[K] (b • b') : TensorKLR Q μ ν') •
        ResLeft.toRes ((a • s : S) : ResLeft Q μ ν' M) =
      (a ⊗ₜ[K] b) • (((1 : KLRAlgebra K Q μ) ⊗ₜ[K] b' : TensorKLR Q μ ν') •
        ResLeft.toRes (s : ResLeft Q μ ν' M))
    rw [Submodule.coe_smul, resLeft_toRes_smul, smul_smul, smul_smul,
      Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
      smul_eq_mul, mul_one]

theorem resLeftExtMap_tmul (S : Submodule (KLRAlgebra K Q μ) (ResLeft Q μ ν' M)) (s : S)
    (b : KLRAlgebra K Q ν') :
    resLeftExtMap S (ExtTensor.tmul s b) =
      ((1 : KLRAlgebra K Q μ) ⊗ₜ[K] b : TensorKLR Q μ ν') • ResLeft.toRes (s : ResLeft Q μ ν' M) :=
  rfl

variable {P : I → I → MvPolynomial (Fin 2) K}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)

include hPQ hP in
/-- For `M` irreducible and a nonzero `R(μ)`-submodule `S ⊆ e_{i^n} M`,
`ε_i(M) ≤ ε_i(S) + n`. -/
theorem epsI_le_of_submodule_resLeft {i : I} [IsSimpleModule (KLRAlgebra K Q (μ + ν')) M]
    (S : Submodule (KLRAlgebra K Q μ) (ResLeft Q μ ν' M)) (hS : S ≠ ⊥) :
    epsI Q (μ + ν') i M ≤ epsI Q μ i S + Multiset.card ν' := by
  have hf0 : resLeftExtMap S ≠ 0 := by
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
    intro h0
    have := LinearMap.congr_fun h0 (ExtTensor.tmul (⟨v, hv⟩ : S) 1)
    rw [resLeftExtMap_tmul, ← Algebra.TensorProduct.one_def, one_smul,
      LinearMap.zero_apply] at this
    exact hv0 this
  exact (epsI_le_of_surjective (indAdjBwd_surjective hf0)).trans
    (epsI_ind_extTensor_le hPQ hP)

/-- For a nonzero `R(μ)`-submodule `S ⊆ e_{i^n} M`, `ε_i(S) + n ≤ ε_i(M)`. -/
theorem epsI_submodule_resLeft_le {i : I} (hν' : ∀ a ∈ ν', a = i)
    (S : Submodule (KLRAlgebra K Q μ) (ResLeft Q μ ν' M)) [Nontrivial S] :
    epsI Q μ i S + Multiset.card ν' ≤ epsI Q (μ + ν') i M := by
  obtain ⟨j, hj, hjt⟩ := exists_tailLen_eq_epsI (Q := Q) (ν := μ) (i := i) (M := S)
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).1 hj
  have hwe := mem_fixSub.1 hw
  have hv : (e (j.append (Seq.constSeq hν')) : KLRAlgebra K Q (μ + ν')) •
      ((ResLeft.toRes ((w : S) : ResLeft Q μ ν' M) : ResSub Q μ ν' M) : M) =
        ((ResLeft.toRes ((w : S) : ResLeft Q μ ν' M) : ResSub Q μ ν' M) : M) := by
    rw [← concat_e_tmul_one_const hν', ← coe_resSub_smul, ← resLeft_toRes_smul,
      ← Submodule.coe_smul, hwe]
  have hne : ((ResLeft.toRes ((w : S) : ResLeft Q μ ν' M) : ResSub Q μ ν' M) : M) ≠ 0 :=
    fun h0 => hw0 (Subtype.ext (Subtype.ext h0))
  have h1 := tailLen_le_epsI (i := i) (fixSub_ne_bot_of_smul_ne_zero (by rwa [hv]))
  have h2 := Seq.le_tailLen_append_const hν' (i := i) j
  omega

include hPQ hP in
/-- **`ε_i` on `e_{i^n} M`**: for `M` irreducible, every nonzero `R(μ)`-submodule `S` of
`e_{i^n} M` has `ε_i(S) + n = ε_i(M)`. -/
theorem epsI_submodule_resLeft {i : I} (hν' : ∀ a ∈ ν', a = i)
    [IsSimpleModule (KLRAlgebra K Q (μ + ν')) M]
    (S : Submodule (KLRAlgebra K Q μ) (ResLeft Q μ ν' M)) (hS : S ≠ ⊥) :
    epsI Q μ i S + Multiset.card ν' = epsI Q (μ + ν') i M := by
  haveI : Nontrivial S := Submodule.nontrivial_iff_ne_bot.2 hS
  exact le_antisymm (epsI_submodule_resLeft_le hν' S)
    (epsI_le_of_submodule_resLeft hPQ hP S hS)

end ResLeft

/-! ### Stable subspaces without the last dot -/

section StableLast

variable {μ ν : Multiset I} {i : I} (hν : ∀ a ∈ ν, a = i)
  {V : Type*} [AddCommGroup V] [Module K V] [Module (KLRAlgebra K Q μ) V]
  [IsScalarTower K (KLRAlgebra K Q μ) V]

/-- `x_1 + ⋯ + x_n` acts by zero on `V ⊠ L(i^n)`. -/
theorem sum_one_tmul_x_smul_eq_zero (y : ExtTensor K V (KLRRep hν Q)) :
    ∑ b, ((1 : KLRAlgebra K Q μ) ⊗ₜ[K] x b : TensorKLR Q μ ν) • y = 0 := by
  rw [← Finset.sum_smul, ← TensorProduct.tmul_sum]
  have : (∑ b, x b : KLRAlgebra K Q ν) = pol (esymm (Fin (Multiset.card ν)) K 1) := by
    rw [MvPolynomial.esymm_one, map_sum]; simp only [pol_X]
  rw [this]
  exact one_tmul_pol_smul_eq_zero hν (esymm_succ_mem_coinvIdeal _ 0) y

include hν in
/-- Variant of `tmul_xDelta_mem`: stability under the dots of all strands but the last one
suffices. -/
theorem tmul_xDelta_mem_of_lt [IsSimpleModule (KLRAlgebra K Q μ) V]
    {P : Submodule K (ExtTensor K V (KLRRep hν Q))} (hP : P ≠ ⊥)
    (ha : ∀ a : KLRAlgebra K Q μ, ∀ y ∈ P, (a ⊗ₜ[K] 1 : TensorKLR Q μ ν) • y ∈ P)
    (hx : ∀ b : Fin (Multiset.card ν), b.val + 1 < Multiset.card ν → ∀ y ∈ P,
      ((1 : KLRAlgebra K Q μ) ⊗ₜ[K] x b : TensorKLR Q μ ν) • y ∈ P)
    (w₀ : V) : ExtTensor.tmul w₀ (lMk hν Q (xDelta (Multiset.card ν))) ∈ P := by
  refine tmul_xDelta_mem (μ := μ) hν hP ha (fun b y hy => ?_) w₀
  by_cases hb : b.val + 1 < Multiset.card ν
  · exact hx b hb y hy
  · have hsum := sum_one_tmul_x_smul_eq_zero (μ := μ) hν y
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b)] at hsum
    rw [eq_neg_of_add_eq_zero_left hsum]
    refine P.neg_mem (P.sum_mem fun b' hb' => hx b' ?_ y hy)
    have hne := Finset.ne_of_mem_erase hb'
    have h1 := b'.2
    have h2 : b'.val ≠ b.val := fun h => hne (Fin.ext h)
    omega

end StableLast

/-! ### Corollary 3.12 -/

section Soc

variable {μ' ν'' ν' : Multiset I} {i : I} (hν'' : ∀ a ∈ ν'', a = i) (hν' : ∀ a ∈ ν', a = i)
  (hν'1 : Multiset.card ν' = 1)
  {P : I → I → MvPolynomial (Fin 2) K}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)
  {M : Type*} [AddCommGroup M] [Module K M] [Module (KLRAlgebra K Q ((μ' + ν'') + ν')) M]
  [IsScalarTower K (KLRAlgebra K Q ((μ' + ν'') + ν')) M]
  (hnil : ∀ a, SmulNilpotent (x a : KLRAlgebra K Q ((μ' + ν'') + ν')) M)
  [FiniteDimensional K M] [IsSimpleModule (KLRAlgebra K Q ((μ' + ν'') + ν')) M]
  (hε : epsI Q ((μ' + ν'') + ν') i M = Multiset.card ν'' + Multiset.card ν')

section Inst

variable [IsSimpleModule (TensorKLR Q μ' (ν'' + ν'))
    (ResSub Q μ' (ν'' + ν') (MAssoc μ' ν'' ν' M))]
  [IsSimpleModule (KLRAlgebra K Q μ')
    (HWSpace Q μ' (ν'' + ν') (ResSub Q μ' (ν'' + ν') (MAssoc μ' ν'' ν' M)))]

set_option maxHeartbeats 400000 in
omit [FiniteDimensional K M] in
include hν'1 hPQ hP hnil hε in
/-- Every nonzero `R(μ' + ν'')`-submodule of `e_i M` contains `socVec w₀`. -/
theorem exists_mem_eq_socVec_resLeft
    (S : Submodule (KLRAlgebra K Q (μ' + ν'')) (ResLeft Q (μ' + ν'') ν' M)) (hS : S ≠ ⊥)
    (w₀ : HWSpace Q μ' (ν'' + ν') (ResSub Q μ' (ν'' + ν') (MAssoc μ' ν'' ν' M))) :
    ∃ v ∈ S, ((ResLeft.toRes v : ResSub Q (μ' + ν'') ν' M) : M) =
      socVec hν'' hν' hPQ hP hnil w₀ := by
  have hνε := forall_add_of_forall hν'' hν'
  have hnilΔ : ∀ b, SmulNilpotent ((1 : KLRAlgebra K Q μ') ⊗ₜ[K] x b :
      TensorKLR Q μ' (ν'' + ν')) (ResSub Q μ' (ν'' + ν') (MAssoc μ' ν'' ν' M)) :=
    fun b => smulNilpotent_resSub b (smulNilpotent_mAssoc hnil _)
  let Φ := hwEquiv hνε hPQ hP hnilΔ
  let P : Submodule K (ExtTensor K
      (HWSpace Q μ' (ν'' + ν') (ResSub Q μ' (ν'' + ν') (MAssoc μ' ν'' ν' M))) (KLRRep hνε Q)) :=
    { carrier := {y | ∃ v ∈ S, (oneConcat Q μ' ν'' : KLRAlgebra K Q (μ' + ν'')) • v = v ∧
        ((ResLeft.toRes v : ResSub Q (μ' + ν'') ν' M) : M) =
          CastMod.val ((Φ y : ResSub Q μ' (ν'' + ν') (MAssoc μ' ν'' ν' M)) :
            MAssoc μ' ν'' ν' M)}
      zero_mem' := ⟨0, S.zero_mem, smul_zero _, by rw [map_zero]; rfl⟩
      add_mem' := by
        rintro y y' ⟨v, hv, hEv, hvy⟩ ⟨v', hv', hEv', hvy'⟩
        refine ⟨v + v', S.add_mem hv hv', by rw [smul_add, hEv, hEv'], ?_⟩
        rw [map_add, resLeft_toRes_add, Submodule.coe_add, Submodule.coe_add, hvy, hvy']
        rfl
      smul_mem' := by
        rintro c y ⟨v, hv, hEv, hvy⟩
        refine ⟨c • v, S.smul_of_tower_mem c hv, by rw [smul_comm, hEv], ?_⟩
        rw [show Φ (c • y) = c • Φ y from Φ.toLinearMap.map_smul_of_tower c y,
          resLeft_toRes_kSmul, Submodule.coe_smul_of_tower, Submodule.coe_smul_of_tower, hvy]
        rfl }
  have hP0 : P ≠ ⊥ := by
    -- a nonzero vector of `S` fixed by `1_{μ',ν''}`
    have hSε := epsI_submodule_resLeft hPQ hP hν' S hS
    haveI : Nontrivial S := Submodule.nontrivial_iff_ne_bot.2 hS
    obtain ⟨j, hj, hjt⟩ := exists_tailLen_eq_epsI (Q := Q) (ν := μ' + ν'') (i := i) (M := S)
    have hjc : j ∈ concatSet μ' ν'' :=
      (mem_concatSet_iff_hasTail hν'').2 (Seq.hasTail_iff.2 (by omega))
    obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).1 hj
    have hw1 : (oneConcat Q μ' ν'' : KLRAlgebra K Q (μ' + ν'')) • w = w := by
      rw [← mem_fixSub.1 hw, smul_smul, oneConcat_mul_e hjc]
    set v₀ : ResLeft Q (μ' + ν'') ν' M := (w : ResLeft Q (μ' + ν'') ν' M)
    have hEv₀ : (oneConcat Q μ' ν'' : KLRAlgebra K Q (μ' + ν'')) • v₀ = v₀ :=
      congrArg Subtype.val hw1
    have hz : CastMod.of (h := (add_assoc μ' ν'' ν').symm)
        ((ResLeft.toRes v₀ : ResSub Q (μ' + ν'') ν' M) : M) ∈
        fixSub K (MAssoc μ' ν'' ν' M) (oneConcat Q μ' (ν'' + ν')) := by
      rw [mem_fixSub, oneConcat_smul_mAssoc hν'' hν', ← coe_resSub_smul, ← resLeft_toRes_smul,
        hEv₀]
    rw [Submodule.ne_bot_iff]
    refine ⟨Φ.symm ⟨_, hz⟩, ⟨v₀, w.2, hEv₀, ?_⟩, ?_⟩
    · show _ = CastMod.val ((Φ (Φ.symm ⟨_, hz⟩) : ResSub Q μ' (ν'' + ν') (MAssoc μ' ν'' ν' M)) :
        MAssoc μ' ν'' ν' M)
      rw [LinearEquiv.apply_symm_apply]; rfl
    · intro h0
      apply hw0
      have h1 := congrArg (fun y => ((Φ y : ResSub Q μ' (ν'' + ν') (MAssoc μ' ν'' ν' M)) :
        MAssoc μ' ν'' ν' M)) h0
      simp only [LinearEquiv.apply_symm_apply, map_zero, ZeroMemClass.coe_zero] at h1
      exact Subtype.ext (resLeft_toRes_injective (Subtype.ext h1))
  have ha : ∀ a : KLRAlgebra K Q μ', ∀ y ∈ P,
      (a ⊗ₜ[K] 1 : TensorKLR Q μ' (ν'' + ν')) • y ∈ P := by
    rintro a y ⟨v, hv, hEv, hvy⟩
    refine ⟨(concat Q μ' ν'' (a ⊗ₜ 1) : KLRAlgebra K Q (μ' + ν'')) • v, S.smul_mem _ hv, ?_, ?_⟩
    · rw [smul_smul, oneConcat_mul_concat]
    · rw [map_smul, concat_tmul_one_smul_mAssoc hν'' hν', ← hvy, resLeft_toRes_smul,
        coe_resSub_smul]
  have hx : ∀ b : Fin (Multiset.card (ν'' + ν')), b.val + 1 < Multiset.card (ν'' + ν') →
      ∀ y ∈ P, ((1 : KLRAlgebra K Q μ') ⊗ₜ[K] x b : TensorKLR Q μ' (ν'' + ν')) • y ∈ P := by
    rintro b hb y ⟨v, hv, hEv, hvy⟩
    have hb' : b.val < Multiset.card ν'' := by
      have := Multiset.card_add ν'' ν'; omega
    let a' : Fin (Multiset.card (μ' + ν'')) := Seq.posR μ' ⟨b.val, hb'⟩
    refine ⟨(x a' : KLRAlgebra K Q (μ' + ν'')) • v, S.smul_mem _ hv, ?_, ?_⟩
    · have hc : (oneConcat Q μ' ν'' : KLRAlgebra K Q (μ' + ν'')) * x a' =
          x a' * oneConcat Q μ' ν'' := (x_mul_eSum a' _).symm
      rw [smul_smul, hc, ← smul_smul, hEv]
    · have hpos : Seq.posL ν' a' =
          Fin.cast (congrArg Multiset.card (add_assoc μ' ν'' ν').symm) (Seq.posR μ' b) :=
        Fin.ext (by simp only [a', Seq.posL_val, Seq.posR_val, Fin.coe_cast])
      have e1 : ((ResLeft.toRes ((x a' : KLRAlgebra K Q (μ' + ν'')) • v) :
          ResSub Q (μ' + ν'') ν' M) : M) =
          (x (Seq.posL ν' a') : KLRAlgebra K Q ((μ' + ν'') + ν')) •
            ((ResLeft.toRes v : ResSub Q (μ' + ν'') ν' M) : M) := by
        rw [resLeft_toRes_smul, coe_resSub_smul, concat_x_tmul_one, mul_smul,
          mem_fixSub.1 (ResLeft.toRes v).2]
      have e2 : CastMod.val ((Φ (((1 : KLRAlgebra K Q μ') ⊗ₜ[K] x b :
          TensorKLR Q μ' (ν'' + ν')) • y) : ResSub Q μ' (ν'' + ν') (MAssoc μ' ν'' ν' M)) :
            MAssoc μ' ν'' ν' M) =
          (x (Fin.cast (congrArg Multiset.card (add_assoc μ' ν'' ν').symm) (Seq.posR μ' b)) :
            KLRAlgebra K Q ((μ' + ν'') + ν')) •
            CastMod.val ((Φ y : ResSub Q μ' (ν'' + ν') (MAssoc μ' ν'' ν' M)) :
              MAssoc μ' ν'' ν' M) := by
        rw [map_smul, one_tmul_x_smul_mAssoc]
      rw [e1, e2, ← hvy, hpos]
  have hmem := tmul_xDelta_mem_of_lt hνε hP0 ha hx w₀
  obtain ⟨v, hv, -, hvy⟩ := hmem
  exact ⟨v, hv, hvy⟩

end Inst

include hν'' hν' hν'1 hPQ hP hnil hε in
/-- Any two simple `R(μ' + ν'')`-submodules of `e_i M` coincide. -/
theorem socle_resLeft_unique
    (S₁ S₂ : Submodule (KLRAlgebra K Q (μ' + ν'')) (ResLeft Q (μ' + ν'') ν' M))
    [IsSimpleModule (KLRAlgebra K Q (μ' + ν'')) S₁]
    [IsSimpleModule (KLRAlgebra K Q (μ' + ν'')) S₂] : S₁ = S₂ := by
  have hνε := forall_add_of_forall hν'' hν'
  haveI := isSimpleModule_castMod (Q := Q) (add_assoc μ' ν'' ν').symm M
  have hε' : epsI Q (μ' + (ν'' + ν')) i (MAssoc μ' ν'' ν' M) = Multiset.card (ν'' + ν') := by
    rw [epsI_castMod, hε, Multiset.card_add]
  obtain ⟨h1, h2, -⟩ := lemma_3_8 hνε hPQ hP (smulNilpotent_mAssoc hnil) hε'
  haveI := IsSimpleModule.nontrivial (KLRAlgebra K Q μ')
    (HWSpace Q μ' (ν'' + ν') (ResSub Q μ' (ν'' + ν') (MAssoc μ' ν'' ν' M)))
  obtain ⟨w₀, hw₀⟩ := exists_ne
    (0 : HWSpace Q μ' (ν'' + ν') (ResSub Q μ' (ν'' + ν') (MAssoc μ' ν'' ν' M)))
  have hA₁ := isSimpleModule_iff_isAtom.1 ‹IsSimpleModule _ S₁›
  have hA₂ := isSimpleModule_iff_isAtom.1 ‹IsSimpleModule _ S₂›
  obtain ⟨v₁, hv₁, e₁⟩ := exists_mem_eq_socVec_resLeft hν'' hν' hν'1 hPQ hP hnil hε S₁ hA₁.1 w₀
  obtain ⟨v₂, hv₂, e₂⟩ := exists_mem_eq_socVec_resLeft hν'' hν' hν'1 hPQ hP hnil hε S₂ hA₂.1 w₀
  have h12 : v₁ = v₂ := Subtype.ext (e₁.trans e₂.symm)
  have hv0 : v₁ ≠ 0 := fun h0 => socVec_ne_zero hν'' hν' hPQ hP hnil hw₀
    (by rw [← e₁, h0]; rfl)
  have hinf : S₁ ⊓ S₂ ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    exact ⟨v₁, ⟨hv₁, h12 ▸ hv₂⟩, hv0⟩
  have hle : S₁ ≤ S₂ := by
    rcases hA₁.le_iff.1 (inf_le_left : S₁ ⊓ S₂ ≤ S₁) with h | h
    · exact absurd h hinf
    · rw [← h]; exact inf_le_right
  exact ((hA₂.le_iff.1 hle).resolve_left hA₁.1)

end Soc

section General

variable {μ ν' : Multiset I} {i : I} (hν' : ∀ a ∈ ν', a = i) (hν'1 : Multiset.card ν' = 1)
  {P : I → I → MvPolynomial (Fin 2) K}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)
  {M : Type*} [AddCommGroup M] [Module K M] [Module (KLRAlgebra K Q (μ + ν')) M]
  [IsScalarTower K (KLRAlgebra K Q (μ + ν')) M] [FiniteDimensional K M]
  [IsSimpleModule (KLRAlgebra K Q (μ + ν')) M]
  (hnil : ∀ a, SmulNilpotent (x a : KLRAlgebra K Q (μ + ν')) M)

include hν' hν'1 hPQ hP hnil in
/-- **KL I, Corollary 3.12** (ungraded): for `M` irreducible (finite-dimensional, nilpotent
dots) with `ε_i(M) > 0`, `soc(e_i M)` is irreducible: any two simple `R(ν - i)`-submodules of
`e_i M` coincide. -/
theorem cor_3_12_socle (hle : 0 < epsI Q (μ + ν') i M)
    (S₁ S₂ : Submodule (KLRAlgebra K Q μ) (ResLeft Q μ ν' M))
    [IsSimpleModule (KLRAlgebra K Q μ) S₁] [IsSimpleModule (KLRAlgebra K Q μ) S₂] :
    S₁ = S₂ := by
  haveI := IsSimpleModule.nontrivial (KLRAlgebra K Q (μ + ν')) M
  obtain ⟨μ', hμ'⟩ := exists_eq_add_replicate (Q := Q) (μ := μ) hν' (M := M) (by rw [hν'1]; omega)
  set d := epsI Q (μ + ν') i M - Multiset.card ν' with hd
  have hε : epsI Q (μ + ν') i M = Multiset.card (Multiset.replicate d i) + Multiset.card ν' := by
    rw [Multiset.card_replicate]; omega
  clear_value d
  subst hμ'
  exact socle_resLeft_unique (ν'' := Multiset.replicate d i)
    (fun a ha => Multiset.eq_of_mem_replicate ha) hν' hν'1 hPQ hP hnil hε S₁ S₂

omit [FiniteDimensional K M] in
include hν' hPQ hP in
/-- **KL I, Corollary 3.12**, second part: `ε_i(soc(e_i M)) = ε_i(M) - 1` (in fact every nonzero
submodule `S` of `e_i M` has `ε_i(S) + 1 = ε_i(M)`, `epsI_submodule_resLeft`). -/
theorem cor_3_12_eps (S : Submodule (KLRAlgebra K Q μ) (ResLeft Q μ ν' M))
    [IsSimpleModule (KLRAlgebra K Q μ) S] :
    epsI Q μ i S + Multiset.card ν' = epsI Q (μ + ν') i M :=
  epsI_submodule_resLeft hPQ hP hν' S (isSimpleModule_iff_isAtom.1 ‹_›).1

end General

end KLRAlgebra

end Categorification.KLR

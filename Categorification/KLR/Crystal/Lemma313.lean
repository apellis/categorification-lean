/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Crystal.Tops
import Categorification.KLR.Crystal.Thm317

/-!
# KL I, Lemma 3.13: iterated crystal operators

Khovanov–Lauda I (arXiv:0803.4121v2), §3.2, **Lemma 3.13** (TeX lines 2211–2218; Kleshchev's
book, Lemma 5.2.1): for an irreducible `M ∈ R(ν)-mod`,

  `soc Δ_{i^n} M ≅ (ẽ_i^n M) ⊠ L(i^n)`,   `hd Ind_{ν,ni} (M ⊠ L(i^n)) ≅ f̃_i^n M`,

and (TeX lines 2204–2206) `ε_i(M) = max {n ≥ 0 | ẽ_i^n M ≠ 0}`.

We work ungraded, over any field `K`, for finite-dimensional modules with nilpotent dots and `Q`
satisfying the hypotheses of the basis theorem, as in `Categorification.KLR.Crystal.CrystalOps`.

## Iterating `ẽ_i` and `f̃_i`

`ẽ_i` takes `R(μ + i)`-modules to `R(μ)`-modules; to iterate it we transport modules along the
equalities of weights `μ + i^{n+1} = (μ + i^n) + i` (`CastMod`), and bundle modules
(`KLRAlgebra.KLRMod Q ν`, an `R(ν)`-module over `K`):

* `KLRAlgebra.KLRMod.eOne`, `KLRAlgebra.KLRMod.fOne` : `ẽ_i`, `f̃_i` on bundled modules;
* `KLRAlgebra.KLRMod.eIter n : KLRMod Q (μ + i^n) → KLRMod Q μ`, **`ẽ_i^n`**;
* `KLRAlgebra.KLRMod.fIter n : KLRMod Q μ → KLRMod Q (μ + i^n)`, **`f̃_i^n`**.

## Proof

A simple module `L` (finite-dimensional, nilpotent dots) with `ε = ε_i(L)` is determined by `ε`
and its *top* `HW(Δ_{i^ε} L)` (Lemma 3.7, `nonempty_equiv_of_hwSpace_equiv`); we write
`KLRAlgebra.KLRMod.IsTop L T` for "`T ≅ HW(Δ_{i^ε} L)`". The one-step results of
`Categorification.KLR.Crystal.Tops` show that `ẽ_i`, `f̃_i` and passing to `HW(soc Δ_{i^n} -)`
preserve tops and shift `ε_i` by `-1`, `+1`, `-n`; iterating gives Lemma 3.13.

## Main results

* `KLRAlgebra.KLRMod.eIter_good` : for `n ≤ ε_i(M)`, `ẽ_i^n M` is simple (finite-dimensional,
  nilpotent dots) with `ε_i(ẽ_i^n M) + n = ε_i(M)`; `KLRAlgebra.KLRMod.eIter_trivial` : `ẽ_i^n M = 0`
  for `n > ε_i(M)`. Hence **`ε_i(M) = max {n | ẽ_i^n M ≠ 0}`**
  (`KLRAlgebra.KLRMod.nontrivial_eIter_iff`).
* `KLRAlgebra.lemma_3_13_soc` (**KL I, Lemma 3.13 (1)**): for `n ≤ ε_i(M)` the simple submodule
  `S` of `Δ_{i^n} M` (`prop_3_10_socle`) satisfies `S ≅ HW(S) ⊠ L(i^n)` with `HW(S) ≅ ẽ_i^n M`.
* `KLRAlgebra.lemma_3_13_hd` (**KL I, Lemma 3.13 (2)**): `hd Ind (N ⊠ L(i^n)) ≅ f̃_i^n N`.
-/

noncomputable section

namespace Categorification.KLR

open Equiv MvPolynomial TypeA MulOpposite Categorification.NilHecke
open scoped TensorProduct

universe u

variable {I : Type u} [DecidableEq I]

namespace KLRAlgebra

variable {K : Type u} [Field K] {Q : I → I → MvPolynomial (Fin 2) K}

/-! ### Transport lemmas -/

section Transport

variable {ν₁ ν₂ : Multiset I}

/-- `CastMod rfl X ≅ X`. -/
def castModRflEquiv (X : Type*) [AddCommGroup X] [Module K X] [Module (KLRAlgebra K Q ν₁) X]
    [IsScalarTower K (KLRAlgebra K Q ν₁) X] :
    CastMod (rfl : ν₁ = ν₁) X ≃ₗ[KLRAlgebra K Q ν₁] X where
  toFun m := CastMod.val m
  invFun m := CastMod.of m
  map_add' _ _ := rfl
  map_smul' r m := by rw [castMod_smul_val, castKLR_rfl]; rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- `CastMod h` is functorial. -/
def castModCongr (h : ν₁ = ν₂) {X Y : Type*} [AddCommGroup X] [Module K X]
    [Module (KLRAlgebra K Q ν₂) X] [IsScalarTower K (KLRAlgebra K Q ν₂) X] [AddCommGroup Y]
    [Module K Y] [Module (KLRAlgebra K Q ν₂) Y] [IsScalarTower K (KLRAlgebra K Q ν₂) Y]
    (e : X ≃ₗ[KLRAlgebra K Q ν₂] Y) : CastMod h X ≃ₗ[KLRAlgebra K Q ν₁] CastMod h Y where
  toFun m := CastMod.of (e (CastMod.val m))
  invFun m := CastMod.of (e.symm (CastMod.val m))
  map_add' m m' := by simp only [CastMod.val, CastMod.of]; exact map_add e _ _
  map_smul' r m := by
    change CastMod.of (e (castKLR Q h r • CastMod.val m)) = CastMod.of (castKLR Q h r • _)
    rw [map_smul]; rfl
  left_inv m := by simp only [CastMod.val, CastMod.of]; exact e.symm_apply_apply _
  right_inv m := by simp only [CastMod.val, CastMod.of]; exact e.apply_symm_apply _

/-- `CastMod h₁ (CastMod h₂ X) ≅ CastMod (h₁.trans h₂) X`. -/
def castModTrans {ν₃ : Multiset I} (h₁ : ν₁ = ν₂) (h₂ : ν₂ = ν₃) (X : Type*) [AddCommGroup X]
    [Module K X] [Module (KLRAlgebra K Q ν₃) X] [IsScalarTower K (KLRAlgebra K Q ν₃) X] :
    CastMod h₁ (CastMod h₂ X) ≃ₗ[KLRAlgebra K Q ν₁] CastMod (h₁.trans h₂) X where
  toFun m := m
  invFun m := m
  map_add' _ _ := rfl
  map_smul' r m := by subst h₁ h₂; rfl
  left_inv _ := rfl
  right_inv _ := rfl

variable {μ ν' : Multiset I}

/-- An isomorphism of `R(μ + ν')`-modules induces `HW(Δ X) ≅ HW(Δ Y)`. -/
def hwResSubEquiv {X Y : Type*} [AddCommGroup X] [Module K X]
    [Module (KLRAlgebra K Q (μ + ν')) X] [IsScalarTower K (KLRAlgebra K Q (μ + ν')) X]
    [AddCommGroup Y] [Module K Y] [Module (KLRAlgebra K Q (μ + ν')) Y]
    [IsScalarTower K (KLRAlgebra K Q (μ + ν')) Y] (e : X ≃ₗ[KLRAlgebra K Q (μ + ν')] Y) :
    HWSpace Q μ ν' (ResSub Q μ ν' X) ≃ₗ[KLRAlgebra K Q μ] HWSpace Q μ ν' (ResSub Q μ ν' Y) where
  toFun w := ⟨resSubMap e.toLinearMap w, fun j => by
    rw [← LinearMap.map_smul, w.2 j, map_zero]⟩
  invFun w := ⟨resSubMap e.symm.toLinearMap w, fun j => by
    rw [← LinearMap.map_smul, w.2 j, map_zero]⟩
  map_add' w w' := Subtype.ext (map_add _ _ _)
  map_smul' a w := Subtype.ext (by
    simp only [RingHom.id_apply, coe_hw_smul]
    exact LinearMap.map_smul _ _ _)
  left_inv w := Subtype.ext (Subtype.ext (e.symm_apply_apply _))
  right_inv w := Subtype.ext (Subtype.ext (e.apply_symm_apply _))

end Transport

/-! ### Bundled modules -/

variable (Q) in
/-- A bundled `R(ν)`-module over `K`. -/
structure KLRMod (ν : Multiset I) where
  /-- The underlying type. -/
  carrier : Type u
  [instAddCommGroup : AddCommGroup carrier]
  [instModuleK : Module K carrier]
  [instModule : Module (KLRAlgebra K Q ν) carrier]
  [instTower : IsScalarTower K (KLRAlgebra K Q ν) carrier]

attribute [instance] KLRMod.instAddCommGroup KLRMod.instModuleK KLRMod.instModule
  KLRMod.instTower

namespace KLRMod

variable {ν ν₁ ν₂ : Multiset I}

instance : CoeSort (KLRMod Q ν) (Type u) := ⟨KLRMod.carrier⟩

/-- Bundle an `R(ν)`-module. -/
abbrev of (M : Type u) [AddCommGroup M] [Module K M] [Module (KLRAlgebra K Q ν) M]
    [IsScalarTower K (KLRAlgebra K Q ν) M] : KLRMod Q ν := ⟨M⟩

/-- `M` is simple, finite-dimensional, and the dots act nilpotently. -/
structure Good (M : KLRMod Q ν) : Prop where
  simple : IsSimpleModule (KLRAlgebra K Q ν) M
  fd : FiniteDimensional K M
  nil : ∀ a, SmulNilpotent (x a : KLRAlgebra K Q ν) M

/-- A module over `R(ν₂)` as a module over `R(ν₁)`, `ν₁ = ν₂`. -/
def cast (h : ν₁ = ν₂) (M : KLRMod Q ν₂) : KLRMod Q ν₁ := of (CastMod h M.carrier)

theorem Good.cast {M : KLRMod Q ν₂} (hM : M.Good) (h : ν₁ = ν₂) : (M.cast h).Good := by
  haveI := hM.simple
  haveI := hM.fd
  refine ⟨isSimpleModule_castMod h M.carrier, inferInstanceAs (FiniteDimensional K M.carrier),
    fun a => ?_⟩
  exact smulNilpotent_castMod (M := M.carrier) (by rw [castKLR_x]; exact hM.nil _)

theorem epsI_cast (i : I) (h : ν₁ = ν₂) (M : KLRMod Q ν₂) :
    epsI Q ν₁ i (M.cast h) = epsI Q ν₂ i M :=
  epsI_castMod h M.carrier i

variable (i : I)

omit [DecidableEq I] in
theorem mem_singleton_eq : ∀ a ∈ ({i} : Multiset I), a = i := fun _ ha =>
  Multiset.mem_singleton.1 ha

/-- **`ẽ_i`** on bundled modules. -/
def eOne {μ : Multiset I} (M : KLRMod Q (μ + {i})) : KLRMod Q μ :=
  of (CrystalE Q μ {i} M.carrier)

/-- **`f̃_i`** on bundled modules. -/
def fOne {μ : Multiset I} (N : KLRMod Q μ) : KLRMod Q (μ + {i}) :=
  of (CrystalF Q μ (mem_singleton_eq i) N.carrier)

omit [DecidableEq I] in
theorem succ_eq (μ : Multiset I) (n : ℕ) :
    μ + Multiset.replicate n i + {i} = μ + Multiset.replicate (n + 1) i := by
  rw [add_assoc, Multiset.replicate_succ, ← Multiset.singleton_add, add_comm (Multiset.replicate n i)]

omit [DecidableEq I] in
theorem zero_eq (μ : Multiset I) : μ = μ + Multiset.replicate 0 i := by simp

/-- **`ẽ_i^n`**: `KLRMod Q (μ + i^n) → KLRMod Q μ`. -/
def eIter (μ : Multiset I) : (n : ℕ) → KLRMod Q (μ + Multiset.replicate n i) →
    KLRMod Q μ
  | 0, M => M.cast (zero_eq i μ)
  | n + 1, M => eIter μ n (eOne i (M.cast (succ_eq i μ n)))

/-- **`f̃_i^n`**: `KLRMod Q μ → KLRMod Q (μ + i^n)`. -/
def fIter (μ : Multiset I) : (n : ℕ) → KLRMod Q μ →
    KLRMod Q (μ + Multiset.replicate n i)
  | 0, N => N.cast (zero_eq i μ).symm
  | n + 1, N => (fOne i (fIter μ n N)).cast (succ_eq i μ n).symm

/-! #### Tops -/

/-- `T ≅ HW(Δ_{i^ε} L)`, `ε = ε_i(L)`: **`T` is the top of `L`**. -/
def IsTop {μ' : Multiset I} (L : KLRMod Q ν) (T : KLRMod Q μ') : Prop :=
  ∃ (ν'' : Multiset I) (_ : ∀ a ∈ ν'', a = i) (h : μ' + ν'' = ν),
    Multiset.card ν'' = epsI Q ν i L ∧
      Nonempty (HWSpace Q μ' ν'' (ResSub Q μ' ν'' (CastMod h L.carrier)) ≃ₗ[KLRAlgebra K Q μ'] T)

variable {i}

theorem IsTop.cast {μ' : Multiset I} {L : KLRMod Q ν₂} {T : KLRMod Q μ'}
    (hL : L.IsTop i T) (h : ν₁ = ν₂) : (L.cast h).IsTop i T := by
  obtain ⟨ν'', hν'', hd, hc, ⟨φ⟩⟩ := hL
  exact ⟨ν'', hν'', hd.trans h.symm, by rw [epsI_cast]; exact hc,
    ⟨(hwResSubEquiv (castModTrans (hd.trans h.symm) h L.carrier)).trans φ⟩⟩

theorem IsTop.of_equiv {μ' : Multiset I} {L L' : KLRMod Q ν} {T : KLRMod Q μ'}
    (hL : L.IsTop i T) (e : L ≃ₗ[KLRAlgebra K Q ν] L') : L'.IsTop i T := by
  obtain ⟨ν'', hν'', hd, hc, ⟨φ⟩⟩ := hL
  exact ⟨ν'', hν'', hd, by rw [← epsI_congr e]; exact hc,
    ⟨(hwResSubEquiv (castModCongr hd e)).symm.trans φ⟩⟩

theorem IsTop.congr {μ' : Multiset I} {L : KLRMod Q ν} {T T' : KLRMod Q μ'}
    (hL : L.IsTop i T) (e : T ≃ₗ[KLRAlgebra K Q μ'] T') : L.IsTop i T' := by
  obtain ⟨ν'', hν'', hd, hc, ⟨φ⟩⟩ := hL
  exact ⟨ν'', hν'', hd, hc, ⟨φ.trans e⟩⟩

theorem exists_isTop {L : KLRMod Q ν} (hL : L.Good) :
    ∃ (μ' : Multiset I) (hd : μ' + Multiset.replicate (epsI Q ν i L.carrier) i = ν),
      L.IsTop i (of (Q := Q) (ν := μ') (HWSpace Q μ' (Multiset.replicate (epsI Q ν i L.carrier) i)
        (ResSub Q μ' (Multiset.replicate (epsI Q ν i L.carrier) i) (CastMod hd L.carrier)))) := by
  haveI := hL.simple
  haveI := IsSimpleModule.nontrivial (KLRAlgebra K Q ν) L
  obtain ⟨s, -, hst⟩ := exists_tailLen_eq_epsI (Q := Q) (ν := ν) (i := i) (M := L.carrier)
  have hle := replicate_le_of_hasTail (Seq.hasTail_iff.2 hst.ge)
  obtain ⟨μ', hμ'⟩ := Multiset.le_iff_exists_add.1 hle
  have hd : μ' + Multiset.replicate (epsI Q ν i L.carrier) i = ν := by
    rw [add_comm]; exact hμ'.symm
  exact ⟨μ', hd, _, fun a ha => Multiset.eq_of_mem_replicate ha, hd,
    Multiset.card_replicate _ _, ⟨LinearEquiv.refl _ _⟩⟩

end KLRMod

/-! ### One step -/

theorem smulNilpotent_resSub_left {μ ν' : Multiset I} {M : Type*} [AddCommGroup M] [Module K M]
    [Module (KLRAlgebra K Q (μ + ν')) M] [IsScalarTower K (KLRAlgebra K Q (μ + ν')) M]
    (a : Fin (Multiset.card μ))
    (h : SmulNilpotent (x (Seq.posL ν' a) : KLRAlgebra K Q (μ + ν')) M) :
    SmulNilpotent ((x a : KLRAlgebra K Q μ) ⊗ₜ[K] (1 : KLRAlgebra K Q ν') : TensorKLR Q μ ν')
      (ResSub Q μ ν' M) := by
  obtain ⟨m, hm⟩ := h
  have key : ∀ (r : ℕ) (w : ResSub Q μ ν' M),
      ((((x a : KLRAlgebra K Q μ) ⊗ₜ[K] (1 : KLRAlgebra K Q ν') : TensorKLR Q μ ν') ^ r • w :
        ResSub Q μ ν' M) : M) = (x (Seq.posL ν' a) : KLRAlgebra K Q (μ + ν')) ^ r • (w : M) := by
    intro r
    induction r with
    | zero => intro w; rw [pow_zero, pow_zero, one_smul, one_smul]
    | succ r ih =>
      intro w
      rw [pow_succ, mul_smul, ih, coe_resSub_smul, concat_x_tmul_one, mul_smul, mem_fixSub.1 w.2,
        ← mul_smul, ← pow_succ]
  exact ⟨m, fun w => Subtype.ext (by rw [key, hm, ZeroMemClass.coe_zero])⟩

namespace KLRMod

variable {i : I} {P : I → I → MvPolynomial (Fin 2) K}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)

omit [DecidableEq I] in
theorem eq_add_replicate {ν'' : Multiset I} (hν'' : ∀ a ∈ ν'', a = i) {n : ℕ}
    (hn : n ≤ Multiset.card ν'') {ν' : Multiset I} (hν' : ∀ a ∈ ν', a = i)
    (hc : Multiset.card ν' = n) :
    ν'' = Multiset.replicate (Multiset.card ν'' - n) i + ν' := by
  rw [Multiset.eq_replicate_card.2 hν'', Multiset.eq_replicate_card.2 hν', hc,
    ← Multiset.replicate_add, Multiset.card_replicate, Nat.sub_add_cancel hn]

include hPQ hP in
/-- **Uniqueness (KL I, Lemma 3.7)**: simple modules with the same `ε_i` and the same top are
isomorphic. -/
theorem nonempty_equiv_of_isTop {ν μ' : Multiset I} {L L' : KLRMod Q ν} (hL : L.Good)
    (hL' : L'.Good) (heps : epsI Q ν i L.carrier = epsI Q ν i L'.carrier) {T : KLRMod Q μ'}
    (hT : L.IsTop i T) (hT' : L'.IsTop i T) : Nonempty (L.carrier ≃ₗ[KLRAlgebra K Q ν] L'.carrier) := by
  obtain ⟨ν₁, hν₁, h₁, hc₁, ⟨φ₁⟩⟩ := hT
  obtain ⟨ν₂, hν₂, h₂, hc₂, ⟨φ₂⟩⟩ := hT'
  have h12 : ν₁ = ν₂ := by
    rw [Multiset.eq_replicate_card.2 hν₁, Multiset.eq_replicate_card.2 hν₂, hc₁, hc₂, heps]
  subst h12
  haveI := hL.simple
  haveI := hL'.simple
  haveI := hL.fd
  haveI := hL'.fd
  haveI := isSimpleModule_castMod (Q := Q) h₁ L.carrier
  haveI := isSimpleModule_castMod (Q := Q) h₂ L'.carrier
  have hnil₁ : ∀ a, SmulNilpotent (x a : KLRAlgebra K Q (μ' + ν₁)) (CastMod h₁ L.carrier) :=
    fun a => smulNilpotent_castMod (M := L.carrier) (by rw [castKLR_x]; exact hL.nil _)
  have hnil₂ : ∀ a, SmulNilpotent (x a : KLRAlgebra K Q (μ' + ν₁)) (CastMod h₂ L'.carrier) :=
    fun a => smulNilpotent_castMod (M := L'.carrier) (by rw [castKLR_x]; exact hL'.nil _)
  have hε₁ : epsI Q (μ' + ν₁) i (CastMod h₁ L.carrier) = Multiset.card ν₁ := by
    rw [epsI_castMod]; exact hc₁.symm
  have hε₂ : epsI Q (μ' + ν₁) i (CastMod h₂ L'.carrier) = Multiset.card ν₁ := by
    rw [epsI_castMod]; exact hc₂.symm
  obtain ⟨e⟩ := nonempty_equiv_of_hwSpace_equiv hν₁ hPQ hP (L := CastMod h₁ L.carrier)
    (L' := CastMod h₂ L'.carrier) hnil₁ hnil₂ hε₁ hε₂ (φ₂.trans φ₁.symm)
  exact ⟨(castModRflEquiv L.carrier).symm.trans ((castModTrans h₁.symm h₁ L.carrier).symm.trans
    ((castModCongr h₁.symm e).trans ((castModTrans h₁.symm h₂ L'.carrier).trans
      (castModRflEquiv L'.carrier))))⟩

include hPQ hP in
/-- `ẽ_i` of a simple module with `ε_i > 0` is simple, with `ε_i` decreased by one. -/
theorem Good.eOne {μ : Multiset I} {M : KLRMod Q (μ + {i})} (hM : M.Good)
    (hpos : 0 < epsI Q (μ + {i}) i M.carrier) :
    (KLRMod.eOne i M).Good ∧
      epsI Q μ i (KLRMod.eOne i M).carrier + 1 = epsI Q (μ + {i}) i M.carrier := by
  haveI := hM.simple
  haveI := hM.fd
  refine ⟨⟨isSimpleModule_crystalE (mem_singleton_eq i) (Multiset.card_singleton i) hPQ hP
    hM.nil hpos, finiteDimensional_submodule' _, smulNilpotent_crystalE hM.nil⟩, ?_⟩
  exact epsI_crystalE (mem_singleton_eq i) (Multiset.card_singleton i) hPQ hP hM.nil hpos

/-- `ẽ_i M = 0` if `ε_i(M) = 0`. -/
theorem Good.eOne_subsingleton {μ : Multiset I} {M : KLRMod Q (μ + {i})} (hM : M.Good)
    (h0 : epsI Q (μ + {i}) i M.carrier = 0) : Subsingleton (KLRMod.eOne i M).carrier := by
  haveI := hM.simple
  haveI := hM.fd
  haveI := IsSimpleModule.nontrivial (KLRAlgebra K Q (μ + {i})) M.carrier
  have := crystalESub_eq_bot (Q := Q) (μ := μ) (M := M.carrier) (mem_singleton_eq i)
    (by rw [Multiset.card_singleton, h0]; exact Nat.one_pos)
  show Subsingleton (crystalESub Q μ {i} M.carrier)
  rw [this]
  infer_instance

include hPQ hP in
/-- `f̃_i N` is simple with `ε_i` increased by `n` (for `hd Ind (N ⊠ L(i^n))`). -/
theorem Good.crystalF {μ ν' : Multiset I} (hν' : ∀ a ∈ ν', a = i) {N : KLRMod Q μ}
    (hN : N.Good) : (of (Q := Q) (ν := μ + ν') (CrystalF Q μ hν' N.carrier)).Good ∧
      epsI Q (μ + ν') i (CrystalF Q μ hν' N.carrier) =
        epsI Q μ i N.carrier + Multiset.card ν' := by
  haveI := hN.simple
  haveI := hN.fd
  exact ⟨⟨isSimpleModule_crystalF hν' hPQ hP hN.nil, instFiniteDimensionalCrystalF hν' hPQ hP,
    smulNilpotent_crystalF hν' hPQ hP hN.nil⟩, epsI_crystalF hν' hPQ hP hN.nil⟩

include hPQ hP in
theorem Good.fOne {μ : Multiset I} {N : KLRMod Q μ} (hN : N.Good) :
    (KLRMod.fOne i N).Good ∧
      epsI Q (μ + {i}) i (KLRMod.fOne i N).carrier = epsI Q μ i N.carrier + 1 :=
  hN.crystalF hPQ hP (mem_singleton_eq i)

omit [DecidableEq I] in
theorem forall_mem_replicate (n : ℕ) : ∀ a ∈ Multiset.replicate n i, a = i := fun _ ha =>
  Multiset.eq_of_mem_replicate ha

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
include hPQ hP in
/-- **`ẽ_i` preserves tops** (`top_crystalE`). -/
theorem IsTop.eOne {μ₀ μ' : Multiset I} {M : KLRMod Q (μ₀ + {i})} (hM : M.Good)
    (hpos : 0 < epsI Q (μ₀ + {i}) i M.carrier) {T : KLRMod Q μ'} (hT : M.IsTop i T) :
    (KLRMod.eOne i M).IsTop i T := by
  haveI := hM.simple
  haveI := hM.fd
  obtain ⟨ν'', hν'', hd, hc, ⟨φ⟩⟩ := hT
  generalize he : epsI Q (μ₀ + {i}) i M.carrier = e at hpos hc
  have hν''eq : ν'' = Multiset.replicate (e - 1) i + {i} := by
    have := eq_add_replicate hν'' (n := 1) (by omega) (mem_singleton_eq i)
      (Multiset.card_singleton i)
    rwa [hc] at this
  subst hν''eq
  have hμ₀ : μ₀ = μ' + Multiset.replicate (e - 1) i := by
    have : μ' + Multiset.replicate (e - 1) i + {i} = μ₀ + {i} := by rw [add_assoc]; exact hd
    exact (add_right_cancel this).symm
  subst hμ₀
  have hε : epsI Q ((μ' + Multiset.replicate (e - 1) i) + {i}) i M.carrier =
      Multiset.card (Multiset.replicate (e - 1) i) + Multiset.card ({i} : Multiset I) := by
    rw [he, Multiset.card_replicate, Multiset.card_singleton]; omega
  obtain ⟨hεE, ⟨ψ⟩⟩ := top_crystalE (forall_mem_replicate (e - 1)) (mem_singleton_eq i)
    (Multiset.card_singleton i) hPQ hP hM.nil hε
  exact ⟨_, forall_mem_replicate (e - 1), rfl, hεE.symm,
    ⟨(hwResSubEquiv (castModRflEquiv _)).trans (ψ.trans φ)⟩⟩

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
include hPQ hP in
/-- **`hd Ind (- ⊠ L(i^n))` preserves tops** (`top_crystalF`). -/
theorem IsTop.crystalF {μ₀ μ' ν' : Multiset I} (hν' : ∀ a ∈ ν', a = i) {N : KLRMod Q μ₀}
    (hN : N.Good) {T : KLRMod Q μ'} (hT : N.IsTop i T) :
    (of (Q := Q) (ν := μ₀ + ν') (CrystalF Q μ₀ hν' N.carrier)).IsTop i T := by
  haveI := hN.simple
  haveI := hN.fd
  obtain ⟨ν'', hν'', hd, hc, ⟨φ⟩⟩ := hT
  subst hd
  obtain ⟨ψ⟩ := top_crystalF hν'' hν' hPQ hP hN.nil hc.symm
  refine ⟨ν'' + ν', fun a ha => ?_, (add_assoc μ' ν'' ν').symm, ?_,
    ⟨ψ.symm.trans ((hwResSubEquiv (castModRflEquiv N.carrier)).symm.trans φ)⟩⟩
  · rcases Multiset.mem_add.1 ha with ha | ha
    · exact hν'' a ha
    · exact hν' a ha
  · rw [Multiset.card_add, hc]; exact ((hN.crystalF hPQ hP hν').2).symm

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
include hPQ hP in
/-- **Socles of `Δ_{i^n}`** (Proposition 3.10, `top_of_socle`): for `n ≤ ε_i(M)` and `S` the
simple submodule of `Δ_{i^n} M`, `HW(S)` is simple with `ε_i(HW(S)) + n = ε_i(M)` and has the
same top as `M`. -/
theorem isTop_socle {μ₀ ν' μ' : Multiset I} (hν' : ∀ a ∈ ν', a = i) {M : KLRMod Q (μ₀ + ν')}
    (hM : M.Good) (hle : Multiset.card ν' ≤ epsI Q (μ₀ + ν') i M.carrier)
    (S : Submodule (TensorKLR Q μ₀ ν') (ResSub Q μ₀ ν' M.carrier))
    [IsSimpleModule (TensorKLR Q μ₀ ν') S] {T : KLRMod Q μ'} (hT : M.IsTop i T) :
    (of (Q := Q) (ν := μ₀) (HWSpace Q μ₀ ν' S)).Good ∧
      epsI Q μ₀ i (HWSpace Q μ₀ ν' S) + Multiset.card ν' = epsI Q (μ₀ + ν') i M.carrier ∧
      (of (Q := Q) (ν := μ₀) (HWSpace Q μ₀ ν' S)).IsTop i T := by
  haveI := hM.simple
  haveI := hM.fd
  obtain ⟨ν'', hν'', hd, hc, ⟨φ⟩⟩ := hT
  generalize he : epsI Q (μ₀ + ν') i M.carrier = e at hle hc ⊢
  have hν''eq : ν'' = Multiset.replicate (e - Multiset.card ν') i + ν' := by
    have := eq_add_replicate hν'' (n := Multiset.card ν') (by omega) hν' rfl
    rwa [hc] at this
  subst hν''eq
  have hμ₀ : μ₀ = μ' + Multiset.replicate (e - Multiset.card ν') i := by
    have : μ' + Multiset.replicate (e - Multiset.card ν') i + ν' = μ₀ + ν' := by
      rw [add_assoc]; exact hd
    exact (add_right_cancel this).symm
  subst hμ₀
  have hε : epsI Q ((μ' + Multiset.replicate (e - Multiset.card ν') i) + ν') i M.carrier =
      Multiset.card (Multiset.replicate (e - Multiset.card ν') i) + Multiset.card ν' := by
    rw [he, Multiset.card_replicate]; omega
  set μ₁ := μ' + Multiset.replicate (e - Multiset.card ν') i
  have hnilS : ∀ b, SmulNilpotent ((1 : KLRAlgebra K Q μ₁) ⊗ₜ[K] x b : TensorKLR Q μ₁ ν') S :=
    fun b => smulNilpotent_submodule S (smulNilpotent_resSub b (hM.nil _))
  haveI : FiniteDimensional K S := finiteDimensional_submodule' S
  haveI := isSimpleModule_hwSpace hν' hPQ hP hnilS
  haveI : FiniteDimensional K (HWSpace Q μ₁ ν' S) := finiteDimensional_submodule' _
  have hnilN : ∀ a, SmulNilpotent (x a : KLRAlgebra K Q μ₁) (HWSpace Q μ₁ ν' S) := fun a =>
    smulNilpotent_hwSpace_of (smulNilpotent_submodule S (smulNilpotent_resSub_left a (hM.nil _)))
  have hform := (socle_resSub_form hν' hPQ hP hM.nil hε S).2
  obtain ⟨hεN, ⟨ψ⟩⟩ := top_of_socle (forall_mem_replicate _) hν' hPQ hP hM.nil hnilN hε S
    (hwEquiv hν' hPQ hP hnilS)
  refine ⟨⟨inferInstance, inferInstance, hnilN⟩, by rw [hform, he], _,
    forall_mem_replicate _, rfl, hεN.symm, ⟨(hwResSubEquiv (castModRflEquiv _)).trans (ψ.trans φ)⟩⟩

/-! ### Iterates -/

section Iter

variable {i : I} {P : I → I → MvPolynomial (Fin 2) K}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)

theorem eIter_zero (μ : Multiset I) (M : KLRMod Q (μ + Multiset.replicate 0 i)) :
    eIter i μ 0 M = M.cast (zero_eq i μ) := rfl

theorem eIter_succ (μ : Multiset I) (n : ℕ) (M : KLRMod Q (μ + Multiset.replicate (n + 1) i)) :
    eIter i μ (n + 1) M = eIter i μ n (eOne i (M.cast (succ_eq i μ n))) := rfl

theorem fIter_zero (μ : Multiset I) (N : KLRMod Q μ) :
    fIter i μ 0 N = N.cast (zero_eq i μ).symm := rfl

theorem fIter_succ (μ : Multiset I) (n : ℕ) (N : KLRMod Q μ) :
    fIter i μ (n + 1) N = (fOne i (fIter i μ n N)).cast (succ_eq i μ n).symm := rfl

include hPQ hP in
/-- **`ẽ_i^n`**: for `n ≤ ε_i(M)`, `ẽ_i^n M` is simple, `ε_i(ẽ_i^n M) + n = ε_i(M)`, and
`ẽ_i^n M` has the same top as `M`. -/
theorem eIter_spec (μ : Multiset I) :
    ∀ (n : ℕ) (M : KLRMod Q (μ + Multiset.replicate n i)),
    M.Good → n ≤ epsI Q (μ + Multiset.replicate n i) i M.carrier →
    (eIter i μ n M).Good ∧ epsI Q μ i (eIter i μ n M).carrier + n =
      epsI Q (μ + Multiset.replicate n i) i M.carrier ∧
      ∀ {μ' : Multiset I} (T : KLRMod Q μ'), M.IsTop i T →
        (eIter i μ n M).IsTop i T := by
  intro n
  induction n with
  | zero =>
    intro M hM _
    rw [eIter_zero]
    exact ⟨hM.cast _, by rw [epsI_cast]; rfl, fun T hT => hT.cast _⟩
  | succ n ih =>
    intro M hM hle
    rw [eIter_succ]
    have hM' := hM.cast (succ_eq i μ n)
    have heps' := epsI_cast i (succ_eq i μ n) M
    obtain ⟨hE, hεE⟩ := hM'.eOne hPQ hP (by rw [heps']; omega)
    obtain ⟨h1, h2, h3⟩ := ih _ hE (by omega)
    exact ⟨h1, by omega, fun T hT => h3 T ((hT.cast (succ_eq i μ n)).eOne hPQ hP hM'
      (by rw [heps']; omega))⟩

theorem subsingleton_cast {ν₁ ν₂ : Multiset I} (h : ν₁ = ν₂) {M : KLRMod Q ν₂}
    (hM : Subsingleton M.carrier) : Subsingleton (M.cast h).carrier := hM

theorem subsingleton_eOne {μ : Multiset I} {M : KLRMod Q (μ + {i})}
    (hM : Subsingleton M.carrier) : Subsingleton (eOne i M).carrier := by
  refine ⟨fun a b => Subtype.ext ?_⟩
  exact Subtype.ext (Subsingleton.elim (α := M.carrier) _ _)

theorem subsingleton_eIter (μ : Multiset I) : ∀ (n : ℕ) (M : KLRMod Q (μ + Multiset.replicate n i)),
    Subsingleton M.carrier → Subsingleton (eIter i μ n M).carrier := by
  intro n
  induction n with
  | zero => intro M hM; exact subsingleton_cast _ hM
  | succ n ih => intro M hM; exact ih _ (subsingleton_eOne (subsingleton_cast _ hM))

include hPQ hP in
/-- `ẽ_i^n M = 0` for `n > ε_i(M)`. -/
theorem eIter_subsingleton (μ : Multiset I) : ∀ (n : ℕ) (M : KLRMod Q (μ + Multiset.replicate n i)),
    M.Good → epsI Q (μ + Multiset.replicate n i) i M.carrier < n →
    Subsingleton (eIter i μ n M).carrier := by
  intro n
  induction n with
  | zero => intro M _ h; omega
  | succ n ih =>
    intro M hM hlt
    rw [eIter_succ]
    have hM' := hM.cast (succ_eq i μ n)
    have heps' := epsI_cast i (succ_eq i μ n) M
    by_cases h0 : epsI Q (μ + Multiset.replicate (n + 1) i) i M.carrier = 0
    · exact subsingleton_eIter μ n _ (hM'.eOne_subsingleton (by rw [heps', h0]))
    · obtain ⟨hE, hεE⟩ := hM'.eOne hPQ hP (by rw [heps']; omega)
      exact ih _ hE (by omega)

include hPQ hP in
/-- **`ε_i(M) = max {n | ẽ_i^n M ≠ 0}`**. -/
theorem nontrivial_eIter_iff {μ : Multiset I} {n : ℕ} {M : KLRMod Q (μ + Multiset.replicate n i)}
    (hM : M.Good) :
    Nontrivial (eIter i μ n M).carrier ↔ n ≤ epsI Q (μ + Multiset.replicate n i) i M.carrier := by
  constructor
  · intro hnt
    by_contra hlt
    haveI := eIter_subsingleton hPQ hP μ n M hM (by omega)
    exact not_nontrivial _ hnt
  · intro hle
    haveI := (eIter_spec hPQ hP μ n M hM hle).1.simple
    exact IsSimpleModule.nontrivial (KLRAlgebra K Q μ) _

include hPQ hP in
/-- **`f̃_i^n`**: `f̃_i^n N` is simple, `ε_i(f̃_i^n N) = ε_i(N) + n`, and `f̃_i^n N` has the same
top as `N`. -/
theorem fIter_spec (μ : Multiset I) :
    ∀ (n : ℕ) (N : KLRMod Q μ), N.Good →
    (fIter i μ n N).Good ∧
      epsI Q (μ + Multiset.replicate n i) i (fIter i μ n N).carrier = epsI Q μ i N.carrier + n ∧
      ∀ {μ' : Multiset I} (T : KLRMod Q μ'), N.IsTop i T →
        (fIter i μ n N).IsTop i T := by
  intro n
  induction n with
  | zero =>
    intro N hN
    rw [fIter_zero]
    exact ⟨hN.cast _, by rw [epsI_cast]; rfl, fun T hT => hT.cast _⟩
  | succ n ih =>
    intro N hN
    rw [fIter_succ]
    obtain ⟨h1, h2, h3⟩ := ih N hN
    obtain ⟨hF, hεF⟩ := h1.fOne hPQ hP
    refine ⟨hF.cast _, by rw [epsI_cast, hεF, h2]; ring, fun T hT => ?_⟩
    exact (IsTop.crystalF hPQ hP (mem_singleton_eq i) h1 (h3 T hT)).cast _

end Iter

end KLRMod

/-! ### Lemma 3.13 -/

section Main

variable {i : I} {P : I → I → MvPolynomial (Fin 2) K}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)

omit [DecidableEq I] in
theorem add_replicate_eq {μ ν' : Multiset I} (hν' : ∀ a ∈ ν', a = i) :
    μ + Multiset.replicate (Multiset.card ν') i = μ + ν' := by
  rw [← Multiset.eq_replicate_card.2 hν']

include hPQ hP in
/-- **KL I, Lemma 3.13 (1), highest weight form**: for `M` irreducible (finite-dimensional,
nilpotent dots) and `n = card ν' ≤ ε_i(M)`, the simple submodule `S` of `Δ_{i^n} M`
(`prop_3_10_socle`) has `HW(S) ≅ ẽ_i^n M`. -/
theorem lemma_3_13_hw {μ ν' : Multiset I} (hν' : ∀ a ∈ ν', a = i) {M : Type u}
    [AddCommGroup M]
    [Module K M] [Module (KLRAlgebra K Q (μ + ν')) M] [IsScalarTower K (KLRAlgebra K Q (μ + ν')) M]
    [FiniteDimensional K M] [IsSimpleModule (KLRAlgebra K Q (μ + ν')) M]
    (hnil : ∀ a, SmulNilpotent (x a : KLRAlgebra K Q (μ + ν')) M)
    (hle : Multiset.card ν' ≤ epsI Q (μ + ν') i M)
    (S : Submodule (TensorKLR Q μ ν') (ResSub Q μ ν' M)) [IsSimpleModule (TensorKLR Q μ ν') S] :
    Nonempty (HWSpace Q μ ν' S ≃ₗ[KLRAlgebra K Q μ] (KLRMod.eIter i μ (Multiset.card ν')
      ((KLRMod.of (Q := Q) (ν := μ + ν') M).cast (add_replicate_eq hν'))).carrier) := by
  have hMb : (KLRMod.of (Q := Q) (ν := μ + ν') M).Good := ⟨inferInstance, inferInstance, hnil⟩
  obtain ⟨μ', hd, hT⟩ := KLRMod.exists_isTop (i := i) hMb
  obtain ⟨h1, h2, h3⟩ := KLRMod.isTop_socle hPQ hP hν' hMb hle S hT
  have hMc := hMb.cast (add_replicate_eq hν')
  obtain ⟨g1, g2, g3⟩ := KLRMod.eIter_spec hPQ hP μ _ _ hMc
    (by rw [KLRMod.epsI_cast]; exact hle)
  refine KLRMod.nonempty_equiv_of_isTop hPQ hP h1 g1 ?_ h3 (g3 _ (hT.cast _))
  rw [KLRMod.epsI_cast] at g2
  exact Nat.add_right_cancel (h2.trans g2.symm)

include hPQ hP in
/-- **KL I, Lemma 3.13 (1)**: for `M` irreducible (finite-dimensional, nilpotent dots) and
`n = card ν' ≤ ε_i(M)`, the socle `S` of `Δ_{i^n} M` (its unique simple submodule,
`prop_3_10_socle`) is `≅ (ẽ_i^n M) ⊠ L(i^n)`. -/
theorem lemma_3_13_soc {μ ν' : Multiset I} (hν' : ∀ a ∈ ν', a = i) {M : Type u}
    [AddCommGroup M]
    [Module K M] [Module (KLRAlgebra K Q (μ + ν')) M] [IsScalarTower K (KLRAlgebra K Q (μ + ν')) M]
    [FiniteDimensional K M] [IsSimpleModule (KLRAlgebra K Q (μ + ν')) M]
    (hnil : ∀ a, SmulNilpotent (x a : KLRAlgebra K Q (μ + ν')) M)
    (hle : Multiset.card ν' ≤ epsI Q (μ + ν') i M)
    (S : Submodule (TensorKLR Q μ ν') (ResSub Q μ ν' M)) [IsSimpleModule (TensorKLR Q μ ν') S] :
    Nonempty (S ≃ₗ[TensorKLR Q μ ν'] ExtTensor K (KLRMod.eIter i μ (Multiset.card ν')
      ((KLRMod.of (Q := Q) (ν := μ + ν') M).cast (add_replicate_eq hν'))).carrier
        (KLRRep hν' Q)) := by
  obtain ⟨e⟩ := lemma_3_13_hw hPQ hP hν' hnil hle S
  have hnilS : ∀ b, SmulNilpotent ((1 : KLRAlgebra K Q μ) ⊗ₜ[K] x b : TensorKLR Q μ ν') S :=
    fun b => smulNilpotent_submodule S (smulNilpotent_resSub b (hnil _))
  haveI : FiniteDimensional K S := finiteDimensional_submodule' S
  exact ⟨(hwEquiv hν' hPQ hP hnilS).symm.trans (ExtTensor.congr e (LinearEquiv.refl _ _))⟩

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
include hPQ hP in
/-- **KL I, Lemma 3.13 (2)**: for `N` irreducible (finite-dimensional, nilpotent dots),
`hd Ind (N ⊠ L(i^n)) ≅ f̃_i^n N` (`n = card ν'`). -/
theorem lemma_3_13_hd {μ ν' : Multiset I} (hν' : ∀ a ∈ ν', a = i) {N : Type u}
    [AddCommGroup N]
    [Module K N] [Module (KLRAlgebra K Q μ) N] [IsScalarTower K (KLRAlgebra K Q μ) N]
    [FiniteDimensional K N] [IsSimpleModule (KLRAlgebra K Q μ) N]
    (hnilN : ∀ a, SmulNilpotent (x a : KLRAlgebra K Q μ) N) :
    Nonempty (CrystalF Q μ hν' N ≃ₗ[KLRAlgebra K Q (μ + ν')]
      ((KLRMod.fIter i μ (Multiset.card ν') (KLRMod.of (Q := Q) (ν := μ) N)).cast
        (add_replicate_eq hν').symm).carrier) := by
  have hNb : (KLRMod.of (Q := Q) (ν := μ) N).Good := ⟨inferInstance, inferInstance, hnilN⟩
  obtain ⟨μ', hd, hT⟩ := KLRMod.exists_isTop (i := i) hNb
  obtain ⟨h1, h2⟩ := hNb.crystalF hPQ hP hν'
  have h3 := KLRMod.IsTop.crystalF hPQ hP hν' hNb hT
  obtain ⟨g1, g2, g3⟩ := KLRMod.fIter_spec hPQ hP μ (Multiset.card ν') _ hNb
  refine KLRMod.nonempty_equiv_of_isTop hPQ hP h1 (g1.cast _) ?_ h3 ((g3 _ hT).cast _)
  rw [KLRMod.epsI_cast, g2]
  exact h2

end Main

end KLRAlgebra

end Categorification.KLR

end

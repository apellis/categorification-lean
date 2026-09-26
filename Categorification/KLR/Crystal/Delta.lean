/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Crystal.IndDecomp
import Categorification.KLR.SimpleNilHecke

/-!
# The functors `Δ_{i^n}` and the function `ε_i`

Khovanov–Lauda I (arXiv:0803.4121v2), §3.2 "Surjectivity of `γ`" (TeX lines 2080–2102). For an
`R(ν)`-module `M`, `ν = μ + n i`,

  `Δ_{i^n} M = (1_{ν - ni} ⊗ 1_{ni}) M = 1_{μ, ni} M`,

viewed as an `R(μ) ⊗ R(ni)`-module; `ε_i(M)` is the largest `n` with `Δ_{i^n} M ≠ 0`, i.e. "the
length of the longest tail of `i`'s in sequences `k` with `1_k M ≠ 0`".

We work ungraded. The weight `ni` is any multiset `ν'` all of whose labels are `i`
(`hν' : ∀ a ∈ ν', a = i`, e.g. `ν' = Multiset.replicate n i`), and `ν = μ + ν'`.

## Main definitions and results

* `Seq.HasTail i s t`, `Seq.tailLen i s` : `s` ends with `t` letters `i`; the length of the
  longest such tail. `Seq.constSeq hν'` : the sequence `i^n`.
* `KLRAlgebra.seqSupp Q ν M`, `KLRAlgebra.epsI Q ν i M` : the sequences `s` with `1_s M ≠ 0`, and
  **`ε_i(M) = max {tail length of s | 1_s M ≠ 0}`** (the paper's second description; it is `0`
  for `M = 0`). `epsI_le_of_injective`, `epsI_le_of_surjective` : `ε_i` does not increase on
  submodules and quotients.
* `KLRAlgebra.ResSub Q μ ν' M` : **`Δ_{i^n} M = 1_{μ,ν'} M`**, an `R(μ) ⊗ R(ν')`-module (for any
  `ν'`, this is the restriction `Res_{μ,ν'}`); `resSubMap` (functoriality), with
  `resSubMap_injective`, `resSubMap_surjective`, `resSubMap_exact` (**exactness**).
* `KLRAlgebra.nontrivial_resSub_iff` : **`Δ_{i^n} M ≠ 0 ⟺ n ≤ ε_i(M)`** (for `M ≠ 0`), so that
  `ε_i(M) = max {n | Δ_{i^n} M ≠ 0}` as in the paper's definition.
* `KLRAlgebra.fixSubResSubEquiv` (**KL I, Lemma 3.5**, ungraded): for `j ∈ Seq(μ)`,
  `1_j Δ_{i^n} M = 1_{j i^n} M`; so `ch(Δ_{i^n} M) = ∑_j ch(M, j i^n) j`
  (`finrank_fixSub_resSub`).
* `KLRAlgebra.indResEquiv` (**the adjunction (3.x)**, `eq_funs` in the paper, ungraded):
  `Hom_{R(ν)}(Ind_{μ,ν'} N, M) ≃ Hom_{R(μ) ⊗ R(ν')}(N, Δ M)`, with `indAdjBwd_surjective` : a
  nonzero map `N → Δ M` into a simple `M` gives a surjection `Ind N ↠ M`.
-/

noncomputable section

namespace Categorification.KLR

open Equiv MvPolynomial TypeA MulOpposite
open scoped TensorProduct

variable {I : Type*} [DecidableEq I]

/-! ### Tails of sequences -/

namespace Seq

variable {ν μ ν' : Multiset I} {i : I}

/-- `s` ends with (at least) `t` letters `i`. -/
def HasTail (i : I) (s : Seq ν) (t : ℕ) : Prop :=
  t ≤ Multiset.card ν ∧ ∀ a : Fin (Multiset.card ν), Multiset.card ν ≤ a.val + t → s.1 a = i

instance (i : I) (s : Seq ν) (t : ℕ) : Decidable (HasTail i s t) := by
  unfold HasTail; infer_instance

/-- The length of the longest tail of letters `i` of `s`. -/
def tailLen (i : I) (s : Seq ν) : ℕ := Nat.findGreatest (HasTail i s) (Multiset.card ν)

omit [DecidableEq I] in
theorem hasTail_zero (s : Seq ν) : HasTail i s 0 :=
  ⟨Nat.zero_le _, fun a ha => absurd a.2 (by omega)⟩

omit [DecidableEq I] in
theorem HasTail.mono {s : Seq ν} {t t' : ℕ} (h : HasTail i s t) (ht : t' ≤ t) :
    HasTail i s t' :=
  ⟨ht.trans h.1, fun a ha => h.2 a (by omega)⟩

theorem hasTail_tailLen (s : Seq ν) : HasTail i s (tailLen i s) :=
  Nat.findGreatest_spec (P := HasTail i s) (Nat.zero_le _) (hasTail_zero s)

theorem le_tailLen {s : Seq ν} {t : ℕ} (h : HasTail i s t) : t ≤ tailLen i s :=
  Nat.le_findGreatest h.1 h

theorem hasTail_iff {s : Seq ν} {t : ℕ} : HasTail i s t ↔ t ≤ tailLen i s :=
  ⟨le_tailLen, fun h => (hasTail_tailLen s).mono h⟩

theorem tailLen_le_card (s : Seq ν) : tailLen i s ≤ Multiset.card ν := Nat.findGreatest_le _

theorem apply_eq_of_le_tailLen {s : Seq ν} {a : Fin (Multiset.card ν)}
    (h : Multiset.card ν ≤ a.val + tailLen i s) : s.1 a = i :=
  (hasTail_tailLen s).2 a h

theorem add_tailLen_lt {s : Seq ν} {a : Fin (Multiset.card ν)} (h : s.1 a ≠ i) :
    a.val + tailLen i s < Multiset.card ν := by
  by_contra hc
  exact h (apply_eq_of_le_tailLen (by omega))

/-- The sequence `i^n ∈ Seq(ν')` of a weight all of whose labels are `i`. -/
def constSeq (hν' : ∀ a ∈ ν', a = i) : Seq ν' := (uniqueOfForall hν').default

omit [DecidableEq I] in
@[simp] theorem constSeq_apply (hν' : ∀ a ∈ ν', a = i) (b : Fin (Multiset.card ν')) :
    (constSeq hν').1 b = i := rfl

omit [DecidableEq I] in
theorem eq_constSeq (hν' : ∀ a ∈ ν', a = i) (t : Seq ν') : t = constSeq hν' :=
  (uniqueOfForall hν').uniq t

/-- `j i^n` has a tail of length `tail(j) + n`. -/
theorem hasTail_append_const (hν' : ∀ a ∈ ν', a = i) (j : Seq μ) :
    HasTail i (j.append (constSeq hν')) (tailLen i j + Multiset.card ν') := by
  refine ⟨?_, fun a ha => ?_⟩
  · have := tailLen_le_card (i := i) j
    have := Multiset.card_add μ ν'
    omega
  · by_cases h : a.val < Multiset.card μ
    · rw [append_apply_lt _ _ a h]
      refine apply_eq_of_le_tailLen ?_
      have := Multiset.card_add μ ν'
      show Multiset.card μ ≤ a.val + tailLen i j
      omega
    · rw [append_apply_ge _ _ a (by omega)]; rfl

theorem le_tailLen_append_const (hν' : ∀ a ∈ ν', a = i) (j : Seq μ) :
    tailLen i j + Multiset.card ν' ≤ tailLen i (j.append (constSeq hν')) :=
  le_tailLen (hasTail_append_const hν' j)

omit [DecidableEq I] in
/-- Sequences of weight `μ + ν'` ending with `card ν'` letters `i` are concatenations `j i^n`. -/
theorem exists_eq_append_const_of_hasTail (hν' : ∀ a ∈ ν', a = i) {s : Seq (μ + ν')}
    (hs : HasTail i s (Multiset.card ν')) : ∃ j : Seq μ, j.append (constSeq hν') = s := by
  have hR : ∀ b : Fin (Multiset.card ν'), s.1 (posR μ b) = i := fun b =>
    hs.2 _ (by simp only [posR_val, Multiset.card_add]; omega)
  have key : ∀ f : Fin (Multiset.card (μ + ν')) → I, Finset.univ.val.map f =
      Finset.univ.val.map (f ∘ posL ν') + Finset.univ.val.map (f ∘ posR μ) := by
    intro f
    conv_lhs => rw [← Multiset.map_univ_val_equiv (blockEquiv (card_add' μ ν'))]
    rw [Multiset.map_map, ← Finset.univ_disjSum_univ, Finset.val_disjSum, Multiset.disjSum,
      Multiset.map_add, Multiset.map_map, Multiset.map_map]
    rfl
  have hmap := key s.1
  have hR' : Finset.univ.val.map (s.1 ∘ posR μ) = ν' := by
    conv_rhs => rw [Multiset.eq_replicate_card.2 hν']
    rw [show s.1 ∘ posR μ = fun _ => i from funext hR, Multiset.map_const', Finset.card_val,
      Finset.card_univ, Fintype.card_fin]
  rw [s.2, hR'] at hmap
  refine ⟨⟨s.1 ∘ posL ν', (add_right_cancel hmap).symm⟩, ?_⟩
  apply Subtype.ext; funext a
  obtain ⟨c, rfl⟩ := (blockEquiv (card_add' μ ν')).surjective a
  cases c with
  | inl x => exact append_posL _ _ x
  | inr y => exact (append_posR _ _ y).trans (hR y).symm

omit [DecidableEq I] in
theorem hasTail_append_of_forall (hν' : ∀ a ∈ ν', a = i) (j : Seq μ) (c : Seq ν') :
    HasTail i (j.append c) (Multiset.card ν') := by
  have hc := Multiset.card_add μ ν'
  refine ⟨by omega, fun a ha => ?_⟩
  have : Multiset.card μ ≤ a.val := by omega
  rw [append_apply_ge _ _ a this]
  exact hν' _ (c.mem _)

end Seq

namespace KLRAlgebra

variable {k : Type*} [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}

/-! ### Support and `ε_i` -/

section Eps

variable {ν : Multiset I} {i : I}
  {M : Type*} [AddCommGroup M] [Module k M] [Module (KLRAlgebra k Q ν) M]
  [IsScalarTower k (KLRAlgebra k Q ν) M]
  {M' : Type*} [AddCommGroup M'] [Module k M'] [Module (KLRAlgebra k Q ν) M']
  [IsScalarTower k (KLRAlgebra k Q ν) M']

variable (Q ν M) in
/-- The support `{s | 1_s M ≠ 0}` of an `R(ν)`-module. -/
def seqSupp : Finset (Seq ν) := by
  classical exact Finset.univ.filter fun s => fixSub k M (e s : KLRAlgebra k Q ν) ≠ ⊥

theorem mem_seqSupp {s : Seq ν} :
    s ∈ seqSupp Q ν M ↔ fixSub k M (e s : KLRAlgebra k Q ν) ≠ ⊥ := by
  classical
  simp [seqSupp]

variable (Q ν i M) in
/-- **`ε_i(M)`**: the length of the longest tail of `i`'s in the sequences `s` with
`1_s M ≠ 0` (KL I §3.2). -/
def epsI : ℕ := (seqSupp Q ν M).sup (Seq.tailLen i)

theorem tailLen_le_epsI {s : Seq ν} (hs : fixSub k M (e s : KLRAlgebra k Q ν) ≠ ⊥) :
    Seq.tailLen i s ≤ epsI Q ν i M :=
  Finset.le_sup (f := Seq.tailLen i) (mem_seqSupp.2 hs)

theorem epsI_le_iff {t : ℕ} :
    epsI Q ν i M ≤ t ↔ ∀ s, fixSub k M (e s : KLRAlgebra k Q ν) ≠ ⊥ → Seq.tailLen i s ≤ t := by
  rw [epsI, Finset.sup_le_iff]
  exact forall_congr' fun s => by rw [mem_seqSupp]

omit [Module k M] [IsScalarTower k (KLRAlgebra k Q ν) M] in
/-- Every nonzero vector has a nonzero component `1_s v`. -/
theorem exists_e_smul_ne_zero {v : M} (hv : v ≠ 0) :
    ∃ s : Seq ν, (e s : KLRAlgebra k Q ν) • v ≠ 0 := by
  by_contra h
  push_neg at h
  apply hv
  rw [← one_smul (KLRAlgebra k Q ν) v, ← sum_e, Finset.sum_smul]
  exact Finset.sum_eq_zero fun s _ => h s

theorem fixSub_ne_bot_of_smul_ne_zero {s : Seq ν} {v : M}
    (hv : (e s : KLRAlgebra k Q ν) • v ≠ 0) : fixSub k M (e s : KLRAlgebra k Q ν) ≠ ⊥ := by
  rw [Submodule.ne_bot_iff]
  exact ⟨_, smul_mem_fixSub (e_mul_self s) v, hv⟩

theorem seqSupp_nonempty [Nontrivial M] : (seqSupp Q ν M).Nonempty := by
  obtain ⟨v, hv⟩ := exists_ne (0 : M)
  obtain ⟨s, hs⟩ := exists_e_smul_ne_zero (Q := Q) (ν := ν) hv
  exact ⟨s, mem_seqSupp.2 (fixSub_ne_bot_of_smul_ne_zero hs)⟩

/-- For `M ≠ 0` the maximum defining `ε_i(M)` is attained. -/
theorem exists_tailLen_eq_epsI [Nontrivial M] :
    ∃ s : Seq ν, fixSub k M (e s : KLRAlgebra k Q ν) ≠ ⊥ ∧ Seq.tailLen i s = epsI Q ν i M := by
  obtain ⟨s, hs, heq⟩ := Finset.exists_mem_eq_sup _ (seqSupp_nonempty (Q := Q) (ν := ν) (M := M))
    (Seq.tailLen i)
  exact ⟨s, mem_seqSupp.1 hs, heq.symm⟩

theorem fixSub_ne_bot_of_injective {f : M →ₗ[KLRAlgebra k Q ν] M'} (hf : Function.Injective f)
    {s : Seq ν} (hs : fixSub k M (e s : KLRAlgebra k Q ν) ≠ ⊥) :
    fixSub k M' (e s : KLRAlgebra k Q ν) ≠ ⊥ := by
  rw [Submodule.ne_bot_iff] at hs ⊢
  obtain ⟨v, hv, hv0⟩ := hs
  refine ⟨f v, ?_, fun h => hv0 (hf (h.trans (map_zero f).symm))⟩
  rw [mem_fixSub, ← map_smul, mem_fixSub.1 hv]

theorem fixSub_ne_bot_of_surjective {f : M →ₗ[KLRAlgebra k Q ν] M'} (hf : Function.Surjective f)
    {s : Seq ν} (hs : fixSub k M' (e s : KLRAlgebra k Q ν) ≠ ⊥) :
    fixSub k M (e s : KLRAlgebra k Q ν) ≠ ⊥ := by
  rw [Submodule.ne_bot_iff] at hs
  obtain ⟨v', hv', hv0⟩ := hs
  obtain ⟨v, rfl⟩ := hf v'
  refine fixSub_ne_bot_of_smul_ne_zero (v := v) fun h => hv0 ?_
  rw [← mem_fixSub.1 hv', ← map_smul, h, map_zero]

/-- `ε_i` does not increase on submodules. -/
theorem epsI_le_of_injective {f : M →ₗ[KLRAlgebra k Q ν] M'} (hf : Function.Injective f) :
    epsI Q ν i M ≤ epsI Q ν i M' :=
  epsI_le_iff.2 fun _ hs => tailLen_le_epsI (fixSub_ne_bot_of_injective hf hs)

/-- `ε_i` does not increase on quotients. -/
theorem epsI_le_of_surjective {f : M →ₗ[KLRAlgebra k Q ν] M'} (hf : Function.Surjective f) :
    epsI Q ν i M' ≤ epsI Q ν i M :=
  epsI_le_iff.2 fun _ hs => tailLen_le_epsI (fixSub_ne_bot_of_surjective hf hs)

theorem epsI_congr (f : M ≃ₗ[KLRAlgebra k Q ν] M') : epsI Q ν i M = epsI Q ν i M' :=
  le_antisymm (epsI_le_of_injective f.injective) (epsI_le_of_surjective f.surjective)

end Eps

/-! ### `Δ_{i^n} M = 1_{μ,ν'} M` -/

section ResSub

variable {μ ν' : Multiset I}
  (M : Type*) [AddCommGroup M] [Module k M] [Module (KLRAlgebra k Q (μ + ν')) M]
  [IsScalarTower k (KLRAlgebra k Q (μ + ν')) M]
  {M' : Type*} [AddCommGroup M'] [Module k M'] [Module (KLRAlgebra k Q (μ + ν')) M']
  [IsScalarTower k (KLRAlgebra k Q (μ + ν')) M']
  {M'' : Type*} [AddCommGroup M''] [Module k M''] [Module (KLRAlgebra k Q (μ + ν')) M'']
  [IsScalarTower k (KLRAlgebra k Q (μ + ν')) M'']

variable (Q μ ν') in
/-- **`Δ M = 1_{μ,ν'} M`** as a `k`-subspace of `M`; it is an `R(μ) ⊗ R(ν')`-module through
`ι_{μ,ν'}` (for `ν' = n i` this is the paper's `Δ_{i^n} M`). -/
abbrev ResSub : Type _ := fixSub k M (oneConcat Q μ ν')

variable {M}

theorem concat_smul_mem_resSub (t : TensorKLR Q μ ν') (v : M) :
    concat Q μ ν' t • v ∈ fixSub k M (oneConcat Q μ ν') := by
  rw [mem_fixSub, smul_smul, oneConcat_mul_concat]

instance : SMul (TensorKLR Q μ ν') (ResSub Q μ ν' M) :=
  ⟨fun t v => ⟨concat Q μ ν' t • (v : M), concat_smul_mem_resSub t (v : M)⟩⟩

theorem coe_resSub_smul (t : TensorKLR Q μ ν') (v : ResSub Q μ ν' M) :
    ((t • v : ResSub Q μ ν' M) : M) = concat Q μ ν' t • (v : M) := rfl

instance : Module (TensorKLR Q μ ν') (ResSub Q μ ν' M) where
  one_smul v := Subtype.ext (by rw [coe_resSub_smul, concat_one]; exact v.2)
  mul_smul s t v := Subtype.ext (by simp only [coe_resSub_smul, concat_mul, mul_smul])
  smul_zero t := Subtype.ext (by simp only [coe_resSub_smul, ZeroMemClass.coe_zero, smul_zero])
  smul_add t v w := Subtype.ext (by simp only [coe_resSub_smul, Submodule.coe_add, smul_add])
  add_smul s t v := Subtype.ext (by
    simp only [coe_resSub_smul, map_add, add_smul, Submodule.coe_add])
  zero_smul v := Subtype.ext (by
    simp only [coe_resSub_smul, map_zero, zero_smul, ZeroMemClass.coe_zero])

instance : IsScalarTower k (TensorKLR Q μ ν') (ResSub Q μ ν' M) where
  smul_assoc c t v := Subtype.ext (by
    rw [coe_resSub_smul, Submodule.coe_smul, coe_resSub_smul, map_smul, smul_assoc])

/-- `Δ` on morphisms. -/
def resSubMap (f : M →ₗ[KLRAlgebra k Q (μ + ν')] M') :
    ResSub Q μ ν' M →ₗ[TensorKLR Q μ ν'] ResSub Q μ ν' M' where
  toFun v := ⟨f v, by rw [mem_fixSub, ← map_smul, mem_fixSub.1 v.2]⟩
  map_add' v w := Subtype.ext (map_add f _ _)
  map_smul' t v := Subtype.ext (by
    show f (concat Q μ ν' t • (v : M)) = concat Q μ ν' t • f v
    rw [map_smul])

@[simp] theorem coe_resSubMap (f : M →ₗ[KLRAlgebra k Q (μ + ν')] M') (v : ResSub Q μ ν' M) :
    ((resSubMap f v : ResSub Q μ ν' M') : M') = f v := rfl

theorem resSubMap_injective {f : M →ₗ[KLRAlgebra k Q (μ + ν')] M'}
    (hf : Function.Injective f) : Function.Injective (resSubMap (μ := μ) (ν' := ν') f) :=
  fun _ _ h => Subtype.ext (hf (congrArg Subtype.val h))

theorem resSubMap_surjective {f : M →ₗ[KLRAlgebra k Q (μ + ν')] M'}
    (hf : Function.Surjective f) : Function.Surjective (resSubMap (μ := μ) (ν' := ν') f) := by
  intro w
  obtain ⟨v, hv⟩ := hf w
  refine ⟨⟨oneConcat Q μ ν' • v, smul_mem_fixSub oneConcat_idem v⟩, Subtype.ext ?_⟩
  rw [coe_resSubMap, map_smul, hv]
  exact w.2

/-- **Exactness of `Δ`**. -/
theorem resSubMap_exact {f : M →ₗ[KLRAlgebra k Q (μ + ν')] M'}
    {g : M' →ₗ[KLRAlgebra k Q (μ + ν')] M''} (hfg : Function.Exact f g) :
    Function.Exact (resSubMap (μ := μ) (ν' := ν') f) (resSubMap g) := by
  intro w
  constructor
  · intro hw
    obtain ⟨v, hv⟩ := (hfg w).1 (congrArg Subtype.val hw)
    refine ⟨⟨oneConcat Q μ ν' • v, smul_mem_fixSub oneConcat_idem v⟩, Subtype.ext ?_⟩
    rw [coe_resSubMap, map_smul, hv]
    exact w.2
  · rintro ⟨v, rfl⟩
    exact Subtype.ext ((hfg _).2 ⟨v, rfl⟩)

theorem oneConcat_mul_e {s : Seq (μ + ν')} (hs : s ∈ concatSet μ ν') :
    (oneConcat Q μ ν' * e s : KLRAlgebra k Q (μ + ν')) = e s := by
  rw [oneConcat, eSum_mul_e, if_pos hs]

theorem e_mul_oneConcat {s : Seq (μ + ν')} (hs : s ∈ concatSet μ ν') :
    (e s * oneConcat Q μ ν' : KLRAlgebra k Q (μ + ν')) = e s := by
  rw [oneConcat, e_mul_eSum, if_pos hs]

/-- `Δ M ≠ 0` iff `1_s M ≠ 0` for some concatenation `s ∈ Seq(μ) Seq(ν')`. -/
theorem nontrivial_resSub_iff_exists :
    Nontrivial (ResSub Q μ ν' M) ↔
      ∃ s ∈ concatSet μ ν', fixSub k M (e s : KLRAlgebra k Q (μ + ν')) ≠ ⊥ := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := exists_ne (0 : ResSub Q μ ν' M)
    have hv' : (v : M) ≠ 0 := fun h0 => hv (Subtype.ext h0)
    have hsum : (v : M) = ∑ s ∈ concatSet μ ν', (e s : KLRAlgebra k Q (μ + ν')) • (v : M) := by
      calc (v : M) = oneConcat Q μ ν' • (v : M) := (mem_fixSub.1 v.2).symm
        _ = eSum Q (concatSet μ ν') • (v : M) := rfl
        _ = _ := by rw [eSum, Finset.sum_smul]
    by_contra hcon
    push_neg at hcon
    apply hv'
    rw [hsum]
    refine Finset.sum_eq_zero fun s hs => ?_
    have := hcon s hs
    by_contra hne
    exact fixSub_ne_bot_of_smul_ne_zero hne this
  · rintro ⟨s, hs, hne⟩
    rw [Submodule.ne_bot_iff] at hne
    obtain ⟨w, hw, hw0⟩ := hne
    refine ⟨⟨⟨w, ?_⟩, 0, fun h => hw0 (congrArg Subtype.val h)⟩⟩
    rw [mem_fixSub, ← mem_fixSub.1 hw, smul_smul, oneConcat_mul_e hs]

section Const

variable {i : I} (hν' : ∀ a ∈ ν', a = i)

include hν' in
theorem mem_concatSet_iff_hasTail {s : Seq (μ + ν')} :
    s ∈ concatSet μ ν' ↔ Seq.HasTail i s (Multiset.card ν') := by
  constructor
  · intro hs
    obtain ⟨j, c, rfl⟩ := mem_concatSet.1 hs
    exact Seq.hasTail_append_of_forall hν' j c
  · intro hs
    obtain ⟨j, hj⟩ := Seq.exists_eq_append_const_of_hasTail hν' hs
    exact mem_concatSet.2 ⟨j, _, hj⟩

include hν' in
/-- **`Δ_{i^n} M ≠ 0 ⟺ n ≤ ε_i(M)`** (for `M ≠ 0`): `ε_i(M) = max {n | Δ_{i^n} M ≠ 0}`. -/
theorem nontrivial_resSub_iff [Nontrivial M] :
    Nontrivial (ResSub Q μ ν' M) ↔ Multiset.card ν' ≤ epsI Q (μ + ν') i M := by
  rw [nontrivial_resSub_iff_exists]
  constructor
  · rintro ⟨s, hs, hne⟩
    exact (Seq.le_tailLen ((mem_concatSet_iff_hasTail hν').1 hs)).trans (tailLen_le_epsI hne)
  · intro h
    obtain ⟨s, hne, hs⟩ := exists_tailLen_eq_epsI (Q := Q) (ν := μ + ν') (i := i) (M := M)
    exact ⟨s, (mem_concatSet_iff_hasTail hν').2 (Seq.hasTail_iff.2 (hs ▸ h)), hne⟩

include hν' in
theorem concat_e_tmul_one_const (j : Seq μ) :
    concat Q μ ν' (e j ⊗ₜ 1) = e (j.append (Seq.constSeq hν')) := by
  letI := Seq.uniqueOfForall hν'
  rw [concat_e_tmul_one, Fintype.sum_unique]
  rfl

/-- **KL I, Lemma 3.5**: `1_j Δ_{i^n} M = 1_{j i^n} M` for `j ∈ Seq(μ)` (as subspaces of `M`). -/
def fixSubResSubEquiv (j : Seq μ) :
    fixSub k (ResSub Q μ ν' M) (e j ⊗ₜ[k] 1 : TensorKLR Q μ ν') ≃ₗ[k]
      fixSub k M (e (j.append (Seq.constSeq hν')) : KLRAlgebra k Q (μ + ν')) where
  toFun v := ⟨((v : ResSub Q μ ν' M) : M), by
    have h := congrArg Subtype.val (mem_fixSub.1 v.2)
    rw [coe_resSub_smul, concat_e_tmul_one_const hν'] at h
    exact h⟩
  invFun w := ⟨⟨w, by
      rw [mem_fixSub, ← mem_fixSub.1 w.2, smul_smul,
        oneConcat_mul_e (append_mem_concatSet _ _)]⟩, by
    apply Subtype.ext
    rw [coe_resSub_smul, concat_e_tmul_one_const hν']
    exact w.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- **KL I, Lemma 3.5** (dimensions): `ch(Δ_{i^n} M, j) = ch(M, j i^n)`. -/
theorem finrank_fixSub_resSub (j : Seq μ) :
    Module.finrank k (fixSub k (ResSub Q μ ν' M) (e j ⊗ₜ[k] 1 : TensorKLR Q μ ν')) =
      Module.finrank k (fixSub k M (e (j.append (Seq.constSeq hν')) :
        KLRAlgebra k Q (μ + ν'))) :=
  (fixSubResSubEquiv hν' j).finrank_eq

end Const

end ResSub

/-! ### The adjunction `Hom(Ind N, M) ≅ Hom(N, Δ M)` -/

section Adjunction

variable {μ ν' : Multiset I}
  {N : Type*} [AddCommGroup N] [Module k N] [Module (TensorKLR Q μ ν') N]
  [IsScalarTower k (TensorKLR Q μ ν') N]
  {M : Type*} [AddCommGroup M] [Module k M] [Module (KLRAlgebra k Q (μ + ν')) M]
  [IsScalarTower k (KLRAlgebra k Q (μ + ν')) M]

omit [IsScalarTower k (TensorKLR Q μ ν') N] in
theorem smul_tmul_oneConcat (r : IndBimod Q μ ν') (n : N) :
    (r : KLRAlgebra k Q (μ + ν')) • (BalancedTensor.tmul oneConcatSubBimod n : Ind Q μ ν' N) =
      BalancedTensor.tmul r n := by
  rw [BalancedTensor.smul_tmul']
  congr 1
  exact Subtype.ext (Graded.mem_leftIdeal.1 r.2)

omit [IsScalarTower k (TensorKLR Q μ ν') N] in
theorem concat_smul_tmul_oneConcat (t : TensorKLR Q μ ν') (n : N) :
    (concat Q μ ν' t) • (BalancedTensor.tmul oneConcatSubBimod n : Ind Q μ ν' N) =
      BalancedTensor.tmul oneConcatSubBimod (t • n) := by
  rw [BalancedTensor.smul_tmul', ← BalancedTensor.op_smul_tmul]
  congr 1
  apply Subtype.ext
  rw [coe_op_smul, unop_op, Submodule.coe_smul, smul_eq_mul]
  show concat Q μ ν' t * oneConcat Q μ ν' = oneConcat Q μ ν' * concat Q μ ν' t
  rw [concat_mul_oneConcat, oneConcat_mul_concat]

omit [IsScalarTower k (TensorKLR Q μ ν') N] in
/-- `Ind N` is generated by `1_{μ,ν'} ⊗ N`: a submodule containing it is everything. -/
theorem eq_top_of_tmul_oneConcat_mem {P : Submodule (KLRAlgebra k Q (μ + ν')) (Ind Q μ ν' N)}
    (hP : ∀ n : N, BalancedTensor.tmul oneConcatSubBimod n ∈ P) : P = ⊤ := by
  rw [eq_top_iff]
  rintro y -
  induction y using BalancedTensor.induction_on with
  | zero => exact zero_mem _
  | tmul r n => rw [← smul_tmul_oneConcat]; exact P.smul_mem _ (hP n)
  | add y y' hy hy' => exact add_mem hy hy'

/-- The adjunction map `f ↦ (n ↦ f(1_{μ,ν'} ⊗ n))`. -/
def indAdjFwd (f : Ind Q μ ν' N →ₗ[KLRAlgebra k Q (μ + ν')] M) :
    N →ₗ[TensorKLR Q μ ν'] ResSub Q μ ν' M where
  toFun n := ⟨f (BalancedTensor.tmul oneConcatSubBimod n), by
    rw [mem_fixSub, ← map_smul, BalancedTensor.smul_tmul']
    congr 2
    exact Subtype.ext (oneConcat_idem (Q := Q) (ν := μ) (ν' := ν')).eq⟩
  map_add' n n' := Subtype.ext (by
    simp only [BalancedTensor.tmul_add, map_add, Submodule.coe_add])
  map_smul' t n := Subtype.ext (by
    show f (BalancedTensor.tmul oneConcatSubBimod (t • n)) =
      concat Q μ ν' t • f (BalancedTensor.tmul oneConcatSubBimod n)
    rw [← concat_smul_tmul_oneConcat, map_smul])

omit [IsScalarTower k (TensorKLR Q μ ν') N] in
theorem coe_indAdjFwd_apply (f : Ind Q μ ν' N →ₗ[KLRAlgebra k Q (μ + ν')] M) (n : N) :
    ((indAdjFwd f n : ResSub Q μ ν' M) : M) = f (BalancedTensor.tmul oneConcatSubBimod n) := rfl

/-- The bilinear map `(r, n) ↦ r g(n)`. -/
def indAdjBil (g : N →ₗ[TensorKLR Q μ ν'] ResSub Q μ ν' M) :
    IndBimod Q μ ν' →ₗ[k] N →ₗ[k] M :=
  LinearMap.mk₂ k (fun r n => (r : KLRAlgebra k Q (μ + ν')) • ((g n : ResSub Q μ ν' M) : M))
    (fun r r' n => by simp only [Submodule.coe_add, add_smul])
    (fun c r n => by
      show ((c • r : IndBimod Q μ ν') : KLRAlgebra k Q (μ + ν')) • _ = c • _
      rw [Submodule.coe_smul_of_tower, smul_assoc])
    (fun r n n' => by simp only [map_add, Submodule.coe_add, smul_add])
    (fun c r n => by
      show (r : KLRAlgebra k Q (μ + ν')) • ((g (c • n) : ResSub Q μ ν' M) : M) =
        c • ((r : KLRAlgebra k Q (μ + ν')) • ((g n : ResSub Q μ ν' M) : M))
      rw [LinearMap.map_smul_of_tower, Submodule.coe_smul, smul_comm])

theorem indAdjBil_apply (g : N →ₗ[TensorKLR Q μ ν'] ResSub Q μ ν' M) (r : IndBimod Q μ ν')
    (n : N) :
    indAdjBil g r n = (r : KLRAlgebra k Q (μ + ν')) • ((g n : ResSub Q μ ν' M) : M) := rfl

/-- The inverse adjunction map `g ↦ (r ⊗ n ↦ r g(n))`. -/
def indAdjBwd (g : N →ₗ[TensorKLR Q μ ν'] ResSub Q μ ν' M) :
    Ind Q μ ν' N →ₗ[KLRAlgebra k Q (μ + ν')] M :=
  BalancedTensor.liftB (indAdjBil g)
    (fun r t n => by
      rw [indAdjBil_apply, indAdjBil_apply, coe_op_smul, map_smul, coe_resSub_smul, mul_smul,
        unop_op])
    (fun b r n => by
      rw [indAdjBil_apply, indAdjBil_apply, Submodule.coe_smul, smul_eq_mul, mul_smul])

@[simp] theorem indAdjBwd_tmul (g : N →ₗ[TensorKLR Q μ ν'] ResSub Q μ ν' M)
    (r : IndBimod Q μ ν') (n : N) :
    indAdjBwd g (BalancedTensor.tmul r n) =
      (r : KLRAlgebra k Q (μ + ν')) • ((g n : ResSub Q μ ν' M) : M) := rfl

theorem indAdjBwd_tmul_oneConcat (g : N →ₗ[TensorKLR Q μ ν'] ResSub Q μ ν' M) (n : N) :
    indAdjBwd g (BalancedTensor.tmul oneConcatSubBimod n) = ((g n : ResSub Q μ ν' M) : M) := by
  rw [indAdjBwd_tmul]
  exact (g n).2

theorem indAdjBwd_indAdjFwd (f : Ind Q μ ν' N →ₗ[KLRAlgebra k Q (μ + ν')] M) :
    indAdjBwd (indAdjFwd f) = f :=
  BalancedTensor.extB fun r n => by
    rw [indAdjBwd_tmul, coe_indAdjFwd_apply, ← map_smul, smul_tmul_oneConcat]

theorem indAdjFwd_indAdjBwd (g : N →ₗ[TensorKLR Q μ ν'] ResSub Q μ ν' M) :
    indAdjFwd (indAdjBwd g) = g :=
  LinearMap.ext fun n => Subtype.ext (by
    rw [coe_indAdjFwd_apply, indAdjBwd_tmul_oneConcat])

variable (N M) in
/-- **The adjunction (3.x) of KL I §3.2** (`eq_funs`, ungraded):
`Hom_{R(ν)}(Ind_{μ,ν'} N, M) ≅ Hom_{R(μ) ⊗ R(ν')}(N, Δ M)`, `f ↦ (n ↦ f(1 ⊗ n))`. -/
def indResEquiv :
    (Ind Q μ ν' N →ₗ[KLRAlgebra k Q (μ + ν')] M) ≃ (N →ₗ[TensorKLR Q μ ν'] ResSub Q μ ν' M) where
  toFun := indAdjFwd
  invFun := indAdjBwd
  left_inv := indAdjBwd_indAdjFwd
  right_inv := indAdjFwd_indAdjBwd

theorem indAdjBwd_ne_zero {g : N →ₗ[TensorKLR Q μ ν'] ResSub Q μ ν' M} (hg : g ≠ 0) :
    indAdjBwd g ≠ 0 := by
  intro h
  apply hg
  rw [← indAdjFwd_indAdjBwd g, h]
  ext n
  simp [coe_indAdjFwd_apply]

/-- A nonzero map `N → Δ M` into a simple module `M` gives a surjection `Ind N ↠ M`. -/
theorem indAdjBwd_surjective [IsSimpleModule (KLRAlgebra k Q (μ + ν')) M]
    {g : N →ₗ[TensorKLR Q μ ν'] ResSub Q μ ν' M} (hg : g ≠ 0) :
    Function.Surjective (indAdjBwd g) := by
  rw [← LinearMap.range_eq_top]
  refine (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left ?_
  rw [LinearMap.range_eq_bot]
  exact indAdjBwd_ne_zero hg

end Adjunction

end KLRAlgebra

end Categorification.KLR

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Concat
import Categorification.KLR.BasisTheorem
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# `1_{ν,ν'} R(ν + ν')` is a free `R(ν) ⊗ R(ν')`-module

Khovanov–Lauda I (arXiv:0803.4121v2), §2.6, **Proposition 2.16**: `1_{ν,ν'} R(ν + ν')` is a
free left `R(ν) ⊗ R(ν')`-module (acting through the inclusion `ι_{ν,ν'} = concat`), with
basis the elements
`ŵ = ∑_{i,j} {}_{ij}ŵ = 1_{ν,ν'} ψ_{σ(u)}`
over the minimal length representatives `u` of the cosets `(S_n × S_{n'}) u` of the Young
subgroup (`TypeA.Shuffle`), `σ(u)` a reduced word of `u`. Here `ψ_{σ(u)} 1_{u⁻¹(ij)}` is the
diagram of the minimal presentation of `u` with top ends labelled by `ij`, lying in
`{}_{ij}R(ν + ν')_{u⁻¹(ij)}`, as in the paper.

## Main results

* `KLRAlgebra.lbasis` — the basis theorem with dots at the top: for any choice of reduced
  words, `x^d ψ_{ρ w} 1_i` is a `k`-basis of `R(ν)` (from `KLRAlgebra.basis` via the
  horizontal flip).
* `KLRAlgebra.inductionBasis` (**Prop. 2.16, explicit form**): the elements
  `ι(b ⊗ b') ŵ_u`, for `b`, `b'` running over the bases `lbasis` of `R(ν)`, `R(ν')` and `u`
  over the shuffles, form a `k`-basis of `1_{ν,ν'} R(ν + ν')`. The proof identifies them
  with part of the basis `lbasis` of `R(ν + ν')` for the reduced words
  `ρ₁(a) (n + ρ₂(b)) σ(u)` of `(a × b) u` (`TypeA.IsReduced.parabolic`).
* `KLRAlgebra.freeBasis` (**Prop. 2.16**): the elements `ŵ_u` form a basis of
  `1_{ν,ν'} R(ν + ν')` as a left `R(ν) ⊗[k] R(ν')`-module; hence `Module.Free`
  (`KLRAlgebra.free_oneConcat`).
* `KLRAlgebra.concat_injective`: `ι_{ν,ν'}` is injective.

All statements are over an integral domain `k` with the hypotheses of the basis theorem.
-/

namespace Categorification.KLR

open Equiv MvPolynomial TypeA PolyRep
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] [IsDomain k]
  {Q : I → I → MvPolynomial (Fin 2) k} {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)

namespace KLRAlgebra

/-! ### The basis theorem with dots on top -/

section lbasis

variable {μ : Multiset I}

local notation "m" => Multiset.card μ

omit [IsDomain k] in
theorem hflip_ψw (ρ : List ℕ) : hflip (ψw ρ : KLRAlgebra k Q μ) = ψw ρ.reverse := by
  induction ρ with
  | nil => simp
  | cons j ρ ih =>
    rw [ψw_cons, hflip_mul, ih, hflip_ψ, List.reverse_cons, ψw_append]; simp [ψw]

variable (k Q μ) in
/-- The horizontal flip as a `k`-linear equivalence. -/
noncomputable def hflipEquiv : KLRAlgebra k Q μ ≃ₗ[k] KLRAlgebra k Q μ :=
  (flipH k Q μ).toLinearEquiv.trans (MulOpposite.opLinearEquiv k).symm

omit [IsDomain k] in
@[simp] theorem hflipEquiv_apply (a : KLRAlgebra k Q μ) : hflipEquiv k Q μ a = hflip a := rfl

/-- Reindexing `(i', w, d) ↦ (w • i', w⁻¹, d)`. -/
def flipIdx :
    Seq μ × Perm (Fin m) × (Fin m →₀ ℕ) ≃ Seq μ × Perm (Fin m) × (Fin m →₀ ℕ) where
  toFun b := (b.2.1 • b.1, b.2.1⁻¹, b.2.2)
  invFun b := (b.2.1 • b.1, b.2.1⁻¹, b.2.2)
  left_inv b := by simp
  right_inv b := by simp

variable (ρ : Perm (Fin (Multiset.card μ)) → List ℕ)
  (hρ : ∀ w, IsReduced (Multiset.card μ) (ρ w) ∧ wordProd (Multiset.card μ) (ρ w) = w)

/-- The reduced words `ρ'(w) = (ρ(w⁻¹))ʳᵉᵛ`. -/
def revWord (w : Perm (Fin m)) : List ℕ := (ρ w⁻¹).reverse

omit [DecidableEq I] in
include hρ in
theorem revWord_spec (w : Perm (Fin m)) :
    IsReduced m (revWord ρ w) ∧ wordProd m (revWord ρ w) = w := by
  obtain ⟨⟨hv, hl⟩, hw⟩ := hρ w⁻¹
  refine ⟨⟨validWord_reverse.2 hv, ?_⟩, ?_⟩
  · rw [revWord, wordProd_reverse, hw, inv_inv, List.length_reverse, hl, hw, length_inv]
  · rw [revWord, wordProd_reverse, hw, inv_inv]

/-- **KL I, Theorem 2.5, dots on top**: for any choice of reduced words `ρ w`, the elements
`x^d ψ_{ρ w} 1_i` form a basis of `R(μ)`. -/
noncomputable def lbasis :
    Basis (Seq μ × Perm (Fin m) × (Fin m →₀ ℕ)) k (KLRAlgebra k Q μ) :=
  ((basis hPQ hP (revWord ρ) (revWord_spec ρ hρ)).map (hflipEquiv k Q μ)).reindex flipIdx

theorem lbasis_apply (b : Seq μ × Perm (Fin m) × (Fin m →₀ ℕ)) :
    lbasis hPQ hP ρ hρ b = pol (monomial b.2.2 1) * ψw (ρ b.2.1) * e b.1 := by
  obtain ⟨i, v, d⟩ := b
  simp only [lbasis, Basis.reindex_apply, Basis.map_apply, basis_apply, hflipEquiv_apply,
    hflip_mul, hflip_e, hflip_pol, hflip_ψw]
  simp only [flipIdx, Equiv.coe_fn_symm_mk, revWord, List.reverse_reverse, inv_inv]
  rw [← mul_assoc, (e_commute_pol _ _).eq, mul_assoc, e_mul_ψw, ← mul_assoc, (hρ v).2,
    inv_smul_smul]

omit [IsDomain k] in
/-- A left standard element is fixed by the idempotent of its top sequence. -/
theorem e_mul_pol_ψw_e (p : MvPolynomial (Fin m) k) (ρ : List ℕ) (s : Seq μ) :
    (e (wordProd m ρ • s) * (pol p * ψw ρ * e s) : KLRAlgebra k Q μ) =
      pol p * ψw ρ * e s := by
  rw [← mul_assoc, ← mul_assoc, (e_commute_pol _ _).eq, mul_assoc (pol p), e_mul_ψw,
    inv_smul_smul, mul_assoc, mul_assoc, e_mul_self, ← mul_assoc]

end lbasis

/-! ### Proposition 2.16 -/

section Induction

variable {ν ν' : Multiset I}


variable (ν ν') in
/-- Exponent vectors of `ν + ν'` split along the two blocks. -/
noncomputable def expEquiv :
    (Fin (Multiset.card ν) →₀ ℕ) × (Fin (Multiset.card ν') →₀ ℕ) ≃
      (Fin (Multiset.card (ν + ν')) →₀ ℕ) :=
  Finsupp.sumFinsuppEquivProdFinsupp.symm.trans
    (Finsupp.domCongr (blockEquiv (Seq.card_add' ν ν'))).toEquiv

omit [DecidableEq I] in
theorem expEquiv_apply (d : Fin (Multiset.card ν) →₀ ℕ)
    (d' : Fin (Multiset.card ν') →₀ ℕ) :
    expEquiv ν ν' (d, d') = d.mapDomain (Seq.posL ν') + d'.mapDomain (Seq.posR ν) := by
  ext v
  obtain ⟨t, rfl⟩ := (blockEquiv (Seq.card_add' ν ν')).surjective v
  have hL : Function.Injective
      (Seq.posL ν' : Fin (Multiset.card ν) → Fin (Multiset.card (ν + ν'))) :=
    (blockEquiv (Seq.card_add' ν ν')).injective.comp Sum.inl_injective
  have hR : Function.Injective
      (Seq.posR ν : Fin (Multiset.card ν') → Fin (Multiset.card (ν + ν'))) :=
    (blockEquiv (Seq.card_add' ν ν')).injective.comp Sum.inr_injective
  simp only [expEquiv, Equiv.trans_apply, AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv,
    Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply,
    Finsupp.coe_add, Pi.add_apply]
  cases t with
  | inl a =>
    rw [Finsupp.sumFinsuppEquivProdFinsupp_symm_inl]
    rw [show blockEquiv (Seq.card_add' ν ν') (Sum.inl a) = Seq.posL ν' a from rfl,
      Finsupp.mapDomain_apply hL,
      Finsupp.mapDomain_notin_range]
    · simp
    · rintro ⟨b, hb⟩
      exact Sum.inl_ne_inr ((blockEquiv (Seq.card_add' ν ν')).injective hb).symm
  | inr b =>
    rw [Finsupp.sumFinsuppEquivProdFinsupp_symm_inr]
    rw [show blockEquiv (Seq.card_add' ν ν') (Sum.inr b) = Seq.posR ν b from rfl,
      Finsupp.mapDomain_apply hR,
      Finsupp.mapDomain_notin_range]
    · simp
    · rintro ⟨a, ha⟩
      exact Sum.inl_ne_inr ((blockEquiv (Seq.card_add' ν ν')).injective ha)

omit [DecidableEq I] [IsDomain k] in
theorem monomial_expEquiv (d : Fin (Multiset.card ν) →₀ ℕ)
    (d' : Fin (Multiset.card ν') →₀ ℕ) :
    (monomial (expEquiv ν ν' (d, d')) 1 : MvPolynomial (Fin (Multiset.card (ν + ν'))) k) =
      rename (Seq.posL ν') (monomial d 1) * rename (Seq.posR ν) (monomial d' 1) := by
  rw [rename_monomial, rename_monomial, monomial_mul, one_mul, expEquiv_apply]

variable (ρ₁ : Perm (Fin (Multiset.card ν)) → List ℕ)
  (ρ₂ : Perm (Fin (Multiset.card ν')) → List ℕ)
  (σ : Shuffle (Seq.card_add' ν ν') → List ℕ)

/-- The reduced word `ρ₁(a) (n + ρ₂(b)) σ(u)` attached to `w = (a × b) u`, `n = card ν`. -/
noncomputable def parWord (w : Perm (Fin (Multiset.card (ν + ν')))) : List ℕ :=
  ρ₁ ((parabolicEquiv (Seq.card_add' ν ν')).symm w).1 ++
    shiftWord (Multiset.card ν) (ρ₂ ((parabolicEquiv (Seq.card_add' ν ν')).symm w).2.1) ++
    σ ((parabolicEquiv (Seq.card_add' ν ν')).symm w).2.2

omit [DecidableEq I] in
theorem parWord_blockPerm_mul (a : Perm (Fin (Multiset.card ν)))
    (b : Perm (Fin (Multiset.card ν'))) (u : Shuffle (Seq.card_add' ν ν')) :
    parWord ρ₁ ρ₂ σ (blockPerm (Seq.card_add' ν ν') a b * u.1) =
      ρ₁ a ++ shiftWord (Multiset.card ν) (ρ₂ b) ++ σ u := by
  have : (parabolicEquiv (Seq.card_add' ν ν')).symm
      (blockPerm (Seq.card_add' ν ν') a b * u.1) = (a, b, u) :=
    (parabolicEquiv (Seq.card_add' ν ν')).symm_apply_apply (a, b, u)
  rw [parWord, this]

variable
  (hρ₁ : ∀ a, IsReduced (Multiset.card ν) (ρ₁ a) ∧ wordProd (Multiset.card ν) (ρ₁ a) = a)
  (hρ₂ : ∀ b, IsReduced (Multiset.card ν') (ρ₂ b) ∧ wordProd (Multiset.card ν') (ρ₂ b) = b)
  (hσ : ∀ u, IsReduced (Multiset.card (ν + ν')) (σ u) ∧
    wordProd (Multiset.card (ν + ν')) (σ u) = u.1)

omit [DecidableEq I] in
include hρ₁ hρ₂ hσ in
theorem parWord_spec (w : Perm (Fin (Multiset.card (ν + ν')))) :
    IsReduced (Multiset.card (ν + ν')) (parWord ρ₁ ρ₂ σ w) ∧
      wordProd (Multiset.card (ν + ν')) (parWord ρ₁ ρ₂ σ w) = w := by
  obtain ⟨⟨a, b, u⟩, rfl⟩ := (parabolicEquiv (Seq.card_add' ν ν')).surjective w
  rw [parabolicEquiv_apply, parWord_blockPerm_mul]
  have hu : IsShuffle (Seq.card_add' ν ν') (wordProd (Multiset.card (ν + ν')) (σ u)) := by
    rw [(hσ u).2]; exact u.2
  obtain ⟨h1, h2⟩ :=
    IsReduced.parabolic (Seq.card_add' ν ν') (hρ₁ a).1 (hρ₂ b).1 (hσ u).1 hu
  exact ⟨h1, by rw [h2, (hρ₁ a).2, (hρ₂ b).2, (hσ u).2]⟩

/-- Indices of the standard basis `lbasis` of `R(μ)`. -/
abbrev Idx (μ : Multiset I) : Type _ :=
  Seq μ × Perm (Fin (Multiset.card μ)) × (Fin (Multiset.card μ) →₀ ℕ)

variable (ν ν') in
/-- Indices of the basis of `1_{ν,ν'} R(ν + ν')` of Proposition 2.16. -/
abbrev IndIdx : Type _ := (Idx ν × Idx ν') × Shuffle (Seq.card_add' ν ν')

/-- The index map `((i, a, d), (j, b, d'), u) ↦ (u⁻¹(ij), (a × b) u, (d, d'))`. -/
noncomputable def indIdxMap (x : IndIdx ν ν') : Idx (ν + ν') :=
  (x.2.1⁻¹ • x.1.1.1.append x.1.2.1,
    blockPerm (Seq.card_add' ν ν') x.1.1.2.1 x.1.2.2.1 * x.2.1,
    expEquiv ν ν' (x.1.1.2.2, x.1.2.2.2))

omit [DecidableEq I] in
theorem indIdxMap_injective : Function.Injective (indIdxMap (ν := ν) (ν' := ν')) := by
  rintro ⟨⟨⟨i, a, d⟩, ⟨j, b, d'⟩⟩, u⟩ ⟨⟨⟨i', a', f⟩, ⟨j', b', f'⟩⟩, u'⟩
    h
  simp only [indIdxMap, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨rfl, rfl, hu⟩ := blockPerm_mul_injective (Seq.card_add' ν ν') u.2 u'.2 h2
  obtain rfl : u = u' := Subtype.ext hu
  obtain ⟨rfl, rfl⟩ := Seq.append_inj.1 (smul_left_cancel _ h1)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj ((expEquiv ν ν').injective h3)
  rfl

theorem exists_indIdxMap {s : Seq (ν + ν')} {w : Perm (Fin (Multiset.card (ν + ν')))}
    {f : Fin (Multiset.card (ν + ν')) →₀ ℕ}
    (hβ : w • s ∈ concatSet ν ν') : ∃ x, indIdxMap x = (s, w, f) := by
  obtain ⟨i₀, j₀, h₀⟩ := mem_concatSet.1 hβ
  obtain ⟨⟨a, b, u⟩, rfl⟩ := (parabolicEquiv (Seq.card_add' ν ν')).surjective w
  obtain ⟨⟨d, d'⟩, rfl⟩ := (expEquiv ν ν').surjective f
  refine ⟨⟨⟨⟨a⁻¹ • i₀, a, d⟩, ⟨b⁻¹ • j₀, b, d'⟩⟩, u⟩, ?_⟩
  have h₀' : i₀.append j₀ = (blockPerm (Seq.card_add' ν ν') a b * u.1) • s := h₀
  simp only [indIdxMap, Prod.mk.injEq, and_true]
  rw [← Seq.blockPerm_smul_append, h₀', ← blockPerm_inv, ← mul_smul, ← mul_smul, mul_assoc,
    inv_mul_cancel_left, inv_mul_cancel, one_smul]
  exact ⟨rfl, rfl⟩

/-- The basis element `ŵ_u = 1_{ν,ν'} ψ_{σ(u)} = ∑_{i,j} ψ_{σ(u)} 1_{u⁻¹(ij)}`. -/
noncomputable def hatW (u : Shuffle (Seq.card_add' ν ν')) : KLRAlgebra k Q (ν + ν') :=
  oneConcat Q ν ν' * ψw (σ u)

omit [IsDomain k] in
theorem hatW_eq_sum (u : Shuffle (Seq.card_add' ν ν')) :
    (hatW σ u : KLRAlgebra k Q (ν + ν')) =
      ∑ p : Seq ν × Seq ν',
        ψw (σ u) * e ((wordProd (Multiset.card (ν + ν')) (σ u))⁻¹ • p.1.append p.2) := by
  rw [hatW, oneConcat_eq, Finset.sum_mul]
  simp_rw [e_mul_ψw]

variable (Q) in
/-- The submodule `1_{ν,ν'} R(ν + ν')`. -/
noncomputable def oneConcatSub : Submodule k (KLRAlgebra k Q (ν + ν')) :=
  LinearMap.range (LinearMap.mulLeft k (oneConcat Q ν ν'))

omit [IsDomain k] in
theorem mem_oneConcatSub {r : KLRAlgebra k Q (ν + ν')} :
    r ∈ oneConcatSub Q ↔ oneConcat Q ν ν' * r = r := by
  constructor
  · rintro ⟨r', rfl⟩
    simp only [LinearMap.mulLeft_apply, ← mul_assoc, oneConcat_idem.eq]
  · intro h; exact ⟨r, h⟩

/-- The elements `ι(b ⊗ b') ŵ_u` of Proposition 2.16. -/
noncomputable def indElt (x : IndIdx ν ν') : KLRAlgebra k Q (ν + ν') :=
  concat Q ν ν' (lbasis hPQ hP ρ₁ hρ₁ x.1.1 ⊗ₜ lbasis hPQ hP ρ₂ hρ₂ x.1.2) *
    hatW σ x.2

theorem indElt_eq (x : IndIdx ν ν') :
    indElt hPQ hP ρ₁ ρ₂ σ hρ₁ hρ₂ x =
      lbasis hPQ hP (parWord ρ₁ ρ₂ σ) (parWord_spec ρ₁ ρ₂ σ hρ₁ hρ₂ hσ)
        (indIdxMap x) := by
  obtain ⟨⟨⟨i, a, d⟩, ⟨j, b, d'⟩⟩, u⟩ := x
  simp only [indElt, lbasis_apply, indIdxMap]
  rw [concat_pol_ψw_e _ _ (hρ₁ a).1.1 (hρ₂ b).1.1, parWord_blockPerm_mul, monomial_expEquiv,
    hatW, ← mul_assoc, mul_assoc _ (e _), oneConcat, e_mul_eSum,
    if_pos (append_mem_concatSet i j), mul_assoc _ (e _), e_mul_ψw, (hσ u).2, ← mul_assoc,
    mul_assoc (pol _), ← ψw_append]

omit [IsDomain k] in
theorem oneConcat_mul_pol_ψw_e (p : MvPolynomial (Fin (Multiset.card (ν + ν'))) k)
    (ρ : List ℕ) (s : Seq (ν + ν')) :
    (oneConcat Q ν ν' * (pol p * ψw ρ * e s) : KLRAlgebra k Q (ν + ν')) =
      if wordProd (Multiset.card (ν + ν')) ρ • s ∈ concatSet ν ν' then pol p * ψw ρ * e s
      else 0 := by
  rw [← e_mul_pol_ψw_e, ← mul_assoc, oneConcat, eSum_mul_e]
  split_ifs <;> simp

include hσ in
theorem linearIndependent_indElt :
    LinearIndependent k (indElt (Q := Q) hPQ hP ρ₁ ρ₂ σ hρ₁ hρ₂) := by
  have : indElt (Q := Q) hPQ hP ρ₁ ρ₂ σ hρ₁ hρ₂ =
      lbasis hPQ hP (parWord ρ₁ ρ₂ σ) (parWord_spec ρ₁ ρ₂ σ hρ₁ hρ₂ hσ) ∘
        indIdxMap :=
    funext fun x => indElt_eq hPQ hP ρ₁ ρ₂ σ hρ₁ hρ₂ hσ x
  rw [this]
  exact (Basis.linearIndependent _).comp _ indIdxMap_injective

include hσ in
theorem span_indElt :
    Submodule.span k (Set.range (indElt (Q := Q) hPQ hP ρ₁ ρ₂ σ hρ₁ hρ₂)) =
      oneConcatSub Q := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    refine mem_oneConcatSub.2 ?_
    rw [indElt, ← mul_assoc, oneConcat_mul_concat]
  · rintro r ⟨r', rfl⟩
    let B := lbasis (Q := Q) hPQ hP (parWord ρ₁ ρ₂ σ)
      (parWord_spec ρ₁ ρ₂ σ hρ₁ hρ₂ hσ)
    rw [LinearMap.mulLeft_apply, ← B.linearCombination_repr r', Finsupp.linearCombination_apply,
      Finsupp.sum, Finset.mul_sum]
    refine Submodule.sum_mem _ fun β _ => ?_
    rw [mul_smul_comm]
    refine Submodule.smul_mem _ _ ?_
    obtain ⟨s, w, f⟩ := β
    have hB : B (s, w, f) = pol (monomial f 1) * ψw (parWord ρ₁ ρ₂ σ w) * e s :=
      lbasis_apply _ _ _ _ _
    rw [hB, oneConcat_mul_pol_ψw_e, (parWord_spec ρ₁ ρ₂ σ hρ₁ hρ₂ hσ w).2]
    split_ifs with hβ
    · obtain ⟨x, hx⟩ := exists_indIdxMap (f := f) hβ
      rw [← hB, ← hx, ← indElt_eq hPQ hP ρ₁ ρ₂ σ hρ₁ hρ₂ hσ]
      exact Submodule.subset_span ⟨x, rfl⟩
    · exact zero_mem _

/-- **KL I, Proposition 2.16 (explicit form).** The elements `ι(b ⊗ b') ŵ_u`, for `b`, `b'`
in the bases `lbasis` of `R(ν)`, `R(ν')` and `u` a shuffle, form a `k`-basis of
`1_{ν,ν'} R(ν + ν')`. -/
noncomputable def inductionBasis :
    Basis (IndIdx ν ν') k (oneConcatSub (ν := ν) (ν' := ν') Q) :=
  (Basis.span (linearIndependent_indElt hPQ hP ρ₁ ρ₂ σ hρ₁ hρ₂ hσ)).map
    (LinearEquiv.ofEq _ _ (span_indElt hPQ hP ρ₁ ρ₂ σ hρ₁ hρ₂ hσ))

theorem inductionBasis_apply (x : IndIdx ν ν') :
    (inductionBasis hPQ hP ρ₁ ρ₂ σ hρ₁ hρ₂ hσ x : KLRAlgebra k Q (ν + ν')) =
      concat Q ν ν' (lbasis hPQ hP ρ₁ hρ₁ x.1.1 ⊗ₜ lbasis hPQ hP ρ₂ hρ₂ x.1.2) *
        hatW σ x.2 := by
  simp [inductionBasis, Basis.span_apply, indElt]

/-! #### The module structure and freeness -/

omit [IsDomain k] in
theorem concat_mul_mem (t : KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν')
    {r : KLRAlgebra k Q (ν + ν')} (_hr : r ∈ oneConcatSub Q) :
    concat Q ν ν' t * r ∈ oneConcatSub Q :=
  mem_oneConcatSub.2 (by rw [← mul_assoc, oneConcat_mul_concat])

/-- `R(ν) ⊗ R(ν')` acts on `1_{ν,ν'} R(ν + ν')` through `ι_{ν,ν'}`. -/
noncomputable instance : SMul (KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν')
    (oneConcatSub (ν := ν) (ν' := ν') Q) :=
  ⟨fun t r => ⟨concat Q ν ν' t * r, concat_mul_mem t r.2⟩⟩

omit [IsDomain k] in
theorem coe_tensor_smul (t : KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν')
    (r : oneConcatSub (ν := ν) (ν' := ν') Q) :
    ((t • r : oneConcatSub (ν := ν) (ν' := ν') Q) : KLRAlgebra k Q (ν + ν')) =
      concat Q ν ν' t * r := rfl

/-- `1_{ν,ν'} R(ν + ν')` as a left `R(ν) ⊗ R(ν')`-module (the restriction `Res_{ν,ν'}` of
the
regular module). -/
noncomputable instance : Module (KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν')
    (oneConcatSub (ν := ν) (ν' := ν') Q) where
  one_smul r := Subtype.ext (by rw [coe_tensor_smul, concat_one]; exact mem_oneConcatSub.1 r.2)
  mul_smul s t r := Subtype.ext (by simp only [coe_tensor_smul, concat_mul, mul_assoc])
  smul_zero t := Subtype.ext (by simp only [coe_tensor_smul, ZeroMemClass.coe_zero, mul_zero])
  smul_add t r r' := Subtype.ext (by simp only [coe_tensor_smul, Submodule.coe_add, mul_add])
  add_smul s t r := Subtype.ext (by simp only [coe_tensor_smul, map_add, Submodule.coe_add,
    add_mul])
  zero_smul r := Subtype.ext (by simp only [coe_tensor_smul, map_zero, zero_mul,
    ZeroMemClass.coe_zero])

noncomputable instance : IsScalarTower k (KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν')
    (oneConcatSub (ν := ν) (ν' := ν') Q) :=
  ⟨fun c t r => Subtype.ext (by
    rw [coe_tensor_smul, Submodule.coe_smul, coe_tensor_smul, map_smul, smul_mul_assoc])⟩

omit [IsDomain k] in
theorem hatW_mem (u : Shuffle (Seq.card_add' ν ν')) :
    (hatW σ u : KLRAlgebra k Q (ν + ν')) ∈ oneConcatSub Q :=
  mem_oneConcatSub.2 (by rw [hatW, ← mul_assoc, oneConcat_idem.eq])

/-- `ŵ_u` as an element of `1_{ν,ν'} R(ν + ν')`. -/
noncomputable def hatWSub (u : Shuffle (Seq.card_add' ν ν')) :
    oneConcatSub (ν := ν) (ν' := ν') (k := k) Q :=
  ⟨hatW σ u, hatW_mem σ u⟩

/-- The `R(ν) ⊗ R(ν')`-linear map `(t_u)_u ↦ ∑_u ι(t_u) ŵ_u`. -/
noncomputable def freeMap :
    (Shuffle (Seq.card_add' ν ν') →₀ KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν') →ₗ[
      KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν'] oneConcatSub (ν := ν) (ν' := ν') Q :=
  Finsupp.linearCombination _ (hatWSub σ)

/-- The index equivalence between the `k`-basis of `Shuffle →₀ R(ν) ⊗ R(ν')` and
`IndIdx`. -/
def sigmaIdxEquiv : (Σ _ : Shuffle (Seq.card_add' ν ν'), Idx ν × Idx ν') ≃ IndIdx ν ν' :=
  (Equiv.sigmaEquivProd _ _).trans (Equiv.prodComm _ _)

include hPQ hP hρ₁ hρ₂ hσ in
theorem freeMap_bijective : Function.Bijective (freeMap (Q := Q) σ) := by
  let tb :=
    (lbasis (Q := Q) hPQ hP ρ₁ hρ₁).tensorProduct (lbasis (Q := Q) hPQ hP ρ₂ hρ₂)
  let kb := Finsupp.basis (R := k) (ι := Shuffle (Seq.card_add' ν ν')) (fun _ => tb)
  let B := inductionBasis (Q := Q) hPQ hP ρ₁ ρ₂ σ hρ₁ hρ₂ hσ
  have key : (freeMap (Q := Q) σ).restrictScalars k =
      (kb.equiv B sigmaIdxEquiv).toLinearMap := by
    refine kb.ext fun ⟨u, x⟩ => ?_
    rw [LinearEquiv.coe_coe, Basis.equiv_apply]
    apply Subtype.ext
    simp only [LinearMap.restrictScalars_apply, kb, Finsupp.coe_basis, freeMap,
      Finsupp.linearCombination_single, coe_tensor_smul, tb, Basis.tensorProduct_apply']
    rw [show sigmaIdxEquiv ⟨u, x⟩ = (x, u) from rfl, inductionBasis_apply]
    rfl
  have hb : Function.Bijective ((freeMap (Q := Q) σ).restrictScalars k) := by
    rw [key]; exact (kb.equiv B sigmaIdxEquiv).bijective
  exact hb

/-- **KL I, Proposition 2.16.** `1_{ν,ν'} R(ν + ν')` is a free left `R(ν) ⊗ R(ν')`-module
with basis `ŵ_u = 1_{ν,ν'} ψ_{σ(u)}`, `u` running over the minimal length representatives
of the cosets `(S_n × S_{n'}) u`. -/
noncomputable def freeBasis : Basis (Shuffle (Seq.card_add' ν ν'))
    (KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν') (oneConcatSub (ν := ν) (ν' := ν') Q) :=
  Basis.ofRepr
    (LinearEquiv.ofBijective _ (freeMap_bijective hPQ hP ρ₁ ρ₂ σ hρ₁ hρ₂ hσ)).symm

theorem freeBasis_apply (u : Shuffle (Seq.card_add' ν ν')) :
    (freeBasis hPQ hP ρ₁ ρ₂ σ hρ₁ hρ₂ hσ u : KLRAlgebra k Q (ν + ν')) =
      hatW σ u := by
  simp only [freeBasis, Basis.coe_ofRepr, LinearEquiv.symm_symm, LinearEquiv.ofBijective_apply]
  rw [freeMap, Finsupp.linearCombination_single, one_smul]
  rfl

end Induction

/-! ### Consequences for canonical choices of reduced words -/

section Canonical

variable {ν ν' : Multiset I}

include hPQ hP in
/-- **KL I, Proposition 2.16**: `1_{ν,ν'} R(ν + ν')` is a free `R(ν) ⊗ R(ν')`-module. -/
theorem free_oneConcat :
    Module.Free (KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν')
      (oneConcatSub (ν := ν) (ν' := ν') Q) :=
  Module.Free.of_basis (freeBasis hPQ hP (canWord _) (canWord _) (fun u => canWord _ u.1)
    (fun a => ⟨isReduced_canWord _ a, wordProd_canWord _ a⟩)
    (fun b => ⟨isReduced_canWord _ b, wordProd_canWord _ b⟩)
    (fun u => ⟨isReduced_canWord _ u.1, wordProd_canWord _ u.1⟩))

omit [DecidableEq I] in
theorem canWord_one (m : ℕ) : canWord m 1 = [] := by
  have h := length_canWord m 1
  rw [length_one] at h
  exact List.length_eq_zero_iff.1 h

include hPQ hP in
/-- The inclusion `ι_{ν,ν'} : R(ν) ⊗ R(ν') → R(ν + ν')` is injective. -/
theorem concat_injective : Function.Injective (concat Q ν ν') := by
  let σ : Shuffle (Seq.card_add' ν ν') → List ℕ := fun u => canWord _ u.1
  have hσ : ∀ u : Shuffle (Seq.card_add' ν ν'),
      IsReduced _ (σ u) ∧ wordProd _ (σ u) = u.1 :=
    fun u => ⟨isReduced_canWord _ u.1, wordProd_canWord _ u.1⟩
  have hbij := freeMap_bijective (Q := Q) hPQ hP (canWord _) (canWord _) σ
    (fun a => ⟨isReduced_canWord _ a, wordProd_canWord _ a⟩)
    (fun b => ⟨isReduced_canWord _ b, wordProd_canWord _ b⟩) hσ
  let u₁ : Shuffle (Seq.card_add' ν ν') := ⟨1, isShuffle_one _⟩
  have h1 : ∀ t, ((freeMap (Q := Q) σ (Finsupp.single u₁ t) : oneConcatSub Q) :
      KLRAlgebra k Q (ν + ν')) = concat Q ν ν' t := by
    intro t
    rw [freeMap, Finsupp.linearCombination_single, coe_tensor_smul]
    show concat Q ν ν' t * (oneConcat Q ν ν' * ψw (canWord _ 1)) = _
    rw [canWord_one, ψw_nil, mul_one, concat_mul_oneConcat]
  intro t t' h
  have := hbij.1 (a₁ := Finsupp.single u₁ t) (a₂ := Finsupp.single u₁ t')
    (Subtype.ext (by rw [h1, h1, h]))
  exact Finsupp.single_injective u₁ this

end Canonical

end KLRAlgebra

end Categorification.KLR

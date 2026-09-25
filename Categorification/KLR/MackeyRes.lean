/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Restriction

/-!
# Restriction of the projective modules `P_s`

Khovanov–Lauda I (arXiv:0803.4121v2), §2.6, **Proposition 2.19** (first formula, ungraded):
for `s ∈ Seq(ν + ν')`,
`Res_{ν,ν'} P_s ≅ ⊕ P_i ⊗ P_j`,
the sum over all ways of writing `s` as a shuffle of `i ∈ Seq ν` and `j ∈ Seq ν'`.

Here `P_s = R(ν + ν') 1_s` (`KLRAlgebra.projP`). A way of writing `s` as a shuffle of `i` and
`j` is the same as a minimal length coset representative `u` of `(S_n × S_{n'}) \ S_m`
(`TypeA.Shuffle`) with `u • s = ij` (`KLRAlgebra.ShuffleOf s`): the subsequence of `s` at the
positions `u⁻¹(0), …, u⁻¹(n - 1)` is `i` and the complementary subsequence is `j`. The summand
`P_i ⊗ P_j` is realised as the left ideal `(R(ν) ⊗ R(ν')) (1_i ⊗ 1_j)` (`KLRAlgebra.projPP`).

The isomorphism (`KLRAlgebra.resProjEquiv`) sends `(t_u)_u` to `∑_u ι(t_u) ψ_{σ(u)} 1_s`; it is a
consequence of Proposition 2.16 (`KLRAlgebra.freeMap_bijective`). The grading shifts
`{deg(i, j, s)}` of the paper are not recorded here.
-/

namespace Categorification.KLR

open Equiv MvPolynomial TypeA
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k}

namespace KLRAlgebra

section Defs

variable {μ ν ν' : Multiset I}

variable (Q) in
/-- The projective module `P_s = R(μ) 1_s`, as a left ideal. -/
noncomputable def projP (s : Seq μ) : Submodule (KLRAlgebra k Q μ) (KLRAlgebra k Q μ) :=
  Submodule.span _ {e s}

theorem mem_projP {s : Seq μ} {r : KLRAlgebra k Q μ} : r ∈ projP Q s ↔ r * e s = r := by
  rw [projP, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    rw [smul_eq_mul, mul_assoc, e_mul_self]
  · intro h; exact ⟨r, h⟩

variable (Q) in
/-- The projective `R(ν) ⊗ R(ν')`-module `P_i ⊗ P_j`, as the left ideal
`(R(ν) ⊗ R(ν')) (1_i ⊗ 1_j)`. -/
noncomputable def projPP (i : Seq ν) (j : Seq ν') :
    Submodule (KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν') (KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν') :=
  Submodule.span _ {e i ⊗ₜ e j}

theorem mem_projPP {i : Seq ν} {j : Seq ν'} {t : KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν'} :
    t ∈ projPP Q i j ↔ t * (e i ⊗ₜ e j) = t := by
  rw [projPP, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    rw [smul_eq_mul, mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, e_mul_self, e_mul_self]
  · intro h; exact ⟨t, h⟩

variable (ν ν') in
/-- The ways of writing `s` as a shuffle of a sequence of weight `ν` and one of weight `ν'`:
the minimal coset representatives `u` with `u • s ∈ Seq(ν) Seq(ν')`. -/
abbrev ShuffleOf (s : Seq (ν + ν')) : Type :=
  {u : Shuffle (Seq.card_add' ν ν') // u.1 • s ∈ concatSet ν ν'}

noncomputable instance ShuffleOf.instFintypeMackeyRes (s : Seq (ν + ν')) :
    Fintype (ShuffleOf ν ν' s) :=
  Fintype.ofFinite _

/-- The two sequences `(i, j)` with `u • s = ij`. -/
noncomputable def ShuffleOf.split {s : Seq (ν + ν')} (u : ShuffleOf ν ν' s) : Seq ν × Seq ν' :=
  (Classical.choose (mem_concatSet.1 u.2),
    Classical.choose (Classical.choose_spec (mem_concatSet.1 u.2)))

theorem ShuffleOf.split_spec {s : Seq (ν + ν')} (u : ShuffleOf ν ν' s) :
    u.split.1.append u.split.2 = u.1.1 • s :=
  Classical.choose_spec (Classical.choose_spec (mem_concatSet.1 u.2))

end Defs

/-! ### Proposition 2.19 -/

section Main

variable {ν ν' : Multiset I}
  (σ : Shuffle (Seq.card_add' ν ν') → List ℕ)

noncomputable instance instFintypeShuffleMackeyRes : Fintype (Shuffle (Seq.card_add' ν ν')) :=
  Fintype.ofFinite _

/-- The diagram `ψ_{σ(u)} 1_s`, i.e. `ŵ_u 1_s` for `u • s ∈ Seq(ν) Seq(ν')`. -/
noncomputable def resElt (s : Seq (ν + ν')) (u : Shuffle (Seq.card_add' ν ν')) :
    KLRAlgebra k Q (ν + ν') :=
  ψw (σ u) * e s

variable (hσ : ∀ u, IsReduced (Multiset.card (ν + ν')) (σ u) ∧
    wordProd (Multiset.card (ν + ν')) (σ u) = u.1)

include hσ in
theorem resElt_eq (s : Seq (ν + ν')) (u : Shuffle (Seq.card_add' ν ν')) :
    (resElt σ s u : KLRAlgebra k Q (ν + ν')) = e (u.1 • s) * ψw (σ u) := by
  rw [resElt, ψw_mul_e, (hσ u).2]

include hσ in
theorem hatW_mul_e (s : Seq (ν + ν')) (u : Shuffle (Seq.card_add' ν ν')) :
    (hatW σ u * e s : KLRAlgebra k Q (ν + ν')) =
      if u.1 • s ∈ concatSet ν ν' then resElt σ s u else 0 := by
  rw [hatW, mul_assoc, ← resElt, resElt_eq σ hσ, ← mul_assoc, oneConcat, eSum_mul_e]
  split_ifs <;> simp

include hσ in
/-- For `t ∈ P_i ⊗ P_j` with `u • s = ij`, `ι(t) ŵ_u = ι(t) ψ_{σ(u)} 1_s`. -/
theorem concat_mul_resElt (s : Seq (ν + ν')) (u : ShuffleOf ν ν' s)
    {t : KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν'} (ht : t ∈ projPP Q u.split.1 u.split.2) :
    concat Q ν ν' t * resElt σ s u.1 = concat Q ν ν' t * hatW σ u.1 := by
  rw [mem_projPP] at ht
  rw [← ht, concat_mul, concat_e_tmul_e, u.split_spec, resElt_eq σ hσ, hatW, mul_assoc,
    mul_assoc, ← mul_assoc (e _) (oneConcat Q ν ν'), oneConcat, e_mul_eSum, if_pos u.2,
    ← mul_assoc (e _) (e _), e_mul_self]

/-- The map `(t_u)_u ↦ ∑_u ι(t_u) ψ_{σ(u)} 1_s`. -/
noncomputable def resSum (s : Seq (ν + ν'))
    (t : (u : ShuffleOf ν ν' s) → projPP Q u.split.1 u.split.2) : KLRAlgebra k Q (ν + ν') :=
  ∑ u, concat Q ν ν' (t u : KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν') * resElt σ s u.1

theorem resSum_mem_projP (s : Seq (ν + ν'))
    (t : (u : ShuffleOf ν ν' s) → projPP Q u.split.1 u.split.2) :
    resSum σ s t ∈ projP Q s := by
  rw [mem_projP, resSum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [resElt, mul_assoc, mul_assoc, e_mul_self]

theorem oneConcat_mul_resSum (s : Seq (ν + ν'))
    (t : (u : ShuffleOf ν ν' s) → projPP Q u.split.1 u.split.2) :
    oneConcat Q ν ν' * resSum σ s t = resSum σ s t := by
  rw [resSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← mul_assoc, oneConcat_mul_concat]

/-- The `R(ν) ⊗ R(ν')`-linear map `⊕_u P_{i_u} ⊗ P_{j_u} → Res_{ν,ν'} P_s`. -/
noncomputable def resProjMap (s : Seq (ν + ν')) :
    ((u : ShuffleOf ν ν' s) → projPP Q u.split.1 u.split.2) →ₗ[KLRAlgebra k Q ν ⊗[k]
      KLRAlgebra k Q ν']
      Res Q ν ν' (projP Q s) where
  toFun t := ⟨⟨resSum σ s t, resSum_mem_projP σ s t⟩, by
    rw [mem_resSubgroup]
    exact Subtype.ext (by rw [Submodule.coe_smul, smul_eq_mul]; exact oneConcat_mul_resSum σ s t)⟩
  map_add' t t' := by
    refine Subtype.ext (Subtype.ext ?_)
    simp only [resSum, Pi.add_apply, Submodule.coe_add, map_add, add_mul,
      Finset.sum_add_distrib]
    rfl
  map_smul' c t := by
    refine Subtype.ext (Subtype.ext ?_)
    rw [coe_res_smul]
    simp only [resSum, Pi.smul_apply, Submodule.coe_smul, smul_eq_mul, concat_mul, mul_assoc,
      RingHom.id_apply, Finset.mul_sum]

theorem coe_resProjMap (s : Seq (ν + ν'))
    (t : (u : ShuffleOf ν ν' s) → projPP Q u.split.1 u.split.2) :
    ((resProjMap σ s t : projP Q s) : KLRAlgebra k Q (ν + ν')) = resSum σ s t := rfl

variable [IsDomain k] {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)

private theorem sum_subtype_ite {α M : Type*} [Fintype α] [AddCommMonoid M] (p : α → Prop)
    [DecidablePred p] [Fintype {a // p a}] (g : α → M) :
    (∑ a, if p a then g a else 0) = ∑ a : {a // p a}, g a := by
  rw [← Finset.sum_filter, Finset.sum_subtype (Finset.univ.filter p) (p := p) (by simp)]

private theorem sum_subtype_dite {α M : Type*} [Fintype α] [AddCommMonoid M] (p : α → Prop)
    [DecidablePred p] [Fintype {a // p a}] (g : {a // p a} → M) :
    (∑ a, if h : p a then g ⟨a, h⟩ else 0) = ∑ a : {a // p a}, g a := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ p]
  rw [Finset.sum_eq_zero (s := Finset.univ.filter fun a => ¬ p a)
    (fun a ha => dif_neg (Finset.mem_filter.1 ha).2), add_zero]
  rw [Finset.sum_subtype (Finset.univ.filter p) (p := p) (by simp)]
  exact Finset.sum_congr rfl fun a _ => dif_pos a.2

omit [IsDomain k] in
theorem coe_freeMap (f : Shuffle (Seq.card_add' ν ν') →₀ KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν') :
    ((freeMap (Q := Q) σ f : oneConcatSub Q) : KLRAlgebra k Q (ν + ν')) =
      ∑ u, concat Q ν ν' (f u) * hatW σ u := by
  rw [freeMap, Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (fun _ => by simp),
    Submodule.coe_sum]
  rfl

variable (ρ₁ : Perm (Fin (Multiset.card ν)) → List ℕ)
  (ρ₂ : Perm (Fin (Multiset.card ν')) → List ℕ)
  (hρ₁ : ∀ a, IsReduced (Multiset.card ν) (ρ₁ a) ∧ wordProd (Multiset.card ν) (ρ₁ a) = a)
  (hρ₂ : ∀ b, IsReduced (Multiset.card ν') (ρ₂ b) ∧ wordProd (Multiset.card ν') (ρ₂ b) = b)

include hPQ hP hρ₁ hρ₂ hσ in
theorem resProjMap_bijective (s : Seq (ν + ν')) :
    Function.Bijective (resProjMap (Q := Q) σ s) := by
  classical
  have hbij := freeMap_bijective (Q := Q) hPQ hP ρ₁ ρ₂ σ hρ₁ hρ₂ hσ
  constructor
  · intro t t' htt
    have h0 : resSum σ s t = resSum σ s t' := by
      have := congrArg (fun x : Res Q ν ν' (projP Q s) => ((x : projP Q s) :
        KLRAlgebra k Q (ν + ν'))) htt
      simpa only [coe_resProjMap] using this
    let f : (Shuffle (Seq.card_add' ν ν')) → KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν' :=
      fun u => if h : u.1 • s ∈ concatSet ν ν' then (t ⟨u, h⟩ : _) else 0
    let f' : (Shuffle (Seq.card_add' ν ν')) → KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν' :=
      fun u => if h : u.1 • s ∈ concatSet ν ν' then (t' ⟨u, h⟩ : _) else 0
    have hf : ∀ (g : (u : ShuffleOf ν ν' s) → projPP Q u.split.1 u.split.2),
        resSum σ s g = ((freeMap (Q := Q) σ (Finsupp.equivFunOnFinite.symm
          fun u => if h : u.1 • s ∈ concatSet ν ν' then (g ⟨u, h⟩ : _) else 0) : oneConcatSub Q) :
            KLRAlgebra k Q (ν + ν')) := by
      intro g
      rw [coe_freeMap, resSum]
      simp only [Finsupp.equivFunOnFinite_symm_apply_toFun]
      rw [← sum_subtype_dite (fun u : Shuffle (Seq.card_add' ν ν') => u.1 • s ∈ concatSet ν ν')]
      refine Finset.sum_congr rfl fun u _ => ?_
      split_ifs with h
      · exact concat_mul_resElt σ hσ s ⟨u, h⟩ (g ⟨u, h⟩).2
      · rw [map_zero, zero_mul]
    rw [hf t, hf t'] at h0
    have := hbij.1 (Subtype.ext h0)
    funext u
    have hu := congrArg (fun F => F u.1) (Finsupp.equivFunOnFinite.symm.injective this)
    simp only [dif_pos u.2] at hu
    exact Subtype.ext hu
  · rintro ⟨⟨r, hr⟩, hr'⟩
    rw [mem_resSubgroup] at hr'
    have hr1 : oneConcat Q ν ν' * r = r := congrArg Subtype.val hr'
    have hr2 : r * e s = r := mem_projP.1 hr
    obtain ⟨f, hf⟩ := hbij.2 ⟨r, mem_oneConcatSub.2 hr1⟩
    have hfr : r = ∑ u, concat Q ν ν' (f u) * hatW σ u := by
      rw [← coe_freeMap, hf]
    let t : (u : ShuffleOf ν ν' s) → projPP Q u.split.1 u.split.2 := fun u =>
      ⟨f u.1 * (e u.split.1 ⊗ₜ e u.split.2), mem_projPP.2 (by
        rw [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, e_mul_self, e_mul_self])⟩
    refine ⟨t, Subtype.ext (Subtype.ext ?_)⟩
    show resSum σ s t = r
    conv_rhs => rw [← hr2, hfr, Finset.sum_mul]
    simp only [mul_assoc, hatW_mul_e σ hσ, mul_ite, mul_zero]
    rw [sum_subtype_ite (fun u : Shuffle (Seq.card_add' ν ν') => u.1 • s ∈ concatSet ν ν')]
    refine Finset.sum_congr rfl fun u _ => ?_
    show concat Q ν ν' (f u.1 * _) * resElt σ s u.1 = _
    rw [concat_mul, concat_e_tmul_e, ShuffleOf.split_spec, mul_assoc, resElt_eq σ hσ,
      ← mul_assoc (e _), e_mul_self]

/-- **KL I, Proposition 2.19** (first formula, ungraded): for `s ∈ Seq(ν + ν')`,
`Res_{ν,ν'} P_s ≅ ⊕ P_i ⊗ P_j` as left `R(ν) ⊗ R(ν')`-modules, the sum over all ways of writing
`s` as a shuffle of `i ∈ Seq ν` and `j ∈ Seq ν'` (indexed by the minimal coset representatives
`u` with `u • s = ij`). The isomorphism sends `(t_u)_u` to `∑_u ι(t_u) ψ_{σ(u)} 1_s`. -/
noncomputable def resProjEquiv (s : Seq (ν + ν')) :
    ((u : ShuffleOf ν ν' s) → projPP Q u.split.1 u.split.2) ≃ₗ[KLRAlgebra k Q ν ⊗[k]
      KLRAlgebra k Q ν'] Res Q ν ν' (projP Q s) :=
  LinearEquiv.ofBijective (resProjMap σ s) (resProjMap_bijective σ hσ hPQ hP ρ₁ ρ₂ hρ₁ hρ₂ s)

theorem resProjEquiv_apply (s : Seq (ν + ν'))
    (t : (u : ShuffleOf ν ν' s) → projPP Q u.split.1 u.split.2) :
    ((resProjEquiv σ hσ hPQ hP ρ₁ ρ₂ hρ₁ hρ₂ s t : projP Q s) : KLRAlgebra k Q (ν + ν')) =
      ∑ u, concat Q ν ν' (t u : KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν') * (ψw (σ u.1) * e s) :=
  rfl

end Main

end KLRAlgebra

end Categorification.KLR

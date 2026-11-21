/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Crystal.IndDecomp

/-!
# Idempotents killing an induced module

Let `N` be an `R(ν) ⊗ R(ν')`-module on which `1_a ⊗ 1_b` acts by zero unless the first label of
`b` is a fixed colour `c`. If the first `|ν| + 1` labels of `s ∈ Seq(ν + ν')` all differ from
`c`, then `1_s` acts by zero on `Ind N`: in the shuffle decomposition `Ind N ≅ ⊕_u N`
(`indDecomp`) the summand `u` sees `1_{u s}`, and if `u s = a b` with `b` starting with `c`,
the position of that `c` in `s` lies after `|ν| + 1` positions which a shuffle must all send
into the first block, which is impossible.

This is the vanishing of the error terms of the Mackey intertwining in Webster,
arXiv:1309.3796v3, proof of Proposition 5.5, where `c` is the last red strand and `N` is a
cyclotomic quotient in which no black strand may stand first.
-/

noncomputable section

namespace Categorification.KLR

open KLRAlgebra Equiv TypeA
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {ν ν' : Multiset I}

omit [DecidableEq I] in
/-- A shuffle `u` sends the first position of the second block to a position at most `|ν|`
under `u⁻¹`: otherwise `u` would map the first `|ν| + 1` positions into the first block. -/
theorem shuffle_first_inr_le (u : Shuffle (Seq.card_add' ν ν'))
    (h0 : 0 < Multiset.card ν') :
    (u.1⁻¹ (blockEquiv (Seq.card_add' ν ν') (Sum.inr ⟨0, h0⟩))).val ≤ Multiset.card ν := by
  set r := u.1⁻¹ (blockEquiv (Seq.card_add' ν ν') (Sum.inr ⟨0, h0⟩))
  have hc := Multiset.card_add ν ν'
  by_contra hr
  push Not at hr
  have hlt : ∀ q : Fin (Multiset.card ν + 1),
      q.val < Multiset.card (ν + ν') := fun q => by
    have := q.2; rw [Multiset.card_add]; omega
  have hin : ∀ q : Fin (Multiset.card ν + 1),
      (u.1 ⟨q.val, hlt q⟩).val < Multiset.card ν := by
    intro q
    by_contra hq
    push Not at hq
    have hy : (u.1 ⟨q.val, hlt q⟩).val - Multiset.card ν < Multiset.card ν' := by
      have := (u.1 ⟨q.val, hlt q⟩).2; omega
    have hb : blockEquiv (Seq.card_add' ν ν') (Sum.inr ⟨_, hy⟩) = u.1 ⟨q.val, hlt q⟩ :=
      Fin.ext (by simp only [blockEquiv_inr_val]; omega)
    have hmono := u.2.2.monotone (show (⟨0, h0⟩ : Fin (Multiset.card ν')) ≤ ⟨_, hy⟩ from
      Fin.mk_le_mk.2 (Nat.zero_le _))
    rw [hb, Perm.inv_def, Equiv.symm_apply_apply] at hmono
    have : r.val ≤ q.val := hmono
    have := q.2
    omega
  have hinj : Function.Injective fun q : Fin (Multiset.card ν + 1) =>
      (⟨(u.1 ⟨q.val, hlt q⟩).val, hin q⟩ : Fin (Multiset.card ν)) := by
    intro q q' hqq
    have := u.1.injective (Fin.ext (Fin.mk.inj hqq))
    exact Fin.ext (Fin.mk.inj this)
  have := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_fin] at this
  omega

variable {N : Type*} [AddCommGroup N] [Module k N] [Module (TensorKLR Q ν ν') N]
  [IsScalarTower k (TensorKLR Q ν ν') N]

/-- **Idempotents with no colour `c` among their first `|ν| + 1` labels kill `Ind N`** when
`1_a ⊗ 1_b` kills `N` unless `b` starts with `c`. -/
theorem e_smul_ind_eq_zero (hsym : KLRSymm Q) (c : I)
    (hN : ∀ (a : Seq ν) (b : Seq ν') (n : N),
      (∀ h : 0 < Multiset.card ν', b.lbl ⟨0, h⟩ ≠ c) →
        ((e a ⊗ₜ e b : TensorKLR Q ν ν') • n) = 0)
    (s : Seq (ν + ν')) (hs : ∀ q : Fin (Multiset.card (ν + ν')),
      q.val ≤ Multiset.card ν → s.lbl q ≠ c)
    (y : Ind Q ν ν' N) : (e s : KLRAlgebra k Q (ν + ν')) • y = 0 := by
  apply (indDecomp hsym N).injective
  funext u
  rw [indDecomp_e_smul, map_zero, Pi.zero_apply]
  by_cases hm : u.1 • s ∈ concatSet ν ν'
  · obtain ⟨a, b, hab⟩ := mem_concatSet.1 hm
    rw [← hab, concatIdem_append]
    refine hN a b _ fun h0 hb => ?_
    have hpos := Seq.append_posR a b ⟨0, h0⟩
    rw [hab, Seq.smul_apply] at hpos
    have hle := shuffle_first_inr_le u h0
    refine hs _ ?_ (hpos.trans hb)
    exact hle
  · rw [concatIdem_of_not_mem hm, zero_smul]

end Categorification.KLR

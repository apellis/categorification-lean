/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicPsi

/-!
# Lower first-strand terms

Control of the terms discarded by the coefficient map `B`, for the computation
of its value on the intertwiner product in Kang–Kashiwara, arXiv:1102.4677v4, §5.2.
-/

namespace Categorification.KLR.KLRAlgebra

open MvPolynomial TypeA
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}

local notation "R" => KLRAlgebra k Q ν

private theorem range'_zero_eq_range (n : ℕ) : List.range' 0 n = List.range n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range'_concat, List.range_succ, ih]; simp

theorem hflip_tauProd (n : ℕ) : (hflip (tauProd n) : R) = ψw (descRun 0 n) := by
  rw [tauProd, hflip_ψw, descRun, range'_zero_eq_range]

theorem hflip_descRun (n : ℕ) : (hflip (ψw (descRun 0 n)) : R) = tauProd n := by
  rw [hflip_ψw, descRun, List.reverse_reverse, range'_zero_eq_range, tauProd]

theorem hflip_mem_subR1 {u : R} (hu : u ∈ subR1 (k := k) (Q := Q) ν) :
    hflip u ∈ subR1 (k := k) (Q := Q) ν := by
  induction hu using Algebra.adjoin_induction with
  | mem y hy =>
    rcases hy with (⟨b, rfl⟩ | ⟨t, rfl⟩) | ⟨j, hj, rfl⟩
    · rw [hflip_x]; exact x_mem_subR1 _
    · rw [hflip_e]; exact e_mem_subR1 _
    · rw [hflip_ψ]; exact ψ_mem_subR1 hj
  | algebraMap c =>
    rw [Algebra.algebraMap_eq_smul_one, hflip_smul, hflip_one]
    exact Subalgebra.smul_mem _ (Subalgebra.one_mem _) c
  | add y z _ _ hy hz => rw [hflip_add]; exact Subalgebra.add_mem _ hy hz
  | mul y z _ _ hy hz => rw [hflip_mul]; exact Subalgebra.mul_mem _ hz hy

/-- The terms whose first strand travels at most `c` places. -/
noncomputable def firstLower (c : ℕ) : Submodule k R :=
  (spTau (k := k) (Q := Q) ν c).comap (hflipEquiv k Q ν).toLinearMap

theorem mem_firstLower {c : ℕ} {r : R} :
    r ∈ firstLower c ↔ hflip r ∈ spTau (k := k) (Q := Q) ν c := Iff.rfl

theorem firstLower_mono {c d : ℕ} (h : c ≤ d) :
    firstLower (k := k) (Q := Q) (ν := ν) c ≤ firstLower d :=
  fun _ hr => spTau_mono h hr

theorem descRun_mul_mem_firstLower {c b : ℕ} (hb : b ≤ c) {u : R}
    (hu : u ∈ subR1 (k := k) (Q := Q) ν) : ψw (descRun 0 b) * u ∈ firstLower c := by
  rw [mem_firstLower, hflip_mul, hflip_descRun]
  exact mem_spTau hb (hflip_mem_subR1 hu)

theorem firstLower_mul_subR1 {c : ℕ} {r u : R} (hr : r ∈ firstLower c)
    (hu : u ∈ subR1 (k := k) (Q := Q) ν) : r * u ∈ firstLower c := by
  rw [mem_firstLower, hflip_mul]
  exact subR1_mul_mem_spTau (hflip_mem_subR1 hu) hr

theorem spTau_mul_pol {c : ℕ} {r : R} (hr : r ∈ spTau (k := k) (Q := Q) ν c)
    (f : MvPolynomial (Fin (Multiset.card ν)) k) : r * pol f ∈ spTau ν c := by
  induction hr using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, hu, b, hb, rfl⟩ := hy
    rw [mul_assoc]
    apply subR1_mul_mem_spTau hu
    apply spTau_mono hb
    have h := tauProd_pol_mem_spTau (Q := Q) (ν := ν) b f 1 (Subalgebra.one_mem _)
    rwa [mul_one] at h
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [add_mul]; exact Submodule.add_mem _ hy hz
  | smul r y _ hy => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hy

theorem pol_mul_mem_firstLower {c : ℕ} {r : R} (hr : r ∈ firstLower c)
    (f : MvPolynomial (Fin (Multiset.card ν)) k) : pol f * r ∈ firstLower c := by
  rw [mem_firstLower, hflip_mul, hflip_pol]
  exact spTau_mul_pol hr f

/-- A crossing strictly above the reachable first-strand positions cannot increase them. -/
theorem ψ_mul_mem_firstLower {c j : ℕ} {r : R} (hr : r ∈ firstLower c) (hj : c + 1 ≤ j) :
    ψ j * r ∈ firstLower c := by
  rw [mem_firstLower, hflip_mul, hflip_ψ]
  have hr' : hflip r ∈ spTau (k := k) (Q := Q) ν c := hr
  have h := mul_ψw_mem_spTau hr' [j] (by
    intro l hl
    have hl' : l = j := List.mem_singleton.mp hl
    simpa only [hl'] using hj)
  simpa only [ψw_cons, ψw_nil, mul_one] using h

/-- Moving a polynomial past the full crossing changes only lower first-strand terms. -/
theorem tauProd_pol_sub_mem_spTau (n : ℕ) (hn : n < Multiset.card ν)
    (f : MvPolynomial (Fin (Multiset.card ν)) k) :
    tauProd n * pol f - pol (rename (cP (Multiset.card ν) n).symm f) * tauProd n ∈
      spTau (k := k) (Q := Q) ν (n - 1) := by
  induction n generalizing f with
  | zero =>
    simp only [tauProd_zero, cP_zero, Equiv.Perm.one_def, Equiv.refl_symm, Equiv.coe_refl,
      rename_id_apply, one_mul, mul_one, sub_self]
    exact Submodule.zero_mem _
  | succ n ih =>
    have key : (⇑(cP (Multiset.card ν) n).symm ∘
        ⇑(Equiv.swap (⟨n, by omega⟩ : Fin (Multiset.card ν)) ⟨n + 1, hn⟩)) =
        ⇑(cP (Multiset.card ν) (n + 1)).symm := by
      funext b
      rw [cP_succ, Function.comp_apply, ← sadj_eq_swap (by omega)]
      show _ = (cP (Multiset.card ν) n).symm ((sadj (Multiset.card ν) n).symm b)
      rw [sadj_symm]
    have hm : (tauProd n * pol (swapPol n hn f) -
        pol (rename (cP (Multiset.card ν) n).symm (swapPol n hn f)) * tauProd n) * ψ n ∈
        spTau (k := k) (Q := Q) ν n := by
      cases n with
      | zero =>
        simp only [tauProd_zero, cP_zero, Equiv.Perm.one_def, Equiv.refl_symm, Equiv.coe_refl,
          rename_id_apply, one_mul, mul_one, sub_self, zero_mul]
        exact Submodule.zero_mem _
      | succ n =>
        have h := mul_ψw_mem_spTau (ih (by omega) (swapPol (n + 1) hn f)) [n + 1] (by
          intro l hl
          have hl' := List.mem_singleton.mp hl
          omega)
        exact spTau_mono (show n + 1 - 1 ≤ n + 1 by omega)
          (by simpa only [ψw_cons, ψw_nil, mul_one] using h)
    have he := tauProd_pol_mem_spTau (Q := Q) (ν := ν) n
      (NilHecke.dd k (Multiset.card ν) n f) (eqIdem n hn) (eqIdem_mem n hn)
    have hsum := Submodule.add_mem _ hm he
    have heq : (tauProd n * pol (swapPol n hn f) -
        pol (rename (cP (Multiset.card ν) n).symm (swapPol n hn f)) * tauProd n) * ψ n +
        tauProd n * pol (NilHecke.dd k (Multiset.card ν) n f) * eqIdem n hn =
        (tauProd (n + 1) * pol f -
        pol (rename (cP (Multiset.card ν) (n + 1)).symm f) * tauProd (n + 1) : R) := by
      rw [tauProd_succ, mul_assoc (tauProd n) (ψ n) (pol f), ψ_mul_pol n hn, mul_add,
        swapPol, rename_rename, key]
      noncomm_ring
    rw [heq] at hsum
    simpa only [Nat.add_sub_cancel] using hsum

/-- The corresponding lower-error identity for the descending first-strand word. -/
theorem pol_descRun_sub_mem_firstLower (n : ℕ) (hn : n < Multiset.card ν)
    (f : MvPolynomial (Fin (Multiset.card ν)) k) :
    pol f * ψw (descRun 0 n) -
        ψw (descRun 0 n) * pol (rename (cP (Multiset.card ν) n).symm f) ∈
      firstLower (k := k) (Q := Q) (ν := ν) (n - 1) := by
  rw [mem_firstLower, hflip_sub, hflip_mul, hflip_mul, hflip_pol, hflip_pol,
    hflip_descRun]
  exact tauProd_pol_sub_mem_spTau n hn f

/-- The right polynomial multiplying the longest first-strand word in `G_n e(s)`. -/
noncomputable def gLead : (n : ℕ) → n < Multiset.card ν → Seq ν →
    MvPolynomial (Fin (Multiset.card ν)) k
  | 0, _, _ => 1
  | n + 1, hn, s =>
    (if s.1 ⟨n + 1, hn⟩ = s.1 ⟨0, by omega⟩ then
      (X ⟨0, by omega⟩ - X ⟨n + 1, hn⟩) ^ 2 else 1) * gLead n (by omega) s

theorem descRun_succ (n : ℕ) :
    (ψw (descRun 0 (n + 1)) : R) = ψ n * ψw (descRun 0 n) := by
  rw [← hflip_tauProd, tauProd_succ, hflip_mul, hflip_ψ, hflip_tauProd]

/-- The intertwiner has the expected leading first-strand coefficient; all other
terms are strictly lower. This is the coefficient computation used before KK (5.15). -/
theorem gProd_sub_top_mem_firstLower (n : ℕ) (hn : n < Multiset.card ν) (s : Seq ν) :
    (gProd n * e s - ψw (descRun 0 n) * pol (gLead n hn s) * e s : R) ∈
      firstLower (n - 1) := by
  induction n with
  | zero =>
    simp only [gProd_zero, gLead, map_one, descRun, List.range'_zero, List.reverse_nil,
      ψw_nil, one_mul, mul_one, sub_self]
    exact Submodule.zero_mem _
  | succ n ih =>
    have hn' : n < Multiset.card ν := by omega
    let L := gLead (k := k) n hn' s
    let D : R := ψw (descRun 0 n)
    let err : R := gProd n * e s - D * pol L * e s
    have herr : err ∈ firstLower (k := k) (Q := Q) (ν := ν) (n - 1) := ih hn'
    have hcross : ψ n * err ∈ firstLower (k := k) (Q := Q) (ν := ν) n := by
      cases n with
      | zero =>
        have he : err = 0 := by
          simp only [err, D, L, gProd_zero, gLead, map_one, descRun, List.range'_zero,
            List.reverse_nil, ψw_nil, one_mul, mul_one, sub_self]
        rw [he, mul_zero]
        exact Submodule.zero_mem _
      | succ n =>
        exact firstLower_mono (show n + 1 - 1 ≤ n + 1 by omega)
          (ψ_mul_mem_firstLower herr (by omega))
    have htop : D * pol L * e s ∈ firstLower (k := k) (Q := Q) (ν := ν) n := by
      rw [mul_assoc]
      exact descRun_mul_mem_firstLower le_rfl
        (Subalgebra.mul_mem _ (pol_mem_subR1 L) (e_mem_subR1 s))
    have hG : gProd n * e s ∈ firstLower (k := k) (Q := Q) (ν := ν) n := by
      have h := Submodule.add_mem _ (firstLower_mono (Nat.sub_le n 1) herr) htop
      simpa only [err, sub_add_cancel] using h
    have hstep : (gProd (n + 1) * e s : R) =
        (if s.1 ⟨n + 1, hn⟩ = s.1 ⟨0, by omega⟩ then
          (x ⟨n + 1, hn⟩ - x ⟨n, hn'⟩) +
            (x ⟨n + 1, hn⟩ - x ⟨n, hn'⟩) ^ 2 * ψ n else ψ n) * (gProd n * e s) := by
      rw [gProd_succ_mul_e n hn s, ← mul_assoc, gInt_mul_e,
        cP_smul_apply_self n hn', cP_smul_apply_of_lt n hn' s _ (by simp),
        mul_assoc, ← gProd_mul_e n hn' s]
      simp only [eq_comm]
    rw [hstep, gLead]
    split_ifs with hs
    · let d : MvPolynomial (Fin (Multiset.card ν)) k := X ⟨n + 1, hn⟩ - X ⟨n, hn'⟩
      have hd : (pol d : R) = x ⟨n + 1, hn⟩ - x ⟨n, hn'⟩ := by
        dsimp only [d]
        rw [map_sub, pol_X, pol_X]
      have hren : rename (cP (Multiset.card ν) (n + 1)).symm (d ^ 2) =
          (X ⟨0, by omega⟩ - X ⟨n + 1, hn⟩) ^ 2 := by
        have hv : (cP (Multiset.card ν) (n + 1)).symm ⟨n, hn'⟩ = ⟨n + 1, hn⟩ := by
          apply Fin.ext
          rw [cP_symm_val _ _ hn]
          simp
        dsimp only [d]
        rw [map_pow, map_sub, rename_X, rename_X, cP_symm_self, hv]
      have he := firstLower_mul_subR1 (pol_descRun_sub_mem_firstLower (Q := Q)
        (n + 1) hn (d ^ 2)) (Subalgebra.mul_mem _ (pol_mem_subR1 L) (e_mem_subR1 s))
      have h := Submodule.add_mem _ (pol_mul_mem_firstLower hG d)
        (Submodule.add_mem _ (pol_mul_mem_firstLower hcross (d ^ 2)) he)
      rw [hren] at h
      change _ ∈ firstLower (k := k) (Q := Q) (ν := ν) n at h
      convert h using 1 <;>
        (try simp only [map_mul, map_pow, hd, descRun_succ, err, D, L, Nat.add_sub_cancel])
      all_goals noncomm_ring
    · change ψ n * (gProd n * e s) -
        ψw (descRun 0 (n + 1)) * pol (1 * L) * e s ∈ firstLower ((n + 1) - 1)
      rw [one_mul, descRun_succ]
      convert hcross using 1 <;> (try simp only [err, D, Nat.add_sub_cancel])
      all_goals noncomm_ring

section Coefficient

variable (i : I) (β : Multiset I)
local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "A" => KLRAlgebra k Q (Si + β)
local notation "T" => KLRAlgebra k Q Si ⊗[k] KLRAlgebra k Q β

variable [IsDomain k] {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)

theorem bCoord_mul_oneConcat (r : A) :
    bCoord i β hPQ hP (r * oneConcat Q Si β) = bCoord i β hPQ hP r := by
  rw [← concat_one, bCoord_mul_concat, mul_one]

/-- `B` discards every lower first-strand term. -/
theorem bCoord_eq_zero_of_mem_firstLower {c : ℕ} (hc : c < Multiset.card β) {r : A}
    (hr : r ∈ firstLower c) : bCoord i β hPQ hP r = 0 := by
  have key : ∀ z ∈ spTau (k := k) (Q := Q) (Si + β) c,
      bCoord i β hPQ hP (hflip z) = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨u, hu, b, hb, rfl⟩ := hy
      rw [hflip_mul, hflip_tauProd]
      obtain ⟨t, ht⟩ := exists_concat_of_subR1 i β (hflip_mem_subR1 hu)
      rw [← bCoord_mul_oneConcat, mul_assoc, ht]
      have he := firstFree_single (Q := Q) i β (⟨b, by omega⟩ : Fin (Multiset.card β + 1)) t
      rw [← he, bCoord_firstFree, Pi.single_eq_of_ne (by intro h; have := congrArg Fin.val h; simp at this; omega)]
    | zero => rw [hflip_zero, map_zero]
    | add y z _ _ hy hz => rw [hflip_add, map_add, hy, hz, add_zero]
    | smul s y _ hy => rw [hflip_smul, map_smul, hy, smul_zero]
  simpa only [hflip_hflip] using key (hflip r) hr

/-- The final coefficient depends only on the top first-strand term. -/
theorem bCoord_eq_of_sub_mem_firstLower {c : ℕ} (hc : c < Multiset.card β) {r s : A}
    (hrs : r - s ∈ firstLower c) : bCoord i β hPQ hP r = bCoord i β hPQ hP s := by
  have h := bCoord_eq_zero_of_mem_firstLower i β hPQ hP hc hrs
  rw [map_sub, sub_eq_zero] at h
  exact h

/-- A top term with a controlled lower error determines the cyclotomic value of `B`. -/
theorem bMap_eq_of_sub_top_mem_firstLower (a : I → Polynomial k)
    (h1 : 1 < Multiset.card ((Singleton.singleton i : Multiset I) + β))
    (hβ : 0 < Multiset.card β) {c : ℕ} (hc : c < Multiset.card β) (r : A) (t : T)
    (hr : r - ψw (descRun 0 (Multiset.card β)) * concat Q Si β t ∈ firstLower c) :
    bMap i β hPQ hP a h1 hβ (Submodule.Quotient.mk r) = thetaL Q i β a t := by
  rw [bMap_mk]
  change thetaL Q i β a (bCoord i β hPQ hP r) = _
  rw [bCoord_eq_of_sub_mem_firstLower i β hPQ hP hc hr, bCoord_top]

/-- The leading polynomial controls `B` on each intertwiner summand. -/
theorem bCoord_gProd (hβ : 0 < Multiset.card β) (s : Seq (Si + β)) :
    bCoord i β hPQ hP (gProd (Multiset.card β) * e s) =
      bCoord i β hPQ hP (ψw (descRun 0 (Multiset.card β)) *
        pol (gLead (Multiset.card β) (lastPos_lt i β) s) * e s) :=
  bCoord_eq_of_sub_mem_firstLower i β hPQ hP (by omega)
    (gProd_sub_top_mem_firstLower (Multiset.card β) (lastPos_lt i β) s)

end Coefficient

end Categorification.KLR.KLRAlgebra

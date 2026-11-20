/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.IndLastStrandExact

/-!
# The last strand of an induced module when `i` occurs in one factor only

Khovanov–Lauda I (arXiv:0803.4121v2), Proposition 2.18, in the case where the restricted colour
`i` does not occur in the first factor: for `ν' = ν₀' + i` and `i ∉ ν`,
`Φ : Ind_{ν,ν₀'} ₂N → E(Ind_{ν,ν'} N)` is an isomorphism. This is the KLR input of
B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5, in the case where `i` occurs in the weight of the last block only.

Write `1_{-,i} = ι(1_{ν+ν₀'} ⊗ 1_i)` (`lastIdemOf`). In the shuffle basis adapted to the last
strand, the coordinate of `1_{-,i} y` at a shuffle `u` moving the last strand into the first
block vanishes, since `u` then places the strand coloured `i` in the first block. So every `y`
with `1_{-,i} y = y` is supported on the shuffles `v ⊕ 1`, which are the image of `Φ`.

## Main results

* `lastIdemOf_smul_indAppend` : `Φ` lands in `E(Ind_{ν,ν'} N)`;
* `mem_range_indAppend_of_lastIdemOf_smul` : for `i ∉ ν`, `E(Ind_{ν,ν'} N)` lies in the image
  of `Φ`; with `indAppend_injective`, `Φ` is an isomorphism onto `E(Ind_{ν,ν'} N)`.
-/

namespace Categorification.KLR

open Equiv MvPolynomial TypeA MulOpposite
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}

local notation "Si" i:max => (Singleton.singleton i : Multiset I)

namespace KLRAlgebra

section LastIdemOf

variable (Q) (ν ν₀' : Multiset I) (i : I)

/-- The idempotent `1_{-,i} = ι(1_{ν+ν₀'} ⊗ 1_i)` of `R(ν + ν')`, `ν' = ν₀' + i`. -/
noncomputable def lastIdemOf : KLRAlgebra k Q (ν + (ν₀' + Si i)) :=
  castKLR Q (add_assoc ν ν₀' (Si i)) (oneConcat Q (ν + ν₀') (Si i))

theorem lastIdem_eq_lastIdemOf (ν₀ : Multiset I) :
    lastIdem Q ν₀ ν₀' i = lastIdemOf Q (ν₀ + Si i) ν₀' i := rfl

theorem lastIdemOf_eq :
    lastIdemOf Q ν ν₀' i = ∑ s ∈ concatSet (ν + ν₀') (Si i),
      (e (Seq.cast (add_assoc ν ν₀' (Si i)) s) : KLRAlgebra k Q (ν + (ν₀' + Si i))) := by
  rw [lastIdemOf, oneConcat, eSum, map_sum]
  exact Finset.sum_congr rfl fun s _ => castKLR_e _ s

variable {Q ν ν₀' i}

theorem cast_last_of_mem' {s : Seq (ν + ν₀' + Si i)} (hs : s ∈ concatSet (ν + ν₀') (Si i))
    (p : Fin (Multiset.card (ν + (ν₀' + Si i))))
    (hp : p.val = Multiset.card (ν + ν₀')) :
    (Seq.cast (add_assoc ν ν₀' (Si i)) s).1 p = i := by
  rw [Seq.cast_apply]
  exact (Seq.apply_congr _ (by simp [hp])).trans (mem_concatSet_singleton_iff.1 hs)

variable {N : Type*} [AddCommGroup N] [Module k N]
  [Module (TensorKLR Q ν (ν₀' + ({i} : Multiset I))) N]
  [IsScalarTower k (TensorKLR Q ν (ν₀' + ({i} : Multiset I))) N]

/-- **`Φ` lands in `E(Ind_{ν,ν'} N)`.** -/
theorem lastIdemOf_smul_indAppend (z : Ind Q ν ν₀' (ResRight Q ν ν₀' i N)) :
    lastIdemOf Q ν ν₀' i • indAppend z = indAppend z := by
  have h := indAppend_smul (Q := Q) (N := N) (1 : KLRAlgebra k Q (ν + ν₀')) z
  rw [one_smul, appendR_one] at h
  exact h.symm

variable (hsym : KLRSymm Q)

/-- The shuffle coordinates adapted to the last strand. -/
noncomputable abbrev lastDecompOf :
    Ind Q ν (ν₀' + Si i) N ≃ₗ[k] (Shuffle (Seq.card_add' ν (ν₀' + Si i)) → N) :=
  indDecompOf lastWord hsym lastWord_spec N

theorem lastDecompOf_lastIdemOf_smul (y : Ind Q ν (ν₀' + Si i) N)
    (u : Shuffle (Seq.card_add' ν (ν₀' + Si i))) :
    lastDecompOf hsym (lastIdemOf Q ν ν₀' i • y) u =
      ∑ s ∈ concatSet (ν + ν₀') (Si i),
        concatIdem (Q := Q) (u.1 • Seq.cast (add_assoc ν ν₀' (Si i)) s) •
          lastDecompOf hsym y u := by
  rw [lastIdemOf_eq, Finset.sum_smul, map_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun s _ => indDecompOf_e_smul _ hsym _ N _ y u

omit [Module (TensorKLR Q ν (ν₀' + ({i} : Multiset I))) N]
  [IsScalarTower k (TensorKLR Q ν (ν₀' + ({i} : Multiset I))) N] in
/-- A shuffle moving the last strand places it in the first block. -/
theorem concatIdem_smul_cast_eq_zero (hi : i ∉ ν) (u : Shuffle (Seq.card_add' ν (ν₀' + Si i)))
    (hu : u.1 (lastPos (card_add_singleton_eq (i := i))) ≠
      lastPos (card_add_singleton_eq (i := i)))
    {s : Seq (ν + ν₀' + Si i)} (hs : s ∈ concatSet (ν + ν₀') (Si i)) :
    concatIdem (Q := Q) (u.1 • Seq.cast (add_assoc ν ν₀' (Si i)) s) = 0 := by
  refine concatIdem_of_not_mem fun hm => hi ?_
  obtain ⟨a, b, hab⟩ := mem_concatSet.1 hm
  set p := u.1 (lastPos (card_add_singleton_eq (i := i))) with hp
  have hpν : p.val < Multiset.card ν := by
    rcases IsShuffle.val_last (Seq.card_add' ν (ν₀' + Si i)) (card_add_singleton_eq (i := i))
      u.2 with h | h
    · omega
    · exact absurd (Fin.ext h) hu
  have hlbl : (u.1 • Seq.cast (add_assoc ν ν₀' (Si i)) s).1 p = i := by
    rw [Seq.smul_apply, hp, Equiv.symm_apply_apply]
    exact cast_last_of_mem' hs _ (by simp)
  rw [← hab, Seq.append_apply_lt _ _ _ hpν] at hlbl
  exact hlbl ▸ a.mem _

/-- At a shuffle fixing the last strand, the coordinates of `E(Ind_{ν,ν'} N)` lie in `₂N`. -/
theorem tensorAppendR_smul_lastDecompOf_ext {y : Ind Q ν (ν₀' + Si i) N}
    (hy : lastIdemOf Q ν ν₀' i • y = y) (v : Shuffle (Seq.card_add' ν ν₀')) :
    tensorAppendR Q ν ν₀' i 1 • lastDecompOf hsym y
        (extShuffle (Seq.card_add' ν (ν₀' + Si i)) (card_add_singleton_eq (i := i))
          (Seq.card_add' ν ν₀') v) =
      lastDecompOf hsym y (extShuffle (Seq.card_add' ν (ν₀' + Si i))
        (card_add_singleton_eq (i := i)) (Seq.card_add' ν ν₀') v) := by
  have h := lastDecompOf_lastIdemOf_smul hsym y (extShuffle (Seq.card_add' ν (ν₀' + Si i))
    (card_add_singleton_eq (i := i)) (Seq.card_add' ν ν₀') v)
  rw [hy] at h
  rw [h, Finset.smul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [smul_smul, tensorAppendR_one_mul_concatIdem]
  rw [Seq.smul_apply]
  have hl : (extShuffle (Seq.card_add' ν (ν₀' + Si i)) (card_add_singleton_eq (i := i))
      (Seq.card_add' ν ν₀') v).1.symm
      (lastPos (card_add_singleton_eq (i := i))) = lastPos (card_add_singleton_eq (i := i)) := by
    rw [Equiv.symm_apply_eq]
    exact (extPerm_last _ v.1).symm
  rw [show (⟨Multiset.card ν + Multiset.card ν₀', by simp⟩ :
      Fin (Multiset.card (ν + (ν₀' + Si i)))) = lastPos (card_add_singleton_eq (i := i)) from
    Fin.ext (by simp), hl]
  exact cast_last_of_mem' hs _ (by simp)

include hsym in
/-- **`E(Ind_{ν,ν'} N)` is the image of `Φ` when `i ∉ ν`.** -/
theorem mem_range_indAppend_of_lastIdemOf_smul (hi : i ∉ ν) {y : Ind Q ν (ν₀' + Si i) N}
    (hy : lastIdemOf Q ν ν₀' i • y = y) : y ∈ LinearMap.range (indAppend (Q := Q) (N := N)) := by
  have hzero : ∀ u : Shuffle (Seq.card_add' ν (ν₀' + Si i)),
      u.1 (lastPos (card_add_singleton_eq (i := i))) ≠ lastPos (card_add_singleton_eq (i := i)) →
        lastDecompOf hsym y u = 0 := fun u hu => by
    rw [← hy, lastDecompOf_lastIdemOf_smul]
    exact Finset.sum_eq_zero fun s hs => by
      rw [concatIdem_smul_cast_eq_zero hi u hu hs, zero_smul]
  refine ⟨∑ v, BalancedTensor.tmul (hatWRevSub (k := k) (Q := Q) v)
    (InductionAlong.Res.mk (lastDecompOf hsym y (extShuffle (Seq.card_add' ν (ν₀' + Si i))
      (card_add_singleton_eq (i := i)) (Seq.card_add' ν ν₀') v))
      (tensorAppendR_smul_lastDecompOf_ext hsym hy v)), ?_⟩
  rw [map_sum]
  simp_rw [indAppend_tmul_hatWRevSub]
  conv_rhs => rw [← (lastDecompOf hsym).symm_apply_apply y, indDecompOf_symm_apply]
  symm
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ⟨_, extShuffle_injective
    (Seq.card_add' ν (ν₀' + Si i)) (card_add_singleton_eq (i := i)) (Seq.card_add' ν ν₀')⟩))
    (fun u _ hu => ?_), Finset.sum_map]
  · rfl
  · have hne : u.1 (lastPos (card_add_singleton_eq (i := i))) ≠
        lastPos (card_add_singleton_eq (i := i)) := fun he => hu (by
      obtain ⟨v, rfl⟩ := exists_extShuffle_eq (Seq.card_add' ν (ν₀' + Si i))
        (card_add_singleton_eq (i := i)) (Seq.card_add' ν ν₀') he
      exact Finset.mem_map_of_mem _ (Finset.mem_univ v))
    rw [hzero u hne, BalancedTensor.tmul_zero]

end LastIdemOf

end KLRAlgebra

end Categorification.KLR

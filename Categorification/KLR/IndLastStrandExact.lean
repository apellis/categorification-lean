/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.IndLastStrandBij
import Categorification.KLR.Crystal.Delta

/-!
# The last strand of an induced module: the short exact sequence

Khovanov–Lauda I (arXiv:0803.4121v2), Proposition 2.18, in the case where one strand coloured
`i` is restricted off the right of `Ind_{ν,ν'} N`, `ν = ν₀ + i`, `ν' = ν₀' + i`; the KLR input
of B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5.

Write `1_{-,i} = ι(1_{ν+ν₀'} ⊗ 1_i)` for the idempotent of `R(ν + ν')` cutting out the
restriction of the last strand, and `E(Ind_{ν,ν'} N) = 1_{-,i} Ind_{ν,ν'} N`. The maps
`Φ : Ind_{ν,ν₀'} ₂N → Ind_{ν,ν'} N` and `Ψ : Ind_{ν₀,ν'} ₁N → Ind_{ν,ν'} N / Φ(Ind_{ν,ν₀'} ₂N)`
give the exact sequence
`0 → Ind_{ν,ν₀'} ₂N → E(Ind_{ν,ν'} N) → Ind_{ν₀,ν'} ₁N → 0`:

* `Φ` is injective (`indAppend_injective`) and lands in `E(Ind_{ν,ν'} N)`
  (`lastIdem_smul_indAppend`);
* `Ψ` is injective (`indLast_injective`);
* the image of `Ψ` is the image of `E(Ind_{ν,ν'} N)` in the quotient
  (`exists_lastIdem_smul_indLast_eq`, `exists_indLast_eq`).

The coordinates of `1_{-,i} y` in the shuffle basis adapted to the last strand are controlled by
`concatIdem`: at a shuffle fixing the last strand they are fixed by `1 ⊗ 1_{ν₀',i}`, at a shuffle
moving the last strand of `ν` to the end they are fixed by `1_{ν₀,i} ⊗ 1`.
-/

namespace Categorification.KLR

open Equiv MvPolynomial TypeA MulOpposite
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}

local notation "Si" i:max => (Singleton.singleton i : Multiset I)

namespace KLRAlgebra

/-! ### Sequences ending in `i` -/

section Sequences

variable {i : I}

theorem mem_concatSet_singleton_iff {μ : Multiset I} {s : Seq (μ + Si i)} :
    s ∈ concatSet μ (Si i) ↔ s.1 ⟨Multiset.card μ, by simp⟩ = i := by
  rw [mem_concatSet_iff_hasTail (ν' := Si i) (i := i) (by simp)]
  constructor
  · rintro ⟨-, h⟩
    exact h _ (by simp)
  · intro h
    refine ⟨by simp, fun a ha => ?_⟩
    have hlt := a.2
    simp only [Multiset.card_add, Multiset.card_singleton] at ha hlt
    rw [show a = ⟨Multiset.card μ, by simp⟩ from Fin.ext (by simp only; omega)]
    exact h

variable {ν₀ ν₀' : Multiset I}

/-- `(1_{ν₀,i} ⊗ 1) 1_t = 1_t` when the last strand of the first block of `t` is coloured `i`. -/
theorem tensorAppendL_one_mul_concatIdem {ν' : Multiset I} (t : Seq (ν₀ + Si i + ν'))
    (ht : t.1 ⟨Multiset.card ν₀, by simp; omega⟩ = i) :
    tensorAppendL Q ν₀ ν' i 1 * concatIdem t = concatIdem t := by
  by_cases hm : t ∈ concatSet (ν₀ + Si i) ν'
  · obtain ⟨a, b, rfl⟩ := mem_concatSet.1 hm
    rw [concatIdem_append, tensorAppendL_one, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      oneConcat, eSum_mul_e, ite_eq_left]
    rw [mem_concatSet_singleton_iff]
    rw [Seq.append_apply_lt _ _ _ (by simp)] at ht
    exact ht
  · rw [concatIdem_of_not_mem hm, mul_zero]

/-- `(1 ⊗ 1_{ν₀',i}) 1_t = 1_t` when the last strand of `t` is coloured `i`. -/
theorem tensorAppendR_one_mul_concatIdem {ν : Multiset I} (t : Seq (ν + (ν₀' + Si i)))
    (ht : t.1 ⟨Multiset.card ν + Multiset.card ν₀', by simp⟩ = i) :
    tensorAppendR Q ν ν₀' i 1 * concatIdem t = concatIdem t := by
  by_cases hm : t ∈ concatSet ν (ν₀' + Si i)
  · obtain ⟨a, b, rfl⟩ := mem_concatSet.1 hm
    rw [concatIdem_append, tensorAppendR_one, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      oneConcat, eSum_mul_e, ite_eq_left]
    rw [mem_concatSet_singleton_iff]
    rw [Seq.append_apply_ge _ _ _ (by simp)] at ht
    exact (Seq.apply_congr _ (by simp)).trans ht
  · rw [concatIdem_of_not_mem hm, mul_zero]

end Sequences

/-! ### The idempotent `1_{-,i}` -/

section LastIdem

variable (Q) (ν₀ ν₀' : Multiset I) (i : I)

/-- The idempotent `1_{-,i} = ι(1_{ν+ν₀'} ⊗ 1_i)` of `R(ν + ν')`, `ν = ν₀ + i`, `ν' = ν₀' + i`. -/
noncomputable def lastIdem : KLRAlgebra k Q (ν₀ + Si i + (ν₀' + Si i)) :=
  castKLR Q (add_assoc (ν₀ + Si i) ν₀' (Si i)) (oneConcat Q (ν₀ + Si i + ν₀') (Si i))

theorem lastIdem_eq :
    lastIdem Q ν₀ ν₀' i = ∑ s ∈ concatSet (ν₀ + Si i + ν₀') (Si i),
      (e (Seq.cast (add_assoc (ν₀ + Si i) ν₀' (Si i)) s) :
        KLRAlgebra k Q (ν₀ + Si i + (ν₀' + Si i))) := by
  rw [lastIdem, oneConcat, eSum, map_sum]
  exact Finset.sum_congr rfl fun s _ => castKLR_e _ s

variable {Q ν₀ ν₀' i}

theorem lastIdem_mul_lastBimod (r : IndBimod Q ν₀ (ν₀' + Si i)) :
    lastIdem Q ν₀ ν₀' i * (lastBimod Q ν₀ ν₀' i r : KLRAlgebra k Q (ν₀ + Si i + (ν₀' + Si i))) =
      (lastBimod Q ν₀ ν₀' i r : KLRAlgebra k Q (ν₀ + Si i + (ν₀' + Si i))) := by
  rw [lastBimod_apply, coe_lastElt, lastIdem, ← mul_assoc, ← map_mul, ← appendR_one, ← mul_assoc,
    ← map_mul, one_mul]

variable {N : Type*} [AddCommGroup N] [Module k N]
  [Module (TensorKLR Q (ν₀ + ({i} : Multiset I)) (ν₀' + ({i} : Multiset I))) N]
  [IsScalarTower k (TensorKLR Q (ν₀ + ({i} : Multiset I)) (ν₀' + ({i} : Multiset I))) N]

/-- **`Φ` lands in `E(Ind_{ν,ν'} N)`.** -/
theorem lastIdem_smul_indAppend
    (z : Ind Q (ν₀ + Si i) ν₀' (ResRight Q (ν₀ + Si i) ν₀' i N)) :
    lastIdem Q ν₀ ν₀' i • indAppend z = indAppend z := by
  have h := indAppend_smul (Q := Q) (N := N) (1 : KLRAlgebra k Q (ν₀ + Si i + ν₀')) z
  rw [one_smul, appendR_one] at h
  exact h.symm

/-- **The image of `Ψ` lies in the image of `E(Ind_{ν,ν'} N)`.** -/
theorem exists_lastIdem_smul_indLast_eq (x : Ind Q ν₀ (ν₀' + Si i) (ResAppendL Q ν₀ ν₀' i N)) :
    ∃ y : Ind Q (ν₀ + Si i) (ν₀' + Si i) N,
      lastIdem Q ν₀ ν₀' i • y = y ∧ indLast x = Submodule.Quotient.mk y := by
  induction x using BalancedTensor.induction_on with
  | zero => exact ⟨0, smul_zero _, by rw [map_zero, Submodule.Quotient.mk_zero]⟩
  | tmul r n =>
    refine ⟨BalancedTensor.tmul (lastBimod Q ν₀ ν₀' i r) n.val, ?_, indLast_tmul r n⟩
    rw [BalancedTensor.smul_tmul']
    congr 1
    exact Subtype.ext (lastIdem_mul_lastBimod r)
  | add x x' hx hx' =>
    obtain ⟨y, hy, hxy⟩ := hx
    obtain ⟨y', hy', hxy'⟩ := hx'
    exact ⟨y + y', by rw [smul_add, hy, hy'], by rw [map_add, hxy, hxy',
      Submodule.Quotient.mk_add]⟩

end LastIdem

/-! ### Coordinates of `E(Ind_{ν,ν'} N)` -/

section Coordinates

variable {ν₀ ν₀' : Multiset I} {i : I}
variable {N : Type*} [AddCommGroup N] [Module k N]
  [Module (TensorKLR Q (ν₀ + ({i} : Multiset I)) (ν₀' + ({i} : Multiset I))) N]
  [IsScalarTower k (TensorKLR Q (ν₀ + ({i} : Multiset I)) (ν₀' + ({i} : Multiset I))) N]
variable (hsym : KLRSymm Q)

/-- The shuffle coordinates adapted to the last strand. -/
noncomputable abbrev lastDecomp :
    Ind Q (ν₀ + Si i) (ν₀' + Si i) N ≃ₗ[k]
      (Shuffle (Seq.card_add' (ν₀ + Si i) (ν₀' + Si i)) → N) :=
  indDecompOf (lastStrandWord ν₀ ν₀' i) hsym (lastStrandWord_spec ν₀ ν₀' i) N

theorem lastDecomp_lastIdem_smul (y : Ind Q (ν₀ + Si i) (ν₀' + Si i) N)
    (u : Shuffle (Seq.card_add' (ν₀ + Si i) (ν₀' + Si i))) :
    lastDecomp hsym (lastIdem Q ν₀ ν₀' i • y) u =
      ∑ s ∈ concatSet (ν₀ + Si i + ν₀') (Si i),
        concatIdem (Q := Q) (u.1 • Seq.cast (add_assoc (ν₀ + Si i) ν₀' (Si i)) s) •
          lastDecomp hsym y u := by
  rw [lastIdem_eq, Finset.sum_smul, map_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun s _ => indDecompOf_e_smul _ hsym _ N _ y u

/-- If every summand `1_{u s}` of the coordinate action of `1_{-,i}` at `u` is absorbed by `T`,
then `T` fixes the coordinate at `u` of every element of `E(Ind_{ν,ν'} N)`. -/
theorem smul_lastDecomp_of_lastIdem_smul (T : TensorKLR Q (ν₀ + Si i) (ν₀' + Si i))
    {y : Ind Q (ν₀ + Si i) (ν₀' + Si i) N} (hy : lastIdem Q ν₀ ν₀' i • y = y)
    (u : Shuffle (Seq.card_add' (ν₀ + Si i) (ν₀' + Si i)))
    (hT : ∀ s ∈ concatSet (ν₀ + Si i + ν₀') (Si i),
      T * concatIdem (Q := Q) (u.1 • Seq.cast (add_assoc (ν₀ + Si i) ν₀' (Si i)) s) =
        concatIdem (u.1 • Seq.cast (add_assoc (ν₀ + Si i) ν₀' (Si i)) s)) :
    T • lastDecomp hsym y u = lastDecomp hsym y u := by
  have h := lastDecomp_lastIdem_smul hsym y u
  rw [hy] at h
  rw [h, Finset.smul_sum]
  exact Finset.sum_congr rfl fun s hs => by rw [smul_smul, hT s hs]

theorem cast_last_of_mem {s : Seq (ν₀ + Si i + ν₀' + Si i)}
    (hs : s ∈ concatSet (ν₀ + Si i + ν₀') (Si i))
    (p : Fin (Multiset.card (ν₀ + Si i + (ν₀' + Si i))))
    (hp : p.val = Multiset.card (ν₀ + Si i + ν₀')) :
    (Seq.cast (add_assoc (ν₀ + Si i) ν₀' (Si i)) s).1 p = i := by
  rw [Seq.cast_apply]
  exact (Seq.apply_congr _ (by simp [hp])).trans (mem_concatSet_singleton_iff.1 hs)

/-- At a shuffle fixing the last strand, the coordinates of `E(Ind_{ν,ν'} N)` lie in `₂N`. -/
theorem tensorAppendR_smul_lastDecomp_ext {y : Ind Q (ν₀ + Si i) (ν₀' + Si i) N}
    (hy : lastIdem Q ν₀ ν₀' i • y = y) (v : Shuffle (Seq.card_add' (ν₀ + Si i) ν₀')) :
    tensorAppendR Q (ν₀ + Si i) ν₀' i 1 •
        lastDecomp hsym y (lastShuffles ν₀ ν₀' i (Sum.inl v)) =
      lastDecomp hsym y (lastShuffles ν₀ ν₀' i (Sum.inl v)) := by
  refine smul_lastDecomp_of_lastIdem_smul hsym _ hy _ fun s hs =>
    tensorAppendR_one_mul_concatIdem _ ?_
  rw [Seq.smul_apply]
  have hl : (lastShuffles ν₀ ν₀' i (Sum.inl v)).1.symm
      (lastPos (card_add_singleton_eq (ν := ν₀ + Si i) (ν₀' := ν₀') (i := i))) =
      lastPos (card_add_singleton_eq (ν := ν₀ + Si i) (ν₀' := ν₀') (i := i)) := by
    rw [Equiv.symm_apply_eq]
    exact (extPerm_last _ v.1).symm
  rw [show (⟨Multiset.card (ν₀ + Si i) + Multiset.card ν₀', by simp⟩ :
      Fin (Multiset.card (ν₀ + Si i + (ν₀' + Si i)))) =
      lastPos (card_add_singleton_eq (ν := ν₀ + Si i) (ν₀' := ν₀') (i := i)) from
    Fin.ext (by simp), hl]
  exact cast_last_of_mem hs _ (by simp)

/-- At a shuffle moving the last strand of `ν` to the end, the coordinates of
`E(Ind_{ν,ν'} N)` lie in `₁N`. -/
theorem tensorAppendL_smul_lastDecomp_top {y : Ind Q (ν₀ + Si i) (ν₀' + Si i) N}
    (hy : lastIdem Q ν₀ ν₀' i • y = y) (v : Shuffle (lastTop_card ν₀ ν₀' i)) :
    tensorAppendL Q ν₀ (ν₀' + Si i) i 1 •
        lastDecomp hsym y (lastShuffles ν₀ ν₀' i (Sum.inr v)) =
      lastDecomp hsym y (lastShuffles ν₀ ν₀' i (Sum.inr v)) := by
  refine smul_lastDecomp_of_lastIdem_smul hsym _ hy _ fun s hs =>
    tensorAppendL_one_mul_concatIdem _ ?_
  rw [Seq.smul_apply]
  have hl : (lastShuffles ν₀ ν₀' i (Sum.inr v)).1.symm ⟨Multiset.card ν₀, by simp; omega⟩ =
      lastPos (card_add_singleton_eq (ν := ν₀ + Si i) (ν₀' := ν₀') (i := i)) := by
    rw [Equiv.symm_apply_eq]
    exact (topShuffle_last _ _ _ (lastPerm_spec ν₀ ν₀' i).1 (lastPerm_spec ν₀ ν₀' i).2 v).symm
  rw [hl]
  exact cast_last_of_mem hs _ (by simp)

/-- The shuffles of `(ν, ν')`, sorted by the block of their last strand, with the second
block indexed by the shuffles of `(ν₀, ν')`. -/
noncomputable def lastShuffles' :
    Shuffle (Seq.card_add' (ν₀ + Si i) ν₀') ⊕ Shuffle (Seq.card_add' ν₀ (ν₀' + Si i)) ≃
      Shuffle (Seq.card_add' (ν₀ + Si i) (ν₀' + Si i)) :=
  (Equiv.sumCongr (Equiv.refl _)
    (shuffleCongr (Seq.card_add' ν₀ (ν₀' + Si i)) (lastTop_card ν₀ ν₀' i))).trans
    (lastShuffles ν₀ ν₀' i)

include hsym in
/-- **`Ψ` is onto `E(Ind_{ν,ν'} N)` modulo the image of `Φ`.** -/
theorem exists_indLast_eq {y : Ind Q (ν₀ + Si i) (ν₀' + Si i) N}
    (hy : lastIdem Q ν₀ ν₀' i • y = y) :
    ∃ x : Ind Q ν₀ (ν₀' + Si i) (ResAppendL Q ν₀ ν₀' i N),
      indLast x = Submodule.Quotient.mk y := by
  have hyg : y = (lastDecomp hsym).symm (lastDecomp hsym y) :=
    ((lastDecomp hsym).symm_apply_apply y).symm
  rw [indDecompOf_symm_apply, ← (lastShuffles' (ν₀ := ν₀) (ν₀' := ν₀') (i := i)).sum_comp,
    Fintype.sum_sum_type] at hyg
  let zA : Ind Q (ν₀ + Si i) ν₀' (ResRight Q (ν₀ + Si i) ν₀' i N) :=
    ∑ v, BalancedTensor.tmul (hatWRevSub (k := k) (Q := Q) v)
      (InductionAlong.Res.mk (lastDecomp hsym y (lastShuffles ν₀ ν₀' i (Sum.inl v)))
        (tensorAppendR_smul_lastDecomp_ext hsym hy v))
  have hA : indAppend zA = ∑ v, BalancedTensor.tmul (hatWRevSubOf (lastStrandWord ν₀ ν₀' i)
      (lastShuffles' (Sum.inl v)))
      (lastDecomp hsym y (lastShuffles' (Sum.inl v))) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [indAppend_tmul_hatWRevSubOf _ (lastStrandWord_ext ν₀ ν₀' i)]
    rfl
  refine ⟨∑ v₀, BalancedTensor.tmul (hatWRevSub (k := k) (Q := Q) v₀)
    (InductionAlong.Res.mk (lastDecomp hsym y (lastShuffles ν₀ ν₀' i (Sum.inr
      (shuffleCongr (Seq.card_add' ν₀ (ν₀' + Si i)) (lastTop_card ν₀ ν₀' i) v₀))))
      (tensorAppendL_smul_lastDecomp_top hsym hy _)), ?_⟩
  rw [map_sum]
  simp_rw [indLast_tmul_hatWRevSub]
  conv_rhs => rw [hyg, ← hA, Submodule.Quotient.mk_add,
    (Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self _ zA), zero_add,
    ← Submodule.mkQ_apply, map_sum]
  rfl

omit [DecidableEq I] in
theorem lastShuffles'_inr_last (w : Shuffle (Seq.card_add' ν₀ (ν₀' + Si i))) :
    ((lastShuffles' (ν₀ := ν₀) (ν₀' := ν₀') (i := i) (Sum.inr w)).1
        (lastPos (card_add_singleton_eq (ν := ν₀ + Si i) (ν₀' := ν₀') (i := i)))).val =
      Multiset.card ν₀ :=
  congrArg Fin.val (topShuffle_last _ _ _ (lastPerm_spec ν₀ ν₀' i).1 (lastPerm_spec ν₀ ν₀' i).2 _)

include hsym in
/-- **`Ψ` is injective.** -/
theorem indLast_injective :
    Function.Injective (indLast (Q := Q) (ν₀ := ν₀) (ν₀' := ν₀') (i := i) (N := N)) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  set g := indDecomp hsym (ResAppendL Q ν₀ ν₀' i N) x with hg
  have hxg : x = (indDecomp hsym (ResAppendL Q ν₀ ν₀' i N)).symm g :=
    ((indDecomp hsym _).symm_apply_apply x).symm
  rw [indDecomp_symm_apply] at hxg
  rw [hxg, map_sum] at hx
  simp_rw [indLast_tmul_hatWRevSub] at hx
  simp_rw [← Submodule.mkQ_apply] at hx
  rw [← map_sum, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx
  obtain ⟨z, hz⟩ := hx
  suffices g = 0 by rw [hxg, this]; simp
  funext w
  apply InductionAlong.Res.ext
  have h := congrArg (fun y => lastDecomp hsym y (lastShuffles' (Sum.inr w))) hz
  rw [indDecompOf_indAppend_top (lastStrandWord ν₀ ν₀' i) (lastStrandWord_spec ν₀ ν₀' i)
    (lastStrandWord_ext ν₀ ν₀' i) hsym z _ (fun he => by
      have := congrArg Fin.val he
      rw [lastShuffles'_inr_last] at this
      simp at this; omega), map_sum, Finset.sum_apply] at h
  rw [Finset.sum_eq_single w] at h
  · change _ = (lastDecomp hsym (BalancedTensor.tmul _ _)) (lastShuffles' (Sum.inr w)) at h
    rw [indDecompOf_tmul_hatWRevSubOf] at h
    · exact (h.trans (Pi.single_eq_same _ _)).symm
  · intro w' _ hw'
    change (lastDecomp hsym (BalancedTensor.tmul _ _)) (lastShuffles' (Sum.inr w)) = 0
    rw [indDecompOf_tmul_hatWRevSubOf]
    exact Pi.single_eq_of_ne (fun he => hw' (Sum.inr_injective
      ((lastShuffles' (ν₀ := ν₀) (ν₀' := ν₀') (i := i)).injective he)).symm) _
  · simp

end Coordinates

end KLRAlgebra

end Categorification.KLR

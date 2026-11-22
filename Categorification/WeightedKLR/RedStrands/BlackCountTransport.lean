/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.ConcatAssoc
import Categorification.KLR.Reindex
import Categorification.WeightedKLR.RedStrands.StandardBlocks

/-!
# Black counts of transported and concatenated loadings

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §5.1. The
preorder of Definition 5.1 compares the numbers `blackCount s r i` of black `i`-strands left of
the red strand `λ_r`. The comparison of the iterated two-piece standard modules of
Proposition 5.20 with the standard modules of Definition 5.1 computes these numbers for
loadings built by recolouring and concatenation; this file collects those computations.

## Main results

* `blackCount_cast`, `blackCount_map`: black counts are unchanged by transport along an
  equality of weights and by an injective recolouring of the red strands.
* `blackCount_append_left`, `blackCount_append_right`: black counts of a concatenation `cd`,
  for a red strand of `c` and for a red strand of `d`.
* `sum_blackCount_add_le`: in a red-ordered loading, the black strands left of the last red
  strand and the other red strands all lie before it.
-/

namespace Categorification.Stendhal

open KLR TypeA

variable {I : Type*} [DecidableEq I] {ℓ : ℕ}

theorem blackCount_cast {μ μ' : Multiset (I ⊕ Fin ℓ)} (h : μ = μ') (s : Seq μ) (r : Fin ℓ)
    (i : I) : blackCount (Seq.cast h s) r i = blackCount s r i := by
  subst h
  rfl

/-- Recolouring the red strands along an injection does not change the black counts. -/
theorem blackCount_map {ℓ' : ℕ} {g : Fin ℓ → Fin ℓ'} (hg : Function.Injective g)
    {ν : Multiset (I ⊕ Fin ℓ)} (s : Seq ν) (r : Fin ℓ) (i : I) :
    blackCount (Seq.map (Sum.map id g) s) (g r) i = blackCount s r i := by
  have hc := Multiset.card_map (Sum.map id g) ν
  symm
  refine Finset.card_equiv (finCongr hc.symm) fun a => ?_
  have hl : ∀ (x : I ⊕ Fin ℓ) (j : I), Sum.map id g x = .inl j ↔ x = .inl j := by
    intro x j; cases x <;> simp
  have hr : ∀ x : I ⊕ Fin ℓ, Sum.map id g x = .inr (g r) ↔ x = .inr r := by
    intro x; cases x <;> simp [hg.eq_iff]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Seq.map_lbl, hl, hr,
    finCongr_apply]
  have hca : Fin.cast hc (Fin.cast hc.symm a) = a := Fin.ext rfl
  rw [hca]
  refine and_congr_right fun _ => ⟨fun h b hb => ?_, fun h b hb => ?_⟩
  · have := h (Fin.cast hc b) hb
    rw [Fin.lt_def] at this ⊢
    simpa using this
  · have := h (Fin.cast hc.symm b) (by rwa [show Fin.cast hc (Fin.cast hc.symm b) = b from
      Fin.ext rfl])
    rw [Fin.lt_def] at this ⊢
    simpa using this

section Append

variable {ν ν' : Multiset (I ⊕ Fin ℓ)}

omit [DecidableEq I] in
theorem Seq.forall_pos {p : Fin (Multiset.card (ν + ν')) → Prop} :
    (∀ b, p b) ↔ (∀ x, p (Seq.posL ν' x)) ∧ ∀ y, p (Seq.posR ν y) := by
  refine ⟨fun h => ⟨fun x => h _, fun y => h _⟩, fun h b => ?_⟩
  obtain ⟨b | b, rfl⟩ := (blockEquiv (Seq.card_add' ν ν')).surjective b
  exacts [h.1 b, h.2 b]

omit [DecidableEq I] in
theorem Seq.sum_pos {M : Type*} [AddCommMonoid M] (f : Fin (Multiset.card (ν + ν')) → M) :
    ∑ b, f b = ∑ x, f (Seq.posL ν' x) + ∑ y, f (Seq.posR ν y) := by
  rw [← Equiv.sum_comp (blockEquiv (Seq.card_add' ν ν')), Fintype.sum_sum_type]
  rfl

omit [DecidableEq I] in
theorem Seq.posL_lt_posL {x x' : Fin (Multiset.card ν)} :
    Seq.posL ν' x < Seq.posL ν' x' ↔ x < x' := by
  rw [Fin.lt_def, Fin.lt_def, Seq.posL_val, Seq.posL_val]

omit [DecidableEq I] in
theorem Seq.posR_lt_posR {y y' : Fin (Multiset.card ν')} :
    Seq.posR ν y < Seq.posR ν y' ↔ y < y' := by
  rw [Fin.lt_def, Fin.lt_def, Seq.posR_val, Seq.posR_val]
  omega

omit [DecidableEq I] in
theorem Seq.posL_lt_posR (x : Fin (Multiset.card ν)) (y : Fin (Multiset.card ν')) :
    Seq.posL ν' x < Seq.posR ν y := by
  simp only [Fin.lt_def, Seq.posL_val, Seq.posR_val]
  omega

omit [DecidableEq I] in
theorem Seq.not_posR_lt_posL (x : Fin (Multiset.card ν)) (y : Fin (Multiset.card ν')) :
    ¬ Seq.posR ν y < Seq.posL ν' x := by
  simp only [Fin.lt_def, Seq.posL_val, Seq.posR_val, not_lt]
  omega

/-- The black count of `cd` for a red strand of `c` absent from `d` is that of `c`. -/
theorem blackCount_append_left (c : Seq ν) (d : Seq ν') {r : Fin ℓ}
    (hc : ∃ x, c.lbl x = .inr r) (hd : ∀ y, d.lbl y ≠ .inr r) (i : I) :
    blackCount (c.append d) r i = blackCount c r i := by
  obtain ⟨x₀, hx₀⟩ := hc
  rw [blackCount, blackCount, Finset.card_filter, Finset.card_filter, Seq.sum_pos]
  have h2 : ∀ y, ¬ ((c.append d).lbl (Seq.posR ν y) = .inl i ∧
      ∀ b, (c.append d).lbl b = .inr r → Seq.posR ν y < b) := fun y h =>
    Seq.not_posR_lt_posL x₀ y (h.2 _ (by simpa using hx₀))
  simp only [h2, ite_false, Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  simp only [Seq.forall_pos, Seq.lbl, Seq.append_posL, Seq.append_posR, Seq.posL_lt_posL]
  exact propext (and_congr_right fun _ =>
    ⟨fun h b hb => h.1 b hb, fun h => ⟨h, fun y hy => absurd hy (hd y)⟩⟩)

/-- The black count of `cd` for a red strand of `d` absent from `c`: all black `i`-strands of
`c`, and those of `d` left of it. -/
theorem blackCount_append_right (c : Seq ν) (d : Seq ν') {r : Fin ℓ}
    (hc : ∀ x, c.lbl x ≠ .inr r) (hd : ∃ y, d.lbl y = .inr r) (i : I) :
    blackCount (c.append d) r i =
      (Finset.univ.filter fun x => c.lbl x = .inl i).card + blackCount d r i := by
  obtain ⟨y₀, hy₀⟩ := hd
  rw [blackCount, blackCount, Finset.card_filter, Finset.card_filter, Finset.card_filter,
    Seq.sum_pos]
  congr 1
  · refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    simp only [Seq.forall_pos, Seq.lbl, Seq.append_posL, Seq.append_posR]
    exact propext (and_iff_left ⟨fun x' hx' => absurd hx' (hc x'),
      fun y _ => Seq.posL_lt_posR x y⟩)
  · refine Finset.sum_congr rfl fun y _ => ?_
    congr 1
    simp only [Seq.forall_pos, Seq.lbl, Seq.append_posL, Seq.append_posR, Seq.posR_lt_posR]
    exact propext (and_congr_right fun _ =>
      ⟨fun h => h.2, fun h => ⟨fun x' hx' => absurd hx' (hc x'), h⟩⟩)

end Append

section Count

variable {ν : Multiset I}

/-- In a red-ordered loading the black strands of labels in `J` left of the last red strand,
together with the other `ℓ` red strands, lie before the last red strand. -/
theorem sum_blackCount_add_le (s : Seq (stendhalWeight (ℓ + 1) ν)) (hs : IsRedOrdered s)
    (J : Finset I) :
    ∑ i ∈ J, blackCount s (Fin.last ℓ) i + ℓ ≤ (redPos s (Fin.last ℓ)).val := by
  set p := redPos s (Fin.last ℓ) with hp
  let X : Finset (I ⊕ Fin (ℓ + 1)) :=
    (J.map Function.Embedding.inl).disjUnion
      ((Finset.univ : Finset (Fin ℓ)).map (Fin.castSuccEmb.trans Function.Embedding.inr))
      (by
        simp only [Finset.disjoint_left, Finset.mem_map, Function.Embedding.inl_apply,
          Function.Embedding.trans_apply, Fin.castSuccEmb_apply, Function.Embedding.inr_apply]
        rintro _ ⟨i, -, rfl⟩ ⟨r, -, h⟩
        cases h)
  let A := (Finset.Iio p).filter fun a => s.lbl a ∈ X
  have hfib : ∀ x ∈ X, (A.filter fun a => s.lbl a = x).card = countBefore s x p := by
    intro x hx
    rw [countBefore, ← Finset.card_filter]
    congr 1
    ext a
    simp only [A, Finset.mem_filter, Finset.mem_Iio, Finset.mem_univ, true_and, Fin.lt_def]
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2 ▸ hx⟩, h2⟩
  have hA := Finset.card_eq_sum_card_fiberwise (f := s.lbl) (s := A) (t := X)
    (fun a ha => (Finset.mem_filter.1 ha).2)
  rw [Finset.sum_congr rfl hfib, Finset.sum_disjUnion, Finset.sum_map, Finset.sum_map] at hA
  have hred : ∀ r : Fin ℓ, countBefore s (.inr r.castSucc) p = 1 := by
    intro r
    rw [countBefore_inr_redPos hs]
    simp [Fin.val_castSucc, r.2]
  simp only [Function.Embedding.inl_apply, Function.Embedding.trans_apply,
    Fin.castSuccEmb_apply, Function.Embedding.inr_apply, hred, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hA
  have hle : A.card ≤ p.val := (Finset.card_filter_le _ _).trans (Fin.card_Iio p).le
  simp only [blackCount_eq_countBefore, ← hp]
  omega

end Count

end Categorification.Stendhal

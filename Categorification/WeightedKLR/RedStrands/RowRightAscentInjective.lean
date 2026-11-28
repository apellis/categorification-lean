/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.RowBlockAction
import Categorification.WeightedKLR.RedStrands.RowShuffleQuotientCrossing
import Categorification.WeightedKLR.RedStrands.RowShuffleBlocks

/-!
# Right multiplication by an external ascent is injective on a standard column

Webster, arXiv:1309.3796v3, §6.1, proof of Lemma 6.9 (v2: Lemma 6.8). Let `N` be the column of
an aligned row modulo `blockUpperIdeal a b α κ`. If at every quotient coordinate that can be
nonzero at the bottom loading `s_j • s`, the crossing `ψ_j` is an ascent between strands of
different input blocks, then right multiplication by `ψ_j e(s)` is injective on the part of `N`
with bottom `s_j • s`: the coordinate of maximal shuffle length is carried to the extended
shuffle with the same coefficient (`rowColumn_mul_right_ascent_eq_zero`).

For a row of single red strands (a full standard module when `a = b`), a crossing in which a
black strand at the bottom moves left past a red strand going up is such an ascent at every
coordinate, so right multiplication by it is injective (`rowColumn_mul_black_red_eq_zero`).
-/

noncomputable section
namespace Categorification.Stendhal.RedBlock
open KLR KLRAlgebra TypeA BraidedStendhalAlgebra

variable {I : Type} {k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
    (Bs : List (RedBlock I ℓ)) (a b : Fin ℓ) (κ : List (Fin ℓ)) {ν : Multiset I}
local notation "α" => fun r i => boundaryCount (cut a b r) i Bs
local notation "J" => blockUpperIdeal k Q Λ ν a b α κ
local notation "μ" => stendhalWeight ℓ ν
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "P" => projection Q Λ Bs
local notation "π" => AlgHom.comp (RingCon.mkₐ k (TwoSidedIdeal.ringCon J))
  (AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν))

variable (h : weightSum Bs = stendhalWeight ℓ ν) (hal : Aligned a b Bs)
  (hκ : ∀ s : Loadings Bs, redWord (Seq.cast h (place Bs s)) = κ)

include hal hκ in
/-- **Right multiplication by an external ascent is injective on a standard column**
(Webster, arXiv:1309.3796v3, proof of Lemma 6.9). Suppose that at every shuffle index whose
loading projector at the bottom `s₀ = s_j • s` is nonzero in the block quotients, positions `j`
and `j + 1` form an ascent between different input blocks. If `z` lies in the column, has
bottom `s₀`, and `z ψ_j e(s) = 0`, then `z = 0`. -/
theorem rowColumn_mul_right_ascent_eq_zero (hQ : KLRSymm Q) (s : Seq μ) (j : ℕ)
    (hj : j + 1 < (weightSum Bs).card)
    (hasc : ∀ (i : ShuffleIndex Bs) (x : diagrams Q Λ Bs),
      IndexedLoadingProjector Q Λ Bs i (Seq.cast h.symm (sadj (Multiset.card μ) j • s)) x →
      P x ≠ 0 → shufflePerm Bs i ⟨j, by omega⟩ < shufflePerm Bs i ⟨j+1, hj⟩ ∧
        ¬ SameInputBlock Bs i j hj)
    (z : rowColumn Q Λ Bs a b κ h)
    (hz : z.1 * π (e (sadj (Multiset.card μ) j • s)) = z.1)
    (h0 : z.1 * π (ψ j * e s) = 0) : z = 0 := by
  classical
  obtain ⟨n, index, g, w, G, bottom, hG, hw, hfilt, hmul, hbottom, hproj, hunit, hself,
      hother, rebuild⟩ :=
    exists_rowStack_quotient_coordinates_with_indexed_projectors Q Λ Bs a b α κ hQ h
      (violated_of_aligned_shuffleLoading Bs a b κ hal h (fun v _ => hκ v))
  let s₀ := sadj (Multiset.card μ) j • s
  let S := rowStack Q Λ Bs h
  let len : Fin n → ℕ := fun i => (shuffleWord Bs (index i)).length
  have hcard : (weightSum Bs).card = Multiset.card μ := congrArg Multiset.card h
  have hmul' : ∀ i x y, G i (π (S x * y)) = P x * G i (π y) := fun i x y => hmul i x y
  have hbottom' : ∀ i y s, G i (π (y * e s)) = G i (π y) * P (bottom i s) :=
    fun i y s => hbottom i y s
  have hG' : ∀ i y, G i (π y) = P (g i y) := fun i y => hG i y
  by_contra hne
  have hsome : ∃ i, G i z.1 ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (rowColumn_eq_zero_of_quotient_coordinates Q Λ Bs a b κ h hal hκ g w G
      (fun i y => hG i y) hunit rebuild z hall)
  -- the coordinate of maximal shuffle length
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image (Finset.univ.filter fun i => G i z.1 ≠ 0)
    len (by obtain ⟨i, hi⟩ := hsome; exact ⟨i, by simpa using hi⟩)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi₀ hmax
  -- a representative of `z`
  have surj : Function.Surjective (violMk k Q Λ ν) := violMk_surjective
  obtain ⟨v, hv⟩ := z.2
  obtain ⟨y, rfl⟩ := (surj.comp ofKLR_surjective) v
  let Y : R := y * redIdem k Q Λ κ
  have rep : z.1 = π (S 1 * Y) := by
    rw [← hv]
    simp only [Y, map_mul]
    rfl
  -- every coordinate is supported at the bottom `s₀`
  have hsupp (i : Fin n) : G i z.1 = G i z.1 * P (bottom i s₀) := by
    conv_lhs => rw [← hz]
    rw [rep, ← map_mul]
    exact hbottom' i _ s₀
  have hascent (i : Fin n) (hi : G i z.1 ≠ 0) :
      shufflePerm Bs (index i) ⟨j, by omega⟩ < shufflePerm Bs (index i) ⟨j+1, hj⟩ ∧
        ¬ SameInputBlock Bs (index i) j hj := by
    refine hasc (index i) (bottom i s₀) (hproj i s₀) fun hb => hi ?_
    rw [hsupp i, hb, mul_zero]
  -- the extended shuffle at each ascent
  have hext (i : Fin n) (hi : G i z.1 ≠ 0) : ∃ v : Fin n,
      shufflePerm Bs (index v) = shufflePerm Bs (index i) * sadj _ j := by
    obtain ⟨ha, hd⟩ := hascent i hi
    rcases shuffleWord_right_ascent Bs (index i) j hj ha with ⟨v, ⟨hv, _, _⟩, _⟩ | ⟨hs, _⟩
    · exact ⟨index.symm v, by rw [Equiv.apply_symm_apply]; exact hv⟩
    · exact (hd hs).elim
  choose! ext hextv using hext
  have hlen_eq (i : Fin n) : len i = length _ (shufflePerm Bs (index i)) :=
    (isReduced_shuffleWord Bs (index i)).2
  have hlen_ext (i : Fin n) (hi : G i z.1 ≠ 0) : len (ext i) = len i + 1 := by
    rw [hlen_eq, hlen_eq, hextv i hi, length_mul_sadj_of_lt hj (hascent i hi).1]
  let d := ext i₀
  have hcoef (i : Fin n) : G i z.1 = P (g i Y) := by rw [rep, hG', hunit]
  -- the coordinate at `d` of `z ψ_j e(s)`
  have hexpand : G d (z.1 * π (ψ j * e s)) =
      ∑ i, G i z.1 * G d (π (w i * ψ j * e s)) := by
    have hr := rebuild Y
    change π (S 1 * Y) = ∑ i, π (S (g i Y) * w i) at hr
    conv_lhs => rw [rep, hr, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← map_mul, mul_assoc, mul_assoc, ← mul_assoc (w i)]
    change G d (π (S (g i Y) * (w i * ψ j * e s))) = _
    rw [hmul', hcoef]
  have hterm (i : Fin n) : G i z.1 * G d (π (w i * ψ j * e s)) =
      if i = i₀ then G i₀ z.1 * P (bottom d s) else 0 := by
    by_cases hi : G i z.1 = 0
    · rw [hi, zero_mul]
      split_ifs with he
      · subst he; exact (hi₀ hi).elim
      · rfl
    have hle := hmax i hi
    rcases Nat.lt_or_ge (len i) (len i₀) with hlt | hge
    · -- a shorter coordinate only reaches shorter shuffles
      have hz0 : G d (π (w i * ψ j * e s)) = 0 := by
        have hfix : G d (π (w i * ψ j * e s)) =
            G d (π (ψw (shuffleWord Bs (index i)) * ψ j * e s)) := by
          rw [hw i, mul_assoc (S 1), mul_assoc (S 1)]
          change G d (π (S 1 * _)) = _
          rw [hmul', map_one, one_mul, mul_assoc]
        have hmem : (ψw (shuffleWord Bs (index i)) * ψ j * e s : R) ∈
            filt k (stendhalQ Q Λ) μ (len i + 1) := by
          have hvalid : ValidWord (Multiset.card μ) (shuffleWord Bs (index i) ++ [j]) := by
            rw [← hcard]
            exact validWord_append.2 ⟨(isReduced_shuffleWord Bs (index i)).1,
              fun x hx => by obtain rfl := List.mem_singleton.1 hx; exact hj⟩
          have := mem_filt (k := k) (Q := stendhalQ Q Λ) hvalid
            (n := len i + 1) (by simp [len]) 1 s
          simpa [ψw_append, ψw_cons, ψw_nil] using this
        have hb := hfilt d _ _ hmem
        rw [blockShuffleFilt_eq_bot Q Λ Bs (index d) (by
          change len i + 1 < len d
          rw [hlen_ext i₀ hi₀]; omega), Submodule.map_bot, Submodule.mem_bot] at hb
        rw [hfix]; exact hb
      have hne : i ≠ i₀ := by rintro rfl; omega
      rw [hz0, mul_zero]
      simp only [hne, ↓reduceIte]
    · have heq : len i = len i₀ := le_antisymm hle hge
      have hr := rowQuotientCoordinate_external_right_ascent Q Λ Bs a b α κ h index w G bottom
        hw hfilt hmul hbottom hself hother i (ext i) d j hj (hascent i hi).1 (hextv i hi) s
        (Or.inr (by change len i - 2 < len d; rw [hlen_ext i₀ hi₀]; omega))
      rw [hr]
      by_cases he : i = i₀
      · subst he; simp only [d, ↓reduceIte]
      · have hd : d ≠ ext i := by
          intro hd
          apply he
          apply index.injective
          apply shufflePerm_injective Bs
          have := (hextv i hi).symm.trans ((congrArg (fun t => shufflePerm Bs (index t))
            hd.symm).trans (hextv i₀ hi₀))
          exact mul_right_cancel this
        simp only [hd, he, ↓reduceIte, mul_zero]
  have hbot : P (bottom d s) = P (bottom i₀ s₀) :=
    congrArg P (IndexedLoadingProjector.eq_after_right_swap Q Λ Bs h (index i₀) (index d) j
      (hextv i₀ hi₀) s (hproj d s) (hproj i₀ s₀))
  have hval : G d (z.1 * π (ψ j * e s)) = G i₀ z.1 := by
    rw [hexpand, Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_ite_eq' Finset.univ i₀]
    simp only [Finset.mem_univ, ↓reduceIte]
    rw [hbot, ← hsupp]
  rw [h0, map_zero] at hval
  exact hi₀ hval.symm

omit [DecidableEq I] in
private theorem cast_lbl_mk {w w' : Multiset (I ⊕ Fin ℓ)} (e : w = w') (t : Seq w) (j : ℕ)
    (h₁ : j < w'.card) (h₂ : j < w.card) : (Seq.cast e t).lbl ⟨j, h₁⟩ = t.lbl ⟨j, h₂⟩ := by
  subst e; rfl

omit [DecidableEq I] in
private theorem cast_cast_symm {w w' : Multiset (I ⊕ Fin ℓ)} (e : w = w') (t : Seq w') :
    Seq.cast e (Seq.cast e.symm t) = t := by
  subst e; rfl

include hal hκ in
/-- **A black strand moving left past a red strand gives an injective right multiplication on
a full standard column** (Webster, arXiv:1309.3796v3, proof of Lemma 6.9). For a row of single
red strands, if the bottom `s_j • s` has red order `κ`, a black strand at position `j` and a red
strand at position `j + 1`, then `z ψ_j e(s) = 0` forces `z = 0` for `z` in the column with
bottom `s_j • s`. -/
theorem rowColumn_mul_black_red_eq_zero (hQ : KLRSymm Q) (hsize : ∀ B ∈ Bs, B.size = 1)
    (s : Seq μ) (j : ℕ) (hj : j + 1 < (weightSum Bs).card)
    (hord : redWord (sadj (Multiset.card μ) j • s) = κ) {i : I} {r : Fin ℓ}
    (hb : (sadj (Multiset.card μ) j • s).lbl ⟨j, by have := congrArg Multiset.card h; omega⟩ =
      .inl i)
    (hr : (sadj (Multiset.card μ) j • s).lbl ⟨j + 1, by have := congrArg Multiset.card h; omega⟩ =
      .inr r)
    (z : rowColumn Q Λ Bs a b κ h)
    (hz : z.1 * π (e (sadj (Multiset.card μ) j • s)) = z.1)
    (h0 : z.1 * π (ψ j * e s) = 0) : z = 0 := by
  refine rowColumn_mul_right_ascent_eq_zero Q Λ Bs a b κ h hal hκ hQ s j hj ?_ z hz h0
  intro u x hx hPx
  rcases hx.support with rfl | ⟨v, _, hp, rfl⟩
  · exact (hPx (map_zero _)).elim
  have hv : ¬ Violated Bs v := fun hviol => hPx (projection_loadingIdem_eq_zero Q Λ Bs v hviol)
  apply ascent_of_inputBlock_lt
  refine inputBlock_lt_of_black_red Bs hsize h u _ v hv hp ?_ j hj (i := i) (r := r) ?_ ?_
  · rw [cast_cast_symm, hord, hκ v]
  · rw [cast_lbl_mk]; exact hb
  · rw [cast_lbl_mk]; exact hr

end Categorification.Stendhal.RedBlock

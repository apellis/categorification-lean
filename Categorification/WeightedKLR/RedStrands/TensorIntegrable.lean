/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorFinite

/-!
# Vanishing of Webster's tensor product algebra for long strings

Webster, arXiv:1309.3796v2, §5 (the category of finite-dimensional modules over
the algebras `T^λ_ν` for the weights `ν` of an `i`-string is a weak
`sl₂`-categorification in the sense of Chuang–Rouquier, arXiv:math/0407205v2,
§5.1.1). The dot nilpotence of `tensorProjection_dot_nilpotent` holds with
bounds that depend only on the position and on a fixed finite set of black
colours (the quantitative induction of Brundan–Kleshchev, arXiv:0808.2032v3,
Lemma 2.1). A word with boundedly many strands different from `i` then has a
constant block longer than its dot bound, so `T^λ_{n i + β}` is zero for `n`
large. This is the finiteness of the `i`-string through `β`.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR KLRAlgebra MvPolynomial
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ}
    {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin ℓ → I →₀ ℕ)

omit [DecidableEq I] in
private theorem mem_of_lbl_inl {ν : Multiset I} (s : Seq (stendhalWeight ℓ ν))
    (a : Fin (stendhalWeight ℓ ν).card) {j : I} (h : s.lbl a = Sum.inl j) : j ∈ ν := by
  have hm := s.mem a
  change s.lbl a ∈ _ at hm
  rw [h] at hm
  simpa [stendhalWeight] using hm

variable {C : QuantumGroup.CartanDatum I} (hQ : IsRouquierQ C Q)

include hQ in
/-- The annihilating power of each dot of the affine cover in Webster's tensor
product algebra depends only on the dot position once the black colours lie in
a fixed finite set (Webster, arXiv:1309.3796v2, Definitions 4.6–4.7, with the
induction of Brundan–Kleshchev, arXiv:0808.2032v3, Lemma 2.1). -/
theorem exists_uniform_tensor_dot_pow (S : Finset I) :
    ∃ L : ℕ → ℕ, ∀ {ν : Multiset I}, ν.toFinset ⊆ S →
      ∀ p : Fin (stendhalWeight ℓ ν).card,
        affineTensorProjection (Q := Q) Λ ν (x p) ^ L p.val = 0 := by
  classical
  choose c d hc hcd using fun (i j : I) (h : i ≠ j) => hQ.aeval_zero_first i j h
  let D (i j : I) := if h : i ≠ j then d i j h else 0
  let B := S.sup (fun i => S.sup (D i)) + S.sup (fun j => Finset.univ.sup fun r => Λ r j)
  let L (p : ℕ) : ℕ := Nat.rec 1 (fun _ N => max N (N * (N+B))) p
  have hL1 (p : ℕ) : 1 ≤ L p := by
    induction p with
    | zero => exact le_rfl
    | succ p ih => exact ih.trans (le_max_left ..)
  refine ⟨L, ?_⟩
  intro ν hν p
  let T := TensorProductAlgebra k Q Λ ν
  let π := affineTensorProjection (Q := Q) Λ ν
  let _ : Module (KLRAlgebra k (affineCoverQ Q Λ) (stendhalWeight ℓ ν)) T :=
    Module.compHom _ π.toRingHom
  have hpow (b : ℕ) (hb : b < (stendhalWeight ℓ ν).card) (v : T) :
      (pol (X ⟨b, hb⟩ ^ L b) : KLRAlgebra k (affineCoverQ Q Λ) (stendhalWeight ℓ ν)) • v = 0 := by
    induction b generalizing v with
    | zero =>
      apply smul_eq_zero_of_mul_e _ _ v
      intro s w
      change π (pol _ * e s) * w = 0
      change π (pol (X _ ^ 1) * e s) * w = 0
      rw [pow_one, pol_X]
      cases hcs : s.lbl ⟨0, hb⟩ with
      | inl i =>
        rw [map_mul, affineTensorProjection_e_of_violated Λ ν s ⟨hb, by simp [hcs]⟩,
          mul_zero, zero_mul]
      | inr r => rw [affineTensorProjection_x_mul_e_of_red Λ ν s _ (by simp [hcs]), zero_mul]
    | succ b ih =>
      have hb' : b < (stendhalWeight ℓ ν).card := by omega
      have hN : ∀ v : T, (pol (X ⟨b, hb'⟩ ^ L b) :
          KLRAlgebra k (affineCoverQ Q Λ) (stendhalWeight ℓ ν)) • v = 0 := ih hb'
      apply smul_eq_zero_of_mul_e _ _ v
      intro s
      have inc {M : ℕ} (h : M ≤ L (b+1))
          (hm : (X ⟨b+1, hb⟩ : MvPolynomial (Fin _) k) ^ M ∈
            annE (Q := affineCoverQ Q Λ) T s) :
          (X ⟨b+1, hb⟩ : MvPolynomial (Fin _) k) ^ L (b+1) ∈
            annE (Q := affineCoverQ Q Λ) T s := by
        rw [← Nat.sub_add_cancel h, pow_add]
        exact Ideal.mul_mem_left _ _ hm
      have hne (dd : ℕ) (hdd : dd ≤ B) : L b * (L b + dd) ≤ L (b+1) :=
        (Nat.mul_le_mul_left _ (Nat.add_le_add_left hdd _)).trans (le_max_right ..)
      by_cases he : s.lbl ⟨b, by omega⟩ = s.lbl ⟨b+1, hb⟩
      · exact inc (le_max_left ..) (next_pow_mem_annE_of_eq b hb (L b) hN s he)
      cases hj : s.lbl ⟨b+1, hb⟩ with
      | inr r =>
        refine inc (hL1 (b+1)) fun w => ?_
        change π (pol _ * e s) * w = 0
        rw [pow_one, pol_X, affineTensorProjection_x_mul_e_of_red Λ ν s _ (by simp [hj]),
          zero_mul]
      | inl j =>
        have hjS : j ∈ S := hν (Multiset.mem_toFinset.mpr (mem_of_lbl_inl s _ hj))
        cases hi : s.lbl ⟨b, by omega⟩ with
        | inl i =>
          have hij : i ≠ j := by intro h; apply he; rw [hi, hj, h]
          have hiS : i ∈ S := hν (Multiset.mem_toFinset.mpr (mem_of_lbl_inl s _ hi))
          have hQc : aeval (![0, X 1] : Fin 2 → MvPolynomial (Fin 2) k)
              (affineCoverQ Q Λ (s.lbl ⟨b, by omega⟩) (s.lbl ⟨b+1, hb⟩)) =
                MvPolynomial.C (c i j hij) * X 1 ^ d i j hij := by
            rw [hi, hj]
            exact hcd i j hij
          have hd : d i j hij ≤ B := by
            have h := (Finset.le_sup (f := D i) hjS).trans
              (Finset.le_sup (f := fun t => S.sup (D t)) hiS)
            simp only [D, dite_eq_left hij] at h
            exact h.trans (Nat.le_add_right ..)
          exact inc (hne _ hd)
            (next_pow_mem_annE_of_ne b hb (L b) hN s he _ _ (hc i j hij) hQc)
        | inr r =>
          have hQc : aeval (![0, X 1] : Fin 2 → MvPolynomial (Fin 2) k)
              (affineCoverQ Q Λ (s.lbl ⟨b, by omega⟩) (s.lbl ⟨b+1, hb⟩)) =
                MvPolynomial.C 1 * X 1 ^ Λ r j := by
            rw [hi, hj]
            simp [affineCoverQ, stendhalQ]
          have hd : Λ r j ≤ B := by
            have h := (Finset.le_sup (f := fun r => Λ r j) (Finset.mem_univ r)).trans
              (Finset.le_sup (f := fun j => Finset.univ.sup fun r => Λ r j) hjS)
            exact h.trans (Nat.le_add_left ..)
          exact inc (hne _ hd)
            (next_pow_mem_annE_of_ne b hb (L b) hN s he _ _ isUnit_one hQc)
  have hz := hpow p.val p.isLt 1
  change π _ * 1 = 0 at hz
  simpa only [mul_one, map_pow, pol_X] using hz

include hQ in
/-- Adjoining sufficiently many black strands of one colour to fixed black
content gives the zero tensor product algebra: the `i`-string of weights of
`T^λ` through `β` is finite (Webster, arXiv:1309.3796v2, §5; the analogue for
cyclotomic KLR algebras is `CycKLR.eventually_subsingleton_replicate_add`). -/
theorem eventually_subsingleton_tensor (i : I) (β : Multiset I) :
    ∃ B : ℕ, ∀ n ≥ B,
      Subsingleton (TensorProductAlgebra k Q Λ (Multiset.replicate n i + β)) := by
  classical
  let S := insert i β.toFinset
  obtain ⟨L, hL⟩ := exists_uniform_tensor_dot_pow Λ hQ S
  obtain ⟨B, hB⟩ := CycKLR.exists_long_constant_block (I := I ⊕ Fin ℓ) L (Sum.inl i)
    (β.card + ℓ)
  refine ⟨B, ?_⟩
  intro n hn
  let ν := Multiset.replicate n i + β
  let μ := stendhalWeight ℓ ν
  have hν : ν.toFinset ⊆ S := by
    intro j hj
    rcases Multiset.mem_add.mp (Multiset.mem_toFinset.mp hj) with h | h
    · exact Finset.mem_insert.mpr (Or.inl (Multiset.eq_of_mem_replicate h))
    · exact Finset.mem_insert.mpr (Or.inr (Multiset.mem_toFinset.mpr h))
  have hrep : ((Multiset.replicate n i).map Sum.inl).filter
      (· ≠ (Sum.inl i : I ⊕ Fin ℓ)) = 0 := by
    rw [Multiset.map_replicate, Multiset.filter_eq_nil]
    intro a ha
    simp [Multiset.eq_of_mem_replicate ha]
  have hcount : (μ.filter (· ≠ Sum.inl i)).card ≤ β.card + ℓ := by
    simp only [μ, stendhalWeight, ν, Multiset.map_add, Multiset.filter_add, hrep, zero_add,
      Multiset.card_add]
    exact add_le_add ((Multiset.card_le_card (Multiset.filter_le ..)).trans (by simp))
      ((Multiset.card_le_card (Multiset.filter_le ..)).trans (by simp))
  have hlen : B ≤ μ.card := by simp [μ, stendhalWeight, ν]; omega
  let π := affineTensorProjection (Q := Q) Λ ν
  have he (s : Seq μ) : π (e s) = 0 := by
    obtain ⟨p, hpn, hc⟩ := hB s hcount hlen
    apply map_e_eq_zero_of_block_dot_pow π.toRingHom s p (L p) hpn hc
    change π _ = 0
    rw [map_mul, map_pow, hL hν (⟨p, by omega⟩ : Fin μ.card), zero_mul]
  apply subsingleton_of_zero_eq_one
  have hsum := congrArg π (sum_e (k := k) (Q := affineCoverQ Q Λ) (ν := μ))
  simpa [map_sum, he] using hsum

end Categorification.Stendhal

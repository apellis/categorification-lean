/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.EqualBlackReturnKernel
import Categorification.WeightedKLR.RedStrands.BraidedEqualBlackReturns

/-!
# The equal-black right-extreme corner after killing red dots

At the fixed top of the right extreme, all upper elements on the ordinary and
reversed-middle arms are sums of two polynomial PBW rows if those are the only
two compatible permutations. The full-joint coefficient of a relation in that
corner descends through the red-dot quotient. This is the two-black fixed-top
case in the proof of Webster, arXiv:1309.3796v2, §6.1, Lemma 6.8 after (6.21),
before imposing the higher ideal.
-/

noncomputable section
namespace Categorification.Stendhal.BraidedStendhalAlgebra
open KLR TypeA MvPolynomial KLR.KLRAlgebra

variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ} {ν : Multiset I}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}
local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "B" => BraidedStendhalAlgebra k Q Λ ν
local notation "π" => ofKLR k Q Λ ν
local notation "T" => toKLR k Q Λ ν

omit [DecidableEq I] in
/-- If the two adjacent equal black strands are the only black strands, every
red position is fixed by a loading stabilizer. The only permutations from the
nearby joint to the extreme are the return and the return followed by the black
crossing, even in the presence of exterior red spectators. -/
theorem twoBlack_return_permutations (r : Seq μ) (b : ℕ) (hp : b + 2 < m)
    (he : r.lbl ⟨b + 1, by omega⟩ = r.lbl ⟨b + 2, hp⟩)
    (red : ∀ a : Fin m, a ≠ ⟨b + 1, by omega⟩ → a ≠ ⟨b + 2, hp⟩ → (r.lbl a).isRight)
    (w : Equiv.Perm (Fin m)) : w • (sadj m b • r) = r ↔ w = wordProd m [b] ∨ w = wordProd m [b + 1, b] := by
  let j := b + 1
  let L : Fin m := ⟨j, by omega⟩
  let H : Fin m := ⟨j + 1, hp⟩
  have ne : L ≠ H := by intro e; have h := congrArg Fin.val e; change j = j + 1 at h; omega
  have fixed := sadj_smul_eq_self hp he
  constructor
  · intro hw
    let u := w * sadj m b
    have stab : u • r = r := hw
    have labels (a : Fin m) : r.lbl (u a) = r.lbl a := by
      have h := congrArg (fun z : Seq μ => z.lbl (u a)) stab.symm
      simpa only [Seq.lbl, Seq.smul_apply, Equiv.symm_apply_apply] using h
    have outside (a : Fin m) (ha : a ≠ L) (hb : a ≠ H) : u a = a :=
      eq_of_lbl_eq_of_isRight r (labels a) ((labels a).symm ▸ red a ha hb)
    have inside (a : Fin m) (ha : a = L ∨ a = H) : u a = L ∨ u a = H := by
      by_contra! hn
      have same : u a = a := u.injective (outside (u a) hn.1 hn.2)
      exact ha.elim (fun h => hn.1 (same.trans h)) (fun h => hn.2 (same.trans h))
    have oneOrSwap : u = 1 ∨ u = sadj m j := by
      rcases inside L (Or.inl rfl) with hL | hL
      · left
        have hH : u H = H := (inside H (Or.inr rfl)).resolve_left (fun h => ne (u.injective (hL.trans h.symm)))
        apply Equiv.ext
        intro a
        by_cases h₀ : a = L
        · subst a; exact hL
        by_cases h₁ : a = H
        · subst a; exact hH
        exact outside a h₀ h₁
      · right
        have hH : u H = L := (inside H (Or.inr rfl)).resolve_right (fun h => ne (u.injective (hL.trans h.symm)))
        apply Equiv.ext
        intro a
        by_cases h₀ : a = L
        · subst a; exact hL.trans (sadj_apply_left hp).symm
        by_cases h₁ : a = H
        · subst a; exact hH.trans (sadj_apply_right hp).symm
        exact (outside a h₀ h₁).trans (sadj_apply_of_ne a (fun h => h₀ (Fin.ext h)) (fun h => h₁ (Fin.ext h))).symm
    have back : w = u * sadj m b := by simp only [u, mul_assoc, TypeA.sadj_mul_self, mul_one]
    rcases oneOrSwap with hu | hu
    · left; rw [back, hu, one_mul]; simp only [wordProd_cons, wordProd_nil, mul_one]
    · right; rw [back, hu]; simp only [wordProd_cons, wordProd_nil, mul_one, j]
  · rintro (rfl | rfl) <;> simp only [wordProd_cons, wordProd_nil, mul_one, mul_smul, sadj_smul_smul, fixed]

omit [DecidableEq I] in
/-- For a black weight of cardinality two, the two specified black positions
account for every black strand. The matching condition therefore holds with
any number of exterior red spectators. -/
theorem twoBlack_return_permutations_of_card_two (r : Seq μ) (b : ℕ) (hp : b + 2 < m)
    (hν : ν.card = 2) (i : I)
    (hL : r.lbl ⟨b + 1, by omega⟩ = Sum.inl i) (hH : r.lbl ⟨b + 2, hp⟩ = Sum.inl i)
    (w : Equiv.Perm (Fin m)) : w • (sadj m b • r) = r ↔ w = wordProd m [b] ∨ w = wordProd m [b + 1, b] := by
  classical
  apply twoBlack_return_permutations r b hp (hL.trans hH.symm) _ w
  let L : Fin m := ⟨b + 1, by omega⟩
  let H : Fin m := ⟨b + 2, hp⟩
  let black := Finset.univ.filter (fun a : Fin m => (r.lbl a).isLeft)
  have card : black.card = 2 := by
    let isBlack := fun z : I ⊕ Fin ℓ => z.isLeft = true
    have count : Multiset.countP isBlack μ = ν.card := by
      rw [stendhalWeight, Multiset.countP_add, Multiset.countP_map, Multiset.countP_map]
      simp [isBlack]
    have data := congrArg (Multiset.countP isBlack) r.2
    calc
      black.card = Multiset.countP isBlack (Multiset.map r.lbl Finset.univ.val) := by
        rw [Multiset.countP_map]
        rfl
      _ = _ := data.trans (count.trans hν)
  have sub : ({L, H} : Finset (Fin m)) ⊆ black := by
    intro a ha
    rcases Finset.mem_insert.mp ha with h | h
    · subst a; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [L, hL]⟩
    · rw [Finset.mem_singleton] at h; subst a
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [H, hH]⟩
  have ne : L ≠ H := by intro e; have h := congrArg Fin.val e; change b + 1 = b + 2 at h; omega
  have eq : {L, H} = black := Finset.eq_of_subset_of_card_le sub (by simp [card, ne])
  intro a ha hb
  cases h : r.lbl a with
  | inl c =>
    have mem : a ∈ black := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [h]⟩
    rw [← eq, Finset.mem_insert, Finset.mem_singleton] at mem
    exact (mem.elim ha hb).elim
  | inr c => rfl

/-- In the braided Stendhal algebra, a pair of arbitrary supported upper
coefficients at the right extreme whose arm sum vanishes has a common
full-joint coefficient, provided that only the two return permutations reach
the fixed top. In the four-position interval with a repeated black label this
last condition is verified by finite enumeration. Webster, arXiv:1309.3796v2,
§6.1, proof of Lemma 6.8 after (6.21). -/
theorem exists_equalBlack_corner_cycle_coefficient (hQ : KLRSymm Q) (s : Seq μ) (l : List ℕ)
    (b : ℕ) (hp : b + 2 < m) (hl : IsReduced m l) (hjl : IsReduced m ((b + 1) :: l))
    (red : Fin ℓ) (black : I)
    (hr : (wordProd m l • s).lbl ⟨b, by omega⟩ = Sum.inr red)
    (hi : (wordProd m l • s).lbl ⟨b + 1, by omega⟩ = Sum.inl black)
    (hi' : (wordProd m l • s).lbl ⟨b + 2, hp⟩ = Sum.inl black)
    (matching : ∀ w : Equiv.Perm (Fin m), w • (sadj m b • (wordProd m l • s)) = wordProd m l • s ↔
      w = wordProd m [b] ∨ w = wordProd m [b + 1, b]) (x y : B) :
    let r := wordProd m l • s
    let t := sadj m b • r
    let j := b + 1
    π (e r) * x = x → x * π (e t) = x → π (e r) * y = y → y * π (e t) = y →
    x * π (ψw (b :: l) * e s) + y * π (ψw (b :: j :: l) * e s) = 0 →
    ∃ c : B, c * π (e (sadj m j • t)) = c ∧ c * π (ψw [b, j] * e t) = -x ∧ c * π (ψw [j] * e t) = y := by
  intro r t j hx hx' hy hy' rel
  have he : r.lbl ⟨j, by omega⟩ = r.lbl ⟨j + 1, hp⟩ := hi.trans hi'.symm
  have hn : r.lbl ⟨b, by omega⟩ ≠ r.lbl ⟨j, by omega⟩ := by rw [hr, hi]; exact Sum.inr_ne_inl
  have hw : stendhalQ Q Λ (r.lbl ⟨b, by omega⟩) (r.lbl ⟨j, by omega⟩) = X 1 ^ Λ red black := by
    rw [hr, hi, stendhalQ_inr_inl]
  have left (z : B) (hz : π (e r) * z = z) : e r * T z = T z := by
    simpa only [map_mul, toKLR_ofKLR_e] using congrArg T hz
  have right (z : B) (hz : z * π (e t) = z) : T z * e t = T z := by
    simpa only [map_mul, toKLR_ofKLR_e] using congrArg T hz
  have sum := congrArg T rel
  simp only [map_add, map_mul, toKLR_ofKLR_e, toKLR_ofKLR_ψw, map_zero] at sum
  obtain ⟨c, cut, cB, cD⟩ := KLR.KLRAlgebra.exists_equalBlack_corner_cycle_coefficient
    (stendhalQ_symm Q Λ hQ) s l b (Λ red black) hp hl hjl he hn hw matching (T x) (T y)
    (left x hx) (right x hx') (left y hy) (right y hy') sum
  refine ⟨π c, ?_, ?_, ?_⟩
  · exact (map_mul π _ _).symm.trans (congrArg π cut)
  · rw [← map_mul, cB, map_neg, ofKLR_toKLR hQ]
  · rw [← map_mul, cD, ofKLR_toKLR hQ]

end Categorification.Stendhal.BraidedStendhalAlgebra
end

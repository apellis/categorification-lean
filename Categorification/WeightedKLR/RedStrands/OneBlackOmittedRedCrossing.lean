/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.OneBlackHigherCrossing
import Categorification.WeightedKLR.RedStrands.BraidedFactorization
import Categorification.WeightedKLR.RedStrands.BraidedIdentity

/-!
# Crossing an omitted red and its retained neighbor at one black

Webster, arXiv:1309.3796v2, proof of Lemma 6.8 at (6.21).
The omitted red preserves the retained root. The affine cut of every strictly
higher loading factors through the two crossings across the paired reds.
-/

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA

variable {I : Type*} [DecidableEq I] {ℓ : ℕ} {i : I}
local notation "μ" => stendhalWeight ℓ (Singleton.singleton i : Multiset I)
local notation "n" => Multiset.card μ

/-- Crossing the omitted red preserves the retained root at one black. -/
theorem adjacentBlockRoot_oneBlack_eq_sadj_omitted {a b : Fin ℓ} {L M : List (Fin ℓ)}
    (s : Seq μ) (hs : redWord s = L ++ a :: b :: M) {j : ℕ} (hj : j + 1 < n)
    (hr : s.lbl ⟨j, lt_trans (Nat.lt_succ_self _) hj⟩ = .inr b)
    (hb : s.lbl ⟨j + 1, hj⟩ = .inl i) :
    adjacentBlockRoot a b s = adjacentBlockRoot a b (sadj n j • s) := by
  let u : Fin n := ⟨j, lt_trans (Nat.lt_succ_self _) hj⟩
  let v : Fin n := ⟨j + 1, hj⟩
  let t := sadj n j • s
  have hswap (q : Fin n) : t.lbl q = s.lbl (sadj n j q) := sadj_smul_apply j s q
  have ht : redWord t = redWord s :=
    redWord_sadj_smul s hj (by rw [hr, hb]; simp)
  have htu : t.lbl u = .inl i := by
    rw [hswap, show sadj n j u = v from sadj_apply_left hj]
    exact hb
  apply (adjacentBlockRoot_oneBlack_eq_iff hs (ht.trans hs) v u hb htu).2
  intro q hq ps pt hps hpt
  have hpos : ps = sadj n j pt := lbl_inj_of_inr s q hps ((hswap pt).symm.trans hpt)
  have hneL : ps.val ≠ j := by
    intro h
    have heq : ps = u := Fin.ext h
    rw [heq] at hps
    exact hq (Sum.inr.inj (hps.symm.trans hr))
  have hneR : ps.val ≠ j + 1 := by
    intro h
    have heq : ps = v := Fin.ext h
    rw [heq] at hps
    have hbad := hps.symm.trans hb
    cases hbad
  have hfix : sadj n j ps = ps := sadj_apply_of_ne ps hneL hneR
  have hpt' : pt = ps := calc
    pt = sadj n j (sadj n j pt) := (TypeA.sadj_sadj_apply n j pt).symm
    _ = sadj n j ps := congrArg (sadj n j) hpos.symm
    _ = ps := hfix
  rw [hpt']
  change (j + 1 < ps.val) ↔ (j < ps.val)
  omega

end Categorification.Stendhal

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLRAlgebra TypeA

variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ} {i : I}
variable (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
local notation "μ" => stendhalWeight ℓ (Singleton.singleton i : Multiset I)
local notation "n" => Multiset.card μ
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ

/-- The affine cut for every strict higher retained loading factors through
both crossings when the unique black starts immediately right of the pair. -/
theorem oneBlack_cut_factors_across_pair {a b : Fin ℓ} {L M : List (Fin ℓ)}
    (s : Seq μ) (hs : redWord s = L ++ a :: b :: M) (j : ℕ) (hj : j + 2 < n)
    (ha : s.lbl ⟨j, by omega⟩ = .inr a)
    (hr : s.lbl ⟨j + 1, by omega⟩ = .inr b)
    (hb : s.lbl ⟨j + 2, hj⟩ = .inl i)
    (w : Seq μ) (hw : redWord w = redWord s)
    (hlt : adjacentBlockRoot a b s < adjacentBlockRoot a b w) (z : R) :
    ∃ y : R, (ψ (j + 1) * KLRAlgebra.e (sadj n (j + 1) • s)) *
        (ψ j * KLRAlgebra.e (sadj n j • (sadj n (j + 1) • s))) * y =
      KLRAlgebra.e s * z * KLRAlgebra.e w := by
  let t := sadj n (j + 1) • s
  have hj' : j + 1 < n := by omega
  have hswap (q : Fin n) : t.lbl q = s.lbl (sadj n (j + 1) q) := sadj_smul_apply (j + 1) s q
  have ht : redWord t = redWord s :=
    redWord_sadj_smul s hj (by rw [hr, hb]; simp)
  have hta : t.lbl ⟨j, by omega⟩ = .inr a := by
    rw [hswap, sadj_apply_of_ne _ (by change j ≠ j + 1; omega)
      (by change j ≠ j + 1 + 1; omega)]
    exact ha
  have htb : t.lbl ⟨j + 1, hj'⟩ = .inl i := by
    rw [hswap, sadj_apply_left hj]
    exact hb
  have heq := adjacentBlockRoot_oneBlack_eq_sadj_omitted s hs hj hr hb
  have htw : adjacentBlockRoot a b t < adjacentBlockRoot a b w := heq ▸ hlt
  obtain ⟨v, hv⟩ := cut_factors_of_leftDescent (j + 1) hj s w z
    (oneBlack_leftDescent_of_higher hs hw (j + 1) hj hr hb hlt)
  obtain ⟨y, hy⟩ := cut_factors_of_leftDescent j hj' t w v
    (oneBlack_leftDescent_of_higher (ht.trans hs) (hw.trans ht.symm) j hj' hta htb htw)
  refine ⟨y, ?_⟩
  change ((ψ (j + 1) * e t) * (ψ j * e (sadj n j • t))) * y = e s * z * e w
  calc
    _ = (ψ (j + 1) * e t) * (e t * v * e w) := by rw [mul_assoc, hy]
    _ = ((ψ (j + 1) * e t) * v) * e w := by
      simp only [mul_assoc]
      rw [← mul_assoc (e t) (e t), e_mul_self]
    _ = _ := by rw [hv, mul_assoc (e s * z), e_mul_self]

end Categorification.Stendhal.BraidedStendhalAlgebra

namespace Categorification.Stendhal

open KLR

variable {I : Type*} {ℓ : ℕ} {i : I}
local notation "μ" => stendhalWeight ℓ (Singleton.singleton i : Multiset I)
local notation "n" => Multiset.card μ

/-- If the black is immediately right of the omitted red, the retained red
of that canonical adjacent pair is immediately left of the omitted red. -/
theorem oneBlack_retainedRed_of_omittedRed_beforeBlack
    (s : Seq μ) (hs : IsRedOrdered s) {a b : Fin ℓ} (hab : a.val + 1 = b.val)
    (j : ℕ) (hj : j + 2 < n)
    (hr : s.lbl ⟨j + 1, by omega⟩ = .inr b) (hb : s.lbl ⟨j + 2, hj⟩ = .inl i) :
    s.lbl ⟨j, by omega⟩ = .inr a := by
  let p : Fin n := ⟨j, by omega⟩
  let q : Fin n := ⟨j + 1, by omega⟩
  let z : Fin n := ⟨j + 2, hj⟩
  obtain ⟨u, hu⟩ := exists_lbl_eq_inr s a
  have huq : u < q := by
    by_contra! h
    rcases eq_or_lt_of_le h with heq | hlt
    · subst u
      have e := congrArg Fin.val (Sum.inr.inj (hr.symm.trans hu))
      omega
    · have hbad := hs q u b a hlt hr hu
      change b.val < a.val at hbad
      omega
  have hrp : ∃ r : Fin ℓ, s.lbl p = .inr r := by
    cases h : s.lbl p with
    | inr r => exact ⟨r, rfl⟩
    | inl c =>
      exfalso
      have hm := Seq.mem s p
      change s.lbl p ∈ μ at hm
      rw [h] at hm
      have he : c = i := by simpa [stendhalWeight] using hm
      subst c
      have hn : (Finset.univ.val.map s.lbl).Nodup := by
        rw [show Finset.univ.val.map s.lbl = μ from s.2]
        simp [stendhalWeight, List.nodup_ofFn, Sum.inr_injective]
      have eq := Multiset.inj_on_of_nodup_map hn p (by simp) z (by simp) (h.trans hb.symm)
      have bad := congrArg Fin.val eq
      change j = j + 2 at bad
      omega
  obtain ⟨r, hp⟩ := hrp
  change s.lbl p = .inr a
  have hup : u ≤ p := by change u.val ≤ j; change u.val < j + 1 at huq; omega
  rcases eq_or_lt_of_le hup with h | h
  · rwa [← h]
  · have h₁ := hs u p a r h hu hp
    have h₂ := hs p q r b (Nat.lt_succ_self _) hp hr
    change a.val < r.val at h₁
    change r.val < b.val at h₂
    omega

end Categorification.Stendhal

namespace Categorification.Stendhal

open KLR

variable {I : Type} [DecidableEq I] {ℓ : ℕ} {i : I}
local notation "μ" => stendhalWeight ℓ (Singleton.singleton i : Multiset I)
local notation "n" => Multiset.card μ

/-- A canonical one-black loading at the first red has no strictly higher
surviving loading for any adjacent retained pair. -/
theorem isViolated_of_strictly_higher_oneBlack_early
    {a b : Fin ℓ} {s w : Seq μ} {L M : List (Fin ℓ)}
    (hs : redWord s = L ++ a :: b :: M) (hcanonical : IsRedOrdered s)
    (hw : redWord w = redWord s)
    (p : Fin n) (hp : s.lbl p = .inl i) (hpos : p.val ≤ 1)
    (hlt : adjacentBlockRoot a b s < adjacentBlockRoot a b w) : IsViolated w := by
  have h0 : 0 < n := Nat.zero_lt_of_lt p.isLt
  let r0 : Fin ℓ := ⟨0, Nat.zero_lt_of_lt a.isLt⟩
  let w0 : Fin n := ⟨0, h0⟩
  have hwOrdered := (redWord_eq_finRange_iff w).1 (hw.trans ((redWord_eq_finRange_iff s).2 hcanonical))
  have hblack : (Sum.inl i : I ⊕ Fin ℓ) ∈ μ := by simp [stendhalWeight]
  rw [← show Finset.univ.val.map w.lbl = μ from w.2, Multiset.mem_map] at hblack
  obtain ⟨q, _, hq⟩ := hblack
  cases h0Label : w.lbl w0 with
  | inl c => exact ⟨h0, by rw [show w.lbl ⟨0, h0⟩ = .inl c from h0Label]; rfl⟩
  | inr r =>
    have hr0 : r = r0 := by
      obtain ⟨z, hz⟩ := exists_lbl_eq_inr w r0
      by_cases e : w0 = z
      · exact Sum.inr.inj (h0Label.symm.trans (e.symm ▸ hz))
      · have hwz : w0 < z := by
          change (0 : ℕ) < z.val
          apply Nat.pos_of_ne_zero
          exact fun h => e (Fin.ext h.symm)
        exact (Nat.not_lt_zero _ (hwOrdered _ _ _ _ hwz h0Label hz)).elim
    subst r
    exfalso
    apply hlt.not_ge
    apply (adjacentBlockRoot_oneBlack_le_iff (hw.trans hs) hs q p hq hp).2
    intro r _ qr pr hqr hpr hq_lt
    have hr_ne : r ≠ r0 := by
      intro e
      subst r
      have eq : qr = w0 := lbl_inj_of_inr w r0 hqr h0Label
      subst qr
      exact (Nat.not_lt_zero _ hq_lt).elim
    obtain ⟨p0, hp0⟩ := exists_lbl_eq_inr s r0
    have hlt_pr : p0 < pr := by
      by_contra! hnot
      rcases eq_or_lt_of_le hnot with heq | hlt'
      · subst pr
        exact hr_ne (Sum.inr.inj (hpr.symm.trans hp0))
      · exact (Nat.not_lt_zero _ (hcanonical _ _ _ _ hlt' hpr hp0)).elim
    have hp_ne : p.val ≠ pr.val := by
      intro eq
      have hp' : p = pr := Fin.ext eq
      rw [hp'] at hp
      have bad := hp.symm.trans hpr
      cases bad
    change p.val < pr.val
    change p0.val < pr.val at hlt_pr
    omega

end Categorification.Stendhal

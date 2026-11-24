/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.OneBlackHigherCrossing
import Categorification.WeightedKLR.RedStrands.BraidedFactorization

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

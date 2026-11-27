/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidModelMap
import Categorification.WeightedKLR.Rigidity.CupCapModelMap

/-!
# Dots and crossings below the cap generators of a cap after `λ_j`

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17, for a cap inserted after the red strand
`λ_j`. These are the identities in the KLR algebra of `λ⁺` behind the dot and crossing relations
of Definition 7.15 in the model `CupCap.MidModel`: a dot or a crossing of the top passes below
the passage `U` of the cap generator (`CupCap.midCapBot`), modulo diagrams in which a strand
leaves the maximum, and a crossing next to the red strand `λ_{j+1}` moves the passage by one
step.

## Main results

* `CupCap.mid_dot_diff_mem`: a dot passes below the passage.
* `CupCap.mid_cross_far_diff_mem`: a crossing away from `λ_{j+1}` passes below the passage.
* `CupCap.ψ_eSum_passU_eSum`: the crossing just left of the window of the bottom passes below
  the passage of the strands left of it.
* `CupCap.botMap_mul_eSum_mul_ψ_of_red`: a crossing of two red strands below the cap vanishes.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Eat" s:max n:max hn:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s n hn)
local notation "E" s:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s (midPos j s) (midPos_le j s))
local notation "P" n:max d:max => passU Q Λ Λc j hj ν ν₀ n d
local notation "bot" => botMap k Q Λ Λc j hj ν ν₀

omit [DecidableEq I] in
theorem dotPos_val_mid (n : Fin (m + 1)) (a : Fin m) :
    (dotPos (j := j) (hj := hj) (ν₀ := ν₀) n a).val =
      if a.val < n then a.val else a.val + N := by
  rw [dotPos, Fin.val_cast, insertPos_inl_val, Multiset.card_map]

omit [DecidableEq I] in
theorem lt_M_of_lt_m {a : ℕ} (ha : a < m) : a < M := by
  have := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀); omega

/-- A diagram in the exit span at a window equal to `midPos j s` lies in the exit span of the
maximum. -/
theorem mem_midExit_of_eq (s : Seq (stendhalWeight ℓ ν)) {c : ℕ} (hc : c ≤ m)
    (h : c = midPos j s) {y : Rp} (hy : y ∈ exitSpan Q Λ Λc j hj (ν₀ := ν₀) s c hc) :
    y ∈ midExit j hj Q Λ Λc ν ν₀ := by
  subst h; exact mem_midExit s hy

/-- The diagram below the cap generator at a window given by its value. -/
theorem midCapBot_eq_of (s : Seq (stendhalWeight ℓ ν)) {n c : ℕ} (hn : n ≤ midPos j s)
    (h : midPos j s = c) (hc : c ≤ m) :
    midCapBot j hj Q Λ Λc ν₀ s n hn = Eat s c hc * P n (c - n) * Eat s n (by omega) := by
  subst h; rfl

/-- **A dot on the top passes below the passage of the cap generator**, modulo diagrams in which
a strand leaves the maximum. -/
theorem mid_dot_diff_mem (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ midPos j s) (a : Fin m)
    (d d' : Fin M) (hd' : d'.val = if a.val < midPos j s then a.val else a.val + N)
    (hd : d.val = if a.val < n then a.val else a.val + N) :
    (KLRAlgebra.x d' * E s * (P n (midPos j s - n) * Eat s n (hn.trans (midPos_le j s))) -
      E s * P n (midPos j s - n) * Eat s n (hn.trans (midPos_le j s)) * KLRAlgebra.x d : Rp) ∈
      exitSpan Q Λ Λc j hj s (midPos j s) (midPos_le j s) := by
  have hcm := midPos_le j s
  have hnm := hn.trans hcm
  have hM := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  set c := midPos j s with hcdef
  set Pc := P n (c - n)
  have hxm := (commute_x_eSum (Q' := stendhalQ Q (plusLabels Λ Λc j hj)) d'
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s c hcm)).eq
  have hxn := (commute_x_eSum (Q' := stendhalQ Q (plusLabels Λ Λc j hj)) d
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s n hnm)).eq
  have hre : KLRAlgebra.x d' * Eat s c hcm * (Pc * Eat s n hnm) -
      Eat s c hcm * Pc * Eat s n hnm * KLRAlgebra.x d =
      Eat s c hcm * (KLRAlgebra.x d' * Pc - Pc * KLRAlgebra.x d) * Eat s n hnm := by
    calc KLRAlgebra.x d' * Eat s c hcm * (Pc * Eat s n hnm) -
          Eat s c hcm * Pc * Eat s n hnm * KLRAlgebra.x d
        = Eat s c hcm * KLRAlgebra.x d' * Pc * Eat s n hnm -
            Eat s c hcm * Pc * (KLRAlgebra.x d * Eat s n hnm) := by
          rw [hxm]; simp only [mul_assoc]; rw [← hxn]
      _ = _ := by noncomm_ring
  rw [hre]
  refine exitSpan_mul_right s hcm ?_ _
  by_cases ha : a.val < n
  · have hdd : d = d' := Fin.ext (by rw [hd, hd']; split_ifs <;> omega)
    have hc : Commute (KLRAlgebra.x d' : Rp) Pc := commute_passU n (c - n) fun p hp _ =>
      commute_x_underRight _ (Or.inl (by rw [hd']; split_ifs <;> omega))
    rw [hdd, hc.eq, sub_self, mul_zero]
    exact zero_mem _
  by_cases hac : c ≤ a.val
  · have hdd : d = d' := Fin.ext (by rw [hd, hd']; split_ifs <;> omega)
    have hc : Commute (KLRAlgebra.x d' : Rp) Pc := commute_passU n (c - n) fun p _ hp =>
      commute_x_underRight _ (Or.inr (by rw [hd']; split_ifs <;> omega))
    rw [hdd, hc.eq, sub_self, mul_zero]
    exact zero_mem _
  have hda : d.val = a.val + N := by simp [hd, ha]
  have hda' : d'.val = a.val := by rw [hd']; split_ifs <;> omega
  have h1 := passU_add Q Λ Λc (j := j) (hj := hj) (ν := ν) (ν₀ := ν₀) n (a - n) (c - a)
  rw [show a.val - n + (c - a.val) = c - n by omega, show n + (a.val - n) = a.val by omega] at h1
  have h2 := passU_succ_left Q Λ Λc (j := j) (hj := hj) (ν := ν) (ν₀ := ν₀) a (c - a - 1)
  rw [show c - a.val - 1 + 1 = c - a.val by omega] at h2
  set P' := P (a + 1) (c - a - 1)
  set P'' := P n (a - n)
  have hP : Pc = P' * underRight N a * P'' := by
    change passU Q Λ Λc j hj ν ν₀ n (c - n) = _
    rw [h1, h2]
  have hc1 : Commute (KLRAlgebra.x d' : Rp) P' := commute_passU _ _ fun p hp _ =>
    commute_x_underRight _ (Or.inl (by omega))
  have hc2 : Commute (KLRAlgebra.x d : Rp) P'' := commute_passU _ _ fun p _ hp =>
    commute_x_underRight _ (Or.inr (by omega))
  have hE := passU_mul_eSum (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc s (a + 1) (c - a - 1)
    (by omega)
  rw [insertSet_congr' s (p := a.val + 1 + (c - a.val - 1)) _ hcm (by omega)] at hE
  have hD := slides_passing_x (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc s (q := a) (by omega)
  have hxa : (KLRAlgebra.x ⟨a.val, lt_M_of_succ_le (ν₀ := ν₀) (by omega : a.val + 1 ≤ m)⟩ :
      Rp) = KLRAlgebra.x d' := congrArg _ (Fin.ext hda'.symm)
  have hxd : (KLRAlgebra.x ⟨a.val + N, add_N_lt_M_of_succ_le (ν₀ := ν₀)
      (by omega : a.val + 1 ≤ m)⟩ : Rp) = KLRAlgebra.x d := congrArg _ (Fin.ext hda.symm)
  rw [hxa, hxd] at hD
  have hre2 : Eat s c hcm * (KLRAlgebra.x d' * Pc - Pc * KLRAlgebra.x d) =
      P' * (Eat s (a + 1) (by omega) * (KLRAlgebra.x d' * underRight N a -
        underRight N a * KLRAlgebra.x d)) * P'' := by
    have h4 : KLRAlgebra.x d' * (P' * underRight N a * P'') -
        P' * underRight N a * P'' * KLRAlgebra.x d =
        P' * (KLRAlgebra.x d' * underRight N a - underRight N a * KLRAlgebra.x d) * P'' := by
      have e1 : KLRAlgebra.x d' * (P' * underRight N a * P'') =
          P' * KLRAlgebra.x d' * underRight N a * P'' := by
        simp only [← mul_assoc]; rw [hc1.eq]
      have e2 : P' * underRight N a * P'' * KLRAlgebra.x d =
          P' * underRight N a * KLRAlgebra.x d * P'' := by
        simp only [mul_assoc]; rw [hc2.eq]
      rw [e1, e2]; noncomm_ring
    rw [hP, h4]
    simp only [← mul_assoc]
    rw [← hE]
  rw [hre2]
  refine exitSpan_mul_right s hcm ?_ _
  have h3 := passU_mul_mem (j := j) (hj := hj) Q Λ Λc s (a + 1) (c - a - 1) (by omega) hD
  rwa [exitSpan_congr' s (p := a.val + 1 + (c - a.val - 1)) _ hcm (by omega)] at h3

/-- **A crossing of the top away from `λ_{j+1}` passes below the passage of the cap generator**,
modulo diagrams in which a strand leaves the maximum. -/
theorem mid_cross_far_diff_mem (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ midPos j s)
    {p : ℕ} (hp : p + 1 < n ∨ n ≤ p) (hpm : p + 1 < m)
    (hfar : p + 1 < midPos j s ∨ midPos j s + 1 ≤ p) :
    (KLRAlgebra.ψ (crossPos (midPos j s) N p) * E s *
        (P n (midPos j s - n) * Eat s n (hn.trans (midPos_le j s))) -
      Eat (sadj m p • s) (midPos j s) (midPos_le j s) * P n (midPos j s - n) *
        Eat (sadj m p • s) n (hn.trans (midPos_le j s)) * KLRAlgebra.ψ (crossPos n N p) : Rp) ∈
      exitSpan Q Λ Λc j hj (sadj m p • s) (midPos j s) (midPos_le j s) := by
  have hcm := midPos_le j s
  have hnm := hn.trans hcm
  set c := midPos j s with hcdef
  set s' := sadj m p • s
  set Pc := P n (c - n)
  have h1 := ψ_crossPos_mul_eSum (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) s
    hcm (p := p) (by omega)
  have h2 := ψ_crossPos_mul_eSum (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) s
    hnm hp
  have hre : KLRAlgebra.ψ (crossPos c N p) * Eat s c hcm * (Pc * Eat s n hnm) -
      Eat s' c hcm * Pc * Eat s' n hnm * KLRAlgebra.ψ (crossPos n N p) =
      Eat s' c hcm * (KLRAlgebra.ψ (crossPos c N p) * Pc - Pc * KLRAlgebra.ψ (crossPos n N p)) *
        Eat s n hnm := by
    rw [h1]
    simp only [mul_assoc]
    rw [← h2]
    noncomm_ring
  rw [hre]
  refine exitSpan_mul_right _ hcm ?_ _
  rcases hfar with hpc | hpc
  swap
  · have hc1 : crossPos c N p = p + N := by unfold crossPos; split_ifs <;> omega
    have hc2 : crossPos n N p = p + N := by unfold crossPos; split_ifs <;> omega
    have hcom : Commute (KLRAlgebra.ψ (p + N) : Rp) Pc := commute_passU n (c - n) fun q _ hq =>
      commute_ψ_underRight _ (Or.inr (by omega))
    rw [hc1, hc2, hcom.eq, sub_self, mul_zero]
    exact zero_mem _
  have hc1 : crossPos c N p = p := by unfold crossPos; split_ifs <;> omega
  rw [hc1]
  rcases hp with hp | hp
  · have hc : crossPos n N p = p := by unfold crossPos; split_ifs <;> omega
    have hcom : Commute (KLRAlgebra.ψ p : Rp) Pc := commute_passU n (c - n) fun q hq _ =>
      commute_ψ_underRight _ (Or.inl (by omega))
    rw [hc, hcom.eq, sub_self, mul_zero]
    exact zero_mem _
  have hc : crossPos n N p = p + N := by unfold crossPos; split_ifs <;> omega
  rw [hc]
  have h3 := passU_add Q Λ Λc (j := j) (hj := hj) (ν := ν) (ν₀ := ν₀) n (p - n) (c - p)
  rw [show p - n + (c - p) = c - n by omega, show n + (p - n) = p by omega] at h3
  have h4 := passU_add Q Λ Λc (j := j) (hj := hj) (ν := ν) (ν₀ := ν₀) p 2 (c - p - 2)
  rw [show 2 + (c - p - 2) = c - p by omega] at h4
  set P' := P (p + 2) (c - p - 2)
  set P'' := P n (p - n)
  set P2 := P p 2
  have hP : Pc = P' * P2 * P'' := by
    change passU Q Λ Λc j hj ν ν₀ n (c - n) = _
    rw [h3, h4]
  have hc1 : Commute (KLRAlgebra.ψ p : Rp) P' := commute_passU _ _ fun q hq _ =>
    commute_ψ_underRight _ (Or.inl (by omega))
  have hc2 : Commute (KLRAlgebra.ψ (p + N) : Rp) P'' := commute_passU _ _ fun q _ hq =>
    commute_ψ_underRight _ (Or.inr (by omega))
  have hE := passU_mul_eSum (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc s' (p + 2) (c - p - 2)
    (by omega)
  rw [insertSet_congr' s' (p := p + 2 + (c - p - 2)) _ hcm (by omega)] at hE
  have hD := slides_passing_ψ (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) s'
    (q := p) (by omega)
  have h5 : KLRAlgebra.ψ p * Pc - Pc * KLRAlgebra.ψ (p + N) =
      P' * (KLRAlgebra.ψ p * P2 - P2 * KLRAlgebra.ψ (p + N)) * P'' := by
    have e1 : KLRAlgebra.ψ p * (P' * P2 * P'') = P' * KLRAlgebra.ψ p * P2 * P'' := by
      simp only [← mul_assoc]; rw [hc1.eq]
    have e2 : P' * P2 * P'' * KLRAlgebra.ψ (p + N) = P' * P2 * KLRAlgebra.ψ (p + N) * P'' := by
      simp only [mul_assoc]; rw [hc2.eq]
    rw [hP, e1, e2]; noncomm_ring
  rw [h5]
  simp only [← mul_assoc]
  rw [← hE]
  refine exitSpan_mul_right _ hcm ?_ _
  rw [mul_assoc]
  have h6 := passU_mul_mem (j := j) (hj := hj) Q Λ Λc s' (p + 2) (c - p - 2) (by omega) hD
  rwa [exitSpan_congr' s' (p := p + 2 + (c - p - 2)) _ hcm (by omega)] at h6

/-- The crossing `ψ_{p + N}` of the strands of `s` at `p, p + 1` (with the window at `p`) passes
below the passage of the strands at `n, …, p - 1`. -/
theorem ψ_eSum_passU_eSum (s : Seq (stendhalWeight ℓ ν)) {n p : ℕ} (hnp : n ≤ p)
    (hpm : p + 1 < m) :
    (KLRAlgebra.ψ (p + N) * Eat s p (by omega) * (P n (p - n) * Eat s n (by omega)) : Rp) =
      P n (p - n) * Eat (sadj m p • s) n (by omega) * KLRAlgebra.ψ (p + N) := by
  have hE := passU_mul_eSum (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc s n (p - n) (by omega)
  rw [insertSet_congr' s (p := n + (p - n)) _ (show p ≤ m by omega) (by omega)] at hE
  have hψp := ψ_crossPos_mul_eSum (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) s
    (show n ≤ m by omega) (p := p) (Or.inr hnp)
  have hcn : crossPos n N p = p + N := by unfold crossPos; split_ifs <;> omega
  rw [hcn] at hψp
  have hcom : Commute (KLRAlgebra.ψ (p + N) : Rp) (P n (p - n)) :=
    commute_passU n (p - n) fun q _ hq => commute_ψ_underRight _ (Or.inr (by omega))
  rw [mul_assoc, hE, ← mul_assoc (Eat s p _), (KLRAlgebra.eSum_idem _).eq, ← hE, ← mul_assoc,
    hcom.eq, mul_assoc, hψp, ← mul_assoc]

/-- The same, with the window of the top of the passage at `p` on `s_p s`. -/
theorem ψ_eSum_passU_eSum' (s : Seq (stendhalWeight ℓ ν)) {n p : ℕ} (hnp : n ≤ p)
    (hpm : p + 1 < m) :
    (KLRAlgebra.ψ (p + N) * Eat s p (by omega) * (P n (p - n) * Eat s n (by omega)) : Rp) =
      Eat (sadj m p • s) p (by omega) * P n (p - n) * Eat (sadj m p • s) n (by omega) *
        KLRAlgebra.ψ (p + N) := by
  have hE := passU_mul_eSum (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc (sadj m p • s) n (p - n)
    (by omega)
  rw [insertSet_congr' (sadj m p • s) (p := n + (p - n)) _ (show p ≤ m by omega)
    (by omega)] at hE
  rw [ψ_eSum_passU_eSum s hnp hpm, hE]
  conv_rhs => rw [mul_assoc (Eat _ p _) (P n (p - n)), hE, ← mul_assoc,
    (KLRAlgebra.eSum_idem _).eq]

/-- **A crossing of two red strands below the cap vanishes** in `T̃^{λ⁺}`. -/
theorem botMap_mul_eSum_mul_ψ_of_red (s : Seq (stendhalWeight ℓ ν)) {n p : ℕ} (hnp : n ≤ p)
    (hpm : p + 1 < m) (h₁ : (s.lbl ⟨p, by omega⟩).isRight) (h₂ : (s.lbl ⟨p + 1, hpm⟩).isRight)
    (Y : Rp) : bot (Y * Eat (sadj m p • s) n (by omega) * KLRAlgebra.ψ (p + N)) = 0 := by
  have hM := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  have hψ := ψ_crossPos_mul_eSum (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) s
    (show n ≤ m by omega) (p := p) (Or.inr hnp)
  have hcn : crossPos n N p = p + N := by unfold crossPos; split_ifs <;> omega
  rw [hcn] at hψ
  rw [mul_assoc, ← hψ, map_mul, eSum_insertSet, Finset.mul_sum, map_sum,
    Finset.sum_eq_zero, mul_zero]
  intro w _
  have hp' : p + N + 1 < M := by omega
  refine botMap_ψ_mul_e_of_red Q Λ Λc (p + N) hp' _ ?_ ?_
  · rw [insertSeq_lbl_ge s (show n ≤ m by omega) _ ⟨p, by omega⟩ hnp rfl]
    revert h₁; cases s.lbl ⟨p, by omega⟩ <;> simp
  · rw [insertSeq_lbl_ge s (show n ≤ m by omega) _ ⟨p + 1, hpm⟩ (by simp only; omega)
      (by simp only; omega)]
    revert h₂; cases s.lbl ⟨p + 1, hpm⟩ <;> simp

end Categorification.Stendhal.CupCap

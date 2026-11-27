/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KPsiCutAct
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KSrcBlocks

/-!
# The mirror images of the generators of `T^λ` at the maximum

Webster, arXiv:1309.3796v3, Lemma 7.19 (K), proof of the inverse `Ψ`: the generators `e(s)`,
`x_a`, `ψ_p` of `T^λ` act on the model of `K̃^{λ⁺}_λ` by multiplication with the diagrams
`midIdem s`, `midDot a`, `midCross p` of `T̃^{λ⁺}` (`midKLRAct_e_tmul_midGen` and its
companions). Their mirror images, cut by the windows at the maximum, are computed here
(`hflip_midDot`, `hflip_midCross`, `hflip_midCrossAt_far_mul_eSum`).

## Main results

* `Stendhal.CupCap.hflip_midCross`: the mirror image of a crossing, cut by the windows.
* `Stendhal.CupCap.hflip_midCrossAt_far_mul_eSum`: away from the maximum it is a crossing of
  `λ⁺`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite InductionAlong
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Diagrams

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "E" s:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s (midPos j s) (midPos_le j s))

theorem hflip_midIdem (s : Seq (stendhalWeight ℓ ν)) :
    hflip (midIdem j hj Q Λ Λc ν ν₀ s) = E s :=
  hflip_eSum_insertSet s (midPos_le j s)

/-- **The mirror image of a dot**, cut by the windows. -/
theorem hflip_midDot (a : Fin m) :
    hflip (midDot j hj Q Λ Λc ν ν₀ a) = ∑ s : Seq (stendhalWeight ℓ ν),
      KLRAlgebra.x (dotPos (j := j) (hj := hj) (ν₀ := ν₀)
        ⟨midPos j s, Nat.lt_succ_of_le (midPos_le j s)⟩ a) * E s := by
  rw [midDot, hflip_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hflip_mul, hflip_x, hflip_eSum_insertSet, eSum_insertSet_mul_x]

/-- **The mirror image of a crossing**, cut by the windows: on the window at `s` it is the mirror
image of the crossing on the loading `s_p s`. -/
theorem hflip_midCross (p : ℕ) :
    hflip (midCross j hj Q Λ Λc ν ν₀ p) = ∑ s : Seq (stendhalWeight ℓ ν),
      hflip (midCrossAt j hj Q Λ Λc ν ν₀ (sadj m p • s) p) * E s := by
  rw [midCross, hflip_sum, ← Equiv.sum_comp (MulAction.toPerm (sadj m p))]
  refine Finset.sum_congr rfl fun s _ => ?_
  have h := eSum_mul_midCrossAt (j := j) (hj := hj) (Q := Q) (Λ := Λ) (Λc := Λc) (ν₀ := ν₀)
    (sadj m p • s) p
  rw [sadj_smul_sadj_smul] at h
  rw [MulAction.toPerm_apply]
  conv_lhs => rw [← h]
  rw [hflip_mul, hflip_eSum_insertSet]

/-- **Away from the maximum, the mirror image of a crossing on the window at `s` is the crossing
of `λ⁺`.** -/
theorem hflip_midCrossAt_far_mul_eSum (s : Seq (stendhalWeight ℓ ν)) {p : ℕ} (hp : p + 1 < m)
    (hf : p + 1 < midPos j s ∨ midPos j s + 1 ≤ p) :
    hflip (midCrossAt j hj Q Λ Λc ν ν₀ (sadj m p • s) p) * E s =
      KLRAlgebra.ψ (crossPos (midPos j s) N p) * E s := by
  have hm := midPos_sadj_of_far j s hp hf
  have hc : crossPos (midPos j (sadj m p • s)) N p = crossPos (midPos j s) N p := by rw [hm]
  have hpf : p + 1 < midPos j s ∨ midPos j s ≤ p := by omega
  rw [midCrossAt_far (sadj m p • s) hp (by omega) (by omega), hflip_mul, hflip_ψ,
    hflip_eSum_insertSet, hc, mul_assoc, ψ_crossPos_mul_eSum s (midPos_le j s) hpf,
    congrArg (KLRAlgebra.eSum _) (insertSet_congr' (sadj m p • s) (midPos_le j s)
      (midPos_le j (sadj m p • s)) hm.symm), ← mul_assoc, (KLRAlgebra.eSum_idem _).eq]

end Diagrams

section Unit

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} (j : ℕ) (hj : j ≤ ℓ)
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  (θ γ ν₀ : Multiset I)
  (Y : Type) [AddCommGroup Y] [Module k Y]
  [Module (cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) Y]
  [IsScalarTower k (cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) Y] (hQ : KLRSymm Q)
  (L' : Type) [AddCommGroup L'] [Module k L']
  [Module (TensorProductAlgebra k Q Λc ν₀) L'] [IsScalarTower k (TensorProductAlgebra k Q Λc ν₀) L']

set_option hygiene false in
local notation "mkp" => TensorProductAlgebra.mk Q (plusLabels Λ Λc j hj) ((θ + γ) + ν₀)
set_option hygiene false in
local notation "botp" => botMap k Q Λ Λc j hj (θ + γ) ν₀
set_option hygiene false in
local notation "Np" => BlocksOneStepInput Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ
  (PlusInput Q Λ Λc j hj θ ν₀ γ (MidSpect (k := k) Y L'))
set_option hygiene false in
local notation "U" y:max v:max =>
  kSrcUnit j hj Q Λ Λc θ γ ν₀ Y hQ L' (show Np from midSpectTmul (k := k) y v)
set_option hygiene false in
local notation "Th" => tensorOfKLR Q (cutLabels j hj Λ ∘ Fin.castAdd (ℓ - j)) θ
set_option hygiene false in
local notation "Tt" => tensorOfKLR Q (cutLabels j hj Λ ∘ Fin.natAdd j) γ
set_option hygiene false in
local notation "mλ" => Multiset.card (stendhalWeight ℓ (θ + γ))
set_option hygiene false in
local notation "nθ" => Multiset.card (stendhalWeight j θ)
set_option hygiene false in
local notation "nγ" => Multiset.card (stendhalWeight (ℓ - j) γ)
set_option hygiene false in
local notation "N₂" => Multiset.card (stendhalWeight 2 ν₀)

omit [DecidableEq I] in
include hj in
theorem card_cut_eq : mλ = nθ + nγ := by
  have hA := card_stendhalWeight (ℓ := j) (ν := θ)
  have hL := card_stendhalWeight (ℓ := ℓ - j) (ν := γ)
  have hT := card_stendhalWeight (ℓ := ℓ) (ν := θ + γ)
  simp only [Multiset.card_add] at hT
  omega

omit [DecidableEq I] in
include hj in
theorem card_plus_eq :
    Multiset.card (stendhalWeight (ℓ + 2) ((θ + γ) + ν₀)) = nθ + (N₂ + nγ) := by
  have hA := card_stendhalWeight (ℓ := j) (ν := θ)
  have hL := card_stendhalWeight (ℓ := ℓ - j) (ν := γ)
  have hT := card_stendhalWeight (ℓ := ℓ + 2) (ν := (θ + γ) + ν₀)
  have h2 := card_stendhalWeight (ℓ := 2) (ν := ν₀)
  simp only [Multiset.card_add] at hT
  omega

/-- **The mirror image of a dot of the first block acts on the unit through `Y`.** -/
theorem kSrc_flip_midDot_head (a : Fin nθ) (b : Fin mλ) (hb : b.val = a.val) (y : Y) (v : L') :
    mkp (botp (hflip (midDot j hj Q Λ Λc (θ + γ) ν₀ b))) • U y v =
      U ((Th (x a) ⊗ₜ[k] 1 : cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) • y) v := by
  have ha : a.val < Multiset.card (stendhalWeight (ℓ + 2) ((θ + γ) + ν₀)) := by
    have := a.2; rw [card_plus_eq j hj θ γ ν₀]; omega
  rw [hflip_midDot, map_sum, map_sum, Finset.sum_smul]
  simp only [map_mul, mul_smul]
  rw [kSrc_window_smul_unit j hj Q Λ Λc θ γ ν₀ Y hQ L' _ (x ⟨a.val, ha⟩) (fun i l hl hv => ?_) y v]
  · exact kSrc_head_x_smul_unit j hj Q Λ Λc θ γ ν₀ Y hQ L' a ⟨a.val, ha⟩ rfl y v
  · refine congrArg x (Fin.ext ?_)
    simp only [dotPos_val', midPos_cutSeq hj i hl hv, hb]
    split_ifs <;> omega

/-- **The mirror image of a dot of the last block acts on the unit through `Y`.** -/
theorem kSrc_flip_midDot_tail (c : Fin nγ) (b : Fin mλ) (hb : b.val = nθ + c.val) (y : Y)
    (v : L') :
    mkp (botp (hflip (midDot j hj Q Λ Λc (θ + γ) ν₀ b))) • U y v =
      U ((1 ⊗ₜ[k] Tt (x c) : cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) • y) v := by
  have hc : nθ + (N₂ + c.val) < Multiset.card (stendhalWeight (ℓ + 2) ((θ + γ) + ν₀)) := by
    have := c.2; rw [card_plus_eq j hj θ γ ν₀]; omega
  rw [hflip_midDot, map_sum, map_sum, Finset.sum_smul]
  simp only [map_mul, mul_smul]
  rw [kSrc_window_smul_unit j hj Q Λ Λc θ γ ν₀ Y hQ L' _ (x ⟨_, hc⟩) (fun i l hl hv => ?_) y v]
  · exact kSrc_tail_x_smul_unit j hj Q Λ Λc θ γ ν₀ Y hQ L' c ⟨_, hc⟩ rfl y v
  · refine congrArg x (Fin.ext ?_)
    simp only [dotPos_val', midPos_cutSeq hj i hl hv, hb]
    split_ifs <;> omega

/-- **The mirror image of a crossing of the first block acts on the unit through `Y`.** -/
theorem kSrc_flip_midCross_head {p : ℕ} (hp : p + 1 < nθ) (y : Y) (v : L') :
    mkp (botp (hflip (midCross j hj Q Λ Λc (θ + γ) ν₀ p))) • U y v =
      U ((Th (ψ p) ⊗ₜ[k] 1 : cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) • y) v := by
  have hpm : p + 1 < mλ := by rw [card_cut_eq j hj θ γ]; omega
  rw [hflip_midCross, map_sum, map_sum, Finset.sum_smul]
  simp only [map_mul, mul_smul]
  rw [kSrc_window_smul_unit' j hj Q Λ Λc θ γ ν₀ Y hQ L' _ (ψ p) (fun i l hl hv => ?_) y v]
  · exact kSrc_head_ψ_smul_unit j hj Q Λ Λc θ γ ν₀ Y hQ L' hp y v
  · have hm := midPos_cutSeq hj i hl hv
    have hcp : crossPos (midPos j (cutSeq hj i l)) N₂ p = p := by
      rw [hm]; simp only [crossPos]; split_ifs <;> omega
    rw [hflip_midCrossAt_far_mul_eSum _ hpm (Or.inl (by omega)), hcp]

/-- **The mirror image of a crossing of the last block acts on the unit through `Y`.** -/
theorem kSrc_flip_midCross_tail {r : ℕ} (hr0 : 0 < r) (hr : r + 1 < nγ) (y : Y) (v : L') :
    mkp (botp (hflip (midCross j hj Q Λ Λc (θ + γ) ν₀ (nθ + r)))) • U y v =
      U ((1 ⊗ₜ[k] Tt (ψ r) : cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) • y) v := by
  have hpm : nθ + r + 1 < mλ := by rw [card_cut_eq j hj θ γ]; omega
  rw [hflip_midCross, map_sum, map_sum, Finset.sum_smul]
  simp only [map_mul, mul_smul]
  rw [kSrc_window_smul_unit' j hj Q Λ Λc θ γ ν₀ Y hQ L' _ (ψ (nθ + (N₂ + r)))
    (fun i l hl hv => ?_) y v]
  · exact kSrc_tail_ψ_smul_unit j hj Q Λ Λc θ γ ν₀ Y hQ L' hr y v
  · have hm := midPos_cutSeq hj i hl hv
    have hcp : crossPos (midPos j (cutSeq hj i l)) N₂ (nθ + r) = nθ + (N₂ + r) := by
      rw [hm]; simp only [crossPos]; split_ifs <;> omega
    rw [hflip_midCrossAt_far_mul_eSum _ hpm (Or.inr (by omega)), hcp]

/-- **The mirror image of the crossing of `λ_{j+1}` with its right neighbour kills the unit.** -/
theorem kSrc_flip_midCross_cut (hr : 1 < nγ) (y : Y) (v : L') :
    mkp (botp (hflip (midCross j hj Q Λ Λc (θ + γ) ν₀ nθ))) • U y v = 0 := by
  have hpm : nθ + 1 < mλ := by rw [card_cut_eq j hj θ γ]; omega
  rw [hflip_midCross, map_sum, map_sum, Finset.sum_smul]
  simp only [map_mul, mul_smul]
  refine Finset.sum_eq_zero fun s _ => ?_
  by_cases hs : ∃ (i : Seq (stendhalWeight j θ)) (l : Seq (stendhalWeight (ℓ - j) γ)),
      IsRedOrdered l ∧ ¬ IsViolated l ∧ s = cutSeq hj i l
  swap
  · rw [kSrc_window_smul_unit_of_bad j hj Q Λ Λc θ γ ν₀ Y hQ L' s hs, smul_zero]
  obtain ⟨i, l, hl, hv, rfl⟩ := hs
  have hm := midPos_cutSeq hj i hl hv
  have hm' := midPos_sadj_right (j := j) (cutSeq hj i l) hpm hm.symm
  rcases hlb : (sadj mλ nθ • cutSeq hj i l).lbl ⟨nθ, by omega⟩ with b | rr
  · rw [midCrossAt_left (sadj mλ nθ • cutSeq hj i l) hpm hm'.symm hlb, hflip_mul, hflip_mul,
      hflip_ψ, hflip_eSum_insertSet, ← mul_smul, ← map_mul, ← map_mul]
    have hcp : crossPos (midPos j (cutSeq hj i l)) N₂ nθ = nθ + N₂ := by
      rw [hm]; simp only [crossPos]; split_ifs <;> omega
    rw [mul_assoc, mul_assoc (hflip (underLeft N₂ nθ)), ← hcp,
      ψ_crossPos_mul_eSum _ (midPos_le j _) (Or.inr hm.le)]
    simp only [← mul_assoc]
    rw [map_mul, map_mul, mul_smul, hcp]
    have h0 : mkp (botp (ψ (nθ + N₂))) • U y v = 0 :=
      kSrc_tail_ψ_zero_smul_unit j hj Q Λ Λc θ γ ν₀ Y hQ L' hr y v
    rw [h0, smul_zero]
  · rw [midCrossAt_left_red (sadj mλ nθ • cutSeq hj i l) hpm hm'.symm hlb, hflip_zero, map_zero,
      map_zero, zero_smul]

end Unit

end Categorification.Stendhal.CupCap

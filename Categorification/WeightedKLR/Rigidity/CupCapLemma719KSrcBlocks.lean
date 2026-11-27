/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KSrcMid
import Categorification.WeightedKLR.Rigidity.CupCapMidRelBraidCases

/-!
# The outer blocks acting on the unit of the right side

Webster, arXiv:1309.3796v3, Lemma 7.19 (K), proof of the inverse `Ψ`: the dots and crossings of
the outer blocks `λ_1, …, λ_j` and `λ_{j+1}, …, λ_ℓ` of `λ⁺` act on the unit `1 ⊗ (y ⊠ v)` of
`S_+(Y ⊠ L')` through their action on `Y` (`kSrc_head_x_smul_unit`, `kSrc_head_ψ_smul_unit`,
`kSrc_tail_x_smul_unit`, `kSrc_tail_ψ_smul_unit`). The crossing of the first two strands vanishes
in every Stendhal algebra (`tensorOfKLR_ψ_zero`), since the leftmost strand of a nonviolated
loading is red.

## Main results

* `Stendhal.CupCap.tensorOfKLR_ψ_zero`: `ψ_0 = 0` in `T^λ`.
* `Stendhal.CupCap.kSrc_head_tail_smul_unit`: the outer blocks act on the unit through `Y`.
* `Stendhal.CupCap.kSrc_window_smul_unit'`: the window decomposition of the unit, for diagrams
  agreeing with a fixed one on the windows with a good tail.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Vanishing

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}
  {ℓ' : ℕ} {Λ' : Fin ℓ' → I →₀ ℕ} {ν' : Multiset I}

omit [DecidableEq I] in
/-- Crossing the first two strands of a nonviolated red-ordered loading gives a violated or
red-unordered loading. -/
theorem sadj_zero_smul_bad {l : Seq (stendhalWeight ℓ' ν')}
    (hm : 1 < Multiset.card (stendhalWeight ℓ' ν')) (hl : IsRedOrdered l ∧ ¬ IsViolated l) :
    ¬ (IsRedOrdered (sadj (Multiset.card (stendhalWeight ℓ' ν')) 0 • l) ∧
      ¬ IsViolated (sadj (Multiset.card (stendhalWeight ℓ' ν')) 0 • l)) := by
  rintro ⟨ho, hv⟩
  obtain ⟨r, hr⟩ : ∃ r, l.lbl ⟨0, by omega⟩ = .inr r := by
    rcases hc : l.lbl ⟨0, by omega⟩ with b | r
    · exact absurd ⟨by omega, by rw [hc]; rfl⟩ hl.2
    · exact ⟨r, rfl⟩
  have h0 := lbl_sadj_self l (q := 0) hm
  have h1 := lbl_sadj_succ l (q := 0) hm
  rcases hc : l.lbl ⟨0 + 1, hm⟩ with b | r'
  · exact hv ⟨by omega, by rw [h0, hc]; rfl⟩
  · have hlt := hl.1 ⟨0, by omega⟩ ⟨0 + 1, hm⟩ r r' (Fin.mk_lt_mk.2 (by omega)) hr hc
    have hlt' := ho ⟨0, by omega⟩ ⟨0 + 1, hm⟩ r' r (Fin.mk_lt_mk.2 (by omega)) (h0.trans hc)
      (h1.trans hr)
    exact lt_asymm hlt hlt'

theorem tensorOfKLR_e_of_bad {l : Seq (stendhalWeight ℓ' ν')}
    (hl : ¬ (IsRedOrdered l ∧ ¬ IsViolated l)) : tensorOfKLR Q Λ' ν' (e l) = 0 := by
  by_cases ho : IsRedOrdered l
  · exact tensorOfKLR_e_of_isViolated (not_not.1 fun h => hl ⟨ho, h⟩)
  · exact tensorOfKLR_e_of_not_isRedOrdered ho

/-- **The crossing of the first two strands vanishes in `T^λ`**: the leftmost strand of a
nonviolated loading is red, so crossing it with its neighbour gives a violated or red-unordered
loading. -/
theorem tensorOfKLR_ψ_zero : tensorOfKLR Q Λ' ν' (ψ 0) = 0 := by
  classical
  by_cases hm : 1 < Multiset.card (stendhalWeight ℓ' ν')
  swap
  · rw [ψ_eq_zero 0 (by omega)]
    simp only [tensorOfKLR, map_zero]
  have hmul : ∀ a b : KLRAlgebra k (stendhalQ Q Λ') (stendhalWeight ℓ' ν'),
      tensorOfKLR Q Λ' ν' (a * b) = tensorOfKLR Q Λ' ν' a * tensorOfKLR Q Λ' ν' b := fun a b => by
    simp only [tensorOfKLR, map_mul]
  have hsum : ∀ (F : Seq (stendhalWeight ℓ' ν') → KLRAlgebra k (stendhalQ Q Λ')
      (stendhalWeight ℓ' ν')), tensorOfKLR Q Λ' ν' (∑ l, F l) =
        ∑ l, tensorOfKLR Q Λ' ν' (F l) := fun F => by
    simp only [tensorOfKLR, map_sum]
  rw [← mul_one (ψ 0), ← sum_e, Finset.mul_sum, hsum]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : IsRedOrdered l ∧ ¬ IsViolated l
  · rw [ψ_mul_e, hmul, tensorOfKLR_e_of_bad (sadj_zero_smul_bad hm hl), zero_mul]
  · rw [hmul, tensorOfKLR_e_of_bad hl, mul_zero]

end Vanishing

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} (j : ℕ) (hj : j ≤ ℓ)
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  (θ γ ν₀ : Multiset I)
  (Y : Type) [AddCommGroup Y] [Module k Y]
  [Module (cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) Y]
  [IsScalarTower k (cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) Y] (hQ : KLRSymm Q)
  (L' : Type) [AddCommGroup L'] [Module k L']
  [Module (TensorProductAlgebra k Q Λc ν₀) L'] [IsScalarTower k (TensorProductAlgebra k Q Λc ν₀) L']

set_option hygiene false in
local notation "Xs" => KCutSrc j hj Q Λ Λc θ γ ν₀ Y hQ L'
set_option hygiene false in
local notation "mkp" => TensorProductAlgebra.mk Q (plusLabels Λ Λc j hj) ((θ + γ) + ν₀)
set_option hygiene false in
local notation "botp" => botMap k Q Λ Λc j hj (θ + γ) ν₀
set_option hygiene false in
local notation "Np" => BlocksOneStepInput Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ
  (PlusInput Q Λ Λc j hj θ ν₀ γ (MidSpect (k := k) Y L'))
set_option hygiene false in
local notation "Pt" => kSrcPart j hj Q Λ Λc θ γ ν₀ Y hQ L'
set_option hygiene false in
local notation "U" y:max v:max =>
  kSrcUnit j hj Q Λ Λc θ γ ν₀ Y hQ L' (show Np from midSpectTmul (k := k) y v)
set_option hygiene false in
local notation "Rp" => KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj))
  (stendhalWeight (ℓ + 2) ((θ + γ) + ν₀))
set_option hygiene false in
local notation "Sp" => stendhalQ Q (plusBlockLabels Λ Λc j hj)
set_option hygiene false in
local notation "Λt" => blocksTailLabels (plusBlockLabels Λ Λc j hj)
set_option hygiene false in
local notation "Ws" s:max => KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
  (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s (midPos j s) (midPos_le j s))
set_option hygiene false in
local notation "Th" => tensorOfKLR Q (cutLabels j hj Λ ∘ Fin.castAdd (ℓ - j)) θ
set_option hygiene false in
local notation "Tt" => tensorOfKLR Q (cutLabels j hj Λ ∘ Fin.natAdd j) γ

/-- **The outer blocks act on the unit through `Y`.** -/
theorem kSrc_head_tail_smul_unit
    (a : KLRAlgebra k (stendhalQ Q (plusBlockLabels Λ Λc j hj ∘ Fin.castAdd (2 + (ℓ - j))))
      (stendhalWeight j θ))
    (c : KLRAlgebra k (stendhalQ Q (Λt ∘ Fin.natAdd 2)) (stendhalWeight (ℓ - j) γ))
    (y : Y) (v : L') :
    kSrcUnit j hj Q Λ Λc θ γ ν₀ Y hQ L' ((plusHeadEmb j hj Q Λ Λc θ a ⊗ₜ[k]
      (plusMidEmb j hj Q Λ Λc ν₀ 1 ⊗ₜ[k] plusTailEmb j hj Q Λ Λc γ c)) •
        (show Np from midSpectTmul (k := k) y v)) =
      U ((relabelTensorProductAlgebra Q (plusBlockLabels_head Λ Λc j hj) θ
            (tensorOfKLR Q _ θ a) ⊗ₜ[k]
          relabelTensorProductAlgebra Q (plusBlockLabels_tail Λ Λc j hj) γ
            (tensorOfKLR Q _ γ c) : cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) • y) v := by
  rw [plusInput_tmul_smul]
  erw [relabel_tensorOfKLR_one, one_smul]

/-- **The dots of the first block act on the unit through `Y`.** -/
theorem kSrc_head_x_smul_unit (a : Fin (Multiset.card (stendhalWeight j θ)))
    (a' : Fin (Multiset.card (stendhalWeight (ℓ + 2) ((θ + γ) + ν₀)))) (ha : a'.val = a.val)
    (y : Y) (v : L') :
    mkp (botp (x a')) • U y v =
      U ((Th (x a) ⊗ₜ[k] 1 : cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) • y) v := by
  have hφ : plusHeadEmb j hj Q Λ Λc θ (x a) = x (Fin.cast (Multiset.card_map _ _).symm a) := by
    rw [AlgEquiv.coe_toAlgHom, relabelEquiv_apply, relabelHom_x]
  have key := kSrcUnit_isInd3InputHom j hj Q Λ Λc θ γ ν₀ Y hQ L'
    (plusHeadEmb j hj Q Λ Λc θ (x a) ⊗ₜ[k]
      (plusMidEmb j hj Q Λ Λc ν₀ 1 ⊗ₜ[k] plusTailEmb j hj Q Λ Λc γ 1))
    (show Np from midSpectTmul (k := k) y v)
  rw [kSrc_head_tail_smul_unit] at key
  erw [relabel_tensorOfKLR_x Q (Λ₂ := cutLabels j hj Λ ∘ Fin.castAdd (ℓ - j))
      (plusBlockLabels_head Λ Λc j hj) θ a, relabel_tensorOfKLR_one] at key
  rw [key, map_one, map_one, ← Algebra.TensorProduct.one_def, hφ, concat3_x_tmul_one, map_mul,
    Module.End.mul_apply, kSrc_oneConcat3,
    kSrcOneStepRep_x j hj Q Λ Λc θ γ ν₀ Y hQ L' _ a' (by simp [Seq.posL, ha])]

/-- **The crossings of the first block act on the unit through `Y`.** -/
theorem kSrc_head_ψ_smul_unit {p : ℕ} (hp : p + 1 < Multiset.card (stendhalWeight j θ))
    (y : Y) (v : L') :
    mkp (botp (ψ p)) • U y v =
      U ((Th (ψ p) ⊗ₜ[k] 1 : cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) • y) v := by
  have hφ : plusHeadEmb j hj Q Λ Λc θ (ψ p) = ψ p := by
    rw [AlgEquiv.coe_toAlgHom, relabelEquiv_apply, relabelHom_ψ]
  have key := kSrcUnit_isInd3InputHom j hj Q Λ Λc θ γ ν₀ Y hQ L'
    (plusHeadEmb j hj Q Λ Λc θ (ψ p) ⊗ₜ[k]
      (plusMidEmb j hj Q Λ Λc ν₀ 1 ⊗ₜ[k] plusTailEmb j hj Q Λ Λc γ 1))
    (show Np from midSpectTmul (k := k) y v)
  rw [kSrc_head_tail_smul_unit] at key
  erw [relabel_tensorOfKLR_ψ Q (Λ₂ := cutLabels j hj Λ ∘ Fin.castAdd (ℓ - j))
      (plusBlockLabels_head Λ Λc j hj) θ p, relabel_tensorOfKLR_one] at key
  rw [key, map_one, map_one, ← Algebra.TensorProduct.one_def, hφ,
    concat3_ψ_tmul_one (by rw [Multiset.card_map]; exact hp), map_mul,
    Module.End.mul_apply, kSrc_oneConcat3, kSrcOneStepRep_ψ]

/-- **The dots of the last block act on the unit through `Y`.** -/
theorem kSrc_tail_x_smul_unit (c : Fin (Multiset.card (stendhalWeight (ℓ - j) γ)))
    (c' : Fin (Multiset.card (stendhalWeight (ℓ + 2) ((θ + γ) + ν₀))))
    (hc : c'.val = Multiset.card (stendhalWeight j θ) +
      (Multiset.card (stendhalWeight 2 ν₀) + c.val)) (y : Y) (v : L') :
    mkp (botp (x c')) • U y v =
      U ((1 ⊗ₜ[k] Tt (x c) : cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) • y) v := by
  have hφ : plusTailEmb j hj Q Λ Λc γ (x c) =
      x (Fin.cast (Multiset.card_map _ _).symm (Fin.cast (Multiset.card_map _ _).symm c)) := by
    simp only [plusTailEmb, plusTailEmb₀, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      relabelEquiv_apply, relabelHom_x]
  have key := kSrcUnit_isInd3InputHom j hj Q Λ Λc θ γ ν₀ Y hQ L'
    (plusHeadEmb j hj Q Λ Λc θ 1 ⊗ₜ[k]
      (plusMidEmb j hj Q Λ Λc ν₀ 1 ⊗ₜ[k] plusTailEmb j hj Q Λ Λc γ (x c)))
    (show Np from midSpectTmul (k := k) y v)
  rw [kSrc_head_tail_smul_unit] at key
  erw [relabel_tensorOfKLR_x Q (Λ₂ := cutLabels j hj Λ ∘ Fin.natAdd j)
      (plusBlockLabels_tail Λ Λc j hj) γ c, relabel_tensorOfKLR_one] at key
  rw [key, map_one, map_one, hφ, concat3_one_tmul_one_tmul_x, map_mul,
    Module.End.mul_apply, kSrc_oneConcat3,
    kSrcOneStepRep_x j hj Q Λ Λc θ γ ν₀ Y hQ L' _ c' (by simp [Seq.posR, hc])]

/-- **The crossings of the last block act on the unit through `Y`.** -/
theorem kSrc_tail_ψ_smul_unit {r : ℕ} (hr : r + 1 < Multiset.card (stendhalWeight (ℓ - j) γ))
    (y : Y) (v : L') :
    mkp (botp (ψ (Multiset.card (stendhalWeight j θ) +
        (Multiset.card (stendhalWeight 2 ν₀) + r)))) • U y v =
      U ((1 ⊗ₜ[k] Tt (ψ r) : cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) • y) v := by
  have hφ : plusTailEmb j hj Q Λ Λc γ (ψ r) = ψ r := by
    simp only [plusTailEmb, plusTailEmb₀, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      relabelEquiv_apply, relabelHom_ψ]
  have key := kSrcUnit_isInd3InputHom j hj Q Λ Λc θ γ ν₀ Y hQ L'
    (plusHeadEmb j hj Q Λ Λc θ 1 ⊗ₜ[k]
      (plusMidEmb j hj Q Λ Λc ν₀ 1 ⊗ₜ[k] plusTailEmb j hj Q Λ Λc γ (ψ r)))
    (show Np from midSpectTmul (k := k) y v)
  rw [kSrc_head_tail_smul_unit] at key
  erw [relabel_tensorOfKLR_ψ Q (Λ₂ := cutLabels j hj Λ ∘ Fin.natAdd j)
      (plusBlockLabels_tail Λ Λc j hj) γ r, relabel_tensorOfKLR_one] at key
  rw [key, map_one, map_one, hφ,
    concat3_one_tmul_one_tmul_ψ (by simp only [Multiset.card_map]; exact hr), map_mul,
    Module.End.mul_apply, kSrc_oneConcat3, kSrcOneStepRep_ψ]
  simp only [Multiset.card_map]

/-- **The crossing of `λ_{j+1}` with its right neighbour vanishes on the unit.** -/
theorem kSrc_tail_ψ_zero_smul_unit (hr : 1 < Multiset.card (stendhalWeight (ℓ - j) γ))
    (y : Y) (v : L') :
    mkp (botp (ψ (Multiset.card (stendhalWeight j θ) +
        (Multiset.card (stendhalWeight 2 ν₀) + 0)))) • U y v = 0 := by
  rw [kSrc_tail_ψ_smul_unit j hj Q Λ Λc θ γ ν₀ Y hQ L' (r := 0) (by omega), tensorOfKLR_ψ_zero,
    TensorProduct.tmul_zero]
  erw [zero_smul (cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) y, midSpectTmul_zero_left]
  exact map_zero _

/-- A window at a loading that is not `i ⊔ l` with a good tail kills the unit. -/
theorem kSrc_window_smul_unit_of_bad (s : Seq (stendhalWeight ℓ (θ + γ)))
    (hs : ¬ ∃ (i : Seq (stendhalWeight j θ)) (l : Seq (stendhalWeight (ℓ - j) γ)),
      IsRedOrdered l ∧ ¬ IsViolated l ∧ s = cutSeq hj i l) (y : Y) (v : L') :
    mkp (botp (Ws s)) • U y v = 0 := by
  rw [kSrc_eSum_insertSet_smul_unit]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun l _ => ?_
  split_ifs with h
  · refine Finset.sum_eq_zero fun w _ => kSrcPart_eq_zero_of_bad j hj Q Λ Λc θ γ ν₀ Y hQ L' i w
      (fun hl => hs ⟨i, l, hl.1, hl.2, h⟩) y v
  · rfl

/-- **Diagrams cut by the windows at the maximum act on the unit through their value at the
cut**, for diagrams that agree with `G` on each window with a good tail. -/
theorem kSrc_window_smul_unit' (F : Seq (stendhalWeight ℓ (θ + γ)) → Rp) (G : Rp)
    (hF : ∀ (i : Seq (stendhalWeight j θ)) (l : Seq (stendhalWeight (ℓ - j) γ)),
      IsRedOrdered l → ¬ IsViolated l →
        F (cutSeq hj i l) * Ws (cutSeq hj i l) = G * Ws (cutSeq hj i l)) (y : Y) (v : L') :
    ∑ s : Seq (stendhalWeight ℓ (θ + γ)), mkp (botp (F s)) • mkp (botp (Ws s)) • U y v =
      mkp (botp G) • U y v := by
  have key : ∀ s, mkp (botp (F s)) • mkp (botp (Ws s)) • U y v =
      mkp (botp G) • mkp (botp (Ws s)) • U y v := fun s => by
    by_cases hs : ∃ (i : Seq (stendhalWeight j θ)) (l : Seq (stendhalWeight (ℓ - j) γ)),
        IsRedOrdered l ∧ ¬ IsViolated l ∧ s = cutSeq hj i l
    · obtain ⟨i, l, h1, h2, rfl⟩ := hs
      rw [← mul_smul, ← map_mul, ← map_mul, hF i l h1 h2, map_mul, map_mul, mul_smul]
    · rw [kSrc_window_smul_unit_of_bad j hj Q Λ Λc θ γ ν₀ Y hQ L' s hs, smul_zero, smul_zero]
  rw [Finset.sum_congr rfl fun s _ => key s]
  exact kSrc_window_smul_unit j hj Q Λ Λc θ γ ν₀ Y hQ L' (fun _ => G) G (fun _ _ _ _ => rfl) y v

omit [DecidableEq I] in
/-- **The loading `i ⊔ l` determines `i` and `l`.** -/
theorem cutSeq_inj {i i' : Seq (stendhalWeight j θ)} {l l' : Seq (stendhalWeight (ℓ - j) γ)}
    (h : cutSeq hj i l = cutSeq hj i' l') : i = i' ∧ l = l' := by
  have hA := card_stendhalWeight (ℓ := j) (ν := θ)
  have hL := card_stendhalWeight (ℓ := ℓ - j) (ν := γ)
  have hT := card_stendhalWeight (ℓ := ℓ) (ν := θ + γ)
  simp only [Multiset.card_add] at hT
  have hinj₁ : Function.Injective (fun z : I ⊕ Fin j => Sum.map id
      (Fin.cast (Nat.add_sub_of_le hj)) (Sum.map id (Fin.castAdd (ℓ - j)) z)) :=
    (Sum.map_injective.2 ⟨Function.injective_id, Fin.cast_injective _⟩).comp
      (Sum.map_injective.2 ⟨Function.injective_id, Fin.castAdd_injective _ _⟩)
  have hinj₂ : Function.Injective (fun z : I ⊕ Fin (ℓ - j) => Sum.map id
      (Fin.cast (Nat.add_sub_of_le hj)) (Sum.map id (Fin.natAdd j) z)) :=
    (Sum.map_injective.2 ⟨Function.injective_id, Fin.cast_injective _⟩).comp
      (Sum.map_injective.2 ⟨Function.injective_id, Fin.natAdd_injective _ _⟩)
  constructor
  · refine Subtype.ext (funext fun b => ?_)
    have hb : b.val < Multiset.card (stendhalWeight ℓ (θ + γ)) := by have := b.2; omega
    have hc : (cutSeq hj i l).1 ⟨b.val, hb⟩ = (cutSeq hj i' l').1 ⟨b.val, hb⟩ := by rw [h]
    rw [cutSeq_apply_lt hj i l _ b.val rfl b.2, cutSeq_apply_lt hj i' l' _ b.val rfl b.2] at hc
    exact hinj₁ hc
  · refine Subtype.ext (funext fun b => ?_)
    have hb : b.val + Multiset.card (stendhalWeight j θ) <
        Multiset.card (stendhalWeight ℓ (θ + γ)) := by have := b.2; omega
    have hc : (cutSeq hj i l).1 ⟨_, hb⟩ = (cutSeq hj i' l').1 ⟨_, hb⟩ := by rw [h]
    rw [cutSeq_apply_ge hj i l _ b.val rfl, cutSeq_apply_ge hj i' l' _ b.val rfl] at hc
    exact hinj₂ hc

/-- **The idempotents of the blocks act on the unit through the window at `i ⊔ l`.** -/
theorem kSrc_e_cut_smul_unit (i : Seq (stendhalWeight j θ)) (l : Seq (stendhalWeight (ℓ - j) γ))
    (y : Y) (v : L') :
    U ((Th (e i) ⊗ₜ[k] Tt (e l) : cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) • y) v =
      mkp (botp (Ws (cutSeq hj i l))) • U y v := by
  have h1 : (plusMidEmb j hj Q Λ Λc ν₀ 1) =
      ∑ w : Seq (stendhalWeight 2 ν₀), plusMidEmb j hj Q Λ Λc ν₀ (e w) := by
    rw [← map_sum, sum_e]
  have hL : U ((Th (e i) ⊗ₜ[k] Tt (e l) : cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) • y) v =
      ∑ w : Seq (stendhalWeight 2 ν₀), Pt i w l y v := by
    have key := kSrc_head_tail_smul_unit j hj Q Λ Λc θ γ ν₀ Y hQ L' (e i) (e l) y v
    erw [relabel_tensorOfKLR_e Q (Λ₂ := cutLabels j hj Λ ∘ Fin.castAdd (ℓ - j))
        (plusBlockLabels_head Λ Λc j hj) θ i,
      relabel_tensorOfKLR_e Q (Λ₂ := cutLabels j hj Λ ∘ Fin.natAdd j)
        (plusBlockLabels_tail Λ Λc j hj) γ l] at key
    rw [← key, h1, TensorProduct.sum_tmul, TensorProduct.tmul_sum, Finset.sum_smul, map_sum]
    rfl
  rw [hL, kSrc_eSum_insertSet_smul_unit,
    Fintype.sum_eq_single i (fun i' hi' => Finset.sum_eq_zero fun l' _ =>
      ite_eq_right_iff.2 fun h => absurd (cutSeq_inj j hj θ γ h).1.symm hi'),
    Fintype.sum_eq_single l (fun l' hl' =>
      ite_eq_right_iff.2 fun h => absurd (cutSeq_inj j hj θ γ h).2.symm hl'),
    ite_eq_left_of_eq_true _ _ (eq_self _)]

end Categorification.Stendhal.CupCap

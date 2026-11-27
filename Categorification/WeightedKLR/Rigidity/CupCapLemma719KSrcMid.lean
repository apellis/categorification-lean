/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KSrcWindow

/-!
# Diagrams at the maximum acting on the unit of the right side

Webster, arXiv:1309.3796v3, Lemma 7.19 (K), proof of the inverse `Ψ`: a diagram `x` of
`T̃^{(μ,μ*)}` placed at the maximum `midPos` acts on the unit `1 ⊗ (y ⊠ v)` of `S_+(Y ⊠ L')` as
`x` acts on `L'` (`kSrc_midBot_e_smul_unit`, `kSrc_midBot_x_smul_unit`,
`kSrc_midBot_ψ_smul_unit`). This is the balance of the inverse over the cups and caps.

## Main results

* `Stendhal.CupCap.kSrc_window_smul_unit`: diagrams cut by the windows at the maximum act on the
  unit through their value at the cut.
* `Stendhal.CupCap.kSrc_mid_smul_unit`: the middle block acts on the unit through `L'`.
* `Stendhal.CupCap.kSrc_midBot_e_smul_unit`, `Stendhal.CupCap.kSrc_midBot_x_smul_unit`,
  `Stendhal.CupCap.kSrc_midBot_ψ_smul_unit`: the generators at the maximum.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

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

/-- **The unit is the sum of its parts at the block loadings.** -/
theorem kSrcPart_sum (y : Y) (v : L') :
    ∑ i : Seq (stendhalWeight j θ), ∑ l : Seq (stendhalWeight (ℓ - j) γ),
      ∑ w : Seq (stendhalWeight 2 ν₀), Pt i w l y v = U y v := by
  conv_rhs => rw [kSrcUnit_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun w _ => ?_
  rw [kSrc_e_plusCutSeq_smul_unit]
  rfl

/-- **Diagrams cut by the windows at the maximum act on the unit through their value at the
cut**: if `F s` equals `G` at every loading `i ⊔ l` with a good tail, then
`∑_s F(s) E_s` acts on the unit as `G`. -/
theorem kSrc_window_smul_unit (F : Seq (stendhalWeight ℓ (θ + γ)) → Rp) (G : Rp)
    (hF : ∀ (i : Seq (stendhalWeight j θ)) (l : Seq (stendhalWeight (ℓ - j) γ)),
      IsRedOrdered l → ¬ IsViolated l → F (cutSeq hj i l) = G) (y : Y) (v : L') :
    ∑ s : Seq (stendhalWeight ℓ (θ + γ)), mkp (botp (F s)) • mkp (botp (Ws s)) • U y v =
      mkp (botp G) • U y v := by
  simp only [kSrc_eSum_insertSet_smul_unit, Finset.smul_sum, smul_ite, smul_zero]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun i _ => ?_).trans
    (by rw [← kSrcPart_sum, Finset.smul_sum])
  rw [Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  by_cases hl : IsRedOrdered l ∧ ¬ IsViolated l
  · rw [hF i l hl.1 hl.2, Finset.smul_sum]
  · simp only [kSrcPart_eq_zero_of_bad j hj Q Λ Λc θ γ ν₀ Y hQ L' _ _ hl, smul_zero,
      Finset.sum_const_zero]

/-- **The middle block acts on the unit through `L'`.** -/
theorem kSrc_mid_smul_unit
    (b : KLRAlgebra k (stendhalQ Q (Λt ∘ Fin.castAdd (ℓ - j))) (stendhalWeight 2 ν₀))
    (y : Y) (v : L') :
    kSrcUnit j hj Q Λ Λc θ γ ν₀ Y hQ L' (((1 : KLRAlgebra k Sp
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ))) ⊗ₜ[k]
      (plusMidEmb j hj Q Λ Λc ν₀ b ⊗ₜ[k] (1 : KLRAlgebra k Sp
        (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
        (Multiset.map (Sum.map (id : I → I) (Fin.natAdd 2)) (stendhalWeight (ℓ - j) γ)))))) •
        (show Np from midSpectTmul (k := k) y v)) =
      U y (relabelTensorProductAlgebra Q (plusBlockLabels_cup Λ Λc j hj) ν₀
        (tensorOfKLR Q _ ν₀ b) • v) := by
  have h1' : (1 : KLRAlgebra k Sp
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ))) ⊗ₜ[k]
      (plusMidEmb j hj Q Λ Λc ν₀ b ⊗ₜ[k] (1 : KLRAlgebra k Sp
        (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
        (Multiset.map (Sum.map (id : I → I) (Fin.natAdd 2)) (stendhalWeight (ℓ - j) γ))))) =
      plusHeadEmb j hj Q Λ Λc θ 1 ⊗ₜ[k]
        (plusMidEmb j hj Q Λ Λc ν₀ b ⊗ₜ[k] plusTailEmb j hj Q Λ Λc γ 1) := by
    rw [map_one, map_one]
  rw [h1', plusInput_tmul_smul]
  erw [relabel_tensorOfKLR_one, relabel_tensorOfKLR_one, ← Algebra.TensorProduct.one_def,
    one_smul]

/-- **The idempotents at the maximum act on the unit through `L'`.** -/
theorem kSrc_midBot_e_smul_unit (w : Seq (stendhalWeight 2 ν₀)) (y : Y) (v : L') :
    mkp (midBot j hj Q Λ Λc (θ + γ) ν₀ (e w)) • U y v = U y (tensorOfKLR Q Λc ν₀ (e w) • v) := by
  rw [← relabel_tensorOfKLR_e Q (plusBlockLabels_cup Λ Λc j hj) ν₀ w, ← kSrc_mid_smul_unit,
    one_tmul_e_tmul_one_eq_sum (plusHeadEmb j hj Q Λ Λc θ) (plusMidEmb j hj Q Λ Λc ν₀)
      (plusTailEmb j hj Q Λ Λc γ) w, midBot_apply, midMapKLR]
  simp only [insertMap_e, map_sum, Finset.sum_smul, kSrc_e_insertSeq_smul_unit]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  rfl

/-- **The dots at the maximum act on the unit through `L'`.** -/
theorem kSrc_midBot_x_smul_unit (b : Fin (Multiset.card (stendhalWeight 2 ν₀))) (y : Y)
    (v : L') :
    mkp (midBot j hj Q Λ Λc (θ + γ) ν₀ (x b)) • U y v = U y (tensorOfKLR Q Λc ν₀ (x b) • v) := by
  have hφ : plusMidEmb j hj Q Λ Λc ν₀ (x b) =
      x (Fin.cast (Multiset.card_map _ _).symm (Fin.cast (Multiset.card_map _ _).symm b)) := by
    simp only [plusMidEmb, plusMidEmb₀, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      relabelEquiv_apply, relabelHom_x]
  have hb := add_lt_M (I := I) (ν₀ := ν₀) (Nat.lt_succ_iff.1 (cutPos j hj θ γ).2) b
  erw [← relabel_tensorOfKLR_x Q (plusBlockLabels_cup Λ Λc j hj) ν₀ b]
  rw [← kSrc_mid_smul_unit, kSrcUnit_isInd3InputHom, hφ, concat3_one_tmul_x_tmul_one, map_mul,
    Module.End.mul_apply, kSrc_oneConcat3,
    kSrcOneStepRep_x j hj Q Λ Λc θ γ ν₀ Y hQ L' _ ⟨_, hb⟩ (by simp [Seq.posR, Seq.posL]),
    midBot_apply, midMapKLR]
  simp only [insertMap_x, map_sum, map_mul, Finset.sum_smul, mul_smul]
  refine kSrc_window_smul_unit j hj Q Λ Λc θ γ ν₀ Y hQ L' _ _ (fun i l hl hv => ?_) y v
  exact congrArg x (Fin.ext (by simp [midPos_cutSeq hj i hl hv]))

/-- **The crossings at the maximum act on the unit through `L'`.** -/
theorem kSrc_midBot_ψ_smul_unit (q : ℕ) (y : Y) (v : L') :
    mkp (midBot j hj Q Λ Λc (θ + γ) ν₀ (ψ q)) • U y v = U y (tensorOfKLR Q Λc ν₀ (ψ q) • v) := by
  by_cases hq : q + 1 < Multiset.card (stendhalWeight 2 ν₀)
  swap
  · have h0 : (show Np from midSpectTmul (k := k) y (0 : L')) = 0 := TensorProduct.tmul_zero _ _
    have ht : tensorOfKLR Q Λc ν₀ (0 : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) = 0 :=
      by simp only [tensorOfKLR, map_zero]
    rw [ψ_eq_zero q (by omega), map_zero, map_zero, zero_smul, ht,
      zero_smul (TensorProductAlgebra k Q Λc ν₀) v, h0, map_zero]
  have hφ : plusMidEmb j hj Q Λ Λc ν₀ (ψ q) = ψ q := by
    simp only [plusMidEmb, plusMidEmb₀, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      relabelEquiv_apply, relabelHom_ψ]
  erw [← relabel_tensorOfKLR_ψ Q (plusBlockLabels_cup Λ Λc j hj) ν₀ q]
  rw [← kSrc_mid_smul_unit, kSrcUnit_isInd3InputHom, hφ,
    concat3_one_tmul_ψ_tmul_one (by simp only [Multiset.card_map]; exact hq), map_mul,
    Module.End.mul_apply, kSrc_oneConcat3, kSrcOneStepRep_ψ, Multiset.card_map, midBot_apply,
    midMapKLR]
  simp only [insertMap_ψ _ _ hq, map_sum, map_mul, Finset.sum_smul, mul_smul]
  refine kSrc_window_smul_unit j hj Q Λ Λc θ γ ν₀ Y hQ L' _ _ (fun i l hl hv => ?_) y v
  rw [midPos_cutSeq hj i hl hv]

theorem kSrcU_add (y : Y) (v v' : L') : U y (v + v') = U y v + U y v' := by
  rw [← map_add]
  exact congrArg (kSrcUnit j hj Q Λ Λc θ γ ν₀ Y hQ L') (TensorProduct.tmul_add y v v')

theorem kSrcU_smul (y : Y) (c : k) (v : L') : U y (c • v) = c • U y v := by
  rw [← map_smul]
  exact congrArg (kSrcUnit j hj Q Λ Λc θ γ ν₀ Y hQ L') (TensorProduct.tmul_smul c y v)

theorem tensorOfKLR_add' (a b : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) :
    tensorOfKLR Q Λc ν₀ (a + b) = tensorOfKLR Q Λc ν₀ a + tensorOfKLR Q Λc ν₀ b := by
  simp only [tensorOfKLR, map_add]

theorem tensorOfKLR_mul' (a b : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) :
    tensorOfKLR Q Λc ν₀ (a * b) = tensorOfKLR Q Λc ν₀ a * tensorOfKLR Q Λc ν₀ b := by
  simp only [tensorOfKLR, map_mul]

theorem tensorOfKLR_smul' (c : k) (a : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) :
    tensorOfKLR Q Λc ν₀ (c • a) = c • tensorOfKLR Q Λc ν₀ a := by
  simp only [tensorOfKLR, map_smul]

/-- **Every diagram at the maximum acts on the unit as it acts on `L'`.** -/
theorem kSrc_midBot_smul_unit (g : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀))
    (y : Y) (v : L') :
    mkp (midBot j hj Q Λ Λc (θ + γ) ν₀ g) • U y v = U y (tensorOfKLR Q Λc ν₀ g • v) := by
  let P : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀) → Prop := fun g =>
    ∀ (y : Y) (v : L'),
      mkp (midBot j hj Q Λ Λc (θ + γ) ν₀ g) • U y v = U y (tensorOfKLR Q Λc ν₀ g • v)
  have hadd : ∀ a b, P a → P b → P (a + b) := fun a b ha hb y v => by
    rw [map_add, map_add, add_smul, ha, hb, tensorOfKLR_add', add_smul, kSrcU_add]
  have hmul : ∀ a b, P a → P b → P (a * b) := fun a b ha hb y v => by
    rw [map_mul, map_mul, mul_smul, hb, ha, tensorOfKLR_mul', mul_smul]
  have hsmul : ∀ (c : k) a, P a → P (c • a) := fun c a ha y v => by
    rw [map_smul, map_smul, smul_assoc, ha, tensorOfKLR_smul', smul_assoc, kSrcU_smul]
  have hzero : P 0 := fun y v => by
    have h0 : (show Np from midSpectTmul (k := k) y (0 : L')) = 0 := TensorProduct.tmul_zero _ _
    have ht : tensorOfKLR Q Λc ν₀ (0 : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) = 0 :=
      by simp only [tensorOfKLR, map_zero]
    rw [map_zero, map_zero, zero_smul, ht, zero_smul (TensorProductAlgebra k Q Λc ν₀) v, h0,
      map_zero]
  have he : ∀ w, P (e w) := fun w => kSrc_midBot_e_smul_unit j hj Q Λ Λc θ γ ν₀ Y hQ L' w
  have hone : P 1 := by
    rw [← sum_e]
    exact Finset.sum_induction _ P hadd hzero fun w _ => he w
  let S : Subalgebra k (KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) :=
    { carrier := {g | P g}
      mul_mem' := fun {a b} => hmul a b
      add_mem' := fun {a b} => hadd a b
      algebraMap_mem' := fun c => by
        rw [Algebra.algebraMap_eq_smul_one]
        exact hsmul c 1 hone }
  exact mem_of_gens (AlgHom.id k _) S he
    (fun b => kSrc_midBot_x_smul_unit j hj Q Λ Λc θ γ ν₀ Y hQ L' b)
    (fun q => kSrc_midBot_ψ_smul_unit j hj Q Λ Λc θ γ ν₀ Y hQ L' q) g y v

end Categorification.Stendhal.CupCap

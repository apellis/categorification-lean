/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KPsiCutSlides
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KCutInputGen

/-!
# The family `y ↦ f_y` intertwines the two blocks of `λ`

Webster, arXiv:1309.3796v3, Lemma 7.19 (K), proof of the inverse `Ψ`: for a pair `t` of
juxtaposed affine diagrams of the two blocks of `λ`, `f_{t y} = f_y(· t)`. This is the
intertwining condition that lets `y ↦ f_y` extend over the partial standardization `S_cut Y`.

## Main results

* `Stendhal.CupCap.isCutInputHom_kCapFamily`: the intertwining condition for `y ↦ f_y`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite InductionAlong
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {θ γ ν₀ : Multiset I}
  (Y : Type) [AddCommGroup Y] [Module k Y]
  [Module (cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) Y]
  [IsScalarTower k (cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) Y] (hQ : KLRSymm Q)
  {L' : Type} [AddCommGroup L'] [Module k L']
  [Module (TensorProductAlgebra k Q Λc ν₀) L'] [IsScalarTower k (TensorProductAlgebra k Q Λc ν₀) L']

set_option hygiene false in
local notation "Np" => BlocksOneStepInput Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ
  (PlusInput Q Λ Λc j hj θ ν₀ γ (MidSpect (k := k) Y L'))
set_option hygiene false in
local notation "U" y:max v:max =>
  kSrcUnit j hj Q Λ Λc θ γ ν₀ Y hQ L' (show Np from midSpectTmul (k := k) y v)
set_option hygiene false in
local notation "Lc" => CapCoef Q Λc ν₀ L'
set_option hygiene false in
local notation "mkp" => TensorProductAlgebra.mk Q (plusLabels Λ Λc j hj) ((θ + γ) + ν₀)
set_option hygiene false in
local notation "botp" => botMap k Q Λ Λc j hj (θ + γ) ν₀
set_option hygiene false in
local notation "Rp" => KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj))
  (stendhalWeight (ℓ + 2) ((θ + γ) + ν₀))
set_option hygiene false in
local notation "Rλ" => KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ (θ + γ))
set_option hygiene false in
local notation "Sc" => stendhalQ Q (cutLabels j hj Λ)
set_option hygiene false in
local notation "αc" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j)))
  (stendhalWeight j θ)
set_option hygiene false in
local notation "δc" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
  (stendhalWeight (ℓ - j) γ)
set_option hygiene false in
local notation "cast_c" => castLabelsTensorProductAlgebra Q (Nat.add_sub_of_le hj) Λ (θ + γ)
set_option hygiene false in
local notation "Th" => tensorOfKLR Q (cutLabels j hj Λ ∘ Fin.castAdd (ℓ - j)) θ
set_option hygiene false in
local notation "Tt" => tensorOfKLR Q (cutLabels j hj Λ ∘ Fin.natAdd j) γ
set_option hygiene false in
local notation "nθ" => Multiset.card (stendhalWeight j θ)
set_option hygiene false in
local notation "nγ" => Multiset.card (stendhalWeight (ℓ - j) γ)

variable {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : Lc), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}
  (hR : MidKLRRel j hj Q Λ Λc (θ + γ) ν₀ Lc hL)
  (hP : PullOff k Q Λc ν₀ Lc) (hPL : PullOffLeft k Q Λc ν₀ Lc)
  (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))

variable (j hj Q Λ Λc θ γ ν₀ L') in
/-- **The action of `T^λ` on the maps out of the reflected cap**, through the labels of the cut. -/
abbrev kCutHomRepCut :=
  (kCutHomRep j hj Q Λ Λc θ γ ν₀ Y hQ L').comp (cast_c).toAlgHom

set_option hygiene false in
local notation "σc" => kCutHomRepCut j hj Q Λ Λc θ γ ν₀ Y hQ L'
set_option hygiene false in
local notation "fF" => kCapFamily Y hQ hR hP hPL hκ

/-- **The reduction of the intertwining condition to a slide**: if `g` is a diagram of `λ` at the
cut whose relabelling is `a`, the mirror image of `a` slides through the model as `Y₀`, and the
mirror image of `Y₀` takes the unit at `y` to the unit at `t y`, then `f_{t y} = g · f_y`. -/
theorem kCapFamily_smul_of_slide (t : cutFactorAlgebra Q (cutLabels j hj Λ) θ γ)
    (g : TensorProductAlgebra k Q (cutLabels j hj Λ) (θ + γ)) (a : Rλ) (Y₀ : Rp)
    (hcast : cast_c g = TensorProductAlgebra.mk Q Λ (θ + γ) (topMap k Q Λ (θ + γ) a))
    (ha : ∀ (Z : Rp) (v : Lc), midKLRAct hR (hflip a)
        (Ind.tmul (midGen j hj Q Λ Λc (θ + γ) ν₀ (botp Z)) v) =
      Ind.tmul (midGen j hj Q Λ Λc (θ + γ) ν₀ (botp (Y₀ * Z))) v)
    (hU : ∀ (y : Y) (v : L'), U (t • y) v = mkp (botp (hflip Y₀)) • U y v) (y : Y) :
    fF (t • y) = σc g (fF y) := by
  refine LinearMap.ext fun r => ?_
  change kCapLin Y hQ hR hP hPL hκ (t • y) r =
    kCapLin Y hQ hR hP hPL hκ y (op (cast_c g) • r)
  rw [hcast]
  exact kCapLin_op_mk_smul_of_slide Y hQ hR hP hPL hκ y (t • y) a Y₀ ha (hU y) r

set_option hygiene false in
local notation "IC" => IsCutAt Q (cutLabels j hj Λ) θ γ σc fF

/-- **The pairs of idempotents of the two blocks.** -/
theorem kCapFamily_isCutAt_e (i : Seq (stendhalWeight j θ)) (l : Seq (stendhalWeight (ℓ - j) γ)) :
    IC ((cutHeadEmb j hj Q Λ θ).toAlgHom (e i) ⊗ₜ[k] (cutTailEmb j hj Q Λ γ).toAlgHom (e l)) :=
    fun y => by
  have hcat : concat Sc αc δc
      (cutHeadEmb j hj Q Λ θ (e i) ⊗ₜ[k] cutTailEmb j hj Q Λ γ (e l)) =
      e ((Seq.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) i).append
        (Seq.map (Sum.map (id : I → I) (Fin.natAdd j)) l)) := by
    rw [relabelEquiv_apply, relabelEquiv_apply, relabelHom_e, relabelHom_e, concat_e_tmul_e]
    rfl
  change fF (cutInputMap Q (cutLabels j hj Λ) θ γ
      (cutHeadEmb j hj Q Λ θ (e i) ⊗ₜ[k] cutTailEmb j hj Q Λ γ (e l)) • y) =
    σc (cutAffineMap Q (cutLabels j hj Λ) θ γ (concat Sc αc δc
      (cutHeadEmb j hj Q Λ θ (e i) ⊗ₜ[k] cutTailEmb j hj Q Λ γ (e l)))) (fF y)
  rw [hcat, cutInputMap_emb]
  refine kCapFamily_smul_of_slide Y hQ hR hP hPL hκ _ _ (e (cutSeq hj i l))
    (midIdem j hj Q Λ Λc (θ + γ) ν₀ (cutSeq hj i l))
    (cast_c_cutAffineMap_e j hj Q Λ θ γ _ (cutSeq hj i l)
      (fun p q hpq => (castLabelsSeq_lbl _ _ _ p).trans (congrArg _ (Seq.apply_congr _
        (by simp [hpq]))))) (fun Z v => ?_) (fun y v => ?_) y
  · rw [hflip_e, midKLRAct_e, midEnd_tmul_midGen Lc hL, map_mul]
  · rw [hflip_midIdem]
    exact kSrc_e_cut_smul_unit j hj Q Λ Λc θ γ ν₀ Y hQ L' i l y v

/-- **The dots of the first block.** -/
theorem kCapFamily_isCutAt_head_x (h1 : IC 1) (a : Fin nθ) :
    IC ((cutHeadEmb j hj Q Λ θ).toAlgHom (x a) ⊗ₜ (1 : KLRAlgebra k Sc δc)) := by
  have hb : a.val < Multiset.card (stendhalWeight ℓ (θ + γ)) := by
    have := a.2; rw [card_cut_eq j hj θ γ]; omega
  have ht : (cutHeadEmb j hj Q Λ θ).toAlgHom (x a) ⊗ₜ (1 : KLRAlgebra k Sc δc) =
      cutHeadEmb j hj Q Λ θ (x a) ⊗ₜ[k] cutTailEmb j hj Q Λ γ 1 := by
    rw [map_one]; rfl
  rw [ht]
  refine isCutAt_of_concat_eq σc fF h1 _
    (x (Seq.posL _ (Fin.cast (Multiset.card_map _ _).symm a)))
    (by rw [map_one, relabelEquiv_apply, relabelHom_x, concat_x_tmul_one]) fun y => ?_
  rw [cutInputMap_emb, tensorOfKLR_one]
  exact kCapFamily_smul_of_slide Y hQ hR hP hPL hκ _ _ (x ⟨a.val, hb⟩)
    (midDot j hj Q Λ Λc (θ + γ) ν₀ ⟨a.val, hb⟩)
    (cast_c_cutAffineMap_x j hj Q Λ θ γ _ ⟨a.val, hb⟩ rfl)
    (fun Z v => by rw [hflip_x, midKLRAct_x, midEnd_tmul_midGen Lc hL, map_mul])
    (fun y v => (kSrc_flip_midDot_head j hj Q Λ Λc θ γ ν₀ Y hQ L' a ⟨a.val, hb⟩ rfl y v).symm) y

/-- **The crossings of the first block.** -/
theorem kCapFamily_isCutAt_head_ψ (h1 : IC 1) (p : ℕ) :
    IC ((cutHeadEmb j hj Q Λ θ).toAlgHom (ψ p) ⊗ₜ (1 : KLRAlgebra k Sc δc)) := by
  by_cases hp : p + 1 < nθ
  swap
  · rw [ψ_eq_zero p (by omega), map_zero, TensorProduct.zero_tmul]
    exact IsCutAt.zero σc fF
  have ht : (cutHeadEmb j hj Q Λ θ).toAlgHom (ψ p) ⊗ₜ (1 : KLRAlgebra k Sc δc) =
      cutHeadEmb j hj Q Λ θ (ψ p) ⊗ₜ[k] cutTailEmb j hj Q Λ γ 1 := by
    rw [map_one]; rfl
  rw [ht]
  refine isCutAt_of_concat_eq σc fF h1 _ (ψ p)
    (by rw [map_one, relabelEquiv_apply, relabelHom_ψ,
      KLRAlgebra.concat_ψ_tmul_one (by rw [Multiset.card_map]; exact hp)]) fun y => ?_
  rw [cutInputMap_emb, tensorOfKLR_one]
  exact kCapFamily_smul_of_slide Y hQ hR hP hPL hκ _ _ (ψ p)
    (midCross j hj Q Λ Λc (θ + γ) ν₀ p) (cast_c_cutAffineMap_ψ j hj Q Λ θ γ p)
    (fun Z v => by rw [hflip_ψ, midKLRAct_ψ, midEnd_tmul_midGen Lc hL, map_mul])
    (fun y v => (kSrc_flip_midCross_head j hj Q Λ Λc θ γ ν₀ Y hQ L' hp y v).symm) y

/-- **The dots of the last block.** -/
theorem kCapFamily_isCutAt_tail_x (h1 : IC 1) (c : Fin nγ) :
    IC ((1 : KLRAlgebra k Sc αc) ⊗ₜ (cutTailEmb j hj Q Λ γ).toAlgHom (x c)) := by
  have hb : nθ + c.val < Multiset.card (stendhalWeight ℓ (θ + γ)) := by
    have := c.2; rw [card_cut_eq j hj θ γ]; omega
  have ht : (1 : KLRAlgebra k Sc αc) ⊗ₜ (cutTailEmb j hj Q Λ γ).toAlgHom (x c) =
      cutHeadEmb j hj Q Λ θ 1 ⊗ₜ[k] cutTailEmb j hj Q Λ γ (x c) := by
    rw [map_one]; rfl
  rw [ht]
  refine isCutAt_of_concat_eq σc fF h1 _
    (x (Seq.posR _ (Fin.cast (Multiset.card_map _ _).symm c)))
    (by rw [map_one, relabelEquiv_apply, relabelHom_x, KLRAlgebra.concat_one_tmul_x])
    fun y => ?_
  rw [cutInputMap_emb, tensorOfKLR_one]
  exact kCapFamily_smul_of_slide Y hQ hR hP hPL hκ _ _ (x ⟨_, hb⟩)
    (midDot j hj Q Λ Λc (θ + γ) ν₀ ⟨_, hb⟩)
    (cast_c_cutAffineMap_x j hj Q Λ θ γ _ ⟨_, hb⟩ (by simp))
    (fun Z v => by rw [hflip_x, midKLRAct_x, midEnd_tmul_midGen Lc hL, map_mul])
    (fun y v => (kSrc_flip_midDot_tail j hj Q Λ Λc θ γ ν₀ Y hQ L' c ⟨_, hb⟩ rfl y v).symm) y

/-- **The crossings of the last block**; the crossing `ψ_0` of the red strand `λ_{j+1}` with
its right neighbour vanishes on both sides. -/
theorem kCapFamily_isCutAt_tail_ψ (h1 : IC 1) (r : ℕ) :
    IC ((1 : KLRAlgebra k Sc αc) ⊗ₜ (cutTailEmb j hj Q Λ γ).toAlgHom (ψ r)) := by
  by_cases hr : r + 1 < nγ
  swap
  · rw [ψ_eq_zero r (by omega), map_zero, TensorProduct.tmul_zero]
    exact IsCutAt.zero σc fF
  have ht : (1 : KLRAlgebra k Sc αc) ⊗ₜ (cutTailEmb j hj Q Λ γ).toAlgHom (ψ r) =
      cutHeadEmb j hj Q Λ θ 1 ⊗ₜ[k] cutTailEmb j hj Q Λ γ (ψ r) := by
    rw [map_one]; rfl
  rw [ht]
  refine isCutAt_of_concat_eq σc fF h1 _ (ψ (nθ + r))
    (by rw [map_one, relabelEquiv_apply, relabelHom_ψ,
      KLRAlgebra.concat_one_tmul_ψ (by simp only [Multiset.card_map]; exact hr),
      Multiset.card_map]) fun y => ?_
  rw [cutInputMap_emb, tensorOfKLR_one]
  refine kCapFamily_smul_of_slide Y hQ hR hP hPL hκ _ _ (ψ (nθ + r))
    (midCross j hj Q Λ Λc (θ + γ) ν₀ (nθ + r)) (cast_c_cutAffineMap_ψ j hj Q Λ θ γ _)
    (fun Z v => by rw [hflip_ψ, midKLRAct_ψ, midEnd_tmul_midGen Lc hL, map_mul])
    (fun y v => ?_) y
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · have h0 : (0 : cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) • y = (0 : k) • y := by
      rw [zero_smul (cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) y, zero_smul k y]
    rw [tensorOfKLR_ψ_zero, TensorProduct.tmul_zero, h0,
      kSrcU_smul_left j hj Q Λ Λc θ γ ν₀ Y hQ L', zero_smul]
    exact (kSrc_flip_midCross_cut j hj Q Λ Λc θ γ ν₀ Y hQ L' hr y v).symm
  · exact (kSrc_flip_midCross_tail j hj Q Λ Λc θ γ ν₀ Y hQ L' hr0 hr y v).symm

/-- **`y ↦ f_y` intertwines the two blocks of `λ`** (Webster, arXiv:1309.3796v3, proof of
Lemma 7.19 (K)): `f_{t y} = f_y(· t)` for juxtaposed affine diagrams `t` of the two blocks. -/
theorem isCutInputHom_kCapFamily :
    IsCutInputHom Q (cutLabels j hj Λ) θ γ Y σc fF := by
  have hE := kCapFamily_isCutAt_e Y hQ hR hP hPL hκ
  have h1 := isCutAt_one_of_e σc fF _ _ hE
  exact isCutInputHom_of_gens σc fF _ _ (AlgEquiv.surjective _) (AlgEquiv.surjective _) hE
    (kCapFamily_isCutAt_head_x Y hQ hR hP hPL hκ h1)
    (kCapFamily_isCutAt_head_ψ Y hQ hR hP hPL hκ h1)
    (kCapFamily_isCutAt_tail_x Y hQ hR hP hPL hκ h1)
    (kCapFamily_isCutAt_tail_ψ Y hQ hR hP hPL hκ h1)

end Categorification.Stendhal.CupCap

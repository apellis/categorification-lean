/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapTraceCutLeadingLoading
import Categorification.WeightedKLR.Rigidity.CupCapTraceCutHeadCorner

/-!
# The corner of the window loading in the leading layer of `S_+(X)`

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half, step L5 (the corner
`e(l⁺_w) · Lay⁺` as the image of the cut corner).

For a loading `s` with the head condition, `l` the cut loading and `l⁺_w` the window loading,
`Ξ_{q₁}` carries `e(pre l) ⊗ e(suf l)` to `e(l)` on the layer `0` of the induced model of
`S_cut(Res X)` (`indMackeyLeftMap_cutLoading_e_smul`). The identity-shuffle span at the cut is
stable under `e(pre l) ⊗ e(suf l)` (`exists_cutLoading_smul_topOneSpan`). As `e(l⁺_w)` is an
idempotent on the layers (`indMackeyLayerAct_e_idem`) whose corner lies in the leading summand
(`range_indMackeyLayerAct_windowLoading_le`), `leadingLayerSpanEquiv_e_smul` identifies the
corner `e(l⁺_w) · Lay⁺` exactly with the images under `leadingLayerSpanEquiv` of
`Ξ_{q₁}(e(l) · ε_{e(w)} y)` (`mem_range_indMackeyLayerAct_windowLoading_iff`).

The window factor `ε_{e(w)}` acts on `Res X` through the idempotent `e_w = e(w)` of the middle
tensor product algebra `T^{Λc}(ν₀)`: the image of `e(w̃)` there is `e_w`
(`relabel_cutPrefixProjection_e_window`, `plusWindowEnd_e_eq`), so `ε_{e(w)}` is an idempotent
(`plusWindowEnd_e_idem`) whose image is the corner `e_w · Res X`.

Webster's proof does not spell this out. No new hypothesis.

## Main results

* `KLR.KLRAlgebra.indMackeyLayerAct_e_idem`.
* `Stendhal.CupCap.indMackeyLeftMap_cutLoading_e_smul`,
  `Stendhal.CupCap.exists_cutLoading_smul_topOneSpan`,
  `Stendhal.CupCap.mem_range_indMackeyLayerAct_windowLoading_iff`.
* `Stendhal.CupCap.relabel_cutPrefixProjection_e_window`, `Stendhal.CupCap.plusWindowEnd_e_eq`,
  `Stendhal.CupCap.plusMidEnd_mul`, `Stendhal.CupCap.plusWindowEnd_e_idem`.
-/

noncomputable section

namespace Categorification.KLR.KLRAlgebra

open TypeA
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {ν'' ν''' : Multiset I}
  (N : Type*) [AddCommGroup N] [Module k N] [Module (TensorKLR Q ν'' ν''') N]

/-- A loading idempotent acts on the layers of `Ind N` as an idempotent. -/
theorem indMackeyLayerAct_e_idem (σ : Seq (ν'' + ν''')) {n : ℕ} (c : ℕ)
    (w : IndMackeyLayer Q ν'' ν''' N n c) :
    indMackeyLayerAct N (e σ : KLRAlgebra k Q (ν'' + ν'''))
        (fun _ _ hy => e_mul_mem_mackeyFilt _ hy) c
        (indMackeyLayerAct N (e σ : KLRAlgebra k Q (ν'' + ν'''))
          (fun _ _ hy => e_mul_mem_mackeyFilt _ hy) c w) =
      indMackeyLayerAct N (e σ : KLRAlgebra k Q (ν'' + ν'''))
        (fun _ _ hy => e_mul_mem_mackeyFilt _ hy) c w := by
  rw [indMackeyLayerAct_mul]
  exact LinearMap.congr_fun (indMackeyLayerAct_congr N c (e_mul_self σ) _ _) w

end Categorification.KLR.KLRAlgebra

namespace Categorification.Stendhal

open KLR KLRAlgebra

/-- Relabelling `T^{Λ₁}(ν)` along `Λ₁ = Λ₂` fixes the images of loading idempotents. -/
theorem relabelTensorProductAlgebra_tensorOfKLR_e {I k : Type*} [DecidableEq I] [CommRing k]
    (Q : I → I → MvPolynomial (Fin 2) k) {n : ℕ} {Λ₁ Λ₂ : Fin n → I →₀ ℕ} (hΛ : Λ₁ = Λ₂)
    (ν : Multiset I) (t : Seq (stendhalWeight n ν)) :
    relabelTensorProductAlgebra Q hΛ ν (tensorOfKLR Q Λ₁ ν (e t)) =
      tensorOfKLR Q Λ₂ ν (e t) := by
  subst hΛ
  rfl

end Categorification.Stendhal

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA
open scoped TensorProduct

section Window

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {θ γ ν₀ : Multiset I}

local notation "Sc" => stendhalQ Q (cutLabels j hj Λ)

attribute [local instance] botCornerModuleRight botCornerModuleRight_isScalarTower

/-- **The window idempotent in the middle block**: the image of `e(w̃)` (the window loading
`w` read in the inner labels) in `T^{Λc}(ν₀)` is the loading idempotent `e_w`. -/
theorem relabel_cutPrefixProjection_e_window (w : Seq (stendhalWeight 2 ν₀)) :
    relabelTensorProductAlgebra Q (plusBlockLabels_cup Λ Λc j hj) ν₀
        (cutPrefixProjection (a := 2) (r := ℓ - j) Q (blocksTailLabels (plusBlockLabels Λ Λc j hj))
          ν₀ (e (Seq.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) w))) =
      tensorOfKLR Q Λc ν₀ (e w) := by
  rw [cutPrefixProjection_e_map]
  exact relabelTensorProductAlgebra_tensorOfKLR_e Q _ ν₀ w

omit [DecidableEq I] in
/-- The loading idempotents of `T^{Λc}(ν₀)` are idempotents. -/
theorem tensorOfKLR_e_mul_self [DecidableEq I] (w : Seq (stendhalWeight 2 ν₀)) :
    tensorOfKLR Q Λc ν₀ (e w) * tensorOfKLR Q Λc ν₀ (e w) = tensorOfKLR Q Λc ν₀ (e w) := by
  simp only [tensorOfKLR, ← map_mul, e_mul_self]

variable (X : Type*) [AddCommGroup X] [Module k X]
  [Module (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X]
  [IsScalarTower k (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X]

local notation "Yc" => CutInput Q (cutLabels j hj Λ) θ γ (PlusRes j hj Q Λ Λc θ γ ν₀ X)

omit [Module k X] [IsScalarTower k (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X] in
/-- The middle block acts on `Res X` multiplicatively. -/
theorem plusMidEnd_mul (u u' : TensorProductAlgebra k Q Λc ν₀)
    (x : PlusRes j hj Q Λ Λc θ γ ν₀ X) :
    plusMidEnd X u (plusMidEnd X u' x) = plusMidEnd X (u * u') x := by
  change (((1 : TensorProductAlgebra k Q (Λ ∘ Fin.castLE hj) θ) ⊗ₜ
      (u ⊗ₜ (1 : TensorProductAlgebra k Q (plusTailLabels Λ j hj) γ)) :
      PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) •
      (((1 : TensorProductAlgebra k Q (Λ ∘ Fin.castLE hj) θ) ⊗ₜ
      (u' ⊗ₜ (1 : TensorProductAlgebra k Q (plusTailLabels Λ j hj) γ)) :
      PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) • (show X from x)) : X) =
    (((1 : TensorProductAlgebra k Q (Λ ∘ Fin.castLE hj) θ) ⊗ₜ
      ((u * u') ⊗ₜ (1 : TensorProductAlgebra k Q (plusTailLabels Λ j hj) γ)) :
      PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) • (show X from x) : X)
  rw [smul_smul, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul, one_mul]

variable (s : Seq (stendhalWeight ℓ (θ + γ))) (w : Seq (stendhalWeight 2 ν₀))
  (q' : MackeyQuad (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
        (midPos_le_card_cut s))
      (Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s))
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ))
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)))

/-- **`ε_{e(w)}` is the action of `e_w`** (Webster v3, Lemma 7.19, trace half, step L5): the
window factor of the window loading `w` acts on `E' · Res X` through the loading idempotent
`e_w` of the middle block `T^{Λc}(ν₀)`. -/
theorem plusWindowEnd_e_eq :
    plusWindowEnd X s q' (e (Seq.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) w)) =
      botCornerEnd q' Yc (cutInputHom (a := j) (r := ℓ - j) Q (cutLabels j hj Λ) θ γ
        (plusMidEnd X (tensorOfKLR Q Λc ν₀ (e w)))) := by
  rw [plusWindowEnd, relabel_cutPrefixProjection_e_window]

/-- **`ε_{e(w)}` is an idempotent** on `E' · Res X`. -/
theorem plusWindowEnd_e_idem (z : botCorner Sc q' Yc) :
    plusWindowEnd X s q' (e (Seq.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) w))
        (plusWindowEnd X s q' (e (Seq.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) w)) z) =
      plusWindowEnd X s q' (e (Seq.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) w)) z := by
  rw [plusWindowEnd_e_eq]
  apply Subtype.ext
  exact (plusMidEnd_mul X _ _ (show PlusRes j hj Q Λ Λc θ γ ν₀ X from (z : Yc))).trans
    (congrArg (fun u => plusMidEnd X u (show PlusRes j hj Q Λ Λc θ γ ν₀ X from (z : Yc)))
      (tensorOfKLR_e_mul_self w))

end Window

section Range

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {θ γ ν₀ : Multiset I}

local notation "Sc" => stendhalQ Q (cutLabels j hj Λ)
local notation "Sp" => stendhalQ Q (plusBlockLabels Λ Λc j hj)

attribute [local instance] botCornerModuleRight botCornerModuleRight_isScalarTower

variable (X : Type) [AddCommGroup X] [Module k X]
  [Module (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X]
  [IsScalarTower k (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X] (hQ : KLRSymm Q)

local notation "Yc" => CutInput Q (cutLabels j hj Λ) θ γ (PlusRes j hj Q Λ Λc θ γ ν₀ X)
local notation "Nₒ" => CutInput Q (plusBlockLabels Λ Λc j hj) θ (ν₀ + γ)
  (BlocksMid Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ (PlusInput Q Λ Λc j hj θ ν₀ γ X) hQ)

variable (s : Seq (stendhalWeight ℓ (θ + γ))) (w : Seq (stendhalWeight 2 ν₀))

local notation "preC" => Seq.prefixSeq (cutLoading j hj θ γ s) (midPos j s + 0)
  (midPos_le_card_cut s)
local notation "sufC" => Seq.suffixSeq (cutLoading j hj θ γ s) (midPos j s + 0)
  (midPos_le_card_cut s)
local notation "wP" => Seq.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) w
local notation "LayP" => IndMackeyLayer Sp
  (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ))
  (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (2 + (ℓ - j)) (ν₀ + γ)))
  Nₒ (Multiset.card (Seq.prefixWt (windowLoading j hj θ γ ν₀ s w)
    (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s)))
  (Multiset.card (stendhalWeight 2 ν₀))

omit [IsScalarTower k (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X] in
/-- **The cut side at the layer level** (Webster v3, Lemma 7.19, trace half, step L5): `Ξ_{q₁}`
carries `e(pre l) ⊗ e(suf l)` to the action of the cut loading `e(l)` on the layer `0` of the
induced model of `S_cut(Res X)`. -/
theorem indMackeyLeftMap_cutLoading_e_smul 
    (q₁ : {q : MackeyQuad (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
          (midPos_le_card_cut s))
          (Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s))
          (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ))
          (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)) //
            Multiset.card q.β = 0})
    (v : MackeyLeftInd Sc Yc q₁.1) :
    indMackeyLeftMap (Q := Sc)
        (Seq.prefixWt_add_suffixWt (cutLoading j hj θ γ s) _ (midPos_le_card_cut s)).symm
        Yc q₁.1 q₁.2
        (((e preC : KLRAlgebra k Sc _) ⊗ₜ (e sufC : KLRAlgebra k Sc _) : TensorKLR Sc _ _) • v) =
      indMackeyLayerAct Yc (e (cutLoading j hj θ γ s))
        (fun _ _ hy => e_mul_mem_mackeyFilt _ hy) 0
        (indMackeyLeftMap (Q := Sc)
          (Seq.prefixWt_add_suffixWt (cutLoading j hj θ γ s) _ (midPos_le_card_cut s)).symm
          Yc q₁.1 q₁.2 v) :=
  indMackeyLeftMap_e_smul Yc (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s)
    q₁.1 q₁.2 v

/-- **The identity-shuffle span at the cut is stable under `e(l)`**: for the cut loading `l`,
`(e(pre l) ⊗ e(suf l)) · T'(x)` lies in `mackeyTopOneSpan`. -/
theorem exists_cutLoading_smul_topOneSpan
    (q' : MackeyQuad (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
        (midPos_le_card_cut s))
      (Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s))
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ))
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)))
    (hq' : q'.β = 0) (x : Ind Sc q'.γ q'.δ (botCorner Sc q' Yc)) :
    ∃ y' : mackeyTopOneSpan (Q := Sc) q' Yc, (y' : MackeyLeftInd Sc Yc q') =
      (((e preC : KLRAlgebra k Sc _) ⊗ₜ (e sufC : KLRAlgebra k Sc _) : TensorKLR Sc _ _) •
        (topOneCornerEquiv q' Yc (stendhalQ_symm Q (cutLabels j hj Λ) hQ) x :
          MackeyLeftInd Sc Yc q')) := by
  have hel : ((e preC : KLRAlgebra k Sc _) ⊗ₜ (e sufC : KLRAlgebra k Sc _) : TensorKLR Sc _ _) =
      castAlg Sc q'.h₁ (concat Sc q'.α q'.β (castAlg Sc (leadingQuad'_α_eq s q' hq')
        (e preC : KLRAlgebra k Sc _) ⊗ₜ (1 : KLRAlgebra k Sc q'.β))) ⊗ₜ
      castAlg Sc q'.h₂ (castAlg Sc q'.h₂.symm (e sufC : KLRAlgebra k Sc _)) := by
    rw [castAlg_concat_e_prefixSeq_cutLoading s q' hq', castAlg_castAlg_symm]
  refine ⟨topOneCornerEquiv q' Yc (stendhalQ_symm Q (cutLabels j hj Λ) hQ)
    (castAlg Sc q'.h₂.symm (e sufC : KLRAlgebra k Sc _) • BalancedTensor.mapRight
      (botCornerLeftEnd q' Yc (castAlg Sc (leadingQuad'_α_eq s q' hq')
        (e preC : KLRAlgebra k Sc _) ⊗ₜ (1 : KLRAlgebra k Sc q'.β))) x), ?_⟩
  refine Eq.symm (Eq.trans (congrArg (fun t : TensorKLR Sc _ _ => t •
    (topOneCornerEquiv q' Yc (stendhalQ_symm Q (cutLabels j hj Λ) hQ) x :
      MackeyLeftInd Sc Yc q')) hel) ?_)
  exact topOneCornerEquiv_tmul_smul q' Yc (stendhalQ_symm Q (cutLabels j hj Λ) hQ) _ _ x

/-- **The identity-shuffle span at the cut is stable under `e(l)` after `ε_{e(w)}`**: the form
of `exists_cutLoading_smul_topOneSpan` used for (T_w). -/
theorem exists_cutLoading_window_smul_topOneSpan
    (q' : MackeyQuad (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
        (midPos_le_card_cut s))
      (Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s))
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ))
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)))
    (hq' : q'.β = 0) (y : mackeyTopOneSpan (Q := Sc) q' Yc) :
    ∃ y' : mackeyTopOneSpan (Q := Sc) q' Yc, (y' : MackeyLeftInd Sc Yc q') =
      (((e preC : KLRAlgebra k Sc _) ⊗ₜ (e sufC : KLRAlgebra k Sc _) : TensorKLR Sc _ _) •
        (topOneCornerEquiv q' Yc (stendhalQ_symm Q (cutLabels j hj Λ) hQ)
          (BalancedTensor.mapRight (plusWindowEnd X s q' (e wP))
            ((topOneCornerEquiv q' Yc (stendhalQ_symm Q (cutLabels j hj Λ) hQ)).symm y)) :
          MackeyLeftInd Sc Yc q')) :=
  exists_cutLoading_smul_topOneSpan X hQ s q' hq' _

/-- An element of the leading summand fixed by `e(l⁺_w)` is the image of
`Ξ_{q₁}(e(l) · T'(Ind ε_{e(w)} (T'⁻¹ y)))`. -/
theorem exists_leadingLayerSpanEquiv_cutLoading_eq (hsc : KLRSymm Sc) (hsp : KLRSymm Sp)
    (hs : ∀ a : Fin (Multiset.card (stendhalWeight ℓ (θ + γ))), a.val < midPos j s →
      ∀ u : Fin ℓ, s.lbl a = .inr u → u.val < j)
    (q₀ : {q : MackeyQuad (Seq.prefixWt (windowLoading j hj θ γ ν₀ s w)
          (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
          (Seq.suffixWt (windowLoading j hj θ γ ν₀ s w)
          (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
          (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ))
          (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
          (stendhalWeight (2 + (ℓ - j)) (ν₀ + γ))) //
            Multiset.card q.β = Multiset.card (stendhalWeight 2 ν₀)})
    (hq₀ : q₀.1.β = (stendhalWeight 2 ν₀).map (windowColour j hj))
    (q₁ : {q : MackeyQuad (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
          (midPos_le_card_cut s))
          (Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s))
          (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ))
          (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)) //
            Multiset.card q.β = 0})
    (hq₁ : q₁.1.β = 0) (z : LayP) (y : mackeyTopOneSpan (Q := Sc) q₁.1 Yc)
    (hz : (leadingLayerSpanEquiv X hQ hsc hsp s w hs q₀ hq₀ q₁ hq₁
      (Submodule.equivMapOfInjective _
        (indMackeyLeftMap_injective_of_klrSymm _ Yc hsc q₁) _ y)).1 = z)
    (hzz : indMackeyLayerAct Nₒ (e (windowLoading j hj θ γ ν₀ s w))
        (fun _ _ hy => e_mul_mem_mackeyFilt _ hy) (Multiset.card (stendhalWeight 2 ν₀)) z = z) :
      ∃ y y' : mackeyTopOneSpan (Q := Sc) q₁.1 Yc,
        (y' : MackeyLeftInd Sc Yc q₁.1) =
          (((e preC : KLRAlgebra k Sc _) ⊗ₜ (e sufC : KLRAlgebra k Sc _) : TensorKLR Sc _ _) •
            (topOneCornerEquiv q₁.1 Yc (stendhalQ_symm Q (cutLabels j hj Λ) hQ)
              (BalancedTensor.mapRight (plusWindowEnd X s q₁.1 (e wP))
                ((topOneCornerEquiv q₁.1 Yc (stendhalQ_symm Q (cutLabels j hj Λ) hQ)).symm y)) :
              MackeyLeftInd Sc Yc q₁.1)) ∧
        (leadingLayerSpanEquiv X hQ hsc hsp s w hs q₀ hq₀ q₁ hq₁
          (Submodule.equivMapOfInjective _
            (indMackeyLeftMap_injective_of_klrSymm _ Yc hsc q₁) _ y')).1 = z := by
  have hex := exists_cutLoading_window_smul_topOneSpan (I := I) (k := k) (ℓ := ℓ) (j := j)
    (hj := hj) (Q := Q) (Λ := Λ) (Λc := Λc) (θ := θ) (γ := γ) (ν₀ := ν₀) X hQ s w q₁.1 hq₁ y
  obtain ⟨y', hy'⟩ := hex
  refine ⟨y, y', hy', ?_⟩
  refine (leadingLayerSpanEquiv_e_smul (I := I) (k := k) (ℓ := ℓ) (j := j) (hj := hj)
    (Q := Q) (Λ := Λ) (Λc := Λc) (θ := θ) (γ := γ) (ν₀ := ν₀) X hQ hsc hsp s w hs q₀ hq₀ q₁ hq₁
      y y' hy').trans ?_
  exact (congrArg (fun t : LayP => indMackeyLayerAct Nₒ (e (windowLoading j hj θ γ ν₀ s w))
    (fun _ _ hy => e_mul_mem_mackeyFilt _ hy) (Multiset.card (stendhalWeight 2 ν₀)) t) hz).trans hzz

/-- **The corner of the window loading in the leading layer** (Webster v3, Lemma 7.19, trace
half, step L5): an element of the layer `N` of the induced model of `S_+(X)` lies in the corner
`e(l⁺_w) · Lay⁺` exactly when it is the image under `leadingLayerSpanEquiv` of
`Ξ_{q₁}(e(l) · T'(Ind ε_{e(w)} (T'⁻¹ y)))` for some `y` in the identity-shuffle span at the
cut. -/
theorem mem_range_indMackeyLayerAct_windowLoading_iff (hsc : KLRSymm Sc) (hsp : KLRSymm Sp)
    (hs : ∀ a : Fin (Multiset.card (stendhalWeight ℓ (θ + γ))), a.val < midPos j s →
      ∀ u : Fin ℓ, s.lbl a = .inr u → u.val < j)
    (q₀ : {q : MackeyQuad (Seq.prefixWt (windowLoading j hj θ γ ν₀ s w)
          (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
          (Seq.suffixWt (windowLoading j hj θ γ ν₀ s w)
          (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
          (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ))
          (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
          (stendhalWeight (2 + (ℓ - j)) (ν₀ + γ))) //
            Multiset.card q.β = Multiset.card (stendhalWeight 2 ν₀)})
    (hq₀ : q₀.1.β = (stendhalWeight 2 ν₀).map (windowColour j hj))
    (q₁ : {q : MackeyQuad (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
          (midPos_le_card_cut s))
          (Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s))
          (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ))
          (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)) //
            Multiset.card q.β = 0})
    (hq₁ : q₁.1.β = 0) (z : LayP) :
    z ∈ LinearMap.range (indMackeyLayerAct Nₒ (e (windowLoading j hj θ γ ν₀ s w))
        (fun _ _ hy => e_mul_mem_mackeyFilt _ hy) (Multiset.card (stendhalWeight 2 ν₀))) ↔
      ∃ y y' : mackeyTopOneSpan (Q := Sc) q₁.1 Yc,
        (y' : MackeyLeftInd Sc Yc q₁.1) =
          (((e preC : KLRAlgebra k Sc _) ⊗ₜ (e sufC : KLRAlgebra k Sc _) : TensorKLR Sc _ _) •
            (topOneCornerEquiv q₁.1 Yc (stendhalQ_symm Q (cutLabels j hj Λ) hQ)
              (BalancedTensor.mapRight (plusWindowEnd X s q₁.1 (e wP))
                ((topOneCornerEquiv q₁.1 Yc (stendhalQ_symm Q (cutLabels j hj Λ) hQ)).symm y)) :
              MackeyLeftInd Sc Yc q₁.1)) ∧
        (leadingLayerSpanEquiv X hQ hsc hsp s w hs q₀ hq₀ q₁ hq₁
          (Submodule.equivMapOfInjective _
            (indMackeyLeftMap_injective_of_klrSymm _ Yc hsc q₁) _ y')).1 = z := by
  constructor
  · rintro ⟨u, rfl⟩
    have hz0 := range_indMackeyLayerAct_windowLoading_le (I := I) (k := k) (ℓ := ℓ) (j := j)
      (hj := hj) (Q := Q) (Λ := Λ) (Λc := Λc) (θ := θ) (γ := γ) (ν₀ := ν₀)
      X hQ hsp s w hs q₀ hq₀
      (LinearMap.mem_range_self _ u)
    let zz : (mackeyTopOneSpan (Q := Sp) q₀.1 Nₒ).map (indMackeyLeftMap (Q := Sp)
        (Seq.prefixWt_add_suffixWt (windowLoading j hj θ γ ν₀ s w) _
          (midPos_add_le_card (hj := hj) s)).symm Nₒ q₀.1 q₀.2) := ⟨_, hz0⟩
    have hv := LinearEquiv.apply_symm_apply (leadingLayerSpanEquiv (I := I) (k := k) (ℓ := ℓ)
      (j := j) (hj := hj) (Q := Q) (Λ := Λ) (Λc := Λc) (θ := θ) (γ := γ) (ν₀ := ν₀)
      X hQ hsc hsp s w hs q₀ hq₀ q₁ hq₁) zz
    have hy := LinearEquiv.apply_symm_apply (Submodule.equivMapOfInjective _
      (indMackeyLeftMap_injective_of_klrSymm (Q := Sc) _ Yc hsc q₁)
        (mackeyTopOneSpan (Q := Sc) q₁.1 Yc))
      ((leadingLayerSpanEquiv (I := I) (k := k) (ℓ := ℓ) (j := j) (hj := hj)
      (Q := Q) (Λ := Λ) (Λc := Λc) (θ := θ) (γ := γ) (ν₀ := ν₀)
        X hQ hsc hsp s w hs q₀ hq₀ q₁ hq₁).symm zz)
    have hvv := (congrArg (leadingLayerSpanEquiv (I := I) (k := k) (ℓ := ℓ) (j := j) (hj := hj)
      (Q := Q) (Λ := Λ) (Λc := Λc) (θ := θ) (γ := γ) (ν₀ := ν₀)
      X hQ hsc hsp s w hs q₀ hq₀ q₁ hq₁) hy).trans hv
    exact exists_leadingLayerSpanEquiv_cutLoading_eq (I := I) (k := k) (ℓ := ℓ) (j := j) (hj := hj)
      (Q := Q) (Λ := Λ) (Λc := Λc) (θ := θ) (γ := γ) (ν₀ := ν₀) X hQ s w hsc hsp hs
      q₀ hq₀ q₁ hq₁ _ _ (congrArg Subtype.val hvv) (indMackeyLayerAct_e_idem Nₒ _ _ u)
  · rintro ⟨y, y', hy, rfl⟩
    exact ⟨_, (leadingLayerSpanEquiv_e_smul (I := I) (k := k) (ℓ := ℓ) (j := j) (hj := hj)
      (Q := Q) (Λ := Λ) (Λc := Λc) (θ := θ) (γ := γ) (ν₀ := ν₀) X hQ hsc hsp s w hs q₀ hq₀ q₁ hq₁
      y y' hy).symm⟩

end Range

end Categorification.Stendhal.CupCap

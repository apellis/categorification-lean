/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KPsiCutHom
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KCutLift

/-!
# The inverse `Ψ` of Lemma 7.19 (K) at the cut

Webster, arXiv:1309.3796v3, Lemma 7.19 (K), at the cut: the family `y ↦ f_y` extends over the
partial standardization `S_cut Y` (`isCutInputHom_kCapFamily`), and the resulting balanced map
is `Ψ : K^σ(S_cut Y) → S_+(Y ⊠ L')`, `T^{λ⁺}`-linear. It is a left inverse of `Φ = kCutPhi`.

## Main definitions

* `Stendhal.CupCap.kPsi`: the map `Ψ`.

## Main results

* `Stendhal.CupCap.kCapLin_capSum_cutPos`: `f_y` takes the cap generator at the cut to the unit.
* `Stendhal.CupCap.kPsi_kCutPhi`: `Ψ ∘ Φ = id`.
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
local notation "fM" => kModelMap j hj Q Λ Λc θ γ ν₀ Y hQ L'
set_option hygiene false in
local notation "mkp" => TensorProductAlgebra.mk Q (plusLabels Λ Λc j hj) ((θ + γ) + ν₀)
set_option hygiene false in
local notation "botp" => botMap k Q Λ Λc j hj (θ + γ) ν₀
set_option hygiene false in
local notation "Rp" => KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj))
  (stendhalWeight (ℓ + 2) ((θ + γ) + ν₀))
set_option hygiene false in
local notation "Tp" => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) ((θ + γ) + ν₀)
set_option hygiene false in
local notation "cast_c" => castLabelsTensorProductAlgebra Q (Nat.add_sub_of_le hj) Λ (θ + γ)
set_option hygiene false in
local notation "Ws" s:max => KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
  (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s (midPos j s) (midPos_le j s))
set_option hygiene false in
local notation "Kσ" => ReflectedCap j hj Q Λ Λc (θ + γ) ν₀ Lc

variable {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : Lc), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}
  (hR : MidKLRRel j hj Q Λ Λc (θ + γ) ν₀ Lc hL)
  (hP : PullOff k Q Λc ν₀ Lc) (hPL : PullOffLeft k Q Λc ν₀ Lc)
  (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))

/-! ### `f_y` on the cap generator at the cut -/

theorem kModelMap_tmul_midGen (y : Y) (W : Rp) (v : Lc) :
    fM y (Ind.tmul (midGen j hj Q Λ Λc (θ + γ) ν₀ (botp W)) v) =
      mkp (botp (hflip W)) • U y (show L' from v) := by
  rw [kModelMap_tmul, midGen_val, unop_op, plusFlip_mul, mul_smul,
    kSrc_flip_midStendhal_one_smul_unit, plusFlip_botMap]

/-- **`f_y` on a cap generator**: it is the mirror image of the diagram below the generator in the
model, acting on the unit. -/
theorem kCapLin_capGen (y : Y) (s : Seq (stendhalWeight ℓ (θ + γ)))
    (n : Fin (Multiset.card (stendhalWeight ℓ (θ + γ)) + 1)) (v : L') :
    kCapLin Y hQ hR hP hPL hκ y
        (capGen j hj Q Λ Λc (θ + γ) ν₀ s n (toCapCoef (Q := Q) (Λc := Λc) (ν₀ := ν₀) v)) =
      if h : n.val ≤ midPos j s then
        fM y (midCapScalar j Q ν₀ s n • Ind.tmul (midGen j hj Q Λ Λc (θ + γ) ν₀
          (botp (midCapBot j hj Q Λ Λc ν₀ s n h))) (toCapCoef (Q := Q) (Λc := Λc) (ν₀ := ν₀) v))
      else 0 := by
  change fM y (ofMidBimod Lc hL hR (midCapModelEquiv hP hPL hκ hR
    (capElt 1 s n (toCapCoef (Q := Q) (Λc := Λc) (ν₀ := ν₀) v) 1))) = _
  rw [capElt_one_one_mid, midCapModelEquiv_mk]
  change fM y (midCapImage Lc (s, n) _) = _
  unfold midCapImage
  split_ifs with h
  · rfl
  · exact map_zero _

set_option hygiene false in
local notation "nθ" => Multiset.card (stendhalWeight j θ)

/-- **`f_y` on the cap generator at the cut and the loading `s`** is the window of `s` acting on
the unit: for a good `s` the generator sits at the maximum, and for a bad `s` both sides vanish. -/
theorem kCapLin_capGen_cutPos (y : Y) (s : Seq (stendhalWeight ℓ (θ + γ))) (v : L') :
    kCapLin Y hQ hR hP hPL hκ y (capGen j hj Q Λ Λc (θ + γ) ν₀ s (cutPos j hj θ γ)
        (toCapCoef (Q := Q) (Λc := Λc) (ν₀ := ν₀) v)) = mkp (botp (Ws s)) • U y v := by
  rw [kCapLin_capGen]
  by_cases hs : ∃ (i : Seq (stendhalWeight j θ)) (l : Seq (stendhalWeight (ℓ - j) γ)),
      IsRedOrdered l ∧ ¬ IsViolated l ∧ s = cutSeq hj i l
  · obtain ⟨i, l, hl, hv, rfl⟩ := hs
    have hm := midPos_cutSeq hj i hl hv
    have hn : (cutPos j hj θ γ).val ≤ midPos j (cutSeq hj i l) := hm.ge
    simp only [hn, ↓reduceDIte]
    have hsc : midCapScalar j Q ν₀ (cutSeq hj i l) (cutPos j hj θ γ) = 1 := by
      simp [midCapScalar, hm]
    rw [hsc, one_smul, kModelMap_tmul_midGen]
    have hc : nθ ≤ Multiset.card (stendhalWeight ℓ (θ + γ)) := hm ▸ midPos_le j _
    rw [midCapBot_eq_of (cutSeq hj i l) hn hm hc]
    simp only [Nat.sub_self, passU_zero, mul_one, (KLRAlgebra.eSum_idem _).eq,
      hflip_eSum_insertSet]
    rw [congrArg (KLRAlgebra.eSum _) (insertSet_congr' (cutSeq hj i l) hc
      (midPos_le j (cutSeq hj i l)) hm.symm)]
    rfl
  · rw [kSrc_window_smul_unit_of_bad j hj Q Λ Λc θ γ ν₀ Y hQ L' s hs]
    split_ifs with hn
    · rw [midModel_algebraMap_smul, kModelMap_smul, kModelMap_tmul_midGen, midCapBot, hflip_mul,
        hflip_mul, map_mul, map_mul, map_mul, map_mul, mul_smul, mul_smul,
        hflip_eSum_insertSet s (midPos_le j s)]
      erw [kSrc_window_smul_unit_of_bad j hj Q Λ Λc θ γ ν₀ Y hQ L' s hs]
      rw [smul_zero, smul_zero, smul_zero]
    · rfl

/-- **`f_y` takes the cap generator at the cut to the unit**: `f_y(cap(|h|, v)) = 1 ⊗ (y ⊠ v)`. -/
theorem kCapLin_capSum_cutPos (y : Y) (v : L') :
    kCapLin Y hQ hR hP hPL hκ y (capSum j hj Q Λ Λc (θ + γ) ν₀ (cutPos j hj θ γ)
        (toCapCoef (Q := Q) (Λc := Λc) (ν₀ := ν₀) v)) = U y v := by
  rw [capSum, map_sum]
  simp only [kCapLin_capGen_cutPos]
  have h := kSrc_window_smul_unit j hj Q Λ Λc θ γ ν₀ Y hQ L' (fun _ => 1) 1
    (fun _ _ _ _ => rfl) y v
  simpa only [map_one, one_smul] using h

/-! ### The map `Ψ` -/

set_option hygiene false in
local notation "σc" => kCutHomRepCut j hj Q Λ Λc θ γ ν₀ Y hQ L'

/-- **The extension of `y ↦ f_y` over the partial standardization at the cut.** -/
def kPsiLift : KCutStd j hj Q Λ θ γ Y hQ →ₗ[k] (Kσ →ₗ[Tp] KCutSrc j hj Q Λ Λc θ γ ν₀ Y hQ L') :=
  cutStandardLift Q (cutLabels j hj Λ) θ γ (kCapFamily Y hQ hR hP hPL hκ)
    (isCutInputHom_kCapFamily Y hQ hR hP hPL hκ)

/-- **The balance of `Ψ`**: `T^λ` acting on `S_cut Y` corresponds to its right action on `K^σ`. -/
theorem kPsiLift_smul (t : TensorProductAlgebra k Q Λ (θ + γ)) (n : KCutStd j hj Q Λ θ γ Y hQ)
    (r : Kσ) : kPsiLift Y hQ hR hP hPL hκ (t • n) r = kPsiLift Y hQ hR hP hPL hκ n (op t • r) := by
  rw [kCutStd_smul_def]
  change cutStandardLift Q (cutLabels j hj Λ) θ γ (kCapFamily Y hQ hR hP hPL hκ)
    (isCutInputHom_kCapFamily Y hQ hR hP hPL hκ)
    (cutStandardAction Q (cutLabels j hj Λ) θ γ Y hQ ((cast_c).symm t) n) r = _
  rw [cutStandardLift_action]
  change kPsiLift Y hQ hR hP hPL hκ n (op ((cast_c) ((cast_c).symm t)) • r) = _
  rw [AlgEquiv.apply_symm_apply]

/-- **The inverse `Ψ : K^σ(S_cut Y) → S_+(Y ⊠ L')`** of Lemma 7.19 (K) at the cut
(Webster, arXiv:1309.3796v3), `r ⊗ m ↦ f_m(r)`; it is `T^{λ⁺}`-linear. -/
def kPsi : KCutTarget j hj Q Λ Λc θ γ ν₀ Y hQ L' →ₗ[Tp] KCutSrc j hj Q Λ Λc θ γ ν₀ Y hQ L' :=
  BalancedTensor.liftOfHom (kPsiLift Y hQ hR hP hPL hκ).toAddMonoidHom
    (kPsiLift_smul Y hQ hR hP hPL hκ)

theorem kPsi_tmul (r : Kσ) (n : KCutStd j hj Q Λ θ γ Y hQ) :
    kPsi Y hQ hR hP hPL hκ (BalancedTensor.tmul r n : KCutTarget j hj Q Λ Λc θ γ ν₀ Y hQ L') =
      kPsiLift Y hQ hR hP hPL hκ n r := rfl

/-- **`Ψ ∘ Φ` is the identity on the units.** -/
theorem kPsi_kCutPhi_unit (y : Y) (v : L') :
    kPsi Y hQ hR hP hPL hκ (kCutPhi j hj Q Λ Λc θ γ ν₀ Y hQ L'
        (plusStandardUnit hQ (midSpectTmul (k := k) y v))) =
      toKCutSrc (plusStandardUnit hQ (midSpectTmul (k := k) y v)) := by
  rw [kCutPhi_unit, kPsi_tmul]
  change cutStandardLift Q (cutLabels j hj Λ) θ γ (kCapFamily Y hQ hR hP hPL hκ)
    (isCutInputHom_kCapFamily Y hQ hR hP hPL hκ)
    (cutStandardUnit Q (cutLabels j hj Λ) θ γ Y y) _ = _
  rw [cutStandardLift_unit]
  exact kCapLin_capSum_cutPos Y hQ hR hP hPL hκ y v

/-- `Ψ ∘ Φ`, as a `k`-linear endomorphism of `S_+(Y ⊠ L')`. -/
def kPsiPhi : KCutSource j hj Q Λ Λc θ γ ν₀ Y hQ L' →ₗ[k] KCutSource j hj Q Λ Λc θ γ ν₀ Y hQ L' :=
  ((kPsi Y hQ hR hP hPL hκ).restrictScalars k).comp (kCutPhi j hj Q Λ Λc θ γ ν₀ Y hQ L')

theorem kPsiPhi_apply (u : KCutSource j hj Q Λ Λc θ γ ν₀ Y hQ L') :
    kPsiPhi Y hQ hR hP hPL hκ u =
      kPsi Y hQ hR hP hPL hκ (kCutPhi j hj Q Λ Λc θ γ ν₀ Y hQ L' u) := rfl

/-- **`Ψ ∘ Φ` is linear over `T^{λ⁺}`.** -/
theorem kPsiPhi_action (t : TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (θ + (ν₀ + γ)))
    (u : KCutSource j hj Q Λ Λc θ γ ν₀ Y hQ L') :
    kPsiPhi Y hQ hR hP hPL hκ
        (plusStandardAction Q Λ Λc j hj θ ν₀ γ (MidSpect (k := k) Y L') hQ t u) =
      plusStandardAction Q Λ Λc j hj θ ν₀ γ (MidSpect (k := k) Y L') hQ t
        (kPsiPhi Y hQ hR hP hPL hκ u) := by
  refine (congrArg (kPsi Y hQ hR hP hPL hκ)
    (kCutPhi_action j hj Q Λ Λc θ γ ν₀ Y hQ L' t u)).trans ?_
  change kPsi Y hQ hR hP hPL hκ
    (castTensorProductAlgebra Q (plusLabels Λ Λc j hj) (plusWeight_eq θ γ ν₀) t •
      kCutPhi j hj Q Λ Λc θ γ ν₀ Y hQ L' u) = _
  rw [map_smul]
  refine Eq.trans ?_ (congrArg (fun t' => plusStandardAction Q Λ Λc j hj θ ν₀ γ
    (MidSpect (k := k) Y L') hQ t' (kPsiPhi Y hQ hR hP hPL hκ u)) (AlgEquiv.symm_apply_apply
      (castTensorProductAlgebra Q (plusLabels Λ Λc j hj) (plusWeight_eq θ γ ν₀)) t))
  rfl

/-- **`Ψ ∘ Φ = id`** (Webster, arXiv:1309.3796v3, Lemma 7.19 (K) at the cut): `Φ` has the left
inverse `Ψ`. -/
theorem kPsi_kCutPhi (u : KCutSource j hj Q Λ Λc θ γ ν₀ Y hQ L') :
    kPsi Y hQ hR hP hPL hκ (kCutPhi j hj Q Λ Λc θ γ ν₀ Y hQ L' u) = toKCutSrc u := by
  have hu : ((kPsiPhi Y hQ hR hP hPL hκ).comp
        (plusStandardUnit (N := MidSpect (k := k) Y L') hQ) :
        Y ⊗[k] L' →ₗ[k] KCutSource j hj Q Λ Λc θ γ ν₀ Y hQ L') =
      (plusStandardUnit (N := MidSpect (k := k) Y L') hQ :
        Y ⊗[k] L' →ₗ[k] KCutSource j hj Q Λ Λc θ γ ν₀ Y hQ L') :=
    TensorProduct.ext' fun y v => kPsi_kCutPhi_unit Y hQ hR hP hPL hκ y v
  have h : kPsiPhi Y hQ hR hP hPL hκ = LinearMap.id :=
    plusStandardLift_unique (ρ := plusStandardAction Q Λ Λc j hj θ ν₀ γ (MidSpect (k := k) Y L') hQ)
      hQ (kPsiPhi_action Y hQ hR hP hPL hκ) (fun _ _ => rfl) fun n => LinearMap.congr_fun hu n
  exact LinearMap.congr_fun h u

end Categorification.Stendhal.CupCap

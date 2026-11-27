/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KPsi
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KCutUnitE

/-!
# `Φ ∘ Ψ = id` in Lemma 7.19 (K) at the cut

Webster, arXiv:1309.3796v3, Lemma 7.19 (K), at the cut: the comparison map
`Φ : S_+(Y ⊠ L') → K^σ(S_cut Y)` is an isomorphism with inverse `Ψ`.

On `K^σ ⊗ S_cut Y`, a cap generator at a loading `s` of the top only meets the unit through
`e(s)`, which kills the unit unless `s = i ⊔ l` with a good tail; there the generator sits at the
cut `|h|`. Hence every element `r ⊗ (1 ⊗ y)` is reached from the cap generators at the cut, which
are the images under `Φ` of the units.

## Main results

* `Stendhal.CupCap.tmul_capGen_unit_of_bad`: generators at bad loadings vanish on the unit.
* `Stendhal.CupCap.kCutPhi_kPsi`: `Φ ∘ Ψ = id`.
* `Stendhal.CupCap.kCutPhiEquiv`: `Φ` as a linear equivalence.
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
local notation "Lc" => CapCoef Q Λc ν₀ L'
set_option hygiene false in
local notation "Kσ" => ReflectedCap j hj Q Λ Λc (θ + γ) ν₀ Lc
set_option hygiene false in
local notation "Xt" => KCutTarget j hj Q Λ Λc θ γ ν₀ Y hQ L'
set_option hygiene false in
local notation "u" y:max => kCutUnit j hj Q Λ θ γ Y hQ y
set_option hygiene false in
local notation "Tt" => tensorOfKLR Q (cutLabels j hj Λ ∘ Fin.natAdd j) γ

/-! ### Cap generators on the unit -/

omit [IsScalarTower k (TensorProductAlgebra k Q Λc ν₀) L'] in
/-- **A cap generator at a bad loading vanishes on the unit.** -/
theorem tmul_capGen_unit_of_bad (s : Seq (stendhalWeight ℓ (θ + γ)))
    (hs : ¬ ∃ (i : Seq (stendhalWeight j θ)) (l : Seq (stendhalWeight (ℓ - j) γ)),
      IsRedOrdered l ∧ ¬ IsViolated l ∧ s = cutSeq hj i l)
    (q : Fin (Multiset.card (stendhalWeight ℓ (θ + γ)) + 1)) (c : Lc) (y : Y) :
    (BalancedTensor.tmul (capGen j hj Q Λ Λc (θ + γ) ν₀ s q c) (u y) : Xt) = 0 := by
  have he := op_e_smul_capGen (j := j) (hj := hj) (Q := Q) (Λ := Λ) (Λc := Λc) (ν₀ := ν₀)
    s s q c
  simp only [↓reduceIte] at he
  rw [← he]
  erw [BalancedTensor.op_smul_tmul]
  rw [kCut_e_smul_unit]
  have h0 : ∀ (i : Seq (stendhalWeight j θ)) (l : Seq (stendhalWeight (ℓ - j) γ)),
      (if s = cutSeq hj i l then
        u ((tensorOfKLR Q (cutLabels j hj Λ ∘ Fin.castAdd (ℓ - j)) θ (e i) ⊗ₜ[k] Tt (e l) :
          cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) • y) else 0) = 0 := fun i l => by
    split_ifs with h
    · have hl : ¬ (IsRedOrdered l ∧ ¬ IsViolated l) := fun hl => hs ⟨i, l, hl.1, hl.2, h⟩
      rw [tensorOfKLR_e_of_bad hl, TensorProduct.tmul_zero,
        zero_smul (cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) y, map_zero]
    · rfl
  simp only [h0, Finset.sum_const_zero]
  exact BalancedTensor.tmul_zero _

omit [IsScalarTower k (TensorProductAlgebra k Q Λc ν₀) L'] in
/-- **On the unit, a cap generator at the maximum equals the generator at the cut.** -/
theorem tmul_capGen_midCPos_unit (s : Seq (stendhalWeight ℓ (θ + γ))) (c : Lc) (y : Y) :
    (BalancedTensor.tmul (capGen j hj Q Λ Λc (θ + γ) ν₀ s (midCPos j s) c) (u y) : Xt) =
      BalancedTensor.tmul (capGen j hj Q Λ Λc (θ + γ) ν₀ s (cutPos j hj θ γ) c) (u y) := by
  by_cases hs : ∃ (i : Seq (stendhalWeight j θ)) (l : Seq (stendhalWeight (ℓ - j) γ)),
      IsRedOrdered l ∧ ¬ IsViolated l ∧ s = cutSeq hj i l
  · obtain ⟨i, l, hl, hv, rfl⟩ := hs
    have hp : midCPos j (cutSeq hj i l) = cutPos j hj θ γ := Fin.ext (midPos_cutSeq hj i hl hv)
    rw [hp]
  · rw [tmul_capGen_unit_of_bad Y hQ s hs, tmul_capGen_unit_of_bad Y hQ s hs]

set_option hygiene false in
local notation "Np" => BlocksOneStepInput Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ
  (PlusInput Q Λ Λc j hj θ ν₀ γ (MidSpect (k := k) Y L'))
set_option hygiene false in
local notation "U" y:max v:max =>
  kSrcUnit j hj Q Λ Λc θ γ ν₀ Y hQ L' (show Np from midSpectTmul (k := k) y v)
set_option hygiene false in
local notation "fM" => kModelMap j hj Q Λ Λc θ γ ν₀ Y hQ L'
set_option hygiene false in
local notation "mkp" => TensorProductAlgebra.mk Q (plusLabels Λ Λc j hj) ((θ + γ) + ν₀)
set_option hygiene false in
local notation "botp" => botMap k Q Λ Λc j hj (θ + γ) ν₀
set_option hygiene false in
local notation "Tp" => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) ((θ + γ) + ν₀)
set_option hygiene false in
local notation "Tλ" => TensorProductAlgebra k Q Λ (θ + γ)
set_option hygiene false in
local notation "Fm" => midModelToCapAdd j hj Q Λ Λc (θ + γ) ν₀ Lc
set_option hygiene false in
local notation "Φ" => kCutPhi j hj Q Λ Λc θ γ ν₀ Y hQ L'

/-- **`Φ` is linear over `T^{λ⁺}((θ + γ) + ν₀)`.** -/
theorem kCutPhi_smul (t : Tp) (x : KCutSrc j hj Q Λ Λc θ γ ν₀ Y hQ L') :
    Φ (t • x) = t • Φ x := by
  have h := kCutPhi_action j hj Q Λ Λc θ γ ν₀ Y hQ L'
    ((castTensorProductAlgebra Q (plusLabels Λ Λc j hj) (plusWeight_eq θ γ ν₀)).symm t) x
  refine h.trans ?_
  change castTensorProductAlgebra Q (plusLabels Λ Λc j hj) (plusWeight_eq θ γ ν₀)
    ((castTensorProductAlgebra Q (plusLabels Λ Λc j hj) (plusWeight_eq θ γ ν₀)).symm t) • Φ x = _
  rw [AlgEquiv.apply_symm_apply]

omit [IsScalarTower k (TensorProductAlgebra k Q Λc ν₀) L'] in
theorem sum_tmul_kCutTarget {ι : Type*} (F : Finset ι) (r : ι → Kσ)
    (n : KCutStd j hj Q Λ θ γ Y hQ) :
    (BalancedTensor.tmul (∑ i ∈ F, r i) n : Xt) = ∑ i ∈ F, BalancedTensor.tmul (r i) n := by
  classical
  induction F using Finset.induction_on with
  | empty => exact BalancedTensor.zero_tmul n
  | insert i F hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, BalancedTensor.add_tmul, ih]

/-- **`Φ ∘ f_y` on the model**: it is `w ↦ w ⊗ (1 ⊗ y)`, read in `K^σ`. -/
theorem kCutPhi_kModelMap (y : Y) (w : MidModel j hj Q Λ Λc (θ + γ) ν₀ Lc) :
    Φ (fM y w) = (BalancedTensor.tmul (toRefl (Fm w)) (u y) : Xt) := by
  induction w using Ind.induction_on with
  | zero =>
    rw [map_zero, map_zero, map_zero]
    exact (BalancedTensor.zero_tmul _).symm
  | add w w' hw hw' =>
    rw [map_add, map_add, map_add, hw, hw', toRefl_add, BalancedTensor.add_tmul]
  | tmul z v =>
    obtain ⟨Z, hZ⟩ := topMap_surjective' (k := k) (Q := Q) (Λ := plusLabels Λ Λc j hj)
      (ν := (θ + γ) + ν₀) z.1.unop
    have hz : z = midGen j hj Q Λ Λc (θ + γ) ν₀ (botp Z) := by
      rw [← midGen_unop_val z]
      exact congrArg _ hZ.symm
    rw [hz, kModelMap_tmul_midGen, kCutPhi_smul, kSrcUnit_apply]
    erw [kCutPhi_unit]
    rw [midModelToCapAdd_tmul_midGen, midInvFun]
    rw [show toRefl (∑ s : Seq (stendhalWeight ℓ (θ + γ)),
        (Env.mk 1 (botp Z) : Env k Q Λ Λc j hj (θ + γ) ν₀) •
          midGenCap j hj Q Λ Λc ν₀ s v) = ∑ s : Seq (stendhalWeight ℓ (θ + γ)),
        mkp (botp (hflip Z)) • capGen j hj Q Λ Λc (θ + γ) ν₀ s (midCPos j s) v from ?_]
    · rw [← Finset.smul_sum, ← BalancedTensor.smul_tmul']
      congr 1
      rw [capSum, sum_tmul_kCutTarget, sum_tmul_kCutTarget]
      exact Finset.sum_congr rfl fun s _ => (tmul_capGen_midCPos_unit Y hQ s v y).symm
    · refine (map_sum (AddMonoidHom.mk' (toRefl (L := Lc) (Λ := Λ) (Λc := Λc) (j := j)
        (hj := hj) (ν := θ + γ) (ν₀ := ν₀) (Q := Q)) toRefl_add) _ _).trans ?_
      refine Finset.sum_congr rfl fun s _ => ?_
      change toRefl _ = _
      have h := mk_smul_toRefl (hflip Z) (midGenCap j hj Q Λ Λc ν₀ s v)
      rw [hflip_hflip] at h
      exact h.symm

set_option hygiene false in
local notation "cast_c" => castLabelsTensorProductAlgebra Q (Nat.add_sub_of_le hj) Λ (θ + γ)
set_option hygiene false in
local notation "Std" => KCutStd j hj Q Λ θ γ Y hQ

variable {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : Lc), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}
  (hR : MidKLRRel j hj Q Λ Λc (θ + γ) ν₀ Lc hL)
  (hP : PullOff k Q Λc ν₀ Lc) (hPL : PullOffLeft k Q Λc ν₀ Lc)
  (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))

/-- **`Φ ∘ f_y` is `r ↦ r ⊗ (1 ⊗ y)`.** -/
theorem kCutPhi_kCapLin (y : Y) (r : Kσ) :
    Φ (kCapLin Y hQ hR hP hPL hκ y r) = (BalancedTensor.tmul r (u y) : Xt) := by
  obtain ⟨c, rfl⟩ := toRefl_surjective r
  change Φ (fM y (ofMidBimod Lc hL hR (midCapModelEquiv hP hPL hκ hR c))) = _
  rw [kCutPhi_kModelMap]
  have hc : Fm (ofMidBimod Lc hL hR (midCapModelEquiv hP hPL hκ hR c)) = c :=
    (midCapModelEquiv hP hPL hκ hR).symm_apply_apply c
  rw [hc]

/-! ### The maps `n ↦ (r ↦ r ⊗ n)` and `n ↦ (r ↦ Φ Ψ (r ⊗ n))` -/

omit [IsScalarTower k (TensorProductAlgebra k Q Λc ν₀) L'] in
theorem tmul_smul_kCutTarget (c : k) (r : Kσ) (n : Std) :
    (show Xt from BalancedTensor.tmul r (c • n)) = c • (show Xt from BalancedTensor.tmul r n) := by
  rw [← algebraMap_smul_kCutStd, ← BalancedTensor.op_smul_tmul, reflectedCap_op_algebraMap_smul,
    ← BalancedTensor.smul_tmul']
  rfl

variable (j hj Q Λ Λc θ γ ν₀ L') in
/-- **`T^λ` acting on `Hom_{T^{λ⁺}}(K^σ, K^σ(S_cut Y))`** by precomposition, through the labels
of the cut. -/
abbrev kTgtHomRep :=
  (BalancedTensor.precompRep Tp Kσ Xt (fun c z => reflectedCap_op_algebraMap_smul c z)).comp
    (cast_c).toAlgHom

omit [IsScalarTower k (TensorProductAlgebra k Q Λc ν₀) L'] in
variable (j hj Q Λ Λc θ γ ν₀ L') in
/-- The map `n ↦ (r ↦ r ⊗ n)`. -/
def kTmulHom : Std →ₗ[k] (Kσ →ₗ[Tp] Xt) where
  toFun n :=
    { toFun := fun r => BalancedTensor.tmul r n
      map_add' := fun r r' => BalancedTensor.add_tmul r r' n
      map_smul' := fun b r => (BalancedTensor.smul_tmul' b r n).symm }
  map_add' n n' := LinearMap.ext fun r => BalancedTensor.tmul_add r n n'
  map_smul' c n := LinearMap.ext fun r => tmul_smul_kCutTarget Y hQ c r n

/-- `Φ ∘ Ψ`, linear over `T^{λ⁺}`. -/
def kPhiPsiTp : Xt →ₗ[Tp] Xt where
  toFun z := Φ (kPsi Y hQ hR hP hPL hκ z)
  map_add' z z' := by rw [map_add, map_add]
  map_smul' t z := by rw [map_smul, kCutPhi_smul]; rfl

/-- The map `n ↦ (r ↦ Φ Ψ (r ⊗ n))`. -/
def kTmulHom' : Std →ₗ[k] (Kσ →ₗ[Tp] Xt) where
  toFun n := (kPhiPsiTp Y hQ hR hP hPL hκ).comp (kTmulHom j hj Q Λ Λc θ γ ν₀ Y hQ L' n)
  map_add' n n' := LinearMap.ext fun r => by
    change Φ (kPsi Y hQ hR hP hPL hκ (BalancedTensor.tmul r (n + n'))) =
      Φ (kPsi Y hQ hR hP hPL hκ (BalancedTensor.tmul r n)) +
        Φ (kPsi Y hQ hR hP hPL hκ (BalancedTensor.tmul r n'))
    rw [BalancedTensor.tmul_add, map_add, map_add]
  map_smul' c n := LinearMap.ext fun r => by
    change Φ (kPsi Y hQ hR hP hPL hκ (show Xt from BalancedTensor.tmul r (c • n))) =
      c • Φ (kPsi Y hQ hR hP hPL hκ (show Xt from BalancedTensor.tmul r n))
    rw [tmul_smul_kCutTarget, show ∀ z : Xt, c • z = algebraMap k Tp c • z from fun _ => rfl,
      map_smul, kCutPhi_smul]
    rfl

omit [IsScalarTower k (TensorProductAlgebra k Q Λc ν₀) L'] in
theorem kTmulHom_action (t : TensorProductAlgebra k Q (cutLabels j hj Λ) (θ + γ)) (n : Std) :
    kTmulHom j hj Q Λ Λc θ γ ν₀ Y hQ L'
        (cutStandardAction Q (cutLabels j hj Λ) θ γ Y hQ t n) =
      kTgtHomRep j hj Q Λ Λc θ γ ν₀ Y hQ L' t (kTmulHom j hj Q Λ Λc θ γ ν₀ Y hQ L' n) := by
  refine LinearMap.ext fun r => ?_
  have ht : cutStandardAction Q (cutLabels j hj Λ) θ γ Y hQ t n =
      (cast_c t) • (show Std from n) := by
    rw [kCutStd_smul_def]
    change _ = cutStandardAction Q (cutLabels j hj Λ) θ γ Y hQ ((cast_c).symm (cast_c t)) n
    rw [AlgEquiv.symm_apply_apply]
  change (show Xt from BalancedTensor.tmul r
      (show Std from cutStandardAction Q (cutLabels j hj Λ) θ γ Y hQ t n)) =
    (show Xt from BalancedTensor.tmul (op (cast_c t) • r) n)
  rw [ht, BalancedTensor.op_smul_tmul]

/-- **`Φ ∘ Ψ = id`** (Webster, arXiv:1309.3796v3, Lemma 7.19 (K) at the cut). -/
theorem kCutPhi_kPsi (z : Xt) : Φ (kPsi Y hQ hR hP hPL hκ z) = z := by
  have h : kTmulHom' Y hQ hR hP hPL hκ = kTmulHom j hj Q Λ Λc θ γ ν₀ Y hQ L' :=
    cutStandardLift_unique Q (cutLabels j hj Λ) θ γ hQ
      (σ := kTgtHomRep j hj Q Λ Λc θ γ ν₀ Y hQ L')
      (fun t n => LinearMap.ext fun r =>
        congrArg (fun z => Φ (kPsi Y hQ hR hP hPL hκ z))
          (LinearMap.congr_fun (kTmulHom_action Y hQ t n) r))
      (kTmulHom_action Y hQ) fun y => LinearMap.ext fun r => by
        change Φ (cutStandardLift Q (cutLabels j hj Λ) θ γ (kCapFamily Y hQ hR hP hPL hκ)
          (isCutInputHom_kCapFamily Y hQ hR hP hPL hκ)
          (cutStandardUnit Q (cutLabels j hj Λ) θ γ Y y) r) = BalancedTensor.tmul r (u y)
        rw [cutStandardLift_unit]
        exact kCutPhi_kCapLin Y hQ hR hP hPL hκ y r
  induction z using BalancedTensor.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul r n => exact LinearMap.congr_fun (LinearMap.congr_fun h n) r
  | add z z' hz hz' => rw [map_add, map_add, hz, hz']

/-- **Lemma 7.19 (K) at the cut** (Webster, arXiv:1309.3796v3): `Φ : S_+(Y ⊠ L') → K^σ(S_cut Y)`
is an isomorphism, with inverse `Ψ`. -/
def kCutPhiEquiv :
    KCutSource j hj Q Λ Λc θ γ ν₀ Y hQ L' ≃ₗ[k] KCutTarget j hj Q Λ Λc θ γ ν₀ Y hQ L' :=
  LinearEquiv.ofLinearMap (kCutPhi j hj Q Λ Λc θ γ ν₀ Y hQ L')
    ((kPsi Y hQ hR hP hPL hκ).restrictScalars k)
    (LinearMap.ext fun z => kCutPhi_kPsi Y hQ hR hP hPL hκ z)
    (LinearMap.ext fun x => kPsi_kCutPhi Y hQ hR hP hPL hκ x)

theorem kCutPhiEquiv_apply (x : KCutSource j hj Q Λ Λc θ γ ν₀ Y hQ L') :
    kCutPhiEquiv Y hQ hR hP hPL hκ x = Φ x := rfl

end Categorification.Stendhal.CupCap

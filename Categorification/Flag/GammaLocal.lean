/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.GammaWord
import Categorification.Flag.Relabel
import Categorification.Flag.AdjacentCrossing

/-!
# Two upward strands in the path model and their Borel models

For a path `E_i E_j` (KL III: `E_i E_j 1_{r₂}`, the strand `E_j` applied first) the 1-morphism
`Γ(E_i E_j 1) = H_{(+_j r₂)^{+i}} ⊗_{H_{+_j r₂}} H_{r₂^{+j}}` of `Categorification.Flag.GammaWord`
uses the variables `Gen r₁` for the left factor and `Gen r₂` for the right factor. We identify it
with the tensor product `EERing` of `Categorification.Flag.Crossing`, in which both factors are
Borel rings of labellings of the single set of variables `Gen r₂`: the strand `E_j` moves the
variable `v₂ = ⟨j + 1, 0⟩` and the strand `E_i` moves a prescribed variable `v₁` (in the block
`i + 1` after the first move).

## Main definitions

* `BRing.tensorRingEquiv` : transport of a tensor product of bimodules along ring isomorphisms of
  the factors and of the middle ring.
* `eeB`, `eeRel`, `eeM`, `eeA` : the identifications of the middle ring, of the left factor and of
  the outer left ring.
* `eeEquiv K i j … : Γ(E_i E_j 1) ≃+* EERing Sigma.fst v₁ v₂ j.castSucc`, with its values on pure
  tensors (`eeEquiv_tmul`), on the outer actions (`eeEquiv_left`, `eeEquiv_right`) and on the
  dots (`eeEquiv_xi_left`, `eeEquiv_xi_right`).
* `transportBHom` : bimodule maps between two models.

## `Γ_N` of upward crossings on the path model (KL III Definition 6.2, (6.8))

* `crossEEP` (`i = j`, the divided difference `crossEE`), with the nilHecke relations
  `crossEEP_sq` (`ψ² = 0`), `crossEEP_xiL`, `crossEEP_xiR` (dot slides);
* `crossFarP` (`i · j = 0`, the swap `crossFar`), with `crossFarP_sq` (`ψ_{ji} ψ_{ij} = 1`),
  `crossFarP_xiL`, `crossFarP_xiR` (dot slides);
* `crossAdjNF`, `crossAdjFN` (`j = i + 1`: the restriction `crossNF` and minus the push-forward
  `crossFN` of `Categorification.Flag.AdjacentCrossing`), with `crossAdj_sq_NF`,
  `crossAdj_sq_FN` (`ψ_{ji} ψ_{ij} = (i - j)(x_left - x_right)`, KL III (4.11), (6.19)) and the dot
  slides `crossAdjNF_xiL`, `crossAdjNF_xiR`, `crossAdjFN_xiL`, `crossAdjFN_xiR` (KL III (4.12),
  (6.18));
* `adj_degenerate` : if `E_{i+1} E_i 1_{r₂} = 0`, the two dots of `E_i E_{i+1} 1_{r₂}` agree, so
  (4.11) holds with both crossings zero.

Together these are all two-strand relations of the `R(ν)` part of `U→(sl_n)` (KL III
Definition 4.1: `sqEq`, `sqNe`, `slideLEq`, `slideREq`, `slideLNe`, `slideRNe` of the KLR
presentation, on upward strands) in `Flag_N`; see `Categorification.Diagrams.KL3.GammaFlagSigned`
for the comparison with the signed polynomials `Q^τ`.
-/

noncomputable section

open scoped TensorProduct

namespace Categorification.Flag

universe u

/-! ### Transport of tensor products -/

namespace BRing

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] (M : BRing A B)
  (N : BRing B C) {R P Q : Type u} [CommRing R] [CommRing P] [CommRing Q] [Algebra R P]
  [Algebra R Q] (eB : B ≃+* R) (eM : M.T ≃+* P) (eN : N.T ≃+* Q)
  (hM : ∀ b, eM (M.right b) = algebraMap R P (eB b))
  (hN : ∀ b, eN (N.left b) = algebraMap R Q (eB b))

/-- The forward map of `tensorRingEquiv`. -/
def tensorFwd : TT M N →+* P ⊗[R] Q :=
  liftRingHom (Algebra.TensorProduct.includeLeftRingHom.comp eM.toRingHom)
    ((Algebra.TensorProduct.includeRight : Q →ₐ[R] P ⊗[R] Q).toRingHom.comp eN.toRingHom)
    (fun b => by
      show eM (M.right b) ⊗ₜ[R] (1 : Q) = (1 : P) ⊗ₜ[R] eN (N.left b)
      rw [hM, hN]
      exact Algebra.TensorProduct.tmul_one_eq_one_tmul (eB b))

theorem tensorFwd_tmul (m : M.T) (n : N.T) :
    tensorFwd M N eB eM eN hM hN (tmul M N m n) = eM m ⊗ₜ[R] eN n := by
  show eM m ⊗ₜ[R] (1 : Q) * (1 : P) ⊗ₜ[R] eN n = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

include hM in
theorem eM_symm_algebraMap (r : R) : eM.symm (algebraMap R P r) = M.right (eB.symm r) := by
  apply eM.injective
  rw [RingEquiv.apply_symm_apply, hM, RingEquiv.apply_symm_apply]

include hN in
theorem eN_symm_algebraMap (r : R) : eN.symm (algebraMap R Q r) = N.left (eB.symm r) := by
  apply eN.injective
  rw [RingEquiv.apply_symm_apply, hN, RingEquiv.apply_symm_apply]

/-- The inverse map of `tensorRingEquiv`. -/
def tensorBwd : P ⊗[R] Q →+* TT M N :=
  letI : Algebra R (TT M N) := ((inclL M N).comp (M.right.comp eB.symm.toRingHom)).toAlgebra
  (Algebra.TensorProduct.productMap
    { (inclL M N).comp eM.symm.toRingHom with
      commutes' := fun r => by
        show inclL M N (eM.symm (algebraMap R P r)) = inclL M N (M.right (eB.symm r))
        rw [eM_symm_algebraMap M eB eM hM] }
    { (inclR M N).comp eN.symm.toRingHom with
      commutes' := fun r => by
        show inclR M N (eN.symm (algebraMap R Q r)) = inclL M N (M.right (eB.symm r))
        rw [eN_symm_algebraMap N eB eN hN, inclR_apply, inclL_apply, tmul_right_one] }).toRingHom

theorem tensorBwd_tmul (p : P) (q : Q) :
    tensorBwd M N eB eM eN hM hN (p ⊗ₜ[R] q) = tmul M N (eM.symm p) (eN.symm q) := by
  show inclL M N (eM.symm p) * inclR M N (eN.symm q) = _
  rw [inclL_apply, inclR_apply, tmul_mul_tmul, mul_one, one_mul]

theorem tensorBwd_comp_tensorFwd :
    (tensorBwd M N eB eM eN hM hN).comp (tensorFwd M N eB eM eN hM hN) = RingHom.id _ :=
  ringHom_ext fun m n => by
    rw [RingHom.comp_apply, tensorFwd_tmul, tensorBwd_tmul, RingEquiv.symm_apply_apply,
      RingEquiv.symm_apply_apply, RingHom.id_apply]

theorem tensorFwd_comp_tensorBwd :
    (tensorFwd M N eB eM eN hM hN).comp (tensorBwd M N eB eM eN hM hN) = RingHom.id _ :=
  RingHom.ext fun t => by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul p q =>
      rw [RingHom.comp_apply, tensorBwd_tmul, tensorFwd_tmul, RingEquiv.apply_symm_apply,
        RingEquiv.apply_symm_apply, RingHom.id_apply]
    | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- **Transport of a tensor product** of bimodules along ring isomorphisms `M.T ≅ P`, `N.T ≅ Q`,
`B ≅ R` compatible with the actions of the middle ring: `M ⊗_B N ≅ P ⊗_R Q`. -/
def tensorRingEquiv : TT M N ≃+* P ⊗[R] Q :=
  RingEquiv.ofHomInv (tensorFwd M N eB eM eN hM hN) (tensorBwd M N eB eM eN hM hN)
    (tensorBwd_comp_tensorFwd M N eB eM eN hM hN) (tensorFwd_comp_tensorBwd M N eB eM eN hM hN)

theorem tensorRingEquiv_tmul (m : M.T) (n : N.T) :
    tensorRingEquiv M N eB eM eN hM hN (tmul M N m n) = eM m ⊗ₜ[R] eN n :=
  tensorFwd_tmul M N eB eM eN hM hN m n

theorem tensorRingEquiv_symm_tmul (p : P) (q : Q) :
    (tensorRingEquiv M N eB eM eN hM hN).symm (p ⊗ₜ[R] q) = tmul M N (eM.symm p) (eN.symm q) :=
  tensorBwd_tmul M N eB eM eN hM hN p q

end BRing

/-! ### The Borel model of two upward strands -/

section EEModel

variable {K : Type u} [Field K] {m : ℕ}

attribute [local instance] rightAlgebra midAlgebra

variable (i j : Fin m) {t r₁ r₂ : Comp m} (h₁ : StepR (true, i) r₁ t) (h₂ : StepR (true, j) r₂ r₁)

/-- The labelling after the first move (`E_j`), on the variables `Gen r₂`. -/
abbrev labJ : Gen r₂ → Fin (m + 1) :=
  moveLab (Sigma.fst : Gen r₂ → Fin (m + 1)) (movedVar j r₂ h₂.2) j.castSucc

variable (K) in
/-- The middle ring `H_{r₁} ≅ BorelRing (labJ)`. -/
def eeB : H K r₁ ≃ₐ[K] BorelRing K (labJ j h₂) :=
  (hCast K h₂.1.symm).trans (borelEquivH' K _ (raise j r₂) (card_moveLab j r₂ h₂.2)).symm

theorem eeB_x (j' : Fin (m + 1)) (α : ℕ) : eeB K j h₂ (x K r₁ j' α) = xB K (labJ j h₂) j' α := by
  rw [eeB, AlgEquiv.trans_apply, hCast_x, borelEquivH'_symm_x]

variable (v₁ : Gen r₂) (hv₁ : labJ j h₂ v₁ = i.succ)

theorem eeHc (j' : Fin (m + 1)) :
    Fintype.card {x : Gen r₁ // x.1 = j'} = Fintype.card {x : Gen r₂ // labJ j h₂ x = j'} := by
  rw [card_fibre_sigma, card_moveLab, h₂.1]

/-- The relabelling `Gen r₁ ≃ Gen r₂` sending the variable moved by `E_i` to `v₁`. -/
def eeRel : Gen r₁ ≃ Gen r₂ :=
  relabel (Sigma.fst : Gen r₁ → Fin (m + 1)) (labJ j h₂) (movedVar i r₁ h₁.2) v₁ (eeHc j h₂)
    hv₁.symm

variable (K) in
/-- The left factor `H_{r₁^{+i}} ≅ BorelRing (split labJ v₁)`. -/
def eeM : ERing K i r₁ h₁.2 ≃ₐ[K] BorelRing K (splitLab (labJ j h₂) v₁) :=
  borelCongr K (eeRel i j h₁ h₂ v₁ hv₁) (relabel_split _ _ _ _ _ _)

theorem eeRel_lab (x : Gen r₁) : labJ j h₂ (eeRel i j h₁ h₂ v₁ hv₁ x) = x.1 :=
  relabel_lab _ _ _ _ _ _ x

theorem eeRel_move (x : Gen r₁) :
    moveLab (labJ j h₂) v₁ i.castSucc (eeRel i j h₁ h₂ v₁ hv₁ x) =
      moveLab (Sigma.fst : Gen r₁ → Fin (m + 1)) (movedVar i r₁ h₁.2) i.castSucc x :=
  relabel_move _ _ _ _ _ _ i.castSucc x

theorem eeRel_self : eeRel i j h₁ h₂ v₁ hv₁ (movedVar i r₁ h₁.2) = v₁ := relabel_self _ _ _ _ _ _

theorem eeM_right (b : H K r₁) :
    eeM K i j h₁ h₂ v₁ hv₁ (eRight K i r₁ h₁.2 b) = pR K (labJ j h₂) v₁ (eeB K j h₂ b) := by
  have hb : borelCongr K (eeRel i j h₁ h₂ v₁ hv₁) (eeRel_lab i j h₁ h₂ v₁ hv₁) (hEquiv K r₁ b) =
      eeB K j h₂ b := by
    have : ((borelCongr K (eeRel i j h₁ h₂ v₁ hv₁) (eeRel_lab i j h₁ h₂ v₁ hv₁)).toAlgHom.comp
        (hEquiv K r₁).toAlgHom) = (eeB K j h₂).toAlgHom :=
      algHom_H_ext fun j' α => by
        simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, hEquiv_x,
          borelCongr_xB, eeB_x]
    exact congrArg (fun φ : H K r₁ →ₐ[K] _ => φ b) this
  rw [eRight, AlgHom.comp_apply, eeM, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, pR,
    borelCongr_refineHom K _ _ (eeRel_lab i j h₁ h₂ v₁ hv₁) _ (refines_splitLab _ _), hb]
  rfl

include h₁ hv₁ in
theorem eeHcA (j' : Fin (m + 1)) :
    Fintype.card {x : Gen r₂ // moveLab (labJ j h₂) v₁ i.castSucc x = j'} = t j' := by
  rw [← h₁.1, ← card_moveLab i r₁ h₁.2 j']
  exact Fintype.card_congr ((eeRel i j h₁ h₂ v₁ hv₁).subtypeEquiv fun x => by
    rw [eeRel_move]).symm

variable (K) in
/-- The left outer ring `H_t ≅ BorelRing (move labJ v₁ i)`. -/
def eeA : H K t ≃ₐ[K] BorelRing K (moveLab (labJ j h₂) v₁ i.castSucc) :=
  (borelEquivH' K _ t (eeHcA i j h₁ h₂ v₁ hv₁)).symm

theorem eeM_left (a : H K t) :
    eeM K i j h₁ h₂ v₁ hv₁ (eLeft K i r₁ h₁.2 (hCast K h₁.1.symm a)) =
      pL K (labJ j h₂) v₁ i.castSucc (eeA K i j h₁ h₂ v₁ hv₁ a) := by
  have ha : borelCongr K (eeRel i j h₁ h₂ v₁ hv₁) (eeRel_move i j h₁ h₂ v₁ hv₁)
      ((borelEquivH' K _ (raise i r₁) (card_moveLab i r₁ h₁.2)).symm (hCast K h₁.1.symm a)) =
      eeA K i j h₁ h₂ v₁ hv₁ a := by
    have : ((borelCongr K (eeRel i j h₁ h₂ v₁ hv₁) (eeRel_move i j h₁ h₂ v₁ hv₁)).toAlgHom.comp
        ((borelEquivH' K _ (raise i r₁) (card_moveLab i r₁ h₁.2)).symm.toAlgHom.comp
          (hCast K h₁.1.symm).toAlgHom)) = (eeA K i j h₁ h₂ v₁ hv₁).toAlgHom :=
      algHom_H_ext fun j' α => by
        simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, hCast_x,
          borelEquivH'_symm_x, borelCongr_xB, eeA]
    exact congrArg (fun φ : H K t →ₐ[K] _ => φ a) this
  rw [eLeft, AlgHom.comp_apply, eeM, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, pL,
    borelCongr_refineHom K _ _ (eeRel_move i j h₁ h₂ v₁ hv₁) _ (refines_splitLab_move _ _ _), ha]
  rfl

theorem eeM_xi : eeM K i j h₁ h₂ v₁ hv₁ (eXi K i r₁ h₁.2) = xi K (labJ j h₂) v₁ := by
  rw [eeM, eXi, xi]
  refine borelCongr_mk K _ _ _ _ ?_
  change MvPolynomial.rename (eeRel i j h₁ h₂ v₁ hv₁) (MvPolynomial.X (movedVar i r₁ h₁.2)) =
    MvPolynomial.X v₁
  rw [MvPolynomial.rename_X, eeRel_self]

variable (K) in
/-- **The Borel model of two upward strands**:
`Γ(E_i E_j 1) ≅ H(split (move v₂ j) v₁) ⊗_{H(move v₂ j)} H(split v₂)` on the variables `Gen r₂`. -/
def eeEquiv : BRing.TT (stepB K (true, i) r₁ t h₁) (stepB K (true, j) r₂ r₁ h₂) ≃+*
    EERing (k := K) (Sigma.fst : Gen r₂ → Fin (m + 1)) v₁ (movedVar j r₂ h₂.2) j.castSucc :=
  BRing.tensorRingEquiv (stepB K (true, i) r₁ t h₁) (stepB K (true, j) r₂ r₁ h₂)
    (eeB K j h₂).toRingEquiv (eeM K i j h₁ h₂ v₁ hv₁).toRingEquiv (RingEquiv.refl _)
    (fun b => by
      show eeM K i j h₁ h₂ v₁ hv₁ (eRight K i r₁ h₁.2 b) = pR K (labJ j h₂) v₁ (eeB K j h₂ b)
      exact eeM_right i j h₁ h₂ v₁ hv₁ b)
    (fun _ => rfl)

theorem eeEquiv_tmul (a : ERing K i r₁ h₁.2) (b : ERing K j r₂ h₂.2) :
    eeEquiv K i j h₁ h₂ v₁ hv₁ (BRing.tmul _ _ a b) = eeM K i j h₁ h₂ v₁ hv₁ a ⊗ₜ b := by
  unfold eeEquiv
  rw [BRing.tensorRingEquiv_tmul]
  rfl

theorem eeEquiv_left (a : H K t) :
    eeEquiv K i j h₁ h₂ v₁ hv₁ (((stepB K (true, i) r₁ t h₁).tensor (stepB K (true, j) r₂ r₁ h₂)).left a) =
      pL K (labJ j h₂) v₁ i.castSucc (eeA K i j h₁ h₂ v₁ hv₁ a) ⊗ₜ 1 := by
  rw [BRing.tensor_left, eeEquiv_tmul]
  exact congrArg (· ⊗ₜ _) (eeM_left i j h₁ h₂ v₁ hv₁ a)

theorem eeEquiv_right (c : H K r₂) :
    eeEquiv K i j h₁ h₂ v₁ hv₁ (((stepB K (true, i) r₁ t h₁).tensor (stepB K (true, j) r₂ r₁ h₂)).right c) =
      1 ⊗ₜ pR K (Sigma.fst : Gen r₂ → Fin (m + 1)) (movedVar j r₂ h₂.2) (hEquiv K r₂ c) := by
  rw [BRing.tensor_right, eeEquiv_tmul, map_one]
  rfl

theorem eeEquiv_xi_left :
    eeEquiv K i j h₁ h₂ v₁ hv₁ (BRing.tmul _ _ (eXi K i r₁ h₁.2) 1) = xi K (labJ j h₂) v₁ ⊗ₜ 1 := by
  rw [eeEquiv_tmul, eeM_xi]

theorem eeEquiv_xi_right :
    eeEquiv K i j h₁ h₂ v₁ hv₁ (BRing.tmul _ _ 1 (eXi K j r₂ h₂.2)) =
      1 ⊗ₜ xi K (Sigma.fst : Gen r₂ → Fin (m + 1)) (movedVar j r₂ h₂.2) := by
  rw [eeEquiv_tmul, map_one]
  rfl

end EEModel

/-! ### Two strands of the same colour (nilHecke) -/

section SameColour

variable {K : Type u} [Field K] {m : ℕ}

attribute [local instance] rightAlgebra midAlgebra jointAlgebra

theorem crossEE_add {V : Type*} [Fintype V] [DecidableEq V] {J : Type*} [Fintype J]
    [DecidableEq J] (lab : V → J) (v₁ v₂ : V) (j₂ : J) (hne : v₁ ≠ v₂) (hj : lab v₁ ≠ j₂)
    (a b : EERing (k := K) lab v₁ v₂ j₂) :
    crossEE K lab v₁ v₂ j₂ hne hj (a + b) =
      crossEE K lab v₁ v₂ j₂ hne hj a + crossEE K lab v₁ v₂ j₂ hne hj b := by
  apply (tensorEquiv K lab v₁ v₂ j₂ hne hj).injective
  rw [tensorEquiv_crossEE, map_add, map_add, map_add, tensorEquiv_crossEE, tensorEquiv_crossEE]

variable (i : Fin m) {t r₁ r₂ : Comp m} (h₁ : StepR (true, i) r₁ t) (h₂ : StepR (true, i) r₂ r₁)
  (v₁ : Gen r₂) (hv₁ : labJ i h₂ v₁ = i.succ)

include hv₁ in
theorem ee_ne : v₁ ≠ movedVar i r₂ h₂.2 := by
  rintro rfl
  rw [labJ, moveLab_self] at hv₁
  exact (Fin.castSucc_lt_succ i).ne hv₁

include hv₁ in
theorem ee_lab : v₁.1 = i.succ := by
  have := hv₁
  rw [labJ, moveLab, Function.update_of_ne (ee_ne i h₂ v₁ hv₁)] at this
  exact this

include hv₁ in
theorem ee_hj : (Sigma.fst : Gen r₂ → Fin (m + 1)) v₁ ≠ i.castSucc := by
  rw [ee_lab i h₂ v₁ hv₁]; exact (Fin.castSucc_lt_succ i).ne'

/-- The two-strand bimodule `Γ(E_i E_i 1)` of the path model. -/
abbrev EEP : BRing (H K t) (H K r₂) := (stepB K (true, i) r₁ t h₁).tensor (stepB K (true, i) r₂ r₁ h₂)

/-- The dot on the left strand of `Γ(E_i E_i 1)`. -/
abbrev xiL : (EEP (K := K) i h₁ h₂).T := BRing.tmul _ _ (eXi K i r₁ h₁.2) 1

/-- The dot on the right strand of `Γ(E_i E_i 1)`. -/
abbrev xiR : (EEP (K := K) i h₁ h₂).T := BRing.tmul _ _ 1 (eXi K i r₂ h₂.2)

variable (K) in
/-- **`Γ` of the upward crossing of two strands coloured `i`** (KL III (6.8), `i = j`) on the
path model, transported from the divided difference `crossEE` of the Borel model. -/
def crossEEP : BHom (EEP (K := K) i h₁ h₂) (EEP (K := K) i h₁ h₂) where
  toFun y := (eeEquiv K i i h₁ h₂ v₁ hv₁).symm (crossEE K (Sigma.fst : Gen r₂ → Fin (m + 1)) v₁
    (movedVar i r₂ h₂.2) i.castSucc (ee_ne i h₂ v₁ hv₁) (ee_hj i h₂ v₁ hv₁)
    (eeEquiv K i i h₁ h₂ v₁ hv₁ y))
  map_add a b := by
    rw [map_add, crossEE_add, map_add]
  map_left a y := by
    rw [map_mul, eeEquiv_left, crossEE_left, map_mul]
    congr 1
    rw [← eeEquiv_left i i h₁ h₂ v₁ hv₁ a, RingEquiv.symm_apply_apply]
  map_right c y := by
    rw [map_mul, eeEquiv_right, crossEE_right _ _ _ _ _ _
      ((ee_lab i h₂ v₁ hv₁).trans rfl), map_mul]
    congr 1
    rw [← eeEquiv_right i i h₁ h₂ v₁ hv₁ c, RingEquiv.symm_apply_apply]

theorem crossEEP_apply (y : (EEP (K := K) i h₁ h₂).T) :
    eeEquiv K i i h₁ h₂ v₁ hv₁ (crossEEP K i h₁ h₂ v₁ hv₁ y) =
      crossEE K (Sigma.fst : Gen r₂ → Fin (m + 1)) v₁ (movedVar i r₂ h₂.2) i.castSucc
        (ee_ne i h₂ v₁ hv₁) (ee_hj i h₂ v₁ hv₁) (eeEquiv K i i h₁ h₂ v₁ hv₁ y) :=
  RingEquiv.apply_symm_apply _ _

/-- **The nilHecke relation `ψ² = 0`** (KL III Definition 3.1, `i = j`; `KLR.Diagram.Rel.sqEq`). -/
theorem crossEEP_sq : (crossEEP K i h₁ h₂ v₁ hv₁).comp (crossEEP K i h₁ h₂ v₁ hv₁) = 0 := by
  refine BHom.ext fun y => ?_
  apply (eeEquiv K i i h₁ h₂ v₁ hv₁).injective
  rw [BHom.comp_apply, crossEEP_apply, crossEEP_apply, crossEE_crossEE, BHom.zero_apply, map_zero]

/-- **Dot slide** `ψ ∘ x_left = 1 + x_right ∘ ψ` (KL III Definition 3.1, `i = j`;
`KLR.Diagram.Rel.slideREq`). -/
theorem crossEEP_xiL :
    (crossEEP K i h₁ h₂ v₁ hv₁).comp (BHom.mulB (xiL i h₁ h₂)) =
      BHom.id _ + (BHom.mulB (xiR i h₁ h₂)).comp (crossEEP K i h₁ h₂ v₁ hv₁) := by
  refine BHom.ext fun y => ?_
  apply (eeEquiv K i i h₁ h₂ v₁ hv₁).injective
  rw [BHom.comp_apply, crossEEP_apply, BHom.mulB_apply, map_mul, eeEquiv_xi_left,
    crossEE_xi_left, BHom.add_apply, BHom.id_apply, BHom.comp_apply, BHom.mulB_apply, map_add,
    map_mul, crossEEP_apply, eeEquiv_xi_right]

/-- **Dot slide** `ψ ∘ x_right = x_left ∘ ψ - 1` (KL III Definition 3.1, `i = j`;
`KLR.Diagram.Rel.slideLEq`). -/
theorem crossEEP_xiR :
    (crossEEP K i h₁ h₂ v₁ hv₁).comp (BHom.mulB (xiR i h₁ h₂)) =
      (BHom.mulB (xiL i h₁ h₂)).comp (crossEEP K i h₁ h₂ v₁ hv₁) - BHom.id _ := by
  refine BHom.ext fun y => ?_
  apply (eeEquiv K i i h₁ h₂ v₁ hv₁).injective
  rw [BHom.comp_apply, crossEEP_apply, BHom.mulB_apply, map_mul, eeEquiv_xi_right,
    crossEE_xi_right, BHom.sub_apply, BHom.id_apply, BHom.comp_apply, BHom.mulB_apply, map_sub,
    map_mul, crossEEP_apply, eeEquiv_xi_left]

end SameColour

/-! ### Transport of bimodule maps -/

section Transport

variable {A B : Type u} [CommRing A] [CommRing B] {M N : BRing A B} {X Y : Type u} [CommRing X]
  [CommRing Y]

/-- A map `f : X → Y` between models `Φ : M.T ≅ X`, `Ψ : N.T ≅ Y`, additive and compatible with
the actions, gives a bimodule map `M → N`. -/
def transportBHom (Φ : M.T ≃+* X) (Ψ : N.T ≃+* Y) (f : X → Y) (hadd : ∀ a b, f (a + b) = f a + f b)
    (hl : ∀ a y, f (Φ (M.left a) * y) = Ψ (N.left a) * f y)
    (hr : ∀ c y, f (Φ (M.right c) * y) = Ψ (N.right c) * f y) : BHom M N where
  toFun y := Ψ.symm (f (Φ y))
  map_add a b := by rw [map_add, hadd, map_add]
  map_left a y := by rw [map_mul, hl, map_mul, RingEquiv.symm_apply_apply]
  map_right c y := by rw [map_mul, hr, map_mul, RingEquiv.symm_apply_apply]

theorem transportBHom_apply (Φ : M.T ≃+* X) (Ψ : N.T ≃+* Y) (f : X → Y) (hadd) (hl) (hr)
    (y : M.T) : Ψ (transportBHom Φ Ψ f hadd hl hr y) = f (Φ y) :=
  RingEquiv.apply_symm_apply _ _

end Transport

/-! ### Two strands of distant colours -/

section Far

variable {K : Type u} [Field K] {m : ℕ}

attribute [local instance] rightAlgebra midAlgebra jointAlgebra

section FarBorel

variable {V : Type*} [Fintype V] [DecidableEq V] {J : Type*} [Fintype J] [DecidableEq J]
  (lab : V → J) (v₁ v₂ : V) (j₁ j₂ : J) (hne : v₁ ≠ v₂) (h₁ : lab v₁ ≠ j₂) (h₂ : lab v₂ ≠ j₁)

theorem crossFar_apply' (t : EERing (k := K) lab v₁ v₂ j₂) :
    tensorEquiv K lab v₂ v₁ j₁ hne.symm h₂ (crossFar K lab v₁ v₂ j₁ j₂ hne h₁ h₂ t) =
      refineHom K (refines_joint_swap hne) (tensorEquiv K lab v₁ v₂ j₂ hne h₁ t) :=
  AlgEquiv.apply_symm_apply _ _

theorem crossFar_add' (a b : EERing (k := K) lab v₁ v₂ j₂) :
    crossFar K lab v₁ v₂ j₁ j₂ hne h₁ h₂ (a + b) =
      crossFar K lab v₁ v₂ j₁ j₂ hne h₁ h₂ a + crossFar K lab v₁ v₂ j₁ j₂ hne h₁ h₂ b := by
  simp only [crossFar, map_add]

theorem crossFar_mul' (a b : EERing (k := K) lab v₁ v₂ j₂) :
    crossFar K lab v₁ v₂ j₁ j₂ hne h₁ h₂ (a * b : EERing (k := K) lab v₁ v₂ j₂) =
      (crossFar K lab v₁ v₂ j₁ j₂ hne h₁ h₂ a * crossFar K lab v₁ v₂ j₁ j₂ hne h₁ h₂ b :
        EERing (k := K) lab v₂ v₁ j₁) := by
  simp only [crossFar, map_mul]

include hne in
theorem refines_outer_far :
    Refines (moveLab (moveLab lab v₁ j₁) v₂ j₂) (moveLab (moveLab lab v₂ j₂) v₁ j₁) :=
  refines_of_eq (moveLab_comm hne j₁ j₂).symm

/-- `crossFar` is a map of left modules over the outer ring. -/
theorem crossFar_left (q : BorelRing K (moveLab (moveLab lab v₂ j₂) v₁ j₁))
    (t : EERing (k := K) lab v₁ v₂ j₂) :
    crossFar K lab v₁ v₂ j₁ j₂ hne h₁ h₂ ((pL K (moveLab lab v₂ j₂) v₁ j₁ q ⊗ₜ 1) * t) =
      (pL K (moveLab lab v₁ j₁) v₂ j₂ (refineHom K (refines_outer_far lab v₁ v₂ j₁ j₂ hne) q) ⊗ₜ 1) *
        crossFar K lab v₁ v₂ j₁ j₂ hne h₁ h₂ t := by
  rw [crossFar_mul']
  congr 1
  apply (tensorEquiv K lab v₂ v₁ j₁ hne.symm h₂).injective
  rw [crossFar_apply']
  simp only [tensorEquiv, AlgEquiv.coe_ofBijective]
  rw [jointMap_tmul, jointMap_tmul, map_one, map_one, mul_one, mul_one]
  simp only [pL, refineHom_comp_apply]

/-- `crossFar` on a dot of the left strand. -/
theorem crossFar_xi_left (t : EERing (k := K) lab v₁ v₂ j₂) :
    crossFar K lab v₁ v₂ j₁ j₂ hne h₁ h₂ ((xi K (moveLab lab v₂ j₂) v₁ ⊗ₜ 1) * t) =
      (1 ⊗ₜ xi K lab v₁) * crossFar K lab v₁ v₂ j₁ j₂ hne h₁ h₂ t := by
  rw [crossFar_mul']
  congr 1
  simpa using crossFar_xi (k := K) lab v₁ v₂ j₁ j₂ hne h₁ h₂ 1 0

/-- `crossFar` on a dot of the right strand. -/
theorem crossFar_xi_right (t : EERing (k := K) lab v₁ v₂ j₂) :
    crossFar K lab v₁ v₂ j₁ j₂ hne h₁ h₂ ((1 ⊗ₜ xi K lab v₂) * t) =
      (xi K (moveLab lab v₁ j₁) v₂ ⊗ₜ 1) * crossFar K lab v₁ v₂ j₁ j₂ hne h₁ h₂ t := by
  rw [crossFar_mul']
  congr 1
  simpa using crossFar_xi (k := K) lab v₁ v₂ j₁ j₂ hne h₁ h₂ 0 1

end FarBorel

end Far

/-! ### Relabelling the outer ring -/

section OuterRing

variable {K : Type u} [Field K] {m : ℕ}

theorem refineHom_xB_of_eq {V : Type*} [Fintype V] [DecidableEq V] {J : Type*} [Fintype J]
    [DecidableEq J] {l₁ l₂ : V → J}
    (h : l₁ = l₂) (hr : Refines l₂ l₁) (j : J) (α : ℕ) :
    refineHom K hr (xB K l₁ j α) = xB K l₂ j α := by
  subst h; exact refineHom_self hr _

/-- The outer left rings of two Borel models of `E_i E_j 1` and `E_j E_i 1` with the same final
labelling agree. -/
theorem eeA_refine (i j : Fin m) {t r₁ r₂ : Comp m} (h₁ : StepR (true, i) r₁ t)
    (h₂ : StepR (true, j) r₂ r₁) (v₁ : Gen r₂) (hv₁ : labJ j h₂ v₁ = i.succ) {r₁' : Comp m}
    (h₁' : StepR (true, j) r₁' t) (h₂' : StepR (true, i) r₂ r₁') (v₁' : Gen r₂)
    (hv₁' : labJ i h₂' v₁' = j.succ)
    (heq : moveLab (labJ j h₂) v₁ i.castSucc = moveLab (labJ i h₂') v₁' j.castSucc) (a : H K t) :
    refineHom K (refines_of_eq heq.symm) (eeA K i j h₁ h₂ v₁ hv₁ a) = eeA K j i h₁' h₂' v₁' hv₁' a := by
  have : (refineHom K (refines_of_eq heq.symm)).comp (eeA K i j h₁ h₂ v₁ hv₁).toAlgHom =
      (eeA K j i h₁' h₂' v₁' hv₁').toAlgHom :=
    algHom_H_ext fun j' α => by
      simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, eeA,
        borelEquivH'_symm_x, refineHom_xB_of_eq heq]
  exact congrArg (fun φ : H K t →ₐ[K] _ => φ a) this

end OuterRing

/-! ### The crossing of distant colours on the path model -/

section FarPath

variable {K : Type u} [Field K] {m : ℕ}

attribute [local instance] rightAlgebra midAlgebra jointAlgebra

theorem movedVar_ne (i j : Fin m) (hij : i ≠ j) {r₂ : Comp m} (hi : 0 < r₂ i.succ)
    (hj : 0 < r₂ j.succ) : movedVar i r₂ hi ≠ movedVar j r₂ hj := by
  intro h
  exact hij (Fin.succ_injective _ (congrArg Sigma.fst h))

theorem far_hv (i j : Fin m) (hij : i ≠ j) {r₁ r₁' r₂ : Comp m} (h₂ : StepR (true, j) r₂ r₁)
    (h₂' : StepR (true, i) r₂ r₁') : labJ j h₂ (movedVar i r₂ h₂'.2) = i.succ := by
  rw [labJ, moveLab, Function.update_of_ne (movedVar_ne i j hij h₂'.2 h₂.2)]
  rfl

/-- The two-strand bimodule `Γ(E_a E_b 1)` of the path model. -/
abbrev TwoP {a b : Fin m} {t r₁ r₂ : Comp m} (h₁ : StepR (true, a) r₁ t)
    (h₂ : StepR (true, b) r₂ r₁) : BRing (H K t) (H K r₂) :=
  (stepB K (true, a) r₁ t h₁).tensor (stepB K (true, b) r₂ r₁ h₂)

theorem far_heq (i j : Fin m) (hij : i ≠ j) {r₁ r₁' r₂ : Comp m} (h₂ : StepR (true, j) r₂ r₁)
    (h₂' : StepR (true, i) r₂ r₁') :
    moveLab (labJ j h₂) (movedVar i r₂ h₂'.2) i.castSucc =
      moveLab (labJ i h₂') (movedVar j r₂ h₂.2) j.castSucc :=
  moveLab_comm (movedVar_ne i j hij h₂'.2 h₂.2) i.castSucc j.castSucc

variable (K) in
/-- **`Γ` of the upward crossing `E_i E_j → E_j E_i` for distant colours** (KL III (6.8),
`i · j = 0`: `ξ_i^{a} ⊗ ξ_j^{b} ↦ ξ_j^{b} ⊗ ξ_i^{a}`) on the path model: the crossing `crossFar`
of the Borel model, in which `E_j` moves `⟨j+1, 0⟩` and `E_i` moves `⟨i+1, 0⟩`. -/
def crossFarP (i j : Fin m) (hij : i ≠ j) (hf₁ : i.succ ≠ j.castSucc) (hf₂ : j.succ ≠ i.castSucc)
    {t r₁ r₂ r₁' : Comp m} (h₁ : StepR (true, i) r₁ t) (h₂ : StepR (true, j) r₂ r₁)
    (h₁' : StepR (true, j) r₁' t) (h₂' : StepR (true, i) r₂ r₁') :
    BHom (TwoP (K := K) h₁ h₂) (TwoP (K := K) h₁' h₂') :=
  transportBHom (eeEquiv K i j h₁ h₂ (movedVar i r₂ h₂'.2) (far_hv i j hij h₂ h₂'))
    (eeEquiv K j i h₁' h₂' (movedVar j r₂ h₂.2) (far_hv j i hij.symm h₂' h₂))
    (crossFar K (Sigma.fst : Gen r₂ → Fin (m + 1)) (movedVar i r₂ h₂'.2) (movedVar j r₂ h₂.2)
      i.castSucc j.castSucc (movedVar_ne i j hij h₂'.2 h₂.2) hf₁ hf₂)
    (crossFar_add' _ _ _ _ _ _ _ _)
    (fun a y => by
      rw [eeEquiv_left, crossFar_left, eeEquiv_left]
      congr 3
      exact eeA_refine i j h₁ h₂ _ _ h₁' h₂' _ _ (far_heq i j hij h₂ h₂') a)
    (fun c y => by
      rw [eeEquiv_right, crossFar_right, eeEquiv_right])

variable (i j : Fin m) (hij : i ≠ j) (hf₁ : i.succ ≠ j.castSucc) (hf₂ : j.succ ≠ i.castSucc)
  {t r₁ r₂ r₁' : Comp m} (h₁ : StepR (true, i) r₁ t) (h₂ : StepR (true, j) r₂ r₁)
  (h₁' : StepR (true, j) r₁' t) (h₂' : StepR (true, i) r₂ r₁')

theorem crossFarP_apply (y : (TwoP (K := K) h₁ h₂).T) :
    eeEquiv K j i h₁' h₂' (movedVar j r₂ h₂.2) (far_hv j i hij.symm h₂' h₂)
        (crossFarP K i j hij hf₁ hf₂ h₁ h₂ h₁' h₂' y) =
      crossFar K (Sigma.fst : Gen r₂ → Fin (m + 1)) (movedVar i r₂ h₂'.2) (movedVar j r₂ h₂.2)
        i.castSucc j.castSucc (movedVar_ne i j hij h₂'.2 h₂.2) hf₁ hf₂
        (eeEquiv K i j h₁ h₂ (movedVar i r₂ h₂'.2) (far_hv i j hij h₂ h₂') y) := by
  unfold crossFarP
  exact transportBHom_apply (M := TwoP (K := K) h₁ h₂) (N := TwoP (K := K) h₁' h₂') _ _ _ _ _ _ y

/-- **The relation `ψ_{ji} ψ_{ij} = 1` for distant colours** (KL III (4.11), `i · j = 0`;
`KLR.Diagram.Rel.sqNe` with `Q^τ_{ij} = 1`) on the path model. -/
theorem crossFarP_sq :
    (crossFarP K j i hij.symm hf₂ hf₁ h₁' h₂' h₁ h₂).comp
      (crossFarP K i j hij hf₁ hf₂ h₁ h₂ h₁' h₂') = BHom.id _ := by
  refine BHom.ext fun y => ?_
  apply (eeEquiv K i j h₁ h₂ (movedVar i r₂ h₂'.2) (far_hv i j hij h₂ h₂')).injective
  rw [BHom.comp_apply, BHom.id_apply]
  exact (crossFarP_apply j i hij.symm hf₂ hf₁ h₁' h₂' h₁ h₂ _).trans
    ((congrArg _ (crossFarP_apply i j hij hf₁ hf₂ h₁ h₂ h₁' h₂' y)).trans
      (crossFar_crossFar _ _ _ _ _ _ _ _ _))

/-- **Dot slide** for distant colours (KL III (4.12)): a dot on the left strand (`i`) before the
crossing is a dot on the right strand after it. -/
theorem crossFarP_xiL :
    (crossFarP K i j hij hf₁ hf₂ h₁ h₂ h₁' h₂').comp
        (BHom.mulB (BRing.tmul _ _ (eXi K i r₁ h₁.2) 1)) =
      (BHom.mulB (BRing.tmul _ _ 1 (eXi K i r₂ h₂'.2))).comp
        (crossFarP K i j hij hf₁ hf₂ h₁ h₂ h₁' h₂') := by
  refine BHom.ext fun y => ?_
  apply (eeEquiv K j i h₁' h₂' (movedVar j r₂ h₂.2) (far_hv j i hij.symm h₂' h₂)).injective
  rw [BHom.comp_apply, BHom.comp_apply, BHom.mulB_apply, BHom.mulB_apply, crossFarP_apply,
    map_mul, map_mul, eeEquiv_xi_left, crossFar_xi_left, crossFarP_apply, eeEquiv_xi_right]

/-- **Dot slide** for distant colours (KL III (4.12)): a dot on the right strand (`j`) before the
crossing is a dot on the left strand after it. -/
theorem crossFarP_xiR :
    (crossFarP K i j hij hf₁ hf₂ h₁ h₂ h₁' h₂').comp
        (BHom.mulB (BRing.tmul _ _ 1 (eXi K j r₂ h₂.2))) =
      (BHom.mulB (BRing.tmul _ _ (eXi K j r₁' h₁'.2) 1)).comp
        (crossFarP K i j hij hf₁ hf₂ h₁ h₂ h₁' h₂') := by
  refine BHom.ext fun y => ?_
  apply (eeEquiv K j i h₁' h₂' (movedVar j r₂ h₂.2) (far_hv j i hij.symm h₂' h₂)).injective
  rw [BHom.comp_apply, BHom.comp_apply, BHom.mulB_apply, BHom.mulB_apply, crossFarP_apply,
    map_mul, map_mul, eeEquiv_xi_right, crossFar_xi_right, crossFarP_apply, eeEquiv_xi_left]

end FarPath

/-! ### Adjacent colours: the non-flag crossings with a general label `β` -/

section AdjBeta

variable {K : Type u} [Field K] {V : Type*} [Fintype V] [DecidableEq V] {J : Type*} [Fintype J]
  [DecidableEq J] (lab : V → J) (v w : V) (α β : J) (hβ : lab v = β) (hw : lab w ≠ β)
  (hα : lab w ≠ α)

attribute [local instance] rightAlgebra midAlgebra jointAlgebra

include hβ hw hα in
/-- `crossNF` with the label `β = lab v` of the block of `v` given separately. -/
def crossNFβ (t : EERing (k := K) lab v w β) : EERing (k := K) lab w v α := by
  subst hβ; exact crossNF α hw hα t

include hβ hw hα in
/-- `crossFN` with the label `β = lab v` of the block of `v` given separately. -/
def crossFNβ (s : EERing (k := K) lab w v α) : EERing (k := K) lab v w β := by
  subst hβ; exact crossFN α hw hα s

theorem crossNFβ_add (t t' : EERing (k := K) lab v w β) :
    crossNFβ lab v w α β hβ hw hα (t + t') =
      crossNFβ lab v w α β hβ hw hα t + crossNFβ lab v w α β hβ hw hα t' := by
  subst hβ; exact crossNF_add α hw hα t t'

theorem crossNFβ_mul (t t' : EERing (k := K) lab v w β) :
    crossNFβ lab v w α β hβ hw hα (t * t') =
      crossNFβ lab v w α β hβ hw hα t * crossNFβ lab v w α β hβ hw hα t' := by
  subst hβ; exact crossNF_mul α hw hα t t'

theorem crossFNβ_add (s s' : EERing (k := K) lab w v α) :
    crossFNβ lab v w α β hβ hw hα (s + s') =
      crossFNβ lab v w α β hβ hw hα s + crossFNβ lab v w α β hβ hw hα s' := by
  subst hβ; exact crossFN_add α hw hα s s'

theorem crossFNβ_crossNFβ (t : EERing (k := K) lab v w β) :
    crossFNβ lab v w α β hβ hw hα (crossNFβ lab v w α β hβ hw hα t) =
      ((xi K (moveLab lab w β) v ⊗ₜ[BorelRing K (moveLab lab w β)] (1 : BorelRing K (splitLab lab w))) -
        (1 ⊗ₜ xi K lab w)) * t := by
  subst hβ; exact crossFN_crossNF α hw hα t

theorem crossNFβ_crossFNβ (s : EERing (k := K) lab w v α) :
    crossNFβ lab v w α β hβ hw hα (crossFNβ lab v w α β hβ hw hα s) =
      (((1 : BorelRing K (splitLab (moveLab lab v α) w)) ⊗ₜ[BorelRing K (moveLab lab v α)]
        xi K lab v) - (xi K (moveLab lab v α) w ⊗ₜ 1)) * s := by
  subst hβ; exact crossNF_crossFN α hw hα s

theorem crossNFβ_xi₁_mul (t : EERing (k := K) lab v w β) :
    crossNFβ lab v w α β hβ hw hα
        ((xi K (moveLab lab w β) v ⊗ₜ[BorelRing K (moveLab lab w β)]
          (1 : BorelRing K (splitLab lab w))) * t) =
      ((1 : BorelRing K (splitLab (moveLab lab v α) w)) ⊗ₜ[BorelRing K (moveLab lab v α)]
        xi K lab v) * crossNFβ lab v w α β hβ hw hα t := by
  subst hβ; exact crossNF_xiN₁_mul α hw hα t

theorem crossNFβ_xi₂_mul (t : EERing (k := K) lab v w β) :
    crossNFβ lab v w α β hβ hw hα
        (((1 : BorelRing K (splitLab (moveLab lab w β) v)) ⊗ₜ[BorelRing K (moveLab lab w β)]
          xi K lab w) * t) =
      (xi K (moveLab lab v α) w ⊗ₜ[BorelRing K (moveLab lab v α)]
        (1 : BorelRing K (splitLab lab v))) * crossNFβ lab v w α β hβ hw hα t := by
  subst hβ; exact crossNF_xiN₂_mul α hw hα t

theorem crossFNβ_xw_mul (s : EERing (k := K) lab w v α) :
    crossFNβ lab v w α β hβ hw hα
        ((xi K (moveLab lab v α) w ⊗ₜ[BorelRing K (moveLab lab v α)]
          (1 : BorelRing K (splitLab lab v))) * s) =
      ((1 : BorelRing K (splitLab (moveLab lab w β) v)) ⊗ₜ[BorelRing K (moveLab lab w β)]
        xi K lab w) * crossFNβ lab v w α β hβ hw hα s := by
  subst hβ; exact crossFN_xw_mul α hw hα s

theorem crossFNβ_xv_mul (s : EERing (k := K) lab w v α) :
    crossFNβ lab v w α β hβ hw hα
        (((1 : BorelRing K (splitLab (moveLab lab v α) w)) ⊗ₜ[BorelRing K (moveLab lab v α)]
          xi K lab v) * s) =
      (xi K (moveLab lab w β) v ⊗ₜ[BorelRing K (moveLab lab w β)]
        (1 : BorelRing K (splitLab lab w))) * crossFNβ lab v w α β hβ hw hα s := by
  subst hβ; exact crossFN_xv_mul α hw hα s

theorem crossNFβ_right (r : BorelRing K lab) (t : EERing (k := K) lab v w β) :
    crossNFβ lab v w α β hβ hw hα
        (((1 : BorelRing K (splitLab (moveLab lab w β) v)) ⊗ₜ[BorelRing K (moveLab lab w β)]
          pR K lab w r) * t) =
      ((1 : BorelRing K (splitLab (moveLab lab v α) w)) ⊗ₜ[BorelRing K (moveLab lab v α)]
        pR K lab v r) * crossNFβ lab v w α β hβ hw hα t := by
  subst hβ; exact crossNF_right α hw hα r t

theorem crossFNβ_right (r : BorelRing K lab) (s : EERing (k := K) lab w v α) :
    crossFNβ lab v w α β hβ hw hα
        (((1 : BorelRing K (splitLab (moveLab lab v α) w)) ⊗ₜ[BorelRing K (moveLab lab v α)]
          pR K lab v r) * s) =
      ((1 : BorelRing K (splitLab (moveLab lab w β) v)) ⊗ₜ[BorelRing K (moveLab lab w β)]
        pR K lab w r) * crossFNβ lab v w α β hβ hw hα s := by
  subst hβ; exact crossFN_right α hw hα r s

include hβ hw in
theorem refines_outerβ :
    Refines (moveLab (moveLab lab v α) w β) (moveLab (moveLab lab w β) v α) := by
  subst hβ; exact refines_outer α (ne_of_lab_ne hw)

theorem crossNFβ_left (q : BorelRing K (moveLab (moveLab lab w β) v α))
    (t : EERing (k := K) lab v w β) :
    crossNFβ lab v w α β hβ hw hα ((pL K (moveLab lab w β) v α q ⊗ₜ[BorelRing K (moveLab lab w β)]
        (1 : BorelRing K (splitLab lab w))) * t) =
      (pL K (moveLab lab v α) w β (refineHom K (refines_outerβ lab v w α β hβ hw) q) ⊗ₜ[BorelRing K
        (moveLab lab v α)] (1 : BorelRing K (splitLab lab v))) * crossNFβ lab v w α β hβ hw hα t := by
  subst hβ; exact crossNF_left α hw hα q t

theorem crossFNβ_left (q : BorelRing K (moveLab (moveLab lab w β) v α))
    (s : EERing (k := K) lab w v α) :
    crossFNβ lab v w α β hβ hw hα ((pL K (moveLab lab v α) w β
        (refineHom K (refines_outerβ lab v w α β hβ hw) q) ⊗ₜ[BorelRing K (moveLab lab v α)]
          (1 : BorelRing K (splitLab lab v))) * s) =
      (pL K (moveLab lab w β) v α q ⊗ₜ[BorelRing K (moveLab lab w β)]
        (1 : BorelRing K (splitLab lab w))) * crossFNβ lab v w α β hβ hw hα s := by
  subst hβ; exact crossFN_left α hw hα q s

end AdjBeta

/-! ### The crossings of adjacent colours on the path model -/

section AdjPath

variable {K : Type u} [Field K] {m : ℕ}

attribute [local instance] rightAlgebra midAlgebra jointAlgebra

theorem adj_ne {i j : Fin m} (hadj : j.castSucc = i.succ) : i ≠ j := by
  rintro rfl
  exact (Fin.castSucc_lt_succ i).ne hadj

theorem adj_hα {i j : Fin m} (hadj : j.castSucc = i.succ) : j.succ ≠ i.castSucc := by
  intro h
  have h1 := congrArg Fin.val hadj
  have h2 := congrArg Fin.val h
  simp only [Fin.coe_castSucc, Fin.val_succ] at h1 h2
  omega

theorem adj_hw (j : Fin m) : j.succ ≠ j.castSucc := (Fin.castSucc_lt_succ j).ne'

variable (K) in
/-- **`Γ` of the upward crossing `E_i E_{i+1} → E_{i+1} E_i`** (KL III (6.8), case `i → j`:
`ξ_i^{a} ⊗ ξ_j^{b} ↦ ξ_j^{b} ⊗ ξ_i^{a}`) on the path model; `E_i E_{i+1} 1` is the non-flag tensor
product and the map is the restriction `crossNF`. Here `j = i + 1` (`hadj`). -/
def crossAdjNF (i j : Fin m) (hadj : j.castSucc = i.succ) {t r₁ r₂ r₁' : Comp m}
    (h₁ : StepR (true, i) r₁ t) (h₂ : StepR (true, j) r₂ r₁) (h₁' : StepR (true, j) r₁' t)
    (h₂' : StepR (true, i) r₂ r₁') : BHom (TwoP (K := K) h₁ h₂) (TwoP (K := K) h₁' h₂') :=
  transportBHom (eeEquiv K i j h₁ h₂ (movedVar i r₂ h₂'.2) (far_hv i j (adj_ne hadj) h₂ h₂'))
    (eeEquiv K j i h₁' h₂' (movedVar j r₂ h₂.2) (far_hv j i (adj_ne hadj).symm h₂' h₂))
    (crossNFβ (Sigma.fst : Gen r₂ → Fin (m + 1)) (movedVar i r₂ h₂'.2) (movedVar j r₂ h₂.2)
      i.castSucc j.castSucc hadj.symm (adj_hw j) (adj_hα hadj))
    (crossNFβ_add _ _ _ _ _ _ _ _)
    (fun a y => by
      rw [eeEquiv_left, crossNFβ_left, eeEquiv_left]
      congr 3
      exact eeA_refine i j h₁ h₂ _ _ h₁' h₂' _ _ (far_heq i j (adj_ne hadj) h₂ h₂') a)
    (fun c y => by
      rw [eeEquiv_right, crossNFβ_right, eeEquiv_right])

variable (K) in
/-- **`Γ` of the upward crossing `E_{i+1} E_i → E_i E_{i+1}`** (KL III (6.8), case `j → i`:
`ξ_i^{a} ⊗ ξ_j^{b} ↦ ξ_j^{b} ⊗ ξ_i^{a+1} - ξ_j^{b+1} ⊗ ξ_i^{a}`) on the path model: minus the
push-forward `crossFN` from the flag variety `E_{i+1} E_i 1` to the non-flag product. -/
def crossAdjFN (i j : Fin m) (hadj : j.castSucc = i.succ) {t r₁ r₂ r₁' : Comp m}
    (h₁ : StepR (true, i) r₁ t) (h₂ : StepR (true, j) r₂ r₁) (h₁' : StepR (true, j) r₁' t)
    (h₂' : StepR (true, i) r₂ r₁') : BHom (TwoP (K := K) h₁' h₂') (TwoP (K := K) h₁ h₂) :=
  transportBHom (eeEquiv K j i h₁' h₂' (movedVar j r₂ h₂.2) (far_hv j i (adj_ne hadj).symm h₂' h₂))
    (eeEquiv K i j h₁ h₂ (movedVar i r₂ h₂'.2) (far_hv i j (adj_ne hadj) h₂ h₂'))
    (fun s => -crossFNβ (Sigma.fst : Gen r₂ → Fin (m + 1)) (movedVar i r₂ h₂'.2)
      (movedVar j r₂ h₂.2) i.castSucc j.castSucc hadj.symm (adj_hw j) (adj_hα hadj) s)
    (fun a b => by beta_reduce; rw [crossFNβ_add, neg_add])
    (fun a y => by
      beta_reduce
      rw [eeEquiv_left, eeEquiv_left, ← eeA_refine i j h₁ h₂ _ _ h₁' h₂' _ _
        (far_heq i j (adj_ne hadj) h₂ h₂') a, crossFNβ_left, mul_neg])
    (fun c y => by
      beta_reduce
      rw [eeEquiv_right, crossFNβ_right, eeEquiv_right, mul_neg])

variable (i j : Fin m) (hadj : j.castSucc = i.succ) {t r₁ r₂ r₁' : Comp m}
  (h₁ : StepR (true, i) r₁ t) (h₂ : StepR (true, j) r₂ r₁) (h₁' : StepR (true, j) r₁' t)
  (h₂' : StepR (true, i) r₂ r₁')

theorem crossAdjNF_apply (y : (TwoP (K := K) h₁ h₂).T) :
    eeEquiv K j i h₁' h₂' (movedVar j r₂ h₂.2) (far_hv j i (adj_ne hadj).symm h₂' h₂)
        (crossAdjNF K i j hadj h₁ h₂ h₁' h₂' y) =
      crossNFβ (Sigma.fst : Gen r₂ → Fin (m + 1)) (movedVar i r₂ h₂'.2) (movedVar j r₂ h₂.2)
        i.castSucc j.castSucc hadj.symm (adj_hw j) (adj_hα hadj)
        (eeEquiv K i j h₁ h₂ (movedVar i r₂ h₂'.2) (far_hv i j (adj_ne hadj) h₂ h₂') y) := by
  unfold crossAdjNF
  exact transportBHom_apply (M := TwoP (K := K) h₁ h₂) (N := TwoP (K := K) h₁' h₂') _ _ _ _ _ _ y

theorem crossAdjFN_apply (y : (TwoP (K := K) h₁' h₂').T) :
    eeEquiv K i j h₁ h₂ (movedVar i r₂ h₂'.2) (far_hv i j (adj_ne hadj) h₂ h₂')
        (crossAdjFN K i j hadj h₁ h₂ h₁' h₂' y) =
      -crossFNβ (Sigma.fst : Gen r₂ → Fin (m + 1)) (movedVar i r₂ h₂'.2) (movedVar j r₂ h₂.2)
        i.castSucc j.castSucc hadj.symm (adj_hw j) (adj_hα hadj)
        (eeEquiv K j i h₁' h₂' (movedVar j r₂ h₂.2) (far_hv j i (adj_ne hadj).symm h₂' h₂) y) := by
  unfold crossAdjFN
  exact transportBHom_apply (M := TwoP (K := K) h₁' h₂') (N := TwoP (K := K) h₁ h₂) _ _ _ _ _ _ y

/-- **KL III (4.11)/(6.19) for `i · j = -1` on `E_i E_{i+1}`**: the double crossing is
`(i - (i+1)) (x_left - x_right) = x_right - x_left` (`KLR.Diagram.Rel.sqNe` with
`Q^τ_{i,i+1}(u, v) = -(u - v)`). -/
theorem crossAdj_sq_NF :
    (crossAdjFN K i j hadj h₁ h₂ h₁' h₂').comp (crossAdjNF K i j hadj h₁ h₂ h₁' h₂') =
      BHom.mulB (BRing.tmul _ _ 1 (eXi K j r₂ h₂.2) - BRing.tmul _ _ (eXi K i r₁ h₁.2) 1) := by
  refine BHom.ext fun y => ?_
  apply (eeEquiv K i j h₁ h₂ (movedVar i r₂ h₂'.2) (far_hv i j (adj_ne hadj) h₂ h₂')).injective
  rw [BHom.comp_apply, crossAdjFN_apply, crossAdjNF_apply, crossFNβ_crossNFβ, BHom.mulB_apply,
    map_mul, map_sub, eeEquiv_xi_left, eeEquiv_xi_right, ← neg_mul, neg_sub]

theorem crossNFβ_neg {V : Type*} [Fintype V] [DecidableEq V] {J : Type*} [Fintype J]
    [DecidableEq J] (lab : V → J) (v w : V) (α β : J) (hβ : lab v = β) (hw : lab w ≠ β)
    (hα : lab w ≠ α) (s : EERing (k := K) lab v w β) :
    crossNFβ lab v w α β hβ hw hα (-s) = -crossNFβ lab v w α β hβ hw hα s := by
  rw [eq_neg_iff_add_eq_zero, ← crossNFβ_add, neg_add_cancel]
  subst hβ
  simp only [crossNFβ, crossNF_apply, map_zero]

/-- **KL III (4.11)/(6.19) for `i · j = -1` on `E_{i+1} E_i`**: the double crossing is
`((i+1) - i)(x_left - x_right) = x_left - x_right`. -/
theorem crossAdj_sq_FN :
    (crossAdjNF K i j hadj h₁ h₂ h₁' h₂').comp (crossAdjFN K i j hadj h₁ h₂ h₁' h₂') =
      BHom.mulB (BRing.tmul _ _ (eXi K j r₁' h₁'.2) 1 - BRing.tmul _ _ 1 (eXi K i r₂ h₂'.2)) := by
  refine BHom.ext fun y => ?_
  apply (eeEquiv K j i h₁' h₂' (movedVar j r₂ h₂.2) (far_hv j i (adj_ne hadj).symm h₂' h₂)).injective
  rw [BHom.comp_apply, crossAdjNF_apply, crossAdjFN_apply, crossNFβ_neg, crossNFβ_crossFNβ,
    BHom.mulB_apply, map_mul, map_sub, eeEquiv_xi_left, eeEquiv_xi_right, ← neg_mul, neg_sub]

/-- **Dot slide** (KL III (4.12)) through `crossAdjNF`, left strand (`i`). -/
theorem crossAdjNF_xiL :
    (crossAdjNF K i j hadj h₁ h₂ h₁' h₂').comp (BHom.mulB (BRing.tmul _ _ (eXi K i r₁ h₁.2) 1)) =
      (BHom.mulB (BRing.tmul _ _ 1 (eXi K i r₂ h₂'.2))).comp (crossAdjNF K i j hadj h₁ h₂ h₁' h₂') := by
  refine BHom.ext fun y => ?_
  apply (eeEquiv K j i h₁' h₂' (movedVar j r₂ h₂.2) (far_hv j i (adj_ne hadj).symm h₂' h₂)).injective
  rw [BHom.comp_apply, BHom.comp_apply, BHom.mulB_apply, BHom.mulB_apply, crossAdjNF_apply,
    map_mul, map_mul, eeEquiv_xi_left, crossNFβ_xi₁_mul, crossAdjNF_apply, eeEquiv_xi_right]

/-- **Dot slide** (KL III (4.12)) through `crossAdjNF`, right strand (`j`). -/
theorem crossAdjNF_xiR :
    (crossAdjNF K i j hadj h₁ h₂ h₁' h₂').comp (BHom.mulB (BRing.tmul _ _ 1 (eXi K j r₂ h₂.2))) =
      (BHom.mulB (BRing.tmul _ _ (eXi K j r₁' h₁'.2) 1)).comp (crossAdjNF K i j hadj h₁ h₂ h₁' h₂') := by
  refine BHom.ext fun y => ?_
  apply (eeEquiv K j i h₁' h₂' (movedVar j r₂ h₂.2) (far_hv j i (adj_ne hadj).symm h₂' h₂)).injective
  rw [BHom.comp_apply, BHom.comp_apply, BHom.mulB_apply, BHom.mulB_apply, crossAdjNF_apply,
    map_mul, map_mul, eeEquiv_xi_right, crossNFβ_xi₂_mul, crossAdjNF_apply, eeEquiv_xi_left]

/-- **Dot slide** (KL III (4.12)) through `crossAdjFN`, left strand (`j`). -/
theorem crossAdjFN_xiL :
    (crossAdjFN K i j hadj h₁ h₂ h₁' h₂').comp (BHom.mulB (BRing.tmul _ _ (eXi K j r₁' h₁'.2) 1)) =
      (BHom.mulB (BRing.tmul _ _ 1 (eXi K j r₂ h₂.2))).comp (crossAdjFN K i j hadj h₁ h₂ h₁' h₂') := by
  refine BHom.ext fun y => ?_
  apply (eeEquiv K i j h₁ h₂ (movedVar i r₂ h₂'.2) (far_hv i j (adj_ne hadj) h₂ h₂')).injective
  rw [BHom.comp_apply, BHom.comp_apply, BHom.mulB_apply, BHom.mulB_apply, crossAdjFN_apply,
    map_mul, map_mul, eeEquiv_xi_left, crossFNβ_xw_mul, crossAdjFN_apply, eeEquiv_xi_right, mul_neg]

/-- **Dot slide** (KL III (4.12)) through `crossAdjFN`, right strand (`i`). -/
theorem crossAdjFN_xiR :
    (crossAdjFN K i j hadj h₁ h₂ h₁' h₂').comp (BHom.mulB (BRing.tmul _ _ 1 (eXi K i r₂ h₂'.2))) =
      (BHom.mulB (BRing.tmul _ _ (eXi K i r₁ h₁.2) 1)).comp (crossAdjFN K i j hadj h₁ h₂ h₁' h₂') := by
  refine BHom.ext fun y => ?_
  apply (eeEquiv K i j h₁ h₂ (movedVar i r₂ h₂'.2) (far_hv i j (adj_ne hadj) h₂ h₂')).injective
  rw [BHom.comp_apply, BHom.comp_apply, BHom.mulB_apply, BHom.mulB_apply, crossAdjFN_apply,
    map_mul, map_mul, eeEquiv_xi_right, crossFNβ_xv_mul, crossAdjFN_apply, eeEquiv_xi_left, mul_neg]

end AdjPath

/-! ### The degenerate adjacent case -/

section AdjDegenerate

variable {K : Type u} [Field K] {m : ℕ}

attribute [local instance] rightAlgebra midAlgebra

/-- **The degenerate case of KL III (4.11) for `j = i + 1`**: if `r₂` has no unit in block `i + 1`
(`k_{i+1} = k_i`), then `E_{i+1} E_i 1_{r₂} = 0` (the step `E_i` from `r₂` is impossible), so both
crossings between `E_i E_{i+1} 1` and `E_{i+1} E_i 1` vanish, and the relation
`ψ_{i+1,i} ψ_{i,i+1} = x_right - x_left` requires the two dots of `E_i E_{i+1} 1` to agree. They do:
here `E_i` moves the same variable that `E_{i+1}` moved into block `i + 1`. -/
theorem adj_degenerate (i j : Fin m) (hadj : j.castSucc = i.succ) {t r₁ r₂ : Comp m}
    (h₁ : StepR (true, i) r₁ t) (h₂ : StepR (true, j) r₂ r₁) (h0 : r₂ i.succ = 0) :
    BRing.tmul (stepB K (true, i) r₁ t h₁) (stepB K (true, j) r₂ r₁ h₂) (eXi K i r₁ h₁.2) 1 =
      BRing.tmul _ _ 1 (eXi K j r₂ h₂.2) := by
  have hv : labJ j h₂ (movedVar j r₂ h₂.2) = i.succ := by
    rw [labJ, moveLab_self, hadj]
  apply (eeEquiv K i j h₁ h₂ (movedVar j r₂ h₂.2) hv).injective
  rw [eeEquiv_xi_left, eeEquiv_xi_right]
  refine degenerate_xi (Sigma.fst : Gen r₂ → Fin (m + 1)) (movedVar j r₂ h₂.2) j.castSucc
    fun x hx => ?_
  have h1 : (x.2 : ℕ) < r₂ x.1 := x.2.2
  have h2 : r₂ x.1 = 0 := by rw [hx, hadj, h0]
  omega

end AdjDegenerate

end Categorification.Flag

end

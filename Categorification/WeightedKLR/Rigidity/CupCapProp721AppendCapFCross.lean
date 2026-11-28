/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapFDot
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapECross

/-!
# `K ∘ 𝔉_i² ≅ 𝔉_i² ∘ K` and the same-colour crossing

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the compatibility of `K ∘ 𝔉_i ≅ 𝔉_i ∘ K` with the crossing on `𝔉_i²`. The
crossing on inductions is the mate of the crossing on restrictions (`indCrossOfEq`, the action of
`-ψ`); on a generator `1 ⊗ (z ⊗ n)` it is `σ(z) ⊗ (1 ⊗ n)`
(`CupCap.indCrossOfEq_self_tmul`, from `InductionAlong.conjugateEquiv_symm_resAct₂_tmul`). Two
applications of `CupCap.capFOrdIsoOfEq` give `K ∘ 𝔉_i² ≅ 𝔉_i² ∘ K`
(`CupCap.capFCompIsoOfEq`), whose inverse sends `1 ⊗ (1 ⊗ (c ⊗ x))` to
`bwd₂(1 ⊗ bwd₁(1 ⊗ c)) ⊗ (1 ⊗ (1 ⊗ x))`. It carries the crossing on `𝔉_i²` to the crossing on
`𝔉⁺_i²` as soon as `bwd₂(1 ⊗ bwd₁(1 ⊗ ·))` carries the right action of the crossing of the two
appended strands of `T^{λ⁺}` to the left action of the crossing of the two appended strands of
`T^λ` (`CupCap.capFCompIsoOfEq_cross`). This is the hypothesis of the part for `𝔈_i`
(`CupCap.capECompIsoOfEq_cross`), with `ι₂ ∘ ι₁` replaced by `bwd₂(1 ⊗ bwd₁(1 ⊗ ·))`.

## Main definitions

* `CupCap.capFCompIsoOfEq`: `K ∘ 𝔉_i² ≅ 𝔉_i² ∘ K`.

## Main results

* `CupCap.indCrossOfEq_self_tmul`, `CupCap.capFCompIsoOfEq_inv_unitGen`.
* `CupCap.capFCompIsoOfEq_cross`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory KLR KLRAlgebra MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Induction

theorem indFunctorIsoOfEq_inv_tmul {A B : Type} [Ring A] [Ring B] {φ φ' : A →ₙ+* B}
    (h : ∀ a, φ a = φ' a) (N : ModuleCat.{0} A) (n : N) :
    ((indFunctorIsoOfEq h).inv.app N).hom (Ind.tmul (unitGen φ') n) =
      (Ind.tmul (unitGen φ) n : Ind N φ) :=
  congrArg (Ind.tmul · n) (Subtype.ext (by
    change φ' 1 * φ' 1 = φ 1
    rw [← map_mul, one_mul, h]))

/-- `φ(a)` acting on `1 ⊗ n` is `1 ⊗ a n`. -/
theorem ind_smul_unitGen_tmul {A B : Type} [Ring A] [Ring B] {φ : A →ₙ+* B} {N : Type}
    [AddCommGroup N] [Module A N] (a : A) (n : N) :
    φ a • (Ind.tmul (unitGen φ) n : Ind N φ) = Ind.tmul (unitGen φ) (a • n) := by
  rw [Ind.smul_tmul, ← Ind.op_smul_tmul]
  congr 1
  exact Subtype.ext (by
    change φ a * φ 1 = φ 1 * φ a
    rw [← map_mul, ← map_mul, mul_one, one_mul])

variable {A₀ A₁ A₂ : Type} [Ring A₀] [Ring A₁] [Ring A₂] {φ₁ : A₀ →ₙ+* A₁} {φ₂ : A₁ →ₙ+* A₂}
  {N : Type} [AddCommGroup N] [Module A₀ N]

theorem ind_unitGen_tmul_tmul (z : Corner φ₁) (n : N) :
    (Ind.tmul (unitGen φ₂) (Ind.tmul z n) : Ind (Ind N φ₁) φ₂) =
      φ₂ z.1 • Ind.tmul (unitGen φ₂) (Ind.tmul (unitGen φ₁) n) := by
  rw [ind_tmul_eq_smul_unitGen z, ind_smul_unitGen_tmul]

/-- `n ↦ 1 ⊗ (1 ⊗ n)`, into a twice induced module. -/
def indUnitTwo : N →+ Ind (Ind N φ₁) φ₂ :=
  AddMonoidHom.mk' (fun n => Ind.tmul (unitGen φ₂) (Ind.tmul (unitGen φ₁) n)) fun n n' =>
    (congrArg (Ind.tmul (unitGen φ₂)) (Ind.tmul_add _ n n')).trans (Ind.tmul_add _ _ _)

theorem indUnitTwo_apply (n : N) :
    (indUnitTwo n : Ind (Ind N φ₁) φ₂) = Ind.tmul (unitGen φ₂) (Ind.tmul (unitGen φ₁) n) :=
  rfl

/-- Linear maps out of a twice induced module agree once they agree on `1 ⊗ (1 ⊗ n)`. -/
theorem ind₂_linearMap_ext {P : Type} [AddCommGroup P] [Module A₂ P]
    {f g : Ind (Ind N φ₁) φ₂ →ₗ[A₂] P}
    (h : f.toAddMonoidHom.comp indUnitTwo = g.toAddMonoidHom.comp indUnitTwo) : f = g :=
  Ind.ext fun z m => by
    rw [ind_tmul_eq_smul_unitGen z, map_smul, map_smul]
    congr 1
    induction m using Ind.induction_on with
    | zero => rw [Ind.tmul_zero, map_zero, map_zero]
    | tmul z₁ n =>
      rw [ind_unitGen_tmul_tmul, map_smul, map_smul]
      exact congrArg (φ₂ z₁.1 • ·) (DFunLike.congr_fun h n)
    | add s t hs ht => rw [Ind.tmul_add, map_add, map_add, hs, ht]

/-- `CupCap.ind₂_linearMap_ext` for an additively generating family of `N`. -/
theorem ind₂_linearMap_ext_of {P : Type} [AddCommGroup P] [Module A₂ P] {S : Type} {t : S → N}
    (ht : ∀ φ ψ : N →+ P, (∀ s, φ (t s) = ψ (t s)) → φ = ψ)
    {f g : Ind (Ind N φ₁) φ₂ →ₗ[A₂] P}
    (h : ∀ s, f (Ind.tmul (unitGen φ₂) (Ind.tmul (unitGen φ₁) (t s))) =
      g (Ind.tmul (unitGen φ₂) (Ind.tmul (unitGen φ₁) (t s)))) : f = g :=
  ind₂_linearMap_ext (ht _ _ h)

/-- `CupCap.ind₂_linearMap_ext_of` for two composites of linear maps, evaluated at a point. -/
theorem ind₂_comp_ext {P M₁ M₂ : Type} [AddCommGroup P] [Module A₂ P] [AddCommGroup M₁]
    [Module A₂ M₁] [AddCommGroup M₂] [Module A₂ M₂] {S : Type} {t : S → N}
    (ht : ∀ φ ψ : N →+ P, (∀ s, φ (t s) = ψ (t s)) → φ = ψ)
    (A : M₁ →ₗ[A₂] P) (B : Ind (Ind N φ₁) φ₂ →ₗ[A₂] M₁) (C : M₂ →ₗ[A₂] P)
    (D : Ind (Ind N φ₁) φ₂ →ₗ[A₂] M₂)
    (h : ∀ s, A (B (Ind.tmul (unitGen φ₂) (Ind.tmul (unitGen φ₁) (t s)))) =
      C (D (Ind.tmul (unitGen φ₂) (Ind.tmul (unitGen φ₁) (t s)))))
    (y : Ind (Ind N φ₁) φ₂) : A (B y) = C (D y) :=
  LinearMap.congr_fun (ind₂_linearMap_ext_of ht (f := A ∘ₗ B) (g := C ∘ₗ D) h) y

end Induction

section Absorb

variable {R M : Type} [Ring R] [AddCommGroup M] [Module R M] {B : M}

theorem smul_absorb_left {e₂ e x : R} (he : e • B = B) (hxe : x * e = e * x)
    (hee : e₂ * e = e) : ((e₂ * x) * e) • B = x • B := by
  calc ((e₂ * x) * e) • B = e₂ • x • B := by rw [mul_smul, he, mul_smul]
    _ = x • B := by
      conv_rhs => rw [← he, smul_smul, hxe, ← hee, mul_assoc, mul_smul, ← hxe, mul_smul, he]

theorem smul_absorb_right {f f₂ p : R} (hf₂ : f₂ • B = B) (hf : f • B = B)
    (hpf : p * f = f * p) : (f * (p * f₂)) • B = p • B := by
  rw [mul_smul, mul_smul, hf₂, ← mul_smul, ← hpf, mul_smul, hf]

end Absorb

section Generic

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {n : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ' : Fin n → I →₀ ℕ)

theorem castOp_appendedCross_fix (i : I) {μ β δ : Multiset I}
    (h₁ : ({i} : Multiset I) + μ = β) (h₂ : ({i} : Multiset I) + β = δ) :
    appendBlackOpOfEq Q Λ' i h₂ 1 *
        castOp Q Λ' (h₁ ▸ h₂ : ({i} : Multiset I) + (({i} : Multiset I) + μ) = δ)
          (op (appendedCross Q Λ' i μ)) =
      castOp Q Λ' (h₁ ▸ h₂ : ({i} : Multiset I) + (({i} : Multiset I) + μ) = δ)
        (op (appendedCross Q Λ' i μ)) := by
  subst h₁ h₂
  exact op_appendedCross_fix Q Λ' i μ

theorem castOp_appendedCross_commute (i : I) {μ β δ : Multiset I}
    (h₁ : ({i} : Multiset I) + μ = β) (h₂ : ({i} : Multiset I) + β = δ)
    (a : (TensorProductAlgebra k Q Λ' μ)ᵐᵒᵖ) :
    castOp Q Λ' (h₁ ▸ h₂ : ({i} : Multiset I) + (({i} : Multiset I) + μ) = δ)
        (op (appendedCross Q Λ' i μ)) *
          appendBlackOpOfEq Q Λ' i h₂ (appendBlackOpOfEq Q Λ' i h₁ a) =
      appendBlackOpOfEq Q Λ' i h₂ (appendBlackOpOfEq Q Λ' i h₁ a) *
        castOp Q Λ' (h₁ ▸ h₂ : ({i} : Multiset I) + (({i} : Multiset I) + μ) = δ)
          (op (appendedCross Q Λ' i μ)) := by
  subst h₁ h₂
  exact op_appendedCross_commute Q Λ' i μ a

/-- **The same-colour crossing on `𝔉_i²` on generators**: the mate `indCrossOfEq` of the action
of `-ψ` on restrictions sends `1 ⊗ (z ⊗ n)` to `σ(z) ⊗ (1 ⊗ n)`. -/
theorem indCrossOfEq_self_tmul (hsym : KLRSymm Q) (i : I) {μ β δ : Multiset I}
    (h₁ : ({i} : Multiset I) + μ = β) (h₂ : ({i} : Multiset I) + β = δ)
    (N : ModuleCat.{0} (TensorProductAlgebra k Q Λ' μ)ᵐᵒᵖ)
    (z : Corner (appendBlackOpOfEq Q Λ' i h₁)) (x : N) :
    ((indCrossOfEq Λ' hsym i i h₁ h₂ h₁ h₂).app N).hom
        (Ind.tmul (unitGen (appendBlackOpOfEq Q Λ' i h₂)) (Ind.tmul z x)) =
      Ind.tmul (sigmaElt (appendBlackOpOfEq Q Λ' i h₁) (appendBlackOpOfEq Q Λ' i h₂)
        (castOp Q Λ' (h₁ ▸ h₂ : ({i} : Multiset I) + (({i} : Multiset I) + μ) = δ)
          (op (appendedCross Q Λ' i μ))) z)
        (Ind.tmul (unitGen (appendBlackOpOfEq Q Λ' i h₁)) x) :=
  conjugateEquiv_symm_resAct₂_tmul _ _ (castOp_appendedCross_commute Λ' i h₁ h₂)
    (castOp_appendedCross_fix Λ' i h₁ h₂) (resCrossOfEq Λ' hsym i i h₁ h₂ h₁ h₂)
    (fun M => ModuleCat.hom_ext (LinearMap.ext fun r => Res.ext (Res.ext
      (resCrossOfEq_self_app_val Λ' hsym i h₁ h₂ M r)))) N z x

end Generic

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν₀ : Multiset I}
  {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  {ν : Multiset I} {i : I}

set_option hygiene false in
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
set_option hygiene false in
local notation "νᵢᵢ" =>
  ((Singleton.singleton i : Multiset I) + ((Singleton.singleton i : Multiset I) + ν))
set_option hygiene false in
local notation "TA" => TensorProductAlgebra k Q Λ ν
set_option hygiene false in
local notation "TAᵢ" => TensorProductAlgebra k Q Λ νᵢ
set_option hygiene false in
local notation "TAᵢᵢ" => TensorProductAlgebra k Q Λ νᵢᵢ
set_option hygiene false in
local notation "TPp" => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
set_option hygiene false in
local notation "TPpᵢ" => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (νᵢ + ν₀)
set_option hygiene false in
local notation "TPpᵢᵢ" => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (νᵢᵢ + ν₀)
set_option hygiene false in
local notation "CB" => CapBimodule k Q Λ Λc j hj ν ν₀ L
set_option hygiene false in
local notation "CBᵢ" => CapBimodule k Q Λ Λc j hj νᵢ ν₀ L
set_option hygiene false in
local notation "CBᵢᵢ" => CapBimodule k Q Λ Λc j hj νᵢᵢ ν₀ L
set_option hygiene false in
local notation "OrdK" => ordTensor TPpᵐᵒᵖ TAᵐᵒᵖ (OpBimodule TA CB)
set_option hygiene false in
local notation "OrdKᵢ" => ordTensor TPpᵢᵐᵒᵖ TAᵢᵐᵒᵖ (OpBimodule TAᵢ CBᵢ)
set_option hygiene false in
local notation "OrdKᵢᵢ" => ordTensor TPpᵢᵢᵐᵒᵖ TAᵢᵢᵐᵒᵖ (OpBimodule TAᵢᵢ CBᵢᵢ)
set_option hygiene false in
local notation "aT₁" => appendBlackTPAOp k Q Λ Λc j hj ν ν₀ i
set_option hygiene false in
local notation "aT₂" => appendBlackTPAOp k Q Λ Λc j hj νᵢ ν₀ i
set_option hygiene false in
local notation "φ⁺₁" => appendBlackOpOfEq Q (plusLabels Λ Λc j hj) i (plusWeight_assoc ν ν₀ i)
set_option hygiene false in
local notation "φ⁺₂" => appendBlackOpOfEq Q (plusLabels Λ Λc j hj) i (plusWeight_assoc νᵢ ν₀ i)
set_option hygiene false in
local notation "Fᵖ" => blackFOfEq Q (plusLabels Λ Λc j hj) i (plusWeight_assoc ν ν₀ i)
set_option hygiene false in
local notation "Fᵖᵢ" => blackFOfEq Q (plusLabels Λ Λc j hj) i (plusWeight_assoc νᵢ ν₀ i)
set_option hygiene false in
local notation "aOp" => appendBlackOp Q Λ i ν
set_option hygiene false in
local notation "aOpᵢ" => appendBlackOp Q Λ i νᵢ

/-! ### The inverse isomorphisms on generators -/

theorem capFOrdIsoOfEq_inv_unitGen (D : CapFData k Q Λ Λc j hj ν₀ L ν i)
    (X : ModuleCat.{0} TAᵐᵒᵖ) (c : CB) (x : X) :
    ((capFOrdIsoOfEq D).inv.app X).hom (Ind.tmul (unitGen φ⁺₁)
        (DG.TensorProductOver.tmul (M := InDegreeZero (OpBimodule TA CB)) (N := InDegreeZero X)
          TAᵐᵒᵖ c x : (OrdK).obj X)) =
      DG.TensorProductOver.tmul (M := InDegreeZero (OpBimodule TAᵢ CBᵢ))
        (N := InDegreeZero ((blackF Q Λ i ν).obj X)) TAᵢᵐᵒᵖ
        (D.bwd (Ind.tmul (unitGen aT₁) c)) (Ind.tmul (unitGen aOp) x) := by
  change capFOrdBwd D X
    (((indFunctorIsoOfEq (appendBlackTPAOp_eq_ofEq k Q Λ Λc j hj ν₀ ν i)).inv.app
    ((OrdK).obj X)).hom (Ind.tmul (unitGen φ⁺₁) (DG.TensorProductOver.tmul
      (M := InDegreeZero (OpBimodule TA CB)) (N := InDegreeZero X) TAᵐᵒᵖ c x))) = _
  exact (congrArg (capFOrdBwd D X) (indFunctorIsoOfEq_inv_tmul _ _ _)).trans rfl

/-- **`K ∘ 𝔉_i² ≅ 𝔉_i² ∘ K`** (Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.21): two
applications of `CupCap.capFOrdIsoOfEq`. -/
def capFCompIsoOfEq (D₁ : CapFData k Q Λ Λc j hj ν₀ L ν i)
    (D₂ : CapFData k Q Λ Λc j hj ν₀ L νᵢ i) :
    (blackF Q Λ i ν ⋙ blackF Q Λ i νᵢ) ⋙ OrdKᵢᵢ ≅ OrdK ⋙ (Fᵖ ⋙ Fᵖᵢ) :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (capFOrdIsoOfEq D₂) ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (capFOrdIsoOfEq D₁) _ ≪≫
    Functor.associator _ _ _

theorem capFCompIsoOfEq_inv_unitGen (D₁ : CapFData k Q Λ Λc j hj ν₀ L ν i)
    (D₂ : CapFData k Q Λ Λc j hj ν₀ L νᵢ i) (X : ModuleCat.{0} TAᵐᵒᵖ) (c : CB) (x : X) :
    ((capFCompIsoOfEq D₁ D₂).inv.app X).hom (Ind.tmul (unitGen φ⁺₂) (Ind.tmul (unitGen φ⁺₁)
        (DG.TensorProductOver.tmul (M := InDegreeZero (OpBimodule TA CB)) (N := InDegreeZero X)
          TAᵐᵒᵖ c x : (OrdK).obj X))) =
      DG.TensorProductOver.tmul (M := InDegreeZero (OpBimodule TAᵢᵢ CBᵢᵢ))
        (N := InDegreeZero ((blackF Q Λ i νᵢ).obj ((blackF Q Λ i ν).obj X))) TAᵢᵢᵐᵒᵖ
        (D₂.bwd (Ind.tmul (unitGen aT₂) (D₁.bwd (Ind.tmul (unitGen aT₁) c))))
        (Ind.tmul (unitGen aOpᵢ) (Ind.tmul (unitGen aOp) x)) := by
  change ((capFOrdIsoOfEq D₂).inv.app ((blackF Q Λ i ν).obj X)).hom (Ind.tmul (unitGen φ⁺₂)
    (((capFOrdIsoOfEq D₁).inv.app X).hom (Ind.tmul (unitGen φ⁺₁)
      (DG.TensorProductOver.tmul (M := InDegreeZero (OpBimodule TA CB)) (N := InDegreeZero X)
        TAᵐᵒᵖ c x)))) = _
  rw [capFOrdIsoOfEq_inv_unitGen]
  exact capFOrdIsoOfEq_inv_unitGen D₂ _ _ _

/-! ### The crossing -/

section Fix

variable (D : CapFData k Q Λ Λc j hj ν₀ L ν i)

theorem CapFData.unit_smul_bwd (w : Ind CB aT₁) :
    (appendBlack Q Λ i ν : TA →ₙ+* TAᵢ) 1 • D.bwd w = D.bwd w := by
  rw [← D.bwd_smul_left, capLeftMul_one, Ind.map_id]
  rfl

theorem CapFData.bwd_unitGen_smul (b : TPpᵐᵒᵖ) (c : CB) :
    aT₁ b • D.bwd (Ind.tmul (unitGen aT₁) c) = D.bwd (Ind.tmul (unitGen aT₁) (b • c)) := by
  rw [← D.bwd_smul_right, ind_smul_unitGen_tmul]

end Fix

theorem capFCompIsoOfEq_inv_cross_tmul (hQ : KLRSymm Q)
    (D₁ : CapFData k Q Λ Λc j hj ν₀ L ν i) (D₂ : CapFData k Q Λ Λc j hj ν₀ L νᵢ i)
    (hcross : ∀ c : CB, appendedCross Q Λ i ν •
        D₂.bwd (Ind.tmul (unitGen aT₂) (D₁.bwd (Ind.tmul (unitGen aT₁) c))) =
      (capCrossPlusOp (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) (ν := ν)
        (i := i)) • D₂.bwd (Ind.tmul (unitGen aT₂) (D₁.bwd (Ind.tmul (unitGen aT₁) c))))
    (X : ModuleCat.{0} TAᵐᵒᵖ)
    (τ : (blackF Q Λ i ν ⋙ blackF Q Λ i νᵢ).obj X ⟶ (blackF Q Λ i ν ⋙ blackF Q Λ i νᵢ).obj X)
    (hτ : ∀ x : X, τ.hom (Ind.tmul (unitGen aOpᵢ) (Ind.tmul (unitGen aOp) x)) =
      (sigmaElt aOp aOpᵢ (op (appendedCross Q Λ i ν)) (unitGen aOp)).1 •
        (Ind.tmul (unitGen aOpᵢ) (Ind.tmul (unitGen aOp) x) :
          (blackF Q Λ i ν ⋙ blackF Q Λ i νᵢ).obj X)) (c : CB) (x : X) :
    ((OrdKᵢᵢ).map τ).hom
        (((capFCompIsoOfEq D₁ D₂).inv.app X).hom (Ind.tmul (unitGen φ⁺₂)
          (Ind.tmul (unitGen φ⁺₁) (DG.TensorProductOver.tmul
            (M := InDegreeZero (OpBimodule TA CB)) (N := InDegreeZero X) TAᵐᵒᵖ c x)))) =
      ((capFCompIsoOfEq D₁ D₂).inv.app X).hom
        (((indCrossOfEq (plusLabels Λ Λc j hj) hQ i i (plusWeight_assoc ν ν₀ i)
          (plusWeight_assoc νᵢ ν₀ i) (plusWeight_assoc ν ν₀ i) (plusWeight_assoc νᵢ ν₀ i)).app
            ((OrdK).obj X)).hom (Ind.tmul (unitGen φ⁺₂)
          (Ind.tmul (unitGen φ⁺₁) (DG.TensorProductOver.tmul
            (M := InDegreeZero (OpBimodule TA CB)) (N := InDegreeZero X) TAᵐᵒᵖ c x)))) := by
  set B := D₂.bwd (Ind.tmul (unitGen aT₂) (D₁.bwd (Ind.tmul (unitGen aT₁) c))) with hBdef
  set y := D₁.bwd (Ind.tmul (unitGen aT₁) c) with hydef
  have hy : (appendBlack Q Λ i ν : TA →ₙ+* TAᵢ) 1 • y = y := D₁.unit_smul_bwd _
  have hy' : aT₁ 1 • y = y := (D₁.bwd_unitGen_smul 1 c).trans (by rw [one_smul])
  have he₂ : (appendBlack Q Λ i νᵢ : TAᵢ →ₙ+* TAᵢᵢ) 1 • B = B := D₂.unit_smul_bwd _
  have he : (appendBlack Q Λ i νᵢ : TAᵢ →ₙ+* TAᵢᵢ)
      ((appendBlack Q Λ i ν : TA →ₙ+* TAᵢ) 1) • B = B := by
    rw [hBdef, ← D₂.bwd_smul_left]
    exact congrArg (fun w => D₂.bwd (Ind.tmul (unitGen aT₂) w)) hy
  have hf₂ : aT₂ 1 • B = B := (D₂.bwd_unitGen_smul 1 y).trans (by rw [one_smul])
  have hf : aT₂ (aT₁ 1) • B = B := (D₂.bwd_unitGen_smul (aT₁ 1) y).trans (by rw [hy'])
  have hcr : (((appendBlack Q Λ i νᵢ : TAᵢ →ₙ+* TAᵢᵢ) 1 * appendedCross Q Λ i ν) *
      (appendBlack Q Λ i νᵢ : TAᵢ →ₙ+* TAᵢᵢ) ((appendBlack Q Λ i ν : TA →ₙ+* TAᵢ) 1)) • B =
        appendedCross Q Λ i ν • B := by
    refine smul_absorb_left he (appendedCross_commute Q Λ i ν 1) ?_
    rw [← map_mul, one_mul]
  have hc := castOp_appendedCross_commute (Q := Q) (plusLabels Λ Λc j hj) i
    (plusWeight_assoc ν ν₀ i) (plusWeight_assoc νᵢ ν₀ i) 1
  simp only [← appendBlackTPAOp_eq_ofEq] at hc
  have hcrP : (φ⁺₂ (φ⁺₁ 1) * ((capCrossPlusOp (Q := Q) (Λ := Λ) (Λc := Λc) (j := j)
      (hj := hj) (ν₀ := ν₀) (ν := ν) (i := i)) * φ⁺₂ 1)) • B =
        (capCrossPlusOp (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) (ν := ν)
          (i := i)) • B := by
    simp only [← appendBlackTPAOp_eq_ofEq]
    exact smul_absorb_right hf₂ hf hc
  have H1 := hτ x
  have H2 := (indCrossOfEq_self_tmul (plusLabels Λ Λc j hj) hQ i (plusWeight_assoc ν ν₀ i)
    (plusWeight_assoc νᵢ ν₀ i) ((OrdK).obj X) (unitGen _)
      (DG.TensorProductOver.tmul (M := InDegreeZero (OpBimodule TA CB)) (N := InDegreeZero X)
        TAᵐᵒᵖ c x)).trans (ind_tmul_eq_smul_unitGen _ _)
  have hI := capFCompIsoOfEq_inv_unitGen D₁ D₂ X c x
  refine (congrArg ((OrdKᵢᵢ).map τ).hom hI).trans ?_
  refine (congrArg (fun t => DG.TensorProductOver.tmul (M := InDegreeZero (OpBimodule TAᵢᵢ CBᵢᵢ))
      (N := InDegreeZero ((blackF Q Λ i νᵢ).obj ((blackF Q Λ i ν).obj X))) TAᵢᵢᵐᵒᵖ B t) H1).trans ?_
  refine ((DG.TensorProductOver.op_smul_tmul (A := TAᵢᵢᵐᵒᵖ)
    (M := InDegreeZero (OpBimodule TAᵢᵢ CBᵢᵢ))
    (N := InDegreeZero ((blackF Q Λ i νᵢ).obj ((blackF Q Λ i ν).obj X))) _ B _).symm).trans ?_
  refine (congrArg (fun b : CBᵢᵢ => DG.TensorProductOver.tmul
      (M := InDegreeZero (OpBimodule TAᵢᵢ CBᵢᵢ))
      (N := InDegreeZero ((blackF Q Λ i νᵢ).obj ((blackF Q Λ i ν).obj X))) TAᵢᵢᵐᵒᵖ b
    (Ind.tmul (unitGen aOpᵢ) (Ind.tmul (unitGen aOp) x))) (hcr.trans (hcross c))).trans ?_
  exact Eq.symm ((congrArg ((capFCompIsoOfEq D₁ D₂).inv.app X).hom H2).trans
    ((LinearMap.map_smul _ _ _).trans ((congrArg (_ • ·) hI).trans
      (congrArg (fun b : CBᵢᵢ => DG.TensorProductOver.tmul
          (M := InDegreeZero (OpBimodule TAᵢᵢ CBᵢᵢ))
      (N := InDegreeZero ((blackF Q Λ i νᵢ).obj ((blackF Q Λ i ν).obj X))) TAᵢᵢᵐᵒᵖ b
        (Ind.tmul (unitGen aOpᵢ) (Ind.tmul (unitGen aOp) x))) hcrP))))

theorem capFCompIsoOfEq_inv_cross_app (hQ : KLRSymm Q) (D₁ : CapFData k Q Λ Λc j hj ν₀ L ν i)
    (D₂ : CapFData k Q Λ Λc j hj ν₀ L νᵢ i)
    (hcross : ∀ c : CB, appendedCross Q Λ i ν •
        D₂.bwd (Ind.tmul (unitGen aT₂) (D₁.bwd (Ind.tmul (unitGen aT₁) c))) =
      (capCrossPlusOp (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) (ν := ν)
        (i := i)) • D₂.bwd (Ind.tmul (unitGen aT₂) (D₁.bwd (Ind.tmul (unitGen aT₁) c))))
    (X : ModuleCat.{0} TAᵐᵒᵖ)
    (τ : (blackF Q Λ i ν ⋙ blackF Q Λ i νᵢ).obj X ⟶ (blackF Q Λ i ν ⋙ blackF Q Λ i νᵢ).obj X)
    (hτ : ∀ x : X, τ.hom (Ind.tmul (unitGen aOpᵢ) (Ind.tmul (unitGen aOp) x)) =
      (sigmaElt aOp aOpᵢ (op (appendedCross Q Λ i ν)) (unitGen aOp)).1 •
        (Ind.tmul (unitGen aOpᵢ) (Ind.tmul (unitGen aOp) x) :
          (blackF Q Λ i ν ⋙ blackF Q Λ i νᵢ).obj X)) (y : (OrdK ⋙ (Fᵖ ⋙ Fᵖᵢ)).obj X) :
    ((OrdKᵢᵢ).map τ).hom
        (((capFCompIsoOfEq D₁ D₂).inv.app X).hom y) =
      ((capFCompIsoOfEq D₁ D₂).inv.app X).hom
        (((indCrossOfEq (plusLabels Λ Λc j hj) hQ i i (plusWeight_assoc ν ν₀ i)
          (plusWeight_assoc νᵢ ν₀ i) (plusWeight_assoc ν ν₀ i) (plusWeight_assoc νᵢ ν₀ i)).app
            ((OrdK).obj X)).hom y) := by
  exact ind₂_comp_ext (φ₁ := φ⁺₁) (φ₂ := φ⁺₂)
    (S := InDegreeZero (OpBimodule TA CB) × InDegreeZero X)
    (t := fun p => DG.TensorProductOver.tmul (M := InDegreeZero (OpBimodule TA CB))
      (N := InDegreeZero X) TAᵐᵒᵖ p.1 p.2)
    (fun _ _ h => DG.TensorProductOver.addHom_ext fun m n => h (m, n))
    ((OrdKᵢᵢ).map τ).hom ((capFCompIsoOfEq D₁ D₂).inv.app X).hom
    ((capFCompIsoOfEq D₁ D₂).inv.app X).hom
    ((indCrossOfEq (plusLabels Λ Λc j hj) hQ i i (plusWeight_assoc ν ν₀ i)
          (plusWeight_assoc νᵢ ν₀ i) (plusWeight_assoc ν ν₀ i) (plusWeight_assoc νᵢ ν₀ i)).app
            ((OrdK).obj X)).hom
    (fun p => capFCompIsoOfEq_inv_cross_tmul hQ D₁ D₂ hcross X τ hτ p.1 p.2) y

/-- **`K ∘ 𝔉_i² ≅ 𝔉_i² ∘ K` carries the crossing to the crossing** (Webster, arXiv:1309.3796v3,
§7.3, proof of Proposition 7.21): if `bwd₂(1 ⊗ bwd₁(1 ⊗ ·))` carries the right action of the
crossing of the two appended strands of `T^{λ⁺}` to the left action of the crossing of the two
appended strands of `T^λ`, then `(K ∘ τ) ≫ φ = φ ≫ (τ ∘ K)` for
`φ = CupCap.capFCompIsoOfEq D₁ D₂`, with `τ` the crossings `indCrossOfEq` on `𝔉_i²` and on
`𝔉⁺_i²`. -/
theorem capFCompIsoOfEq_cross (hQ : KLRSymm Q) (D₁ : CapFData k Q Λ Λc j hj ν₀ L ν i)
    (D₂ : CapFData k Q Λ Λc j hj ν₀ L νᵢ i)
    (hcross : ∀ c : CB, appendedCross Q Λ i ν •
        D₂.bwd (Ind.tmul (unitGen aT₂) (D₁.bwd (Ind.tmul (unitGen aT₁) c))) =
      (capCrossPlusOp (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) (ν := ν)
        (i := i)) • D₂.bwd (Ind.tmul (unitGen aT₂) (D₁.bwd (Ind.tmul (unitGen aT₁) c)))) :
    (Functor.whiskerRight (indCrossOfEq Λ hQ i i rfl rfl rfl rfl) OrdKᵢᵢ :
        (blackF Q Λ i ν ⋙ blackF Q Λ i νᵢ) ⋙ OrdKᵢᵢ ⟶
          (blackF Q Λ i ν ⋙ blackF Q Λ i νᵢ) ⋙ OrdKᵢᵢ) ≫ (capFCompIsoOfEq D₁ D₂).hom =
      (capFCompIsoOfEq D₁ D₂).hom ≫ Functor.whiskerLeft OrdK
        (indCrossOfEq (plusLabels Λ Λc j hj) hQ i i (plusWeight_assoc ν ν₀ i)
          (plusWeight_assoc νᵢ ν₀ i) (plusWeight_assoc ν ν₀ i) (plusWeight_assoc νᵢ ν₀ i)) := by
  suffices key : (capFCompIsoOfEq D₁ D₂).inv ≫
      (Functor.whiskerRight (indCrossOfEq Λ hQ i i rfl rfl rfl rfl) OrdKᵢᵢ :
        (blackF Q Λ i ν ⋙ blackF Q Λ i νᵢ) ⋙ OrdKᵢᵢ ⟶
          (blackF Q Λ i ν ⋙ blackF Q Λ i νᵢ) ⋙ OrdKᵢᵢ) =
      Functor.whiskerLeft OrdK
        (indCrossOfEq (plusLabels Λ Λc j hj) hQ i i (plusWeight_assoc ν ν₀ i)
          (plusWeight_assoc νᵢ ν₀ i) (plusWeight_assoc ν ν₀ i) (plusWeight_assoc νᵢ ν₀ i)) ≫
        (capFCompIsoOfEq D₁ D₂).inv from
    (Iso.inv_comp_eq _).1 ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (capFCompIsoOfEq D₁ D₂).hom) key).trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) (capFCompIsoOfEq D₁ D₂).inv_hom_id).trans (Category.comp_id _)))))
  exact NatTrans.ext (funext fun X => ModuleCat.hom_ext (LinearMap.ext
    (capFCompIsoOfEq_inv_cross_app hQ D₁ D₂ hcross X
      ((indCrossOfEq Λ hQ i i rfl rfl rfl rfl).app X) fun x =>
        (indCrossOfEq_self_tmul Λ hQ i (rfl : ({i} : Multiset I) + ν = _)
          (rfl : ({i} : Multiset I) + νᵢ = _) X (unitGen _) x).trans
          (ind_tmul_eq_smul_unitGen _ _))))

end Categorification.Stendhal.CupCap

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KCutNatural
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KPaper
import Categorification.WeightedKLR.RedStrands.StandardBimoduleProjective
import Categorification.Algebra.TensorMate
import Categorification.Algebra.DerivedTensorHomology

/-!
# Lemma 7.19 (K) at the cut as an isomorphism of bimodules

Webster, arXiv:1309.3796v3, Lemma 7.19, at the cut at the `j`-th red strand, for the trace half
of the lemma. Let `D` be the algebra of the two blocks of `λ` at the cut, `T = T^λ(θ + γ)`,
`T⁺ = T^{λ⁺}((θ + γ) + ν₀)` and `E` the algebra of the three blocks of `λ⁺`. The functors of
(K) at the cut are tensoring with bimodules:

* `S_cut = S ⊗_D -`, with `S = S_cut(D)` (`KappaS`), a `T`–`D` bimodule;
* `S_+ = S₊ ⊗_E -`, with `S₊ = S_+(E)` (`KappaSp`), a `T⁺`–`E` bimodule;
* `- ⊠ L' = K_b ⊗_D -`, with `K_b = D ⊠ L'` (`MidSpect`), an `E`–`D` bimodule;
* `K^σ ⊗_T -`, with the reflected cap `K^σ`, a `T⁺`–`T` bimodule.

The isomorphism of (K) at `Y = D` (`kCutPhiEquiv`) gives
`κ : K^σ ⊗_T S ≅ S₊ ⊗_E K_b` (`kappaCut`), linear over `T⁺` (`kappaCut_smul`) and over `D` on
the right (`kappaCut_op_smul`, from the naturality of (K) in `Y`). This is the input of the mate
(`TensorMate.mate`).

## Main definitions

* `Stendhal.CupCap.KappaS`, `Stendhal.CupCap.KappaSp`, `Stendhal.CupCap.kappaCut`.

## Route hypotheses

Those of `kCutPhiEquiv`: `hL`, `hR`, `hP`, `hPL`, `hκ`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification

section Generic

open CategoryTheory TensorRepresented MulOpposite

theorem ewEquiv_symm_natural {A B : Type} [Ring A] [Ring B] (F : ModuleCat.{0} B ⥤ ModuleCat.{0} A)
    [F.Additive] (hF : IsTensorRepresented F) {Z Y : ModuleCat.{0} B} (g : Z ⟶ Y) (y : F.obj Z) :
    (ewEquiv F hF Y).symm ((F.map g).hom y) =
      DG.TensorProductOver.map LinearMap.id g.hom ((ewEquiv F hF Z).symm y) := by
  apply (ewEquiv F hF Y).injective
  rw [LinearEquiv.apply_symm_apply, ← ewEquiv_natural, LinearEquiv.apply_symm_apply]

theorem ordinaryBalancedTensorAddEquiv_smul {k A B M N : Type*} [CommRing k] [Ring A] [Ring B]
    [Algebra k A] [Algebra k B] [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
    [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M] [AddCommGroup N] [Module k N] [Module B N]
    [IsScalarTower k B N] (hM : ∀ (c : k) (m : M), op (algebraMap k B c) • m = c • m) (a : A)
    (x : DG.TensorProductOver B M N) :
    ordinaryBalancedTensorAddEquiv (A := A) hM (a • x) =
      a • ordinaryBalancedTensorAddEquiv hM x := by
  induction x using DG.TensorProductOver.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul m n =>
    rw [DG.TensorProductOver.smul_tmul, ordinaryBalancedTensorAddEquiv_tmul,
      ordinaryBalancedTensorAddEquiv_tmul, BalancedTensor.smul_tmul']
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

end Generic

end Categorification

namespace Categorification.Stendhal.CupCap

open CategoryTheory KLR KLRAlgebra TypeA MulOpposite TensorRepresented
open scoped TensorProduct DG.TensorProductOver.RightAction

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} (j : ℕ) (hj : j ≤ ℓ)
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  (θ γ ν₀ : Multiset I) (hQ : KLRSymm Q)
  (L' : Type) [AddCommGroup L'] [Module k L']
  [Module (TensorProductAlgebra k Q Λc ν₀) L'] [IsScalarTower k (TensorProductAlgebra k Q Λc ν₀) L']

set_option hygiene false in
local notation "Dc" => cutFactorAlgebra Q (cutLabels j hj Λ) θ γ
set_option hygiene false in
local notation "Tc" => TensorProductAlgebra k Q Λ (θ + γ)
set_option hygiene false in
local notation "Tp" => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) ((θ + γ) + ν₀)
set_option hygiene false in
local notation "PF" => PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ
set_option hygiene false in
local notation "Kb" => KappaKb j hj Q Λ Λc θ γ ν₀ L'

/-- The semiring structure of the algebra of the three blocks of `λ⁺`, through its ring
structure. -/
private abbrev pfNonAssocSemiringK : NonAssocSemiring PF := Semiring.toNonAssocSemiring

attribute [local instance high] pfNonAssocSemiringK

/-! ### The bimodule `K_b = D ⊠ L'` -/

/-- Right multiplication by `b` on `D`, a map of left `D`-modules. -/
def dRightMul (b : Dc) : Dc →ₗ[Dc] Dc := LinearMap.toSpanSingleton Dc Dc b

theorem dRightMul_apply (b d : Dc) : dRightMul j hj Q Λ θ γ b d = d * b := rfl

/-- **The bimodule `K_b = D ⊠ L'`** of `- ⊠ L'`, an `E`–`D` bimodule. -/
@[nolint unusedArguments]
def KappaKb (j' : ℕ) (hj' : j' ≤ ℓ) (Q' : I → I → MvPolynomial (Fin 2) k) (Λ' : Fin ℓ → I →₀ ℕ)
    (_Λc' : Fin 2 → I →₀ ℕ) (θ' γ' _ν₀' : Multiset I) (L'' : Type) [AddCommGroup L'']
    [Module k L''] : Type :=
  MidSpect (k := k) (cutFactorAlgebra Q' (cutLabels j' hj' Λ') θ' γ') L''

instance : AddCommGroup Kb := inferInstanceAs (AddCommGroup (MidSpect (k := k) Dc L'))
instance : Module k Kb := inferInstanceAs (Module k (MidSpect (k := k) Dc L'))
instance : Module PF Kb := inferInstanceAs (Module PF (MidSpect (k := k) Dc L'))
instance : IsScalarTower k PF Kb := inferInstanceAs (IsScalarTower k PF (MidSpect (k := k) Dc L'))

/-- `D` acting on `D ⊠ L'` from the right, through the first factor. -/
instance : SMul Dcᵐᵒᵖ Kb where
  smul b z := (midSpectMap (B := TensorProductAlgebra k Q Λc ν₀) (L := L')
    (dRightMul j hj Q Λ θ γ b.unop) (show MidSpect (k := k) Dc L' from z) : MidSpect Dc L')

theorem kb_op_smul_def (b : Dcᵐᵒᵖ) (z : Kb) :
    b • z = (midSpectMap (B := TensorProductAlgebra k Q Λc ν₀) (L := L')
      (dRightMul j hj Q Λ θ γ b.unop) (show MidSpect (k := k) Dc L' from z) :
        MidSpect (k := k) Dc L') := rfl

theorem kb_op_smul_tmul (b : Dcᵐᵒᵖ) (d : Dc) (v : L') :
    b • (show Kb from midSpectTmul (k := k) d v) =
      (show Kb from midSpectTmul (k := k) (d * b.unop) v) := rfl

instance : Module Dcᵐᵒᵖ Kb where
  one_smul z := by
    change (LinearMap.rTensor L' ((dRightMul j hj Q Λ θ γ 1).restrictScalars k))
      (show Dc ⊗[k] L' from z) = z
    rw [show (dRightMul j hj Q Λ θ γ 1).restrictScalars k = LinearMap.id from
      LinearMap.ext fun d => mul_one d, LinearMap.rTensor_id, LinearMap.id_apply]
  mul_smul b b' z := by
    change (LinearMap.rTensor L' ((dRightMul j hj Q Λ θ γ (b * b').unop).restrictScalars k))
      (show Dc ⊗[k] L' from z) = (LinearMap.rTensor L' ((dRightMul j hj Q Λ θ γ
        b.unop).restrictScalars k)) ((LinearMap.rTensor L' ((dRightMul j hj Q Λ θ γ
          b'.unop).restrictScalars k)) (show Dc ⊗[k] L' from z))
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
    congr 2
    exact LinearMap.ext fun d => by
      change d * (b'.unop * b.unop) = d * b'.unop * b.unop
      rw [mul_assoc]
  smul_zero b := map_zero _
  smul_add b := map_add _
  add_smul b b' z := by
    change (LinearMap.rTensor L' ((dRightMul j hj Q Λ θ γ (b + b').unop).restrictScalars k))
      (show Dc ⊗[k] L' from z) = (LinearMap.rTensor L' ((dRightMul j hj Q Λ θ γ
        b.unop).restrictScalars k)) (show Dc ⊗[k] L' from z) + (LinearMap.rTensor L'
          ((dRightMul j hj Q Λ θ γ b'.unop).restrictScalars k)) (show Dc ⊗[k] L' from z)
    rw [← LinearMap.add_apply, ← LinearMap.rTensor_add]
    congr 2
    exact LinearMap.ext fun d => mul_add d _ _
  zero_smul z := by
    change (LinearMap.rTensor L' ((dRightMul j hj Q Λ θ γ 0).restrictScalars k))
      (show Dc ⊗[k] L' from z) = 0
    rw [show (dRightMul j hj Q Λ θ γ 0).restrictScalars k = 0 from
      LinearMap.ext fun d => mul_zero d, LinearMap.rTensor_zero, LinearMap.zero_apply]

instance : SMulCommClass PF Dcᵐᵒᵖ Kb where
  smul_comm x b z :=
    ((midSpectMap (B := TensorProductAlgebra k Q Λc ν₀) (L := L')
      (dRightMul j hj Q Λ θ γ b.unop)).map_smul x (show MidSpect (k := k) Dc L' from z)).symm

/-! ### The bimodules `S` and `S₊` -/

/-- The relabelling `T^λ(θ + γ) → T^{λ_1…λ_j | λ_{j+1}…λ_ℓ}(θ + γ)` of the cut. -/
abbrev kappaPsi : Tc →ₐ[k] TensorProductAlgebra k Q (cutLabels j hj Λ) (θ + γ) :=
  (castLabelsTensorProductAlgebra Q (Nat.add_sub_of_le hj) Λ (θ + γ)).symm.toAlgHom

/-- **`S_cut` as a functor** to left `T^λ(θ + γ)`-modules. -/
abbrev kappaSFunctor : ModuleCat.{0} Dc ⥤ ModuleCat.{0} Tc :=
  cutStandardFunctor Q hQ (cutLabels j hj Λ) θ γ (kappaPsi j hj Q Λ θ γ)

/-- **The bimodule `S = S_cut(D)`**, a `T`–`D` bimodule. -/
abbrev KappaS : Type := Bimod (kappaSFunctor j hj Q Λ θ γ hQ)

/-- The weights `(θ + γ) + ν₀ → θ + (ν₀ + γ)` of `T^{λ⁺}`. -/
abbrev kappaCast : Tp →+* TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (θ + (ν₀ + γ)) :=
  (castTensorProductAlgebra Q (plusLabels Λ Λc j hj)
    (plusWeight_eq θ γ ν₀)).symm.toRingEquiv.toRingHom

/-- **`S_+` as a functor** to left `T^{λ⁺}((θ + γ) + ν₀)`-modules. -/
abbrev kappaSpFunctor : ModuleCat.{0} (plusFactorAlgCat Q Λ Λc j hj θ ν₀ γ) ⥤ ModuleCat.{0} Tp :=
  plusStandardFunctor Q hQ Λ Λc j hj θ ν₀ γ ⋙
    ModuleCat.restrictScalars.{0} (kappaCast j hj Q Λ Λc θ γ ν₀)

/-- **The bimodule `S₊ = S_+(E)`**, a `T⁺`–`E` bimodule. -/
abbrev KappaSp : Type := Bimod (kappaSpFunctor j hj Q Λ Λc θ γ ν₀ hQ)

theorem isTensorRepresented_kappaSFunctor :
    IsTensorRepresented (kappaSFunctor j hj Q Λ θ γ hQ) :=
  isTensorRepresented_cutStandardFunctor Q hQ (cutLabels j hj Λ) θ γ (kappaPsi j hj Q Λ θ γ)

theorem isTensorRepresented_kappaSpFunctor :
    IsTensorRepresented (kappaSpFunctor j hj Q Λ Λc θ γ ν₀ hQ) :=
  isTensorRepresented_plusStandardFunctor Q hQ Λ Λc j hj θ ν₀ γ

theorem isFinProj_kappaSFunctor : IsFinProj (kappaSFunctor j hj Q Λ θ γ hQ) :=
  (cutStandardFunctorPresented Q hQ (cutLabels j hj Λ) θ γ (kappaPsi j hj Q Λ θ γ)).isFinProj hQ

theorem isFinProj_kappaSpFunctor : IsFinProj (kappaSpFunctor j hj Q Λ Λc θ γ ν₀ hQ) :=
  have h := isFinProj_plusStandardFunctor Q hQ Λ Λc j hj θ ν₀ γ
  ⟨h.projective, h.finite⟩

example : AddCommGroup (KappaS j hj Q Λ θ γ hQ) := inferInstance
example : Module Tc (KappaS j hj Q Λ θ γ hQ) := inferInstance
example : Module Dcᵐᵒᵖ (KappaS j hj Q Λ θ γ hQ) := inferInstance

/-! ### The isomorphism `κ` -/

set_option hygiene false in
local notation "Kσ" => ReflectedCap j hj Q Λ Λc (θ + γ) ν₀ (CapCoef Q Λc ν₀ L')
set_option hygiene false in
local notation "Sb" => KappaS j hj Q Λ θ γ hQ
set_option hygiene false in
local notation "Spb" => KappaSp j hj Q Λ Λc θ γ ν₀ hQ

omit [IsScalarTower k (TensorProductAlgebra k Q Λc ν₀) L'] in
theorem reflectedCap_int_action (c : ℤ) (m : Kσ) : op (algebraMap ℤ Tc c) • m = c • m := by
  have h : (algebraMap ℤ Tc) c = (c : Tc) := eq_intCast _ c
  rw [h, op_intCast, Int.cast_smul_eq_zsmul]

/-- The regular module `D`, bundled, is `D`. -/
def regularEquiv : (ModuleCat.of Dc Dc : Type) ≃ₗ[Dc] Dc where
  toFun d := d
  invFun d := d
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- `S_cut(M)` for a module `M ≅ D`, as the partial standardization at the cut of `D`. -/
def kappaSEquivOf (M : ModuleCat.{0} Dc) (e : M ≃ₗ[Dc] Dc) :
    (kappaSFunctor j hj Q Λ θ γ hQ).obj M ≃ₗ[Tc] KCutStd j hj Q Λ θ γ Dc hQ where
  __ := cutStandardMapEquiv Q (cutLabels j hj Λ) θ γ e
  map_smul' _ z := cutStandardMap_action Q (cutLabels j hj Λ) θ γ hQ e.toLinearMap _ z

theorem kappaSEquivOf_apply (M : ModuleCat.{0} Dc) (e : M ≃ₗ[Dc] Dc)
    (z : (kappaSFunctor j hj Q Λ θ γ hQ).obj M) :
    kappaSEquivOf j hj Q Λ θ γ hQ M e z = cutStandardMap Q (cutLabels j hj Λ) θ γ e.toLinearMap z :=
  rfl

/-- **`S = S_cut(D)`, as the partial standardization at the cut of the regular module.** -/
def kappaSEquiv : Sb ≃ₗ[Tc] KCutStd j hj Q Λ θ γ Dc hQ :=
  kappaSEquivOf j hj Q Λ θ γ hQ (ModuleCat.of Dc Dc) (regularEquiv j hj Q Λ θ γ)

/-- `K^σ ⊗_T S` is the left side `K^σ(S_cut D)` of (K) at the cut. -/
def kappaLeft : DG.TensorProductOver Tc Kσ Sb ≃+ KCutTarget j hj Q Λ Λc θ γ ν₀ Dc hQ L' :=
  (ordinaryBalancedTensorAddEquiv (k := ℤ) (A := Tp) (B := Tc) (N := Sb)
    (reflectedCap_int_action j hj Q Λ Λc θ γ ν₀ L')).trans
      (BalancedTensor.congrRight (kappaSEquiv j hj Q Λ θ γ hQ)).toAddEquiv

/-- `S_+(N)` for a module `N ≅ D ⊠ L'`, as the right side `S_+(D ⊠ L')` of (K) at the cut. -/
def kappaSpEquivOf (N : ModuleCat.{0} (plusFactorAlgCat Q Λ Λc j hj θ ν₀ γ))
    (e : PlusWrap Q Λ Λc j hj θ ν₀ γ N ≃ₗ[PF] MidSpect (k := k) Dc L') :
    (kappaSpFunctor j hj Q Λ Λc θ γ ν₀ hQ).obj N ≃ₗ[Tp] KCutSrc j hj Q Λ Λc θ γ ν₀ Dc hQ L' where
  __ := plusStandardEquiv Q Λ Λc j hj θ ν₀ γ hQ e
  map_smul' _ z := plusStandardMap_action Q Λ Λc j hj θ ν₀ γ hQ e.toLinearMap _ z

theorem kappaSpEquivOf_apply (N : ModuleCat.{0} (plusFactorAlgCat Q Λ Λc j hj θ ν₀ γ))
    (e : PlusWrap Q Λ Λc j hj θ ν₀ γ N ≃ₗ[PF] MidSpect (k := k) Dc L')
    (z : (kappaSpFunctor j hj Q Λ Λc θ γ ν₀ hQ).obj N) :
    kappaSpEquivOf j hj Q Λ Λc θ γ ν₀ hQ L' N e z =
      plusStandardMap Q Λ Λc j hj θ ν₀ γ hQ e.toLinearMap z := rfl

/-- The bundled `D ⊠ L'` is `D ⊠ L'`. -/
def kbWrapEquiv :
    PlusWrap Q Λ Λc j hj θ ν₀ γ (ModuleCat.of (plusFactorAlgCat Q Λ Λc j hj θ ν₀ γ) Kb)
      ≃ₗ[PF] MidSpect (k := k) Dc L' where
  toFun z := z
  invFun z := z
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- `S₊ ⊗_E K_b` is the right side `S_+(D ⊠ L')` of (K) at the cut (Eilenberg–Watts). -/
def kappaRight : KCutSrc j hj Q Λ Λc θ γ ν₀ Dc hQ L' ≃ₗ[Tp] DG.TensorProductOver PF Spb Kb :=
  (kappaSpEquivOf j hj Q Λ Λc θ γ ν₀ hQ L' _ (kbWrapEquiv j hj Q Λ Λc θ γ ν₀ L')).symm.trans
    (ewEquiv (kappaSpFunctor j hj Q Λ Λc θ γ ν₀ hQ)
      (isTensorRepresented_kappaSpFunctor j hj Q Λ Λc θ γ ν₀ hQ)
      (ModuleCat.of (plusFactorAlgCat Q Λ Λc j hj θ ν₀ γ) Kb)).symm

/-! ### `κ` and its linearity -/

omit [IsScalarTower k (TensorProductAlgebra k Q Λc ν₀) L'] in
theorem kappaLeft_tmul (r : Kσ) (z : Sb) :
    kappaLeft j hj Q Λ Λc θ γ ν₀ hQ L' (DG.TensorProductOver.tmul Tc r z) =
      BalancedTensor.tmul r (kappaSEquiv j hj Q Λ θ γ hQ z) := rfl

omit [IsScalarTower k (TensorProductAlgebra k Q Λc ν₀) L'] in
theorem kappaLeft_smul (t : Tp) (x : DG.TensorProductOver Tc Kσ Sb) :
    kappaLeft j hj Q Λ Λc θ γ ν₀ hQ L' (t • x) = t • kappaLeft j hj Q Λ Λc θ γ ν₀ hQ L' x := by
  change BalancedTensor.congrRight (kappaSEquiv j hj Q Λ θ γ hQ)
      (ordinaryBalancedTensorAddEquiv (k := ℤ) (A := Tp) (B := Tc) (N := Sb)
        (reflectedCap_int_action j hj Q Λ Λc θ γ ν₀ L') (t • x)) =
    t • BalancedTensor.congrRight (kappaSEquiv j hj Q Λ θ γ hQ)
      (ordinaryBalancedTensorAddEquiv (k := ℤ) (A := Tp) (B := Tc) (N := Sb)
        (reflectedCap_int_action j hj Q Λ Λc θ γ ν₀ L') x)
  rw [ordinaryBalancedTensorAddEquiv_smul, LinearEquiv.map_smul]

/-- `S_cut` of a map between modules isomorphic to `D`, in the coordinates of `S_cut(D)`. -/
theorem kappaSEquivOf_map {M M' : ModuleCat.{0} Dc} (e : M ≃ₗ[Dc] Dc) (e' : M' ≃ₗ[Dc] Dc)
    (g : M ⟶ M') (f : Dc →ₗ[Dc] Dc) (h : ∀ x, e' (g x) = f (e x))
    (z : (kappaSFunctor j hj Q Λ θ γ hQ).obj M) :
    kappaSEquivOf j hj Q Λ θ γ hQ M' e' (((kappaSFunctor j hj Q Λ θ γ hQ).map g).hom z) =
      kCutStdMap j hj Q Λ θ γ hQ f (kappaSEquivOf j hj Q Λ θ γ hQ M e z) := by
  change cutStandardMap Q (cutLabels j hj Λ) θ γ e'.toLinearMap
      (cutStandardMap Q (cutLabels j hj Λ) θ γ g.hom z) =
    cutStandardMap Q (cutLabels j hj Λ) θ γ f
      (cutStandardMap Q (cutLabels j hj Λ) θ γ e.toLinearMap z)
  rw [← cutStandardMap_comp, ← cutStandardMap_comp,
    show e'.toLinearMap ∘ₗ g.hom = f ∘ₗ e.toLinearMap from LinearMap.ext h]

/-- Right multiplication by `b` on the bundled regular module. -/
theorem kappaSEquiv_op_smul (b : Dcᵐᵒᵖ) (z : Sb) :
    kappaSEquiv j hj Q Λ θ γ hQ (b • z) =
      kCutStdMap j hj Q Λ θ γ hQ (dRightMul j hj Q Λ θ γ b.unop)
        (kappaSEquiv j hj Q Λ θ γ hQ z) :=
  kappaSEquivOf_map j hj Q Λ θ γ hQ _ _ (rmul (ModuleCat.of Dc Dc) b.unop) _ (fun _ => rfl) z

omit [IsScalarTower k (TensorProductAlgebra k Q Λc ν₀) L'] in
theorem kappaLeft_op_smul (b : Dcᵐᵒᵖ) (x : DG.TensorProductOver Tc Kσ Sb) :
    kappaLeft j hj Q Λ Λc θ γ ν₀ hQ L' (b • x) =
      kCutTargetMap j hj Q Λ Λc θ γ ν₀ hQ L' (dRightMul j hj Q Λ θ γ b.unop)
        (kappaLeft j hj Q Λ Λc θ γ ν₀ hQ L' x) :=
  DFunLike.congr_fun (DG.TensorProductOver.addHom_ext
    (f := (kappaLeft j hj Q Λ Λc θ γ ν₀ hQ L').toAddMonoidHom.comp
      (DG.TensorProductOver.rightAct Tc Kσ Sb b))
    (g := (kCutTargetMap j hj Q Λ Λc θ γ ν₀ hQ L'
      (dRightMul j hj Q Λ θ γ b.unop)).toAddMonoidHom.comp
        (kappaLeft j hj Q Λ Λc θ γ ν₀ hQ L').toAddMonoidHom) fun r z => by
      change kappaLeft j hj Q Λ Λc θ γ ν₀ hQ L' (DG.TensorProductOver.tmul Tc r (b • z)) = _
      rw [kappaLeft_tmul, kappaSEquiv_op_smul]
      rfl) x

/-- Right multiplication by `b` on `K_b`, as a map of `E`-modules. -/
def kbRightMul (b : Dcᵐᵒᵖ) : Kb →ₗ[PF] Kb where
  toFun z := b • z
  map_add' x y := smul_add b x y
  map_smul' x z := (smul_comm x b z).symm

/-- `S_+` of a map between modules isomorphic to `D ⊠ L'`, in the coordinates of
`S_+(D ⊠ L')`. -/
theorem kappaSpEquivOf_map {N N' : ModuleCat.{0} (plusFactorAlgCat Q Λ Λc j hj θ ν₀ γ)}
    (e : PlusWrap Q Λ Λc j hj θ ν₀ γ N ≃ₗ[PF] MidSpect (k := k) Dc L')
    (e' : PlusWrap Q Λ Λc j hj θ ν₀ γ N' ≃ₗ[PF] MidSpect (k := k) Dc L') (g : N ⟶ N')
    (f : MidSpect (k := k) Dc L' →ₗ[PF] MidSpect (k := k) Dc L')
    (h : ∀ x, e' (g x) = f (e x)) (z : (kappaSpFunctor j hj Q Λ Λc θ γ ν₀ hQ).obj N) :
    kappaSpEquivOf j hj Q Λ Λc θ γ ν₀ hQ L' N' e'
        (((kappaSpFunctor j hj Q Λ Λc θ γ ν₀ hQ).map g).hom z) =
      plusStandardMap Q Λ Λc j hj θ ν₀ γ hQ f (kappaSpEquivOf j hj Q Λ Λc θ γ ν₀ hQ L' N e z) := by
  change plusStandardMap Q Λ Λc j hj θ ν₀ γ hQ e'.toLinearMap
      (plusStandardMap Q Λ Λc j hj θ ν₀ γ hQ (plusWrapHom Q Λ Λc j hj θ ν₀ γ g) z) =
    plusStandardMap Q Λ Λc j hj θ ν₀ γ hQ f
      (plusStandardMap Q Λ Λc j hj θ ν₀ γ hQ e.toLinearMap z)
  have H : e'.toLinearMap ∘ₗ plusWrapHom Q Λ Λc j hj θ ν₀ γ g = f ∘ₗ e.toLinearMap :=
    LinearMap.ext h
  exact (plusStandardMap_comp Q Λ Λc j hj θ ν₀ γ hQ _ _ z).symm.trans
    ((congrArg (fun φ => plusStandardMap Q Λ Λc j hj θ ν₀ γ hQ φ z) H).trans
      (plusStandardMap_comp Q Λ Λc j hj θ ν₀ γ hQ _ _ z))

theorem kappaRight_natural (b : Dcᵐᵒᵖ) (u : KCutSrc j hj Q Λ Λc θ γ ν₀ Dc hQ L') :
    kappaRight j hj Q Λ Λc θ γ ν₀ hQ L'
        (kCutSourceMap j hj Q Λ Λc θ γ ν₀ hQ L' (dRightMul j hj Q Λ θ γ b.unop) u) =
      b • kappaRight j hj Q Λ Λc θ γ ν₀ hQ L' u := by
  let hF := isTensorRepresented_kappaSpFunctor j hj Q Λ Λc θ γ ν₀ hQ
  let N := ModuleCat.of (plusFactorAlgCat Q Λ Λc j hj θ ν₀ γ) Kb
  let g : N ⟶ N := ModuleCat.ofHom (kbRightMul j hj Q Λ Λc θ γ ν₀ L' b)
  let e := kappaSpEquivOf j hj Q Λ Λc θ γ ν₀ hQ L' N (kbWrapEquiv j hj Q Λ Λc θ γ ν₀ L')
  let t := (ewEquiv (kappaSpFunctor j hj Q Λ Λc θ γ ν₀ hQ) hF N).symm (e.symm u)
  have hb : (b • t : DG.TensorProductOver PF Spb Kb) =
      DG.TensorProductOver.map LinearMap.id g.hom t :=
    DFunLike.congr_fun (DG.TensorProductOver.addHom_ext
      (f := DG.TensorProductOver.rightAct PF Spb Kb b)
      (g := DG.TensorProductOver.map LinearMap.id g.hom) fun p z => by
        rw [DG.TensorProductOver.rightAct_tmul, DG.TensorProductOver.map_tmul]
        rfl) t
  have hA : e.symm (kCutSourceMap j hj Q Λ Λc θ γ ν₀ hQ L' (dRightMul j hj Q Λ θ γ b.unop) u) =
      ((kappaSpFunctor j hj Q Λ Λc θ γ ν₀ hQ).map g).hom (e.symm u) := by
    apply e.injective
    rw [LinearEquiv.apply_symm_apply]
    exact ((kappaSpEquivOf_map j hj Q Λ Λc θ γ ν₀ hQ L' _ _ g _ (fun _ => rfl) _).trans
      (congrArg _ (e.apply_symm_apply u))).symm
  exact (congrArg (ewEquiv (kappaSpFunctor j hj Q Λ Λc θ γ ν₀ hQ) hF N).symm hA).trans
    ((ewEquiv_symm_natural _ hF g _).trans hb.symm)

variable {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : CapCoef Q Λc ν₀ L'), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}
  (hR : MidKLRRel j hj Q Λ Λc (θ + γ) ν₀ (CapCoef Q Λc ν₀ L') hL)
  (hP : PullOff k Q Λc ν₀ (CapCoef Q Λc ν₀ L')) (hPL : PullOffLeft k Q Λc ν₀ (CapCoef Q Λc ν₀ L'))
  (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))

/-- **Lemma 7.19 (K) at the cut, as an isomorphism of bimodules**:
`κ : K^σ ⊗_T S ≅ S₊ ⊗_E K_b`, the isomorphism `K^σ(S_cut D) ≅ S_+(D ⊠ L')` of (K) at `Y = D`
(`kCutPhiEquiv`, inverted) read through tensor representability. -/
def kappaCut : DG.TensorProductOver Tc Kσ Sb ≃+ DG.TensorProductOver PF Spb Kb :=
  ((kappaLeft j hj Q Λ Λc θ γ ν₀ hQ L').trans
    (kCutPhiEquiv Dc hQ hR hP hPL hκ).symm.toAddEquiv).trans
      (kappaRight j hj Q Λ Λc θ γ ν₀ hQ L').toAddEquiv

theorem kappaCut_apply (x : DG.TensorProductOver Tc Kσ Sb) :
    kappaCut j hj Q Λ Λc θ γ ν₀ hQ L' hR hP hPL hκ x =
      kappaRight j hj Q Λ Λc θ γ ν₀ hQ L' (kPsi Dc hQ hR hP hPL hκ
        (kappaLeft j hj Q Λ Λc θ γ ν₀ hQ L' x)) := rfl

/-- **`κ` is linear over `T^{λ⁺}`.** -/
theorem kappaCut_smul (t : Tp) (x : DG.TensorProductOver Tc Kσ Sb) :
    kappaCut j hj Q Λ Λc θ γ ν₀ hQ L' hR hP hPL hκ (t • x) =
      t • kappaCut j hj Q Λ Λc θ γ ν₀ hQ L' hR hP hPL hκ x :=
  (kappaCut_apply j hj Q Λ Λc θ γ ν₀ hQ L' hR hP hPL hκ _).trans
    ((congrArg (fun z => kappaRight j hj Q Λ Λc θ γ ν₀ hQ L' (kPsi Dc hQ hR hP hPL hκ z))
      (kappaLeft_smul j hj Q Λ Λc θ γ ν₀ hQ L' t x)).trans
    ((congrArg (kappaRight j hj Q Λ Λc θ γ ν₀ hQ L')
      ((kPsi Dc hQ hR hP hPL hκ).map_smul t _)).trans
    ((kappaRight j hj Q Λ Λc θ γ ν₀ hQ L').map_smul t _)))

/-- **`κ` is linear over `D` on the right**, by the naturality of (K) in `Y`. -/
theorem kappaCut_op_smul (b : Dcᵐᵒᵖ) (x : DG.TensorProductOver Tc Kσ Sb) :
    kappaCut j hj Q Λ Λc θ γ ν₀ hQ L' hR hP hPL hκ (b • x) =
      b • kappaCut j hj Q Λ Λc θ γ ν₀ hQ L' hR hP hPL hκ x :=
  (kappaCut_apply j hj Q Λ Λc θ γ ν₀ hQ L' hR hP hPL hκ _).trans
    ((congrArg (fun z => kappaRight j hj Q Λ Λc θ γ ν₀ hQ L' (kPsi Dc hQ hR hP hPL hκ z))
      (kappaLeft_op_smul j hj Q Λ Λc θ γ ν₀ hQ L' b x)).trans
    ((congrArg (kappaRight j hj Q Λ Λc θ γ ν₀ hQ L')
      (kCutPhiEquiv_symm_natural j hj Q Λ Λc θ γ ν₀ hQ L' (dRightMul j hj Q Λ θ γ b.unop)
        hR hP hPL hκ _)).trans
    (kappaRight_natural j hj Q Λ Λc θ γ ν₀ hQ L' b _)))

end Categorification.Stendhal.CupCap

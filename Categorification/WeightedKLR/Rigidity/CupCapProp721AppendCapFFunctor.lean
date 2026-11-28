/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapEFunctor

/-!
# `K ∘ 𝔉_i ≅ 𝔉_i ∘ K` on right modules

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the part for `𝔉_i`, at the level of module categories. On right modules,
`K = - ⊗_{T^λ_ν} K_ν` is `ordTensor` with the bimodule `K_ν = CapBimodule`, and `𝔉_i` is
induction along appending a black strand (`blackF`, `M ↦ M ⊗ e' T^λ_{{i} + ν}`; on the `λ⁺` side
`InductionAlong.functor` along `appendBlackTPAOp`). For every right `T^λ_ν`-module `M`,
`(M ⊗ e' T) ⊗ K_{{i} + ν} ≅ (M ⊗ K_ν) ⊗ e'⁺ T⁺`, naturally in `M` (`CupCap.capFOrdIso`).

The argument uses only an isomorphism `e' K_{{i} + ν} ≅ 𝔉_i(K_ν)` of
`(T^λ_ν, T^{λ⁺})`-bimodules, packaged as `CupCap.CapFData`: a map `fwd : K_{{i} + ν} → 𝔉_i(K_ν)`
(left multiplication by `e'` followed by the isomorphism) and its inverse `bwd`, compatible with
both actions.

## Main definitions

* `CupCap.capLeftMul`: the left action of `a ∈ T^λ_ν` on `K_ν`, as a map of right modules.
* `CupCap.CapFData`: the bimodule isomorphism `e' K_{{i} + ν} ≅ 𝔉_i(K_ν)`.
* `CupCap.capFOrdEquiv`: `(M ⊗ e' T) ⊗ K_{{i} + ν} ≅ (M ⊗ K_ν) ⊗ e'⁺ T⁺`.
* `CupCap.capFOrdIso`: the natural isomorphism `𝔉_i ⋙ K ≅ K ⋙ 𝔉_i`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory KLR KLRAlgebra MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν₀ : Multiset I}
  {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

variable (ν : Multiset I) (i : I)

set_option hygiene false in
local notation "TA" => TensorProductAlgebra k Q Λ ν
set_option hygiene false in
local notation "TAᵢ" => TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν)
set_option hygiene false in
local notation "TPp" => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
set_option hygiene false in
local notation "TPpᵢ" =>
  TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (((Singleton.singleton i : Multiset I) + ν) + ν₀)
set_option hygiene false in
local notation "CB" => CapBimodule k Q Λ Λc j hj ν ν₀ L
set_option hygiene false in
local notation "CBᵢ" => CapBimodule k Q Λ Λc j hj ((Singleton.singleton i : Multiset I) + ν) ν₀ L
set_option hygiene false in
local notation "aBl" => (appendBlack Q Λ i ν : TensorProductAlgebra k Q Λ ν →ₙ+*
  TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν))
set_option hygiene false in
local notation "aT" => appendBlackTPAOp k Q Λ Λc j hj ν ν₀ i
set_option hygiene false in
local notation "OrdK" => ordTensor TPpᵐᵒᵖ TAᵐᵒᵖ (OpBimodule TA CB)
set_option hygiene false in
local notation "OrdKᵢ" => ordTensor TPpᵢᵐᵒᵖ TAᵢᵐᵒᵖ (OpBimodule TAᵢ CBᵢ)
set_option hygiene false in
local notation "aOp" => appendBlackOp Q Λ i ν

variable {ν} in
variable (k Q Λ Λc j hj ν₀ L) in
/-- The left action of `a ∈ T^λ_ν` on `K_ν`, as a map of right `T^{λ⁺}`-modules. -/
def capLeftMul (a : TA) : CB →ₗ[TPpᵐᵒᵖ] CB where
  toFun c := a • c
  map_add' := smul_add a
  map_smul' b c := smul_comm a b c

theorem capLeftMul_one :
    capLeftMul k Q Λ Λc j hj ν₀ L (1 : TA) = LinearMap.id :=
  LinearMap.ext fun c => one_smul _ c

variable (k Q Λ Λc j hj ν₀ L) in
/-- **The isomorphism `e' K_{{i} + ν} ≅ 𝔉_i(K_ν)`** of `(T^λ_ν, T^{λ⁺})`-bimodules: `fwd`
(left multiplication by `e'`, then the isomorphism) and its inverse `bwd`. -/
structure CapFData where
  /-- `K_{{i} + ν} → 𝔉_i(K_ν)`, vanishing off `e' K_{{i} + ν}`. -/
  fwd : CBᵢ →+ Ind CB aT
  /-- `𝔉_i(K_ν) → e' K_{{i} + ν} ⊆ K_{{i} + ν}`. -/
  bwd : Ind CB aT →+ CBᵢ
  fwd_smul_left : ∀ (a : TA) (c : CBᵢ),
    fwd (aBl a • c) = Ind.map (capLeftMul k Q Λ Λc j hj ν₀ L a) (fwd c)
  fwd_smul_right : ∀ (b : TPpᵢᵐᵒᵖ) (c : CBᵢ), fwd (b • c) = b • fwd c
  bwd_smul_left : ∀ (a : TA) (w : Ind CB aT),
    bwd (Ind.map (capLeftMul k Q Λ Λc j hj ν₀ L a) w) = aBl a • bwd w
  bwd_smul_right : ∀ (b : TPpᵢᵐᵒᵖ) (w : Ind CB aT), bwd (b • w) = b • bwd w
  fwd_bwd : ∀ w, fwd (bwd w) = w
  bwd_fwd : ∀ c, bwd (fwd c) = aBl 1 • c

variable {ν i}

namespace CapFData

variable (D : CapFData k Q Λ Λc j hj ν₀ L ν i)

theorem fwd_unit (c : CBᵢ) : D.fwd (aBl 1 • c) = D.fwd c := by
  rw [D.fwd_smul_left, capLeftMul_one, Ind.map_id]
  rfl

end CapFData

variable (D : CapFData k Q Λ Λc j hj ν₀ L ν i) (X : ModuleCat.{0} TAᵐᵒᵖ)

set_option hygiene false in
local notation "T₁" => DG.TensorProductOver.tmul (M := InDegreeZero (OpBimodule TAᵢ CBᵢ))
  (N := InDegreeZero ((blackF Q Λ i ν).obj X)) TAᵢᵐᵒᵖ
set_option hygiene false in
local notation "T₀" c:max x:max => (DG.TensorProductOver.tmul
  (M := InDegreeZero (OpBimodule TA CB)) (N := InDegreeZero X) TAᵐᵒᵖ c x : (OrdK).obj X)
set_option hygiene false in
local notation "FX" => Ind X aOp
set_option hygiene false in
local notation "IK" => Ind ((OrdK).obj X) aT
set_option hygiene false in
local notation "IT" => Ind.tmul (N := ((OrdK).obj X : Type)) (φ := aT)

/-! ### `w, x ↦ w ⊗ x` from `𝔉_i(K_ν)` and `M` -/

omit [DecidableEq I] in
/-- Additive maps out of an induced module agree once they agree on the generators `z ⊗ n`. -/
private theorem indAddHom_ext {A B : Type} [Ring A] [Ring B] {φ : A →ₙ+* B} {N : Type}
    [AddCommGroup N] [Module A N] {P : Type*} [AddCommGroup P] {f g : Ind N φ →+ P}
    (h : ∀ z n, f (Ind.tmul z n) = g (Ind.tmul z n)) : f = g :=
  AddMonoidHom.ext fun t => by
    induction t using Ind.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul z n => exact h z n
    | add s t hs ht => rw [map_add, map_add, hs, ht]

/-- `w ⊗ c, x ↦ w ⊗ (c ⊗ x)`, from `𝔉_i(K_ν)` and `M` to `𝔉_i(K_ν ⊗ M)`. -/
def indTensorRight : Ind CB aT →+ (X →+ IK) :=
  Ind.liftAdd (fun w c => AddMonoidHom.mk' (fun x => IT w (T₀ c x))
      fun _ _ => (congrArg (IT w) (DG.TensorProductOver.tmul_add _ _ _)).trans
        (Ind.tmul_add _ _ _))
    (fun _ _ _ => AddMonoidHom.ext fun _ => Ind.add_tmul _ _ _)
    (fun w _ _ => AddMonoidHom.ext fun _ =>
      (congrArg (IT w) (DG.TensorProductOver.add_tmul _ _ _)).trans (Ind.tmul_add _ _ _))
    (fun w b c => AddMonoidHom.ext fun x =>
      Ind.op_smul_tmul (N := ((OrdK).obj X : Type)) w b (T₀ c x))

theorem indTensorRight_tmul (w : Corner aT) (c : CB) (x : X) :
    indTensorRight X (Ind.tmul w c) x = IT w (T₀ c x) :=
  rfl

theorem indTensorRight_add (w w' : Ind CB aT) (x : X) :
    indTensorRight X (w + w') x = indTensorRight X w x + indTensorRight X w' x :=
  DFunLike.congr_fun (map_add (indTensorRight X) w w') x

theorem indTensorRight_capLeftMul (a : TAᵐᵒᵖ) (w : Ind CB aT) (x : X) :
    indTensorRight X (Ind.map (capLeftMul k Q Λ Λc j hj ν₀ L (unop a)) w) x =
      indTensorRight X w (a • x) :=
  DFunLike.congr_fun (indAddHom_ext
    (f := ((indTensorRight X).flip x).comp
      (Ind.map (capLeftMul k Q Λ Λc j hj ν₀ L (unop a))).toAddMonoidHom)
    (g := (indTensorRight X).flip (a • x))
    fun z c => congrArg (IT z) (DG.TensorProductOver.op_smul_tmul (A := TAᵐᵒᵖ)
      (M := InDegreeZero (OpBimodule TA CB)) (N := InDegreeZero X) a c x)) w

theorem indTensorRight_smul (b : TPpᵢᵐᵒᵖ) (w : Ind CB aT) (x : X) :
    indTensorRight X (b • w) x = b • indTensorRight X w x :=
  DFunLike.congr_fun (indAddHom_ext
    (f := ((indTensorRight X).flip x).comp
      (AddMonoidHom.mk' (fun w : Ind CB aT => b • w) (smul_add b)))
    (g := (AddMonoidHom.mk' (fun s : IK => b • s) (smul_add b)).comp ((indTensorRight X).flip x))
    fun z c => (congrArg (fun y => indTensorRight X y x) (Ind.smul_tmul b z c)).trans
      (Ind.smul_tmul (N := ((OrdK).obj X : Type)) b z (T₀ c x)).symm) w

/-! ### The forward map -/

/-- `c, z ⊗ x ↦ fwd(z c) ⊗ x`, for `c ∈ K_{{i} + ν}` and `z ⊗ x ∈ 𝔉_i M`. -/
def capFOrdInner (c : CBᵢ) : FX →+ IK :=
  Ind.liftAdd (fun z x => indTensorRight X (D.fwd (unop z.1 • c)) x)
    (fun z z' x => (congrArg (fun y => indTensorRight X y x)
      ((congrArg D.fwd (add_smul (unop z.1) (unop z'.1) c)).trans (map_add _ _ _))).trans
      (indTensorRight_add X _ _ x))
    (fun _ x x' => map_add _ x x')
    (fun z a x => (congrArg (fun y => indTensorRight X y x)
      ((congrArg D.fwd (mul_smul (aBl (unop a)) (unop z.1) c)).trans
        (D.fwd_smul_left _ _))).trans (indTensorRight_capLeftMul X a _ x))

theorem capFOrdInner_tmul (c : CBᵢ) (z : Corner aOp) (x : X) :
    capFOrdInner D X c (Ind.tmul z x) = indTensorRight X (D.fwd (unop z.1 • c)) x :=
  rfl

theorem capFOrdInner_smul (c : CBᵢ) (b : TAᵢᵐᵒᵖ) (t : FX) :
    capFOrdInner D X c (b • t) = capFOrdInner D X (unop b • c) t :=
  DFunLike.congr_fun (indAddHom_ext
    (f := (capFOrdInner D X c).comp (AddMonoidHom.mk' (fun t : FX => b • t) (smul_add b)))
    (g := capFOrdInner D X (unop b • c))
    fun z x => (congrArg (capFOrdInner D X c) (Ind.smul_tmul b z x)).trans
      (congrArg (fun y => indTensorRight X (D.fwd y) x) (mul_smul (unop z.1) (unop b) c))) t

theorem capFOrdInner_add (c c' : CBᵢ) :
    capFOrdInner D X (c + c') = capFOrdInner D X c + capFOrdInner D X c' :=
  indAddHom_ext fun z x => (congrArg (fun y => indTensorRight X y x)
    ((congrArg D.fwd (smul_add (unop z.1) c c')).trans (map_add _ _ _))).trans
    (indTensorRight_add X _ _ x)

/-- The bilinear map `c, t ↦ capFOrdInner c t`. -/
def capFOrdBil :
    InDegreeZero (OpBimodule TAᵢ CBᵢ) →+ InDegreeZero ((blackF Q Λ i ν).obj X) →+ IK :=
  AddMonoidHom.mk' (fun c => capFOrdInner D X (c : CBᵢ)) fun c c' =>
    capFOrdInner_add D X (c : CBᵢ) c'

/-- **`(M ⊗ e' T) ⊗ K_{{i} + ν} → (M ⊗ K_ν) ⊗ e'⁺ T⁺`**, `c ⊗ (z ⊗ x) ↦ fwd(z c) ⊗ x`. -/
def capFOrdFwd : (OrdKᵢ).obj ((blackF Q Λ i ν).obj X) →+ IK :=
  DG.TensorProductOver.lift (capFOrdBil D X) fun b c t =>
    (capFOrdInner_smul D X (c : CBᵢ) b t).symm

theorem capFOrdFwd_tmul (c : CBᵢ) (t : FX) : capFOrdFwd D X (T₁ c t) = capFOrdInner D X c t :=
  rfl

/-! ### The backward map -/

theorem capFOrd_unitGen_smul (a : TAᵐᵒᵖ) :
    (op (aBl (unop a)) • unitGen aOp : Corner aOp) = op a • unitGen aOp := by
  refine Subtype.ext ?_
  change aOp a * aOp 1 = aOp 1 * aOp a
  rw [← map_mul, ← map_mul, mul_one, one_mul]

/-- `c, x ↦ bwd(w ⊗ c) ⊗ (e' ⊗ x)`. -/
def capFOrdBwdBil (w : Corner aT) : InDegreeZero (OpBimodule TA CB) →+ InDegreeZero X →+
    (OrdKᵢ).obj ((blackF Q Λ i ν).obj X) :=
  AddMonoidHom.mk' (fun c => AddMonoidHom.mk'
      (fun x => T₁ (D.bwd (Ind.tmul w c)) (Ind.tmul (unitGen aOp) x))
      fun x x' => (congrArg (T₁ (D.bwd (Ind.tmul w c))) (Ind.tmul_add _ x x')).trans
        (DG.TensorProductOver.tmul_add _ _ _))
    fun c c' => AddMonoidHom.ext fun x =>
      (congrArg (fun y : CBᵢ => T₁ y (Ind.tmul (unitGen aOp) x))
        ((congrArg D.bwd (Ind.tmul_add w (c : CB) (c' : CB))).trans (map_add D.bwd _ _))).trans
        (DG.TensorProductOver.add_tmul _ _ _)

theorem capFOrdBwdBil_balanced (w : Corner aT) (a : TAᵐᵒᵖ) (c : InDegreeZero (OpBimodule TA CB))
    (x : InDegreeZero X) : capFOrdBwdBil D X w (op a • c) x = capFOrdBwdBil D X w c (a • x) := by
  change T₁ (D.bwd (Ind.map (capLeftMul k Q Λ Λc j hj ν₀ L (unop a)) (Ind.tmul w (c : CB))))
      (Ind.tmul (unitGen aOp) x) = T₁ (D.bwd (Ind.tmul w (c : CB))) (Ind.tmul (unitGen aOp) (a • x))
  rw [D.bwd_smul_left]
  refine (DG.TensorProductOver.op_smul_tmul (A := TAᵢᵐᵒᵖ)
    (M := InDegreeZero (OpBimodule TAᵢ CBᵢ)) (N := InDegreeZero ((blackF Q Λ i ν).obj X))
    (op (aBl (unop a))) (D.bwd (Ind.tmul w (c : CB))) (Ind.tmul (unitGen aOp) x)).trans ?_
  refine congrArg (T₁ (D.bwd (Ind.tmul w (c : CB)))) ?_
  change op (aBl (unop a)) • Ind.tmul (unitGen aOp) (x : X) = Ind.tmul (unitGen aOp) (a • (x : X))
  rw [Ind.smul_tmul, capFOrd_unitGen_smul, Ind.op_smul_tmul]

/-- `s ↦ ` the image of `w ⊗ s`, for `s ∈ K_ν ⊗ M`. -/
def capFOrdBwdInner (w : Corner aT) : (OrdK).obj X →+ (OrdKᵢ).obj ((blackF Q Λ i ν).obj X) :=
  DG.TensorProductOver.lift (capFOrdBwdBil D X w) (capFOrdBwdBil_balanced D X w)

theorem capFOrdBwdInner_add (w w' : Corner aT) :
    capFOrdBwdInner D X (w + w') = capFOrdBwdInner D X w + capFOrdBwdInner D X w' :=
  DG.TensorProductOver.addHom_ext fun c x =>
    (congrArg (fun y : CBᵢ => T₁ y (Ind.tmul (unitGen aOp) x))
      ((congrArg D.bwd (Ind.add_tmul w w' (c : CB))).trans (map_add D.bwd _ _))).trans
      (DG.TensorProductOver.add_tmul _ _ _)

theorem capFOrdBwdInner_smul (w : Corner aT) (b : TPpᵐᵒᵖ) (s : (OrdK).obj X) :
    capFOrdBwdInner D X (op b • w) s = capFOrdBwdInner D X w (b • s) :=
  DFunLike.congr_fun (DG.TensorProductOver.addHom_ext
    (f := capFOrdBwdInner D X (op b • w))
    (g := (capFOrdBwdInner D X w).comp
      (AddMonoidHom.mk' (fun s : (OrdK).obj X => b • s) (smul_add b)))
    fun c x => congrArg (fun y : CBᵢ => T₁ y (Ind.tmul (unitGen aOp) x))
      (congrArg D.bwd (Ind.op_smul_tmul w b (c : CB)))) s

/-- **`(M ⊗ K_ν) ⊗ e'⁺ T⁺ → (M ⊗ e' T) ⊗ K_{{i} + ν}`**,
`w ⊗ (c ⊗ x) ↦ bwd(w ⊗ c) ⊗ (e' ⊗ x)`. -/
def capFOrdBwd : IK →+ (OrdKᵢ).obj ((blackF Q Λ i ν).obj X) :=
  Ind.liftAdd (fun w s => capFOrdBwdInner D X w s)
    (fun w w' s => DFunLike.congr_fun (capFOrdBwdInner_add D X w w') s)
    (fun _ s s' => map_add _ s s') (capFOrdBwdInner_smul D X)

theorem capFOrdBwd_indTensorRight (w : Ind CB aT) (x : X) :
    capFOrdBwd D X (indTensorRight X w x) = T₁ (D.bwd w) (Ind.tmul (unitGen aOp) x) :=
  DFunLike.congr_fun (indAddHom_ext
    (f := (capFOrdBwd D X).comp ((indTensorRight X).flip x))
    (g := (AddMonoidHom.mk' (fun y : CBᵢ => T₁ y (Ind.tmul (unitGen aOp) x))
      fun _ _ => DG.TensorProductOver.add_tmul _ _ _).comp D.bwd)
    fun _ _ => rfl) w

/-! ### The two maps are inverse -/

theorem capFOrdBwd_fwd_tmul (c : CBᵢ) (t : FX) :
    capFOrdBwd D X (capFOrdFwd D X (T₁ c t)) = T₁ c t :=
  DFunLike.congr_fun (indAddHom_ext
    (f := ((capFOrdBwd D X).comp (capFOrdInner D X c)))
    (g := AddMonoidHom.mk' (T₁ c) (DG.TensorProductOver.tmul_add (A := TAᵢᵐᵒᵖ)
      (M := InDegreeZero (OpBimodule TAᵢ CBᵢ)) (N := InDegreeZero ((blackF Q Λ i ν).obj X)) c))
    fun z x => by
      change capFOrdBwd D X (indTensorRight X (D.fwd (unop z.1 • c)) x) = T₁ c (Ind.tmul z x)
      rw [capFOrdBwd_indTensorRight, D.bwd_fwd, ← mul_smul]
      have hz : aBl 1 * unop z.1 = unop z.1 := congrArg unop z.2
      rw [hz]
      refine (DG.TensorProductOver.op_smul_tmul (A := TAᵢᵐᵒᵖ)
        (M := InDegreeZero (OpBimodule TAᵢ CBᵢ)) (N := InDegreeZero ((blackF Q Λ i ν).obj X))
        z.1 c (Ind.tmul (unitGen aOp) x)).trans ?_
      refine congrArg (T₁ c) ?_
      change z.1 • Ind.tmul (unitGen aOp) x = Ind.tmul z x
      rw [Ind.smul_tmul]
      exact congrArg (fun y => Ind.tmul y x) (Subtype.ext z.2)) t

theorem capFOrdBwd_fwd (t : (OrdKᵢ).obj ((blackF Q Λ i ν).obj X)) :
    capFOrdBwd D X (capFOrdFwd D X t) = t :=
  DFunLike.congr_fun (DG.TensorProductOver.addHom_ext
    (f := (capFOrdBwd D X).comp (capFOrdFwd D X)) (g := AddMonoidHom.id _)
    fun c t => capFOrdBwd_fwd_tmul D X (c : CBᵢ) t) t

theorem capFOrdFwd_bwd (s : IK) : capFOrdFwd D X (capFOrdBwd D X s) = s :=
  DFunLike.congr_fun (indAddHom_ext (f := (capFOrdFwd D X).comp (capFOrdBwd D X))
    (g := AddMonoidHom.id _) fun w s => DFunLike.congr_fun (DG.TensorProductOver.addHom_ext
      (f := (capFOrdFwd D X).comp (capFOrdBwdInner D X w))
      (g := AddMonoidHom.mk' (IT w) (Ind.tmul_add (N := ((OrdK).obj X : Type)) w)) fun c x => by
        change indTensorRight X (D.fwd (aBl 1 • D.bwd (Ind.tmul w (c : CB)))) x = _
        rw [D.fwd_unit, D.fwd_bwd]
        rfl) s) s

/-! ### Linearity and naturality -/

theorem capFOrdInner_smul_right (b : TPpᵢᵐᵒᵖ) (c : CBᵢ) (t : FX) :
    capFOrdInner D X (b • c) t = b • capFOrdInner D X c t :=
  DFunLike.congr_fun (indAddHom_ext (f := capFOrdInner D X (b • c))
    (g := (AddMonoidHom.mk' (fun s : IK => b • s) (smul_add b)).comp (capFOrdInner D X c))
    fun z x => (congrArg (fun y => indTensorRight X y x)
      ((congrArg D.fwd (smul_comm (unop z.1) b c)).trans (D.fwd_smul_right _ _))).trans
      (indTensorRight_smul X b _ x)) t

theorem capFOrdFwd_smul (b : TPpᵢᵐᵒᵖ) (t : (OrdKᵢ).obj ((blackF Q Λ i ν).obj X)) :
    capFOrdFwd D X (b • t) = b • capFOrdFwd D X t :=
  DFunLike.congr_fun (DG.TensorProductOver.addHom_ext
    (f := (capFOrdFwd D X).comp (AddMonoidHom.mk'
      (fun s : (OrdKᵢ).obj ((blackF Q Λ i ν).obj X) => b • s) (smul_add b)))
    (g := (AddMonoidHom.mk' (fun s : IK => b • s) (smul_add b)).comp (capFOrdFwd D X))
    fun c t => capFOrdInner_smul_right D X b (c : CBᵢ) t) t

/-- **`(M ⊗ e' T) ⊗ K_{{i} + ν} ≅ (M ⊗ K_ν) ⊗ e'⁺ T⁺`** as right `T^{λ⁺}`-modules,
`c ⊗ (z ⊗ x) ↦ fwd(z c) ⊗ x`. -/
def capFOrdEquiv :
    (OrdKᵢ).obj ((blackF Q Λ i ν).obj X) ≃ₗ[TPpᵢᵐᵒᵖ]
      (InductionAlong.functor.{0, 0} aT).obj ((OrdK).obj X) where
  toFun := capFOrdFwd D X
  invFun := capFOrdBwd D X
  map_add' := map_add _
  map_smul' := capFOrdFwd_smul D X
  left_inv := capFOrdBwd_fwd D X
  right_inv := capFOrdFwd_bwd D X

theorem indTensorRight_map {Y : ModuleCat.{0} TAᵐᵒᵖ} (g : X ⟶ Y) (w : Ind CB aT) (x : X) :
    Ind.map ((OrdK).map g).hom (indTensorRight X w x) = indTensorRight Y w (g.hom x) :=
  DFunLike.congr_fun (indAddHom_ext
    (f := (Ind.map ((OrdK).map g).hom).toAddMonoidHom.comp ((indTensorRight X).flip x))
    (g := (indTensorRight Y).flip (g.hom x)) fun _ _ => rfl) w

/-- **`K ∘ 𝔉_i ≅ 𝔉_i ∘ K` on right modules** (Webster, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the part for `𝔉_i`): `(M ⊗ e' T) ⊗ K_{{i} + ν} ≅ (M ⊗ K_ν) ⊗ e'⁺ T⁺`,
`c ⊗ (z ⊗ x) ↦ fwd(z c) ⊗ x`, naturally in the right `T^λ_ν`-module `M`. Both sides are
composites of `ordTensor` and induction functors, the form taken by
`mapDerivedCategoryIsoOfIso`. -/
def capFOrdIso : blackF Q Λ i ν ⋙ OrdKᵢ ≅ OrdK ⋙ InductionAlong.functor.{0, 0} aT :=
  NatIso.ofComponents (fun X => (capFOrdEquiv D X).toModuleIso) fun {X Y} g =>
    ModuleCat.hom_ext (LinearMap.toAddMonoidHom_injective
      (DG.TensorProductOver.addHom_ext fun c t => DFunLike.congr_fun (indAddHom_ext
        (f := (capFOrdFwd D Y).comp ((AddMonoidHom.mk' (DG.TensorProductOver.tmul
          (M := InDegreeZero (OpBimodule TAᵢ CBᵢ)) (N := InDegreeZero ((blackF Q Λ i ν).obj Y))
          TAᵢᵐᵒᵖ c) (DG.TensorProductOver.tmul_add (A := TAᵢᵐᵒᵖ)
          (M := InDegreeZero (OpBimodule TAᵢ CBᵢ)) (N := InDegreeZero ((blackF Q Λ i ν).obj Y))
          c)).comp (Ind.map g.hom).toAddMonoidHom))
        (g := (Ind.map ((OrdK).map g).hom).toAddMonoidHom.comp
          ((capFOrdFwd D X).comp (AddMonoidHom.mk' (DG.TensorProductOver.tmul
            (M := InDegreeZero (OpBimodule TAᵢ CBᵢ))
            (N := InDegreeZero ((blackF Q Λ i ν).obj X)) TAᵢᵐᵒᵖ c)
            (DG.TensorProductOver.tmul_add (A := TAᵢᵐᵒᵖ)
            (M := InDegreeZero (OpBimodule TAᵢ CBᵢ))
            (N := InDegreeZero ((blackF Q Λ i ν).obj X)) c))))
        fun _ x => (indTensorRight_map X g _ x).symm) t))

end Categorification.Stendhal.CupCap

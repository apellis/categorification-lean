/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapE
import Categorification.WeightedKLR.RedStrands.BlackModuleFunctors
import Categorification.Algebra.DegreewiseTensor

/-!
# `K ∘ 𝔈_i ≅ 𝔈_i ∘ K` on right modules

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the part for `𝔈_i`, at the level of module categories. On right modules,
`K = - ⊗_{T^λ_ν} K_ν` is `ordTensor` with the bimodule `K_ν = CapBimodule`, and `𝔈_i` is
restriction along appending a black strand (`blackE`, `M ↦ M e'`; on the `λ⁺` side
`InductionAlong.resFunctor` along `appendBlackTPAOp`). For every right `T^λ_{{i} + ν}`-module
`M`, the map `c ⊗ m ↦ ι(c) ⊗ m` is an isomorphism
`K_ν ⊗ M e' ≅ (K_{{i} + ν} ⊗ M) e'⁺`, natural in `M` (`CupCap.capEOrdIso`).

The argument uses only the bimodule isomorphism `T^λ_{{i} + ν} e' ⊗_{T^λ_ν} K_ν ≅ K_{{i} + ν} e'⁺`
of `CupCap.capEEquiv` and the compatibilities of `ι` with both actions, packaged as
`CupCap.CapAppendData`. The two cases are `CupCap.capAppendDataMid` (`j < ℓ`) and
`CupCap.capAppendDataTop` (`j = ℓ`).

Route hypotheses (tracked), as for `CupCap.capEEquivMid` and `CupCap.capEEquivTop`: each piece
`L e(t)` finitely generated over `k` (`hfin`), `Q` symmetric (`hQ`), the cup scalars units
(`hκ`) and the pull-off identities (`hP`, `hPL`).

## Main definitions

* `CupCap.CapAppendData`: a map `ι : K_ν → K_{{i} + ν}` compatible with both actions, with the
  multiplication `T^λ_{{i} + ν} e' ⊗ K_ν → K_{{i} + ν} e'⁺` an isomorphism.
* `CupCap.capEOrdEquiv`: `K_ν ⊗ M e' ≅ (K_{{i} + ν} ⊗ M) e'⁺`.
* `CupCap.capEOrdIso`: the natural isomorphism `𝔈_i ⋙ K ≅ K ⋙ 𝔈_i`.
* `CupCap.capEOrdIsoMid`, `CupCap.capEOrdIsoTop`: the two cases.
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

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "TA" => TensorProductAlgebra k Q Λ ν
local notation "TAᵢ" => TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν)
local notation "TPp" => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
local notation "TPpᵢ" =>
  TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (((Singleton.singleton i : Multiset I) + ν) + ν₀)
local notation "CB" => CapBimodule k Q Λ Λc j hj ν ν₀ L
local notation "CBᵢ" => CapBimodule k Q Λ Λc j hj ((Singleton.singleton i : Multiset I) + ν) ν₀ L
local notation "aBl" => (appendBlack Q Λ i ν : TensorProductAlgebra k Q Λ ν →ₙ+*
  TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν))
local notation "aT" => appendBlackTPAOp k Q Λ Λc j hj ν ν₀ i
local notation "OrdK" => ordTensor TPpᵐᵒᵖ TAᵐᵒᵖ (OpBimodule TA CB)
local notation "OrdKᵢ" => ordTensor TPpᵢᵐᵒᵖ TAᵢᵐᵒᵖ (OpBimodule TAᵢ CBᵢ)
local notation "aOp" => appendBlackOp Q Λ i ν

variable (k Q Λ Λc j hj ν₀ L) in
/-- **A map appending a black strand to `K_ν`**: an additive map `ι : K_ν → K_{{i} + ν}` carrying
the left action of `a` to that of `appendBlack(a)` and the right action of `b` to that of
`appendBlack(b)`, together with the isomorphism `T^λ_{{i} + ν} e' ⊗_{T^λ_ν} K_ν ≅ K_{{i} + ν} e'⁺`,
`a ⊗ c ↦ a · ι(c)`. -/
structure CapAppendData where
  /-- The map `K_ν → K_{{i} + ν}`. -/
  iota : CB →+ CBᵢ
  smul_left : ∀ (a : TA) (c : CB), iota (a • c) = aBl a • iota c
  smul_right : ∀ (b : TPpᵐᵒᵖ) (c : CB), iota (b • c) = aT b • iota c
  /-- `T^λ_{{i} + ν} e' ⊗_{T^λ_ν} K_ν ≅ K_{{i} + ν} e'⁺`. -/
  equiv : Ind CB aBl ≃ₗ[TAᵢ] LinearMap.range (capERight L ν i : CBᵢ →ₗ[TAᵢ] CBᵢ)
  equiv_tmul : ∀ (z : Corner aBl) (c : CB), (equiv (Ind.tmul z c) : CBᵢ) = z.1 • iota c

variable {ν i}

namespace CapAppendData

variable (D : CapAppendData k Q Λ Λc j hj ν₀ L ν i)

theorem fix (c : CB) : aT 1 • D.iota c = D.iota c := by
  rw [← D.smul_right, one_smul]

/-- `K_{{i} + ν} → T^λ_{{i} + ν} e' ⊗_{T^λ_ν} K_ν`: the right action of `e'⁺`, followed by the
inverse of `D.equiv`. -/
def proj : CBᵢ →ₗ[TAᵢ] Ind CB aBl :=
  D.equiv.symm.toLinearMap ∘ₗ (capERight L ν i : CBᵢ →ₗ[TAᵢ] CBᵢ).rangeRestrict

theorem equiv_proj (c : CBᵢ) : (D.equiv (D.proj c) : CBᵢ) = aT 1 • c := by
  change ((D.equiv (D.equiv.symm _)) : CBᵢ) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem proj_iota (c : CB) : D.proj (D.iota c) = Ind.tmul (unitGen aBl) c := by
  refine D.equiv.symm_apply_eq.mpr (Subtype.ext ?_)
  change aT 1 • D.iota c = (D.equiv (Ind.tmul (unitGen aBl) c) : CBᵢ)
  rw [D.equiv_tmul]
  exact (D.fix c).trans ((congrArg D.iota (one_smul _ c)).symm.trans (D.smul_left 1 c))

end CapAppendData

variable (D : CapAppendData k Q Λ Λc j hj ν₀ L ν i)
  (X : ModuleCat.{0} (TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν))ᵐᵒᵖ)

set_option hygiene false in
local notation "T₁" => DG.TensorProductOver.tmul (M := InDegreeZero (OpBimodule TAᵢ CBᵢ))
  (N := InDegreeZero X) TAᵢᵐᵒᵖ
set_option hygiene false in
local notation "T₀" => DG.TensorProductOver.tmul (M := InDegreeZero (OpBimodule TA CB))
  (N := InDegreeZero ((blackE Q Λ i ν).obj X)) TAᵐᵒᵖ
set_option hygiene false in
local notation "rv" => InductionAlong.Res.val (φ := aOp) (M := X)

theorem capEOrd_fixRes (c : CB) (m : InductionAlong.Res aOp X) :
    (aT 1 • T₁ (D.iota c) m.val : (OrdKᵢ).obj X) = T₁ (D.iota c) m.val :=
  congrArg (fun y : CBᵢ => T₁ y m.val) (D.fix c)

/-- The bilinear map `c, m ↦ ι(c) ⊗ m`. -/
def capEOrdBil : InDegreeZero (OpBimodule TA CB) →+
    InDegreeZero ((blackE Q Λ i ν).obj X) →+ (resFunctor.{0, 0} aT).obj ((OrdKᵢ).obj X) :=
  AddMonoidHom.mk' (fun c => AddMonoidHom.mk'
      (fun m => InductionAlong.Res.mk (T₁ (D.iota c) (rv m)) (capEOrd_fixRes D X c m))
      (fun _ _ => InductionAlong.Res.ext (DG.TensorProductOver.tmul_add _ _ _)))
    (fun c c' => AddMonoidHom.ext fun m => InductionAlong.Res.ext
      ((congrArg (fun y : CBᵢ => T₁ y (rv m)) (map_add D.iota (c : CB) (c' : CB))).trans
        (DG.TensorProductOver.add_tmul _ _ _)))

theorem capEOrdBil_tmul (c : InDegreeZero (OpBimodule TA CB))
    (m : InDegreeZero ((blackE Q Λ i ν).obj X)) :
    InductionAlong.Res.val (capEOrdBil D X c m) = T₁ (D.iota c) (rv m) :=
  rfl

theorem capEOrdBil_balanced (b : TAᵐᵒᵖ) (c : InDegreeZero (OpBimodule TA CB))
    (m : InDegreeZero ((blackE Q Λ i ν).obj X)) :
    capEOrdBil D X (op b • c) m = capEOrdBil D X c (b • m) :=
  InductionAlong.Res.ext
    ((congrArg (fun y : CBᵢ => T₁ y (rv m)) (D.smul_left (unop b) (c : CB))).trans
    (DG.TensorProductOver.op_smul_tmul (A := TAᵢᵐᵒᵖ)
      (M := InDegreeZero (OpBimodule TAᵢ CBᵢ)) (N := InDegreeZero X) (op (aBl (unop b)))
      (D.iota (c : CB)) (rv m)))

/-- **`K_ν ⊗ M e' → (K_{{i} + ν} ⊗ M) e'⁺`**, `c ⊗ m ↦ ι(c) ⊗ m`. -/
def capEOrdFwd :
    (OrdK).obj ((blackE Q Λ i ν).obj X) →+ (resFunctor.{0, 0} aT).obj ((OrdKᵢ).obj X) :=
  DG.TensorProductOver.lift (capEOrdBil D X) (capEOrdBil_balanced D X)

theorem capEOrdFwd_tmul (c : InDegreeZero (OpBimodule TA CB))
    (m : InDegreeZero ((blackE Q Λ i ν).obj X)) :
    capEOrdFwd D X (T₀ c m) = capEOrdBil D X c m :=
  rfl

theorem capEOrd_cornerFix (z : Corner aBl) (x : X) : aOp 1 • (op z.1 • x : X) = op z.1 • x := by
  rw [← mul_smul]
  exact congrArg (· • x) (congrArg op z.2)

/-- `x ↦ x a` for `a ∈ T^λ_{{i} + ν} e'`, into `M e'`. -/
def capEOrdCorner (z : Corner aBl) : X →+ InductionAlong.Res aOp X :=
  AddMonoidHom.mk' (fun x => InductionAlong.Res.mk (op z.1 • x) (capEOrd_cornerFix X z x))
    fun x x' => InductionAlong.Res.ext (smul_add _ x x')

theorem capEOrdCorner_add (z z' : Corner aBl) (x : X) :
    capEOrdCorner X (z + z') x = capEOrdCorner X z x + capEOrdCorner X z' x :=
  InductionAlong.Res.ext (add_smul (op z.1) (op z'.1) x)

theorem capEOrdCorner_op_smul (a : TA) (z : Corner aBl) (x : X) :
    capEOrdCorner X (op a • z) x = op a • capEOrdCorner X z x :=
  InductionAlong.Res.ext (mul_smul (op (aBl a)) (op z.1) x)

theorem capEOrdCorner_smul (a : TAᵢ) (z : Corner aBl) (x : X) :
    capEOrdCorner X (a • z) x = capEOrdCorner X z (op a • x) :=
  InductionAlong.Res.ext (mul_smul (op z.1) (op a) x)

theorem capEOrdCorner_unitGen (m : InductionAlong.Res aOp X) :
    capEOrdCorner X (unitGen aBl) m.val = m :=
  InductionAlong.Res.ext m.prop

/-- `a ⊗ c, x ↦ c ⊗ x a`, from `T^λ_{{i} + ν} e' ⊗_{T^λ_ν} K_ν` and `M`. -/
def capEOrdG : Ind CB aBl →+ (X →+ (OrdK).obj ((blackE Q Λ i ν).obj X)) :=
  Ind.liftAdd (fun z c => AddMonoidHom.mk' (fun x => T₀ c (capEOrdCorner X z x))
      (fun x x' => (congrArg (T₀ c) (map_add (capEOrdCorner X z) x x')).trans
        (DG.TensorProductOver.tmul_add _ _ _)))
    (fun z z' c => AddMonoidHom.ext fun x => (congrArg (T₀ c) (capEOrdCorner_add X z z' x)).trans
      (DG.TensorProductOver.tmul_add _ _ _))
    (fun _ _ _ => AddMonoidHom.ext fun _ => DG.TensorProductOver.add_tmul _ _ _)
    (fun z a c => AddMonoidHom.ext fun x => (congrArg (T₀ c) (capEOrdCorner_op_smul X a z x)).trans
      (DG.TensorProductOver.op_smul_tmul (A := TAᵐᵒᵖ) (M := InDegreeZero (OpBimodule TA CB))
        (N := InDegreeZero ((blackE Q Λ i ν).obj X)) (op a) c (capEOrdCorner X z x)).symm)

theorem capEOrdG_tmul (z : Corner aBl) (c : CB) (x : X) :
    capEOrdG X (Ind.tmul z c) x = T₀ c (capEOrdCorner X z x) :=
  rfl

theorem capEOrdG_smul (a : TAᵢ) (w : Ind CB aBl) (x : X) :
    capEOrdG X (a • w) x = capEOrdG X w (op a • x) := by
  induction w using Ind.induction_on with
  | zero => rw [smul_zero, map_zero, AddMonoidHom.zero_apply, AddMonoidHom.zero_apply]
  | tmul z c =>
    rw [Ind.smul_tmul]
    exact congrArg (T₀ c) (capEOrdCorner_smul X a z x)
  | add w w' hw hw' =>
    rw [smul_add, map_add, map_add, AddMonoidHom.add_apply, AddMonoidHom.add_apply, hw, hw']

/-- `(K_{{i} + ν} ⊗ M) → K_ν ⊗ M e'`, `c ⊗ x ↦ G(proj c, x)`. -/
def capEOrdBwdRaw : (OrdKᵢ).obj X →+ (OrdK).obj ((blackE Q Λ i ν).obj X) :=
  DG.TensorProductOver.lift
    ((capEOrdG X).comp (D.proj.toAddMonoidHom : CBᵢ →+ Ind CB aBl) :
      InDegreeZero (OpBimodule TAᵢ CBᵢ) →+ InDegreeZero X →+ _)
    (fun b c x => (congrArg (fun w => capEOrdG X w x) (D.proj.map_smul (unop b) c)).trans
      (capEOrdG_smul X _ _ _))

theorem capEOrdBwdRaw_tmul (c : CBᵢ) (x : X) :
    capEOrdBwdRaw D X (T₁ c x) = capEOrdG X (D.proj c) x :=
  rfl

theorem capEOrdFwd_G (w : Ind CB aBl) (x : X) :
    InductionAlong.Res.val (capEOrdFwd D X (capEOrdG X w x)) = T₁ (D.equiv w : CBᵢ) x := by
  induction w using Ind.induction_on with
  | zero =>
    simp only [map_zero, AddMonoidHom.zero_apply, ZeroMemClass.coe_zero]
    exact (DG.TensorProductOver.zero_tmul _).symm
  | tmul z c =>
    exact (DG.TensorProductOver.op_smul_tmul (A := TAᵢᵐᵒᵖ)
      (M := InDegreeZero (OpBimodule TAᵢ CBᵢ)) (N := InDegreeZero X) (op z.1)
      (D.iota c) x).symm.trans (congrArg (fun y : CBᵢ => T₁ y x) (D.equiv_tmul z c).symm)
  | add w w' hw hw' =>
    rw [map_add, AddMonoidHom.add_apply, map_add]
    change InductionAlong.Res.val _ + InductionAlong.Res.val _ = _
    rw [hw, hw', map_add, Submodule.coe_add]
    exact (DG.TensorProductOver.add_tmul _ _ _).symm

theorem capEOrdFwd_bwdRaw (s : (OrdKᵢ).obj X) :
    InductionAlong.Res.val (capEOrdFwd D X (capEOrdBwdRaw D X s)) = aT 1 • s :=
  DFunLike.congr_fun (DG.TensorProductOver.addHom_ext
    (f := (AddMonoidHom.mk' (InductionAlong.Res.val (φ := aT) (M := (OrdKᵢ).obj X))
      fun _ _ => rfl).comp ((capEOrdFwd D X).comp (capEOrdBwdRaw D X)))
    (g := AddMonoidHom.mk' (fun s : (OrdKᵢ).obj X => aT 1 • s) (smul_add _)) fun c x =>
      (capEOrdFwd_G D X _ x).trans (congrArg (fun y : CBᵢ => T₁ y x) (D.equiv_proj c))) s

/-- **`(K_{{i} + ν} ⊗ M) e'⁺ → K_ν ⊗ M e'`**, the inverse of `capEOrdFwd`. -/
def capEOrdBwd :
    (resFunctor.{0, 0} aT).obj ((OrdKᵢ).obj X) →+ (OrdK).obj ((blackE Q Λ i ν).obj X) :=
  (capEOrdBwdRaw D X).comp (AddMonoidHom.mk' (InductionAlong.Res.val (φ := aT)) fun _ _ => rfl)

theorem capEOrdBwd_fwd (t : (OrdK).obj ((blackE Q Λ i ν).obj X)) :
    capEOrdBwd D X (capEOrdFwd D X t) = t :=
  DFunLike.congr_fun (DG.TensorProductOver.addHom_ext
    (f := (capEOrdBwd D X).comp (capEOrdFwd D X)) (g := AddMonoidHom.id _) fun c m =>
      (congrArg (fun w => capEOrdG X w (rv m)) (D.proj_iota c)).trans
        (congrArg (T₀ c) (capEOrdCorner_unitGen X m))) t

theorem capEOrdFwd_bwd (t : (resFunctor.{0, 0} aT).obj ((OrdKᵢ).obj X)) :
    capEOrdFwd D X (capEOrdBwd D X t) = t :=
  InductionAlong.Res.ext ((capEOrdFwd_bwdRaw D X _).trans (InductionAlong.Res.prop t))

theorem capEOrdFwd_smul (b : TPpᵐᵒᵖ) (t : (OrdK).obj ((blackE Q Λ i ν).obj X)) :
    capEOrdFwd D X (b • t) = b • capEOrdFwd D X t :=
  DFunLike.congr_fun (DG.TensorProductOver.addHom_ext
    (f := (capEOrdFwd D X).comp
      (AddMonoidHom.mk' (fun s : (OrdK).obj ((blackE Q Λ i ν).obj X) => b • s) (smul_add _)))
    (g := (AddMonoidHom.mk' (fun s : (resFunctor.{0, 0} aT).obj ((OrdKᵢ).obj X) => b • s)
      (smul_add _)).comp (capEOrdFwd D X)) fun c m =>
      InductionAlong.Res.ext (congrArg (fun y : CBᵢ => T₁ y (rv m)) (D.smul_right b c))) t

/-- **`K_ν ⊗_{T^λ_ν} M e' ≅ (K_{{i} + ν} ⊗_{T^λ_{{i} + ν}} M) e'⁺`** as right
`T^{λ⁺}_{ν + ν₀}`-modules, `c ⊗ m ↦ ι(c) ⊗ m`. -/
def capEOrdEquiv :
    (OrdK).obj ((blackE Q Λ i ν).obj X) ≃ₗ[TPpᵐᵒᵖ] (resFunctor.{0, 0} aT).obj ((OrdKᵢ).obj X) where
  toFun := capEOrdFwd D X
  invFun := capEOrdBwd D X
  map_add' := map_add _
  map_smul' := capEOrdFwd_smul D X
  left_inv := capEOrdBwd_fwd D X
  right_inv := capEOrdFwd_bwd D X

/-- **`K ∘ 𝔈_i ≅ 𝔈_i ∘ K` on right modules** (Webster, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the part for `𝔈_i`): `K_ν ⊗ M e' ≅ (K_{{i} + ν} ⊗ M) e'⁺`, `c ⊗ m ↦ ι(c) ⊗ m`,
naturally in the right `T^λ_{{i} + ν}`-module `M`. Both sides are composites of `ordTensor` and
restriction functors, the form taken by `mapDerivedCategoryIsoOfIso`. -/
def capEOrdIso : blackE Q Λ i ν ⋙ OrdK ≅ OrdKᵢ ⋙ resFunctor.{0, 0} aT :=
  NatIso.ofComponents (fun X => (capEOrdEquiv D X).toModuleIso) fun _ =>
    ModuleCat.hom_ext (LinearMap.toAddMonoidHom_injective
      (DG.TensorProductOver.addHom_ext fun _ _ => rfl))

theorem capEOrdIso_hom_tmul (c : CB) (m : InductionAlong.Res aOp X) :
    InductionAlong.Res.val (((capEOrdIso D).hom.app X).hom (T₀ c m)) = T₁ (D.iota c) m.val :=
  rfl

/-! ### The two cases -/

section Cases

variable (ν i) {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}
  [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
  (hR' : MidKLRRel j hj Q Λ Λc ((Singleton.singleton i : Multiset I) + ν) ν₀ L hL)
  (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
  (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i')) (hQ : KLRSymm Q)
  (hfin : ∀ (t : Seq (stendhalWeight 2 ν₀)) (ht : IsRedOrdered t), Module.Finite k
    (BalancedTensor.idemPart k L (op (StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λc) t ht))))

/-- Appending a black strand to `K_ν` for `j < ℓ` (`CupCap.capIota`, `CupCap.capEEquivMid`).
Route hypotheses (tracked): `hfin`, `hQ`, `hκ`, `hP`, `hPL`. -/
def capAppendDataMid (h : j < ℓ) : CapAppendData k Q Λ Λc j hj ν₀ L ν i where
  iota := capIota ν i hR hR' hP hPL hκ h
  smul_left := capIotaK_smul_left ν i _ (capIota_capLeftLin ν i hR hR' hP hPL hκ h)
  smul_right := capIotaK_smul_right ν i _ (capIota_smul ν i hR hR' hP hPL hκ h)
  equiv := capEEquivMid ν i hR hR' hP hPL hκ hQ hfin h
  equiv_tmul := capEEquivMid_apply ν i hR hR' hP hPL hκ hQ hfin h

/-- Appending a black strand to `K_ν` for `j = ℓ` (`CupCap.capTopIota`, `CupCap.capEEquivTop`).
Route hypotheses (tracked): `hfin`, `hQ`, `hκ`, `hP`, `hPL`. -/
def capAppendDataTop (h : ¬ j < ℓ) : CapAppendData k Q Λ Λc j hj ν₀ L ν i where
  iota := capTopIota ν i hR hR' hP hPL hκ h
  smul_left := capIotaK_smul_left ν i _ (capTopIota_capLeftLin ν i hR hR' hP hPL hκ h)
  smul_right := capIotaK_smul_right ν i _ (capTopIota_smul ν i hR hR' hP hPL hκ h)
  equiv := capEEquivTop ν i hR hR' hP hPL hκ hQ hfin h
  equiv_tmul := capEEquivTop_apply ν i hR hR' hP hPL hκ hQ hfin h

/-- **`K ∘ 𝔈_i ≅ 𝔈_i ∘ K` on right modules for `j < ℓ`** (Webster, arXiv:1309.3796v3, §7.3,
proof of Proposition 7.21). Route hypotheses (tracked): `hfin`, `hQ`, `hκ`, `hP`, `hPL`. -/
def capEOrdIsoMid (h : j < ℓ) : blackE Q Λ i ν ⋙ OrdK ≅ OrdKᵢ ⋙ resFunctor.{0, 0} aT :=
  capEOrdIso (capAppendDataMid ν i hR hR' hP hPL hκ hQ hfin h)

/-- **`K ∘ 𝔈_i ≅ 𝔈_i ∘ K` on right modules for `j = ℓ`** (Webster, arXiv:1309.3796v3, §7.3,
proof of Proposition 7.21). Route hypotheses (tracked): `hfin`, `hQ`, `hκ`, `hP`, `hPL`. -/
def capEOrdIsoTop (h : ¬ j < ℓ) : blackE Q Λ i ν ⋙ OrdK ≅ OrdKᵢ ⋙ resFunctor.{0, 0} aT :=
  capEOrdIso (capAppendDataTop ν i hR hR' hP hPL hκ hQ hfin h)

end Cases

end Categorification.Stendhal.CupCap

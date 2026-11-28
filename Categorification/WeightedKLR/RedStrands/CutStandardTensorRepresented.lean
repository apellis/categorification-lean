/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.CutSpectTensorRepresented

/-!
# Functors presented by a partial standardization at a cut are tensoring with a bimodule

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1. Let
`ι : D → R` be a map of `k`-algebras from the factor algebra `D` of a cut, and let
`F : R-mod → A-mod` be a functor whose value on `Z`, as an additive group, is identified with
the partial standardization at the cut of `Z` restricted to `D`, compatibly with maps and with
the scalars of `k` (`CutStandardPresented`). Then `F` is tensoring with its value on the
regular module (`CutStandardPresented.isTensorRepresented`). The argument is the one of
`isTensorRepresented_cutSpectFunctor`: the inverse of the Eilenberg–Watts map sends the class
of `m ⊗ n` to `[m ⊗ 1] ⊗ n`. The partial standardizations of `λ⁺` with three blocks are
presented in this way, one cut at a time.

## Main definitions

* `Stendhal.CutRestr`: an `R`-module restricted to `D` along `ι`.
* `Stendhal.CutStandardPresented`: the identification of `F` with a partial standardization.

## Main results

* `Stendhal.CutStandardPresented.isTensorRepresented`.
-/

universe u

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory DG KLR KLRAlgebra TypeA MulOpposite TensorRepresented
open scoped TensorProduct

variable {I k : Type u} [DecidableEq I] [CommRing k] {a r : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (a + r) → I →₀ ℕ) (θ β : Multiset I)
  {R : Type u} [Ring R] [Algebra k R] (ι : cutFactorAlgebra Q Λ θ β →ₐ[k] R)

/-- An `R`-module, as a module over the factor algebra `D` of the cut along `ι`. -/
@[nolint unusedArguments]
def CutRestr (_ι : cutFactorAlgebra Q Λ θ β →ₐ[k] R) (Z : Type u) : Type u := Z

/-- A map of `k`-algebras out of the factor algebra of the cut, with the instances of
`CutRestr`. -/
def cutAlgHom (f : cutFactorAlgebra Q Λ θ β →ₐ[k] R) : cutFactorAlgebra Q Λ θ β →ₐ[k] R := f

section Restr

variable (Z : Type u) [AddCommGroup Z] [Module k Z] [Module R Z] [IsScalarTower k R Z]

instance : AddCommGroup (CutRestr Q Λ θ β ι Z) := inferInstanceAs (AddCommGroup Z)
instance : Module k (CutRestr Q Λ θ β ι Z) := inferInstanceAs (Module k Z)
instance : Module (cutFactorAlgebra Q Λ θ β) (CutRestr Q Λ θ β ι Z) :=
  Module.compHom Z ι.toRingHom

instance : IsScalarTower k (cutFactorAlgebra Q Λ θ β) (CutRestr Q Λ θ β ι Z) where
  smul_assoc c d n := by
    change ι (c • d) • (show Z from n) = c • ι d • (show Z from n)
    rw [map_smul, smul_assoc]

variable {Z} {Y : Type u} [AddCommGroup Y] [Module k Y] [Module R Y] [IsScalarTower k R Y]

/-- A map of `R`-modules, as a map of their restrictions to `D`. -/
def cutRestrHom (g : Z →ₗ[R] Y) : CutRestr Q Λ θ β ι Z →ₗ[cutFactorAlgebra Q Λ θ β]
    CutRestr Q Λ θ β ι Y where
  toFun n := (g n : Y)
  map_add' := g.map_add
  map_smul' d n := g.map_smul (ι d) n

end Restr

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

variable {A : Type u} [Ring A] [Algebra k A]

/-- **A functor presented by the partial standardization at a cut**: the value of `F` on `Z`
is identified, as an additive group, with the partial standardization of `Z` restricted to
`D`, compatibly with maps and with the scalars of `k`. -/
structure CutStandardPresented (F : ModuleCat.{u} R ⥤ ModuleCat.{u} A) where
  /-- The identification of `F(Z)` with the partial standardization. -/
  equiv : ∀ Z : ModuleCat.{u} R, F.obj Z ≃+ CutStandard Q Λ θ β (CutRestr Q Λ θ β ι Z)
  map : ∀ {Z Y : ModuleCat.{u} R} (g : Z ⟶ Y) (x : F.obj Z),
    equiv Y ((F.map g).hom x) = cutStandardMap Q Λ θ β (cutRestrHom Q Λ θ β ι g.hom) (equiv Z x)
  smul : ∀ (Z : ModuleCat.{u} R) (c : k) (x : F.obj Z),
    equiv Z (algebraMap k A c • x) = c • equiv Z x

namespace CutStandardPresented

variable {Q Λ θ β ι} {F : ModuleCat.{u} R ⥤ ModuleCat.{u} A}
  (H : CutStandardPresented Q Λ θ β ι F)

local notation "S" => stendhalQ Q Λ
local notation "α" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd r)) (stendhalWeight a θ)
local notation "δ" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd a)) (stendhalWeight r β)
local notation "P" => (eSum S (cutOrderedLoadings (a := a) (r := r) θ β) : KLRAlgebra k S (α + δ))

variable (R) in
/-- The regular module of `R`, as an object whose `k`-structure is the one of a module over a
`k`-algebra. -/
def regular : ModuleCat.{u} R := regularModule R

local notation "X" => regular R

/-- The map `x ↦ x z` out of the regular module. -/
def rmulReg (Z : ModuleCat.{u} R) (z : Z) : X ⟶ Z := rmul Z z

/-- An element of `R`, as an element of the input of the induction. -/
def elt (x : R) : CutInput Q Λ θ β (CutRestr Q Λ θ β ι X) := x

/-- The class in `F(R)` of an element of the induced module. -/
def cls (y : CutShuffle Q Λ θ β (CutRestr Q Λ θ β ι X)) : Bimod F :=
  (H.equiv X).symm (Submodule.Quotient.mk y)

/-- The generator `[m ⊗ 1]` of `F(R)`. -/
def gen (m : IndBimod S α δ) : Bimod F := H.cls (BalancedTensor.tmul m (elt (ι := ι) 1))

theorem equiv_cls (y : CutShuffle Q Λ θ β (CutRestr Q Λ θ β ι X)) :
    H.equiv X (H.cls y) = Submodule.Quotient.mk y :=
  (H.equiv X).apply_symm_apply _

theorem cls_add (y y' : CutShuffle Q Λ θ β (CutRestr Q Λ θ β ι X)) :
    H.cls (y + y') = H.cls y + H.cls y' := by
  rw [cls, cls, cls, Submodule.Quotient.mk_add, map_add]; rfl

theorem cls_zero : H.cls 0 = 0 := by
  rw [cls, Submodule.Quotient.mk_zero, map_zero]; rfl

theorem cls_smul (c : k) (y : CutShuffle Q Λ θ β (CutRestr Q Λ θ β ι X)) :
    H.cls (c • y) = algebraMap k A c • H.cls y := by
  refine (H.equiv X).injective ((H.equiv_cls _).trans (Eq.trans ?_ (H.smul X c (H.cls y)).symm))
  rw [equiv_cls, Submodule.Quotient.mk_smul]

theorem cls_eSum (y : CutShuffle Q Λ θ β (CutRestr Q Λ θ β ι X)) : H.cls (P • y) = H.cls y :=
  congrArg (H.equiv X).symm (cutStandard_mk_eSum_smul Q Λ θ β _ y)

theorem gen_add (m m' : IndBimod S α δ) : H.gen (m + m') = H.gen m + H.gen m' := by
  rw [gen, BalancedTensor.add_tmul, cls_add]; rfl

theorem gen_smul (c : k) (m : IndBimod S α δ) : H.gen (c • m) = algebraMap k A c • H.gen m := by
  rw [gen, BalancedTensor.smul_tmul, cls_smul]; rfl

theorem gen_eSum (m : IndBimod S α δ) : H.gen (P • m) = H.gen m := by
  rw [gen, ← BalancedTensor.smul_tmul', cls_eSum]; rfl

theorem gen_op_smul (m : IndBimod S α δ) (x : R) :
    op x • H.gen m = H.cls (BalancedTensor.tmul m (elt (ι := ι) x)) := by
  refine (H.equiv X).injective ((H.map (rmulReg X (show X from x)) (H.gen m)).trans ?_)
  refine (congrArg (cutStandardMap Q Λ θ β _) (H.equiv_cls _)).trans
    (Eq.trans ?_ (H.equiv_cls _).symm)
  exact congrArg (fun y => Submodule.Quotient.mk (BalancedTensor.tmul m (elt (ι := ι) y)))
    (one_mul x)

theorem gen_op_algebraMap (c : k) (m : IndBimod S α δ) :
    op (algebraMap k R c) • H.gen m = algebraMap k A c • H.gen m := by
  rw [gen_op_smul, ← gen_smul, gen, BalancedTensor.smul_tmul, ← BalancedTensor.tmul_smul]
  exact congrArg (fun y => H.cls (BalancedTensor.tmul m (elt (ι := ι) y))) (mul_one _).symm

theorem gen_balanced (m : IndBimod S α δ) (b : TensorKLR S α δ) :
    H.gen (op b • m) = op (ι (cutInputMap Q Λ θ β b)) • H.gen m := by
  rw [gen, BalancedTensor.op_smul_tmul, gen_op_smul]
  exact congrArg (fun y => H.cls (BalancedTensor.tmul m (elt (ι := ι) y))) (mul_one _)

/-! ### The inverse of the Eilenberg–Watts map -/

variable [F.Additive]

variable (Z : ModuleCat.{u} R)

/-- The `k`-structure of `F(R) ⊗_R Z`, through the left action of `A`. -/
abbrev tensorScalars : Module k (TensorProductOver R (Bimod F) Z) :=
  Module.compHom _ (algebraMap k A)

attribute [local instance] tensorScalars

/-- The bilinear map `(m, n) ↦ [m ⊗ 1] ⊗ n`. -/
def invBil : IndBimod S α δ →ₗ[k] CutInput Q Λ θ β (CutRestr Q Λ θ β ι Z) →ₗ[k]
    TensorProductOver R (Bimod F) Z :=
  LinearMap.mk₂ k (fun m n => TensorProductOver.tmul R (H.gen m) (show Z from n))
    (fun m m' n => by rw [gen_add, TensorProductOver.add_tmul])
    (fun c m n => by rw [gen_smul]; rfl)
    (fun m n n' => TensorProductOver.tmul_add (A := R) _ (show Z from n) (show Z from n'))
    (fun c m n => by
      change TensorProductOver.tmul R _ (algebraMap k R c • (show Z from n)) = _
      rw [← TensorProductOver.op_smul_tmul, gen_op_algebraMap]; rfl)

theorem invBil_balanced (m : IndBimod S α δ) (b : TensorKLR S α δ)
    (n : CutInput Q Λ θ β (CutRestr Q Λ θ β ι Z)) :
    H.invBil Z (op b • m) n = H.invBil Z m (b • n) := by
  change TensorProductOver.tmul R (H.gen (op b • m)) (show Z from n) =
    TensorProductOver.tmul R (H.gen m) (ι (cutInputMap Q Λ θ β b) • (show Z from n))
  rw [gen_balanced, TensorProductOver.op_smul_tmul]

/-- The inverse of the Eilenberg–Watts map on the induced module: `m ⊗ n ↦ [m ⊗ 1] ⊗ n`. -/
def inv : CutShuffle Q Λ θ β (CutRestr Q Λ θ β ι Z) →ₗ[k] TensorProductOver R (Bimod F) Z :=
  BalancedTensor.lift (H.invBil Z) (H.invBil_balanced Z)

theorem inv_eSum (y : CutShuffle Q Λ θ β (CutRestr Q Λ θ β ι Z)) :
    H.inv Z (P • y) = H.inv Z y := by
  induction y using BalancedTensor.induction_on with
  | zero => rw [smul_zero]
  | tmul m n =>
    rw [BalancedTensor.smul_tmul']
    change TensorProductOver.tmul R (H.gen (P • m)) (show Z from n) = _
    rw [gen_eSum]; rfl
  | add y y' hy hy' => rw [smul_add, map_add, map_add, hy, hy']

theorem equiv_ewMap_inv (y : CutShuffle Q Λ θ β (CutRestr Q Λ θ β ι Z)) :
    H.equiv Z (ewMap F Z (H.inv Z y)) = Submodule.Quotient.mk y := by
  induction y using BalancedTensor.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]; exact (Submodule.Quotient.mk_zero _).symm
  | tmul m n =>
    refine (H.map (rmulReg Z (show Z from n)) (H.gen m)).trans
      ((congrArg (cutStandardMap Q Λ θ β _) (H.equiv_cls _)).trans ?_)
    exact congrArg (fun x : Z => Submodule.Quotient.mk (BalancedTensor.tmul m
      (show CutInput Q Λ θ β (CutRestr Q Λ θ β ι Z) from x))) (one_smul R (show Z from n))
  | add y y' hy hy' =>
    rw [map_add, map_add, map_add, hy, hy']
    exact (Submodule.Quotient.mk_add _).symm

/-- Every tensor has a representative in the induced module on which the inverse map takes the
value of the tensor. -/
theorem exists_rep (t : TensorProductOver R (Bimod F) Z) :
    ∃ y, Submodule.Quotient.mk y = H.equiv Z (ewMap F Z t) ∧ H.inv Z y = t := by
  induction t using TensorProductOver.induction_on with
  | zero => exact ⟨0, by rw [map_zero, map_zero]; exact Submodule.Quotient.mk_zero _,
      map_zero _⟩
  | tmul p z =>
    obtain ⟨y₁, hy₁⟩ := Submodule.Quotient.mk_surjective _ (H.equiv X p)
    have hp : H.cls y₁ = p := by
      rw [cls, hy₁]; exact (H.equiv X).symm_apply_apply p
    subst hp
    clear hy₁
    refine ⟨cutShuffleMap Q Λ θ β (cutRestrHom Q Λ θ β ι (rmulReg Z z).hom) y₁, ?_, ?_⟩
    · exact ((H.map (rmulReg Z z) (H.cls y₁)).trans
        (congrArg (cutStandardMap Q Λ θ β _) (H.equiv_cls y₁))).symm
    induction y₁ using BalancedTensor.induction_on with
    | zero =>
      rw [map_zero, map_zero, cls_zero]
      exact (TensorProductOver.zero_tmul (A := R) (M := Bimod F) z).symm
    | tmul m d =>
      change TensorProductOver.tmul R (H.gen m) ((show R from d) • z) =
        TensorProductOver.tmul R (H.cls (BalancedTensor.tmul m (elt (ι := ι) d))) z
      rw [← TensorProductOver.op_smul_tmul, gen_op_smul]
    | add y y' hy hy' =>
      rw [map_add, map_add, hy, hy', cls_add]
      exact (TensorProductOver.add_tmul (A := R) _ _ z).symm
  | add t t' ht ht' =>
    obtain ⟨y, hy, hy'⟩ := ht
    obtain ⟨y', hz, hz'⟩ := ht'
    exact ⟨y + y', by rw [Submodule.Quotient.mk_add, hy, hz, map_add, map_add],
      by rw [map_add, hy', hz']⟩

include H in
/-- **A functor presented by the partial standardization at a cut is tensoring with a
bimodule**, its value on the regular module. -/
theorem isTensorRepresented : IsTensorRepresented F := by
  intro Z
  refine ⟨fun t t' h => ?_, fun v => ?_⟩
  · obtain ⟨y, hy, rfl⟩ := H.exists_rep Z t
    obtain ⟨y', hy', rfl⟩ := H.exists_rep Z t'
    have hyy : P • (y - y') = 0 := (Submodule.Quotient.eq _).1 (hy.trans
      ((congrArg (H.equiv Z) h).trans hy'.symm))
    rw [← sub_eq_zero, ← map_sub, ← inv_eSum, hyy, map_zero]
  · obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (H.equiv Z v)
    refine ⟨H.inv Z y, (H.equiv Z).injective ?_⟩
    rw [equiv_ewMap_inv, hy]

end CutStandardPresented

end Categorification.Stendhal

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.TensorMate

/-!
# Bijectivity of a mate from its Hom form

In the setting of `TensorMate.mate`, let `S₊` also be finitely generated projective as a right
`R₃`-module. For a left `R₃`-module `X`, the Hom form of the mate is

`Θ_X : S ⊗_{R₀} Hom_{R₃}(K_b, X) → Hom_{R₂}(K, S₊ ⊗_{R₃} X)`,
`s ⊗ g ↦ (r ↦ (id ⊗ g)(κ (r ⊗ s)))`.

Under `Hom_{R₃}(S₊^∨ ⊗_{R₂} K, X) = Hom_{R₂}(K, S₊ ⊗_{R₃} X)` and
`Hom_{R₃}(K_b ⊗_{R₀} S^∨, X) = S ⊗_{R₀} Hom_{R₃}(K_b, X)`, precomposition with the mate `Φ` is
`Θ_X` (`TensorMate.homOfTensor_mateTheta_tensorOfHom`). So, by the Yoneda argument, `Φ` is bijective
once `Θ_X` is surjective at `X = S₊^∨ ⊗_{R₂} K` and injective at `X = K_b ⊗_{R₀} S^∨`
(`TensorMate.mate_bijective_of_mateTheta`).

This is the form in which the comparison of the trace half of B. Webster, *Knot invariants and
higher representation theory*, arXiv:1309.3796v3, Lemma 7.19, is checked: `Θ_X` is computed
through left exact functors, so only `Hom` out of the coevaluation bimodule enters.

## Main definitions

* `TensorMate.KbHom`: `Hom_{R₃}(K_b, X)` as a left `R₀`-module, `(c g)(x) = g(x c)`.
* `TensorMate.mateTheta`: the Hom form `Θ_X` of the mate.

## Main results

* `TensorMate.mate_bijective_of_mateTheta`.
-/

noncomputable section

namespace Categorification

namespace TensorMate

open DG MulOpposite
open scoped DG.TensorProductOver.RightAction

universe u

variable {R₀ R₁ R₂ R₃ : Type u} [Ring R₀] [Ring R₁] [Ring R₂] [Ring R₃]
  {K : Type u} [AddCommGroup K] [Module R₂ K] [Module R₁ᵐᵒᵖ K] [SMulCommClass R₂ R₁ᵐᵒᵖ K]
  {Kb : Type u} [AddCommGroup Kb] [Module R₃ Kb] [Module R₀ᵐᵒᵖ Kb] [SMulCommClass R₃ R₀ᵐᵒᵖ Kb]
  {S : Type u} [AddCommGroup S] [Module R₁ S] [Module R₀ᵐᵒᵖ S]
  {Sp : Type u} [AddCommGroup Sp] [Module R₂ Sp] [Module R₃ᵐᵒᵖ Sp] [SMulCommClass R₂ R₃ᵐᵒᵖ Sp]

section KbHom

variable (R₀ Kb) (X : Type u) [AddCommGroup X] [Module R₃ X]

/-- `Hom_{R₃}(K_b, X)`, a left `R₀`-module through the right action on `K_b`. -/
def KbHom (_R₀ R₃ : Type u) [Ring R₃] (Kb : Type u) [AddCommGroup Kb] [Module R₃ Kb]
    (X : Type u) [AddCommGroup X] [Module R₃ X] : Type u :=
  Kb →ₗ[R₃] X

instance : AddCommGroup (KbHom R₀ R₃ Kb X) := inferInstanceAs (AddCommGroup (Kb →ₗ[R₃] X))

instance : FunLike (KbHom R₀ R₃ Kb X) Kb X := inferInstanceAs (FunLike (Kb →ₗ[R₃] X) Kb X)

instance : LinearMapClass (KbHom R₀ R₃ Kb X) R₃ Kb X :=
  inferInstanceAs (LinearMapClass (Kb →ₗ[R₃] X) R₃ Kb X)

variable {R₀ Kb X}

/-- An `R₃`-linear map `K_b → X` as an element of `KbHom`. -/
def KbHom.of (g : Kb →ₗ[R₃] X) : KbHom R₀ R₃ Kb X := g

/-- The underlying `R₃`-linear map. -/
def KbHom.toLin (g : KbHom R₀ R₃ Kb X) : Kb →ₗ[R₃] X := g

omit [Ring R₀] [Module R₀ᵐᵒᵖ Kb] [SMulCommClass R₃ R₀ᵐᵒᵖ Kb] in
@[simp] theorem KbHom.of_apply (g : Kb →ₗ[R₃] X) (x : Kb) :
    KbHom.of (R₀ := R₀) (X := X) g x = g x := rfl

omit [Ring R₀] [Module R₀ᵐᵒᵖ Kb] [SMulCommClass R₃ R₀ᵐᵒᵖ Kb] in
@[simp] theorem KbHom.toLin_apply (g : KbHom R₀ R₃ Kb X) (x : Kb) : g.toLin x = g x := rfl

omit [Ring R₀] [Module R₀ᵐᵒᵖ Kb] [SMulCommClass R₃ R₀ᵐᵒᵖ Kb] in
@[ext] theorem KbHom.ext {g g' : KbHom R₀ R₃ Kb X} (h : ∀ x, g x = g' x) : g = g' :=
  LinearMap.ext h

omit [Ring R₀] [Module R₀ᵐᵒᵖ Kb] [SMulCommClass R₃ R₀ᵐᵒᵖ Kb] in
@[simp] theorem KbHom.add_apply (g g' : KbHom R₀ R₃ Kb X) (x : Kb) : (g + g') x = g x + g' x := rfl

omit [Ring R₀] [Module R₀ᵐᵒᵖ Kb] [SMulCommClass R₃ R₀ᵐᵒᵖ Kb] in
@[simp] theorem KbHom.zero_apply (x : Kb) : (0 : KbHom R₀ R₃ Kb X) x = 0 := rfl

instance : SMul R₀ (KbHom R₀ R₃ Kb X) where
  smul c g := KbHom.of
    { toFun := fun x => g (op c • x)
      map_add' := fun x x' => by rw [smul_add, map_add]
      map_smul' := fun a x => by rw [← smul_comm a (op c) x, map_smul]; rfl }

@[simp] theorem KbHom.smul_apply (c : R₀) (g : KbHom R₀ R₃ Kb X) (x : Kb) :
    (c • g) x = g (op c • x) := rfl

instance : Module R₀ (KbHom R₀ R₃ Kb X) where
  one_smul g := KbHom.ext fun x => by rw [KbHom.smul_apply, op_one, one_smul]
  mul_smul c c' g := KbHom.ext fun x => by
    rw [KbHom.smul_apply, KbHom.smul_apply, KbHom.smul_apply, op_mul, mul_smul]
  smul_zero c := KbHom.ext fun x => rfl
  smul_add c g g' := KbHom.ext fun x => rfl
  add_smul c c' g := KbHom.ext fun x => by
    rw [KbHom.smul_apply, KbHom.add_apply, KbHom.smul_apply, KbHom.smul_apply, op_add, add_smul,
      map_add]
  zero_smul g := KbHom.ext fun x => by
    rw [KbHom.smul_apply, op_zero, zero_smul, map_zero, KbHom.zero_apply]

end KbHom

section Post

variable {X : Type u} [AddCommGroup X] [Module R₃ X]

variable (Sp) in
/-- `id ⊗ g : S₊ ⊗_{R₃} K_b → S₊ ⊗_{R₃} X`. -/
def postMap (g : Kb →ₗ[R₃] X) : TensorProductOver R₃ Sp Kb →+ TensorProductOver R₃ Sp X :=
  TensorProductOver.map LinearMap.id g

theorem postMap_tmul (g : Kb →ₗ[R₃] X) (p : Sp) (x : Kb) :
    postMap Sp g (TensorProductOver.tmul R₃ p x) = TensorProductOver.tmul R₃ p (g x) := rfl

theorem postMap_smul (g : Kb →ₗ[R₃] X) (t : R₂) (q : TensorProductOver R₃ Sp Kb) :
    postMap Sp g (t • q) = t • postMap Sp g q := by
  induction q using TensorProductOver.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul p x => rfl
  | add q q' hq hq' => rw [smul_add, map_add, map_add, hq, hq', smul_add]

omit [SMulCommClass R₃ R₀ᵐᵒᵖ Kb] in
theorem dualEv_postMap (f : RightDualModule R₃ Sp) (g : Kb →ₗ[R₃] X)
    (q : TensorProductOver R₃ Sp Kb) : dualEv X f (postMap Sp g q) = g (dualEv Kb f q) := by
  induction q using TensorProductOver.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul p x => rw [postMap_tmul, dualEv_tmul, dualEv_tmul, map_smul]
  | add q q' hq hq' => rw [map_add, map_add, hq, hq', map_add, map_add]

end Post

variable [Module.Projective R₀ᵐᵒᵖ S] [Module.Finite R₀ᵐᵒᵖ S]
  [Module.Projective R₃ᵐᵒᵖ Sp] [Module.Finite R₃ᵐᵒᵖ Sp]

local notation "e" => RightDualModule.dualBasisVec R₀ S
local notation "φ" => RightDualModule.dualBasisCoord R₀ S
local notation "e'" => RightDualModule.dualBasisVec R₃ Sp
local notation "φ'" => RightDualModule.dualBasisCoord R₃ Sp

variable [SMulCommClass R₁ R₀ᵐᵒᵖ S] (R₀)
  (κ : TensorProductOver R₁ K S →+ TensorProductOver R₃ Sp Kb)
  (hκ : ∀ (t : R₂) (x : TensorProductOver R₁ K S), κ (t • x) = t • κ x)
  (hκr : ∀ (c : R₀ᵐᵒᵖ) (x : TensorProductOver R₁ K S), κ (c • x) = c • κ x)

local notation "P" => TensorProductOver R₂ (RightDualModule R₃ Sp) K
local notation "Q" => TensorProductOver R₀ Kb (RightDualModule R₀ S)

section Theta

variable (X : Type u) [AddCommGroup X] [Module R₃ X]

/-- `r ↦ (id ⊗ g)(κ (r ⊗ s))`, as a map of left `R₂`-modules. -/
def thetaGen (s : S) (g : KbHom R₀ R₃ Kb X) : K →ₗ[R₂] TensorProductOver R₃ Sp X where
  toFun r := postMap Sp g.toLin (κ (TensorProductOver.tmul R₁ r s))
  map_add' r r' := by rw [TensorProductOver.add_tmul, map_add, map_add]
  map_smul' t r := by
    rw [RingHom.id_apply, ← postMap_smul, ← hκ]
    rfl

omit [Ring R₀] [Module R₀ᵐᵒᵖ Kb] [SMulCommClass R₃ R₀ᵐᵒᵖ Kb] [Module R₀ᵐᵒᵖ S]
  [Module.Projective R₀ᵐᵒᵖ S] [Module.Finite R₀ᵐᵒᵖ S] [Module.Projective R₃ᵐᵒᵖ Sp]
  [Module.Finite R₃ᵐᵒᵖ Sp] [SMulCommClass R₁ R₀ᵐᵒᵖ S] in
theorem thetaGen_apply (s : S) (g : KbHom R₀ R₃ Kb X) (r : K) :
    thetaGen R₀ κ hκ X s g r = postMap Sp g.toLin (κ (TensorProductOver.tmul R₁ r s)) := rfl

/-- The bi-additive map `(s, g) ↦ thetaGen s g`. -/
def thetaBil : S →+ KbHom R₀ R₃ Kb X →+ (K →ₗ[R₂] TensorProductOver R₃ Sp X) :=
  AddMonoidHom.mk' (fun s => AddMonoidHom.mk' (thetaGen R₀ κ hκ X s) fun g g' =>
      LinearMap.ext fun r => by
        simp only [thetaGen_apply, LinearMap.add_apply]
        induction κ (TensorProductOver.tmul R₁ r s) using TensorProductOver.induction_on with
        | zero => simp only [map_zero, add_zero]
        | tmul p x => rw [postMap_tmul, postMap_tmul, postMap_tmul]; exact
            TensorProductOver.tmul_add p _ _
        | add q q' hq hq' => rw [map_add, map_add, map_add, hq, hq']; abel)
    fun s s' => AddMonoidHom.ext fun g => LinearMap.ext fun r => by
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, LinearMap.add_apply,
        thetaGen_apply, TensorProductOver.tmul_add, map_add]

omit [Module.Projective R₀ᵐᵒᵖ S] [Module.Finite R₀ᵐᵒᵖ S] [Module.Projective R₃ᵐᵒᵖ Sp]
  [Module.Finite R₃ᵐᵒᵖ Sp] in
include hκr in
theorem thetaBil_balanced (c : R₀) (s : S) (g : KbHom R₀ R₃ Kb X) :
    thetaBil R₀ κ hκ X (op c • s) g = thetaBil R₀ κ hκ X s (c • g) := by
  refine LinearMap.ext fun r => ?_
  change postMap Sp g.toLin (κ (TensorProductOver.tmul R₁ r (op c • s))) =
    postMap Sp (c • g).toLin (κ (TensorProductOver.tmul R₁ r s))
  rw [show TensorProductOver.tmul R₁ r (op c • s) =
    (op c • TensorProductOver.tmul R₁ r s : TensorProductOver R₁ K S) from rfl, hκr]
  induction κ (TensorProductOver.tmul R₁ r s) using TensorProductOver.induction_on with
  | zero => rw [smul_zero, map_zero, map_zero]
  | tmul p x => rfl
  | add q q' hq hq' =>
    rw [smul_add, map_add, map_add, hq, hq']

/-- **The Hom form `Θ_X` of the mate**: `s ⊗ g ↦ (r ↦ (id ⊗ g)(κ (r ⊗ s)))`. -/
def mateTheta : TensorProductOver R₀ S (KbHom R₀ R₃ Kb X) →+ (K →ₗ[R₂] TensorProductOver R₃ Sp X) :=
  TensorProductOver.lift (thetaBil R₀ κ hκ X) (thetaBil_balanced R₀ κ hκ hκr X)

omit [Module.Projective R₀ᵐᵒᵖ S] [Module.Finite R₀ᵐᵒᵖ S] [Module.Projective R₃ᵐᵒᵖ Sp]
  [Module.Finite R₃ᵐᵒᵖ Sp] in
theorem mateTheta_tmul (s : S) (g : KbHom R₀ R₃ Kb X) :
    mateTheta R₀ κ hκ hκr X (TensorProductOver.tmul R₀ s g) = thetaGen R₀ κ hκ X s g := rfl

end Theta

section Yoneda

variable {R₀} {X : Type u} [AddCommGroup X] [Module R₃ X]

omit [SMulCommClass R₃ R₀ᵐᵒᵖ Kb] [Module.Projective R₀ᵐᵒᵖ S] [Module.Finite R₀ᵐᵒᵖ S]
  [SMulCommClass R₁ R₀ᵐᵒᵖ S] in
/-- `Hom_{R₂}(K, S₊ ⊗_{R₃} X) → Hom_{R₃}(S₊^∨ ⊗_{R₂} K, X)`, `u ↦ (f ⊗ r ↦ ev_f (u r))`. -/
def homOfTensor (u : K →ₗ[R₂] TensorProductOver R₃ Sp X) : P →+ X :=
  TensorProductOver.lift
    (AddMonoidHom.mk' (fun f => (dualEv X f).comp u.toAddMonoidHom) fun f f' =>
      AddMonoidHom.ext fun r => dualEv_add f f' (u r))
    fun t f r => by
      change dualEv X (op t • f) (u r) = dualEv X f (u (t • r))
      rw [dualEv_op_smul, u.map_smul]

omit [SMulCommClass R₃ R₀ᵐᵒᵖ Kb] [Module.Projective R₀ᵐᵒᵖ S] [Module.Finite R₀ᵐᵒᵖ S]
  [SMulCommClass R₁ R₀ᵐᵒᵖ S] in
omit [Module.Projective R₃ᵐᵒᵖ Sp] [Module.Finite R₃ᵐᵒᵖ Sp] in
theorem homOfTensor_tmul (u : K →ₗ[R₂] TensorProductOver R₃ Sp X) (f : RightDualModule R₃ Sp)
    (r : K) : homOfTensor u (TensorProductOver.tmul R₂ f r) = dualEv X f (u r) := rfl

omit [SMulCommClass R₃ R₀ᵐᵒᵖ Kb] [Module.Projective R₀ᵐᵒᵖ S] [Module.Finite R₀ᵐᵒᵖ S]
  [SMulCommClass R₁ R₀ᵐᵒᵖ S] in
/-- `u` is recovered from `homOfTensor u`: `u r = Σ_j e'_j ⊗ (homOfTensor u)(φ'_j ⊗ r)`. -/
theorem sum_tmul_homOfTensor (u : K →ₗ[R₂] TensorProductOver R₃ Sp X) (r : K) :
    ∑ j, TensorProductOver.tmul R₃ (e' j) (homOfTensor u (TensorProductOver.tmul R₂ (φ' j) r)) =
      u r := by
  simp only [homOfTensor_tmul]
  induction u r using TensorProductOver.induction_on with
  | zero => simp only [map_zero, TensorProductOver.tmul_zero, Finset.sum_const_zero]
  | tmul p x =>
    simp only [dualEv_tmul]
    conv_rhs => rw [← RightDualModule.sum_dualBasis R₃ Sp p, sum_tmul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← TensorProductOver.op_smul_tmul, op_unop]
  | add q q' hq hq' =>
    simp only [map_add, TensorProductOver.tmul_add, Finset.sum_add_distrib, hq, hq']

omit [SMulCommClass R₃ R₀ᵐᵒᵖ Kb] [Module.Projective R₀ᵐᵒᵖ S] [Module.Finite R₀ᵐᵒᵖ S]
  [SMulCommClass R₁ R₀ᵐᵒᵖ S] in
theorem homOfTensor_injective {u u' : K →ₗ[R₂] TensorProductOver R₃ Sp X}
    (h : homOfTensor u = homOfTensor u') : u = u' :=
  LinearMap.ext fun r => by rw [← sum_tmul_homOfTensor, h, sum_tmul_homOfTensor]

omit [SMulCommClass R₃ R₀ᵐᵒᵖ Kb] [Module.Projective R₀ᵐᵒᵖ S] [Module.Finite R₀ᵐᵒᵖ S]
  [SMulCommClass R₁ R₀ᵐᵒᵖ S] in
/-- The element of `Hom_{R₂}(K, S₊ ⊗_{R₃} P)` corresponding to the identity of `P`. -/
def unitTensor : K →ₗ[R₂] TensorProductOver R₃ Sp P where
  toFun r := ∑ j, TensorProductOver.tmul R₃ (e' j) (TensorProductOver.tmul R₂ (φ' j) r)
  map_add' r r' := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TensorProductOver.tmul_add, TensorProductOver.tmul_add]
  map_smul' t r := by
    rw [RingHom.id_apply, Finset.smul_sum]
    have h1 : ∀ j, t • TensorProductOver.tmul R₃ (e' j) (TensorProductOver.tmul R₂ (φ' j) r) =
        ∑ i, TensorProductOver.tmul R₃ (e' i)
          (TensorProductOver.tmul R₂ (unop (φ' i (t • e' j)) • φ' j) r) := fun j => by
      rw [TensorProductOver.smul_tmul]
      conv_lhs => rw [← RightDualModule.sum_dualBasis R₃ Sp (t • e' j), sum_tmul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← op_unop (φ' i (t • e' j)), TensorProductOver.op_smul_tmul, unop_op,
        TensorProductOver.smul_tmul]
    simp only [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← tmul_sum, ← sum_tmul, ← TensorProductOver.op_smul_tmul]
    exact (congrArg (fun ψ => TensorProductOver.tmul R₃ (e' i) (TensorProductOver.tmul R₂ ψ r))
      (RightDualModule.sum_dualBasis_dual R₃ Sp (op t • φ' i))).symm

omit [SMulCommClass R₃ R₀ᵐᵒᵖ Kb] [Module.Projective R₀ᵐᵒᵖ S] [Module.Finite R₀ᵐᵒᵖ S]
  [SMulCommClass R₁ R₀ᵐᵒᵖ S] in
theorem homOfTensor_unitTensor (y : P) :
    homOfTensor (unitTensor (K := K) (Sp := Sp)) y = y := by
  induction y using TensorProductOver.induction_on with
  | zero => rw [map_zero]
  | tmul f r =>
    rw [homOfTensor_tmul]
    change dualEv P f (∑ j, TensorProductOver.tmul R₃ (e' j)
      (TensorProductOver.tmul R₂ (φ' j) r)) = _
    rw [map_sum]
    simp only [dualEv_tmul, TensorProductOver.smul_tmul]
    rw [← sum_tmul, RightDualModule.sum_dualBasis_dual]
  | add y y' hy hy' => rw [map_add, hy, hy']

/-- The bi-additive map `(x, ψ) ↦ g(x ψ(s))`. -/
def homOfGenBil (s : S) (g : KbHom R₀ R₃ Kb X) : Kb →+ RightDualModule R₀ S →+ X :=
  AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun ψ => g (ψ s • x)) fun ψ ψ' => by
      change g ((ψ + ψ') s • x) = g (ψ s • x) + g (ψ' s • x)
      rw [RightDualModule.add_apply, add_smul, map_add])
    fun x x' => AddMonoidHom.ext fun ψ => by
      change g (ψ s • (x + x')) = g (ψ s • x) + g (ψ s • x')
      rw [smul_add, map_add]

omit [SMulCommClass R₃ R₀ᵐᵒᵖ Kb] [Module.Projective R₀ᵐᵒᵖ S] [Module.Finite R₀ᵐᵒᵖ S] in
theorem homOfGenBil_balanced (s : S) (g : KbHom R₀ R₃ Kb X) (c : R₀) (x : Kb)
    (ψ : RightDualModule R₀ S) : homOfGenBil s g (op c • x) ψ = homOfGenBil s g x (c • ψ) := by
  change g (ψ s • op c • x) = g ((c • ψ) s • x)
  rw [RightDualModule.smul_apply, mul_smul]

/-- `x ⊗ ψ ↦ g(x ψ(s))`, as an additive map `K_b ⊗_{R₀} S^∨ → X`. -/
def homOfGenAdd (s : S) (g : KbHom R₀ R₃ Kb X) : Q →+ X :=
  TensorProductOver.lift (homOfGenBil s g) (homOfGenBil_balanced s g)

omit [Module.Projective R₀ᵐᵒᵖ S] [Module.Finite R₀ᵐᵒᵖ S] in
theorem homOfGenAdd_smul (s : S) (g : KbHom R₀ R₃ Kb X) (a : R₃) (y : Q) :
    homOfGenAdd s g (a • y) = a • homOfGenAdd s g y := by
  induction y using TensorProductOver.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul x ψ =>
    change g (ψ s • a • x) = a • g (ψ s • x)
    rw [← smul_comm a (ψ s) x, map_smul]
  | add y y' hy hy' => rw [smul_add, map_add, map_add, hy, hy', smul_add]

/-- `x ⊗ ψ ↦ g(x ψ(s))`, the map `K_b ⊗_{R₀} S^∨ → X` of `s ⊗ g`. -/
def homOfGen (s : S) (g : KbHom R₀ R₃ Kb X) : Q →ₗ[R₃] X where
  toFun := homOfGenAdd s g
  map_add' := map_add (homOfGenAdd s g)
  map_smul' := homOfGenAdd_smul s g

omit [Module.Projective R₀ᵐᵒᵖ S] [Module.Finite R₀ᵐᵒᵖ S] in
theorem homOfGen_tmul (s : S) (g : KbHom R₀ R₃ Kb X) (x : Kb) (ψ : RightDualModule R₀ S) :
    homOfGen s g (TensorProductOver.tmul R₀ x ψ) = g (ψ s • x) := rfl

omit [Module.Projective R₀ᵐᵒᵖ S] [Module.Finite R₀ᵐᵒᵖ S] in
theorem homOfGen_add_left (s s' : S) (g : KbHom R₀ R₃ Kb X) :
    homOfGen (s + s') g = homOfGen s g + homOfGen s' g := by
  refine LinearMap.toAddMonoidHom_injective (TensorProductOver.addHom_ext fun x ψ => ?_)
  change g (ψ (s + s') • x) = g (ψ s • x) + g (ψ s' • x)
  rw [map_add, add_smul, map_add]

omit [Module.Projective R₀ᵐᵒᵖ S] [Module.Finite R₀ᵐᵒᵖ S] in
theorem homOfGen_add_right (s : S) (g g' : KbHom R₀ R₃ Kb X) :
    homOfGen s (g + g') = homOfGen s g + homOfGen s g' := by
  exact LinearMap.toAddMonoidHom_injective (TensorProductOver.addHom_ext fun x ψ => rfl)

omit [Module.Projective R₀ᵐᵒᵖ S] [Module.Finite R₀ᵐᵒᵖ S] in
theorem homOfGen_balanced (c : R₀) (s : S) (g : KbHom R₀ R₃ Kb X) :
    homOfGen (op c • s) g = homOfGen s (c • g) := by
  refine LinearMap.toAddMonoidHom_injective (TensorProductOver.addHom_ext fun x ψ => ?_)
  change g (ψ (op c • s) • x) = g (op c • ψ s • x)
  rw [show ψ (op c • s) = op c * ψ s from map_smul ψ (op c) s, mul_smul]

/-- **`S ⊗_{R₀} Hom_{R₃}(K_b, X) → Hom_{R₃}(K_b ⊗_{R₀} S^∨, X)`**, `s ⊗ g ↦ (x ⊗ ψ ↦ g(x ψ(s)))`. -/
def homOfTensorDual : TensorProductOver R₀ S (KbHom R₀ R₃ Kb X) →+ (Q →ₗ[R₃] X) :=
  TensorProductOver.lift
    (AddMonoidHom.mk' (fun s => AddMonoidHom.mk' (homOfGen s) (homOfGen_add_right s))
      fun s s' => AddMonoidHom.ext fun g => homOfGen_add_left s s' g)
    fun c s g => homOfGen_balanced c s g

/-- **`Hom_{R₃}(K_b ⊗_{R₀} S^∨, X) → S ⊗_{R₀} Hom_{R₃}(K_b, X)`**,
`h ↦ Σ_i e_i ⊗ (x ↦ h(x ⊗ φ_i))`. -/
def tensorOfHom (h : Q →ₗ[R₃] X) : TensorProductOver R₀ S (KbHom R₀ R₃ Kb X) :=
  ∑ i, TensorProductOver.tmul R₀ (e i) (KbHom.of
    { toFun := fun x => h (TensorProductOver.tmul R₀ x (φ i))
      map_add' := fun x x' => by rw [TensorProductOver.add_tmul, map_add]
      map_smul' := fun a x => by
        rw [RingHom.id_apply, ← map_smul]
        rfl })

theorem tensorOfHom_add (h h' : Q →ₗ[R₃] X) :
    tensorOfHom (h + h') = tensorOfHom h + tensorOfHom h' := by
  simp only [tensorOfHom, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← TensorProductOver.tmul_add]
  rfl

theorem tensorOfHom_homOfTensorDual (t : TensorProductOver R₀ S (KbHom R₀ R₃ Kb X)) :
    tensorOfHom (homOfTensorDual t) = t := by
  induction t using TensorProductOver.induction_on with
  | zero =>
    simp only [tensorOfHom, map_zero, LinearMap.zero_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    exact (congrArg (TensorProductOver.tmul R₀ (e i)) (KbHom.ext fun x => rfl)).trans
      (TensorProductOver.tmul_zero _)
  | tmul s g =>
    rw [tensorOfHom]
    conv_rhs => rw [← RightDualModule.sum_dualBasis R₀ S s, sum_tmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← op_unop (φ i s), TensorProductOver.op_smul_tmul]
    exact congrArg (TensorProductOver.tmul R₀ (e i)) (KbHom.ext fun x => rfl)
  | add t t' ht ht' => rw [map_add, tensorOfHom_add, ht, ht']

theorem homOfTensorDual_tensorOfHom (h : Q →ₗ[R₃] X) : homOfTensorDual (tensorOfHom h) = h := by
  refine LinearMap.toAddMonoidHom_injective (TensorProductOver.addHom_ext fun x ψ => ?_)
  change homOfTensorDual (∑ i, _) (TensorProductOver.tmul R₀ x ψ) =
    h (TensorProductOver.tmul R₀ x ψ)
  rw [map_sum, LinearMap.sum_apply]
  have hi : ∀ i, homOfTensorDual (TensorProductOver.tmul R₀ (e i) (KbHom.of
      { toFun := fun x => h (TensorProductOver.tmul R₀ x (φ i))
        map_add' := fun x x' => by rw [TensorProductOver.add_tmul, map_add]
        map_smul' := fun a x => by
          rw [RingHom.id_apply, ← map_smul]
          rfl })) (TensorProductOver.tmul R₀ x ψ) =
      h (TensorProductOver.tmul R₀ x (unop (ψ (e i)) • φ i)) := fun i => by
    rw [← TensorProductOver.op_smul_tmul, op_unop]
    rfl
  rw [Finset.sum_congr rfl fun i _ => hi i, ← map_sum, ← tmul_sum,
    RightDualModule.sum_dualBasis_dual]

end Yoneda

section Bijective

omit [Module.Projective R₃ᵐᵒᵖ Sp] [Module.Finite R₃ᵐᵒᵖ Sp] in
/-- **Precomposition with the mate is the Hom form `Θ_X`**, under the two Hom-tensor
identifications. -/
theorem homOfTensor_mateTheta_tensorOfHom {X : Type u} [AddCommGroup X] [Module R₃ X]
    (h : Q →ₗ[R₃] X) (y : P) :
    homOfTensor (mateTheta R₀ κ hκ hκr X (tensorOfHom h)) y = h (mate R₀ κ hκ y) := by
  induction y using TensorProductOver.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul f r =>
    rw [homOfTensor_tmul, mate_tmul, map_sum, tensorOfHom, map_sum, LinearMap.sum_apply,
      map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mateTheta_tmul, thetaGen_apply, dualEv_postMap]
    rfl
  | add y y' hy hy' => rw [map_add, map_add, hy, hy', map_add]

/-- **The mate is bijective** if its Hom form `Θ_X` is surjective at `X = S₊^∨ ⊗_{R₂} K` and
injective at `X = K_b ⊗_{R₀} S^∨` (the Yoneda argument). -/
theorem mate_bijective_of_mateTheta (hsurj : Function.Surjective (mateTheta R₀ κ hκ hκr P))
    (hinj : Function.Injective (mateTheta R₀ κ hκ hκr Q)) :
    Function.Bijective (mate R₀ κ hκ) := by
  obtain ⟨t, ht⟩ := hsurj unitTensor
  have hψ : ∀ y, homOfTensorDual t (mate R₀ κ hκ y) = y := fun y => by
    have key := homOfTensor_mateTheta_tensorOfHom R₀ κ hκ hκr (homOfTensorDual t) y
    rw [tensorOfHom_homOfTensorDual, ht, homOfTensor_unitTensor] at key
    exact key.symm
  refine ⟨fun y y' hyy => by rw [← hψ y, hyy, hψ y'], fun q => ⟨homOfTensorDual t q, ?_⟩⟩
  have h₁ : homOfTensor (mateTheta R₀ κ hκ hκr Q
      (tensorOfHom ((mateLinear R₀ κ hκ).comp (homOfTensorDual t)))) =
      homOfTensor (mateTheta R₀ κ hκ hκr Q (tensorOfHom LinearMap.id)) :=
    AddMonoidHom.ext fun y => by
      rw [homOfTensor_mateTheta_tensorOfHom, homOfTensor_mateTheta_tensorOfHom,
        LinearMap.comp_apply,
        mateLinear_apply, hψ, LinearMap.id_apply]
  have h₂ := congrArg homOfTensorDual (hinj (homOfTensor_injective h₁))
  rw [homOfTensorDual_tensorOfHom, homOfTensorDual_tensorOfHom] at h₂
  exact LinearMap.congr_fun h₂ q

end Bijective

end TensorMate

end Categorification

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapCoeInduced
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KFlip
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KPsiFlip
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KCoef
import Categorification.WeightedKLR.Rigidity.CupCapLeftLoop
import Categorification.Algebra.InductionAlongAdjunction

/-!
# Maps out of the reflected cap bimodule

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half. Let `T⁺ = T^{λ⁺}` and let
`L'` be a left `T^{μ μ*}`-module, whose reflection `CapCoef L'` gives the coefficients at the
maximum of the cap. The reflected cap bimodule `K^σ` (`ReflectedCap`) is, through the
reflection `σ` of `T⁺`, the bimodule `K^{λ⁺}_λ`, which is induced from its coefficients along
the diagrams at the maximum (`capCoeEquiv`). With the induction–restriction adjunction
(`InductionAlong.Ind.homEquiv`) this gives, for a left `T⁺`-module `M`,

`Hom_{T⁺}(K^σ, M) ≃ Hom_W(L', e · M)` (`reflectedCapHomEquiv`).

Here `W` is the KLR algebra of the strands at the maximum, acting on `L'` through its image in
`T^{μ μ*}`. The idempotent `e` is the reflected unit of the maximum (`windowUnit`). A diagram
`x` acts on `e · M` through `T⁺` by `windowAct x`, the sum over the loadings `s` of `λ` of the
diagrams `ι_s(x)` on the windows at `midPos s` (`windowAct_eq_sum`). The reflections of the two
actions match because placing a diagram in a window commutes with the reflection
(`hflip_insertMap`, `tensorFlipRingEquiv_tensorOfKLR_insertMap`).

The action of the window diagrams is stated over the KLR algebra `W` rather than over
`T^{μ μ*}`, because the window map need not descend to `T^{μ μ*}`. A map that is linear over
`W` is the same as a map that is linear over `T̃^{μ μ*}`, which is what the adjunction gives
(`cupMap_surjective`).

## Main definitions

* `Stendhal.CupCap.windowUnit`, `Stendhal.CupCap.windowAct`: the idempotent `e` and the
  window action in `T⁺`.
* `Stendhal.CupCap.WindowPart`: `e · M` as a module over the window KLR algebra.
* `Stendhal.CupCap.WindowCoef`: `L'` as a module over the window KLR algebra.
* `Stendhal.CupCap.ReflectedTarget`: a left `T⁺`-module as a right one, through `σ`.
* `Stendhal.CupCap.reflectedCapHomEquiv`: `Hom_{T⁺}(K^σ, M) ≃ Hom_W(L', e · M)`.

## Main results

* `Stendhal.CupCap.windowAct_eq_sum`, `Stendhal.CupCap.windowUnit_eq_windowAct`,
  `Stendhal.CupCap.plusFlip_midStendhal_cupMap`.
* `Stendhal.CupCap.tensorFlipRingEquiv_tensorOfKLR_insertMap`: the reflection of a diagram
  placed in a window.
* `Stendhal.CupCap.reflectedCapHomEquiv_apply_val`.

## Route hypotheses

Those of `capCoeEquiv` for the coefficients `CapCoef L'`: `hL` (support of the coefficients),
`hR` (`MidKLRRel`), `hP`, `hPL` (`PullOff`, `PullOffLeft`) and `hκ` (the cup scalars are
units).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} (j : ℕ) (hj : j ≤ ℓ)
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  (ν ν₀ : Multiset I)

set_option hygiene false in
local notation "Tq" => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
set_option hygiene false in
local notation "Rc" => KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)
set_option hygiene false in
local notation "mkP" => TensorProductAlgebra.mk Q (plusLabels Λ Λc j hj) (ν + ν₀)
set_option hygiene false in
local notation "σp" => tensorFlipRingEquiv (Q := Q) (Λ := plusLabels Λ Λc j hj) (ν + ν₀)

/-! ### The window action in `T⁺` -/

/-- **The reflected unit of the maximum** `e`, an idempotent of `T⁺`. -/
def windowUnit : TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀) :=
  plusFlip j hj Q Λ Λc ν ν₀ (midStendhal j hj Q Λ Λc ν ν₀ 1)

/-- **The window action**: a diagram on the strands at the maximum, placed on the window at
`midPos s` for every loading `s` of `λ`, in `T⁺`. -/
def windowAct (g : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) :
    TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀) :=
  mkP (midBot j hj Q Λ Λc ν ν₀ g)

variable {j hj Q Λ Λc ν ν₀}

theorem windowAct_eq (g : Rc) :
    windowAct j hj Q Λ Λc ν ν₀ g =
      tensorOfKLR Q (plusLabels Λ Λc j hj) (ν + ν₀) (midMapKLR j hj Q Λ Λc ν ν₀ g) := rfl

/-- **The window action is the sum of the diagrams `ι_s(x)`** on the windows at `midPos s`. -/
theorem windowAct_eq_sum (g : Rc) :
    windowAct j hj Q Λ Λc ν ν₀ g = ∑ s : Seq (stendhalWeight ℓ ν),
      tensorOfKLR Q (plusLabels Λ Λc j hj) (ν + ν₀)
        (insertMap (j := j) (hj := hj) Q Λ Λc s (midPos j s) (midPos_le j s) g) := by
  rw [windowAct_eq, midMapKLR]
  exact map_sum (stendhalTensorProjection (Q := Q) (plusLabels Λ Λc j hj) (ν + ν₀)) _ _

theorem windowAct_mul (g h : Rc) :
    windowAct j hj Q Λ Λc ν ν₀ (g * h) =
      windowAct j hj Q Λ Λc ν ν₀ g * windowAct j hj Q Λ Λc ν ν₀ h := by
  rw [windowAct, windowAct, windowAct, map_mul, map_mul]

theorem windowAct_add (g h : Rc) :
    windowAct j hj Q Λ Λc ν ν₀ (g + h) =
      windowAct j hj Q Λ Λc ν ν₀ g + windowAct j hj Q Λ Λc ν ν₀ h := by
  rw [windowAct, windowAct, windowAct, map_add, map_add]

theorem windowAct_zero : windowAct j hj Q Λ Λc ν ν₀ (0 : Rc) = 0 := by
  rw [windowAct, map_zero, map_zero]

/-- The reflected unit of the maximum is the window action of the red-ordered idempotent. -/
theorem windowUnit_eq_windowAct :
    windowUnit j hj Q Λ Λc ν ν₀ = windowAct j hj Q Λ Λc ν ν₀ (redOrderedKLR k Q Λc ν₀) := by
  rw [windowUnit, midStendhal_one_eq_midBot, plusFlip_midBot, hflip_redOrderedKLR]
  rfl

theorem windowAct_mul_windowUnit (g : Rc) :
    windowAct j hj Q Λ Λc ν ν₀ g * windowUnit j hj Q Λ Λc ν ν₀ =
      windowUnit j hj Q Λ Λc ν ν₀ * windowAct j hj Q Λ Λc ν ν₀ g := by
  have h := (commute_midStendhal_one_midBot (j := j) (hj := hj) (Q := Q) (Λ := Λ) (Λc := Λc)
    (ν := ν) (ν₀ := ν₀) g).eq
  rw [midStendhal_one_eq_midBot] at h
  rw [windowUnit_eq_windowAct, windowAct, windowAct, ← map_mul, ← h, map_mul]

theorem windowAct_one_mul_windowUnit :
    windowAct j hj Q Λ Λc ν ν₀ 1 * windowUnit j hj Q Λ Λc ν ν₀ = windowUnit j hj Q Λ Λc ν ν₀ := by
  rw [windowUnit_eq_windowAct, ← windowAct_mul, one_mul]

/-- **The reflection of a diagram of `T̃^{μ μ*}` at the maximum** is the window action of its
mirror image, cut by `e`. -/
theorem plusFlip_midStendhal_cupMap (y : Rc) :
    plusFlip j hj Q Λ Λc ν ν₀ (midStendhal j hj Q Λ Λc ν ν₀ (cupMap k Q Λc ν₀ y)) =
      windowAct j hj Q Λ Λc ν ν₀ (hflip y) * windowUnit j hj Q Λ Λc ν ν₀ := by
  rw [midStendhal_cupMap', plusFlip_mul, plusFlip_midBot]
  rfl

/-- **The reflection of a diagram placed in a window** is its mirror image placed in the same
window. -/
theorem tensorFlipRingEquiv_tensorOfKLR_insertMap (s : Seq (stendhalWeight ℓ ν)) {n : ℕ}
    (hn : n ≤ Multiset.card (stendhalWeight ℓ ν)) (x : Rc) :
    σp (tensorOfKLR Q (plusLabels Λ Λc j hj) (ν + ν₀)
        (insertMap (j := j) (hj := hj) Q Λ Λc s n hn x)) =
      op (tensorOfKLR Q (plusLabels Λ Λc j hj) (ν + ν₀)
        (insertMap (j := j) (hj := hj) Q Λ Λc s n hn (hflip x))) := by
  rw [← hflip_insertMap]
  exact tensorFlipRingEquiv_mk _

/-! ### The part `e · M` as a module over the window -/

section WindowPart

variable (j hj Q Λ Λc ν ν₀)
variable (M : Type*) [AddCommGroup M] [Module Tq M]

/-- The elements of `M` fixed by `e`. -/
def windowFixed : AddSubgroup M where
  carrier := {m | windowUnit j hj Q Λ Λc ν ν₀ • m = m}
  add_mem' {x y} hx hy := by
    change windowUnit j hj Q Λ Λc ν ν₀ • (x + y) = x + y
    rw [smul_add, hx, hy]
  zero_mem' := smul_zero _
  neg_mem' {x} hx := by
    change windowUnit j hj Q Λ Λc ν ν₀ • -x = -x
    rw [smul_neg, hx]

/-- **The part `e · M`**, a module over the KLR algebra of the strands at the maximum through the
window action. -/
def WindowPart : Type _ := windowFixed j hj Q Λ Λc ν ν₀ M

instance : AddCommGroup (WindowPart j hj Q Λ Λc ν ν₀ M) :=
  inferInstanceAs (AddCommGroup (windowFixed j hj Q Λ Λc ν ν₀ M))

variable {j hj Q Λ Λc ν ν₀ M}

namespace WindowPart

/-- The underlying element of `M`. -/
def val (m : WindowPart j hj Q Λ Λc ν ν₀ M) : M := (show windowFixed j hj Q Λ Λc ν ν₀ M from m).1

theorem prop (m : WindowPart j hj Q Λ Λc ν ν₀ M) : windowUnit j hj Q Λ Λc ν ν₀ • m.val = m.val :=
  (show windowFixed j hj Q Λ Λc ν ν₀ M from m).2

/-- An element of `M` fixed by `e`. -/
def mk (m : M) (h : windowUnit j hj Q Λ Λc ν ν₀ • m = m) : WindowPart j hj Q Λ Λc ν ν₀ M :=
  (⟨m, h⟩ : windowFixed j hj Q Λ Λc ν ν₀ M)

@[simp] theorem val_mk (m : M) (h : windowUnit j hj Q Λ Λc ν ν₀ • m = m) :
    (mk m h : WindowPart j hj Q Λ Λc ν ν₀ M).val = m := rfl

theorem ext {m m' : WindowPart j hj Q Λ Λc ν ν₀ M} (h : m.val = m'.val) : m = m' :=
  Subtype.ext (p := fun x => x ∈ windowFixed j hj Q Λ Λc ν ν₀ M) h

@[simp] theorem val_add (m m' : WindowPart j hj Q Λ Λc ν ν₀ M) :
    (m + m').val = m.val + m'.val := rfl

@[simp] theorem val_zero : (0 : WindowPart j hj Q Λ Λc ν ν₀ M).val = 0 := rfl

theorem windowAct_smul_mem (g : Rc) (m : WindowPart j hj Q Λ Λc ν ν₀ M) :
    windowUnit j hj Q Λ Λc ν ν₀ • windowAct j hj Q Λ Λc ν ν₀ g • m.val =
      windowAct j hj Q Λ Λc ν ν₀ g • m.val := by
  conv_rhs => rw [← m.prop]
  rw [smul_smul, smul_smul, windowAct_mul_windowUnit]

/-- A diagram on the strands at the maximum acts on `e · M` by the window action. -/
instance : Module Rc (WindowPart j hj Q Λ Λc ν ν₀ M) where
  smul g m := mk (windowAct j hj Q Λ Λc ν ν₀ g • m.val) (windowAct_smul_mem g m)
  one_smul m := ext (by
    change windowAct j hj Q Λ Λc ν ν₀ 1 • m.val = m.val
    conv_lhs => rw [← m.prop]
    rw [smul_smul, windowAct_one_mul_windowUnit, m.prop])
  mul_smul g h m := ext (by
    change windowAct j hj Q Λ Λc ν ν₀ (g * h) • m.val =
      windowAct j hj Q Λ Λc ν ν₀ g • windowAct j hj Q Λ Λc ν ν₀ h • m.val
    rw [windowAct_mul, mul_smul])
  smul_zero g := ext (smul_zero (windowAct j hj Q Λ Λc ν ν₀ g))
  smul_add g m m' := ext (smul_add (windowAct j hj Q Λ Λc ν ν₀ g) m.val m'.val)
  add_smul g h m := ext (by
    change windowAct j hj Q Λ Λc ν ν₀ (g + h) • m.val =
      windowAct j hj Q Λ Λc ν ν₀ g • m.val + windowAct j hj Q Λ Λc ν ν₀ h • m.val
    rw [windowAct_add, add_smul])
  zero_smul m := ext (by
    change windowAct j hj Q Λ Λc ν ν₀ 0 • m.val = 0
    rw [windowAct_zero, zero_smul])

@[simp] theorem val_smul (g : Rc) (m : WindowPart j hj Q Λ Λc ν ν₀ M) :
    (g • m).val = windowAct j hj Q Λ Λc ν ν₀ g • m.val := rfl

end WindowPart

end WindowPart

/-! ### `L'` as a module over the window -/

section WindowCoef

/-- **A left `T^{μ μ*}`-module as a module over the KLR algebra of the strands at the maximum**,
through the image of diagrams in `T^{μ μ*}`. -/
@[nolint unusedArguments]
def WindowCoef (_Q : I → I → MvPolynomial (Fin 2) k) (_Λc : Fin 2 → I →₀ ℕ)
    (_ν₀ : Multiset I) (L' : Type) : Type := L'

variable {L' : Type} [AddCommGroup L'] [Module (TensorProductAlgebra k Q Λc ν₀) L']

instance : AddCommGroup (WindowCoef Q Λc ν₀ L') := inferInstanceAs (AddCommGroup L')

instance : Module Rc (WindowCoef Q Λc ν₀ L') :=
  Module.compHom L' (stendhalTensorProjection (Q := Q) Λc ν₀).toRingHom

/-- An element of `L'` as an element of `WindowCoef`. -/
def toWindowCoef (v : L') : WindowCoef Q Λc ν₀ L' := v

/-- The element of `L'` underlying an element of `WindowCoef`. -/
def ofWindowCoef (v : WindowCoef Q Λc ν₀ L') : L' := v

theorem smul_toWindowCoef (g : Rc) (v : L') :
    g • toWindowCoef (Q := Q) (Λc := Λc) (ν₀ := ν₀) v =
      toWindowCoef (tensorOfKLR Q Λc ν₀ g • v) := rfl

end WindowCoef

/-! ### Left modules of `T⁺` as right modules -/

section Target

/-- **A left `T⁺`-module as a right `T⁺`-module** through the reflection `σ`. -/
@[nolint unusedArguments]
def ReflectedTarget (_j : ℕ) (_hj : _j ≤ ℓ) (_Q : I → I → MvPolynomial (Fin 2) k)
    (_Λ : Fin ℓ → I →₀ ℕ) (_Λc : Fin 2 → I →₀ ℕ) (_ν _ν₀ : Multiset I) (M : Type*) :
    Type _ := M

variable {M : Type*} [AddCommGroup M] [Module Tq M]

instance : AddCommGroup (ReflectedTarget j hj Q Λ Λc ν ν₀ M) := inferInstanceAs (AddCommGroup M)

instance : Module Tqᵐᵒᵖ (ReflectedTarget j hj Q Λ Λc ν ν₀ M) :=
  Module.compHom M ((σp).symm : Tqᵐᵒᵖ →+* Tq)

/-- An element of `M` as an element of `ReflectedTarget`. -/
def toReflectedTarget (m : M) : ReflectedTarget j hj Q Λ Λc ν ν₀ M := m

/-- The element of `M` underlying an element of `ReflectedTarget`. -/
def ofReflectedTarget (m : ReflectedTarget j hj Q Λ Λc ν ν₀ M) : M := m

theorem op_smul_reflectedTarget (t : Tqᵐᵒᵖ) (m : ReflectedTarget j hj Q Λ Λc ν ν₀ M) :
    ofReflectedTarget (t • m) = (σp).symm t • ofReflectedTarget m := rfl

variable {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

/-- **Maps out of the reflected cap are maps of right modules out of the cap.** -/
def reflectedCapHomFlip :
    (ReflectedCap j hj Q Λ Λc ν ν₀ L →ₗ[Tq] M) ≃+
      (CapBimodule k Q Λ Λc j hj ν ν₀ L →ₗ[Tqᵐᵒᵖ] ReflectedTarget j hj Q Λ Λc ν ν₀ M) where
  toFun f :=
    { toFun := fun z => toReflectedTarget (f (toReflectedCap z))
      map_add' := fun z z' => f.map_add (toReflectedCap z) (toReflectedCap z')
      map_smul' := fun t z => by
        change f (toReflectedCap (t • z)) = (σp).symm t • f (toReflectedCap z)
        rw [← map_smul, smul_toReflectedCap, RingEquiv.apply_symm_apply] }
  invFun g :=
    { toFun := fun z => ofReflectedTarget (g (ofReflectedCap z))
      map_add' := fun z z' => g.map_add (ofReflectedCap z) (ofReflectedCap z')
      map_smul' := fun s z => by
        change ofReflectedTarget (g ((σp s) • ofReflectedCap z)) =
          s • ofReflectedTarget (g (ofReflectedCap z))
        rw [map_smul, op_smul_reflectedTarget, RingEquiv.symm_apply_apply] }
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

end Target

/-! ### The adjunction -/

section Adjunction

variable {L' : Type} [AddCommGroup L'] [Module k L'] [Module (TensorProductAlgebra k Q Λc ν₀) L']
  {M : Type*} [AddCommGroup M] [Module Tq M]

set_option hygiene false in
local notation "Lc" => CapCoef Q Λc ν₀ L'
set_option hygiene false in
local notation "RT" => ReflectedTarget j hj Q Λ Λc ν ν₀ M
set_option hygiene false in
local notation "ofRT" => ofReflectedTarget (j := j) (hj := hj) (Q := Q) (Λ := Λ) (Λc := Λc)
  (ν := ν) (ν₀ := ν₀) (M := M)
set_option hygiene false in
local notation "toWC" => toWindowCoef (Q := Q) (Λc := Λc) (ν₀ := ν₀) (L' := L')
set_option hygiene false in
local notation "toRT" => toReflectedTarget (j := j) (hj := hj) (Q := Q) (Λ := Λ) (Λc := Λc)
  (ν := ν) (ν₀ := ν₀) (M := M)

/-- The idempotent of the restriction along the diagrams at the maximum acts on the reflected
target as `e`. -/
theorem capCoeOp_one_smul (m : RT) :
    ofReflectedTarget (capCoeOp k Q Λ Λc j hj ν ν₀ 1 • m) =
      windowUnit j hj Q Λ Λc ν ν₀ • ofReflectedTarget m := rfl

theorem capCoeOp_cupMap_smul (y : Rc) (m : RT)
    (hm : windowUnit j hj Q Λ Λc ν ν₀ • ofReflectedTarget m = ofReflectedTarget m) :
    ofReflectedTarget (capCoeOp k Q Λ Λc j hj ν ν₀ (op (cupMap k Q Λc ν₀ y)) • m) =
      windowAct j hj Q Λ Λc ν ν₀ (hflip y) • ofReflectedTarget m := by
  change plusFlip j hj Q Λ Λc ν ν₀ (midStendhal j hj Q Λ Λc ν ν₀ (cupMap k Q Λc ν₀ y)) •
    ofReflectedTarget m = _
  rw [plusFlip_midStendhal_cupMap, mul_smul, hm]

theorem op_cupMap_smul_capCoef (y : Rc) (v : L') :
    (op (cupMap k Q Λc ν₀ y) • toCapCoef (Q := Q) (Λc := Λc) (ν₀ := ν₀) v : Lc) =
      toCapCoef (tensorOfKLR Q Λc ν₀ (hflip y) • v) :=
  op_smul_capCoef y v

/-- The restriction of the reflected target along the diagrams at the maximum is `e · M` over
the window: the forward map. -/
def resWindowHom (f : Lc →ₗ[(StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ] Res (capCoeOp k Q Λ Λc j hj ν ν₀) RT) :
    WindowCoef Q Λc ν₀ L' →ₗ[Rc] WindowPart j hj Q Λ Λc ν ν₀ M where
  toFun v := WindowPart.mk (ofReflectedTarget (f (toCapCoef (ofWindowCoef v))).val)
    (f (toCapCoef (ofWindowCoef v))).prop
  map_add' v v' := WindowPart.ext (by
    simp only [WindowPart.val_mk, WindowPart.val_add]
    exact congrArg Res.val (f.map_add (toCapCoef v) (toCapCoef v')))
  map_smul' g v := WindowPart.ext (by
    have h1 : (toCapCoef (tensorOfKLR Q Λc ν₀ g • ofWindowCoef v) : Lc) =
        op (cupMap k Q Λc ν₀ (hflip g)) • toCapCoef (ofWindowCoef v) := by
      rw [op_cupMap_smul_capCoef, hflip_hflip]
    have h2 := capCoeOp_cupMap_smul (M := M) (hflip g) (f (toCapCoef (ofWindowCoef v))).val
      (f (toCapCoef (ofWindowCoef v))).prop
    rw [hflip_hflip] at h2
    refine (congrArg (fun x => ofRT (f x).val) h1).trans ?_
    rw [map_smul, Res.val_smul]
    exact h2)

/-- The restriction of the reflected target along the diagrams at the maximum is `e · M` over
the window: the inverse map. -/
def windowResHom (g : WindowCoef Q Λc ν₀ L' →ₗ[Rc] WindowPart j hj Q Λ Λc ν ν₀ M) :
    Lc →ₗ[(StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ] Res (capCoeOp k Q Λ Λc j hj ν ν₀) RT where
  toFun v := Res.mk (toRT (g (toWC (show L' from v))).val) (g (toWC (show L' from v))).prop
  map_add' v v' := Res.ext (congrArg (WindowPart.val (M := M))
    (g.map_add (toWC (show L' from v)) (toWC (show L' from v'))))
  map_smul' c v := Res.ext (by
    obtain ⟨y, hy⟩ := cupMap_surjective Q Λc c.unop
    have hc : c = op (cupMap k Q Λc ν₀ y) := by rw [hy, op_unop]
    subst hc
    have h1 : toWC (show L' from (op (cupMap k Q Λc ν₀ y) • v : Lc)) =
        hflip y • toWC (show L' from v) :=
      congrArg toWC (op_cupMap_smul_capCoef y (show L' from v))
    have h2 := capCoeOp_cupMap_smul (M := M) y (toRT (g (toWC (show L' from v))).val)
      (g (toWC (show L' from v))).prop
    refine (congrArg (fun x => toRT (g x).val) h1).trans ?_
    rw [map_smul, WindowPart.val_smul]
    exact h2.symm)

/-- **The restriction along the diagrams at the maximum is `e · M` over the window.** -/
def resWindowEquiv :
    (Lc →ₗ[(StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ] Res (capCoeOp k Q Λ Λc j hj ν ν₀) RT) ≃+
      (WindowCoef Q Λc ν₀ L' →ₗ[Rc] WindowPart j hj Q Λ Λc ν ν₀ M) where
  toFun := resWindowHom
  invFun := windowResHom
  left_inv _ := LinearMap.ext fun _ => Res.ext rfl
  right_inv _ := LinearMap.ext fun _ => WindowPart.ext rfl
  map_add' _ _ := LinearMap.ext fun _ => WindowPart.ext rfl

variable {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : Lc), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}
  (hR : MidKLRRel j hj Q Λ Λc ν ν₀ Lc hL) (hP : PullOff k Q Λc ν₀ Lc)
  (hPL : PullOffLeft k Q Λc ν₀ Lc) (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))

/-- Maps out of the cap are maps out of the induced module `L ⊗ e T⁺`. -/
def capHomIndEquiv :
    (CapBimodule k Q Λ Λc j hj ν ν₀ Lc →ₗ[Tqᵐᵒᵖ] RT) ≃+
      (Ind Lc (capCoeOp k Q Λ Λc j hj ν ν₀) →ₗ[Tqᵐᵒᵖ] RT) where
  toFun f := f.comp (capCoeEquiv hR hP hPL hκ).symm.toLinearMap
  invFun g := g.comp (capCoeEquiv hR hP hPL hκ).toLinearMap
  left_inv f := LinearMap.ext fun z => congrArg f ((capCoeEquiv hR hP hPL hκ).symm_apply_apply z)
  right_inv g := LinearMap.ext fun z => congrArg g ((capCoeEquiv hR hP hPL hκ).apply_symm_apply z)
  map_add' _ _ := rfl

/-- **Maps out of the reflected cap** (Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19,
trace half): `Hom_{T⁺}(K^σ, M) ≃ Hom_W(L', e · M)`, where the KLR algebra `W` of the strands at
the maximum acts on `L'` through `T^{μ μ*}` and on `e · M` by the window action. The map sends
`f` to `v ↦ f(cap ⊗ v)`, the image of the generator of the induced module.

Route hypotheses: those of `capCoeEquiv`. -/
def reflectedCapHomEquiv :
    (ReflectedCap j hj Q Λ Λc ν ν₀ Lc →ₗ[Tq] M) ≃+
      (WindowCoef Q Λc ν₀ L' →ₗ[Rc] WindowPart j hj Q Λ Λc ν ν₀ M) :=
  let e₀ : (ReflectedCap j hj Q Λ Λc ν ν₀ Lc →ₗ[Tq] M) ≃+
      (CapBimodule k Q Λ Λc j hj ν ν₀ Lc →ₗ[Tqᵐᵒᵖ] RT) :=
    reflectedCapHomFlip
  let e₀' : (CapBimodule k Q Λ Λc j hj ν ν₀ Lc →ₗ[Tqᵐᵒᵖ] RT) ≃+
      (Ind Lc (capCoeOp k Q Λ Λc j hj ν ν₀) →ₗ[Tqᵐᵒᵖ] RT) :=
    capHomIndEquiv hR hP hPL hκ
  let e₁ := e₀.trans e₀'
  let e₂ : (Ind Lc (capCoeOp k Q Λ Λc j hj ν ν₀) →ₗ[Tqᵐᵒᵖ] RT) ≃+
      (Lc →ₗ[(StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ] Res (capCoeOp k Q Λ Λc j hj ν ν₀) RT) :=
    Ind.homEquiv
  (e₁.trans e₂).trans (resWindowEquiv (L' := L') (M := M))

theorem reflectedCapHomEquiv_apply_val (f : ReflectedCap j hj Q Λ Λc ν ν₀ Lc →ₗ[Tq] M)
    (v : L') :
    (reflectedCapHomEquiv hR hP hPL hκ f (toWindowCoef v)).val =
      f (toReflectedCap ((capCoeEquiv hR hP hPL hκ).symm
        (Ind.tmul (unitGen (capCoeOp k Q Λ Λc j hj ν ν₀)) (toCapCoef v)))) := rfl

/-- **The window acts on the image of `L'`**: for `f : K^σ → M`, the image of `x · v` is the
window action of `x`, a sum of the diagrams `ι_s(x)` (`windowAct_eq_sum`), on the image of `v`. -/
theorem reflectedCapHomEquiv_smul_val (f : ReflectedCap j hj Q Λ Λc ν ν₀ Lc →ₗ[Tq] M) (x : Rc)
    (v : WindowCoef Q Λc ν₀ L') :
    (reflectedCapHomEquiv hR hP hPL hκ f (x • v)).val =
      windowAct j hj Q Λ Λc ν ν₀ x • (reflectedCapHomEquiv hR hP hPL hκ f v).val := by
  rw [map_smul, WindowPart.val_smul]

theorem reflectedCapHomEquiv_symm_apply
    (g : WindowCoef Q Λc ν₀ L' →ₗ[Rc] WindowPart j hj Q Λ Λc ν ν₀ M)
    (z : Corner (capCoeOp k Q Λ Λc j hj ν ν₀)) (v : L') :
    (reflectedCapHomEquiv hR hP hPL hκ).symm g
        (toReflectedCap ((capCoeEquiv hR hP hPL hκ).symm (Ind.tmul z (toCapCoef v)))) =
      ofReflectedTarget (z.1 • toReflectedTarget (j := j) (hj := hj) (Q := Q) (Λ := Λ)
        (Λc := Λc) (ν := ν) (ν₀ := ν₀) (g (toWindowCoef v)).val) := by
  change ofReflectedTarget (Ind.homEquiv.symm (windowResHom g)
    ((capCoeEquiv hR hP hPL hκ) ((capCoeEquiv hR hP hPL hκ).symm _))) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

end Adjunction

end Categorification.Stendhal.CupCap

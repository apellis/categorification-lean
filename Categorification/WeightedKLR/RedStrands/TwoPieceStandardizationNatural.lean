/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TwoPieceStandardizationEquiv
import Categorification.Algebra.BalancedTensorEndAction

/-!
# Naturality of `M ⊗_B S^L_α ≅ S(X_M)` in the module `M`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5. An endomorphism `g` of the right module `M` over the block algebra of `ℓ + 1`
red strands induces endomorphisms of `M ⊗_B S^L_α` (`M ⊗ g`), of
`X_M = M ⊗_{B'} S^L_{α'}` as a module over the factor algebra (`twoPieceEnd g`) and of the
two-piece standardization `S(X_M)` (`S(twoPieceEnd g)`), and the isomorphism
`splitStandardEquiv` intertwines them (`splitStandardEquiv_mapRight`). These maps are
multiplicative in `g` (`twoPieceEndAlg`, `parabolicEndAlg`), so an algebra acting on `M` by
module endomorphisms acts compatibly on all three. This is the form in which the filtrations of
Proposition 5.5 are carried through the induction on the number of red strands.

## Main definitions

* `initRestrictEnd`, `twoPieceEnd`: the endomorphisms of `InitRestrict M` and of `X_M`.
* `twoPieceEndAlg`, `parabolicEndAlg`: these as maps of algebras.

## Main results

* `splitStandardEquiv_mapRight`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra MulOpposite
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace StendhalAlgebra

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (hQ : KLRSymm Q)

/-- The scalar tower `k → T(θ + β) → S N`. -/
local instance parabolicStandardT_isScalarTower_natural {θ β : Multiset I} (N : Type*)
    [AddCommGroup N] [Module k N] [Module (parabolicFactorAlgebra Q Λ θ β) N]
    [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N] :
    IsScalarTower k (TensorProductAlgebra k Q Λ (θ + β)) (ParabolicStandardT Q Λ θ β N hQ) :=
  ⟨fun c t y => DFunLike.congr_fun (map_smul (parabolicStandardAction Q Λ θ β N hQ) c t) y⟩

section Parabolic

variable {θ β : Multiset I} {N : Type*} [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ θ β) N] [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N]

/-- Standardization on endomorphisms, as a map of algebras. -/
def parabolicEndAlg : Module.End (parabolicFactorAlgebra Q Λ θ β) N →ₐ[k]
    Module.End (TensorProductAlgebra k Q Λ (θ + β)) (ParabolicStandardT Q Λ θ β N hQ) where
  toFun g := parabolicStandardMapT Q Λ hQ g
  map_one' := parabolicStandardMapT_id Q Λ hQ
  map_mul' g g' := parabolicStandardMapT_comp Q Λ hQ g' g
  map_zero' := parabolicStandardMapT_zero Q Λ hQ
  map_add' := parabolicStandardMapT_add Q Λ hQ
  commutes' c := parabolicStandardT_ext Q Λ θ β hQ fun n => by
    rw [parabolicStandardMapT_unit, Module.algebraMap_end_apply, Module.algebraMap_end_apply]
    exact map_smul (parabolicStandardUnit Q Λ θ β N) c n

@[simp] theorem parabolicEndAlg_apply (g : Module.End (parabolicFactorAlgebra Q Λ θ β) N) :
    parabolicEndAlg Q Λ hQ g = parabolicStandardMapT Q Λ hQ g := rfl

end Parabolic

variable (b : Fin (ℓ + 2) → Multiset I)

local notation "𝔹" => BlockAlgebra k Q Λ b
local notation "B'" => BlockAlgebra k Q (Λ ∘ Fin.castSucc) (initBlocks b)
local notation "Cyc" => CycKLR k Q (fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i)
  (lastBlock b)
local notation "Told" => TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) (initWeight b)
local notation "D" => parabolicFactorAlgebra Q Λ (initWeight b) (lastBlock b)

variable {M : Type*} [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]

local notation "ofR" => initRestrictOf Q Λ b (M := M)

/-- An endomorphism of `M` as an endomorphism of `M` over the block algebra of the first `ℓ`
red strands. -/
def initRestrictEnd (g : Module.End 𝔹ᵐᵒᵖ M) : Module.End B'ᵐᵒᵖ (InitRestrict Q Λ b M) where
  toFun m := ofR (g ((ofR).symm m))
  map_add' m m' := by rw [map_add, map_add, map_add]
  map_smul' a m := by
    obtain ⟨m, rfl⟩ := (ofR).surjective m
    induction a using MulOpposite.rec' with | _ x =>
    rw [op_smul_initRestrictOf, RingHom.id_apply, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply, map_smul, op_smul_initRestrictOf]

omit [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M] in
theorem initRestrictEnd_of (g : Module.End 𝔹ᵐᵒᵖ M) (m : M) :
    initRestrictEnd Q Λ b g (ofR m) = ofR (g m) := rfl

omit [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M] in
theorem lastFactorEnd_comp_initRestrictEnd (g : Module.End 𝔹ᵐᵒᵖ M) (c : Cyc) :
    lastFactorEnd Q Λ b c ∘ₗ initRestrictEnd Q Λ b g =
      initRestrictEnd Q Λ b g ∘ₗ lastFactorEnd Q Λ b c := by
  refine LinearMap.ext fun m => ?_
  obtain ⟨m, rfl⟩ := (ofR).surjective m
  rw [LinearMap.comp_apply, LinearMap.comp_apply, initRestrictEnd_of, lastFactorEnd_of,
    lastFactorEnd_of, initRestrictEnd_of]
  exact congrArg ofR (map_smul g _ m).symm

variable (hα' : RootNonViolated (ν := initWeight b) (blockRoot (initBlocks b)))

local notation "L'" => BlockLeftStandard Q (Λ ∘ Fin.castSucc) (initBlocks b) rfl hα'
local notation "XL" => LeftStandardization Q (Λ ∘ Fin.castSucc) (initBlocks b) rfl hα'
  (InitRestrict Q Λ b M)
local notation "ofX" => twoPieceInputOf Q Λ b M hα'
local notation "mR" => BalancedTensor.mapRight (k := k) (B := Told) (M := L')

theorem twoPieceInput_smul_def (d : D) (x : XL) :
    d • ofX x = ofX (twoPieceInputAction Q Λ b M hα' d x) := rfl

theorem twoPieceInputAction_tmul (t : Told) (c : Cyc) (x : XL) :
    twoPieceInputAction Q Λ b M hα' (t ⊗ₜ c) x = t • mR (lastFactorEnd Q Λ b c) x := by
  rw [twoPieceInputAction, Algebra.TensorProduct.lift_tmul, Module.End.mul_apply]
  rfl

/-- **The endomorphism `X_g` of `X_M = M ⊗_{B'} S^L_{α'}`** over the factor algebra. -/
def twoPieceEnd (g : Module.End 𝔹ᵐᵒᵖ M) :
    Module.End D (TwoPieceInput Q Λ b M hα') where
  toFun x := ofX (mR (initRestrictEnd Q Λ b g) ((ofX).symm x))
  map_add' x y := by rw [map_add, map_add, map_add]
  map_smul' d x := by
    obtain ⟨x, rfl⟩ := (ofX).surjective x
    rw [RingHom.id_apply, twoPieceInput_smul_def, twoPieceInput_smul_def,
      LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    congr 1
    induction d using TensorProduct.inductionOn with
    | tmul t c =>
      rw [twoPieceInputAction_tmul, twoPieceInputAction_tmul, map_smul, ← LinearMap.comp_apply,
        ← LinearMap.comp_apply, ← BalancedTensor.mapRight_comp, ← BalancedTensor.mapRight_comp,
        lastFactorEnd_comp_initRestrictEnd]
    | add d d' hd hd' => simp only [map_add, LinearMap.add_apply, hd, hd']

theorem twoPieceEnd_of (g : Module.End 𝔹ᵐᵒᵖ M) (x : XL) :
    twoPieceEnd Q Λ b hα' g (ofX x) = ofX (mR (initRestrictEnd Q Λ b g) x) := rfl

/-- `g ↦ X_g` as a map of algebras. -/
def twoPieceEndAlg : Module.End 𝔹ᵐᵒᵖ M →ₐ[k] Module.End D (TwoPieceInput Q Λ b M hα') where
  toFun := twoPieceEnd Q Λ b hα'
  map_one' := LinearMap.ext fun x => by
    obtain ⟨x, rfl⟩ := (ofX).surjective x
    rw [twoPieceEnd_of]
    exact congrArg ofX (LinearMap.congr_fun BalancedTensor.mapRight_id x)
  map_mul' g g' := LinearMap.ext fun x => by
    obtain ⟨x, rfl⟩ := (ofX).surjective x
    rw [Module.End.mul_apply, twoPieceEnd_of, twoPieceEnd_of, twoPieceEnd_of]
    exact congrArg ofX (LinearMap.congr_fun
      (BalancedTensor.mapRight_comp (initRestrictEnd Q Λ b g') (initRestrictEnd Q Λ b g)) x)
  map_zero' := LinearMap.ext fun x => by
    obtain ⟨x, rfl⟩ := (ofX).surjective x
    rw [twoPieceEnd_of, LinearMap.zero_apply]
    refine (congrArg ofX ?_).trans (map_zero ofX)
    exact LinearMap.congr_fun (map_zero (BalancedTensor.endMapRight k Told L'
      (N := InitRestrict Q Λ b M))) x
  map_add' g g' := LinearMap.ext fun x => by
    obtain ⟨x, rfl⟩ := (ofX).surjective x
    rw [LinearMap.add_apply, twoPieceEnd_of, twoPieceEnd_of, twoPieceEnd_of, ← map_add]
    exact congrArg ofX (LinearMap.congr_fun
      (BalancedTensor.mapRight_add (initRestrictEnd Q Λ b g) (initRestrictEnd Q Λ b g')) x)
  commutes' c := LinearMap.ext fun x => by
    obtain ⟨x, rfl⟩ := (ofX).surjective x
    rw [twoPieceEnd_of, Module.algebraMap_end_apply]
    have h : initRestrictEnd Q Λ b (algebraMap k (Module.End 𝔹ᵐᵒᵖ M) c) =
        c • (LinearMap.id : Module.End B'ᵐᵒᵖ (InitRestrict Q Λ b M)) := rfl
    rw [h, BalancedTensor.mapRight_smul, BalancedTensor.mapRight_id]
    rfl

@[simp] theorem twoPieceEndAlg_apply (g : Module.End 𝔹ᵐᵒᵖ M) :
    twoPieceEndAlg Q Λ b hα' g = twoPieceEnd Q Λ b hα' g := rfl

variable (hα : RootNonViolated (ν := initWeight b + lastBlock b) (blockRoot b))

local notation "L" => BlockLeftStandard Q Λ b (blockPrefix_last b) hα

theorem splitStandardTo_twoPieceEnd (g : Module.End 𝔹ᵐᵒᵖ M) :
    (splitStandardTo Q Λ hQ b hα' hα M).comp
        (parabolicStandardMapT Q Λ hQ (twoPieceEnd Q Λ b hα' g)) =
      (BalancedTensor.mapRight (k := k) (B := TensorProductAlgebra k Q Λ
        (initWeight b + lastBlock b)) (M := L) g).comp (splitStandardTo Q Λ hQ b hα' hα M) := by
  refine parabolicStandardT_ext Q Λ (initWeight b) (lastBlock b) hQ fun n => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, parabolicStandardMapT_unit,
    splitStandardTo_unit, splitStandardTo_unit]
  obtain ⟨x, rfl⟩ := (ofX).surjective n
  rw [twoPieceEnd_of]
  induction x using BalancedTensor.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul l m =>
    obtain ⟨m, rfl⟩ := (ofR).surjective m
    rw [BalancedTensor.mapRight_tmul, initRestrictEnd_of, splitInputMap_of, splitInputMap_of,
      LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, BalancedTensor.mapRight_tmul]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add, map_add, map_add]

/-- **Naturality of `M ⊗_B S^L_α ≅ S(X_M)` in `M`.** -/
theorem splitStandardEquiv_mapRight (g : Module.End 𝔹ᵐᵒᵖ M)
    (y : LeftStandardization Q Λ b (blockPrefix_last b) hα M) :
    splitStandardEquiv Q Λ hQ b hα' hα M
        (BalancedTensor.mapRight (k := k) (B := TensorProductAlgebra k Q Λ
          (initWeight b + lastBlock b)) (M := L) g y) =
      parabolicStandardMapT Q Λ hQ (twoPieceEnd Q Λ b hα' g)
        (splitStandardEquiv Q Λ hQ b hα' hα M y) := by
  apply (splitStandardEquiv Q Λ hQ b hα' hα M).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  change _ = splitStandardTo Q Λ hQ b hα' hα M (parabolicStandardMapT Q Λ hQ
    (twoPieceEnd Q Λ b hα' g) (splitStandardEquiv Q Λ hQ b hα' hα M y))
  rw [← LinearMap.comp_apply, splitStandardTo_twoPieceEnd, LinearMap.comp_apply]
  change _ = BalancedTensor.mapRight (k := k) (B := TensorProductAlgebra k Q Λ
    (initWeight b + lastBlock b)) (M := L) g ((splitStandardEquiv Q Λ hQ b hα' hα M).symm
      (splitStandardEquiv Q Λ hQ b hα' hα M y))
  rw [LinearEquiv.symm_apply_apply]

end StendhalAlgebra

end Categorification.Stendhal

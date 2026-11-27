/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiTopEquiv
import Categorification.WeightedKLR.RedStrands.EiInductionAction
import Categorification.Algebra.TensorActSplit

/-!
# `₁Fᵢ` of the two-piece input is the module of the induction hypothesis

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5, `F`-part. For a right module `M` over the block algebra of `ℓ + 1` red strands,
with `θ` the weight of the first `ℓ` red strands and `β` the last block, inducing the input
`X_M = M ⊗_{B'} S^L_{α'}` of the two-piece standardization along the last black strand of the
first factor gives `Fᵢ(M|_{B'} ⊗_{B'} S^L_{α'})`, the module to which the induction hypothesis
applies, with the last cyclotomic factor acting through `M` (`fiLeftInputEquiv`). The
isomorphism is natural in endomorphisms of `M` (`fiLeftInputEquiv_natural`).
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra MulOpposite InductionAlong
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace StendhalAlgebra

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I)
  (b : Fin (ℓ + 2) → Multiset I)
  (M : Type) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  (hα₁ : RootNonViolated (ν := initWeight b) (blockRoot (initBlocks b)))
  (C : Type) [Ring C] [Algebra k C] (ρ : C →ₐ[k] Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M)

local notation "Cyc" =>
  CycKLR k Q (fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i) (lastBlock b)
local notation "Tθ" => TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) (initWeight b)
local notation "Tiθ" =>
  TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) ((Singleton.singleton i : Multiset I) + initWeight b)
local notation "XL" => LeftStandardization Q (Λ ∘ Fin.castSucc) (initBlocks b) rfl hα₁
  (InitRestrict Q Λ b M)
local notation "X" => TwoPieceInput Q Λ b M hα₁
local notation "ofX" => twoPieceInputOf Q Λ b M hα₁
local notation "mR" => BalancedTensor.mapRight (k := k) (B := Tθ)
  (M := BlockLeftStandard Q (Λ ∘ Fin.castSucc) (initBlocks b) rfl hα₁)
local notation "φ₁" => appendBlackNU (Q := Q) (Λ := Λ ∘ Fin.castSucc) i (initWeight b)
local notation "ψ₁" => leftAppendHom Q Λ i (initWeight b) (lastBlock b)
local notation "El" => FirstIndLeft Q Λ i (initWeight b) (lastBlock b) X
local notation "ρ₁" => inductionAction Q Λ b M (rfl : lastBlock b = lastBlock b) C ρ
local notation "ρtop" => fiTopAction Q i (Λ ∘ Fin.castSucc) (initBlocks b) (initWeight b) rfl hα₁
  (Cyc ⊗[k] C) (InitRestrict Q Λ b M) ρ₁
local notation "Y₁" => TensorAct k Tiθ (Cyc ⊗[k] C) ρtop
local notation "SY" => SplitLeft k Tiθ Cyc C Y₁

theorem leftAppendHom_tmul_appendBlackNU (t : Tθ) (c : Cyc) :
    ψ₁ (t ⊗ₜ c) = φ₁ t ⊗ₜ c := rfl

/-- The restriction of `X_M` to the first factor `T^{λ'}(θ)` is `M|_{B'} ⊗_{B'} S^L_{α'}`. -/
def twoPieceLeftFactorEquiv : LeftFactorRes k Tθ Cyc X ≃ₗ[Tθ] XL where
  toFun x := (ofX).symm (show X from x)
  invFun y := (show LeftFactorRes k Tθ Cyc X from ofX y)
  map_add' x y := map_add (ofX).symm (show X from x) (show X from y)
  map_smul' t x := by
    obtain ⟨y, rfl⟩ := (ofX).surjective (show X from x)
    change (ofX).symm ((t ⊗ₜ (1 : Cyc) : parabolicFactorAlgebra Q Λ (initWeight b) (lastBlock b)) •
      ofX y) = t • (ofX).symm (ofX y)
    rw [twoPieceInput_smul_def, twoPieceInputAction_tmul, lastFactorEnd_one,
      BalancedTensor.mapRight_id, LinearMap.id_apply, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply]
  left_inv x := (ofX).apply_symm_apply (show X from x)
  right_inv y := (ofX).symm_apply_apply y

/-- The underlying additive map of `₁Fᵢ X_M ≅ Fᵢ(M|_{B'} ⊗ S^L_{α'})`. -/
def fiLeftInputFun : El ≃+ IndK k XL φ₁ :=
  (indLeftFactorEquiv φ₁ (appendBlackNU_smul Q i (Λ ∘ Fin.castSucc) (initWeight b)) ψ₁
    (leftAppendHom_tmul_appendBlackNU Q Λ i b) : El ≃ₗ[k] _).toAddEquiv.trans
    (Ind.mapEquiv (twoPieceLeftFactorEquiv Q Λ b M hα₁)).toAddEquiv

theorem fiLeftInputFun_apply (w : El) :
    fiLeftInputFun Q Λ i b M hα₁ w = Ind.mapEquiv (twoPieceLeftFactorEquiv Q Λ b M hα₁)
      (indLeftFactorEquiv φ₁ (appendBlackNU_smul Q i (Λ ∘ Fin.castSucc) (initWeight b)) ψ₁
        (leftAppendHom_tmul_appendBlackNU Q Λ i b) w) := rfl

theorem fiLeftInputFun_tmul_one (t : Tiθ) (w : El) :
    fiLeftInputFun Q Λ i b M hα₁
        ((t ⊗ₜ (1 : Cyc) : parabolicFactorAlgebra Q Λ (({i} : Multiset I) + initWeight b)
          (lastBlock b)) • w) =
      t • fiLeftInputFun Q Λ i b M hα₁ w := by
  rw [fiLeftInputFun_apply, indLeftFactorEquiv_tmul_one_smul φ₁
    (appendBlackNU_smul Q i (Λ ∘ Fin.castSucc) (initWeight b)) ψ₁
    (leftAppendHom_tmul_appendBlackNU Q Λ i b) t w]
  exact map_smul (Ind.mapEquiv (twoPieceLeftFactorEquiv Q Λ b M hα₁)) t _

theorem fiLeftInputFun_one_tmul (c : Cyc) (w : El) :
    fiLeftInputFun Q Λ i b M hα₁
        (((1 : Tiθ) ⊗ₜ c : parabolicFactorAlgebra Q Λ (({i} : Multiset I) + initWeight b)
          (lastBlock b)) • w) =
      IndK.map (mR (lastFactorEnd Q Λ b c)) (fiLeftInputFun Q Λ i b M hα₁ w) := by
  rw [fiLeftInputFun_apply, indLeftFactorEquiv_one_tmul_smul φ₁
    (appendBlackNU_smul Q i (Λ ∘ Fin.castSucc) (initWeight b)) ψ₁
    (leftAppendHom_tmul_appendBlackNU Q Λ i b) c w]
  refine IndK.map_comm_apply (k := k)
    (e := (twoPieceLeftFactorEquiv Q Λ b M hα₁).toLinearMap) (fun x => ?_) _
  obtain ⟨y, rfl⟩ := (ofX).surjective (show X from x)
  change (ofX).symm (((1 : Tθ) ⊗ₜ c : parabolicFactorAlgebra Q Λ (initWeight b) (lastBlock b)) •
    ofX y) = mR (lastFactorEnd Q Λ b c) ((ofX).symm (ofX y))
  rw [twoPieceInput_smul_def, twoPieceInputAction_tmul, one_smul, LinearEquiv.symm_apply_apply,
    LinearEquiv.symm_apply_apply]

theorem fiLeftInputFun_natural (g : Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M) (w : El) :
    fiLeftInputFun Q Λ i b M hα₁ (IndK.map (twoPieceEnd Q Λ b hα₁ g) w) =
      IndK.map (mR (initRestrictEnd Q Λ b g)) (fiLeftInputFun Q Λ i b M hα₁ w) := by
  rw [fiLeftInputFun_apply, fiLeftInputFun_apply, indLeftFactorEquiv_map φ₁
    (appendBlackNU_smul Q i (Λ ∘ Fin.castSucc) (initWeight b)) ψ₁
    (leftAppendHom_tmul_appendBlackNU Q Λ i b) (twoPieceEnd Q Λ b hα₁ g) w]
  refine IndK.map_comm_apply (k := k)
    (e := (twoPieceLeftFactorEquiv Q Λ b M hα₁).toLinearMap) (fun x => ?_) _
  obtain ⟨y, rfl⟩ := (ofX).surjective (show X from x)
  change (ofX).symm (twoPieceEnd Q Λ b hα₁ g (ofX y)) =
    mR (initRestrictEnd Q Λ b g) ((ofX).symm (ofX y))
  rw [twoPieceEnd_of, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

local notation "D'" => parabolicFactorAlgebra Q Λ
  ((Singleton.singleton i : Multiset I) + initWeight b) (lastBlock b)

theorem fiTopAction_tmul_one_eq (c : Cyc) (x : IndK k XL φ₁) :
    ρtop (c ⊗ₜ 1) x = IndK.map (mR (lastFactorEnd Q Λ b c)) x := by
  change IndK.map (mR (ρ₁ (c ⊗ₜ 1))) x = _
  rw [inductionAction_tmul_one]
  rfl

theorem fiTopAction_one_tmul_eq (c : C) (x : IndK k XL φ₁) :
    ρtop (1 ⊗ₜ c) x = IndK.map (mR (initRestrictEnd Q Λ b (ρ c))) x := by
  change IndK.map (mR (ρ₁ (1 ⊗ₜ c))) x = _
  rw [inductionAction_one_tmul]

/-- The underlying additive map of `₁Fᵢ X_M ≅ Fᵢ(M|_{B'} ⊗ S^L_{α'})`, into the split module. -/
def fiLeftInputHom : El →+ SY :=
  ((SplitLeft.of : Y₁ ≃+ SY).toAddMonoidHom.comp
    (TensorAct.of (k := k) (A := Tiθ) (C := Cyc ⊗[k] C) (ρ := ρtop)).toAddMonoidHom).comp
    (fiLeftInputFun Q Λ i b M hα₁).toAddMonoidHom

theorem fiLeftInputHom_apply (w : El) :
    fiLeftInputHom Q Λ i b M hα₁ C ρ w =
      (SplitLeft.of : Y₁ ≃+ SY) (TensorAct.of (ρ := ρtop) (fiLeftInputFun Q Λ i b M hα₁ w)) :=
  rfl

theorem fiLeftInputHom_tmul_one (t : Tiθ) (w : El) :
    fiLeftInputHom Q Λ i b M hα₁ C ρ ((t ⊗ₜ 1 : D') • w) =
      (t ⊗ₜ 1 : D') • fiLeftInputHom Q Λ i b M hα₁ C ρ w :=
  (congrArg (fun u => SplitLeft.of (k := k) (A₁ := Tiθ) (A₂ := Cyc) (C := C)
      (TensorAct.of (ρ := ρtop) u)) (fiLeftInputFun_tmul_one Q Λ i b M hα₁ t w)).trans
    (SplitLeft.tmul_one_smul_of_of (C := C) ρtop t _).symm

theorem fiLeftInputHom_one_tmul (c : Cyc) (w : El) :
    fiLeftInputHom Q Λ i b M hα₁ C ρ ((1 ⊗ₜ c : D') • w) =
      (1 ⊗ₜ c : D') • fiLeftInputHom Q Λ i b M hα₁ C ρ w :=
  (congrArg (fun u => SplitLeft.of (k := k) (A₁ := Tiθ) (A₂ := Cyc) (C := C)
      (TensorAct.of (ρ := ρtop) u)) ((fiLeftInputFun_one_tmul Q Λ i b M hα₁ c w).trans
        (fiTopAction_tmul_one_eq Q Λ i b M hα₁ C ρ c _).symm)).trans
    (SplitLeft.one_tmul_smul_of_of (C := C) ρtop c _).symm

/-- **`₁Fᵢ X_M ≅ Fᵢ(M|_{B'} ⊗ S^L_{α'})` as modules over `T^{λ'}(i + θ) ⊗ R(β)`.** -/
def fiLeftInputEquiv : El ≃ₗ[D'] SY :=
  LinearEquiv.ofBijective
    (tensorLinearOfGenerators (A := Tiθ) (C := Cyc) (fiLeftInputHom Q Λ i b M hα₁ C ρ)
      (fiLeftInputHom_tmul_one Q Λ i b M hα₁ C ρ) (fiLeftInputHom_one_tmul Q Λ i b M hα₁ C ρ))
    ((SplitLeft.of : Y₁ ≃+ SY).bijective.comp
      ((TensorAct.of (k := k) (A := Tiθ) (C := Cyc ⊗[k] C) (ρ := ρtop)).bijective.comp
        (fiLeftInputFun Q Λ i b M hα₁).bijective))

theorem fiLeftInputEquiv_apply (w : El) :
    fiLeftInputEquiv Q Λ i b M hα₁ C ρ w =
      (SplitLeft.of : Y₁ ≃+ SY) (TensorAct.of (ρ := ρtop) (fiLeftInputFun Q Λ i b M hα₁ w)) :=
  rfl

/-- **`fiLeftInputEquiv` intertwines the actions of `C`.** -/
theorem fiLeftInputEquiv_natural (c : C) (w : El) :
    fiLeftInputEquiv Q Λ i b M hα₁ C ρ
        (fiLeftAction Q Λ i (initWeight b) (lastBlock b) C ((twoPieceEndAlg Q Λ b hα₁).comp ρ)
          c w) =
      SplitLeft.action Y₁ c (fiLeftInputEquiv Q Λ i b M hα₁ C ρ w) :=
  (congrArg (fun u => SplitLeft.of (k := k) (A₁ := Tiθ) (A₂ := Cyc) (C := C)
      (TensorAct.of (ρ := ρtop) u)) ((fiLeftInputFun_natural Q Λ i b M hα₁ (ρ c) w).trans
        (fiTopAction_one_tmul_eq Q Λ i b M hα₁ C ρ c _).symm)).trans
    (SplitLeft.action_of_of (A₂ := Cyc) ρtop c _).symm

end StendhalAlgebra

end Categorification.Stendhal

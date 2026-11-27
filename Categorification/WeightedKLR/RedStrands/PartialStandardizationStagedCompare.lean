/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationStagedCasts
import Categorification.WeightedKLR.RedStrands.PartialStandardizationStagedZero
import Categorification.WeightedKLR.RedStrands.EiStepOne

/-!
# The standardization in stages is the standardization of Definition 5.4

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1,
Definition 5.4 and proof of Proposition 5.5. Let `b_0 = 0, b_1, …, b_n` be blocks and `M` a
right module over the block algebra `B = R(b_0) ⊗ R^{λ_1}(b_1) ⊗ ⋯ ⊗ R^{λ_n}(b_n)`, with a
commuting action `ρ` of a spectator algebra `E`. Regard `M` as a module `Z` over the algebra of
the singleton blocks `T^{λ_1}(b_1) ⊗ ⋯ ⊗ T^{λ_n}(b_n)` (through `singBlockHom`) and `E`. Then the
standardization in stages of `Z` (`singStd`) is the standardization `M ⊗_B S^L_α` of
Definition 5.4, compatibly with the actions of `T^λ` and of `E` (`stagedComparison`, a
`StagedComparison`).

The comparison is built by induction on the number of red strands. With no red strands it is
`leftStandardizationZeroEquiv` (`stagedComparisonZero`). For `n + 1` red strands, the first
stage gives `X_M = M ⊗_{B'} S^L_{α'}` by induction (`lastStageInputEquiv`); the last stage, the
partial standardization of `X_M` at the cut before the last red strand, is its parabolic
standardization (`cutParabolicTransfer`), which is `M ⊗_B S^L_α` by `splitStandardEquiv`
(`stagedStepEquiv`, `stagedComparisonSucc`).
-/

noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace Categorification.Stendhal

open CategoryTheory KLR MulOpposite StendhalAlgebra
open scoped TensorProduct

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

variable {I : Type} [DecidableEq I] {k : Type} [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q)

/-- **A comparison of the standardization in stages with Definition 5.4**: an additive
isomorphism `S_staged(Z) ≅ M ⊗_B S^L_α` intertwining the actions of `T^λ` (through the
identification of the black weights) and of the spectator `E`. -/
structure StagedComparison (n : ℕ) (Λ : Fin n → I →₀ ℕ) (b : Fin (n + 1) → Multiset I)
    (θ : Fin n → Multiset I) {ν : Multiset I} (hb : blockPrefix b (n + 1) = ν)
    (hw : singWeight n θ = ν)
    (hα : RootNonViolated (ν := ν) (blockRoot b)) (E : AlgCat.{0} k) (M : Type)
    [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
    [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
    (ρ : E →ₐ[k] Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M)
    (Z : ModuleCat.{0} (singAlg Q n Λ θ ⊗[k] E)) where
  /-- The underlying additive isomorphism. -/
  equiv : (singStd Q hQ n Λ θ E).obj Z ≃+ LeftStandardization Q Λ b hb hα M
  smul_left (t : TensorProductAlgebra k Q Λ (singWeight n θ))
    (x : (singStd Q hQ n Λ θ E).obj Z) :
    equiv ((t ⊗ₜ[k] (1 : E)) • x) = castTensorProductAlgebra Q Λ hw t • equiv x
  smul_right (e : E) (x : (singStd Q hQ n Λ θ E).obj Z) :
    equiv (((1 : TensorProductAlgebra k Q Λ (singWeight n θ)) ⊗ₜ[k] e) • x) =
      BalancedTensor.mapRight (k := k) (B := TensorProductAlgebra k Q Λ ν)
        (M := BlockLeftStandard Q Λ b hb hα) (ρ e) (equiv x)

namespace StagedComparison

variable {Q hQ} {n : ℕ} {Λ : Fin n → I →₀ ℕ} {b : Fin (n + 1) → Multiset I}
  {θ : Fin n → Multiset I} {ν : Multiset I} {hb : blockPrefix b (n + 1) = ν}
  {hw : singWeight n θ = ν}
  {hα : RootNonViolated (ν := ν) (blockRoot b)} {E : AlgCat.{0} k} {M : Type}
  [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  {ρ : E →ₐ[k] Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M}
  {Z : ModuleCat.{0} (singAlg Q n Λ θ ⊗[k] E)}

/-- The comparison is linear over the ground field. -/
theorem equiv_smul (C : StagedComparison Q hQ n Λ b θ hb hw hα E M ρ Z) (c : k)
    (x : (singStd Q hQ n Λ θ E).obj Z) : C.equiv (c • x) = c • C.equiv x := by
  have h : c • x = (algebraMap k (TensorProductAlgebra k Q Λ (singWeight n θ)) c ⊗ₜ[k]
      (1 : E)) • x := rfl
  rw [h, C.smul_left, AlgEquiv.commutes, algebraMap_smul]

/-- The comparison as a linear isomorphism. -/
def linearEquiv (C : StagedComparison Q hQ n Λ b θ hb hw hα E M ρ Z) :
    (singStd Q hQ n Λ θ E).obj Z ≃ₗ[k] LeftStandardization Q Λ b hb hα M :=
  { C.equiv with map_smul' := C.equiv_smul }

end StagedComparison

/-- `singBlockHom` along an identification `b ∘ succ = θ` of the singleton weights. -/
def singBlockHomOf (n : ℕ) (Λ : Fin n → I →₀ ℕ) (b : Fin (n + 1) → Multiset I)
    {θ : Fin n → Multiset I} (hθ : b ∘ Fin.succ = θ) :
    singAlg Q n Λ θ →ₐ[k] (BlockAlgebra k Q Λ b)ᵐᵒᵖ :=
  hθ ▸ singBlockHom Q n Λ b

section Base

variable (Λ : Fin 0 → I →₀ ℕ) (b : Fin 1 → Multiset I) (θ : Fin 0 → Multiset I) (hb0 : b 0 = 0)
  {ν : Multiset I}
  (hb : blockPrefix b 1 = ν) (hw : singWeight 0 θ = ν)
  (hα : RootNonViolated (ν := ν) (blockRoot b)) (E : AlgCat.{0} k) {M : Type}
  [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  (ρ : E →ₐ[k] Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M)
  (Z : ModuleCat.{0} (singAlg Q 0 Λ θ ⊗[k] E)) (ψ : Z ≃+ M)
  (hψl : ∀ (s : singAlg Q 0 Λ θ) (z : Z),
    ψ ((s ⊗ₜ[k] (1 : E)) • z) = singBlockHom Q 0 Λ b s • ψ z)
  (hψr : ∀ (e : E) (z : Z), ψ (((1 : singAlg Q 0 Λ θ) ⊗ₜ[k] e) • z) = ρ e (ψ z))

/-- **The comparison with no red strands.** -/
def stagedComparisonZero : StagedComparison Q hQ 0 Λ b θ hb hw hα E M ρ Z := by
  obtain rfl : ν = 0 := hw.symm
  exact
    { equiv := ψ.trans (leftStandardizationZeroEquiv Q Λ b hb0 hb hα M).symm.toAddEquiv
      smul_left := fun t x => by
        change (leftStandardizationZeroEquiv Q Λ b hb0 hb hα M).symm (ψ ((t ⊗ₜ[k] (1 : E)) • x)) =
          castTensorProductAlgebra Q Λ hw t •
            (leftStandardizationZeroEquiv Q Λ b hb0 hb hα M).symm (ψ x)
        have h1 := leftStandardizationZeroEquiv_smul Q Λ b hb0 hb hα M
          (show TensorProductAlgebra k Q Λ 0 from t)
          ((leftStandardizationZeroEquiv Q Λ b hb0 hb hα M).symm (ψ x))
        rw [LinearEquiv.apply_symm_apply] at h1
        have h2 : ψ ((t ⊗ₜ[k] (1 : E)) • x) =
            tensorProductAlgebraZeroEquiv Q Λ (show TensorProductAlgebra k Q Λ 0 from t) • ψ x :=
          (hψl t (show Z from x)).trans ((congrArg (· • ψ x) (singBlockHom_zero Q Λ b t)).trans
            (algebraMap_smul (BlockAlgebra k Q Λ b)ᵐᵒᵖ _ (ψ x)))
        apply (leftStandardizationZeroEquiv Q Λ b hb0 hb hα M).injective
        exact (LinearEquiv.apply_symm_apply _ _).trans (h2.trans h1.symm)
      smul_right := fun e x => by
        change (leftStandardizationZeroEquiv Q Λ b hb0 hb hα M).symm
            (ψ (((1 : TensorProductAlgebra k Q Λ (singWeight 0 θ)) ⊗ₜ[k] e) • x)) =
          BalancedTensor.mapRight (k := k) (B := TensorProductAlgebra k Q Λ 0)
            (M := BlockLeftStandard Q Λ b hb hα) (ρ e)
            ((leftStandardizationZeroEquiv Q Λ b hb0 hb hα M).symm (ψ x))
        apply (leftStandardizationZeroEquiv Q Λ b hb0 hb hα M).injective
        rw [leftStandardizationZeroEquiv_mapRight, LinearEquiv.apply_symm_apply,
          LinearEquiv.apply_symm_apply]
        exact hψr e x }

end Base

theorem tensorProductAlgebraCast_symm_apply {m : ℕ} {Λ₁ Λ₂ : Fin m → I →₀ ℕ} (h : Λ₁ = Λ₂)
    (ν : Multiset I) (t : TensorProductAlgebra k Q Λ₂ ν) :
    (tensorProductAlgebraCast Q h ν).symm t = tensorProductAlgebraCast Q h.symm ν t := by
  subst h
  rfl

theorem cutParabolicFactorEquiv_tmul {m : ℕ} (Λ : Fin (m + 1) → I →₀ ℕ) {θ ν : Multiset I}
    (β : Multiset I) (hw : θ = ν) (t : TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) θ)
    (c : TensorProductAlgebra k Q (Λ ∘ Fin.natAdd m) β) :
    cutParabolicFactorEquiv Q Λ β hw (t ⊗ₜ[k] c) =
      castTensorProductAlgebra Q (Λ ∘ Fin.castSucc) hw t ⊗ₜ[k]
        (SingleRed.cyclotomicEquiv Q (fun _ : Fin 1 => Λ (Fin.last m)) β).symm
          ((tensorProductAlgebraCast Q (congrArg (Λ ∘ ·) (lastIndex_eq_natAdd (ℓ := m))) β).symm
            c) := rfl

section Step

variable (n : ℕ) (Λ : Fin (n + 1) → I →₀ ℕ) (b : Fin (n + 2) → Multiset I)
  (E : AlgCat.{0} k) {M : Type}
  [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  (ρ : E →ₐ[k] Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M)
  (Z : ModuleCat.{0} (singAlg Q (n + 1) Λ (b ∘ Fin.succ) ⊗[k] E)) (ψ : Z ≃+ M)
  (hψl : ∀ (s : singAlg Q (n + 1) Λ (b ∘ Fin.succ)) (z : Z),
    ψ ((s ⊗ₜ[k] (1 : E)) • z) = singBlockHom Q (n + 1) Λ b s • ψ z)
  (hψr : ∀ (e : E) (z : Z),
    ψ (((1 : singAlg Q (n + 1) Λ (b ∘ Fin.succ)) ⊗ₜ[k] e) • z) = ρ e (ψ z))

/-- The spectator of the first stage. -/
abbrev initSpect : AlgCat.{0} k := AlgCat.of k (singLast Q Λ (b ∘ Fin.succ) ⊗[k] E)

/-- The module of the first stage: `Z` over the first `n` singleton blocks and the spectator
`T^{λ_{n+1}}(b_{n+1}) ⊗ E`. -/
abbrev initStageModule : ModuleCat.{0}
    (singAlg Q n (Λ ∘ Fin.castSucc) ((b ∘ Fin.succ) ∘ Fin.castSucc) ⊗[k] initSpect Q n Λ b E) :=
  (ModuleCat.restrictScalars.{0} (singAssocIn Q n Λ (b ∘ Fin.succ) E)).obj Z

/-- `ψ` on the module of the first stage. -/
def initStageEquiv : initStageModule Q n Λ b E Z ≃+ InitRestrict Q Λ b M := ψ

omit [Module k M] [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M] in
include hψl in
theorem initStageEquiv_smul_left
    (s : singAlg Q n (Λ ∘ Fin.castSucc) ((b ∘ Fin.succ) ∘ Fin.castSucc))
    (z : initStageModule Q n Λ b E Z) :
    initStageEquiv Q n Λ b E Z ψ ((s ⊗ₜ[k] (1 : initSpect Q n Λ b E)) • z) =
      singBlockHom Q n (Λ ∘ Fin.castSucc) (initBlocks b) s • initStageEquiv Q n Λ b E Z ψ z := by
  refine (hψl (s ⊗ₜ[k] (1 : singLast Q Λ (b ∘ Fin.succ))) (show Z from z)).trans ?_
  rw [singBlockHom_succ_tmul, map_one, mul_one]
  rfl

include hψl hψr in
theorem initStageEquiv_smul_right (e' : initSpect Q n Λ b E) (z : initStageModule Q n Λ b E Z) :
    initStageEquiv Q n Λ b E Z ψ
        (((1 : singAlg Q n (Λ ∘ Fin.castSucc) ((b ∘ Fin.succ) ∘ Fin.castSucc)) ⊗ₜ[k] e') • z) =
      initSpectatorAction Q n Λ b E ρ e' (initStageEquiv Q n Λ b E Z ψ z) := by
  induction e' using TensorProduct.inductionOn with
  | tmul c e =>
    let s1 : singAlg Q (n + 1) Λ (b ∘ Fin.succ) :=
      (1 : singAlg Q n (Λ ∘ Fin.castSucc) ((b ∘ Fin.succ) ∘ Fin.castSucc)) ⊗ₜ[k] c
    let s0 : singAlg Q (n + 1) Λ (b ∘ Fin.succ) := 1
    have h : initStageEquiv Q n Λ b E Z ψ
        (((1 : singAlg Q n (Λ ∘ Fin.castSucc) ((b ∘ Fin.succ) ∘ Fin.castSucc)) ⊗ₜ[k]
          ((c ⊗ₜ[k] e : singLast Q Λ (b ∘ Fin.succ) ⊗[k] E) : initSpect Q n Λ b E)) • z) =
        ψ ((s1 ⊗ₜ[k] (1 : E)) • (s0 ⊗ₜ[k] e) • (show Z from z)) := by
      change ψ (singAssocIn Q n Λ (b ∘ Fin.succ) E _ • (show Z from z)) = _
      rw [← mul_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      rfl
    rw [h, hψl, hψr, singBlockHom_succ_tmul, map_one, map_one, one_mul, singLastBlockHom_eq,
      initSpectatorAction_tmul, Module.End.mul_apply]
    rfl
  | add x y hx hy =>
    let S := singAlg Q n (Λ ∘ Fin.castSucc) ((b ∘ Fin.succ) ∘ Fin.castSucc)
    let ax : S ⊗[k] initSpect Q n Λ b E := (1 : S) ⊗ₜ[k] x
    let ay : S ⊗[k] initSpect Q n Λ b E := (1 : S) ⊗ₜ[k] y
    have e1 : ((1 : S) ⊗ₜ[k] (x + y) : S ⊗[k] initSpect Q n Λ b E) = ax + ay :=
      TensorProduct.tmul_add _ _ _
    have e2 : ((ax + ay) • z : initStageModule Q n Λ b E Z) = ax • z + ay • z := add_smul _ _ _
    rw [e1, e2, map_add, hx, hy, map_add, LinearMap.add_apply]

/-- The input of the last stage: the result of the first stage, over the factor algebra of the
cut before the last red strand and the spectator `E`. -/
abbrev lastStageInput : ModuleCat.{0} (cutSpectAlgebra (a := n) (r := 1) Q Λ
    (singWeight n ((b ∘ Fin.succ) ∘ Fin.castSucc)) ((b ∘ Fin.succ) (Fin.last n)) E) :=
  (ModuleCat.restrictScalars.{0} (singAssocOut Q n Λ (b ∘ Fin.succ) E)).obj
    ((singStd Q hQ n (Λ ∘ Fin.castSucc) ((b ∘ Fin.succ) ∘ Fin.castSucc) (initSpect Q n Λ b E)).obj
      (initStageModule Q n Λ b E Z))

variable (hb0 : leftBlock b = 0)

/-- The comparison of the first stage, as the induction hypothesis. -/
abbrev InitComparison :=
  StagedComparison Q hQ n (Λ ∘ Fin.castSucc) (initBlocks b)
    ((b ∘ Fin.succ) ∘ Fin.castSucc) (ν := initWeight b) rfl
    (singWeight_eq_blockPrefix n (initBlocks b) hb0) (rootNonViolated_initBlocks hb0)
    (initSpect Q n Λ b E) (InitRestrict Q Λ b M) (initSpectatorAction Q n Λ b E ρ)
    (initStageModule Q n Λ b E Z)

variable {Q hQ n Λ b E ρ Z hb0}

local notation "θ₀" => singWeight n ((b ∘ Fin.succ) ∘ Fin.castSucc)
local notation "β₀" => (b ∘ Fin.succ) (Fin.last n)

/-- **The input of the last stage is `X_M`**, the standardization of `M` over the first red
strands with the last factor acting through `M`. -/
def lastStageInputEquiv (C : InitComparison Q hQ n Λ b E ρ Z hb0) :
    CutSpectInput (a := n) (r := 1) Q Λ θ₀ β₀ E (lastStageInput Q hQ n Λ b E Z) ≃ₗ[k]
      TwoPieceInput Q Λ b M (rootNonViolated_initBlocks hb0) :=
  { C.equiv with
    map_smul' := fun c x => by
      change C.equiv (singAssocOut Q n Λ (b ∘ Fin.succ) E (algebraMap k _ c) •
        (show (singStd Q hQ n (Λ ∘ Fin.castSucc) ((b ∘ Fin.succ) ∘ Fin.castSucc)
          (initSpect Q n Λ b E)).obj (initStageModule Q n Λ b E Z) from x)) = c • C.equiv x
      rw [show singAssocOut Q n Λ (b ∘ Fin.succ) E (algebraMap k _ c) = algebraMap k _ c from
        AlgHom.commutes _ c]
      exact C.equiv_smul c _ }

theorem lastStageInputEquiv_apply (C : InitComparison Q hQ n Λ b E ρ Z hb0)
    (x : CutSpectInput (a := n) (r := 1) Q Λ θ₀ β₀ E (lastStageInput Q hQ n Λ b E Z)) :
    lastStageInputEquiv C x = C.equiv x := rfl

/-- `X_M` over the parabolic factor algebra, with the last block written `b_{n+1}`. -/
abbrev twoPieceInputModuleSucc
    (hα' : RootNonViolated (ν := initWeight b) (blockRoot (initBlocks b))) :
    Module (parabolicFactorAlgebra Q Λ (initWeight b) β₀) (TwoPieceInput Q Λ b M hα') :=
  inferInstanceAs (Module (parabolicFactorAlgebra Q Λ (initWeight b) (lastBlock b)) _)

attribute [local instance] twoPieceInputModuleSucc

/-- The scalar tower for `twoPieceInputModuleSucc`. -/
theorem twoPieceInput_isScalarTower_succ
    (hα' : RootNonViolated (ν := initWeight b) (blockRoot (initBlocks b))) :
    IsScalarTower k (parabolicFactorAlgebra Q Λ (initWeight b) β₀)
      (TwoPieceInput Q Λ b M hα') :=
  inferInstanceAs (IsScalarTower k (parabolicFactorAlgebra Q Λ (initWeight b) (lastBlock b)) _)

attribute [local instance] twoPieceInput_isScalarTower_succ

/-- **`X_M` intertwines the factor algebras of the cut and of the parabolic model.** -/
theorem lastStageInputEquiv_smul (C : InitComparison Q hQ n Λ b E ρ Z hb0)
    (d : cutFactorAlgebra (a := n) (r := 1) Q Λ θ₀ β₀)
    (x : CutSpectInput (a := n) (r := 1) Q Λ θ₀ β₀ E (lastStageInput Q hQ n Λ b E Z)) :
    lastStageInputEquiv C (d • x) =
      cutParabolicFactorEquiv Q Λ β₀ (singWeight_eq_blockPrefix n (initBlocks b) hb0) d •
        lastStageInputEquiv C x := by
  induction d using TensorProduct.inductionOn with
  | tmul t c =>
    let S := TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) θ₀
    let y : (singStd Q hQ n (Λ ∘ Fin.castSucc) ((b ∘ Fin.succ) ∘ Fin.castSucc)
        (initSpect Q n Λ b E)).obj (initStageModule Q n Λ b E Z) := x
    let e1 : initSpect Q n Λ b E := (c ⊗ₜ[k] (1 : E) : singLast Q Λ (b ∘ Fin.succ) ⊗[k] E)
    have h : lastStageInputEquiv C
        ((t ⊗ₜ[k] c : cutFactorAlgebra (a := n) (r := 1) Q Λ θ₀ β₀) • x) =
        C.equiv ((t ⊗ₜ[k] (1 : initSpect Q n Λ b E)) • ((1 : S) ⊗ₜ[k] e1) • y) := by
      change C.equiv (singAssocOut Q n Λ (b ∘ Fin.succ) E ((t ⊗ₜ[k] c) ⊗ₜ[k] (1 : E)) • y) = _
      rw [← mul_smul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rfl
    have h3 : initSpectatorAction Q n Λ b E ρ e1 = lastFactorEnd Q Λ b (singLastCyc Q n Λ b c) :=
      (initSpectatorAction_tmul Q n Λ b E ρ c 1).trans (by
        rw [map_one]
        exact mul_one _)
    have h4 : singLastCyc Q n Λ b c =
        (SingleRed.cyclotomicEquiv Q (fun _ : Fin 1 => Λ (Fin.last n)) (lastBlock b)).symm
          ((tensorProductAlgebraCast Q (congrArg (Λ ∘ ·) (lastIndex_eq_natAdd (ℓ := n)))
            (lastBlock b)).symm c) := by
      rw [tensorProductAlgebraCast_symm_apply]
      rfl
    refine h.trans ((C.smul_left t _).trans ((congrArg (_ • ·) (C.smul_right e1 y)).trans ?_))
    rw [h3, h4]
    exact (twoPieceInputAction_tmul (M := M) Q Λ b (rootNonViolated_initBlocks hb0) _ _ _).symm
  | add d d' hd hd' => rw [add_smul, map_add, hd, hd', map_add, add_smul]


/-- The root condition at the total weight written `b_0 + ⋯ + b_n + b_{n+1}`. -/
theorem rootNonViolated_blockPrefix_last {ν : Multiset I} (hb : blockPrefix b (n + 2) = ν)
    (hα : RootNonViolated (ν := ν) (blockRoot b)) :
    RootNonViolated (ν := initWeight b + lastBlock b) (blockRoot b) := by
  subst hb
  exact blockPrefix_last b ▸ hα

local notation "N₁" =>
  CutSpectInput (a := n) (r := 1) Q Λ θ₀ β₀ E (lastStageInput Q hQ n Λ b E Z)

/-- **The comparison of the last stage**: the partial standardization of `X_M` at the last cut
is `M ⊗_B S^L_α`, through the parabolic model and `splitStandardEquiv`. -/
def stagedStepEquiv (C : InitComparison Q hQ n Λ b E ρ Z hb0) {ν : Multiset I}
    (hb : blockPrefix b (n + 2) = ν) (hα : RootNonViolated (ν := ν) (blockRoot b)) :
    CutStandard (a := n) (r := 1) Q Λ θ₀ β₀ N₁ ≃+ LeftStandardization Q Λ b hb hα M :=
  ((cutParabolicTransfer Q Λ (θ := θ₀) β₀ (singWeight_eq_blockPrefix n (initBlocks b) hb0)
      (lastStageInputEquiv C) (lastStageInputEquiv_smul C)).toAddEquiv.trans
    (splitStandardEquiv Q Λ hQ b (rootNonViolated_initBlocks hb0)
      (rootNonViolated_blockPrefix_last hb hα) M).symm.toAddEquiv).trans
    (leftStandardizationWeightCast Q (blockPrefix_last b) hb
      (rootNonViolated_blockPrefix_last hb hα) hα M).toAddEquiv

/-- The comparison of the last stage is linear over `T^λ`. -/
theorem stagedStepEquiv_action (C : InitComparison Q hQ n Λ b E ρ Z hb0) {ν : Multiset I}
    (hb : blockPrefix b (n + 2) = ν) (hw : singWeight (n + 1) (b ∘ Fin.succ) = ν)
    (hα : RootNonViolated (ν := ν) (blockRoot b))
    (t : TensorProductAlgebra k Q Λ (θ₀ + β₀)) (z : CutStandard (a := n) (r := 1) Q Λ θ₀ β₀ N₁) :
    stagedStepEquiv C hb hα (cutStandardAction (a := n) (r := 1) Q Λ θ₀ β₀ N₁ hQ t z) =
      castTensorProductAlgebra Q Λ hw t • stagedStepEquiv C hb hα z := by
  have hw' := singWeight_eq_blockPrefix n (initBlocks b) hb0
  have hα₁ := rootNonViolated_blockPrefix_last hb hα
  have h1 := cutParabolicTransfer_action Q Λ (θ := θ₀) β₀ hw' hQ (lastStageInputEquiv C)
    (lastStageInputEquiv_smul C) t z
  have h2 := (splitStandardEquiv Q Λ hQ b (rootNonViolated_initBlocks hb0) hα₁ M).symm.map_smul
    (castTensorProductAlgebra Q Λ (congrArg (· + β₀) hw') t)
    (show ParabolicStandardT Q Λ (initWeight b) (lastBlock b)
      (TwoPieceInput Q Λ b M (rootNonViolated_initBlocks hb0)) hQ from
      cutParabolicTransfer Q Λ (θ := θ₀) β₀ hw' (lastStageInputEquiv C)
        (lastStageInputEquiv_smul C) z)
  have h3 := leftStandardizationWeightCast_smul Q (blockPrefix_last b) hb hα₁ hα M
    (castTensorProductAlgebra Q Λ (congrArg (· + β₀) hw') t)
    ((splitStandardEquiv Q Λ hQ b (rootNonViolated_initBlocks hb0) hα₁ M).symm
      (cutParabolicTransfer Q Λ (θ := θ₀) β₀ hw' (lastStageInputEquiv C)
        (lastStageInputEquiv_smul C) z))
  change leftStandardizationWeightCast Q (blockPrefix_last b) hb hα₁ hα M
      ((splitStandardEquiv Q Λ hQ b (rootNonViolated_initBlocks hb0) hα₁ M).symm
        (cutParabolicTransfer Q Λ (θ := θ₀) β₀ hw' (lastStageInputEquiv C)
          (lastStageInputEquiv_smul C)
          (cutStandardAction (a := n) (r := 1) Q Λ θ₀ β₀ N₁ hQ t z))) = _
  rw [h1]
  refine (congrArg (leftStandardizationWeightCast Q (blockPrefix_last b) hb hα₁ hα M) h2).trans
    (h3.trans ?_)
  rw [castTensorProductAlgebra_trans]
  rfl

/-- The spectator acts on the input of the last stage through `X_{ρ(e)}`. -/
theorem lastStageInputEquiv_spectEnd (C : InitComparison Q hQ n Λ b E ρ Z hb0) (e : E)
    (y : N₁) :
    lastStageInputEquiv C
        (cutSpectEnd (a := n) (r := 1) Q Λ θ₀ β₀ E (lastStageInput Q hQ n Λ b E Z) e y) =
      twoPieceEnd Q Λ b (rootNonViolated_initBlocks hb0) (ρ e) (lastStageInputEquiv C y) := by
  let S := TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) θ₀
  let y' : (singStd Q hQ n (Λ ∘ Fin.castSucc) ((b ∘ Fin.succ) ∘ Fin.castSucc)
      (initSpect Q n Λ b E)).obj (initStageModule Q n Λ b E Z) := y
  let e1 : initSpect Q n Λ b E :=
    ((1 : singLast Q Λ (b ∘ Fin.succ)) ⊗ₜ[k] e : singLast Q Λ (b ∘ Fin.succ) ⊗[k] E)
  have h : lastStageInputEquiv C
      (cutSpectEnd (a := n) (r := 1) Q Λ θ₀ β₀ E (lastStageInput Q hQ n Λ b E Z) e y) =
      C.equiv (((1 : S) ⊗ₜ[k] e1) • y') := rfl
  rw [h, C.smul_right, initSpectatorAction_tmul, map_one, lastFactorEnd_one,
    ← Module.End.one_eq_id, one_mul]
  rfl

/-- The comparison of the last stage intertwines the spectator actions. -/
theorem stagedStepEquiv_spectEnd (C : InitComparison Q hQ n Λ b E ρ Z hb0) {ν : Multiset I}
    (hb : blockPrefix b (n + 2) = ν) (hα : RootNonViolated (ν := ν) (blockRoot b)) (e : E)
    (z : CutStandard (a := n) (r := 1) Q Λ θ₀ β₀ N₁) :
    stagedStepEquiv C hb hα (cutStandardMap (a := n) (r := 1) Q Λ θ₀ β₀
        (cutSpectEnd (a := n) (r := 1) Q Λ θ₀ β₀ E (lastStageInput Q hQ n Λ b E Z) e) z) =
      BalancedTensor.mapRight (k := k) (B := TensorProductAlgebra k Q Λ ν)
        (M := BlockLeftStandard Q Λ b hb hα) (ρ e) (stagedStepEquiv C hb hα z) := by
  have hw' := singWeight_eq_blockPrefix n (initBlocks b) hb0
  have hα₁ := rootNonViolated_blockPrefix_last hb hα
  have h1 := cutParabolicTransfer_natural Q Λ (θ := θ₀) β₀ hw' (lastStageInputEquiv C)
    (lastStageInputEquiv_smul C) (lastStageInputEquiv C) (lastStageInputEquiv_smul C)
    (cutSpectEnd (a := n) (r := 1) Q Λ θ₀ β₀ E (lastStageInput Q hQ n Λ b E Z) e)
    (twoPieceEnd Q Λ b (rootNonViolated_initBlocks hb0) (ρ e))
    (lastStageInputEquiv_spectEnd C e) z
  have h2 : ∀ w, (splitStandardEquiv Q Λ hQ b (rootNonViolated_initBlocks hb0) hα₁ M).symm
      (parabolicStandardMapT Q Λ hQ (twoPieceEnd Q Λ b (rootNonViolated_initBlocks hb0) (ρ e))
        w) =
      BalancedTensor.mapRight (k := k) (B := TensorProductAlgebra k Q Λ
          (initWeight b + lastBlock b)) (M := BlockLeftStandard Q Λ b (blockPrefix_last b) hα₁)
        (ρ e) ((splitStandardEquiv Q Λ hQ b (rootNonViolated_initBlocks hb0) hα₁ M).symm w) := by
    intro w
    apply (splitStandardEquiv Q Λ hQ b (rootNonViolated_initBlocks hb0) hα₁ M).injective
    rw [splitStandardEquiv_mapRight, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  change leftStandardizationWeightCast Q (blockPrefix_last b) hb hα₁ hα M
      ((splitStandardEquiv Q Λ hQ b (rootNonViolated_initBlocks hb0) hα₁ M).symm
        (cutParabolicTransfer Q Λ (θ := θ₀) β₀ hw' (lastStageInputEquiv C)
          (lastStageInputEquiv_smul C)
          (cutStandardMap (a := n) (r := 1) Q Λ θ₀ β₀
            (cutSpectEnd (a := n) (r := 1) Q Λ θ₀ β₀ E (lastStageInput Q hQ n Λ b E Z) e) z))) =
    _
  rw [h1]
  exact (congrArg (leftStandardizationWeightCast Q (blockPrefix_last b) hb hα₁ hα M) (h2 _)).trans
    (leftStandardizationWeightCast_mapRight Q (blockPrefix_last b) hb hα₁ hα M (ρ e) _)

/-- **The comparison step**: a comparison for the first `n` red strands gives one for `n + 1`. -/
def stagedComparisonSucc (C : InitComparison Q hQ n Λ b E ρ Z hb0) {ν : Multiset I}
    (hb : blockPrefix b (n + 2) = ν) (hw : singWeight (n + 1) (b ∘ Fin.succ) = ν)
    (hα : RootNonViolated (ν := ν) (blockRoot b)) :
    StagedComparison Q hQ (n + 1) Λ b (b ∘ Fin.succ) hb hw hα E M ρ Z where
  equiv := stagedStepEquiv C hb hα
  smul_left t x := by
    have h : @Eq (CutStandard (a := n) (r := 1) Q Λ θ₀ β₀ N₁) ((t ⊗ₜ[k] (1 : E)) • x)
        (cutStandardAction (a := n) (r := 1) Q Λ θ₀ β₀ N₁ hQ t x) :=
      congrArg (cutStandardAction (a := n) (r := 1) Q Λ θ₀ β₀ N₁ hQ t)
        (LinearMap.congr_fun (map_one (cutSpectAction (a := n) (r := 1) Q Λ θ₀ β₀ E
          (lastStageInput Q hQ n Λ b E Z))) x)
    exact (congrArg (stagedStepEquiv C hb hα) h).trans (stagedStepEquiv_action C hb hw hα t x)
  smul_right e x := by
    have h : @Eq (CutStandard (a := n) (r := 1) Q Λ θ₀ β₀ N₁)
        (((1 : TensorProductAlgebra k Q Λ (singWeight (n + 1) (b ∘ Fin.succ))) ⊗ₜ[k] e) • x)
        (cutStandardMap (a := n) (r := 1) Q Λ θ₀ β₀
          (cutSpectEnd (a := n) (r := 1) Q Λ θ₀ β₀ E (lastStageInput Q hQ n Λ b E Z) e) x) :=
      LinearMap.congr_fun (map_one (cutStandardAction (a := n) (r := 1) Q Λ θ₀ β₀ N₁ hQ))
        (cutSpectAction (a := n) (r := 1) Q Λ θ₀ β₀ E (lastStageInput Q hQ n Λ b E Z) e x)
    exact (congrArg (stagedStepEquiv C hb hα) h).trans (stagedStepEquiv_spectEnd C hb hα e x)

end Step

/-- **The standardization in stages is the standardization of Definition 5.4.** Let `M` be a
right module over the block algebra of blocks `b` with `b_0 = 0`, with a commuting action `ρ`
of `E`, and `ψ : Z ≃ M` an identification of `M` with a module `Z` over the algebra of the
singleton blocks and `E`. Then `S_staged(Z) ≅ M ⊗_B S^L_α`, compatibly with `T^λ` and `E`. -/
def stagedComparison : (n : ℕ) → (Λ : Fin n → I →₀ ℕ) → (b : Fin (n + 1) → Multiset I) →
    (θ : Fin n → Multiset I) → (hθ : b ∘ Fin.succ = θ) → (hb0 : leftBlock b = 0) →
    {ν : Multiset I} → (hb : blockPrefix b (n + 1) = ν) → (hw : singWeight n θ = ν) →
    (hα : RootNonViolated (ν := ν) (blockRoot b)) → (E : AlgCat.{0} k) → {M : Type} →
    [AddCommGroup M] → [Module k M] → [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M] →
    [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M] →
    (ρ : E →ₐ[k] Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M) →
    (Z : ModuleCat.{0} (singAlg Q n Λ θ ⊗[k] E)) → (ψ : Z ≃+ M) →
    (∀ (s : singAlg Q n Λ θ) (z : Z),
      ψ ((s ⊗ₜ[k] (1 : E)) • z) = singBlockHomOf Q n Λ b hθ s • ψ z) →
    (∀ (e : E) (z : Z), ψ (((1 : singAlg Q n Λ θ) ⊗ₜ[k] e) • z) = ρ e (ψ z)) →
    StagedComparison Q hQ n Λ b θ hb hw hα E M ρ Z
  | 0, Λ, b, θ, hθ, hb0, _, hb, hw, hα, E, _, _, _, _, _, ρ, Z, ψ, hψl, hψr => by
    subst hθ
    exact stagedComparisonZero Q hQ Λ b (b ∘ Fin.succ) hb0 hb hw hα E ρ Z ψ hψl hψr
  | n + 1, Λ, b, θ, hθ, hb0, _, hb, hw, hα, E, _, _, _, _, _, ρ, Z, ψ, hψl, hψr => by
    subst hθ
    exact stagedComparisonSucc (hb0 := hb0)
      (stagedComparison n (Λ ∘ Fin.castSucc) (initBlocks b) ((b ∘ Fin.succ) ∘ Fin.castSucc) rfl
        hb0 rfl (singWeight_eq_blockPrefix n (initBlocks b) hb0)
        (rootNonViolated_initBlocks hb0) (initSpect Q n Λ b E) (initSpectatorAction Q n Λ b E ρ)
        (initStageModule Q n Λ b E Z) (initStageEquiv Q n Λ b E Z ψ)
        (initStageEquiv_smul_left Q n Λ b E Z ψ hψl)
        (initStageEquiv_smul_right Q n Λ b E ρ Z ψ hψl hψr)) hb hw hα

end Categorification.Stendhal

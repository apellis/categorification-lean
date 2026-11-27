/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TwoPieceLastBlackRes
import Categorification.WeightedKLR.RedStrands.FiInitInduction
import Categorification.Algebra.InductionAlongBalancedTensor

/-!
# `ₗFᵢ` is induction along the last cyclotomic factor

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5, `F`-part. Let `b` be blocks of `ℓ + 1` red strands and `c` the blocks with one
black strand of colour `i` added to the last block. Through the splittings
`B(b) ≅ B'(b) ⊗ R^{λ_{ℓ+1}}(β)` and `B(c) ≅ B'(b) ⊗ R^{λ_{ℓ+1}}(i + β)` of the block algebras,
the map `B(b) → B(c)` of `ₗFᵢ` is `1 ⊗ (adding a strand on the right)`
(`splitLastBig_blockBlackRes`). Hence, for a right `B(b)`-module `M`, inducing `M` along it is
inducing `M`, regarded as a module over `R^{λ_{ℓ+1}}(β)` (`LastCycRes`), along the last
cyclotomic factor (`lastIndSplit`): compatibly with the last cyclotomic factor
(`lastIndSplit_lastSmul`), with the block algebra of the first red strands
(`lastIndSplit_initSmul`), and naturally in `M` (`lastIndSplit_map`).
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra MulOpposite InductionAlong
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace StendhalAlgebra

theorem blockAlgebraCast_symm_cast {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) {c c' : Fin (ℓ + 1) → Multiset I}
    (h : c = c') (x : BlockAlgebra k Q Λ c) :
    blockAlgebraCast Q Λ h.symm (blockAlgebraCast Q Λ h x) = x := by
  subst h
  rfl

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I)
  {b c : Fin (ℓ + 2) → Multiset I} (h0 : leftBlock b = leftBlock c)
  (hr : ∀ r, r ≠ Fin.last ℓ → rightBlock b r = rightBlock c r)
  (hκ : {i} + rightBlock b (Fin.last ℓ) = rightBlock c (Fin.last ℓ))

local notation "Cyc" β => CycKLR k Q (redCyc Λ (Fin.last ℓ)) β
local notation "E" => blockBlackRes Q Λ i (Fin.last ℓ) (b := c) (b' := b) h0 hr hκ
local notation "B₁" => BlockAlgebra k Q (Λ ∘ Fin.castSucc) (initBlocks b)
local notation "β" => lastBlock b
local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "cL" => AbsentColour.cyclotomicLast Q i (redCyc Λ (Fin.last ℓ)) (lastBlock b)
local notation "fl" => CycKLR.flip (redCyc Λ (Fin.last ℓ))

include h0 hr in
/-- The first blocks of `c` are those of `b`. -/
theorem initBlocks_lastBig : initBlocks c = initBlocks b :=
  (initBlocks_eq_of_last (b := c) (b' := b) h0 hr).symm

/-- The splitting of the block algebra of `c`, over the first block algebra of `b`. -/
def splitLastBig : BlockAlgebra k Q Λ c ≃ₐ[k] B₁ ⊗[k] Cyc (Si + β) :=
  (blockSplit Q Λ c).trans (Algebra.TensorProduct.congr
    (blockAlgebraCast Q (Λ ∘ Fin.castSucc) (initBlocks_lastBig h0 hr))
    (CyclotomicAction.castCyc Q (redCyc Λ (Fin.last ℓ)) hκ.symm))

theorem splitLastBig_initBlockAlgHom (x : BlockAlgebra k Q (Λ ∘ Fin.castSucc) (initBlocks c)) :
    splitLastBig Q Λ i h0 hr hκ (initBlockAlgHom Q Λ c x) =
      blockAlgebraCast Q (Λ ∘ Fin.castSucc) (initBlocks_lastBig h0 hr) x ⊗ₜ 1 := by
  rw [splitLastBig, AlgEquiv.trans_apply, blockSplit_initBlockAlgHom,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  change _ ⊗ₜ[k] (CyclotomicAction.castCyc Q (redCyc Λ (Fin.last ℓ)) _) 1 = _
  rw [map_one]
  rfl

theorem splitLastBig_lastBlockAlgHom (y : Cyc (rightBlock c (Fin.last ℓ))) :
    splitLastBig Q Λ i h0 hr hκ (lastBlockAlgHom Q Λ c y) =
      1 ⊗ₜ CyclotomicAction.castCyc Q (redCyc Λ (Fin.last ℓ)) hκ.symm y := by
  rw [splitLastBig, AlgEquiv.trans_apply, blockSplit_lastBlockAlgHom,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  change (blockAlgebraCast Q (Λ ∘ Fin.castSucc) _) 1 ⊗ₜ[k] _ = _
  rw [map_one]
  rfl

/-- **`ₗFᵢ` on the split block algebras is `1 ⊗ (adding a strand on the right)`.** -/
theorem splitLastBig_blockBlackRes (x : B₁) (y : Cyc β) :
    splitLastBig Q Λ i h0 hr hκ (E (initBlockAlgHom Q Λ b x * lastBlockAlgHom Q Λ b y)) =
      x ⊗ₜ cL y := by
  rw [map_mul (E), blockBlackRes_initBlockAlgHom_last, mul_assoc, ← map_mul (E), one_mul,
    blockBlackRes_lastBlockAlgHom_last, map_mul, splitLastBig_initBlockAlgHom,
    splitLastBig_lastBlockAlgHom, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
    blockAlgebraCast_symm_cast, castCyc_symm_castCyc]
  rfl

/-- The splitting of the opposite block algebra of `b`, with the last factor first. -/
def splitLastSmallOp : (BlockAlgebra k Q Λ b)ᵐᵒᵖ ≃ₐ[k] (Cyc β) ⊗[k] B₁ᵐᵒᵖ :=
  (AlgEquiv.op (blockSplit Q Λ b)).trans
    ((Algebra.TensorProduct.opAlgEquiv k k B₁ (Cyc β)).symm.trans
      ((Algebra.TensorProduct.congr AlgEquiv.refl
        (CycKLR.flipEquiv (redCyc Λ (Fin.last ℓ)) β).symm).trans
        (Algebra.TensorProduct.comm k _ _)))

/-- The splitting of the opposite block algebra of `c`, with the last factor first. -/
def splitLastBigOp : (BlockAlgebra k Q Λ c)ᵐᵒᵖ ≃ₐ[k] (Cyc (Si + β)) ⊗[k] B₁ᵐᵒᵖ :=
  (AlgEquiv.op (splitLastBig Q Λ i h0 hr hκ)).trans
    ((Algebra.TensorProduct.opAlgEquiv k k B₁ (Cyc (Si + β))).symm.trans
      ((Algebra.TensorProduct.congr AlgEquiv.refl
        (CycKLR.flipEquiv (redCyc Λ (Fin.last ℓ)) (Si + β)).symm).trans
        (Algebra.TensorProduct.comm k _ _)))

theorem splitLastSmallOp_op (x : B₁) (y : Cyc β) :
    splitLastSmallOp Q Λ (b := b) (op (initBlockAlgHom Q Λ b x * lastBlockAlgHom Q Λ b y)) =
      fl β y ⊗ₜ op x := by
  change Algebra.TensorProduct.comm k _ _ (Algebra.TensorProduct.congr AlgEquiv.refl
    (CycKLR.flipEquiv (redCyc Λ (Fin.last ℓ)) β).symm
      ((Algebra.TensorProduct.opAlgEquiv k k B₁ (Cyc β)).symm
        (op (blockSplit Q Λ b (initBlockAlgHom Q Λ b x * lastBlockAlgHom Q Λ b y))))) = _
  rw [← blockSplit_symm_tmul, AlgEquiv.apply_symm_apply,
    Algebra.TensorProduct.opAlgEquiv_symm_tmul, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.comm_tmul]
  rfl

theorem splitLastBigOp_op (x : B₁) (y : Cyc (Si + β)) :
    splitLastBigOp Q Λ i h0 hr hκ (op ((splitLastBig Q Λ i h0 hr hκ).symm (x ⊗ₜ y))) =
      fl (Si + β) y ⊗ₜ op x := by
  change Algebra.TensorProduct.comm k _ _ (Algebra.TensorProduct.congr AlgEquiv.refl
    (CycKLR.flipEquiv (redCyc Λ (Fin.last ℓ)) (Si + β)).symm
      ((Algebra.TensorProduct.opAlgEquiv k k B₁ (Cyc (Si + β))).symm
        (op (splitLastBig Q Λ i h0 hr hκ ((splitLastBig Q Λ i h0 hr hκ).symm (x ⊗ₜ y)))))) = _
  rw [AlgEquiv.apply_symm_apply, Algebra.TensorProduct.opAlgEquiv_symm_tmul,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.comm_tmul]
  rfl

/-- Adding a strand on the right of the last cyclotomic factor. -/
abbrev lastCycHom : (Cyc β) →ₙ+* (Cyc (Si + β)) :=
  NonUnitalRingHomClass.toNonUnitalRingHom cL

theorem lastCycHom_smul (r : k) (y : Cyc β) :
    lastCycHom Q Λ i (b := b) (r • y) = r • lastCycHom Q Λ i (b := b) y :=
  map_smul cL r y

/-- `1 ⊗ (adding a strand)` on the split opposite algebras. -/
abbrev splitLastRes : @NonUnitalRingHom ((Cyc β) ⊗[k] B₁ᵐᵒᵖ) ((Cyc (Si + β)) ⊗[k] B₁ᵐᵒᵖ)
    Ring.toNonAssocRing.toNonUnitalNonAssocSemiring
    Ring.toNonAssocRing.toNonUnitalNonAssocSemiring :=
  tensorLeft k B₁ᵐᵒᵖ (lastCycHom Q Λ i (b := b)) (lastCycHom_smul Q Λ i)

/-- **The splittings intertwine `ₗFᵢ` with `1 ⊗ (adding a strand)`.** -/
theorem splitLastRes_splitLastSmallOp (t : (BlockAlgebra k Q Λ b)ᵐᵒᵖ) :
    splitLastRes Q Λ i (splitLastSmallOp Q Λ t) =
      splitLastBigOp Q Λ i h0 hr hκ (blockBlackResOp Q Λ i (Fin.last ℓ) h0 hr hκ t) := by
  obtain ⟨x, rfl⟩ := MulOpposite.op_surjective t
  obtain ⟨s, rfl⟩ := (blockSplit Q Λ b).symm.surjective x
  induction s using TensorProduct.inductionOn with
  | tmul x y =>
    rw [blockSplit_symm_tmul, splitLastSmallOp_op, tensorLeft_tmul]
    change _ = splitLastBigOp Q Λ i h0 hr hκ
      (op (E (initBlockAlgHom Q Λ b x * lastBlockAlgHom Q Λ b y)))
    rw [← (splitLastBig Q Λ i h0 hr hκ).symm_apply_apply
      (E (initBlockAlgHom Q Λ b x * lastBlockAlgHom Q Λ b y)), splitLastBig_blockBlackRes,
      splitLastBigOp_op]
    exact congrArg (· ⊗ₜ[k] op x)
      (CycKLR.flip_cyclotomicLast (redCyc Λ (Fin.last ℓ)) β i y).symm
  | add s t hs ht => rw [map_add, op_add, map_add, map_add, hs, ht, map_add, map_add]

section Module

variable (M : Type) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]

variable (b) in
/-- The restriction of `M` to the first red strands, with the last cyclotomic factor acting. -/
def LastCycRes : Type := InitRestrict Q Λ b M

instance : AddCommGroup (LastCycRes Q Λ b M) :=
  inferInstanceAs (AddCommGroup (InitRestrict Q Λ b M))
instance : Module k (LastCycRes Q Λ b M) := inferInstanceAs (Module k (InitRestrict Q Λ b M))
instance : Module B₁ᵐᵒᵖ (LastCycRes Q Λ b M) :=
  inferInstanceAs (Module B₁ᵐᵒᵖ (InitRestrict Q Λ b M))
instance : IsScalarTower k B₁ᵐᵒᵖ (LastCycRes Q Λ b M) :=
  inferInstanceAs (IsScalarTower k B₁ᵐᵒᵖ (InitRestrict Q Λ b M))
instance : Module (Cyc β) (LastCycRes Q Λ b M) :=
  Module.compHom (InitRestrict Q Λ b M) (lastFactorEndAlg Q Λ b M).toRingHom

theorem lastCycRes_smul_def (y : Cyc β) (m : LastCycRes Q Λ b M) :
    y • m = (show LastCycRes Q Λ b M from lastFactorEnd Q Λ b y (show InitRestrict Q Λ b M from m))
      := rfl

instance : SMulCommClass B₁ᵐᵒᵖ (Cyc β) (LastCycRes Q Λ b M) where
  smul_comm r y m := (map_smul (lastFactorEnd Q Λ b y) r (show InitRestrict Q Λ b M from m)).symm

instance : IsScalarTower k (Cyc β) (LastCycRes Q Λ b M) where
  smul_assoc r y m := by
    change lastFactorEnd Q Λ b (r • y) _ = r • lastFactorEnd Q Λ b y _
    rw [← lastFactorEndAlg_apply, map_smul, LinearMap.smul_apply]
    rfl

/-- The identity `M → LastCycRes M`. -/
def toLastCycRes : M ≃+ LastCycRes Q Λ b M := (initRestrictOf Q Λ b).toAddEquiv

theorem splitLastSmallOp_symm_tmul_one (y : Cyc β) :
    (splitLastSmallOp Q Λ (b := b)).symm (y ⊗ₜ (1 : B₁ᵐᵒᵖ)) =
      op (lastBlockAlgHom Q Λ b (fl β y)) := by
  rw [AlgEquiv.symm_apply_eq, ← one_mul (lastBlockAlgHom Q Λ b (fl β y)),
    ← map_one (initBlockAlgHom Q Λ b), splitLastSmallOp_op, CycKLR.flip_flip, op_one]

theorem splitLastSmallOp_symm_one_tmul (x : B₁) :
    (splitLastSmallOp Q Λ (b := b)).symm ((1 : Cyc β) ⊗ₜ op x) = op (initBlockAlgHom Q Λ b x) := by
  rw [AlgEquiv.symm_apply_eq, ← mul_one (initBlockAlgHom Q Λ b x),
    ← map_one (lastBlockAlgHom Q Λ b), splitLastSmallOp_op]
  exact congrArg (· ⊗ₜ[k] op x) (cycFlip_one (Q := Q) (redCyc Λ (Fin.last ℓ)) β).symm

theorem toLastCycRes_smul (y : Cyc β) (m : M) :
    toLastCycRes Q Λ (b := b) M ((splitLastSmallOp Q Λ (b := b)).symm (y ⊗ₜ (1 : B₁ᵐᵒᵖ)) • m) =
      y • toLastCycRes Q Λ (b := b) M m := by
  rw [splitLastSmallOp_symm_tmul_one]
  rfl

/-- **`ₗFᵢ M` as induction of `M` along the last cyclotomic factor.** -/
def lastIndSplit :
    IndK k M (blockBlackResOp Q Λ i (Fin.last ℓ) h0 hr hκ) ≃+
      IndK k (LastCycRes Q Λ b M) (lastCycHom Q Λ i (b := b)) :=
  splitInd (splitLastSmallOp Q Λ) (splitLastBigOp Q Λ i h0 hr hκ)
    (blockBlackResOp Q Λ i (Fin.last ℓ) h0 hr hκ) (lastCycHom Q Λ i (b := b))
    (lastCycHom_smul Q Λ i) (splitLastRes_splitLastSmallOp Q Λ i h0 hr hκ)
    (toLastCycRes Q Λ (b := b) M) (toLastCycRes_smul Q Λ M)

theorem splitLastBigOp_symm_tmul_one (y : Cyc (Si + β)) :
    (splitLastBigOp Q Λ i h0 hr hκ).symm (y ⊗ₜ (1 : B₁ᵐᵒᵖ)) =
      op (lastBlockAlgHom Q Λ c (CyclotomicAction.castCyc Q (redCyc Λ (Fin.last ℓ)) hκ
        (fl (Si + β) y))) := by
  rw [AlgEquiv.symm_apply_eq, ← (splitLastBig Q Λ i h0 hr hκ).symm_apply_apply
    (lastBlockAlgHom Q Λ c _), splitLastBig_lastBlockAlgHom, castCyc_symm_castCyc,
    splitLastBigOp_op, CycKLR.flip_flip, op_one]

theorem splitLastBigOp_symm_one_tmul (x : B₁) :
    (splitLastBigOp Q Λ i h0 hr hκ).symm ((1 : Cyc (Si + β)) ⊗ₜ op x) =
      op (initBlockAlgHom Q Λ c
        ((blockAlgebraCast Q (Λ ∘ Fin.castSucc) (initBlocks_lastBig h0 hr)).symm x)) := by
  rw [AlgEquiv.symm_apply_eq, ← (splitLastBig Q Λ i h0 hr hκ).symm_apply_apply
    (initBlockAlgHom Q Λ c _), splitLastBig_initBlockAlgHom, AlgEquiv.apply_symm_apply,
    splitLastBigOp_op]
  exact congrArg (· ⊗ₜ[k] op x) (cycFlip_one (Q := Q) (redCyc Λ (Fin.last ℓ)) (Si + β)).symm

local notation "φc" => lastCycHom Q Λ i (b := b)
local notation "ι" => lastIndSplit Q Λ i h0 hr hκ M

/-- **`lastIndSplit` intertwines the last cyclotomic factors.** -/
theorem lastIndSplit_lastSmul (y : Cyc (Si + β))
    (w : IndK k M (blockBlackResOp Q Λ i (Fin.last ℓ) h0 hr hκ)) :
    ι (op (lastBlockAlgHom Q Λ c (CyclotomicAction.castCyc Q (redCyc Λ (Fin.last ℓ)) hκ
      (fl (Si + β) y))) • w) = y • ι w := by
  rw [← splitLastBigOp_symm_tmul_one]
  exact splitInd_smul _ _ _ _ _ _ _ _ y w

/-- **`lastIndSplit` is `k`-linear.** -/
theorem lastIndSplit_smul (r : k) (w : IndK k M (blockBlackResOp Q Λ i (Fin.last ℓ) h0 hr hκ)) :
    ι (r • w) = r • ι w := by
  have h : r • w = (splitLastBigOp Q Λ i h0 hr hκ).symm
      (algebraMap k (Cyc (Si + β)) r ⊗ₜ (1 : B₁ᵐᵒᵖ)) • w := by
    rw [← Algebra.TensorProduct.algebraMap_apply, AlgEquiv.commutes]
    rfl
  rw [h]
  exact splitInd_smul _ _ _ _ _ _ _ _ (algebraMap k (Cyc (Si + β)) r) w

/-- **`lastIndSplit` intertwines the first red strands** with the action of
`B'(b)ᵐᵒᵖ` on `LastCycRes M`. -/
theorem lastIndSplit_initSmul (x : B₁)
    (w : IndK k M (blockBlackResOp Q Λ i (Fin.last ℓ) h0 hr hκ)) :
    ι (op (initBlockAlgHom Q Λ c
        ((blockAlgebraCast Q (Λ ∘ Fin.castSucc) (initBlocks_lastBig h0 hr)).symm x)) • w) =
      IndK.map (rSmulA (A := Cyc β) (op x : B₁ᵐᵒᵖ)) (ι w) := by
  rw [← splitLastBigOp_symm_one_tmul]
  refine splitInd_one_tmul_smul _ _ _ _ _ _ _ _ (op x) _ (fun m => ?_) w
  rw [splitLastSmallOp_symm_one_tmul]
  rfl

/-- An endomorphism of `M` as an endomorphism of `LastCycRes M` over the last factor. -/
def lastCycResEnd (g : Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M) :
    LastCycRes Q Λ b M →ₗ[Cyc β] LastCycRes Q Λ b M where
  toFun m := toLastCycRes Q Λ (b := b) M (g ((toLastCycRes Q Λ (b := b) M).symm m))
  map_add' m m' := by rw [map_add, map_add, map_add]
  map_smul' y m := g.map_smul _ ((toLastCycRes Q Λ (b := b) M).symm m)

/-- **`lastIndSplit` is natural** in endomorphisms of `M`. -/
theorem lastIndSplit_map (g : Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M)
    (w : IndK k M (blockBlackResOp Q Λ i (Fin.last ℓ) h0 hr hκ)) :
    ι (IndK.map g w) = IndK.map (lastCycResEnd Q Λ M g) (ι w) :=
  splitInd_map _ _ _ _ _ _ _ _ g (lastCycResEnd Q Λ M g) (fun _ => rfl) w

local notation "Fl" => BlockBlackInd Q Λ i (Fin.last ℓ) h0 hr hκ M

/-- `ₗFᵢ M` restricted to the first red strands, over the first block algebra of `b`. -/
abbrev LastBlackRes : Type :=
  CastBlockModule Q (Λ ∘ Fin.castSucc) (initBlocks_lastBig h0 hr) (InitRestrict Q Λ c Fl)

/-- The identity `ₗFᵢ M → LastBlackRes`. -/
def toLastBlackRes : Fl ≃ₗ[k] LastBlackRes Q Λ i h0 hr hκ M :=
  (initRestrictOf Q Λ c).trans (castBlockModuleOf Q (Λ ∘ Fin.castSucc) (initBlocks_lastBig h0 hr))

/-- **`ₗFᵢ M` restricted to the first red strands is induction of `M` along the last
cyclotomic factor.** -/
def lastBlackIndEquiv :
    IndK k (LastCycRes Q Λ b M) φc ≃ₗ[k] LastBlackRes Q Λ i h0 hr hκ M where
  toFun w := toLastBlackRes Q Λ i h0 hr hκ M ((ι).symm w)
  invFun y := ι ((toLastBlackRes Q Λ i h0 hr hκ M).symm y)
  map_add' w w' := by rw [map_add, map_add]
  map_smul' r w := by
    rw [RingHom.id_apply, ← map_smul]
    congr 1
    apply (ι).injective
    rw [lastIndSplit_smul, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  left_inv w := by
    change ι ((toLastBlackRes Q Λ i h0 hr hκ M).symm (toLastBlackRes Q Λ i h0 hr hκ M _)) = w
    rw [LinearEquiv.symm_apply_apply, AddEquiv.apply_symm_apply]
  right_inv y := by
    change toLastBlackRes Q Λ i h0 hr hκ M ((ι).symm (ι _)) = y
    rw [AddEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]

theorem lastBlackIndEquiv_symm_apply (y : LastBlackRes Q Λ i h0 hr hκ M) :
    (lastBlackIndEquiv Q Λ i h0 hr hκ M).symm y = ι ((toLastBlackRes Q Λ i h0 hr hκ M).symm y) :=
  rfl

/-- **`lastBlackIndEquiv` intertwines the first red strands.** -/
theorem lastBlackIndEquiv_rSmul (x : B₁) (w : IndK k (LastCycRes Q Λ b M) φc) :
    lastBlackIndEquiv Q Λ i h0 hr hκ M (IndK.map (rSmulA (A := Cyc β) (op x : B₁ᵐᵒᵖ)) w) =
      (op x : B₁ᵐᵒᵖ) • lastBlackIndEquiv Q Λ i h0 hr hκ M w := by
  apply (lastBlackIndEquiv Q Λ i h0 hr hκ M).symm.injective
  rw [LinearEquiv.symm_apply_apply, lastBlackIndEquiv_symm_apply]
  change _ = ι (op (initBlockAlgHom Q Λ c
    ((blockAlgebraCast Q (Λ ∘ Fin.castSucc) (initBlocks_lastBig h0 hr)).symm x)) • (ι).symm w)
  rw [lastIndSplit_initSmul, AddEquiv.apply_symm_apply]

/-- **`lastBlackIndEquiv` intertwines the last cyclotomic factors.** -/
theorem lastBlackIndEquiv_lastSmul (y : Cyc (Si + β)) (w : IndK k (LastCycRes Q Λ b M) φc) :
    lastBlackIndEquiv Q Λ i h0 hr hκ M (y • w) =
      toLastBlackRes Q Λ i h0 hr hκ M (op (lastBlockAlgHom Q Λ c (fl (rightBlock c (Fin.last ℓ))
        (CyclotomicAction.castCyc Q (redCyc Λ (Fin.last ℓ)) hκ y))) •
          (toLastBlackRes Q Λ i h0 hr hκ M).symm (lastBlackIndEquiv Q Λ i h0 hr hκ M w)) := by
  apply (lastBlackIndEquiv Q Λ i h0 hr hκ M).symm.injective
  rw [LinearEquiv.symm_apply_apply, lastBlackIndEquiv_symm_apply, LinearEquiv.symm_apply_apply,
    cycFlip_castCyc]
  refine Eq.trans ?_ (lastIndSplit_lastSmul Q Λ i h0 hr hκ M y _).symm
  change y • w = y • ι ((toLastBlackRes Q Λ i h0 hr hκ M).symm (toLastBlackRes Q Λ i h0 hr hκ M
    ((ι).symm w)))
  rw [LinearEquiv.symm_apply_apply, AddEquiv.apply_symm_apply]

/-- **Naturality of `lastBlackIndEquiv`** in endomorphisms of `M`. -/
theorem lastBlackIndEquiv_natural (g : Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M)
    (w : IndK k (LastCycRes Q Λ b M) φc) :
    lastBlackIndEquiv Q Λ i h0 hr hκ M (IndK.map (lastCycResEnd Q Λ M g) w) =
      toLastBlackRes Q Λ i h0 hr hκ M (IndK.map g
        ((toLastBlackRes Q Λ i h0 hr hκ M).symm (lastBlackIndEquiv Q Λ i h0 hr hκ M w))) := by
  apply (lastBlackIndEquiv Q Λ i h0 hr hκ M).symm.injective
  rw [LinearEquiv.symm_apply_apply, lastBlackIndEquiv_symm_apply, LinearEquiv.symm_apply_apply,
    lastIndSplit_map]
  change _ = IndK.map (lastCycResEnd Q Λ M g) (ι ((toLastBlackRes Q Λ i h0 hr hκ M).symm
    (toLastBlackRes Q Λ i h0 hr hκ M ((ι).symm w))))
  rw [LinearEquiv.symm_apply_apply, AddEquiv.apply_symm_apply]

end Module

end StendhalAlgebra

end Categorification.Stendhal

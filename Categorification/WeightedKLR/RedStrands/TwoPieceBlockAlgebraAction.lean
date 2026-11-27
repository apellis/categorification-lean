/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TwoPieceBlockAlgebra
import Categorification.WeightedKLR.RedStrands.TwoPieceRootStandardBlocks
import Categorification.WeightedKLR.RedStrands.TwoPieceRootStandardLastBlock
import Categorification.KLR.CyclotomicFlip

/-!
# The two-piece isomorphism intertwines the block algebra actions

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1,
Proposition 5.3 and proof of Proposition 5.5. Let `Φ : S(S^L_{α'} ⊠ R^{λ_{ℓ+1}}(β)) ≅ S^L_α` be
the two-piece isomorphism (`twoPieceRootStandardEquiv`). For every `x` in the block algebra `B'`
of the first `ℓ` red strands, `Φ` intertwines the standardization of `x ⊠ id` with the action
of `x` through `B' → B` (`twoPieceRootStandardEquiv_initBlockAlg`); for every `c` in the last
factor it intertwines the standardization of `id ⊠ (· flip(c))` with the action of `c`
(`twoPieceRootStandardEquiv_lastBlockAlg`). This extends the statements for the generators
(`twoPieceRootStandardEquiv_initBlock`, `twoPieceRootStandardEquiv_lastBlock`) to the whole
block algebras.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open KLR
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (hQ : KLRSymm Q)

section Functor

variable {θ β : Multiset I} {N N' : Type*}
  [AddCommGroup N] [Module k N] [Module (parabolicFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N]
  [AddCommGroup N'] [Module k N'] [Module (parabolicFactorAlgebra Q Λ θ β) N']
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N']

theorem parabolicStandardMapT_unit (g : N →ₗ[parabolicFactorAlgebra Q Λ θ β] N') (n : N) :
    parabolicStandardMapT Q Λ hQ g (parabolicStandardTUnit Q Λ θ β hQ n) =
      parabolicStandardTUnit Q Λ θ β hQ (g n) := rfl

end Functor

theorem intertwine_comp {R : Type*} [Semiring R] {V W : Type*} [AddCommMonoid V] [Module R V]
    [AddCommMonoid W] [Module R W] {e : V →ₗ[R] W} {f f' : Module.End R V}
    {g g' : Module.End R W} (h : e ∘ₗ f = g ∘ₗ e) (h' : e ∘ₗ f' = g' ∘ₗ e) :
    e ∘ₗ (f ∘ₗ f') = (g ∘ₗ g') ∘ₗ e := by
  rw [← LinearMap.comp_assoc, h, LinearMap.comp_assoc, h', LinearMap.comp_assoc]

theorem intertwine_add {R : Type*} [Semiring R] {V W : Type*} [AddCommMonoid V] [Module R V]
    [AddCommMonoid W] [Module R W] {e : V →ₗ[R] W} {f f' : Module.End R V}
    {g g' : Module.End R W} (h : e ∘ₗ f = g ∘ₗ e) (h' : e ∘ₗ f' = g' ∘ₗ e) :
    e ∘ₗ (f + f') = (g + g') ∘ₗ e := by
  rw [LinearMap.comp_add, h, h', LinearMap.add_comp]

theorem ExtTensor.map_add_left {A B : Type*} [Ring A] [Algebra k A] [Ring B] [Algebra k B]
    {P P' Q Q' : Type*} [AddCommGroup P] [Module k P] [Module A P] [IsScalarTower k A P]
    [AddCommGroup Q] [Module k Q] [Module B Q] [IsScalarTower k B Q]
    [AddCommGroup P'] [Module k P'] [Module A P'] [IsScalarTower k A P']
    [AddCommGroup Q'] [Module k Q'] [Module B Q'] [IsScalarTower k B Q']
    (f f' : P →ₗ[A] P') (g : Q →ₗ[B] Q') :
    ExtTensor.map (k := k) (f + f') g = ExtTensor.map f g + ExtTensor.map f' g :=
  LinearMap.ext fun x => by
    induction x using ExtTensor.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul p q => exact ExtTensor.add_tmul _ _ _
    | add x y hx hy => rw [map_add, map_add, hx, hy]

variable (b : Fin (ℓ + 2) → Multiset I)

local notation "Told" => TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) (initWeight b)
local notation "D" => parabolicFactorAlgebra Q Λ (initWeight b) (lastBlock b)
local notation "Tν" => TensorProductAlgebra k Q Λ (initWeight b + lastBlock b)
local notation "L'" => StendhalAlgebra.LeftRootStandard Q (Λ ∘ Fin.castSucc) (ν := initWeight b)
  (blockRoot (initBlocks b))
local notation "L" => StendhalAlgebra.LeftRootStandard Q Λ (ν := initWeight b + lastBlock b)
  (blockRoot b)
set_option quotPrecheck false in
local notation "N₀" => (rootSplitInput Q Λ b).carrier
local notation "B" => StendhalAlgebra.BlockAlgebra k Q Λ b
local notation "B'" => StendhalAlgebra.BlockAlgebra k Q (Λ ∘ Fin.castSucc) (initBlocks b)
local notation "Cyc" => CycKLR k Q (StendhalAlgebra.redCyc Λ (Fin.last ℓ))
  (StendhalAlgebra.rightBlock b (Fin.last ℓ))

theorem rootSplitLeftMap_mul (f g : Module.End Told L') :
    rootSplitLeftMap Q Λ b (f * g) = rootSplitLeftMap Q Λ b f ∘ₗ rootSplitLeftMap Q Λ b g :=
  LinearMap.ext fun x => by
    induction x using ExtTensor.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul p q => rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem rootSplitLeftMap_one :
    rootSplitLeftMap Q Λ b 1 = LinearMap.id :=
  LinearMap.ext fun x => by
    induction x using ExtTensor.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul p q => rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem rootSplitLeftMap_add (f g : Module.End Told L') :
    rootSplitLeftMap Q Λ b (f + g) = rootSplitLeftMap Q Λ b f + rootSplitLeftMap Q Λ b g :=
  ExtTensor.map_add_left _ _ _

variable (hα' : StendhalAlgebra.RootNonViolated (ν := initWeight b) (blockRoot (initBlocks b)))
  (hα : StendhalAlgebra.RootNonViolated (ν := initWeight b + lastBlock b) (blockRoot b))

set_option quotPrecheck false in
local notation "Φ" => (twoPieceRootStandardEquiv Q Λ hQ b).toLinearMap
set_option quotPrecheck false in
local notation "F'" => StendhalAlgebra.leftBlockActionOf Q (Λ ∘ Fin.castSucc) (initBlocks b) rfl hα'
set_option quotPrecheck false in
local notation "F" => StendhalAlgebra.leftBlockActionOf Q Λ b (blockPrefix_last b) hα

theorem twoPieceRootStandardEquiv_init_gen₀ (a : KLRAlgebra k Q (StendhalAlgebra.leftBlock b)) :
    Φ ∘ₗ parabolicStandardMapT Q Λ hQ (rootSplitLeftMap Q Λ b (F' (a ⊗ₜ 1))) =
      F (StendhalAlgebra.initBlockAlgHom Q Λ b (a ⊗ₜ 1)) ∘ₗ Φ := by
  rw [StendhalAlgebra.initBlockAlgHom_tmul_one]
  simp only [StendhalAlgebra.leftBlockActionOf, AlgHom.comp_apply,
    StendhalAlgebra.blockAction_tmul_one]
  exact twoPieceRootStandardEquiv_initBlock Q Λ hQ b (Nat.succ_pos ℓ) hα' hα a

theorem initLhs_mul (x y : B') :
    parabolicStandardMapT Q Λ hQ (rootSplitLeftMap Q Λ b (F' (x * y))) =
      parabolicStandardMapT Q Λ hQ (rootSplitLeftMap Q Λ b (F' x)) ∘ₗ
        parabolicStandardMapT Q Λ hQ (rootSplitLeftMap Q Λ b (F' y)) := by
  rw [map_mul, rootSplitLeftMap_mul, parabolicStandardMapT_comp]

theorem initLhs_add (x y : B') :
    parabolicStandardMapT Q Λ hQ (rootSplitLeftMap Q Λ b (F' (x + y))) =
      parabolicStandardMapT Q Λ hQ (rootSplitLeftMap Q Λ b (F' x)) +
        parabolicStandardMapT Q Λ hQ (rootSplitLeftMap Q Λ b (F' y)) := by
  rw [show F' (x + y) = F' x + F' y from (F').toRingHom.map_add x y, rootSplitLeftMap_add,
    parabolicStandardMapT_add]

/-- `x ∈ B'` is intertwined by the two-piece isomorphism. -/
def InitIntertwined (x : B') : Prop :=
  Φ ∘ₗ parabolicStandardMapT Q Λ hQ (rootSplitLeftMap Q Λ b (F' x)) =
    F (StendhalAlgebra.initBlockAlgHom Q Λ b x) ∘ₗ Φ

theorem initIntertwined_mul {x y : B'} (hx : InitIntertwined Q Λ hQ b hα' hα x)
    (hy : InitIntertwined Q Λ hQ b hα' hα y) : InitIntertwined Q Λ hQ b hα' hα (x * y) := by
  unfold InitIntertwined at hx hy ⊢
  rw [initLhs_mul, show F (StendhalAlgebra.initBlockAlgHom Q Λ b (x * y)) =
      F (StendhalAlgebra.initBlockAlgHom Q Λ b x) ∘ₗ F (StendhalAlgebra.initBlockAlgHom Q Λ b y)
    from ((F).toRingHom.comp (StendhalAlgebra.initBlockAlgHom Q Λ b).toRingHom).map_mul x y]
  exact intertwine_comp hx hy

theorem initIntertwined_add {x y : B'} (hx : InitIntertwined Q Λ hQ b hα' hα x)
    (hy : InitIntertwined Q Λ hQ b hα' hα y) : InitIntertwined Q Λ hQ b hα' hα (x + y) := by
  unfold InitIntertwined at hx hy ⊢
  rw [initLhs_add, show F (StendhalAlgebra.initBlockAlgHom Q Λ b (x + y)) =
      F (StendhalAlgebra.initBlockAlgHom Q Λ b x) + F (StendhalAlgebra.initBlockAlgHom Q Λ b y)
    from ((F).toRingHom.comp (StendhalAlgebra.initBlockAlgHom Q Λ b).toRingHom).map_add x y]
  exact intertwine_add hx hy

theorem initIntertwined_algebraMap (c : k) :
    InitIntertwined Q Λ hQ b hα' hα (algebraMap k B' c) := by
  unfold InitIntertwined
  rw [Algebra.TensorProduct.algebraMap_apply]
  exact twoPieceRootStandardEquiv_init_gen₀ Q Λ hQ b hα' hα _

theorem initIntertwined_single (r : Fin ℓ)
    (c : CycKLR k Q (StendhalAlgebra.redCyc (Λ ∘ Fin.castSucc) r)
      (StendhalAlgebra.rightBlock (initBlocks b) r)) :
    InitIntertwined Q Λ hQ b hα' hα (1 ⊗ₜ PiTensorProduct.singleAlgHom (R := k)
      (A := fun r : Fin ℓ => CycKLR k Q (StendhalAlgebra.redCyc (Λ ∘ Fin.castSucc) r)
        (StendhalAlgebra.rightBlock (initBlocks b) r)) r c) := by
  obtain ⟨u, rfl⟩ := CycKLR.mk_surjective c
  unfold InitIntertwined
  rw [StendhalAlgebra.initBlockAlgHom_one_tmul_single]
  simp only [StendhalAlgebra.leftBlockActionOf, AlgHom.comp_apply,
    StendhalAlgebra.blockAction_one_tmul_single]
  refine (twoPieceRootStandardEquiv_initBlock Q Λ hQ b (Nat.succ_lt_succ r.2) hα' hα u).trans ?_
  exact congrArg (fun f => StendhalAlgebra.rootReflectConj Q Λ hα f ∘ₗ Φ)
    (StendhalAlgebra.blockAction_one_tmul_single (blockPrefix_last b) r.castSucc u).symm

/-- **The two-piece isomorphism intertwines the action of the block algebra of the first `ℓ` red
strands**: `Φ ∘ S(x ⊠ id) = x ∘ Φ` for every `x ∈ B'` (arXiv:1309.3796v3, Proposition 5.3 and
proof of Proposition 5.5). -/
theorem twoPieceRootStandardEquiv_initBlockAlg (x : B') :
    Φ ∘ₗ parabolicStandardMapT Q Λ hQ (rootSplitLeftMap Q Λ b (F' x)) =
      F (StendhalAlgebra.initBlockAlgHom Q Λ b x) ∘ₗ Φ := by
  have h1 := initIntertwined_algebraMap Q Λ hQ b hα' hα 1
  have h0 := initIntertwined_algebraMap Q Λ hQ b hα' hα 0
  rw [map_one] at h1
  rw [map_zero] at h0
  let P : Subalgebra k B' :=
    { carrier := {x | InitIntertwined Q Λ hQ b hα' hα x}
      mul_mem' := initIntertwined_mul Q Λ hQ b hα' hα
      add_mem' := initIntertwined_add Q Λ hQ b hα' hα
      one_mem' := h1
      zero_mem' := h0
      algebraMap_mem' := initIntertwined_algebraMap Q Λ hQ b hα' hα }
  have hP : P = ⊤ := PiTensorProduct.tensor_subalgebra_eq_top P
    (fun a => twoPieceRootStandardEquiv_init_gen₀ Q Λ hQ b hα' hα a)
    (fun r c => initIntertwined_single Q Λ hQ b hα' hα r c)
  exact (hP ▸ Algebra.mem_top : x ∈ P)

/-- **The two-piece isomorphism intertwines the action of the last factor**:
`Φ ∘ S(id ⊠ (· flip(c))) = c ∘ Φ` for every `c ∈ R^{λ_{ℓ+1}}(β)` (arXiv:1309.3796v3,
Proposition 5.3 and proof of Proposition 5.5). -/
theorem twoPieceRootStandardEquiv_lastBlockAlg (c : Cyc) :
    Φ ∘ₗ parabolicStandardMapT Q Λ hQ (rootSplitRightMap Q Λ b
          (CycKLR.flip (StendhalAlgebra.redCyc Λ (Fin.last ℓ)) (lastBlock b) c)) =
      F (StendhalAlgebra.lastBlockAlgHom Q Λ b c) ∘ₗ Φ := by
  obtain ⟨a, rfl⟩ := CycKLR.mk_surjective c
  have h := twoPieceRootStandardEquiv_lastBlock Q Λ hQ b hα a
  rw [StendhalAlgebra.lastBlockAlgHom_apply]
  change _ = StendhalAlgebra.rootReflectConj Q Λ hα (StendhalAlgebra.blockAction Q Λ
    (blockPrefix_last b) (1 ⊗ₜ _)) ∘ₗ _
  rw [StendhalAlgebra.blockAction_one_tmul_single]
  exact (congrArg (fun y => Φ ∘ₗ parabolicStandardMapT Q Λ hQ (rootSplitRightMap Q Λ b y))
    (CycKLR.flip_mk _ _ a)).trans h

end Categorification.Stendhal

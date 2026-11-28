/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PrependRedStandard
import Categorification.Algebra.PiTensorProductCons
import Categorification.Algebra.CommutingFamilySingle
import Categorification.WeightedKLR.RedStrands.Standardization
import Categorification.WeightedKLR.RedStrands.TwoPieceBlockAlgebra

/-!
# The block action after adding a red strand on the left

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.26. After adding the red strand `λ₀` on the left, the block `b_0` lies right of
`λ₀`, so it acts on `S_{(0, α)}` through the cyclotomic quotient `R^{λ₀}(b_0)`. This gives an
algebra map from the block algebra of `b` to that of `0, b_0, …, b_ℓ`,
`R(b_0) ⊗ ⨂_r R^{λ_r}(b_{r+1}) → R(0) ⊗ R^{λ₀}(b_0) ⊗ ⨂_r R^{λ_r}(b_{r+1})`
(`prependBlockAlgHom`), and adding the red strand `Θ : S_α → S_{(0, α)}` intertwines the two
block actions along it (`prependRedStandard_blockAction`).

## Main definitions

* `StendhalAlgebra.prependBlockAlgHom`.

## Main results

* `StendhalAlgebra.prependRedStandard_blockAction`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification

/-- For algebra maps `A : B → End_R(M)`, `A' : B' → End_{R'}(M')`, `π : B → B'` and an additive
`k`-linear `Θ : M → M'`, the elements `β` with `Θ ∘ A(β) = A'(π β) ∘ Θ` form a subalgebra. -/
def intertwinerSubalgebra {k : Type*} [CommRing k] {B B' R R' M M' : Type*} [Ring B] [Ring B']
    [Algebra k B] [Algebra k B'] [Ring R] [Ring R'] [AddCommGroup M] [AddCommGroup M']
    [Algebra k R] [Algebra k R'] [Module R M] [Module R' M'] [Module k M] [Module k M']
    [SMulCommClass R k M] [SMulCommClass R' k M'] [IsScalarTower k R M] [IsScalarTower k R' M']
    (A : B →ₐ[k] Module.End R M) (A' : B' →ₐ[k] Module.End R' M')
    (π : B →ₐ[k] B') (Θ : M →+ M') (hΘ : ∀ (c : k) v, Θ (c • v) = c • Θ v) :
    Subalgebra k B where
  carrier := {β | ∀ v, Θ (A β v) = A' (π β) (Θ v)}
  mul_mem' {x y} hx hy v := by
    show Θ (A (x * y) v) = A' (π (x * y)) (Θ v)
    simp only [map_mul, Module.End.mul_apply]
    rw [hx (A y v), hy v]
  add_mem' {x y} hx hy v := by
    show Θ (A (x + y) v) = A' (π (x + y)) (Θ v)
    simp only [map_add, LinearMap.add_apply]
    rw [hx v, hy v]
  algebraMap_mem' c v := by
    show Θ (A (algebraMap k B c) v) = A' (π (algebraMap k B c)) (Θ v)
    simp only [AlgHom.commutes, Module.algebraMap_end_apply]
    exact hΘ c v

end Categorification

namespace Categorification.Stendhal

open KLR StendhalAlgebra MulOpposite
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace StendhalAlgebra


variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin (ℓ + 1) → I →₀ ℕ} {ν : Multiset I}
  (b : Fin (ℓ + 1) → Multiset I)

/-- The cyclotomic factors of the block algebra of `0, b_0, …, b_ℓ`. -/
abbrev consCycFactor (Λ : Fin (ℓ + 1) → I →₀ ℕ) (b : Fin (ℓ + 1) → Multiset I)
    (r : Fin (ℓ + 1)) : Type :=
  CycKLR k Q (redCyc Λ r) (rightBlock (consBlocks b) r)

variable (Q Λ) in
/-- **The block algebra map of an added red strand**:
`R(b_0) ⊗ ⨂_r R^{λ_r}(b_{r+1}) → R(0) ⊗ R^{λ₀}(b_0) ⊗ ⨂_r R^{λ_r}(b_{r+1})`, the cyclotomic
quotient on the first factor. -/
def prependBlockAlgHom :
    BlockAlgebra k Q (Λ ∘ Fin.succ) b →ₐ[k] BlockAlgebra k Q Λ (consBlocks b) :=
  (Algebra.TensorProduct.includeRight (R := k)
      (A := KLRAlgebra k Q (leftBlock (consBlocks b)))).comp
    ((PiTensorProduct.consAlgEquiv k (consCycFactor (k := k) (Q := Q) Λ b)).symm.toAlgHom.comp
      (Algebra.TensorProduct.map (CycKLR.mk k Q (redCyc Λ 0) (leftBlock b)) (AlgHom.id k _)))

theorem prependBlockAlgHom_tmul_one (a : KLRAlgebra k Q (leftBlock b)) :
    prependBlockAlgHom Q Λ b (a ⊗ₜ 1) =
      1 ⊗ₜ PiTensorProduct.singleAlgHom (R := k) (A := consCycFactor (k := k) (Q := Q) Λ b) 0
        (CycKLR.mk k Q (redCyc Λ 0) _ a) := by
  show (1 : KLRAlgebra k Q (leftBlock (consBlocks b))) ⊗ₜ
      (PiTensorProduct.consAlgEquiv k (consCycFactor (k := k) (Q := Q) Λ b)).symm
        (CycKLR.mk k Q (redCyc Λ 0) (leftBlock b) a ⊗ₜ 1) = _
  exact congrArg (TensorProduct.tmul k (1 : KLRAlgebra k Q (leftBlock (consBlocks b))))
    (PiTensorProduct.consAlgEquiv_symm_tmul_one (A := consCycFactor (k := k) (Q := Q) Λ b) _)

theorem prependBlockAlgHom_one_tmul_single (r : Fin ℓ) (u : KLRAlgebra k Q (rightBlock b r)) :
    prependBlockAlgHom Q Λ b
        (1 ⊗ₜ PiTensorProduct.singleAlgHom r (CycKLR.mk k Q (redCyc (Λ ∘ Fin.succ) r) _ u)) =
      1 ⊗ₜ PiTensorProduct.singleAlgHom (R := k) (A := consCycFactor (k := k) (Q := Q) Λ b)
        r.succ (CycKLR.mk k Q (redCyc Λ r.succ) _ u) := by
  show (1 : KLRAlgebra k Q (leftBlock (consBlocks b))) ⊗ₜ
      (PiTensorProduct.consAlgEquiv k (consCycFactor (k := k) (Q := Q) Λ b)).symm
        (CycKLR.mk k Q (redCyc Λ 0) (leftBlock b) 1 ⊗ₜ
          PiTensorProduct.singleAlgHom r (CycKLR.mk k Q (redCyc (Λ ∘ Fin.succ) r) _ u)) = _
  rw [map_one]
  exact congrArg (TensorProduct.tmul k (1 : KLRAlgebra k Q (leftBlock (consBlocks b))))
    (PiTensorProduct.consAlgEquiv_symm_one_tmul_single
      (A := consCycFactor (k := k) (Q := Q) Λ b) r _)

section Intertwine

variable (hb : blockPrefix b (ℓ + 1) = ν)
  (h : blockRoot (consBlocks b) = Fin.cons (0 : I → ℕ) (blockRoot b))

theorem prependRedStandard_blockAction_tmul_one (a : KLRAlgebra k Q (leftBlock b))
    (v : rootStandard (ν := ν) Q (Λ ∘ Fin.succ) (blockRoot b)) :
    prependRedStandard h (blockAction Q (Λ ∘ Fin.succ) hb (a ⊗ₜ 1) v) =
      blockAction Q Λ (b := consBlocks b) (blockPrefix_consBlocks_eq b hb)
        (prependBlockAlgHom Q Λ b (a ⊗ₜ 1)) (prependRedStandard h v) := by
  rw [blockAction_tmul_one, prependBlockAlgHom_tmul_one]
  refine (prependRedStandard_rootBlockAction b hb h 0 _ a v).trans ?_
  exact congrArg (fun f => f (prependRedStandard h v)) (blockAction_one_tmul_single (Λ := Λ)
    (b := consBlocks b) (blockPrefix_consBlocks_eq b hb) 0 a).symm

theorem prependRedStandard_blockAction_one_tmul_single (r : Fin ℓ)
    (u : KLRAlgebra k Q (rightBlock b r))
    (v : rootStandard (ν := ν) Q (Λ ∘ Fin.succ) (blockRoot b)) :
    prependRedStandard h (blockAction Q (Λ ∘ Fin.succ) hb
        (1 ⊗ₜ PiTensorProduct.singleAlgHom r (CycKLR.mk k Q (redCyc (Λ ∘ Fin.succ) r) _ u)) v) =
      blockAction Q Λ (b := consBlocks b) (blockPrefix_consBlocks_eq b hb)
        (prependBlockAlgHom Q Λ b
          (1 ⊗ₜ PiTensorProduct.singleAlgHom r (CycKLR.mk k Q (redCyc (Λ ∘ Fin.succ) r) _ u)))
        (prependRedStandard h v) := by
  rw [blockAction_one_tmul_single, prependBlockAlgHom_one_tmul_single]
  refine (prependRedStandard_rootBlockAction b hb h (r.val + 1) _ u v).trans ?_
  exact congrArg (fun f => f (prependRedStandard h v)) (blockAction_one_tmul_single (Λ := Λ)
    (b := consBlocks b) (blockPrefix_consBlocks_eq b hb) r.succ u).symm

/-- The block algebra elements whose action `Θ` intertwines. -/
abbrev prependIntertwiners : Subalgebra k (BlockAlgebra k Q (Λ ∘ Fin.succ) b) :=
  Categorification.intertwinerSubalgebra (blockAction Q (Λ ∘ Fin.succ) hb)
    (blockAction Q Λ (b := consBlocks b) (blockPrefix_consBlocks_eq b hb))
    (prependBlockAlgHom Q Λ b) (prependRedStandard h) (prependRedStandard_smul h)

/-- **Adding the red strand intertwines the block actions**:
`Θ(β · v) = π(β) · Θ(v)` for `β` in the block algebra of `b` and `v ∈ S_α`
(arXiv:1309.3796v3, proof of Proposition 5.26). -/
theorem prependRedStandard_blockAction (β : BlockAlgebra k Q (Λ ∘ Fin.succ) b)
    (v : rootStandard (ν := ν) Q (Λ ∘ Fin.succ) (blockRoot b)) :
    prependRedStandard h (blockAction Q (Λ ∘ Fin.succ) hb β v) =
      blockAction Q Λ (b := consBlocks b) (blockPrefix_consBlocks_eq b hb)
        (prependBlockAlgHom Q Λ b β) (prependRedStandard h v) := by
  have hP : prependIntertwiners (k := k) (Q := Q) (Λ := Λ) b hb h = ⊤ := by
    refine PiTensorProduct.tensor_subalgebra_eq_top _
      (fun a => prependRedStandard_blockAction_tmul_one b hb h a) (fun r c => ?_)
    obtain ⟨u, rfl⟩ := CycKLR.mk_surjective c
    exact prependRedStandard_blockAction_one_tmul_single b hb h r u
  exact (hP ▸ Algebra.mem_top : β ∈ prependIntertwiners (k := k) (Q := Q) (Λ := Λ) b hb h) v

end Intertwine

end StendhalAlgebra

end Categorification.Stendhal

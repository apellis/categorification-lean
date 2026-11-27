/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LeftStandardization
import Categorification.WeightedKLR.RedStrands.TwoPieceBlocks
import Categorification.Algebra.CommutingFamilySingle

/-!
# The block algebra of `ℓ + 1` red strands from that of the first `ℓ`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1,
Proposition 5.3. For blocks `b_0, …, b_{ℓ+1}`, the block algebra
`B = R(b_0) ⊗ R^{λ_1}(b_1) ⊗ ⋯ ⊗ R^{λ_{ℓ+1}}(b_{ℓ+1})` of `ℓ + 1` red strands receives two
commuting algebra maps: from the block algebra `B'` of the first `ℓ` red strands
(`initBlockAlgHom`) and from the last factor `R^{λ_{ℓ+1}}(b_{ℓ+1})` (`lastBlockAlgHom`). Their
images generate `B` (`blockAlgebra_subalgebra_eq_top`). On the generators the block action of
Proposition 5.3 is the action of the block diagrams (`blockAction_tmul_one`,
`blockAction_one_tmul_single`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open KLR
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace StendhalAlgebra

section Generic

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ} {ν : Multiset I}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {b : Fin (ℓ + 1) → Multiset I}

theorem blockAction_tmul_one (hb : blockPrefix b (ℓ + 1) = ν) (a : KLRAlgebra k Q (leftBlock b)) :
    blockAction Q Λ hb (a ⊗ₜ 1) = rootBlockAction Q Λ hb 0 (Nat.succ_pos ℓ) a := by
  rw [blockAction, Algebra.TensorProduct.lift_tmul, map_one, mul_one]

theorem blockAction_one_tmul_single (hb : blockPrefix b (ℓ + 1) = ν) (r : Fin ℓ)
    (u : KLRAlgebra k Q (rightBlock b r)) :
    blockAction Q Λ hb (1 ⊗ₜ PiTensorProduct.singleAlgHom (R := k)
        (A := fun r : Fin ℓ => CycKLR k Q (redCyc Λ r) (rightBlock b r)) r
        (CycKLR.mk k Q (redCyc Λ r) _ u)) =
      rootBlockAction Q Λ hb (r.val + 1) (Nat.succ_lt_succ r.2) u := by
  rw [blockAction, Algebra.TensorProduct.lift_tmul, map_one, one_mul, cycBlocksAction,
    PiTensorProduct.liftCommuting_singleAlgHom, cycBlockAction_mk]

end Generic

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (b : Fin (ℓ + 2) → Multiset I)

local notation "B" => BlockAlgebra k Q Λ b
local notation "B'" => BlockAlgebra k Q (Λ ∘ Fin.castSucc) (initBlocks b)
local notation "Cyc" => CycKLR k Q (redCyc Λ (Fin.last ℓ)) (rightBlock b (Fin.last ℓ))
local notation "Fac" => fun r : Fin (ℓ + 1) => CycKLR k Q (redCyc Λ r) (rightBlock b r)

/-- The factors of the first `ℓ` red strands, included in the tensor product of the factors of
all `ℓ + 1`. -/
def initFactorsAlgHom :
    (⨂[k] r : Fin ℓ, CycKLR k Q (redCyc (Λ ∘ Fin.castSucc) r) (rightBlock (initBlocks b) r)) →ₐ[k]
      ⨂[k] r : Fin (ℓ + 1), CycKLR k Q (redCyc Λ r) (rightBlock b r) :=
  PiTensorProduct.liftCommuting (R := k)
    (A := fun r : Fin ℓ => CycKLR k Q (redCyc (Λ ∘ Fin.castSucc) r) (rightBlock (initBlocks b) r))
    (fun r => PiTensorProduct.singleAlgHom (R := k) (A := Fac) r.castSucc)
    fun i j h a c => PiTensorProduct.commute_singleAlgHom (R := k) (A := Fac)
      (i := i.castSucc) (j := j.castSucc)
      (fun h' => (ne_of_lt h) (Fin.castSucc_injective _ h')) a c

/-- **The block algebra of the first `ℓ` red strands in that of all `ℓ + 1`**: the identity on
`R(b_0)` and the inclusion of the factors `R^{λ_r}(b_r)`, `r ≤ ℓ`. -/
def initBlockAlgHom : B' →ₐ[k] B :=
  Algebra.TensorProduct.map (AlgHom.id k (KLRAlgebra k Q (leftBlock b))) (initFactorsAlgHom Q Λ b)

/-- **The last factor `R^{λ_{ℓ+1}}(b_{ℓ+1})` in the block algebra.** -/
def lastBlockAlgHom : Cyc →ₐ[k] B :=
  Algebra.TensorProduct.includeRight.comp
    (PiTensorProduct.singleAlgHom (R := k) (A := Fac) (Fin.last ℓ))

theorem initBlockAlgHom_tmul_one (a : KLRAlgebra k Q (leftBlock b)) :
    initBlockAlgHom Q Λ b (a ⊗ₜ 1) = a ⊗ₜ 1 := by
  rw [initBlockAlgHom, Algebra.TensorProduct.map_tmul, map_one]
  rfl

theorem initBlockAlgHom_one_tmul_single (r : Fin ℓ)
    (c : CycKLR k Q (redCyc Λ r.castSucc) (rightBlock b r.castSucc)) :
    initBlockAlgHom Q Λ b (1 ⊗ₜ PiTensorProduct.singleAlgHom (R := k)
        (A := fun r : Fin ℓ =>
          CycKLR k Q (redCyc (Λ ∘ Fin.castSucc) r) (rightBlock (initBlocks b) r)) r c) =
      1 ⊗ₜ PiTensorProduct.singleAlgHom (R := k) (A := Fac) r.castSucc c := by
  rw [initBlockAlgHom, Algebra.TensorProduct.map_tmul, map_one, initFactorsAlgHom,
    PiTensorProduct.liftCommuting_singleAlgHom]
  rfl

theorem lastBlockAlgHom_apply (c : Cyc) :
    lastBlockAlgHom Q Λ b c =
      1 ⊗ₜ PiTensorProduct.singleAlgHom (R := k) (A := Fac) (Fin.last ℓ) c := rfl

/-- A subalgebra of the block algebra containing the images of the block algebra of the first
`ℓ` red strands and of the last factor is everything. -/
theorem blockAlgebra_subalgebra_eq_top (P : Subalgebra k B)
    (h₁ : ∀ x, initBlockAlgHom Q Λ b x ∈ P) (h₂ : ∀ c, lastBlockAlgHom Q Λ b c ∈ P) :
    P = ⊤ := by
  refine PiTensorProduct.tensor_subalgebra_eq_top P (fun a => ?_) fun i a => ?_
  · rw [← initBlockAlgHom_tmul_one]
    exact h₁ _
  · induction i using Fin.lastCases with
    | last => exact h₂ a
    | cast r =>
      rw [← initBlockAlgHom_one_tmul_single]
      exact h₁ _

/-- Two algebra maps out of the block algebra agree when they agree on the images of the block
algebra of the first `ℓ` red strands and of the last factor. -/
theorem blockAlgebra_algHom_ext {S : Type*} [Ring S] [Algebra k S] {f g : B →ₐ[k] S}
    (h₁ : f.comp (initBlockAlgHom Q Λ b) = g.comp (initBlockAlgHom Q Λ b))
    (h₂ : f.comp (lastBlockAlgHom Q Λ b) = g.comp (lastBlockAlgHom Q Λ b)) : f = g := by
  have := blockAlgebra_subalgebra_eq_top Q Λ b (AlgHom.equalizer f g)
    (fun x => AlgHom.congr_fun h₁ x) (fun c => AlgHom.congr_fun h₂ c)
  exact AlgHom.ext fun x => (this ▸ Algebra.mem_top : x ∈ AlgHom.equalizer f g)

/-- The images of the block algebra of the first `ℓ` red strands and of the last factor
commute. -/
theorem commute_initBlockAlgHom_lastBlockAlgHom (x : B') (c : Cyc) :
    Commute (initBlockAlgHom Q Λ b x) (lastBlockAlgHom Q Λ b c) := by
  have hP := PiTensorProduct.tensor_subalgebra_eq_top
    ((Subalgebra.centralizer k {lastBlockAlgHom Q Λ b c}).comap (initBlockAlgHom Q Λ b))
    (fun a => ?_) fun r a => ?_
  · have hx : x ∈ ((Subalgebra.centralizer k {lastBlockAlgHom Q Λ b c}).comap
        (initBlockAlgHom Q Λ b)) := hP ▸ Algebra.mem_top
    exact (Subalgebra.mem_centralizer_iff k).1 hx _ rfl |>.symm
  · refine (Subalgebra.mem_centralizer_iff k).2 fun y hy => ?_
    rw [Set.mem_singleton_iff.1 hy]
    change lastBlockAlgHom Q Λ b c * initBlockAlgHom Q Λ b (a ⊗ₜ 1) =
      initBlockAlgHom Q Λ b (a ⊗ₜ 1) * lastBlockAlgHom Q Λ b c
    rw [initBlockAlgHom_tmul_one, lastBlockAlgHom_apply, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul]
    simp only [mul_one, one_mul]
  · refine (Subalgebra.mem_centralizer_iff k).2 fun y hy => ?_
    rw [Set.mem_singleton_iff.1 hy]
    change lastBlockAlgHom Q Λ b c * initBlockAlgHom Q Λ b (1 ⊗ₜ _) =
      initBlockAlgHom Q Λ b (1 ⊗ₜ _) * lastBlockAlgHom Q Λ b c
    rw [initBlockAlgHom_one_tmul_single, lastBlockAlgHom_apply,
      Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      (PiTensorProduct.commute_singleAlgHom (R := k) (A := Fac) (Fin.castSucc_ne_last r).symm c
        (show Fac r.castSucc from a)).eq]

end StendhalAlgebra

end Categorification.Stendhal

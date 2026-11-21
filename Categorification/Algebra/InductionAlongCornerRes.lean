/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.IdempotentEquiv
import Categorification.Algebra.InductionAlongRes
import Categorification.Algebra.InductionAlongTensor

/-!
# An idempotent piece of an induced module as an induced module

Let `φ : A →ₙ+* B`, `ψ : A' →ₙ+* B` and `φ' : A →ₙ+* A'` be nonunital ring maps. The piece
`ψ(1) (B φ(1) ⊗_A N)` of the induction of an `A`-module `N` along `φ` is
`ψ(1) B φ(1) ⊗_A N`. If the `(A', A)`-bimodule `ψ(1) B φ(1)` is isomorphic to `A' φ'(1)`, this
piece is therefore the induction of `N` along `φ'` (`fixSubIndEquiv`). This is the module-level
form of a bimodule isomorphism such as B. Webster, *Knot invariants and higher representation
theory*, arXiv:1309.3796v3, Proposition 4.32, used in the dimension count of the proof of
Proposition 5.5.
-/

namespace Categorification

open MulOpposite

noncomputable section

namespace InductionAlong

universe u w

variable {A A' B : Type u} [Ring A] [Ring A'] [Ring B] {φ : A →ₙ+* B} {ψ : A' →ₙ+* B}
  {φ' : A →ₙ+* A'} {N : Type w} [AddCommGroup N] [Module A N]

/-- A bimodule isomorphism `A' φ'(1) ≅ ψ(1) B φ(1)`, the latter given as the elements `z` of
`B φ(1)` with `ψ(1) z = z`. -/
structure CornerIso (φ : A →ₙ+* B) (ψ : A' →ₙ+* B) (φ' : A →ₙ+* A') where
  /-- The map `A' φ'(1) → B φ(1)`. -/
  toFun : Corner φ' →+ Corner φ
  /-- The inverse, defined on all of `B φ(1)` and vanishing on `(1 - ψ(1)) B φ(1)`. -/
  invFun : Corner φ →+ Corner φ'
  fixed : ∀ g, ψ 1 * (toFun g).1 = (toFun g).1
  inv_toFun : ∀ g, invFun (toFun g) = g
  toFun_inv : ∀ z, (toFun (invFun z)).1 = ψ 1 * z.1
  inv_unit : ∀ z, invFun z = invFun ⟨ψ 1 * z.1, by
    change ψ 1 * z.1 * φ 1 = ψ 1 * z.1
    rw [mul_assoc, z.2]⟩
  map_left : ∀ (a : A') g, (toFun (a • g)).1 = ψ a * (toFun g).1
  map_right : ∀ (a : A) g, toFun (op a • g) = op a • toFun g
  inv_right : ∀ (a : A) z, invFun (op a • z) = op a • invFun z

namespace CornerIso

variable (c : CornerIso φ ψ φ')

/-- `g ⊗ n ↦ c(g) ⊗ n`. -/
def fwd : Ind N φ' →+ Ind N φ :=
  Ind.liftAdd (fun g n => Ind.tmul (c.toFun g) n)
    (fun g g' n => by rw [map_add, Ind.add_tmul])
    (fun g n n' => Ind.tmul_add _ n n')
    (fun g a n => by rw [c.map_right, Ind.op_smul_tmul])

/-- `z ⊗ n ↦ c⁻¹(ψ(1) z) ⊗ n`. -/
def bwd : Ind N φ →+ Ind N φ' :=
  Ind.liftAdd (fun z n => Ind.tmul (c.invFun z) n)
    (fun z z' n => by rw [map_add, Ind.add_tmul])
    (fun z n n' => Ind.tmul_add _ n n')
    (fun z a n => by rw [c.inv_right, Ind.op_smul_tmul])

theorem fwd_tmul (g : Corner φ') (n : N) : c.fwd (Ind.tmul g n) = Ind.tmul (c.toFun g) n := rfl

theorem bwd_tmul (z : Corner φ) (n : N) : c.bwd (Ind.tmul z n) = Ind.tmul (c.invFun z) n := rfl

theorem bwd_fwd (x : Ind N φ') : c.bwd (c.fwd x) = x := by
  induction x using Ind.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul g n => rw [fwd_tmul, bwd_tmul, c.inv_toFun]
  | add s t hs ht => rw [map_add, map_add, hs, ht]

theorem fwd_bwd (x : Ind N φ) : c.fwd (c.bwd x) = ψ 1 • x := by
  induction x using Ind.induction_on with
  | zero => rw [map_zero, map_zero, smul_zero]
  | tmul z n =>
    rw [bwd_tmul, fwd_tmul, Ind.smul_tmul]
    congr 1
    exact Subtype.ext (c.toFun_inv z)
  | add s t hs ht => rw [map_add, map_add, hs, ht, smul_add]

theorem fixed_fwd (x : Ind N φ') : ψ 1 • c.fwd x = c.fwd x := by
  induction x using Ind.induction_on with
  | zero => rw [map_zero, smul_zero]
  | tmul g n =>
    rw [fwd_tmul, Ind.smul_tmul]
    congr 1
    exact Subtype.ext (c.fixed g)
  | add s t hs ht => rw [map_add, smul_add, hs, ht]

theorem fwd_smul (a : A') (x : Ind N φ') : c.fwd (a • x) = ψ a • c.fwd x := by
  induction x using Ind.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul g n =>
    rw [Ind.smul_tmul, fwd_tmul, fwd_tmul, Ind.smul_tmul]
    congr 1
    exact Subtype.ext (c.map_left a g)
  | add s t hs ht => rw [smul_add, map_add, map_add, hs, ht, smul_add]

end CornerIso

variable (k : Type*) [CommRing k] [Algebra k A'] [Algebra k B]
  (hψ : ∀ c : k, ψ (algebraMap k A' c) = algebraMap k B c * ψ 1)

include hψ in
theorem CornerIso.bwd_smul_of_fixed (c : CornerIso φ ψ φ') (r : k) (y : Ind N φ)
    (hy : ψ 1 • y = y) : c.bwd (algebraMap k B r • y) = algebraMap k A' r • c.bwd y := by
  apply (show Function.Injective (c.fwd (N := N)) from
    Function.LeftInverse.injective c.bwd_fwd)
  rw [c.fwd_smul, c.fwd_bwd, c.fwd_bwd, hψ, smul_smul, hy, Algebra.commutes]

include hψ in
/-- **The piece `ψ(1) Ind_φ N` is `Ind_{φ'} N`** for a bimodule isomorphism
`A' φ'(1) ≅ ψ(1) B φ(1)`. -/
def fixSubIndEquiv (c : CornerIso φ ψ φ') :
    fixSub k (IndK k N φ) (ψ 1) ≃ₗ[k] IndK k N φ' where
  toFun x := c.bwd (N := N) x.1
  invFun x := ⟨c.fwd (N := N) x, c.fixed_fwd x⟩
  map_add' x y := map_add (c.bwd (N := N)) x.1 y.1
  map_smul' r x := CornerIso.bwd_smul_of_fixed k hψ c r x.1 x.2
  left_inv x := Subtype.ext ((c.fwd_bwd (N := N) x.1).trans x.2)
  right_inv x := c.bwd_fwd (N := N) x

include hψ in
theorem finrank_fixSub_ind (c : CornerIso φ ψ φ') :
    Module.finrank k (fixSub k (IndK k N φ) (ψ 1)) = Module.finrank k (IndK k N φ') :=
  (fixSubIndEquiv k hψ c).finrank_eq

end InductionAlong

end

end Categorification

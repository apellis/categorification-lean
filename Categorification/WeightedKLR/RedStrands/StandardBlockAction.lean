/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.RedStrands.StandardBlockMaps
import Categorification.Algebra.CommutingFamily

/-!
# The block action on the standard module `S_α`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1,
Proposition 5.3.

For a decomposition `b_0 + ⋯ + b_ℓ = ν` of the black weight and the root function `α` of the
blocks, the block maps `R(b_j) → e_α T̃^λ e_α` (`StendhalAlgebra.blockHom`) act on the standard
module `S_α`. On the block `b_{r+1}`, immediately to the right of the red strand `λ_r`, the
cyclotomic ideal of `λ_r` acts by zero (`StendhalAlgebra.rootAction_blockHom_cycElt`), so the
action factors through the cyclotomic quotient `R^{λ_r}(b_{r+1})`. The actions of different
blocks commute, which assembles them into an algebra map
`R(b_0) ⊗ R^{λ_0}(b_1) ⊗ ⋯ ⊗ R^{λ_{ℓ-1}}(b_ℓ) → End_{T̃^λ}(S_α)`.

The cyclotomic quotients here are those of a single red strand, `T^{λ_r}_{μ_r} = R^{λ_r}(b_{r+1})`
in the notation of the source; the indices of the red strands start at `0`.

## Main definitions

* `Stendhal.StendhalAlgebra.cycBlockAction`: the action of `R^{λ_r}(b_{r+1})` on `S_α`.
* `Stendhal.StendhalAlgebra.blockAction`: the algebra map of Proposition 5.3.
-/

namespace Categorification.Stendhal

open KLR KLRAlgebra
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
  {b : Fin (ℓ + 1) → Multiset I}

/-- `AlgHom.commutes` with both algebra structures named explicitly. -/
theorem algHom_commutes_of {A B : Type*} [Semiring A] [Semiring B] (iA : Algebra k A)
    (iB : Algebra k B) (f : @AlgHom k A B _ _ _ iA iB) (c : k) :
    f (@algebraMap k A _ _ iA c) = @algebraMap k B _ _ iB c :=
  f.commutes c

/-- In a corner `E (e B e) E` of a corner, the two `k`-algebra structures obtained by applying
twice either `KLR.cornerAlgebra` or `IsIdempotentElem.instAlgebraCorner_categorification` have
the same unit map. -/
theorem algebraMap_nestedCorner {B : Type*} [Ring B] [Algebra k B] {e : B}
    (he : IsIdempotentElem e) {E : he.Corner} (hE : IsIdempotentElem E) (c : k) :
    @algebraMap k hE.Corner _ _
        (@KLR.cornerAlgebra k _ he.Corner _ (KLR.cornerAlgebra he) E hE) c =
      @algebraMap k hE.Corner _ _
        (@IsIdempotentElem.instAlgebraCorner_categorification k he.Corner _ _
          (IsIdempotentElem.instAlgebraCorner_categorification he) E hE) c := by
  refine Subtype.ext (Subtype.ext ?_)
  have hx := (Subsemigroup.mem_corner_iff he).1 E.2
  show algebraMap k B c * e * E.1 = c • E.1
  rw [mul_assoc, hx.1, Algebra.smul_def]

namespace StendhalAlgebra

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

/-- The cyclotomic weight `X^{⟨α_i^∨, λ_r⟩}` of the red strand `λ_r`. -/
noncomputable abbrev redCyc (Λ : Fin ℓ → I →₀ ℕ) (r : Fin ℓ) : I → Polynomial k :=
  fun i => Polynomial.X ^ Λ r i

/-- The block `b_{r+1}` immediately to the right of the red strand `λ_r`. -/
abbrev rightBlock (b : Fin (ℓ + 1) → Multiset I) (r : Fin ℓ) : Multiset I :=
  b ⟨r.val + 1, Nat.succ_lt_succ r.2⟩

local notation "EndS" =>
  Module.End (StendhalAlgebra k Q Λ ν)ᵐᵒᵖ (rootStandard (ν := ν) Q Λ (blockRoot b))

variable (Q Λ) in
/-- The action of `R(b_j)` on the standard module `S_α` through the block map of the `j`-th
black block (arXiv:1309.3796v3, proof of Proposition 5.3). -/
noncomputable def rootBlockAction (hb : blockPrefix b (ℓ + 1) = ν) (j : ℕ) (hj : j < ℓ + 1) :
    KLRAlgebra k Q (b ⟨j, hj⟩) →ₐ[k] EndS :=
  AlgHom.mk
    { toFun := fun a => rootAction (ν := ν) Q Λ (blockRoot b) (blockHom Q Λ hb j hj a)
      map_one' := by simp only [map_one]
      map_mul' := fun a a' => by simp only [map_mul]
      map_zero' := by simp only [map_zero]
      map_add' := fun a a' => by simp only [map_add] } fun c => by
    show rootAction (ν := ν) Q Λ (blockRoot b) (blockHom Q Λ hb j hj (algebraMap k _ c)) = _
    rw [algHom_commutes_of _ _ (blockHom Q Λ hb j hj) c, algebraMap_nestedCorner,
      algHom_commutes_of _ _ (rootAction (ν := ν) Q Λ (blockRoot b)) c]

theorem rootBlockAction_apply (hb : blockPrefix b (ℓ + 1) = ν) (j : ℕ) (hj : j < ℓ + 1)
    (a : KLRAlgebra k Q (b ⟨j, hj⟩)) :
    rootBlockAction Q Λ hb j hj a =
      rootAction (ν := ν) Q Λ (blockRoot b) (blockHom Q Λ hb j hj a) :=
  rfl

theorem commute_rootBlockAction (hb : blockPrefix b (ℓ + 1) = ν) {j j' : ℕ}
    (hj : j < ℓ + 1) (hj' : j' < ℓ + 1) (h : j < j') (a : KLRAlgebra k Q (b ⟨j, hj⟩))
    (a' : KLRAlgebra k Q (b ⟨j', hj'⟩)) :
    Commute (rootBlockAction Q Λ hb j hj a) (rootBlockAction Q Λ hb j' hj' a') :=
  (commute_blockHom hb hj hj' h a a').map (rootAction (ν := ν) Q Λ (blockRoot b))

variable (Q Λ) in
/-- The action of the cyclotomic quotient `R^{λ_r}(b_{r+1})` on the standard module `S_α`
(arXiv:1309.3796v3, proof of Proposition 5.3). -/
noncomputable def cycBlockAction (hb : blockPrefix b (ℓ + 1) = ν) (r : Fin ℓ) :
    CycKLR k Q (redCyc Λ r) (rightBlock b r) →ₐ[k] EndS :=
  CycKLR.lift (rootBlockAction Q Λ hb (r.val + 1) (Nat.succ_lt_succ r.2))
    (rootAction_blockHom_cycElt hb r)

theorem cycBlockAction_mk (hb : blockPrefix b (ℓ + 1) = ν) (r : Fin ℓ)
    (u : KLRAlgebra k Q (rightBlock b r)) :
    cycBlockAction Q Λ hb r (CycKLR.mk k Q (redCyc Λ r) _ u) =
      rootBlockAction Q Λ hb (r.val + 1) (Nat.succ_lt_succ r.2) u :=
  CycKLR.lift_mk _ _ u

theorem commute_cycBlockAction (hb : blockPrefix b (ℓ + 1) = ν) {r r' : Fin ℓ} (h : r < r')
    (a : CycKLR k Q (redCyc Λ r) (rightBlock b r))
    (a' : CycKLR k Q (redCyc Λ r') (rightBlock b r')) :
    Commute (cycBlockAction Q Λ hb r a) (cycBlockAction Q Λ hb r' a') := by
  obtain ⟨u, rfl⟩ := CycKLR.mk_surjective a
  obtain ⟨u', rfl⟩ := CycKLR.mk_surjective a'
  rw [cycBlockAction_mk, cycBlockAction_mk]
  exact commute_rootBlockAction hb _ _ (by simpa using h) u u'

variable (Q Λ) in
/-- The action of `R^{λ_0}(b_1) ⊗ ⋯ ⊗ R^{λ_{ℓ-1}}(b_ℓ)` on `S_α`. -/
noncomputable def cycBlocksAction (hb : blockPrefix b (ℓ + 1) = ν) :
    (⨂[k] r : Fin ℓ, CycKLR k Q (redCyc Λ r) (rightBlock b r)) →ₐ[k] EndS :=
  PiTensorProduct.liftCommuting (cycBlockAction Q Λ hb)
    fun _ _ h => commute_cycBlockAction hb h

/-- The leftmost black block `b_0`. -/
abbrev leftBlock (b : Fin (ℓ + 1) → Multiset I) : Multiset I :=
  b ⟨0, Nat.succ_pos ℓ⟩

variable (Q Λ) in
/-- **Proposition 5.3** of arXiv:1309.3796v3: the block maps induce an algebra map
`R(b_0) ⊗ R^{λ_0}(b_1) ⊗ ⋯ ⊗ R^{λ_{ℓ-1}}(b_ℓ) → End_{T̃^λ}(S_α)`, sending
`a_0 ⊗ a_1 ⊗ ⋯ ⊗ a_ℓ` to the action of the diagram placing `a_j` on the `j`-th black block. -/
noncomputable def blockAction (hb : blockPrefix b (ℓ + 1) = ν) :
    KLRAlgebra k Q (leftBlock b) ⊗[k]
        (⨂[k] r : Fin ℓ, CycKLR k Q (redCyc Λ r) (rightBlock b r)) →ₐ[k] EndS :=
  Algebra.TensorProduct.lift (rootBlockAction Q Λ hb 0 (Nat.succ_pos ℓ))
    (cycBlocksAction Q Λ hb) fun a t =>
      PiTensorProduct.commute_liftCommuting _ _ (fun r a' => by
        obtain ⟨u, rfl⟩ := CycKLR.mk_surjective a'
        rw [cycBlockAction_mk]
        exact commute_rootBlockAction hb _ _ (Nat.succ_pos _) a u) t

theorem blockAction_tmul_tprod (hb : blockPrefix b (ℓ + 1) = ν)
    (a : KLRAlgebra k Q (leftBlock b)) (u : ∀ r : Fin ℓ, KLRAlgebra k Q (rightBlock b r)) :
    blockAction Q Λ hb (a ⊗ₜ PiTensorProduct.tprod k
        fun r => CycKLR.mk k Q (redCyc Λ r) _ (u r)) =
      rootBlockAction Q Λ hb 0 (Nat.succ_pos ℓ) a *
        (List.ofFn fun r => rootBlockAction Q Λ hb (r.val + 1) (Nat.succ_lt_succ r.2) (u r)).prod
    := by
  simp [blockAction, cycBlocksAction, cycBlockAction_mk]
  rfl

end StendhalAlgebra

end Categorification.Stendhal

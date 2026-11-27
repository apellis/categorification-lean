/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongTensorFactorAction

/-!
# Induction commutes with a balanced tensor product on the other side

Let `L` be a `(T, R)`-bimodule and `N` a left module over `R` and over `A` with commuting
actions. Then `L ⊗_R N` is an `A`-module through the action on `N`, and inducing it along a
nonunital map `φ : A → B` is `L ⊗_R (Bφ(1) ⊗_A N)`:
`Bφ(1) ⊗_A (L ⊗_R N) ≅ L ⊗_R (Bφ(1) ⊗_A N)`, `z ⊗ (l ⊗ n) ↦ l ⊗ (z ⊗ n)`
(`indBalancedEquiv`). The statement is made for modules `X ≅ L ⊗_R N` and `N' ≅ Ind_φ N`
identified with these compatibly with the actions, and records how the actions of `B` and of `T`
are carried (`indBalancedEquiv_smul`, `indBalancedEquiv_map`). In B. Webster, *Knot invariants
and higher representation theory*, arXiv:1309.3796v3, proof of Proposition 5.5, `F`-part, this
moves the induction `₂Fᵢ` along the last cyclotomic factor through the left standard module of
the first red strands.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace Categorification

namespace InductionAlong

open MulOpposite
open scoped TensorProduct

universe u w

variable {k : Type*} [CommRing k] {T : Type*} [Ring T] [Algebra k T] {R : Type*} [Ring R]
  [Algebra k R] {A B : Type u} [Ring A] [Ring B] [Algebra k A] [Algebra k B] {φ : A →ₙ+* B}
  (hφ : ∀ (c : k) (t : A), φ (c • t) = c • φ t)
  {L : Type*} [AddCommGroup L] [Module k L] [Module T L] [IsScalarTower k T L] [Module Rᵐᵒᵖ L]
  [SMulCommClass T Rᵐᵒᵖ L]
  {N : Type w} [AddCommGroup N] [Module k N] [Module R N] [IsScalarTower k R N] [Module A N]
  [SMulCommClass R A N]
  {N' : Type*} [AddCommGroup N'] [Module k N'] [Module R N'] [IsScalarTower k R N']
  {X : Type w} [AddCommGroup X] [Module k X] [Module A X] [IsScalarTower k A X]
  (σ : A → N →ₗ[R] N) (hσ : ∀ a n, σ a n = a • n)
  (g : X ≃ₗ[k] BalancedTensor k T R L N)
  (hg : ∀ (a : A) (x : X), g (a • x) = BalancedTensor.mapRight (σ a) (g x))
  (f : IndK k N φ ≃ₗ[k] N')

omit [Algebra k A] in
/-- Induction on elements of `IndK k N φ`. -/
@[elab_as_elim]
theorem IndK.induction_on' {M : Type w} [AddCommGroup M] [Module A M] {motive : IndK k M φ → Prop}
    (t : IndK k M φ) (zero : motive 0) (tmul : ∀ z n, motive (IndK.tmul z n))
    (add : ∀ s t, motive s → motive t → motive (s + t)) : motive t :=
  Ind.induction_on t zero tmul add

/-- The action of `r ∈ R` on `N`, an `A`-linear map. -/
def rSmulA (r : R) : N →ₗ[A] N where
  toFun n := r • n
  map_add' := smul_add r
  map_smul' a n := smul_comm r a n

variable (hf : ∀ (r : R) (w : IndK k N φ), f (IndK.map (rSmulA r) w) = r • f w)

include hf in
/-- `n ↦ f (z ⊗ n)`, an `R`-linear map. -/
def indBalancedSlice (z : Corner φ) : N →ₗ[R] N' where
  toFun n := f (IndK.tmul z n)
  map_add' n n' := by
    rw [← map_add]
    exact congrArg f (Ind.tmul_add z n n')
  map_smul' r n := hf r (IndK.tmul z n)

theorem indBalancedSlice_apply (z : Corner φ) (n : N) :
    indBalancedSlice f hf z n = f (IndK.tmul z n) := rfl

theorem indBalancedSlice_add (z z' : Corner φ) :
    indBalancedSlice f hf (z + z') = indBalancedSlice f hf z + indBalancedSlice f hf z' :=
  LinearMap.ext fun n => by
    rw [LinearMap.add_apply, indBalancedSlice_apply, indBalancedSlice_apply,
      indBalancedSlice_apply, ← map_add]
    exact congrArg f (Ind.add_tmul z z' n)

include hσ in
theorem indBalancedSlice_op_smul (z : Corner φ) (a : A) :
    indBalancedSlice f hf (op a • z) = (indBalancedSlice f hf z).comp (σ a) :=
  LinearMap.ext fun n => by
    rw [LinearMap.comp_apply, indBalancedSlice_apply, indBalancedSlice_apply, hσ]
    exact congrArg f (Ind.op_smul_tmul z a n)

theorem mapRight_add_apply (h h' : N →ₗ[R] N') (y : BalancedTensor k T R L N) :
    BalancedTensor.mapRight (h + h') y =
      BalancedTensor.mapRight h y + BalancedTensor.mapRight h' y := by
  induction y using BalancedTensor.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, add_zero]
  | tmul l n =>
    rw [BalancedTensor.mapRight_tmul, BalancedTensor.mapRight_tmul, BalancedTensor.mapRight_tmul,
      LinearMap.add_apply, BalancedTensor.tmul_add]
  | add y y' hy hy' => rw [map_add, map_add, map_add, hy, hy', add_add_add_comm]

/-- The underlying additive map of `indBalancedEquiv`, `z ⊗ (l ⊗ n) ↦ l ⊗ f (z ⊗ n)`. -/
def indBalancedFwd : IndK k X φ →+ BalancedTensor k T R L N' :=
  Ind.liftAdd (fun z x => BalancedTensor.mapRight (indBalancedSlice f hf z) (g x))
    (fun z z' x => by rw [indBalancedSlice_add, mapRight_add_apply])
    (fun z x x' => by rw [map_add, map_add])
    (fun z a x => by
      rw [indBalancedSlice_op_smul σ hσ f hf, hg, BalancedTensor.mapRight_comp,
        LinearMap.comp_apply])

theorem indBalancedFwd_tmul (z : Corner φ) (x : X) :
    indBalancedFwd σ hσ g hg f hf (IndK.tmul z x) =
      BalancedTensor.mapRight (indBalancedSlice f hf z) (g x) := rfl

include hσ hg in
theorem smul_symm_tmul (a : A) (l : L) (n : N) :
    a • g.symm (BalancedTensor.tmul l n) = g.symm (BalancedTensor.tmul l (a • n)) := by
  apply g.injective
  rw [hg, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
    BalancedTensor.mapRight_tmul, hσ]

/-- For `l ∈ L`, the map `z ⊗ n ↦ z ⊗ g⁻¹ (l ⊗ n)`. -/
def indBalancedInner (l : L) : IndK k N φ →ₗ[B] IndK k X φ :=
  Ind.lift (fun z n => IndK.tmul z (g.symm (BalancedTensor.tmul l n)))
    (fun z z' n => Ind.add_tmul z z' _)
    (fun z n n' => by
      rw [BalancedTensor.tmul_add, map_add]
      exact Ind.tmul_add z _ _)
    (fun z a n => by
      rw [← smul_symm_tmul σ hσ g hg]
      exact Ind.op_smul_tmul z a _)
    (fun b z n => (Ind.smul_tmul b z _).symm)

theorem indBalancedInner_tmul (l : L) (z : Corner φ) (n : N) :
    indBalancedInner σ hσ g hg l (IndK.tmul z n) =
      IndK.tmul z (g.symm (BalancedTensor.tmul l n)) := rfl

theorem indBalancedInner_add (l l' : L) (w : IndK k N φ) :
    indBalancedInner σ hσ g hg (l + l') w =
      indBalancedInner σ hσ g hg l w + indBalancedInner σ hσ g hg l' w := by
  induction w using IndK.induction_on' with
  | zero => rw [map_zero, map_zero, map_zero, add_zero]
  | tmul z n =>
    change IndK.tmul z (g.symm (BalancedTensor.tmul (l + l') n)) =
      IndK.tmul z (g.symm (BalancedTensor.tmul l n)) +
        IndK.tmul z (g.symm (BalancedTensor.tmul l' n))
    rw [BalancedTensor.add_tmul, map_add]
    exact Ind.tmul_add z _ _
  | add s t hs ht => rw [map_add, map_add, map_add, hs, ht, add_add_add_comm]

include hφ in
theorem indBalancedInner_smul (c : k) (l : L) (w : IndK k N φ) :
    indBalancedInner σ hσ g hg (c • l) w = c • indBalancedInner σ hσ g hg l w := by
  induction w using IndK.induction_on' with
  | zero => rw [map_zero, map_zero, smul_zero]
  | tmul z n =>
    change IndK.tmul z (g.symm (BalancedTensor.tmul (c • l) n)) =
      c • IndK.tmul z (g.symm (BalancedTensor.tmul l n))
    rw [BalancedTensor.smul_tmul, map_smul]
    exact Ind.tmul_algebraMap_smul (k := k) (N := X) (φ := φ) hφ z c _
  | add s t hs ht => rw [map_add, map_add, hs, ht, smul_add]

include hf in
theorem symm_smul_apply (r : R) (n' : N') :
    f.symm (r • n') = IndK.map (rSmulA r) (f.symm n') := by
  apply f.injective
  rw [LinearEquiv.apply_symm_apply, hf, LinearEquiv.apply_symm_apply]

/-- The bilinear map `(l, n') ↦ (z ⊗ n ↦ z ⊗ g⁻¹ (l ⊗ n)) (f⁻¹ n')`. -/
def indBalancedBil : L →ₗ[k] N' →ₗ[k] IndK k X φ :=
  LinearMap.mk₂ k (fun l n' => indBalancedInner σ hσ g hg l (f.symm n'))
    (fun l l' n' => indBalancedInner_add σ hσ g hg l l' _)
    (fun c l n' => indBalancedInner_smul hφ σ hσ g hg c l _)
    (fun l n' n'' => by rw [map_add, map_add])
    (fun c l n' => by rw [map_smul, ← IndK.algebraMap_smul, map_smul, IndK.algebraMap_smul])

include hf in
theorem indBalancedBil_balanced (l : L) (r : R) (n' : N') :
    indBalancedBil hφ σ hσ g hg f (op r • l) n' = indBalancedBil hφ σ hσ g hg f l (r • n') := by
  change indBalancedInner σ hσ g hg (op r • l) (f.symm n') =
    indBalancedInner σ hσ g hg l (f.symm (r • n'))
  rw [symm_smul_apply f hf]
  induction f.symm n' using IndK.induction_on' with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul z n =>
    change IndK.tmul z (g.symm (BalancedTensor.tmul (op r • l) n)) =
      IndK.tmul z (g.symm (BalancedTensor.tmul l (r • n)))
    rw [BalancedTensor.op_smul_tmul]
  | add s t hs ht => rw [map_add, map_add, map_add, hs, ht]

/-- The inverse of `indBalancedEquiv`, `l ⊗ f (z ⊗ n) ↦ z ⊗ g⁻¹ (l ⊗ n)`. -/
def indBalancedBwd : BalancedTensor k T R L N' →ₗ[k] IndK k X φ :=
  BalancedTensor.lift (indBalancedBil hφ σ hσ g hg f) (indBalancedBil_balanced hφ σ hσ g hg f hf)

theorem indBalancedBwd_tmul (l : L) (n' : N') :
    indBalancedBwd hφ σ hσ g hg f hf (BalancedTensor.tmul l n') =
      indBalancedInner σ hσ g hg l (f.symm n') := rfl

theorem indBalancedBwd_fwd (w : IndK k X φ) :
    indBalancedBwd hφ σ hσ g hg f hf (indBalancedFwd σ hσ g hg f hf w) = w := by
  induction w using IndK.induction_on' with
  | zero => rw [map_zero, map_zero]
  | tmul z x =>
    change indBalancedBwd hφ σ hσ g hg f hf
      (BalancedTensor.mapRight (indBalancedSlice f hf z) (g x)) = IndK.tmul z x
    rw [← g.symm_apply_apply x]
    induction g x using BalancedTensor.induction_on with
    | zero =>
      rw [map_zero, map_zero, map_zero]
      exact (Ind.tmul_zero z).symm
    | tmul l n =>
      rw [LinearEquiv.apply_symm_apply, BalancedTensor.mapRight_tmul, indBalancedBwd_tmul,
        indBalancedSlice_apply, LinearEquiv.symm_apply_apply]
      rfl
    | add y y' hy hy' =>
      rw [LinearEquiv.apply_symm_apply] at hy hy' ⊢
      rw [map_add, map_add, hy, hy', map_add]
      exact (Ind.tmul_add z _ _).symm
  | add s t hs ht => rw [map_add, map_add, hs, ht]

theorem indBalancedFwd_bwd (y : BalancedTensor k T R L N') :
    indBalancedFwd σ hσ g hg f hf (indBalancedBwd hφ σ hσ g hg f hf y) = y := by
  induction y using BalancedTensor.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul l n' =>
    rw [indBalancedBwd_tmul, ← f.apply_symm_apply n']
    induction f.symm n' using IndK.induction_on' with
    | zero => rw [map_zero, map_zero, map_zero, map_zero, BalancedTensor.tmul_zero]
    | tmul z n =>
      rw [LinearEquiv.symm_apply_apply, indBalancedInner_tmul, indBalancedFwd_tmul,
        LinearEquiv.apply_symm_apply, BalancedTensor.mapRight_tmul, indBalancedSlice_apply]
    | add s t hs ht =>
      rw [LinearEquiv.symm_apply_apply] at hs ht ⊢
      rw [map_add, map_add, hs, ht, map_add, BalancedTensor.tmul_add]
  | add y y' hy hy' => rw [map_add, map_add, hy, hy']

/-- **Induction commutes with `L ⊗_R -`**: `Ind_φ (L ⊗_R N) ≅ L ⊗_R Ind_φ N`. -/
def indBalancedEquiv : IndK k X φ ≃+ BalancedTensor k T R L N' where
  toFun := indBalancedFwd σ hσ g hg f hf
  invFun := indBalancedBwd hφ σ hσ g hg f hf
  left_inv := indBalancedBwd_fwd hφ σ hσ g hg f hf
  right_inv := indBalancedFwd_bwd hφ σ hσ g hg f hf
  map_add' := map_add _

theorem indBalancedEquiv_tmul (z : Corner φ) (x : X) :
    indBalancedEquiv hφ σ hσ g hg f hf (IndK.tmul z x) =
      BalancedTensor.mapRight (indBalancedSlice f hf z) (g x) := rfl

/-- **`indBalancedEquiv` carries the action of `B` to the action on `N'`.** -/
theorem indBalancedEquiv_smul (b : B) (h : N' →ₗ[R] N') (hh : ∀ w, f (b • w) = h (f w))
    (w : IndK k X φ) :
    indBalancedEquiv hφ σ hσ g hg f hf (b • w) =
      BalancedTensor.mapRight h (indBalancedEquiv hφ σ hσ g hg f hf w) := by
  induction w using IndK.induction_on' with
  | zero => rw [smul_zero, map_zero, map_zero]
  | tmul z x =>
    refine (congrArg (indBalancedEquiv hφ σ hσ g hg f hf) (Ind.smul_tmul b z x)).trans ?_
    change BalancedTensor.mapRight (indBalancedSlice f hf (b • z)) (g x) =
      BalancedTensor.mapRight h (BalancedTensor.mapRight (indBalancedSlice f hf z) (g x))
    rw [← LinearMap.comp_apply (BalancedTensor.mapRight h), ← BalancedTensor.mapRight_comp]
    congr 2
    refine LinearMap.ext fun n => ?_
    rw [LinearMap.comp_apply, indBalancedSlice_apply, indBalancedSlice_apply, ← hh]
    exact congrArg f (Ind.smul_tmul b z n).symm
  | add s t hs ht => rw [smul_add, map_add, map_add, hs, ht, map_add]

/-- **`indBalancedEquiv` carries maps of `X` acting on `L` to the same maps.** -/
theorem indBalancedEquiv_map (σT : X →ₗ[A] X) (t : T) (ht : ∀ x, g (σT x) = t • g x)
    (w : IndK k X φ) :
    indBalancedEquiv hφ σ hσ g hg f hf (IndK.map σT w) =
      t • indBalancedEquiv hφ σ hσ g hg f hf w := by
  induction w using IndK.induction_on' with
  | zero => rw [map_zero, map_zero, smul_zero]
  | tmul z x =>
    change BalancedTensor.mapRight (indBalancedSlice f hf z) (g (σT x)) =
      t • BalancedTensor.mapRight (indBalancedSlice f hf z) (g x)
    rw [ht, map_smul]
  | add s t' hs ht' => rw [map_add, map_add, hs, ht', ← smul_add, ← map_add]

end InductionAlong

end Categorification

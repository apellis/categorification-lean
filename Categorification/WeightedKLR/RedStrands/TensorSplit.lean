/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorAction

/-!
# Splitting the ordered tensor product into two blocks

The ordered tensor product `V^{λ₁} ⊗ ⋯ ⊗ V^{λ_{a+b}}` of Webster, arXiv:1309.3796v2, §4.7,
carries the action of the iterated coproduct, appending one factor at a time
(`tensorRepresentation`). Splitting off the first `a` factors identifies it, as a
representation, with the tensor product of the two blocks under the coproduct
(`tensorSplit`, `intertwines_tensorSplit`). This is coassociativity of `Δ`
([Lus] 3.1.4), and it is the input for placing the braiding of two adjacent factors
inside the ordered tensor product (Webster, arXiv:1309.3796v3, (1.1), Corollary 6.11;
v2: Corollary 6.10).

## Main definitions and results

* `pairRep`: the action of `A ⊗ A` on `M ⊗ N` from actions of `A` on `M` and `N`.
* `Intertwines`: a linear map commuting with two actions.
* `tensorSplit`: `⨂_{j < a + b} V_j ≃ (⨂_{j < a} V_j) ⊗ (⨂_{j < b} V_{a + j})`.
* `intertwines_tensorSplit`: it intertwines `tensorRepresentation` with
  `pairRep ρ ρ ∘ Δ`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993.
-/

noncomputable section

namespace Categorification.Stendhal.FirstWeight

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop
open scoped TensorProduct

local notation "𝕍" => (RatFunc.X : RatFunc ℚ)
local notation "𝕂" => RatFunc ℚ
local instance tensorSplitInst1 : NeZero 𝕍 := ⟨RatFunc.X_ne_zero⟩

/-! ### Actions on tensor products -/

section Generic

variable {A : Type*} [Ring A] [Algebra 𝕂 A]
  {M M' N N' P : Type*} [AddCommMonoid M] [Module 𝕂 M] [AddCommMonoid M'] [Module 𝕂 M']
  [AddCommMonoid N] [Module 𝕂 N] [AddCommMonoid N'] [Module 𝕂 N'] [AddCommMonoid P] [Module 𝕂 P]

/-- The action of `A ⊗ A` on `M ⊗ N` from actions of `A` on `M` and on `N`. -/
def pairRep {A B : Type*} [Ring A] [Algebra 𝕂 A] [Ring B] [Algebra 𝕂 B]
    (ρM : A →ₐ[𝕂] Module.End 𝕂 M) (ρN : B →ₐ[𝕂] Module.End 𝕂 N) :
    A ⊗[𝕂] B →ₐ[𝕂] Module.End 𝕂 (M ⊗[𝕂] N) :=
  (Module.endTensorEndAlgHom (R := 𝕂) (S := 𝕂) (A := 𝕂)).comp (Algebra.TensorProduct.map ρM ρN)

@[simp] theorem pairRep_tmul {A B : Type*} [Ring A] [Algebra 𝕂 A] [Ring B] [Algebra 𝕂 B]
    (ρM : A →ₐ[𝕂] Module.End 𝕂 M) (ρN : B →ₐ[𝕂] Module.End 𝕂 N) (a : A) (b : B) (x : M) (y : N) :
    pairRep ρM ρN (a ⊗ₜ[𝕂] b) (x ⊗ₜ[𝕂] y) = ρM a x ⊗ₜ[𝕂] ρN b y := by
  simp [pairRep, Module.endTensorEndAlgHom_apply]

/-- `f : M → M'` intertwines the actions `ρ` and `ρ'`. -/
def Intertwines {B : Type*} [Ring B] [Algebra 𝕂 B] (ρ : B →ₐ[𝕂] Module.End 𝕂 M)
    (ρ' : B →ₐ[𝕂] Module.End 𝕂 M') (f : M →ₗ[𝕂] M') : Prop :=
  ∀ b x, f (ρ b x) = ρ' b (f x)

variable {B : Type*} [Ring B] [Algebra 𝕂 B]

theorem Intertwines.comp {ρ : B →ₐ[𝕂] Module.End 𝕂 M} {ρ' : B →ₐ[𝕂] Module.End 𝕂 M'}
    {ρ'' : B →ₐ[𝕂] Module.End 𝕂 P} {f : M →ₗ[𝕂] M'} {g : M' →ₗ[𝕂] P}
    (hf : Intertwines ρ ρ' f) (hg : Intertwines ρ' ρ'' g) : Intertwines ρ ρ'' (g ∘ₗ f) :=
  fun b x ↦ by rw [LinearMap.comp_apply, hf, hg, LinearMap.comp_apply]

theorem Intertwines.id (ρ : B →ₐ[𝕂] Module.End 𝕂 M) : Intertwines ρ ρ LinearMap.id :=
  fun _ _ ↦ rfl

theorem Intertwines.restrict {C : Type*} [Ring C] [Algebra 𝕂 C] {ρ : B →ₐ[𝕂] Module.End 𝕂 M}
    {ρ' : B →ₐ[𝕂] Module.End 𝕂 M'} {f : M →ₗ[𝕂] M'} (hf : Intertwines ρ ρ' f) (φ : C →ₐ[𝕂] B) :
    Intertwines (ρ.comp φ) (ρ'.comp φ) f :=
  fun c x ↦ hf (φ c) x

/-- The inverse of an intertwining equivalence intertwines. -/
theorem Intertwines.symm {ρ : B →ₐ[𝕂] Module.End 𝕂 M} {ρ' : B →ₐ[𝕂] Module.End 𝕂 M'}
    {e : M ≃ₗ[𝕂] M'} (he : Intertwines ρ ρ' e.toLinearMap) :
    Intertwines ρ' ρ e.symm.toLinearMap := fun b x ↦ by
  apply e.injective
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  have := he b (e.symm x)
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at this
  exact this.symm

theorem Intertwines.tensorMap {ρ₁ : A →ₐ[𝕂] Module.End 𝕂 M} {ρ₁' : A →ₐ[𝕂] Module.End 𝕂 M'}
    {ρ₂ : A →ₐ[𝕂] Module.End 𝕂 N} {ρ₂' : A →ₐ[𝕂] Module.End 𝕂 N'} {f : M →ₗ[𝕂] M'}
    {g : N →ₗ[𝕂] N'} (hf : Intertwines ρ₁ ρ₁' f) (hg : Intertwines ρ₂ ρ₂' g) :
    Intertwines (pairRep ρ₁ ρ₂) (pairRep ρ₁' ρ₂') (TensorProduct.map f g) := by
  intro t z
  induction t using TensorProduct.inductionOn with
  | add s t hs ht => simp only [map_add, LinearMap.add_apply, hs, ht]
  | tmul a b =>
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => simp only [map_add, hz, hz']
    | tmul x y => simp [hf a x, hg b y]

/-- `pairRep` of a composite action. -/
theorem pairRep_comp_left {C : Type*} [Ring C] [Algebra 𝕂 C] (ρM : C →ₐ[𝕂] Module.End 𝕂 M)
    (φ : A →ₐ[𝕂] C) (ρN : A →ₐ[𝕂] Module.End 𝕂 N) (t : A ⊗[𝕂] A) :
    pairRep (ρM.comp φ) ρN t =
      (Module.endTensorEndAlgHom (R := 𝕂) (S := 𝕂) (A := 𝕂)).comp
        (Algebra.TensorProduct.map ρM ρN) (Algebra.TensorProduct.map φ (AlgHom.id 𝕂 A) t) := by
  induction t using TensorProduct.inductionOn with
  | add s t hs ht => simp only [map_add, hs, ht]
  | tmul a b => simp [pairRep]

end Generic

/-! ### Associativity -/

section Assoc

variable {M₁ M₂ M₃ : Type*} [AddCommMonoid M₁] [Module 𝕂 M₁] [AddCommMonoid M₂] [Module 𝕂 M₂]
  [AddCommMonoid M₃] [Module 𝕂 M₃] {I Y : Type*} [DecidableEq I] [AddCommGroup Y]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y}

local notation "𝕌" => LieLean.QuantumGroup R 𝕍
local notation "Δ" => comul R 𝕍

/-- The associator `(M₁ ⊗ M₂) ⊗ M₃ ≃ M₁ ⊗ (M₂ ⊗ M₃)` intertwines the two iterated coproduct
actions; this is coassociativity of `Δ`. -/
theorem intertwines_assoc (ρ₁ : 𝕌 →ₐ[𝕂] Module.End 𝕂 M₁) (ρ₂ : 𝕌 →ₐ[𝕂] Module.End 𝕂 M₂)
    (ρ₃ : 𝕌 →ₐ[𝕂] Module.End 𝕂 M₃) :
    Intertwines ((pairRep ((pairRep ρ₁ ρ₂).comp Δ) ρ₃).comp Δ)
      ((pairRep ρ₁ ((pairRep ρ₂ ρ₃).comp Δ)).comp Δ)
      (TensorProduct.assoc 𝕂 M₁ M₂ M₃).toLinearMap := by
  intro u z
  -- both sides through the triple coproduct
  have hL : ∀ w : (𝕌 ⊗[𝕂] 𝕌) ⊗[𝕂] 𝕌, ∀ z : (M₁ ⊗[𝕂] M₂) ⊗[𝕂] M₃,
      TensorProduct.assoc 𝕂 M₁ M₂ M₃
          (pairRep (pairRep ρ₁ ρ₂) ρ₃ w z) =
        pairRep ρ₁ (pairRep ρ₂ ρ₃) (Algebra.TensorProduct.assoc 𝕂 𝕂 𝕂 𝕌 𝕌 𝕌 w)
          (TensorProduct.assoc 𝕂 M₁ M₂ M₃ z) := by
    intro w z
    induction w using TensorProduct.inductionOn with
    | add s t hs ht => simp only [map_add, LinearMap.add_apply, hs, ht]
    | tmul st c =>
      induction st using TensorProduct.inductionOn with
      | add s t hs ht => simp only [TensorProduct.add_tmul, map_add, LinearMap.add_apply, hs, ht]
      | tmul a b =>
        induction z using TensorProduct.inductionOn with
        | add z z' hz hz' => simp only [map_add, hz, hz']
        | tmul xy w =>
          induction xy using TensorProduct.inductionOn with
          | add z z' hz hz' => simp only [TensorProduct.add_tmul, map_add, hz, hz']
          | tmul x y => simp
  have h1 : (pairRep ((pairRep ρ₁ ρ₂).comp Δ) ρ₃) (Δ u) =
      pairRep (pairRep ρ₁ ρ₂) ρ₃ (Algebra.TensorProduct.map Δ (AlgHom.id 𝕂 𝕌) (Δ u)) :=
    pairRep_comp_left _ _ _ _
  have h2 : ∀ t : 𝕌 ⊗[𝕂] 𝕌, pairRep ρ₁ ((pairRep ρ₂ ρ₃).comp Δ) t =
      pairRep ρ₁ (pairRep ρ₂ ρ₃) (Algebra.TensorProduct.map (AlgHom.id 𝕂 𝕌) Δ t) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | add s t hs ht => simp only [map_add, hs, ht]
    | tmul a b => simp [pairRep]
  have hc : Algebra.TensorProduct.assoc 𝕂 𝕂 𝕂 𝕌 𝕌 𝕌
      (Algebra.TensorProduct.map Δ (AlgHom.id 𝕂 𝕌) (Δ u)) =
        Algebra.TensorProduct.map (AlgHom.id 𝕂 𝕌) Δ (Δ u) :=
    congrArg (fun φ : 𝕌 →ₐ[𝕂] 𝕌 ⊗[𝕂] (𝕌 ⊗[𝕂] 𝕌) ↦ φ u) (comul_coassoc R 𝕍)
  simp only [AlgHom.comp_apply, LinearEquiv.coe_coe]
  rw [h1, hL, hc, h2]

end Assoc

/-! ### The split -/

section Split

variable {I Y : Type*} [DecidableEq I] [AddCommGroup Y]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y}

local notation "𝕌" => LieLean.QuantumGroup R 𝕍
local notation "Δ" => comul R 𝕍
local notation "ρ" => tensorRepresentation

private abbrev Fac (w : Dom R) := IrreducibleModule R 𝕍 w.1

/-- The ordered tensor product of `a + b` factors as the tensor product of its first `a` and
its last `b` factors. -/
def tensorSplit {a b : ℕ} (wt : Fin (a + b) → Dom R) :
    TensorSpace wt ≃ₗ[𝕂]
      TensorSpace (fun i : Fin a ↦ wt (Fin.castAdd b i)) ⊗[𝕂]
        TensorSpace (fun i : Fin b ↦ wt (Fin.natAdd a i)) :=
  (PiTensorProduct.reindex 𝕂 (fun j ↦ Fac (wt j)) finSumFinEquiv.symm).trans
    (PiTensorProduct.tmulEquivDep 𝕂 (fun j : Fin a ⊕ Fin b ↦ Fac (wt (finSumFinEquiv j)))).symm

theorem tensorSplit_tprod {a b : ℕ} (wt : Fin (a + b) → Dom R) (x : ∀ j, Fac (wt j)) :
    tensorSplit wt (PiTensorProduct.tprod 𝕂 x) =
      PiTensorProduct.tprod 𝕂 (fun i : Fin a ↦ x (Fin.castAdd b i)) ⊗ₜ[𝕂]
        PiTensorProduct.tprod 𝕂 (fun i : Fin b ↦ x (Fin.natAdd a i)) := by
  erw [tensorSplit, LinearEquiv.trans_apply, PiTensorProduct.reindex_tprod,
    PiTensorProduct.tmulEquivDep_symm_apply]
  rfl

/-- The action of the zero-factor tensor product is through the counit. -/
theorem tensorRepresentation_zero (wt : Fin 0 → Dom R) (u : 𝕌) (z : TensorSpace wt) :
    ρ wt u z = counit R 𝕍 u • z := rfl

/-- On `M ⊗ ⨂_∅`, the coproduct action is the action on `M`. -/
theorem pairRep_comul_empty {M : Type*} [AddCommMonoid M] [Module 𝕂 M]
    (ρM : 𝕌 →ₐ[𝕂] Module.End 𝕂 M) (w₀ : Fin 0 → Dom R) (u : 𝕌) (x : M) (e : TensorSpace w₀) :
    pairRep ρM (ρ w₀) (Δ u) (x ⊗ₜ[𝕂] e) = ρM u x ⊗ₜ[𝕂] e := by
  have key : ∀ t : 𝕌 ⊗[𝕂] 𝕌, pairRep ρM (ρ w₀) t (x ⊗ₜ[𝕂] e) =
      ρM (Algebra.TensorProduct.rid 𝕂 𝕂 𝕌
        (Algebra.TensorProduct.map (AlgHom.id 𝕂 𝕌) (counit R 𝕍) t)) x ⊗ₜ[𝕂] e := by
    intro t
    induction t using TensorProduct.inductionOn with
    | add s t hs ht => simp only [map_add, LinearMap.add_apply, hs, ht, TensorProduct.add_tmul]
    | tmul a b =>
      rw [pairRep_tmul, tensorRepresentation_zero, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply, Algebra.TensorProduct.rid_tmul, map_smul, LinearMap.smul_apply,
        TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  have hc := congrArg (fun φ : 𝕌 →ₐ[𝕂] 𝕌 ⊗[𝕂] 𝕂 ↦ φ u) (counit_lTensor_comul R 𝕍)
  simp only [AlgHom.comp_apply] at hc
  rw [key, hc]
  simp

/-- On `⨂_∅ ⊗ M`, the coproduct action is the action on `M`. -/
theorem pairRep_comul_empty_left {M : Type*} [AddCommMonoid M] [Module 𝕂 M]
    (ρM : 𝕌 →ₐ[𝕂] Module.End 𝕂 M) (w₀ : Fin 0 → Dom R) (u : 𝕌) (e : TensorSpace w₀) (x : M) :
    pairRep (ρ w₀) ρM (Δ u) (e ⊗ₜ[𝕂] x) = e ⊗ₜ[𝕂] ρM u x := by
  have key : ∀ t : 𝕌 ⊗[𝕂] 𝕌, pairRep (ρ w₀) ρM t (e ⊗ₜ[𝕂] x) =
      e ⊗ₜ[𝕂] ρM (Algebra.TensorProduct.lid 𝕂 𝕌
        (Algebra.TensorProduct.map (counit R 𝕍) (AlgHom.id 𝕂 𝕌) t)) x := by
    intro t
    induction t using TensorProduct.inductionOn with
    | add s t hs ht => simp only [map_add, LinearMap.add_apply, hs, ht, TensorProduct.tmul_add]
    | tmul a b =>
      rw [pairRep_tmul, tensorRepresentation_zero, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply, Algebra.TensorProduct.lid_tmul, map_smul, LinearMap.smul_apply,
        TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  have hc := congrArg (fun φ : 𝕌 →ₐ[𝕂] 𝕂 ⊗[𝕂] 𝕌 ↦ φ u) (counit_rTensor_comul R 𝕍)
  simp only [AlgHom.comp_apply] at hc
  rw [key, hc]
  simp

/-- The action of `n + 1` factors is the coproduct action on the first `n` and the last. -/
theorem intertwines_tensorSplitLast {n : ℕ} (wt : Fin (n + 1) → Dom R) :
    Intertwines (ρ wt)
      ((pairRep (ρ fun j : Fin n ↦ wt j.castSucc) (Algebra.lsmul 𝕂 𝕂 (Fac (wt (Fin.last n))))).comp
        Δ)
      (tensorSplitLast wt).toLinearMap := fun u z ↦ by
  change tensorSplitLast wt ((tensorSplitLast wt).symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem tensorSplit_zero {a : ℕ} (wt : Fin (a + 0) → Dom R) (z : TensorSpace wt) :
    tensorSplit wt z =
      (show TensorSpace (fun i : Fin a ↦ wt (Fin.castAdd 0 i)) from z) ⊗ₜ[𝕂]
        PiTensorProduct.tprod 𝕂 (fun i : Fin 0 ↦ i.elim0) := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    rw [map_smul, tensorSplit_tprod, TensorProduct.smul_tmul']
    congr 2
    exact funext fun i : Fin 0 ↦ i.elim0
  | add z z' hz hz' => rw [map_add, hz, hz', TensorProduct.add_tmul]

/-- `tensorSplit` intertwines the ordered action with the coproduct action on the two
blocks. -/
theorem intertwines_tensorSplit {a : ℕ} : ∀ {b : ℕ} (wt : Fin (a + b) → Dom R),
    Intertwines (ρ wt)
      ((pairRep (ρ fun i : Fin a ↦ wt (Fin.castAdd b i))
        (ρ fun i : Fin b ↦ wt (Fin.natAdd a i))).comp Δ)
      (tensorSplit wt).toLinearMap
  | 0, wt => fun u z ↦ by
    simp only [LinearEquiv.coe_coe, AlgHom.comp_apply]
    rw [tensorSplit_zero, tensorSplit_zero, pairRep_comul_empty]
    rfl
  | b + 1, wt => by
    have ih := intertwines_tensorSplit (b := b) (fun j : Fin (a + b) ↦ wt j.castSucc)
    -- `tensorSplit` factors through the last split
    have hG : (tensorSplit wt).toLinearMap =
        (TensorProduct.map LinearMap.id
            (tensorSplitLast (fun i : Fin (b + 1) ↦ wt (Fin.natAdd a i))).symm.toLinearMap) ∘ₗ
          (TensorProduct.assoc 𝕂 _ _ _).toLinearMap ∘ₗ
          (TensorProduct.map (tensorSplit (fun j : Fin (a + b) ↦ wt j.castSucc)).toLinearMap
            LinearMap.id) ∘ₗ (tensorSplitLast (ℓ := a + b) wt).toLinearMap := by
      refine PiTensorProduct.ext (MultilinearMap.ext fun x ↦ ?_)
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [tensorSplitLast_tprod, TensorProduct.map_tmul]
      simp only [LinearEquiv.coe_coe, LinearMap.id_apply, tensorSplit_tprod]
      rw [TensorProduct.assoc_tmul, TensorProduct.map_tmul, LinearMap.id_apply]
      congr 1
      simp only [LinearEquiv.coe_coe]
      rw [LinearEquiv.eq_symm_apply, tensorSplitLast_tprod]
      rfl
    rw [hG]
    exact (((intertwines_tensorSplitLast (n := a + b) wt).comp
      (Intertwines.restrict (Intertwines.tensorMap ih (Intertwines.id _)) Δ)).comp
      (intertwines_assoc _ _ _)).comp
      (Intertwines.restrict (Intertwines.tensorMap (Intertwines.id _)
        (intertwines_tensorSplitLast (fun i : Fin (b + 1) ↦ wt (Fin.natAdd a i))).symm) Δ)

/-! ### Relabelling, one factor and two factors -/

/-- The ordered tensor products of two equal weight sequences. -/
def tensorCongr {n : ℕ} {wt wt' : Fin n → Dom R} (h : wt = wt') :
    TensorSpace wt ≃ₗ[𝕂] TensorSpace wt' := by
  subst h; exact LinearEquiv.refl _ _

theorem intertwines_tensorCongr {n : ℕ} {wt wt' : Fin n → Dom R} (h : wt = wt') :
    Intertwines (ρ wt) (ρ wt') (tensorCongr h).toLinearMap := by
  subst h; exact Intertwines.id _

theorem tensorCongr_tprod {n : ℕ} {wt wt' : Fin n → Dom R} (h : wt = wt')
    (y : ∀ j, Fac (wt j)) (y' : ∀ j, Fac (wt' j)) (hy : ∀ j, HEq (y j) (y' j)) :
    tensorCongr h (PiTensorProduct.tprod 𝕂 y) = PiTensorProduct.tprod 𝕂 y' := by
  subst h
  rw [show y = y' from funext fun j ↦ eq_of_heq (hy j)]
  rfl

/-- The ordered tensor product of one factor. -/
def tensorOne (w : Fin 1 → Dom R) : TensorSpace w ≃ₗ[𝕂] Fac (w 0) :=
  PiTensorProduct.subsingletonEquiv 0

theorem tensorOne_tprod (w : Fin 1 → Dom R) (x : ∀ j, Fac (w j)) :
    tensorOne w (PiTensorProduct.tprod 𝕂 x) = x 0 :=
  PiTensorProduct.subsingletonEquiv_apply_tprod _ _

/-- Splitting off the last of one factor leaves the empty tensor product. -/
theorem tensorSplitLast_one (w : Fin 1 → Dom R) (z : TensorSpace w) :
    tensorSplitLast w z =
      PiTensorProduct.tprod 𝕂 (fun i : Fin 0 ↦ i.elim0) ⊗ₜ[𝕂] tensorOne w z := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    rw [map_smul, map_smul, tensorSplitLast_tprod, tensorOne_tprod, TensorProduct.tmul_smul]
    congr 2
    exact congrArg _ (funext fun i : Fin 0 ↦ i.elim0)
  | add z z' hz hz' => rw [map_add, map_add, hz, hz', TensorProduct.tmul_add]

theorem intertwines_tensorOne (w : Fin 1 → Dom R) :
    Intertwines (ρ w) (Algebra.lsmul 𝕂 𝕂 (Fac (w 0))) (tensorOne w).toLinearMap := by
  intro u z
  have h := intertwines_tensorSplitLast w u z
  simp only [LinearEquiv.coe_coe, AlgHom.comp_apply] at h
  rw [tensorSplitLast_one, tensorSplitLast_one, pairRep_comul_empty_left] at h
  have h' := congrArg ((TensorProduct.lid 𝕂 (Fac (w 0))).toLinearMap ∘ₗ TensorProduct.map
    (PiTensorProduct.isEmptyEquiv (Fin 0)).toLinearMap LinearMap.id) h
  simpa [PiTensorProduct.isEmptyEquiv_apply_tprod] using h'

/-- The ordered tensor product of two factors. -/
def tensorPair (w : Fin 2 → Dom R) : TensorSpace w ≃ₗ[𝕂] Fac (w 0) ⊗[𝕂] Fac (w 1) :=
  (tensorSplit (a := 1) (b := 1) w).trans (TensorProduct.congr (tensorOne _) (tensorOne _))

theorem tensorPair_tprod (w : Fin 2 → Dom R) (x : ∀ j, Fac (w j)) :
    tensorPair w (PiTensorProduct.tprod 𝕂 x) = x 0 ⊗ₜ[𝕂] x 1 := by
  rw [tensorPair, LinearEquiv.trans_apply, tensorSplit_tprod, TensorProduct.congr_tmul,
    tensorOne_tprod, tensorOne_tprod]
  rfl

theorem intertwines_tensorPair (w : Fin 2 → Dom R) :
    Intertwines (ρ w)
      ((pairRep (Algebra.lsmul 𝕂 𝕂 (Fac (w 0))) (Algebra.lsmul 𝕂 𝕂 (Fac (w 1)))).comp Δ)
      (tensorPair w).toLinearMap :=
  (intertwines_tensorSplit (a := 1) (b := 1) w).comp
    (Intertwines.restrict (Intertwines.tensorMap (intertwines_tensorOne _)
      (intertwines_tensorOne _)) Δ)

end Split

end Categorification.Stendhal.FirstWeight

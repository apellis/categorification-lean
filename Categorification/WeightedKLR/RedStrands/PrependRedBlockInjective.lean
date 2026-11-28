/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PrependRedBlockAction
import Categorification.WeightedKLR.RedStrands.StandardizationFullyFaithful
import Categorification.WeightedKLR.RedStrands.RootReflectUnit
import Categorification.KLR.CyclotomicLargeLevel
import Categorification.KLR.BasisTheoremGeneral

/-!
# The block action on `[e_α]` is injective

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.26, for root functions with `α(0) ≠ 0`. For blocks `b_0, …, b_ℓ` of the black
weight, the map `β ↦ β · [e_α]` from the block algebra `R(b_0) ⊗ ⨂_r R^{λ_r}(b_{r+1})` of
Proposition 5.3 to the standard module `S_α` of `T̃^λ` is injective
(`StendhalAlgebra.blockAction_rootStandardUnit_injective`).

Webster's argument: add a red strand `λ₀` on the left. The block `b_0` then lies right of `λ₀`
and the comparison map `Θ : S_α → S_{(0, α)}` intertwines the block actions along the
cyclotomic quotient `R(b_0) → R^{λ₀}(b_0)` on the first factor
(`prependRedStandard_blockAction`). For the blocks `0, b_0, …, b_ℓ` the block action is
injective (the case `b_0 = 0` of Proposition 5.26, `bijective_leftBlockActionOf`), and a given
nonzero element of `R(b_0)` survives in `R^{λ₀}(b_0)` once `λ₀` is large
(`KLRAlgebra.exists_cycKLR_mk_ne_zero`, for a grading with dots of positive degree).

## Main results

* `TensorProduct.exists_coeff_rTensor_ne_zero`: a nonzero tensor `x ∈ M ⊗ N` over a field has a
  nonzero coefficient `m` such that `x` survives every linear map not killing `m`.
* `StendhalAlgebra.blockAction_rootStandardUnit_injective`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace TensorProduct

universe u

variable {k M N : Type*} [Field k] [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

/-- A nonzero tensor `x ∈ M ⊗ N` over a field has a nonzero coefficient `m ∈ M` such that
`(f ⊗ 1) x ≠ 0` for every linear map `f` with `f m ≠ 0`. -/
theorem exists_coeff_rTensor_ne_zero {x : M ⊗[k] N} (hx : x ≠ 0) :
    ∃ m : M, m ≠ 0 ∧ ∀ (M' : Type u) [AddCommGroup M'] [Module k M'] (f : M →ₗ[k] M'),
      f m ≠ 0 → LinearMap.rTensor N f x ≠ 0 := by
  classical
  let 𝒞 := Module.Basis.ofVectorSpace k N
  let e := TensorProduct.equivFinsuppOfBasisRight (M := M) 𝒞
  have he : ∀ (M' : Type u) [AddCommGroup M'] [Module k M'] (f : M →ₗ[k] M') (y : M ⊗[k] N),
      TensorProduct.equivFinsuppOfBasisRight (M := M') 𝒞
        (LinearMap.rTensor N f y) = Finsupp.mapRange f (map_zero f) (e y) := by
    intro M' _ _ f y
    induction y with
    | tmul m n =>
      rw [LinearMap.rTensor_tmul, TensorProduct.equivFinsuppOfBasisRight_apply_tmul,
        TensorProduct.equivFinsuppOfBasisRight_apply_tmul, Finsupp.mapRange_mapRange]
      congr 1
      funext r
      exact (map_smul f r m).symm
    | add y y' hy hy' =>
      rw [map_add, map_add, hy, hy', map_add]
      exact (Finsupp.mapRange_add (fun a b => map_add f a b) _ _).symm
  have hex : e x ≠ 0 := fun h => hx (e.injective (h.trans (map_zero e).symm))
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 hex
  refine ⟨e x i, hi, fun M' _ _ f hf h => hf ?_⟩
  have := congrArg (fun z => z i) (he M' f x)
  simp only [h, map_zero, Finsupp.coe_zero, Pi.zero_apply, Finsupp.mapRange_apply] at this
  exact this.symm

end TensorProduct

namespace Categorification.KLR.KLRAlgebra

/-- For symmetric `Q`, the KLR algebra is nontrivial (it has a basis, KL I Theorem 2.5). -/
theorem nontrivial_of_symm {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] [Nontrivial k]
    {Q : I → I → MvPolynomial (Fin 2) k} (hQ : KLRSymm Q) (ν : Multiset I) :
    Nontrivial (KLRAlgebra k Q ν) := by
  let B := basisOfSymm hQ (fun w => TypeA.canWord _ w)
    (fun w => ⟨TypeA.isReduced_canWord _ w, TypeA.wordProd_canWord _ w⟩) (ν := ν)
  obtain ⟨s⟩ : Nonempty (Seq ν) := inferInstance
  exact ⟨⟨B (s, 1, 0), 0, B.ne_zero _⟩⟩

end Categorification.KLR.KLRAlgebra

namespace Categorification.Stendhal

open KLR StendhalAlgebra MulOpposite
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace StendhalAlgebra

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}

section Unit

variable {n : ℕ} {Λ : Fin n → I →₀ ℕ} {ν : Multiset I} (α : Fin n → I → ℕ)

variable (Q Λ ν) in
/-- The generator `[e_α]` of the standard module `S_α`. -/
def rootStandardUnit : rootStandard (ν := ν) Q Λ α :=
  rootStandardMk Q Λ α (rootIdem Q Λ α) (isIdempotentElem_rootIdem α).eq

/-- An endomorphism of `S_α` vanishing on `[e_α]` vanishes. -/
theorem eq_zero_of_apply_rootStandardUnit
    (f : Module.End (StendhalAlgebra k Q Λ ν)ᵐᵒᵖ (rootStandard (ν := ν) Q Λ α))
    (hf : f (rootStandardUnit Q Λ ν α) = 0) : f = 0 := by
  ext ⟨q, hq⟩
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hq
  have hz' := (mem_span_singleton_iff_mul (isIdempotentElem_rootIdem α) z).1 hz
  have hw : (⟨(rootUpper Q Λ α).mkQ z, hq⟩ : rootStandard (ν := ν) Q Λ α) =
      op z • rootStandardUnit Q Λ ν α := by
    apply Subtype.ext
    change (rootUpper Q Λ α).mkQ z = (rootUpper Q Λ α).mkQ (rootIdem Q Λ α * z)
    rw [hz']
  rw [hw, map_smul, hf, smul_zero]
  rfl

end Unit

theorem prependRedStandard_rootStandardUnit {ℓ : ℕ} {Λ : Fin (ℓ + 1) → I →₀ ℕ} {ν : Multiset I}
    {α : Fin ℓ → I → ℕ} {α' : Fin (ℓ + 1) → I → ℕ} (h : α' = Fin.cons (0 : I → ℕ) α) :
    prependRedStandard h (rootStandardUnit Q (Λ ∘ Fin.succ) ν α) =
      rootStandardUnit Q Λ ν α' := by
  apply Subtype.ext
  change Submodule.Quotient.mk (prependRedStendhal Q Λ ν (rootIdem Q (Λ ∘ Fin.succ) α)) =
    Submodule.Quotient.mk (rootIdem Q Λ α')
  rw [prependRedStendhal_rootIdem_of_eq h]

/-- For blocks with `b_0 = 0` and at least one red strand, the block action of Proposition 5.3
on `S_α` is injective (from `bijective_leftBlockActionOf`). -/
theorem injective_blockAction_of_zero (hQ : KLRSymm Q) {n : ℕ} (hn : 0 < n)
    (Λ : Fin n → I →₀ ℕ) {b : Fin (n + 1) → Multiset I} {ν : Multiset I}
    (hb : blockPrefix b (n + 1) = ν) (hb0 : b 0 = 0) :
    Function.Injective (blockAction Q Λ hb) := by
  subst hb
  have h := (bijective_leftBlockActionOf Q Λ b (rootNonViolated_blockRoot hn hb0) hQ hb0).1
  rw [leftBlockActionOf, AlgHom.coe_comp] at h
  exact h.of_comp

theorem prependBlockAlgHom_apply {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ) (b : Fin (ℓ + 1) → Multiset I)
    (β : BlockAlgebra k Q (Λ ∘ Fin.succ) b) :
    prependBlockAlgHom Q Λ b β = Algebra.TensorProduct.includeRight
      ((PiTensorProduct.consAlgEquiv k (consCycFactor (k := k) (Q := Q) Λ b)).symm
        (LinearMap.rTensor _ (CycKLR.mk k Q (redCyc Λ 0) (leftBlock b)).toLinearMap β)) := by
  rw [prependBlockAlgHom, AlgHom.comp_apply, AlgHom.comp_apply]
  congr 2

/-- **The block action on `[e_α]` is injective** (Webster, arXiv:1309.3796v3, proof of
Proposition 5.26, for any first block `b_0`): for symmetric `Q` with a grading in which dots
have positive degree, `β ↦ β · [e_α]` is injective on the block algebra
`R(b_0) ⊗ R^{λ_1}(b_1) ⊗ ⋯ ⊗ R^{λ_ℓ}(b_ℓ)`. -/
theorem blockAction_rootStandardUnit_injective (hQ : KLRSymm Q) (G : KLR.GradingDatum Q)
    (hG : ∀ a, 0 < G.degX a) {ℓ : ℕ} (Λ₀ : Fin ℓ → I →₀ ℕ) {ν : Multiset I}
    (b : Fin (ℓ + 1) → Multiset I) (hb : blockPrefix b (ℓ + 1) = ν) :
    Function.Injective fun β : BlockAlgebra k Q Λ₀ b =>
      blockAction Q Λ₀ hb β (rootStandardUnit Q Λ₀ ν (blockRoot b)) := by
  classical
  have key : ∀ β : BlockAlgebra k Q Λ₀ b,
      blockAction Q Λ₀ hb β (rootStandardUnit Q Λ₀ ν (blockRoot b)) = 0 → β = 0 := by
    intro β hβ
    by_contra hne
    obtain ⟨m, hm, hf⟩ := TensorProduct.exists_coeff_rTensor_ne_zero.{0} hne
    obtain ⟨N, hN⟩ := KLRAlgebra.exists_cycKLR_mk_ne_zero G hG hm
    let l₀ : I →₀ ℕ := N • Multiset.toFinsupp (leftBlock b)
    let Λ : Fin (ℓ + 1) → I →₀ ℕ := Fin.cons l₀ Λ₀
    have hmk : CycKLR.mk k Q (redCyc Λ 0) (leftBlock b) m ≠ 0 := by
      refine hN (fun i => l₀ i) fun i hi => ?_
      change N ≤ N * Multiset.count i (leftBlock b)
      exact Nat.le_mul_of_pos_right N (Multiset.count_pos.2 hi)
    have h1 := hf _ (CycKLR.mk k Q (redCyc Λ 0) (leftBlock b)).toLinearMap hmk
    have h2 : prependBlockAlgHom Q Λ b β ≠ 0 := by
      intro h
      apply h1
      have := KLRAlgebra.nontrivial_of_symm hQ (leftBlock (consBlocks b))
      have hinj := Algebra.TensorProduct.includeRight_injective (R := k)
        (A := KLRAlgebra k Q (leftBlock (consBlocks b)))
        (B := ⨂[k] r : Fin (ℓ + 1), consCycFactor (k := k) (Q := Q) Λ b r)
        (algebraMap k _).injective
      rw [prependBlockAlgHom_apply] at h
      have h' := hinj (h.trans (map_zero _).symm)
      exact (PiTensorProduct.consAlgEquiv k _).symm.injective (h'.trans (map_zero _).symm)
    have hb' := blockPrefix_consBlocks_eq b hb
    have h3 : blockAction Q Λ hb' (prependBlockAlgHom Q Λ b β) ≠ 0 := fun h =>
      h2 (injective_blockAction_of_zero hQ (Nat.succ_pos ℓ) Λ hb' rfl
        (h.trans (map_zero _).symm))
    apply h3
    apply eq_zero_of_apply_rootStandardUnit
    rw [← prependRedStandard_rootStandardUnit (blockRoot_consBlocks b),
      ← prependRedStandard_blockAction b hb (blockRoot_consBlocks b)]
    exact (congrArg (prependRedStandard (blockRoot_consBlocks b)) hβ).trans (map_zero _)
  intro β β' h
  rw [← sub_eq_zero]
  refine key _ ?_
  simp only at h
  rw [map_sub, LinearMap.sub_apply, h, sub_self]

end StendhalAlgebra

end Categorification.Stendhal

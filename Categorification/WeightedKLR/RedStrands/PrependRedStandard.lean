/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PrependRedRootUpper
import Categorification.WeightedKLR.RedStrands.StandardBlockAction

/-!
# Adding a red strand on the left of the standard module `S_α`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.26, for the comparison of `T̃^λ` with `T^{(λ₀, λ)}`. Adding the red strand `λ₀`
sends `U_α` into `U_{(0, α)}` and `e_α` to `e_{(0, α)}`, so it induces an additive map
`Θ : S_α → S_{(0, α)}`, `[y] ↦ [λ₀ y]` (`prependRedStandard`). It intertwines the block action
of `b_j` on `S_α` with that of the block `j + 1` of `0, b_0, …, b_ℓ` on `S_{(0, α)}`
(`prependRedStandard_rootBlockAction`).

## Main definitions

* `StendhalAlgebra.prependRedStandard`: the map `Θ`.

## Main results

* `StendhalAlgebra.prependRedStandard_rootAction`, `prependRedStandard_rootBlockAction`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR StendhalAlgebra MulOpposite

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace StendhalAlgebra

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I)

local notation "T̃" => StendhalAlgebra k Q (Λ ∘ Fin.succ) ν
local notation "T̃'" => StendhalAlgebra k Q Λ ν
local notation "φ" => prependRedStendhal Q Λ ν

variable {Q Λ ν} {α : Fin ℓ → I → ℕ} {α' : Fin (ℓ + 1) → I → ℕ}

theorem prependRedStendhal_rootIdem_of_eq (h : α' = Fin.cons (0 : I → ℕ) α) :
    φ (rootIdem Q (Λ ∘ Fin.succ) α) = rootIdem Q Λ α' := by
  subst h
  exact prependRedStendhal_rootIdem Q Λ ν α

theorem prependRedStendhal_mem_rootUpper_of_eq (h : α' = Fin.cons (0 : I → ℕ) α) {y : T̃}
    (hy : y ∈ rootUpper Q (Λ ∘ Fin.succ) α) : φ y ∈ rootUpper Q Λ α' := by
  subst h
  exact prependRedStendhal_mem_rootUpper Q Λ ν α hy

/-- Adding the red strand on the quotients `T̃^λ / U_α → T̃^{(λ₀, λ)} / U_{(0, α)}`. -/
def prependRedQuot (h : α' = Fin.cons (0 : I → ℕ) α) :
    T̃ ⧸ rootUpper Q (Λ ∘ Fin.succ) α →+ T̃' ⧸ rootUpper Q Λ α' :=
  QuotientAddGroup.map _ _ (φ : T̃ →+ T̃') fun _ hy =>
    prependRedStendhal_mem_rootUpper_of_eq h hy

theorem prependRedQuot_mk (h : α' = Fin.cons (0 : I → ℕ) α) (y : T̃) :
    prependRedQuot h (Submodule.Quotient.mk y) = Submodule.Quotient.mk (φ y) := rfl

theorem prependRedQuot_mem (h : α' = Fin.cons (0 : I → ℕ) α)
    (v : rootStandard (ν := ν) Q (Λ ∘ Fin.succ) α) :
    prependRedQuot h v.1 ∈ rootStandard (ν := ν) Q Λ α' := by
  obtain ⟨z, hz, hv⟩ := Submodule.mem_map.1 v.2
  rw [← hv]
  refine Submodule.mem_map.2 ⟨φ z, (mem_span_singleton_iff_mul
    (isIdempotentElem_rootIdem α') _).2 ?_, rfl⟩
  rw [← prependRedStendhal_rootIdem_of_eq h, ← map_mul,
    (mem_span_singleton_iff_mul (isIdempotentElem_rootIdem α) z).1 hz]

/-- **Adding the red strand on standard modules**: `Θ : S_α → S_{(0, α)}`, `[y] ↦ [λ₀ y]`
(arXiv:1309.3796v3, proof of Proposition 5.26). -/
def prependRedStandard (h : α' = Fin.cons (0 : I → ℕ) α) :
    rootStandard (ν := ν) Q (Λ ∘ Fin.succ) α →+ rootStandard (ν := ν) Q Λ α' where
  toFun v := ⟨prependRedQuot h v.1, prependRedQuot_mem h v⟩
  map_zero' := Subtype.ext (map_zero (prependRedQuot h))
  map_add' v w := Subtype.ext (map_add (prependRedQuot h) v.1 w.1)

theorem val_prependRedStandard (h : α' = Fin.cons (0 : I → ℕ) α)
    (v : rootStandard (ν := ν) Q (Λ ∘ Fin.succ) α) :
    (prependRedStandard h v).1 = prependRedQuot h v.1 := rfl

/-- `Θ` intertwines the corner actions along adding the red strand. -/
theorem prependRedStandard_rootAction (h : α' = Fin.cons (0 : I → ℕ) α)
    (c : (isIdempotentElem_rootIdem (Q := Q) (Λ := Λ ∘ Fin.succ) (ν := ν) α).Corner)
    (c' : (isIdempotentElem_rootIdem (Q := Q) (Λ := Λ) (ν := ν) α').Corner)
    (hc : c'.1 = φ c.1) (v : rootStandard (ν := ν) Q (Λ ∘ Fin.succ) α) :
    prependRedStandard h (rootAction Q (Λ ∘ Fin.succ) α c v) =
      rootAction Q Λ α' c' (prependRedStandard h v) := by
  obtain ⟨q, hq⟩ := v
  obtain ⟨z, -, rfl⟩ := Submodule.mem_map.1 hq
  apply Subtype.ext
  change prependRedQuot h (Submodule.Quotient.mk (c.1 * z)) =
    Submodule.Quotient.mk (c'.1 * φ z)
  rw [prependRedQuot_mk, map_mul, hc]

theorem prependRedStandard_smul (h : α' = Fin.cons (0 : I → ℕ) α) (c : k)
    (v : rootStandard (ν := ν) Q (Λ ∘ Fin.succ) α) :
    prependRedStandard h (c • v) = c • prependRedStandard h v := by
  obtain ⟨q, hq⟩ := v
  obtain ⟨z, -, rfl⟩ := Submodule.mem_map.1 hq
  apply Subtype.ext
  change prependRedQuot h (Submodule.Quotient.mk (c • z)) =
    Submodule.Quotient.mk (c • φ z)
  rw [prependRedQuot_mk, map_smul]


section Blocks

variable (b : Fin (ℓ + 1) → Multiset I) (hb : blockPrefix b (ℓ + 1) = ν)

/-- `Θ` intertwines the action of `R(b_j)` on `S_α` with that of the block `j + 1` of
`0, b_0, …, b_ℓ` on `S_{(0, α)}`. -/
theorem prependRedStandard_rootBlockAction
    (h : blockRoot (consBlocks b) = Fin.cons (0 : I → ℕ) (blockRoot b)) (j : ℕ) (hj : j < ℓ + 1)
    (z : KLRAlgebra k Q (b ⟨j, hj⟩)) (v : rootStandard (ν := ν) Q (Λ ∘ Fin.succ) (blockRoot b)) :
    prependRedStandard h (rootBlockAction Q (Λ ∘ Fin.succ) hb j hj z v) =
      rootBlockAction Q Λ (b := consBlocks b) (blockPrefix_consBlocks_eq b hb) (j + 1)
        (Nat.succ_lt_succ hj) z (prependRedStandard h v) := by
  rw [rootBlockAction_apply]
  exact prependRedStandard_rootAction h _ (consBlockHom b hb j hj z)
    (Subtype.ext (prependBlockVal_eq (Q := Q) (Λ := Λ) b hb j hj z).symm) v

end Blocks

end StendhalAlgebra

end Categorification.Stendhal

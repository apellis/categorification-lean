/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorWordProjectives
import Categorification.WeightedKLR.RedStrands.BlockAssignment

/-!
# Lowering on the first factors of an ordered tensor product

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Lemma 5.19. The iterated coproduct of `F_i` acts on `V^{λ_1} ⊗ ⋯ ⊗ V^{λ_ℓ}` as
`∑_r 1 ⊗ ⋯ ⊗ 1 ⊗ F_i ⊗ K̃_{-i} ⊗ ⋯ ⊗ K̃_{-i}` (`F_i` in factor `r`). A black strand of a
loading only meets the red strands to its left, so we also use the partial operator
`F_i^{<c}`, which lowers only in the first `c` factors and applies `K̃_{-i}` only up to factor
`c`. Applying `F_i^{<c}` for each black strand, with `c` the number of red strands to its left,
gives Webster's vector `v^κ_i` inside the full tensor product (`loadingVector_eq`).

## Main definitions

* `FirstWeight.lowerAt`, `FirstWeight.partialLower`: the operators above.
* `FirstWeight.loadingVector`: the vector of a word in black and red letters.

## Main results

* `FirstWeight.tensorRepresentation_F`: the iterated coproduct of `F_i` is `partialLower ℓ`.
* `FirstWeight.tensorWordUndivided_eq_loadingVector`: `v^κ_i` is the loading vector.
-/

noncomputable section
namespace Categorification.Stendhal.FirstWeight

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop
open scoped TensorProduct
open KLR.KLRAlgebra (expandDiv)
open KLR (expandDiv_append)

local notation "𝕍" => (RatFunc.X : RatFunc ℚ)
local notation "𝕂" => RatFunc ℚ
local instance : NeZero 𝕍 := ⟨RatFunc.X_ne_zero⟩

variable {I Y : Type*} [DecidableEq I] [AddCommGroup Y]
    {D : LusztigCartanDatum I} {R : D.RootDatum Y} {ℓ : ℕ}

private abbrev Factor (wt : Dom R) := IrreducibleModule R 𝕍 wt.1

/-- The factor maps of `lowerAt`: `F_i` in factor `r`, `K̃_{-i}` in the factors strictly between
`r` and `c`, and the identity elsewhere. -/
def lowerFactor (wt : Fin ℓ → Dom R) (c : ℕ) (i : I) (r j : Fin ℓ) :
    Factor (wt j) →ₗ[𝕂] Factor (wt j) :=
  if j = r then DistribSMul.toLinearMap 𝕂 _ (F R 𝕍 i)
  else if r < j ∧ (j : ℕ) < c then DistribSMul.toLinearMap 𝕂 _ (K R 𝕍 (-ktilde R i))
  else LinearMap.id

/-- `1 ⊗ ⋯ ⊗ 1 ⊗ F_i ⊗ K̃_{-i} ⊗ ⋯ ⊗ K̃_{-i} ⊗ 1 ⊗ ⋯ ⊗ 1`, with `F_i` in factor `r` and
`K̃_{-i}` in the factors `r < j < c`. -/
def lowerAt (wt : Fin ℓ → Dom R) (c : ℕ) (i : I) (r : Fin ℓ) : Module.End 𝕂 (TensorSpace wt) :=
  PiTensorProduct.map (lowerFactor wt c i r)

/-- The partial coproduct of `F_i` on the first `c` factors. -/
def partialLower (wt : Fin ℓ → Dom R) (c : ℕ) (i : I) : Module.End 𝕂 (TensorSpace wt) :=
  ∑ r ∈ Finset.univ.filter (fun r : Fin ℓ => (r : ℕ) < c), lowerAt wt c i r

theorem lowerAt_tprod (wt : Fin ℓ → Dom R) (c : ℕ) (i : I) (r : Fin ℓ)
    (x : ∀ j, Factor (wt j)) :
    lowerAt wt c i r (PiTensorProduct.tprod 𝕂 x) =
      PiTensorProduct.tprod 𝕂 (fun j => lowerFactor wt c i r j (x j)) :=
  PiTensorProduct.map_tprod _ _

section Append

variable (wt : Fin (ℓ + 1) → Dom R)
local notation "wt₀" => fun j : Fin ℓ => wt (Fin.castSucc j)
local notation "V₁" => Factor (wt (Fin.last ℓ))

theorem appendTensor_tprod (x : ∀ j : Fin ℓ, Factor (wt j.castSucc)) (y : V₁) :
    appendTensor wt (PiTensorProduct.tprod 𝕂 x) y =
      PiTensorProduct.tprod 𝕂 (Fin.lastCases (motive := fun j => Factor (wt j)) y x) := by
  apply (tensorSplitLast wt).injective
  rw [appendTensor, LinearEquiv.apply_symm_apply, tensorSplitLast_tprod]
  simp

/-- The pure tensors `appendTensor (tprod x) y` span. -/
theorem linearMap_ext_appendTensor {M : Type*} [AddCommGroup M] [Module 𝕂 M]
    {f g : TensorSpace wt →ₗ[𝕂] M}
    (h : ∀ (x : ∀ j : Fin ℓ, Factor (wt j.castSucc)) (y : V₁),
      f (appendTensor wt (PiTensorProduct.tprod 𝕂 x) y) =
        g (appendTensor wt (PiTensorProduct.tprod 𝕂 x) y)) : f = g := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro z
  have hz : PiTensorProduct.tprod 𝕂 z = appendTensor wt
      (PiTensorProduct.tprod 𝕂 (fun j : Fin ℓ => z j.castSucc)) (z (Fin.last ℓ)) := by
    rw [appendTensor_tprod]
    congr 1
    funext j
    induction j using Fin.lastCases <;> simp
  simpa [hz] using h _ _

/-- `appendTensor` as a linear map in the prefix. -/
def appendRight (y : V₁) : TensorSpace wt₀ →ₗ[𝕂] TensorSpace wt :=
  (tensorSplitLast wt).symm.toLinearMap ∘ₗ (TensorProduct.mk 𝕂 _ _).flip y

theorem appendRight_apply (x : TensorSpace wt₀) (y : V₁) :
    appendRight wt y x = appendTensor wt x y := rfl

theorem lowerFactor_castSucc {c c' : ℕ} (hc : ∀ j : Fin ℓ, ((j : ℕ) < c ↔ (j : ℕ) < c'))
    (i : I) (r j : Fin ℓ) :
    lowerFactor wt c i r.castSucc j.castSucc = lowerFactor (fun j : Fin ℓ => wt j.castSucc) c' i r j := by
  simp only [lowerFactor, Fin.castSucc_inj, Fin.castSucc_lt_castSucc_iff, Fin.val_castSucc, hc j]

theorem lowerFactor_castSucc_last {c : ℕ} (i : I) (r : Fin ℓ) :
    lowerFactor wt c i r.castSucc (Fin.last ℓ) =
      if ℓ < c then DistribSMul.toLinearMap 𝕂 _ (K R 𝕍 (-ktilde R i)) else LinearMap.id := by
  simp [lowerFactor, (Fin.castSucc_lt_last r).ne', Fin.castSucc_lt_last r]

theorem lowerAt_castSucc_appendTensor {c c' : ℕ} (hc : ∀ j : Fin ℓ, ((j : ℕ) < c ↔ (j : ℕ) < c'))
    (i : I) (r : Fin ℓ) (x : ∀ j : Fin ℓ, Factor (wt j.castSucc)) (y : V₁) :
    lowerAt wt c i r.castSucc (appendTensor wt (PiTensorProduct.tprod 𝕂 x) y) =
      appendTensor wt (lowerAt (fun j : Fin ℓ => wt j.castSucc) c' i r (PiTensorProduct.tprod 𝕂 x))
        (lowerFactor wt c i r.castSucc (Fin.last ℓ) y) := by
  rw [appendTensor_tprod, lowerAt_tprod, lowerAt_tprod, appendTensor_tprod]
  congr 1
  funext j
  induction j using Fin.lastCases with
  | last => simp
  | cast j => simp [lowerFactor_castSucc wt hc]

theorem filter_lt_castSucc {c : ℕ} (hc : c ≤ ℓ) :
    (Finset.univ.filter fun r : Fin (ℓ + 1) => (r : ℕ) < c) =
      (Finset.univ.filter fun r : Fin ℓ => (r : ℕ) < c).map Fin.castSuccEmb := by
  ext r
  induction r using Fin.lastCases with
  | last => simp; omega
  | cast r => simp

theorem filter_lt_succ :
    (Finset.univ.filter fun r : Fin (ℓ + 1) => (r : ℕ) < ℓ + 1) =
      insert (Fin.last ℓ) ((Finset.univ.filter fun r : Fin ℓ => (r : ℕ) < ℓ).map Fin.castSuccEmb) := by
  ext r
  induction r using Fin.lastCases with
  | last => simp
  | cast r => simp [(Fin.castSucc_lt_last r).ne]

/-- A partial lowering that does not reach the last factor commutes with appending it. -/
theorem partialLower_appendTensor {c : ℕ} (hc : c ≤ ℓ) (i : I) (x : TensorSpace wt₀) (y : V₁) :
    partialLower wt c i (appendTensor wt x y) = appendTensor wt (partialLower wt₀ c i x) y := by
  rw [← appendRight_apply, ← appendRight_apply, ← LinearMap.comp_apply, ← LinearMap.comp_apply]
  congr 1
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro z
  change partialLower wt c i (appendTensor wt (PiTensorProduct.tprod 𝕂 z) y) =
    appendTensor wt (partialLower wt₀ c i (PiTensorProduct.tprod 𝕂 z)) y
  rw [partialLower, partialLower, filter_lt_castSucc hc, Finset.sum_map, LinearMap.sum_apply,
    LinearMap.sum_apply]
  simp only [← appendRight_apply, map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [appendRight_apply, appendRight_apply, Fin.coe_castSuccEmb,
    lowerAt_castSucc_appendTensor wt (c' := c) (fun _ => Iff.rfl), lowerFactor_castSucc_last,
    ite_eq_right (by omega)]
  rfl

end Append

/-- **The iterated coproduct of `F_i`** acts on `V^{λ_1} ⊗ ⋯ ⊗ V^{λ_ℓ}` as
`∑_r 1 ⊗ ⋯ ⊗ F_i ⊗ K̃_{-i} ⊗ ⋯ ⊗ K̃_{-i}`. -/
theorem tensorRepresentation_F : ∀ {ℓ : ℕ} (wt : Fin ℓ → Dom R) (i : I),
    tensorRepresentation wt (F R 𝕍 i) = partialLower wt ℓ i
  | 0, wt, i => by
    refine LinearMap.ext fun x => ?_
    change (Algebra.ofId 𝕂 (Module.End 𝕂 (TensorSpace wt))) (counit R 𝕍 (F R 𝕍 i)) x = _
    simp [counit_F, partialLower]
  | ℓ + 1, wt, i => by
    apply linearMap_ext_appendTensor wt
    intro x y
    rw [tensorRepresentation_F_append, tensorRepresentation_F (fun j => wt j.castSucc) i,
      partialLower, partialLower, filter_lt_succ, Finset.sum_insert (by simp), Finset.sum_map,
      LinearMap.add_apply, LinearMap.sum_apply, LinearMap.sum_apply]
    have h1 : appendTensor wt (∑ r ∈ Finset.univ.filter (fun r : Fin ℓ => (r : ℕ) < ℓ),
        lowerAt (fun j => wt j.castSucc) ℓ i r (PiTensorProduct.tprod 𝕂 x))
          (K R 𝕍 (-ktilde R i) • y) =
        ∑ r ∈ Finset.univ.filter (fun r : Fin ℓ => (r : ℕ) < ℓ),
          lowerAt wt (ℓ + 1) i (Fin.castSuccEmb r)
            (appendTensor wt (PiTensorProduct.tprod 𝕂 x) y) := by
      simp only [← appendRight_apply, map_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [appendRight_apply, appendRight_apply, Fin.coe_castSuccEmb,
        lowerAt_castSucc_appendTensor wt (c' := ℓ) (fun j => by omega), lowerFactor_castSucc_last,
        ite_eq_left (by omega)]
      rfl
    have h2 : appendTensor wt (PiTensorProduct.tprod 𝕂 x) (F R 𝕍 i • y) =
        lowerAt wt (ℓ + 1) i (Fin.last ℓ) (appendTensor wt (PiTensorProduct.tprod 𝕂 x) y) := by
      rw [appendTensor_tprod, appendTensor_tprod, lowerAt_tprod]
      congr 1
      funext j
      induction j using Fin.lastCases with
      | last => simp [lowerFactor]
      | cast j =>
        simp [lowerFactor, (Fin.castSucc_lt_last j).ne, not_lt.2 (Fin.castSucc_lt_last j).le]
    rw [h1, h2]
    exact add_comm _ _

section LoadingVector

variable {n : ℕ}

/-- The vector of a reversed word: each black letter `i` applies `F_i^{<c}`, with `c` the
number of red letters before it. -/
def loadingVectorRev (wt : Fin ℓ → Dom R) : List (I ⊕ Fin n) → TensorSpace wt
  | [] => PiTensorProduct.tprod 𝕂 (fun j => IrreducibleModule.hwv R 𝕍 (wt j).1)
  | .inl i :: u => partialLower wt (redCount u) i (loadingVectorRev wt u)
  | .inr _ :: u => loadingVectorRev wt u

/-- **Webster's vector `v^κ_i`** of a word in black and red letters, inside the full tensor
product `V^{λ_1} ⊗ ⋯ ⊗ V^{λ_ℓ}` (arXiv:1309.3796v3, before Lemma 5.19): read left to right,
a black letter `i` applies `F_i` through the coproduct on the factors of the red letters before
it. -/
def loadingVector (wt : Fin ℓ → Dom R) (u : List (I ⊕ Fin n)) : TensorSpace wt :=
  loadingVectorRev wt u.reverse

theorem loadingVector_nil (wt : Fin ℓ → Dom R) :
    loadingVector wt ([] : List (I ⊕ Fin n)) =
      PiTensorProduct.tprod 𝕂 (fun j => IrreducibleModule.hwv R 𝕍 (wt j).1) := rfl

theorem loadingVector_append_inl (wt : Fin ℓ → Dom R) (u : List (I ⊕ Fin n)) (i : I) :
    loadingVector wt (u ++ [.inl i]) = partialLower wt (redCount u) i (loadingVector wt u) := by
  simp [loadingVector, loadingVectorRev]

theorem loadingVector_append_inr (wt : Fin ℓ → Dom R) (u : List (I ⊕ Fin n)) (r : Fin n) :
    loadingVector wt (u ++ [.inr r]) = loadingVector wt u := by
  simp [loadingVector, loadingVectorRev]

theorem loadingVector_append_replicate (wt : Fin ℓ → Dom R) (u : List (I ⊕ Fin n)) (i : I) :
    ∀ a : ℕ, loadingVector wt (u ++ List.replicate a (.inl i)) =
      (partialLower wt (redCount u) i ^ a) (loadingVector wt u)
  | 0 => by simp
  | a + 1 => by
    rw [List.replicate_succ', ← List.append_assoc, loadingVector_append_inl,
      loadingVector_append_replicate wt u i a, redCount_append]
    simp [pow_succ', redCount, List.countP_replicate]

/-- Red labels only enter through their number. -/
theorem loadingVector_map_addRedColor (wt : Fin ℓ → Dom R) (u : List (I ⊕ Fin n)) :
    loadingVector wt (u.map (addRedColor n)) = loadingVector wt u := by
  induction u using List.reverseRecOn with
  | nil => rfl
  | append_singleton u a ih =>
    rcases a with i | r
    · rw [List.map_append, List.map_singleton, show addRedColor n (.inl i) = .inl i from rfl,
        loadingVector_append_inl, loadingVector_append_inl, ih]
      congr 2
      simp [redCount, List.countP_map, Function.comp_def]
    · rw [List.map_append, List.map_singleton, show addRedColor n (.inr r) = .inr r.castSucc from rfl,
        loadingVector_append_inr, loadingVector_append_inr, ih]

/-- Appending a factor with its highest weight vector to a loading vector whose black letters
meet at most the existing factors. -/
theorem appendTensor_loadingVector (wt : Fin (ℓ + 1) → Dom R) :
    ∀ (u : List (I ⊕ Fin n)), redCount u ≤ ℓ →
      appendTensor wt (loadingVector (fun j => wt j.castSucc) u)
        (IrreducibleModule.hwv R 𝕍 (wt (Fin.last ℓ)).1) = loadingVector wt u := by
  intro u
  induction u using List.reverseRecOn with
  | nil =>
    intro _
    rw [loadingVector_nil, loadingVector_nil, appendTensor_tprod]
    congr 1
    funext j
    induction j using Fin.lastCases <;> simp
  | append_singleton u a ih =>
    intro hu
    rw [redCount_append] at hu
    rcases a with i | r
    · rw [loadingVector_append_inl, loadingVector_append_inl,
        ← partialLower_appendTensor wt (by omega), ih (by omega)]
    · rw [loadingVector_append_inr, loadingVector_append_inr, ih (by simp at hu; omega)]

end LoadingVector

omit [DecidableEq I] in
theorem TensorWord.expandDiv_blocks_red {n : ℕ} (w : TensorWord I n) :
    expandDiv w.red.blocks = (expandDiv w.blocks).map (addRedColor n) ++ [.inr (Fin.last n)] := by
  rw [TensorWord.blocks, expandDiv_append]
  congr 1
  simp only [expandDiv, List.flatMap_map, List.map_flatMap, List.map_replicate]
  rfl

omit [DecidableEq I] in
theorem TensorWord.expandDiv_blocks_black {n : ℕ} (w : TensorWord I n) (i : I) (a : ℕ) :
    expandDiv (w.black i a).blocks = expandDiv w.blocks ++ List.replicate a (.inl i) := by
  rw [TensorWord.blocks, expandDiv_append]
  simp [expandDiv]

omit [DecidableEq I] in
theorem TensorWord.redCount_blocks : ∀ {n : ℕ} (w : TensorWord I n),
    redCount (expandDiv w.blocks) = n
  | _, .empty => rfl
  | n + 1, .red w => by
    have h := w.redCount_blocks
    rw [TensorWord.expandDiv_blocks_red, redCount_append]
    simp only [redCount, List.countP_map, Function.comp_def] at h ⊢
    simpa using h
  | _, .black w i a => by
    rw [TensorWord.expandDiv_blocks_black, redCount_append, w.redCount_blocks]
    simp [redCount, List.countP_replicate]

section Bridge

variable {C : Categorification.QuantumGroup.CartanDatum I} {Rc : C.toLusztig.RootDatum Y}

/-- **`v^κ_i` is the loading vector** (arXiv:1309.3796v3, before Lemma 5.19): the vector of a
tensor word, applying ordinary powers of `F_i` at its black blocks, is the loading vector of its
expanded letters. -/
theorem tensorWordUndivided_eq_loadingVector : ∀ {n : ℕ} (w : TensorWord I n)
    (wt : Fin n → Dom Rc), tensorWordUndivided w wt = loadingVector wt (expandDiv w.blocks)
  | _, .empty, wt => by
    rw [tensorWordUndivided, tensorWordVector,
      show expandDiv (TensorWord.empty (I := I)).blocks = [] from rfl, loadingVector_nil]
  | n + 1, .red w, wt => by
    have h := tensorWordUndivided_eq_loadingVector w (fun j => wt j.castSucc)
    rw [tensorWordUndivided, h, TensorWord.expandDiv_blocks_red, loadingVector_append_inr,
      loadingVector_map_addRedColor, appendTensor_loadingVector wt _ (w.redCount_blocks).le]
  | n, .black w i a, wt => by
    have h := tensorWordUndivided_eq_loadingVector w wt
    rw [tensorWordUndivided, h, TensorWord.expandDiv_blocks_black, loadingVector_append_replicate,
      map_pow, tensorRepresentation_F, w.redCount_blocks]

end Bridge

end Categorification.Stendhal.FirstWeight

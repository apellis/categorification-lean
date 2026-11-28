/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.SMoveModuleCorner
import Categorification.WeightedKLR.RedStrands.Vacuum

/-!
# Loading corners of the S-move partial standardizations

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22. For the two cuts of the S-move, whose outer block `P_∅` is a single red
strand with no black strand, the corner of `𝕊(P_∅ ⊠ X)` (resp. `𝕊(X ⊠ P_∅)`) at the
concatenation of the red strand with a loading `j` of the inner block is
`T^{λ}(0) ⊗ e(j) X` (resp. `e(j) X ⊗ T^{λ}(0)`).

The outer block has a single loading, so its loading idempotent is `1`
(`cutPrefixProjection_e_emptyLeft`), and the input idempotent `1_{red · j}` acts on
`P_∅ ⊠ X` as `1 ⊗ e(j)` (`cutInputIdemEnd_emptyLeft`). Over a field, the vectors of `L ⊗ X`
fixed by `1 ⊗ g` are `L ⊗ X^g` (`lTensorKerEquiv`).

## Main definitions

* `Stendhal.lTensorKerEquiv`, `Stendhal.rTensorKerEquiv`: `ker (M ⊗ f) ≅ M ⊗ ker f` over a field.
* `Stendhal.emptyLeftCornerEquiv`: `e(red · j) 𝕊(P_∅ ⊠ X) ≅ T^{λ_1}(0) ⊗ e(j) X`.
* `Stendhal.emptyRightCornerEquiv`: `e(i · red) 𝕊(X ⊠ P_∅) ≅ e(i) X ⊗ T^{λ_ℓ}(0)`.
* `Stendhal.emptyLeftCornerInputEquiv`, `Stendhal.emptyRightCornerInputEquiv`: the same with
  `T^{λ}(0) ≅ k`, so the corners are `e(j) X` and `e(i) X`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA
open scoped TensorProduct

/-! ### Kernels of tensored maps over a field -/

section Flat

variable {k : Type*} [Field k] {M X Y : Type*} [AddCommGroup M] [Module k M]
  [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]

variable (M) in
/-- Over a field, `ker (M ⊗ f) ≅ M ⊗ ker f`. -/
def lTensorKerEquiv (f : X →ₗ[k] Y) :
    M ⊗[k] LinearMap.ker f ≃ₗ[k] LinearMap.ker (f.lTensor M) :=
  (LinearEquiv.ofInjective ((LinearMap.ker f).subtype.lTensor M)
    (Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective)).trans
    (LinearEquiv.ofEq _ _
      (Module.Flat.lTensor_exact M (LinearMap.exact_subtype_ker_map f)).linearMap_ker_eq.symm)

variable (M) in
/-- Over a field, `ker (f ⊗ M) ≅ ker f ⊗ M`. -/
def rTensorKerEquiv (f : X →ₗ[k] Y) :
    LinearMap.ker f ⊗[k] M ≃ₗ[k] LinearMap.ker (f.rTensor M) :=
  (LinearEquiv.ofInjective ((LinearMap.ker f).subtype.rTensor M)
    (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective)).trans
    (LinearEquiv.ofEq _ _
      (Module.Flat.rTensor_exact M (LinearMap.exact_subtype_ker_map f)).linearMap_ker_eq.symm)

end Flat

/-! ### The cut `{1} | {2, …}` with no black strand in the first block -/

section EmptyLeft

variable {I k : Type} [DecidableEq I] [Field k] {r : ℕ} (Q : I → I → MvPolynomial (Fin 2) k)
  (Λ : Fin (1 + r) → I →₀ ℕ) (β : Multiset I) (hQ : KLRSymm Q)

local notation "α" =>
  Multiset.map (Sum.map (id : I → I) (Fin.castAdd r)) (stendhalWeight 1 (0 : Multiset I))
local notation "δ" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd 1)) (stendhalWeight r β)
local notation "L" => TensorProductAlgebra k Q (Λ ∘ Fin.castAdd r) 0
local notation "C" => TensorProductAlgebra k Q (Λ ∘ Fin.natAdd 1) β

omit [DecidableEq I] in
/-- The first block of the cut has a single loading. -/
theorem subsingleton_seq_emptyLeft : Subsingleton (Seq α) := by
  constructor
  intro i i'
  apply Subtype.ext
  funext p
  have hi := i.mem p
  have hi' := i'.mem p
  simp [stendhalWeight] at hi hi'
  rw [hi, hi']

/-- The loading idempotent of the first block is `1` in `T^{λ_1}(0)`. -/
theorem cutPrefixProjection_e_emptyLeft (i : Seq α) :
    cutPrefixProjection Q Λ (0 : Multiset I) (e i) = 1 := by
  have := subsingleton_seq_emptyLeft (I := I) (r := r)
  rw [← map_one (cutPrefixProjection Q Λ (0 : Multiset I)),
    ← sum_e (k := k) (Q := stendhalQ Q Λ) (ν := α), Fintype.sum_subsingleton _ i]

variable (X : Type) [AddCommGroup X] [Module k X]
  [Module (TensorProductAlgebra k Q (Λ ∘ Fin.natAdd 1) β) X]
  [IsScalarTower k (TensorProductAlgebra k Q (Λ ∘ Fin.natAdd 1) β) X]

/-- The input idempotent `1_{red · j}` acts on `P_∅ ⊠ X` as `1 ⊗ e(j)`. -/
theorem cutInputIdemEnd_emptyLeft (i : Seq α) (j : Seq δ) :
    cutInputIdemEnd Q Λ 0 β (ExtTensor k L X) (i.append j) =
      (Algebra.lsmul k k X (cutSuffixProjection Q Λ β (e j))).lTensor L := by
  apply TensorProduct.ext'
  intro l x
  change cutInputMap Q Λ 0 β (concatIdem (Q := stendhalQ Q Λ) (i.append j)) •
    (ExtTensor.tmul l x : ExtTensor k L X) = _
  rw [concatIdem_append, cutInputMap, Algebra.TensorProduct.map_tmul, ExtTensor.smul_tmul,
    cutPrefixProjection_e_emptyLeft, one_smul]
  rfl

/-- **The loading corner of `𝕊^{λ_1; λ_2, …}(P_∅ ⊠ X)`** (Webster, arXiv:1309.3796v3, §7.3,
proof of Proposition 7.22): the vectors fixed by `e(red · j)` are `T^{λ_1}(0) ⊗ e(j) X`. -/
def emptyLeftCornerEquiv (i : Seq α) (j : Seq δ) :
    LinearMap.ker (cutLoadingEnd Q Λ 0 β (ExtTensor k L X) hQ (i.append j) - 1) ≃ₗ[k]
      L ⊗[k] LinearMap.ker (Algebra.lsmul k k X (cutSuffixProjection Q Λ β (e j)) - 1) :=
  (cutStandardLoadingFixedEquiv Q Λ 0 β (ExtTensor k L X) hQ
    (isUnshuffledLoading_append_emptyLeft Q Λ β i j)).trans
    ((LinearEquiv.ofEq _ _ (by
      rw [cutInputIdemEnd_emptyLeft, LinearMap.lTensor_sub, Module.End.one_eq_id,
        Module.End.one_eq_id, LinearMap.lTensor_id]
      rfl)).trans
      (lTensorKerEquiv L _).symm)

/-- **The loading corner of `𝕊^{λ_1; λ_2, …}(P_∅ ⊠ X)` is `e(j) X`**: with
`T^{λ_1}(0) ≅ k` (`tensorProductAlgebraZeroEquiv`), the vectors of `𝕊(P_∅ ⊠ X)` fixed by
`e(red · j)` are those of `X` fixed by `e(j)`. -/
def emptyLeftCornerInputEquiv (i : Seq α) (j : Seq δ) :
    LinearMap.ker (cutLoadingEnd Q Λ 0 β (ExtTensor k L X) hQ (i.append j) - 1) ≃ₗ[k]
      LinearMap.ker (Algebra.lsmul k k X (cutSuffixProjection Q Λ β (e j)) - 1) :=
  (emptyLeftCornerEquiv Q Λ β hQ X i j).trans
    ((TensorProduct.congr (tensorProductAlgebraZeroEquiv Q (Λ ∘ Fin.castAdd r)).toLinearEquiv
      (LinearEquiv.refl k _)).trans (TensorProduct.lid k _))

end EmptyLeft

/-! ### The cut `{1, …} | {last}` with no black strand in the last block -/

section EmptyRight

variable {I k : Type} [DecidableEq I] [Field k] {a : ℕ} (Q : I → I → MvPolynomial (Fin 2) k)
  (Λ : Fin (a + 1) → I →₀ ℕ) (θ : Multiset I) (hQ : KLRSymm Q)

local notation "α" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd 1)) (stendhalWeight a θ)
local notation "δ" =>
  Multiset.map (Sum.map (id : I → I) (Fin.natAdd a)) (stendhalWeight 1 (0 : Multiset I))
local notation "L" => TensorProductAlgebra k Q (Λ ∘ Fin.castAdd 1) θ
local notation "C" => TensorProductAlgebra k Q (Λ ∘ Fin.natAdd a) 0

omit [DecidableEq I] in
/-- The last block of the cut has a single loading. -/
theorem subsingleton_seq_emptyRight : Subsingleton (Seq δ) := by
  constructor
  intro j j'
  apply Subtype.ext
  funext p
  have hj := j.mem p
  have hj' := j'.mem p
  simp [stendhalWeight] at hj hj'
  rw [hj, hj']

/-- The loading idempotent of the last block is `1` in `T^{λ_ℓ}(0)`. -/
theorem cutSuffixProjection_e_emptyRight (j : Seq δ) :
    cutSuffixProjection Q Λ (0 : Multiset I) (e j) = 1 := by
  have := subsingleton_seq_emptyRight (I := I) (a := a)
  rw [← map_one (cutSuffixProjection Q Λ (0 : Multiset I)),
    ← sum_e (k := k) (Q := stendhalQ Q Λ) (ν := δ), Fintype.sum_subsingleton _ j]

variable (X : Type) [AddCommGroup X] [Module k X]
  [Module (TensorProductAlgebra k Q (Λ ∘ Fin.castAdd 1) θ) X]
  [IsScalarTower k (TensorProductAlgebra k Q (Λ ∘ Fin.castAdd 1) θ) X]

/-- The input idempotent `1_{i · red}` acts on `X ⊠ P_∅` as `e(i) ⊗ 1`. -/
theorem cutInputIdemEnd_emptyRight (i : Seq α) (j : Seq δ) :
    cutInputIdemEnd Q Λ θ 0 (ExtTensor k X C) (i.append j) =
      (Algebra.lsmul k k X (cutPrefixProjection Q Λ θ (e i))).rTensor C := by
  apply TensorProduct.ext'
  intro x c
  change cutInputMap Q Λ θ 0 (concatIdem (Q := stendhalQ Q Λ) (i.append j)) •
    (ExtTensor.tmul x c : ExtTensor k X C) = _
  rw [concatIdem_append, cutInputMap, Algebra.TensorProduct.map_tmul, ExtTensor.smul_tmul,
    cutSuffixProjection_e_emptyRight, one_smul]
  rfl

/-- **The loading corner of `𝕊^{…, λ_a; λ_{a+1}}(X ⊠ P_∅)`** (Webster, arXiv:1309.3796v3,
§7.3, proof of Proposition 7.22): the vectors fixed by `e(i · red)` are
`e(i) X ⊗ T^{λ_{a+1}}(0)`. -/
def emptyRightCornerEquiv (i : Seq α) (j : Seq δ) :
    LinearMap.ker (cutLoadingEnd Q Λ θ 0 (ExtTensor k X C) hQ (i.append j) - 1) ≃ₗ[k]
      LinearMap.ker (Algebra.lsmul k k X (cutPrefixProjection Q Λ θ (e i)) - 1) ⊗[k] C :=
  (cutStandardLoadingFixedEquiv Q Λ θ 0 (ExtTensor k X C) hQ
    (isUnshuffledLoading_append_emptyRight Q Λ θ i j)).trans
    ((LinearEquiv.ofEq _ _ (by
      rw [cutInputIdemEnd_emptyRight, LinearMap.rTensor_sub, Module.End.one_eq_id,
        Module.End.one_eq_id, LinearMap.rTensor_id]
      rfl)).trans
      (rTensorKerEquiv C _).symm)

/-- **The loading corner of `𝕊^{…, λ_a; λ_{a+1}}(X ⊠ P_∅)` is `e(i) X`**: with
`T^{λ_{a+1}}(0) ≅ k` (`tensorProductAlgebraZeroEquiv`), the vectors of `𝕊(X ⊠ P_∅)` fixed by
`e(i · red)` are those of `X` fixed by `e(i)`. -/
def emptyRightCornerInputEquiv (i : Seq α) (j : Seq δ) :
    LinearMap.ker (cutLoadingEnd Q Λ θ 0 (ExtTensor k X C) hQ (i.append j) - 1) ≃ₗ[k]
      LinearMap.ker (Algebra.lsmul k k X (cutPrefixProjection Q Λ θ (e i)) - 1) :=
  (emptyRightCornerEquiv Q Λ θ hQ X i j).trans
    ((TensorProduct.congr (LinearEquiv.refl k _)
      (tensorProductAlgebraZeroEquiv Q (Λ ∘ Fin.natAdd a)).toLinearEquiv).trans
      (TensorProduct.rid k _))

end EmptyRight

end Categorification.Stendhal

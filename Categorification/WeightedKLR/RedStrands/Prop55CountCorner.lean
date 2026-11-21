/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.Algebra.InductionAlongCornerRes
import Categorification.WeightedKLR.RedStrands.LastRedBlackEquiv

/-!
# The last-red piece of a black induction

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
Proposition 4.32 identifies `e_ℓ T_{i+ν} ν_i(e_ℓ)` with `T₀_{i+ν} ν_i(1)` as bimodules
(`lastRedBlackEquiv`). This file packages that isomorphism as a `CornerIso` and deduces that
for a `T₀_ν`-module `N`, the last-red piece `e_ℓ Ind N` of the induction of `N` along
"add the last red strand, then the black strand `i`" is the induction of `N` along adding the
black strand `i` to `T^{λ'}` (`lastRedPieceIndEquiv`). This is the red last-strand piece in the
dimension count of the proof of Proposition 5.5 (tracking issue #405).

## Main results

* `lastRedBlackCornerIso`: Proposition 4.32 as a `CornerIso`.
* `lastRedPieceIndEquiv`, `finrank_lastRedPiece_ind`.
-/

noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace Categorification.Stendhal

open KLR KLRAlgebra InductionAlong MulOpposite

variable {I : Type} {ℓ : ℕ} [DecidableEq I] {k : Type*} [CommRing k]
  {C : QuantumGroup.CartanDatum I}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I) (ν : Multiset I)
  (hQ : IsRouquierQ C Q)

local notation "Λ₀" => (Λ ∘ Fin.castSucc)
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "T₀" => TensorProductAlgebra k Q Λ₀ ν
local notation "T₀'" => TensorProductAlgebra k Q Λ₀ νᵢ
local notation "T'" => TensorProductAlgebra k Q Λ νᵢ

/-- Adding the last red strand, as a nonunital map `T^{λ'}_β → T^λ_β`. -/
def appendRedHom (β : Multiset I) :
    TensorProductAlgebra k Q Λ₀ β →ₙ+* TensorProductAlgebra k Q Λ β :=
  (KLR.cornerVal (TensorProductAlgebra.isIdempotentElem_lastRedIdem Q Λ β)).comp
    (appendRed Q Λ β).toRingHom.toNonUnitalRingHom

theorem appendRedHom_apply (β : Multiset I) (x : TensorProductAlgebra k Q Λ₀ β) :
    appendRedHom Q Λ β x = (appendRed Q Λ β x).val := rfl

/-- Adding the black strand `i` to `T^{λ'}`, as a nonunital ring map. -/
def appendBlackOldHom : T₀ →ₙ+* T₀' :=
  NonUnitalRingHomClass.toNonUnitalRingHom (appendBlack Q Λ₀ i ν)

/-- Adding the last red strand and then the black strand `i`. -/
def redBlackHom : T₀ →ₙ+* T' :=
  (NonUnitalRingHomClass.toNonUnitalRingHom (appendBlack Q Λ i ν)).comp (appendRedHom Q Λ ν)

theorem redBlackHom_apply (h : T₀) :
    redBlackHom Q Λ i ν h = appendBlack Q Λ i ν (appendRed Q Λ ν h).val := rfl

theorem redBlackHom_one :
    redBlackHom Q Λ i ν 1 =
      appendBlack Q Λ i ν (TensorProductAlgebra.lastRedIdem Q Λ ν) := by
  rw [redBlackHom_apply, appendRed_one_val]

theorem appendRedHom_one : appendRedHom Q Λ νᵢ 1 = TensorProductAlgebra.lastRedIdem Q Λ νᵢ :=
  appendRed_one_val Q Λ νᵢ

/-- The map of Proposition 4.32 on `T₀_{i+ν} ν_i(1)`, landing in `T_{i+ν} ν_i(e_ℓ)`. -/
def lastRedBlackCornerFun : Corner (appendBlackOldHom Q Λ i ν) →+ Corner (redBlackHom Q Λ i ν) where
  toFun g := ⟨lastRedBlackMap Q Λ i ν g.1, by
    change _ * redBlackHom Q Λ i ν 1 = _
    rw [redBlackHom_one, lastRedBlackMap_mul_appendBlack_lastRedIdem]⟩
  map_zero' := Subtype.ext (map_zero (lastRedBlackMap Q Λ i ν))
  map_add' g g' := Subtype.ext (map_add (lastRedBlackMap Q Λ i ν) g.1 g'.1)

theorem lastRedBlackCornerFun_val (g : Corner (appendBlackOldHom Q Λ i ν)) :
    (lastRedBlackCornerFun Q Λ i ν g).1 = lastRedBlackMap Q Λ i ν g.1 := rfl

theorem lastRedIdem_mul_mem (z : Corner (redBlackHom Q Λ i ν)) :
    TensorProductAlgebra.lastRedIdem Q Λ νᵢ * z.1 ∈ lastRedCornerSubmodule Q Λ i ν := by
  have hz : z.1 * appendBlack Q Λ i ν (TensorProductAlgebra.lastRedIdem Q Λ ν) = z.1 := by
    rw [← redBlackHom_one]; exact z.2
  change _ * (_ * z.1) * _ = _ * z.1
  rw [← mul_assoc, (TensorProductAlgebra.isIdempotentElem_lastRedIdem Q Λ νᵢ).eq, mul_assoc,
    hz]

/-- The inverse of Proposition 4.32, precomposed with left multiplication by `e_ℓ`. -/
def lastRedBlackCornerInv :
    Corner (redBlackHom Q Λ i ν) →+ Corner (appendBlackOldHom Q Λ i ν) where
  toFun z := ⟨((lastRedBlackEquiv Q Λ i ν hQ).symm
      ⟨_, lastRedIdem_mul_mem Q Λ i ν z⟩).1,
    ((lastRedBlackEquiv Q Λ i ν hQ).symm ⟨_, lastRedIdem_mul_mem Q Λ i ν z⟩).2⟩
  map_zero' := Subtype.ext (by
    have : (⟨_, lastRedIdem_mul_mem Q Λ i ν 0⟩ : lastRedCornerSubmodule Q Λ i ν) = 0 :=
      Subtype.ext (mul_zero _)
    simp only [this, map_zero]
    rfl)
  map_add' z z' := Subtype.ext (by
    have : (⟨_, lastRedIdem_mul_mem Q Λ i ν (z + z')⟩ : lastRedCornerSubmodule Q Λ i ν) =
        ⟨_, lastRedIdem_mul_mem Q Λ i ν z⟩ + ⟨_, lastRedIdem_mul_mem Q Λ i ν z'⟩ :=
      Subtype.ext (mul_add _ _ _)
    simp only [this, map_add]
    rfl)

theorem lastRedBlackMap_cornerInv (z : Corner (redBlackHom Q Λ i ν)) :
    lastRedBlackMap Q Λ i ν (lastRedBlackCornerInv Q Λ i ν hQ z).1 =
      TensorProductAlgebra.lastRedIdem Q Λ νᵢ * z.1 := by
  change lastRedBlackMap Q Λ i ν ((lastRedBlackEquiv Q Λ i ν hQ).symm _).1 = _
  rw [← lastRedBlackEquiv_apply Q Λ i ν hQ, LinearEquiv.apply_symm_apply]

theorem lastRedBlackCornerInv_congr (z z' : Corner (redBlackHom Q Λ i ν))
    (h : TensorProductAlgebra.lastRedIdem Q Λ νᵢ * z.1 =
      TensorProductAlgebra.lastRedIdem Q Λ νᵢ * z'.1) :
    lastRedBlackCornerInv Q Λ i ν hQ z = lastRedBlackCornerInv Q Λ i ν hQ z' := by
  have : (⟨_, lastRedIdem_mul_mem Q Λ i ν z⟩ : lastRedCornerSubmodule Q Λ i ν) =
      ⟨_, lastRedIdem_mul_mem Q Λ i ν z'⟩ := Subtype.ext h
  exact Subtype.ext (congrArg (fun y => ((lastRedBlackEquiv Q Λ i ν hQ).symm y).1) this)

include hQ in
theorem lastRedBlackCornerFun_injective :
    Function.Injective (lastRedBlackCornerFun Q Λ i ν) := by
  intro g g' h
  have h' : lastRedBlackEquiv Q Λ i ν hQ ⟨g.1, g.2⟩ = lastRedBlackEquiv Q Λ i ν hQ ⟨g'.1, g'.2⟩ :=
    Subtype.ext (by
      rw [lastRedBlackEquiv_apply, lastRedBlackEquiv_apply]; exact congrArg Subtype.val h)
  exact Subtype.ext (congrArg Subtype.val ((lastRedBlackEquiv Q Λ i ν hQ).injective h'))

/-- **Proposition 4.32 as a corner isomorphism** (arXiv:1309.3796v3):
`T₀_{i+ν} ν_i(1) ≅ e_ℓ T_{i+ν} ν_i(e_ℓ)` as `(T₀_{i+ν}, T₀_ν)`-bimodules. -/
def lastRedBlackCornerIso :
    CornerIso (redBlackHom Q Λ i ν) (appendRedHom Q Λ νᵢ) (appendBlackOldHom Q Λ i ν) where
  toFun := lastRedBlackCornerFun Q Λ i ν
  invFun := lastRedBlackCornerInv Q Λ i ν hQ
  fixed g := by
    rw [appendRedHom_one, lastRedBlackCornerFun_val, lastRedIdem_mul_lastRedBlackMap]
  inv_toFun g := lastRedBlackCornerFun_injective Q Λ i ν hQ (Subtype.ext (by
    simp only [lastRedBlackCornerFun_val, lastRedBlackMap_cornerInv,
      lastRedIdem_mul_lastRedBlackMap]))
  toFun_inv z := by
    rw [lastRedBlackCornerFun_val, lastRedBlackMap_cornerInv, appendRedHom_one]
  inv_unit z := lastRedBlackCornerInv_congr Q Λ i ν hQ _ _ (by
    change _ * z.1 = _ * (appendRedHom Q Λ νᵢ 1 * z.1)
    rw [appendRedHom_one, ← mul_assoc,
      (TensorProductAlgebra.isIdempotentElem_lastRedIdem Q Λ νᵢ).eq])
  map_left a g := by
    change lastRedBlackMap Q Λ i ν (a * g.1) = _
    rw [lastRedBlackMap_mul_left, appendRedHom_apply, lastRedBlackCornerFun_val]
  map_right a g := Subtype.ext (by
    change lastRedBlackMap Q Λ i ν (g.1 * appendBlack Q Λ₀ i ν a) =
      lastRedBlackMap Q Λ i ν g.1 * redBlackHom Q Λ i ν a
    rw [lastRedBlackMap_mul_appendBlack, redBlackHom_apply])
  inv_right a z := lastRedBlackCornerFun_injective Q Λ i ν hQ (Subtype.ext (by
    change lastRedBlackMap Q Λ i ν _ = lastRedBlackMap Q Λ i ν
      ((lastRedBlackCornerInv Q Λ i ν hQ z).1 * appendBlack Q Λ₀ i ν a)
    rw [lastRedBlackMap_cornerInv, lastRedBlackMap_mul_appendBlack, lastRedBlackMap_cornerInv]
    change _ * (z.1 * redBlackHom Q Λ i ν a) = _
    rw [← mul_assoc]
    rfl))

theorem appendRedHom_algebraMap (c : k) :
    appendRedHom Q Λ νᵢ (algebraMap k T₀' c) =
      algebraMap k T' c * appendRedHom Q Λ νᵢ 1 := by
  rw [Algebra.algebraMap_eq_smul_one, appendRedHom_apply, map_smul, KLR.Corner.val_smul,
    ← appendRedHom_apply, Algebra.smul_def]

variable (N : Type*) [AddCommGroup N]
  [Module (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) ν) N]

/-- **The last-red piece of `F_i` after adding the last red strand**: for a `T₀_ν`-module `N`,
`e_ℓ Ind_{ν_i ∘ red} N ≅ Ind_{ν_i} N` (Webster, arXiv:1309.3796v3, Proposition 4.32). -/
def lastRedPieceIndEquiv :
    fixSub k (IndK k N (redBlackHom Q Λ i ν)) (TensorProductAlgebra.lastRedIdem Q Λ νᵢ) ≃ₗ[k]
      IndK k N (appendBlackOldHom Q Λ i ν) := by
  rw [← appendRedHom_one]
  exact fixSubIndEquiv k (appendRedHom_algebraMap Q Λ i ν) (lastRedBlackCornerIso Q Λ i ν hQ)

include hQ in
theorem finrank_lastRedPiece_ind :
    Module.finrank k
        (fixSub k (IndK k N (redBlackHom Q Λ i ν)) (TensorProductAlgebra.lastRedIdem Q Λ νᵢ)) =
      Module.finrank k (IndK k N (appendBlackOldHom Q Λ i ν)) :=
  (lastRedPieceIndEquiv Q Λ i ν hQ N).finrank_eq

end Categorification.Stendhal

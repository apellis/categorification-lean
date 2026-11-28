/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendGen

/-!
# Appending a black strand to KLR diagrams of `λ`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21. The functor `𝔉_i` restricts along the map `T̃^λ_ν → T̃^λ_{{i} + ν}` appending a
black strand of colour `i` at the right (`Stendhal.appendBlackStendhal`). On KLR diagrams of `λ`
this is the first block embedding of `μ + {i}`, transported to the weight of `λ` at `{i} + ν`
(`CupCap.appendLam`, `CupCap.appendBlackAllOrders_ofKLR_appendLam`). It sends `e(s)` to
`e(s i)`, and `x_a` and `ψ_p` to themselves times `appendLam 1 = ∑_s e(s i)`.

## Main definitions

* `CupCap.appendLam`: appending the black strand to a KLR diagram of `λ`.

## Main results

* `CupCap.appendLam_e`, `CupCap.appendLam_x`, `CupCap.appendLam_ψ`, `CupCap.appendLam_one`.
* `CupCap.appendBlackAllOrders_ofKLR_appendLam`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra MvPolynomial

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (ν : Multiset I) (i : I)

local notation "σᵢ" => (Singleton.singleton (Sum.inl i) : Multiset (I ⊕ Fin ℓ))
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "μ" => stendhalWeight ℓ ν
local notation "S" => stendhalQ Q Λ

/-- **Appending a black strand of colour `i` at the right** of a KLR diagram of `λ`. -/
def appendLam : KLRAlgebra k S μ →ₙₐ[k] KLRAlgebra k S (stendhalWeight ℓ νᵢ) where
  toFun z := castKLR S (stendhalWeight_addBlack i ν) ((blockL μ σᵢ).hom S z).val
  map_zero' := by rw [map_zero, Corner.val_zero, map_zero]
  map_add' x y := by rw [map_add, Corner.val_add, map_add]
  map_mul' x y := by rw [map_mul, Corner.val_mul, map_mul]
  map_smul' c z := by rw [map_smul, Corner.val_smul, map_smul]; rfl

theorem appendLam_apply (z : KLRAlgebra k S μ) :
    appendLam Q Λ ν i z = castKLR S (stendhalWeight_addBlack i ν) ((blockL μ σᵢ).hom S z).val :=
  rfl

variable {Q Λ ν i}

theorem appendLam_e (s : Seq μ) :
    appendLam Q Λ ν i (KLRAlgebra.e s) = KLRAlgebra.e (appendBlackLoading i ν s) := by
  have hf : (blockL μ σᵢ).F s = {s.append (default : Seq σᵢ)} := by
    ext u
    change u ∈ Finset.univ.image (fun a : Seq σᵢ => s.append a) ↔ _
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun ⟨a, ha⟩ => ha ▸ congrArg s.append (Subsingleton.elim a default),
      fun h => ⟨default, h.symm⟩⟩
  rw [appendLam_apply, BlockEmb.hom_e, BlockEmb.val_gE, BlockEmb.eF, hf, eSum,
    Finset.sum_singleton, castKLR_e]
  rfl

theorem appendLam_one :
    appendLam Q Λ ν i 1 = ∑ s : Seq μ, KLRAlgebra.e (appendBlackLoading i ν s) := by
  rw [← KLRAlgebra.sum_e, map_sum]
  exact Finset.sum_congr rfl fun s _ => appendLam_e s

theorem appendLam_x (a : Fin (Multiset.card μ)) :
    appendLam Q Λ ν i (KLRAlgebra.x a) =
      KLRAlgebra.x (Fin.cast (congrArg Multiset.card (stendhalWeight_addBlack i ν))
        (Seq.posL σᵢ a)) * appendLam Q Λ ν i 1 := by
  rw [appendLam_apply, appendLam_apply, BlockEmb.hom_x, val_polCorner, pol_X, map_mul,
    castKLR_x, map_one, Corner.val_one]
  rfl

theorem appendLam_ψ {p : ℕ} (hp : p + 1 < Multiset.card μ) :
    appendLam Q Λ ν i (KLRAlgebra.ψ p) = KLRAlgebra.ψ p * appendLam Q Λ ν i 1 := by
  rw [appendLam_apply, appendLam_apply, BlockEmb.hom_ψ, BlockEmb.val_gψ _ hp, map_mul,
    castKLR_ψ, map_one, Corner.val_one]
  simp only [blockL, zero_add]

/-- On a KLR diagram, appending the black strand in the Stendhal algebra is `appendLam`. -/
theorem appendBlackAllOrders_ofKLR_appendLam (z : KLRAlgebra k S μ) :
    (appendBlackAllOrders Q Λ i ν (StendhalAlgebraAllOrders.ofKLR k Q Λ ν z)).val =
      StendhalAlgebraAllOrders.ofKLR k Q Λ νᵢ (appendLam Q Λ ν i z) := by
  rw [appendBlackAllOrders_ofKLR_val, concat_tmul, map_one, Corner.val_one, Corner.val_mul_E]
  rfl

end Categorification.Stendhal.CupCap

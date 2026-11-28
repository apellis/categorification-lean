/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicAffineQuotients
import Categorification.WeightedKLR.RedStrands.PartialStandardizationBlocksPlus
import Categorification.WeightedKLR.RedStrands.BlackIdempotent
import Categorification.KLR.ReindexCompose

/-!
# The block projection of a concatenation of relabelled diagrams

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half, step L5 (the intertwining
of the bottom corners).

Let `f : Fin m → Fin n` be an injection of red labels and `c = id ⊕ f`. The block projection
`redSubfamilyProjection` onto `T^{Λ ∘ f}(ν)` is the image in the tensor product algebra after
undoing the relabelling `𝐢 ↦ c ∘ 𝐢` (`redSubfamilyProjection_relabel_apply`). For weights
`α = c(α₀)`, `γ = c(γ₀)` with `α₀ + γ₀` the Stendhal weight of `ν`, the relabellings
`subfamilyRelabel` of `α₀` and `γ₀` are compatible with concatenation, and so the projection of
`ι_{α,γ}` of relabelled diagrams is the image of `ι_{α₀,γ₀}` of the original ones
(`redSubfamilyProjection_castAlg_concat`). This is the label computation behind the head and tail
factors of the leading Mackey data.

Webster's proof does not spell this out. No new hypothesis.

## Main definitions

* `Stendhal.subfamilyRelabel`.

## Main results

* `Stendhal.stendhalQ_sumMap`, `Stendhal.subfamilyRelabel_equiv`,
  `Stendhal.redSubfamilyProjection_relabel_apply`,
  `Stendhal.redSubfamilyProjection_castAlg_concat`,
  `Stendhal.relabelTensorProductAlgebra_tensorOfKLR_ofParams`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra
open scoped TensorProduct

variable {I k : Type*} [DecidableEq I] [CommRing k] {m n : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin n → I →₀ ℕ)
  {f : Fin m → Fin n} (hf : Function.Injective f) (ν : Multiset I)

omit [DecidableEq I] in
/-- The Stendhal parameters of `Λ`, read along `id ⊕ f`, are those of `Λ ∘ f`. -/
theorem stendhalQ_sumMap (f : Fin m → Fin n) (a b : I ⊕ Fin m) :
    stendhalQ Q Λ (Sum.map (id : I → I) f a) (Sum.map (id : I → I) f b) =
      stendhalQ Q (Λ ∘ f) a b := by
  rcases a with a | a <;> rcases b with b | b <;> rfl

omit [DecidableEq I] in
include hf in
theorem subfamilyColour_injective : Function.Injective (Sum.map (id : I → I) f) :=
  Sum.map_injective.2 ⟨Function.injective_id, hf⟩

/-- **Relabelling a weight of the red subfamily `f`** into the ambient labels:
`Seq μ₀ ≃ Seq μ`, `𝐢 ↦ (id ⊕ f) ∘ 𝐢`, for `μ = μ₀.map (id ⊕ f)`. -/
def subfamilyRelabel {μ₀ : Multiset (I ⊕ Fin m)} {μ : Multiset (I ⊕ Fin n)}
    (h : μ₀.map (Sum.map (id : I → I) f) = μ) :
    SeqRelabel k (stendhalQ Q (Λ ∘ f)) (stendhalQ Q Λ) μ₀ μ :=
  (SeqRelabel.ofInjectiveOf (subfamilyColour_injective hf) (stendhalQ Q Λ) (stendhalQ Q (Λ ∘ f))
    (fun a b _ => stendhalQ_sumMap Q Λ f a b) μ₀).castRight h

omit [DecidableEq I] in
theorem subfamilyRelabel_equiv {μ₀ : Multiset (I ⊕ Fin m)} {μ : Multiset (I ⊕ Fin n)}
    (h : μ₀.map (Sum.map (id : I → I) f) = μ) (i : Seq μ₀) :
    (subfamilyRelabel Q Λ hf h).equiv i = seqCast h (Seq.map (Sum.map (id : I → I) f) i) :=
  SeqRelabel.castRight_equiv _ h i

/-- The block projection undoes the relabelling `redSubfamilyRelabel`. -/
theorem redSubfamilyProjection_relabel_apply
    (z : KLRAlgebra k (stendhalQ Q (Λ ∘ f)) (stendhalWeight m ν)) :
    redSubfamilyProjection Q Λ f hf ν (relabelHom (redSubfamilyRelabel Q Λ f hf ν) z) =
      tensorOfKLR Q (Λ ∘ f) ν z := by
  rw [← relabelEquiv_apply]
  simp only [redSubfamilyProjection, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.symm_apply_apply]

omit [DecidableEq I] in
private theorem seqCast_seqCast_map {μ₀ μ₁ : Multiset (I ⊕ Fin m)} {μ μ' : Multiset (I ⊕ Fin n)}
    (h₀ : μ₀ = μ₁) (h₁ : μ₀.map (Sum.map (id : I → I) f) = μ) (h : μ = μ')
    (h' : μ₁.map (Sum.map (id : I → I) f) = μ') (i : Seq μ₀) :
    seqCast h (seqCast h₁ (Seq.map (Sum.map (id : I → I) f) i)) =
      seqCast h' (Seq.map (Sum.map (id : I → I) f) (seqCast h₀ i)) := by
  subst h₀ h₁ h
  rfl

/-- **The block projection of `ι_{α,γ}` of relabelled diagrams** (`α = c(α₀)`, `γ = c(γ₀)`,
`c = id ⊕ f`) is the image in `T^{Λ ∘ f}(ν)` of `ι_{α₀,γ₀}` of the original diagrams. -/
theorem redSubfamilyProjection_castAlg_concat {α₀ γ₀ : Multiset (I ⊕ Fin m)}
    {α γ : Multiset (I ⊕ Fin n)} (h₀ : α₀ + γ₀ = stendhalWeight m ν)
    (hα : α₀.map (Sum.map (id : I → I) f) = α) (hγ : γ₀.map (Sum.map (id : I → I) f) = γ)
    (h : α + γ = (stendhalWeight m ν).map (Sum.map (id : I → I) f))
    (t : TensorKLR (stendhalQ Q (Λ ∘ f)) α₀ γ₀) :
    redSubfamilyProjection Q Λ f hf ν (castAlg (stendhalQ Q Λ) h
        (concat (stendhalQ Q Λ) α γ (Algebra.TensorProduct.map
          (relabelHom (subfamilyRelabel Q Λ hf hα))
          (relabelHom (subfamilyRelabel Q Λ hf hγ)) t))) =
      tensorOfKLR Q (Λ ∘ f) ν (castKLR (stendhalQ Q (Λ ∘ f)) h₀
        (concat (stendhalQ Q (Λ ∘ f)) α₀ γ₀ t)) := by
  have hαγ : (α₀ + γ₀).map (Sum.map (id : I → I) f) = α + γ := by
    rw [Multiset.map_add, hα, hγ]
  have happ : ∀ (i : Seq α₀) (j : Seq γ₀), (subfamilyRelabel Q Λ hf hαγ).equiv (i.append j) =
      ((subfamilyRelabel Q Λ hf hα).equiv i).append ((subfamilyRelabel Q Λ hf hγ).equiv j) := by
    intro i j
    simp only [subfamilyRelabel_equiv]
    exact Seq.seqCast_map_append hα hγ hαγ i j
  rw [← relabelHom_concat _ _ _ happ, ← relabelHom_castRight,
    relabelHom_eq_of_equiv _ ((redSubfamilyRelabel Q Λ f hf ν).castLeft h₀),
    relabelHom_castLeft, redSubfamilyProjection_relabel_apply]
  intro i
  rw [SeqRelabel.castRight_equiv, subfamilyRelabel_equiv, SeqRelabel.castLeft_equiv]
  exact seqCast_seqCast_map h₀ hαγ h rfl i

/-- Relabelling `T^{Λ₁}(ν) ≅ T^{Λ₂}(ν)` along `Λ₁ = Λ₂` on the image of a KLR element, read
through the identity relabelling of the Stendhal parameters. -/
theorem relabelTensorProductAlgebra_tensorOfKLR_ofParams {n' : ℕ} {Λ₁ Λ₂ : Fin n' → I →₀ ℕ}
    (hΛ : Λ₁ = Λ₂) (hQ : ∀ a b, a ≠ b → stendhalQ Q Λ₁ a b = stendhalQ Q Λ₂ a b)
    (z : KLRAlgebra k (stendhalQ Q Λ₂) (stendhalWeight n' ν)) :
    relabelTensorProductAlgebra Q hΛ ν
        (tensorOfKLR Q Λ₁ ν (relabelHom (SeqRelabel.ofParams hQ _) z)) =
      tensorOfKLR Q Λ₂ ν z := by
  subst hΛ
  rw [relabelHom_ofParams_self]
  rfl

end Categorification.Stendhal

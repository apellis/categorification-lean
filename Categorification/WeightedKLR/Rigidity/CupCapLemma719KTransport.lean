/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationBlocksPlus
import Categorification.WeightedKLR.RedStrands.BlackIdempotent
import Categorification.WeightedKLR.RedStrands.ParabolicAffineQuotients

/-!
# Generators of tensor product algebras under relabelling and reindexing

Webster, arXiv:1309.3796v3, Lemma 7.19 (K), proof: the comparison map is checked on generators,
which are moved between the tensor product algebras of `λ`, of `λ⁺` and of the blocks of their
partial standardizations. The algebras involved differ by a reindexing `Fin.cast` of the red
labels (`castLabelsTensorProductAlgebra`), an equality of black weights
(`castTensorProductAlgebra`) or an equality of red labels (`relabelTensorProductAlgebra`). This
file records how the images of the KLR generators `e(s)`, `x_a` and `ψ_p` are carried along.

## Main definitions

* `Stendhal.castLabelsSeq`: a loading carried along a reindexing of the red labels.

## Main results

* `Stendhal.castLabels_tensorOfKLR_e`, `_x`, `_ψ`: through a reindexing of the red labels
  and an equality of weights.
* `Stendhal.relabel_tensorOfKLR_e`, `_x`, `_ψ`: through an equality of red labels.
* `Stendhal.redSubfamilyProjection_relabelEquiv`: the projection of a block, on its relabelled
  diagrams.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra

variable {I k : Type*} [DecidableEq I] [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)

section CastLabels

variable {n n' : ℕ} (h : n = n') {ν ν' : Multiset I} {μ : Multiset (I ⊕ Fin n)}
  (hμ : μ = stendhalWeight n ν)

omit [DecidableEq I] in
/-- **A loading carried along a reindexing of the red labels** and an identification of its
weight. -/
def castLabelsSeq (s : Seq μ) : Seq (stendhalWeight n' ν) := by
  subst hμ h
  exact s

omit [DecidableEq I] in
include h hμ in
theorem card_castLabels (p : Fin (Multiset.card (stendhalWeight n' ν))) :
    p.val < Multiset.card μ := by
  subst hμ h
  exact p.2

omit [DecidableEq I] in
theorem castLabelsSeq_lbl (s : Seq μ) (p : Fin (Multiset.card (stendhalWeight n' ν))) :
    (castLabelsSeq h hμ s).lbl p =
      Sum.map id (Fin.cast h) (s.lbl ⟨p.val, card_castLabels h hμ p⟩) := by
  subst hμ h
  change s.lbl p = _
  rcases s.lbl p with b | r <;> rfl

variable (Λ : Fin n' → I →₀ ℕ) (hw : ν = ν')

/-- The image of `e(s)` along a reindexing of the red labels and an equality of weights. -/
theorem castLabels_tensorOfKLR_e (s : Seq μ) (s' : Seq (stendhalWeight n' ν'))
    (hs : ∀ (p : Fin (Multiset.card (stendhalWeight n' ν'))) (q : Fin (Multiset.card μ)),
      p.val = q.val → s'.lbl p = Sum.map id (Fin.cast h) (s.lbl q)) :
    castTensorProductAlgebra Q Λ hw (castLabelsTensorProductAlgebra Q h Λ ν
        (tensorOfKLR Q (Λ ∘ Fin.cast h) ν (castKLR _ hμ (e s)))) =
      tensorOfKLR Q Λ ν' (e s') := by
  subst hμ h hw
  have hs' : s' = s := by
    apply Subtype.ext
    funext p
    refine (hs p p rfl).trans ?_
    change Sum.map id (Fin.cast rfl) (s.lbl p) = s.lbl p
    rcases s.lbl p with b | r <;> rfl
  rw [hs']
  rfl

/-- The image of `x_a` along a reindexing of the red labels and an equality of weights. -/
theorem castLabels_tensorOfKLR_x (a : Fin (Multiset.card μ))
    (a' : Fin (Multiset.card (stendhalWeight n' ν'))) (ha : a'.val = a.val) :
    castTensorProductAlgebra Q Λ hw (castLabelsTensorProductAlgebra Q h Λ ν
        (tensorOfKLR Q (Λ ∘ Fin.cast h) ν (castKLR _ hμ (x a)))) =
      tensorOfKLR Q Λ ν' (x a') := by
  subst hμ h hw
  rw [show a' = a from Fin.ext ha]
  rfl

/-- The image of `ψ_p` along a reindexing of the red labels and an equality of weights. -/
theorem castLabels_tensorOfKLR_ψ (p : ℕ) :
    castTensorProductAlgebra Q Λ hw (castLabelsTensorProductAlgebra Q h Λ ν
        (tensorOfKLR Q (Λ ∘ Fin.cast h) ν (castKLR _ hμ (ψ p)))) =
      tensorOfKLR Q Λ ν' (ψ p) := by
  subst hμ h hw
  rfl

end CastLabels

section Relabel

variable {n : ℕ} {Λ₁ Λ₂ : Fin n → I →₀ ℕ} (h : Λ₁ = Λ₂) (ν : Multiset I)

/-- The image of `e(s)` along an equality of red labels. -/
theorem relabel_tensorOfKLR_e (s : Seq (stendhalWeight n ν)) :
    relabelTensorProductAlgebra Q h ν (tensorOfKLR Q Λ₁ ν (e s)) = tensorOfKLR Q Λ₂ ν (e s) := by
  subst h
  rfl

/-- The image of `x_a` along an equality of red labels. -/
theorem relabel_tensorOfKLR_x (a : Fin (Multiset.card (stendhalWeight n ν))) :
    relabelTensorProductAlgebra Q h ν (tensorOfKLR Q Λ₁ ν (x a)) = tensorOfKLR Q Λ₂ ν (x a) := by
  subst h
  rfl

/-- The image of `ψ_p` along an equality of red labels. -/
theorem relabel_tensorOfKLR_ψ (p : ℕ) :
    relabelTensorProductAlgebra Q h ν (tensorOfKLR Q Λ₁ ν (ψ p)) = tensorOfKLR Q Λ₂ ν (ψ p) := by
  subst h
  rfl

end Relabel

theorem tensorOfKLR_one {n : ℕ} (Λ : Fin n → I →₀ ℕ) (ν : Multiset I) :
    tensorOfKLR Q Λ ν 1 = 1 := by
  simp only [tensorOfKLR, map_one]

theorem relabel_tensorOfKLR_one {n : ℕ} {Λ₁ Λ₂ : Fin n → I →₀ ℕ} (h : Λ₁ = Λ₂)
    (ν : Multiset I) : relabelTensorProductAlgebra Q h ν (tensorOfKLR Q Λ₁ ν 1) = 1 := by
  rw [tensorOfKLR_one, map_one]

/-- **The projection of a block on its relabelled diagrams** is the quotient map of the block. -/
theorem redSubfamilyProjection_relabelEquiv {m n : ℕ} (Λ : Fin n → I →₀ ℕ) (f : Fin m → Fin n)
    (hf : Function.Injective f) (ν : Multiset I)
    (z : KLRAlgebra k (stendhalQ Q (Λ ∘ f)) (stendhalWeight m ν)) :
    redSubfamilyProjection Q Λ f hf ν (relabelEquiv (redSubfamilyRelabel Q Λ f hf ν) z) =
      tensorOfKLR Q (Λ ∘ f) ν z := by
  simp only [redSubfamilyProjection, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.symm_apply_apply]

end Categorification.Stendhal

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.StendhalGrading
import Categorification.WeightedKLR.RedStrands.StendhalBasis
import Categorification.KLR.GradedBasis

/-!
# Homogeneous diagram bases in the violating quotient

B. Webster, arXiv:1309.3796v2, Definitions 4.4–4.7 and Proposition 4.16.
The Stendhal terms spanning the red-ordered algebra descend to homogeneous spanning
elements of the violating quotient. Over a field this gives a basis obtained by
choosing an independent subfamily. Its degree fibres are finite and give the
coefficients of the graded dimension when dots have positive degree. The selection
does not give a combinatorial test for membership in this basis.
-/

namespace Categorification.Stendhal

open Equiv KLR TypeA StendhalAlgebraAllOrders
open Categorification.Graded

variable {I : Type} [DecidableEq I] {ℓ : ℕ} {ν : Multiset I}

variable {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  (hρ : ∀ w, IsReduced (Multiset.card (stendhalWeight ℓ ν)) (ρ w) ∧
    wordProd (Multiset.card (stendhalWeight ℓ ν)) (ρ w) = w)

section Spanning
variable {k : Type*} [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)

/-- The image in `T^λ` of a standard Stendhal diagram (Definition 4.6 and Proposition 4.16). -/
noncomputable def tensorProductTerm (b : {b // IsStendhalTerm (ν := ν) (ℓ := ℓ) ρ b}) : TensorProductAlgebra k Q Λ ν :=
  TensorProductAlgebra.mk Q Λ ν (stendhalTerm Q Λ (fun w => (hρ w).2) b)

/-- The projected terms span the violating quotient over any commutative ring. -/
theorem span_tensorProductTerm :
    Submodule.span k (Set.range (tensorProductTerm hρ Q Λ)) = ⊤ := by
  let π := (TensorProductAlgebra.mk Q Λ ν).toLinearMap
  have htop := top_unique (span_stendhalTerm (Q := Q) (Λ := Λ) hρ)
  have h := congrArg (Submodule.map π) htop
  have hπ : Function.Surjective π := (StendhalAlgebra.violatedIdeal k Q Λ ν).ringCon.mk'_surjective
  rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top,
    LinearMap.range_eq_top.mpr hπ] at h
  exact h

variable {Q Λ}

/-- Degree of a projected Stendhal diagram, including the case that it vanishes in the quotient. -/
theorem tensorProductTerm_mem_grade (G : KLR.GradingDatum (stendhalQ Q Λ))
    (b : {b // IsStendhalTerm (ν := ν) (ℓ := ℓ) ρ b}) :
    tensorProductTerm hρ Q Λ b ∈ tensorProductGrade G ν (G.stdDeg ρ b.1) :=
  Graded.mem_map_of_mem _ _ (show stendhalTerm Q Λ (fun w => (hρ w).2) b ∈
    stendhalGrade G ν (G.stdDeg ρ b.1) from
    Graded.mem_map_of_mem _ _ (G.stdElt_mem_grade ρ b.1))

end Spanning

section Basis
variable {k : Type*} [Field k] (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)

/-- Indices of a maximal linearly independent subfamily of projected Stendhal terms.
The choice is over the coefficient field of the quotient. -/
noncomputable def tensorProductBasisIndices : Set {b // IsStendhalTerm (ν := ν) (ℓ := ℓ) ρ b} :=
  (linearIndepOn_empty k (tensorProductTerm hρ Q Λ)).extend (Set.empty_subset Set.univ)

private theorem independent_basisTerms :
    LinearIndependent k (fun b : tensorProductBasisIndices hρ Q Λ => tensorProductTerm hρ Q Λ b.1) :=
  (linearIndepOn_empty k (tensorProductTerm hρ Q Λ)).linearIndepOn_extend (Set.empty_subset Set.univ)

private theorem span_basisTerms :
    ⊤ ≤ Submodule.span k (Set.range fun b : tensorProductBasisIndices hρ Q Λ =>
      tensorProductTerm hρ Q Λ b.1) := by
  have ht := (linearIndepOn_empty k (tensorProductTerm hρ Q Λ)).span_image_extend_eq_span_image
    (Set.empty_subset Set.univ)
  rw [Set.image_univ, span_tensorProductTerm] at ht
  rw [← Set.image_eq_range (f := tensorProductTerm hρ Q Λ)]
  exact ht.ge

/-- A basis of `T^λ` selected from the images of the spanning terms of Proposition 4.16. -/
noncomputable def tensorProductBasis :
    Module.Basis (tensorProductBasisIndices hρ Q Λ) k (TensorProductAlgebra k Q Λ ν) :=
  Module.Basis.mk (independent_basisTerms hρ Q Λ) (span_basisTerms hρ Q Λ)

@[simp] theorem tensorProductBasis_apply (b : tensorProductBasisIndices hρ Q Λ) :
    tensorProductBasis hρ Q Λ b = tensorProductTerm hρ Q Λ b.1 := by
  rw [tensorProductBasis, Module.Basis.mk_apply]

variable {Q Λ} (G : KLR.GradingDatum (stendhalQ Q Λ))

private theorem finite_basis_degree (hX : ∀ a, 0 < G.degX a) (d : ℤ) :
    {b : tensorProductBasisIndices hρ Q Λ | G.stdDeg ρ b.1.1 = d}.Finite :=
  ((G.finite_stdDeg_eq ρ hX d).preimage Subtype.val_injective.injOn).preimage
    Subtype.val_injective.injOn

private theorem bddBelow_basis_degree (hX : ∀ a, 0 < G.degX a) :
    BddBelow (Set.range fun b : tensorProductBasisIndices hρ Q Λ => G.stdDeg ρ b.1.1) :=
  (G.bddBelow_stdDeg ρ (fun a => (hX a).le) Set.univ).mono
    (by rintro _ ⟨b, rfl⟩; exact ⟨b.1.1, Set.mem_univ _, rfl⟩)

/-- The coefficients of the graded dimension of `T^λ` count a chosen independent
subfamily in each diagram degree. This gives a field-level count. Webster's closed
pairing description requires the separate projective Hom calculation of Lemma 4.36. -/
theorem coeff_gdim_tensorProductGrade (hX : ∀ a, 0 < G.degX a) (d : ℤ) :
    (gdim (tensorProductGrade G ν)).coeff d =
      (Nat.card {b : tensorProductBasisIndices hρ Q Λ | G.stdDeg ρ b.1.1 = d} : ℤ) := by
  let B := tensorProductBasis hρ Q Λ
  let deg := fun b : tensorProductBasisIndices hρ Q Λ => G.stdDeg ρ b.1.1
  have hb : ∀ b, B b ∈ tensorProductGrade G ν (deg b) := fun b => by
    rw [show B b = tensorProductTerm hρ Q Λ b.1 from tensorProductBasis_apply ..]
    exact tensorProductTerm_mem_grade hρ G b.1
  have h := coeff_gdim_inf_span (tensorProductGrade G ν) deg B.linearIndependent hb Set.univ
    (fun n => by simpa [deg] using finite_basis_degree hρ G hX n)
    (by simpa [deg] using bddBelow_basis_degree hρ G hX) d
  simpa [B.span_eq, deg] using h

end Basis

end Categorification.Stendhal

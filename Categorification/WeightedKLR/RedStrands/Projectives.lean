/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.QuotientBasis
import Categorification.Algebra.Graded.HomForm

/-!
# Graded Homs between sequence projectives of the violating quotient

Webster, arXiv:1309.3796v2, §4.7, Lemma 4.36. Evaluation on the source
idempotent identifies a homogeneous Hom between undivided principal projectives
with the homogeneous component of a diagram corner. Its dimension counts the
chosen quotient basis diagrams having the specified endpoints and degree.
The library uses left projectives. For Webster’s right projectives in Definition
4.34 the two endpoint arguments of the corresponding corner are exchanged.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR TypeA Equiv Categorification.Graded StendhalAlgebraAllOrders

section Principal

variable {I : Type*} [DecidableEq I] {k : Type*} [Field k] {ℓ : ℕ} {ν : Multiset I}
    {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}
    (G : KLR.GradingDatum (stendhalQ Q Λ))

local notation "A" => TensorProductAlgebra k Q Λ ν
local notation "μ" => stendhalWeight ℓ ν

private abbrev boundary (i : Seq μ) (hi : IsRedOrdered i) : A := (TensorProductAlgebra.mk Q Λ ν) (StendhalAlgebra.e i hi)

private theorem boundary_idem (i : Seq μ) (hi : IsRedOrdered i) :
    IsIdempotentElem (boundary (Q := Q) (Λ := Λ) i hi) := by
  apply IsIdempotentElem.map
  change (_ * _ : StendhalAlgebra k Q Λ ν) = _
  apply Subtype.ext
  change StendhalAlgebraAllOrders.e i * StendhalAlgebraAllOrders.e i = (StendhalAlgebraAllOrders.e i : StendhalAlgebraAllOrders k Q Λ ν)
  simp [e_mul_e]

/-- The boundary strand idempotent remains idempotent in the violating quotient. -/
theorem isIdempotentElem_mk_e (i : Seq μ) (hi : IsRedOrdered i) :
    IsIdempotentElem (TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e i hi)) := boundary_idem i hi

/-- The undivided projective at a red-ordered sequence in Webster, §4.7. -/
def sequenceProj (i : Seq μ) (hi : IsRedOrdered i) : GProj (tensorProductGrade G ν) :=
  GProj.ofIdempotent _ (boundary_idem i hi) (mk_e_mem_tensorProductGrade G ν i hi)

end Principal

variable {I : Type} [DecidableEq I] {k : Type*} [Field k] {ℓ : ℕ} {ν : Multiset I}
    {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}
    (G : KLR.GradingDatum (stendhalQ Q Λ))

local notation "A" => TensorProductAlgebra k Q Λ ν
local notation "μ" => stendhalWeight ℓ ν

variable {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
    (hρ : ∀ w, IsReduced (Multiset.card (stendhalWeight ℓ ν)) (ρ w) ∧ wordProd (Multiset.card (stendhalWeight ℓ ν)) (ρ w) = w)

/-- The ordered boundary conditions on a basis diagram, read from bottom to top. -/
def hasEndpoints (i j : Seq μ) (b : tensorProductBasisIndices (ν := ν) hρ Q Λ) : Prop :=
  b.1.1.1 = i ∧ b.1.1.2.1 • b.1.1.1 = j

local notation "B" => tensorProductBasis (ν := ν) hρ Q Λ
local notation "Idx" => tensorProductBasisIndices (ν := ν) hρ Q Λ

open Classical in
private lemma sandwich_basis (i j : Seq μ) (hi : IsRedOrdered i) (hj : IsRedOrdered j)
    (b : Idx) : boundary j hj * B b * boundary i hi =
      if hasEndpoints hρ i j b then B b else 0 := by
  classical
  rw [tensorProductBasis_apply, tensorProductTerm, boundary, boundary, ← map_mul, ← map_mul,
    e_mul_stendhalTerm]
  by_cases ht : b.1.1.2.1 • b.1.1.1 = j
  · simp only [ht, ite_true, stendhalTerm_mul_e, hasEndpoints, and_true]
    split_ifs <;> simp_all
  · simp [ht, hasEndpoints]

open Classical in
/-- Compressing a Stendhal PBW basis diagram by two loading idempotents
selects its ordered bottom and top boundaries. -/
theorem sandwich_tensorProductBasis (i j : Seq μ) (hi : IsRedOrdered i) (hj : IsRedOrdered j)
    (b : Idx) :
    TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e j hj) * B b *
      TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e i hi) =
      if hasEndpoints hρ i j b then B b else 0 :=
  sandwich_basis hρ i j hi hj b

private lemma range_boundary (i j : Seq μ) (hi : IsRedOrdered i) (hj : IsRedOrdered j) :
    LinearMap.range (((leftIdeal (boundary i hi : A)).subtype.restrictScalars k).comp
      (idemSubspace k (leftIdeal (boundary i hi : A)) (boundary j hj : A)).subtype) =
      Submodule.span k (B '' {b | hasEndpoints hρ i j b}) := by
  classical
  apply le_antisymm
  · rintro _ ⟨⟨⟨x, hx⟩, hjx⟩, rfl⟩
    have hx' : x * boundary i hi = x := hx
    have hjx' : boundary j hj * x = x := congrArg Subtype.val hjx
    change x ∈ _
    suffices boundary j hj * x * boundary i hi ∈ Submodule.span k (B '' {b | hasEndpoints hρ i j b}) by
      simpa only [hjx', hx'] using this
    conv =>
      arg 2
      rw [← (B).linearCombination_repr x]
    rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.mul_sum, Finset.sum_mul]
    apply Submodule.sum_mem
    intro b _
    rw [mul_smul_comm, smul_mul_assoc, sandwich_basis]
    split_ifs with h
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, h, rfl⟩)
    · simp
  · apply Submodule.span_le.2
    rintro _ ⟨b, hb, rfl⟩
    change hasEndpoints hρ i j b at hb
    have he := sandwich_basis hρ i j hi hj b
    simp only [hb, ite_true] at he
    refine ⟨⟨⟨B b, ?_⟩, Subtype.ext ?_⟩, rfl⟩
    · change B b * boundary i hi = B b
      conv_lhs => rw [← he, mul_assoc _ (boundary i hi), (isIdempotentElem_mk_e i hi).eq]
      exact he
    · change boundary j hj * B b = B b
      conv_lhs => rw [← he, ← mul_assoc, ← mul_assoc, (boundary_idem j hj).eq]
      exact he

/-- Degreewise Hom dimension of undivided projectives on the diagram side of
Webster, arXiv:1309.3796v2, Lemma 4.36. The basis subfamily is chosen over the
coefficient field. Positive dot degrees ensure finiteness of every degree fibre. -/
theorem finrank_homGrade_sequenceProj (hX : ∀ a, 0 < G.degX a)
    (i j : Seq μ) (hi : IsRedOrdered i) (hj : IsRedOrdered j) (d : ℤ) :
    Module.finrank k (homGrade A (sequenceProj G j hj).grading (sequenceProj G i hi).grading d) =
      Nat.card {b : Idx | hasEndpoints hρ i j b ∧ G.stdDeg ρ b.1.1 = d} := by
  have h := (homGradeIdemEquiv (ℳ := (sequenceProj G i hi).grading)
    (boundary_idem j hj) (mk_e_mem_tensorProductGrade G ν j hj) d).finrank_eq
  refine h.trans ?_
  have hc := finrank_comap (tensorProductGrade G ν) (f :=
    ((leftIdeal (boundary i hi : A)).subtype.restrictScalars k).comp
      (idemSubspace k (leftIdeal (boundary i hi : A)) (boundary j hj : A)).subtype)
    (Subtype.val_injective.comp Subtype.val_injective) d
  refine hc.trans ?_
  rw [range_boundary hρ i j hi hj]
  apply finrank_inf_span _ (fun b : Idx => G.stdDeg ρ b.1.1) (B).linearIndependent
  · intro b
    rw [tensorProductBasis_apply]
    exact tensorProductTerm_mem_grade hρ G b.1
  · have hf : {b : Idx | G.stdDeg ρ b.1.1 = d}.Finite :=
      ((G.finite_stdDeg_eq ρ hX d).preimage Subtype.val_injective.injOn).preimage
        Subtype.val_injective.injOn
    exact hf.subset fun b hb => hb.2

end Categorification.Stendhal

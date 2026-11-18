/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleDownComparison
import Categorification.WeightedKLR.RedStrands.DoubleDownLift

/-!
# The span of downward diagrams in the signed corner

In the proof of Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v2, §4.5, Lemma 4.28, a reduced diagram on all-down boundaries,
after bubbles have been removed, is an ordinary diagram. This module assembles the
ordinary lifts of these diagrams into a single element of the ordinary violating
algebra, allowing different representatives at each matrix entry.
-/

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams KLR KLR.Diagram TypeA
open scoped Classical
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe w u v

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}} {k : Type w} [CommRing k]
  (P : Presentation.{w, max u v} (signature RD (Subtype.val ∘ Λ)) k)
  (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin ℓ → I →₀ ℕ)
  (scalars : I → I → kˣ) {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "Ord" => {s : Seq μ // IsRedOrdered s}
local notation "labels" => (Subtype.val ∘ Λ)
local notation "R" => affineCoverQ Q exponents
local notation "P₁" => addRedUpRelations RD labels k
  (addMixedBlackRelations RD labels k scalars (addDownRelations RD labels R P))
local notation "O" => downContextObj RD labels 0 [] []

/-- Send a linear diagram at two ordered all-down loadings to the entry of the
signed violating algebra used in Webster, arXiv:1309.3796v2, Definition 4.27. -/
def signedDiagramEntry (s t : Ord) :
    LinDiagram k (O (ob (word s.val))) (O (ob (word t.val))) →ₗ[k] (downObj P s ⟶ downObj P t) :=
  (signedDownEntry P s t).comp (((P.castLinearEquiv (downContextObj_word s.val)
    (downContextObj_word t.val)).toLinearMap).comp (P.linFunctor.mapLinearMap k))

/-- The subspace of the signed violating Hom spanned by diagrams all of whose
layers are downward, as in the reduction in Webster, arXiv:1309.3796v2, Lemma 4.28. -/
def downwardDiagramSpan (s t : Ord) : Submodule k (downObj P s ⟶ downObj P t) :=
  Submodule.span k {x | ∃ d : O (ob (word s.val)) ⟶ O (ob (word t.val)),
    (∀ L ∈ Diagram.layers d, ∃ g, downMove g = some L.gen.2) ∧
      x = signedDiagramEntry P s t (LinDiagram.of d)}

private theorem downwardDiagramSpan_le (s t : Ord) :
    downwardDiagramSpan P s t ≤
      LinearMap.range ((signedDiagramEntry P s t).comp (downLinear RD labels k 0 [] [])) := by
  apply Submodule.span_le.mpr
  rintro x ⟨d, hd, rfl⟩
  obtain ⟨f, hf⟩ := exists_downDiagramLift RD labels k 0 d hd
  exact ⟨LinDiagram.of f, congrArg (signedDiagramEntry P s t) hf⟩

/-- In the surjectivity proof of Webster, arXiv:1309.3796v2, Lemma 4.28,
every fixed-content matrix whose entries are spanned by downward diagrams has
a preimage under the ordinary algebra map. The geometric straightening of a
general signed diagram is a separate step of the proof. -/
theorem mem_range_ordinaryToDownwardMatrix_of_downwardDiagramSpan
    (M : downwardMatrix (P₁) ν) (hM : ∀ s t, M s t ∈ downwardDiagramSpan (P₁) s t) :
    M ∈ (ordinaryToDownwardMatrix P Q exponents scalars).range := by
  classical
  have hpre (s t : Ord) := downwardDiagramSpan_le (P₁) s t (hM s t)
  choose f hf using hpre
  let F (s t : Seq μ) : LinDiagram k (ob (word s)) (ob (word t)) :=
    if hs : IsRedOrdered s then if ht : IsRedOrdered t then f ⟨s, hs⟩ ⟨t, ht⟩ else 0 else 0
  refine ⟨affineTensorProjection exponents ν ((diagREquiv k R μ).symm
    (fun s t => (KLR.Diagram.pres k R).lin (F s t))), MatEnd.ext fun s t => ?_⟩
  refine (ordinaryToDownwardMatrix_raw_entries P Q exponents scalars F s t).trans ?_
  have hF : F s.val t.val = f s t := by simp [F, s.property, t.property]
  rw [hF]
  exact hf s t

/-- To verify that every violating Hom is spanned by downward diagrams, it suffices
to straighten individual raw signed diagrams before the violation quotient. -/
theorem downwardDiagramSpan_eq_top_of_diagrams (s t : Ord)
    (h : ∀ d : obj RD labels 0 ((word s.val).map DoubleStrand.down) ⟶
        obj RD labels 0 ((word t.val).map DoubleStrand.down),
      signedDownEntry P s t (P.diag d) ∈ downwardDiagramSpan P s t) :
    downwardDiagramSpan P s t = ⊤ := by
  apply top_unique
  intro f hf
  clear hf
  let q := violatingFunctor P (downRightWeight RD Λ ν)
  obtain ⟨⟨f⟩, rfl⟩ := q.map_surjective f
  change signedDownEntry P s t f ∈ downwardDiagramSpan P s t
  change (signedSeqObj P s.val ⟶ signedSeqObj P t.val) at f
  induction f using P.hom_induction with
  | diag d => exact h d
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add f g hf hg => rw [map_add]; exact Submodule.add_mem _ hf hg
  | smul c f hf => rw [map_smul]; exact Submodule.smul_mem _ c hf

/-- The geometric spanning step of Webster, arXiv:1309.3796v2, Lemma 4.28 implies
surjectivity of the ordinary map. The hypothesis concerns classes of single raw
signed diagrams at two specified boundaries. -/
theorem ordinaryToDownwardMatrix_surjective_of_straightening
    (h : ∀ (s t : Ord) (d : obj RD labels 0 ((word s.val).map DoubleStrand.down) ⟶
        obj RD labels 0 ((word t.val).map DoubleStrand.down)),
      signedDownEntry (P₁) s t ((P₁).diag d) ∈ downwardDiagramSpan (P₁) s t) :
    Function.Surjective (ordinaryToDownwardMatrix P Q exponents scalars (ν := ν)) := by
  intro M
  apply mem_range_ordinaryToDownwardMatrix_of_downwardDiagramSpan
  intro s t
  rw [downwardDiagramSpan_eq_top_of_diagrams _ _ _ (h s t)]
  exact Submodule.mem_top

end Categorification.Stendhal.DoubleDiagram

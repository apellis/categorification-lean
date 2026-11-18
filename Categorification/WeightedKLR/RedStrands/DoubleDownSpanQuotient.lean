/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleDownSpan
import Categorification.WeightedKLR.RedStrands.DoubleSpanningQuotient

/-! # Downward spanning descends to the ordinary comparison target
Webster, arXiv:1309.3796v2, §4.5, Lemma 4.28.
-/
noncomputable section
namespace Categorification.Stendhal.DoubleDiagram
open CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams KLR KLR.Diagram
open scoped Classical
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe u v w
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {ℓ : ℕ} {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}}
  {k : Type w} [CommRing k] (P J : Presentation.{w,max u v} (signature RD (Subtype.val ∘ Λ)) k)
  (inc : ∀ a b, P.ideal a b ≤ J.ideal a b) {ν : Multiset I}
local notation "Ord" => {s : Seq (stendhalWeight ℓ ν) // IsRedOrdered s}
local notation "O" => downContextObj RD (Subtype.val ∘ Λ) 0 [] []

private theorem signedDiagramEntry_eq (s t : Ord)
    (d : LinDiagram k (O (ob (word s.val))) (O (ob (word t.val)))) :
    signedDiagramEntry P s t d = violatingEntry P (downTriple RD Λ s) (downTriple RD Λ t)
      (LinDiagram.cast d (downContextObj_word s.val) (downContextObj_word t.val)) := by
  change signedDownEntry P s t (P.castHom (downContextObj_word (RD := RD) (Λ := Λ) s.val)
    (downContextObj_word (RD := RD) (Λ := Λ) t.val) (P.lin d)) =
    signedDownEntry P s t (P.lin (LinDiagram.cast d (downContextObj_word s.val) (downContextObj_word t.val)))
  rw [Presentation.lin_cast]
  rfl

include inc in
/-- A further quotient preserves downward spanning at each pair of loadings. -/
theorem downwardDiagramSpan_eq_top_of_ideal_le (s t : Ord) (hs : downwardDiagramSpan P s t = ⊤) :
    downwardDiagramSpan J s t = ⊤ := by
  apply top_unique
  intro f hf
  clear hf
  obtain ⟨g,rfl⟩ := violatingExtension_map_surjective P J inc (downTriple RD Λ s) (downTriple RD Λ t) f
  have hg : g ∈ downwardDiagramSpan P s t := hs.symm ▸ Submodule.mem_top
  induction hg using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨d,hd,rfl⟩ := hz
    rw [signedDiagramEntry_eq, violatingExtension_map_entry, ← signedDiagramEntry_eq]
    exact Submodule.subset_span ⟨d,hd,rfl⟩
  | zero => rw [Functor.map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [Functor.map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [Functor.map_smul]; exact Submodule.smul_mem _ c ha

variable (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin ℓ → I →₀ ℕ) (scalars : I → I → kˣ)
local notation "lab" => (Subtype.val ∘ Λ)
local notation "T" => addRedUpRelations RD lab k (addMixedBlackRelations RD lab k scalars
  (addDownRelations RD lab (affineCoverQ Q exponents) P))

/-- Entrywise downward spanning in the base presentation suffices for
surjectivity of the ordinary comparison map after adjoining the down, mixed
and red/up relations. -/
theorem ordinaryToDownwardMatrix_surjective_of_base_span (h : ∀ s t : Ord, downwardDiagramSpan P s t = ⊤) :
    Function.Surjective (ordinaryToDownwardMatrix P Q exponents scalars (ν := ν)) := by
  intro M
  apply mem_range_ordinaryToDownwardMatrix_of_downwardDiagramSpan
  intro s t
  have hi (a b : Obj (signature RD lab)) : P.ideal a b ≤ (T).ideal a b := by
    exact (Presentation.relationsHold_iff_ideal_le P (T)).mp
      (fun i => (T).lin_rel_self (.inl (.inl (.inl i)))) a b
  rw [downwardDiagramSpan_eq_top_of_ideal_le P (T) hi s t (h s t)]
  exact Submodule.mem_top

end Categorification.Stendhal.DoubleDiagram

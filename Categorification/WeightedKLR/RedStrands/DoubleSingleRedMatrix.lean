/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleSingleRedLoading
import Categorification.WeightedKLR.RedStrands.DoubleDownSpan
import Categorification.WeightedKLR.RedStrands.DoubleSingleRedSpanning
import Categorification.WeightedKLR.RedStrands.DoubleSpanningQuotient

/-! # Assembling the single-red downward corner

Webster, arXiv:1309.3796v3, §4.6, Lemma 4.29. A pure black downward
generator to the right of a fixed red remains downward after reflection.
-/

noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams KLR KL3.Diagram
open scoped Classical
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
universe w u v
variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}}
  {k : Type w} [CommRing k] (P : Presentation.{w,max u v} (signature RD (Subtype.val ∘ Λ)) k)
  {η : X}

local notation "lab" => Subtype.val ∘ Λ
local notation "tr" => DoubleStendhalTriple RD Λ 0 η

/-- The span of downward-layer diagrams projected to two specified signed boundaries. -/
def downLayerBoundarySpan (a b : tr) : Submodule k
    ((violatingFunctor P η).obj a ⟶ (violatingFunctor P η).obj b) :=
  Submodule.span k {f | ∃ d : obj RD lab 0 a.val.word ⟶ obj RD lab 0 b.val.word,
    (∀ L ∈ Diagram.layers d, ∃ g, downMove g = some L.gen.2) ∧
    f = (violatingFunctor P η).map (InducedCategory.homMk (X := a) (Y := b) (P.diag d))}

theorem downLayerBoundarySpan_le_downwardDiagramSpan {ν : Multiset I}
    (s t : {s : Seq (stendhalWeight ℓ ν) // IsRedOrdered s}) :
    downLayerBoundarySpan P (downTriple RD Λ s) (downTriple RD Λ t) ≤ downwardDiagramSpan P s t := by
  apply Submodule.span_le.mpr
  rintro f ⟨d, hd, rfl⟩
  let es := downContextObj_word (RD := RD) (Λ := Λ) s.val
  let et := downContextObj_word (RD := RD) (Λ := Λ) t.val
  let d' := Diagram.cast d es.symm et.symm
  apply Submodule.subset_span
  refine ⟨d', ?_, ?_⟩
  · exact hd
  · change signedDownEntry P s t (P.diag d) =
      signedDownEntry P s t (P.castHom es et (P.diag d'))
    rw [Presentation.castHom_diag]
    congr 2

section Single
variable {Λ₁ : Fin 1 → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}}
  (B : Presentation.{w,max u v} (signature RD (Subtype.val ∘ Λ₁)) k)
local notation "lab₁" => Subtype.val ∘ Λ₁
local notation "pfx" => ([Sum.inr 0] : List (DoubleStrand I 1))

/-- Reflection sends each pure downward black layer to an ordinary downward
layer in the signed presentation, with reversed order at a crossing. -/
theorem singleRedBlackEntry_mem_downLayerBoundarySpan {s t : List (Letter I)}
    (hs : endWeight RD lab₁ 0 (pfx ++ blackWord s ++ []) = η)
    (ht : endWeight RD lab₁ 0 (pfx ++ blackWord t ++ []) = η)
    (A : List (LayerData I)) (hA : SChain s A t)
    (hdown : ∀ x ∈ A, ∃ q : KLR.Diagram.Gen I, x.2.1 = CL.dnShape q) :
    singleRedBlackEntry B s t hs ht (LinDiagram.of (mkD RD (endWeight RD lab₁ 0 pfx) A hA)) ∈
      downLayerBoundarySpan B (singleRedTriple RD s hs) (singleRedTriple RD t ht) := by
  let d := blackDiagram RD lab₁ 0 pfx [] (mkD RD _ A hA)
  apply Submodule.subset_span
  refine ⟨d, ?_, ?_⟩
  · intro L hL
    change L ∈ Diagram.layers (blackDiagram _ _ _ _ _ _) at hL
    rw [layers_blackDiagram_mkD] at hL
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hL
    obtain ⟨q, hq⟩ := hdown x hx
    change ∃ q', downMove q' = some (.black (Sig.shape x.2.1))
    rw [hq]
    cases q with
    | dot i => exact ⟨.dot (.inl i), rfl⟩
    | cross i j => exact ⟨.cross (.inl j) (.inl i), rfl⟩
  · change (violatingFunctor B η).map (InducedCategory.homMk (X := singleRedTriple RD s hs)
      (Y := singleRedTriple RD t ht) (B.lin
        (blackLinear RD lab₁ k 0 pfx [] (LinDiagram.of (mkD RD _ A hA))))) = _
    rw [blackLinear_of]
    rfl

variable (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin 1 → I →₀ ℕ)
  (scalars : I → I → kˣ) {ν : Multiset I}
local notation "T" => addRedUpRelations RD lab₁ k
  (addMixedBlackRelations RD lab₁ k scalars (addDownRelations RD lab₁ (affineCoverQ Q exponents) B))
local notation "η₁" => downRightWeight RD Λ₁ ν

/-- For one red strand, only the downward black words following the red
are needed to span the whole matrix algebra. -/
theorem singleRed_matrix_surjective_of_blackSpan
    (span : ∀ (s t : List I) (hs : endWeight RD lab₁ 0 (pfx ++ blackWord (s.map dn) ++ []) = η₁)
      (ht : endWeight RD lab₁ 0 (pfx ++ blackWord (t.map dn) ++ []) = η₁),
      downLayerBoundarySpan (T) (singleRedTriple RD _ hs) (singleRedTriple RD _ ht) = ⊤) :
    Function.Surjective (ordinaryToDownwardMatrix B Q exponents scalars (ν := ν)) := by
  intro f
  apply mem_range_ordinaryToDownwardMatrix_of_downwardDiagramSpan
  intro s t
  by_cases hs : IsViolated s.val
  · have hz (g : downObj (T) s ⟶ downObj (T) t) : g = 0 := by
      rw [← Category.id_comp g, downObj_id_eq_zero (T) s hs, Limits.zero_comp]
    exact (hz (f s t)).symm ▸ Submodule.zero_mem _
  by_cases ht : IsViolated t.val
  · have hz (g : downObj (T) s ⟶ downObj (T) t) : g = 0 := by
      rw [← Category.comp_id g, downObj_id_eq_zero (T) t ht, Limits.comp_zero]
    exact (hz (f s t)).symm ▸ Submodule.zero_mem _
  apply downLayerBoundarySpan_le_downwardDiagramSpan
  have htop : downLayerBoundarySpan (T) (downTriple RD Λ₁ s) (downTriple RD Λ₁ t) = ⊤ := by
    obtain ⟨z,hz,he⟩ := downTriple_eq_singleRedTriple RD Λ₁ s hs
    obtain ⟨w,hw,hf⟩ := downTriple_eq_singleRedTriple RD Λ₁ t ht
    rw [he,hf]
    exact span z w hz hw
  rw [htop]
  exact Submodule.mem_top

local notation "U" => singleRedSpanningPresentation RD Λ₁ Q exponents B
local notation "V" => addRedUpRelations RD lab₁ k
  (addMixedBlackRelations RD lab₁ k scalars (addDownRelations RD lab₁ (affineCoverQ Q exponents) U))

/-- Webster v3, Lemma 4.29, surjectivity for one red strand and arbitrary
black content in the reflected KL III presentation. The red dot powers must
agree with the coroot pairings of the dominant label. -/
theorem singleRed_ordinaryToDownwardMatrix_surjective
    (he : ∀ i, (exponents 0 i : ℤ) = RD.pair (RD.iY i) (Λ₁ 0).val) :
    Function.Surjective (ordinaryToDownwardMatrix (Λ := Λ₁) (U) Q exponents scalars (ν := ν)) := by
  apply singleRed_matrix_surjective_of_blackSpan
  intro s t hs ht
  have hsub (a b : Obj (signature RD lab₁)) : (U).ideal a b ≤ (V).ideal a b := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨r, u, v, h, pre, post⟩
    apply Submodule.subset_span
    cases r with
    | user r => exact Presentation.IdealGen.intro (P := V) (.user (.inl (.inl (.inl r)))) u v h pre post
    | interchange r hr => exact Presentation.IdealGen.intro (P := V) (.interchange r hr) u v h pre post
  apply top_unique
  intro f hf
  clear hf
  obtain ⟨g, rfl⟩ := violatingExtension_map_surjective (U) (V) hsub
    (singleRedTriple RD _ hs) (singleRedTriple RD _ ht) f
  have hg := singleRed_span_downwardBlack RD Λ₁ Q exponents B he s t hs ht g
  induction hg using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨xs, hx, hdown, rfl⟩ := hz
    rw [violatingExtension_map_singleRedBlackEntry]
    exact singleRedBlackEntry_mem_downLayerBoundarySpan (V) hs ht xs hx hdown
  | zero => rw [Functor.map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [Functor.map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [Functor.map_smul]; exact Submodule.smul_mem _ c ha


end Single
end Categorification.Stendhal.DoubleDiagram

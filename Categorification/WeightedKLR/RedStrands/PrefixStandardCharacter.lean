/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LastRedMaskWords
import Categorification.WeightedKLR.RedStrands.PrefixTensorTests

/-!
# The earlier-factor simple character in standardization

In the induction in Webster, arXiv:1309.3796v2, §4.7, Theorem 4.38 and §5,
Theorem 5.8, the earlier grading is the restriction of the full red grading.
The earlier idempotent of a surviving shuffle projects to the loading of its
masked factor word. Its graded dimension in an earlier simple top computes
the corresponding tensor coordinate under an identification of the earlier
word generators.
-/
noncomputable section
namespace Categorification.Stendhal.FirstWeight

open KLR KLRAlgebra QuantumGroup Categorification.Graded GProj LieLean LieLean.QuantumGroup.GrandLoop LusztigF
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
local notation "LP" => LaurentPolynomial ℤ
private abbrev inversion := (LaurentPolynomial.invert (R := ℤ)).toRingEquiv
private local instance prefixStandardInvPair : RingHomInvPair inversion.toRingHom inversion.toRingHom := RingHomInvPair.of_ringEquiv inversion

variable {I k Y : Type*} [DecidableEq I] [Field k] [AddCommGroup Y] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin (ℓ+1) → I →₀ ℕ) (C : CartanDatum I)
  (hQ : IsRouquierQ C Q)

private abbrev wordGrading {n : ℕ} (L : Fin n → I →₀ ℕ) (C : CartanDatum I) (h : IsRouquierQ C Q) :=
  stendhalGradingDatum L h.gradingDatum (fun i => C.dot i i / 2) (dotDegree C h)

local notation "G" => wordGrading Λ C hQ
local notation "Λ₀" => Λ ∘ Fin.castSucc
local notation "G₀" => wordGrading (Λ₀) C hQ
local notation "Ps" => fun β : Multiset I => K0 (tensorProductGrade (G₀) β)

omit [DecidableEq I] in
/-- Omitting the last red strand retains the Rouquier degrees of all earlier dots and
crossings (Webster, arXiv:1309.3796v2, Definition 4.4). -/
theorem restrictRedGrading_wordGrading :
    restrictRedGrading Q Λ G = G₀ := by
  unfold wordGrading restrictRedGrading stendhalGradingDatum
  congr 1
  · funext a
    cases a <;> rfl
  · funext a b
    cases a <;> cases b <;> rfl

private def sameGradedModule {A : Type*} [Ring A] [Algebra k A]
    {g h : ℤ → Submodule k A} (e : g = h) (M : GFin h) : GFin g where
  carrier := M.carrier
  addCommGroup := M.addCommGroup
  module := M.module
  moduleK := M.moduleK
  isScalarTower := M.isScalarTower
  grading := M.grading
  decomposition := M.decomposition
  gradedSMul := e.symm ▸ M.gradedSMul
  finiteDimensional := M.finiteDimensional

private theorem sameGradedModule_idem {A : Type*} [Ring A] [Algebra k A]
    {g h : ℤ → Submodule k A} (e : g = h) (M : GFin h) (z : A) :
    integralLaurentEval (gdimPoly (Graded.idem (sameGradedModule e M).grading z)) =
      integralLaurentEval (gdimPoly (Graded.idem M.grading z)) := rfl

/-- Earlier simple top as an input to standardization, keeping its underlying graded
vector space and changing only the proof of compatibility of the algebra action. -/
def prefixStandardTop (θ : Multiset I) (b : IndecClass (tensorProductGrade (G₀) θ)) :
    GFin (tensorProductGrade (restrictRedGrading Q Λ G) θ) :=
  sameGradedModule (congrArg (fun g => tensorProductGrade g θ) (restrictRedGrading_wordGrading Λ C hQ))
    (prefixSimpleTop (Λ₀) C hQ ⟨θ,b⟩)

private theorem ofFn_map_label {J K : Type*} (f : J → K) {a : Multiset J} (s : Seq a) :
    List.ofFn (Seq.map f s).1 = (List.ofFn s.1).map f := by
  rw [List.map_ofFn]
  exact (List.ofFn_congr (Multiset.card_map f a).symm (f ∘ s.1)).symm

/-- A relabelled ordinary earlier word projects to its tensor-algebra boundary. -/
theorem parabolicPrefixProjection_of_word (p : TensorWord I ℓ)
    (t : Seq ((stendhalWeight ℓ p.content.toMultiset).map (addRedColor ℓ)))
    (ht : List.ofFn t.1 = (expandDiv p.blocks).map (addRedColor ℓ)) :
    parabolicPrefixProjection Q Λ p.content.toMultiset (e t) =
      TensorProductAlgebra.mk Q (Λ₀) p.content.toMultiset (StendhalAlgebra.e p.loading p.blocks_redOrdered) := by
  have he : t = Seq.map (addRedColor ℓ) p.loading := by
    apply Subtype.ext
    apply List.ofFn_injective
    rw [ht,ofFn_map_label,TensorWord.loading,Seq.ofFn_ofList]
  rw [he]
  exact redSubfamilyProjection_e Q Λ _ _ _ p.loading p.blocks_redOrdered

variable {R : C.toLusztig.RootDatum Y} [Finite I] (wt : Fin (ℓ+1) → Dom R) (hR : R.IsXRegular)
local notation "wt₀" => fun j : Fin ℓ => wt (Fin.castSucc j)
variable (E : DirectSum (Multiset I) (fun γ => K0 (tensorProductGrade (wordGrading
  (Λ ∘ Fin.castSucc) C hQ) γ)) ≃ₛₗ[inversion.toRingHom] integralTensor (fun j : Fin ℓ => wt (Fin.castSucc j)))
variable (hE : ∀ w, E (tensorWordProjectiveClass (Λ ∘ Fin.castSucc) C hQ w) =
  integralWordVector (C := C) (fun j : Fin ℓ => wt (Fin.castSucc j)) w)

private def prefixValue (θ : Multiset I) (b : IndecClass (tensorProductGrade (G₀) θ))
    (z : TensorProductAlgebra k Q (Λ₀) θ) :=
  integralLaurentEval (gdimPoly (Graded.idem (prefixSimpleTop (Λ₀) C hQ ⟨θ,b⟩).grading z))

omit [Finite I] in
private theorem prefixStandardValue (θ : Multiset I) (b : IndecClass (tensorProductGrade (G₀) θ))
    (z : TensorProductAlgebra k Q (Λ₀) θ) :
    integralLaurentEval (gdimPoly (Graded.idem (prefixStandardTop Λ C hQ θ b).grading z)) =
      prefixValue Λ C hQ θ b z :=
  sameGradedModule_idem (congrArg (fun g => tensorProductGrade g θ) (restrictRedGrading_wordGrading Λ C hQ))
    (prefixSimpleTop (Λ₀) C hQ ⟨θ,b⟩) z

include hE in
private theorem prefixTest_of_word (p : TensorWord I ℓ) (θ : Multiset I)
    (b : IndecClass (tensorProductGrade (G₀) θ))
    (t : Seq ((stendhalWeight ℓ θ).map (addRedColor ℓ)))
    (hc : p.content.toMultiset = θ) (ht : List.ofFn t.1 = (expandDiv p.blocks).map (addRedColor ℓ)) :
    prefixValue Λ C hQ θ b (parabolicPrefixProjection Q Λ θ (e t)) =
      prefixTopTest (Λ₀) C hQ wt₀ hR E ⟨θ,b⟩ (barOrdinaryWord p wt₀) := by
  subst θ
  exact (congrArg (prefixValue Λ C hQ _ b) (parabolicPrefixProjection_of_word Λ p t ht)).trans
    (prefixTopTest_word (Λ₀) C hQ wt₀ hR E hE p b).symm

include hE
/-- The prefix idempotent of every surviving shuffle has graded dimension given by
the earlier simple-top coordinate on its masked tensor word (Webster, §4.7, Theorem 4.38). -/
theorem prefixStandardTop_mask (θ : Multiset I) (b : IndecClass (tensorProductGrade (G₀) θ))
    {δ : Multiset (I ⊕ Fin (ℓ+1))} (w : TensorWord I (ℓ+1))
    (s : Seq ((stendhalWeight ℓ θ).map (addRedColor ℓ) + δ)) (hw : List.ofFn s.1 = expandDiv w.blocks)
    (u : {u : ShuffleOf ((stendhalWeight ℓ θ).map (addRedColor ℓ)) δ s //
      (List.ofFn u.split.2.1).head? = some (.inr (Fin.last ℓ))}) :
    integralLaurentEval (gdimPoly (Graded.idem (prefixStandardTop Λ C hQ θ b).grading
      (parabolicPrefixProjection Q Λ θ (e u.1.split.1)))) =
      prefixTopTest (Λ₀) C hQ wt₀ hR E ⟨θ,b⟩ (prefixMaskVector w wt (ordinaryShuffleEquiv w s hw u).1) := by
  let c := ordinaryShuffleEquiv w s hw u
  apply (prefixStandardValue Λ C hQ θ b _).trans
  exact prefixTest_of_word Λ C hQ wt hR E hE (prefixMaskWord w c.1) θ b _
    ((prefixMaskContent_iff w θ c.1).mp c.2.1) (ordinaryShuffleEquiv_left_word w s hw u)

/-- Earlier simple-top coordinates vanish on suffix masks with the wrong earlier black
content, as required in the standardization shuffle sum for Webster, Theorem 4.38. -/
theorem prefixTopTest_mask_of_ne (θ : Multiset I) (b : IndecClass (tensorProductGrade (G₀) θ))
    (w : TensorWord I (ℓ+1)) (c : Fin (lastRedWord w).2.length → Bool)
    (hc : (maskSubword false (lastRedBlackTags w c) : Multiset (I ⊕ Fin (ℓ+1))) ≠
      (stendhalWeight ℓ θ).map (addRedColor ℓ)) :
    prefixTopTest (Λ₀) C hQ wt₀ hR E ⟨θ,b⟩ (prefixMaskVector w wt c) = 0 :=
  prefixTopTest_word_of_ne (Λ₀) C hQ wt₀ hR E hE ⟨θ,b⟩ (prefixMaskWord w c)
    (fun he => hc ((prefixMaskContent_iff w θ c).mpr he.symm))

end Categorification.Stendhal.FirstWeight

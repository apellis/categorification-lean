/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorHomGeneration
import Categorification.WeightedKLR.RedStrands.TensorFormWordSymmetry
import Categorification.WeightedKLR.RedStrands.BoundaryHomReflection
import Categorification.WeightedKLR.RedStrands.LastRedPairing

/-!
# Boundary symmetries for the graded Hom comparison

Webster, arXiv:1309.3796v2, Lemma 4.36. Reflection exchanges two ordered
boundary projectives. A common terminal red strand can be removed on both
the algebra and representation sides.
-/

noncomputable section
namespace Categorification.Stendhal.FirstWeight

open KLR KLRAlgebra KLGamma KL2 Categorification.Graded QuantumGroup QuantumGroup.UDot
open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
local notation "LP" => LaurentPolynomial ℤ
local notation "L" => RatFunc ℚ
local instance : NeZero (RatFunc.X : L) := ⟨RatFunc.X_ne_zero⟩
variable {I : Type} {k Y : Type*} [DecidableEq I] [Field k] [AddCommGroup Y] [Finite I]
  {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)
  {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular) {ℓ : ℕ}

private abbrev canonicalGrade {m : ℕ} (Λ : Fin m → I →₀ ℕ) :=
  stendhalGradingDatum Λ hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)

section Boundary
variable (Λ : Fin ℓ → I →₀ ℕ) (wt : Fin ℓ → Dom R)
  (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i)) (ν : Multiset I)
local notation "G" => canonicalGrade C hQ Λ
local notation "K" => tensorProjectiveGroup C hQ Λ
local notation "ι" => DirectSum.lof LP _ K ν
local notation "η" => tensorModuleEquiv C hQ hR Λ wt hwt
local notation "B" => TensorPairing.orderedForm hR wt
local notation "A" => tensorHomAgrees C hQ hR Λ wt hwt ν

omit [Finite I] [DecidableEq I] in
private theorem singleton_factorial (s : List (I ⊕ Fin ℓ)) :
    divQFact2 C ((s.map (fun j => (j,(1 : ℕ)))).filterMap
      (fun q => q.1.getLeft?.map (fun i => (i,q.2)))) = 1 := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    cases a <;> simpa [divQFact2, List.filterMap_cons] using ih

omit [Finite I] in
private theorem boundary_class_congr (s t : KLR.Seq (stendhalWeight ℓ ν))
    (hs : IsRedOrdered s) (ht : IsRedOrdered t) (h : s = t) :
    K0.of (sequenceProj G s hs) = K0.of (sequenceProj G t ht) := by
  subst t
  rfl

private theorem boundary_word (s : KLR.Seq (stendhalWeight ℓ ν)) (hs : IsRedOrdered s) :
    ∃ w : TensorWord I ℓ, (η (ι (K0.of (sequenceProj G s hs)))).val = tensorWordVector w wt := by
  let l := List.ofFn s.1
  let d := l.map (fun j => (j,(1 : ℕ)))
  have he : expandDiv d = l := by
    have H (v : List (I ⊕ Fin ℓ)) : expandDiv (v.map (fun j => (j,(1 : ℕ)))) = v := by
      induction v <;> simp_all [expandDiv]
    exact H l
  have hl : (l : Multiset _) = stendhalWeight ℓ ν := Seq.coe_ofFn s
  have hd := (congrArg ((↑) : List (I ⊕ Fin ℓ) → Multiset (I ⊕ Fin ℓ)) he).trans hl
  have ho : IsRedOrdered (Seq.ofList _ hd) := by rw [Seq.ofList_congr he hd hl, Seq.ofList_ofFn]; exact hs
  obtain ⟨w, hw, hb⟩ := exists_tensorWord_of_ordered d hd ho
  have hν : w.content.toMultiset = ν := Multiset.map_injective Sum.inl_injective (add_right_cancel
    (w.blocks_weight.symm.trans ((congrArg ((↑) : List (I ⊕ Fin ℓ) → Multiset (I ⊕ Fin ℓ)) hw).trans hd)))
  obtain rfl := hν
  have hs' : w.loading = s :=
    (Seq.ofList_congr (hw.trans he) w.blocks_weight hl).trans (Seq.ofList_ofFn s hl)
  have hf : divQFact2 C w.blackBlocks = 1 := hb ▸ singleton_factorial C l
  have hk := tensorWordProjective_factorial Λ C hQ w
  rw [hf, one_smul] at hk
  refine ⟨w, ?_⟩
  have hcls := (boundary_class_congr C hQ Λ _ s w.loading hs w.blocks_redOrdered hs'.symm).trans hk
  rw [hcls]
  change (η (tensorWordProjectiveClass Λ C hQ w)).val = _
  rw [tensorModuleEquiv_word]
  rfl

/-- For arbitrary ordered boundaries, agreement for one ordering is equivalent
to agreement for the reverse ordering. -/
theorem tensorHomAgrees_sequenceProj_comm (s t : KLR.Seq (stendhalWeight ℓ ν))
    (hs : IsRedOrdered s) (ht : IsRedOrdered t) :
    A (K0.of (sequenceProj G s hs)) (K0.of (sequenceProj G t ht)) ↔
      A (K0.of (sequenceProj G t ht)) (K0.of (sequenceProj G s hs)) := by
  have hsym : ∀ a b, (G).degΨ a b = (G).degΨ b a := by
    rintro (a|a) (b|b) <;> try rfl
    exact congrArg Neg.neg (C.symm a b)
  obtain ⟨w, hw⟩ := boundary_word C hQ hR Λ wt hwt ν s hs
  obtain ⟨v, hv⟩ := boundary_word C hQ hR Λ wt hwt ν t ht
  rw [tensorHomAgrees_iff_homGdimPoly, tensorHomAgrees_iff_homGdimPoly, hw, hv,
    homGdimPoly_sequenceProj_symm G hsym s t hs ht, TensorPairing.orderedForm_tensorWord_comm hR wt v w]

end Boundary
section Append
variable (Λ : Fin (ℓ+1) → I →₀ ℕ) (wt : Fin (ℓ+1) → Dom R)
  (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i)) (ν : Multiset I)
local notation "G" => canonicalGrade C hQ Λ
local notation "Λ₀" => Λ ∘ Fin.castSucc
local notation "wt₀" => fun j => wt (Fin.castSucc j)
local notation "G₀" => canonicalGrade C hQ Λ₀
local notation "K" => tensorProjectiveGroup C hQ Λ
local notation "K₀" => tensorProjectiveGroup C hQ Λ₀
local notation "ι" => DirectSum.lof LP _ K ν
local notation "ι₀" => DirectSum.lof LP _ K₀ ν
local notation "η" => tensorModuleEquiv C hQ hR Λ wt hwt
local notation "η₀" => tensorModuleEquiv C hQ hR Λ₀ wt₀ (fun j i => hwt (Fin.castSucc j) i)
local notation "A" => tensorHomAgrees C hQ hR Λ wt hwt ν
local notation "A₀" => tensorHomAgrees C hQ hR Λ₀ wt₀ (fun j i => hwt (Fin.castSucc j) i) ν
local notation "app" => appendRedLoading (ℓ := ℓ) (ν := ν)

omit [Finite I] [DecidableEq I] in
private theorem canonicalGrade_restrict : restrictRedGrading Q Λ G = G₀ := by
  unfold restrictRedGrading canonicalGrade stendhalGradingDatum
  congr 1
  · funext a
    cases a <;> rfl
  · funext a b
    cases a <;> cases b <;> rfl

private theorem appendRed_sequence_vector (s : KLR.Seq (stendhalWeight ℓ ν)) (hs : IsRedOrdered s) :
    (η (ι (K0.of (sequenceProj G (app s) ((appendRedLoading_ordered_iff s).2 hs))))).val =
      appendTensor wt (η₀ (ι₀ (K0.of (sequenceProj G₀ s hs)))).val
        (IrreducibleModule.hwv R (RatFunc.X : L) (wt (Fin.last ℓ)).1) := by
  rw [← tensorModuleEquiv_lastRed C hQ hR Λ wt hwt (ι₀ (K0.of (sequenceProj G₀ s hs)))]
  apply congrArg (fun a => (η a).val)
  rw [totalLastRedIndK0, DirectSum.toModule_lof, LinearMap.comp_apply]
  apply congrArg (ι)
  have H (D : GradingDatum (stendhalQ Q Λ₀)) (h : restrictRedGrading Q Λ G = D) :
      (h ▸ lastRedIndK0 G ν : K0 (tensorProductGrade D ν) →ₗ[LP] K ν)
        (K0.of (sequenceProj D s hs)) =
        K0.of (sequenceProj G (app s) ((appendRedLoading_ordered_iff s).2 hs)) := by
    subst D
    exact lastRedIndK0_sequenceProj G ν s hs
  exact (H G₀ (canonicalGrade_restrict C hQ Λ)).symm

/-- In the red–red endpoint case of Webster's Lemma 4.36, agreement is
equivalent to agreement for the two shorter boundaries. -/
theorem tensorHomAgrees_appendRed (s t : KLR.Seq (stendhalWeight ℓ ν))
    (hs : IsRedOrdered s) (ht : IsRedOrdered t) :
    A (K0.of (sequenceProj G (app s) ((appendRedLoading_ordered_iff s).2 hs)))
      (K0.of (sequenceProj G (app t) ((appendRedLoading_ordered_iff t).2 ht))) ↔
    A₀ (K0.of (sequenceProj G₀ s hs)) (K0.of (sequenceProj G₀ t ht)) := by
  have he : gdimPoly (homGrade (TensorProductAlgebra k Q Λ ν)
      (sequenceProj G (app s) ((appendRedLoading_ordered_iff s).2 hs)).grading
      (sequenceProj G (app t) ((appendRedLoading_ordered_iff t).2 ht)).grading) =
      gdimPoly (homGrade (TensorProductAlgebra k Q Λ₀ ν)
        (sequenceProj G₀ s hs).grading (sequenceProj G₀ t ht).grading) := by
    classical
    let polynomial (f : ℤ → ℤ) : LP :=
      if hf : (Function.support f).Finite then .ofCoeff (Finsupp.ofSupportFinite f hf) else 0
    change polynomial _ = polynomial _
    apply congrArg polynomial
    funext d
    apply congrArg (fun a : ℕ => (a : ℤ))
    have H := finrank_homGrade_appendRed hQ G ν s t hs ht d
    rw [canonicalGrade_restrict C hQ Λ] at H
    exact H
  rw [tensorHomAgrees_iff_homGdimPoly, tensorHomAgrees_iff_homGdimPoly, he,
    appendRed_sequence_vector C hQ hR Λ wt hwt ν t ht, appendRed_sequence_vector C hQ hR Λ wt hwt ν s hs,
    TensorPairing.orderedForm_append_highest]

end Append
end Categorification.Stendhal.FirstWeight

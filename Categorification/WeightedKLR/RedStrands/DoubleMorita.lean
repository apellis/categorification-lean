/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleAllDownIdeal
import Mathlib.CategoryTheory.Idempotents.FunctorExtension
import Mathlib.CategoryTheory.Preadditive.Mat

/-!
# The all-down inclusion after additive idempotent completion

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
§4.5, Theorem 4.29. In a fixed violating fibre, generation by all-down
boundary identities makes each object a retract of a finite direct sum of
all-down objects. The full all-down inclusion therefore induces an equivalence
of additive idempotent completions.
-/

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory Idempotents QuantumGroup QuantumGroup.UDot StringDiagrams
open scoped BigOperators

section Completion

variable {D : Type*} [Category* D] [Preadditive D]
  {k : Type*} [CommRing k] [Linear k D] (S : ObjectProperty D)

/-- A morphism in the span of composites through a family is a finite sum of such composites,
with coefficients absorbed in the first factor. -/
theorem finiteFactorization {a b : D} {f : a ⟶ b}
    (hf : f ∈ factorSpan k id S a b) :
    ∃ (n : ℕ) (c : Fin n → S.FullSubcategory)
      (u : ∀ i, a ⟶ (c i).obj) (v : ∀ i, (c i).obj ⟶ b), (∑ i, u i ≫ v i) = f := by
  classical
  let factors : Set (a ⟶ b) :=
    {g | ∃ c, S c ∧ ∃ (u : a ⟶ c) (v : c ⟶ b), g = u ≫ v}
  change f ∈ Submodule.span k factors at hf
  obtain ⟨r, hr⟩ := (Finsupp.mem_span_iff_linearCombination k factors f).mp hf
  choose c hc u v huv using fun g : factors => g.property
  let e := Fintype.equivFin (↑r.support : Type _)
  refine ⟨Fintype.card (↑r.support : Type _), fun i => ⟨c (e.symm i), hc (e.symm i)⟩,
    fun i => r (e.symm i) • u (e.symm i), fun i => v (e.symm i), ?_⟩
  simp only [Linear.smul_comp, ← huv]
  calc
    _ = ∑ x : ↑r.support, r x.val • x.val.val :=
      Equiv.sum_comp e.symm (fun x : ↑r.support => r x.val • x.val.val)
    _ = ∑ x ∈ r.support, r x • x.val :=
      Finset.sum_coe_sort r.support (fun x : factors => r x • x.val)
    _ = f := by
      simpa only [Finsupp.linearCombination_apply, Finsupp.sum] using hr

private theorem matrixRetract
    (h : ∀ a : D, 𝟙 a ∈ factorSpan k id S a a) (M : Mat_ D) :
    ∃ N : Mat_ S.FullSubcategory, Nonempty (Retract M (S.ι.mapMat_.obj N)) := by
  classical
  choose n c u v huv using fun i : M.ι => finiteFactorization S (h (M.X i))
  let N : Mat_ S.FullSubcategory := ⟨Σ i : M.ι, Fin (n i), fun t => c t.1 t.2⟩
  let iota : M ⟶ S.ι.mapMat_.obj N := fun i t =>
    if h : i = t.1 then eqToHom (congrArg M.X h) ≫ u t.1 t.2 else 0
  let pi : S.ι.mapMat_.obj N ⟶ M := fun t j =>
    if h : t.1 = j then v t.1 t.2 ≫ eqToHom (congrArg M.X h) else 0
  refine ⟨N, ⟨⟨iota, pi, ?_⟩⟩⟩
  apply Mat_.hom_ext
  intro i j
  rw [Mat_.comp_apply]
  change (∑ t : Σ a : M.ι, Fin (n a), iota i t ≫ pi t j) = _
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  calc
    _ = ∑ t : Fin (n i), iota i ⟨i, t⟩ ≫ pi ⟨i, t⟩ j := by
      apply Finset.sum_eq_single i
      · intro a _ ha
        apply Finset.sum_eq_zero
        intro t _
        simp [iota, ha.symm]
      · simp
    _ = _ := by
      by_cases hij : i = j
      · subst j
        rw [Mat_.id_apply_self, ← huv i]
        apply Finset.sum_congr rfl
        intro t _
        calc
          _ = (𝟙 (M.X i) ≫ u i t) ≫ (v i t ≫ 𝟙 (M.X i)) := by
            simp only [iota, pi, dite_eq_left rfl, eqToHom_refl]
            rfl
          _ = _ := by rw [Category.id_comp, Category.comp_id]
      · simp [iota, pi, hij]

private abbrev onKaroubi {A B : Type*} [Category* A] [Category* B]
    (F : A ⥤ B) : Karoubi A ⥤ Karoubi B :=
  FunctorExtension₁.obj (F ⋙ toKaroubi B)

private def fullyFaithfulOnKaroubi {A B : Type*} [Category* A] [Category* B]
    (F : A ⥤ B) (hF : F.FullyFaithful) : (onKaroubi F).FullyFaithful where
  preimage {P Q} f := ⟨hF.preimage f.f, hF.map_injective (by
    have hc : F.map P.p ≫ f.f ≫ F.map Q.p = f.f := f.comm
    have hp : F.map (hF.preimage f.f) = f.f := hF.map_preimage f.f
    simp only [F.map_comp]
    exact (congrArg (fun g => F.map P.p ≫ g ≫ F.map Q.p) hp).trans (hc.trans hp.symm))⟩
  map_preimage f := Karoubi.hom_ext _ _ (hF.map_preimage _)
  preimage_map f := Karoubi.hom_ext _ _ (hF.preimage_map _)

private def fullyFaithfulMatrixInclusion : S.ι.mapMat_.FullyFaithful where
  preimage f i j := ObjectProperty.homMk (f i j)
  map_preimage _ := rfl
  preimage_map _ := Mat_.hom_ext _ _ fun _ _ => ObjectProperty.hom_ext S rfl

private theorem isEquivalenceOnKaroubi {A B : Type*} [Category* A] [Category* B]
    (F : A ⥤ B) (ff : F.FullyFaithful)
    (h : ∀ X : B, ∃ Y : A, Nonempty (Retract X (F.obj Y))) :
    (onKaroubi F).IsEquivalence := by
  let full := fullyFaithfulOnKaroubi F ff
  refine ⟨full.faithful, full.full, ?_⟩
  constructor
  intro P
  obtain ⟨Y, ⟨r⟩⟩ := h P.X
  have split {X : B} (f : P.X ⟶ X) : r.i ≫ r.r ≫ f = f := by
    rw [← Category.assoc, r.retract, Category.id_comp]
  let p := ff.preimage (r.r ≫ P.p ≫ r.i)
  have hp : F.map p = r.r ≫ P.p ≫ r.i := ff.map_preimage _
  have idem : p ≫ p = p := by
    apply ff.map_injective
    simp [F.map_comp, hp, Category.assoc, split, P.idem_assoc]
  let Q : Karoubi A := ⟨Y, p, idem⟩
  refine ⟨Q, ⟨{
    hom := ⟨r.r ≫ P.p, ?_⟩
    inv := ⟨P.p ≫ r.i, ?_⟩
    hom_inv_id := Karoubi.hom_ext _ _ ?_
    inv_hom_id := Karoubi.hom_ext _ _ ?_ }⟩⟩
  · change F.map p ≫ (r.r ≫ P.p) ≫ P.p = r.r ≫ P.p
    simp [hp, Category.assoc, split, P.idem]
  · change P.p ≫ (P.p ≫ r.i) ≫ F.map p = P.p ≫ r.i
    simp [hp, Category.assoc, split, P.idem_assoc]
  · change (r.r ≫ P.p) ≫ P.p ≫ r.i = F.map p
    simp [hp, Category.assoc, P.idem_assoc]
  · change (P.p ≫ r.i) ≫ r.r ≫ P.p = P.p
    simp [Category.assoc, split, P.idem]

end Completion

section AllDownFibre

variable {I X Y : Type*} {C : CartanDatum I} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {ℓ : ℕ} {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}}
  {k : Type*} [CommRing k] (P : Presentation (signature RD (fun r => (Λ r).val)) k)
  {right : X}

/-- The object property defining the full all-down subcategory of the violating fibre. -/
def allDownProperty : ObjectProperty (ViolatingCategory P right) := fun b => b.as.val.AllDown

/-- The all-down inclusion on additive idempotent completions. -/
abbrev allDownCompletionInclusion :=
  onKaroubi (allDownProperty P (right := right)).ι.mapMat_

/-- The Morita step of Webster, arXiv:1309.3796v2, §4.5, Theorem 4.29.
If the all-down boundary identities generate in a fixed violating fibre,
the full all-down inclusion induces an equivalence on additive idempotent
completions. The source is the all-down subcategory of the signed quotient. -/
theorem allDownCompletionInclusion_isEquivalence
    (h : ∀ b : BoundaryCategory P right, 𝟙 ((violatingFunctor P right).obj b) ∈
      factorSpan k (violatingFunctor P right).obj (fun c => c.val.AllDown) b b) :
    (allDownCompletionInclusion P (right := right)).IsEquivalence := by
  apply isEquivalenceOnKaroubi _ (fullyFaithfulMatrixInclusion (allDownProperty P))
  apply matrixRetract (k := k)
  rintro ⟨b⟩
  have le : factorSpan k (violatingFunctor P right).obj (fun c => c.val.AllDown) b b ≤
      factorSpan k id (allDownProperty P) ((violatingFunctor P right).obj b)
        ((violatingFunctor P right).obj b) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨c, hc, u, v, rfl⟩
    exact Submodule.subset_span ⟨(violatingFunctor P right).obj c, hc, u, v, rfl⟩
  exact le (h b)

end AllDownFibre

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {ℓ : ℕ} {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}}
  {k : Type w} [CommRing k] (P : Presentation.{w, max u v} (signature RD (fun r => (Λ r).val)) k)
  {right : X}

/-- The mixed black and red/up relations (2.3c), (2.4a), and (4.4e) give the
equivalence of additive idempotent completions for the all-down inclusion
in each violating fibre (Webster, arXiv:1309.3796v2, §4.5, Theorem 4.29). -/
theorem allDownCompletionInclusion_isEquivalence_addRelations (t : I → I → kˣ) :
    (allDownCompletionInclusion (right := right)
      (addRedUpRelations RD (fun r => (Λ r).val) k
        (addMixedBlackRelations RD (fun r => (Λ r).val) k t P))).IsEquivalence :=
  allDownCompletionInclusion_isEquivalence _ (id_mem_allDownFactorSpan P t)

end Categorification.Stendhal.DoubleDiagram

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.RedStrands.DoubleBoundaryInduction
import Categorification.WeightedKLR.RedStrands.DoubleRedUp
import Categorification.WeightedKLR.RedStrands.DoubleViolatingQuotient

/-!
# Generation by all-down identities in a fixed weight

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
§4.5, proof of Theorem 4.29. In the violating quotient, the red/up bigons give
the red crossing step of the induction. The remaining input is the local
factorization of the identity for a downward strand followed by an upward strand.
-/

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory StringDiagrams QuantumGroup QuantumGroup.UDot

section Factor

variable {T D : Type*} [Category* D] (k : Type*) [CommRing k] [Preadditive D] [Linear k D]
    (G : T → D) (S : T → Prop)

/-- Linear combinations of maps through members of a specified family of objects. -/
def factorSpan (a b : T) : Submodule k (G a ⟶ G b) :=
  Submodule.span k {f | ∃ c, S c ∧ ∃ (u : G a ⟶ G c) (v : G c ⟶ G b), f = u ≫ v}

private theorem factorSpan_comp {a b c d : T} (u : G a ⟶ G b) (v : G c ⟶ G d)
    {f : G b ⟶ G c} (hf : f ∈ factorSpan k G S b c) : u ≫ f ≫ v ∈ factorSpan k G S a d := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨x, hx, g, h, rfl⟩ := hf
    exact Submodule.subset_span ⟨x, hx, u ≫ g, h ≫ v, by simp⟩
  | zero => simp
  | add f g _ _ hf hg =>
    rw [Preadditive.add_comp, Preadditive.comp_add]
    exact Submodule.add_mem _ hf hg
  | smul r f _ hf =>
    rw [Linear.smul_comp, Linear.comp_smul]
    exact Submodule.smul_mem _ r hf

private theorem factorSpan_id_of_iso {a b : T} (e : G a ≅ G b)
    (h : 𝟙 (G b) ∈ factorSpan k G S b b) : 𝟙 (G a) ∈ factorSpan k G S a a := by
  simpa only [Category.id_comp, Iso.hom_inv_id] using factorSpan_comp k G S e.hom e.inv h

private theorem factorSpan_le_of_id (S' : T → Prop)
    (h : ∀ c, S' c → 𝟙 (G c) ∈ factorSpan k G S c c) (a b : T) :
    factorSpan k G S' a b ≤ factorSpan k G S a b := by
  apply Submodule.span_le.mpr
  rintro _ ⟨c, hc, u, v, rfl⟩
  change u ≫ v ∈ factorSpan k G S a b
  simpa only [Category.id_comp] using factorSpan_comp k G S u v (h c hc)

end Factor

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
    {RD : WeightDatum C X Y} {ℓ : ℕ} {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}}
    {k : Type w} [CommRing k] (P : Presentation.{w, max u v} (signature RD (fun r => (Λ r).val)) k)
    {right : X}

local notation "Q" => addRedUpRelations RD (fun r => Subtype.val (Λ r)) k P
local notation "F" => violatingFunctor Q right
local notation "T" => DoubleStendhalTriple RD Λ 0 right

/-- The ideal-generation step in the fixed-weight violating quotient (Webster,
arXiv:1309.3796v2, §4.5, Theorem 4.29). The sole local hypothesis is the mixed black
factorization: one may use the swapped boundary and, for matching colours, the boundary
with the pair removed. Equation (4.4e) supplies the red/up isomorphism. -/
theorem id_mem_allDownFactorSpan_of_mixed
    (mixed : ∀ L R i j (b : T), b.val.word = L ++ .inl (false, j) :: .inl (true, i) :: R →
      𝟙 ((F).obj b) ∈ factorSpan k (F).obj (fun d =>
        d.val.word = L ++ .inl (true, i) :: .inl (false, j) :: R ∨
          j = i ∧ d.val.word = L ++ R) b b)
    (b : T) : 𝟙 ((F).obj b) ∈ factorSpan k (F).obj (fun d => d.val.AllDown) b b := by
  let good (d : DoubleBoundary I ℓ) := ∀ h : d.rightWeight RD (fun r => (Λ r).val) 0 = right,
    𝟙 ((F).obj ⟨d, h⟩) ∈ factorSpan k (F).obj (fun c => c.val.AllDown) ⟨d, h⟩ ⟨d, h⟩
  suffices all : ∀ d, good d from all b.val b.property
  apply DoubleBoundary.induction_moveUpLeft
  · intro d hd h
    exact Submodule.subset_span ⟨⟨d, h⟩, hd, 𝟙 _, 𝟙 _, (Category.id_comp _).symm⟩
  · intro i R h hw
    let d : BoundaryCategory Q right := ⟨⟨_, h⟩, hw⟩
    have hzero : 𝟙 ((F).obj d) = 0 :=
      DoubleViolatingQuotient.id_eq_zero k (tripleObj Q) (x := d) ⟨(true, i), rfl⟩
    rw [hzero]
    exact Submodule.zero_mem _
  · intro L R i r swap h hw
    let b' : T := ⟨⟨L ++ .inr r :: .inl (true, i) :: R, h⟩, hw⟩
    let c : T := ⟨⟨L ++ .inl (true, i) :: .inr r :: R, by
      rw [List.filterMap_append] at h ⊢
      exact h⟩, by
      simpa [DoubleBoundary.rightWeight, add_left_comm, add_comm, add_assoc] using hw⟩
    let iso : (F).obj b' ≅ (F).obj c := (F).mapIso (InducedCategory.isoMk (by
      simpa [tripleObj, b', c, List.append_assoc] using
        redUpCrossingIso RD (fun r => (Λ r).val) P 0 L r i R))
    exact factorSpan_id_of_iso k (F).obj (fun d => d.val.AllDown) iso (swap c.val.redOrder c.property)
  · intro L R i j swap erase h hw
    let b' : T := ⟨⟨_, h⟩, hw⟩
    refine factorSpan_le_of_id k (F).obj (fun d => d.val.AllDown) _ ?_ b' b' (mixed L R i j b' rfl)
    rintro ⟨⟨w, ord⟩, weight⟩ hword
    change w = _ ∨ _ ∧ w = _ at hword
    obtain rfl | ⟨heq, rfl⟩ := hword
    · exact swap ord weight
    · exact erase heq ord weight

end Categorification.Stendhal.DoubleDiagram

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleDownComparison
import Categorification.WeightedKLR.RedStrands.DoubleVacuumCharacter
import Categorification.WeightedKLR.RedStrands.EmptyTensor

/-!
# The all-down comparison for the empty red family

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
§4.5, Lemma 4.28. In positive black content the violating ideal kills both
algebras. In black content zero, the unique matrix entry is the signed vacuum
endomorphism algebra, and the ordinary comparison preserves scalars.
-/

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory StringDiagrams QuantumGroup QuantumGroup.UDot KLR KLR.Diagram
open scoped Classical
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {Λ : Fin 0 → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}}
  {k : Type w} [CommRing k]
  (base : Presentation.{w, max u v} (signature RD (Subtype.val ∘ Λ)) k)
  (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin 0 → I →₀ ℕ) (scalars : I → I → kˣ)

local notation "labels" => Subtype.val ∘ Λ
local notation "R" => affineCoverQ Q exponents
local notation "signed" => addRedUpRelations RD labels k
  (addMixedBlackRelations RD labels k scalars (addDownRelations RD labels R base))

private theorem isViolated_of_empty_red {ν : Multiset I} (hν : ν ≠ 0)
    (s : Seq (stendhalWeight 0 ν)) : IsViolated s := by
  have h : 0 < (stendhalWeight 0 ν).card := by
    simpa [stendhalWeight] using Multiset.card_pos.mpr hν
  refine ⟨h, ?_⟩
  rcases s.lbl ⟨0, h⟩ with _ | r
  · rfl
  · exact r.elim0

private theorem subsingleton_downwardMatrix_of_empty_red {ν : Multiset I} (hν : ν ≠ 0) :
    Subsingleton (downwardMatrix signed ν) := by
  refine ⟨fun f g => MatEnd.ext fun s t => ?_⟩
  have hzero (m : downObj signed s ⟶ downObj signed t) : m = 0 := by
    rw [← Category.id_comp m, downObj_id_eq_zero signed s (isViolated_of_empty_red hν s.val),
      Limits.zero_comp]
  exact (hzero (f s t)).trans (hzero (g s t)).symm

local notation "EmptyBoundary" => {s : Seq (stendhalWeight 0 (0 : Multiset I)) // IsRedOrdered s}

private def emptyBoundary : EmptyBoundary := ⟨vacuumSeq, vacuumSeq_ordered⟩

private theorem eq_emptyBoundary (s : EmptyBoundary) : s = emptyBoundary := by
  apply Subtype.ext
  apply Subtype.ext
  funext a
  have h := a.isLt
  simp [stendhalWeight] at h

private theorem empty_boundary_word :
    (downTriple RD Λ (emptyBoundary (I := I))).val.word = [] := by
  change (List.ofFn (vacuumSeq (I := I) (ℓ := 0)).lbl).map DoubleStrand.down = []
  apply List.length_eq_zero_iff.mp
  simp [stendhalWeight]

private theorem scalarMap_empty_end_bijective [IsEmpty base.Rel]
    (right : X) (hr : right = 0) (b : DoubleStendhalTriple RD Λ 0 right) (hb : b.val.word = []) :
    Function.Bijective (algebraMap k (End ((violatingFunctor signed right).obj b))) := by
  subst right
  have eq : b = vacuumBoundary signed := Subtype.ext (DoubleBoundary.ext hb)
  rw [eq]
  exact vacuum_algebraMap_bijective base scalars R

private theorem scalarMap_empty_matrix_bijective [IsEmpty base.Rel] :
    Function.Bijective (algebraMap k (downwardMatrix signed 0)) := by
  let s := emptyBoundary (I := I)
  have hr : downRightWeight RD Λ (0 : Multiset I) = 0 := by simp [downRightWeight]
  have hVac : Function.Bijective (algebraMap k (End (downObj signed s))) :=
    scalarMap_empty_end_bijective base Q exponents scalars _ hr _ empty_boundary_word
  have hEntry (c : k) : (algebraMap k (downwardMatrix signed 0) c) s s =
      algebraMap k (End (downObj signed s)) c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, MatEnd.smul_apply,
      MatEnd.one_apply_self]
    rfl
  constructor
  · intro c d h
    apply hVac.injective
    rw [← hEntry, ← hEntry, h]
  · intro a
    obtain ⟨c, hc⟩ := hVac.surjective (a s s)
    refine ⟨c, MatEnd.ext fun i j => ?_⟩
    obtain rfl : i = s := eq_emptyBoundary i
    obtain rfl : j = s := eq_emptyBoundary j
    exact (hEntry c).trans hc

/-- The ordinary diagram map in Webster, arXiv:1309.3796v2, §4.5, Lemma 4.28,
is bijective for the empty red family in every black content, for the signed
presentation with the downward, mixed black, and red/up relations over a free base. -/
theorem ordinaryToDownwardMatrix_bijective_empty_red [IsEmpty base.Rel] (ν : Multiset I) :
    Function.Bijective (ordinaryToDownwardMatrix base Q exponents scalars (ν := ν)) := by
  by_cases hν : ν = 0
  · subst ν
    let E := tensorProductAlgebraZeroEquiv (k := k) Q exponents
    have hOrd : Function.Bijective (algebraMap k (TensorProductAlgebra k Q exponents 0)) := by
      have he : ⇑(algebraMap k (TensorProductAlgebra k Q exponents 0)) = E.symm := by
        funext c
        simpa only [Algebra.algebraMap_self, RingHom.id_apply] using (E.symm.commutes c).symm
      rw [he]
      exact E.symm.bijective
    let f := ordinaryToDownwardMatrix base Q exponents scalars (ν := 0)
    apply (Function.Bijective.of_comp_iff (⇑f) hOrd).mp
    have hcomp : (⇑f) ∘ algebraMap k (TensorProductAlgebra k Q exponents 0) =
        algebraMap k (downwardMatrix signed 0) := funext f.commutes
    rw [hcomp]
    exact scalarMap_empty_matrix_bijective base Q exponents scalars
  · have hOrd : Subsingleton (TensorProductAlgebra k Q exponents ν) := by
      have hExponents : exponents = Fin.elim0 := funext fun r => r.elim0
      subst exponents
      exact subsingleton_emptyTensorAlgebra Q hν
    have hSigned := subsingleton_downwardMatrix_of_empty_red base Q exponents scalars hν
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ y⟩⟩

end Categorification.Stendhal.DoubleDiagram

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLVacuumFunctor

/-!
# The vacuum evaluation kills violated boundaries

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29. The reflection of a boundary reverses
it, so the leftmost boundary strand is the first functor applied to the vacuum. When that strand
is black (a violated boundary, Definition 4.27 of arXiv:1309.3796v2) its functor is cyclotomic
induction or restriction in a colour with cyclotomic polynomial `1`, which kills the vacuum
supported on the empty block. Hence the vacuum evaluation functor of the downward block factors
through the violating quotient (`downVacuumQuotientFunctor`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Diagrams.BicatInterp

open CategoryTheory CategoryTheory.Limits TwoRep StringDiagrams

universe u₀ u₁ u₂ w v u

variable {S : Signature.{u₀, u₁, u₂}} {k : Type w} [CommRing k]
  (M : Model S (LinearCat.{w, v, u} k))

/-- **Words whose last strand kills an object kill it.** The last strand of a word is the first
functor applied, so if it sends `V` to a zero object, so does the whole word. -/
theorem isZero_word_obj_of_getLast {t : S.Region} (V : M.obj t) {c : S.Colour}
    (hz : ∀ (y : S.Region) (hx : S.colourTgt c = t) (hy : S.colourSrc c = y),
      IsZero ((M.strandAt c t y hx hy).obj.obj V)) :
    ∀ (s : S.Region) (w : List S.Colour) (h : S.ok s w) (e : S.endR s w = t),
      w.getLast? = some c → IsZero ((M.word s w t h e).obj.obj V)
  | _, [], _, _, hc => by simp at hc
  | s, [c'], h, e, hc => by
    obtain rfl : c' = c := by simpa using hc
    exact hz s e h.1
  | s, c₀ :: c' :: w, h, e, hc =>
    Functor.map_isZero (M.strandAt c₀ _ _ rfl h.1).obj
      (isZero_word_obj_of_getLast V hz (S.colourTgt c₀) (c' :: w) h.2 e (by simpa using hc))

end Categorification.Diagrams.BicatInterp

namespace Categorification.InductionAlong

open CategoryTheory

/-- Extension of scalars sends a zero module to a zero module. -/
theorem functor_id_eq_zero {A B : Type u} [Ring A] [Ring B] {φ : A →ₙ+* B}
    {M : ModuleCat.{max u w} A} (h : 𝟙 M = 0) : 𝟙 ((functor.{u, w} φ).obj M) = 0 := by
  rw [← (functor.{u, w} φ).map_id, h, Functor.map_zero]

end Categorification.InductionAlong

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Limits QuantumGroup QuantumGroup.UDot StringDiagrams KLR
  TwoRep CyclotomicAction DoubleDiagram KL3.Diagram Diagrams.BicatInterp InductionAlong

universe u v w v₁

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type u} {ℓ : ℕ} {Λ : Fin ℓ → I →₀ ℕ} {C : CartanDatum I}
  [DecidableEq I] {k : Type v} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {hQ : IsRouquierQ C Q} (hc : CoverDotCentral Λ C Q) {ν : Multiset I}

local notation "Wgt" => cyclotomicCoverWeightDatum Λ C
local notation "L" => cyclotomicCoverHighest (I := I) (ℓ := ℓ)
local notation "S" => cyclotomicCoverQ C Λ Q
local notation "hS" => isRouquierQ_cyclotomicCoverQ C Λ Q hQ
local notation "sym" => IsRouquierQ.klrSymm hS
local notation "lead" => IsRouquierQ.polyInY_leading hS
local notation "deg" => IsRouquierQ.polyInY_degree_pair hS Wgt
local notation "p" => cyclotomicCoverPolynomial (I := I) (ℓ := ℓ) (k := k)
local notation "monic" => cyclotomicCoverPolynomial_monic (k := k)
local notation "topDeg" => cyclotomicCoverPolynomial_natDegree (k := k) Λ C
local notation "wt₀" => (blockWeight Wgt L 0 : I ⊕ Fin ℓ → ℤ)
set_option quotPrecheck false in
set_option hygiene false in
local notation "Fam" => cyclotomicFamily.{u, v, w} sym lead monic Wgt L topDeg deg
local notation "rt" => downRightWeight (coordinateDatum Λ C) (coordinateRedWeights Λ C) ν

/-- **A black strand of the cover kills objects supported on the empty block**: its functor
is cyclotomic induction or restriction in a colour with cyclotomic polynomial `1`. -/
theorem isZero_strandAt_inl (b : Bool) (j : I) (r : I ⊕ Fin ℓ → ℤ) {x y : I ⊕ Fin ℓ → ℤ}
    (hx : (⟨(b, .inl j), r⟩ : Col (I ⊕ Fin ℓ) (I ⊕ Fin ℓ → ℤ)).r = x)
    (hy : sh Wgt ((b, .inl j) : Letter (I ⊕ Fin ℓ)) + r = y)
    {V : weightSpace.{u, v, w} S p Wgt L x} (hV : ∀ β, β.1 ≠ 0 → IsZero (V β)) :
    IsZero (((Fam).model.strandAt ⟨(b, .inl j), r⟩ x y hx hy).obj.obj V) := by
  cases b
  · exact isZero_globalF_obj (Sum.inl j) _ hV
  · exact isZero_globalE_obj (Sum.inl j) rfl _ hV

omit [DecidableEq I] in
/-- The last letter of the reflection of a boundary starting with a black strand. -/
theorem getLast_coverObj_cons (s : Letter I) (rest : List (DoubleStrand I ℓ)) :
    (coverObj (Λ := Λ) (C := C)
      (obj (coordinateDatum Λ C) (redWeight Wgt) 0 (.inl s :: rest))).word.getLast?
      = some (⟨coverLetter (.inl s), wt₀ - 0⟩ : Col (I ⊕ Fin ℓ) (I ⊕ Fin ℓ → ℤ)) := by
  change (((colours (coordinateDatum Λ C) (redWeight Wgt) 0 (.inl s :: rest)).map
    (coverColour wt₀)).reverse).getLast? = _
  simp [colours, coverColour]

/-- **Violated boundaries evaluate to zero.** A boundary of the downward block whose leftmost
strand is black is reflected to a word whose first-applied functor is cyclotomic induction or
restriction in a black colour, which kills the vacuum supported on the empty block. -/
theorem downVacuumFunctor_id_eq_zero
    {P : Presentation.{v, v₁} (signature (coordinateDatum Λ C) (redWeight Wgt)) k}
    (hP : CoverRelsNegligible.{u, v, w} Λ C hQ hc wt₀ P) (hwf : P.WFDom)
    (x : DoubleDiagram.BoundaryCategory (k := k) (Λ := coordinateRedWeights Λ C) P rt)
    : x.val.IsViolated → 𝟙 ((downVacuumFunctor hc hP hwf).obj x) = 0 := by
  rintro ⟨s, hs⟩
  obtain ⟨rest, hrest⟩ : ∃ rest, x.val.word = .inl s :: rest := by
    cases h : x.val.word with
    | nil => rw [h] at hs; simp at hs
    | cons a rest => rw [h] at hs; simp at hs; exact ⟨rest, by rw [hs]⟩
  have hW := isZero_word_obj_of_getLast (Fam).model (coverVacuum.{u, v, w} Λ C hQ)
    (c := ⟨coverLetter (.inl s), wt₀ - 0⟩)
    (fun _ hx' hy' => isZero_strandAt_inl (hQ := hQ) (!s.1) s.2 _ hx' hy'
      (fun β hβ => isZero_emptyBlockObj hβ))
    (wt₀ - rt) _ (cond_downBoundary x).1 (cond_downBoundary x).2.1
    (by rw [hrest]; exact getLast_coverObj_cons s rest)
  rw [IsZero.iff_id_eq_zero] at hW
  change 𝟙 ((functor (RingHom.toNonUnitalRingHom (AlgHom.toRingHom
    (cyclotomicCoverToTensor (Q := Q) Λ ν C)))).obj _) = 0
  exact InductionAlong.functor_id_eq_zero (congrFun hW _)

/-- **The vacuum evaluation on the violating quotient** (Webster, arXiv:1309.3796v3, §4.6,
proof of Lemma 4.29): the vacuum evaluation of the downward block factors through the
quotient by the violated boundary identities. -/
def downVacuumQuotientFunctor
    {P : Presentation.{v, v₁} (signature (coordinateDatum Λ C) (redWeight Wgt)) k}
    (hP : CoverRelsNegligible.{u, v, w} Λ C hQ hc wt₀ P) (hwf : P.WFDom) :
    DoubleDiagram.ViolatingCategory (k := k) (Λ := coordinateRedWeights Λ C) P rt ⥤
      ModuleCat.{max u v w} (TensorProductAlgebra k Q Λ ν) :=
  letI : (downVacuumFunctor (ν := ν) hc hP hwf).Additive := ⟨fun {_ _} {f g} =>
    presentedVacuumEval_add hc (blockWeight_stendhalWeight Λ C ν) hP hwf _ _ f.hom g.hom⟩
  letI : (downVacuumFunctor (ν := ν) hc hP hwf).Linear k := ⟨fun {_ _} f r =>
    presentedVacuumEval_smul hc (blockWeight_stendhalWeight Λ C ν) hP hwf _ _ r f.hom⟩
  DoubleViolatingQuotient.lift k
    (DoubleDiagram.tripleObj (Λ := coordinateRedWeights Λ C) P (right := rt))
    (downVacuumFunctor (ν := ν) hc hP hwf)
    (downVacuumFunctor_id_eq_zero (ν := ν) hc hP hwf)

end Categorification.Stendhal

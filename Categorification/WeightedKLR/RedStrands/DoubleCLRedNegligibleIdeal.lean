/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLWhisker
import Categorification.WeightedKLR.RedStrands.DoubleCLCoordinate
import Categorification.WeightedKLR.RedStrands.DoubleCLNegligibleWords
import Categorification.TwoRep.AdmissibleClosure

/-!
# Red-negligibility of the cyclotomic evaluation on a tensor ideal

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29. A morphism of the
Cautis–Lauda presentation of the extended datum is *cover red-negligible* if
every admissible component of its Cautis–Lauda action on the cyclotomic weight
spaces is red-negligible (`CoverRedNegligible`). Reflected strands of double
diagrams are upward or black (`redAllowed_coverColour`), so this property is
closed under the operations generating a tensor ideal. Hence, if the reflected
image of every relation of a presentation of double diagrams is cover
red-negligible, so is the reflected image of every element of its tensor ideal
(`coverRedNegligible_of_mem_ideal`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory Bicategory QuantumGroup QuantumGroup.UDot StringDiagrams KLR TwoRep
  CyclotomicAction Diagrams.BicatInterp DoubleDiagram KL3.Diagram

universe u v w v₁

/-- A reflected strand is upward or black. -/
theorem redAllowed_coverColour {I : Type u} {ℓ : ℕ} {X : Type*} [AddCommGroup X] (o : X)
    (c : X × DoubleStrand I ℓ) :
    RedAllowed (Set.range (Sum.inr : Fin ℓ → I ⊕ Fin ℓ)) (coverColour o c) := by
  rcases c with ⟨x, s | r⟩
  · right
    rintro ⟨r, hr⟩
    cases hr
  · left
    rfl

variable {I : Type u} {k : Type v} [Field k] {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (C : CartanDatum I)
  [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k} (hQ : IsRouquierQ C Q)

local notation "D" => I ⊕ Fin ℓ
local notation "Wgt" => cyclotomicCoverWeightDatum Λ C
local notation "S" => cyclotomicCoverQ C Λ Q
local notation "hS" => isRouquierQ_cyclotomicCoverQ C Λ Q hQ
local notation "sym" => IsRouquierQ.klrSymm hS
local notation "lead" => IsRouquierQ.polyInY_leading hS
local notation "deg" => IsRouquierQ.polyInY_degree_pair hS Wgt
local notation "Sc" => cyclotomicScalars sym lead Wgt deg
local notation "hC" => extendedCartanDatum_dot_inl Λ C
local notation "L" => cyclotomicCoverHighest (I := I) (ℓ := ℓ)
local notation "p" => cyclotomicCoverPolynomial (I := I) (ℓ := ℓ) (k := k)
set_option quotPrecheck false in
set_option hygiene false in
local notation "Fam" => cyclotomicFamily.{u, v, w} sym lead
  (cyclotomicCoverPolynomial_monic (k := k)) Wgt L (cyclotomicCoverPolynomial_natDegree (k := k) Λ C) deg
local notation "PCL" => KL3.Diagram.CL.presCL Wgt k Sc

include hQ in
/-- The relations of the Cautis–Lauda presentation hold in the cyclotomic action. -/
theorem presCL_cover_rel (r : (PCL).Rel) {s t : D → ℤ} (ha : Cond s t ((PCL).dom r))
    (hb : Cond s t ((PCL).cod r)) :
    admissibleMap (RouqFamily.genImg Fam Sc) ha hb ((PCL).rel r) = 0 :=
  RouqFamily.presCL_rel Fam Sc
    (cyclotomicFamily_brundanUpKLR sym lead (cyclotomicCoverPolynomial_monic (k := k)) Wgt L
      (cyclotomicCoverPolynomial_natDegree (k := k) Λ C) deg fun i j h =>
        coeff_eq_zero_of_lt_of_hom _ (IsRouquierQ.homogeneous hS i j h))
    (cyclotomicFamily_mixedInversion Wgt L sym lead (cyclotomicCoverPolynomial_monic (k := k))
      (cyclotomicCoverPolynomial_natDegree (k := k) Λ C) deg) (fun _ => rfl)
    (kkScalars_s_eq_zero _ sym _ (IsRouquierQ.homogeneous hS)) r ha hb

omit [DecidableEq I] in
/-- The red dot sums are central in the cyclotomic KLR algebras of the extended datum. -/
abbrev CoverDotCentral (Q : I → I → MvPolynomial (Fin 2) k) : Prop :=
  ∀ δ c (z : CycKLR k (cyclotomicCoverQ C Λ Q) (cyclotomicCoverPolynomial (k := k)) δ),
    Commute z (cyclotomicColourDot (cyclotomicCoverQ C Λ Q)
      (cyclotomicCoverPolynomial (k := k)) δ c)

variable (hc : CoverDotCentral Λ C Q)

/-- Red-negligibility of a 2-morphism between functors into a cyclotomic weight space of the
extended datum, for the red colours. -/
def CoverRed {s t : D → ℤ}
    {F F' : (Fam).model.lift.obj (fo t) ⟶ (Fam).model.lift.obj (fo s)} (θ : F ⟶ F') : Prop :=
  RedNegligible.{u, v, w} (Z := (Fam).model.lift.obj (fo t)) (y := s) (F := F) (G := F')
    S p hc (Set.range Sum.inr) Wgt L θ

namespace CoverRed

variable {Λ C hQ hc} {s t : I ⊕ Fin ℓ → ℤ}

theorem zero {F F' : (Fam).model.lift.obj (fo t) ⟶ (Fam).model.lift.obj (fo s)} :
    CoverRed.{u, v, w} Λ C hQ hc (0 : F ⟶ F') :=
  RedNegligible.zero _ _

theorem add {F F' : (Fam).model.lift.obj (fo t) ⟶ (Fam).model.lift.obj (fo s)}
    {θ θ' : F ⟶ F'} (h : CoverRed.{u, v, w} Λ C hQ hc θ) (h' : CoverRed.{u, v, w} Λ C hQ hc θ') :
    CoverRed.{u, v, w} Λ C hQ hc (θ + θ') :=
  RedNegligible.add h h'

theorem smul {F F' : (Fam).model.lift.obj (fo t) ⟶ (Fam).model.lift.obj (fo s)} (r : k)
    {θ : F ⟶ F'} (h : CoverRed.{u, v, w} Λ C hQ hc θ) : CoverRed.{u, v, w} Λ C hQ hc (r • θ) :=
  RedNegligible.smul r h

theorem comp_left {F F' F'' : (Fam).model.lift.obj (fo t) ⟶ (Fam).model.lift.obj (fo s)}
    (η : F ⟶ F') {θ : F' ⟶ F''} (h : CoverRed.{u, v, w} Λ C hQ hc θ) : CoverRed.{u, v, w} Λ C hQ hc (η ≫ θ) :=
  RedNegligible.comp_left η h

theorem comp_right {F F' F'' : (Fam).model.lift.obj (fo t) ⟶ (Fam).model.lift.obj (fo s)}
    {θ : F ⟶ F'} (η : F' ⟶ F'') (h : CoverRed.{u, v, w} Λ C hQ hc θ) : CoverRed.{u, v, w} Λ C hQ hc (θ ≫ η) :=
  RedNegligible.comp_right η h

end CoverRed

/-- **Cover red-negligible morphisms.** Every admissible component of the
Cautis–Lauda action of the morphism on the cyclotomic weight spaces of the
extended datum is red-negligible. -/
def CoverRedNegligible {c d : Obj (psig Wgt)} (φ : (PCL).obj c ⟶ (PCL).obj d) : Prop :=
  AdmissibleHolds (RouqFamily.genImg Fam Sc) PCL (presCL_cover_rel Λ C hQ)
    Signature.IsEven.odd_eq_false (fun {_ _} {_ _} θ => CoverRed.{u, v, w} Λ C hQ hc θ) φ

namespace CoverRedNegligible

variable {Λ C hQ hc} {c d e : Obj (psig (cyclotomicCoverWeightDatum Λ C))}

theorem zero : CoverRedNegligible.{u, v, w} Λ C hQ hc (0 : (PCL).obj c ⟶ (PCL).obj d) :=
  AdmissibleHolds.zero (fun {_ _ _ _} => CoverRed.zero)

theorem add {f g : (PCL).obj c ⟶ (PCL).obj d} (hf : CoverRedNegligible.{u, v, w} Λ C hQ hc f)
    (hg : CoverRedNegligible.{u, v, w} Λ C hQ hc g) : CoverRedNegligible.{u, v, w} Λ C hQ hc (f + g) :=
  AdmissibleHolds.add (fun h h' => CoverRed.add h h') hf hg

theorem smul (r : k) {f : (PCL).obj c ⟶ (PCL).obj d} (hf : CoverRedNegligible.{u, v, w} Λ C hQ hc f) :
    CoverRedNegligible.{u, v, w} Λ C hQ hc (r • f) :=
  AdmissibleHolds.smul (fun r _ h => CoverRed.smul r h) r hf

theorem comp_left (g : (PCL).obj c ⟶ (PCL).obj d) {f : (PCL).obj d ⟶ (PCL).obj e}
    (hf : CoverRedNegligible.{u, v, w} Λ C hQ hc f) : CoverRedNegligible.{u, v, w} Λ C hQ hc (g ≫ f) :=
  AdmissibleHolds.comp_left (fun {_ _ _ _} => CoverRed.zero)
    (fun η _ h => CoverRed.comp_left η h) g hf

theorem comp_right {f : (PCL).obj c ⟶ (PCL).obj d} (g : (PCL).obj d ⟶ (PCL).obj e)
    (hf : CoverRedNegligible.{u, v, w} Λ C hQ hc f) : CoverRedNegligible.{u, v, w} Λ C hQ hc (f ≫ g) :=
  AdmissibleHolds.comp_right (fun {_ _ _ _} => CoverRed.zero)
    (fun η h => CoverRed.comp_right η h) g hf

/-- Whiskering by words of reflected strands preserves cover red-negligibility. -/
theorem whisk (o : D → ℤ) {f : (PCL).obj c ⟶ (PCL).obj d} (U : Obj (psig Wgt))
    (V : List (psig Wgt).Colour) (hf : CoverRedNegligible.{u, v, w} Λ C hQ hc f)
    (hU : ∀ x ∈ U.word, x ∈ Set.range (coverColour (I := I) (ℓ := ℓ) o))
    (hV : ∀ x ∈ V, x ∈ Set.range (coverColour (I := I) (ℓ := ℓ) o)) :
    CoverRedNegligible.{u, v, w} Λ C hQ hc ((PCL).whisk f U V) := by
  refine AdmissibleHolds.whisk (fun {_ _ _ _} => CoverRed.zero)
    (fun x : (psig Wgt).Colour => x ∈ Set.range (coverColour (I := I) (ℓ := ℓ) o))
    (fun η _ h => CoverRed.comp_left η h)
    (fun η h => CoverRed.comp_right η h) ?_ hf U V hU hV
  intro s t s' t' v hv hvt w' hw hws x y θ _ hw' hθ
  unfold CoverRed at hθ ⊢
  refine RedNegligible.whiskerLeft _ ?_
  exact RedNegligible.whiskerRight_word sym lead (cyclotomicCoverPolynomial_monic (k := k)) _ deg
    s' w' s hw hws (fun c hc' => by
      obtain ⟨c₀, rfl⟩ := hw' c hc'
      exact redAllowed_coverColour o c₀) hθ

end CoverRedNegligible

/-- **Red-negligibility on a tensor ideal.** If the reflected image of every relation of a
presentation `P` of double diagrams with well-formed domains is cover red-negligible, so is the
reflected image of every element of the tensor ideal of `P`. -/
theorem coverRedNegligible_of_mem_ideal (o : D → ℤ)
    (P : Presentation.{v, v₁} (signature (coordinateDatum Λ C) (redWeight Wgt)) k)
    (hwf : P.WFDom)
    (hrel : ∀ i, Nonempty (P.dom i ⟶ P.cod i) →
      CoverRedNegligible.{u, v, w} Λ C hQ hc (coverCL Λ C hQ o (P.rel i)))
    {a b : Obj (signature (coordinateDatum Λ C) (redWeight Wgt))} {f : LinDiagram k a b}
    (hf : f ∈ P.ideal a b) : CoverRedNegligible.{u, v, w} Λ C hQ hc (coverCL Λ C hQ o f) :=
  coverLin_mem_of_mem_ideal Wgt hC o PCL coverSign P hwf
    (fun φ => CoverRedNegligible.{u, v, w} Λ C hQ hc φ) CoverRedNegligible.zero.{u, v, w} CoverRedNegligible.add.{u, v, w}
    CoverRedNegligible.smul.{u, v, w} CoverRedNegligible.comp_left.{u, v, w}
    CoverRedNegligible.comp_right.{u, v, w}
    (fun U V hf hU hV => CoverRedNegligible.whisk.{u, v, w} o U V hf hU hV) hrel hf

end Categorification.Stendhal

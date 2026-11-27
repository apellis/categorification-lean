/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCapBubblePositionQ
import Categorification.WeightedKLR.RedStrands.DoubleCapCupPositionsQ
import Categorification.WeightedKLR.RedStrands.DoubleCapCrossPositionsQ
import Categorification.WeightedKLR.RedStrands.DoubleCapDotPositionsQ
import Categorification.WeightedKLR.RedStrands.DoubleDownSpanQuotient

/-!
# Surjectivity onto the all-down matrix corner

Webster, arXiv:1309.3796v2, §4.5, Lemma 4.28 (v3, §4.6, Lemma 4.29). Each signed diagram between
two all-down ordered loadings belongs to the span of ordinary diagrams in
the violating quotient. The crossing-count induction checks every placement
of a dot, cup or admissible crossing relative to the terminal cap. Entrywise
spanning gives surjectivity of the ordinary algebra homomorphism.
The cap presentation includes the reflected black relations of `U_Q(g)`, for arbitrary
Cautis–Lauda scalars; the pitchforks then hold up to units, which the spans absorb.

This is the version of `DoubleCapSurjectivity` in which the black strands carry the relations of
Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, Definition 1.1, `r = 1`; `CLQ.pres RD k sc`) instead
of the KL III relations. Each declaration carries the suffix `Q`.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.Stendhal.DoubleDiagram
open CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams KLR KLR.Diagram
universe u v w
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {ℓ : ℕ} {weights : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}}
  {k : Type w} [CommRing k] {sc : KL3.Diagram.CL.CLScalars C k} {ν : Multiset I}
local notation "lab" => (Subtype.val ∘ weights)
variable (P : Presentation.{w,max u v} (signature RD (Subtype.val ∘ weights)) k)
  (Q : I → I → MvPolynomial (Fin 2) k) (e : Fin ℓ → I →₀ ℕ) (t : I → I → k)
local notation "Ord" => {s : Seq (stendhalWeight ℓ ν) // IsRedOrdered s}
local notation "A" => signedCapKLPresentationQ RD lab sc P Q e t

/-- With reflected KL III black relations and coroot red exponents, ordinary
diagrams span between any two ordered all-down loadings. -/
theorem signedCapKL_downwardDiagramSpan_eq_topQ
    (hshift : ∀ r i, (e r i : ℤ) = RD.pair (RD.iY i) (weights r).val) (s z : Ord) :
    downwardDiagramSpan (A) s z = ⊤ := by
  apply downwardDiagramSpan_eq_top_of_terminalCaps
  apply pushesTerminalCaps_of_positions _ _ (cutHeight_down ..)
  · exact capSuccessor_allDotsQ RD lab sc P Q e t (signedDownEntry (A) s z)
  · exact capSuccessor_allCupsQ RD lab sc P Q e t (signedDownEntry (A) s z)
      (capSuccessor_downCupBothQ P Q e t hshift s z)
  · exact capSuccessor_allCrossingsQ RD lab sc P Q e t (signedDownEntry (A) s z)

/-- Surjectivity of the ordinary comparison for the signed cap presentation with
reflected KL III black relations,
with the exponent of each red strand equal to its coroot pairing. -/
theorem signedCapKL_ordinaryToDownwardMatrix_surjectiveQ
    (scalars : I → I → kˣ) (hshift : ∀ r i, (e r i : ℤ) = RD.pair (RD.iY i) (weights r).val) :
    Function.Surjective (ordinaryToDownwardMatrix (A) Q e scalars (ν := ν)) :=
  ordinaryToDownwardMatrix_surjective_of_base_span (A) Q e scalars
    (signedCapKL_downwardDiagramSpan_eq_topQ P Q e t hshift)

/-- With finitely many colours use the red weights themselves in both
presentations. The signed presentation uses reflected `U_Q(g)` black relations. -/
theorem signedCapKL_ordinaryToDownwardMatrix_ofWeights_surjectiveQ [Finite I] (scalars : I → I → kˣ) :
    let exponents := corootExponents (Λ := weights) (fun _ => Set.toFinite _)
    Function.Surjective (ordinaryToDownwardMatrix_ofWeights
      (signedCapKLPresentationQ RD lab sc P Q exponents (fun i j => (scalars i j : k))) Q scalars (ν := ν)) :=
  signedCapKL_ordinaryToDownwardMatrix_surjectiveQ P Q _ _ scalars (corootExponents_pair _)

end Categorification.Stendhal.DoubleDiagram

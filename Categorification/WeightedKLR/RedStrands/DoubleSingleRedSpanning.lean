/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleRedPrefixBlackSpanning
import Categorification.WeightedKLR.RedStrands.DoubleSingleRedReduction

/-!
# Downward spanning for one dominant red strand

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29, and Khovanov–Lauda
III, arXiv:0807.3250v1, Lemma 3.9. Every surviving diagram has its single
red strand first. Black straightening moves all bubble factors next to that
strand. At a dominant red weight the positive-degree generators of the
bubble algebra are real bubbles, and the red-prefix relation kills them.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe u v w
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
    (RD : WeightDatum C X Y) {k : Type w} [CommRing k]
    (weights : Fin 1 → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x})
    (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin 1 → I →₀ ℕ)
    (base : Presentation.{w, max u v} (signature RD (Subtype.val ∘ weights)) k)

local notation "labels" => (Subtype.val ∘ weights)
private abbrev firstRed : List (DoubleStrand I 1) := [.inr 0]
local notation "η" => endWeight RD labels 0 firstRed
local notation "K" => pres RD k

/-- A one-red presentation containing the reflected KL black relations
and the red slides used in Webster v3, Lemma 4.29. -/
abbrev singleRedSpanningPresentation :=
  redPrefixSpanningPresentation RD weights Q exponents base

local notation "B" => singleRedSpanningPresentation RD weights Q exponents base

private theorem singleRedKL_eqs (r : (K).Rel) :
    (B).lin (blackMirrorLinear RD labels ((K).rel r)) = 0 :=
  (B).lin_rel_self (.inl (.inl (.inl (.inl (.inr r)))))

variable {right : X}
local notation "redEnd" => (fun (s : List (Letter I)) => endWeight RD labels 0 (firstRed ++ blackWord s ++ []))
local notation "bd" => singleRedTriple (Λd := weights) RD
local notation "V" => violatingFunctor B right

/-- Reflection and projection of a presented black Hom with the single red on its left. -/
def singleRedKLHom (s t : List (Letter I)) (hs : redEnd s = right) (ht : redEnd t = right) :
    ((K).obj (ob RD η s) ⟶ (K).obj (ob RD η t)) →ₗ[k] ((V).obj (bd s hs) ⟶ (V).obj (bd t ht)) :=
  (singleRedProjection B s t hs ht).comp
    (blackPrefixHom RD labels 0 firstRed B (singleRedKL_eqs RD weights Q exponents base))

variable (he : ∀ i, (exponents 0 i : ℤ) = RD.pair (RD.iY i) (weights 0).val)

include he in
/-- Webster, arXiv:1309.3796v3, §4.6, Lemma 4.29, for the entries with
one dominant red and arbitrary all-down black words. Every morphism in
the violating quotient is a linear combination of downward diagrams. -/
theorem singleRed_span_downwardBlack (s t : List I)
    (hs : redEnd (dns s) = right) (ht : redEnd (dns t) = right)
    (f : (V).obj (bd (dns s) hs) ⟶ (V).obj (bd (dns t) ht)) :
    f ∈ Submodule.span k {g | ∃ (A : List (LayerData I)) (hA : SChain (dns s) A (dns t)),
      DownBlackLayers A ∧ g = singleRedBlackEntry B (dns s) (dns t) hs ht
        (LinDiagram.of (mkD RD η A hA))} := by
  obtain ⟨d, rfl⟩ := singleRedBlackEntry_surjective B (dns s) (dns t) hs ht f
  exact redPrefixBlackEntry_mem_span RD weights Q exponents base [0] [] rfl
    (fun r => Fin.fin_one_eq_zero r ▸ he) s t hs ht d

end Categorification.Stendhal.DoubleDiagram

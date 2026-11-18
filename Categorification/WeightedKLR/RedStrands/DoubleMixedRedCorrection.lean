/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleMixedRedReduction
import Categorification.WeightedKLR.RedStrands.DoubleCrossingCapInduction
import Categorification.WeightedKLR.RedStrands.DoubleRedBraidBubbles

/-!
# Crossing-free corrections to the mixed red braid

Webster, arXiv:1309.3796v2, Definition 4.5 (4.1a), Definition 4.24 and
Lemma 4.28. The divided-difference monomials have physical representatives
consisting of a single black cup, two blocks of downward dots, and a cap.
-/
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams KL3.Diagram KLR.Diagram

universe w u v
variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)
  (μ : X) (L : List (DoubleStrand I ℓ)) (r : Fin ℓ) (i : I) (R : List (DoubleStrand I ℓ))
  {k : Type w} [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)
  (exponents : Fin ℓ → I →₀ ℕ) (P : Presentation.{w,max u v} (signature RD Λ) k)

local notation "E" => (Sum.inl (true, i) : DoubleStrand I ℓ)
local notation "F" => (Sum.inl (false, i) : DoubleStrand I ℓ)
local notation "red" => (Sum.inr r : DoubleStrand I ℓ)
local notation "dᵢ" => (Sum.inl i : I ⊕ Fin ℓ)
local notation "rL" => (Sum.inr r : I ⊕ Fin ℓ)
local notation "O" => ob [dᵢ,rL,dᵢ]
local notation "P₀" => pres k (affineCoverQ Q exponents)
local notation "Pd" => addDownRelations RD Λ (affineCoverQ Q exponents) P
local notation "tr" => downPresentedFunctor RD Λ (affineCoverQ Q exponents) P μ (L ++ [E]) (E :: R)
local notation "mid" => ((L ++ [E]) ++ [F,red,F] ++ E :: R)

private def mateCupLayer : RedBraidMateSide → SignedLayer I ℓ
  | .left => (L ++ [E,F,red], .black (.cup (false,i)), R)
  | .right => (L, .black (.cup (true,i)), red :: F :: E :: R)

private def mateCapLayer : RedBraidMateSide → SignedLayer I ℓ
  | .left => (L, .black (.cap (false,i)), red :: F :: E :: R)
  | .right => (L ++ [E,F,red], .black (.cap (true,i)), R)

private theorem mateCupChain (s : RedBraidMateSide) :
    signedChain (L ++ s.bottom r i i ++ R) [mateCupLayer L r i R s] mid := by
  cases s <;> simp [RedBraidMateSide.bottom, mateCupLayer, signedChain, Move.bottom, Move.top, List.append_assoc]

private theorem mateCapChain (s : RedBraidMateSide) :
    signedChain mid [mateCapLayer L r i R s] (L ++ s.flip.bottom r i i ++ R) := by
  cases s <;> simp [RedBraidMateSide.flip, RedBraidMateSide.bottom, mateCapLayer, signedChain,
    Move.bottom, Move.top, List.append_assoc]

private theorem mate_linear_layers (s : RedBraidMateSide) (d : End ((P₀).obj O)) (ls : List (SignedLayer I ℓ))
    (hc : signedChain mid ls mid) (hd : (tr).map d = signedDg RD Λ (Pd) μ mid mid ls) :
    redEqualBraidMate RD Λ μ L r i R Q exponents P s d =
    signedDg RD Λ (Pd) μ (L ++ s.bottom r i i ++ R) (L ++ s.flip.bottom r i i ++ R)
      ([mateCupLayer L r i R s] ++ ls ++ [mateCapLayer L r i R s]) := by
  have hcup := mateCupChain L r i R s
  have hcap := mateCapChain L r i R s
  rw [← signedDg_comp RD Λ (Pd) μ (hcup.append hc) hcap,
    ← signedDg_comp RD Λ (Pd) μ hcup hc, ← hd, Category.assoc]
  cases s with
  | left =>
    rw [signedDg_eq_diag_of_layers RD Λ (Pd) μ hcup (redBraidMateCup RD Λ μ L r i i R .left) rfl,
      signedDg_eq_diag_of_layers RD Λ (Pd) μ hcap (redBraidMateCap RD Λ μ L r i i R .left) rfl]
    rfl
  | right =>
    rw [signedDg_eq_diag_of_layers RD Λ (Pd) μ hcup (redBraidMateCup RD Λ μ L r i i R .right) rfl,
      signedDg_eq_diag_of_layers RD Λ (Pd) μ hcap (redBraidMateCap RD Λ μ L r i i R .right) rfl]
    rfl

/-- The span of raw diagrams of crossing number zero. -/
def crossingFreeSpan (s z : List (DoubleStrand I ℓ)) :
    Submodule k (P.obj (obj RD Λ μ s) ⟶ P.obj (obj RD Λ μ z)) :=
  Submodule.span k {f | ∃ d : obj RD Λ μ s ⟶ obj RD Λ μ z, crossingNumber d = 0 ∧ f = P.diag d}

private theorem signedDg_mem_crossingFreeSpan {s z : List (DoubleStrand I ℓ)}
    (A : List (SignedLayer I ℓ)) (hc : signedChain s A z) (hz : ∀ x ∈ A, x.2.1.isCrossing = false) :
    signedDg RD Λ P μ s z A ∈ crossingFreeSpan RD Λ μ P s z := by
  rw [signedDg_of RD Λ P μ hc]
  apply Submodule.subset_span
  refine ⟨_, ?_, rfl⟩
  change (signedLayers RD Λ μ A).countP (fun l => l.gen.2.isCrossing) = 0
  rw [signedLayers, List.countP_map, List.countP_eq_zero]
  intro x hx
  change ¬ x.2.1.isCrossing = true
  simp [hz x hx]

/-- The actual layers of a monomial in the mated red braid correction. -/
def redBraidCorrectionLayers (s : RedBraidMateSide) (a b : ℕ) : List (SignedLayer I ℓ) :=
  [mateCupLayer L r i R s] ++ downRedBraidDotLayers L i r R a b ++ [mateCapLayer L r i R s]

/-- A mated divided-difference monomial is the stated cup, dots, and cap. -/
theorem redBraidMate_dotMonomial (s : RedBraidMateSide) (a b : ℕ) :
    redEqualBraidMate RD Λ μ L r i R Q exponents P s
      (End.of ((P₀).diag (E0 dᵢ rL dᵢ)) ^ a * End.of ((P₀).diag (E2 dᵢ rL dᵢ)) ^ b) =
    signedDg RD Λ (Pd) μ (L ++ s.bottom r i i ++ R) (L ++ s.flip.bottom r i i ++ R)
      (redBraidCorrectionLayers L r i R s a b) :=
  mate_linear_layers RD Λ μ L r i R Q exponents P s _ _
    (downRedBraidDotLayers_chain L i r R a b)
    (downRedBraidDotMonomial_layers RD Λ μ L i r R Q exponents P a b)

/-- Every layer in a dotted red-braid correction has zero crossings. -/
theorem redBraidCorrectionLayers_crossFree (s : RedBraidMateSide) (a b : ℕ) :
    ∀ x ∈ redBraidCorrectionLayers L r i R s a b, x.2.1.isCrossing = false := by
  intro x hx
  simp only [redBraidCorrectionLayers, downRedBraidDotLayers, List.mem_append, List.mem_singleton,
    List.mem_replicate] at hx
  rcases hx with (rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩) | rfl <;> cases s <;> rfl

variable (t : I → I → k)
local notation "Pm" => addRedUpRelations RD Λ k (addRedUpSlideRelations RD Λ
  (addRedCapRelations RD Λ (addRedCupRelations RD Λ P)))
local notation "Pf" => addBlackAdjunctionRelations RD Λ (addMixedCupPitchforkRelations RD Λ (Pm) t)
local notation "Pc" => addDownRelations RD Λ (affineCoverQ Q exponents) (Pf)

/-- Webster v2, Definitions 4.5 and 4.24, Lemma 4.28. In either middle-downward
order with equal black colours, the red mixed braid difference belongs to the
span of physical, well-formed diagrams with zero crossings. -/
theorem mixedRed_triplePoint_sub_mem_crossingFreeSpan (s : RedBraidMateSide) :
    mixedMiddleBraid RD Λ μ L r i i R Q exponents P t s false -
      mixedMiddleBraid RD Λ μ L r i i R Q exponents P t s true ∈
      crossingFreeSpan RD Λ μ (Pc) (L ++ s.bottom r i i ++ R) (L ++ s.flip.bottom r i i ++ R) := by
  rw [mixedRed_triplePoint_correction]
  apply Submodule.neg_mem
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro m _
  let b := exponents r i - 1 - m
  rw [redBraidMate_dotMonomial]
  exact signedDg_mem_crossingFreeSpan RD Λ μ (Pc) (redBraidCorrectionLayers L r i R s m b)
    (((mateCupChain L r i R s).append (downRedBraidDotLayers_chain L i r R m b)).append (mateCapChain L r i R s))
    (redBraidCorrectionLayers_crossFree L r i R s m b)

/-- The red mixed Reidemeister III substitution preserves the diagram modulo the
span of zero-crossing terms. This covers all six bottom orders and all pairs
of black colours, in any signed horizontal context. -/
theorem mixedRed_triplePoint_mod_crossingFree (j : I) (o : MixedRedOrder) :
    signedDg RD Λ (Pc) μ (L ++ o.word r i j ++ R) (L ++ (o.word r i j).reverse ++ R)
      (mixedRedTripleLayers L r i j R o false) -
      signedDg RD Λ (Pc) μ (L ++ o.word r i j ++ R) (L ++ (o.word r i j).reverse ++ R)
        (mixedRedTripleLayers L r i j R o true) ∈
      crossingFreeSpan RD Λ μ (Pc) (L ++ o.word r i j ++ R) (L ++ (o.word r i j).reverse ++ R) := by
  classical
  by_cases h : i = j
  · subst j
    cases o with
    | EFR => exact mixedRed_triplePoint_sub_mem_crossingFreeSpan RD Λ μ L r i R Q exponents P t .left
    | RFE => exact mixedRed_triplePoint_sub_mem_crossingFreeSpan RD Λ μ L r i R Q exponents P t .right
    | ERF | FRE | REF | FER =>
      rw [mixedRed_triplePoint_outer RD Λ μ L r i i R Q exponents P t _ rfl, sub_self]
      exact Submodule.zero_mem _
  · rw [mixedRed_triplePoint_ne RD Λ μ L r i j R Q exponents P t o h, sub_self]
    exact Submodule.zero_mem _

/-- Both expanded mixed braid words have exactly three physical crossings. -/
theorem mixedRedTripleLayers_crossingNumber (j : I) (o : MixedRedOrder) (right : Bool) :
    (signedLayers RD Λ μ (mixedRedTripleLayers L r i j R o right)).countP
      (fun l => l.gen.2.isCrossing) = 3 := by
  cases o <;> cases right <;> rfl

/-- Inserting a zero-crossing correction between a prefix and suffix lowers
the original three-crossing degree, also after any linear projection. -/
theorem crossingFreeSpan_in_fewerCrossings {s z : List (DoubleStrand I ℓ)}
    {a b c : Obj (signature RD Λ)} (pre : a ⟶ obj RD Λ μ s) (post : obj RD Λ μ z ⟶ b) (tail : b ⟶ c)
    {V : Type*} [AddCommGroup V] [Module k V] (π : (P.obj a ⟶ P.obj c) →ₗ[k] V)
    {f : P.obj (obj RD Λ μ s) ⟶ P.obj (obj RD Λ μ z)} (hf : f ∈ crossingFreeSpan RD Λ μ P s z) :
    π (P.diag pre ≫ f ≫ P.diag (post ≫ tail)) ∈
      fewerCrossings k (fun d => π (P.diag d)) tail (crossingNumber pre + 3 + crossingNumber post) := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨e, he, rfl⟩ := hg
    apply Submodule.subset_span
    refine ⟨(pre ≫ e) ≫ post, ?_, ?_⟩
    · simp [crossingNumber_comp, he]
    · simp [Presentation.diag_comp, Category.assoc]
  | zero => simp
  | add f g _ _ hf hg =>
    rw [Preadditive.add_comp, Preadditive.comp_add, map_add]
    exact Submodule.add_mem _ hf hg
  | smul a f _ hf =>
    rw [Linear.smul_comp, Linear.comp_smul, map_smul]
    exact Submodule.smul_mem _ a hf

end Categorification.Stendhal.DoubleDiagram

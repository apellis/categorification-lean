/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleDiagramRewriting
import Categorification.WeightedKLR.RedStrands.DoubleRedTriple
import Categorification.WeightedKLR.RedStrands.DoubleRedCup
import StringDiagrams.Transport

/-!
# Red triple points with oppositely directed black strands

Webster, arXiv:1309.3796v2, Definition 4.24, (4.4a–e) and the crossing
reduction in Lemma 4.28. Expand a sideways crossing into its defining
cup, upward black crossing, and cap. If the downward black strand starts
on the outside of the three strands, the two triple-point diagrams agree.
-/
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe w u v
variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)
  {k : Type w} [CommRing k] (P : Presentation.{w,max u v} (signature RD Λ) k)
  (μ : X) (L : List (DoubleStrand I ℓ)) (r : Fin ℓ) (i j : I) (R : List (DoubleStrand I ℓ))

local notation "T" => addRedUpRelations RD Λ k (addRedUpSlideRelations RD Λ
  (addRedCapRelations RD Λ (addRedCupRelations RD Λ P)))

private theorem signedEq {s t : List (DoubleStrand I ℓ)} {A B : List (SignedLayer I ℓ)}
    {a b : Obj (signature RD Λ)} (d e : a ⟶ b) (he : (T).diag d = (T).diag e)
    (hs : a = obj RD Λ μ s) (ht : b = obj RD Λ μ t)
    (hA : signedChain s A t) (hB : signedChain s B t)
    (h₁ : Diagram.layers d = signedLayers RD Λ μ A) (h₂ : Diagram.layers e = signedLayers RD Λ μ B) :
    signedDg RD Λ (T) μ s t A = signedDg RD Λ (T) μ s t B := by
  rw [signedDg_eq_diag_of_layers RD Λ (T) μ hA (Diagram.cast d hs ht) (by simpa using h₁),
    signedDg_eq_diag_of_layers RD Λ (T) μ hB (Diagram.cast e hs ht) (by simpa using h₂),
    ← Presentation.castHom_diag, ← Presentation.castHom_diag, he]

private theorem cupMate (l : Letter I) :
    signedDg RD Λ (T) μ (L ++ [.inr r] ++ R) (L ++ [.inl l, .inr r, .inl l.dual] ++ R)
      [(L, .black (.cup l), .inr r :: R), (L ++ [.inl l], .blackRed l.dual r, R)] =
    signedDg RD Λ (T) μ (L ++ [.inr r] ++ R) (L ++ [.inl l, .inr r, .inl l.dual] ++ R)
      [(L ++ [.inr r], .black (.cup l), R), (L, .redBlack r l, .inl l.dual :: R)] := by
  apply signedEq RD Λ P μ (redCupLeft RD Λ μ L l r R) (redCupRight RD Λ μ L l r R)
    ((T).diag_eq_of_rel (.inl (.inl (.inl (.inr ⟨μ, L, l, r, R⟩)))) rfl) rfl rfl
  all_goals first | rfl | simp [signedChain, Move.bottom, Move.top, List.append_assoc]

private theorem capMate (l : Letter I) :
    signedDg RD Λ (T) μ (L ++ [.inl l.dual, .inr r, .inl l] ++ R) (L ++ [.inr r] ++ R)
      [(L ++ [.inl l.dual], .redBlack r l, R), (L, .black (.cap l), .inr r :: R)] =
    signedDg RD Λ (T) μ (L ++ [.inl l.dual, .inr r, .inl l] ++ R) (L ++ [.inr r] ++ R)
      [(L, .blackRed l.dual r, .inl l :: R), (L ++ [.inr r], .black (.cap l), R)] := by
  apply signedEq RD Λ P μ (redCapLeft RD Λ μ L l r R) (redCapRight RD Λ μ L l r R)
    ((T).diag_eq_of_rel (.inl (.inl (.inr ⟨μ, L, l, r, R⟩))) rfl) rfl rfl
  all_goals first | rfl | simp [signedChain, Move.bottom, Move.top, List.append_assoc]

local notation "eᵢ" => (Sum.inl (true, i) : DoubleStrand I ℓ)
local notation "eⱼ" => (Sum.inl (true, j) : DoubleStrand I ℓ)
local notation "fⱼ" => (Sum.inl (false, j) : DoubleStrand I ℓ)
local notation "red" => (Sum.inr r : DoubleStrand I ℓ)

private theorem upRedLeft :
    signedDg RD Λ (T) μ (L ++ [red, eᵢ, eⱼ] ++ R) (L ++ [eⱼ, eᵢ, red] ++ R)
      [(L, .redBlack r (true, i), (eⱼ :: R)),
        ((L ++ [eᵢ]), .redBlack r (true, j), R),
        (L, .black (.cross true i j), (red :: R))] =
    signedDg RD Λ (T) μ (L ++ [red, eᵢ, eⱼ] ++ R) (L ++ [eⱼ, eᵢ, red] ++ R)
      [((L ++ [red]), .black (.cross true i j), R),
        (L, .redBlack r (true, j), (eᵢ :: R)),
        ((L ++ [eⱼ]), .redBlack r (true, i), R)] := by
  have h : (T).diag (redUpSlide RD Λ μ L r (.cross i j) R false) =
      (T).diag (redUpSlide RD Λ μ L r (.cross i j) R true) :=
    (T).diag_eq_of_rel (.inl (.inr ⟨μ, L, r, .cross i j, R, false⟩)) rfl
  apply signedEq RD Λ P μ (redUpSlide RD Λ μ L r (.cross i j) R true)
    (redUpSlide RD Λ μ L r (.cross i j) R false) h.symm
  all_goals first | rfl | simp [signedChain, Move.bottom, Move.top, List.append_assoc, upBlackWord,
    signedLayers, redUpSlide, redThroughUpWord, upBlackMoveDiagram, UpBlackMove.shape, moveDiagram]

private theorem upRedMiddle :
    signedDg RD Λ (T) μ (L ++ [eᵢ, red, eⱼ] ++ R) (L ++ [eⱼ, red, eᵢ] ++ R)
      [(L, .blackRed (true, i) r, (eⱼ :: R)),
        ((L ++ [red]), .black (.cross true i j), R),
        (L, .redBlack r (true, j), (eᵢ :: R))] =
    signedDg RD Λ (T) μ (L ++ [eᵢ, red, eⱼ] ++ R) (L ++ [eⱼ, red, eᵢ] ++ R)
      [((L ++ [eᵢ]), .redBlack r (true, j), R),
        (L, .black (.cross true i j), (red :: R)),
        ((L ++ [eⱼ]), .blackRed (true, i) r, R)] := by
  apply signedEq RD Λ P μ (middleRedViaLeft RD Λ μ L R r i j) (middleRedViaRight RD Λ μ L R r i j)
    (middleRed_triplePoint RD Λ μ L R r i j (addRedCapRelations RD Λ (addRedCupRelations RD Λ P))) rfl rfl
  all_goals first | rfl | simp [signedChain, Move.bottom, Move.top, List.append_assoc,
    signedLayers, layers_middleRedViaLeft, layers_middleRedViaRight]

private theorem upRedRight :
    signedDg RD Λ (T) μ (L ++ [eᵢ, eⱼ, red] ++ R) (L ++ [red, eⱼ, eᵢ] ++ R)
      [(L, .black (.cross true i j), (red :: R)),
        ((L ++ [eⱼ]), .blackRed (true, i) r, R),
        (L, .blackRed (true, j) r, (eᵢ :: R))] =
    signedDg RD Λ (T) μ (L ++ [eᵢ, eⱼ, red] ++ R) (L ++ [red, eⱼ, eᵢ] ++ R)
      [((L ++ [eᵢ]), .blackRed (true, j) r, R),
        (L, .blackRed (true, i) r, (eⱼ :: R)),
        ((L ++ [red]), .black (.cross true i j), R)] := by
  have h : (T).diag (redUpSlideMirror RD Λ μ L r (.cross i j) R false) =
      (T).diag (redUpSlideMirror RD Λ μ L r (.cross i j) R true) :=
    (T).diag_eq_of_rel (.inl (.inr ⟨μ, L, r, .cross i j, R, true⟩)) rfl
  apply signedEq RD Λ P μ (redUpSlideMirror RD Λ μ L r (.cross i j) R false)
    (redUpSlideMirror RD Λ μ L r (.cross i j) R true) h
  all_goals first | rfl | simp [signedChain, Move.bottom, Move.top, List.append_assoc, upBlackWord,
    signedLayers, redUpSlideMirror, upWordThroughRed, upBlackMoveDiagram, UpBlackMove.shape, moveDiagram]

/-- Relative order of a red, an upward black i, and a downward black j. -/
inductive MixedRedOrder
  | EFR | ERF | FER | FRE | REF | RFE

/-- The left-to-right boundary of the mixed triple. -/
def MixedRedOrder.word : MixedRedOrder → List (DoubleStrand I ℓ)
  | .EFR => [eᵢ, fⱼ, red]
  | .ERF => [eᵢ, red, fⱼ]
  | .FER => [fⱼ, eᵢ, red]
  | .FRE => [fⱼ, red, eᵢ]
  | .REF => [red, eᵢ, fⱼ]
  | .RFE => [red, fⱼ, eᵢ]

/-- The starting order of the mixed black crossing. -/
inductive MixedBlackOrder | EF | FE

/-- Read the sideways crossing as the mate of an upward crossing. -/
def upwardMateLayers : MixedBlackOrder → List (SignedLayer I ℓ)
  | .EF => [(L, .black (.cup (false, j)), eᵢ :: fⱼ :: R),
      (L ++ [fⱼ], .black (.cross true j i), fⱼ :: R),
      (L ++ [fⱼ, eᵢ], .black (.cap (false, j)), R)]
  | .FE => [(L ++ [fⱼ, eᵢ], .black (.cup (true, j)), R),
      (L ++ [fⱼ], .black (.cross true i j), fⱼ :: R),
      (L, .black (.cap (true, j)), eᵢ :: fⱼ :: R)]

private inductive MixedRedPair
  | EF | FE | ER | RE | FR | RF

private def MixedRedPair.rows (p : List (DoubleStrand I ℓ)) (q : List (DoubleStrand I ℓ)) :
    MixedRedPair → List (SignedLayer I ℓ)
  | .EF => upwardMateLayers p i j q .EF
  | .FE => upwardMateLayers p i j q .FE
  | .ER => [(p, .blackRed (true, i) r, q)]
  | .RE => [(p, .redBlack r (true, i), q)]
  | .FR => [(p, .blackRed (false, j) r, q)]
  | .RF => [(p, .redBlack r (false, j), q)]

private def mixedRows (a b c : DoubleStrand I ℓ) (ab ac bc : MixedRedPair) (right : Bool) :
    List (SignedLayer I ℓ) :=
  if right then
    bc.rows r i j (L ++ [a]) R ++ ac.rows r i j L (b :: R) ++ ab.rows r i j (L ++ [c]) R
  else
    ab.rows r i j L (c :: R) ++ ac.rows r i j (L ++ [b]) R ++ bc.rows r i j L (a :: R)

/-- Layers of either braid word on this ordered boundary, counting the sideways
black crossing as its cup, its upward crossing, and its cap. -/
def mixedRedTripleLayers (o : MixedRedOrder) (right : Bool) : List (SignedLayer I ℓ) :=
  match o with
  | .EFR => mixedRows L r i j R eᵢ fⱼ red .EF .ER .FR right
  | .ERF => mixedRows L r i j R eᵢ red fⱼ .ER .EF .RF right
  | .FER => mixedRows L r i j R fⱼ eᵢ red .FE .FR .ER right
  | .FRE => mixedRows L r i j R fⱼ red eᵢ .FR .FE .RE right
  | .REF => mixedRows L r i j R red eᵢ fⱼ .RE .RF .EF right
  | .RFE => mixedRows L r i j R red fⱼ eᵢ .RF .RE .FE right

/-- Whether the downward black strand is at an outside endpoint of the braid. -/
def MixedRedOrder.downOutside : MixedRedOrder → Bool
  | .EFR | .RFE => false
  | _ => true

private theorem switchERF :
    signedDg RD Λ (T) μ (L ++ [eᵢ, red, fⱼ] ++ R) (L ++ [fⱼ, red, eᵢ] ++ R) (mixedRedTripleLayers L r i j R .ERF false) =
    signedDg RD Λ (T) μ (L ++ [eᵢ, red, fⱼ] ++ R) (L ++ [fⱼ, red, eᵢ] ++ R) (mixedRedTripleLayers L r i j R .ERF true) := by
  simp only [mixedRedTripleLayers, mixedRows, MixedRedPair.rows, upwardMateLayers, Bool.false_eq_true, ite_false, ite_true,
    List.cons_append, List.nil_append, List.append_assoc]
  signed_step 3 with ((signedDg_swap RD Λ (T) μ L [eᵢ] R (.redBlack r (false, j)) (.black (.cap (false, j))) rfl rfl).symm)
  signed_step 2 with ((signedDg_swap RD Λ (T) μ L [] (fⱼ :: R) (.redBlack r (false, j)) (.black (.cross true j i)) rfl rfl).symm)
  signed_step 1 with ((cupMate RD Λ P μ L r (eᵢ :: fⱼ :: R) (false, j)).symm)
  signed_step 0 with ((signedDg_swap RD Λ (T) μ L [] (fⱼ :: R) (.black (.cup (false, j))) (.blackRed (true, i) r) rfl rfl).symm)
  signed_step 1 with ((upRedRight RD Λ P μ (L ++ [fⱼ]) r j i (fⱼ :: R)).symm)
  signed_step 3 with (signedDg_swap RD Λ (T) μ (L ++ [fⱼ]) [] R (.blackRed (true, i) r) (.black (.cap (false, j))) rfl rfl)
  signed_step 2 with ((capMate RD Λ P μ (L ++ [fⱼ, eᵢ]) r R (false, j)).symm)
  signed_step 1 with (signedDg_swap RD Λ (T) μ (L ++ [fⱼ]) [] R (.black (.cross true j i)) (.redBlack r (false, j)) rfl rfl)
  signed_step 0 with (signedDg_swap RD Λ (T) μ L [eᵢ] R (.black (.cup (false, j))) (.redBlack r (false, j)) rfl rfl)
  rfl

private theorem switchFER :
    signedDg RD Λ (T) μ (L ++ [fⱼ, eᵢ, red] ++ R) (L ++ [red, eᵢ, fⱼ] ++ R) (mixedRedTripleLayers L r i j R .FER false) =
    signedDg RD Λ (T) μ (L ++ [fⱼ, eᵢ, red] ++ R) (L ++ [red, eᵢ, fⱼ] ++ R) (mixedRedTripleLayers L r i j R .FER true) := by
  simp only [mixedRedTripleLayers, mixedRows, MixedRedPair.rows, upwardMateLayers, Bool.false_eq_true, ite_false, ite_true,
    List.cons_append, List.nil_append, List.append_assoc]
  signed_step 2 with (signedDg_swap RD Λ (T) μ L [eᵢ] R (.black (.cap (true, j))) (.blackRed (false, j) r) rfl rfl)
  signed_step 1 with (signedDg_swap RD Λ (T) μ (L ++ [fⱼ]) [] R (.black (.cross true i j)) (.blackRed (false, j) r) rfl rfl)
  signed_step 0 with (cupMate RD Λ P μ (L ++ [fⱼ, eᵢ]) r R (true, j))
  signed_step 3 with (signedDg_swap RD Λ (T) μ L [] (fⱼ :: R) (.black (.cap (true, j))) (.blackRed (true, i) r) rfl rfl)
  signed_step 1 with ((upRedMiddle RD Λ P μ (L ++ [fⱼ]) r i j (fⱼ :: R)).symm)
  signed_step 0 with ((signedDg_swap RD Λ (T) μ (L ++ [fⱼ]) [] R (.blackRed (true, i) r) (.black (.cup (true, j))) rfl rfl).symm)
  signed_step 3 with (capMate RD Λ P μ L r (eᵢ :: fⱼ :: R) (true, j))
  signed_step 2 with ((signedDg_swap RD Λ (T) μ L [] (fⱼ :: R) (.blackRed (false, j) r) (.black (.cross true i j)) rfl rfl).symm)
  signed_step 1 with ((signedDg_swap RD Λ (T) μ L [eᵢ] R (.blackRed (false, j) r) (.black (.cup (true, j))) rfl rfl).symm)
  rfl

private theorem switchFRE :
    signedDg RD Λ (T) μ (L ++ [fⱼ, red, eᵢ] ++ R) (L ++ [eᵢ, red, fⱼ] ++ R) (mixedRedTripleLayers L r i j R .FRE false) =
    signedDg RD Λ (T) μ (L ++ [fⱼ, red, eᵢ] ++ R) (L ++ [eᵢ, red, fⱼ] ++ R) (mixedRedTripleLayers L r i j R .FRE true) := by
  simp only [mixedRedTripleLayers, mixedRows, MixedRedPair.rows, upwardMateLayers, Bool.false_eq_true, ite_false, ite_true,
    List.cons_append, List.nil_append, List.append_assoc]
  signed_step 0 with (signedDg_swap RD Λ (T) μ L [eᵢ] R (.blackRed (false, j) r) (.black (.cup (true, j))) rfl rfl)
  signed_step 1 with (signedDg_swap RD Λ (T) μ L [] (fⱼ :: R) (.blackRed (false, j) r) (.black (.cross true i j)) rfl rfl)
  signed_step 2 with ((capMate RD Λ P μ L r (eᵢ :: fⱼ :: R) (true, j)).symm)
  signed_step 3 with (signedDg_swap RD Λ (T) μ L [] (fⱼ :: R) (.black (.cap (true, j))) (.redBlack r (true, i)) rfl rfl)
  signed_step 1 with ((upRedLeft RD Λ P μ (L ++ [fⱼ]) r i j (fⱼ :: R)).symm)
  signed_step 0 with ((signedDg_swap RD Λ (T) μ (L ++ [fⱼ]) [] R (.redBlack r (true, i)) (.black (.cup (true, j))) rfl rfl).symm)
  signed_step 1 with ((cupMate RD Λ P μ (L ++ [fⱼ, eᵢ]) r R (true, j)).symm)
  signed_step 2 with ((signedDg_swap RD Λ (T) μ (L ++ [fⱼ]) [] R (.black (.cross true i j)) (.blackRed (false, j) r) rfl rfl).symm)
  signed_step 3 with ((signedDg_swap RD Λ (T) μ L [eᵢ] R (.black (.cap (true, j))) (.blackRed (false, j) r) rfl rfl).symm)
  rfl

private theorem switchREF :
    signedDg RD Λ (T) μ (L ++ [red, eᵢ, fⱼ] ++ R) (L ++ [fⱼ, eᵢ, red] ++ R) (mixedRedTripleLayers L r i j R .REF false) =
    signedDg RD Λ (T) μ (L ++ [red, eᵢ, fⱼ] ++ R) (L ++ [fⱼ, eᵢ, red] ++ R) (mixedRedTripleLayers L r i j R .REF true) := by
  simp only [mixedRedTripleLayers, mixedRows, MixedRedPair.rows, upwardMateLayers, Bool.false_eq_true, ite_false, ite_true,
    List.cons_append, List.nil_append, List.append_assoc]
  signed_step 1 with ((signedDg_swap RD Λ (T) μ L [eᵢ] R (.black (.cup (false, j))) (.redBlack r (false, j)) rfl rfl).symm)
  signed_step 0 with ((signedDg_swap RD Λ (T) μ L [] (fⱼ :: R) (.black (.cup (false, j))) (.redBlack r (true, i)) rfl rfl).symm)
  signed_step 2 with ((signedDg_swap RD Λ (T) μ (L ++ [fⱼ]) [] R (.black (.cross true j i)) (.redBlack r (false, j)) rfl rfl).symm)
  signed_step 3 with (capMate RD Λ P μ (L ++ [fⱼ, eᵢ]) r R (false, j))
  signed_step 1 with ((upRedMiddle RD Λ P μ (L ++ [fⱼ]) r j i (fⱼ :: R)).symm)
  signed_step 0 with (cupMate RD Λ P μ L r (eᵢ :: fⱼ :: R) (false, j))
  signed_step 1 with (signedDg_swap RD Λ (T) μ L [] (fⱼ :: R) (.redBlack r (false, j)) (.black (.cross true j i)) rfl rfl)
  signed_step 3 with (signedDg_swap RD Λ (T) μ (L ++ [fⱼ]) [] R (.redBlack r (true, i)) (.black (.cap (false, j))) rfl rfl)
  signed_step 2 with (signedDg_swap RD Λ (T) μ L [eᵢ] R (.redBlack r (false, j)) (.black (.cap (false, j))) rfl rfl)
  rfl

/-- Webster, arXiv:1309.3796v2, §4.5, Definition 4.24 and Lemma 4.28.
When Fⱼ is an outer strand, the red mixed triple point follows from the
upward triple point by taking a black mate. This holds also for i=j. -/
theorem mixedRed_triplePoint_of_downOutside (o : MixedRedOrder) (ho : o.downOutside) :
    signedDg RD Λ (T) μ (L ++ o.word r i j ++ R) (L ++ (o.word r i j).reverse ++ R)
      (mixedRedTripleLayers L r i j R o false) =
    signedDg RD Λ (T) μ (L ++ o.word r i j ++ R) (L ++ (o.word r i j).reverse ++ R)
      (mixedRedTripleLayers L r i j R o true) := by
  cases o with
  | EFR | RFE => contradiction
  | ERF => exact switchERF RD Λ P μ L r i j R
  | FER => exact switchFER RD Λ P μ L r i j R
  | FRE => exact switchFRE RD Λ P μ L r i j R
  | REF => exact switchREF RD Λ P μ L r i j R

end Categorification.Stendhal.DoubleDiagram

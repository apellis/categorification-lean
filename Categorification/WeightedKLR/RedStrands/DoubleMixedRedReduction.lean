/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleRedBraidMateLayers
import Categorification.WeightedKLR.RedStrands.DoubleMixedRedPitchfork
import Categorification.WeightedKLR.RedStrands.DoubleMixedRedTriple

/-!
# Mixed red triple points with the downward black strand in the middle

Webster, arXiv:1309.3796v2, Definitions 4.5 and 4.24, Lemma 4.28. Bend the ordinary
downward red braid and apply the black cup pitchfork with its scalar. The two
mixed triples differ by a sum of crossing-free diagrams for equal black colours.
-/
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams KLR.Diagram KL3.Diagram

universe w u v
variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)
  (μ : X) (L : List (DoubleStrand I ℓ)) (r : Fin ℓ) (i j : I) (R : List (DoubleStrand I ℓ))
  {k : Type w} [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)
  (exponents : Fin ℓ → I →₀ ℕ) (P : Presentation.{w,max u v} (signature RD Λ) k) (t : I → I → k)

local notation "eᵢ" => (Sum.inl (true, i) : DoubleStrand I ℓ)
local notation "fⱼ" => (Sum.inl (false, j) : DoubleStrand I ℓ)
local notation "fᵢ" => (Sum.inl (false, i) : DoubleStrand I ℓ)
local notation "red" => (Sum.inr r : DoubleStrand I ℓ)
local notation "dᵢ" => (Sum.inl i : I ⊕ Fin ℓ)
local notation "dⱼ" => (Sum.inl j : I ⊕ Fin ℓ)
local notation "rL" => (Sum.inr r : I ⊕ Fin ℓ)
local notation "P₀" => pres k (affineCoverQ Q exponents)
local notation "Pm" => addRedUpRelations RD Λ k (addRedUpSlideRelations RD Λ
  (addRedCapRelations RD Λ (addRedCupRelations RD Λ P)))
local notation "Pf" => addBlackAdjunctionRelations RD Λ (addMixedCupPitchforkRelations RD Λ (Pm) t)
local notation "Pd" => addDownRelations RD Λ (affineCoverQ Q exponents) (Pf)

private def signedLin {s z : List (DoubleStrand I ℓ)} (A : List (SignedLayer I ℓ)) :
    LinDiagram k (obj RD Λ μ s) (obj RD Λ μ z) := by
  classical
  exact if h : signedChain s A z then LinDiagram.of (Diagram.mk _ (chain_signedLayers RD Λ μ h)) else 0

private theorem lin_signedLin {s z : List (DoubleStrand I ℓ)} (A : List (SignedLayer I ℓ)) :
    P.lin (signedLin RD Λ μ (s := s) (z := z) A) = signedDg RD Λ P μ s z A := by
  classical
  by_cases h : signedChain s A z <;> simp [signedLin, signedDg, h]

private theorem liftHalfMate {s z : List (DoubleStrand I ℓ)} {A B : List (SignedLayer I ℓ)} {c : k}
    (h : signedDg RD Λ (Pf) μ s z A = c • signedDg RD Λ (Pf) μ s z B) :
    signedDg RD Λ (Pd) μ s z A = c • signedDg RD Λ (Pd) μ s z B := by
  simp only [← lin_signedLin, ← Presentation.lin_smul] at h ⊢
  exact lin_eq_addRels (Pf) h

private theorem frame {s a b z : List (DoubleStrand I ℓ)} {A B : List (SignedLayer I ℓ)} {c : k}
    (pre post : List (SignedLayer I ℓ))
    (h : signedDg RD Λ (Pd) μ a b A = c • signedDg RD Λ (Pd) μ a b B)
    (hp : signedChain s pre a) (hA : signedChain a A b) (hB : signedChain a B b)
    (hq : signedChain b post z) :
    signedDg RD Λ (Pd) μ s z (pre ++ A ++ post) = c • signedDg RD Λ (Pd) μ s z (pre ++ B ++ post) := by
  rw [← signedDg_comp RD Λ (Pd) μ (hp.append hA) hq,
    ← signedDg_comp RD Λ (Pd) μ (hp.append hB) hq,
    ← signedDg_comp RD Λ (Pd) μ hp hA, ← signedDg_comp RD Λ (Pd) μ hp hB, h,
    Linear.comp_smul, Linear.smul_comp]

private theorem cupMate (μ : X) (p q : List (DoubleStrand I ℓ))
    (l : KL3.Diagram.Letter I) (r : Fin ℓ) :
    signedDg RD Λ (Pd) μ (p ++ [.inr r] ++ q) (p ++ [.inl l, .inr r, .inl l.dual] ++ q)
      [(p, .black (.cup l), .inr r :: q), (p ++ [.inl l], .blackRed l.dual r, q)] =
    signedDg RD Λ (Pd) μ (p ++ [.inr r] ++ q) (p ++ [.inl l, .inr r, .inl l.dual] ++ q)
      [(p ++ [.inr r], .black (.cup l), q), (p, .redBlack r l, .inl l.dual :: q)] := by
  rw [signedDg_eq_diag_of_layers RD Λ (Pd) μ
    (by simp [signedChain, Move.bottom, Move.top, List.append_assoc]) (redCupLeft RD Λ μ p l r q) rfl,
    signedDg_eq_diag_of_layers RD Λ (Pd) μ
    (by simp [signedChain, Move.bottom, Move.top, List.append_assoc]) (redCupRight RD Λ μ p l r q) rfl]
  exact (Pd).diag_eq_of_rel (.inl (.inl (.inl (.inl (.inl (.inl (.inr ⟨μ, p, l, r, q⟩))))))) rfl

private theorem capMate (μ : X) (p q : List (DoubleStrand I ℓ))
    (l : KL3.Diagram.Letter I) (r : Fin ℓ) :
    signedDg RD Λ (Pd) μ (p ++ [.inl l.dual, .inr r, .inl l] ++ q) (p ++ [.inr r] ++ q)
      [(p ++ [.inl l.dual], .redBlack r l, q), (p, .black (.cap l), .inr r :: q)] =
    signedDg RD Λ (Pd) μ (p ++ [.inl l.dual, .inr r, .inl l] ++ q) (p ++ [.inr r] ++ q)
      [(p, .blackRed l.dual r, .inl l :: q), (p ++ [.inr r], .black (.cap l), q)] := by
  rw [signedDg_eq_diag_of_layers RD Λ (Pd) μ
    (by simp [signedChain, Move.bottom, Move.top, List.append_assoc]) (redCapLeft RD Λ μ p l r q) rfl,
    signedDg_eq_diag_of_layers RD Λ (Pd) μ
    (by simp [signedChain, Move.bottom, Move.top, List.append_assoc]) (redCapRight RD Λ μ p l r q) rfl]
  exact (Pd).diag_eq_of_rel (.inl (.inl (.inl (.inl (.inl (.inr ⟨μ, p, l, r, q⟩)))))) rfl

private theorem mixed_left_braidR :
    signedDg RD Λ (Pd) μ (L ++ [eᵢ, fⱼ, red] ++ R) (L ++ [red, fⱼ, eᵢ] ++ R) (mixedRedTripleLayers L r i j R .EFR false) =
      t j i • redBraidMate RD Λ μ L r i j R Q exponents (Pf) .left ((P₀).diag (braidR dⱼ rL dᵢ)) := by
  rw [redBraidMate_left_braidR]
  let A := upwardMateLayers L i j (red :: R) .EF
  let pre : List (SignedLayer I ℓ) := []
  let post : List (SignedLayer I ℓ) := [((L ++ [fⱼ]), (.blackRed (true, i) r), R),
      (L, (.blackRed (false, j) r), (eᵢ :: R))]
  change signedDg RD Λ (Pd) μ _ _ (pre ++ A ++ post) = _
  refine (frame RD Λ μ Q exponents P t (s := (L ++ [eᵢ, fⱼ, red] ++ R)) (z := (L ++ [red, fⱼ, eᵢ] ++ R)) pre post
    (liftHalfMate RD Λ μ Q exponents P t (mixedBlack_halfMate_EF RD Λ (Pm) μ L i j (red :: R) t))
    (by simp [pre, signedChain, List.append_assoc])
    (by simp [upwardMateLayers, signedChain, Move.bottom, Move.top, List.append_assoc])
    (by simp [downwardMateLayers, signedChain, Move.bottom, Move.top, List.append_assoc])
    (by simp [post, signedChain, Move.bottom, Move.top, List.append_assoc])).trans ?_
  apply congrArg (t j i • ·)
  dsimp only [pre, post, downwardMateLayers, List.cons_append, List.nil_append, List.append_assoc]
  signed_step 2 with (signedDg_swap RD Λ (Pd) μ L [fⱼ] R (.black (.cap (false, i))) (.blackRed (true, i) r) rfl rfl)
  signed_step 1 with (signedDg_swap RD Λ (Pd) μ (L ++ [eᵢ]) [] R (.black (.cross false j i)) (.blackRed (true, i) r) rfl rfl)
  signed_step 0 with (cupMate RD Λ Q exponents P t μ (L ++ [eᵢ, fⱼ]) R (false, i) r)
  signed_step 3 with (signedDg_swap RD Λ (Pd) μ L [] (eᵢ :: R) (.black (.cap (false, i))) (.blackRed (false, j) r) rfl rfl)
  rfl

private theorem mixed_left_braidL :
    signedDg RD Λ (Pd) μ (L ++ [eᵢ, fⱼ, red] ++ R) (L ++ [red, fⱼ, eᵢ] ++ R) (mixedRedTripleLayers L r i j R .EFR true) =
      t j i • redBraidMate RD Λ μ L r i j R Q exponents (Pf) .left ((P₀).diag (braidL dⱼ rL dᵢ)) := by
  rw [redBraidMate_left_braidL]
  let A := upwardMateLayers (L ++ [red]) i j R .EF
  let pre : List (SignedLayer I ℓ) := [((L ++ [eᵢ]), (.blackRed (false, j) r), R),
      (L, (.blackRed (true, i) r), (fⱼ :: R))]
  let post : List (SignedLayer I ℓ) := []
  change signedDg RD Λ (Pd) μ _ _ (pre ++ A ++ post) = _
  refine (frame RD Λ μ Q exponents P t (s := (L ++ [eᵢ, fⱼ, red] ++ R)) (z := (L ++ [red, fⱼ, eᵢ] ++ R)) pre post
    (liftHalfMate RD Λ μ Q exponents P t (mixedBlack_halfMate_EF RD Λ (Pm) μ (L ++ [red]) i j R t))
    (by simp [pre, signedChain, Move.bottom, Move.top, List.append_assoc])
    (by simp [upwardMateLayers, signedChain, Move.bottom, Move.top, List.append_assoc])
    (by simp [downwardMateLayers, signedChain, Move.bottom, Move.top, List.append_assoc])
    (by simp [post, signedChain, List.append_assoc])).trans ?_
  apply congrArg (t j i • ·)
  dsimp only [pre, post, downwardMateLayers, List.cons_append, List.nil_append, List.append_assoc]
  signed_step 1 with (signedDg_swap RD Λ (Pd) μ L [fⱼ] R (.blackRed (true, i) r) (.black (.cup (false, i))) rfl rfl)
  signed_step 2 with (signedDg_swap RD Λ (Pd) μ L [] (eᵢ :: R) (.blackRed (true, i) r) (.black (.cross false j i)) rfl rfl)
  signed_step 3 with ((capMate RD Λ Q exponents P t μ L (fⱼ :: eᵢ :: R) (false, i) r).symm)
  signed_step 0 with (signedDg_swap RD Λ (Pd) μ (L ++ [eᵢ]) [] R (.blackRed (false, j) r) (.black (.cup (false, i))) rfl rfl)
  rfl

private theorem mixed_right_braidR :
    signedDg RD Λ (Pd) μ (L ++ [red, fⱼ, eᵢ] ++ R) (L ++ [eᵢ, fⱼ, red] ++ R) (mixedRedTripleLayers L r i j R .RFE false) =
      t j i • redBraidMate RD Λ μ L r i j R Q exponents (Pf) .right ((P₀).diag (braidR dᵢ rL dⱼ)) := by
  rw [redBraidMate_right_braidR]
  let A := upwardMateLayers L i j (red :: R) .FE
  let pre : List (SignedLayer I ℓ) := [(L, (.redBlack r (false, j)), (eᵢ :: R)),
      ((L ++ [fⱼ]), (.redBlack r (true, i)), R)]
  let post : List (SignedLayer I ℓ) := []
  change signedDg RD Λ (Pd) μ _ _ (pre ++ A ++ post) = _
  refine (frame RD Λ μ Q exponents P t (s := (L ++ [red, fⱼ, eᵢ] ++ R)) (z := (L ++ [eᵢ, fⱼ, red] ++ R)) pre post
    (liftHalfMate RD Λ μ Q exponents P t (mixedBlack_halfMate_FE RD Λ (Pm) μ L i j (red :: R) t))
    (by simp [pre, signedChain, Move.bottom, Move.top, List.append_assoc])
    (by simp [upwardMateLayers, signedChain, Move.bottom, Move.top, List.append_assoc])
    (by simp [downwardMateLayers, signedChain, Move.bottom, Move.top, List.append_assoc])
    (by simp [post, signedChain, List.append_assoc])).trans ?_
  apply congrArg (t j i • ·)
  dsimp only [pre, post, downwardMateLayers, List.cons_append, List.nil_append, List.append_assoc]
  signed_step 1 with ((signedDg_swap RD Λ (Pd) μ L [fⱼ] R (.black (.cup (true, i))) (.redBlack r (true, i)) rfl rfl).symm)
  signed_step 0 with ((signedDg_swap RD Λ (Pd) μ L [] (eᵢ :: R) (.black (.cup (true, i))) (.redBlack r (false, j)) rfl rfl).symm)
  signed_step 2 with ((signedDg_swap RD Λ (Pd) μ (L ++ [eᵢ]) [] R (.black (.cross false i j)) (.redBlack r (true, i)) rfl rfl).symm)
  signed_step 3 with (capMate RD Λ Q exponents P t μ (L ++ [eᵢ, fⱼ]) R (true, i) r)
  rfl

private theorem mixed_right_braidL :
    signedDg RD Λ (Pd) μ (L ++ [red, fⱼ, eᵢ] ++ R) (L ++ [eᵢ, fⱼ, red] ++ R) (mixedRedTripleLayers L r i j R .RFE true) =
      t j i • redBraidMate RD Λ μ L r i j R Q exponents (Pf) .right ((P₀).diag (braidL dᵢ rL dⱼ)) := by
  rw [redBraidMate_right_braidL]
  let A := upwardMateLayers (L ++ [red]) i j R .FE
  let pre : List (SignedLayer I ℓ) := []
  let post : List (SignedLayer I ℓ) := [(L, (.redBlack r (true, i)), (fⱼ :: R)),
      ((L ++ [eᵢ]), (.redBlack r (false, j)), R)]
  change signedDg RD Λ (Pd) μ _ _ (pre ++ A ++ post) = _
  refine (frame RD Λ μ Q exponents P t (s := (L ++ [red, fⱼ, eᵢ] ++ R)) (z := (L ++ [eᵢ, fⱼ, red] ++ R)) pre post
    (liftHalfMate RD Λ μ Q exponents P t (mixedBlack_halfMate_FE RD Λ (Pm) μ (L ++ [red]) i j R t))
    (by simp [pre, signedChain, List.append_assoc])
    (by simp [upwardMateLayers, signedChain, Move.bottom, Move.top, List.append_assoc])
    (by simp [downwardMateLayers, signedChain, Move.bottom, Move.top, List.append_assoc])
    (by simp [post, signedChain, Move.bottom, Move.top, List.append_assoc])).trans ?_
  apply congrArg (t j i • ·)
  dsimp only [pre, post, downwardMateLayers, List.cons_append, List.nil_append, List.append_assoc]
  signed_step 2 with ((signedDg_swap RD Λ (Pd) μ L [fⱼ] R (.redBlack r (true, i)) (.black (.cap (true, i))) rfl rfl).symm)
  signed_step 3 with ((signedDg_swap RD Λ (Pd) μ (L ++ [eᵢ]) [] R (.redBlack r (false, j)) (.black (.cap (true, i))) rfl rfl).symm)
  signed_step 1 with ((signedDg_swap RD Λ (Pd) μ L [] (eᵢ :: R) (.redBlack r (true, i)) (.black (.cross false i j)) rfl rfl).symm)
  signed_step 0 with ((cupMate RD Λ Q exponents P t μ L (fⱼ :: eᵢ :: R) (true, i) r).symm)
  rfl


/-- The bottom order of the mixed triple with a middle downward strand. -/
def RedBraidMateSide.order : RedBraidMateSide → MixedRedOrder
  | .left => .EFR
  | .right => .RFE

/-- The physical mixed braid in either middle-downward ordering and either crossing order. -/
def mixedMiddleBraid (side : RedBraidMateSide) (right : Bool) :
    (Pd).obj (obj RD Λ μ (L ++ side.bottom r i j ++ R)) ⟶
      (Pd).obj (obj RD Λ μ (L ++ side.flip.bottom r i j ++ R)) :=
  signedDg RD Λ (Pd) μ _ _ (mixedRedTripleLayers L r i j R side.order right)

/-- Webster v2, Definition 4.24 and Lemma 4.28. The two mixed triple points
in the remaining two boundary orders agree for distinct black colours. -/
theorem mixedRed_triplePoint_of_ne (h : i ≠ j) (s : RedBraidMateSide) :
    mixedMiddleBraid RD Λ μ L r i j R Q exponents P t s false =
      mixedMiddleBraid RD Λ μ L r i j R Q exponents P t s true := by
  cases s with
  | left =>
    dsimp only [mixedMiddleBraid, RedBraidMateSide.bottom, RedBraidMateSide.flip, RedBraidMateSide.order]
    rw [mixed_left_braidR RD Λ μ L r i j R Q exponents P t,
      mixed_left_braidL RD Λ μ L r i j R Q exponents P t]
    exact congrArg (t j i • ·) (redBraidMate_ne RD Λ μ L r i j R Q exponents (Pf) h .left).symm
  | right =>
    dsimp only [mixedMiddleBraid, RedBraidMateSide.bottom, RedBraidMateSide.flip, RedBraidMateSide.order]
    rw [mixed_right_braidR RD Λ μ L r i j R Q exponents P t,
      mixed_right_braidL RD Λ μ L r i j R Q exponents P t]
    exact congrArg (t j i • ·) (redBraidMate_ne RD Λ μ L r i j R Q exponents (Pf) h .right).symm

/-- Webster v2, Definition 4.5 (4.1a), Definition 4.24, and Lemma 4.28.
At equal black colours, subtracting the right-starting mixed braid from the
left-starting one contributes the negative of the mated divided difference.
Each term has a cup, ordinary dots, and a cap. -/
theorem mixedRed_triplePoint_correction (s : RedBraidMateSide) :
    mixedMiddleBraid RD Λ μ L r i i R Q exponents P t s false -
      mixedMiddleBraid RD Λ μ L r i i R Q exponents P t s true =
    -(t i i • ∑ m ∈ Finset.range (exponents r i),
      redEqualBraidMate RD Λ μ L r i R Q exponents (Pf) s
        (End.of ((P₀).diag (E0 dᵢ rL dᵢ)) ^ m *
          End.of ((P₀).diag (E2 dᵢ rL dᵢ)) ^ (exponents r i - 1 - m))) := by
  rw [← redBraidMate_eq RD Λ μ L r i R Q exponents (Pf) s]
  cases s with
  | left =>
    dsimp only [mixedMiddleBraid, RedBraidMateSide.bottom, RedBraidMateSide.flip, RedBraidMateSide.order]
    rw [mixed_left_braidR RD Λ μ L r i i R Q exponents P t,
      mixed_left_braidL RD Λ μ L r i i R Q exponents P t, ← smul_sub, ← smul_neg, neg_sub]
    rfl
  | right =>
    dsimp only [mixedMiddleBraid, RedBraidMateSide.bottom, RedBraidMateSide.flip, RedBraidMateSide.order]
    rw [mixed_right_braidR RD Λ μ L r i i R Q exponents P t,
      mixed_right_braidL RD Λ μ L r i i R Q exponents P t, ← smul_sub, ← smul_neg, neg_sub]
    rfl

/-- Every boundary order with the downward strand outside has an exact mixed
triple point in the same presentation as the two middle-downward equations. -/
theorem mixedRed_triplePoint_outer (o : MixedRedOrder) (ho : o.downOutside) :
    signedDg RD Λ (Pd) μ (L ++ o.word r i j ++ R) (L ++ (o.word r i j).reverse ++ R)
      (mixedRedTripleLayers L r i j R o false) =
    signedDg RD Λ (Pd) μ (L ++ o.word r i j ++ R) (L ++ (o.word r i j).reverse ++ R)
      (mixedRedTripleLayers L r i j R o true) := by
  have h := mixedRed_triplePoint_of_downOutside RD Λ P μ L r i j R o ho
  simp only [← lin_signedLin] at h ⊢
  apply lin_eq_addRels (Pf)
  apply lin_eq_addRels (addMixedCupPitchforkRelations RD Λ (Pm) t)
  exact lin_eq_addRels (Pm) h

/-- For different black colours, the physical red mixed Reidemeister III move
holds for all six permutations of the strands, in one signed presentation. -/
theorem mixedRed_triplePoint_ne (o : MixedRedOrder) (h : i ≠ j) :
    signedDg RD Λ (Pd) μ (L ++ o.word r i j ++ R) (L ++ (o.word r i j).reverse ++ R)
      (mixedRedTripleLayers L r i j R o false) =
    signedDg RD Λ (Pd) μ (L ++ o.word r i j ++ R) (L ++ (o.word r i j).reverse ++ R)
      (mixedRedTripleLayers L r i j R o true) := by
  cases o with
  | EFR => exact mixedRed_triplePoint_of_ne RD Λ μ L r i j R Q exponents P t h .left
  | RFE => exact mixedRed_triplePoint_of_ne RD Λ μ L r i j R Q exponents P t h .right
  | ERF | REF | FRE | FER => exact mixedRed_triplePoint_outer RD Λ μ L r i j R Q exponents P t _ rfl

end Categorification.Stendhal.DoubleDiagram

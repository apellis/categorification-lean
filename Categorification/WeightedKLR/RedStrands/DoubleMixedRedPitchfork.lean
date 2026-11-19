/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleMixedRedTriple
import Categorification.WeightedKLR.RedStrands.DoubleBlackAdjunction

/-!
# The two half-mates of a black crossing

Webster, arXiv:1309.3796v2, Definition 2.4, first cup pitchfork (2.1a)
and its vertical mirror. Capping either cup equation and cancelling a
biadjunction triangle expresses the upward-defined sideways crossing as
the downward-defined mate multiplied by the printed parameter tⱼᵢ.
-/
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe w u v
variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)
  {k : Type w} [CommRing k] (P : Presentation.{w,max u v} (signature RD Λ) k)
  (μ : X) (L : List (DoubleStrand I ℓ)) (i j : I) (R : List (DoubleStrand I ℓ))

private abbrev E (i : I) : DoubleStrand I ℓ := .inl (true, i)
private abbrev F (i : I) : DoubleStrand I ℓ := .inl (false, i)

/-- Read the sideways crossing as the mate of a downward crossing. -/
def downwardMateLayers : MixedBlackOrder → List (SignedLayer I ℓ)
  | .EF => [(L ++ [E i, F j], .black (.cup (false, i)), R),
      (L ++ [E i], .black (.cross false j i), E i :: R),
      (L, .black (.cap (false, i)), F j :: E i :: R)]
  | .FE => [(L, .black (.cup (true, i)), F j :: E i :: R),
      (L ++ [E i], .black (.cross false i j), E i :: R),
      (L ++ [E i, F j], .black (.cap (true, i)), R)]

private def forkTarget : MixedBlackOrder → List (DoubleStrand I ℓ)
  | .EF => [F i, F j, E i]
  | .FE => [E i, F j, F i]

/-- Straight branch of the cup pitchfork, with its downward crossing. -/
def downCupPitchforkLayers : MixedBlackOrder → List (SignedLayer I ℓ)
  | .EF => [(L ++ [F j], .black (.cup (false, i)), R),
      (L, .black (.cross false j i), E i :: R)]
  | .FE => [(L, .black (.cup (true, i)), F j :: R),
      (L ++ [E i], .black (.cross false i j), R)]

/-- Bent branch of the cup pitchfork, with the sideways crossing expanded. -/
def mixedCupPitchforkLayers : MixedBlackOrder → List (SignedLayer I ℓ)
  | .EF => (L, .black (.cup (false, i)), F j :: R) ::
      upwardMateLayers (L ++ [F i]) i j R .EF
  | .FE => (L ++ [F j], .black (.cup (true, i)), R) ::
      upwardMateLayers L i j (F i :: R) .FE

private theorem forkChain (o : MixedBlackOrder) :
    signedChain (L ++ [F j] ++ R) (downCupPitchforkLayers L i j R o) (L ++ forkTarget i j o ++ R) ∧
    signedChain (L ++ [F j] ++ R) (mixedCupPitchforkLayers L i j R o) (L ++ forkTarget i j o ++ R) := by
  cases o <;> simp [signedChain, Move.bottom, Move.top, forkTarget, downCupPitchforkLayers,
    mixedCupPitchforkLayers, upwardMateLayers, F, E, List.append_assoc]

/-- The first cup pitchfork or its mirror with black through-colour j, cup-colour i. -/
structure MixedCupPitchfork (X : Type v) (I : Type u) (ℓ : ℕ) where
  leftWeight : X
  left : List (DoubleStrand I ℓ)
  cupColour : I
  throughColour : I
  right : List (DoubleStrand I ℓ)
  order : MixedBlackOrder

private abbrev MixedCupPitchfork.source (a : MixedCupPitchfork X I ℓ) :=
  obj RD Λ a.leftWeight (a.left ++ [F a.throughColour] ++ a.right)

private abbrev MixedCupPitchfork.target (a : MixedCupPitchfork X I ℓ) :=
  obj RD Λ a.leftWeight (a.left ++ forkTarget a.cupColour a.throughColour a.order ++ a.right)

private def mixedCupPitchforkRelation (t : I → I → k) (a : MixedCupPitchfork X I ℓ) :
    LinDiagram k (a.source RD Λ) (a.target RD Λ) :=
  let h := forkChain a.left a.cupColour a.throughColour a.right a.order
  LinDiagram.of (Diagram.mk _ (chain_signedLayers RD Λ a.leftWeight h.2)) -
    t a.throughColour a.cupColour • LinDiagram.of (Diagram.mk _ (chain_signedLayers RD Λ a.leftWeight h.1))

/-- Adjoin the first cup equation of Webster v2 (2.1a) and its mirror in signed contexts. -/
def addMixedCupPitchforkRelations (t : I → I → k) :
    Presentation.{w,max u v} (signature RD Λ) k :=
  P.addRels _ (MixedCupPitchfork.source RD Λ) (MixedCupPitchfork.target RD Λ)
    (mixedCupPitchforkRelation RD Λ t)

/-- The adjoined cup pitchfork relation is the bent branch minus `tⱼᵢ` times the straight
branch. -/
theorem addMixedCupPitchforkRelations_rel (t : I → I → k) (a : MixedCupPitchfork X I ℓ) :
    ∃ d₁ d₂ : (addMixedCupPitchforkRelations RD Λ P t).dom (.inr a) ⟶
        (addMixedCupPitchforkRelations RD Λ P t).cod (.inr a),
      (addMixedCupPitchforkRelations RD Λ P t).rel (.inr a) =
        LinDiagram.of d₁ - t a.throughColour a.cupColour • LinDiagram.of d₂ ∧
      Diagram.layers d₁ = signedLayers RD Λ a.leftWeight
        (mixedCupPitchforkLayers a.left a.cupColour a.throughColour a.right a.order) ∧
      Diagram.layers d₂ = signedLayers RD Λ a.leftWeight
        (downCupPitchforkLayers a.left a.cupColour a.throughColour a.right a.order) :=
  ⟨_, _, rfl, rfl, rfl⟩

variable (t : I → I → k)
local notation "T" => addBlackAdjunctionRelations RD Λ (addMixedCupPitchforkRelations RD Λ P t)

private theorem fork (o : MixedBlackOrder) {s : List (DoubleStrand I ℓ)} (hs : s = L ++ [F j] ++ R) :
    signedDg RD Λ (T) μ s (L ++ forkTarget i j o ++ R)
        (mixedCupPitchforkLayers L i j R o) =
    t j i • signedDg RD Λ (T) μ s (L ++ forkTarget i j o ++ R)
        (downCupPitchforkLayers L i j R o) := by
  subst s
  let a : MixedCupPitchfork X I ℓ := ⟨μ,L,i,j,R,o⟩
  have h := (T).lin_rel_self (.inl (.inr a))
  change (T).lin (mixedCupPitchforkRelation RD Λ t a) = 0 at h
  simp only [mixedCupPitchforkRelation, Presentation.lin_sub, Presentation.lin_smul,
    Presentation.lin_of, sub_eq_zero] at h
  rw [signedDg_of RD Λ (T) μ (forkChain L i j R o).2,
    signedDg_of RD Λ (T) μ (forkChain L i j R o).1]
  exact h

private theorem snakeR :
    signedDg RD Λ (T) μ (L ++ [E i] ++ R) (L ++ [E i] ++ R)
      [(L ++ [E i], .black (.cup (false,i)), R),
       (L, .black (.cap (false,i)), E i :: R)] =
    signedDg RD Λ (T) μ (L ++ [E i] ++ R) (L ++ [E i] ++ R) [] := by
  rw [signedDg_nil, signedDg_eq_diag_of_layers RD Λ (T) μ
    (by simp [signedChain, Move.bottom, Move.top, List.append_assoc])
    (blackSnakeRight RD Λ μ L (true,i) R) rfl]
  apply blackSnakeRight_eq

private theorem snakeL :
    signedDg RD Λ (T) μ (L ++ [E i] ++ R) (L ++ [E i] ++ R)
      [(L, .black (.cup (true,i)), E i :: R),
       (L ++ [E i], .black (.cap (true,i)), R)] =
    signedDg RD Λ (T) μ (L ++ [E i] ++ R) (L ++ [E i] ++ R) [] := by
  rw [signedDg_nil, signedDg_eq_diag_of_layers RD Λ (T) μ
    (by simp [signedChain, Move.bottom, Move.top, List.append_assoc])
    (blackSnakeLeft RD Λ μ L (true,i) R) rfl]
  apply blackSnakeLeft_eq

/-- Append the same moves after a scalar-weighted diagram equation. -/
theorem signedDg_append_smul {s b z : List (DoubleStrand I ℓ)} {A B post : List (SignedLayer I ℓ)}
    {c : k} (h : signedDg RD Λ P μ s b A = c • signedDg RD Λ P μ s b B)
    (hA : signedChain s A b) (hB : signedChain s B b) (hp : signedChain b post z) :
    signedDg RD Λ P μ s z (A ++ post) = c • signedDg RD Λ P μ s z (B ++ post) := by
  rw [← signedDg_comp RD Λ P μ hA hp, ← signedDg_comp RD Λ P μ hB hp, h, Linear.smul_comp]

private theorem capForkEF :
    signedDg RD Λ (T) μ (L ++ [E i, F j] ++ R) (L ++ [F j, E i] ++ R)
      ((mixedCupPitchforkLayers (L ++ [E i]) i j R .EF) ++
        [(L, .black (.cap (false,i)), F j :: E i :: R)]) =
    t j i • signedDg RD Λ (T) μ (L ++ [E i, F j] ++ R) (L ++ [F j, E i] ++ R)
      (downwardMateLayers L i j R .EF) := by
  have h := signedDg_append_smul RD Λ (T) μ (fork RD Λ P μ (L ++ [E i]) i j R t .EF
    (s := L ++ [E i, F j] ++ R) (by simp [List.append_assoc]))
    (by simp [mixedCupPitchforkLayers, upwardMateLayers, signedChain, Move.bottom, Move.top,
      forkTarget, List.append_assoc])
    (by simp [downCupPitchforkLayers, signedChain, Move.bottom, Move.top, forkTarget, List.append_assoc])
    (post := [(L, .black (.cap (false,i)), F j :: E i :: R)])
    (z := L ++ [F j,E i] ++ R) (by simp [forkTarget, signedChain, Move.bottom, Move.top,
      E, F, List.append_assoc])
  simpa only [downwardMateLayers, downCupPitchforkLayers, List.cons_append, List.nil_append,
    List.append_assoc] using h

private theorem capForkFE :
    signedDg RD Λ (T) μ (L ++ [F j, E i] ++ R) (L ++ [E i, F j] ++ R)
      ((mixedCupPitchforkLayers L i j (E i :: R) .FE) ++
        [(L ++ [E i, F j], .black (.cap (true,i)), R)]) =
    t j i • signedDg RD Λ (T) μ (L ++ [F j, E i] ++ R) (L ++ [E i, F j] ++ R)
      (downwardMateLayers L i j R .FE) := by
  have h := signedDg_append_smul RD Λ (T) μ (fork RD Λ P μ L i j (E i :: R) t .FE
    (s := L ++ [F j, E i] ++ R) (by simp [List.append_assoc]))
    (by simpa [List.append_assoc] using (forkChain L i j (E i :: R) .FE).2) (by simpa [List.append_assoc] using (forkChain L i j (E i :: R) .FE).1)
    (post := [(L ++ [E i,F j], .black (.cap (true,i)), R)])
    (z := L ++ [E i,F j] ++ R) (by simp [forkTarget, signedChain, Move.bottom, Move.top,
      E, F, List.append_assoc])
  simpa only [downwardMateLayers, downCupPitchforkLayers, List.cons_append, List.nil_append,
    List.append_assoc] using h

/-- The sideways crossing EᵢFⱼ is tⱼᵢ times its downward-crossing mate. -/
theorem mixedBlack_halfMate_EF :
    signedDg RD Λ (T) μ (L ++ [E i, F j] ++ R) (L ++ [F j, E i] ++ R)
      (upwardMateLayers L i j R .EF) =
    t j i • signedDg RD Λ (T) μ (L ++ [E i, F j] ++ R) (L ++ [F j, E i] ++ R)
      (downwardMateLayers L i j R .EF) := by
  apply Eq.trans _ (capForkEF RD Λ P μ L i j R t)
  symm
  simp only [upwardMateLayers, mixedCupPitchforkLayers, List.cons_append, List.nil_append,
    List.append_assoc]
  signed_step 3 with ((signedDg_swap RD Λ (T) μ L [F j, E i] R
    (.black (.cap (false,i))) (.black (.cap (false,j))) rfl rfl).symm)
  signed_step 2 with ((signedDg_swap RD Λ (T) μ L [F j] (F j :: R)
    (.black (.cap (false,i))) (.black (.cross true j i)) rfl rfl).symm)
  signed_step 1 with ((signedDg_swap RD Λ (T) μ L [] (E i :: F j :: R)
    (.black (.cap (false,i))) (.black (.cup (false,j))) rfl rfl).symm)
  signed_step 0 with (snakeR RD Λ P μ L i (F j :: R) t)
  simp

/-- The sideways crossing FⱼEᵢ is tⱼᵢ times its downward-crossing mate. -/
theorem mixedBlack_halfMate_FE :
    signedDg RD Λ (T) μ (L ++ [F j, E i] ++ R) (L ++ [E i, F j] ++ R)
      (upwardMateLayers L i j R .FE) =
    t j i • signedDg RD Λ (T) μ (L ++ [F j, E i] ++ R) (L ++ [E i, F j] ++ R)
      (downwardMateLayers L i j R .FE) := by
  apply Eq.trans _ (capForkFE RD Λ P μ L i j R t)
  symm
  simp only [upwardMateLayers, mixedCupPitchforkLayers, List.cons_append, List.nil_append]
  signed_step 3 with (signedDg_swap RD Λ (T) μ L [E i,F j] R
    (.black (.cap (true,j))) (.black (.cap (true,i))) rfl rfl)
  signed_step 2 with (signedDg_swap RD Λ (T) μ (L ++ [F j]) [F j] R
    (.black (.cross true i j)) (.black (.cap (true,i))) rfl rfl)
  signed_step 1 with (signedDg_swap RD Λ (T) μ (L ++ [F j,E i]) [] R
    (.black (.cup (true,j))) (.black (.cap (true,i))) rfl rfl)
  signed_step 0 with (snakeL RD Λ P μ (L ++ [F j]) i R t)
  rfl

end Categorification.Stendhal.DoubleDiagram

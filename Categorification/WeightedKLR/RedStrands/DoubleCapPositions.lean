/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapBlockInduction
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapInterleave
import Categorification.Diagrams.KL3.SpanningSetElim

/-!
# Positions of signed moves immediately below a cap

The position split in the proof of Khovanov–Lauda III, Proposition 3.11,
used in Webster, arXiv:1309.3796v2, §4.5, Lemma 4.28, depends only on
the output word of the preceding move. There are five positions for a dot
and eight for the outputs of a crossing or cup. The actual signed generators
and the upward black mates realize these cases without red bends or red-red
crossings.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory StringDiagrams QuantumGroup QuantumGroup.UDot KL3.Diagram KLR KLR.Diagram

universe w u v

/-- The five positions of the marked strand `x` relative to cap ends `A,B`. The
indices are left and right move contexts, then left, inside and right cap contexts. -/
inductive DotPlacement {α : Type*} (A B : α) :
    List α → α → List α → List α → List α → List α → Prop
  | before (u : List α) (x : α) (m s q : List α) :
      DotPlacement A B u x (m ++ [A] ++ s ++ [B] ++ q) (u ++ [x] ++ m) s q
  | leftEnd (p s q : List α) : DotPlacement A B p A (s ++ [B] ++ q) p s q
  | inside (p u : List α) (x : α) (v q : List α) :
      DotPlacement A B (p ++ [A] ++ u) x (v ++ [B] ++ q) p (u ++ [x] ++ v) q
  | rightEnd (p s q : List α) : DotPlacement A B (p ++ [A] ++ s) B q p s q
  | after (p s m : List α) (x : α) (v : List α) :
      DotPlacement A B (p ++ [A] ++ s ++ [B] ++ m) x v p s (m ++ [x] ++ v)

/-- The eight positions of the adjacent output strands `y,z`. -/
inductive PairPlacement {α : Type*} (A B : α) :
    List α → α → α → List α → List α → List α → List α → Prop
  | before (u : List α) (y z : α) (m s q : List α) :
      PairPlacement A B u y z (m ++ [A] ++ s ++ [B] ++ q) (u ++ [y,z] ++ m) s q
  | enterLeft (u : List α) (y : α) (s q : List α) :
      PairPlacement A B u y A (s ++ [B] ++ q) (u ++ [y]) s q
  | first (p : List α) (z : α) (s q : List α) :
      PairPlacement A B p A z (s ++ [B] ++ q) p (z :: s) q
  | both (p q : List α) : PairPlacement A B p A B q p [] q
  | inside (p u : List α) (y z : α) (v q : List α) :
      PairPlacement A B (p ++ [A] ++ u) y z (v ++ [B] ++ q) p (u ++ [y,z] ++ v) q
  | last (p s : List α) (y : α) (q : List α) :
      PairPlacement A B (p ++ [A] ++ s) y B q p (s ++ [y]) q
  | enterRight (p s : List α) (z : α) (v : List α) :
      PairPlacement A B (p ++ [A] ++ s) B z v p s (z :: v)
  | after (p s m : List α) (y z : α) (v : List α) :
      PairPlacement A B (p ++ [A] ++ s ++ [B] ++ m) y z v p s (m ++ [y,z] ++ v)

theorem dotPlacement_of_eq {α : Type*} {A B x : α} {u v p s q : List α}
    (h : u ++ [x] ++ v = p ++ [A] ++ s ++ [B] ++ q) : DotPlacement A B u x v p s q := by
  rcases posDot h with ⟨m,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨m,n,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ | ⟨m,rfl,rfl⟩
  exacts [.before .., .leftEnd .., .inside .., .rightEnd .., .after ..]

theorem pairPlacement_of_eq {α : Type*} {A B y z : α} {u v p s q : List α}
    (h : u ++ [y,z] ++ v = p ++ [A] ++ s ++ [B] ++ q) : PairPlacement A B u y z v p s q := by
  rcases posPair h with ⟨m,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,m,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl,rfl⟩ | ⟨m,n,rfl,rfl,rfl⟩ | ⟨m,rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ | ⟨m,rfl,rfl⟩
  exacts [.before .., .enterLeft .., .first .., .both .., .inside .., .last .., .enterRight .., .after ..]

variable {I : Type u} {ℓ : ℕ}
local notation "B" => DoubleStrand I ℓ

/-- A forward elementary move in the cap calculus. Only physically admissible
crossings occur and all bends are black. -/
inductive CapPredecessor (I : Type u) (ℓ : ℕ)
  | dot (l : Letter I)
  | cup (l : Letter I)
  | cross (x y : DoubleStrand I ℓ) (allowed : CanCross x y)

namespace CapPredecessor

def bottom : CapPredecessor I ℓ → List B
  | .dot s => [.inl s]
  | .cup _ => []
  | .cross x y _ => [x,y]

def top : CapPredecessor I ℓ → List B
  | .dot s => [.inl s]
  | .cup s => [.inl s,.inl s.dual]
  | .cross x y _ => [y,x]

def rows (m : CapPredecessor I ℓ) (u v : List B) : List (SignedLayer I ℓ) :=
  match m with
  | .dot s => [(u,.black (.dot s),v)]
  | .cup s => [(u,.black (.cup s),v)]
  | .cross x y _ => signedCrossLayers u x y v

/-- Relative position uses the upper strands, so a crossing appears in the
order opposite to its input. -/
def Placement (m : CapPredecessor I ℓ) (u v p s : List B) (l : Letter I) (q : List B) : Prop :=
  match m with
  | .dot x => DotPlacement (.inl l.dual) (.inl l) u (.inl x) v p s q
  | .cup x => PairPlacement (.inl l.dual) (.inl l) u (.inl x) (.inl x.dual) v p s q
  | .cross x y _ => PairPlacement (.inl l.dual) (.inl l) u y x v p s q

theorem placement_of_top (m : CapPredecessor I ℓ) (u v p s : List B) (l : Letter I) (q : List B)
    (h : u ++ m.top ++ v = p ++ [.inl l.dual] ++ s ++ [.inl l] ++ q) : m.Placement u v p s l q := by
  cases m with
  | dot => exact dotPlacement_of_eq h
  | cup | cross => exact pairPlacement_of_eq h

theorem chain (m : CapPredecessor I ℓ) (u v : List B) : signedChain (u ++ m.bottom ++ v)
    (m.rows u v) (u ++ m.top ++ v) := by
  cases m with
  | dot s | cup s => simp [rows, signedChain, top, bottom, Move.top, Move.bottom, Shape.dom, Shape.cod]
  | cross x y h => exact signedCrossLayers_chain u h v

theorem rows_ne_nil (m : CapPredecessor I ℓ) (u v : List B) : m.rows u v ≠ [] := by
  cases m with
  | dot | cup => simp [rows]
  | cross x y h =>
    have hc := signedCrossLayers_crossings u h v
    intro he
    change signedCrossLayers u x y v = [] at he
    rw [he] at hc
    contradiction

end CapPredecessor

variable {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {Λ : Fin ℓ → X}
local notation "S" => signature RD Λ

/-- Recover both word boundaries of a nonempty physical list of signed layers. -/
theorem boundaries_of_signedLayers {b c : Obj S} (g : b ⟶ c) (μ : X)
    {u v : List B} {ls : List (SignedLayer I ℓ)} (hc : signedChain u ls v) (hn : ls ≠ [])
    (hg : Diagram.layers g = signedLayers RD Λ μ ls) :
    b = obj RD Λ μ u ∧ c = obj RD Λ μ v := by
  have h₁ := Diagram.chain g
  rw [hg] at h₁
  have h₂ := chain_signedLayers RD Λ μ hc
  have h : b = obj RD Λ μ u := by
    cases ls with
    | nil => contradiction
    | cons L ls => exact h₁.2.1.symm.trans h₂.2.1
  exact ⟨h, (h ▸ h₁ : Chain (obj RD Λ μ u) _ c).target_unique h₂⟩

private theorem of_noncap (g : Move I ℓ) (u v : List B) (hc : ¬g.IsCap) :
    ∃ m : CapPredecessor I ℓ, m.rows u v = [(u,g,v)] := by
  cases g with
  | black s =>
    cases s with
    | dot x => exact ⟨.dot x,rfl⟩
    | cup x => exact ⟨.cup x,rfl⟩
    | cap => exact False.elim (hc trivial)
    | cross ε i j =>
      refine ⟨.cross (.inl (ε,i)) (.inl (ε,j)) trivial, ?_⟩
      cases ε <;> rfl
  | redBlack r x => exact ⟨.cross (.inr r) (.inl x) trivial, rfl⟩
  | blackRed x r => exact ⟨.cross (.inl x) (.inr r) trivial, rfl⟩

variable (k : Type w) [CommRing k] {M : Type*} [AddCommGroup M] [Module k M]
  {a t : Obj (signature RD Λ)} (E : (a ⟶ t) → M)

/-- Projected successor statement for a specified placement of a preceding
move. All physical layers, the entire exterior prefix, the dot count, and the
continuation are explicit. -/
def CapSuccessorAt (m : CapPredecessor I ℓ) (u v L U : List B) (l : Letter I) (R : List B) : Prop :=
  ∀ (μ : X) (p : a ⟶ obj RD Λ μ (u ++ m.bottom ++ v)), ForwardPath a p → ResolvesSignedCapBlocks k E p →
    ∀ (g : obj RD Λ μ (u ++ m.bottom ++ v) ⟶ obj RD Λ μ (u ++ m.top ++ v)),
      Diagram.layers g = signedLayers RD Λ μ (m.rows u v) →
      ∀ {e : Obj S} (block : obj RD Λ μ (u ++ m.top ++ v) ⟶ e) (d : ℕ) (post : e ⟶ t),
        Diagram.layers block = signedLayers RD Λ μ (signedCapBlock L U l R d) →
        E (((p ≫ g) ≫ block) ≫ post) ∈ forwardSpan k E post (crossingNumber (p ≫ g) + U.length) ⊔
          fewerCrossings k E post (crossingNumber (p ≫ g) + U.length)

/-- The five dot, eight cup, and eight admissible crossing positions exhaust
the successors of a physical forward word at an all-down source. -/
theorem pushesTerminalCaps_of_positions (ha : cutHeight a = 0)
    (dot : ∀ x u v L U l R,
      DotPlacement (.inl l.dual) (.inl l) u (.inl x) v L U R →
        CapSuccessorAt k E (.dot x) u v L U l R)
    (cup : ∀ x u v L U l R,
      PairPlacement (.inl l.dual) (.inl l) u (.inl x) (.inl x.dual) v L U R →
        CapSuccessorAt k E (.cup x) u v L U l R)
    (cross : ∀ x y (hxy : CanCross x y) u v L U l R,
      PairPlacement (.inl l.dual) (.inl l) u y x v L U R →
        CapSuccessorAt k E (.cross x y hxy) u v L U l R) : PushesTerminalCaps k E := by
  have applyMove {b c : Obj S} (p : a ⟶ b) (hp : ForwardPath a p) (ih : ResolvesSignedCapBlocks k E p)
      (g : b ⟶ c) (μ : X) (m : CapPredecessor I ℓ) (u v : List B)
      (hg : Diagram.layers g = signedLayers RD Λ μ (m.rows u v)) : ResolvesSignedCapBlocks k E (p ≫ g) := by
    obtain ⟨hb,hc⟩ := boundaries_of_signedLayers g μ (m.chain u v) (m.rows_ne_nil u v) hg
    subst b c
    intro e block L U l R d he hl post
    have ht := congrArg (fun q : Obj S => q.word.map Prod.snd) he
    change (colours RD Λ μ (u ++ m.top ++ v)).map Prod.snd =
      (colours RD Λ μ (L ++ [.inl l.dual] ++ U ++ [.inl l] ++ R)).map Prod.snd at ht
    simp only [forget_colours] at ht
    have pos := m.placement_of_top u v L U l R ht
    have law : CapSuccessorAt k E m u v L U l R := by
      cases m with
      | dot x => exact dot x u v L U l R pos
      | cup x => exact cup x u v L U l R pos
      | cross x y h => exact cross x y h u v L U l R pos
    exact law μ p hp ih g hg block d post hl
  apply pushesTerminalCaps_of_capBlock_steps k E ha
  · intro b c p hp ih g M hg hn
    have hc := Diagram.chain g
    rw [hg] at hc
    have e := recover_signed_layer RD Λ M hc.1
    obtain ⟨m,hm⟩ := of_noncap M.gen.2 (M.left.map Prod.snd) (M.right.map Prod.snd) hn
    apply applyMove p hp ih g M.start m (M.left.map Prod.snd) (M.right.map Prod.snd)
    rw [hm, hg]
    exact congrArg (fun x => [x]) e.symm
  · intro b c p hp ih g L R i j o ho
    cases o with
    | EF => exact applyMove p hp ih g b.start (.cross (.inl (up i)) (.inl (dn j)) trivial) L R ho
    | FE => exact applyMove p hp ih g b.start (.cross (.inl (dn j)) (.inl (up i)) trivial) L R ho

end Categorification.Stendhal.DoubleDiagram

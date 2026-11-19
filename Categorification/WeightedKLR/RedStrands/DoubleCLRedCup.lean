/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLMoveContext
import Categorification.WeightedKLR.RedStrands.DoubleRedCup

/-!
# The red cup relations after the cover functor

Webster, arXiv:1309.3796v3, §4.5, Definition 4.24, and §4.6, proof of Lemma 4.29. The red cup
relation of `addRedCupRelations` slides a black cup through a red strand. After reflection it
becomes a sideways crossing of a black cup with an upward red strand, and the two sides agree by
the interchange law and one zigzag identity (`redCup_reflect_up`, `redCup_reflect_dn`). Hence
the relation vanishes after the cover functor in every presentation with the pivotal zigzag
identities (`coverLin_redCupRel`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram.CL

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe u v w
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {k : Type w} [CommRing k]
  (P : Presentation.{w, max u v} (psig RD) k)

/-- A cup of colour `up b` slides through an upward strand of colour `a` from the right, the
sideways crossing being written as a mate. -/
theorem redCup_reflect_up (hz : P.PivotalZigzags (inv RD).toColourDuality) (ν : X) (a b : I) :
    dgC P ν [up a] [up b, up a, dn b]
        [([], .cup (up b), [up a]), ([up b, dn b, up a], .cup (up b), []),
          ([up b, dn b], .cross true a b, [dn b]), ([up b], .cap (up b), [up a, dn b])] =
      dgC P ν [up a] [up b, up a, dn b]
        [([up a], .cup (up b), []), ([], .cross true a b, [dn b])] := by
  dswapC 0
  dswapC 1
  datC 2 [] [up a, dn b] (dgC_zigL' P hz (wt RD ν [up a, dn b]) (up b))

/-- A cup of colour `dn b` slides through an upward strand of colour `a` from the right, the
sideways crossing being written as a mate. -/
theorem redCup_reflect_dn (hz : P.PivotalZigzags (inv RD).toColourDuality) (ν : X) (a b : I) :
    dgC P ν [up a] [dn b, up a, up b]
        [([up a], .cup (dn b), []), ([], .cup (dn b), [up a, dn b, up b]),
          ([dn b], .cross true b a, [dn b, up b]), ([dn b, up a], .cap (dn b), [up b])] =
      dgC P ν [up a] [dn b, up a, up b]
        [([], .cup (dn b), [up a]), ([dn b], .cross true b a, [])] := by
  dswapC 0
  dswapC 1
  datC 2 [dn b, up a] [] (dgC_zigR' P hz (wt RD ν []) (dn b))

end Categorification.KL3.Diagram.CL

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram KL3.Diagram.CL StringDiagrams TwoRep

universe w u v

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {C' : CartanDatum (I ⊕ Fin ℓ)}
  {X Y : Type v} [AddCommGroup X] [AddCommGroup Y] (W : WeightDatum C' X Y)
  (hC : ∀ i j, C'.dot (.inl i) (.inl j) = C.dot i j) (o : X)
  {k : Type w} [CommRing k]

local notation "RD" => blackDatum W hC
local notation "Λ" => redWeight W
local notation "κ" => coverColourMap W hC o
local notation "CM" => coverMirror W hC o

variable (Q : Presentation.{w, max u v} (psig W) k) (σ : Move I ℓ → k)

/-- The cover functor on a retyped double diagram. -/
theorem coverLin_cast {a b a' b' : Obj (signature RD Λ)} (f : a ⟶ b) (ha : a = a') (hb : b = b') :
    coverLin W hC o Q σ (LinDiagram.of (Diagram.cast f ha hb)) =
      eqToHom (by rw [ha]) ≫ coverLin W hC o Q σ (LinDiagram.of f) ≫ eqToHom (by rw [hb]) := by
  subst ha hb
  simp

/-- `coverLin_moveDiagram_ctx` in terms of the normal forms `dgC`. -/
theorem coverLin_moveDiagram_dgC (μ : X) (u : List (DoubleStrand I ℓ)) (m : Move I ℓ)
    (v : List (DoubleStrand I ℓ)) :
    SChain (coverWord v ++ coverWord m.bottom ++ coverWord u)
        ((coverMoveL m).map (whL (coverWord v) (coverWord u)))
        (coverWord v ++ coverWord m.top ++ coverWord u) ∧
    ∃ (e₁ : Q.obj ((κ).obj ((CM).obj (obj RD Λ μ (u ++ m.bottom ++ v)))) =
        Q.obj (ob W (o - μ) (coverWord v ++ coverWord m.bottom ++ coverWord u)))
      (e₂ : Q.obj (ob W (o - μ) (coverWord v ++ coverWord m.top ++ coverWord u)) =
        Q.obj ((κ).obj ((CM).obj (obj RD Λ μ (u ++ m.top ++ v))))),
      coverLin W hC o Q σ (LinDiagram.of (moveDiagram RD Λ μ u m v)) =
        σ m • (eqToHom e₁ ≫ dgC Q (o - μ) _ _
          ((coverMoveL m).map (whL (coverWord v) (coverWord u))) ≫ eqToHom e₂) := by
  obtain ⟨h, e₁, e₂, he⟩ := coverLin_moveDiagram_ctx W hC o Q σ μ u m v
  exact ⟨h, e₁, e₂, by rw [he, dgC_of h]⟩

/-- Two normal-form diagrams composed through an identification of their common boundary. -/
theorem eqToHom_dgC_comp {A₀ B₀ : Q.Presented} {ν : X}
    {s₁ t₁ s₂ t₂ s t r : List (Letter (I ⊕ Fin ℓ))}
    (hs : s₁ = s) (ht : t₁ = t) (hs' : s₂ = t) (hr : t₂ = r)
    {A B L : List (LayerData (I ⊕ Fin ℓ))} (hA : SChain s₁ A t₁) (hB : SChain s₂ B t₂)
    (hL : A ++ B = L) (x₁ : A₀ = Q.obj (ob W ν s₁)) (x₂ : Q.obj (ob W ν t₁) = Q.obj (ob W ν s₂))
    (x₃ : Q.obj (ob W ν t₂) = B₀) (y₁ : A₀ = Q.obj (ob W ν s)) (y₂ : Q.obj (ob W ν r) = B₀) :
    eqToHom x₁ ≫ dgC Q ν s₁ t₁ A ≫ eqToHom x₂ ≫ dgC Q ν s₂ t₂ B ≫ eqToHom x₃ =
      eqToHom y₁ ≫ dgC Q ν s r L ≫ eqToHom y₂ := by
  subst hs ht hs' hr hL
  rw [eqToHom_refl, Category.id_comp, ← Category.assoc (dgC Q ν _ _ A), dgC_comp hA hB]

/-- The reflected left-hand side of the red cup relation: a cup to the right of the red strand,
then a sideways crossing of the red strand with its left end. -/
def redCupLeftL (l : Letter I) (r : Fin ℓ) : List (LayerData (I ⊕ Fin ℓ)) :=
  ([(true, .inr r)], .cup (l.1, .inl l.2), []) ::
    (coverMoveL (.blackRed l.dual r)).map (whL [] [coverLetter (.inl l)])

/-- The reflected right-hand side of the red cup relation: a cup to the left of the red strand,
then a sideways crossing of the red strand with its right end. -/
def redCupRightL (l : Letter I) (r : Fin ℓ) : List (LayerData (I ⊕ Fin ℓ)) :=
  ([], .cup (l.1, .inl l.2), [(true, .inr r)]) ::
    (coverMoveL (.redBlack r l)).map (whL [coverLetter (.inl l.dual)] [])

theorem redCupLeftL_eq_redCupRightL (hz : Q.PivotalZigzags (inv W).toColourDuality) (ν : X)
    (l : Letter I) (r : Fin ℓ) :
    dgC Q ν [(true, .inr r)] [coverLetter (.inl l.dual), (true, .inr r), coverLetter (.inl l)]
        (redCupLeftL l r) =
      dgC Q ν [(true, .inr r)] [coverLetter (.inl l.dual), (true, .inr r), coverLetter (.inl l)]
        (redCupRightL l r) := by
  rcases l with ⟨_ | _, j⟩
  · exact redCup_reflect_dn Q hz ν (.inr r) (.inl j)
  · exact (redCup_reflect_up Q hz ν (.inr r) (.inl j)).symm

theorem coverWord_cons (a : DoubleStrand I ℓ) (w : List (DoubleStrand I ℓ)) :
    coverWord (a :: w) = coverWord w ++ [coverLetter a] := by
  simp [coverWord]

theorem coverLetter_inr (r : Fin ℓ) : coverLetter (I := I) (.inr r) = (true, .inr r) := rfl

/-- The bottom boundary of the red cup relations. -/
abbrev redCupBottom (r : Fin ℓ) : List (DoubleStrand I ℓ) := [.inr r]

/-- The top boundary of the red cup relations. -/
abbrev redCupTop (l : Letter I) (r : Fin ℓ) : List (DoubleStrand I ℓ) :=
  [.inl l, .inr r, .inl l.dual]

variable [DecidableEq I]

/-- The cover functor on the left-hand side of the red cup relation. -/
theorem coverLin_redCupLeft (μ : X) (u : List (DoubleStrand I ℓ)) (l : Letter I) (r : Fin ℓ)
    (v : List (DoubleStrand I ℓ))
    (e₁ : Q.obj ((κ).obj ((CM).obj (obj RD Λ μ (u ++ redCupBottom r ++ v)))) =
        Q.obj (ob W (o - μ) (coverWord (u ++ redCupBottom r ++ v))))
    (e₂ : Q.obj (ob W (o - μ) (coverWord (u ++ redCupTop l r ++ v))) =
        Q.obj ((κ).obj ((CM).obj (obj RD Λ μ (u ++ redCupTop l r ++ v))))) :
      coverLin W hC o Q coverSign (LinDiagram.of (redCupLeft RD Λ μ u l r v)) =
        eqToHom e₁ ≫ (dgC Q (o - μ) (coverWord (u ++ redCupBottom r ++ v))
          (coverWord (u ++ redCupTop l r ++ v))
          ((redCupLeftL l r).map (whL (coverWord v) (coverWord u))) :
          Q.obj (ob W (o - μ) (coverWord (u ++ redCupBottom r ++ v))) ⟶
          Q.obj (ob W (o - μ) (coverWord (u ++ redCupTop l r ++ v)))) ≫
          eqToHom e₂ := by
  obtain ⟨h₁, x₁, x₂, he₁⟩ :=
    coverLin_moveDiagram_dgC W hC o Q coverSign μ u (.black (.cup l)) (.inr r :: v)
  obtain ⟨h₂, x₃, x₄, he₂⟩ :=
    coverLin_moveDiagram_dgC W hC o Q coverSign μ (u ++ [.inl l]) (.blackRed l.dual r) v
  simp only [redCupLeft]
  rw [LinDiagram.of_comp, coverLin_comp, coverLin_cast, coverLin_cast, he₁, he₂]
  have hs₁ : coverSign (k := k) (ℓ := ℓ) (.black (.cup l)) = 1 := rfl
  have hs₂ : coverSign (k := k) (ℓ := ℓ) (.blackRed l.dual r) = 1 := rfl
  rw [hs₁, hs₂, one_smul, one_smul]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  refine eqToHom_dgC_comp W Q ?_ ?_ rfl ?_ h₁ h₂ ?_ _ _ _ _ _
  · simp [coverWord_cons, coverWord_append, coverLetter_inr, Move.bottom]
  · simp [coverWord_cons, coverWord_append, coverLetter_inr, Move.top, Move.bottom]
  · simp [coverWord_cons, coverWord_append, coverLetter_inr, Move.top]
  · have hc : coverMoveL (.black (.cup l) : Move I ℓ) = [([], .cup (l.1, .inl l.2), [])] := rfl
    simp [hc, redCupLeftL, coverWord_cons, coverWord_append, coverLetter_inr, whL, List.map_map,
      Function.comp_def]

/-- The cover functor on the right-hand side of the red cup relation. -/
theorem coverLin_redCupRight (μ : X) (u : List (DoubleStrand I ℓ)) (l : Letter I) (r : Fin ℓ)
    (v : List (DoubleStrand I ℓ))
    (e₁ : Q.obj ((κ).obj ((CM).obj (obj RD Λ μ (u ++ redCupBottom r ++ v)))) =
        Q.obj (ob W (o - μ) (coverWord (u ++ redCupBottom r ++ v))))
    (e₂ : Q.obj (ob W (o - μ) (coverWord (u ++ redCupTop l r ++ v))) =
        Q.obj ((κ).obj ((CM).obj (obj RD Λ μ (u ++ redCupTop l r ++ v))))) :
      coverLin W hC o Q coverSign (LinDiagram.of (redCupRight RD Λ μ u l r v)) =
        eqToHom e₁ ≫ (dgC Q (o - μ) (coverWord (u ++ redCupBottom r ++ v))
          (coverWord (u ++ redCupTop l r ++ v))
          ((redCupRightL l r).map (whL (coverWord v) (coverWord u))) :
          Q.obj (ob W (o - μ) (coverWord (u ++ redCupBottom r ++ v))) ⟶
          Q.obj (ob W (o - μ) (coverWord (u ++ redCupTop l r ++ v)))) ≫
          eqToHom e₂ := by
  obtain ⟨h₁, x₁, x₂, he₁⟩ :=
    coverLin_moveDiagram_dgC W hC o Q coverSign μ (u ++ [.inr r]) (.black (.cup l)) v
  obtain ⟨h₂, x₃, x₄, he₂⟩ :=
    coverLin_moveDiagram_dgC W hC o Q coverSign μ u (.redBlack r l) (.inl l.dual :: v)
  simp only [redCupRight]
  rw [LinDiagram.of_comp, coverLin_comp, coverLin_cast, coverLin_cast, he₁, he₂]
  have hs₁ : coverSign (k := k) (ℓ := ℓ) (.black (.cup l)) = 1 := rfl
  have hs₂ : coverSign (k := k) (ℓ := ℓ) (.redBlack r l) = 1 := rfl
  rw [hs₁, hs₂, one_smul, one_smul]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  refine eqToHom_dgC_comp W Q ?_ ?_ rfl ?_ h₁ h₂ ?_ _ _ _ _ _
  · simp [coverWord_cons, coverWord_append, coverLetter_inr, Move.bottom]
  · simp [coverWord_cons, coverWord_append, coverLetter_inr, Move.top, Move.bottom]
  · simp [coverWord_cons, coverWord_append, coverLetter_inr, Move.top]
  · have hc : coverMoveL (.black (.cup l) : Move I ℓ) = [([], .cup (l.1, .inl l.2), [])] := rfl
    simp [hc, redCupRightL, coverWord_cons, coverWord_append, coverLetter_inr, whL, List.map_map,
      Function.comp_def]

/-- **The red cup relations vanish after the cover functor** in every presentation with the
pivotal zigzag identities. -/
theorem coverLin_redCupRel (hz : Q.PivotalZigzags (inv W).toColourDuality)
    (a : RedCapRelation X I ℓ) :
    coverLin W hC o Q coverSign
      (LinDiagram.of (redCupLeft RD Λ a.leftWeight a.left a.black a.red a.right) -
        LinDiagram.of (redCupRight RD Λ a.leftWeight a.left a.black a.red a.right)) = 0 := by
  obtain ⟨μ, u, l, r, v⟩ := a
  rw [show ∀ {a b} (f g : LinDiagram k a b), coverLin W hC o Q coverSign (f - g) =
      coverLin W hC o Q coverSign f - coverLin W hC o Q coverSign g from fun f g => by
    simp only [coverLin, freeLift_map_layerLin, Functor.map_sub], sub_eq_zero]
  have e₁ := congrArg Q.obj (coverObj W hC o μ (u ++ redCupBottom r ++ v))
  have e₂ := (congrArg Q.obj (coverObj W hC o μ (u ++ redCupTop l r ++ v))).symm
  rw [coverLin_redCupLeft W hC o Q μ u l r v e₁ e₂,
    coverLin_redCupRight W hC o Q μ u l r v e₁ e₂]
  congr 2
  exact dgC_step Q (o - μ) [] [] (coverWord v) (coverWord u)
    (redCupLeftL_eq_redCupRightL W Q hz _ l r)
    (by simp [SChain, coverWord_cons, coverWord_append, coverLetter_inr])
    (by simp [SChain, coverWord_cons, coverWord_append, coverLetter_inr]) (by simp) (by simp)

end Categorification.Stendhal.DoubleDiagram

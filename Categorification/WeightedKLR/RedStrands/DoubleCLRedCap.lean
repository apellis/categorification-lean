/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLRedCup
import Categorification.WeightedKLR.RedStrands.DoubleRedCap

/-!
# The red cap relations after the cover functor

Webster, arXiv:1309.3796v3, §4.5, Definition 4.24, and §4.6, proof of Lemma 4.29. The red cap
relation of `addRedCapRelations` slides a black cap through a red strand. After reflection it
becomes a sideways crossing of an upward red strand with a black cap, and the two sides agree by
the interchange law and one zigzag identity (`redCap_reflect_up`, `redCap_reflect_dn`). Hence
the relation vanishes after the cover functor in every presentation with the pivotal zigzag
identities (`coverLin_redCapRel`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram.CL

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe u v w
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {k : Type w} [CommRing k]
  (P : Presentation.{w, max u v} (psig RD) k)

/-- A cap of colour `dn b` slides through an upward strand of colour `a`, the sideways crossing
being written as a mate. -/
theorem redCap_reflect_dn (hz : P.PivotalZigzags (inv RD).toColourDuality) (ν : X) (a b : I) :
    dgC P ν [up b, up a, dn b] [up a]
        [([up b], .cup (dn b), [up a, dn b]), ([up b, dn b], .cross true b a, [dn b]),
          ([up b, dn b, up a], .cap (dn b), []), ([], .cap (dn b), [up a])] =
      dgC P ν [up b, up a, dn b] [up a]
        [([], .cross true b a, [dn b]), ([up a], .cap (dn b), [])] := by
  dswapC 2
  dswapC 1
  datC 0 [] [up a, dn b] (dgC_zigR' P hz (wt RD ν [up a, dn b]) (dn b))

/-- A cap of colour `up b` slides through an upward strand of colour `a`, the sideways crossing
being written as a mate. -/
theorem redCap_reflect_up (hz : P.PivotalZigzags (inv RD).toColourDuality) (ν : X) (a b : I) :
    dgC P ν [dn b, up a, up b] [up a]
        [([dn b, up a], .cup (up b), [up b]), ([dn b], .cross true a b, [dn b, up b]),
          ([], .cap (up b), [up a, dn b, up b]), ([up a], .cap (up b), [])] =
      dgC P ν [dn b, up a, up b] [up a]
        [([dn b], .cross true a b, []), ([], .cap (up b), [up a])] := by
  dswapC 2
  dswapC 1
  datC 0 [dn b, up a] [] (dgC_zigL' P hz (wt RD ν []) (up b))

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

variable (Q : Presentation.{w, max u v} (psig W) k)

/-- The reflected left-hand side of the red cap relation: a sideways crossing of the red strand
with the left end of a black cap, then the cap to the right of the red strand. -/
def redCapLeftL (l : Letter I) (r : Fin ℓ) : List (LayerData (I ⊕ Fin ℓ)) :=
  (coverMoveL (.redBlack r l)).map (whL [] [coverLetter (.inl l.dual)]) ++
    [([(true, .inr r)], .cap (l.1, .inl l.2), [])]

/-- The reflected right-hand side of the red cap relation: a sideways crossing of the red strand
with the right end of a black cap, then the cap to the left of the red strand. -/
def redCapRightL (l : Letter I) (r : Fin ℓ) : List (LayerData (I ⊕ Fin ℓ)) :=
  (coverMoveL (.blackRed l.dual r)).map (whL [coverLetter (.inl l)] []) ++
    [([], .cap (l.1, .inl l.2), [(true, .inr r)])]

theorem redCapLeftL_eq_redCapRightL (hz : Q.PivotalZigzags (inv W).toColourDuality) (ν : X)
    (l : Letter I) (r : Fin ℓ) :
    dgC Q ν [coverLetter (.inl l), (true, .inr r), coverLetter (.inl l.dual)] [(true, .inr r)]
        (redCapLeftL l r) =
      dgC Q ν [coverLetter (.inl l), (true, .inr r), coverLetter (.inl l.dual)] [(true, .inr r)]
        (redCapRightL l r) := by
  rcases l with ⟨_ | _, j⟩
  · exact (redCap_reflect_dn Q hz ν (.inr r) (.inl j)).symm
  · exact redCap_reflect_up Q hz ν (.inr r) (.inl j)

/-- The top boundary of the red cap relations. -/
abbrev redCapTop (r : Fin ℓ) : List (DoubleStrand I ℓ) := [.inr r]

/-- The bottom boundary of the red cap relations. -/
abbrev redCapBottom (l : Letter I) (r : Fin ℓ) : List (DoubleStrand I ℓ) :=
  [.inl l.dual, .inr r, .inl l]

variable [DecidableEq I]

/-- The cover functor on the left-hand side of the red cap relation. -/
theorem coverLin_redCapLeft (μ : X) (u : List (DoubleStrand I ℓ)) (l : Letter I) (r : Fin ℓ)
    (v : List (DoubleStrand I ℓ))
    (e₁ : Q.obj ((κ).obj ((CM).obj (obj RD Λ μ (u ++ redCapBottom l r ++ v)))) =
        Q.obj (ob W (o - μ) (coverWord (u ++ redCapBottom l r ++ v))))
    (e₂ : Q.obj (ob W (o - μ) (coverWord (u ++ redCapTop r ++ v))) =
        Q.obj ((κ).obj ((CM).obj (obj RD Λ μ (u ++ redCapTop r ++ v))))) :
      coverLin W hC o Q coverSign (LinDiagram.of (redCapLeft RD Λ μ u l r v)) =
        eqToHom e₁ ≫ (dgC Q (o - μ) (coverWord (u ++ redCapBottom l r ++ v))
          (coverWord (u ++ redCapTop r ++ v))
          ((redCapLeftL l r).map (whL (coverWord v) (coverWord u))) :
          Q.obj (ob W (o - μ) (coverWord (u ++ redCapBottom l r ++ v))) ⟶
          Q.obj (ob W (o - μ) (coverWord (u ++ redCapTop r ++ v)))) ≫
          eqToHom e₂ := by
  obtain ⟨h₁, x₁, x₂, he₁⟩ :=
    coverLin_moveDiagram_dgC W hC o Q coverSign μ (u ++ [.inl l.dual]) (.redBlack r l) v
  obtain ⟨h₂, x₃, x₄, he₂⟩ :=
    coverLin_moveDiagram_dgC W hC o Q coverSign μ u (.black (.cap l)) (.inr r :: v)
  simp only [redCapLeft]
  rw [LinDiagram.of_comp, coverLin_comp, coverLin_cast, coverLin_cast, he₁, he₂]
  have hs₁ : coverSign (k := k) (ℓ := ℓ) (.redBlack r l) = 1 := rfl
  have hs₂ : coverSign (k := k) (ℓ := ℓ) (.black (.cap l)) = 1 := rfl
  rw [hs₁, hs₂, one_smul, one_smul]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  refine eqToHom_dgC_comp W Q ?_ ?_ rfl ?_ h₁ h₂ ?_ _ _ _ _ _
  · simp [coverWord_cons, coverWord_append, coverLetter_inr, Move.bottom]
  · simp [coverWord_cons, coverWord_append, coverLetter_inr, Move.top, Move.bottom]
  · simp [coverWord_cons, coverWord_append, coverLetter_inr, Move.top]
  · have hc : coverMoveL (.black (.cap l) : Move I ℓ) = [([], .cap (l.1, .inl l.2), [])] := rfl
    simp [hc, redCapLeftL, coverWord_cons, coverWord_append, coverLetter_inr, whL, List.map_map,
      Function.comp_def]

/-- The cover functor on the right-hand side of the red cap relation. -/
theorem coverLin_redCapRight (μ : X) (u : List (DoubleStrand I ℓ)) (l : Letter I) (r : Fin ℓ)
    (v : List (DoubleStrand I ℓ))
    (e₁ : Q.obj ((κ).obj ((CM).obj (obj RD Λ μ (u ++ redCapBottom l r ++ v)))) =
        Q.obj (ob W (o - μ) (coverWord (u ++ redCapBottom l r ++ v))))
    (e₂ : Q.obj (ob W (o - μ) (coverWord (u ++ redCapTop r ++ v))) =
        Q.obj ((κ).obj ((CM).obj (obj RD Λ μ (u ++ redCapTop r ++ v))))) :
      coverLin W hC o Q coverSign (LinDiagram.of (redCapRight RD Λ μ u l r v)) =
        eqToHom e₁ ≫ (dgC Q (o - μ) (coverWord (u ++ redCapBottom l r ++ v))
          (coverWord (u ++ redCapTop r ++ v))
          ((redCapRightL l r).map (whL (coverWord v) (coverWord u))) :
          Q.obj (ob W (o - μ) (coverWord (u ++ redCapBottom l r ++ v))) ⟶
          Q.obj (ob W (o - μ) (coverWord (u ++ redCapTop r ++ v)))) ≫
          eqToHom e₂ := by
  obtain ⟨h₁, x₁, x₂, he₁⟩ :=
    coverLin_moveDiagram_dgC W hC o Q coverSign μ u (.blackRed l.dual r) (.inl l :: v)
  obtain ⟨h₂, x₃, x₄, he₂⟩ :=
    coverLin_moveDiagram_dgC W hC o Q coverSign μ (u ++ [.inr r]) (.black (.cap l)) v
  simp only [redCapRight]
  rw [LinDiagram.of_comp, coverLin_comp, coverLin_cast, coverLin_cast, he₁, he₂]
  have hs₁ : coverSign (k := k) (ℓ := ℓ) (.blackRed l.dual r) = 1 := rfl
  have hs₂ : coverSign (k := k) (ℓ := ℓ) (.black (.cap l)) = 1 := rfl
  rw [hs₁, hs₂, one_smul, one_smul]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  refine eqToHom_dgC_comp W Q ?_ ?_ rfl ?_ h₁ h₂ ?_ _ _ _ _ _
  · simp [coverWord_cons, coverWord_append, coverLetter_inr, Move.bottom]
  · simp [coverWord_cons, coverWord_append, coverLetter_inr, Move.top, Move.bottom]
  · simp [coverWord_cons, coverWord_append, coverLetter_inr, Move.top]
  · have hc : coverMoveL (.black (.cap l) : Move I ℓ) = [([], .cap (l.1, .inl l.2), [])] := rfl
    simp [hc, redCapRightL, coverWord_cons, coverWord_append, coverLetter_inr, whL, List.map_map,
      Function.comp_def]

/-- **The red cap relations vanish after the cover functor** in every presentation with the
pivotal zigzag identities. -/
theorem coverLin_redCapRel (hz : Q.PivotalZigzags (inv W).toColourDuality)
    (a : RedCapRelation X I ℓ) :
    coverLin W hC o Q coverSign
      (LinDiagram.of (redCapLeft RD Λ a.leftWeight a.left a.black a.red a.right) -
        LinDiagram.of (redCapRight RD Λ a.leftWeight a.left a.black a.red a.right)) = 0 := by
  obtain ⟨μ, u, l, r, v⟩ := a
  rw [show ∀ {a b} (f g : LinDiagram k a b), coverLin W hC o Q coverSign (f - g) =
      coverLin W hC o Q coverSign f - coverLin W hC o Q coverSign g from fun f g => by
    simp only [coverLin, freeLift_map_layerLin, Functor.map_sub], sub_eq_zero]
  have e₁ := congrArg Q.obj (coverObj W hC o μ (u ++ redCapBottom l r ++ v))
  have e₂ := (congrArg Q.obj (coverObj W hC o μ (u ++ redCapTop r ++ v))).symm
  rw [coverLin_redCapLeft W hC o Q μ u l r v e₁ e₂,
    coverLin_redCapRight W hC o Q μ u l r v e₁ e₂]
  congr 2
  exact dgC_step Q (o - μ) [] [] (coverWord v) (coverWord u)
    (redCapLeftL_eq_redCapRightL W Q hz _ l r)
    (by simp [SChain, coverWord_cons, coverWord_append, coverLetter_inr])
    (by simp [SChain, coverWord_cons, coverWord_append, coverLetter_inr]) (by simp) (by simp)

end Categorification.Stendhal.DoubleDiagram

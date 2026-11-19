/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLRedUp
import Categorification.Diagrams.CL.Rotate

/-!
# The cover functor on a move in context

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29. A single double move placed between
two words of double strands is sent by the cover functor to the KL diagram of the reflected
move, placed between the reflections of the two words (in the opposite order) and rescaled by
the weight of the move (`coverLin_moveDiagram_ctx`). The result is stated through the normal
forms `dgC` of `KL3.Diagram.CL`, so that the images of the relations of the double diagrams
can be computed with the slide calculus.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams TwoRep

universe w u v

/-- A scaled, whiskered diagram image is the scaled image of any diagram with the whiskered
layers. -/
theorem whisk_layers {S : Signature} {R : Type*} [CommRing R] (Q : Presentation S R)
    {x y a b : Obj S} (r : R) (e2 : Q.obj x = Q.obj a) (d₀ : a ⟶ b) (e3 : Q.obj b = Q.obj y)
    (u : Obj S) (v : List S.Colour) (hw : a.WhiskerOK u v) {a' b' a'' b'' : Obj S}
    (d' : a' ⟶ b') (hL : (Diagram.layers d₀).map (·.whisker u v) = Diagram.layers d')
    {z z' : Obj S} (e0 : Q.obj a'' = Q.obj z) (e1 : Q.obj z = Q.obj (x.whisker u v))
    (e4 : Q.obj (y.whisker u v) = Q.obj z') (e5 : Q.obj z' = Q.obj b'')
    (f1 : Q.obj a'' = Q.obj a') (f2 : Q.obj b' = Q.obj b'') :
    eqToHom e0 ≫ (eqToHom e1 ≫ Q.whisk (r • (eqToHom e2 ≫ Q.diag d₀ ≫ eqToHom e3)) u v ≫
      eqToHom e4) ≫ eqToHom e5 = r • (eqToHom f1 ≫ Q.diag d' ≫ eqToHom f2) := by
  obtain rfl := Q.obj_injective e2
  obtain rfl := Q.obj_injective e3
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rw [Q.whisk_smul, Q.whisk_diag _ _ _ hw,
    Q.diag_eq_of_layers_eq' (Diagram.whisker d₀ u v hw) d'
      (Q.obj_injective ((e0.trans e1).symm.trans f1)) (Q.obj_injective ((e4.trans e5).trans f2.symm))
      (by rw [Diagram.layers_whisker, hL])]
  simp

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {C' : CartanDatum (I ⊕ Fin ℓ)}
  {X Y : Type v} [AddCommGroup X] [AddCommGroup Y] (W : WeightDatum C' X Y)
  (hC : ∀ i j, C'.dot (.inl i) (.inl j) = C.dot i j) (o : X)
  {k : Type w} [CommRing k] {v' : Type*}

local notation "RD" => blackDatum W hC
local notation "Λ" => redWeight W
local notation "κ" => coverColourMap W hC o
local notation "CM" => coverMirror W hC o

/-- The layers of the KL diagram of a reflected double move. -/
def coverMoveL : Move I ℓ → List (LayerData (I ⊕ Fin ℓ))
  | .black (.dot l) => [([], .dot (!l.1, .inl l.2), [])]
  | .black (.cross ε i j) => [([], .cross (!ε) (.inl j) (.inl i), [])]
  | .black (.cup l) => [([], .cup (l.1, .inl l.2), [])]
  | .black (.cap l) => [([], .cap (l.1, .inl l.2), [])]
  | .blackRed (false, j) r => [([], .cross true (.inr r) (.inl j), [])]
  | .blackRed (true, j) r => crosslL (.inr r) (.inl j)
  | .redBlack r (false, j) => [([], .cross true (.inl j) (.inr r), [])]
  | .redBlack r (true, j) => crossrL (.inr r) (.inl j)

/-- The KL diagram of a reflected move is the normal-form diagram of its layers. -/
theorem coverMove_eq_mkD (ν : X) (m : Move I ℓ) :
    ∃ h : SChain (coverWord m.bottom) (coverMoveL m) (coverWord m.top),
      coverMove W ν m = mkD W ν (coverMoveL m) h := by
  rcases m with ((l | ⟨ε, i, j⟩ | l | l) | ⟨⟨_ | _, j⟩, r⟩ | ⟨r, ⟨_ | _, j⟩⟩) <;>
    exact ⟨by first
      | exact ⟨rfl, rfl⟩
      | exact ⟨rfl, rfl, rfl, rfl⟩
      | exact ⟨rfl, by simp [coverWord, coverLetter, Move.top, Letter.dual]⟩
      | exact ⟨by simp [coverWord, coverLetter, Move.bottom, Letter.dual], rfl⟩, rfl⟩

variable (Q : Presentation.{w, v'} (psig W) k) (σ : Move I ℓ → k)

theorem coverMirror_left (μ : X) (u : List (DoubleStrand I ℓ)) (m : Move I ℓ)
    (v : List (DoubleStrand I ℓ)) :
    (κ).obj ⟨((CM).toLayerMap.layer (layer RD Λ μ u m v)).start,
      ((CM).toLayerMap.layer (layer RD Λ μ u m v)).left⟩ =
      ob W (wt W (wt W (o - μ) (coverWord u)) (coverWord m.bottom)) (coverWord v) := by
  have e : wt W (wt W (o - μ) (coverWord u)) (coverWord m.bottom) =
      o - endWeight RD Λ (endWeight RD Λ μ u) m.bottom := by
    rw [← wt_append, ← coverWord_append, wt_coverWord W hC, endWeight_append]
  refine Obj.ext ?_ ?_
  · change @HSub.hSub X X X _ o ((signature RD Λ).endR
      ((endWeight RD Λ (endWeight RD Λ μ u) m.bottom : X)) (colours RD Λ _ v)) = _
    rw [colours_endR, e]
    exact (wt_coverWord W hC o _ v).symm.trans rfl
  · change ((colours RD Λ _ v).map (coverColour o)).reverse = _
    rw [e]
    exact coverColours W hC o _ v

theorem coverMirror_right (μ : X) (u : List (DoubleStrand I ℓ)) (m : Move I ℓ)
    (v : List (DoubleStrand I ℓ)) :
    (κ).word ((CM).toLayerMap.layer (layer RD Λ μ u m v)).right = wd W (o - μ) (coverWord u) :=
  coverColours W hC o μ u

theorem coverObj (μ : X) (w : List (DoubleStrand I ℓ)) :
    (κ).obj ((CM).obj (obj RD Λ μ w)) = ob W (o - μ) (coverWord w) :=
  Obj.ext ((congrArg (fun x : X => o - x) (colours_endR RD Λ μ w)).trans
    (wt_coverWord W hC o μ w).symm) (coverColours W hC o μ w)

omit [AddCommGroup Y] in
theorem coverWord_append₃ (u b v : List (DoubleStrand I ℓ)) :
    coverWord (u ++ b ++ v) = coverWord v ++ coverWord b ++ coverWord u := by
  simp [coverWord_append]

/-- **The cover functor on a move in context.** A double move `m` between the words `u` and `v`
is sent to the KL diagram of the reflected move between the reflections of `v` and `u`, rescaled
by `σ m`. -/
theorem coverLin_moveDiagram_ctx (μ : X) (u : List (DoubleStrand I ℓ)) (m : Move I ℓ)
    (v : List (DoubleStrand I ℓ)) :
    ∃ (h : SChain (coverWord v ++ coverWord m.bottom ++ coverWord u)
        ((coverMoveL m).map (whL (coverWord v) (coverWord u)))
        (coverWord v ++ coverWord m.top ++ coverWord u))
      (e₁ : Q.obj ((κ).obj ((CM).obj (obj RD Λ μ (u ++ m.bottom ++ v)))) =
        Q.obj (ob W (o - μ) (coverWord v ++ coverWord m.bottom ++ coverWord u)))
      (e₂ : Q.obj (ob W (o - μ) (coverWord v ++ coverWord m.top ++ coverWord u)) =
        Q.obj ((κ).obj ((CM).obj (obj RD Λ μ (u ++ m.top ++ v))))),
      coverLin W hC o Q σ (LinDiagram.of (moveDiagram RD Λ μ u m v)) =
        σ m • (eqToHom e₁ ≫ Q.diag (mkD W (o - μ) _ h) ≫ eqToHom e₂) := by
  obtain ⟨h₀, hmk⟩ := coverMove_eq_mkD W (o - endWeight RD Λ μ u) m
  refine ⟨h₀.whisk _ _,
    congrArg Q.obj ((coverObj W hC o μ _).trans (by rw [coverWord_append₃])),
    congrArg Q.obj ((coverObj W hC o μ _).trans (by rw [coverWord_append₃])).symm, ?_⟩
  rw [coverLin, LayerMap.lin_of, LinDiagram.of, freeLift_map_single, one_smul]
  change eqToHom _ ≫ (eqToHom _ ≫
    Q.whisk (coverImage W hC o Q σ (endWeight RD Λ μ u, m)) _ _ ≫
      eqToHom _) ≫ eqToHom _ = _
  rw [coverImage]
  have hu := wt_coverWord W hC o μ u
  refine whisk_layers Q _ _ _ _ _ _ ?hw _ ?hL _ _ _ _ _ _
  case hw =>
    rw [coverMirror_left, coverMirror_right]
    rw [← hu]
    exact whiskerOK_ob W (o - μ) (coverWord v) (coverWord u) (coverWord m.bottom)
  case hL =>
    rw [coverMirror_left, coverMirror_right, hmk, layers_mkD, layers_mkD,
      ← layList_whisker W (o - μ) (coverWord v) (coverWord u) h₀, hu]

end Categorification.Stendhal.DoubleDiagram

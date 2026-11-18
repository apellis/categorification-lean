/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleBubbleRelations
import Categorification.WeightedKLR.RedStrands.DoubleRedCup

/-!
# A counterclockwise bubble crossing a red strand

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
§4.5, proof of Theorem 4.25, the red crossing mates and the red/black bigon
(4.2). For the physical counterclockwise bubble the down strand is on the
left. Sliding the mates across a red strand replaces the upward bigon on
the left by the downward bigon on the right. The latter puts the red
coroot multiplicity on the downward leg. With local left coroot coordinate
`n` and red multiplicity `δ`, the counterclockwise threshold increases from
`n - 1` to `n + δ - 1`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe w u v

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)

variable (μ : X) (L : List (DoubleStrand I ℓ)) (i : I) (r : Fin ℓ)
  (R : List (DoubleStrand I ℓ))

local notation "blackDown" => (Sum.inl (dn i) : DoubleStrand I ℓ)
local notation "blackUp" => (Sum.inl (up i) : DoubleStrand I ℓ)
local notation "redStrand" => (Sum.inr r : DoubleStrand I ℓ)
local notation "redObj" => obj RD Λ μ (L ++ [redStrand] ++ R)
local notation "leftObj" => obj RD Λ μ (L ++ [blackDown, blackUp, redStrand] ++ R)
local notation "middleObj" => obj RD Λ μ (L ++ [blackDown, redStrand, blackUp] ++ R)
local notation "rightObj" => obj RD Λ μ (L ++ [redStrand, blackDown, blackUp] ++ R)

private def cupLeft : redObj ⟶ leftObj :=
  Diagram.cast (moveDiagram RD Λ μ L (.black (.cup (dn i))) (redStrand :: R))
    (by simp [Move.bottom, List.append_assoc]) (by simp [Move.top, List.append_assoc])

private def cupRight : redObj ⟶ rightObj :=
  Diagram.cast (moveDiagram RD Λ μ (L ++ [redStrand]) (.black (.cup (dn i))) R)
    (by simp [Move.bottom]) (by simp [Move.top, List.append_assoc])

private def capLeft : leftObj ⟶ redObj :=
  Diagram.cast (moveDiagram RD Λ μ L (.black (.cap (up i))) (redStrand :: R))
    (by simp [Move.bottom, List.append_assoc]) (by simp [Move.top, List.append_assoc])

private def capRight : rightObj ⟶ redObj :=
  Diagram.cast (moveDiagram RD Λ μ (L ++ [redStrand]) (.black (.cap (up i))) R)
    (by simp [Move.bottom, List.append_assoc]) (by simp [Move.top])

private def upToMiddle : leftObj ⟶ middleObj :=
  Diagram.cast (moveDiagram RD Λ μ (L ++ [blackDown]) (.blackRed (up i) r) R)
    (by simp [Move.bottom, List.append_assoc]) (by simp [Move.top, List.append_assoc])

private def upFromMiddle : middleObj ⟶ leftObj :=
  Diagram.cast (moveDiagram RD Λ μ (L ++ [blackDown]) (.redBlack r (up i)) R)
    (by simp [Move.bottom, List.append_assoc]) (by simp [Move.top, List.append_assoc])

private def downToMiddle : rightObj ⟶ middleObj :=
  Diagram.cast (moveDiagram RD Λ μ L (.redBlack r (dn i)) (blackUp :: R))
    (by simp [Move.bottom, List.append_assoc]) (by simp [Move.top, List.append_assoc])

private def downFromMiddle : middleObj ⟶ rightObj :=
  Diagram.cast (moveDiagram RD Λ μ L (.blackRed (dn i) r) (blackUp :: R))
    (by simp [Move.bottom, List.append_assoc]) (by simp [Move.top, List.append_assoc])

private def dotRight : End rightObj :=
  Diagram.cast (moveDiagram RD Λ μ (L ++ [redStrand]) (.black (.dot (dn i))) (blackUp :: R))
    (by simp [Move.bottom, List.append_assoc]) (by simp [Move.top, List.append_assoc])

private def dotLeft : End leftObj :=
  Diagram.cast (moveDiagram RD Λ μ L (.black (.dot (dn i))) (blackUp :: redStrand :: R))
    (by simp [Move.bottom, List.append_assoc]) (by simp [Move.top, List.append_assoc])

private def dotMiddle : End middleObj :=
  Diagram.cast (moveDiagram RD Λ μ L (.black (.dot (dn i))) (redStrand :: blackUp :: R))
    (by simp [Move.bottom, List.append_assoc]) (by simp [Move.top, List.append_assoc])

/-- A real counterclockwise bubble to the left of the chosen red strand. -/
def ccwBubbleBeforeRed (m : ℕ) : End redObj :=
  Diagram.cast (blackDiagram RD Λ μ L (redStrand :: R) (cwReal RD (endWeight RD Λ μ L) i m))
    (by simp [blackWord, List.append_assoc]) (by simp [blackWord, List.append_assoc])

/-- A real counterclockwise bubble to the right of the chosen red strand. -/
def ccwBubbleAfterRed (m : ℕ) : End redObj :=
  Diagram.cast (blackDiagram RD Λ μ (L ++ [redStrand]) R
    (cwReal RD (endWeight RD Λ μ (L ++ [redStrand])) i m))
    (by simp [blackWord]) (by simp [blackWord])

private theorem layers_pow {S : Signature} {a : Obj S} (d : End a) :
    ∀ m : ℕ, Diagram.layers (d ^ m) = (List.replicate m (Diagram.layers d)).flatten
  | 0 => rfl
  | m + 1 => by
    rw [pow_succ]
    change Diagram.layers (d ≫ d ^ m) = _
    rw [Diagram.layers_comp, layers_pow d m, List.replicate_succ, List.flatten_cons]

private theorem ccwBubbleBeforeRed_factor (m : ℕ) :
    ccwBubbleBeforeRed RD Λ μ L i r R m =
      cupLeft RD Λ μ L i r R ≫ (dotLeft RD Λ μ L i r R ^ m) ≫ capLeft RD Λ μ L i r R := by
  apply Diagram.ext
  rw [ccwBubbleBeforeRed, Diagram.layers_cast]
  change Diagram.layers (blackDiagram RD Λ μ L (redStrand :: R)
    (BubbleOrientation.counterclockwise.beforeReflection RD (endWeight RD Λ μ L) i m)) = _
  rw [realBubble_layers]
  simp only [Diagram.layers_comp, layers_pow, cupLeft, dotLeft, capLeft, Diagram.layers_cast,
    moveDiagram, Diagram.layers_layer, List.flatten_replicate_singleton]
  rfl

private theorem ccwBubbleAfterRed_factor (m : ℕ) :
    ccwBubbleAfterRed RD Λ μ L i r R m =
      cupRight RD Λ μ L i r R ≫ (dotRight RD Λ μ L i r R ^ m) ≫ capRight RD Λ μ L i r R := by
  apply Diagram.ext
  rw [ccwBubbleAfterRed, Diagram.layers_cast]
  change Diagram.layers (blackDiagram RD Λ μ (L ++ [redStrand]) R
    (BubbleOrientation.counterclockwise.beforeReflection RD (endWeight RD Λ μ (L ++ [redStrand])) i m)) = _
  rw [realBubble_layers]
  simp only [Diagram.layers_comp, layers_pow, cupRight, dotRight, capRight, Diagram.layers_cast,
    moveDiagram, Diagram.layers_layer, List.flatten_replicate_singleton]
  rfl

private theorem diag_eq_addRels {S : Signature} {k : Type w} [CommRing k]
    (P : Presentation.{w, v} S k) {J : Type v} {dom cod : J → Obj S}
    {rel : ∀ j, LinDiagram k (dom j) (cod j)} {a b : Obj S} {f g : a ⟶ b}
    (h : P.diag f = P.diag g) :
    (P.addRels J dom cod rel).diag f = (P.addRels J dom cod rel).diag g := by
  simp only [Presentation.diag, Presentation.lin_eq_iff] at h ⊢
  refine Submodule.span_mono ?_ h
  rintro _ ⟨x, l, r, hw, pre, post⟩
  cases x with
  | user j =>
    exact Presentation.IdealGen.intro (P := P.addRels J dom cod rel)
      (.user (Sum.inl j)) l r hw pre post
  | interchange x hx =>
    exact Presentation.IdealGen.intro (P := P.addRels J dom cod rel)
      (.interchange x hx) l r hw pre post

private theorem diag_cast_eq {S : Signature} {k : Type w} [CommRing k]
    (P : Presentation S k) {a b a' b' : Obj S} {f g : a ⟶ b} (ha : a = a') (hb : b = b')
    (h : P.diag f = P.diag g) :
    P.diag (Diagram.cast f ha hb) = P.diag (Diagram.cast g ha hb) := by
  subst a' b'
  simpa only [Diagram.cast_rfl] using h

private theorem diag_pow {S : Signature} {k : Type w} [CommRing k]
    (P : Presentation S k) {a : Obj S} (f : End a) (n : ℕ) :
    P.diag (f ^ n) = End.of (P.diag f) ^ n :=
  let F : Obj S ⥤ P.Presented := ⟨P.obj, P.diag, P.diag_id, P.diag_comp⟩
  map_pow (F.mapEnd (X := a)) f n

variable {k : Type w} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin ℓ → I →₀ ℕ)
  (P : Presentation.{w, max u v} (signature RD Λ) k)

local notation "Pmates" => addRedCapRelations RD Λ (addRedCupRelations RD Λ P)
local notation "Pup" => addRedUpRelations RD Λ k (Pmates)
local notation "Pslide" => addDownRelations RD Λ (affineCoverQ Q exponents) (Pup)

private theorem upBigon :
    (Pslide).diag (upToMiddle RD Λ μ L i r R ≫ upFromMiddle RD Λ μ L i r R) = 𝟙 _ := by
  let b : End (obj RD Λ μ ((L ++ [blackDown]) ++ [blackUp, redStrand] ++ R)) :=
    moveDiagram RD Λ μ (L ++ [blackDown]) (.blackRed (up i) r) R ≫
    moveDiagram RD Λ μ (L ++ [blackDown]) (.redBlack r (up i)) R
  have he : obj RD Λ μ ((L ++ [blackDown]) ++ [blackUp, redStrand] ++ R) = leftObj := by
    simp [List.append_assoc]
  have hb : (Pup).diag b = (Pup).diag (𝟙 _) := by
    simp only [b, Presentation.diag_comp, Presentation.diag_id]
    exact (redUpCrossingIso RD Λ (Pmates) μ (L ++ [blackDown]) r i R).inv_hom_id
  have hc := diag_cast_eq (Pup) he he hb
  have hcast : Diagram.cast (𝟙 _) he he = 𝟙 leftObj := Diagram.ext rfl
  have hmove : Diagram.cast b he he =
      upToMiddle RD Λ μ L i r R ≫ upFromMiddle RD Λ μ L i r R := Diagram.ext rfl
  have hbase := (congrArg ((Pup).diag (a := leftObj) (b := leftObj)) hmove.symm).trans
    (hc.trans (congrArg ((Pup).diag (a := leftObj) (b := leftObj)) hcast))
  exact (diag_eq_addRels (Pup) hbase).trans ((Pslide).diag_id _)

private theorem downBigon :
    (Pslide).diag (downToMiddle RD Λ μ L i r R ≫ downFromMiddle RD Λ μ L i r R) =
      (Pslide).diag (dotRight RD Λ μ L i r R ^ exponents r i) := by
  let b := moveDiagram RD Λ μ L (.redBlack r (dn i)) (blackUp :: R) ≫
    moveDiagram RD Λ μ L (.blackRed (dn i) r) (blackUp :: R)
  let e := redDownDotRedLeft RD Λ μ L r i (blackUp :: R)
  have he : obj RD Λ μ (L ++ [redStrand, blackDown] ++ blackUp :: R) = rightObj := by
    simp [List.append_assoc]
  have hb : (Pslide).diag b = (Pslide).diag (e ^ exponents r i) :=
     (redDown_bigon_redLeft RD Λ Q exponents (Pup) μ L r i (blackUp :: R)).trans
       (diag_pow (Pslide) e (exponents r i)).symm
  have hc := diag_cast_eq (Pslide) he he hb
  have hd : Diagram.cast (e ^ exponents r i) he he = dotRight RD Λ μ L i r R ^ exponents r i := by
    apply Diagram.ext
    simp only [Diagram.layers_cast, layers_pow]
    rfl
  rwa [hd, ← show downToMiddle RD Λ μ L i r R ≫ downFromMiddle RD Λ μ L i r R =
      Diagram.cast b he he from Diagram.ext rfl] at hc

private theorem downCross_dot :
    (Pslide).diag (dotRight RD Λ μ L i r R) ≫ (Pslide).diag (downToMiddle RD Λ μ L i r R) =
      (Pslide).diag (downToMiddle RD Λ μ L i r R) ≫ (Pslide).diag (dotMiddle RD Λ μ L i r R) := by
  let c := moveDiagram RD Λ μ L (.redBlack r (dn i)) (blackUp :: R)
  let d := redDownDotRedLeft RD Λ μ L r i (blackUp :: R)
  let e := redDownDotBlackLeft RD Λ μ L r i (blackUp :: R)
  have ha : obj RD Λ μ (L ++ [redStrand, blackDown] ++ blackUp :: R) = rightObj := by
    simp [List.append_assoc]
  have hb : obj RD Λ μ (L ++ [blackDown, redStrand] ++ blackUp :: R) = middleObj := by
    simp [List.append_assoc]
  have h : (Pslide).diag (d ≫ c) = (Pslide).diag (c ≫ e) := by
    simp only [c, d, e, Presentation.diag_comp]
    exact (redDown_dot_slide_redLeft RD Λ Q exponents (Pup) μ L r i (blackUp :: R)).symm
  have hs := diag_cast_eq (Pslide) ha hb h
  have h₁ : Diagram.cast (d ≫ c) ha hb =
      dotRight RD Λ μ L i r R ≫ downToMiddle RD Λ μ L i r R := Diagram.ext rfl
  have h₂ : Diagram.cast (c ≫ e) ha hb =
      downToMiddle RD Λ μ L i r R ≫ dotMiddle RD Λ μ L i r R := Diagram.ext rfl
  simpa only [h₁, h₂, Presentation.diag_comp] using hs

private theorem upCross_dot :
    (Pslide).diag (dotLeft RD Λ μ L i r R) ≫ (Pslide).diag (upToMiddle RD Λ μ L i r R) =
      (Pslide).diag (upToMiddle RD Λ μ L i r R) ≫ (Pslide).diag (dotMiddle RD Λ μ L i r R) := by
  rw [← Presentation.diag_comp, ← Presentation.diag_comp]
  let η := endWeight RD Λ μ L
  let ξ := endWeight RD Λ (endWeight RD Λ μ L) [blackDown]
  let tail := colours RD Λ (endWeight RD Λ ξ [blackUp, redStrand]) R
  apply (Pslide).diag_interchange_of_layers_of_even μ (colours RD Λ μ L) [] tail
    (η, .black (.dot (dn i))) (ξ, .blackRed (up i) r) (Or.inl rfl)
  all_goals
    simp [dotLeft, dotMiddle, upToMiddle, moveDiagram, layer, signature, η, ξ, tail,
      Move.bottom, Move.top, Shape.dom, Shape.cod, colours, colours_append,
      endWeight, DoubleStrand.weight, add_assoc, add_left_comm, add_comm]

private theorem commute_pow {D : Type*} [Category* D] {a b : D} (f : a ⟶ b)
    (x : End a) (y : End b) (h : x ≫ f = f ≫ y) :
    ∀ m : ℕ, (x ^ m) ≫ f = f ≫ (y ^ m)
  | 0 => by simp
  | m + 1 => by
    rw [pow_succ, pow_succ]
    change (x ≫ x ^ m) ≫ f = f ≫ (y ≫ y ^ m)
    rw [Category.assoc, commute_pow f x y h m, ← Category.assoc, h, Category.assoc]

/-- A real counterclockwise bubble to the left of a red strand equals the
counterclockwise bubble to its right with the red multiplicity added to the dot count.
The cup and cap mates in Webster, arXiv:1309.3796v2, proof of Theorem 4.25,
give this shift from (4.2) and (4.4e). -/
theorem ccwBubble_slide (m : ℕ) :
    (Pslide).diag (ccwBubbleBeforeRed RD Λ μ L i r R m) =
      (Pslide).diag (ccwBubbleAfterRed RD Λ μ L i r R (m + exponents r i)) := by
  have hcup : (Pslide).diag (cupLeft RD Λ μ L i r R ≫ upToMiddle RD Λ μ L i r R) =
      (Pslide).diag (cupRight RD Λ μ L i r R ≫ downToMiddle RD Λ μ L i r R) :=
    (Pslide).diag_eq_of_rel (.inl (.inl (.inl (.inr ⟨μ, L, dn i, r, R⟩)))) rfl
  have hcap : (Pslide).diag (upFromMiddle RD Λ μ L i r R ≫ capLeft RD Λ μ L i r R) =
      (Pslide).diag (downFromMiddle RD Λ μ L i r R ≫ capRight RD Λ μ L i r R) :=
    (Pslide).diag_eq_of_rel (.inl (.inl (.inr ⟨μ, L, up i, r, R⟩))) rfl
  have h := congrArg₂ (fun f g => f ≫ (Pslide).diag (dotMiddle RD Λ μ L i r R ^ m) ≫ g) hcup hcap
  simp only [Presentation.diag_comp, Category.assoc] at h
  have hpowL : (Pslide).diag (dotLeft RD Λ μ L i r R ^ m) ≫
      (Pslide).diag (upToMiddle RD Λ μ L i r R) =
      (Pslide).diag (upToMiddle RD Λ μ L i r R) ≫
        (Pslide).diag (dotMiddle RD Λ μ L i r R ^ m) := by
    simp only [diag_pow]
    exact commute_pow _ _ _ (upCross_dot RD Λ μ L i r R Q exponents P) m
  have hpowR : (Pslide).diag (dotRight RD Λ μ L i r R ^ m) ≫
      (Pslide).diag (downToMiddle RD Λ μ L i r R) =
      (Pslide).diag (downToMiddle RD Λ μ L i r R) ≫
        (Pslide).diag (dotMiddle RD Λ μ L i r R ^ m) := by
    simp only [diag_pow]
    exact commute_pow _ _ _ (downCross_dot RD Λ μ L i r R Q exponents P) m
  have ha := congrArg (fun f => f ≫ (Pslide).diag (upFromMiddle RD Λ μ L i r R) ≫
    (Pslide).diag (capLeft RD Λ μ L i r R)) hpowL.symm
  have hb := congrArg (fun f => f ≫ (Pslide).diag (downFromMiddle RD Λ μ L i r R) ≫
    (Pslide).diag (capRight RD Λ μ L i r R)) hpowR.symm
  simp only [Category.assoc] at ha hb
  rw [ha, hb] at h
  have hu := upBigon RD Λ μ L i r R Q exponents P
  have hd := downBigon RD Λ μ L i r R Q exponents P
  simp only [Presentation.diag_comp] at hu hd
  have hleft : (Pslide).diag (upToMiddle RD Λ μ L i r R) ≫
      (Pslide).diag (upFromMiddle RD Λ μ L i r R) ≫ (Pslide).diag (capLeft RD Λ μ L i r R) =
      (Pslide).diag (capLeft RD Λ μ L i r R) := by
    rw [← Category.assoc, hu, Category.id_comp]
  have hright : (Pslide).diag (downToMiddle RD Λ μ L i r R) ≫
      (Pslide).diag (downFromMiddle RD Λ μ L i r R) ≫ (Pslide).diag (capRight RD Λ μ L i r R) =
      (Pslide).diag (dotRight RD Λ μ L i r R ^ exponents r i) ≫
        (Pslide).diag (capRight RD Λ μ L i r R) := by
    rw [← Category.assoc, hd]
  rw [hleft, hright] at h
  have hp : (Pslide).diag (dotRight RD Λ μ L i r R ^ m) ≫
      (Pslide).diag (dotRight RD Λ μ L i r R ^ exponents r i) =
      (Pslide).diag (dotRight RD Λ μ L i r R ^ (m + exponents r i)) := by
    rw [← Presentation.diag_comp]
    congr 1
    change dotRight RD Λ μ L i r R ^ exponents r i * dotRight RD Λ μ L i r R ^ m = _
    rw [← pow_add, Nat.add_comm]
  have hp' := congrArg (fun f => f ≫ (Pslide).diag (capRight RD Λ μ L i r R)) hp
  simp only [Category.assoc] at hp'
  rw [hp'] at h
  simpa only [ccwBubbleBeforeRed_factor, ccwBubbleAfterRed_factor, Presentation.diag_comp] using h

/-- The undotted instance of the real counterclockwise bubble shift. -/
theorem ccwBubble_slide_zero :
    (Pslide).diag (ccwBubbleBeforeRed RD Λ μ L i r R 0) =
      (Pslide).diag (ccwBubbleAfterRed RD Λ μ L i r R (exponents r i)) := by
  simpa only [zero_add] using ccwBubble_slide RD Λ μ L i r R Q exponents P 0

end Categorification.Stendhal.DoubleDiagram

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleRedBubble
import Categorification.WeightedKLR.RedStrands.DoubleBlackAdjunction

/-!
# A clockwise bubble crossing a red strand

Webster, arXiv:1309.3796v2 and v3, §4.5, proof of Theorem 4.25, and the
red/black bigon (4.2). A clockwise bubble to the right of a red strand slides
to its left, adding the coroot multiplicity to the downward leg. Dot
cyclicity identifies this representative with the one used in the black
bubble relations.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe w u v
variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)
  (μ : X) (L : List (DoubleStrand I ℓ)) (i : I) (r : Fin ℓ)
  (R : List (DoubleStrand I ℓ))

local notation "downStrand" => (Sum.inl (dn i) : DoubleStrand I ℓ)
local notation "upStrand" => (Sum.inl (up i) : DoubleStrand I ℓ)
local notation "λr" => (Sum.inr r : DoubleStrand I ℓ)
local notation "b₀" => obj RD Λ μ (L ++ [λr] ++ R)
local notation "bₗ" => obj RD Λ μ (L ++ [upStrand, downStrand, λr] ++ R)
local notation "bₘ" => obj RD Λ μ (L ++ [upStrand, λr, downStrand] ++ R)
local notation "bᵣ" => obj RD Λ μ (L ++ [λr, upStrand, downStrand] ++ R)

private def leftCup : b₀ ⟶ bₗ :=
  Diagram.cast (moveDiagram RD Λ μ L (.black (.cup (up i))) (λr :: R))
    (by simp [Move.bottom, List.append_assoc]) (by simp [Move.top, List.append_assoc])

private def rightCup : b₀ ⟶ bᵣ :=
  Diagram.cast (moveDiagram RD Λ μ (L ++ [λr]) (.black (.cup (up i))) R)
    (by simp [Move.bottom]) (by simp [Move.top, List.append_assoc])

private def leftCap : bₗ ⟶ b₀ :=
  Diagram.cast (moveDiagram RD Λ μ L (.black (.cap (dn i))) (λr :: R))
    (by simp [Move.bottom, List.append_assoc]) (by simp [Move.top, List.append_assoc])

private def rightCap : bᵣ ⟶ b₀ :=
  Diagram.cast (moveDiagram RD Λ μ (L ++ [λr]) (.black (.cap (dn i))) R)
    (by simp [Move.bottom, List.append_assoc]) (by simp [Move.top])

private def leftIn : bₗ ⟶ bₘ :=
  Diagram.cast (moveDiagram RD Λ μ (L ++ [upStrand]) (.blackRed (dn i) r) R)
    (by simp [Move.bottom, List.append_assoc]) (by simp [Move.top, List.append_assoc])

private def leftOut : bₘ ⟶ bₗ :=
  Diagram.cast (moveDiagram RD Λ μ (L ++ [upStrand]) (.redBlack r (dn i)) R)
    (by simp [Move.bottom, List.append_assoc]) (by simp [Move.top, List.append_assoc])

private def rightIn : bᵣ ⟶ bₘ :=
  Diagram.cast (moveDiagram RD Λ μ L (.redBlack r (up i)) (downStrand :: R))
    (by simp [Move.bottom, List.append_assoc]) (by simp [Move.top, List.append_assoc])

private def rightOut : bₘ ⟶ bᵣ :=
  Diagram.cast (moveDiagram RD Λ μ L (.blackRed (up i) r) (downStrand :: R))
    (by simp [Move.bottom, List.append_assoc]) (by simp [Move.top, List.append_assoc])

private def leftDot : End bₗ :=
  Diagram.cast (redDownDotBlackLeft RD Λ μ (L ++ [upStrand]) r i R)
    (by simp [List.append_assoc]) (by simp [List.append_assoc])

private def middleDot : End bₘ :=
  Diagram.cast (redDownDotRedLeft RD Λ μ (L ++ [upStrand]) r i R)
    (by simp [List.append_assoc]) (by simp [List.append_assoc])

private def rightDot : End bᵣ :=
  Diagram.cast (moveDiagram RD Λ μ (L ++ [λr, upStrand]) (.black (.dot (dn i))) R)
    (by simp [Move.bottom, List.append_assoc]) (by simp [Move.top, List.append_assoc])

/-- The clockwise bubble before the chosen red strand, with all dots on its
downward leg. -/
def clockwiseBubbleBeforeRed (m : ℕ) : End b₀ :=
  leftCup RD Λ μ L i r R ≫ (leftDot RD Λ μ L i r R ^ m) ≫ leftCap RD Λ μ L i r R

/-- The clockwise bubble after the chosen red strand, with all dots on its
downward leg. -/
def clockwiseBubbleAfterRed (m : ℕ) : End b₀ :=
  rightCup RD Λ μ L i r R ≫ (rightDot RD Λ μ L i r R ^ m) ≫ rightCap RD Λ μ L i r R

/-- The clockwise bubble to the left of the red strand in the black
bubble convention, with dots on its upward leg. -/
def cwBubbleBeforeRed (m : ℕ) : End b₀ :=
  Diagram.cast (blackDiagram RD Λ μ L (λr :: R) (ccwReal RD (endWeight RD Λ μ L) i m))
    (by simp [blackWord, List.append_assoc]) (by simp [blackWord, List.append_assoc])

/-- The clockwise bubble to the right of the red strand in the black
bubble convention, with dots on its upward leg. -/
def cwBubbleAfterRed (m : ℕ) : End b₀ :=
  Diagram.cast (blackDiagram RD Λ μ (L ++ [λr]) R
    (ccwReal RD (endWeight RD Λ μ (L ++ [λr])) i m))
    (by simp [blackWord]) (by simp [blackWord])

variable {k : Type w} [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)
  (exponents : Fin ℓ → I →₀ ℕ) (P : Presentation.{w, max u v} (signature RD Λ) k)

local notation "Pmates" => addRedCapRelations RD Λ (addRedCupRelations RD Λ P)
local notation "Pup" => addRedUpRelations RD Λ k (Pmates)
local notation "Pslide" => addDownRelations RD Λ (affineCoverQ Q exponents) (Pup)

private theorem diag_cast_eq {S : Signature} (A : Presentation S k)
    {a b a' b' : Obj S} {f g : a ⟶ b} (ha : a = a') (hb : b = b')
    (h : A.diag f = A.diag g) :
    A.diag (Diagram.cast f ha hb) = A.diag (Diagram.cast g ha hb) := by
  subst a' b'
  exact h

private theorem diag_pow {S : Signature} (A : Presentation S k) {a : Obj S} (f : End a)
    (n : ℕ) : A.diag (f ^ n) = End.of (A.diag f) ^ n :=
  let F : Obj S ⥤ A.Presented := ⟨A.obj, A.diag, A.diag_id, A.diag_comp⟩
  map_pow (F.mapEnd (X := a)) f n

private theorem leftIn_dot :
    (Pslide).diag (leftDot RD Λ μ L i r R) ≫ (Pslide).diag (leftIn RD Λ μ L i r R) =
      (Pslide).diag (leftIn RD Λ μ L i r R) ≫ (Pslide).diag (middleDot RD Λ μ L i r R) := by
  let c := moveDiagram RD Λ μ (L ++ [upStrand]) (.blackRed (dn i) r) R
  let x := redDownDotBlackLeft RD Λ μ (L ++ [upStrand]) r i R
  let y := redDownDotRedLeft RD Λ μ (L ++ [upStrand]) r i R
  have h : (Pslide).diag (x ≫ c) = (Pslide).diag (c ≫ y) := by
    simp only [Presentation.diag_comp, x, y, c]
    exact (redDown_dot_slide_blackLeft RD Λ Q exponents (Pup) μ (L ++ [upStrand]) r i R).symm
  let ha : obj RD Λ μ ((L ++ [upStrand]) ++ [downStrand, λr] ++ R) = bₗ := by simp [List.append_assoc]
  let hb : obj RD Λ μ ((L ++ [upStrand]) ++ [λr, downStrand] ++ R) = bₘ := by simp [List.append_assoc]
  have h₁ : Diagram.cast (x ≫ c) ha hb = leftDot RD Λ μ L i r R ≫ leftIn RD Λ μ L i r R :=
    Diagram.ext rfl
  have h₂ : Diagram.cast (c ≫ y) ha hb = leftIn RD Λ μ L i r R ≫ middleDot RD Λ μ L i r R :=
    Diagram.ext rfl
  simpa only [h₁, h₂, Presentation.diag_comp] using diag_cast_eq (Pslide) ha hb h

private theorem rightIn_dot :
    (Pslide).diag (rightDot RD Λ μ L i r R) ≫ (Pslide).diag (rightIn RD Λ μ L i r R) =
      (Pslide).diag (rightIn RD Λ μ L i r R) ≫ (Pslide).diag (middleDot RD Λ μ L i r R) := by
  rw [← Presentation.diag_comp, ← Presentation.diag_comp]
  let η := endWeight RD Λ μ L
  let ξ := endWeight RD Λ η [λr, upStrand]
  let tail := colours RD Λ (endWeight RD Λ ξ [downStrand]) R
  symm
  apply (Pslide).diag_interchange_of_layers_of_even μ (colours RD Λ μ L) [] tail
    (η, .redBlack r (up i)) (ξ, .black (.dot (dn i))) (Or.inl rfl)
  all_goals
    simp [rightDot, middleDot, redDownDotRedLeft, rightIn, moveDiagram, layer, signature, η, ξ, tail,
      Move.bottom, Move.top, Shape.dom, Shape.cod, colours, colours_append,
      endWeight, DoubleStrand.weight, add_assoc, add_left_comm, add_comm]

private theorem layers_pow {S : Signature} {a : Obj S} (f : End a) : ∀ m : ℕ,
    Diagram.layers (f ^ m) = (List.replicate m (Diagram.layers f)).flatten
  | 0 => rfl
  | m + 1 => by
    rw [pow_succ]
    change Diagram.layers (f ≫ f ^ m) = _
    rw [Diagram.layers_comp, layers_pow f m, List.replicate_succ, List.flatten_cons]

/-- The geometric clockwise loop on either side of red carries its dots on the downward leg. -/
theorem layers_clockwiseBubbleBeforeRed (m : ℕ) :
    Diagram.layers (clockwiseBubbleBeforeRed RD Λ μ L i r R m) =
      [layer RD Λ μ L (.black (.cup (up i))) (λr :: R)] ++
      List.replicate m (layer RD Λ μ (L ++ [upStrand]) (.black (.dot (dn i))) (λr :: R)) ++
      [layer RD Λ μ L (.black (.cap (dn i))) (λr :: R)] := by
  simp only [clockwiseBubbleBeforeRed, Diagram.layers_comp, layers_pow, leftCup, leftDot, leftCap,
    redDownDotBlackLeft, moveDiagram, Diagram.layers_cast, Diagram.layers_layer, List.flatten_replicate_singleton]
  rfl

theorem layers_clockwiseBubbleAfterRed (m : ℕ) :
    Diagram.layers (clockwiseBubbleAfterRed RD Λ μ L i r R m) =
      [layer RD Λ μ (L ++ [λr]) (.black (.cup (up i))) R] ++
      List.replicate m (layer RD Λ μ ((L ++ [λr]) ++ [upStrand]) (.black (.dot (dn i))) R) ++
      [layer RD Λ μ (L ++ [λr]) (.black (.cap (dn i))) R] := by
  simp only [clockwiseBubbleAfterRed, Diagram.layers_comp, layers_pow, rightCup, rightDot, rightCap,
    moveDiagram, Diagram.layers_cast, Diagram.layers_layer, List.flatten_replicate_singleton,
    List.append_assoc, List.singleton_append]
  rfl

private theorem left_bigon :
    (Pslide).diag (leftIn RD Λ μ L i r R ≫ leftOut RD Λ μ L i r R) =
      (Pslide).diag (leftDot RD Λ μ L i r R ^ exponents r i) := by
  let b := moveDiagram RD Λ μ (L ++ [upStrand]) (.blackRed (dn i) r) R ≫
    moveDiagram RD Λ μ (L ++ [upStrand]) (.redBlack r (dn i)) R
  let x := redDownDotBlackLeft RD Λ μ (L ++ [upStrand]) r i R
  have he : obj RD Λ μ ((L ++ [upStrand]) ++ [downStrand, λr] ++ R) = bₗ := by
    simp [List.append_assoc]
  have h : (Pslide).diag b = (Pslide).diag (x ^ exponents r i) :=
    (redDown_bigon_blackLeft RD Λ Q exponents (Pup) μ (L ++ [upStrand]) r i R).trans
      (diag_pow (Pslide) x (exponents r i)).symm
  have hb : Diagram.cast b he he = leftIn RD Λ μ L i r R ≫ leftOut RD Λ μ L i r R :=
    Diagram.ext rfl
  have hx : Diagram.cast (x ^ exponents r i) he he = leftDot RD Λ μ L i r R ^ exponents r i := by
    apply Diagram.ext
    simp only [Diagram.layers_cast, layers_pow]
    rfl
  simpa only [hb, hx] using diag_cast_eq (Pslide) he he h

private theorem diag_eq_addRels {S : Signature} (A : Presentation.{w, v} S k)
    {J : Type v} {dom cod : J → Obj S} {rel : ∀ j, LinDiagram k (dom j) (cod j)}
    {a b : Obj S} {f g : a ⟶ b} (h : A.diag f = A.diag g) :
    (A.addRels J dom cod rel).diag f = (A.addRels J dom cod rel).diag g := by
  simp only [Presentation.diag, Presentation.lin_eq_iff] at h ⊢
  refine Submodule.span_mono ?_ h
  rintro _ ⟨x, l, r, hw, pre, post⟩
  cases x with
  | user j =>
    exact Presentation.IdealGen.intro (P := A.addRels J dom cod rel)
      (.user (Sum.inl j)) l r hw pre post
  | interchange x hx =>
    exact Presentation.IdealGen.intro (P := A.addRels J dom cod rel)
      (.interchange x hx) l r hw pre post

private theorem right_bigon :
    (Pslide).diag (rightIn RD Λ μ L i r R ≫ rightOut RD Λ μ L i r R) = 𝟙 _ := by
  let b : End (obj RD Λ μ (L ++ [λr, upStrand] ++ downStrand :: R)) :=
    moveDiagram RD Λ μ L (.redBlack r (up i)) (downStrand :: R) ≫
    moveDiagram RD Λ μ L (.blackRed (up i) r) (downStrand :: R)
  have he : obj RD Λ μ (L ++ [λr, upStrand] ++ downStrand :: R) = bᵣ := by
    simp [List.append_assoc]
  have h : (Pup).diag b = (Pup).diag (𝟙 _) := by
    simp only [b, Presentation.diag_comp, Presentation.diag_id]
    exact (redUpCrossingIso RD Λ (Pmates) μ L r i (downStrand :: R)).hom_inv_id
  have hb : Diagram.cast b he he = rightIn RD Λ μ L i r R ≫ rightOut RD Λ μ L i r R :=
    Diagram.ext rfl
  have hx : Diagram.cast (𝟙 _) he he = 𝟙 bᵣ := Diagram.ext rfl
  have h' := diag_cast_eq (Pup) he he h
  rw [hb, hx] at h'
  exact (diag_eq_addRels (Pup) h').trans ((Pslide).diag_id _)

private theorem dotPower_comp {D : Type*} [Category* D] {a b : D} (f : a ⟶ b)
    (x : End a) (y : End b) (h : x ≫ f = f ≫ y) :
    ∀ m : ℕ, (x ^ m) ≫ f = f ≫ (y ^ m)
  | 0 => by simp
  | m + 1 => by
    rw [pow_succ, pow_succ]
    change (x ≫ x ^ m) ≫ f = f ≫ (y ≫ y ^ m)
    rw [Category.assoc, dotPower_comp f x y h m, ← Category.assoc, h, Category.assoc]

/-- Slide a clockwise bubble from the right to the left of a red strand, adding
the red coroot multiplicity to the dot count. The two red/cup and red/cap mates
from Webster's proof of Theorem 4.25 and (4.2), (4.4e) suffice. -/
theorem clockwiseBubble_slide (m : ℕ) :
    (Pslide).diag (clockwiseBubbleAfterRed RD Λ μ L i r R m) =
      (Pslide).diag (clockwiseBubbleBeforeRed RD Λ μ L i r R (m + exponents r i)) := by
  have hcup : (Pslide).diag (leftCup RD Λ μ L i r R ≫ leftIn RD Λ μ L i r R) =
      (Pslide).diag (rightCup RD Λ μ L i r R ≫ rightIn RD Λ μ L i r R) :=
    (Pslide).diag_eq_of_rel (.inl (.inl (.inl (.inr ⟨μ, L, up i, r, R⟩)))) rfl
  have hcap : (Pslide).diag (leftOut RD Λ μ L i r R ≫ leftCap RD Λ μ L i r R) =
      (Pslide).diag (rightOut RD Λ μ L i r R ≫ rightCap RD Λ μ L i r R) :=
    (Pslide).diag_eq_of_rel (.inl (.inl (.inr ⟨μ, L, dn i, r, R⟩))) rfl
  have h := congrArg₂ (fun f g => f ≫ (Pslide).diag (middleDot RD Λ μ L i r R ^ m) ≫ g) hcup hcap
  simp only [Presentation.diag_comp, Category.assoc] at h
  have hl : (Pslide).diag (leftDot RD Λ μ L i r R ^ m) ≫ (Pslide).diag (leftIn RD Λ μ L i r R) =
      (Pslide).diag (leftIn RD Λ μ L i r R) ≫ (Pslide).diag (middleDot RD Λ μ L i r R ^ m) := by
    simp only [diag_pow]
    exact dotPower_comp _ _ _ (leftIn_dot RD Λ μ L i r R Q exponents P) m
  have hr : (Pslide).diag (rightDot RD Λ μ L i r R ^ m) ≫ (Pslide).diag (rightIn RD Λ μ L i r R) =
      (Pslide).diag (rightIn RD Λ μ L i r R) ≫ (Pslide).diag (middleDot RD Λ μ L i r R ^ m) := by
    simp only [diag_pow]
    exact dotPower_comp _ _ _ (rightIn_dot RD Λ μ L i r R Q exponents P) m
  have hm := congrArg (fun f => f ≫ (Pslide).diag (leftOut RD Λ μ L i r R) ≫
    (Pslide).diag (leftCap RD Λ μ L i r R)) hl.symm
  have hn := congrArg (fun f => f ≫ (Pslide).diag (rightOut RD Λ μ L i r R) ≫
    (Pslide).diag (rightCap RD Λ μ L i r R)) hr.symm
  simp only [Category.assoc] at hm hn
  rw [hm, hn] at h
  have hL : (Pslide).diag (leftIn RD Λ μ L i r R) ≫ (Pslide).diag (leftOut RD Λ μ L i r R) ≫
      (Pslide).diag (leftCap RD Λ μ L i r R) =
      (Pslide).diag (leftDot RD Λ μ L i r R ^ exponents r i) ≫ (Pslide).diag (leftCap RD Λ μ L i r R) := by
    rw [← Category.assoc, ← Presentation.diag_comp, left_bigon]
  have hR : (Pslide).diag (rightIn RD Λ μ L i r R) ≫ (Pslide).diag (rightOut RD Λ μ L i r R) ≫
      (Pslide).diag (rightCap RD Λ μ L i r R) = (Pslide).diag (rightCap RD Λ μ L i r R) := by
    rw [← Category.assoc, ← Presentation.diag_comp, right_bigon, Category.id_comp]
  rw [hL, hR] at h
  have hp : (Pslide).diag (leftDot RD Λ μ L i r R ^ m) ≫
      (Pslide).diag (leftDot RD Λ μ L i r R ^ exponents r i) =
      (Pslide).diag (leftDot RD Λ μ L i r R ^ (m + exponents r i)) := by
    rw [← Presentation.diag_comp]
    congr 1
    change leftDot RD Λ μ L i r R ^ exponents r i * leftDot RD Λ μ L i r R ^ m = _
    rw [← pow_add, Nat.add_comm]
  have hp' := congrArg (fun f => f ≫ (Pslide).diag (leftCap RD Λ μ L i r R)) hp
  simp only [Category.assoc] at hp'
  rw [hp'] at h
  simpa only [clockwiseBubbleBeforeRed, clockwiseBubbleAfterRed, Presentation.diag_comp] using h.symm

section Cyclicity

local notation "Padj" => addBlackAdjunctionRelations RD Λ (Pslide)

private theorem cup_leg_powers {D : Type*} [Category* D] {a b : D} (c : a ⟶ b)
    (x y : End b) (hc : c ≫ x = c ≫ y) (hxy : x ≫ y = y ≫ x) (m : ℕ) :
    c ≫ (x ^ m) = c ≫ (y ^ m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    calc
      _ = (c ≫ (x ^ m)) ≫ x := by rw [pow_succ']; exact (Category.assoc ..).symm
      _ = (c ≫ (y ^ m)) ≫ x := by rw [ih]
      _ = (c ≫ x) ≫ (y ^ m) := by
        rw [Category.assoc, dotPower_comp x y y hxy.symm m, ← Category.assoc]
      _ = (c ≫ y) ≫ (y ^ m) := by rw [hc]
      _ = _ := by rw [pow_succ]; exact Category.assoc ..

private theorem pairDots_commute (A : Presentation.{w, max u v} (signature RD Λ) k)
    (a b : List (DoubleStrand I ℓ)) (l : Letter I) :
    A.diag (blackPairDotLeft RD Λ μ a l b) ≫ A.diag (blackPairDotRight RD Λ μ a l b) =
      A.diag (blackPairDotRight RD Λ μ a l b) ≫ A.diag (blackPairDotLeft RD Λ μ a l b) := by
  rw [← Presentation.diag_comp, ← Presentation.diag_comp]
  let η := endWeight RD Λ μ a
  let ξ := endWeight RD Λ η [Sum.inl l]
  let tail := colours RD Λ (endWeight RD Λ ξ [Sum.inl l.dual]) b
  apply A.diag_interchange_of_layers_of_even μ (colours RD Λ μ a) [] tail
    (η, .black (.dot l)) (ξ, .black (.dot l.dual)) (Or.inl rfl)
  all_goals
    simp [blackPairDotLeft, blackPairDotRight, moveDiagram, layer, signature, η, ξ, tail,
      Move.bottom, Move.top, Shape.dom, Shape.cod, colours, colours_append,
      endWeight, DoubleStrand.weight, add_assoc, add_left_comm, add_comm]

private theorem blackBubble_leg (a b : List (DoubleStrand I ℓ)) (m : ℕ) :
    (Padj).diag (Diagram.cast
      (blackCup RD Λ μ a (up i) b ≫ (blackPairDotRight RD Λ μ a (up i) b ^ m) ≫
        blackCap RD Λ μ a (up i) b)
      (by simp [blackWord]) (by simp [blackWord])) =
    (Padj).diag (blackDiagram RD Λ μ a b (ccwReal RD (endWeight RD Λ μ a) i m)) := by
  have hraw : blackDiagram RD Λ μ a b (ccwReal RD (endWeight RD Λ μ a) i m) =
      Diagram.cast (blackCup RD Λ μ a (up i) b ≫ (blackPairDotLeft RD Λ μ a (up i) b ^ m) ≫
        blackCap RD Λ μ a (up i) b) (by simp [blackWord]) (by simp [blackWord]) := by
    apply Diagram.ext
    rw [show ccwReal RD (endWeight RD Λ μ a) i m =
      BubbleOrientation.clockwise.beforeReflection RD (endWeight RD Λ μ a) i m from rfl,
      realBubble_layers]
    simp only [Diagram.layers_comp, Diagram.layers_cast, layers_pow, List.flatten_replicate_singleton,
      blackCup, blackCap, blackPairDotLeft, moveDiagram, Diagram.layers_layer]
    rfl
  -- Both outer-boundary lists differ only by the empty black word.
  have he : obj RD Λ μ (a ++ b) = obj RD Λ μ (a ++ blackWord [] ++ b) := by simp [blackWord]
  let U := blackCup RD Λ μ a (up i) b
  let E := blackCap RD Λ μ a (up i) b
  let x := blackPairDotLeft RD Λ μ a (up i) b
  let y := blackPairDotRight RD Λ μ a (up i) b
  have hc : (Padj).diag U ≫ (Padj).diag x = (Padj).diag U ≫ (Padj).diag y := by
    simpa only [U, x, y, blackCupDotLeft, blackCupDotRight, Presentation.diag_comp] using
      blackCup_dot_slide RD Λ μ a (up i) b (Pslide)
  have hp := cup_leg_powers ((Padj).diag U) (End.of ((Padj).diag x)) (End.of ((Padj).diag y))
    hc (pairDots_commute RD Λ μ (Padj) a b (up i)) m
  have h : (Padj).diag (U ≫ (y ^ m) ≫ E) = (Padj).diag (U ≫ (x ^ m) ≫ E) := by
    simp only [Presentation.diag_comp, diag_pow, ← Category.assoc]
    rw [hp]
  exact (diag_cast_eq (Padj) he he h).trans (congrArg ((Padj).diag) hraw.symm)

private theorem cwBubbleBeforeRed_eq (m : ℕ) :
    (Padj).diag (clockwiseBubbleBeforeRed RD Λ μ L i r R m) =
      (Padj).diag (cwBubbleBeforeRed RD Λ μ L i r R m) := by
  let e : obj RD Λ μ (L ++ blackWord [] ++ λr :: R) = b₀ := by
    simp [blackWord, List.append_assoc]
  have h := diag_cast_eq (Padj) e e (blackBubble_leg RD Λ μ i Q exponents P L (λr :: R) m)
  convert h using 2 <;> try rfl
  apply Diagram.ext
  simp only [Diagram.layers_cast, clockwiseBubbleBeforeRed, Diagram.layers_comp, layers_pow,
    leftCup, leftDot, leftCap, blackCup, blackCap, blackPairDotRight, redDownDotBlackLeft]
  rfl

private theorem cwBubbleAfterRed_eq (m : ℕ) :
    (Padj).diag (clockwiseBubbleAfterRed RD Λ μ L i r R m) =
      (Padj).diag (cwBubbleAfterRed RD Λ μ L i r R m) := by
  let e : obj RD Λ μ ((L ++ [λr]) ++ blackWord [] ++ R) = b₀ := by simp [blackWord]
  have h := diag_cast_eq (Padj) e e (blackBubble_leg RD Λ μ i Q exponents P (L ++ [λr]) R m)
  convert h using 2 <;> try rfl
  apply Diagram.ext
  simp only [Diagram.layers_cast, clockwiseBubbleAfterRed, Diagram.layers_comp, layers_pow,
    rightCup, rightDot, rightCap, blackCup, blackCap, blackPairDotRight, moveDiagram,
    Diagram.layers_layer, List.append_assoc, List.singleton_append]
  rfl

/-- Slide a real clockwise bubble to the left of red in the canonical black
bubble convention. The dot count increases by the red coroot multiplicity. -/
theorem cwBubble_slide (m : ℕ) :
    (Padj).diag (cwBubbleAfterRed RD Λ μ L i r R m) =
      (Padj).diag (cwBubbleBeforeRed RD Λ μ L i r R (m + exponents r i)) := by
  rw [← cwBubbleAfterRed_eq, ← cwBubbleBeforeRed_eq]
  exact diag_eq_addRels (Pslide) (clockwiseBubble_slide RD Λ μ L i r R Q exponents P m)

end Cyclicity

end Categorification.Stendhal.DoubleDiagram

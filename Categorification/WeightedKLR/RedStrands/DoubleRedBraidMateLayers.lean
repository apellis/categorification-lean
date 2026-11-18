/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleRedBraidMate
import Categorification.WeightedKLR.RedStrands.DoubleDiagramRewriting

/-!
# The physical layers of a mated red braid

Webster, arXiv:1309.3796v2, Definitions 4.5 and 4.24. Each one-strand
mate of a downward red braid has a single cup, three crossings, and a cap.
-/
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams KLR.Diagram

universe w u v
variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)
  (μ : X) (L : List (DoubleStrand I ℓ)) (r : Fin ℓ) (i j : I) (R : List (DoubleStrand I ℓ))
  {k : Type w} [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)
  (exponents : Fin ℓ → I →₀ ℕ) (P : Presentation.{w,max u v} (signature RD Λ) k)

local notation "eᵢ" => (Sum.inl (true, i) : DoubleStrand I ℓ)
local notation "fⱼ" => (Sum.inl (false, j) : DoubleStrand I ℓ)
local notation "fᵢ" => (Sum.inl (false, i) : DoubleStrand I ℓ)
local notation "red" => (Sum.inr r : DoubleStrand I ℓ)
local notation "dᵢ" => (Sum.inl i : I ⊕ Fin ℓ)
local notation "dⱼ" => (Sum.inl j : I ⊕ Fin ℓ)
local notation "rL" => (Sum.inr r : I ⊕ Fin ℓ)
local notation "P₀" => pres k (affineCoverQ Q exponents)
local notation "Pd" => addDownRelations RD Λ (affineCoverQ Q exponents) P
local notation "T" => downPresentedFunctor RD Λ (affineCoverQ Q exponents) P μ (L ++ [eᵢ]) (eᵢ :: R)

private theorem mapBraidLayer (a b : List (I ⊕ Fin ℓ)) (g : Gen (I ⊕ Fin ℓ))
    {d : Move I ℓ} (hd : downMove g = some d) :
    (T).map ((P₀).diag (dl a g b (a := ob (a ++ g.dom ++ b)) (b := ob (a ++ g.cod ++ b)) rfl rfl)) =
      (Pd).diag (downLayerDiagram RD Λ μ (L ++ [eᵢ]) (eᵢ :: R) (lay a g b) hd) :=
  downPresentedFunctor_layer RD Λ (affineCoverQ Q exponents) P μ (L ++ [eᵢ]) (eᵢ :: R)
    (lay a g b) (lay_valid a g b) rfl rfl hd

/-- The physical cup, three crossings, and cap for either downward braid word. -/
def redBraidMateLayers : RedBraidMateSide → Bool → List (SignedLayer I ℓ)
  | .left, true =>
    [ ((L ++ [eᵢ, fⱼ, red]), (.black (.cup (false, i))), R),
      ((L ++ [eᵢ, fⱼ]), (.redBlack r (false, i)), (eᵢ :: R)),
      ((L ++ [eᵢ]), (.black (.cross false j i)), (red :: eᵢ :: R)),
      ((L ++ [eᵢ, fᵢ]), (.blackRed (false, j) r), (eᵢ :: R)),
      (L, (.black (.cap (false, i))), (red :: fⱼ :: eᵢ :: R)) ]
  | .left, false =>
    [ ((L ++ [eᵢ, fⱼ, red]), (.black (.cup (false, i))), R),
      ((L ++ [eᵢ]), (.blackRed (false, j) r), (fᵢ :: eᵢ :: R)),
      ((L ++ [eᵢ, red]), (.black (.cross false j i)), (eᵢ :: R)),
      ((L ++ [eᵢ]), (.redBlack r (false, i)), (fⱼ :: eᵢ :: R)),
      (L, (.black (.cap (false, i))), (red :: fⱼ :: eᵢ :: R)) ]
  | .right, true =>
    [ (L, (.black (.cup (true, i))), (red :: fⱼ :: eᵢ :: R)),
      ((L ++ [eᵢ, fᵢ]), (.redBlack r (false, j)), (eᵢ :: R)),
      ((L ++ [eᵢ]), (.black (.cross false i j)), (red :: eᵢ :: R)),
      ((L ++ [eᵢ, fⱼ]), (.blackRed (false, i) r), (eᵢ :: R)),
      ((L ++ [eᵢ, fⱼ, red]), (.black (.cap (true, i))), R) ]
  | .right, false =>
    [ (L, (.black (.cup (true, i))), (red :: fⱼ :: eᵢ :: R)),
      ((L ++ [eᵢ]), (.blackRed (false, i) r), (fⱼ :: eᵢ :: R)),
      ((L ++ [eᵢ, red]), (.black (.cross false i j)), (eᵢ :: R)),
      ((L ++ [eᵢ]), (.redBlack r (false, j)), (fᵢ :: eᵢ :: R)),
      ((L ++ [eᵢ, fⱼ, red]), (.black (.cap (true, i))), R) ]

/-- Physical layers of the braidR mate with upward input on the left. -/
theorem redBraidMate_left_braidR :
    redBraidMate RD Λ μ L r i j R Q exponents P .left ((P₀).diag (braidR dⱼ rL dᵢ)) =
      signedDg RD Λ (Pd) μ (L ++ [eᵢ, fⱼ, red] ++ R) (L ++ [red, fⱼ, eᵢ] ++ R) (redBraidMateLayers L r i j R .left true) := by
  change (Pd).diag (redBraidMateCup RD Λ μ L r i j R .left) ≫ (T).map ((P₀).diag (braidR dⱼ rL dᵢ)) ≫
    (Pd).diag (redBraidMateCap RD Λ μ L r i j R .left) = _
  rw [show (P₀).diag (braidR dⱼ rL dᵢ) =
    (P₀).diag (XR dⱼ rL dᵢ) ≫ (P₀).diag (XL dⱼ dᵢ rL) ≫ (P₀).diag (XR dᵢ dⱼ rL) by
      simp only [Presentation.diag_comp], Functor.map_comp, Functor.map_comp]
  change (Pd).diag _ ≫ ((T).map ((P₀).diag (dl [dⱼ] (.cross rL dᵢ) [] rfl rfl)) ≫
    (T).map ((P₀).diag (dl [] (.cross dⱼ dᵢ) [rL] rfl rfl)) ≫
    (T).map ((P₀).diag (dl [dᵢ] (.cross dⱼ rL) [] rfl rfl))) ≫ (Pd).diag _ = _
  rw [mapBraidLayer RD Λ μ L i R Q exponents P [dⱼ] [] (.cross rL dᵢ) (d := (.redBlack r (false, i))) rfl,
    mapBraidLayer RD Λ μ L i R Q exponents P [] [rL] (.cross dⱼ dᵢ) (d := (.black (.cross false j i))) rfl,
    mapBraidLayer RD Λ μ L i R Q exponents P [dᵢ] [] (.cross dⱼ rL) (d := (.blackRed (false, j) r)) rfl]
  simp only [← Presentation.diag_comp]
  symm
  apply signedDg_eq_diag_of_layers RD Λ (Pd) μ (by
    simp [signedChain, redBraidMateLayers, Move.bottom, Move.top, List.append_assoc])
  simp [signedLayers, redBraidMateLayers, redBraidMateCup, redBraidMateCap,
    Diagram.layers_comp, Diagram.layers_cast, moveDiagram, List.append_assoc, DoubleStrand.down]

/-- Physical layers of the braidL mate with upward input on the left. -/
theorem redBraidMate_left_braidL :
    redBraidMate RD Λ μ L r i j R Q exponents P .left ((P₀).diag (braidL dⱼ rL dᵢ)) =
      signedDg RD Λ (Pd) μ (L ++ [eᵢ, fⱼ, red] ++ R) (L ++ [red, fⱼ, eᵢ] ++ R) (redBraidMateLayers L r i j R .left false) := by
  change (Pd).diag (redBraidMateCup RD Λ μ L r i j R .left) ≫ (T).map ((P₀).diag (braidL dⱼ rL dᵢ)) ≫
    (Pd).diag (redBraidMateCap RD Λ μ L r i j R .left) = _
  rw [show (P₀).diag (braidL dⱼ rL dᵢ) =
    (P₀).diag (XL dⱼ rL dᵢ) ≫ (P₀).diag (XR rL dⱼ dᵢ) ≫ (P₀).diag (XL rL dᵢ dⱼ) by
      simp only [Presentation.diag_comp], Functor.map_comp, Functor.map_comp]
  change (Pd).diag _ ≫ ((T).map ((P₀).diag (dl [] (.cross dⱼ rL) [dᵢ] rfl rfl)) ≫
    (T).map ((P₀).diag (dl [rL] (.cross dⱼ dᵢ) [] rfl rfl)) ≫
    (T).map ((P₀).diag (dl [] (.cross rL dᵢ) [dⱼ] rfl rfl))) ≫ (Pd).diag _ = _
  rw [mapBraidLayer RD Λ μ L i R Q exponents P [] [dᵢ] (.cross dⱼ rL) (d := (.blackRed (false, j) r)) rfl,
    mapBraidLayer RD Λ μ L i R Q exponents P [rL] [] (.cross dⱼ dᵢ) (d := (.black (.cross false j i))) rfl,
    mapBraidLayer RD Λ μ L i R Q exponents P [] [dⱼ] (.cross rL dᵢ) (d := (.redBlack r (false, i))) rfl]
  simp only [← Presentation.diag_comp]
  symm
  apply signedDg_eq_diag_of_layers RD Λ (Pd) μ (by
    simp [signedChain, redBraidMateLayers, Move.bottom, Move.top, List.append_assoc])
  simp [signedLayers, redBraidMateLayers, redBraidMateCup, redBraidMateCap,
    Diagram.layers_comp, Diagram.layers_cast, moveDiagram, List.append_assoc, DoubleStrand.down]

/-- Physical layers of the braidR mate with upward input on the right. -/
theorem redBraidMate_right_braidR :
    redBraidMate RD Λ μ L r i j R Q exponents P .right ((P₀).diag (braidR dᵢ rL dⱼ)) =
      signedDg RD Λ (Pd) μ (L ++ [red, fⱼ, eᵢ] ++ R) (L ++ [eᵢ, fⱼ, red] ++ R) (redBraidMateLayers L r i j R .right true) := by
  change (Pd).diag (redBraidMateCup RD Λ μ L r i j R .right) ≫ (T).map ((P₀).diag (braidR dᵢ rL dⱼ)) ≫
    (Pd).diag (redBraidMateCap RD Λ μ L r i j R .right) = _
  rw [show (P₀).diag (braidR dᵢ rL dⱼ) =
    (P₀).diag (XR dᵢ rL dⱼ) ≫ (P₀).diag (XL dᵢ dⱼ rL) ≫ (P₀).diag (XR dⱼ dᵢ rL) by
      simp only [Presentation.diag_comp], Functor.map_comp, Functor.map_comp]
  change (Pd).diag _ ≫ ((T).map ((P₀).diag (dl [dᵢ] (.cross rL dⱼ) [] rfl rfl)) ≫
    (T).map ((P₀).diag (dl [] (.cross dᵢ dⱼ) [rL] rfl rfl)) ≫
    (T).map ((P₀).diag (dl [dⱼ] (.cross dᵢ rL) [] rfl rfl))) ≫ (Pd).diag _ = _
  rw [mapBraidLayer RD Λ μ L i R Q exponents P [dᵢ] [] (.cross rL dⱼ) (d := (.redBlack r (false, j))) rfl,
    mapBraidLayer RD Λ μ L i R Q exponents P [] [rL] (.cross dᵢ dⱼ) (d := (.black (.cross false i j))) rfl,
    mapBraidLayer RD Λ μ L i R Q exponents P [dⱼ] [] (.cross dᵢ rL) (d := (.blackRed (false, i) r)) rfl]
  simp only [← Presentation.diag_comp]
  symm
  apply signedDg_eq_diag_of_layers RD Λ (Pd) μ (by
    simp [signedChain, redBraidMateLayers, Move.bottom, Move.top, List.append_assoc])
  simp [signedLayers, redBraidMateLayers, redBraidMateCup, redBraidMateCap,
    Diagram.layers_comp, Diagram.layers_cast, moveDiagram, List.append_assoc, DoubleStrand.down]

/-- Physical layers of the braidL mate with upward input on the right. -/
theorem redBraidMate_right_braidL :
    redBraidMate RD Λ μ L r i j R Q exponents P .right ((P₀).diag (braidL dᵢ rL dⱼ)) =
      signedDg RD Λ (Pd) μ (L ++ [red, fⱼ, eᵢ] ++ R) (L ++ [eᵢ, fⱼ, red] ++ R) (redBraidMateLayers L r i j R .right false) := by
  change (Pd).diag (redBraidMateCup RD Λ μ L r i j R .right) ≫ (T).map ((P₀).diag (braidL dᵢ rL dⱼ)) ≫
    (Pd).diag (redBraidMateCap RD Λ μ L r i j R .right) = _
  rw [show (P₀).diag (braidL dᵢ rL dⱼ) =
    (P₀).diag (XL dᵢ rL dⱼ) ≫ (P₀).diag (XR rL dᵢ dⱼ) ≫ (P₀).diag (XL rL dⱼ dᵢ) by
      simp only [Presentation.diag_comp], Functor.map_comp, Functor.map_comp]
  change (Pd).diag _ ≫ ((T).map ((P₀).diag (dl [] (.cross dᵢ rL) [dⱼ] rfl rfl)) ≫
    (T).map ((P₀).diag (dl [rL] (.cross dᵢ dⱼ) [] rfl rfl)) ≫
    (T).map ((P₀).diag (dl [] (.cross rL dⱼ) [dᵢ] rfl rfl))) ≫ (Pd).diag _ = _
  rw [mapBraidLayer RD Λ μ L i R Q exponents P [] [dⱼ] (.cross dᵢ rL) (d := (.blackRed (false, i) r)) rfl,
    mapBraidLayer RD Λ μ L i R Q exponents P [rL] [] (.cross dᵢ dⱼ) (d := (.black (.cross false i j))) rfl,
    mapBraidLayer RD Λ μ L i R Q exponents P [] [dᵢ] (.cross rL dⱼ) (d := (.redBlack r (false, j))) rfl]
  simp only [← Presentation.diag_comp]
  symm
  apply signedDg_eq_diag_of_layers RD Λ (Pd) μ (by
    simp [signedChain, redBraidMateLayers, Move.bottom, Move.top, List.append_assoc])
  simp [signedLayers, redBraidMateLayers, redBraidMateCup, redBraidMateCap,
    Diagram.layers_comp, Diagram.layers_cast, moveDiagram, List.append_assoc, DoubleStrand.down]

end Categorification.Stendhal.DoubleDiagram

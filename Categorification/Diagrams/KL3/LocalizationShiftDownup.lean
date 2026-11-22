/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.LocalizationShiftCyclicCross
import Categorification.Diagrams.KL3.Pitchfork
import Categorification.Diagrams.KL3.BubbleSlidesEq

/-!
# The double sideways crossings under the weight shift of `U′`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
Proposition 3.30. The images of the relations `downupEF` and `downupFE` (KL III
`eq_downup_ij-gen`, `i ≠ j`) under the weight shift `shiftFree RD k δ a b` vanish
(`shift_rel_downupEF`, `shift_rel_downupFE`).

The image of a sideways crossing is the crossing conjugated by dot powers on its downward
strand (`zg_img_crossl`, `zg_img_crossr`). For distinct colours a downward dot slides through a
sideways crossing (`dg_dot_crossl`, `dg_dot_crossr`: rotate it to an upward dot at the cap,
slide it through the upward crossing, and rotate it back at the cup), hence so does every
integer power of it in `U′` (`ldot_crossl`, `ldot_crossr`). The dot powers then cancel against
each other once the two crossings compose to the identity.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.KL3.Diagram
open CategoryTheory StringDiagrams QuantumGroup UDot Presentation
universe w u v
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {k : Type w} [CommRing k]

variable (RD k) in
theorem dg_dot_crossr (ν : X) (i j : I) (h : i ≠ j) :
    dg RD k ν [dn j, up i] [up i, dn j] (([], .dot (dn j), [up i]) :: crossrL i j) =
      dg RD k ν [dn j, up i] [up i, dn j] (crossrL i j ++ [([up i], .dot (dn j), [])]) := by
  dnorm
  dswap 0; dswap 1
  dat 2 [] [up i, dn j] (dg_dot_cap_up RD k _ j)
  dat 1 [dn j] [dn j] (dg_slideLNe RD k _ i j h)
  dat 0 [dn j, up i] [] (dg_dot_cupUp RD k j _).symm
  dswap 1; dswap 2

variable (RD k) in
theorem dg_dot_crossl (ν : X) (i j : I) (h : j ≠ i) :
    dg RD k ν [up i, dn j] [dn j, up i] (([up i], .dot (dn j), []) :: crosslL i j) =
      dg RD k ν [up i, dn j] [dn j, up i] (crosslL i j ++ [([], .dot (dn j), [up i])]) := by
  dnorm
  dswap 0; dswap 1
  dat 2 [dn j, up i] [] (dg_dot_cap_dn RD k _ j)
  dat 1 [dn j] [dn j] (dg_slideRNe RD k _ j i h).symm
  dat 0 [] [up i, dn j] (dg_dot_cupDn RD k j _)
  dswap 1; dswap 2

theorem ldot_crossr (ν : X) (i j : I) (h : i ≠ j) (n : ℤ) :
    zdot RD k ν [] j [up i] n ≫ ldg RD k ν [dn j, up i] [up i, dn j] (crossrL i j) =
      ldg RD k ν [dn j, up i] [up i, dn j] (crossrL i j) ≫ zdot RD k ν [up i] j [] n := by
  refine zdot_comp_of_one (RD := RD) (k := k) (A := []) (B := [up i]) (A' := [up i])
    (B' := []) ν _ ?_ n
  rw [← ldg_single_dot, ← ldg_single_dot]
  exact (ldg_comp RD k (sChain_single ([], .dot (dn j), [up i])) (by schain)).trans
    ((congrArg (toLoc RD k).map (dg_dot_crossr RD k ν i j h)).trans
      (ldg_comp RD k (by schain) (sChain_single ([up i], .dot (dn j), []))).symm)

theorem ldot_crossl (ν : X) (i j : I) (h : j ≠ i) (n : ℤ) :
    zdot RD k ν [up i] j [] n ≫ ldg RD k ν [up i, dn j] [dn j, up i] (crosslL i j) =
      ldg RD k ν [up i, dn j] [dn j, up i] (crosslL i j) ≫ zdot RD k ν [] j [up i] n := by
  refine zdot_comp_of_one (RD := RD) (k := k) (A := [up i]) (B := []) (A' := [])
    (B' := [up i]) ν _ ?_ n
  rw [← ldg_single_dot, ← ldg_single_dot]
  exact (ldg_comp RD k (sChain_single ([up i], .dot (dn j), [])) (by schain)).trans
    ((congrArg (toLoc RD k).map (dg_dot_crossl RD k ν i j h)).trans
      (ldg_comp RD k (by schain) (sChain_single ([], .dot (dn j), [up i]))).symm)

theorem zg_dot_lays_dot (ν : X) (A B A' B' : List (Letter I)) (i j : I) (n m : ℤ)
    (ls : List (LayerData I)) (h : SChain (A ++ [dn i] ++ B) ls (A' ++ [dn j] ++ B')) :
    zg RD k ν (A ++ [dn i] ++ B) (A' ++ [dn j] ++ B')
        (.dot A i B n :: (ls.map .lay ++ [.dot A' j B' m])) =
      zdot RD k ν A i B n ≫ ldg RD k ν _ _ ls ≫ zdot RD k ν A' j B' m := by
  rw [zg_dot_cons, zg_append_dot ν _ _ _ _ (dChain_lays h), zg_lays ν h]

variable (a b : I → ℤ)

theorem zg_img_crossr (ν : X) (i j : I) :
    zg RD k ν [dn j, up i] [up i, dn j] ((crossrL i j).flatMap (layStep a b)) =
      zdot RD k ν [] j [up i] (a j) ≫ ldg RD k ν [dn j, up i] [up i, dn j] (crossrL i j) ≫
        zdot RD k ν [up i] j [] (-a j) := by
  have f1 := (zg_slideL (RD := RD) (k := k) ν [] [] [dn j] (.cross true i j) j (a j)).symm
  refine (zg_local' ν [up i, dn j] (s := [dn j, up i])
    (A := [.lay ([dn j, up i], .cup (up j), []), .dot [dn j, up i, up j] j [] (-a j)])
    [.lay ([], .cap (up j), [up i, dn j])] f1 (by dchain) (by dchain) (by dchain)).trans ?_
  have f2 := (zg_dotComm (RD := RD) (k := k) ν [] [up i, up j] [] j j (a j) (-a j)).symm
  refine (zg_local' ν [up i, dn j] (s := [dn j, up i])
    (A := [.lay ([dn j, up i], .cup (up j), [])])
    [.lay ([dn j], .cross true i j, [dn j]), .lay ([], .cap (up j), [up i, dn j])] f2
    (by dchain) (by dchain) (by dchain)).trans ?_
  have f3 := (zg_slideL (RD := RD) (k := k) ν [] [up i] [] (.cup (up j)) j (a j)).symm
  refine (zg_local' ν [up i, dn j] (s := [dn j, up i]) (A := [])
    [.dot [dn j, up i, up j] j [] (-a j), .lay ([dn j], .cross true i j, [dn j]),
      .lay ([], .cap (up j), [up i, dn j])] f3 (by dchain) (by dchain) (by dchain)).trans ?_
  have f4 := zg_slideR (RD := RD) (k := k) ν [dn j] [] [] (.cross true i j) j (-a j)
  refine (zg_local' ν [up i, dn j] (s := [dn j, up i])
    (A := [.dot [] j [up i] (a j), .lay ([dn j, up i], .cup (up j), [])])
    [.lay ([], .cap (up j), [up i, dn j])] f4 (by dchain) (by dchain) (by dchain)).trans ?_
  have f5 := zg_slideR (RD := RD) (k := k) ν [] [up i] [] (.cap (up j)) j (-a j)
  refine (zg_local' ν [up i, dn j] (s := [dn j, up i])
    (A := [.dot [] j [up i] (a j), .lay ([dn j, up i], .cup (up j), []),
      .lay ([dn j], .cross true i j, [dn j])])
    [] f5 (by dchain) (by dchain) (by dchain)).trans ?_
  exact zg_dot_lays_dot ν [] [up i] [up i] [] j j (a j) (-a j) (crossrL i j) (by schain)

theorem zg_img_crossl (ν : X) (i j : I) :
    zg RD k ν [up i, dn j] [dn j, up i] ((crosslL i j).flatMap (layStep a b)) =
      zdot RD k ν [up i] j [] (b j) ≫ ldg RD k ν [up i, dn j] [dn j, up i] (crosslL i j) ≫
        zdot RD k ν [] j [up i] (-b j) := by
  have g1 := (zg_slideR (RD := RD) (k := k) ν [dn j] [] [] (.cross true j i) j (b j)).symm
  refine (zg_local' ν [dn j, up i] (s := [up i, dn j])
    (A := [.lay ([], .cup (dn j), [up i, dn j]), .dot [] j [up j, up i, dn j] (-b j)])
    [.lay ([dn j, up i], .cap (dn j), [])] g1 (by dchain) (by dchain) (by dchain)).trans ?_
  have g2 := zg_dotComm (RD := RD) (k := k) ν [] [up j, up i] [] j j (-b j) (b j)
  refine (zg_local' ν [dn j, up i] (s := [up i, dn j])
    (A := [.lay ([], .cup (dn j), [up i, dn j])])
    [.lay ([dn j], .cross true j i, [dn j]), .lay ([dn j, up i], .cap (dn j), [])] g2
    (by dchain) (by dchain) (by dchain)).trans ?_
  have g3 := (zg_slideR (RD := RD) (k := k) ν [] [up i] [] (.cup (dn j)) j (b j)).symm
  refine (zg_local' ν [dn j, up i] (s := [up i, dn j]) (A := [])
    [.dot [] j [up j, up i, dn j] (-b j), .lay ([dn j], .cross true j i, [dn j]),
      .lay ([dn j, up i], .cap (dn j), [])] g3 (by dchain) (by dchain) (by dchain)).trans ?_
  have g4 := zg_slideL (RD := RD) (k := k) ν [] [] [dn j] (.cross true j i) j (-b j)
  refine (zg_local' ν [dn j, up i] (s := [up i, dn j])
    (A := [.dot [up i] j [] (b j), .lay ([], .cup (dn j), [up i, dn j])])
    [.lay ([dn j, up i], .cap (dn j), [])] g4 (by dchain) (by dchain) (by dchain)).trans ?_
  have g5 := zg_slideL (RD := RD) (k := k) ν [] [up i] [] (.cap (dn j)) j (-b j)
  refine (zg_local' ν [dn j, up i] (s := [up i, dn j])
    (A := [.dot [up i] j [] (b j), .lay ([], .cup (dn j), [up i, dn j]),
      .lay ([dn j], .cross true j i, [dn j])])
    [] g5 (by dchain) (by dchain) (by dchain)).trans ?_
  exact zg_dot_lays_dot ν [up i] [] [] [up i] j j (b j) (-b j) (crosslL i j) (by schain)

theorem zg_downupEF (ν : X) (i j : I) (h : i ≠ j) :
    zg RD k ν [up i, dn j] [up i, dn j] ((crosslL i j ++ crossrL i j).flatMap (layStep a b)) =
      zg RD k ν [up i, dn j] [up i, dn j] (([] : List (LayerData I)).flatMap (layStep a b)) := by
  rw [List.flatMap_append, zg_append ν (r := [dn j, up i]) _ _ (by dchain), zg_img_crossl,
    zg_img_crossr]
  simp only [Category.assoc]
  rw [← Category.assoc (zdot RD k ν [] j [up i] (-b j)), ← zdot_add,
    ← Category.assoc (zdot RD k ν [] j [up i] _), ldot_crossr ν i j h, Category.assoc,
    ← zdot_add, ← Category.assoc (ldg RD k ν _ _ (crosslL i j)),
    ldg_comp RD k (by schain) (by schain)]
  have e : ldg RD k ν [up i, dn j] [up i, dn j] (crosslL i j ++ crossrL i j) = 𝟙 _ :=
    (congrArg (toLoc RD k).map (dg_downupEF RD k i j h ν)).trans (ldg_nil RD k ν _)
  rw [e, Category.id_comp, ← zdot_add, show -a j + (a j + -b j) + b j = 0 by ring, zdot_zero]
  exact (zg_nil ν _).symm

theorem zg_downupFE (ν : X) (i j : I) (h : i ≠ j) :
    zg RD k ν [dn i, up j] [dn i, up j] ((crossrL j i ++ crosslL j i).flatMap (layStep a b)) =
      zg RD k ν [dn i, up j] [dn i, up j] (([] : List (LayerData I)).flatMap (layStep a b)) := by
  rw [List.flatMap_append, zg_append ν (r := [up j, dn i]) _ _ (by dchain), zg_img_crossr,
    zg_img_crossl]
  simp only [Category.assoc]
  rw [← Category.assoc (zdot RD k ν [up j] i [] (-a i)), ← zdot_add,
    ← Category.assoc (zdot RD k ν [up j] i [] _), ldot_crossl ν j i h, Category.assoc,
    ← zdot_add, ← Category.assoc (ldg RD k ν _ _ (crossrL j i)),
    ldg_comp RD k (by schain) (by schain)]
  have e : ldg RD k ν [dn i, up j] [dn i, up j] (crossrL j i ++ crosslL j i) = 𝟙 _ :=
    (congrArg (toLoc RD k).map (dg_downupFE RD k i j h ν)).trans (ldg_nil RD k ν _)
  rw [e, Category.id_comp, ← zdot_add, show -b i + (b i + -a i) + a i = 0 by ring, zdot_zero]
  exact (zg_nil ν _).symm

variable (RD k) (δ : X)

/-- **The relation `downupEF`** (KL III `eq_downup_ij-gen`) holds for the images of the weight
shift. -/
theorem shift_rel_downupEF (i j : I) (h : i ≠ j) (μ : X) :
    (freeLift k (shiftFree RD k δ a b)).map
      ((presLoc RD k).rel (.inl (.inr (.downupEF i j h μ)))) = 0 := by
  have e1 : crossl RD i j μ ≫ crossr RD i j μ =
      mkD RD μ (crosslL i j ++ crossrL i j) (by schain) := mkD_comp RD μ _ _ _ _
  have e2 : 𝟙 (ob RD μ [up i, dn j]) = mkD RD μ ([] : List (LayerData I)) rfl := by
    ext; simp
  show (freeLift k (shiftFree RD k δ a b)).map (inclLin RD k
    (LinDiagram.of (crossl RD i j μ ≫ crossr RD i j μ) - LinDiagram.of (𝟙 _))) = 0
  rw [e1, e2]
  exact shiftLin_mkD_sub RD k δ a b μ _ _ _ _ (zg_downupEF a b (μ + δ) i j h)

/-- **The relation `downupFE`** (KL III `eq_downup_ij-gen`) holds for the images of the weight
shift. -/
theorem shift_rel_downupFE (i j : I) (h : i ≠ j) (μ : X) :
    (freeLift k (shiftFree RD k δ a b)).map
      ((presLoc RD k).rel (.inl (.inr (.downupFE i j h μ)))) = 0 := by
  have e1 : crossr RD j i μ ≫ crossl RD j i μ =
      mkD RD μ (crossrL j i ++ crosslL j i) (by schain) := mkD_comp RD μ _ _ _ _
  have e2 : 𝟙 (ob RD μ [dn i, up j]) = mkD RD μ ([] : List (LayerData I)) rfl := by
    ext; simp
  show (freeLift k (shiftFree RD k δ a b)).map (inclLin RD k
    (LinDiagram.of (crossr RD j i μ ≫ crossl RD j i μ) - LinDiagram.of (𝟙 _))) = 0
  rw [e1, e2]
  exact shiftLin_mkD_sub RD k δ a b μ _ _ _ _ (zg_downupFE a b (μ + δ) i j h)

end Categorification.KL3.Diagram

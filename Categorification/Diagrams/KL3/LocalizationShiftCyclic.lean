/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.LocalizationShiftZigzag

/-!
# The dot cyclicity relations under the weight shift of `U′`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
Proposition 3.30. The images of the cyclicity relations for dots (KL III (3.3), `cycDotR`
and `cycDotL`) under the weight shift `shiftFree RD k δ a b` vanish
(`shift_rel_cycDotR`, `shift_rel_cycDotL`): the inverse dots inserted at the cup and the cap
slide along the rotated strand, cancel against each other up to a conjugation of the downward
dot by a power of the dot unit, and the rotated dot is then removed by `dg_cycDotR`,
`dg_cycDotL`.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.KL3.Diagram
open CategoryTheory StringDiagrams QuantumGroup UDot Presentation
universe w u v
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k] (δ : X) (a b : I → ℤ)

/-- A relation `d - d'` between two normal-form diagrams with the same boundary holds for the
images of the weight shift as soon as the composites of their images agree. -/
theorem shiftLin_mkD_sub (μ : X) {s t : List (Letter I)} (ls ls' : List (LayerData I))
    (h : SChain s ls t) (h' : SChain s ls' t)
    (hz : zg RD k (μ + δ) s t (ls.flatMap (layStep a b)) =
      zg RD k (μ + δ) s t (ls'.flatMap (layStep a b))) :
    (freeLift k (shiftFree RD k δ a b)).map
      (inclLin RD k (LinDiagram.of (mkD RD μ ls h) - LinDiagram.of (mkD RD μ ls' h'))) = 0 := by
  rw [map_sub, inclLin_of, inclLin_of, Functor.map_sub, freeLift_map_of, freeLift_map_of,
    shiftFree_map_mkD, shiftFree_map_mkD, imgList_eq_zg, imgList_eq_zg, hz, sub_self]

variable {RD k}

theorem zg_conj_dot (ν : X) (i : I) (n : ℤ) :
    zg RD k ν ([] ++ [dn i] ++ []) ([] ++ [dn i] ++ [])
      [.dot [] i [] n, .lay ([], .dot (dn i), []), .dot [] i [] (-n)] =
      zg RD k ν ([] ++ [dn i] ++ []) ([] ++ [dn i] ++ []) [.lay ([], .dot (dn i), [])] := by
  rw [zg_cons_tail ν _ _ _ (fun s' => (zg_dot_one ν s' _ [] i [] [.dot [] i [] (-n)]).symm),
    zg_dot_add, zg_dot_add, show -n + (1 + n) = 1 by ring, zg_dot_one]

theorem zg_cycDotR (ν : X) (i : I) :
    zg RD k ν [dn i] [dn i] ([([dn i], .cup (up i), []), ([dn i], .dot (up i), [dn i]),
        ([], .cap (up i), [dn i])].flatMap (layStep a b)) =
      zg RD k ν [dn i] [dn i] ([([], .dot (dn i), [])].flatMap (layStep a b)) := by
  have e1 := zg_slideR (RD := RD) (k := k) ν [dn i] [] [] (.dot (up i)) i (-a i)
  have h1 := zg_local' ν [dn i] (s := [dn i]) (A := [.lay ([dn i], .cup (up i), [])])
    [.dot [] i ([up i] ++ [dn i]) (a i), .lay ([], .cap (up i), [dn i])] e1
    ⟨rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩
  refine h1.trans ?_
  have e2 := (zg_dotComm (RD := RD) (k := k) ν [] [up i] [] i i (a i) (-a i)).symm
  have h2 := zg_local' ν [dn i] (s := [dn i])
    (A := [.lay ([dn i], .cup (up i), []), .lay ([dn i], .dot (up i), [dn i])])
    [.lay ([], .cap (up i), [dn i])] e2 ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩
  refine h2.trans ?_
  have e3 := zg_slideR (RD := RD) (k := k) ν [] [] [] (.cap (up i)) i (-a i)
  have h3 := zg_local' ν [dn i] (s := [dn i])
    (A := [.lay ([dn i], .cup (up i), []), .lay ([dn i], .dot (up i), [dn i]),
      .dot [] i ([up i] ++ [dn i]) (a i)]) [] e3
    ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩
  refine h3.trans ?_
  have e4 := (zg_slideL (RD := RD) (k := k) ν [] [] [dn i] (.dot (up i)) i (a i)).symm
  have h4 := zg_local' ν [dn i] (s := [dn i]) (A := [.lay ([dn i], .cup (up i), [])])
    [.lay ([], .cap (up i), [dn i]), .dot [] i [] (-a i)] e4
    ⟨rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩
  refine h4.trans ?_
  have e5 := (zg_slideL (RD := RD) (k := k) ν [] [] [] (.cup (up i)) i (a i)).symm
  have h5 := zg_local' ν [dn i] (s := [dn i]) (A := [])
    [.lay ([dn i], .dot (up i), [dn i]), .lay ([], .cap (up i), [dn i]), .dot [] i [] (-a i)] e5
    rfl ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩
  refine h5.trans ?_
  have e6 : zg RD k ν ([] ++ [dn i] ++ []) ([] ++ [dn i] ++ [])
      [.lay ([dn i], .cup (up i), []), .lay ([dn i], .dot (up i), [dn i]),
        .lay ([], .cap (up i), [dn i])] =
      zg RD k ν ([] ++ [dn i] ++ []) ([] ++ [dn i] ++ []) [.lay ([], .dot (dn i), [])] :=
    (zg_lays_all ν _ _ [_, _, _]).trans ((congrArg (toLoc RD k).map
      (dg_cycDotR RD k i ν).symm).trans (zg_lays_all ν _ _ [_]).symm)
  have h6 := zg_local' ν [dn i] (s := [dn i]) (A := [.dot [] i [] (a i)])
    [.dot [] i [] (-a i)] e6 ⟨rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl⟩
  refine h6.trans ?_
  exact zg_conj_dot ν i (a i)

theorem zg_cycDotL (ν : X) (i : I) :
    zg RD k ν [dn i] [dn i] ([([], .cup (dn i), [dn i]), ([dn i], .dot (up i), [dn i]),
        ([dn i], .cap (dn i), [])].flatMap (layStep a b)) =
      zg RD k ν [dn i] [dn i] ([([], .dot (dn i), [])].flatMap (layStep a b)) := by
  have e1 := zg_slideL (RD := RD) (k := k) ν [] [] [dn i] (.dot (up i)) i (-b i)
  have h1 := zg_local' ν [dn i] (s := [dn i]) (A := [.lay ([], .cup (dn i), [dn i])])
    [.dot ([dn i] ++ [up i]) i [] (b i), .lay ([dn i], .cap (dn i), [])] e1
    ⟨rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩
  refine h1.trans ?_
  have e2 := zg_dotComm (RD := RD) (k := k) ν [] [up i] [] i i (-b i) (b i)
  have h2 := zg_local' ν [dn i] (s := [dn i])
    (A := [.lay ([], .cup (dn i), [dn i]), .lay ([dn i], .dot (up i), [dn i])])
    [.lay ([dn i], .cap (dn i), [])] e2 ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩
  refine h2.trans ?_
  have e3 := zg_slideL (RD := RD) (k := k) ν [] [] [] (.cap (dn i)) i (-b i)
  have h3 := zg_local' ν [dn i] (s := [dn i])
    (A := [.lay ([], .cup (dn i), [dn i]), .lay ([dn i], .dot (up i), [dn i]),
      .dot ([dn i] ++ [up i]) i [] (b i)]) [] e3
    ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩
  refine h3.trans ?_
  have e4 := (zg_slideR (RD := RD) (k := k) ν [dn i] [] [] (.dot (up i)) i (b i)).symm
  have h4 := zg_local' ν [dn i] (s := [dn i]) (A := [.lay ([], .cup (dn i), [dn i])])
    [.lay ([dn i], .cap (dn i), []), .dot [] i [] (-b i)] e4
    ⟨rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩
  refine h4.trans ?_
  have e5 := (zg_slideR (RD := RD) (k := k) ν [] [] [] (.cup (dn i)) i (b i)).symm
  have h5 := zg_local' ν [dn i] (s := [dn i]) (A := [])
    [.lay ([dn i], .dot (up i), [dn i]), .lay ([dn i], .cap (dn i), []), .dot [] i [] (-b i)] e5
    rfl ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩
  refine h5.trans ?_
  have e6 : zg RD k ν ([] ++ [dn i] ++ []) ([] ++ [dn i] ++ [])
      [.lay ([], .cup (dn i), [dn i]), .lay ([dn i], .dot (up i), [dn i]),
        .lay ([dn i], .cap (dn i), [])] =
      zg RD k ν ([] ++ [dn i] ++ []) ([] ++ [dn i] ++ []) [.lay ([], .dot (dn i), [])] :=
    (zg_lays_all ν _ _ [_, _, _]).trans ((congrArg (toLoc RD k).map
      (dg_cycDotL RD k i ν).symm).trans (zg_lays_all ν _ _ [_]).symm)
  have h6 := zg_local' ν [dn i] (s := [dn i]) (A := [.dot [] i [] (b i)])
    [.dot [] i [] (-b i)] e6 ⟨rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl⟩
  refine h6.trans ?_
  exact zg_conj_dot ν i (b i)

variable (RD k)

/-- **The cyclicity relation `cycDotR`** (KL III (3.3)) holds for the images of the weight
shift. -/
theorem shift_rel_cycDotR (i : I) (μ : X) :
    (freeLift k (shiftFree RD k δ a b)).map ((presLoc RD k).rel (.inl (.inr (.cycDotR i μ)))) =
      0 :=
  shiftLin_mkD_sub RD k δ a b μ _ _ _ _ (zg_cycDotR a b (μ + δ) i)

/-- **The cyclicity relation `cycDotL`** (KL III (3.3)) holds for the images of the weight
shift. -/
theorem shift_rel_cycDotL (i : I) (μ : X) :
    (freeLift k (shiftFree RD k δ a b)).map ((presLoc RD k).rel (.inl (.inr (.cycDotL i μ)))) =
      0 :=
  shiftLin_mkD_sub RD k δ a b μ _ _ _ _ (zg_cycDotL a b (μ + δ) i)

end Categorification.KL3.Diagram

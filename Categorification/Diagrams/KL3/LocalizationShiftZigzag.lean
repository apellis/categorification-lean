/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.LocalizationShiftCalculus

/-!
# The zigzag relations under the weight shift of `U′`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
Proposition 3.30. The images of the two zigzag relations of the pivotal extension under the
weight shift `shiftImg RD k δ a b` vanish (`shift_rel_zigL`, `shift_rel_zigR`): the dots
`y^{∓a_i}`, `y^{∓b_i}` placed on the downward legs of the cup and the cap cancel after being
slid along the strand. No hypothesis on `a`, `b` is needed.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.KL3.Diagram
open CategoryTheory StringDiagrams QuantumGroup UDot Presentation
universe w u v
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k]

theorem diagram_eq_of_layers {S : Signature} {a b a' b' : Obj S} (f : a ⟶ b) (g : a' ⟶ b')
    (ha : a = a') (hb : b = b') (h : Diagram.layers f = Diagram.layers g) :
    f = eqToHom ha ≫ g ≫ eqToHom hb.symm := by
  subst ha hb
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact Diagram.ext h

theorem layers_zigL (c : Col I X) :
    Diagram.layers (Pivotal.zigL (inv RD).toColourDuality c) =
      layList RD c.r [([], .cup c.l, [c.l]), ([c.l], .cap c.l, [])] := by
  simp only [layList_cons, layList_nil, Pivotal.zigL, Diagram.layers_leftZigzag,
    Pivotal.cupD, Pivotal.capD, Diagram.layers_layer, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append]
  refine List.cons_eq_cons.2
    ⟨Layer.ext ?_ ?_ ?_ ?_, List.cons_eq_cons.2 ⟨Layer.ext ?_ ?_ ?_ ?_, rfl⟩⟩
  all_goals (try simp [lay, Layer.wr, Layer.wl, Shape.gen])
  all_goals rfl

theorem layers_zigR (c : Col I X) :
    Diagram.layers (Pivotal.zigR (inv RD).toColourDuality c) =
      layList RD (sh RD c.l + c.r)
        [([c.l.dual], .cup c.l, []), ([], .cap c.l, [c.l.dual])] := by
  simp only [layList_cons, layList_nil, Pivotal.zigR, Diagram.layers_rightZigzag,
    Pivotal.cupD, Pivotal.capD, Diagram.layers_layer, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append]
  refine List.cons_eq_cons.2
    ⟨Layer.ext ?_ ?_ ?_ ?_, List.cons_eq_cons.2 ⟨Layer.ext ?_ ?_ ?_ ?_, rfl⟩⟩
  all_goals (try simp [lay, Layer.wr, Layer.wl, Shape.gen, inv_dual])
  all_goals rfl

theorem ldg_zigL (μ : X) (l : Letter I) :
    ldg RD k μ [l] [l] [([], .cup l, [l]), ([l], .cap l, [])] = 𝟙 _ := by
  rw [ldg, dg_zigL]; exact (toLoc RD k).map_id _

theorem ldg_zigR (μ : X) (l : Letter I) :
    ldg RD k μ [l.dual] [l.dual] [([l.dual], .cup l, []), ([], .cap l, [l.dual])] = 𝟙 _ := by
  rw [ldg, dg_zigR]; exact (toLoc RD k).map_id _

theorem inclD_zigL (c : Col I X) :
    inclD RD (Pivotal.zigL (inv RD).toColourDuality c) =
      eqToHom (congrArg (incl RD).obj (Obj.ext rfl rfl)) ≫
        inclD RD (mkD RD c.r [([], .cup c.l, [c.l]), ([c.l], .cap c.l, [])] ⟨rfl, rfl, rfl⟩) ≫
        eqToHom (congrArg (incl RD).obj (Obj.ext rfl rfl)) :=
  diagram_eq_of_layers _ _ (congrArg (incl RD).obj (Obj.ext rfl rfl))
    (congrArg (incl RD).obj (Obj.ext rfl rfl))
    (by rw [LayerMap.layers_map, LayerMap.layers_map, layers_zigL]; rfl)

theorem dualObj_eq_ob (c : Col I X) :
    Pivotal.dualObj (inv RD).toColourDuality c = ob RD (sh RD c.l + c.r) [c.l.dual] :=
  Obj.ext (show c.r = sh RD c.l.dual + (sh RD c.l + c.r) by
    rw [← add_assoc, sh_dual_add_sh, zero_add]) rfl

theorem inclD_zigR (c : Col I X) :
    inclD RD (Pivotal.zigR (inv RD).toColourDuality c) =
      eqToHom (congrArg (incl RD).obj (dualObj_eq_ob RD c)) ≫
        inclD RD (mkD RD (sh RD c.l + c.r)
          [([c.l.dual], .cup c.l, []), ([], .cap c.l, [c.l.dual])] ⟨rfl, rfl, rfl⟩) ≫
        eqToHom (congrArg (incl RD).obj (dualObj_eq_ob RD c)).symm :=
  diagram_eq_of_layers _ _ (congrArg (incl RD).obj (dualObj_eq_ob RD c))
    (congrArg (incl RD).obj (dualObj_eq_ob RD c))
    (by rw [LayerMap.layers_map, LayerMap.layers_map, layers_zigR]; rfl)

section Zig
variable {RD k}
variable (a b : I → ℤ)

/-- `zg_local` with the local equation first, so that it determines the boundaries. -/
theorem zg_local' (ν : X) {s r r' : List (Letter I)} (t : List (Letter I))
    {A M M' : List (DStep I)} (B : List (DStep I))
    (e : zg RD k ν r r' M = zg RD k ν r r' M') (hA : DChain s A r) (hM : DChain r M r')
    (hM' : DChain r M' r') :
    zg RD k ν s t (A ++ M ++ B) = zg RD k ν s t (A ++ M' ++ B) :=
  zg_local ν t B hA hM hM' e

theorem zg_zigL_up (ν : X) (i : I) :
    zg RD k ν [up i] [up i]
      ([([], .cup (up i), [up i]), ([up i], .cap (up i), [])].flatMap (layStep a b)) =
      𝟙 _ := by
  have e : zg RD k ν ([up i] ++ [dn i] ++ [up i]) ([up i] ++ [dn i] ++ [up i])
      [.dot [up i] i [up i] (-a i), .dot [up i] i [up i] (a i)] =
      zg RD k ν ([up i] ++ [dn i] ++ [up i]) ([up i] ++ [dn i] ++ [up i]) [] := by
    rw [zg_dot_add, add_neg_cancel, zg_dot_zero]
  refine Eq.trans (zg_local' ν [up i] (s := [up i]) (A := [.lay ([], .cup (up i), [up i])])
    [.lay ([up i], .cap (up i), [])] e ⟨rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ rfl) ?_
  exact (zg_lays_all ν _ _ [_, _]).trans (ldg_zigL RD k ν (up i))

theorem zg_zigL_dn (ν : X) (i : I) :
    zg RD k ν [dn i] [dn i]
      ([([], .cup (dn i), [dn i]), ([dn i], .cap (dn i), [])].flatMap (layStep a b)) =
      𝟙 _ := by
  refine Eq.trans (zg_local' ν [dn i] (s := [dn i]) (A := [.lay ([], .cup (dn i), [dn i])])
    [.lay ([dn i], .cap (dn i), [])] (zg_dotComm ν [] [up i] [] i i (-b i) (b i))
    ⟨rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩) ?_
  refine Eq.trans (zg_local' ν [dn i] (s := [dn i]) (A := [])
    [.dot [] i ([up i] ++ [dn i] ++ []) (-b i), .lay ([dn i], .cap (dn i), [])]
    (zg_slideR ν [] [] [] (.cup (dn i)) i (b i)).symm rfl ⟨rfl, rfl, rfl⟩
    ⟨rfl, rfl, rfl⟩) ?_
  have e3 := zg_slideL (RD := RD) (k := k) ν [] [] [] (.cap (dn i)) i (-b i)
  have h3 := zg_local' ν [dn i] (s := [dn i])
    (A := [.dot [] i [] (b i), .lay ([], .cup (dn i), [dn i])]) [] e3
    ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩
  refine h3.trans ?_
  have e : zg RD k ν ([] ++ [dn i] ++ []) ([] ++ [dn i] ++ [])
      [.lay ([], .cup (dn i), [dn i]), .lay ([dn i], .cap (dn i), [])] =
      zg RD k ν ([] ++ [dn i] ++ []) ([] ++ [dn i] ++ []) [] := by
    rw [zg_nil]; exact (zg_lays_all ν _ _ [_, _]).trans (ldg_zigL RD k ν (dn i))
  refine Eq.trans (zg_local' ν [dn i] (s := [dn i]) (A := [.dot [] i [] (b i)])
    [.dot [] i [] (-b i)] e ⟨rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ rfl) ?_
  show zg RD k ν ([] ++ [dn i] ++ []) ([] ++ [dn i] ++ [])
    [.dot [] i [] (b i), .dot [] i [] (-b i)] = _
  rw [zg_dot_add, neg_add_cancel, zg_dot_zero, zg_nil]
  rfl

theorem zg_zigL (ν : X) (l : Letter I) :
    zg RD k ν ([] ++ (Shape.cup l).dom ++ [l]) ([l] ++ (Shape.cap l).cod ++ [])
      ([([], .cup l, [l]), ([l], .cap l, [])].flatMap (layStep a b)) = 𝟙 _ := by
  obtain ⟨_ | _, i⟩ := l
  · exact zg_zigL_dn a b ν i
  · exact zg_zigL_up a b ν i

variable (δ : X)

theorem shiftFree_map_zigL (c : Col I X) :
    (shiftFree RD k δ a b).map (inclD RD (Pivotal.zigL (inv RD).toColourDuality c)) =
      𝟙 _ := by
  simp only [inclD_zigL, Functor.map_comp, eqToHom_map]
  rw [shiftFree_map_mkD, imgList_eq_zg, zg_zigL]
  simp only [Category.id_comp, eqToHom_trans, eqToHom_refl]
  rfl

variable {δ}

theorem zg_zigR_up (ν : X) (i : I) :
    zg RD k ν [dn i] [dn i]
      ([([dn i], .cup (up i), []), ([], .cap (up i), [dn i])].flatMap (layStep a b)) =
      𝟙 _ := by
  have e1 := (zg_dotComm (RD := RD) (k := k) ν [] [up i] [] i i (a i) (-a i)).symm
  have h1 := zg_local' ν [dn i] (s := [dn i]) (A := [.lay ([dn i], .cup (up i), [])])
    [.lay ([], .cap (up i), [dn i])] e1 ⟨rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩
  refine h1.trans ?_
  have e2 := (zg_slideL (RD := RD) (k := k) ν [] [] [] (.cup (up i)) i (a i)).symm
  have h2 := zg_local' ν [dn i] (s := [dn i]) (A := [])
    [.dot ([dn i] ++ [up i]) i [] (-a i), .lay ([], .cap (up i), [dn i])] e2
    rfl ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩
  refine h2.trans ?_
  have e3 := zg_slideR (RD := RD) (k := k) ν [] [] [] (.cap (up i)) i (-a i)
  have h3 := zg_local' ν [dn i] (s := [dn i])
    (A := [.dot [] i [] (a i), .lay ([dn i], .cup (up i), [])]) [] e3
    ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩
  refine h3.trans ?_
  have e : zg RD k ν ([] ++ [dn i] ++ []) ([] ++ [dn i] ++ [])
      [.lay ([dn i], .cup (up i), []), .lay ([], .cap (up i), [dn i])] =
      zg RD k ν ([] ++ [dn i] ++ []) ([] ++ [dn i] ++ []) [] := by
    rw [zg_nil]; exact (zg_lays_all ν _ _ [_, _]).trans (ldg_zigR RD k ν (up i))
  refine Eq.trans (zg_local' ν [dn i] (s := [dn i]) (A := [.dot [] i [] (a i)])
    [.dot [] i [] (-a i)] e ⟨rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ rfl) ?_
  show zg RD k ν ([] ++ [dn i] ++ []) ([] ++ [dn i] ++ [])
    [.dot [] i [] (a i), .dot [] i [] (-a i)] = _
  rw [zg_dot_add, neg_add_cancel, zg_dot_zero, zg_nil]
  rfl

theorem zg_zigR_dn (ν : X) (i : I) :
    zg RD k ν [up i] [up i]
      ([([up i], .cup (dn i), []), ([], .cap (dn i), [up i])].flatMap (layStep a b)) =
      𝟙 _ := by
  have e : zg RD k ν ([up i] ++ [dn i] ++ [up i]) ([up i] ++ [dn i] ++ [up i])
      [.dot [up i] i [up i] (-b i), .dot [up i] i [up i] (b i)] =
      zg RD k ν ([up i] ++ [dn i] ++ [up i]) ([up i] ++ [dn i] ++ [up i]) [] := by
    rw [zg_dot_add, add_neg_cancel, zg_dot_zero]
  refine Eq.trans (zg_local' ν [up i] (s := [up i]) (A := [.lay ([up i], .cup (dn i), [])])
    [.lay ([], .cap (dn i), [up i])] e ⟨rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ rfl) ?_
  exact (zg_lays_all ν _ _ [_, _]).trans (ldg_zigR RD k ν (dn i))

theorem zg_zigR (ν : X) (l : Letter I) :
    zg RD k ν [l.dual] ([] ++ (Shape.cap l).cod ++ [l.dual])
      ([([l.dual], .cup l, []), ([], .cap l, [l.dual])].flatMap (layStep a b)) = 𝟙 _ := by
  obtain ⟨_ | _, i⟩ := l
  · exact zg_zigR_dn a b ν i
  · exact zg_zigR_up a b ν i

variable (δ)

theorem shiftFree_map_zigR (c : Col I X) :
    (shiftFree RD k δ a b).map (inclD RD (Pivotal.zigR (inv RD).toColourDuality c)) =
      𝟙 _ := by
  simp only [inclD_zigR, Functor.map_comp, eqToHom_map]
  rw [shiftFree_map_mkD, imgList_eq_zg, zg_zigR]
  simp only [Category.id_comp, eqToHom_trans, eqToHom_refl]

variable (RD k)

/-- **The left zigzag relation** holds for the images of the weight shift. -/
theorem shift_rel_zigL (c : Col I X) :
    (freeLift k (shiftFree RD k δ a b)).map ((presLoc RD k).rel (.inl (.inl (.inr (.inl c))))) =
      0 := by
  have e : (presLoc RD k).rel (.inl (.inl (.inr (.inl c)))) =
      inclLin RD k (LinDiagram.of (Pivotal.zigL (inv RD).toColourDuality c) -
        LinDiagram.of (𝟙 _)) := rfl
  rw [e, map_sub, inclLin_of, inclLin_of, Functor.map_sub, freeLift_map_of, freeLift_map_of,
    shiftFree_map_zigL]
  exact sub_eq_zero.2 ((shiftFree RD k δ a b).map_id _).symm

/-- **The right zigzag relation** holds for the images of the weight shift. -/
theorem shift_rel_zigR (c : Col I X) :
    (freeLift k (shiftFree RD k δ a b)).map ((presLoc RD k).rel (.inl (.inl (.inr (.inr c))))) =
      0 := by
  have e : (presLoc RD k).rel (.inl (.inl (.inr (.inr c)))) =
      inclLin RD k (LinDiagram.of (Pivotal.zigR (inv RD).toColourDuality c) -
        LinDiagram.of (𝟙 _)) := rfl
  rw [e, map_sub, inclLin_of, inclLin_of, Functor.map_sub, freeLift_map_of, freeLift_map_of,
    shiftFree_map_zigR]
  exact sub_eq_zero.2 ((shiftFree RD k δ a b).map_id _).symm

end Zig
end Categorification.KL3.Diagram

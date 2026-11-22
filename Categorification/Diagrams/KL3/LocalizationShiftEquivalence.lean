/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.LocalizationShiftFunctor
import Categorification.Diagrams.KL3.LiftGenComp

/-!
# The weight shift of `U′` is an equivalence (Webster Prop. 3.30)

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
Proposition 3.30. Under Webster's condition `a i - b i = -⟨i, δ⟩`, the weight shift
`shiftFunctorOf hab` of the presented category of `U′` and the reverse shift
`shiftFunctorInv hab` (by `-δ`, with exponents `-a`, `-b`) are mutually inverse up to natural
isomorphisms with `eqToHom` components.

* `shiftCompIso`: two shifts with `δ + δ' = 0`, `a + a' = 0`, `b + b' = 0` compose to a functor
  isomorphic to the identity (via `isoIdOfLiftGenComp`; the generator check is `shift_hgen`,
  where the dots on cups and caps cancel).
* `shiftEquivalence`: the equivalence of the presented category of `U′`.
* `shiftHomEquivalence`: its restriction to Hom categories, `U′(μ, μ') ≌ U′(μ + δ, μ' + δ)`.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.KL3.Diagram
open CategoryTheory StringDiagrams QuantumGroup UDot Presentation
universe w u v u₀ u₁ u₂ w' v'

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k]

/-- A functor sends integer powers of a unit to integer powers of its image. -/
theorem functor_map_units_zpow {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (F : 𝒞 ⥤ 𝒟) {x : 𝒞}
    {y : 𝒟} (h : F.obj x = y) (U : (End x)ˣ) (U' : (End y)ˣ)
    (hU : F.map (U : End x) = eqToHom h ≫ (U' : End y) ≫ eqToHom h.symm) (n : ℤ) :
    F.map ((U ^ n : (End x)ˣ) : End x) =
      eqToHom h ≫ ((U' ^ n : (End y)ˣ) : End y) ≫ eqToHom h.symm := by
  subst h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hU ⊢
  have e : Units.map (F.mapEnd x) U = U' := Units.ext hU
  rw [← e, ← map_zpow]
  rfl

/-- The shifts by `δ` and `δ'` with `δ + δ' = 0` compose to the identity on objects. -/
theorem shiftMap_obj_obj (δ δ' : X) (hδ : δ + δ' = 0) (a : Obj (lsig RD)) :
    (shiftMap RD δ').obj ((shiftMap RD δ).obj a) = a := by
  refine Obj.ext ?_ ?_
  · show @HAdd.hAdd X X X _ (@HAdd.hAdd X X X _ a.start δ) δ' = a.start
    rw [add_assoc, hδ, add_zero]
  · show List.map _ (List.map _ a.word) = a.word
    rw [List.map_map]
    conv_rhs => rw [← List.map_id a.word]
    refine List.map_congr_left fun c _ => ?_
    obtain ⟨l, r⟩ := c
    show (⟨l, r + δ + δ'⟩ : Col I X) = ⟨l, r⟩
    rw [add_assoc, hδ, add_zero]

theorem shiftMap_word_word (δ δ' : X) (hδ : δ + δ' = 0) (w : List (Col I X)) :
    (shiftMap RD δ').word ((shiftMap RD δ).word w) = w := by
  have := shiftMap_obj_obj RD δ δ' hδ ⟨(0 : X), w⟩
  exact congrArg Obj.word this

theorem shiftMap_nonempty (δ : X) (g : (lsig RD).Gen) :
    Nonempty (LocalMap.genDom (shiftMap RD δ) g ⟶ LocalMap.genCod (shiftMap RD δ) g) := by
  rcases g with ((g0 | c | c) | p)
  · rcases g0 with c | ⟨ε, i, j, ν⟩
    · rw [genDom_dot, genCod_dot]; exact ⟨lgenD RD (c.r + δ) (.dot c.l)⟩
    · rw [genDom_cross, genCod_cross]; exact ⟨lgenD RD (ν + δ) (.cross ε i j)⟩
  · rw [genDom_cup, genCod_cup]; exact ⟨lgenD RD (sh RD c.l + c.r + δ) (.cup c.l)⟩
  · rw [genDom_cap, genCod_cap]; exact ⟨lgenD RD (c.r + δ) (.cap c.l)⟩
  · have e : LocalMap.genCod (shiftMap RD δ) (.inr p : (lsig RD).Gen) =
        LocalMap.genDom (shiftMap RD δ) (.inr p : (lsig RD).Gen) := rfl
    rw [e, genDom_inv]; exact ⟨invDotF RD p.1 (p.2 + δ)⟩

/-- Diagrams with the same layers agree up to `eqToHom` conjugation. -/
theorem eqToHom_diag_eqToHom {S : Signature.{u₀, u₁, u₂}} {R : Type w'} [CommRing R]
    (P : Presentation.{w', v'} S R)
    {a b a' b' : Obj S} (d : Diagram a b) (d' : Diagram a' b')
    (h : Diagram.layers d = Diagram.layers d')
    {x y : P.Presented} (p : x = P.obj a) (q : P.obj b = y) (p' : x = P.obj a')
    (q' : P.obj b' = y) :
    eqToHom p ≫ P.diag d ≫ eqToHom q = eqToHom p' ≫ P.diag d' ≫ eqToHom q' := by
  have ha : a = a' := congrArg (fun z : P.Presented => z.as) (p.symm.trans p')
  have hb : b = b' := congrArg (fun z : P.Presented => z.as) (q.trans q'.symm)
  rw [P.diag_eq_of_layers_eq' d d' ha hb h]
  simp

theorem diag_eqToHom_eq {S : Signature.{u₀, u₁, u₂}} {R : Type w'} [CommRing R]
    (P : Presentation.{w', v'} S R)
    {a b a' b' : Obj S} (d : Diagram a b) (d' : Diagram a' b')
    (h : Diagram.layers d = Diagram.layers d') {y : P.Presented} (q : P.obj b = y)
    (p' : P.obj a = P.obj a') (q' : P.obj b' = y) :
    P.diag d ≫ eqToHom q = eqToHom p' ≫ P.diag d' ≫ eqToHom q' := by
  simpa using eqToHom_diag_eqToHom P d d' h rfl q p' q'

theorem eqToHom_diag_eq {S : Signature.{u₀, u₁, u₂}} {R : Type w'} [CommRing R]
    (P : Presentation.{w', v'} S R)
    {a b a' b' : Obj S} (d : Diagram a b) (d' : Diagram a' b')
    (h : Diagram.layers d = Diagram.layers d') {x : P.Presented} (p : x = P.obj a)
    (p' : x = P.obj a') (q' : P.obj b' = P.obj b) :
    eqToHom p ≫ P.diag d = eqToHom p' ≫ P.diag d' ≫ eqToHom q' := by
  simpa using eqToHom_diag_eqToHom P d d' h p rfl p' q'

/-- Integer dot powers with exponents summing to zero cancel. -/
theorem zdot_cancel_assoc (ν : X) (u : List (Letter I)) (i : I) (v : List (Letter I))
    {m n : ℤ} (h : m + n = 0) {Z : (presLoc RD k).Presented}
    (f : lob RD k ν (u ++ [dn i] ++ v) ⟶ Z) :
    zdot RD k ν u i v n ≫ zdot RD k ν u i v m ≫ f = f := by
  rw [← Category.assoc, ← zdot_add, h, zdot_zero, Category.id_comp]

section Shift

variable (δ' : X) (a' b' : I → ℤ) (h' : ShiftRelations RD k δ' a' b')

theorem shiftFunctor_map_diag {p q : Obj (lsig RD)} (d : p ⟶ q) :
    (shiftFunctor RD k δ' a' b' h').map ((presLoc RD k).diag d) =
      (shiftFree RD k δ' a' b').map d :=
  LocalMap.liftGen_diag _ _ _ _ d

theorem shiftFunctor_map_ldot (ν : X) (u : List (Letter I)) (i : I) (v : List (Letter I)) :
    (shiftFunctor RD k δ' a' b' h').map (ldot RD k ν u i v) =
      eqToHom (shiftFree_obj_ob RD k δ' a' b' ν _) ≫ ldot RD k (ν + δ') u i v ≫
        eqToHom (shiftFree_obj_ob RD k δ' a' b' ν _).symm := by
  rw [ldot, shiftFunctor_map_diag, shiftFree_map_mkD]
  simp only [imgList, imgLay, eqToHom_refl, Category.id_comp, Category.comp_id]
  rw [ldg_of]
  rfl

theorem shiftFunctor_map_zdot (ν : X) (u : List (Letter I)) (i : I) (v : List (Letter I))
    (n : ℤ) :
    (shiftFunctor RD k δ' a' b' h').map (zdot RD k ν u i v n) =
      eqToHom (shiftFree_obj_ob RD k δ' a' b' ν _) ≫ zdot RD k (ν + δ') u i v n ≫
        eqToHom (shiftFree_obj_ob RD k δ' a' b' ν _).symm :=
  functor_map_units_zpow (shiftFunctor RD k δ' a' b' h')
    (shiftFree_obj_ob RD k δ' a' b' ν _ :
      (shiftFunctor RD k δ' a' b' h').obj (lob RD k ν (u ++ [dn i] ++ v)) = _)
    (dotUnit RD k ν u i v)
    (dotUnit RD k (ν + δ') u i v) (shiftFunctor_map_ldot RD k δ' a' b' h' ν u i v) n

variable (δ : X) (a b : I → ℤ) (hδ : δ + δ' = 0) (hA : ∀ i, a i + a' i = 0)
  (hB : ∀ i, b i + b' i = 0)

include hδ in
theorem shift_hgen_dot (c : Col I X)
    (hbv : (bareLayer (S := lsig RD) (.inl (.gen (.dot c)))).Valid) :
    (shiftFunctor RD k δ' a' b' h').map (shiftImg RD k δ a b (.inl (.gen (.dot c)))) =
      eqToHom (congrArg (presLoc RD k).obj (genDom_comp (shiftMap RD δ) (shiftMap RD δ')
        (shiftMap_obj_obj RD δ δ' hδ) (.inl (.gen (.dot c))))) ≫
        (presLoc RD k).diag (Diagram.ofLayer _ hbv) ≫
          eqToHom (congrArg (presLoc RD k).obj (genCod_comp (shiftMap RD δ) (shiftMap RD δ')
            (shiftMap_obj_obj RD δ δ' hδ) (.inl (.gen (.dot c)))).symm) := by
  simp only [shiftImg, Functor.map_comp, eqToHom_map, lgen, shiftFunctor_map_diag,
    shiftFree_map_mkD, imgList, imgLay, eqToHom_refl, Category.id_comp, Category.comp_id,
    Category.assoc, eqToHom_trans_assoc]
  rw [show ldg RD k (c.r + δ + δ') ([] ++ (Shape.dot c.l).dom ++ [])
      ([] ++ (Shape.dot c.l).cod ++ []) [([], Shape.dot c.l, [])] = _ from
    ldg_of RD k (μ := c.r + δ + δ') (sChain_single ([], Shape.dot c.l, []))]
  simp only [← Category.assoc, eqToHom_trans]
  simp only [Category.assoc]
  refine eqToHom_diag_eqToHom _ _ _ ?_ _ _ _ _
  show [_] = [_]
  congr 1
  refine Layer.ext ?_ rfl ?_ rfl
  · show wt RD (c.r + δ + δ') ([] ++ [c.l] ++ []) = (psig RD).left ((Shape.dot c.l).gen RD c.r)
    rw [Shape.left_gen, add_assoc, hδ, add_zero]
    rfl
  · show (Sum.inl (Shape.gen RD (c.r + δ + δ') (.dot c.l)) : (lsig RD).Gen) =
      Sum.inl (Shape.gen RD c.r (.dot c.l))
    rw [add_assoc, hδ, add_zero]

include hδ hA hB in
theorem shift_hgen_cup (c : Col I X)
    (hbv : (bareLayer (S := lsig RD) (.inl (.cup c))).Valid) :
    (shiftFunctor RD k δ' a' b' h').map (shiftImg RD k δ a b (.inl (.cup c))) =
      eqToHom (congrArg (presLoc RD k).obj (genDom_comp (shiftMap RD δ) (shiftMap RD δ')
        (shiftMap_obj_obj RD δ δ' hδ) (.inl (.cup c)))) ≫
        (presLoc RD k).diag (Diagram.ofLayer _ hbv) ≫
          eqToHom (congrArg (presLoc RD k).obj (genCod_comp (shiftMap RD δ) (shiftMap RD δ')
            (shiftMap_obj_obj RD δ δ' hδ) (.inl (.cup c))).symm) := by
  obtain ⟨⟨_ | _, i⟩, r⟩ := c
  · simp only [shiftImg, cupImg, cupDec, Functor.map_comp, eqToHom_map, lgen,
      shiftFunctor_map_diag,
      shiftFree_map_mkD, imgList, imgLay, cupDecAt, shiftFunctor_map_zdot, eqToHom_refl,
      Category.id_comp, Category.comp_id, Category.assoc, eqToHom_trans_assoc]
    erw [zdot_cancel_assoc RD k _ _ _ _ (show -b i + -b' i = 0 by have := hB i; omega)]
    rw [show ldg RD k (sh RD (false, i) + r + δ + δ') ([] ++ (Shape.cup (false, i)).dom ++ [])
        ([] ++ [(false, i), Letter.dual (false, i)] ++ []) [([], Shape.cup (false, i), [])] = _ from
        ldg_of RD k (μ := sh RD (false, i) + r + δ + δ')
          (sChain_single ([], .cup (false, i), [])),
      eqToHom_trans]
    refine diag_eqToHom_eq _ _ _ ?_ _ _ _
    show [_] = [_]
    congr 1
    refine Layer.ext ?_ rfl ?_ rfl
    · show sh RD (false, i) + r + δ + δ' = sh RD (false, i) + r
      rw [add_assoc _ δ, hδ, add_zero]
    · have e : sh RD (Letter.dual (false, i)) + (sh RD (false, i) + r + δ + δ') = r := by
        rw [sh_dual, add_assoc _ δ, hδ, add_zero]; abel
      show (Sum.inl (PivotalGen.cup ⟨(false, i), sh RD (Letter.dual (false, i)) +
        (sh RD (false, i) + r + δ + δ')⟩) : (lsig RD).Gen) =
          Sum.inl (PivotalGen.cup ⟨(false, i), r⟩)
      rw [e]
  · simp only [shiftImg, cupImg, cupDec, Functor.map_comp, eqToHom_map, lgen,
      shiftFunctor_map_diag,
      shiftFree_map_mkD, imgList, imgLay, cupDecAt, shiftFunctor_map_zdot, eqToHom_refl,
      Category.id_comp, Category.comp_id, Category.assoc, eqToHom_trans_assoc]
    erw [zdot_cancel_assoc RD k _ _ _ _ (show -a i + -a' i = 0 by have := hA i; omega)]
    rw [show ldg RD k (sh RD (true, i) + r + δ + δ') ([] ++ (Shape.cup (true, i)).dom ++ [])
        ([] ++ [(true, i), Letter.dual (true, i)] ++ []) [([], Shape.cup (true, i), [])] = _ from
        ldg_of RD k (μ := sh RD (true, i) + r + δ + δ')
          (sChain_single ([], .cup (true, i), [])),
      eqToHom_trans]
    refine diag_eqToHom_eq _ _ _ ?_ _ _ _
    show [_] = [_]
    congr 1
    refine Layer.ext ?_ rfl ?_ rfl
    · show sh RD (true, i) + r + δ + δ' = sh RD (true, i) + r
      rw [add_assoc _ δ, hδ, add_zero]
    · have e : sh RD (Letter.dual (true, i)) + (sh RD (true, i) + r + δ + δ') = r := by
        rw [sh_dual, add_assoc _ δ, hδ, add_zero]; abel
      show (Sum.inl (PivotalGen.cup ⟨(true, i), sh RD (Letter.dual (true, i)) +
        (sh RD (true, i) + r + δ + δ')⟩) : (lsig RD).Gen) =
          Sum.inl (PivotalGen.cup ⟨(true, i), r⟩)
      rw [e]

include hδ in
theorem shift_hgen_cross (ε : Bool) (i j : I) (ν : X)
    (hbv : (bareLayer (S := lsig RD) (.inl (.gen (.cross ε i j ν)))).Valid) :
    (shiftFunctor RD k δ' a' b' h').map (shiftImg RD k δ a b (.inl (.gen (.cross ε i j ν)))) =
      eqToHom (congrArg (presLoc RD k).obj (genDom_comp (shiftMap RD δ) (shiftMap RD δ')
        (shiftMap_obj_obj RD δ δ' hδ) (.inl (.gen (.cross ε i j ν))))) ≫
        (presLoc RD k).diag (Diagram.ofLayer _ hbv) ≫
          eqToHom (congrArg (presLoc RD k).obj (genCod_comp (shiftMap RD δ) (shiftMap RD δ')
            (shiftMap_obj_obj RD δ δ' hδ) (.inl (.gen (.cross ε i j ν)))).symm) := by
  simp only [shiftImg, Functor.map_comp, eqToHom_map, lgen, shiftFunctor_map_diag,
    shiftFree_map_mkD, imgList, imgLay, eqToHom_refl, Category.id_comp, Category.comp_id,
    Category.assoc, eqToHom_trans_assoc]
  rw [show ldg RD k (ν + δ + δ') ([] ++ (Shape.cross ε i j).dom ++ [])
      ([] ++ (Shape.cross ε i j).cod ++ []) [([], Shape.cross ε i j, [])] = _ from
    ldg_of RD k (μ := ν + δ + δ') (sChain_single ([], Shape.cross ε i j, []))]
  simp only [← Category.assoc, eqToHom_trans]
  simp only [Category.assoc]
  refine eqToHom_diag_eqToHom _ _ _ ?_ _ _ _ _
  show [_] = [_]
  congr 1
  refine Layer.ext ?_ rfl ?_ rfl
  · show wt RD (ν + δ + δ') ([] ++ (Shape.cross ε i j).dom ++ []) =
      (psig RD).left ((Shape.cross ε i j).gen RD ν)
    rw [Shape.left_gen, add_assoc, hδ, add_zero]
    rfl
  · show (Sum.inl (Shape.gen RD (ν + δ + δ') (.cross ε i j)) : (lsig RD).Gen) =
      Sum.inl (Shape.gen RD ν (.cross ε i j))
    rw [add_assoc, hδ, add_zero]

include hδ in
theorem shift_hgen_inv (p : I × X)
    (hbv : (bareLayer (S := lsig RD) (.inr p)).Valid) :
    (shiftFunctor RD k δ' a' b' h').map (shiftImg RD k δ a b (.inr p)) =
      eqToHom (congrArg (presLoc RD k).obj (genDom_comp (shiftMap RD δ) (shiftMap RD δ')
        (shiftMap_obj_obj RD δ δ' hδ) (.inr p))) ≫
        (presLoc RD k).diag (Diagram.ofLayer _ hbv) ≫
          eqToHom (congrArg (presLoc RD k).obj (genCod_comp (shiftMap RD δ) (shiftMap RD δ')
            (shiftMap_obj_obj RD δ δ' hδ) (.inr p)).symm) := by
  simp only [shiftImg, Functor.map_comp, eqToHom_map, shiftFunctor_map_diag,
    shiftFree_map_invDotF, Category.assoc, eqToHom_trans_assoc]
  simp only [← Category.assoc, eqToHom_trans]
  simp only [Category.assoc]
  refine eqToHom_diag_eqToHom _ _ _ ?_ _ _ _ _
  show [_] = [_]
  congr 1
  refine Layer.ext ?_ rfl ?_ rfl
  · show wt RD (p.2 + δ + δ') ([] ++ [dn p.1] ++ []) = (lsig RD).left (.inr p)
    rw [add_assoc, hδ, add_zero]
    rfl
  · show (Sum.inr (p.1, wt RD (p.2 + δ + δ') []) : (lsig RD).Gen) = Sum.inr p
    show (Sum.inr (p.1, p.2 + δ + δ') : (lsig RD).Gen) = Sum.inr p
    rw [add_assoc, hδ, add_zero]

include hδ hA hB in
theorem shift_hgen_cap (c : Col I X)
    (hbv : (bareLayer (S := lsig RD) (.inl (.cap c))).Valid) :
    (shiftFunctor RD k δ' a' b' h').map (shiftImg RD k δ a b (.inl (.cap c))) =
      eqToHom (congrArg (presLoc RD k).obj (genDom_comp (shiftMap RD δ) (shiftMap RD δ')
        (shiftMap_obj_obj RD δ δ' hδ) (.inl (.cap c)))) ≫
        (presLoc RD k).diag (Diagram.ofLayer _ hbv) ≫
          eqToHom (congrArg (presLoc RD k).obj (genCod_comp (shiftMap RD δ) (shiftMap RD δ')
            (shiftMap_obj_obj RD δ δ' hδ) (.inl (.cap c))).symm) := by
  obtain ⟨⟨_ | _, i⟩, r⟩ := c
  · simp only [shiftImg, capImg, capDec, Functor.map_comp, eqToHom_map, lgen,
      shiftFunctor_map_diag, shiftFree_map_mkD, imgList, imgLay, capDecAt,
      shiftFunctor_map_zdot, eqToHom_refl, Category.id_comp, Category.comp_id, Category.assoc,
      eqToHom_trans_assoc]
    erw [zdot_cancel_assoc RD k _ _ _ _ (show b' i + b i = 0 by have := hB i; omega)]
    rw [show ldg RD k (r + δ + δ') ([] ++ [Letter.dual (false, i), (false, i)] ++ [])
        ([] ++ (Shape.cap (false, i)).cod ++ []) [([], Shape.cap (false, i), [])] = _ from
        ldg_of RD k (μ := r + δ + δ') (sChain_single ([], .cap (false, i), []))]
    refine eqToHom_diag_eq _ _ _ ?_ _ _ _
    show [_] = [_]
    congr 1
    refine Layer.ext ?_ rfl ?_ rfl
    · show wt RD (r + δ + δ') ([] ++ [Letter.dual (false, i), (false, i)] ++ []) =
        (psig RD).left ((Shape.cap (false, i)).gen RD r)
      rw [Shape.left_gen, add_assoc, hδ, add_zero]
      rfl
    · show (Sum.inl (PivotalGen.cap ⟨(false, i), r + δ + δ'⟩) : (lsig RD).Gen) =
        Sum.inl (PivotalGen.cap ⟨(false, i), r⟩)
      rw [add_assoc, hδ, add_zero]
  · simp only [shiftImg, capImg, capDec, Functor.map_comp, eqToHom_map, lgen,
      shiftFunctor_map_diag, shiftFree_map_mkD, imgList, imgLay, capDecAt,
      shiftFunctor_map_zdot, eqToHom_refl, Category.id_comp, Category.comp_id, Category.assoc,
      eqToHom_trans_assoc]
    erw [zdot_cancel_assoc RD k _ _ _ _ (show a' i + a i = 0 by have := hA i; omega)]
    rw [show ldg RD k (r + δ + δ') ([] ++ [Letter.dual (true, i), (true, i)] ++ [])
        ([] ++ (Shape.cap (true, i)).cod ++ []) [([], Shape.cap (true, i), [])] = _ from
        ldg_of RD k (μ := r + δ + δ') (sChain_single ([], .cap (true, i), []))]
    refine eqToHom_diag_eq _ _ _ ?_ _ _ _
    show [_] = [_]
    congr 1
    refine Layer.ext ?_ rfl ?_ rfl
    · show wt RD (r + δ + δ') ([] ++ [Letter.dual (true, i), (true, i)] ++ []) =
        (psig RD).left ((Shape.cap (true, i)).gen RD r)
      rw [Shape.left_gen, add_assoc, hδ, add_zero]
      rfl
    · show (Sum.inl (PivotalGen.cap ⟨(true, i), r + δ + δ'⟩) : (lsig RD).Gen) =
        Sum.inl (PivotalGen.cap ⟨(true, i), r⟩)
      rw [add_assoc, hδ, add_zero]


include hδ hA hB in
/-- The composite of two opposite weight shifts sends every generator to itself. -/
theorem shift_hgen (g : (lsig RD).Gen) (hb : (bareLayer g).Valid) :
    (shiftFunctor RD k δ' a' b' h').map (shiftImg RD k δ a b g) =
      eqToHom (congrArg (presLoc RD k).obj (genDom_comp (shiftMap RD δ) (shiftMap RD δ')
        (shiftMap_obj_obj RD δ δ' hδ) g)) ≫
        (presLoc RD k).diag (Diagram.ofLayer _ hb) ≫
          eqToHom (congrArg (presLoc RD k).obj (genCod_comp (shiftMap RD δ) (shiftMap RD δ')
            (shiftMap_obj_obj RD δ δ' hδ) g).symm) := by
  rcases g with ((g0 | c | c) | p)
  · rcases g0 with (c | ⟨ε, i, j, ν⟩)
    · exact shift_hgen_dot RD k δ' a' b' h' δ a b hδ c hb
    · exact shift_hgen_cross RD k δ' a' b' h' δ a b hδ ε i j ν hb
  · exact shift_hgen_cup RD k δ' a' b' h' δ a b hδ hA hB c hb
  · exact shift_hgen_cap RD k δ' a' b' h' δ a b hδ hA hB c hb
  · exact shift_hgen_inv RD k δ' a' b' h' δ a b hδ p hb

/-- The weight shifts by `δ` and by `δ'` with `δ + δ' = 0` and opposite exponents compose to a
functor isomorphic to the identity, with `eqToHom` components. -/
def shiftCompIso (h : ShiftRelations RD k δ a b) :
    shiftFunctor RD k δ a b h ⋙ shiftFunctor RD k δ' a' b' h' ≅ 𝟭 (presLoc RD k).Presented :=
  isoIdOfLiftGenComp (shiftMap RD δ) (shiftMap RD δ') (shiftImg RD k δ a b)
    (shiftImg_parity RD k δ a b) h (shiftImg RD k δ' a' b') (shiftImg_parity RD k δ' a' b') h'
    (shiftMap_obj_obj RD δ δ' hδ) (shiftMap_word_word RD δ δ' hδ)
    (fun g _ => shiftMap_nonempty RD δ g) (shift_hgen RD k δ' a' b' h' δ a b hδ hA hB)

theorem shiftCompIso_hom_app (h : ShiftRelations RD k δ a b) (x : (presLoc RD k).Presented) :
    (shiftCompIso RD k δ' a' b' h' δ a b hδ hA hB h).hom.app x =
      eqToHom (congrArg (presLoc RD k).obj (shiftMap_obj_obj RD δ δ' hδ x.as)) :=
  isoIdOfLiftGenComp_hom_app _ _ _ _ _ _ _ _ _ _ _ _ x.as

theorem shiftCompIso_inv_app (h : ShiftRelations RD k δ a b) (x : (presLoc RD k).Presented) :
    (shiftCompIso RD k δ' a' b' h' δ a b hδ hA hB h).inv.app x =
      eqToHom (congrArg (presLoc RD k).obj (shiftMap_obj_obj RD δ δ' hδ x.as)).symm := by
  rw [← cancel_epi ((shiftCompIso RD k δ' a' b' h' δ a b hδ hA hB h).hom.app x),
    Iso.hom_inv_id_app, shiftCompIso_hom_app, eqToHom_trans, eqToHom_refl]

end Shift

section Equivalence

variable [DecidableEq I] (δ : X) (a b : I → ℤ)

/-- **The weight shift of `U′` is an equivalence** (Webster arXiv:1309.3796v2,
Proposition 3.30), under Webster's condition `a i - b i = -⟨i, δ⟩`; its inverse is the shift by
`-δ` with exponents `-a`, `-b`, and the unit and counit have `eqToHom` components. -/
def shiftEquivalence (hab : ∀ i, a i - b i = -ip RD i δ) :
    (presLoc RD k).Presented ≌ (presLoc RD k).Presented where
  functor := shiftFunctorOf RD k δ a b hab
  inverse := shiftFunctorInv RD k δ a b hab
  unitIso := (shiftCompIso RD k (-δ) (fun i => -a i) (fun i => -b i)
    (shiftRelations RD k (-δ) (fun i => -a i) (fun i => -b i) (shift_neg_condition RD δ a b hab))
    δ a b
    (add_neg_cancel δ) (fun i => add_neg_cancel (a i)) (fun i => add_neg_cancel (b i))
    (shiftRelations RD k δ a b hab)).symm
  counitIso := shiftCompIso RD k δ a b (shiftRelations RD k δ a b hab) (-δ) (fun i => -a i)
    (fun i => -b i)
    (neg_add_cancel δ) (fun i => neg_add_cancel (a i)) (fun i => neg_add_cancel (b i))
    (shiftRelations RD k (-δ) (fun i => -a i) (fun i => -b i) (shift_neg_condition RD δ a b hab))
  functor_unitIso_comp x := by
    simp only [Iso.symm_hom, shiftCompIso_hom_app, shiftCompIso_inv_app, eqToHom_map,
      eqToHom_trans, eqToHom_refl]

end Equivalence

/-- An equivalence restricts to full subcategories `P`, `Q` when its functor sends `P` into `Q`
and its inverse sends `Q` into `P`. -/
def equivalenceFullSubcategory {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (e : 𝒞 ≌ 𝒟)
    (P : ObjectProperty 𝒞) (Q : ObjectProperty 𝒟) (hF : ∀ x, P x → Q (e.functor.obj x))
    (hG : ∀ y, Q y → P (e.inverse.obj y)) : P.FullSubcategory ≌ Q.FullSubcategory where
  functor := Q.lift (P.ι ⋙ e.functor) (fun x => hF _ x.property)
  inverse := P.lift (Q.ι ⋙ e.inverse) (fun y => hG _ y.property)
  unitIso := (P.fullyFaithfulι.whiskeringRight _).preimageIso (P.ι.isoWhiskerLeft e.unitIso)
  counitIso := (Q.fullyFaithfulι.whiskeringRight _).preimageIso
    (Q.ι.isoWhiskerLeft e.counitIso)
  functor_unitIso_comp x := ObjectProperty.hom_ext _ (e.functor_unit_comp x.obj)

theorem lsig_endR_shift (δ : X) (r : X) (w : List (Col I X)) :
    (lsig RD).endR (@HAdd.hAdd X X X _ r δ) (w.map (shiftMap RD δ).colour) =
      @HAdd.hAdd X X X _ ((lsig RD).endR r w) δ := by
  induction w generalizing r with
  | nil => rfl
  | cons c w ih => exact ih c.r

theorem shiftMap_endR (δ : X) (x : Obj (lsig RD)) :
    ((shiftMap RD δ).obj x).endR = @HAdd.hAdd X X X _ x.endR δ :=
  lsig_endR_shift RD δ x.start x.word

/-- The objects of `U′` (the 1-morphisms `μ → μ'`) with rightmost region `μ` and leftmost
region `μ'`: the Hom category `U′(μ, μ')`. -/
def homWeights (μ μ' : X) : ObjectProperty (presLoc RD k).Presented :=
  fun x => x.as.endR = μ ∧ x.as.start = μ'

theorem shiftFunctor_homWeights {δ : X} {a b : I → ℤ} (h : ShiftRelations RD k δ a b)
    {μ μ' : X} (x : (presLoc RD k).Presented) (hx : homWeights RD k μ μ' x) :
    homWeights RD k (μ + δ) (μ' + δ) ((shiftFunctor RD k δ a b h).obj x) :=
  ⟨(shiftMap_endR RD δ x.as).trans (congrArg (· + δ) hx.1), congrArg (· + δ) hx.2⟩

section HomEquivalence

variable [DecidableEq I] (δ : X) (a b : I → ℤ)

/-- **Webster arXiv:1309.3796v2, Proposition 3.30**, on Hom categories: under Webster's
condition `a i - b i = -⟨i, δ⟩`, the weight shift is an equivalence
`U′(μ, μ') ≌ U′(μ + δ, μ' + δ)`. -/
def shiftHomEquivalence (hab : ∀ i, a i - b i = -ip RD i δ) (μ μ' : X) :
    (homWeights RD k μ μ').FullSubcategory ≌
      (homWeights RD k (μ + δ) (μ' + δ)).FullSubcategory :=
  equivalenceFullSubcategory (shiftEquivalence RD k δ a b hab) _ _
    (fun x hx => shiftFunctor_homWeights RD k (shiftRelations RD k δ a b hab) x hx)
    (fun y hy => by
      have h := shiftFunctor_homWeights RD k
        (shiftRelations RD k (-δ) (fun i => -a i) (fun i => -b i)
          (shift_neg_condition RD δ a b hab)) y hy
      simp only [add_neg_cancel_right] at h
      exact h)

end HomEquivalence

end Categorification.KL3.Diagram

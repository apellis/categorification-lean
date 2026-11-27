/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CL.CycMixed
import Categorification.Diagrams.CL.DownKLR

/-!
# Rotation of all normal-form diagrams in a presentation on the signature of `U`

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, §2.2 (`sec:cycbiadjoint`, eqs. `eq_cyclic_dot`, `eq_almost_cyclic`, p. 6).

`Categorification.Diagrams.CL.Rotate` computes the rotation by `180°` (`rotC`, the right mate for
nested cups and caps) of normal-form diagrams all of whose generators are upward. Here the same
computation is done for diagrams with arbitrary generators, given a scalar `σ g` for every shape
`g` such that the (unstraightened) rotation `rotRaw` of the generator `g` is `σ g` times the
rotated generator `rotSh g` (`hσ`):

* `rotC_dgW`: **the rotation of a normal-form diagram is the diagram of the rotated layers in
  reversed order** (`rotLs`), times the product of the scalars `σ g` of its generators.

For `U_Q(g)` (`presCL`), with the zigzag relations, `eq_cyclic_dot` and `eq_almost_cyclic`:

* `dgC_rotRaw_gen`: every generator satisfies `hσ` with `σ = sigmaCL`: `t_{ij}` for the upward
  crossing `E_j E_i ⟶ E_i E_j`, `t_{ji}^{-1}` for the downward crossing `F_j F_i ⟶ F_i F_j`, `1`
  for dots, cups and caps. The downward generators are first written as left rotations of upward
  ones (`cycDotL`, `cycCrossL`), whose right rotation straightens by the zigzag relations
  (`dgC_rotRaw_rotDotL`, `dgC_rotRaw_rotCrossL`); no cyclicity is used.
* `rotC_dgCL`: **the rotation by `180°` of every normal-form diagram of `U_Q(g)`**.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Categorification.KL3.Diagram.CL

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation Bicategory

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {k : Type w} [CommRing k]

section RotW

variable {P : Presentation.{w, max u v} (psig RD) k} {hz : P.PivotalZigzags (inv RD).toColourDuality}

local notation "BBC" => biadj (pivotalBiadj (inv RD) P hz)

variable (σ : Shape I → k)
  (hσ : ∀ (g : Shape I) (μ : X),
    dgC P μ (rd g.cod) (rd g.dom) (rotRaw g.dom g.cod [([], g, [])]) =
      σ g • dgC P μ (rd g.cod) (rd g.dom) [([], rotSh g, [])])

include hσ in
/-- **The rotation of a generator**: its mate is `σ g` times the rotated generator. -/
theorem mateC_genW (ν μ : X) (g : Shape I) (h₁ : wt RD ν g.dom = μ)
    (h₂ : wt RD ν g.cod = μ) :
    ∃ Z, mateC P hz (obC P ν μ g.dom h₁) (obC P ν μ g.cod h₂)
        (dgC P ν g.dom g.cod [([], g, [])]) = σ g • Z ∧
      IsDgC P Z (layList RD μ [([], rotSh g, [])]) := by
  have hg₀ : SChain g.dom [([], g, [])] g.cod := by simp
  have hc : SChain (rd g.cod) [([], rotSh g, [])] (rd g.dom) := by
    simp [rotSh_dom, rotSh_cod]
  refine ⟨eqToHom (congrArg P.obj (congrArg Bicat.Hom.obj (dual_obC P ν μ g.cod h₂))) ≫
      dgC P μ (rd g.cod) (rd g.dom) [([], rotSh g, [])] ≫
        eqToHom (congrArg P.obj (congrArg Bicat.Hom.obj (dual_obC P ν μ g.dom h₁)).symm),
    ?_, ((isDgC_dg μ hc).comp_eqToHom _).eqToHom_comp _⟩
  rw [mateC_dgC hz ν μ _ _ h₁ h₂ hg₀, ← Linear.comp_smul, ← Linear.smul_comp]
  congr 2
  exact hσ g μ

include hσ in
/-- **The rotation of a whiskered generator is the whiskered rotated generator**, times the
scalar of the generator: `(u ⊗ g ⊗ v)^* = σ g · (v* ⊗ g^rot ⊗ u*)`. -/
theorem mateC_layerW (μ ν : X) (u v : List (Letter I)) (g : Shape I)
    (hs : wt RD μ (u ++ g.dom ++ v) = ν) (ht : wt RD μ (u ++ g.cod ++ v) = ν) :
    ∃ Z, mateC P hz (obC P μ ν _ hs) (obC P μ ν _ ht)
        (dgC P μ (u ++ g.dom ++ v) (u ++ g.cod ++ v) [(u, g, v)]) = σ g • Z ∧
      IsDgC P Z (layList RD ν [(rd v, rotSh g, rd u)]) := by
  have h₂ : wt RD (wt RD μ v) g.cod = wt RD (wt RD μ v) g.dom :=
    (Shape.wt_dom_eq_wt_cod (wt RD μ v) g).symm
  have hu : wt RD (wt RD (wt RD μ v) g.dom) u = ν := by
    rw [← hs, List.append_assoc, wt_append, wt_append]
  let V := obC P μ (wt RD μ v) v rfl
  let G₁ := obC P (wt RD μ v) (wt RD (wt RD μ v) g.dom) g.dom rfl
  let G₂ := obC P (wt RD μ v) (wt RD (wt RD μ v) g.dom) g.cod h₂
  let Uh := obC P (wt RD (wt RD μ v) g.dom) ν u hu
  let θ : G₁ ⟶ G₂ := dgC P (wt RD μ v) g.dom g.cod [([], g, [])]
  have hθ : IsDiag P θ (layList RD (wt RD μ v) [([], g, [])]) :=
    isDgC_dg (wt RD μ v) (show SChain g.dom [([], g, [])] g.cod by simp)
  obtain ⟨Z₀, hZ₀, hZ₀l⟩ := mateC_genW (hz := hz) σ hσ (wt RD μ v) _ g rfl h₂
  let θ' : G₁ ⟶ G₂ := (Biadjunction.rightMateLinearEquiv k (BBC G₁) (BBC G₂)).symm Z₀
  have hθ'm : Biadjunction.rightMate (BBC G₁) (BBC G₂) θ' = Z₀ :=
    (Biadjunction.rightMateLinearEquiv k (BBC G₁) (BBC G₂)).apply_symm_apply Z₀
  have hθθ' : θ = σ g • θ' := by
    apply (Biadjunction.rightMateLinearEquiv k (BBC G₁) (BBC G₂)).injective
    rw [map_smul]
    exact hZ₀.trans (congrArg (σ g • ·) hθ'm.symm)
  have hbase : IsDiag P (Biadjunction.rightMate (BBC G₁) (BBC G₂) θ')
      (layList RD (wt RD (wt RD μ v) g.dom) [([], rotSh g, [])]) := by
    rw [hθ'm]; exact hZ₀l
  have hW := (IsDiag.rightMate_whiskerRight hz V hbase).rightMate_whiskerLeft hz Uh
  have hX : IsDiag P (Uh ◁ (θ ▷ V))
      (((layList RD (wt RD μ v) [([], g, [])]).map (·.wr V.obj.word)).map (·.wl Uh.obj)) :=
    (hθ.whiskerRight V).whiskerLeft Uh
  have e : obC P μ ν (u ++ g.dom ++ v) hs = Uh ≫ (G₁ ≫ V) := by
    refine Bicat.Hom.ext (Obj.ext ?_ ?_)
    · show wt RD μ (u ++ g.dom ++ v) = wt RD (wt RD (wt RD μ v) g.dom) u
      rw [hu, hs]
    · show wd RD μ (u ++ g.dom ++ v) =
        wd RD (wt RD (wt RD μ v) g.dom) u ++ (wd RD (wt RD μ v) g.dom ++ wd RD μ v)
      simp [wd_append, wt_append, List.append_assoc]
  have e' : obC P μ ν (u ++ g.cod ++ v) ht = Uh ≫ (G₂ ≫ V) := by
    refine Bicat.Hom.ext (Obj.ext ?_ ?_)
    · show wt RD μ (u ++ g.cod ++ v) = wt RD (wt RD (wt RD μ v) g.dom) u
      rw [hu, ht]
    · show wd RD μ (u ++ g.cod ++ v) =
        wd RD (wt RD (wt RD μ v) g.dom) u ++ (wd RD (wt RD μ v) g.cod ++ wd RD μ v)
      simp [wd_append, wt_append, List.append_assoc, h₂]
  have hdg : IsDiag P (show obC P μ ν _ hs ⟶ obC P μ ν _ ht from
      dgC P μ (u ++ g.dom ++ v) (u ++ g.cod ++ v) [(u, g, v)])
      (((layList RD (wt RD μ v) [([], g, [])]).map (·.wr V.obj.word)).map (·.wl Uh.obj)) := by
    refine IsDiag.congr (P := P) (θ := (show obC P μ ν _ hs ⟶ obC P μ ν _ ht from
      dgC P μ (u ++ g.dom ++ v) (u ++ g.cod ++ v) [(u, g, v)]))
      (isDgC_dg μ (show SChain (u ++ g.dom ++ v) [(u, g, v)] (u ++ g.cod ++ v) from
        ⟨rfl, rfl⟩)) ?_
    simp only [layList_cons, layList_nil, List.map_cons, List.map_nil]
    congr 1
    rw [show V.obj.word = wd RD μ v from rfl, lay_wr_eq RD μ (wt RD μ v) v [] [] g rfl,
      show Uh.obj = ob RD (wt RD (wt RD μ v) g.dom) u from rfl,
      lay_wl_eq RD μ (wt RD (wt RD μ v) g.dom) u [] ([] ++ v) g ?_]
    · simp
    · simp [wt_append]
  have heq := hdg.eq_eqToHom hX e e'
  have H := rightMate_eqToHom_conj hz e e' (Uh ◁ (θ ▷ V))
  have hsm : Uh ◁ (θ ▷ V) = σ g • (Uh ◁ (θ' ▷ V)) := by
    rw [hθθ', LocallyLinear.smul_whiskerRight, LocallyLinear.whiskerLeft_smul]
  refine ⟨show P.dualHom (inv RD).toColourDuality.pivotal (obC P μ ν _ ht) ⟶
      P.dualHom (inv RD).toColourDuality.pivotal (obC P μ ν _ hs) from
    eqToHom (congrArg (P.dualHom (inv RD).toColourDuality.pivotal) e') ≫
      Biadjunction.rightMate (BBC (Uh ≫ (G₁ ≫ V))) (BBC (Uh ≫ (G₂ ≫ V))) (Uh ◁ (θ' ▷ V)) ≫
        eqToHom (congrArg (P.dualHom (inv RD).toColourDuality.pivotal) e).symm, ?_, ?_⟩
  · rw [mateC_apply]
    refine (congrArg (Biadjunction.rightMate (BBC (obC P μ ν _ hs)) (BBC (obC P μ ν _ ht)))
      heq).trans ?_
    rw [H, hsm, Biadjunction.rightMate_smul, Linear.smul_comp, Linear.comp_smul]
  · have hfin : IsDiag P (eqToHom (congrArg (P.dualHom (inv RD).toColourDuality.pivotal) e') ≫
        Biadjunction.rightMate (BBC (Uh ≫ (G₁ ≫ V))) (BBC (Uh ≫ (G₂ ≫ V))) (Uh ◁ (θ' ▷ V)) ≫
          eqToHom (congrArg (P.dualHom (inv RD).toColourDuality.pivotal) e).symm)
        (((layList RD (wt RD (wt RD μ v) g.dom) [([], rotSh g, [])]).map
          (·.wl (P.dualHom (inv RD).toColourDuality.pivotal V).obj)).map
            (·.wr (P.dualHom (inv RD).toColourDuality.pivotal Uh).obj.word)) :=
      (hW.comp_eqToHom _).eqToHom_comp _
    refine hfin.congr ?_
    have eV := congrArg Bicat.Hom.obj (dual_obC P μ (wt RD μ v) v rfl)
    have eU := congrArg (fun x => (Bicat.Hom.obj x).word)
      (dual_obC P (wt RD (wt RD μ v) g.dom) ν u hu)
    simp only [obC_obj, ob_word] at eV eU
    simp only [layList_cons, layList_nil, List.map_cons, List.map_nil]
    rw [show V = obC P μ (wt RD μ v) v rfl from rfl, eV,
      show Uh = obC P (wt RD (wt RD μ v) g.dom) ν u hu from rfl, eU,
      lay_wl_eq RD _ (wt RD μ v) (rd v) [] [] (rotSh g)
        (by simp [rotSh_dom, wt_rd_of RD _ _ g.cod h₂]),
      lay_wr_eq RD ν _ (rd u) _ [] (rotSh g) (wt_rd_of RD _ _ u hu)]
    simp

/-! ## The rotation of upward normal-form diagrams -/

include hσ in
/-- The rotation of a single layer. -/
theorem rotC_dg_singleW (μ ν : X) (x : LayerData I)
    (hs : wt RD μ (x.1 ++ x.2.1.dom ++ x.2.2) = ν) (ht : wt RD μ (x.1 ++ x.2.1.cod ++ x.2.2) = ν) :
    rotC P hz μ ν _ _ _ _ hs ht rfl rfl (dgC P μ _ _ [x]) =
      σ x.2.1 • dgC P ν (rd (x.1 ++ x.2.1.cod ++ x.2.2)) (rd (x.1 ++ x.2.1.dom ++ x.2.2))
        [rotLD x] := by
  obtain ⟨u, g, v⟩ := x
  obtain ⟨Z, hZ, hZl⟩ := mateC_layerW (hz := hz) σ hσ μ ν u v g hs ht
  rw [rotC_apply, hZ, Linear.smul_comp, Linear.comp_smul]
  congr 1
  have H := (hZl.eqToHom_comp (rotC_e₁ P μ ν _ _ ht rfl)).comp_eqToHom
    (rotC_e₁ P μ ν _ _ hs rfl).symm
  have H' := isDgC_dg (P := P) ν (sChain_rotLs
    (show SChain (u ++ g.dom ++ v) [(u, g, v)] (u ++ g.cod ++ v) from ⟨rfl, rfl⟩))
  simpa [rotLs] using H.eq_eqToHom H' rfl rfl

include hσ in
/-- **The rotation of a normal-form diagram is the diagram of the rotated layers in reversed
order**, times the product of the scalars `σ g` of its generators. -/
theorem rotC_dgW (μ ν : X) {s t : List (Letter I)} (ls : List (LayerData I)) (h : SChain s ls t)
    (hs : wt RD μ s = ν) (ht : wt RD μ t = ν) :
    rotC P hz μ ν s t (rd s) (rd t) hs ht rfl rfl (dgC P μ s t ls) =
      (ls.map fun x => σ x.2.1).prod • dgC P ν (rd t) (rd s) (rotLs ls) := by
  induction ls generalizing s with
  | nil =>
    obtain rfl : s = t := h
    rw [dgC_nil, rotC_id, rotLs_nil, dgC_nil, List.map_nil, List.prod_nil, one_smul]
  | cons x ls ih =>
    obtain ⟨rfl, h'⟩ := h
    have hr : wt RD μ (x.1 ++ x.2.1.cod ++ x.2.2) = ν := by
      rw [← ht, SChain.wt_eq RD μ h']
    rw [show x :: ls = [x] ++ ls from rfl, ← dgC_comp (show SChain _ [x] _ from ⟨rfl, rfl⟩) h',
      rotC_comp P hz μ ν _ _ _ _ _ _ hs hr ht rfl rfl rfl,
      ih h' hr,
      rotC_dg_singleW σ hσ μ ν x hs hr,
      Linear.smul_comp, Linear.comp_smul, smul_smul, rotLs_append,
      show rotLs [x] = [rotLD x] from rfl,
      dgC_comp (sChain_rotLs h') (show SChain (rd (x.1 ++ x.2.1.cod ++ x.2.2)) [rotLD x]
        (rd (x.1 ++ x.2.1.dom ++ x.2.2)) from
          sChain_rotLs (show SChain _ [x] _ from ⟨rfl, rfl⟩)),
      List.map_append, List.prod_append, List.map_singleton, List.prod_singleton, mul_comm]

include hσ in
/-- `rotC_dgW` with the boundaries of the rotation given as `s'`, `t'`. -/
theorem rotC_dgW' (μ ν : X) {s t s' t' : List (Letter I)} (ls : List (LayerData I))
    (h : SChain s ls t) (hs : wt RD μ s = ν) (ht : wt RD μ t = ν)
    (es : rd s = s') (et : rd t = t') :
    rotC P hz μ ν s t s' t' hs ht es et (dgC P μ s t ls) =
      (ls.map fun x => σ x.2.1).prod • dgC P ν t' s' (rotLs ls) := by
  subst es et
  exact rotC_dgW σ hσ μ ν ls h hs ht

end RotW

/-! ## The rotated generators, straightened by the zigzag relations -/

section Zig

variable {P : Presentation.{w, max u v} (psig RD) k} (hz : P.PivotalZigzags (inv RD).toColourDuality)
include hz

/-- The unstraightened rotation of a normal-form diagram is a rotation (`rotC_dgC`), with the
rightmost region of the diagram determined by that of its rotation. -/
theorem dgC_rotRaw_eq_rotC (μ : X) {s t : List (Letter I)} (ls : List (LayerData I))
    (h : SChain s ls t) (ht : wt RD (wt RD μ (rd s)) t = μ) :
    dgC P μ (rd t) (rd s) (rotRaw s t ls) =
      rotC P hz (wt RD μ (rd s)) μ s t (rd s) (rd t)
        (by simpa using wt_rd RD μ (rd s)) ht rfl rfl (dgC P (wt RD μ (rd s)) s t ls) :=
  (rotC_dgC hz _ μ ls h _ ht).symm

/-- The rotation of the cup `1 ⟶ l l*` is the cap `l* l ⟶ 1` (zigzag relations). -/
theorem dgC_rotRaw_cup (μ : X) (l : Letter I) :
    dgC P μ (rd [l, l.dual]) (rd []) (rotRaw [] [l, l.dual] [([], .cup l, [])]) =
      dgC P μ (rd [l, l.dual]) (rd []) [([], rotSh (.cup l), [])] := by
  obtain ⟨_ | _, i⟩ := l
  · show dgC P μ [dn i, up i] [] _ = dgC P μ [dn i, up i] [] _
    simp only [rotRaw, nCups, nCaps, rd_cons, rd_nil, List.nil_append, List.singleton_append,
      rotSh_cup, List.map_nil, List.map_cons, whL, List.append_nil, Letter.dual_mk,
      Bool.not_false, Bool.not_true]
    datC 0 [dn i] [] (dgC_zigR' _ hz _ (dn i))
  · show dgC P μ [up i, dn i] [] _ = dgC P μ [up i, dn i] [] _
    simp only [rotRaw, nCups, nCaps, rd_cons, rd_nil, List.nil_append, List.singleton_append,
      rotSh_cup, List.map_nil, List.map_cons, whL, List.append_nil, Letter.dual_mk,
      Bool.not_false, Bool.not_true]
    datC 0 [up i] [] (dgC_zigR' _ hz _ (up i))

/-- The rotation of the cap `l* l ⟶ 1` is the cup `1 ⟶ l* l` (zigzag relations). -/
theorem dgC_rotRaw_cap (μ : X) (l : Letter I) :
    dgC P μ (rd []) (rd [l.dual, l]) (rotRaw [l.dual, l] [] [([], .cap l, [])]) =
      dgC P μ (rd []) (rd [l.dual, l]) [([], rotSh (.cap l), [])] := by
  obtain ⟨_ | _, i⟩ := l
  · show dgC P μ [] [up i, dn i] _ = dgC P μ [] [up i, dn i] _
    simp only [rotRaw, nCups, nCaps, rd_cons, rd_nil, List.nil_append, List.singleton_append,
      rotSh_cap, List.map_nil, List.map_cons, whL, List.append_nil, Letter.dual_mk,
      Bool.not_false, Bool.not_true]
    datC 1 [] [dn i] (dgC_zigR' _ hz _ (dn i))
  · show dgC P μ [] [dn i, up i] _ = dgC P μ [] [dn i, up i] _
    simp only [rotRaw, nCups, nCaps, rd_cons, rd_nil, List.nil_append, List.singleton_append,
      rotSh_cap, List.map_nil, List.map_cons, whL, List.append_nil, Letter.dual_mk,
      Bool.not_false, Bool.not_true]
    datC 1 [] [up i] (dgC_zigR' _ hz _ (up i))

/-- The rotation of the left rotation `rotDotL` of the upward dot is the upward dot (zigzag
relations). -/
theorem dgC_rotRaw_rotDotL (μ : X) (i : I) :
    dgC P μ [up i] [up i] (rotRaw [dn i] [dn i]
      [([], .cup (dn i), [dn i]), ([dn i], .dot (up i), [dn i]), ([dn i], .cap (dn i), [])]) =
      dgC P μ [up i] [up i] [([], .dot (up i), [])] := by
  simp only [rotRaw, nCups, nCaps, rd, List.map_cons, List.map_nil,
    List.reverse_cons, List.reverse_nil, Letter.dual_dn]
  dnorm
  dswapC 0; dswapC 1
  datC 2 [up i, dn i] [] (dgC_zigR' _ hz _ (dn i))
  dswapC 1
  datC 0 [] [] (dgC_zigR' _ hz _ (dn i))

/-- The rotation of the left rotation `rotCrossL j i` of the upward crossing is the upward
crossing `E_j E_i ⟶ E_i E_j` (zigzag relations). -/
theorem dgC_rotRaw_rotCrossL (μ : X) (j i : I) :
    dgC P μ [up j, up i] [up i, up j] (rotRaw [dn j, dn i] [dn i, dn j]
      [([], .cup (dn i), [dn j, dn i]), ([dn i], .cup (dn j), [up i, dn j, dn i]),
      ([dn i, dn j], .cross true j i, [dn j, dn i]), ([dn i, dn j, up i], .cap (dn j), [dn i]),
      ([dn i, dn j], .cap (dn i), [])]) =
      dgC P μ [up j, up i] [up i, up j] [([], .cross true j i, [])] := by
  simp only [rotRaw, nCups, nCaps, rd, List.map_cons, List.map_nil,
    List.reverse_cons, List.reverse_nil, Letter.dual_dn]
  dnorm
  dswapC 1; dswapC 0; dswapC 2; dswapC 1
  dswapC 6; dswapC 5; dswapC 4; dswapC 3; dswapC 2
  dswapC 1
  datC 0 [up j] [] (dgC_zigR' _ hz _ (dn i))
  dswapC 5; dswapC 4; dswapC 3; dswapC 2; dswapC 1
  datC 0 [] [up i] (dgC_zigR' _ hz _ (dn j))
  dswapC 1; dswapC 0
  dswapC 2
  datC 1 [up i] [] (dgC_zigR' _ hz _ (dn j))
  datC 1 [] [up j] (dgC_zigR' _ hz _ (dn i))

end Zig

/-! ## The rotation of all generators of `U_Q(g)` -/

section CLRot

variable (RD) (k) (S : CLScalars C k)

/-- The scalars of the rotated generators of `U_Q(g)` (`eq_cyclic_dot`, `eq_almost_cyclic`):
`t_{ij}` for the upward crossing `E_j E_i ⟶ E_i E_j`, `t_{ji}^{-1}` for the downward crossing
`F_j F_i ⟶ F_i F_j`, and `1` for dots, cups and caps. -/
def sigmaCL : Shape I → k
  | .cross true j i => (S.t i j : k)
  | .cross false j i => (((S.t j i)⁻¹ : kˣ) : k)
  | _ => 1

/-- **The rotation of every generator of `U_Q(g)` is `sigmaCL` times the rotated generator.** -/
theorem dgC_rotRaw_gen (g : Shape I) (μ : X) :
    dgC (presCL RD k S) μ (rd g.cod) (rd g.dom) (rotRaw g.dom g.cod [([], g, [])]) =
      sigmaCL k S g • dgC (presCL RD k S) μ (rd g.cod) (rd g.dom) [([], rotSh g, [])] := by
  rcases g with ⟨_ | _, i⟩ | ⟨_ | _, j, i⟩ | l | l
  · -- downward dot: `downDot = rotDotL` (`eq_cyclic_dot`)
    have hs : wt RD (wt RD μ (rd [dn i])) [dn i] = μ := by simp
    show dgC (presCL RD k S) μ [up i] [up i] (rotRaw [dn i] [dn i] [([], .dot (dn i), [])]) =
      (1 : k) • dgC (presCL RD k S) μ [up i] [up i] [([], .dot (up i), [])]
    rw [one_smul]
    refine (dgC_rotRaw_eq_rotC (zigzags RD k S) μ [([], .dot (dn i), [])] (by schain) hs).trans ?_
    have hD : dgC (presCL RD k S) (wt RD μ (rd [dn i])) [dn i] [dn i] [([], .dot (dn i), [])] =
        dgC (presCL RD k S) (wt RD μ (rd [dn i])) [dn i] [dn i]
          [([], .cup (dn i), [dn i]), ([dn i], .dot (up i), [dn i]), ([dn i], .cap (dn i), [])] := by
      rw [dgC_of (by schain), dgC_of (by schain)]
      exact ((presCL RD k S).diag_eq_of_rel (.inr (.cycDotL i _)) rfl).symm
    rw [hD, rotC_dgC (zigzags RD k S) _ μ _ (by schain) _ hs]
    exact dgC_rotRaw_rotDotL (zigzags RD k S) μ i
  · -- upward dot
    show dgC (presCL RD k S) μ [dn i] [dn i] _ = (1 : k) • _
    rw [one_smul]
    simp only [rotRaw, nCups, nCaps, rd, List.map_cons, List.map_nil,
      List.reverse_cons, List.reverse_nil, Letter.dual_up, rotSh_dot]
    dnorm
    rw [dgC_of (by schain), dgC_of (by schain)]
    exact presCL_rotDotR RD k S i μ
  · -- downward crossing: `downCross j i = t_{ji}^{-1} rotCrossL j i` (`eq_almost_cyclic`)
    have hs : wt RD (wt RD μ (rd [dn j, dn i])) [dn j, dn i] = μ := by simp
    have ht : wt RD (wt RD μ (rd [dn j, dn i])) [dn i, dn j] = μ :=
      (Shape.wt_dom_eq_wt_cod _ (.cross false j i)).symm.trans hs
    show dgC (presCL RD k S) μ [up j, up i] [up i, up j]
        (rotRaw [dn j, dn i] [dn i, dn j] [([], .cross false j i, [])]) =
      (((S.t j i)⁻¹ : kˣ) : k) •
        dgC (presCL RD k S) μ [up j, up i] [up i, up j] [([], .cross true j i, [])]
    refine (dgC_rotRaw_eq_rotC (zigzags RD k S) μ [([], .cross false j i, [])] (by schain)
      ht).trans ?_
    have hD : dgC (presCL RD k S) (wt RD μ (rd [dn j, dn i])) [dn j, dn i] [dn i, dn j]
          [([], .cross false j i, [])] =
        (((S.t j i)⁻¹ : kˣ) : k) • dgC (presCL RD k S) (wt RD μ (rd [dn j, dn i]))
          [dn j, dn i] [dn i, dn j]
          [([], .cup (dn i), [dn j, dn i]), ([dn i], .cup (dn j), [up i, dn j, dn i]),
            ([dn i, dn j], .cross true j i, [dn j, dn i]),
            ([dn i, dn j, up i], .cap (dn j), [dn i]), ([dn i, dn j], .cap (dn i), [])] := by
      have h := (presCL RD k S).lin_rel_self (.inr (.cycCrossL j i (wt RD μ (rd [dn j, dn i]))))
      change (presCL RD k S).lin ((((S.t j i)⁻¹ : kˣ) : k) •
        LinDiagram.of (rotCrossL RD j i _) - LinDiagram.of (downCross RD j i _)) = 0 at h
      rw [lin_sub, lin_smul, lin_of, lin_of, sub_eq_zero] at h
      rw [dgC_of (by schain), dgC_of (by schain)]
      exact h.symm
    rw [hD, map_smul, rotC_dgC (zigzags RD k S) _ μ _ (by schain) hs ht]
    exact congrArg (_ • ·) (dgC_rotRaw_rotCrossL (zigzags RD k S) μ j i)
  · -- upward crossing
    show dgC (presCL RD k S) μ [dn j, dn i] [dn i, dn j] _ = (S.t i j : k) • _
    simp only [rotRaw, nCups, nCaps, rd, List.map_cons, List.map_nil,
      List.reverse_cons, List.reverse_nil, Letter.dual_up, rotSh_cross]
    dnorm
    rw [dgC_of (by schain), dgC_of (by schain)]
    exact presCL_rotCrossR RD k S j i μ
  · rw [show sigmaCL k S (.cup l) = 1 from rfl, one_smul]
    exact dgC_rotRaw_cup (zigzags RD k S) μ l
  · rw [show sigmaCL k S (.cap l) = 1 from rfl, one_smul]
    exact dgC_rotRaw_cap (zigzags RD k S) μ l

/-- **The rotation by `180°` of a normal-form diagram of `U_Q(g)`** is the diagram of the rotated
layers in reversed order, times the product of the scalars `sigmaCL` of its generators:
`t_{ij}` for each upward crossing `E_j E_i ⟶ E_i E_j`, `t_{ji}^{-1}` for each downward crossing
`F_j F_i ⟶ F_i F_j`. -/
theorem rotC_dgCL (μ ν : X) {s t : List (Letter I)} (ls : List (LayerData I)) (h : SChain s ls t)
    (hs : wt RD μ s = ν) (ht : wt RD μ t = ν) :
    rotC (presCL RD k S) (zigzags RD k S) μ ν s t (rd s) (rd t) hs ht rfl rfl
        (dgC (presCL RD k S) μ s t ls) =
      (ls.map fun x => sigmaCL k S x.2.1).prod • dgC (presCL RD k S) ν (rd t) (rd s) (rotLs ls) :=
  rotC_dgW (hz := zigzags RD k S) (sigmaCL k S) (dgC_rotRaw_gen RD k S) μ ν ls h hs ht

end CLRot

end Categorification.KL3.Diagram.CL

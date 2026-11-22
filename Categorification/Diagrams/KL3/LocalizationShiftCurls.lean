/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.LocalizationShiftNegBubbles
import Categorification.Diagrams.KL3.LocalizationShiftBubbles
import Categorification.Diagrams.KL3.Markov

/-!
# Right curls under the weight shift of `U′`

Infrastructure for the curl relations in the proof that the weight shift of the localized
2-category `U′` respects its defining relations (Webster arXiv:1309.3796v2, Proposition 3.30).

## Main results

* `Cz_succ`: the image of a right curl with `z + 1` dots on the downward strand is a dot times
  the curl with `z` dots, minus a whiskered clockwise bubble with `z` dots.
* `toLoc_plcL`, `whisk_toLoc`: placing a morphism of `U` in context agrees with whiskering in `U′`.
* `Bz_eq`: the whiskered clockwise bubble is the image of `bubRU`.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.KL3.Diagram
open CategoryTheory StringDiagrams QuantumGroup UDot Presentation
universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {k : Type w} [CommRing k]

section CurlR

variable (ν : X) (i : I)

/-- In `U`: a downward dot entering the cap of a right curl is an upward dot on the other leg. -/
theorem dg_dotcap_curl :
    dg RD k ν [up i, up i, dn i] [up i]
        [([up i, up i], .dot (dn i), []), ([up i], .cap (dn i), [])] =
      dg RD k ν [up i, up i, dn i] [up i]
        [([up i], .dot (up i), [dn i]), ([up i], .cap (dn i), [])] :=
  dg_step RD k ν [] [] [up i] [] (s := [up i, dn i]) (t := [])
    (dg_dot_cap_dn RD k (wt RD ν []) i) (by schain) (by schain) (by simp [whL]) (by simp [whL])

/-- In `U`: the nilHecke relation for the crossing of a right curl. -/
theorem dg_cross_dot_curl :
    dg RD k ν [up i, up i, dn i] [up i, up i, dn i]
        [([], .cross true i i, [dn i]), ([up i], .dot (up i), [dn i])] =
      dg RD k ν [up i, up i, dn i] [up i, up i, dn i]
        [([], .dot (up i), [up i, dn i]), ([], .cross true i i, [dn i])] -
      dg RD k ν [up i, up i, dn i] [up i, up i, dn i] [] := by
  have E : dg RD k (wt RD ν [dn i]) [up i, up i] [up i, up i]
      [([], .cross true i i, []), ([up i], .dot (up i), [])] =
      dg RD k (wt RD ν [dn i]) [up i, up i] [up i, up i]
        [([], .dot (up i), [up i]), ([], .cross true i i, [])] -
      dg RD k (wt RD ν [dn i]) [up i, up i] [up i, up i] [] := by
    rw [dg_slideREq]; abel
  have key := dg_stepL RD k ν (s₀ := [up i, up i, dn i]) (t₀ := [up i, up i, dn i]) [] [] [] [dn i]
    (L := [([], .cross true i i, [dn i]), ([up i], .dot (up i), [dn i])]) E (by schain) (by schain)
    (by simp [whL])
  rw [key, map_sub, ctxL_dg RD k ν (by schain) (by schain),
    ctxL_dg RD k ν (by schain) (by schain)]
  simp [whL]

/-- In `U`: an upward dot slides below the cup of a right curl. -/
theorem dg_dot_cup_curl :
    dg RD k ν [up i] [up i, up i, dn i] [([], .dot (up i), []), ([up i], .cup (up i), [])] =
      dg RD k ν [up i] [up i, up i, dn i]
        [([up i], .cup (up i), []), ([], .dot (up i), [up i, dn i])] := by
  simpa using dg_swap RD k ν [up i] [up i, up i, dn i] [] [] [] (.dot (up i)) (.cup (up i))

variable (RD k)

/-- The image of the right curl with `z` dots, before identification with the right side. -/
abbrev Cz (z : ℤ) : lob RD k ν [up i] ⟶ lob RD k ν [up i] :=
  ldg RD k ν [up i] [up i, up i, dn i] [([up i], .cup (up i), [])] ≫
    ldg RD k ν [up i, up i, dn i] [up i, up i, dn i] [([], .cross true i i, [dn i])] ≫
      zdot RD k ν [up i, up i] i [] z ≫
        ldg RD k ν [up i, up i, dn i] [up i] [([up i], .cap (dn i), [])]

/-- A whiskered clockwise bubble with `z` dots in `U′`. -/
abbrev Bz (z : ℤ) : lob RD k ν [up i] ⟶ lob RD k ν [up i] :=
  ldg RD k ν [up i] [up i, up i, dn i] [([up i], .cup (up i), [])] ≫
      zdot RD k ν [up i, up i] i [] z ≫
        ldg RD k ν [up i, up i, dn i] [up i] [([up i], .cap (dn i), [])]

/-- An upward dot on `E_i` in `U′`. -/
abbrev Xu : lob RD k ν [up i] ⟶ lob RD k ν [up i] :=
  ldg RD k ν [up i] [up i] [([], .dot (up i), [])]

theorem Cz_succ (z : ℤ) :
    Cz RD k ν i (z + 1) = Xu RD k ν i ≫ Cz RD k ν i z - Bz RD k ν i z := by
  have F1 : zdot RD k ν [up i, up i] i [] 1 ≫
      ldg RD k ν [up i, up i, dn i] [up i] [([up i], .cap (dn i), [])] =
      ldg RD k ν [up i, up i, dn i] [up i, up i, dn i] [([up i], .dot (up i), [dn i])] ≫
        ldg RD k ν [up i, up i, dn i] [up i] [([up i], .cap (dn i), [])] := by
    rw [zdot_one, ldot, ← ldg_of]
    exact (ldg_comp RD k (A := [([up i, up i], .dot (dn i), [])])
      (B := [([up i], .cap (dn i), [])]) (by schain) (by schain)).trans
      ((congrArg (toLoc RD k).map (dg_dotcap_curl (RD := RD) (k := k) ν i)).trans
        (ldg_comp RD k (A := [([up i], .dot (up i), [dn i])])
          (B := [([up i], .cap (dn i), [])]) (by schain) (by schain)).symm)
  have F2 : zdot RD k ν [up i, up i] i [] z ≫
      ldg RD k ν [up i, up i, dn i] [up i, up i, dn i] [([up i], .dot (up i), [dn i])] =
      ldg RD k ν [up i, up i, dn i] [up i, up i, dn i] [([up i], .dot (up i), [dn i])] ≫
        zdot RD k ν [up i, up i] i [] z := by
    refine zdot_comp_of_one (RD := RD) (k := k) (A := [up i, up i]) (B := [])
      (A' := [up i, up i]) (B' := []) ν _ ?_ z
    rw [zdot_one, ldot, ← ldg_of]
    exact (ldg_comp RD k (A := [([up i, up i], .dot (dn i), [])])
      (B := [([up i], .dot (up i), [dn i])]) (by schain) (by schain)).trans
      ((congrArg (toLoc RD k).map
        (dg_swap RD k ν _ _ [up i] [] [] (.dot (up i)) (.dot (dn i))).symm).trans
        (ldg_comp RD k (A := [([up i], .dot (up i), [dn i])])
          (B := [([up i, up i], .dot (dn i), [])]) (by schain) (by schain)).symm)
  have F3 : ldg RD k ν [up i, up i, dn i] [up i, up i, dn i] [([], .cross true i i, [dn i])] ≫
      ldg RD k ν [up i, up i, dn i] [up i, up i, dn i] [([up i], .dot (up i), [dn i])] =
      ldg RD k ν [up i, up i, dn i] [up i, up i, dn i] [([], .dot (up i), [up i, dn i])] ≫
        ldg RD k ν [up i, up i, dn i] [up i, up i, dn i] [([], .cross true i i, [dn i])] -
      𝟙 _ := by
    rw [ldg_comp RD k (by schain) (by schain), ldg_comp RD k (by schain) (by schain), ldg,
      ← ldg_nil RD k ν, ldg, ← Functor.map_sub]
    exact congrArg (toLoc RD k).map (dg_cross_dot_curl (RD := RD) (k := k) ν i)
  have F4 : ldg RD k ν [up i] [up i, up i, dn i] [([up i], .cup (up i), [])] ≫
      ldg RD k ν [up i, up i, dn i] [up i, up i, dn i] [([], .dot (up i), [up i, dn i])] =
      Xu RD k ν i ≫ ldg RD k ν [up i] [up i, up i, dn i] [([up i], .cup (up i), [])] := by
    rw [ldg_comp RD k (by schain) (by schain), ldg_comp RD k (by schain) (by schain)]
    exact congrArg (toLoc RD k).map (dg_dot_cup_curl (RD := RD) (k := k) ν i).symm
  simp only [Cz, Bz]
  rw [add_comm, zdot_add, Category.assoc, F1, ← Category.assoc (zdot _ _ _ _ _ _ z), F2,
    Category.assoc, ← Category.assoc _ (ldg _ _ _ _ _ [([up i], .dot (up i), [dn i])]), F3,
    Preadditive.sub_comp, Category.id_comp, Preadditive.comp_sub, Category.assoc, ← Category.assoc _
      (ldg _ _ _ _ _ [([], .dot (up i), [up i, dn i])]), F4]
  simp only [Category.assoc]

end CurlR

section Whisk

variable (RD k)

/-- The localization of a placed 2-morphism is the placed localization. -/
theorem toLoc_plcL (μ : X) (u v s t : List (Letter I))
    (hst : wt RD (wt RD μ v) t = wt RD (wt RD μ v) s)
    (f : (pres RD k).obj (ob RD (wt RD μ v) s) ⟶ (pres RD k).obj (ob RD (wt RD μ v) t)) :
    (toLoc RD k).map (plcL RD k μ u v s t f) =
      eqToHom (congrArg (presLoc RD k).obj (lob_whisker RD μ u v s).symm) ≫
        (presLoc RD k).whisk ((toLoc RD k).map f) (lU RD μ u v s) (wd RD μ v) ≫
          eqToHom (congrArg (presLoc RD k).obj (lob_whisker' RD μ u v s t hst)) := by
  rw [plcL, dite_eq_left hst]
  simp only [plc, LinearMap.coe_mk, AddHom.coe_mk, Functor.map_comp, eqToHom_map]
  unfold toLoc
  rw [SigMap.lift_whisk _ _ _ _ (whiskerOK_ob RD μ u v s)]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
  rfl

theorem whisk_toLoc (μ : X) (u v s t : List (Letter I))
    (hst : wt RD (wt RD μ v) t = wt RD (wt RD μ v) s)
    (f : (pres RD k).obj (ob RD (wt RD μ v) s) ⟶ (pres RD k).obj (ob RD (wt RD μ v) t))
    (U : Obj (lsig RD)) (hU : U = lU RD μ u v s) :
    (presLoc RD k).whisk ((toLoc RD k).map f) U (wd RD μ v) =
      eqToHom (congrArg (presLoc RD k).obj (hU ▸ lob_whisker RD μ u v s)) ≫
        (toLoc RD k).map (plcL RD k μ u v s t f) ≫
          eqToHom (congrArg (presLoc RD k).obj (hU ▸ lob_whisker' RD μ u v s t hst)).symm := by
  subst hU
  rw [toLoc_plcL RD k μ u v s t hst]
  simp

/-- The whiskered clockwise bubble of `U′` is the image of the whiskered bubble of `U`. -/
theorem Bz_eq (ν : X) (i : I) (z : ℤ) :
    Bz RD k ν i z = (toLoc RD k).map (bubRU RD k ν (up i) (cwU RD k ν i z)) := by
  have hc : SChain [] [([], .cup (up i), [])] [up i, dn i] := ⟨rfl, rfl⟩
  have hk : SChain [up i, dn i] [([], .cap (dn i), [])] [] := ⟨rfl, rfl⟩
  have e : lU RD ν [up i] [] [] = lU RD ν [up i] [] [up i, dn i] :=
    congrArg (fun w => (incl RD).obj (ob RD w [up i])) (hc.wt_eq RD _).symm
  rw [bubRU, toLoc_plcL RD k ν [up i] [] [] [] rfl, ← zcw_eq, zcw, Presentation.whisk_comp,
    Presentation.whisk_comp, ldg, ldg,
    whisk_toLoc RD k ν [up i] [] [] [up i, dn i] (hc.wt_eq RD _) _ _ rfl,
    whisk_toLoc RD k ν [up i] [] [up i, dn i] [] (hk.wt_eq RD _) _ _ e]
  erw [plcL_dg RD k ν [up i] [] [] [up i, dn i] [([], .cup (up i), [])],
    plcL_dg RD k ν [up i] [] [up i, dn i] [] [([], .cap (dn i), [])]]
  rw [whisk_zdot RD k ν [up i] i [] z _ _ (by rw [e]; exact lwhiskerOK RD ν [up i] [] [up i, dn i])
      ν [up i, up i] [] (by rw [e]; exact lob_whisker RD ν [up i] [] [up i, dn i])
      (by rw [e]; rfl)]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    Category.comp_id, List.map, whL, List.append_nil]
  rfl

end Whisk

end Categorification.KL3.Diagram

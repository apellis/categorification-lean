/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CL.BrundanMid

/-!
# The left rotation of mixed crossings from the mixed relations

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, `eq_almost_cyclic` (p. 6): the relation `cycCrossL j i` for `i ≠ j` follows
from the right rotation `cycCrossR j i`, the zigzag relations and the mixed relations
`downupEF`, `downupFE`. The proof rotates the mixed relations by `180°` (`rotC`, which is
contravariant): the rotation of `crossl j i` is `crossr i j`, so the rotation of `crossr j i` is
`t_{ij} t_{ji}^{-1}` times `crossl i j`, and rotating once more by the right adjunction of the
strand `i` gives the two rotations of the crossing `E_j E_i ⟶ E_i E_j`.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Categorification.KL3.Diagram.CL

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {k : Type w} [CommRing k]

section Rot

variable {P : Presentation.{w, max u v} (psig RD) k} (hz : P.PivotalZigzags (inv RD).toColourDuality)
include hz

/-- The rotation of a normal-form diagram, in normal form (before straightening). -/
theorem rotC_dgC (μ ν : X) {s t : List (Letter I)} (ls : List (LayerData I)) (h : SChain s ls t)
    (hs : wt RD μ s = ν) (ht : wt RD μ t = ν) :
    rotC P hz μ ν s t (rd s) (rd t) hs ht rfl rfl (dgC P μ s t ls) =
      dgC P ν (rd t) (rd s) (rotRaw s t ls) := by
  rw [rotC_apply, mateC_dgC hz μ ν s t hs ht h]
  simp

/-- **The rotation of `crossl j i` is `crossr i j`** (zigzag relations only). -/
theorem rotC_crossl (i j : I) (ν : X) :
    dgC P ν [dn j, up i] [up i, dn j] (rotRaw [up j, dn i] [dn i, up j] (crosslL j i)) =
      dgC P ν [dn j, up i] [up i, dn j] (crossrL i j) := by
  simp only [rotRaw, nCups, nCaps, rd, crosslL, crossrL, List.map_cons, List.map_nil,
    List.reverse_cons, List.reverse_nil, Letter.dual_up, Letter.dual_dn]
  dnorm
  dswapC 1; dswapC 2
  datC 3 [dn j, up i, dn i, up j] [dn j] (dgC_zigR' _ hz _ (dn i))
  dswapC 2
  datC 1 [dn j] [up j, dn j] (dgC_zigR' _ hz _ (dn i))

/-- The rotation of a sideways crossing `E_i F_j ⟶ F_j E_i` (strand `i` upward) by the right
adjunction of the strand `i`: the downward crossing `F_j F_i ⟶ F_i F_j`. -/
def rotRiLs (i j : I) (g : List (LayerData I)) : List (LayerData I) :=
  [([], .cup (dn i), [dn j, dn i])] ++ g.map (whL [dn i] [dn i]) ++ [([dn i, dn j], .cap (dn i), [])]

/-- **The rotation of `crossr j i`, rotated once more by the right adjunction of `i`, is the
right rotation `rotCrossR j i` of the crossing `E_j E_i ⟶ E_i E_j`** (zigzag relations only). -/
theorem rotRi_rotC_crossr (i j : I) (μ : X) :
    dgC P μ [dn j, dn i] [dn i, dn j]
        (rotRiLs i j (rotRaw [dn i, up j] [up j, dn i] (crossrL j i))) =
      dgC P μ [dn j, dn i] [dn i, dn j]
        [([dn j, dn i], .cup (up j), []), ([dn j, dn i, up j], .cup (up i), [dn j]),
          ([dn j, dn i], .cross true j i, [dn i, dn j]), ([dn j], .cap (up i), [up j, dn i, dn j]),
          ([], .cap (up j), [dn i, dn j])] := by
  simp only [rotRiLs, rotRaw, nCups, nCaps, rd, crossrL, List.map_cons, List.map_nil,
    List.reverse_cons, List.reverse_nil, Letter.dual_up, Letter.dual_dn]
  dnorm
  dswapC 0; dswapC 1; dswapC 2; dswapC 3; dswapC 4; dswapC 5
  datC 6 [] [dn j, up i, dn i] (dgC_zigL' _ hz _ (dn i))
  dswapC 5; dswapC 4; dswapC 3; dswapC 2; dswapC 1
  datC 0 [dn j] [] (dgC_zigL' _ hz _ (dn i))

end Rot

/-! ## `U_Q(g)` without the left rotation of mixed crossings -/

variable (RD) in
/-- The relations of `presCL` other than the left rotation `cycCrossL j i` of mixed crossings. -/
def noCycL : Rel RD → Prop
  | .cycCrossL j i _ => j = i
  | _ => True

variable (RD k) in
/-- **`U_Q(g)` without the left rotation of mixed crossings**: all relations of `presCL` except
`cycCrossL j i` for `j ≠ i`. -/
def presNC (S : CLScalars C k) : Presentation.{w, max u v} (psig RD) k :=
  ((pres0 RD k).pivotal (inv RD).toColourDuality).addRels {r : Rel RD // noCycL RD r}
    (fun r => r.1.dom) (fun r => r.1.cod) (fun r => relationCL RD k S r.1)

theorem presNC_zigzags (S : CLScalars C k) :
    (presNC RD k S).PivotalZigzags (inv RD).toColourDuality :=
  Presentation.pivotal_addRels_zigzags (inv RD).toColourDuality (pres0 RD k) _ _ _ _

theorem presNC_lin_rel (S : CLScalars C k) (r : Rel RD) (h : noCycL RD r) :
    (presNC RD k S).lin (relationCL RD k S r) = 0 :=
  (presNC RD k S).lin_rel_self (.inr ⟨r, h⟩)

theorem dgC_crossl_diag (P : Presentation.{w, max u v} (psig RD) k) (i j : I) (μ : X) :
    dgC P μ [up i, dn j] [dn j, up i] (crosslL i j) = P.diag (crossl RD i j μ) := by
  rw [dgC_of (by schain)]; rfl

theorem dgC_crossr_diag (P : Presentation.{w, max u v} (psig RD) k) (i j : I) (μ : X) :
    dgC P μ [dn j, up i] [up i, dn j] (crossrL i j) = P.diag (crossr RD i j μ) := by
  rw [dgC_of (by schain)]; rfl

/-- **The left rotation of a mixed crossing in terms of the right rotation**, from the zigzag and
mixed relations (`downupEF i j`, `downupFE i j`): `rotCrossL j i = t_{ji} t_{ij}^{-1} rotCrossR j i`
in `presNC`. -/
theorem presNC_rotCrossL (S : CLScalars C k) {i j : I} (hij : i ≠ j) (μ' : X) :
    (presNC RD k S).diag (rotCrossL RD j i μ') =
      ((S.t j i : k) * (((S.t i j)⁻¹ : kˣ) : k)) • (presNC RD k S).diag (rotCrossR RD j i μ') := by
  set P := presNC RD k S
  have hz := presNC_zigzags (RD := RD) (k := k) S
  set ν : X := wt RD μ' [dn i]
  set μ : X := wt RD μ' [dn j]
  -- the mixed relations
  have hFE : dgC P μ [dn i, up j] [up j, dn i] (crossrL j i) ≫
      dgC P μ [up j, dn i] [dn i, up j] (crosslL j i) = (S.t i j : k) • 𝟙 _ := by
    have key := presNC_lin_rel (RD := RD) (k := k) S (.downupFE i j hij μ) trivial
    change P.lin (LinDiagram.of (crossr RD j i μ ≫ crossl RD j i μ) -
      (S.t i j : k) • LinDiagram.of (𝟙 _)) = 0 at key
    rw [Presentation.lin_sub, Presentation.lin_smul, Presentation.lin_of, Presentation.lin_of,
      Presentation.diag_comp] at key
    erw [Presentation.diag_id, sub_eq_zero] at key
    rw [dgC_crossr_diag, dgC_crossl_diag]; exact key
  have hEF : dgC P ν [up i, dn j] [dn j, up i] (crosslL i j) ≫
      dgC P ν [dn j, up i] [up i, dn j] (crossrL i j) = (S.t j i : k) • 𝟙 _ := by
    have key := presNC_lin_rel (RD := RD) (k := k) S (.downupEF i j hij ν) trivial
    change P.lin (LinDiagram.of (crossl RD i j ν ≫ crossr RD i j ν) -
      (S.t j i : k) • LinDiagram.of (𝟙 _)) = 0 at key
    rw [Presentation.lin_sub, Presentation.lin_smul, Presentation.lin_of, Presentation.lin_of,
      Presentation.diag_comp] at key
    erw [Presentation.diag_id, sub_eq_zero] at key
    rw [dgC_crossl_diag, dgC_crossr_diag]; exact key
  -- the rotation of `downupFE`
  have hs : wt RD μ [dn i, up j] = ν := by
    simp only [μ, ν, wt_cons, wt_nil, sh, up, dn, sgn]; abel
  have ht : wt RD μ [up j, dn i] = ν := by
    simp only [μ, ν, wt_cons, wt_nil, sh, up, dn, sgn]; abel
  have hrot := congrArg (rotC P hz μ ν [dn i, up j] [dn i, up j] _ _ hs hs rfl rfl) hFE
  rw [rotC_comp P hz μ ν _ [up j, dn i] _ _ _ _ hs ht hs rfl rfl rfl, map_smul, rotC_id,
    rotC_dgC hz μ ν _ (by schain) hs ht, rotC_dgC hz μ ν _ (by schain) ht hs] at hrot
  have hrot' : dgC P ν [dn j, up i] [up i, dn j] (rotRaw [up j, dn i] [dn i, up j] (crosslL j i)) ≫
      dgC P ν [up i, dn j] [dn j, up i] (rotRaw [dn i, up j] [up j, dn i] (crossrL j i)) =
      (S.t i j : k) • 𝟙 _ := hrot
  rw [rotC_crossl hz i j ν] at hrot'
  -- hence `crossl i j = t_{ji} t_{ij}^{-1} R` for `R` the rotation of `crossr j i`
  set R := dgC P ν [up i, dn j] [dn j, up i] (rotRaw [dn i, up j] [up j, dn i] (crossrL j i))
  have hR : dgC P ν [up i, dn j] [dn j, up i] (crosslL i j) =
      ((S.t j i : k) * (((S.t i j)⁻¹ : kˣ) : k)) • R := by
    have h1 : dgC P ν [up i, dn j] [dn j, up i] (crosslL i j) =
        dgC P ν [up i, dn j] [dn j, up i] (crosslL i j) ≫
          ((((S.t i j)⁻¹ : kˣ) : k) • (dgC P ν [dn j, up i] [up i, dn j] (crossrL i j) ≫ R)) := by
      rw [hrot', smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul,
        Category.comp_id]
    rw [h1, Linear.comp_smul, ← Category.assoc, hEF, Linear.smul_comp, Category.id_comp,
      smul_smul, mul_comm]
  -- rotate by the right adjunction of `i`
  have eL : P.diag (rotCrossL RD j i μ') =
      ctxLC P μ' [dn j, dn i] [dn i, dn j] [([], .cup (dn i), [dn j, dn i])] [dn i] [dn i]
        [([dn i, dn j], .cap (dn i), [])] [up i, dn j] [dn j, up i]
        (dgC P ν [up i, dn j] [dn j, up i] (crosslL i j)) := by
    rw [ctxLC_dg _ _ (by schain) (by schain), dgC_of (by simp only [crosslL]; schain)]
    rfl
  have eR : P.diag (rotCrossR RD j i μ') =
      ctxLC P μ' [dn j, dn i] [dn i, dn j] [([], .cup (dn i), [dn j, dn i])] [dn i] [dn i]
        [([dn i, dn j], .cap (dn i), [])] [up i, dn j] [dn j, up i] R := by
    rw [ctxLC_dg _ _ (by schain) (by schain)]
    rw [show [([], Shape.cup (dn i), [dn j, dn i])] ++
        (rotRaw [dn i, up j] [up j, dn i] (crossrL j i)).map (whL [dn i] [dn i]) ++
        [([dn i, dn j], Shape.cap (dn i), [])] =
        rotRiLs i j (rotRaw [dn i, up j] [up j, dn i] (crossrL j i)) from rfl,
      rotRi_rotC_crossr hz (P := P) i j μ', dgC_of (by schain)]
    rfl
  rw [eL, eR, hR, map_smul]


/-- **`Q`-cyclicity of mixed crossings, left rotation** (`cycCrossL j i`, `j ≠ i`) holds in
`presNC`: it follows from the right rotation and the mixed relations. -/
theorem presNC_lin_cycCrossL (S : CLScalars C k) {j i : I} (hji : j ≠ i) (μ : X) :
    (presNC RD k S).lin (relationCL RD k S (.cycCrossL j i μ)) = 0 := by
  have hR := presNC_lin_rel (RD := RD) (k := k) S (.cycCrossR j i μ) trivial
  change (presNC RD k S).lin ((((S.t i j)⁻¹ : kˣ) : k) • LinDiagram.of (rotCrossR RD j i μ) -
    LinDiagram.of (downCross RD j i μ)) = 0 at hR
  change (presNC RD k S).lin ((((S.t j i)⁻¹ : kˣ) : k) • LinDiagram.of (rotCrossL RD j i μ) -
    LinDiagram.of (downCross RD j i μ)) = 0
  rw [Presentation.lin_sub, Presentation.lin_smul, Presentation.lin_of, Presentation.lin_of,
    sub_eq_zero] at hR
  rw [Presentation.lin_sub, Presentation.lin_smul, Presentation.lin_of, Presentation.lin_of,
    presNC_rotCrossL S hji.symm μ, smul_smul, ← hR, sub_eq_zero]
  congr 1
  rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

end Categorification.KL3.Diagram.CL

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.Localization
import StringDiagrams.LayerMap.Local

/-!
# Weight shifts of the localization `U′` (towards Webster, Proposition 3.30)

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §3.6,
Proposition 3.30: for weights `μ, μ′` and integers `aᵢ, bᵢ` with `aᵢ - bᵢ = αᵢ^∨(μ - μ′)`,
the 2-morphism categories `Hom_{U′}(μ, μ + ν)` and `Hom_{U′}(μ′, μ′ + ν)` are equivalent, by the
map fixing dots and crossings and sending `ι ↦ (y^{-aᵢ} ⊗ 1)ι`, `ε ↦ ε(y^{aᵢ} ⊗ 1)`,
`ι′ ↦ (y^{-bᵢ} ⊗ 1)ι′`, `ε′ ↦ ε′(y^{bᵢ} ⊗ 1)`.

This file provides the data of that map on the presentation `presLoc` of `U′`
(`Categorification.Diagrams.KL3.Localization`) and the functor it induces once the relations
are checked. It does **not** yet prove Proposition 3.30.

## Encoding and conventions

* Regions are shifted by `δ = μ′ - μ` (`shiftMap`): the strand colour `⟨l, r⟩` (right region `r`)
  goes to `⟨l, r + δ⟩`. A 1-morphism with rightmost region `μ` (Webster's `Hom_{U′}(μ, μ+ν)`)
  goes to one with rightmost region `μ + δ = μ′`. So Webster's condition reads
  `a i - b i = -⟨i, δ⟩` in the library's pairing.
* Webster's diagrams are mirror images of the library's (the library reads 1-morphisms from the
  left region to the right region). Webster's `ι, ε` (exponent `aᵢ`) are the library's cup and cap
  of colour `up i`; his `ι′, ε′` (exponent `bᵢ`) are the cup and cap of colour `dn i`. In both
  cases the dot power is placed on the downward (`F`) leg, where `y` is invertible in `U′`
  (`cupDec`, `capDec`). Negative powers are the inverse dots of `U′` (`dotUnit`, `zdot`).
* Under this map a clockwise bubble with `m` dots at region `λ` goes to a clockwise bubble with
  `m + ⟨i, δ⟩` dots at `λ + δ`, and a counterclockwise one with `m` dots to `m - ⟨i, δ⟩` dots;
  the degree is preserved. Small cases of the bubble, curl and decomposition relations were
  checked by hand to be consistent with the map; no counterexample to the printed statement was
  found.

## Main definitions

* `shiftMap RD δ`: the relabelling of regions and colours.
* `dotUnit`, `zdot`: the downward dot as a unit of `End` in `U′`, and its integer powers
  (`zdot_add`, `zdot_zero`, `zdot_one`, `zdot_neg_one`).
* `shiftImg RD k δ a b`: the image of each generator of `presLoc` (Webster Prop. 3.30).
* `ShiftRelations RD k δ a b`: the statement that every relation of `presLoc` is sent to `0`.
* `shiftFunctor`: the induced functor `(presLoc RD k).Presented ⥤ (presLoc RD k).Presented`,
  under `ShiftRelations`.

## Remaining for Proposition 3.30

1. `ShiftRelations` for the relations of `pres` transported to `U′`: zigzags, cyclicity, KLR,
   the `EF`/`FE` decompositions, curls and bubble relations (the last three need the `U′`
   calculus with integer dot powers on curls and the Grassmannian relation in `U′`), and for the
   `LocRel` relations (`invLeft`, `invRight`, `cw`, `ccw`).
2. The inverse functor (shift by `-δ` with `-a`, `-b`) and the identities of the composites, which
   follow from agreement on generators.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y)

instance : (lsig RD).IsEven := ⟨fun _ => rfl⟩

/-! ## The relabelling of regions -/

/-- The relabelling of `U′` shifting every region by `δ`: the colour `⟨l, r⟩` goes to
`⟨l, r + δ⟩` (the region part of Webster arXiv:1309.3796v2, Proposition 3.30). -/
def shiftMap (δ : X) : ColourMap (lsig RD) (lsig RD) where
  region (μ : X) := (μ + δ : X)
  colour (c : Col I X) := (⟨c.l, c.r + δ⟩ : Col I X)
  colourSrc c := (add_assoc (sh RD c.l) c.r δ).symm
  colourTgt _ := rfl

theorem wt_add_shift (δ μ : X) (t : List (Letter I)) : wt RD (μ + δ) t = wt RD μ t + δ := by
  rw [wt_eq_add_wX, wt_eq_add_wX, add_assoc]

theorem wd_shift (δ μ : X) (t : List (Letter I)) :
    (wd RD μ t).map (fun c => (⟨c.l, c.r + δ⟩ : Col I X)) = wd RD (μ + δ) t := by
  induction t with
  | nil => rfl
  | cons l t ih => simp [ih, wt_add_shift]

theorem shiftMap_ob (δ μ : X) (t : List (Letter I)) :
    (shiftMap RD δ).obj ((incl RD).obj (ob RD μ t)) = (incl RD).obj (ob RD (μ + δ) t) := by
  refine Obj.ext ?_ ?_
  · show wt RD μ t + δ = wt RD (μ + δ) t
    exact (wt_add_shift RD δ μ t).symm
  · show List.map _ (wd RD μ t) = wd RD (μ + δ) t
    exact wd_shift RD δ μ t

/-! ## Dots as units of `U′` -/

section Units

variable (k : Type w) [CommRing k]

/-- The object `E_t 1_μ` of `U′`. -/
abbrev lob (μ : X) (t : List (Letter I)) : (presLoc RD k).Presented :=
  (presLoc RD k).obj ((incl RD).obj (ob RD μ t))

/-- The left whiskering object `E_u` placed to the left of `E_s 1_{μ + v_X}`. -/
abbrev lU (μ : X) (u v s : List (Letter I)) : Obj (lsig RD) :=
  (incl RD).obj (ob RD (wt RD (wt RD μ v) s) u)

theorem lwhiskerOK (μ : X) (u v s : List (Letter I)) :
    ((incl RD).obj (ob RD (wt RD μ v) s)).WhiskerOK (lU RD μ u v s) (wd RD μ v) :=
  (incl RD).whiskerOK (whiskerOK_ob RD μ u v s)

theorem lob_whisker (μ : X) (u v s : List (Letter I)) :
    ((incl RD).obj (ob RD (wt RD μ v) s)).whisker (lU RD μ u v s) (wd RD μ v) =
      (incl RD).obj (ob RD μ (u ++ s ++ v)) :=
  congrArg (incl RD).obj (ob_whisker RD μ u v s s rfl)

/-- Placement of an endomorphism of `E_s 1_{μ + v_X}` in `U′` between the strands `u`, `v`. -/
def lplc (μ : X) (u v s : List (Letter I)) (f : lob RD k (wt RD μ v) s ⟶ lob RD k (wt RD μ v) s) :
    lob RD k μ (u ++ s ++ v) ⟶ lob RD k μ (u ++ s ++ v) :=
  eqToHom (congrArg (presLoc RD k).obj (lob_whisker RD μ u v s).symm) ≫
    (presLoc RD k).whisk f (lU RD μ u v s) (wd RD μ v) ≫
      eqToHom (congrArg (presLoc RD k).obj (lob_whisker RD μ u v s))

theorem lplc_comp (μ : X) (u v s : List (Letter I)) (f g) :
    lplc RD k μ u v s (f ≫ g) = lplc RD k μ u v s f ≫ lplc RD k μ u v s g := by
  simp [lplc, Presentation.whisk_comp]

theorem lplc_id (μ : X) (u v s : List (Letter I)) :
    lplc RD k μ u v s (𝟙 _) = 𝟙 _ := by
  simp [lplc, Presentation.whisk_id _ _ _ _ (lwhiskerOK RD μ u v s)]

theorem invDotLayer_whisker (μ : X) (u : List (Letter I)) (i : I) (v : List (Letter I)) :
    (invDotLayer RD (wt RD μ v) [] i []).whisker (lU RD μ u v [dn i]) (wd RD μ v) =
      invDotLayer RD μ u i v := by
  have e : wt RD (wt RD μ v) [dn i] = wt RD μ ([dn i] ++ v) := (wt_append RD μ [dn i] v).symm
  refine Layer.ext ?_ ?_ rfl rfl
  · change wt RD (wt RD (wt RD μ v) [dn i]) u = wt RD μ (u ++ [dn i] ++ v)
    simp only [List.append_assoc, wt_append]
  · change wd RD (wt RD (wt RD μ v) [dn i]) u ++ ([] : List (Col I X)) =
      wd RD (wt RD μ ([dn i] ++ v)) u
    rw [List.append_nil, e]

theorem invDot_eq_lplc (μ : X) (u : List (Letter I)) (i : I) (v : List (Letter I)) :
    (presLoc RD k).diag (invDot RD μ u i v) =
      lplc RD k μ u v [dn i] ((presLoc RD k).diag (invDotF RD i (wt RD μ v))) := by
  rw [lplc, Presentation.whisk_diag _ _ _ _ (lwhiskerOK RD μ u v [dn i]),
    (presLoc RD k).diag_eq_of_layers_eq' (invDot RD μ u i v) _ (lob_whisker RD μ u v [dn i]).symm
      (lob_whisker RD μ u v [dn i]).symm]
  show [invDotLayer RD μ u i v] = [(invDotLayer RD (wt RD μ v) [] i []).whisker _ _]
  rw [invDotLayer_whisker]

/-- The downward dot of `U′` on the strand `F_i` between `u` and `v`. -/
def ldot (μ : X) (u : List (Letter I)) (i : I) (v : List (Letter I)) :
    lob RD k μ (u ++ [dn i] ++ v) ⟶ lob RD k μ (u ++ [dn i] ++ v) :=
  (presLoc RD k).diag (inclD RD (mkD RD μ [(u, .dot (dn i), v)] ⟨rfl, rfl⟩))

theorem ldot_eq_lplc (μ : X) (u : List (Letter I)) (i : I) (v : List (Letter I)) :
    ldot RD k μ u i v =
      lplc RD k μ u v [dn i] ((presLoc RD k).diag (inclD RD (downDot RD i (wt RD μ v)))) := by
  rw [ldot, lplc, Presentation.whisk_diag _ _ _ _ (lwhiskerOK RD μ u v [dn i]),
    (presLoc RD k).diag_eq_of_layers_eq' _ _ (lob_whisker RD μ u v [dn i]).symm
      (lob_whisker RD μ u v [dn i]).symm]
  show [(incl RD).layer (lay RD μ u (.dot (dn i)) v)] =
    [((incl RD).layer (lay RD (wt RD μ v) [] (.dot (dn i)) [])).whisker _ _]
  congr 1
  have := lay_whisker RD μ u v [] (.dot (dn i)) [] [dn i] rfl
  simp only [List.append_nil, List.nil_append] at this
  rw [← this]; rfl

/-- The downward dot is a unit of the endomorphism ring of `E_{u F_i v} 1_μ` in `U′`. -/
def dotUnit (μ : X) (u : List (Letter I)) (i : I) (v : List (Letter I)) :
    (End (lob RD k μ (u ++ [dn i] ++ v)))ˣ where
  val := ldot RD k μ u i v
  inv := (presLoc RD k).diag (invDot RD μ u i v)
  val_inv := by
    rw [End.mul_def, ldot_eq_lplc, invDot_eq_lplc, ← lplc_comp, invDot_comp_downDot, lplc_id]
    rfl
  inv_val := by
    rw [End.mul_def, ldot_eq_lplc, invDot_eq_lplc, ← lplc_comp, downDot_comp_invDot, lplc_id]
    rfl

/-- `n ∈ ℤ` dots on the strand `F_i` between `u` and `v` in `U′` (inverse dots for `n < 0`). -/
def zdot (μ : X) (u : List (Letter I)) (i : I) (v : List (Letter I)) (n : ℤ) :
    lob RD k μ (u ++ [dn i] ++ v) ⟶ lob RD k μ (u ++ [dn i] ++ v) :=
  ((dotUnit RD k μ u i v ^ n : (End (lob RD k μ (u ++ [dn i] ++ v)))ˣ) : End _)

theorem zdot_add (μ : X) (u : List (Letter I)) (i : I) (v : List (Letter I)) (m n : ℤ) :
    zdot RD k μ u i v (m + n) = zdot RD k μ u i v n ≫ zdot RD k μ u i v m := by
  rw [zdot, zpow_add, Units.val_mul, End.mul_def]; rfl

theorem zdot_comm (μ : X) (u : List (Letter I)) (i : I) (v : List (Letter I)) (m n : ℤ) :
    zdot RD k μ u i v m ≫ zdot RD k μ u i v n = zdot RD k μ u i v n ≫ zdot RD k μ u i v m := by
  rw [← zdot_add, ← zdot_add, add_comm]

@[simp] theorem zdot_zero (μ : X) (u : List (Letter I)) (i : I) (v : List (Letter I)) :
    zdot RD k μ u i v 0 = 𝟙 _ := by
  rw [zdot, zpow_zero]; rfl

theorem zdot_one (μ : X) (u : List (Letter I)) (i : I) (v : List (Letter I)) :
    zdot RD k μ u i v 1 = ldot RD k μ u i v := by
  rw [zdot, zpow_one]; rfl

theorem zdot_neg_one (μ : X) (u : List (Letter I)) (i : I) (v : List (Letter I)) :
    zdot RD k μ u i v (-1) = (presLoc RD k).diag (invDot RD μ u i v) := by
  rw [zdot, zpow_neg_one]; rfl

theorem zdot_neg_add_cancel (μ : X) (u : List (Letter I)) (i : I) (v : List (Letter I)) (n : ℤ) :
    zdot RD k μ u i v n ≫ zdot RD k μ u i v (-n) = 𝟙 _ := by
  rw [← zdot_add, neg_add_cancel, zdot_zero]

end Units

/-! ## Images of generators -/

section Images

variable (k : Type w) [CommRing k] (δ : X) (a b : I → ℤ)

/-- The single-layer diagram of `U′` of shape `g` with rightmost region `ν`. -/
abbrev lgen (ν : X) (g : Shape I) : lob RD k ν g.dom ⟶ lob RD k ν g.cod :=
  (presLoc RD k).diag (inclD RD (mkD RD ν [([], g, [])] ⟨by simp, by simp⟩))

/-- The dots placed on the downward leg of the cup `1 → l l*` (Webster's `y^{-a_i}` on the cup
`ι`, resp. `y^{-b_i}` on `ι′`). -/
def cupDec : (l : Letter I) → (ν : X) → (lob RD k ν [l, l.dual] ⟶ lob RD k ν [l, l.dual])
  | (true, i), ν => zdot RD k ν [up i] i [] (-a i)
  | (false, i), ν => zdot RD k ν [] i [up i] (-b i)

/-- The dots placed on the downward leg of the cap `l* l → 1` (Webster's `y^{a_i}` on the cap
`ε`, resp. `y^{b_i}` on `ε′`). -/
def capDec : (l : Letter I) → (ν : X) → (lob RD k ν [l.dual, l] ⟶ lob RD k ν [l.dual, l])
  | (true, i), ν => zdot RD k ν [] i [up i] (a i)
  | (false, i), ν => zdot RD k ν [up i] i [] (b i)

/-- The image of the cup `1 → l l*` with rightmost region `ν`. -/
def cupImg (l : Letter I) (ν : X) : lob RD k ν [] ⟶ lob RD k ν [l, l.dual] :=
  lgen RD k ν (.cup l) ≫ cupDec RD k a b l ν

/-- The image of the cap `l* l → 1` with rightmost region `ν`. -/
def capImg (l : Letter I) (ν : X) : lob RD k ν [l.dual, l] ⟶ lob RD k ν [] :=
  capDec RD k a b l ν ≫ lgen RD k ν (.cap l)

theorem genDom_dot (c : Col I X) :
    LocalMap.genDom (shiftMap RD δ) (.inl (.gen (.dot c)) : (lsig RD).Gen) =
      (incl RD).obj (ob RD (c.r + δ) (Shape.dot c.l).dom) :=
  shiftMap_ob RD δ c.r [c.l]

theorem genCod_dot (c : Col I X) :
    LocalMap.genCod (shiftMap RD δ) (.inl (.gen (.dot c)) : (lsig RD).Gen) =
      (incl RD).obj (ob RD (c.r + δ) (Shape.dot c.l).cod) :=
  shiftMap_ob RD δ c.r [c.l]

theorem genDom_cross (ε : Bool) (i j : I) (ν : X) :
    LocalMap.genDom (shiftMap RD δ) (.inl (.gen (.cross ε i j ν)) : (lsig RD).Gen) =
      (incl RD).obj (ob RD (ν + δ) (Shape.cross ε i j).dom) :=
  shiftMap_ob RD δ ν _

theorem genCod_cross (ε : Bool) (i j : I) (ν : X) :
    LocalMap.genCod (shiftMap RD δ) (.inl (.gen (.cross ε i j ν)) : (lsig RD).Gen) =
      (incl RD).obj (ob RD (ν + δ) (Shape.cross ε i j).cod) := by
  rw [← shiftMap_ob]
  refine Obj.ext ?_ rfl
  change wt RD ν (Shape.cross ε i j).dom + δ = wt RD ν (Shape.cross ε i j).cod + δ
  rw [Shape.wt_dom_eq_wt_cod (RD := RD) ν (.cross ε i j)]

theorem genDom_inv (p : I × X) :
    LocalMap.genDom (shiftMap RD δ) (.inr p : (lsig RD).Gen) =
      (incl RD).obj (ob RD (p.2 + δ) [dn p.1]) :=
  shiftMap_ob RD δ p.2 [dn p.1]

theorem genDom_cup (c : Col I X) :
    LocalMap.genDom (shiftMap RD δ) (.inl (.cup c) : (lsig RD).Gen) =
      (incl RD).obj (ob RD (sh RD c.l + c.r + δ) []) := rfl

theorem genCod_cup (c : Col I X) :
    LocalMap.genCod (shiftMap RD δ) (.inl (.cup c) : (lsig RD).Gen) =
      (incl RD).obj (ob RD (sh RD c.l + c.r + δ) [c.l, c.l.dual]) := by
  have h : sh RD c.l.dual + (sh RD c.l + c.r + δ) = c.r + δ := by
    rw [sh_dual]; abel
  refine Obj.ext ?_ ?_
  · change sh RD c.l + c.r + δ = sh RD c.l + (sh RD c.l.dual + (sh RD c.l + c.r + δ))
    rw [h, add_assoc]
  · change [(⟨c.l, c.r + δ⟩ : Col I X), ⟨c.l.dual, sh RD c.l + c.r + δ⟩] =
      [⟨c.l, sh RD c.l.dual + (sh RD c.l + c.r + δ)⟩, ⟨c.l.dual, sh RD c.l + c.r + δ⟩]
    rw [h]

theorem genDom_cap (c : Col I X) :
    LocalMap.genDom (shiftMap RD δ) (.inl (.cap c) : (lsig RD).Gen) =
      (incl RD).obj (ob RD (c.r + δ) [c.l.dual, c.l]) := by
  refine Obj.ext ?_ ?_
  · change c.r + δ = sh RD c.l.dual + (sh RD c.l + (c.r + δ))
    rw [← add_assoc, sh_dual, neg_add_cancel, zero_add]
  · change [(⟨c.l.dual, sh RD c.l + c.r + δ⟩ : Col I X), ⟨c.l, c.r + δ⟩] =
      [⟨c.l.dual, sh RD c.l + (c.r + δ)⟩, ⟨c.l, c.r + δ⟩]
    rw [add_assoc]

theorem genCod_cap (c : Col I X) :
    LocalMap.genCod (shiftMap RD δ) (.inl (.cap c) : (lsig RD).Gen) =
      (incl RD).obj (ob RD (c.r + δ) []) := rfl

/-- The images of the generators of `U′` under the weight shift by `δ` with exponents `a`, `b`
(Webster arXiv:1309.3796v2, Proposition 3.30): dots, crossings and inverse dots go to the same
generators in the shifted regions; cups and caps are decorated by `∓a_i`, `∓b_i` dots on their
downward legs. -/
def shiftImg : (g : (lsig RD).Gen) →
    ((presLoc RD k).obj (LocalMap.genDom (shiftMap RD δ) g) ⟶
      (presLoc RD k).obj (LocalMap.genCod (shiftMap RD δ) g))
  | .inl (.gen (.dot c)) => eqToHom (congrArg (presLoc RD k).obj (genDom_dot RD δ c)) ≫
      lgen RD k (c.r + δ) (.dot c.l) ≫
        eqToHom (congrArg (presLoc RD k).obj (genCod_dot RD δ c)).symm
  | .inl (.gen (.cross ε i j ν)) =>
      eqToHom (congrArg (presLoc RD k).obj (genDom_cross RD δ ε i j ν)) ≫
        lgen RD k (ν + δ) (.cross ε i j) ≫
          eqToHom (congrArg (presLoc RD k).obj (genCod_cross RD δ ε i j ν)).symm
  | .inl (.cup c) => eqToHom (congrArg (presLoc RD k).obj (genDom_cup RD δ c)) ≫
      cupImg RD k a b c.l (sh RD c.l + c.r + δ) ≫
        eqToHom (congrArg (presLoc RD k).obj (genCod_cup RD δ c)).symm
  | .inl (.cap c) => eqToHom (congrArg (presLoc RD k).obj (genDom_cap RD δ c)) ≫
      capImg RD k a b c.l (c.r + δ) ≫
        eqToHom (congrArg (presLoc RD k).obj (genCod_cap RD δ c)).symm
  | .inr p => eqToHom (congrArg (presLoc RD k).obj (genDom_inv RD δ p)) ≫
      (presLoc RD k).diag (invDotF RD p.1 (p.2 + δ)) ≫
        eqToHom (congrArg (presLoc RD k).obj (genDom_inv RD δ p)).symm

theorem shiftImg_parity (g : (lsig RD).Gen) :
    shiftImg RD k δ a b g ∈ (presLoc RD k).homDeg (Presentation.parityDeg (lsig RD))
      (LocalMap.genDom (shiftMap RD δ) g) (LocalMap.genCod (shiftMap RD δ) g)
      (Presentation.parityDeg (lsig RD) g) :=
  LocalMap.parity_of_isEven (shiftMap RD δ) (shiftImg RD k δ a b) g

/-- The relations of `U′` hold for the images of the generators under the weight shift
(the relation check needed for Webster arXiv:1309.3796v2, Proposition 3.30; not yet proved). -/
def ShiftRelations : Prop :=
  ∀ r, (freeLift k (LocalMap.ofGen (shiftMap RD δ) (shiftImg RD k δ a b)).functor).map
    ((presLoc RD k).rel r) = 0

/-- The weight-shift functor of `U′`, given that the relations hold for the images of the
generators (Webster arXiv:1309.3796v2, Proposition 3.30). -/
def shiftFunctor (h : ShiftRelations RD k δ a b) :
    (presLoc RD k).Presented ⥤ (presLoc RD k).Presented :=
  LocalMap.liftGen (shiftMap RD δ) (shiftImg RD k δ a b) (presLoc RD k)
    (shiftImg_parity RD k δ a b) h

end Images

end Categorification.KL3.Diagram

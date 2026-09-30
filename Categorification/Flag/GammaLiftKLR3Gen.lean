/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.GammaLiftKLR2

/-!
# `Γ_N` of the KLR generators on three upward strands

The bimodule evaluations (whiskered on the right by any word `v`, from any start region `s`) of the
three-strand KLR diagrams `XL c d e`, `XR c d e` (crossings of the strands `0, 1` and `1, 2`) and
`E0`, `E1`, `E2` (dots) of `Categorification.KLR.Diagram`, placed on upward strands with rightmost
region `μ`. The images are stated through the path-model maps `imXL`, `imWR`, `imE0`, `imE1`,
`imE2` on three-strand words whose regions are arbitrary (they are defined for variable regions;
the relation checks instantiate them):

* `evalB_XL`: `imXL`, the whiskered two-strand crossing `locTwo (crossU c d …)`;
* `evalB_XR`: `imWR`, the strand `E_c` whiskered with `locTwo (crossU d e …)`, followed by the
  identification `trW` of the region to the right of `E_c` (`μ + d + e` computed in the two
  orders of the strands; `wordXR`);
* `evalB_E0`, `evalB_E1`, `evalB_E2`: multiplication by the three dots (the generators of
  `Categorification.Flag.ev3`).

The identifications `trW` are absorbed into the next crossing (`trW_absorb_imXL`). The composites
of the images along the two sides of the braid relation are the maps `braidL`, `braidR` of
`Categorification.Flag.GammaThree` (`imBraidL`, `imBraidR`, `trW_absorb_braidR`).
-/

-- Preserve elaboration of semireducible diagram transports.
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Flag

open StringDiagrams Categorification.KL3.Diagram CategoryTheory MvPolynomial

universe u

variable {K : Type u} [Field K] {m : ℕ} {N : ℕ}

local notation "RD" => slRootDatum m

/-! ### Path-model maps on three-strand words -/

section Images

variable (K)

/-- The crossing of the first two strands of a three-strand upward word. -/
def imXL (a b c : Fin m) {s x y z x' : Wt m} {v : List (psig RD).Colour}
    (h : WOK N s (⟨up a, x⟩ :: ⟨up b, y⟩ :: ⟨up c, z⟩ :: v))
    (h' : WOK N s (⟨up b, x'⟩ :: ⟨up a, y⟩ :: ⟨up c, z⟩ :: v)) :
    BHom (gammaR K N s _ h) (gammaR K N s _ h') :=
  locTwo (crossU K a b h.step h.tail.step h'.step h'.tail.step)
    ((stepB K _ _ _ h.tail.tail.step).tensor (gammaR K N _ v h.tail.tail.tail))

/-- The crossing of the last two strands of a three-strand upward word. -/
def imWR (a b c : Fin m) {s x y z y' : Wt m} {v : List (psig RD).Colour}
    (h : WOK N s (⟨up a, x⟩ :: ⟨up b, y⟩ :: ⟨up c, z⟩ :: v))
    (h' : WOK N s (⟨up a, x⟩ :: ⟨up c, y'⟩ :: ⟨up b, z⟩ :: v)) :
    BHom (gammaR K N s _ h) (gammaR K N s _ h') :=
  BHom.whiskerLeft (stepB K _ _ _ h.step)
    (locTwo (crossU K b c h.tail.step h.tail.tail.step h'.tail.step h'.tail.tail.step)
      (gammaR K N _ v h.tail.tail.tail))

/-- The dot on the first strand of a three-strand upward word. -/
def imE0 (a b c : Fin m) {s x y z : Wt m} {v : List (psig RD).Colour}
    (h : WOK N s (⟨up a, x⟩ :: ⟨up b, y⟩ :: ⟨up c, z⟩ :: v)) :
    (gammaR K N s _ h).T :=
  BRing.tmul (stepB K _ _ _ h.step)
    ((stepB K _ _ _ h.tail.step).tensor ((stepB K _ _ _ h.tail.tail.step).tensor
      (gammaR K N _ v h.tail.tail.tail))) (eXi K a _ (h.step : StepR (true, a) _ _).2) 1

/-- The dot on the second strand of a three-strand upward word. -/
def imE1 (a b c : Fin m) {s x y z : Wt m} {v : List (psig RD).Colour}
    (h : WOK N s (⟨up a, x⟩ :: ⟨up b, y⟩ :: ⟨up c, z⟩ :: v)) :
    (gammaR K N s _ h).T :=
  BRing.tmul (stepB K _ _ _ h.step)
    ((stepB K _ _ _ h.tail.step).tensor ((stepB K _ _ _ h.tail.tail.step).tensor
      (gammaR K N _ v h.tail.tail.tail))) 1
    (BRing.tmul (stepB K _ _ _ h.tail.step)
      ((stepB K _ _ _ h.tail.tail.step).tensor (gammaR K N _ v h.tail.tail.tail))
      (eXi K b _ (h.tail.step : StepR (true, b) _ _).2) 1)

/-- The dot on the third strand of a three-strand upward word. -/
def imE2 (a b c : Fin m) {s x y z : Wt m} {v : List (psig RD).Colour}
    (h : WOK N s (⟨up a, x⟩ :: ⟨up b, y⟩ :: ⟨up c, z⟩ :: v)) :
    (gammaR K N s _ h).T :=
  BRing.tmul (stepB K _ _ _ h.step)
    ((stepB K _ _ _ h.tail.step).tensor ((stepB K _ _ _ h.tail.tail.step).tensor
      (gammaR K N _ v h.tail.tail.tail))) 1
    (BRing.tmul (stepB K _ _ _ h.tail.step)
      ((stepB K _ _ _ h.tail.tail.step).tensor (gammaR K N _ v h.tail.tail.tail)) 1
      (BRing.tmul (stepB K _ _ _ h.tail.tail.step) (gammaR K N _ v h.tail.tail.tail)
        (eXi K c _ (h.tail.tail.step : StepR (true, c) _ _).2) 1))

end Images

/-! ### Composites -/

/-- An identification of the first region is absorbed by a following crossing of the first two
strands. -/
theorem trW_absorb_imXL (a b c : Fin m) {s x x₀ y z x' : Wt m} {v : List (psig RD).Colour}
    (hx : x₀ = x)
    (ew : (⟨up a, x₀⟩ :: ⟨up b, y⟩ :: ⟨up c, z⟩ :: v : List (WCol m)) =
      ⟨up a, x⟩ :: ⟨up b, y⟩ :: ⟨up c, z⟩ :: v)
    (hL : WOK N s (⟨up a, x₀⟩ :: ⟨up b, y⟩ :: ⟨up c, z⟩ :: v))
    (h : WOK N s (⟨up a, x⟩ :: ⟨up b, y⟩ :: ⟨up c, z⟩ :: v))
    (h' : WOK N s (⟨up b, x'⟩ :: ⟨up a, y⟩ :: ⟨up c, z⟩ :: v)) :
    (imXL K a b c h h').comp (trW s ew hL h) = imXL K a b c hL h' := by
  subst hx
  rw [trW_self]
  rfl

/-- `trW_absorb_imXL` inside a composite. -/
theorem trW_absorb_imXL' (a b c : Fin m) {s x x₀ y z x' : Wt m} {v : List (psig RD).Colour}
    (hx : x₀ = x)
    (ew : (⟨up a, x₀⟩ :: ⟨up b, y⟩ :: ⟨up c, z⟩ :: v : List (WCol m)) =
      ⟨up a, x⟩ :: ⟨up b, y⟩ :: ⟨up c, z⟩ :: v)
    (hL : WOK N s (⟨up a, x₀⟩ :: ⟨up b, y⟩ :: ⟨up c, z⟩ :: v))
    (h : WOK N s (⟨up a, x⟩ :: ⟨up b, y⟩ :: ⟨up c, z⟩ :: v))
    (h' : WOK N s (⟨up b, x'⟩ :: ⟨up a, y⟩ :: ⟨up c, z⟩ :: v)) {M : BRing (H K (compOf N s)) K}
    (φ : BHom M (gammaR K N s _ hL)) :
    (imXL K a b c h h').comp ((trW s ew hL h).comp φ) = (imXL K a b c hL h').comp φ := by
  rw [← BHom.comp_assoc, trW_absorb_imXL a b c hx ew hL h h']

/-- The composite along `ψ₀ ψ₁ ψ₀` is `braidL`. -/
theorem imBraidL (c d e : Fin m) {s x y z x₁ y₂ x₃ : Wt m} {v : List (psig RD).Colour}
    (ha : WOK N s (⟨up c, x⟩ :: ⟨up d, y⟩ :: ⟨up e, z⟩ :: v))
    (hm : WOK N s (⟨up d, x₁⟩ :: ⟨up c, y⟩ :: ⟨up e, z⟩ :: v))
    (hL : WOK N s (⟨up d, x₁⟩ :: ⟨up e, y₂⟩ :: ⟨up c, z⟩ :: v))
    (hb : WOK N s (⟨up e, x₃⟩ :: ⟨up d, y₂⟩ :: ⟨up c, z⟩ :: v)) :
    (imXL K d e c hL hb).comp ((imWR K d c e hm hL).comp (imXL K c d e ha hm)) =
      braidL K c d e ha.step ha.tail.step ha.tail.tail.step hm.step hm.tail.step hL.tail.step
        hb.step hb.tail.step hb.tail.tail.step (gammaR K N _ v ha.tail.tail.tail) :=
  rfl

/-- The composite along `ψ₁ ψ₀ ψ₁` is `braidR`. -/
theorem imBraidR (c d e : Fin m) {s x y z y₁ x₂ y₃ : Wt m} {v : List (psig RD).Colour}
    (ha : WOK N s (⟨up c, x⟩ :: ⟨up d, y⟩ :: ⟨up e, z⟩ :: v))
    (hL : WOK N s (⟨up c, x⟩ :: ⟨up e, y₁⟩ :: ⟨up d, z⟩ :: v))
    (hm : WOK N s (⟨up e, x₂⟩ :: ⟨up c, y₁⟩ :: ⟨up d, z⟩ :: v))
    (hL' : WOK N s (⟨up e, x₂⟩ :: ⟨up d, y₃⟩ :: ⟨up c, z⟩ :: v)) :
    (imWR K e c d hm hL').comp ((imXL K c e d hL hm).comp (imWR K c d e ha hL)) =
      braidR K c d e ha.step ha.tail.step ha.tail.tail.step hL.tail.step hL.tail.tail.step
        hm.tail.step hm.step hL'.tail.step hL'.tail.tail.step (gammaR K N _ v ha.tail.tail.tail) :=
  rfl

/-- An identification of the first region of the target is absorbed by `braidR`. -/
theorem trW_absorb_braidR (c d e : Fin m) {s x y z y₁ x₂ x₃ y₃ : Wt m}
    {v : List (psig RD).Colour} (hx : x₂ = x₃)
    (ew : (⟨up e, x₂⟩ :: ⟨up d, y₃⟩ :: ⟨up c, z⟩ :: v : List (WCol m)) =
      ⟨up e, x₃⟩ :: ⟨up d, y₃⟩ :: ⟨up c, z⟩ :: v)
    (ha : WOK N s (⟨up c, x⟩ :: ⟨up d, y⟩ :: ⟨up e, z⟩ :: v))
    (hL : WOK N s (⟨up c, x⟩ :: ⟨up e, y₁⟩ :: ⟨up d, z⟩ :: v))
    (hm : WOK N s (⟨up e, x₂⟩ :: ⟨up c, y₁⟩ :: ⟨up d, z⟩ :: v))
    (hL' : WOK N s (⟨up e, x₂⟩ :: ⟨up d, y₃⟩ :: ⟨up c, z⟩ :: v))
    (hb : WOK N s (⟨up e, x₃⟩ :: ⟨up d, y₃⟩ :: ⟨up c, z⟩ :: v))
    (hb₁ : StepR (true, c) (compOf N y₁) (compOf N x₃)) :
    (trW s ew hL' hb).comp
        (braidR K c d e ha.step ha.tail.step ha.tail.tail.step hL.tail.step hL.tail.tail.step
          hm.tail.step hm.step hL'.tail.step hL'.tail.tail.step (gammaR K N _ v ha.tail.tail.tail)) =
      braidR K c d e ha.step ha.tail.step ha.tail.tail.step hL.tail.step hL.tail.tail.step
        hb₁ hb.step hb.tail.step hb.tail.tail.step (gammaR K N _ v ha.tail.tail.tail) := by
  subst hx
  rw [trW_self]
  rfl

/-! ### The generators -/

variable (dnScal : Fin m → Fin m → K)

theorem evalB_XL (c d e : Fin m) (μ s : Wt m) (v : List (psig RD).Colour)
    (ha : WOK N s ((ob RD μ (ups [c, d, e])).word ++ v))
    (hb : WOK N s ((ob RD μ (ups [d, c, e])).word ++ v)) :
    evalB K N dnScal s v ha hb (upLin RD K μ (LinDiagram.of (KLR.Diagram.XL c d e))) =
      imXL K c d e ha hb := by
  rw [upLin_of, evalB_of]
  simp only [layers_upDiag, KLR.Diagram.layers_dl, List.map_cons, List.map_nil, chainBD]
  split_ifs with h
  · simp only [trW_self, BHom.id_comp', BHom.comp_id']
    rw [show genScal K dnScal (dataV v (upLay RD μ (KLR.Diagram.lay [] (.cross c d) [e]))).2.1 = 1
      from rfl, BHom.csmul_one]
    rfl
  · exact absurd hb h

/-- The region to the right of the first strand, in the two orders of the other two. -/
theorem wordXR (c d e : Fin m) (μ : Wt m) (v : List (psig RD).Colour) :
    ((⟨up c, wt RD μ [up d, up e]⟩ :: ⟨up e, wt RD μ [up d]⟩ :: ⟨up d, μ⟩ :: v :
      List (WCol m)) = (ob RD μ (ups [c, e, d])).word ++ v) := by
  show _ = (⟨up c, wt RD μ [up e, up d]⟩ :: ⟨up e, wt RD μ [up d]⟩ :: ⟨up d, μ⟩ :: v :
    List (WCol m))
  simp only [wt_cons, wt_nil, add_left_comm (sh RD (up d))]

theorem evalB_XR (c d e : Fin m) (μ s : Wt m) (v : List (psig RD).Colour)
    (ha : WOK N s ((ob RD μ (ups [c, d, e])).word ++ v))
    (hb : WOK N s ((ob RD μ (ups [c, e, d])).word ++ v))
    (hL : WOK N s (⟨up c, wt RD μ [up d, up e]⟩ :: ⟨up e, wt RD μ [up d]⟩ :: ⟨up d, μ⟩ :: v)) :
    evalB K N dnScal s v ha hb (upLin RD K μ (LinDiagram.of (KLR.Diagram.XR c d e))) =
      (trW s (wordXR c d e μ v) hL hb).comp (imWR K c d e ha hL) := by
  rw [upLin_of, evalB_of]
  simp only [layers_upDiag, KLR.Diagram.layers_dl, List.map_cons, List.map_nil, chainBD]
  split_ifs with h
  · simp only [trW_self, BHom.comp_id']
    rw [show genScal K dnScal (dataV v (upLay RD μ (KLR.Diagram.lay [c] (.cross d e) []))).2.1 = 1
      from rfl, BHom.csmul_one]
    rfl
  · exact absurd hL h

theorem evalB_E0 (c d e : Fin m) (μ s : Wt m) (v : List (psig RD).Colour)
    (ha : WOK N s ((ob RD μ (ups [c, d, e])).word ++ v)) :
    evalB K N dnScal s v ha ha (upLin RD K μ (LinDiagram.of (KLR.Diagram.E0 c d e))) =
      BHom.mulB (imE0 K c d e ha) := by
  rw [upLin_of, evalB_of]
  show chainBD K N dnScal s _ ([([], .gen (.dot ⟨up c, wt RD μ [up d, up e]⟩), ⟨up d, wt RD μ [up e]⟩ :: ⟨up e, μ⟩ :: v)] : List (LData m)) _ _ ha ha = _
  simp only [chainBD]
  split_ifs with h
  · simp only [trW_self, BHom.id_comp', BHom.comp_id', genScal, BHom.csmul_one]
    simp only [layerMap, genMap, dotMap, locOne, BHom.whiskerRight_mulB]
    rfl
  · exact absurd ha h

theorem evalB_E1 (c d e : Fin m) (μ s : Wt m) (v : List (psig RD).Colour)
    (ha : WOK N s ((ob RD μ (ups [c, d, e])).word ++ v)) :
    evalB K N dnScal s v ha ha (upLin RD K μ (LinDiagram.of (KLR.Diagram.E1 c d e))) =
      BHom.mulB (imE1 K c d e ha) := by
  rw [upLin_of, evalB_of]
  show chainBD K N dnScal s _ ([([⟨up c, wt RD μ [up d, up e]⟩], .gen (.dot ⟨up d, wt RD μ [up e]⟩), ⟨up e, μ⟩ :: v)] : List (LData m)) _ _ ha ha = _
  simp only [chainBD]
  split_ifs with h
  · simp only [trW_self, BHom.id_comp', BHom.comp_id', genScal, BHom.csmul_one]
    simp only [layerMap, genMap, dotMap, locOne, BHom.whiskerRight_mulB, BHom.whiskerLeft_mulB]
    rfl
  · exact absurd ha h

theorem evalB_E2 (c d e : Fin m) (μ s : Wt m) (v : List (psig RD).Colour)
    (ha : WOK N s ((ob RD μ (ups [c, d, e])).word ++ v)) :
    evalB K N dnScal s v ha ha (upLin RD K μ (LinDiagram.of (KLR.Diagram.E2 c d e))) =
      BHom.mulB (imE2 K c d e ha) := by
  rw [upLin_of, evalB_of]
  show chainBD K N dnScal s _ ([([⟨up c, wt RD μ [up d, up e]⟩, ⟨up d, wt RD μ [up e]⟩], .gen (.dot ⟨up e, μ⟩), v)] : List (LData m)) _ _ ha ha = _
  simp only [chainBD]
  split_ifs with h
  · simp only [trW_self, BHom.id_comp', BHom.comp_id', genScal, BHom.csmul_one]
    simp only [layerMap, genMap, dotMap, locOne, BHom.whiskerRight_mulB, BHom.whiskerLeft_mulB]
    rfl
  · exact absurd ha h

end Categorification.Flag

end

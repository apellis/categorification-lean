/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.GammaLiftPoly
import Categorification.Flag.GammaLiftDots
import Categorification.Diagrams.KL3.GammaFlagDegenerate

/-!
# `Γ_N` of the KLR generators on upward strands

The KLR relations of `U_Q(sl_{m+1})` (Cautis–Lauda arXiv:1111.1431v3, §2.3, `sec:KLR`; KL III
Definition 3.1, relations of `R(ν)` on upward strands, relation index `klr μ r`) are relations
among the KLR diagrams `X2`, `D0`, `D1` on two strands and `XL`, `XR`, `E0`, `E1`, `E2` on three
strands (`Categorification.KLR.Diagram`), placed on upward strands with rightmost region `μ`
(`upLin`). This file computes the bimodule evaluation `evalB` of these generators, whiskered on
the right by any word `v`, as the path-model maps of `Categorification.Flag.GammaThree`:

* `evalB_X2`: the crossing is `locTwo (crossU …)` (KL III (6.8));
* `evalB_D0`, `evalB_D1`: the dots are multiplications by `ξ ⊗ 1` and `1 ⊗ ξ ⊗ 1`;
* `evalB_XL`, `evalB_XR`, `evalB_E0`, `evalB_E1`, `evalB_E2`: the same on three strands;

and provides the comparison lemmas used by the relation checks: the left and the right scalar
actions of a path bimodule agree (`gammaR_left_algebraMap`), whiskering `locTwo` of the
multiplication by a polynomial in the two dots (`locTwo_mulB_eval₂`), and the realizability of
the intermediate regions produced by the steps of `Flag_N` (`realized_of_stepR_up`).
-/

-- Preserve elaboration of semireducible diagram transports.
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Flag

open StringDiagrams Categorification.KL3.Diagram CategoryTheory MvPolynomial

universe u

variable {K : Type u} [Field K] {m : ℕ} {N : ℕ}

local notation "RD" => slRootDatum m

/-! ### Scalars of path bimodules -/

theorem stepB_left_algebraMap (l : SLetter m) (r s : Comp m) (h : StepR l r s) (c : K) :
    (stepB K l r s h).left (algebraMap K (H K s) c) =
      (stepB K l r s h).right (algebraMap K (H K r) c) := by
  obtain ⟨b, i⟩ := l
  cases b
  · show (eRight K i s h.2) (algebraMap K _ c) =
      (eLeft K i s h.2) ((hCast K h.1.symm) (algebraMap K _ c))
    rw [AlgEquiv.commutes, AlgHom.commutes, AlgHom.commutes]
  · show (eLeft K i r h.2) ((hCast K h.1.symm) (algebraMap K _ c)) =
      (eRight K i r h.2) (algebraMap K _ c)
    rw [AlgEquiv.commutes, AlgHom.commutes, AlgHom.commutes]

/-- **The left and the right scalar actions of a path bimodule agree.** -/
theorem gammaR_left_algebraMap : ∀ (s : Wt m) (w : List (WCol m)) (h : WOK N s w) (c : K),
    (gammaR K N s w h).left (algebraMap K (H K (compOf N s)) c) = (gammaR K N s w h).right c
  | _, [], _, _ => rfl
  | s, x :: w, h, c => by
    show BRing.tmul _ _ ((stepB K x.l (compOf N x.r) (compOf N s) h.step).left
        (algebraMap K _ c)) 1 = BRing.tmul _ _ 1 ((gammaR K N x.r w h.tail).right c)
    rw [← gammaR_left_algebraMap x.r w h.tail c, stepB_left_algebraMap,
      ← mul_one ((stepB K x.l (compOf N x.r) (compOf N s) h.step).right _), BRing.tmul_balance,
      mul_one]

/-! ### Realized regions from steps -/

theorem realized_of_comp {w : Wt m} {d : Comp m} (hd : ∑ j, d j = N) (hw : compWeight d = w) :
    Realized N w ∧ compOf N w = d :=
  ⟨⟨d, hd, hw⟩, compOf_eq hd hw⟩

theorem sum_raise' (i : Fin m) (d : Comp m) (h : 0 < d i.succ) :
    ∑ j, raise i d j = ∑ j, d j := by
  have key : raise i d + (Pi.single i.succ 1 : Comp m) = d + Pi.single i.castSucc 1 := by
    funext j
    simp only [Pi.add_apply, Pi.single_apply, raise]
    have hne : i.castSucc ≠ i.succ := (Fin.castSucc_lt_succ (i := i)).ne
    by_cases h1 : j = i.castSucc
    · subst h1; simp [hne]
    · by_cases h2 : j = i.succ
      · subst h2; simp [hne.symm]; omega
      · simp [h1, h2]
  have := congrArg (fun d : Comp m => ∑ j, d j) key
  rw [sum_add_single, sum_add_single] at this
  omega

theorem sh_up' (i : Fin m) : sh RD (up i) = (slRootDatum m).iX i := by
  simp [sh, QuantumGroup.UDot.sgn_true]

/-- An upward step out of a realized region (on its right) ends in a realized region. -/
theorem realized_of_stepR_up {μ : Wt m} (hμ : Realized N μ) (i : Fin m) {r' : Comp m}
    (h : StepR (true, i) (compOf N μ) r') :
    Realized N (sh RD (up i) + μ) ∧ compOf N (sh RD (up i) + μ) = r' := by
  obtain ⟨h1, h2⟩ := compOf_spec hμ
  have e := h.1
  subst e
  refine realized_of_comp ((sum_raise' i _ h.2).trans h1) ?_
  rw [compWeight_raise i _ h.2, h2, sh_up', add_comm]

/-- An upward step into a realized region (on its left) starts in a realized region. -/
theorem realized_of_stepR_up' {s : Wt m} (hs : Realized N s) (i : Fin m) {a : Comp m}
    (h : StepR (true, i) a (compOf N s)) (w : Wt m) (hw : sh RD (up i) + w = s) :
    Realized N w ∧ compOf N w = a := by
  obtain ⟨h1, h2⟩ := compOf_spec hs
  have e := h.1
  refine realized_of_comp ?_ ?_
  · rw [← sum_raise' i a h.2, e, h1]
  · have := compWeight_raise i a h.2
    rw [e, h2, ← hw, sh_up'] at this
    rw [add_comm] at this
    exact (add_right_cancel this).symm

/-! ### Two-strand maps on polynomials in the dots -/

section LocTwo

variable {A B C D E : Type u} [CommRing A] [Algebra K A] [CommRing B] [CommRing C] [CommRing E]

/-- **Whiskering the multiplication by a polynomial in the two dots**. -/
theorem locTwo_mulB_eval₂ {L : BRing A B} {L' : BRing B C} (a : L.T) (b : L'.T) (X : BRing C E)
    (p : MvPolynomial (Fin 2) K) :
    locTwo (BHom.mulB (eval₂ ((L.tensor L').left.comp (algebraMap K A))
        ![BRing.tmul L L' a 1, BRing.tmul L L' 1 b] p)) X =
      BHom.mulB (eval₂ ((L.tensor (L'.tensor X)).left.comp (algebraMap K A))
        ![BRing.tmul L (L'.tensor X) a 1, BRing.tmul L (L'.tensor X) 1 (BRing.tmul L' X b 1)] p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    simp only [eval₂_C, RingHom.comp_apply]
    rw [BRing.inclL_apply, BRing.inclL_apply, locTwo_mulB]
    rfl
  | add p q hp hq =>
    rw [eval₂_add, eval₂_add, BHom.mulB_add, BHom.mulB_add, locTwo_add, hp, hq]
  | mul_X p i hp =>
    rw [eval₂_mul, eval₂_mul, eval₂_X, eval₂_X, ← BHom.mulB_comp_mulB, ← BHom.mulB_comp_mulB,
      locTwo_comp, hp]
    congr 1
    fin_cases i
    · exact locTwo_mulB _ _ _
    · exact locTwo_mulB _ _ _

end LocTwo

/-! ### The generators on two strands -/

/-- The step of the first strand of a two-strand upward word. -/
theorem WOK.st₁ {s x μ : Wt m} {c d : Fin m} {v : List (psig RD).Colour}
    (h : WOK N s (⟨up c, x⟩ :: ⟨up d, μ⟩ :: v)) :
    StepR (true, c) (compOf N x) (compOf N s) := h.step

/-- The step of the second strand of a two-strand upward word. -/
theorem WOK.st₂ {s x μ : Wt m} {c d : Fin m} {v : List (psig RD).Colour}
    (h : WOK N s (⟨up c, x⟩ :: ⟨up d, μ⟩ :: v)) :
    StepR (true, d) (compOf N μ) (compOf N x) := h.tail.step

/-- The suffix of a two-strand upward word. -/
theorem WOK.sf₂ {s x μ : Wt m} {c d : Fin m} {v : List (psig RD).Colour}
    (h : WOK N s (⟨up c, x⟩ :: ⟨up d, μ⟩ :: v)) : WOK N μ v := h.tail.tail

theorem evalB_X2 (dnScal : Fin m → Fin m → K) (c d : Fin m) (μ s : Wt m)
    (v : List (psig RD).Colour)
    (ha : WOK N s (⟨up c, sh RD (up d) + μ⟩ :: ⟨up d, μ⟩ :: v))
    (hb : WOK N s (⟨up d, sh RD (up c) + μ⟩ :: ⟨up c, μ⟩ :: v)) :
    evalB K N dnScal (a := ob RD μ (ups [c, d])) (b := ob RD μ (ups [d, c])) s v ha hb
        (upLin RD K μ (LinDiagram.of (KLR.Diagram.X2 c d))) =
      locTwo (crossU K c d ha.st₁ ha.st₂ hb.st₁ hb.st₂) (gammaR K N μ v ha.sf₂) := by
  rw [upLin_of, evalB_of]
  have key : chainBD K N dnScal s (⟨up c, sh RD (up d) + μ⟩ :: ⟨up d, μ⟩ :: v)
      [([], .gen (.cross true c d μ), v)] (⟨up d, sh RD (up c) + μ⟩ :: ⟨up c, μ⟩ :: v)
      (by exact ⟨rfl, rfl⟩) ha hb =
      locTwo (crossU K c d ha.st₁ ha.st₂ hb.st₁ hb.st₂) (gammaR K N μ v ha.sf₂) := by
    simp only [chainBD]
    split_ifs with h
    · simp only [trW_self, BHom.id_comp', BHom.comp_id', genScal, BHom.csmul_one]
      rfl
    · exact absurd hb h
  exact key

theorem evalB_D0 (dnScal : Fin m → Fin m → K) (c d : Fin m) (μ s : Wt m)
    (v : List (psig RD).Colour)
    (ha : WOK N s (⟨up c, sh RD (up d) + μ⟩ :: ⟨up d, μ⟩ :: v)) :
    evalB K N dnScal (a := ob RD μ (ups [c, d])) (b := ob RD μ (ups [c, d])) s v ha ha
        (upLin RD K μ (LinDiagram.of (KLR.Diagram.D0 c d))) =
      BHom.mulB (BRing.tmul (stepB K _ _ _ ha.st₁)
        ((stepB K _ _ _ ha.st₂).tensor (gammaR K N μ v ha.sf₂)) (eXi K c _ ha.st₁.2) 1) := by
  rw [upLin_of, evalB_of]
  have key : chainBD K N dnScal s (⟨up c, sh RD (up d) + μ⟩ :: ⟨up d, μ⟩ :: v)
      [([], .gen (.dot ⟨up c, sh RD (up d) + μ⟩), ⟨up d, μ⟩ :: v)]
      (⟨up c, sh RD (up d) + μ⟩ :: ⟨up d, μ⟩ :: v) (by exact ⟨rfl, rfl⟩) ha ha =
      BHom.mulB (BRing.tmul (stepB K _ _ _ ha.st₁)
        ((stepB K _ _ _ ha.st₂).tensor (gammaR K N μ v ha.sf₂)) (eXi K c _ ha.st₁.2) 1) := by
    simp only [chainBD]
    split_ifs with h
    · simp only [trW_self, BHom.id_comp', BHom.comp_id', genScal, BHom.csmul_one]
      simp only [layerMap, genMap, dotMap, locOne, BHom.whiskerRight_mulB]
      rfl
    · exact absurd ha h
  exact key

theorem evalB_D1 (dnScal : Fin m → Fin m → K) (c d : Fin m) (μ s : Wt m)
    (v : List (psig RD).Colour)
    (ha : WOK N s (⟨up c, sh RD (up d) + μ⟩ :: ⟨up d, μ⟩ :: v)) :
    evalB K N dnScal (a := ob RD μ (ups [c, d])) (b := ob RD μ (ups [c, d])) s v ha ha
        (upLin RD K μ (LinDiagram.of (KLR.Diagram.D1 c d))) =
      BHom.mulB (BRing.tmul (stepB K _ _ _ ha.st₁)
        ((stepB K _ _ _ ha.st₂).tensor (gammaR K N μ v ha.sf₂)) 1
        (BRing.tmul (stepB K _ _ _ ha.st₂) (gammaR K N μ v ha.sf₂) (eXi K d _ ha.st₂.2) 1)) := by
  rw [upLin_of, evalB_of]
  have key : chainBD K N dnScal s (⟨up c, sh RD (up d) + μ⟩ :: ⟨up d, μ⟩ :: v)
      [([⟨up c, sh RD (up d) + μ⟩], .gen (.dot ⟨up d, μ⟩), v)]
      (⟨up c, sh RD (up d) + μ⟩ :: ⟨up d, μ⟩ :: v) (by exact ⟨rfl, rfl⟩) ha ha =
      BHom.mulB (BRing.tmul (stepB K _ _ _ ha.st₁)
        ((stepB K _ _ _ ha.st₂).tensor (gammaR K N μ v ha.sf₂)) 1
        (BRing.tmul (stepB K _ _ _ ha.st₂) (gammaR K N μ v ha.sf₂) (eXi K d _ ha.st₂.2) 1)) := by
    simp only [chainBD]
    split_ifs with h
    · simp only [trW_self, BHom.id_comp', BHom.comp_id', genScal, BHom.csmul_one]
      simp only [layerMap, genMap, dotMap, locOne, BHom.whiskerRight_mulB, BHom.whiskerLeft_mulB]
      rfl
    · exact absurd ha h
  exact key

/-- `evalB` of a composite of upward KLR diagrams through a valid object. -/
theorem evalB_up_comp (dnScal : Fin m → Fin m → K) (μ : Wt m)
    {a b c : Obj (KLR.Diagram.sig (Fin m))} (f : a ⟶ b) (g : b ⟶ c) (s : Wt m)
    (v : List (psig RD).Colour) (ha : WOK N s ((ob RD μ (ups a.word)).word ++ v))
    (hm : WOK N s ((ob RD μ (ups b.word)).word ++ v))
    (hc : WOK N s ((ob RD μ (ups c.word)).word ++ v)) :
    evalB K N dnScal s v ha hc (upLin RD K μ (LinDiagram.of (f ≫ g))) =
      (evalB K N dnScal s v hm hc (upLin RD K μ (LinDiagram.of g))).comp
        (evalB K N dnScal s v ha hm (upLin RD K μ (LinDiagram.of f))) := by
  rw [LinDiagram.of_comp, upLin_comp, evalB_comp dnScal s v ha hm hc]

/-- `evalB` of a composite of upward KLR diagrams through an invalid object is zero. -/
theorem evalB_up_comp_zero (dnScal : Fin m → Fin m → K) (μ : Wt m)
    {a b c : Obj (KLR.Diagram.sig (Fin m))} (f : a ⟶ b) (g : b ⟶ c) (s : Wt m)
    (v : List (psig RD).Colour) (ha : WOK N s ((ob RD μ (ups a.word)).word ++ v))
    (hm : ¬ WOK N s ((ob RD μ (ups b.word)).word ++ v))
    (hc : WOK N s ((ob RD μ (ups c.word)).word ++ v)) :
    evalB K N dnScal s v ha hc (upLin RD K μ (LinDiagram.of (f ≫ g))) = 0 := by
  rw [LinDiagram.of_comp, upLin_comp, evalB_comp_zero dnScal s v ha hm hc]

end Categorification.Flag

end

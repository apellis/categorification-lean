/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.GammaLiftKLR3Gen

/-!
# `Γ_N` respects the braid relations on upward strands

Cautis–Lauda arXiv:1111.1431v3, §2.3 (`sec:KLR`): the braid relations `eq_r3_easy-gen`
(`ψ₀ψ₁ψ₀ = ψ₁ψ₀ψ₁` unless `c = e ≠ d`) and `eq_r3_hard-gen`
(`ψ₀ψ₁ψ₀ - ψ₁ψ₀ψ₁ = r_c Q̄_{cd}(x₀, x₁, x₂)` on `E_c E_d E_c`), i.e. the relations `klr μ (braid …)`
and `klr μ (braidQ …)` of `CL.presCL` (`CL.relationR`); KL III Definition 3.1 and Proposition 6.8
((6.20), (6.21)) for `Γ_N`.

The two sides are evaluated with `evalB` (whiskered on the right by an arbitrary word `v`, from an
arbitrary start region `s`) as composites of the images of the generators
(`Categorification.Flag.GammaLiftKLR3Gen`), which are the maps `braidL`, `braidR` of
`Categorification.Flag.GammaThree` when all intermediate 1-morphisms are nonzero. The cases are
those of `Signed.braid_cases`:

* all intermediate 1-morphisms nonzero: `braid_three`, resp. `Signed.braidQ_signed` (with
  `Q_{cd} = Q^τ_{cd}` and `r_c = 1`);
* `c = e`, `d = c + 1`, `λ_{c+1} = 1`: `ψ₀ψ₁ψ₀` passes through a zero 1-morphism and
  `Γ(ψ₁ψ₀ψ₁) = 1 = -Q̄` (`Signed.braidR_degenerate`);
* `c = e`, `c = d + 1`, `λ_{d+1} = 0`: `ψ₁ψ₀ψ₁` passes through a zero 1-morphism and
  `Γ(ψ₀ψ₁ψ₀) = 1 = Q̄` (`Signed.braidL_degenerate`).
-/

noncomputable section

namespace Categorification.Flag

open StringDiagrams Categorification.KL3.Diagram CategoryTheory MvPolynomial

universe u

variable {K : Type u} [Field K] {m : ℕ} {N : ℕ}

local notation "RD" => slRootDatum m

/-! ### Validity of three-strand objects -/

theorem wok_ob3 {a b c : Fin m} {μ s : Wt m} {v : List (psig RD).Colour}
    (hs : wt RD μ [up a, up b, up c] = s) (hr : Realized N s)
    (h₁ : Realized N (wt RD μ [up b, up c])) (h₂ : Realized N (wt RD μ [up c]))
    (hv : WOK N μ v) : WOK N s ((ob RD μ (ups [a, b, c])).word ++ v) :=
  ⟨hr, hs, h₁, rfl, h₂, rfl, hv⟩

theorem WOK.ob3_src {a b c : Fin m} {μ s : Wt m} {v : List (psig RD).Colour}
    (h : WOK N s ((ob RD μ (ups [a, b, c])).word ++ v)) :
    wt RD μ [up a, up b, up c] = s := h.2.1

theorem WOK.ob3_r₀ {a b c : Fin m} {μ s : Wt m} {v : List (psig RD).Colour}
    (h : WOK N s ((ob RD μ (ups [a, b, c])).word ++ v)) : Realized N s := h.1

theorem WOK.ob3_r₁ {a b c : Fin m} {μ s : Wt m} {v : List (psig RD).Colour}
    (h : WOK N s ((ob RD μ (ups [a, b, c])).word ++ v)) :
    Realized N (wt RD μ [up b, up c]) := h.2.2.1

theorem WOK.ob3_r₂ {a b c : Fin m} {μ s : Wt m} {v : List (psig RD).Colour}
    (h : WOK N s ((ob RD μ (ups [a, b, c])).word ++ v)) :
    Realized N (wt RD μ [up c]) := h.2.2.2.2.1

theorem WOK.ob3_v {a b c : Fin m} {μ s : Wt m} {v : List (psig RD).Colour}
    (h : WOK N s ((ob RD μ (ups [a, b, c])).word ++ v)) : WOK N μ v :=
  h.2.2.2.2.2.2

theorem realized_of_step' {μ' : Wt m} (hμ : Realized N μ') (i : Fin m) {r' : Comp m}
    (h : StepR (true, i) (compOf N μ') r') : Realized N (wt RD μ' [up i]) :=
  (realized_of_stepR_up hμ i h).1

theorem wt_swap₀ (μ : Wt m) (a b c : Fin m) :
    wt RD μ [up a, up b, up c] = wt RD μ [up b, up a, up c] := by
  simp only [wt_cons, wt_nil]; abel

theorem wt_swap₁ (μ : Wt m) (a b c : Fin m) :
    wt RD μ [up a, up b, up c] = wt RD μ [up a, up c, up b] := by
  simp only [wt_cons, wt_nil]; abel

theorem wt_swap₂ (μ : Wt m) (a b : Fin m) : wt RD μ [up a, up b] = wt RD μ [up b, up a] := by
  simp only [wt_cons, wt_nil]; abel

/-- The first region of the top boundary of `XR a b c` from `ob μ [a, b, c]`. -/
theorem wok_XR {a b c : Fin m} {μ s : Wt m} {v : List (psig RD).Colour}
    (h : WOK N s ((ob RD μ (ups [a, c, b])).word ++ v)) :
    WOK N s (⟨up a, wt RD μ [up b, up c]⟩ :: ⟨up c, wt RD μ [up b]⟩ :: ⟨up b, μ⟩ :: v) :=
  ⟨h.1, (wt_swap₁ μ a b c).trans h.ob3_src,
    h.ob3_r₁.congr (wt_swap₂ μ c b), wt_swap₂ μ c b, h.ob3_r₂, rfl, h.ob3_v⟩

/-! ### The composites on normal-form objects -/

/-- The identification after `XR a b c` is absorbed by the following crossing `XL a c b`. -/
theorem absorbXR (a b c : Fin m) (μ s : Wt m) (v : List (psig RD).Colour)
    (hL : WOK N s (⟨up a, wt RD μ [up b, up c]⟩ :: ⟨up c, wt RD μ [up b]⟩ :: ⟨up b, μ⟩ :: v))
    (hm : WOK N s ((ob RD μ (ups [a, c, b])).word ++ v))
    (hb : WOK N s ((ob RD μ (ups [c, a, b])).word ++ v)) {M : BRing (H K (compOf N s)) K}
    (φ : BHom M (gammaR K N s _ hL)) :
    (imXL K a c b hm hb).comp ((trW s (wordXR a b c μ v) hL hm).comp φ) =
      (imXL K a c b hL hb).comp φ :=
  trW_absorb_imXL' a c b (wt_swap₂ μ b c) _ hL hm hb φ

/-- `ψ₀ ψ₁ ψ₀` on normal-form objects. -/
theorem braidL_ob (c d e : Fin m) (μ s : Wt m) (v : List (psig RD).Colour)
    (ha : WOK N s ((ob RD μ (ups [c, d, e])).word ++ v))
    (hm : WOK N s ((ob RD μ (ups [d, c, e])).word ++ v))
    (hL : WOK N s (⟨up d, wt RD μ [up c, up e]⟩ :: ⟨up e, wt RD μ [up c]⟩ :: ⟨up c, μ⟩ :: v))
    (hb : WOK N s ((ob RD μ (ups [e, d, c])).word ++ v)) :
    (imXL K d e c hL hb).comp ((imWR K d c e hm hL).comp (imXL K c d e ha hm)) =
      braidL K c d e ha.step ha.tail.step ha.tail.tail.step hm.step hm.tail.step hL.tail.step
        hb.step hb.tail.step hb.tail.tail.step (gammaR K N _ v ha.tail.tail.tail) :=
  imBraidL c d e ha hm hL hb

/-- `ψ₁ ψ₀ ψ₁` on normal-form objects, followed by the identification of the target. -/
theorem braidR_ob (c d e : Fin m) (μ s : Wt m) (v : List (psig RD).Colour)
    (ha : WOK N s ((ob RD μ (ups [c, d, e])).word ++ v))
    (hL : WOK N s (⟨up c, wt RD μ [up d, up e]⟩ :: ⟨up e, wt RD μ [up d]⟩ :: ⟨up d, μ⟩ :: v))
    (hm : WOK N s ((ob RD μ (ups [e, c, d])).word ++ v))
    (hL' : WOK N s (⟨up e, wt RD μ [up c, up d]⟩ :: ⟨up d, wt RD μ [up c]⟩ :: ⟨up c, μ⟩ :: v))
    (hb : WOK N s ((ob RD μ (ups [e, d, c])).word ++ v))
    (hb₁ : StepR (true, c) (compOf N (wt RD μ [up d])) (compOf N (wt RD μ [up d, up c]))) :
    (trW s (wordXR e c d μ v) hL' hb).comp ((imWR K e c d hm hL').comp
        ((imXL K c e d hL hm).comp (imWR K c d e ha hL))) =
      braidR K c d e ha.step ha.tail.step ha.tail.tail.step hL.tail.step hL.tail.tail.step
        hb₁ hb.step hb.tail.step hb.tail.tail.step (gammaR K N _ v ha.tail.tail.tail) := by
  rw [imBraidR c d e ha hL hm hL']
  exact trW_absorb_braidR c d e (wt_swap₂ μ c d) _ ha hL hm hL' hb hb₁

variable (dnScal : Fin m → Fin m → K)

/-! ### The two sides of the braid relation -/

/-- **`Γ_N(ψ₀ ψ₁ ψ₀)`** when the intermediate objects are valid. -/
theorem evalB_braidL (c d e : Fin m) (μ s : Wt m) (v : List (psig RD).Colour)
    (ha : WOK N s ((ob RD μ (ups [c, d, e])).word ++ v))
    (hm₁ : WOK N s ((ob RD μ (ups [d, c, e])).word ++ v))
    (hm₂ : WOK N s ((ob RD μ (ups [d, e, c])).word ++ v))
    (hb : WOK N s ((ob RD μ (ups [e, d, c])).word ++ v)) :
    evalB K N dnScal s v ha hb (upLin RD K μ (LinDiagram.of (KLR.Diagram.braidL c d e))) =
      braidL K c d e ha.step ha.tail.step ha.tail.tail.step hm₁.step hm₁.tail.step
        (wok_XR (a := d) (b := c) (c := e) hm₂).tail.step hb.step hb.tail.step
        hb.tail.tail.step (gammaR K N _ v ha.tail.tail.tail) := by
  have hL₂ := wok_XR (a := d) (b := c) (c := e) hm₂
  erw [evalB_up_comp dnScal μ (KLR.Diagram.XL c d e)
      (KLR.Diagram.XR d c e ≫ KLR.Diagram.XL d e c) s v ha hm₁ hb,
    evalB_up_comp dnScal μ (KLR.Diagram.XR d c e) (KLR.Diagram.XL d e c) s v hm₁ hm₂ hb,
    evalB_XL dnScal c d e μ s v ha hm₁, evalB_XR dnScal d c e μ s v hm₁ hm₂ hL₂,
    evalB_XL dnScal d e c μ s v hm₂ hb]
  simp only [BHom.comp_assoc]
  rw [absorbXR d c e μ s v hL₂ hm₂ hb, braidL_ob c d e μ s v ha hm₁ hL₂ hb]

/-- **`Γ_N(ψ₁ ψ₀ ψ₁)`** when the intermediate objects are valid. -/
theorem evalB_braidR (c d e : Fin m) (μ s : Wt m) (v : List (psig RD).Colour)
    (ha : WOK N s ((ob RD μ (ups [c, d, e])).word ++ v))
    (hm₁ : WOK N s ((ob RD μ (ups [c, e, d])).word ++ v))
    (hm₂ : WOK N s ((ob RD μ (ups [e, c, d])).word ++ v))
    (hb : WOK N s ((ob RD μ (ups [e, d, c])).word ++ v))
    (hb₁ : StepR (true, c) (compOf N (wt RD μ [up d])) (compOf N (wt RD μ [up d, up c]))) :
    evalB K N dnScal s v ha hb (upLin RD K μ (LinDiagram.of (KLR.Diagram.braidR c d e))) =
      braidR K c d e ha.step ha.tail.step ha.tail.tail.step
        (wok_XR (a := c) (b := d) (c := e) hm₁).tail.step
        (wok_XR (a := c) (b := d) (c := e) hm₁).tail.tail.step hb₁ hb.step hb.tail.step
        hb.tail.tail.step (gammaR K N _ v ha.tail.tail.tail) := by
  have hL₁ := wok_XR (a := c) (b := d) (c := e) hm₁
  have hL₃ := wok_XR (a := e) (b := c) (c := d) hb
  erw [evalB_up_comp dnScal μ (KLR.Diagram.XR c d e)
      (KLR.Diagram.XL c e d ≫ KLR.Diagram.XR e c d) s v ha hm₁ hb,
    evalB_up_comp dnScal μ (KLR.Diagram.XL c e d) (KLR.Diagram.XR e c d) s v hm₁ hm₂ hb,
    evalB_XR dnScal c d e μ s v ha hm₁ hL₁, evalB_XL dnScal c e d μ s v hm₁ hm₂,
    evalB_XR dnScal e c d μ s v hm₂ hb hL₃]
  simp only [BHom.comp_assoc]
  rw [absorbXR c d e μ s v hL₁ hm₁ hm₂, braidR_ob c d e μ s v ha hL₁ hm₂ hL₃ hb hb₁]

/-! ### The braid relation -/

/-- **`Γ_N` respects the braid relation `braid`** (`¬(c = e ∧ c ≠ d)`). -/
theorem evalB_klr_braid (Q : Fin m → Fin m → MvPolynomial (Fin 2) K) (rr : Fin m → K)
    (c d e : Fin m) (hne : ¬(c = e ∧ c ≠ d)) (μ s : Wt m) (v : List (psig RD).Colour)
    (ha : WOK N s ((ob RD μ (ups [c, d, e])).word ++ v))
    (hb : WOK N s ((ob RD μ (ups [e, d, c])).word ++ v)) :
    evalB K N dnScal s v ha hb (upLin RD K μ (CL.relationR K Q rr (.braid c d e hne))) = 0 := by
  simp only [CL.relationR, KLR.Diagram.relation]
  rw [upLin_sub, map_sub, sub_eq_zero]
  rcases Signed.braid_cases c d e ha.step ha.tail.step ha.tail.tail.step hb.step hb.tail.step
      hb.tail.tail.step with
    ⟨a₁, b₂, -, hca, -, -, hdb, -⟩ | ⟨hce, hadj, -⟩ | ⟨hce, hadj, -⟩
  · have hce' : Realized N (wt RD μ [up c, up e]) :=
      realized_of_step' (μ' := wt RD μ [up e]) ha.ob3_r₂ c hca
    have hd' : Realized N (wt RD μ [up d]) :=
      realized_of_step' (μ' := μ) ha.ob3_v.realized d hdb
    have hm₁ : WOK N s ((ob RD μ (ups [d, c, e])).word ++ v) :=
      wok_ob3 ((wt_swap₀ μ d c e).trans ha.ob3_src) ha.ob3_r₀ hce' ha.ob3_r₂ ha.ob3_v
    have hm₂ : WOK N s ((ob RD μ (ups [d, e, c])).word ++ v) :=
      wok_ob3 ((wt_swap₁ μ d e c).trans hm₁.ob3_src) ha.ob3_r₀
        (hce'.congr (wt_swap₂ μ c e)) hb.ob3_r₂ ha.ob3_v
    have hm₁' : WOK N s ((ob RD μ (ups [c, e, d])).word ++ v) :=
      wok_ob3 ((wt_swap₁ μ c e d).trans ha.ob3_src) ha.ob3_r₀
        (ha.ob3_r₁.congr (wt_swap₂ μ d e)) hd' ha.ob3_v
    have hm₂' : WOK N s ((ob RD μ (ups [e, c, d])).word ++ v) :=
      wok_ob3 ((wt_swap₀ μ e c d).trans hm₁'.ob3_src) ha.ob3_r₀
        (hb.ob3_r₁.congr (wt_swap₂ μ d c)) hd' ha.ob3_v
    have hb₁ := stepOK (up c) hd' hb.ob3_r₁ (wt_swap₂ μ c d)
    rw [evalB_braidL dnScal c d e μ s v ha hm₁ hm₂ hb,
      evalB_braidR dnScal c d e μ s v ha hm₁' hm₂' hb hb₁]
    exact braid_three c d e ha.step ha.tail.step ha.tail.tail.step hm₁.step hm₁.tail.step
      (wok_XR (a := d) (b := c) (c := e) hm₂).tail.step
      (wok_XR (a := c) (b := d) (c := e) hm₁').tail.step
      (wok_XR (a := c) (b := d) (c := e) hm₁').tail.tail.step hb₁ hb.step hb.tail.step
      hb.tail.tail.step (gammaR K N _ v ha.tail.tail.tail) hne
  · exact absurd ⟨hce, fun h => by subst h; exact castSucc_ne_succ' c hadj⟩ hne
  · exact absurd ⟨hce, fun h => by subst h; exact castSucc_ne_succ' c hadj⟩ hne

/-! ### The deformed braid relation -/

theorem BHom.zero_sub_id_sub_mulB_neg_one {A : Type u} [CommRing A] (M : BRing A K) :
    (0 : BHom M M) - BHom.id M - BHom.mulB (-1 : M.T) = 0 :=
  BHom.ext fun y => by simp

theorem BHom.id_sub_zero_sub_mulB_one {A : Type u} [CommRing A] (M : BRing A K) :
    BHom.id M - 0 - BHom.mulB (1 : M.T) = 0 :=
  BHom.ext fun y => by simp

theorem eval₂_imE (c d e : Fin m) (μ s : Wt m) (v : List (psig RD).Colour)
    (ha : WOK N s ((ob RD μ (ups [c, d, e])).word ++ v)) (p : MvPolynomial (Fin 3) K) :
    eval₂ (gammaR K N s _ ha).right ![imE0 K c d e ha, imE1 K c d e ha, imE2 K c d e ha] p =
      ev3 K (stepB K _ _ _ ha.step) (stepB K _ _ _ ha.tail.step) (stepB K _ _ _ ha.tail.tail.step)
        (gammaR K N _ v ha.tail.tail.tail) (eXi K c _ (ha.step : StepR (true, c) _ _).2)
        (eXi K d _ (ha.tail.step : StepR (true, d) _ _).2)
        (eXi K e _ (ha.tail.tail.step : StepR (true, e) _ _).2) p := by
  rw [← gammaR_right_eq]
  rfl

/-- **`Γ_N` respects the deformed braid relation `braidQ`** (`c ≠ d`), for `r_c = 1` and
`Q_{cd} = Q^τ_{cd}`. -/
theorem evalB_klr_braidQ (Q : Fin m → Fin m → MvPolynomial (Fin 2) K) (rr : Fin m → K)
    (hr : ∀ c, rr c = 1) (c d : Fin m) (hcd : c ≠ d) (hQ : Q c d = Signed.qSigned K m c d)
    (μ s : Wt m) (v : List (psig RD).Colour)
    (ha hb : WOK N s ((ob RD μ (ups [c, d, c])).word ++ v)) :
    evalB K N dnScal s v ha hb (upLin RD K μ (CL.relationR K Q rr (.braidQ c d hcd))) = 0 := by
  simp only [CL.relationR]
  rw [upLin_sub, upLin_sub, upLin_smul, map_sub, map_sub, map_smul, hr, one_smul, hQ]
  have hpoly := evalB_upLin_lpoly (N := N) dnScal μ (a := KLR.Diagram.ob [c, d, c]) s v ha
    ![KLR.Diagram.E0 c d c, KLR.Diagram.E1 c d c, KLR.Diagram.E2 c d c]
    ![imE0 K c d c ha, imE1 K c d c ha, imE2 K c d c ha]
    (fun i => by
      fin_cases i
      · rw [← upLin_of]; exact evalB_E0 dnScal c d c μ s v ha
      · rw [← upLin_of]; exact evalB_E1 dnScal c d c μ s v ha
      · rw [← upLin_of]; exact evalB_E2 dnScal c d c μ s v ha)
    (KLR.qbar (Signed.qSigned K m c d))
  erw [hpoly]
  erw [eval₂_imE c d c μ s v ha]
  rcases Signed.braid_cases c d c ha.step ha.tail.step ha.tail.tail.step hb.step hb.tail.step
      hb.tail.tail.step with
    ⟨a₁, b₂, -, hca, -, -, hdb, -⟩ | ⟨-, hadj, hdeg₃, hdeg₂, -, -, b₂, -, hdb⟩ |
      ⟨-, hadj, hdeg, -, -, a₁, -, hca⟩
  · have hcc : Realized N (wt RD μ [up c, up c]) :=
      realized_of_step' (μ' := wt RD μ [up c]) ha.ob3_r₂ c hca
    have hd' : Realized N (wt RD μ [up d]) :=
      realized_of_step' (μ' := μ) ha.ob3_v.realized d hdb
    have hm₁ : WOK N s ((ob RD μ (ups [d, c, c])).word ++ v) :=
      wok_ob3 ((wt_swap₀ μ d c c).trans ha.ob3_src) ha.ob3_r₀ hcc ha.ob3_r₂ ha.ob3_v
    have hm₁' : WOK N s ((ob RD μ (ups [c, c, d])).word ++ v) :=
      wok_ob3 ((wt_swap₁ μ c c d).trans ha.ob3_src) ha.ob3_r₀
        (ha.ob3_r₁.congr (wt_swap₂ μ d c)) hd' ha.ob3_v
    have hb₁ := stepOK (up c) hd' hb.ob3_r₁ (wt_swap₂ μ c d)
    rw [evalB_braidL dnScal c d c μ s v ha hm₁ hm₁ hb,
      evalB_braidR dnScal c d c μ s v ha hm₁' hm₁' hb hb₁, sub_eq_zero]
    exact Signed.braidQ_signed c d hcd ha.step ha.tail.step ha.tail.tail.step hm₁.step
      hm₁.tail.step (wok_XR (a := c) (b := d) (c := c) hm₁').tail.step
      (wok_XR (a := c) (b := d) (c := c) hm₁').tail.tail.step (gammaR K N _ v ha.tail.tail.tail)
  · -- `d = c + 1`, `λ_{c+1} = 1`: `ψ₀ψ₁ψ₀ = 0` and `ψ₁ψ₀ψ₁ = 1`
    have hd' : Realized N (wt RD μ [up d]) :=
      realized_of_step' (μ' := μ) ha.ob3_v.realized d hdb
    have hm₁' : WOK N s ((ob RD μ (ups [c, c, d])).word ++ v) :=
      wok_ob3 ((wt_swap₁ μ c c d).trans ha.ob3_src) ha.ob3_r₀
        (ha.ob3_r₁.congr (wt_swap₂ μ d c)) hd' ha.ob3_v
    have hb₁ := stepOK (up c) hd' hb.ob3_r₁ (wt_swap₂ μ c d)
    have hnot : ¬ WOK N s ((ob RD μ (ups [d, c, c])).word ++ v) := fun h =>
      (Nat.pos_iff_ne_zero.mp (h.tail.step : StepR (true, c) _ _).2) hdeg₂
    erw [evalB_up_comp_zero dnScal μ (KLR.Diagram.XL c d c)
      (KLR.Diagram.XR d c c ≫ KLR.Diagram.XL d c c) s v ha hnot hb]
    rw [evalB_braidR dnScal c d c μ s v ha hm₁' hm₁' hb hb₁]
    erw [Signed.braidR_degenerate c d ha.step ha.tail.step ha.tail.tail.step
      (gammaR K N _ v ha.tail.tail.tail) hadj hdeg₃
      (wok_XR (a := c) (b := d) (c := c) hm₁').tail.step
      (wok_XR (a := c) (b := d) (c := c) hm₁').tail.tail.step]
    rw [← Signed.qf_eq_qSigned hcd, Signed.Qf_of_castSucc_eq_succ c d hadj,
      Signed.qbar_X1_sub_X0, map_neg, map_one]
    exact BHom.zero_sub_id_sub_mulB_neg_one _
  · -- `c = d + 1`, `λ_{d+1} = 0`: `ψ₁ψ₀ψ₁ = 0` and `ψ₀ψ₁ψ₀ = 1`
    have hcc : Realized N (wt RD μ [up c, up c]) :=
      realized_of_step' (μ' := wt RD μ [up c]) ha.ob3_r₂ c hca
    have hm₁ : WOK N s ((ob RD μ (ups [d, c, c])).word ++ v) :=
      wok_ob3 ((wt_swap₀ μ d c c).trans ha.ob3_src) ha.ob3_r₀ hcc ha.ob3_r₂ ha.ob3_v
    have hnot : ¬ WOK N s ((ob RD μ (ups [c, c, d])).word ++ v) := fun h =>
      (Nat.pos_iff_ne_zero.mp (h.tail.tail.step : StepR (true, d) _ _).2) hdeg
    rw [evalB_braidL dnScal c d c μ s v ha hm₁ hm₁ hb]
    erw [evalB_up_comp_zero dnScal μ (KLR.Diagram.XR c d c)
      (KLR.Diagram.XL c c d ≫ KLR.Diagram.XR c c d) s v ha hnot hb]
    erw [Signed.braidL_degenerate c d ha.step ha.tail.step ha.tail.tail.step
      (gammaR K N _ v ha.tail.tail.tail) hadj hdeg hm₁.step hm₁.tail.step]
    rw [← Signed.qf_eq_qSigned hcd, Signed.Qf_of_succ_eq_castSucc c d hadj,
      Signed.qbar_X0_sub_X1, map_one]
    exact BHom.id_sub_zero_sub_mulB_one _

end Categorification.Flag

end

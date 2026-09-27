/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.GammaLiftKLRGen
import Categorification.Flag.GammaLiftZig
import Categorification.Diagrams.CL.Presentation

/-!
# `Γ_N` respects the two-strand KLR relations on upward strands

Cautis–Lauda arXiv:1111.1431v3, §2.3 (`sec:KLR`): the relations `eq_nil_rels` (`ψ² = 0` on
`E_i E_i`), `eq_nil_dotslide` (the nilHecke dot slides, with the scalar `r_i`), `eq_r2_ij-gen`
(`ψ² = Q_{ij}(x₀, x₁)`) and `eq_dot_slide_ij-gen` (the dot slides for `i ≠ j`), i.e. the relations
`klr μ r` of `CL.presCL` for the two-strand KLR relations `r` (`CL.relationR`); KL III
Definition 3.1 and Proposition 6.8 for `Γ_N`.

The relations are evaluated with `evalB` (whiskered on the right by an arbitrary word `v`) from
an arbitrary start region `s`: the images of the generators are the path-model maps
(`evalB_X2`, `evalB_D0`, `evalB_D1`), and the relations are

* the dot slides `DotRules.locL`, `DotRules.locR` of `crossU` (`crossU_rules`), with correction
  `τ = 1` for equal colours (`tauU_self`) and `τ = 0` otherwise;
* `ψ² = 0` for equal colours (`crossEEP2_sq`, the divided difference squares to zero);
* `ψ² = Q^τ_{cd}(ξ₀, ξ₁)` for `c ≠ d` (`Signed.gammaCross_sq`), with the polynomial side evaluated
  by `evalB_upLin_lpoly`; when the middle 1-morphism `E_d E_c 1_μ` is zero in the path model,
  the polynomial vanishes (`Signed.swap_cases`, `Signed.degen_qSigned_eq_zero`).

The scalars `r_i` enter only through `r_i = 1` (the `sl_n` scalars `CL.Sln.slnScalars`), and the
polynomial `Q_{cd}` of `sqNe` only through `Q_{cd} = Q^τ_{cd}` (`CL.Sln.qCL_sln_of_ne`).
-/

noncomputable section

namespace Categorification.Flag

open StringDiagrams Categorification.KL3.Diagram CategoryTheory MvPolynomial

universe u

variable {K : Type u} [Field K] {m : ℕ} {N : ℕ}

local notation "RD" => slRootDatum m

/-! ### Path-model lemmas -/

theorem crossEEP2_sq (i : Fin m) {t r₁ r₂ : Comp m} (h₁ : StepR (true, i) r₁ t)
    (h₂ : StepR (true, i) r₂ r₁) :
    (crossEEP2 K i h₁ h₂ h₁ h₂).comp (crossEEP2 K i h₁ h₂ h₁ h₂) = 0 := by
  refine BHom.ext fun y => ?_
  apply (eeEquiv K i i h₁ h₂ (eeVar i h₁ h₂) (eeVar_hv i h₁ h₂)).injective
  rw [BHom.comp_apply, crossEEP2_apply, crossEEP2_apply, crossEE_crossEE, BHom.zero_apply, map_zero]

theorem crossU_self_sq (i : Fin m) {t r₁ r₂ : Comp m} (h₁ : StepR (true, i) r₁ t)
    (h₂ : StepR (true, i) r₂ r₁) :
    (crossU K i i h₁ h₂ h₁ h₂).comp (crossU K i i h₁ h₂ h₁ h₂) = 0 := by
  simp only [crossU, dif_pos rfl]
  exact crossEEP2_sq i h₁ h₂

theorem tauU_of_ne {c d : Fin m} (hcd : c ≠ d) {t r₁ r₂ r₁' : Comp m} (h₁ : StepR (true, c) r₁ t)
    (h₂ : StepR (true, d) r₂ r₁) (h₁' : StepR (true, d) r₁' t) (h₂' : StepR (true, c) r₂ r₁') :
    tauU K c d h₁ h₂ h₁' h₂' = 0 := by
  simp only [tauU, dif_neg hcd]

theorem crossU_eq_gammaCross {c d : Fin m} (hcd : c ≠ d) {t r₁ r₂ r₁' : Comp m}
    (h₁ : StepR (true, c) r₁ t) (h₂ : StepR (true, d) r₂ r₁) (h₁' : StepR (true, d) r₁' t)
    (h₂' : StepR (true, c) r₂ r₁') :
    crossU K c d h₁ h₂ h₁' h₂' = Signed.gammaCross K c d hcd h₁ h₂ h₁' h₂' := by
  simp only [crossU, dif_neg hcd]
  rfl

theorem BHom.mulB_zero'' {A B : Type u} [CommRing A] [CommRing B] (M : BRing A B) :
    BHom.mulB (0 : M.T) = 0 :=
  BHom.ext fun z => zero_mul z

theorem evalB_upLin_id (dnScal : Fin m → Fin m → K) (μ : Wt m) (a : Obj (KLR.Diagram.sig (Fin m)))
    (s : Wt m) (v : List (psig RD).Colour) (ha hb : WOK N s ((ob RD μ (ups a.word)).word ++ v)) :
    evalB K N dnScal s v ha hb (upLin RD K μ (LinDiagram.of (𝟙 a))) = BHom.id _ := by
  rw [upLin_of]
  exact evalB_id dnScal _ s v ha hb

theorem gammaR_right_eq (s : Wt m) (w : List (WCol m)) (h : WOK N s w) :
    (gammaR K N s w h).left.comp (algebraMap K (H K (compOf N s))) = (gammaR K N s w h).right :=
  RingHom.ext fun c => gammaR_left_algebraMap s w h c

/-! ### The dot slides -/

variable (dnScal : Fin m → Fin m → K)

/-- **`Γ_N` respects the nilHecke dot slide `slideREq`** (`r_i = 1`). -/
theorem evalB_klr_slideREq (Q : Fin m → Fin m → MvPolynomial (Fin 2) K) (rr : Fin m → K)
    (hr : ∀ c, rr c = 1) (c : Fin m) (μ s : Wt m) (v : List (psig RD).Colour)
    (ha hb : WOK N s ((ob RD μ (ups [c, c])).word ++ v)) :
    evalB K N dnScal s v ha hb (upLin RD K μ (CL.relationR K Q rr (.slideREq c))) = 0 := by
  have ha' : WOK N s (⟨up c, sh RD (up c) + μ⟩ :: ⟨up c, μ⟩ :: v) := ha
  simp only [CL.relationR]
  rw [upLin_sub, upLin_sub, upLin_smul, map_sub, map_sub, map_smul]
  erw [evalB_up_comp dnScal μ (KLR.Diagram.D0 c c) (KLR.Diagram.X2 c c) s v ha ha hb,
    evalB_up_comp dnScal μ (KLR.Diagram.X2 c c) (KLR.Diagram.D1 c c) s v ha hb hb,
    evalB_D0 dnScal c c μ s v ha', evalB_X2 dnScal c c μ s v ha' ha',
    evalB_D1 dnScal c c μ s v ha']
  erw [evalB_upLin_id]
  have h := (crossU_rules c c ha'.st₁ ha'.st₂ ha'.st₁ ha'.st₂).locL (gammaR K N μ v ha'.sf₂)
  rw [Signed.tauU_self, locTwo_id] at h
  rw [h, hr, one_smul, add_sub_cancel_right]
  exact sub_self _

/-- **`Γ_N` respects the nilHecke dot slide `slideLEq`** (`r_i = 1`). -/
theorem evalB_klr_slideLEq (Q : Fin m → Fin m → MvPolynomial (Fin 2) K) (rr : Fin m → K)
    (hr : ∀ c, rr c = 1) (c : Fin m) (μ s : Wt m) (v : List (psig RD).Colour)
    (ha hb : WOK N s ((ob RD μ (ups [c, c])).word ++ v)) :
    evalB K N dnScal s v ha hb (upLin RD K μ (CL.relationR K Q rr (.slideLEq c))) = 0 := by
  have ha' : WOK N s (⟨up c, sh RD (up c) + μ⟩ :: ⟨up c, μ⟩ :: v) := ha
  simp only [CL.relationR]
  rw [upLin_sub, upLin_sub, upLin_smul, map_sub, map_sub, map_smul]
  erw [evalB_up_comp dnScal μ (KLR.Diagram.X2 c c) (KLR.Diagram.D0 c c) s v ha ha hb,
    evalB_up_comp dnScal μ (KLR.Diagram.D1 c c) (KLR.Diagram.X2 c c) s v ha ha hb,
    evalB_D0 dnScal c c μ s v ha', evalB_X2 dnScal c c μ s v ha' ha',
    evalB_D1 dnScal c c μ s v ha']
  erw [evalB_upLin_id]
  have h := (crossU_rules c c ha'.st₁ ha'.st₂ ha'.st₁ ha'.st₂).locR (gammaR K N μ v ha'.sf₂)
  rw [Signed.tauU_self, locTwo_id] at h
  rw [h, hr, one_smul, sub_sub_cancel]
  exact sub_self _

/-- **`Γ_N` respects the dot slide `slideLNe`** (`c ≠ d`). -/
theorem evalB_klr_slideLNe (Q : Fin m → Fin m → MvPolynomial (Fin 2) K) (rr : Fin m → K)
    (c d : Fin m) (hcd : c ≠ d) (μ s : Wt m) (v : List (psig RD).Colour)
    (ha : WOK N s ((ob RD μ (ups [c, d])).word ++ v))
    (hb : WOK N s ((ob RD μ (ups [d, c])).word ++ v)) :
    evalB K N dnScal s v ha hb (upLin RD K μ (CL.relationR K Q rr (.slideLNe c d hcd))) = 0 := by
  have ha' : WOK N s (⟨up c, sh RD (up d) + μ⟩ :: ⟨up d, μ⟩ :: v) := ha
  have hb' : WOK N s (⟨up d, sh RD (up c) + μ⟩ :: ⟨up c, μ⟩ :: v) := hb
  simp only [CL.relationR, KLR.Diagram.relation]
  rw [upLin_sub, map_sub]
  erw [evalB_up_comp dnScal μ (KLR.Diagram.X2 c d) (KLR.Diagram.D0 d c) s v ha hb hb,
    evalB_up_comp dnScal μ (KLR.Diagram.D1 c d) (KLR.Diagram.X2 c d) s v ha ha hb,
    evalB_D0 dnScal d c μ s v hb', evalB_X2 dnScal c d μ s v ha' hb',
    evalB_D1 dnScal c d μ s v ha']
  have h := (crossU_rules c d ha'.st₁ ha'.st₂ hb'.st₁ hb'.st₂).locR (gammaR K N μ v ha'.sf₂)
  rw [tauU_of_ne hcd, locTwo_zero] at h
  rw [h]
  rw [sub_zero, sub_self]

/-- **`Γ_N` respects the dot slide `slideRNe`** (`c ≠ d`). -/
theorem evalB_klr_slideRNe (Q : Fin m → Fin m → MvPolynomial (Fin 2) K) (rr : Fin m → K)
    (c d : Fin m) (hcd : c ≠ d) (μ s : Wt m) (v : List (psig RD).Colour)
    (ha : WOK N s ((ob RD μ (ups [c, d])).word ++ v))
    (hb : WOK N s ((ob RD μ (ups [d, c])).word ++ v)) :
    evalB K N dnScal s v ha hb (upLin RD K μ (CL.relationR K Q rr (.slideRNe c d hcd))) = 0 := by
  have ha' : WOK N s (⟨up c, sh RD (up d) + μ⟩ :: ⟨up d, μ⟩ :: v) := ha
  have hb' : WOK N s (⟨up d, sh RD (up c) + μ⟩ :: ⟨up c, μ⟩ :: v) := hb
  simp only [CL.relationR, KLR.Diagram.relation]
  rw [upLin_sub, map_sub]
  erw [evalB_up_comp dnScal μ (KLR.Diagram.D0 c d) (KLR.Diagram.X2 c d) s v ha ha hb,
    evalB_up_comp dnScal μ (KLR.Diagram.X2 c d) (KLR.Diagram.D1 d c) s v ha hb hb,
    evalB_D0 dnScal c d μ s v ha', evalB_X2 dnScal c d μ s v ha' hb',
    evalB_D1 dnScal d c μ s v hb']
  have h := (crossU_rules c d ha'.st₁ ha'.st₂ hb'.st₁ hb'.st₂).locL (gammaR K N μ v ha'.sf₂)
  rw [tauU_of_ne hcd, locTwo_zero] at h
  rw [h]
  rw [zero_add, sub_self]

/-! ### The double crossings -/

/-- **`Γ_N` respects `ψ² = 0` on `E_c E_c`** (`sqEq`). -/
theorem evalB_klr_sqEq (Q : Fin m → Fin m → MvPolynomial (Fin 2) K) (rr : Fin m → K)
    (c : Fin m) (μ s : Wt m) (v : List (psig RD).Colour)
    (ha hb : WOK N s ((ob RD μ (ups [c, c])).word ++ v)) :
    evalB K N dnScal s v ha hb (upLin RD K μ (CL.relationR K Q rr (.sqEq c))) = 0 := by
  have ha' : WOK N s (⟨up c, sh RD (up c) + μ⟩ :: ⟨up c, μ⟩ :: v) := ha
  simp only [CL.relationR, KLR.Diagram.relation]
  erw [evalB_up_comp dnScal μ (KLR.Diagram.X2 c c) (KLR.Diagram.X2 c c) s v ha ha hb,
    evalB_X2 dnScal c c μ s v ha' ha', ← locTwo_comp, crossU_self_sq, locTwo_zero]

/-- The middle object `E_d E_c 1_μ` of the double crossing is valid as soon as the second strand
of `E_c` can be moved to the right region of `E_d`. -/
theorem wok_swap {c d : Fin m} {μ s : Wt m} {v : List (psig RD).Colour}
    (ha : WOK N s (⟨up c, sh RD (up d) + μ⟩ :: ⟨up d, μ⟩ :: v)) {r₁' : Comp m}
    (h : StepR (true, c) (compOf N μ) r₁') :
    WOK N s (⟨up d, sh RD (up c) + μ⟩ :: ⟨up c, μ⟩ :: v) :=
  ⟨ha.1, by rw [← ha.2.1]; exact add_left_comm _ _ _,
    (realized_of_stepR_up ha.sf₂.realized c h).1, rfl, ha.sf₂⟩

/-- **`Γ_N` respects `ψ_{dc} ψ_{cd} = Q_{cd}(x₀, x₁)`** (`sqNe`) for `Q_{cd} = Q^τ_{cd}`. -/
theorem evalB_klr_sqNe (Q : Fin m → Fin m → MvPolynomial (Fin 2) K) (rr : Fin m → K)
    (c d : Fin m) (hcd : c ≠ d) (hQ : Q c d = Signed.qSigned K m c d) (μ s : Wt m)
    (v : List (psig RD).Colour) (ha hb : WOK N s ((ob RD μ (ups [c, d])).word ++ v)) :
    evalB K N dnScal s v ha hb (upLin RD K μ (CL.relationR K Q rr (.sqNe c d hcd))) = 0 := by
  have ha' : WOK N s (⟨up c, sh RD (up d) + μ⟩ :: ⟨up d, μ⟩ :: v) := ha
  simp only [CL.relationR, KLR.Diagram.relation]
  rw [upLin_sub, map_sub, hQ]
  -- the polynomial side
  have hpoly := evalB_upLin_lpoly (N := N) dnScal μ (a := KLR.Diagram.ob [c, d]) s v ha
    ![KLR.Diagram.D0 c d, KLR.Diagram.D1 c d]
    ![BRing.tmul (stepB K _ _ _ ha'.st₁)
        ((stepB K _ _ _ ha'.st₂).tensor (gammaR K N μ v ha'.sf₂)) (eXi K c _ ha'.st₁.2) 1,
      BRing.tmul (stepB K _ _ _ ha'.st₁)
        ((stepB K _ _ _ ha'.st₂).tensor (gammaR K N μ v ha'.sf₂)) 1
        (BRing.tmul (stepB K _ _ _ ha'.st₂) (gammaR K N μ v ha'.sf₂) (eXi K d _ ha'.st₂.2) 1)]
    (fun i => by
      fin_cases i
      · rw [← upLin_of]; exact evalB_D0 dnScal c d μ s v ha'
      · rw [← upLin_of]; exact evalB_D1 dnScal c d μ s v ha')
    (Signed.qSigned K m c d)
  erw [hpoly]
  rw [← gammaR_right_eq]
  have htr := locTwo_mulB_eval₂ (K := K) (L := stepB K _ _ _ ha'.st₁) (L' := stepB K _ _ _ ha'.st₂)
    (eXi K c _ ha'.st₁.2) (eXi K d _ ha'.st₂.2) (gammaR K N μ v ha'.sf₂) (Signed.qSigned K m c d)
  by_cases hm : WOK N s ((ob RD μ (ups [d, c])).word ++ v)
  · have hm' : WOK N s (⟨up d, sh RD (up c) + μ⟩ :: ⟨up c, μ⟩ :: v) := hm
    erw [evalB_up_comp dnScal μ (KLR.Diagram.X2 c d) (KLR.Diagram.X2 d c) s v ha hm hb,
      evalB_X2 dnScal c d μ s v ha' hm', evalB_X2 dnScal d c μ s v hm' ha', ← locTwo_comp,
      crossU_eq_gammaCross hcd, crossU_eq_gammaCross (Ne.symm hcd), Signed.gammaCross_sq]
    erw [htr]
    exact sub_self _
  · erw [evalB_up_comp_zero dnScal μ (KLR.Diagram.X2 c d) (KLR.Diagram.X2 d c) s v ha hm hb]
    rw [zero_sub, neg_eq_zero]
    rcases Signed.swap_cases c d ha'.st₁ ha'.st₂ with ⟨r₁', -, h₂'⟩ | ⟨hadj, hdeg⟩
    · exact absurd (wok_swap ha' h₂') hm
    · have h0 := Signed.degen_qSigned_eq_zero (K := K) ha'.st₁ ha'.st₂ hadj hdeg
      erw [← htr]
      rw [Signed.scal] at h0
      rw [h0, BHom.mulB_zero'', locTwo_zero]

end Categorification.Flag

end

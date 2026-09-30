/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.GammaIndepPath
import Categorification.Flag.GammaThree
import Categorification.Flag.GammaTarget

/-!
# The polynomial shadow of `Γ_N` on upward strands

Khovanov–Lauda III (arXiv:0807.3250v1), §6.4 (TeX `sln-2008-ArXiv.tex` l. 9598–9790): "it is
clear that the action on `Pol_ν(ξ)` given by the 2-functor `Γ^G` coincides with the action of
`R(ν)` on `Pol_ν` defined in [KL]", and "`f_D` fixes all other generators of `Γ^G(E_ν 1_λ)`".

For a path `W` of upward strands we consider the elements `evXi q * iotaE z` of `Γ_N(E_W 1_μ)`:
a polynomial `q` in the dots of the strands times an element `z` of the cohomology ring `H_μ` of
the rightmost region. A bimodule map `φ` has **polynomial shadow** `op` (`Shadow`) if it sends
`evXi q * iotaE z` to `evXi (op q) * iotaE z`.

* `shadow_dotLayer`: `Γ_N` of a dot on the `a`-th strand has shadow `q ↦ x_a q`;
* `shadow_crossLayer`: `Γ_N` of an upward crossing of the strands `a`, `a + 1`, coloured `c`
  (left) and `d` (right), has shadow `opCross c d a`: the divided difference `∂_{a,a+1}` if
  `c = d`, and `q ↦ F_{cd}(x_a, x_{a+1}) · s_a q` otherwise, with `F_{cd} = x_{a+1} - x_a` if
  `c = d + 1` and `F_{cd} = 1` otherwise (`Categorification.Flag.Fc`). These are the operators of
  the polynomial representation of KL I §2.3 (`Categorification.KLR.PolyRep.crossComp`) with
  `P = Fc`, i.e. of the KLR algebra with the polynomials `Q_{cd} = Qf c d` (KL III (6.8)).

The proofs combine the dot slides of `Γ_N` of the crossing (`crossU_rules`), its values at `1`
(`crossU_one`, `tauU_one`) and the twisted Leibniz rule (`Categorification.Flag.eval_twisted`).
-/

noncomputable section

namespace Categorification.Flag.Indep

open Categorification.Flag Categorification.KL3.Diagram StringDiagrams MvPolynomial

universe u

variable {K : Type u} [Field K] {m N : ℕ}

local notation "RD" => slRootDatum m

/-! ## The rightmost region -/

/-- The inclusion `H_μ → Γ_N(E_W 1_μ)` of the rightmost factor, for a fixed rightmost region
`μ`. -/
def iotaE (s : Wt m) (W : List (WCol m)) (h : WOK N s W) (μ : Wt m) (e : lastR s W = μ) :
    H K (compOf N μ) →+* (gammaR K N s W h).T :=
  (iotaR s W h).comp (hCast K (congrArg (compOf N) e.symm)).toRingHom

theorem iotaE_cons (s : Wt m) (col : WCol m) (W : List (WCol m)) (h : WOK N s (col :: W))
    (μ : Wt m) (e : lastR s (col :: W) = μ) (z : H K (compOf N μ)) :
    iotaE s (col :: W) h μ e z = BRing.tmul _ _ 1 (iotaE (K := K) col.r W h.tail μ e z) := rfl

theorem evXi_X (s : Wt m) (W : List (WCol m)) (h : WOK N s W) (t : ℕ) :
    evXi (K := K) s W h (X t) = xiAt s W h t := eval₂Hom_X' _ _ t

theorem evXi_C (s : Wt m) (W : List (WCol m)) (h : WOK N s W) (a : K) :
    evXi (K := K) s W h (C a) = (gammaR K N s W h).right a := eval₂Hom_C _ _ a

theorem xiAt_cons_zero (s : Wt m) (col : WCol m) (W : List (WCol m)) (h : WOK N s (col :: W)) :
    xiAt (K := K) s (col :: W) h 0 =
      BRing.tmul _ _ (xiStep K col.l (compOf N col.r) (compOf N s) h.step) 1 := rfl

theorem xiStep_up (i : Fin m) (r s : Comp m) (h : StepR (true, i) r s) :
    xiStep K (true, i) r s h = eXi K i r h.2 := rfl

theorem layerMap_cons (s : Wt m) (col : WCol m) (left : List (WCol m)) (g : (psig RD).Gen)
    (right : List (WCol m)) (hd : WOK N s (col :: left ++ gdom g ++ right))
    (hc : WOK N s (col :: left ++ gcod g ++ right)) :
    layerMap K N s (col :: left) g right hd hc =
      BHom.whiskerLeft (stepB K col.l (compOf N col.r) (compOf N s) hd.step)
        (layerMap K N col.r left g right hd.tail hc.tail) := rfl

theorem xiAt_cons_succ (s : Wt m) (col : WCol m) (W : List (WCol m)) (h : WOK N s (col :: W))
    (t : ℕ) : xiAt (K := K) s (col :: W) h (t + 1) = BRing.tmul _ _ 1 (xiAt col.r W h.tail t) := rfl

/-! ## Shadows -/

/-- `φ` has **polynomial shadow** `op`: it sends `evXi q * iotaE z` to `evXi (op q) * iotaE z`. -/
def Shadow {s : Wt m} {W W' : List (WCol m)} {h : WOK N s W} {h' : WOK N s W'} (μ : Wt m)
    (e : lastR s W = μ) (e' : lastR s W' = μ) (φ : BHom (gammaR K N s W h) (gammaR K N s W' h'))
    (op : MvPolynomial ℕ K → MvPolynomial ℕ K) : Prop :=
  ∀ q z, φ (evXi s W h q * iotaE s W h μ e z) = evXi s W' h' (op q) * iotaE s W' h' μ e' z

theorem Shadow.comp {s : Wt m} {W W' W'' : List (WCol m)} {h : WOK N s W} {h' : WOK N s W'}
    {h'' : WOK N s W''} {μ : Wt m} {e : lastR s W = μ} {e' : lastR s W' = μ}
    {e'' : lastR s W'' = μ} {φ : BHom (gammaR K N s W h) (gammaR K N s W' h')}
    {ψ : BHom (gammaR K N s W' h') (gammaR K N s W'' h'')} {op op' : MvPolynomial ℕ K → MvPolynomial ℕ K}
    (hφ : Shadow μ e e' φ op) (hψ : Shadow μ e' e'' ψ op') :
    Shadow μ e e'' (ψ.comp φ) (op' ∘ op) := fun q z => by
  rw [BHom.comp_apply, hφ, hψ]; rfl

theorem Shadow.csmul {s : Wt m} {W W' : List (WCol m)} {h : WOK N s W} {h' : WOK N s W'}
    {μ : Wt m} {e : lastR s W = μ} {e' : lastR s W' = μ}
    {φ : BHom (gammaR K N s W h) (gammaR K N s W' h')} {op : MvPolynomial ℕ K → MvPolynomial ℕ K}
    (hφ : Shadow μ e e' φ op) (a : K) :
    Shadow μ e e' (BHom.csmul a φ) (fun q => C a * op q) := fun q z => by
  show (gammaR K N s W' h').right a * φ _ = _
  rw [hφ, map_mul, evXi, eval₂Hom_C, ← evXi, mul_assoc]

theorem shadow_trW {s : Wt m} {W W' : List (WCol m)} (eW : W = W') (h : WOK N s W)
    (h' : WOK N s W') {μ : Wt m} (e : lastR s W = μ) (e' : lastR s W' = μ) :
    Shadow μ e e' (trW (K := K) s eW h h') id := by
  subst eW; intro q z; rfl

/-! ## Dots -/

set_option backward.isDefEq.respectTransparency false in
theorem layerMap_dot (col : WCol m) : ∀ (s : Wt m) (left right : List (WCol m))
    (hd : WOK N s (left ++ gdom (.gen (.dot col)) ++ right))
    (hc : WOK N s (left ++ gcod (.gen (.dot col)) ++ right)) (y : (gammaR K N s _ hd).T),
    layerMap K N s left (.gen (.dot col)) right hd hc y = xiAt s _ hd left.length * y
  | s, [], right, hd, hc, y => by
    show locOne (BHom.mulB _) _ y = _
    rw [locOne, BHom.whiskerRight_mulB, BHom.mulB_apply]
    rfl
  | s, c :: left, right, hd, hc, y => by
    show BHom.whiskerLeft _ (layerMap K N c.r left (.gen (.dot col)) right hd.tail hc.tail) y = _
    have ih : layerMap K N c.r left (.gen (.dot col)) right hd.tail hc.tail =
        BHom.mulB (xiAt c.r _ hd.tail left.length) :=
      BHom.ext fun z => layerMap_dot col c.r left right hd.tail hc.tail z
    rw [ih, BHom.whiskerLeft_mulB, BHom.mulB_apply]
    rfl

/-- **`Γ_N` of a dot on the `a`-th strand** has shadow `q ↦ x_a q`. -/
theorem shadow_dotLayer (s : Wt m) (col : WCol m) (left right : List (WCol m))
    (hd : WOK N s (left ++ gdom (.gen (.dot col)) ++ right))
    (hc : WOK N s (left ++ gcod (.gen (.dot col)) ++ right)) {μ : Wt m}
    (e : lastR s (left ++ gdom (.gen (.dot col)) ++ right) = μ)
    (e' : lastR s (left ++ gcod (.gen (.dot col)) ++ right) = μ) :
    Shadow μ e e' (layerMap K N s left (.gen (.dot col)) right hd hc)
      (fun q => X left.length * q) := fun q z => by
  rw [layerMap_dot, map_mul, mul_assoc]
  congr 1
  simp only [evXi, eval₂Hom_X']
  rfl

/-! ## Crossings: the rules -/

section Rules

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]

/-- A dot-slide rule whiskered on the left. -/
theorem whiskerLeft_rule (M : BRing A B) {P P' : BRing B C} (ψ χ ρ : BHom P P') (w : P.T)
    (w' : P'.T) (h : ∀ z, ψ (w * z) = χ z + w' * ρ z) (y : (M.tensor P).T) :
    BHom.whiskerLeft M ψ (BRing.tmul M P 1 w * y) =
      BHom.whiskerLeft M χ y + BRing.tmul M P' 1 w' * BHom.whiskerLeft M ρ y := by
  refine BRing.induction_on (P := fun y => BHom.whiskerLeft M ψ (BRing.tmul M P 1 w * y) =
      BHom.whiskerLeft M χ y + BRing.tmul M P' 1 w' * BHom.whiskerLeft M ρ y) y (by simp)
    (fun a b => ?_) (fun y y' hy hy' => ?_)
  · rw [BRing.tmul_mul_tmul, one_mul, BHom.whiskerLeft_tmul, BHom.whiskerLeft_tmul,
      BHom.whiskerLeft_tmul, h, BRing.tmul_add, BRing.tmul_mul_tmul, one_mul]
  · beta_reduce at hy hy' ⊢
    rw [mul_add, BHom.map_add, hy, hy', BHom.map_add, BHom.map_add, mul_add]; abel

/-- The same with the correction on the other side. -/
theorem whiskerLeft_rule' (M : BRing A B) {P P' : BRing B C} (ψ χ ρ : BHom P P') (w : P.T)
    (w' : P'.T) (h : ∀ z, ψ (w * z) = w' * ρ z - χ z) (y : (M.tensor P).T) :
    BHom.whiskerLeft M ψ (BRing.tmul M P 1 w * y) =
      BRing.tmul M P' 1 w' * BHom.whiskerLeft M ρ y - BHom.whiskerLeft M χ y := by
  have h' : ∀ z, ψ (w * z) = (-χ) z + w' * ρ z := fun z => by
    rw [h, BHom.neg_apply]; abel
  rw [whiskerLeft_rule M ψ (-χ) ρ w w' h' y, BHom.whiskerLeft_neg, BHom.neg_apply]; abel

end Rules

/-- The dot-slide rules and the values at `1` of `Γ_N` of an upward crossing of the strands `a`,
`a + 1` (colours `c`, `d`) together with its correction `τ`. -/
structure CrossRules {s : Wt m} {W W' : List (WCol m)} {h : WOK N s W} {h' : WOK N s W'}
    (μ : Wt m) (e : lastR s W = μ) (e' : lastR s W' = μ)
    (φ τ : BHom (gammaR K N s W h) (gammaR K N s W' h')) (a : ℕ) (c d : Fin m) : Prop where
  τX : ∀ t y, τ (xiAt s W h t * y) = xiAt s W' h' t * τ y
  φa : ∀ y, φ (xiAt s W h a * y) = τ y + xiAt s W' h' (a + 1) * φ y
  φb : ∀ y, φ (xiAt s W h (a + 1) * y) = xiAt s W' h' a * φ y - τ y
  φo : ∀ t, t ≠ a → t ≠ a + 1 → ∀ y, φ (xiAt s W h t * y) = xiAt s W' h' t * φ y
  φι : ∀ z y, φ (iotaE s W h μ e z * y) = iotaE s W' h' μ e' z * φ y
  τι : ∀ z y, τ (iotaE s W h μ e z * y) = iotaE s W' h' μ e' z * τ y
  φ1 : φ 1 = if c = d then 0 else if c.castSucc = d.succ then
    xiAt s W' h' (a + 1) - xiAt s W' h' a else 1
  τ1 : τ 1 = if c = d then 1 else 0

/-- `Γ_N`'s correction term `τ` of an upward crossing, whiskered like `layerMap`. -/
def tauLayer (c d : Fin m) (ν : Wt m) : (s : Wt m) → (left right : List (WCol m)) →
    (hd : WOK N s (left ++ gdom (.gen (.cross true c d ν)) ++ right)) →
    (hc : WOK N s (left ++ gcod (.gen (.cross true c d ν)) ++ right)) →
    BHom (gammaR K N s _ hd) (gammaR K N s _ hc)
  | _, [], right, hd, hc =>
    locTwo (tauU K c d hd.step hd.tail.step hc.step hc.tail.step) (gammaR K N ν right hd.tail.tail)
  | s, col :: left, right, hd, hc =>
    BHom.whiskerLeft (stepB K col.l (compOf N col.r) (compOf N s) hd.step)
      (tauLayer c d ν col.r left right hd.tail hc.tail)

theorem tauLayer_cons (c d : Fin m) (ν s : Wt m) (col : WCol m) (left right : List (WCol m))
    (hd : WOK N s (col :: left ++ gdom (.gen (.cross true c d ν)) ++ right))
    (hc : WOK N s (col :: left ++ gcod (.gen (.cross true c d ν)) ++ right)) :
    tauLayer (K := K) c d ν s (col :: left) right hd hc =
      BHom.whiskerLeft (stepB K col.l (compOf N col.r) (compOf N s) hd.step)
        (tauLayer c d ν col.r left right hd.tail hc.tail) := rfl

theorem layerMap_nil_cross (c d : Fin m) (ν s : Wt m) (right : List (WCol m))
    (hd : WOK N s ([] ++ gdom (.gen (.cross true c d ν)) ++ right))
    (hc : WOK N s ([] ++ gcod (.gen (.cross true c d ν)) ++ right)) :
    layerMap K N s [] (.gen (.cross true c d ν)) right hd hc =
      locTwo (crossU K c d hd.step hd.tail.step hc.step hc.tail.step)
        (gammaR K N ν right hd.tail.tail) := rfl

theorem tauLayer_nil (c d : Fin m) (ν s : Wt m) (right : List (WCol m))
    (hd : WOK N s ([] ++ gdom (.gen (.cross true c d ν)) ++ right))
    (hc : WOK N s ([] ++ gcod (.gen (.cross true c d ν)) ++ right)) :
    tauLayer (K := K) c d ν s [] right hd hc =
      locTwo (tauU K c d hd.step hd.tail.step hc.step hc.tail.step)
        (gammaR K N ν right hd.tail.tail) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem crossRules_base (c d : Fin m) (ν s : Wt m) (right : List (WCol m))
    (hd : WOK N s ([] ++ gdom (.gen (.cross true c d ν)) ++ right))
    (hc : WOK N s ([] ++ gcod (.gen (.cross true c d ν)) ++ right)) {μ : Wt m}
    (e : lastR s ([] ++ gdom (.gen (.cross true c d ν)) ++ right) = μ)
    (e' : lastR s ([] ++ gcod (.gen (.cross true c d ν)) ++ right) = μ) :
    CrossRules (K := K) μ e e' (layerMap K N s [] (.gen (.cross true c d ν)) right hd hc)
      (tauLayer c d ν s [] right hd hc) 0 c d := by
  have hr := crossU_rules (K := K) c d hd.step hd.tail.step hc.step hc.tail.step
  rw [layerMap_nil_cross, tauLayer_nil]
  refine ⟨fun t y => ?_, fun y => ?_, fun y => ?_, fun t h0 h1 y => ?_, fun z y => ?_,
    fun z y => ?_, ?_, ?_⟩
  · rcases t with _ | _ | t
    · exact BHom.congr_apply (hr.locτL _) y
    · exact BHom.congr_apply (hr.locτR _) y
    · rw [mul_comm, mul_comm (xiAt s _ hc (t + 2))]
      exact locTwo_mul_suffix _ _ y (xiAt ν right hd.tail.tail t)
  · exact BHom.congr_apply (hr.locL _) y
  · exact BHom.congr_apply (hr.locR _) y
  · rcases t with _ | _ | t
    · exact absurd rfl h0
    · exact absurd rfl h1
    · rw [mul_comm, mul_comm (xiAt s _ hc (t + 2))]
      exact locTwo_mul_suffix _ _ y (xiAt ν right hd.tail.tail t)
  · rw [mul_comm, mul_comm (iotaE s _ hc μ e' z)]
    exact locTwo_mul_suffix _ _ y (iotaE ν right hd.tail.tail μ e z)
  · rw [mul_comm, mul_comm (iotaE s _ hc μ e' z)]
    exact locTwo_mul_suffix _ _ y (iotaE ν right hd.tail.tail μ e z)
  · rw [locTwo_one, crossU_one, BRing.assoc_hom_apply]
    by_cases hcd : c = d
    · simp only [ite_eq_left hcd, BRing.zero_tmul, map_zero]
    · simp only [ite_eq_right hcd]
      by_cases hadj : c.castSucc = d.succ
      · simp only [ite_eq_left hadj]
        rw [BRing.sub_tmul, map_sub, BRing.assocHom_tmul, BRing.assocHom_tmul, ← BRing.one_eq]
        rfl
      · simp only [ite_eq_right hadj]
        rw [← BRing.one_eq, map_one]
  · rw [locTwo_one, tauU_one, BRing.assoc_hom_apply]
    by_cases hcd : c = d
    · simp only [ite_eq_left hcd]
      rw [← BRing.one_eq, map_one]
    · simp only [ite_eq_right hcd, BRing.zero_tmul, map_zero]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
theorem crossRules_cons (c d : Fin m) (ν s : Wt m) (col : WCol m) (left right : List (WCol m))
    (hd : WOK N s (col :: left ++ gdom (.gen (.cross true c d ν)) ++ right))
    (hc : WOK N s (col :: left ++ gcod (.gen (.cross true c d ν)) ++ right)) {μ : Wt m}
    (e : lastR s (col :: left ++ gdom (.gen (.cross true c d ν)) ++ right) = μ)
    (e' : lastR s (col :: left ++ gcod (.gen (.cross true c d ν)) ++ right) = μ) (a : ℕ)
    (e₀ : lastR col.r (left ++ gdom (.gen (.cross true c d ν)) ++ right) = μ)
    (e₀' : lastR col.r (left ++ gcod (.gen (.cross true c d ν)) ++ right) = μ)
    (ih : CrossRules (K := K) μ e₀ e₀' (layerMap K N col.r left (.gen (.cross true c d ν)) right
      hd.tail hc.tail) (tauLayer c d ν col.r left right hd.tail hc.tail) a c d) :
    CrossRules (K := K) μ e e' (layerMap K N s (col :: left) (.gen (.cross true c d ν)) right hd hc)
      (tauLayer c d ν s (col :: left) right hd hc) (a + 1) c d := by
  rw [layerMap_cons, tauLayer_cons]
  set M := stepB K col.l (compOf N col.r) (compOf N s) hd.step
  set φ := layerMap K N col.r left (.gen (.cross true c d ν)) right hd.tail hc.tail
  set τ := tauLayer (K := K) c d ν col.r left right hd.tail hc.tail
  have left0 : ∀ (F : BHom (gammaR K N col.r _ hd.tail) (gammaR K N col.r _ hc.tail)) y,
      BHom.whiskerLeft M F (xiAt s _ hd 0 * y) = xiAt s _ hc 0 * BHom.whiskerLeft M F y :=
    fun F y => whiskerLeft_mul_left M F y _
  refine ⟨fun t y => ?_, fun y => ?_, fun y => ?_, fun t h0 h1 y => ?_, fun z y => ?_,
    fun z y => ?_, ?_, ?_⟩
  · rcases t with _ | t
    · exact left0 τ y
    · exact whiskerLeft_mul_right M τ _ _ (ih.τX t) y
  · exact whiskerLeft_rule M φ τ φ _ _ ih.φa y
  · exact whiskerLeft_rule' M φ τ φ _ _ ih.φb y
  · rcases t with _ | t
    · exact left0 φ y
    · exact whiskerLeft_mul_right M φ _ _ (ih.φo t (by omega) (by omega)) y
  · exact whiskerLeft_mul_right M φ _ _ (ih.φι z) y
  · exact whiskerLeft_mul_right M τ _ _ (ih.τι z) y
  · rw [whiskerLeft_one', ih.φ1]
    by_cases hcd : c = d
    · simp only [ite_eq_left hcd, BRing.tmul_zero]
    · simp only [ite_eq_right hcd]
      by_cases hadj : c.castSucc = d.succ
      · simp only [ite_eq_left hadj]
        rw [BRing.tmul_sub]; rfl
      · simp only [ite_eq_right hadj]
        exact BRing.one_eq.symm
  · rw [whiskerLeft_one', ih.τ1]
    by_cases hcd : c = d
    · simp only [ite_eq_left hcd]; exact BRing.one_eq.symm
    · simp only [ite_eq_right hcd, BRing.tmul_zero]

theorem crossRules_layer (c d : Fin m) (ν : Wt m) : ∀ (s : Wt m) (left right : List (WCol m))
    (hd : WOK N s (left ++ gdom (.gen (.cross true c d ν)) ++ right))
    (hc : WOK N s (left ++ gcod (.gen (.cross true c d ν)) ++ right)) {μ : Wt m}
    (e : lastR s (left ++ gdom (.gen (.cross true c d ν)) ++ right) = μ)
    (e' : lastR s (left ++ gcod (.gen (.cross true c d ν)) ++ right) = μ),
    CrossRules (K := K) μ e e' (layerMap K N s left (.gen (.cross true c d ν)) right hd hc)
      (tauLayer c d ν s left right hd hc) left.length c d
  | s, [], right, hd, hc, _, e, e' => crossRules_base c d ν s right hd hc e e'
  | s, col :: left, right, hd, hc, _, e, e' =>
    crossRules_cons c d ν s col left right hd hc e e' left.length e e'
      (crossRules_layer c d ν col.r left right hd.tail hc.tail e e')

/-! ## Crossings: the shadow -/

/-- The polynomial shadow of `Γ_N` of an upward crossing of the strands `a`, `a + 1` coloured
`c`, `d` (KL III (6.8); the operators of KL I §2.3 with `P = Fc`). -/
def opCross (c d : Fin m) (a : ℕ) (q : MvPolynomial ℕ K) : MvPolynomial ℕ K :=
  if c = d then ddiff a (a + 1) q
  else rename ![a, a + 1] (Fc K c d) * rename (Equiv.swap a (a + 1)) q

/-- From the rules to the shadow (twisted Leibniz rule). -/
theorem CrossRules.shadow {s : Wt m} {W W' : List (WCol m)} {h : WOK N s W} {h' : WOK N s W'}
    {μ : Wt m} {e : lastR s W = μ} {e' : lastR s W' = μ}
    {φ τ : BHom (gammaR K N s W h) (gammaR K N s W' h')} {a : ℕ} {c d : Fin m}
    (hr : CrossRules μ e e' φ τ a c d) : Shadow μ e e' φ (opCross c d a) := by
  intro q z
  have ev_X : ∀ t, evXi s W h (X t) = xiAt s W h t := evXi_X (K := K) s W h
  have ev_X' : ∀ t, evXi s W' h' (X t) = xiAt s W' h' t := evXi_X (K := K) s W' h'
  have key := eval_twisted (evXi s W h) (evXi s W' h') φ τ a (a + 1) (by omega) φ.map_add
    (fun t y => by rw [ev_X, ev_X']; exact hr.τX t y)
    (fun b y => by
      rw [evXi_C, evXi_C]; exact φ.map_right b y)
    (fun y => by rw [ev_X, ev_X']; exact hr.φa y)
    (fun y => by rw [ev_X, ev_X']; exact hr.φb y)
    (fun t h0 h1 y => by rw [ev_X, ev_X']; exact hr.φo t h0 h1 y) q (iotaE s W h μ e z)
  rw [key]
  have hτz : τ (iotaE s W h μ e z) = iotaE s W' h' μ e' z * τ 1 := by
    rw [← hr.τι z 1, mul_one]
  have hφz : φ (iotaE s W h μ e z) = iotaE s W' h' μ e' z * φ 1 := by
    rw [← hr.φι z 1, mul_one]
  rw [hτz, hφz, hr.τ1, hr.φ1, opCross]
  by_cases hcd : c = d
  · simp [hcd]
  · simp only [ite_eq_right hcd, mul_zero, zero_add, map_mul]
    have hF : evXi s W' h' (rename ![a, a + 1] (Fc K c d)) =
        if c.castSucc = d.succ then xiAt s W' h' (a + 1) - xiAt s W' h' a else 1 := by
      rw [Fc]
      split_ifs <;> simp [ev_X']
    rw [hF]
    ring

/-- **`Γ_N` of an upward crossing of the strands `a`, `a + 1`** (colours `c`, `d`) has shadow
`opCross c d a`. -/
theorem shadow_crossLayer (c d : Fin m) (ν s : Wt m) (left right : List (WCol m))
    (hd : WOK N s (left ++ gdom (.gen (.cross true c d ν)) ++ right))
    (hc : WOK N s (left ++ gcod (.gen (.cross true c d ν)) ++ right)) {μ : Wt m}
    (e : lastR s (left ++ gdom (.gen (.cross true c d ν)) ++ right) = μ)
    (e' : lastR s (left ++ gcod (.gen (.cross true c d ν)) ++ right) = μ) :
    Shadow μ e e' (layerMap K N s left (.gen (.cross true c d ν)) right hd hc)
      (opCross c d left.length) :=
  (crossRules_layer c d ν s left right hd hc e e').shadow

end Categorification.Flag.Indep

end

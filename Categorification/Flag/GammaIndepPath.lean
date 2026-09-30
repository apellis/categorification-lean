/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.GammaIndepERing
import Categorification.Flag.GammaObjects

/-!
# Ring maps out of the path bimodules of upward words

Khovanov–Lauda III (arXiv:0807.3250v1), §6.4 (TeX `sln-2008-ArXiv.tex` l. 9598–9790): "For large
enough `N`, the bimodule `Γ^G(E_ν 1_λ)` contains `Pol_ν(ξ)` as a subspace", and the bubbles act
on "algebraically independent generators" of the cohomology ring of the rightmost region.

For an upward word `w = E_{i_1} ⋯ E_{i_r}` with rightmost region `λ`, the path bimodule
`Γ_N(E_w 1_λ) = H_{…^{+i_1}} ⊗ ⋯ ⊗ H_{λ^{+i_r}} ⊗ H_λ` (`Categorification.Flag.gammaR`) is a
commutative ring. We construct ring maps out of it into a truncated polynomial ring `Tr`
(`Categorification.Flag.Indep.Tr`), which make the phrase "contains `Pol_ν(ξ)`" precise in
bounded degree:

* `evR`: given elements `Ξ_1, …, Ξ_r ∈ Tr` of weight `1` (the Chern roots of the strands) and
  total Chern classes `c` of the rightmost region `λ` (`GoodData`), and provided every block of
  every region of the path is larger than the truncation degree `D` (`PathHyp`), the ring map
  `Γ_N(E_w 1_λ) → Tr` sending the dot `ξ_t` of the `t`-th strand to `Ξ_t` (`evR_xiAt`) and the
  cohomology ring `H_λ` of the rightmost region to `Tr` by the total Chern classes `c`
  (`evR_iotaR`). The total Chern classes of the other regions are determined by KL III (5.15),
  (5.16) (`wData`, `upData`).
* `xiAt s w h t` is the dot of the `t`-th strand, and `iotaR s w h : H_λ → Γ_N(E_w 1_λ)` the
  inclusion of the last tensor factor (the action of the region `λ`, on which bubbles on the far
  right act).
-/

noncomputable section

namespace Categorification.Flag.Indep

open Categorification.Flag Categorification.KL3.Diagram StringDiagrams

universe u

variable {K : Type u} [Field K] {m : ℕ} {σ : Type} {w : σ → ℕ} {D N : ℕ}

/-! ## Hypotheses -/

variable (K w D) in
/-- `Ξ` is a Chern root: homogeneous of weight `1`. -/
def GoodXi (Ξ : Tr K w D) : Prop := sc K w D Ξ = Polynomial.C Ξ * Polynomial.X ∧ aug K w D Ξ = 0

variable (K w D) in
/-- Total Chern classes: augmentation `1` and product `1`. -/
def GoodData (c : Fin (m + 1) → Tr K w D) : Prop :=
  (∀ j, (sc K w D (c j)).coeff 0 = 1) ∧ ∏ j, c j = 1

/-- The total Chern classes of the leftmost region of a path, from those `c` of the rightmost
region and the Chern roots `Ξs` of the strands (KL III (5.15), (5.16), `upData`). -/
def wData : List (WCol m) → List (Tr K w D) → (Fin (m + 1) → Tr K w D) → Fin (m + 1) → Tr K w D
  | col :: ws, Ξ :: Ξs, c => upData col.l.2 Ξ (wData ws Ξs c)
  | _, _, c => c

variable (N) in
/-- The hypotheses of `evR`: all strands are upward, one Chern root per strand, total Chern
classes on the right, and every block of every region larger than the truncation degree. -/
def PathHyp : Wt m → List (WCol m) → List (Tr K w D) → (Fin (m + 1) → Tr K w D) → Prop
  | s, [], [], c => GoodData K w D c ∧ ∀ j, D < compOf N s j
  | s, col :: ws, Ξ :: Ξs, c =>
      col.l.1 = true ∧ GoodXi K w D Ξ ∧ (∀ j, D < compOf N s j) ∧ PathHyp col.r ws Ξs c
  | _, _, _, _ => False

theorem PathHyp.blocks : {s : Wt m} → {ws : List (WCol m)} → {Ξs : List (Tr K w D)} →
    {c : Fin (m + 1) → Tr K w D} → PathHyp N s ws Ξs c → ∀ j, D < compOf N s j
  | _, [], [], _, hp => hp.2
  | _, _ :: _, _ :: _, _, hp => hp.2.2.1

theorem PathHyp.good (hw : ∀ v, 0 < w v) : {s : Wt m} → {ws : List (WCol m)} →
    {Ξs : List (Tr K w D)} → {c : Fin (m + 1) → Tr K w D} → PathHyp N s ws Ξs c →
    GoodData K w D (wData ws Ξs c)
  | _, [], [], _, hp => hp.1
  | _, col :: ws, Ξ :: Ξs, c, hp => by
    have ih := PathHyp.good hw hp.2.2.2
    exact ⟨coeff_sc_upData_zero hw col.l.2 hp.2.1.2 _ ih.1,
      by show ∏ j, upData col.l.2 Ξ (wData ws Ξs c) j = 1; rw [prod_upData hw _ hp.2.1.2, ih.2]⟩

theorem PathHyp.length_eq : {s : Wt m} → {ws : List (WCol m)} → {Ξs : List (Tr K w D)} →
    {c : Fin (m + 1) → Tr K w D} → PathHyp N s ws Ξs c → Ξs.length = ws.length
  | _, [], [], _, _ => rfl
  | _, _ :: _, _ :: _, _, hp => by simp [PathHyp.length_eq hp.2.2.2]

/-! ## `hLift` along equal compositions -/

theorem hLift_hCast {n : ℕ} {d d' : Fin n → ℕ} (e : d = d') (hd : ∀ j, D ≤ d j)
    (hd' : ∀ j, D ≤ d' j) (c : Fin n → Tr K w D) (h0 : ∀ j, (sc K w D (c j)).coeff 0 = 1)
    (hp : ∏ j, c j = 1) (z : H K d) :
    hLift d' hd' c h0 hp (hCast K e z) = hLift d hd c h0 hp z := by
  subst e; rfl

/-! ## The ring maps -/

theorem stepB_up_right (i : Fin m) (r s : Comp m) (hh : StepR (true, i) r s) (b : H K r) :
    (stepB K (true, i) r s hh).right b = eRight K i r hh.2 b := rfl

theorem stepB_up_left (i : Fin m) (r s : Comp m) (hh : StepR (true, i) r s) (z : H K s) :
    (stepB K (true, i) r s hh).left z = eLeft K i r hh.2 (hCast K hh.1.symm z) := rfl

variable (hw : ∀ v, 0 < w v)

/-- The ring map on `Γ(E_i) ⊗ X`, from ring maps on the two factors. -/
def consHom (i : Fin m) (r s : Wt m) (hh : StepR (true, i) (compOf N r) (compOf N s))
    {X : BRing (H K (compOf N r)) K} (f : ERing K i (compOf N r) hh.2 →+* Tr K w D)
    (g : X.T →+* Tr K w D) (hfg : ∀ b, f (eRight K i (compOf N r) hh.2 b) = g (X.left b)) :
    ((stepB K (true, i) (compOf N r) (compOf N s) hh).tensor X).T →+* Tr K w D :=
  BRing.liftRingHom (M := stepB K (true, i) (compOf N r) (compOf N s) hh) (N := X) f g hfg

theorem consHom_tmul (i : Fin m) (r s : Wt m) (hh : StepR (true, i) (compOf N r) (compOf N s))
    {X : BRing (H K (compOf N r)) K} (f : ERing K i (compOf N r) hh.2 →+* Tr K w D)
    (g : X.T →+* Tr K w D) {hfg : ∀ b, f (eRight K i (compOf N r) hh.2 b) = g (X.left b)}
    (a : ERing K i (compOf N r) hh.2) (x : X.T) :
    consHom i r s hh f g hfg (BRing.tmul _ _ a x) = f a * g x := rfl

/-- **The ring map `Γ_N(E_w 1_λ) → Tr`** (see the module docstring), together with its
compatibility with the left action of the leftmost region. -/
def evR : (s : Wt m) → (ws : List (WCol m)) → (h : WOK N s ws) → (Ξs : List (Tr K w D)) →
    (c : Fin (m + 1) → Tr K w D) → (hp : PathHyp N s ws Ξs c) →
    {f : (gammaR K N s ws h).T →+* Tr K w D // ∀ z, f ((gammaR K N s ws h).left z) =
      hLift (compOf N s) (fun j => (hp.blocks j).le) (wData ws Ξs c) (hp.good hw).1
        (hp.good hw).2 z}
  | s, [], _, [], c, hp => ⟨(hLift (compOf N s) (fun j => (hp.blocks j).le) c hp.1.1 hp.1.2).toRingHom,
      fun _ => rfl⟩
  | s, ⟨(true, i), r⟩ :: ws, h, Ξ :: Ξs, c, hp =>
    let g := evR r ws h.tail Ξs c hp.2.2.2
    let f := liftETr hw i (compOf N r) h.step.2 (hp.2.2.2.blocks) (wData ws Ξs c)
      (hp.2.2.2.good hw).1 (hp.2.2.2.good hw).2 Ξ hp.2.1.1 hp.2.1.2
    ⟨consHom i r s h.step f g.1 (fun b => (liftETr_eRight _ _ _ _ _ _ _ _ _ _ _ b).trans (g.2 b).symm),
      fun z => by
        refine (consHom_tmul i r s h.step f g.1 _ 1).trans ?_
        rw [map_one, mul_one, stepB_up_left, liftETr_eLeft]
        exact hLift_hCast _ _ _ _ _ _ z⟩
  | _, ⟨(false, _), _⟩ :: _, _, _ :: _, _, hp => absurd hp.1 Bool.false_ne_true
  | _, [], _, _ :: _, _, hp => hp.elim
  | _, _ :: _, _, [], _, hp => hp.elim

theorem evR_cons_tmul (s : Wt m) (i : Fin m) (r : Wt m) (ws : List (WCol m))
    (h : WOK N s (⟨(true, i), r⟩ :: ws)) (Ξ : Tr K w D) (Ξs : List (Tr K w D))
    (c : Fin (m + 1) → Tr K w D) (hp : PathHyp N s (⟨(true, i), r⟩ :: ws) (Ξ :: Ξs) c)
    (a : ERing K i (compOf N r) h.step.2) (x : (gammaR K N r ws h.tail).T) :
    (evR hw s (⟨(true, i), r⟩ :: ws) h (Ξ :: Ξs) c hp).1 (BRing.tmul _ _ a x) =
      liftETr hw i (compOf N r) h.step.2 (hp.2.2.2.blocks) (wData ws Ξs c)
        (hp.2.2.2.good hw).1 (hp.2.2.2.good hw).2 Ξ hp.2.1.1 hp.2.1.2 a *
      (evR hw r ws h.tail Ξs c hp.2.2.2).1 x := by
  rw [evR]; rfl

/-- The dot of the `t`-th strand (`0` if there is no such strand). -/
def xiAt : (s : Wt m) → (ws : List (WCol m)) → (h : WOK N s ws) → ℕ → (gammaR K N s ws h).T
  | _, [], _, _ => 0
  | s, col :: _, h, 0 => BRing.tmul _ _ (xiStep K col.l (compOf N col.r) (compOf N s) h.step) 1
  | _, col :: ws, h, t + 1 => BRing.tmul _ _ 1 (xiAt col.r ws h.tail t)

/-- The rightmost region of a path. -/
def lastR : Wt m → List (WCol m) → Wt m
  | s, [] => s
  | _, col :: ws => lastR col.r ws

theorem lastR_eq_endR : ∀ (s : Wt m) (ws : List (WCol m)),
    lastR s ws = (psig (slRootDatum m)).endR s ws
  | _, [] => rfl
  | _, col :: ws => lastR_eq_endR col.r ws

/-- The inclusion `H_λ → Γ_N(E_w 1_λ)` of the last tensor factor. -/
def iotaR : (s : Wt m) → (ws : List (WCol m)) → (h : WOK N s ws) →
    H K (compOf N (lastR s ws)) →+* (gammaR K N s ws h).T
  | _, [], _ => RingHom.id _
  | _, col :: ws, h => (BRing.inclR _ _).comp (iotaR col.r ws h.tail)

set_option backward.isDefEq.respectTransparency false in
variable (N) in
/-- The value of `evR` on the dot of the `t`-th strand. -/
theorem evR_xiAt : ∀ (s : Wt m) (ws : List (WCol m)) (h : WOK N s ws) (Ξs : List (Tr K w D))
    (c : Fin (m + 1) → Tr K w D) (hp : PathHyp N s ws Ξs c) (t : ℕ),
    (evR hw s ws h Ξs c hp).1 (xiAt s ws h t) = Ξs.getD t 0
  | _, [], _, [], _, _, t => map_zero _
  | _, ⟨(true, i), r⟩ :: ws, h, Ξ :: Ξs, c, hp, 0 => by
    rw [xiAt, evR_cons_tmul, map_one, mul_one]
    exact liftETr_xi _ _ _ _ _ _ _ _ _ _ _
  | _, ⟨(true, i), r⟩ :: ws, h, Ξ :: Ξs, c, hp, t + 1 => by
    rw [xiAt, evR_cons_tmul, map_one, one_mul]
    exact evR_xiAt _ ws h.tail Ξs c hp.2.2.2 t
  | _, ⟨(false, _), _⟩ :: _, _, _ :: _, _, hp, _ => absurd hp.1 Bool.false_ne_true
  | _, [], _, _ :: _, _, hp, _ => hp.elim
  | _, _ :: _, _, [], _, hp, _ => hp.elim

set_option backward.isDefEq.respectTransparency false in
variable (N) in
/-- The value of `evR` on the rightmost region: the total Chern classes `c`. -/
theorem evR_iotaR : ∀ (s : Wt m) (ws : List (WCol m)) (h : WOK N s ws) (Ξs : List (Tr K w D))
    (c : Fin (m + 1) → Tr K w D) (hp : PathHyp N s ws Ξs c) (z : H K (compOf N (lastR s ws))),
    ∃ hd h0 hprod, (evR hw s ws h Ξs c hp).1 (iotaR s ws h z) = hLift (compOf N (lastR s ws)) hd c h0 hprod z
  | _, [], _, [], _, hp, z => ⟨fun j => (hp.2 j).le, hp.1.1, hp.1.2, rfl⟩
  | _, ⟨(true, i), r⟩ :: ws, h, Ξ :: Ξs, c, hp, z => by
    obtain ⟨hd, h0, hprod, e⟩ := evR_iotaR _ ws h.tail Ξs c hp.2.2.2 z
    refine ⟨hd, h0, hprod, ?_⟩
    rw [iotaR]
    erw [RingHom.comp_apply, BRing.inclR_apply]
    rw [evR_cons_tmul, map_one, one_mul]
    exact e
  | _, ⟨(false, _), _⟩ :: _, _, _ :: _, _, hp, _ => absurd hp.1 Bool.false_ne_true
  | _, [], _, _ :: _, _, hp, _ => hp.elim
  | _, _ :: _, _, [], _, hp, _ => hp.elim

set_option backward.isDefEq.respectTransparency false in
variable (N) in
/-- The value of `evR` on scalars (the right action of `K`). -/
theorem evR_right : ∀ (s : Wt m) (ws : List (WCol m)) (h : WOK N s ws) (Ξs : List (Tr K w D))
    (c : Fin (m + 1) → Tr K w D) (hp : PathHyp N s ws Ξs c) (a : K),
    (evR hw s ws h Ξs c hp).1 ((gammaR K N s ws h).right a) = algebraMap K _ a
  | s, [], _, [], c, hp, a => (hLift (compOf N s) (fun j => (hp.2 j).le) c hp.1.1 hp.1.2).commutes a
  | _, ⟨(true, i), r⟩ :: ws, h, Ξ :: Ξs, c, hp, a => by
    change (evR hw _ _ h _ c hp).1 (BRing.tmul _ _ 1 ((gammaR K N r ws h.tail).right a)) = _
    rw [evR_cons_tmul, map_one, one_mul]
    exact evR_right _ ws h.tail Ξs c hp.2.2.2 a
  | _, ⟨(false, _), _⟩ :: _, _, _ :: _, _, hp, _ => absurd hp.1 Bool.false_ne_true
  | _, [], _, _ :: _, _, hp, _ => hp.elim
  | _, _ :: _, _, [], _, hp, _ => hp.elim

/-! ## Polynomials in the dots -/

/-- **Polynomials in the dots**: `x_t ↦ ξ_t` (the `t`-th strand), scalars through the right
action of `K`. -/
def evXi (s : Wt m) (ws : List (WCol m)) (h : WOK N s ws) :
    MvPolynomial ℕ K →+* (gammaR K N s ws h).T :=
  MvPolynomial.eval₂Hom (gammaR K N s ws h).right (xiAt s ws h)

variable (N) in
theorem evR_evXi (s : Wt m) (ws : List (WCol m)) (h : WOK N s ws) (Ξs : List (Tr K w D))
    (c : Fin (m + 1) → Tr K w D) (hp : PathHyp N s ws Ξs c) (q : MvPolynomial ℕ K) :
    (evR hw s ws h Ξs c hp).1 (evXi s ws h q) = MvPolynomial.aeval (fun t => Ξs.getD t 0) q := by
  induction q using MvPolynomial.induction_on with
  | C a => rw [evXi, MvPolynomial.eval₂Hom_C, evR_right, MvPolynomial.aeval_C]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p t hp =>
    rw [map_mul, map_mul, hp, map_mul, MvPolynomial.aeval_X, evXi, MvPolynomial.eval₂Hom_X',
      evR_xiAt]

end Categorification.Flag.Indep

end

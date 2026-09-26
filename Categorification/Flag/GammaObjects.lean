/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.Basic
import Categorification.Flag.SlRootDatum
import Categorification.Flag.GammaWord

/-!
# The objects of the target of `Γ_N`: path bimodules of words of the presentation

KL III, arXiv:0807.3250v1, §5.2 (the 2-category `Flag_N`, Definition 5.6) and §6.1 (the
2-functor `Γ_N` on 1-morphisms, eq. (6.1)).

We fix `N` and `m` (so `n = m + 1`) and the root datum `slRootDatum m` of `sl_{m+1}`. A region of
the string-diagram presentation of `U` (`Categorification.KL3.Diagram.psig`) is a weight
`λ ∈ ℤ^m`; it is *realized* (`Realized N λ`) if it is the weight `λ(k)` of a composition `k` of
`N` into `m + 1` parts (KL III (5.18), `compWeight`), which is then unique
(`compWeight_injective`); `compOf N λ` is that composition (junk if `λ` is not realized).

An object of the presentation (a 1-morphism: a start region and a word of strands, each strand
carrying the weight of the region to its right) is *valid* (`WOK N s w`) if it is well formed and
all its regions are realized. Consecutive realized regions of a strand automatically satisfy the
step condition of `Flag_N` (`stepOK`, from `step_of_weights`: `λ(k') = λ(k) + i_X` forces
`k' = +_i k`). A valid object goes to the path bimodule `gammaR K N s w`: the iterated tensor
product of the step bimodules `stepB` (KL III Definition 5.6), read with the region to the left
of each strand given by the previous strand (the convention of `gammaP`), ending with the ring of
the rightmost region **viewed as an `(H, K)`-bimodule**: the right action of the rightmost ring is
forgotten. Objects that are not valid go to zero.

Forgetting the right action is harmless: the relations are proved in `Flag_N` for an arbitrary
suffix on the right (`Categorification.Flag.locTwo` and the whiskered cups and caps), and the target
of the functor of the presentation is a category of `K`-modules (`StringDiagrams.Presentation.lift`
needs a `K`-linear category, not a bicategory; see `Categorification.Flag.GammaTarget`).

## Main definitions

* `Realized`, `compOf`, `compOf_spec`, `compOf_eq`; `step_of_weights`, `stepOK`.
* `WOK N s w`: the object `⟨s, w⟩` is valid; `WOK.step`, `WOK.realized`, `WOK.tail`.
* `gammaR K N s w h : BRing (H K (compOf N s)) K`: the path bimodule.
* `trS`: the identification of `stepB ⊗ gammaR` along an equality of regions (needed by cups and
  caps, whose two boundaries continue from syntactically different regions).
* `RT M`: the underlying `K`-module of a bimodule `M : BRing A K` (via the right action).
-/

noncomputable section

namespace Categorification.Flag

open StringDiagrams Categorification.KL3.Diagram

universe u

variable {K : Type u} [Field K] {m : ℕ}

/-- The weights of `sl_{m+1}`. -/
abbrev Wt (m : ℕ) : Type := Fin m → ℤ

/-- The strand colours of the presentation of `U(sl_{m+1})`: a signed letter and the weight of
the region to its right. -/
abbrev WCol (m : ℕ) : Type := (psig (slRootDatum m)).Colour

/-! ### Weights and compositions -/

section Realize

variable (N : ℕ)

/-- The weight `λ` is `λ(k)` for a composition `k` of `N` into `m + 1` parts (KL III (5.18)). -/
def Realized (lam : Wt m) : Prop := ∃ d : Comp m, ∑ j, d j = N ∧ compWeight d = lam

open Classical in
/-- The composition of `N` of weight `λ` (junk if `λ` is not realized). -/
def compOf (lam : Wt m) : Comp m := if h : Realized N lam then h.choose else fun _ => 0

variable {N}

theorem compOf_spec {lam : Wt m} (h : Realized N lam) :
    ∑ j, compOf N lam j = N ∧ compWeight (compOf N lam) = lam := by
  rw [compOf, dif_pos h]
  exact h.choose_spec

theorem compOf_eq {lam : Wt m} {d : Comp m} (hd : ∑ j, d j = N) (hw : compWeight d = lam) :
    compOf N lam = d :=
  compWeight_injective ((compOf_spec ⟨d, hd, hw⟩).2.trans hw.symm)
    ((compOf_spec ⟨d, hd, hw⟩).1.trans hd.symm)

theorem compWeight_add (d e : Comp m) : compWeight (d + e) = compWeight d + compWeight e := by
  funext a
  simp only [compWeight, Pi.add_apply]
  push_cast
  ring

theorem compWeight_single_castSucc_sub (i : Fin m) :
    compWeight (Pi.single i.castSucc 1 : Comp m) =
      compWeight (Pi.single i.succ 1 : Comp m) + (slRootDatum m).iX i := by
  funext a
  simp only [compWeight, Pi.add_apply, slRootDatum_iX_apply, slCartan_dot, Pi.single_apply,
    Fin.ext_iff, Fin.coe_castSucc, Fin.val_succ]
  split_ifs <;> omega

theorem sum_add_single (d : Comp m) (j : Fin (m + 1)) :
    ∑ k, (d + (Pi.single j 1 : Comp m)) k = ∑ k, d k + 1 := by
  simp only [Pi.add_apply, Finset.sum_add_distrib]
  rw [Finset.sum_pi_single']
  simp

/-- **A step between realized weights is a step of compositions**: if `λ(k') = λ(k) + i_X` and
`k`, `k'` have the same size, then `k_{i+1} > 0` and `k' = +_i k`. -/
theorem step_of_weights (i : Fin m) {d d' : Comp m}
    (hw : compWeight d' = compWeight d + (slRootDatum m).iX i) (hs : ∑ j, d' j = ∑ j, d j) :
    0 < d i.succ ∧ raise i d = d' := by
  have key : d + Pi.single i.castSucc 1 = d' + Pi.single i.succ 1 := by
    refine compWeight_injective ?_ ?_
    · rw [compWeight_add, compWeight_add, hw, compWeight_single_castSucc_sub]
      abel
    · rw [sum_add_single, sum_add_single, hs]
  have hi : i.castSucc ≠ i.succ := (Fin.castSucc_lt_succ i).ne
  have e1 : d i.succ = d' i.succ + 1 := by
    have := congrFun key i.succ
    simpa [Pi.single_apply, hi.symm] using this
  refine ⟨by omega, funext fun j => ?_⟩
  have e2 := congrFun key j
  simp only [Pi.add_apply, Pi.single_apply] at e2
  rw [raise]
  by_cases h1 : j = i.castSucc
  · rw [if_pos h1] at e2 ⊢
    rw [if_neg (by rw [h1]; exact hi)] at e2
    omega
  · rw [if_neg h1] at e2 ⊢
    by_cases h2 : j = i.succ
    · rw [if_pos h2] at e2 ⊢
      omega
    · rw [if_neg h2] at e2 ⊢
      omega

/-- **The step condition of `Flag_N` holds between realized regions of a strand.** -/
theorem stepOK (l : SLetter m) {r s : Wt m} (hr : Realized N r) (hs : Realized N s)
    (hsrc : sh (slRootDatum m) l + r = s) : StepR l (compOf N r) (compOf N s) := by
  obtain ⟨hr1, hr2⟩ := compOf_spec hr
  obtain ⟨hs1, hs2⟩ := compOf_spec hs
  obtain ⟨b, i⟩ := l
  cases b with
  | true =>
    have hst := step_of_weights i (d := compOf N r) (d' := compOf N s)
      (by rw [hs2, hr2, ← hsrc]; simp only [sh, QuantumGroup.UDot.sgn_true, one_smul]; exact add_comm _ _) (hs1.trans hr1.symm)
    exact ⟨hst.2, hst.1⟩
  | false =>
    have hst := step_of_weights i (d := compOf N s) (d' := compOf N r)
      (by rw [hs2, hr2, ← hsrc, sh]; simp) (hr1.trans hs1.symm)
    exact ⟨hst.2, hst.1⟩

end Realize

/-! ### Valid objects -/

variable (N : ℕ)

/-- **The object `⟨s, w⟩` is valid**: it is well formed and all its regions are realized. -/
def WOK : Wt m → List (WCol m) → Prop
  | s, [] => Realized N s
  | s, c :: w => Realized N s ∧ sh (slRootDatum m) c.l + c.r = s ∧ WOK c.r w

variable {N}

theorem WOK.realized : {s : Wt m} → {w : List (WCol m)} → WOK N s w → Realized N s
  | _, [], h => h
  | _, _ :: _, h => h.1

theorem WOK.tail {s : Wt m} {c : WCol m} {w : List (WCol m)} (h : WOK N s (c :: w)) :
    WOK N c.r w := h.2.2

/-- The step condition of the first strand of a valid object. -/
theorem WOK.step {s : Wt m} {c : WCol m} {w : List (WCol m)} (h : WOK N s (c :: w)) :
    StepR c.l (compOf N c.r) (compOf N s) :=
  stepOK c.l h.2.2.realized h.1 h.2.1

theorem WOK.src {s : Wt m} {c : WCol m} {w : List (WCol m)} (h : WOK N s (c :: w)) :
    sh (slRootDatum m) c.l + c.r = s := h.2.1

/-- The validity of `⟨s, w⟩` is well formedness plus realizability of all regions. -/
theorem wok_iff (s : Wt m) (w : List (WCol m)) :
    WOK N s w ↔ (psig (slRootDatum m)).ok s w ∧ Realized N s ∧ ∀ c ∈ w, Realized N c.r := by
  induction w generalizing s with
  | nil => exact ⟨fun h => ⟨trivial, h, by simp⟩, fun h => h.2.1⟩
  | cons c w ih =>
    simp only [WOK, ih, Signature.ok_cons, psig_colourSrc, psig_colourTgt, List.mem_cons,
      forall_eq_or_imp]
    constructor
    · rintro ⟨hs, hsrc, hok, hr, hall⟩
      exact ⟨⟨hsrc, hok⟩, hs, hr, hall⟩
    · rintro ⟨⟨hsrc, hok⟩, hs, hr, hall⟩
      exact ⟨hs, hsrc, hok, hr, hall⟩

theorem wok_append {s : Wt m} {w w' : List (WCol m)} :
    WOK N s (w ++ w') ↔ WOK N s w ∧ WOK N ((psig (slRootDatum m)).endR s w) w' := by
  induction w generalizing s with
  | nil =>
    simp only [List.nil_append, Signature.endR_nil]
    exact ⟨fun h => ⟨h.realized, h⟩, fun h => h.2⟩
  | cons c w ih =>
    simp only [List.cons_append, WOK, ih, Signature.endR_cons, psig_colourTgt]
    exact ⟨fun ⟨a, b, c, d⟩ => ⟨⟨a, b, c⟩, d⟩, fun ⟨⟨a, b, c⟩, d⟩ => ⟨a, b, c, d⟩⟩

/-! ### Path bimodules -/

variable (K) (N)

/-- **`Γ_N` of a valid object** `⟨s, w⟩` (KL III (6.1)): the iterated tensor product of the step
bimodules, as an `(H_{k(s)}, K)`-bimodule. -/
def gammaR : (s : Wt m) → (w : List (WCol m)) → WOK N s w → BRing (H K (compOf N s)) K
  | s, [], _ => ⟨H K (compOf N s), RingHom.id _, algebraMap K _⟩
  | s, c :: w, h => (stepB K c.l (compOf N c.r) (compOf N s) h.step).tensor (gammaR c.r w h.tail)

theorem gammaR_cons (s : Wt m) (c : WCol m) (w : List (WCol m)) (h : WOK N s (c :: w)) :
    gammaR K N s (c :: w) h =
      (stepB K c.l (compOf N c.r) (compOf N s) h.step).tensor (gammaR K N c.r w h.tail) := rfl

variable {K N}

/-- The identification of `stepB ⊗ gammaR` along an equality of the region to the right of the
step (the left region `L` is fixed). -/
def trS (l : SLetter m) (L : Wt m) (a b : Wt m) (e : a = b) (p : List (WCol m))
    (h : StepR l (compOf N a) (compOf N L)) (h' : StepR l (compOf N b) (compOf N L))
    (hp : WOK N a p) (hp' : WOK N b p) :
    BHom ((stepB K l (compOf N a) (compOf N L) h).tensor (gammaR K N a p hp))
      ((stepB K l (compOf N b) (compOf N L) h').tensor (gammaR K N b p hp')) := by
  subst e
  exact BHom.id _

@[simp] theorem trS_rfl (l : SLetter m) (L a : Wt m) (p : List (WCol m))
    (h : StepR l (compOf N a) (compOf N L)) (hp : WOK N a p) :
    trS (K := K) l L a a rfl p h h hp hp = BHom.id _ := rfl

/-- The identification of `gammaR` along an equality of words (same start region). -/
def trW (s : Wt m) {w w' : List (WCol m)} (e : w = w') (h : WOK N s w) (h' : WOK N s w') :
    BHom (gammaR K N s w h) (gammaR K N s w' h') := by
  subst e
  exact BHom.id _

@[simp] theorem trW_rfl (s : Wt m) (w : List (WCol m)) (h : WOK N s w) :
    trW (K := K) s (rfl : w = w) h h = BHom.id _ := rfl

theorem trW_self (s : Wt m) {w : List (WCol m)} (e : w = w) (h h' : WOK N s w) :
    trW (K := K) s e h h' = BHom.id _ := rfl

theorem trW_cons (s : Wt m) (c : WCol m) {w w' : List (WCol m)} (e : w = w')
    (h : WOK N s (c :: w)) (h' : WOK N s (c :: w')) :
    trW (K := K) s (congrArg (c :: ·) e) h h' =
      BHom.whiskerLeft (stepB K c.l (compOf N c.r) (compOf N s) h.step)
        (trW c.r e h.tail h'.tail) := by
  subst e
  exact (BHom.whiskerLeft_id _ _).symm

theorem trW_trans (s : Wt m) {w w' w'' : List (WCol m)} (e : w = w') (e' : w' = w'')
    (h : WOK N s w) (h' : WOK N s w') (h'' : WOK N s w'') :
    (trW (K := K) s e' h' h'').comp (trW s e h h') = trW s (e.trans e') h h'' := by
  subst e e'
  rfl

/-! ### Underlying `K`-modules -/

/-- The underlying `K`-module of a bimodule with right ring `K`. -/
def RT {A : Type u} [CommRing A] (M : BRing A K) : Type u := M.T

instance {A : Type u} [CommRing A] (M : BRing A K) : AddCommGroup (RT M) :=
  inferInstanceAs (AddCommGroup M.T)

instance {A : Type u} [CommRing A] (M : BRing A K) : Module K (RT M) :=
  M.right.toModule

theorem RT.smul_def {A : Type u} [CommRing A] (M : BRing A K) (c : K) (x : RT M) :
    c • x = (show M.T from M.right c * (show M.T from x)) := rfl

/-- The `K`-linear map underlying a bimodule map. -/
def BHom.toLin {A : Type u} [CommRing A] {M M' : BRing A K} (φ : BHom M M') :
    RT M →ₗ[K] RT M' where
  toFun := φ
  map_add' := φ.map_add
  map_smul' c x := φ.map_right c x

@[simp] theorem BHom.toLin_apply {A : Type u} [CommRing A] {M M' : BRing A K} (φ : BHom M M')
    (x : RT M) : BHom.toLin φ x = φ x := rfl

theorem BHom.toLin_comp {A : Type u} [CommRing A] {M M' M'' : BRing A K} (φ : BHom M M')
    (ψ : BHom M' M'') : BHom.toLin (ψ.comp φ) = BHom.toLin ψ ∘ₗ BHom.toLin φ := rfl

theorem BHom.toLin_add {A : Type u} [CommRing A] {M M' : BRing A K} (φ ψ : BHom M M') :
    BHom.toLin (φ + ψ) = BHom.toLin φ + BHom.toLin ψ := rfl

theorem BHom.toLin_sub {A : Type u} [CommRing A] {M M' : BRing A K} (φ ψ : BHom M M') :
    BHom.toLin (φ - ψ) = BHom.toLin φ - BHom.toLin ψ := rfl

theorem BHom.toLin_neg {A : Type u} [CommRing A] {M M' : BRing A K} (φ : BHom M M') :
    BHom.toLin (-φ) = -BHom.toLin φ := rfl

theorem BHom.toLin_zero {A : Type u} [CommRing A] {M M' : BRing A K} :
    BHom.toLin (0 : BHom M M') = 0 := rfl

theorem BHom.toLin_id {A : Type u} [CommRing A] (M : BRing A K) :
    BHom.toLin (BHom.id M) = LinearMap.id := rfl

end Categorification.Flag

end

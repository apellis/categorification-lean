/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapTraceCutWindowLoading
import Categorification.WeightedKLR.Rigidity.CupCapReflectedCapAdjunction
import Categorification.Algebra.EndCornerPart

/-!
# The dévissage of the window part of `S_+` at one loading

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half: the reduction of
`Hom_W(L', e'_s S_+(X))` to the leading layer of the head-strand filtration. Here `W` is the
KLR algebra of the strands at the maximum, `s` a loading of `λ` and `e'_s = ι_s(1_{red-ordered})`
the `s`-summand of the reflected unit `e` of the maximum (`windowUnit`).

* `ι_s` is a non-unital ring map `W → T^{λ⁺}` (`windowHomAt`), and `e'_s` commutes with its
  image (`windowHomAt_redOrdered_comm`), because `e` commutes with the window action. So
  `e'_s S_+(X)` is a `W`-module (`EndCornerPart`).
* The head-strand filtration at the end `p + N` of the window, `p = midPos s`, indexed so that
  step `m` is `F_{N - m}` and step `N + 1` is `0` (`plusHeadFilt`), is preserved by `ι_s(W)`
  (Claim A, `plusMackeyFilt_insertMap`), and its step `0` contains `e'_s S_+(X)`
  (`plusWindowCornerFilt_top`, from `plusStandardAction_insertMap_redOrdered_mem`).
* **Dévissage** (`plusWindowCorner_devissage`): if the layers from the first on are right
  orthogonal to `L`, composing with `e'_s S_+(X) → e'_s S_+(X) / F_{N-1}` is a bijection on
  `Hom_W(L, -)`.

**Route hypothesis.** The right orthogonality of the layers (`hlay`) is the coinduced-layer
hypothesis of the trace half of Lemma 7.19 (each layer is coinduced from a corner killing `L'`).
It is a hypothesis of this intermediate statement only, tracked for removal. Webster's proof
does not spell out this step.

## Main results

* `Stendhal.CupCap.windowHomAt`, `Stendhal.CupCap.windowHomAt_redOrdered_comm`,
  `Stendhal.CupCap.windowEndAt`, `Stendhal.CupCap.plusHeadFilt`,
  `Stendhal.CupCap.plusWindowCornerFilt_top`, `Stendhal.CupCap.plusWindowCorner_devissage`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra

section Lower

variable {I k : Type*} [DecidableEq I] [CommRing k] {a r : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin (a + r) → I →₀ ℕ} {θ β : Multiset I}
  {N : Type*} [AddCommGroup N] [Module k N] [Module (cutFactorAlgebra Q Λ θ β) N]

/-- The steps `F_{c-1}` of the Mackey filtration of a cut increase with `c`. -/
theorem cutMackeyFiltLower_mono {n c c' : ℕ} (h : c ≤ c') :
    cutMackeyFiltLower Q Λ θ β N n c ≤ cutMackeyFiltLower Q Λ θ β N n c' := by
  rcases c with _ | c
  · rw [cutMackeyFiltLower_zero]; exact bot_le
  · rcases c' with _ | c'
    · omega
    · rw [cutMackeyFiltLower_succ, cutMackeyFiltLower_succ]
      exact cutMackeyFilt_mono (by omega)

end Lower

namespace CupCap

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {θ γ ν₀ : Multiset I}

set_option hygiene false in
local notation "Rc" => KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)
set_option hygiene false in
local notation "Tq" => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) ((θ + γ) + ν₀)

variable (j hj Q Λ Λc θ γ ν₀) in
/-- **The window at one loading** `ι_s : W → T^{λ⁺}`, a non-unital ring map. -/
def windowHomAt (s : Seq (stendhalWeight ℓ (θ + γ))) : Rc →ₙ+* Tq where
  toFun g := tensorOfKLR Q (plusLabels Λ Λc j hj) ((θ + γ) + ν₀)
    (insertMap (j := j) (hj := hj) Q Λ Λc s (midPos j s) (midPos_le j s) g)
  map_mul' g h := by simp only [insertMap_mul, tensorOfKLR, map_mul]
  map_zero' := by simp only [insertMap, map_zero, KLR.Corner.val_zero, tensorOfKLR]
  map_add' g h := by simp only [insertMap, map_add, KLR.Corner.val_add, tensorOfKLR]

theorem windowHomAt_apply (s : Seq (stendhalWeight ℓ (θ + γ))) (g : Rc) :
    windowHomAt j hj Q Λ Λc θ γ ν₀ s g = tensorOfKLR Q (plusLabels Λ Λc j hj) ((θ + γ) + ν₀)
      (insertMap (j := j) (hj := hj) Q Λ Λc s (midPos j s) (midPos_le j s) g) := rfl

/-- `ι_s(x) · (window action of y) = ι_s(x y)`. -/
theorem windowHomAt_mul_windowAct (s : Seq (stendhalWeight ℓ (θ + γ))) (x y : Rc) :
    windowHomAt j hj Q Λ Λc θ γ ν₀ s x * windowAct j hj Q Λ Λc (θ + γ) ν₀ y =
      windowHomAt j hj Q Λ Λc θ γ ν₀ s (x * y) := by
  rw [windowHomAt_apply, windowAct_eq, windowHomAt_apply, ← insertMap_mul_midMapKLR]
  simp only [tensorOfKLR, map_mul]

/-- The window action of the red-ordered idempotent commutes with the window action. -/
theorem windowAct_redOrdered_mul_comm (g : Rc) :
    windowAct j hj Q Λ Λc (θ + γ) ν₀ (redOrderedKLR k Q Λc ν₀ * g) =
      windowAct j hj Q Λ Λc (θ + γ) ν₀ (g * redOrderedKLR k Q Λc ν₀) := by
  rw [windowAct_mul, windowAct_mul, ← windowUnit_eq_windowAct, windowAct_mul_windowUnit]

/-- **`e'_s = ι_s(1_{red-ordered})` commutes with `ι_s(W)`.** -/
theorem windowHomAt_redOrdered_comm (s : Seq (stendhalWeight ℓ (θ + γ))) (g : Rc) :
    windowHomAt j hj Q Λ Λc θ γ ν₀ s (redOrderedKLR k Q Λc ν₀) *
        windowHomAt j hj Q Λ Λc θ γ ν₀ s g =
      windowHomAt j hj Q Λ Λc θ γ ν₀ s g *
        windowHomAt j hj Q Λ Λc θ γ ν₀ s (redOrderedKLR k Q Λc ν₀) := by
  rw [← map_mul, ← map_mul, ← one_mul (redOrderedKLR k Q Λc ν₀ * g),
    ← one_mul (g * redOrderedKLR k Q Λc ν₀), ← windowHomAt_mul_windowAct,
    ← windowHomAt_mul_windowAct, windowAct_redOrdered_mul_comm]

variable (N : Type) [AddCommGroup N] [Module k N] [Module (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) N]
  [IsScalarTower k (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) N] (hQ : KLRSymm Q)

variable (j hj Q Λ Λc θ γ ν₀) in
/-- The action of `T^{λ⁺}((θ + γ) + ν₀)` on `S_+(N)`. -/
def plusActionCast : Tq →ₐ[k] Module.End k (PlusStandard Q Λ Λc j hj θ ν₀ γ N hQ) :=
  (plusStandardAction Q Λ Λc j hj θ ν₀ γ N hQ).comp
    (castTensorProductAlgebra Q (plusLabels Λ Λc j hj) (plusWeight_eq θ γ ν₀)).symm.toAlgHom

theorem plusActionCast_apply (t : Tq) :
    plusActionCast j hj Q Λ Λc θ γ ν₀ N hQ t = plusStandardAction Q Λ Λc j hj θ ν₀ γ N hQ
      ((castTensorProductAlgebra Q (plusLabels Λ Λc j hj) (plusWeight_eq θ γ ν₀)).symm t) :=
  rfl

variable (j hj Q Λ Λc θ γ ν₀) in
/-- **The window at `s` acting on `S_+(N)`**, `g ↦ ι_s(g)`, a non-unital ring map. -/
def windowEndAt (s : Seq (stendhalWeight ℓ (θ + γ))) :
    Rc →ₙ+* Module.End k (PlusStandard Q Λ Λc j hj θ ν₀ γ N hQ) :=
  (plusActionCast j hj Q Λ Λc θ γ ν₀ N hQ).toRingHom.toNonUnitalRingHom.comp
    (windowHomAt j hj Q Λ Λc θ γ ν₀ s)

theorem windowEndAt_eq (s : Seq (stendhalWeight ℓ (θ + γ))) (g : Rc) :
    windowEndAt j hj Q Λ Λc θ γ ν₀ N hQ s g =
      plusActionCast j hj Q Λ Λc θ γ ν₀ N hQ (windowHomAt j hj Q Λ Λc θ γ ν₀ s g) := rfl

theorem windowEndAt_apply (s : Seq (stendhalWeight ℓ (θ + γ))) (g : Rc) :
    windowEndAt j hj Q Λ Λc θ γ ν₀ N hQ s g = plusStandardAction Q Λ Λc j hj θ ν₀ γ N hQ
      ((castTensorProductAlgebra Q (plusLabels Λ Λc j hj) (plusWeight_eq θ γ ν₀)).symm
        (tensorOfKLR Q (plusLabels Λ Λc j hj) ((θ + γ) + ν₀)
          (insertMap (j := j) (hj := hj) Q Λ Λc s (midPos j s) (midPos_le j s) g))) := rfl

theorem windowEndAt_comm (s : Seq (stendhalWeight ℓ (θ + γ))) (g : Rc) :
    windowEndAt j hj Q Λ Λc θ γ ν₀ N hQ s (redOrderedKLR k Q Λc ν₀) *
        windowEndAt j hj Q Λ Λc θ γ ν₀ N hQ s g =
      windowEndAt j hj Q Λ Λc θ γ ν₀ N hQ s g *
        windowEndAt j hj Q Λ Λc θ γ ν₀ N hQ s (redOrderedKLR k Q Λc ν₀) := by
  have h := congrArg (plusActionCast j hj Q Λ Λc θ γ ν₀ N hQ)
    (windowHomAt_redOrdered_comm (j := j) (hj := hj) (Q := Q) (Λ := Λ) (Λc := Λc) s g)
  rw [map_mul (plusActionCast j hj Q Λ Λc θ γ ν₀ N hQ),
    map_mul (plusActionCast j hj Q Λ Λc θ γ ν₀ N hQ)] at h
  exact h

theorem windowEndAt_one_mul (s : Seq (stendhalWeight ℓ (θ + γ))) :
    windowEndAt j hj Q Λ Λc θ γ ν₀ N hQ s 1 *
        windowEndAt j hj Q Λ Λc θ γ ν₀ N hQ s (redOrderedKLR k Q Λc ν₀) =
      windowEndAt j hj Q Λ Λc θ γ ν₀ N hQ s (redOrderedKLR k Q Λc ν₀) := by
  rw [← map_mul, one_mul]

/-- **Claim A on the steps `F_{c-1}`**: `ι_s(W)` preserves every step of the head-strand
filtration at the end of the window of `s`. -/
theorem windowEndAt_mem_lower (s : Seq (stendhalWeight ℓ (θ + γ))) (c : ℕ) (g : Rc)
    (v : PlusStandard Q Λ Λc j hj θ ν₀ γ N hQ)
    (hv : v ∈ cutMackeyFiltLower Q (plusBlockLabels Λ Λc j hj) θ (ν₀ + γ)
      (BlocksMid Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ (PlusInput Q Λ Λc j hj θ ν₀ γ N) hQ)
      (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) c) :
    windowEndAt j hj Q Λ Λc θ γ ν₀ N hQ s g v ∈
      cutMackeyFiltLower Q (plusBlockLabels Λ Λc j hj) θ (ν₀ + γ)
        (BlocksMid Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ (PlusInput Q Λ Λc j hj θ ν₀ γ N) hQ)
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) c := by
  rcases c with _ | c
  · rw [cutMackeyFiltLower_zero, Submodule.mem_bot] at hv
    rw [hv, map_zero]; exact zero_mem _
  · rw [windowEndAt_apply]
    exact plusMackeyFilt_insertMap j hj Q Λ Λc θ γ ν₀ hQ N s g hv

variable (j hj Q Λ Λc θ γ ν₀) in
/-- **The head-strand filtration at the window of `s`**, indexed for the dévissage: step `m` is
`F_{N - m}` for the top cut at the end `p + N` of the window, and step `N + 1` is `0`. -/
def plusHeadFilt (s : Seq (stendhalWeight ℓ (θ + γ))) (m : ℕ) :
    Submodule k (PlusStandard Q Λ Λc j hj θ ν₀ γ N hQ) :=
  cutMackeyFiltLower Q (plusBlockLabels Λ Λc j hj) θ (ν₀ + γ)
    (BlocksMid Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ (PlusInput Q Λ Λc j hj θ ν₀ γ N) hQ)
    (midPos j s + Multiset.card (stendhalWeight 2 ν₀))
    (Multiset.card (stendhalWeight 2 ν₀) + 1 - m)

/-- **Claim A on the indexed filtration**: `ι_s(W)` preserves every step. -/
theorem plusHeadFilt_action (s : Seq (stendhalWeight ℓ (θ + γ))) (m : ℕ) (g : Rc)
    (v : PlusStandard Q Λ Λc j hj θ ν₀ γ N hQ)
    (hv : v ∈ plusHeadFilt j hj Q Λ Λc θ γ ν₀ N hQ s m) :
    windowEndAt j hj Q Λ Λc θ γ ν₀ N hQ s g v ∈ plusHeadFilt j hj Q Λ Λc θ γ ν₀ N hQ s m := by
  exact windowEndAt_mem_lower N hQ s _ g v hv

theorem plusHeadFilt_anti (s : Seq (stendhalWeight ℓ (θ + γ))) (m : ℕ) :
    plusHeadFilt j hj Q Λ Λc θ γ ν₀ N hQ s (m + 1) ≤ plusHeadFilt j hj Q Λ Λc θ γ ν₀ N hQ s m :=
  cutMackeyFiltLower_mono (by omega)

theorem plusHeadFilt_last (s : Seq (stendhalWeight ℓ (θ + γ))) :
    plusHeadFilt j hj Q Λ Λc θ γ ν₀ N hQ s (Multiset.card (stendhalWeight 2 ν₀) + 1) = ⊥ := by
  rw [plusHeadFilt, Nat.sub_self, cutMackeyFiltLower_zero]

/-- `e'_s S_+(N)` as a `W`-module. -/
local notation "Epart" s => EndCornerPart (windowEndAt j hj Q Λ Λc θ γ ν₀ N hQ s)
  (windowEndAt j hj Q Λ Λc θ γ ν₀ N hQ s (redOrderedKLR k Q Λc ν₀))
  (windowEndAt_comm N hQ s) (windowEndAt_one_mul N hQ s)

/-- **Step `0` is all of `e'_s S_+(N)`**, for `s` whose red strands left of `midPos s` are among
`λ_1, …, λ_j`. -/
theorem plusWindowCornerFilt_top (hsym : KLRSymm (stendhalQ Q (plusBlockLabels Λ Λc j hj)))
    (s : Seq (stendhalWeight ℓ (θ + γ)))
    (hs : ∀ a : Fin (Multiset.card (stendhalWeight ℓ (θ + γ))), a.val < midPos j s →
      ∀ u : Fin ℓ, s.lbl a = .inr u → u.val < j)
    (x : Epart s) : x.val ∈ plusHeadFilt j hj Q Λ Λc θ γ ν₀ N hQ s 0 := by
  have h := plusStandardAction_insertMap_redOrdered_mem Q Λ Λc hQ hsym s hs x.val
  rw [← windowEndAt_apply, x.prop] at h
  exact h

/-- **Dévissage of `Hom_W(L, e'_s S_+(N))`** along the head-strand filtration at the window of
`s`. Route hypothesis `hlay`: the layers from the first on are right orthogonal to `L` (the
coinduced-layer hypothesis of the trace half of Webster v3, Lemma 7.19, tracked for removal).
Then composing with the projection to `e'_s S_+(N) / F_{N-1}` is a bijection. -/
theorem plusWindowCorner_devissage (s : Seq (stendhalWeight ℓ (θ + γ)))
    (L : Type) [AddCommGroup L] [Module Rc L]
    (hlay : ∀ m, 1 ≤ m → IsRightOrthogonal Rc L
      ((endCornerSub _ _ (windowEndAt_comm N hQ s) (windowEndAt_one_mul N hQ s)
          (plusHeadFilt j hj Q Λ Λc θ γ ν₀ N hQ s m) (plusHeadFilt_action N hQ s m)).map
        (endCornerSub _ _ (windowEndAt_comm N hQ s) (windowEndAt_one_mul N hQ s)
          (plusHeadFilt j hj Q Λ Λc θ γ ν₀ N hQ s (m + 1))
          (plusHeadFilt_action N hQ s (m + 1))).mkQ)) :
    Function.Bijective fun h : L →ₗ[Rc] (Epart s) =>
      (endCornerSub _ _ (windowEndAt_comm N hQ s) (windowEndAt_one_mul N hQ s)
        (plusHeadFilt j hj Q Λ Λc θ γ ν₀ N hQ s 1) (plusHeadFilt_action N hQ s 1)).mkQ ∘ₗ h :=
  bijective_mkQ_comp_of_endCornerFilt _ _ _ _ (plusHeadFilt j hj Q Λ Λc θ γ ν₀ N hQ s)
    (plusHeadFilt_action N hQ s) (plusHeadFilt_anti N hQ s) _ (plusHeadFilt_last N hQ s) hlay

end CupCap

end Categorification.Stendhal

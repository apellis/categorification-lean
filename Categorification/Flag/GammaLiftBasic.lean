/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.GammaInterchange
import Categorification.Diagrams.KL3.Relations

/-!
# Evaluating normal-form relations of `U(sl_{m+1})` under `Γ_N`: validity of objects

The relations of KL III / Cautis–Lauda are diagrams in normal form (`Categorification.KL3.
Diagram.mkD`: layers `lay μ u g v` on the objects `ob μ t`). Their images under `Γ_N` are the
chain maps `chainBD`, whose case distinctions are on the validity (`WOK`) of the intermediate
objects. Here: the validity of a normal-form object `ob μ t` (whiskered by `v`) is the
realizability of the weights of its regions (`wok_ob_iff`); the top boundary of a layer is valid
as soon as the corresponding normal-form object is (`wok_dataV_cod`).
-/

noncomputable section

namespace Categorification.Flag

open StringDiagrams Categorification.KL3.Diagram CategoryTheory

universe u

variable {m : ℕ} {N : ℕ}

local notation "RD" => slRootDatum m

/-- **Validity of a normal-form object**: `ob μ t`, followed by `v`, is valid iff the weights
`wt μ t'` of the regions (`t'` the suffixes of `t`) are realized and `v` is valid from `μ`. -/
theorem wok_ob_iff (μ : Wt m) (v : List (psig RD).Colour) :
    ∀ t : List (Letter (Fin m)),
      WOK N (ob RD μ t).start ((ob RD μ t).word ++ v) ↔
        (∀ n, n < t.length → Realized N (wt RD μ (t.drop n))) ∧ WOK N μ v
  | [] => by simp
  | l :: t => by
    show Realized N (wt RD μ (l :: t)) ∧ sh RD l + wt RD μ t = wt RD μ (l :: t) ∧
      WOK N (ob RD μ t).start ((ob RD μ t).word ++ v) ↔ _
    rw [wok_ob_iff μ v t]
    constructor
    · rintro ⟨h0, -, hall, hv⟩
      refine ⟨fun n hn => ?_, hv⟩
      rcases n with _ | n
      · exact h0
      · exact hall n (by simpa using hn)
    · rintro ⟨hall, hv⟩
      exact ⟨hall 0 (by simp), rfl, fun n hn => hall (n + 1) (by simpa using hn), hv⟩

theorem Realized.congr {a b : Wt m} (h : Realized N a) (e : a = b) : Realized N b := e ▸ h

/-- The top boundary of a normal-form layer, whiskered by `v`, is valid as soon as the
corresponding normal-form object is. -/
theorem wok_dataV_cod (μ : Wt m) (u : List (Letter (Fin m))) (g : Shape (Fin m))
    (w : List (Letter (Fin m))) (v : List (psig RD).Colour)
    (h : WOK N (ob RD μ (u ++ g.cod ++ w)).start ((ob RD μ (u ++ g.cod ++ w)).word ++ v)) :
    WOK N (lay RD μ u g w).start ((dataV v (lay RD μ u g w)).1 ++
      gcod (dataV v (lay RD μ u g w)).2.1 ++ (dataV v (lay RD μ u g w)).2.2) := by
  have hc := lay_cod RD μ u g w
  have e : (dataV v (lay RD μ u g w)).1 ++ gcod (dataV v (lay RD μ u g w)).2.1 ++
      (dataV v (lay RD μ u g w)).2.2 = (lay RD μ u g w).cod.word ++ v := by
    simp only [dataV, Layer.cod, List.append_assoc]
  rw [e, show (lay RD μ u g w).start = (lay RD μ u g w).cod.start from rfl, hc]
  exact h

/-- `wok_dataV_cod` with the start region of the chain. -/
theorem wok_dataV_cod' (s : Wt m) (μ : Wt m) (u : List (Letter (Fin m))) (g : Shape (Fin m))
    (w : List (Letter (Fin m))) (v : List (psig RD).Colour)
    (hs : s = (lay RD μ u g w).start)
    (h : WOK N (ob RD μ (u ++ g.cod ++ w)).start ((ob RD μ (u ++ g.cod ++ w)).word ++ v)) :
    WOK N s ((dataV v (lay RD μ u g w)).1 ++
      gcod (dataV v (lay RD μ u g w)).2.1 ++ (dataV v (lay RD μ u g w)).2.2) :=
  hs ▸ wok_dataV_cod μ u g w v h

variable {K : Type u} [Field K]

/-- **Changing the layer data of a chain along an equality** (for instance, rewriting the weights
of the regions into a canonical form): the chain map changes by the identifications `trW` of the
end words. -/
theorem chainBD_congr (dnScal : Fin m → Fin m → K) (s : Wt m) {w₁ w₂ w₁' w₂' : List (WCol m)}
    {ls₁ ls₂ : List (LData m)} (e : w₁ = w₂) (e' : w₁' = w₂') (el : ls₁ = ls₂)
    (h₁ : ChainW w₁ ls₁ w₁') (h₂ : ChainW w₂ ls₂ w₂') (ha₁ : WOK N s w₁) (ha₂ : WOK N s w₂)
    (hb₁ : WOK N s w₁') (hb₂ : WOK N s w₂') :
    chainBD K N dnScal s w₁ ls₁ w₁' h₁ ha₁ hb₁ =
      (trW s e'.symm hb₂ hb₁).comp ((chainBD K N dnScal s w₂ ls₂ w₂' h₂ ha₂ hb₂).comp
        (trW s e ha₁ ha₂)) := by
  subst e e' el
  rfl

/-- **Two chains with the same ends agree** as soon as their layer data can be rewritten to
layer data whose chain maps agree. -/
theorem chainBD_eq_of_congr (dnScal : Fin m → Fin m → K) (s : Wt m)
    {w₁ w₂ w₁' w₂' : List (WCol m)} {ls₁ ls₂ ms₁ ms₂ : List (LData m)} (e : w₁ = w₂)
    (e' : w₁' = w₂') (el : ls₁ = ls₂) (em : ms₁ = ms₂)
    (h₁ : ChainW w₁ ls₁ w₁') (h₂ : ChainW w₂ ls₂ w₂') (k₁ : ChainW w₁ ms₁ w₁')
    (k₂ : ChainW w₂ ms₂ w₂') (ha₁ : WOK N s w₁) (ha₂ : WOK N s w₂) (hb₁ : WOK N s w₁')
    (hb₂ : WOK N s w₂')
    (H : chainBD K N dnScal s w₂ ls₂ w₂' h₂ ha₂ hb₂ = chainBD K N dnScal s w₂ ms₂ w₂' k₂ ha₂ hb₂) :
    chainBD K N dnScal s w₁ ls₁ w₁' h₁ ha₁ hb₁ = chainBD K N dnScal s w₁ ms₁ w₁' k₁ ha₁ hb₁ := by
  subst e e' el em
  exact H

end Categorification.Flag

end

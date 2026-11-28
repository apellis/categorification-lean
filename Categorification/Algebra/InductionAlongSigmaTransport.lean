/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongTransportEquiv
import Categorification.Algebra.InductionAlongSigma

/-!
# Transporting Rouquier's maps along ring isomorphisms

Given ring isomorphisms `A₀ ≃ A₀'`, `A ≃ A'`, `B ≃ B'` intertwining nonunital maps
`φ₂ : A₀ → A`, `φ₁ : A → B` with `φ₂'`, `φ₁'`, and a semilinear isomorphism `M ≃ M'`, the
transports `indResTransport` and `resIndTransport` of `Ind Res M` and `Res Ind M` intertwine

* the units and counits of `Ind ⊣ Res` (`resIndTransport_unitMap`,
  `counitMap_indResTransport`);
* the dots, right multiplication by intertwining elements (`indResTransport_natMap`,
  `resIndTransport_resMap_natMap`);
* Rouquier's rightward crossings `sigmaLin` (`resIndTransport_sigmaLin`).

This moves Rouquier's maps of the categorical action between the tensor product algebra and
the all-down matrix ring through the repaired Webster Lemma 4.29 (arXiv:1309.3796v3).
-/

noncomputable section

namespace Categorification.InductionAlong

open MulOpposite

universe u w

section Basic

variable {A B A' B' : Type u} [Ring A] [Ring B] [Ring A'] [Ring B'] {φ : A →ₙ+* B}
  {φ' : A' →ₙ+* B'} (a : A ≃+* A') (c : B ≃+* B') (h : ∀ t, φ' (a t) = c (φ t))
  {N : Type w} [AddCommGroup N] [Module A N] {N' : Type w} [AddCommGroup N'] [Module A' N']
  (e : N ≃+ N') (he : ∀ (t : A) n, e (t • n) = a t • e n)

theorem transportCorner_unitGen : transportCorner a c h (unitGen φ) = unitGen φ' :=
  Subtype.ext (by
    change c (φ 1) = φ' 1
    rw [← h, map_one])

/-- `Ind.transport` intertwines right multiplication by corresponding intertwining elements. -/
theorem Ind.transport_natMap {d : B} (hd : Intertwines φ φ d) {d' : B'}
    (hd' : Intertwines φ' φ' d') (hdd : c d = d') (x : Ind N φ) :
    Ind.transport a c h e he (natMap hd x) = natMap hd' (Ind.transport a c h e he x) := by
  induction x using Ind.induction_on with
  | zero => simp only [map_zero]
  | add s t hs ht => rw [map_add, map_add, hs, ht, map_add, map_add]
  | tmul z n =>
    rw [natMap_tmul, Ind.transport_tmul, Ind.transport_tmul, natMap_tmul]
    congr 1
    exact Subtype.ext (by
      change c (z.1 * d) = c z.1 * d'
      rw [map_mul, hdd])

end Basic

variable {A₀ A B A₀' A' B' : Type u} [Ring A₀] [Ring A] [Ring B] [Ring A₀'] [Ring A'] [Ring B']
  {φ₂ : A₀ →ₙ+* A} {φ₁ : A →ₙ+* B} {φ₂' : A₀' →ₙ+* A'} {φ₁' : A' →ₙ+* B'}
  (a₀ : A₀ ≃+* A₀') (a : A ≃+* A') (b : B ≃+* B')
  (h₂ : ∀ t, φ₂' (a₀ t) = a (φ₂ t)) (h₁ : ∀ t, φ₁' (a t) = b (φ₁ t))
  {M M' : Type u} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A' M']
  (e : M ≃+ M') (he : ∀ (t : A) m, e (t • m) = a t • e m)

omit [Ring A₀] [Ring A₀'] in
theorem resIndTransport_unitMap (m : M) :
    resIndTransport a b h₁ e he (unitMap (φ := φ₁) M m) = unitMap (φ := φ₁') M' (e m) :=
  Res.ext (by
    change Ind.transport a b h₁ e he (Ind.tmul (unitGen φ₁) m) = Ind.tmul (unitGen φ₁') (e m)
    rw [Ind.transport_tmul, transportCorner_unitGen])

omit [Ring B] [Ring B'] in
theorem counitMap_indResTransport (x : Ind (Res φ₂ M) φ₂) :
    counitMap M' (indResTransport a₀ a h₂ e he x) = e (counitMap M x) := by
  induction x using Ind.induction_on with
  | zero => simp only [map_zero]
  | add s t hs ht => rw [map_add, map_add, hs, ht, map_add, map_add]
  | tmul z m =>
    change counitMap M' (Ind.tmul (transportCorner a₀ a h₂ z) (Res.transport a₀ a h₂ e he m)) =
      e (z.1 • m.val)
    rw [counitMap_tmul, he]
    rfl

omit [Ring B] [Ring B'] in
theorem indResTransport_natMap {d : A} (hd : Intertwines φ₂ φ₂ d) {d' : A'}
    (hd' : Intertwines φ₂' φ₂' d') (hdd : a d = d') (x : Ind (Res φ₂ M) φ₂) :
    indResTransport a₀ a h₂ e he (natMap hd x) = natMap hd' (indResTransport a₀ a h₂ e he x) :=
  Ind.transport_natMap a₀ a h₂ _ _ hd hd' hdd x

omit [Ring A₀] [Ring A₀'] in
theorem resIndTransport_resMap_natMap {d : B} (hd : Intertwines φ₁ φ₁ d) {d' : B'}
    (hd' : Intertwines φ₁' φ₁' d') (hdd : b d = d') (x : Res φ₁ (Ind M φ₁)) :
    resIndTransport a b h₁ e he (Res.map (natMap hd) x) =
      Res.map (natMap hd') (resIndTransport a b h₁ e he x) :=
  Res.ext (Ind.transport_natMap a b h₁ e he hd hd' hdd x.val)

/-- `resIndTransport` and `indResTransport` intertwine the rightward crossings `sigmaLin` of
corresponding elements. -/
theorem resIndTransport_sigmaLin {c : B} (hc : ∀ t, c * φ₁ (φ₂ t) = φ₁ (φ₂ t) * c) {c' : B'}
    (hc' : ∀ t, c' * φ₁' (φ₂' t) = φ₁' (φ₂' t) * c') (hcc : b c = c')
    (x : Ind (Res φ₂ M) φ₂) :
    resIndTransport a b h₁ e he (sigmaLin φ₂ φ₁ hc M x) =
      sigmaLin φ₂' φ₁' hc' M' (indResTransport a₀ a h₂ e he x) := by
  induction x using Ind.induction_on with
  | zero => simp only [map_zero]
  | add s t hs ht => rw [map_add, map_add, hs, ht, map_add, map_add]
  | tmul z m =>
    apply Res.ext
    change Ind.transport a b h₁ e he (Ind.tmul (sigmaElt φ₂ φ₁ c z) m.val) =
      Ind.tmul (sigmaElt φ₂' φ₁' c' (transportCorner a₀ a h₂ z)) (e m.val)
    rw [Ind.transport_tmul]
    congr 1
    exact Subtype.ext (by
      change b (φ₁ z.1 * (c * φ₁ 1)) = φ₁' (a z.1) * (c' * φ₁' 1)
      rw [map_mul, map_mul, hcc, ← h₁, ← h₁]
      exact congrArg (fun t => φ₁' (a z.1) * (c' * φ₁' t)) (map_one a))

end Categorification.InductionAlong
